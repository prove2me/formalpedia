-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4062
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:27:27.911208+00:00
-- url     : https://prove2.me/submissions/5138a9bb-d64b-4c24-8621-8076148b234f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 730395683 ≤ n < 730575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 730396933 1250 730395683 730395697
    0xf0712050a1205071b0603050702010606091e080d05030702151e0a0e0709020307020c010804051e1c05030414060f0403050d0f09051005010509220303240f0f0b 70
    0x7080d2190700412400b0b843c24018203500070304045640300781711400e180f0280c03850111020790b20306104a8550b580141e0a0b90302a00680002441201d402c10280e40c05c02d2501171010503075401d00e040e0070784441030079007048034403418080882c400000707000c030710395041265508100f0608444415424908114401910304c4501204101042400f00e002c01015a00c041d8050074802c0072035800903038031035140019400c21183c03440503006102242c00c1ca54061452644525800000b400c1010350611903450071002d4010b80a0030f9120f5003a4020b107003101000350003051b450030340b40d554807803803c0e1074400c2080c414400c80c0c28058001106010364601da00403c542c00c0b0b503141c20519102d000c06081c50f002480a21000700100f810240b40e20b00348800402c005900040d40b0205001581e00d810a101d60100107032080c444c0b05104401c0d0100840ca652170580805100c1c4c03502041c02c0c0107801114502160881c16503088000c0c030f40d001c000c0b800140c18003000400c4440440f0480c1403401d14180c0882c06000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 730398183 1250 730396933 730396943
    0x50a140103051509040f26120a06030c08010f0b2211190e090709061409030a0b0703021b0d020a022e02030c0c01091203120b0603090f0712050a 63
    0x20003c203114010603440404050006460a02646014205040b82c0246140181c074a0346c10380210388900480090b491500030750640ba624901001c0c0ca0384c170100c03001c00a0220802d0707680c0f4030001c00081c0e414090500180f10b243c00100e21105484894030482c0e02c01c6c400d151264104050001d0f41c0a0b00004009800c040d07814001504000c031005031a02d0320850045024000701c001e40b1460054000b110300d0005601a500f4180c0d0ba0749a44050340c0b1100d490260f50b02080c60000c04c0001d0307001040052000d2034015040c0c03054081c071039642c010101401d4031000f01190f0007050159500c040c2c291114615403c85c80248007041621030b002e07440e80154403003e401011070b070b904c2102100c521035405001c040b0b00c00601c84080c401c058000d40306d8100300c0c0164601c2c014034444426a40c490240740d0b0a070f0f188640541c0c4115180ea6050f10991002c1c003040c0c440940b04e081440c2c03a03070380725000345224942e401c02600c500078a214056003000c2c555049988400710240c030343c4010070300006440001035441 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 730399433 1250 730398183 730398191
    0x605070f06051e0901060302091906080607050307020c010e10030209060702120f070f0e070309051507020c100215040807030c0b0703020702010e010c050a0305031009021909050a140103 81
    0x9420301900c440022500a4060380c14207060207009038860100154a201d9001078039060349400e801a82070310a1403101039400903a01d00820f00b6200301c1382c1c51020726510700d200018101c2c2d564007014100711b000c40b9840c1c08514003108008900d43c060224034082c0c3c2003482d01015201003c000144e40b42482c643d003604155000c591009251075480499003000e4008110f000d00800c034810441c0c5c1c41c030001e560385900c0d0241140004002084035056401c0d038124040d14940e6076100d42049006001c0850195036a02c1070001c1000c0341c030320071401c0c07a0064a6a034046e21604200c9002e0180320b08503414041c0455002d11518445445c0008003141c015034014010340d07a410450608590400d0a481e01038015030b112005c3c4020144c065008101c014402e032a504c1240408000650b94801c4400024043c2d80101c05000c00181c40744d40115800301c0c040200c046c2c480d8481c403001d8100d802003108000030b41c22148602076015004a1b07400c5c000e00080b83c0f4980c01c60304001891903520710842c00c8a040c1615 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 730400683 1250 730399433 730399447
    0x12030c012a2c0105070c3b0403051303060c0908070b09010c080c0f06130c050d0b15120d0c050c04021306080a0902041a010906021207020d05030403050106030803010905130c0605 78
    0xc04d03000c0f51003aa400029075440d00e501c4841d840c4607200641e41ca4081ca580d240041102d035200303144a84901300e1342000711421680c41d0b0300c0503100b0b60b101e0013100300a00789a050220006446100d64215483c444d61042401c9060810f83e82c41c0500b2608042080141402078000d641c6e40003401411031079204c081241c8409200784503900d17040c011030464941d8000c840030000082d00740d00080860394018000ca5018a5640c0d060014040041c0d00c00f601c44960f0200050100000b4107483d100341901a190100000512414074106000c01130640001040065801c0c1481000c00001e03003440400c650452615404075089011044035100c3d82d001c1c401c5420011303e5000043c4c3c424403035160080c01c10302c40f283c40065409007401c88010420f010440d04000850700310310000d4010a0554540c60240c5003458030380800c000c0c18641c00f0100d6040c0310030000840015400e0080400852003107004940365414070f003038401960303801032002c1441d038020614180407824101c4000c0458119050041d0f407000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 730401933 1250 730400683 730400687
    0x60906010518363c18010c020a02040506040515090a02090607030f020105072f1e030405030f060c2b14010911070209040212030c012a2c01 61
    0x280340021448006040b4203a00070340204001ca880b605070819031012000c900329144d040350000f00c402c0c2114400c040306000420b5245a11103400c084101c400c0e0b01c504030700c81840b5080d41d981441020060300901928009c60400740121a00130404903018001072070b1804007800c034006180c03242c40c4030b4105400810005030b0140c0c12260b4429000c0e100d5903450351542005040c080440d40c400c0f0066181000042081e03100d01d01958055080314498990040354100c58001d07503400b070000703500c1c030b004600d96002040f40300c003003c000c036000c1c0703202840d01d0324900382c20142498240c4030b6408079070b0002420000511201c1c01140c803550a8102140500e2003400344100749542d0310416803000910f0304060506100300d001d00c1c1c0741240e51100c0240141c60ba8891840304030302076144029049120a80410018a454180003c000004000701da0030100421030040c2540d00fa00d5041030100200c0f0000d00c10030025176484095564181401c614000094030083c24035286500c004020114042c00300029078 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 730403183 1250 730401933 730401979
    0xc0d05060a0815010528090e0c130f0506060304030f1b080a0914030f12030a02090a030c0807090e0d0e031606080610170c0f12040308060906010518 65
    0x400030003180c030503062605a0000c2c4400a0090303910461b19038950b850041e079100e80103c0f40c005564210080740f450010000003501c05488403100c98004d4501c413004035240d480100e604104220710204843c02c42400b158200d40000d010f40340642800c000704404240c1001007821803e11501d000c00284a000d910580301c2c9141d00001040e40200140035484c0780c3e40a0311380400c0d12211240160708031100c4c02007540d41c01c1003980088190700900b0242ea00c18813000f020355403140e01850090301c2c002124000540110351070300b088460b030045d00c10510040c9001c120703010180c14401c0d410000d82101643c40c80d80c2d44902c1219908101c1c441c0a40c0041d500c081c480c2c4845200c00100c2500340c2600c0d4800039080c0f42c012106903008041c50f00400440b14410901c0b00c40d00e1030207504480d0389484840300145580d11000c11600600001c12200003613001520340988150700a80c1c40a1850824004101c0e00b010701400c1207040003010b110039010030900c00d03603030501710b5001c5414108028117101900306030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 730404433 1250 730403183 730403189
    0x5180a060f0b03091501060c0f1e0305120a0212060f0103110d0606170402060307050310150e011b0203031903150e0106020f032a0a0f12030b090c0d05060a 68
    0x200040100000b0402c0a45014500402482080e0341c46146110242c0122070024031441001410503144500426401d10f0219506030041504d5450071000c00c50148080c0c00d000c5013180056800070b043c5040303041402c1d0007904400303418029480c1040c40c3c0b034110118080500300f03074800c80d007100d01d140d403aa0080c1c1c000508071504941c5240c4522400d52140004c200350320600d000b054404030050300d01b010300540326224640c020b01d000d00399241c584013228681c0000385108406142e0013404902c896104040601c444080c0e6110803c00b94041c00041203090501071040d0514100300c030720801039030003105036035074000d0320042100201014401200031341030300c02d20410404844140481e509081d00c504605907015502190810300b100b880c00c50f660312131038a0640801c110b45644c50b15016400c2d5540780341c8a40c540c103d40c030310491925851980241e451048854200714602060540d8042c09402c660304000c80b5104014500507943c400c40e44030b15209540729a0351440081c00135594031303600c540070b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 730405683 1250 730404433 730404449
    0x1c030f0207060617010b030303061302070219032607050d0f0512180c060a050403060902010905310905120714070807061b0201201213050a06020705180a06 68
    0x15084d600c0030300c0c000701c40c00072142c094154244900e402e00340c140001100d01171080076200350071b200030a4607584000d40107208101c0c1e118a030200341c0c0b140003400740000303005140601000427014140c800e000340300042200f400b0710310200031700c10080031640101d89407810310b9140c144450083d2030880100e440d40300d0b0f06850621080814103021503120070040f10684e0000b94030840386200d20080812495000d4502000c000030020042400050b4642c1c1004016900c10b0514100c0789441c0c130002946d08031000707580d400034540c1200c4081204040340f070031a120240da61003040b428845880b42611141c1252501100060000740401003058080c90707505d000071104241c410b11511050190341f81c9115124490000d0780e02c80c1c041c10015000c100d0001c0d650785c16128412149041d0341030366810b1b5000d090040701c038041c0c4200305501e040445d0040406088113800312110b00c0c01c000c200020346c03e03507800650855101c0503090005807128101540c5040100c00c40303c155031fa50034542806054036400c42e0311 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 730406933 1250 730405683 730405691
    0x1c06050d08040e070e0603130602071e0314040506041e05031507020c061303030c05120a031e23040501020f0a05042402060c070501180309080f1c030f020706 69
    0x144030105001d4400d80f03c4000c2d41c000992150300e81240d0100c10301e0802c540c440010000325403002005100c03510718500c5908003504040a545402c140304203016000a4991800c1c0395442c20985c0c0850020035000c02e0200e080e003040c0c18480841c610b80205d00401013595980b03c03c441c8030481c040e07000002860010222044100d003000810b03441b81d001ea070454003510501d801602640380103001d0f80c02c1c00b5442c0c40041da0062460f1011100007001000695803802034061000c1c500740b00d080180500441030320081100c0c4809074003415100c01e6400c0c02002c10345044400c46038034240c0100c00000344010803981e1425141d40c1840b600900c29590410314040780041c51104040d04800900101c6070050b106020b0241c910320310030040c034954a003000050300034800107056040007001a29050f80201b000046140c0034041140120381e5981098001c07410410b0100043d04c803c0051000c0e58403c200030b811002c05188640841040c07a00b803d45c203043d2501c00d800790f0001154169082541c200f00c0c144 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 730408183 1250 730406933 730406959
    0x9031e0f0b0106020325030507060209041d03130509090304030b071b03020601090507050a02250308040308030105041d1506010c0519022704080702040e120c0d03111c0605 75
    0x1950343d62040d1811a605003400340103d42000201b1a0380728410f0f0141c44051900107541e031742400950142810b00e500c030740d4440c810740300903608603900185a55104000d603911090301540b01d01852403540598494000c44003006001319010060740c0440703510540660241d00e1304042520120002211100d41e90307442c0b0461428980c0c00100241203c0b1415810840b40d03c64140444003841b49110100160303110b400105803c1d1840c1c1d00c1d111500c070b42c03002e0342c2003d10744a9135000300c140d000f54410384038180007000500040c902407283c401d0201035005002c580180001c0101e403204194200c1b40b902c50040c07000a429640641d0043c3c0c01203a211040d03400002815400c00000d5400700c805900400711201c4240d45000704449200110038518290002992107540b40c0712140d2004000700d8102d030300ca05005e0b454010400804030700c80030490341c01740ca48001444a40c84d105200742040304240c00c0c90010f081e0b9002040482d100b00d007681503040100303841c4501d07560240505a00103500441102504 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 730409433 1250 730408183 730408187
    0x3090603090703030f08040822090212061305060a090506011b050d08010e15040908070803070203030a0b03010b370f1d0709120309030b01030b1609031e0f0b0106 71
    0x10b0010740780710f030302c521451240e030401c200d8445404803401060082c0c1000b01413416040400d110050014032201101110313100d034507000581c0c22030501c0150540502041c0035403031902d0a00b0307101c0da100b1003104100514007000024a10001445044045a90340c00446c00691060808200c45140c0d04003000c03038010303145402c0741c2d501d80c03032103071900001c8444001144c01b88a28452a0056680c600c84501e19800403080100401c0092412250181d0401282d000100c1d1440610b220304816005561a854180c1440c0f068032000302820717220b6407414060780b6042e6252080c8140c1e0f10034005005020441040004c00a02400c4050000c541d070109000541034070516141025902c4007001c0c100030000034002c00040290582d0b2180200b41c00704d00a000c080c170b83c0c0ca55001c29a01130b10b040000990740c2c3e02c40e400d4061080c1c10955140400100b007106503845511265006030325868030354504c03480d680b85d40343c8880e1074510b88041669100b403440b00b440051100d002e00c00d6000086040c441d6941c80d40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 730410683 1250 730409433 730409443
    0x30103081903050c0307141b0c120a0503030a09080721200a1101180602060103030f0f0914031f0207020406050111101112042402040f14030309060309 66
    0x151109014141c0030901281d100c0e0148501603618041114119200e106058952001b0300c40c10303d03400c040c01c6c01054101400543d07401c80c000488400792610420364024000540c0b041d0702c00c00b106901107080c9400160001088a901406448000849c030f06c042c50f2180940c42860406482460810826410384845008031a812015a00c2c3c1e06600308417556109060410b00d42c0110641d00100ea002010030a08022000141030500d003502120081c0302c0702d0075100000341c0002c1c0040c3c1c4010010b0040642114110030f140c0d045041124011b9001c1100404000460040344c5c0c040302c0903048d20303034a82c5003046911140540b1040005451030010906070007904812001d80c0b0440c2040c0780022194001c0604120480c902805007591001e54100b040181204280c18418031500b0046207501000016140b8060b902c02d9441c640b116002c5041c1c8850050344001d1082c0541c8100070820502a90071040003c507515841d140e245030281d00c000038198000d040e0803581107100013040000c402d0b40840c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 730411933 1250 730410683 730410697
    0x25030306080c010c0203070515130311210303270f011e15060c11040c0e03060a020a05270622090606080415090c08100f02030402030a020904080d0203010308 69
    0x200315840120b048004490302c800103030303001e034041d001001c050200d414011409007510300d0140101c4c0c80e2144a60745030000508580c81a40c000343c420031090540d02e44059218a445500e0020101c40808601c2881c7c89110103420b01c24804011f90000c911014951030b941c8095200704292241038508107003030b40c0a0480c0034428074400038030074000704541100e07115010941a601c1380034044e00741032020580f0340794016541034450000c595984209955079010340c0c1c2c02c40c0352955400202c200008140f40c0703800d8002c0c05072801d0138014842007a2680c0d00ac4160b03400075481c001581d500501c4030080c0700c4007914000030a03401c200001f428102c01000300c0c40c648600300c6081000c00700307140e4568140d011a4118001c160004035100045004550452000c20301e10703025900c00102c03d0096a507400310b0340215400300e1b00301e4100140310010141e043c8610307074202403c11300135442c2d0b150170b50009456011502c0b0081c0301c0c070001c1020406002249041c1c42c66503504400441d80c03541c403030825030b8040e00201 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 730413183 1250 730411933 730411949
    0x1c0507210b13150e04060e031303030806100e0d0807060c0c021507080d0e010b0a0311030c0108090709020307020f0304030303090b090118080a0e2106010b040608010b25030306 77
    0x18551404142c8544101c502c2d94005050680316035040404140b620342d000761068401a880359014a4140c0050004081d01214510b4215403d40f0b146405031407850002d00c2c00b48a450380d0441c4401058100510360b501500850f61403000000a00d0442d529000d0303940c01600f040e18000721801b026811a40f800c03503840c0200d076001100f88000c010003460b4810000300074000c0c181444024402d02d02c0d90054200a00600700103d003160745034020407c030304a954001d4410045008030042c040c1014011544684021f01e81480b241c40c084031856558030192190840c46d507800800220414030174007204203011000d90641c0d40d141e9a0f400e000b005820000819205001e20501140380c07414144159403170440c0703454081204110726221058150000c4000b1414401585d044613404e555910b42c0b0300c3c000100c4c0c00509180c2e60182e681c0c6107030203c160001e402070803040000f48046500144064111048070003c1a07807030f00c1804050804142c4500b548e4828546401004201501030b0040410f56540d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 730414433 1250 730413183 730413199
    0x306090b010e041505070c0204050906060a15170705040e07020607080703020c0607180f0f18020a0203180a0315050f0f1317160503030f0c1c0507210b 66
    0x152001142400d010f42d4020065070b551640005103110641250741c0c04000c1d8144401c400002e9000f0a084c1ca0044076422266008002000054907250b40c10b88054419400c061003040e0500c10094900303800e45901c070075540030715000514103500c55811035024105c1001c0403200c03802e00000c00307542c4081c140d404a0108030b0400005001c144244241e440070758030340700204481d842d041e0059a0b14440ca11040b5905641078002141100444242000414420490315050352030210301c2c01100000c4a070360302441d80100501600703594000140c03a00c03122600e00384103c80503e0710004084203529131000340030740340030b491404420130309600182c803c102e24440a10303c0e41ea418010000c0f280100d0741d00c060542103292400c00f00d107807202240741c3d290214480c64681901044010812603504030100d0f981d5000100308074007200c0001d4101c0c2c100c480030f0709090411000c41c0011364007215600c02100516510300c00250b0651240450740402408108803110202c101c1c8a0388020b012084c1a2030b0044c002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 730415683 1250 730414433 730414439
    0x4060204150924090311010c061506020f01020702061e0d050705030901240b0a180b070c0602120301030204020313020d1119050901090b01140c03040e0f04050a03270306090b01 77
    0x10405043c1c1e01c007207240e0307800d00c07140d082d03580380e805410b40020030703604100302064031000091440c0f060030150f65503d07400c40000c62400e00000d02c5c001400c1c0c1c0c0d10480707074010f0008074016107400040e0fa00680300b04042c440d0b03d591515105001c3c0c052440c000030405d00305000e01808603004402140954101c0c0020f0162030354110003250300243ca0f0b031400c00d480034281d400b000414010340241c081c1001c58034150742c9484451581c5602c1120503000400414400600c43d41000780c81d1240c00b00621150010b000704851800440c0f20390b003c1440081d0042d81c000001441c0182d281010300206503005040907103984143c140400007282c21400240200d50340748418000d249034485440844400508204460303081c014408040c02c4082e01c1a4144124075041e0030b0016030301409016848900d40044d41c9441c50002c104000b19005002c41e0b49a080050a2002007000419013862080c1c05041103a05d034030b00c8260b900c40c807000c2c0a214100307041c4240c0020007003003810b40250007918040c072213210703841e62 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 730416933 1250 730415683 730415729
    0x3110123010504050f2806080c18192d050a06081902040c0905060a11010614130908040902040e100b0a02060a09080d1d250e040602041509 61
    0x12003543d4200e9070280d101e00046c03644020300d041c0504041110359140f582501071041c0000c0e12000d801041c0d07550414040c40540d42000d244c0c04200703050080056201e4200a0064039007650801c00614815846844607448072960010300d4089001b03c0b12a03515000c3c036035990500402040e10707181d0003642400000260140700103502195244002e84841d083e2650f542080001c02100c1090030600904440005031035840801501c1d45c000507468107003c200d4240d50b154210b880d40e800496030018042d07210801034a4101900b00c02c0d4640c10000030f554101800d101c4d1607406141e2002030418000600850241400410640198144031002100d03580b0340d014442c441c0502d2002100581c442000600c6440c95a000b40c18041e00901c0083c0c503021030301d0010303016518800c011001c04d84c0d140c1da10445001081001450310317240c4040700a107140703050004903c40496442800d8481c1e401c03401003400e0108070760448000384090200001e180200340f202801098040c131610402d0001c4001c0d17000f60325 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 730418183 1250 730416933 730416941
    0x106080105150d02030a02460e180706030e0c09070e15220302030f0c090a2013151b060207030203070605070201051006050408031603110123010504 65
    0x3104030044030100b24090301408014031042006aa140c4644103c0d031003d601c035146201c00398030b21100b42203419005143c03041000700d0303a4903e1307030b00c00d2088201c06601210220459410340b8a4804020007075201c043d4007910400010380c1c0b100e194040d000c40003800d243c041c1c0c4405401c0759101d0507101c03110800410000144000c41e948000b05a1810349030300103160007001d4004810348900d1060a0044404501c0250400070382410214810540d00340150318040041804007200c060091038891154800300d4401d46015254400d00ca1301d0b2401c20a0442d841c481d1403040001040300940c0f14014440800840314082c0f0959280d03820240c00345103994807500034092221409043c03510402031a07502e1070700a501201d01501180400d014040006400f4081c4078007494403a4000f0440d420f25880340680402142d04c0b5000380501004108042d040120544141945a82d00308071005079034202a218111290901c6000e9440c1590b42d04901d028004c001c80a44107400ca0010b0703e03a240c1043c08112 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 730419433 1250 730418183 730418191
    0xc150405011d1302070804210b090120210f040b0601180513090609050f0601050f130b0d05070f151b0204051008160510080f0c07080403120f020106080105 68
    0x403003400300508012403d900242550b42c481c08805280c640e0381c03414590000d01a0310401000c804060188040c040300c1e160030b0346c001e03a0f0b20008004501c126041c1600c803040d00040d481501c1d0011480382d96900702d0458030756105031601c0c41302c1030b1850404d00a1103500003c031401c40340c072088078004c07a10035403081620442c55009148686186e50400381001100d4020507605019241c4840100d03001039614003515035001d205da801002d10b41100d5030b42c0c4e401c080341600090700800d1950208100307035035800a0003158034800e5900090101280340403480020010801800d5442005400180c8178840d90281044905210f0403030386414041350b0071140d034440350740184180c0c0d00c9081518050b15141d44a5500480c0c001d480f03001c1941c1d01d10000b818900e1000308560710102c002d8040000c1c0c2441840840100c100f490a841e039880d1810301c0310074040010b0610100240e021401d0030400802608a502441e08120030440880030f080e0b000b4200152040b02500550908000044000050140c2409 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 730420683 1250 730419433 730419439
    0x6020f01050106030c02030318100915060501031806020702060c0313031119060f02280314030c032806030b01081e030901030908090405040c050a12030c0f02030c150405011d 76
    0xa0364407120240480c0b009031142c0902140107130140700d11600468032034000201e1050b000cc01d0040e20b405501d00859249174807039814141040c0003c08464001c0c0003030304441e40e20980044c0c8610306800401c0d00c45c01a414810202d100c0000e60103040d41282409004a80c400c5019412022011044c07143c6182600440c0e1041001040140066400ba00900433518803a00c111090307001c140628040c2ca01e0290540c441c4607078030b20744000505620640e01d05611540c000b0143c50340c10034001c01049440001c1910700c01941000b14149201e01240d00358070000c1000406101c0107460382440410a44203110390523040c418503131401240040600c00d41c68001c4110055030411031040700540140142c01c00444419004000204940d138461007080c1c0076601400341108054105828040402002c0c0c00c80201e004178511404000f90744001042c2c1c41e684c0c80b0008200400c22480402c1c80c288801c42016800b50510342c0c0300c0740901c586006801203803000d03a201401e00d00075070b0030455264101c460380341d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 730421933 1250 730420683 730420687
    0x8070f0c0b071e140d050301180b0d080a120906050f151e0a05040e06070e03070311040c03020712120b040b0f0f21061e0906060f06040f06020f01050106030c0203 71
    0xe00148950501c030340341c034044c00810214a014072201030a0040d03c10114000c154040b00602511101070710910a442c0c0120f820848101040000303030300315074004401040c11000180c0c40d146584a4110f6031003d0040800600141c05c891034640d01400d0111244000c200078000000c034040480c4402c508280c101030080c2907411160b00c80034003403420f0400900d410440b0400c1c00191911148038558409680318042c00740e904100c2001852004d141ca00030303100e503205080074008102008003100804000320340001d0715a204540a4029025400000c1c0280d030311802810300b400d4020740101500c0c05044010400c181e0080100030449410390078043c2c100d45c61440d07040319810a01d01882c5400c0d00140b40c07110707045541c401d05080188000d0880f100b0340001c01070112074880c800706248060080c0704444103a150513800980d44100042030b05200b10b000540700300305034030360808846c00b820420a81e00001c40d1144030180d0350303100a00e200e00361507203004000509903109100c3c0f1140b030405075000d94 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 730423183 1250 730421933 730421963
    0x280f0f050a080f0a0b0303070b1816061101110a0e10031a2209051507090e0a02210a0207031b050303060907050c0106170609010501141c08070f0c0b07 66
    0xc0208000804180049a5800e120099980c00704060081036114108540c00c618121500c41d2b41800142c1e200142540510034401d8880000054a01550320314170304000860300000d1300c5805082c030807100f0b802d41400000c4408206501096818a00b50161340e0045401d0074200200d003100ca6040080b51880e022a05031f842500e4082074454080030420b17800c0354903442e004a80c03070846484401c1100c89921201c070021a850460210940c40f4415040420f411881c1448682c0d510400034042e545841d8001050010200502808040b0a441256500c905d16080b4a039000a503c001002d40108510fa901e0321000130000b8010240268040b02450a41c1c40b1070003440030311000545200c090103c184103d101c050300034818007008180c01c03403039800c0a41800c10340d10b0900d1409044070f0820303418800113000ca1011035488800c198025262070f00029020b85032442944003241c8014107918000070b0072401d03c5820401d00c8000f502850f440810300f03660700300080c007520400c500280032503c6c0b049a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 730424433 1250 730423183 730423201
    0x3010e07021c11070306141801020901120c170c04140301090203033007050901030b0102030a080c0a180e01240f03050a020408101a0a0303050906280f0f050a08 70
    0x3101c3c0d44501030102c03041309449640d01ca003510708150014400a180d08104100c410700d03445130740350400402008510349a4000002003005030b035280c1c1e4400742c0e43c84001e810301280c0728075491600030902c180c000d0001e04102c040c0503d45da2151003540c50800d130310f1408452901d410b120300cdd00b40c030f0b600400461825804201504501c0c01c82c03041c00070600765010500010105280100d88640f20a0f900d03555a901c03c00000350480725401481411540140914098107800c1042c0f103401c0240c002c01d941d05ca0b40b84603011540100754128004038143c4000f0000390b05210440321a041e1000140d1080126840246048801c13202c00b10b400c001840303d00149400a019500450300701e400344030007601c0c00d600c4407401d0346021911030607511595520303126000346240200707442d000d80300115089181c082c40c5440c010442c0c0200f500c160301c1140300143c640c2174103140c0c1580700404509244040f103801d5068401070700b10054803002102140b044000718240ea8810800c441a424903612150403c0c2c0359000b00c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 730425683 1250 730424433 730424447
    0x90605070b090f0a0b01031a010e071d0307031b0b070b01060c0302150c09040b0a1d064209061605010906240506030105061b07180203010e07021c 64
    0xa0b58040c0c00b540142c010030700000d11040c1410303030061603150b01e60351541c40e159180e03d000815110100d488c10700103101103044096859085081450549010b1b0b10a0f01c6041d40804e000d00203913810321a0071000400c21112600b8a612619440b814001c1c0c00d6640c0500c034000e105100d07005040586c1200107005060103110401c400328020f104465841a071262508194802030340c1e003a001100c003140d0700346946850b004150702ca00e03055402c1d594251030148820181e480041511480c140c0180015850f5200e8169804903900c84107120489000c103600c600241e0082d0185000500354400240d1708620750540888550a20241006280c08000d2510b4107880400500499255403225242c40201305c940c003407800c801140100c0001d80c0c1b1007440700011003a00a60000d40584414001003209569450130b03102125568010180b80990810310542440b065800c040d4880b14680035051101c0103a81c0074505031030711070285004684508600707903a41c0c42c00000104031800350700482e4031002e00c5242c2c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 730426933 1250 730425683 730425691
    0x7020a06081005040617010b1207051005070203010207061e05060a06050a03090c08031317250306062301110606011103091f0207210b06011418090106090605070b 71
    0x10001c001c064680f800074041d10456480804e407000c00c0301049550000c02c1c4105400c4040855040d0315907103d43e01c1079070702d0390f8480c41418402e811a59860311410f02a600320b0781d8490f401002150740d01240d2401c00700400400405d800814400d907008005001d4511825000310001801c0c1da8400e0f1410ba000c483c5507000c41d410608041c0c031507101200090005038143e0141c00420061a21480845600c1512409643c406020550340c8825048011004a036400400725402ea640746400004110740440d10700f264001019030b8904007000406900c0c0050001907141e900031140304540c29030b03004603006103445040b49410303040705000c602a50302a06050160028200c00e8074100141880001c034100c0c402401c9920342c443d01807040b1641a4144004c8020341381280d402c0200c550125001d1800800c40f0000901030b514840c0415030b2680280f543c1c120180308120300075074400032124500c030303800820030b40c0c10302a110b07035800410458010491501540c9c0180d480c40d003070081607120390f184110090 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 730428183 1250 730426933 730426951
    0xe0106320f030a09151a04020d1409060106030501050906010e01030b040b04140108010e06190c02150408071101390c0303170a0b150c0c060d0902010801080307020a0608 74
    0x2011a001c1c103074000281d03100d100a0000007a4410681c203107a8401d902e41d80d0004d0741c6604e0319541c41d0514200e221104101d090680d0300513200c50520600d1002800708107541a0000001002c10000c0380001400b14145c4290759000d00484c0d03600c00502c0000d02c3c040d2009070224504180c02c4059511070352214003201c5d40184046410b45103000820200c0304c0101d04e100140070403500600c11010240164882000c280000f0403142c50011200780100300814003a805407516038400160061081006042d1030300580f10015040c00d041c6440022540b00340c000700e07a4403112030b5114a80751300403186810142c0130342c40b82d6200c1030504072101c034044201c03080c080720100746014501c01144032030368000041d41c0301c0d49400012528014030340845200041c0402162800d007040701c001c42c0c0b11045c0b05508141ca0762401600d82d0b160640c41410803c0d08003840e038000c0404555582280c205400c03001c0480d0003038a0301000e598980c91555140e200c2d40c3e002940020800ca0100030f080c0c030034208258411014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 730429433 1250 730428183 730428187
    0xc070308130c0f060210090809012f07030302240105150c01021308101a06130306050a0522110621040318080303040b0c03060d12021e0a030206011703040803070c0e010632 75
    0x100c85038103003094bc0700c2c5174501e4585c0030403030070700405030100040c900c000c40325012032101c000010115203103001c1c1400380034007907010744030741191700c0b400d45064840c503c082400943d254035200202010014151142d00440d1081c8840c1401e0040d403841009545134488101e0090845610b080c08190b907c2820040756200601100001142c41c0e4031a140c0101d200303400200d440e0419064418141c0c013480703100d1017004080080000003440740c1d00d11500100c02a1410380c1c0320f84d23440c9500e8150000d0405084502401d0768100002c2650040d80e9000104140100160407a01c4080141d5240000c850041490807000045001419120007659002d20020308129503c50a6940c00c0030000e00f4038850307c01351780091840c1204036001c0e1008410380c4080d0000342564586074a00a540744010300c14400304180703004001c269500300344100e03806084071500f01c81d5a0100c1d0300e04010f05407007601c82c11880440000000c40c615110391490002c05186241c0300200664195105550f408800c003622950402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 730430683 1250 730429433 730429487
    0x11d010e240d0f0f020906030f0a0b042a030c29180310020d2304020915190806010e090304060807090e0a020717030c070308130c0f06021009080901 65
    0x143c58001d2074544580c181d40200100d03031040c402007403400742025102e50009e6501580c82070002031000c01058105c10103030082c0d1542e00745407032110034004003580c4811443c040e4104148884a1402c101c0e8480e690f00550b480d0769012000010b0328400e4141004074007507584413138426984c000342413900f100c030141005248074140080d29003206148c1c620201600400d401072000000d10403002d80d800240100c119141d811342c0d05038511140284028803895a41010645c0304c10460940c26480502402e401800700365103018040b1104144104a800e03c202c400105901008002580c01110000d0041d800c140c03d04600707454100b8028048000c0196030040044c1c0d204200e0010390103030045c4d070710050740da64490610211000c900040d02d14003a07010002d09c00456200403c64003c581c052400032181d0302d404004040c070214225001d00000650703a80407400340e180381c481400b1100b45400b2509039200d940c0c0c04c40c0542d24055009014110188010402540900310b032102460520080da41d580d61 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 730431933 1250 730430683 730430693
    0xf0601080c121204062c0f2107091d0c010c030f02031e04080105090d0504050f03010608010c020d110a0803070e010e03010e0f10110301060323011d010e240d 69
    0x130a070b11010000d504400341c1101d502901151407420651246d103a4900c09007040441e80502412100e140115038050803a000d50000400c0040814891020307901d01c9036480028401034854861060149804801c0d039011000c40000c4560054030103840381044400c1c42d85003543c20107210308201c0c003507001c00c20044402c1c401514210b03130300d10303001d04005845a003040d0aa80c00c60304000c000c41d000c0d901000111482c40c0d085001e4034210b81c01241c107102640903500209001d003145038003500d942e60a19816141c02c0c0d8001c100c1c2c0b100c81e20903a68010038051181d000b0b5940d41c0940201a01030360081010601703040c424403030b0072289001810b1007500c0000040202c0e00b110740019a8a61540103103c01940380c20301805503c0050005c008144025070705900100d00502c01071040300203040c2c0d26505100b000c0c00c800840840f404031808108242e40c0d40b41034885005c071040140b0032401950780e001280c500c0d003201c0360340e02075500502d503924040c05800500c1000313a40c00080d150720205513428840011 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 730433183 1250 730431933 730431937
    0x31410060609092d020913050c0c150c0a0c0611160501150602070504020a021e03030a050a051303083c150105030a0c0e040c110f0601080c1212 63
    0x80495680c0b0315107a89444200000c4401d924120580e080202c6900c44158100b90200461140c0c20400160744003132401c000303024248120b0810800909001c10850301e05588800360881c01096810358040ea20442000144690122500120548184a900046031180706032010903486240009120403810070307074080c2900302180e102100d951002403d41002000c0c0118400030b008071100101040c18140040e40f1043c00e4003416018590104407644518420000c8480e01e1150740d018215111000e0203054903030340110b400e41e0b680760801c000714414540a10516114801110314510019100d540403204084042c110300218285d4450700841c020f140046001c28004000715091a0841041101103c1e40020905107210404c65000092070740c11100700c980c480507044000070311002400c1c0c01d944c460440c1c070032107030003603d030a03076000440d5040b443d18000c8001e5401140e8514036440006903440d0b4003405000070360340040c0320400c0c207400c010b0b20240000300003400703480000050100d510026 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 730434433 1250 730433183 730433189
    0x1603030c08270406240804050c090705071e1a2e030201030516020d1407060906050108011a0a050616210f0c0503040515090a0602070914090703141006 66
    0x6210140120000c03031030a8440e4034005c0440c612294803405800b144030005aa11869071428088030310001810000148500c05100c00000c0540701d960400b0071000b08643c2218004032280c480b114042094400600040300c0e05aa00c10700400c44801000d4444614444c09843c01003051107a5040741a034040401e080c110403401561340b01d00c01d03403440c000102a6040a01420b846906030000b2205d0180c3c003054160f050916170600c2400c4001400e0b818110f8850080080d00f90751070040c2c49420402c103604800d0403110043c000f8886003044502442021070307984101c03070303000220031020031160500d00054603466a20268941c070038495926001200043c400b0300322544584e0400e81281140c12680020300f0541500e030180d20b901c00340e0f1307803d5524815802594842c24041600310821507040c0200c0b90381040240409416540d1010065500d00c903078010156150300344080b4000d0a0a84e41d452417184e1100c6000b808105d00d5030b100c811100c0000d0b80007068502134140c4c0011140c240e40540001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 730435683 1250 730434433 730434487
    0x15050c0a0b10090204081504050703050a0c06031127040906090b0708160e0d020d1415060d0f02090a110f090319051b01110111071101021603030c08 65
    0x103920300a404114100b0103a00b080d41c101d8814441406800f000203a600c011001480030108951901d04003d440d040280e1b00042c094896034440030304010144040404489450700c043c41030301082035002c0d1450003041a560700303150081c0d03a268080c1081c08145214504080c000103100070716501e8010681c0c2440d0710a4031804111001d01081590140d105a44540c2100d241c20000c0356a000050480712003000052080e0890400c103820340d9207400c0c0c80c000990740080e881d94508c1d4113005254a50340c0c4603a5140d2090321080000c0d4140c200342c2002510580d10210b41e0001c4c4502d5404c0080c1d0b030302c000d8031104400340c0e80d005103001520300748020500c180000350155180e0340c60a04040c80d005d900504504007001500c100070000d4400030784501c4107501400045115040d50004a900e01660055002151b0030305281714031201803d8010300c0c2e403074069034100000e400094010790341e0f0840d02c0d00030a552840800b0400c00b181c845c8240e42d04a030701c03c080355480c00c101c3c000220b400e4418504c1740f0171 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 730436933 1250 730435683 730435703
    0xc010c2604140109031a0603012910021627020f0c0709090b01050d0203120414090f0717041109072001060602030306010c03030f1109030f0309060415050c0a 69
    0x41c8105030300b030300c55a0080074039280c607025046603070388040055058a15a242929407010820580c3c007900502030384000f2070280c2540c210381a1078500340806081c800c500503141c05000d149128400700320a440e4010043d0a0b20700c041c0303000714004400ea211040c0460942000074140c082051a0000b404603408000ca1f03207842c0c81c0707550440b41c10070740207034810004c1c0b030302e0b00c0b00b00c0c00001d0142052504644c000c0702c1d0f040303490401f800400d0030600c500f00e00e01c40b0440005070120340c3d010115503900f051401525100740d16980c03c0b00354440750105507914804519601c2004800c08441820f156006102c0c5040303041c00c0401ca004545843da0070358a00020a22901e40d0700702107034256a400d10321224400080c03020a2a100c00a900c0b4480a81050704008148802801349070084c0c00840913a200c0c41c40030011000014102041c0b0382003071761054442d0140390f070800d504500c0007007650b4620360001c00052510345080c81240b100c4441c6440c400c1405411302c41d807980f0718820310012240c03a000c0ca40802c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 730438183 1250 730436933 730436939
    0x10905060409090c080c2b0c150e030307050a140f0604030e09060102010c0f082e0e0f042111100f1518090c03050d02010207230c010c2604 61
    0x40c1218107400c90a100e1b07220310fa20f65500e5903104580404110032440200e4810b0010710101410300b01004003500039100941d00041d030408011015243e0080383d40c44008800380f25040640782d1189a0014002d5070007159501d000c40d820350350907a100409881100c00ad504041075160400504803000d402050014041c0445130414082072980104248001c10000260100203080c6050803000c140801c40c4a200040c0d0aa803c04404d0302808600540151214100e545050607001103000790010700390050701080c0c1701800c2212590040741d03c0100e620b01c14014480d046c0e40f55001075503803020030120380741490326640e00740b0444090a00508006c6041000301c85048107a6620804c1d1a5008650356410014000b000f840030406c80fa200001090741051420403040e000c81540020f4a107006040071300780300c80e030150b004211185c403861601c8448030208840141c180d03040c544490f01c5070440740360090158480c0d101b0482d054851080c008405070f54030320103011543c81003145c0b800c1c004001414 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 730439433 1250 730438183 730438193
    0x902030f01050703050711030d050c04050a08011512021c0302010213030b04020a06020d021b060909010b04030c080304050f011b0506010612050c040f050112060b070309030b070309050c060901090506040909 90
    0x103a903100100313003800303447c00600d813459035035034821407480140c1a030703481010881e9491200211401040700802c1094405e8440d080750303000f001161105185000c90001c0001d0b01c5003951540310815400910411851041015065025900003000c80855600b005120040c110049042010f9402403103480c42500c0c252042c0409850160004800d41d400720038048451a0300160b0850043c8081c1c4001344502010800310300d250040e40019944100182c0020411692038005030040b02d003d03113115000c850f0756116060b100d2080b4011143c110b80b48043e120b0155010b4600d004161402d9001c14094a0711500d6031810243c0c207811010014141441c452141c003054050076030004002440e0b14500362a041d48080500c44070f1007014180b00d0030000340000c20f0300560003a0000d010300798503550745115500d0000c11003146400100c40807484580845e07a164880d00c20319800a5118004010850410382084031359003004400d14108408000045002e0315010080e000500300340402103039040f181d00d48 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 730440683 1250 730439433 730439441
    0x603180c120375061409060c040302130513060f06050111010b2b1406060a08010515011817010e06161e090503010e070602010c031a130902030f01050703 67
    0x904010780d030f128844038040304030348210110010300380300b02801d0704914002607055000248401510140c40c0c503540004400f0a03103001885601001c007030f10510b5544c0c00c125812801a800041c0d0440d5419991a4107608103512058020021214400140c600ea0399880240e403039504500341c48540724078080107a0750b002040800080700c990000d000100e5400041048003110b500c03058032004039028050ba1034514411006a00c40c1c0100b1102c500b5281404c04941c1c5040c181c0c1c070f2600892202800041405061140601a0034101c2c3c01c41e8201ea1480011910300c00040032061200c90030040004e0014042030007c00c4010310103002140d2070390403e03c85400e140000b0502e200808001000943d4070f86d210030318800001c070000707850b090080301c1c540c103c2d074100ca5a000740340c2541c0781c030a411041d944002010812521958024040c1c00d035181c4e0b0440550750755662100400620221a50051914881c0524180070420000a000805070002807810f20b0500e400c0c01303c0c0c0d544a00740103003642c1c1070107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 730441933 1250 730440683 730440797
    0x20a0e0102100212040807170a03060515040602030d110408030c1b060702030316030e090f040c060e21031908180c220e160603180c1203 60
    0x21418601d0791904d0380140c00c0000c00080400d8400528001008a809075140c00b0003c3d40c081c1989031001d000002e00140190f009803403040340212071400100e5030503000c44064942a034041e50908045c03c0c4c803400544100c00100d19041d40602c408641480104041c0414101c000001c00183c0c1c82e000c00c1d58020400c0000050051008210b1440503860020485041880d10032803140d0401c80c1d8241100ca0340c000c420348981c800d001e00188018001e0f9000750030f0286004480180203113542e007030140c50300c81d0000082a0030007074040d04409904030442c0d1a0741c400c1980030a5900d000b06050785441d400080043d5500885c0b807040a00c039440550030045070217251020002d040b080e0003080002d2003100205008000044090301030620506a90800d01030000c40100300c55070341c0f042001500545882d40141000280740203a14800c072529081800c01c80c94119050800541c1040504140100300400603814031185070300035031110a170340c1a42103045054520081c2e031056810341d000407401201c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 730443183 1250 730441933 730441963
    0x10c02030a091d061908010204090c020616080c0f0d0510170708070909051c02031c06120807170706020901030e0c0915030c03010e06090106050102190b0a0f020a0e0102 74
    0x200c0080c4020408040213904004100d440034122000034030b50b411500c0f9242c0010299500200e400118207620340c116080c0110581c003030301c905d079039102c214003d003030700d80030354003000440c44400b11b00b517508203a00030020070024149580c130b0b01108008581c140c55050f100813904c5000740504001c100407500c0c000060005500141c44c01e41c2c49e0882e4507030381e02002e0040b20580303075035031080c1010402c3c104203041448011945489200e00c42c0351002c1c2d1a41c002c000e19480059600e0340c40e001a42440c8201c600780c0362100b0780440e5400c03503500d4582e0385401209040f901c1c00d41502c612101c2c0183c000c0580500c40c40f03900003503030364404070b0001004d4810f402c0542070660b00140c1246495991848140c0d80807260025104640c0f581c0380020780780036404410250036500e00121811400d401103605413085036048024051540d0b603400482c1c2d65035a583d244a0309030308884220700001e000c03000701c6030040359401000c03c00307401c048503400890303200c4021040071881101c03040300305580600204280d0000380d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 730444433 1250 730443183 730443209
    0x607080906070926010f0b0a080a0515041a0f2401020303180102090d0803041e03052203080f0c0607030b0a1208120103080403170901051812010c02030a09 68
    0x20000e404481c1030300500da50004c031803c400300c8201c00a4180c0c02c01d01c920304024000329000007a444003c0c00e1080a480c02203004990100e071846000644098203035000d40200240c1c0440c2c130503500c0d0880c0182088820100041d14840c44090f4450564015001241d55050604024240c4005005210305110080302e0512036601c00303030b8020045d0303a84940c088050301c031141d800b900403a009104050000b030340440001c1c046070600880101442c440d40c8540c250400c2e0011030440c9a03800f91000d0001000034004100c1e006a00c28420b00002ca81ba01050310440150f0b1079950f600465000944c8a00b41d600c0c000c078021681000c00c112040e008041800c0802001d6404004100801d400b4000c402c4100c40b40100401009041011510b400310741505181080d6103a181030311413076100e4030050385e4404000200780d80400a1030304845121070161a4945813401a08015007000d100c2c4040c6e6034000e0540807440c14454003801120310007440743c4e01a40d6910084440a000000307540c200c0f071020050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 730445683 1250 730444433 730444441
    0x110c0c010306050a0e09010e030310050f040e072c0109020703180602060115140712140901050313060e06070306091503050706030e0f030406050301050a0e0f0103140a02120607080906 80
    0x11184641309030b0f265003c110754075a840c1000640908054001050f00b0700c0b00000300a0003c02c80e61080b420356100301c0c1c0600d510403003001008140c8044c0f820342189a007103103d081050800f001741c000c55030400301207007520308440001c1007040c00809a01140b5900c0e000030b1baa0042550100e12910340d80423030700a40303010781d007070290082d922401401400700e60b4840231040100c40340184c560003107040790407070740030b607603e00524200006100f400c1100d000708540f409400b08540c40101601c2541c003041e0348a9096584040305031528248540307081d10803030b0352018412007e03a400d20200e40b03d05481c0e02d000c43c00e80d181040b100119490900801d40c620741030401440040c002141010840c3c0440c036000c180144001d180c241061480441c1c80224440020002200ea8000002d58122078040303514002c01940d506102004150032981003000f44038500060000070000d0b00601e904c04100c004403050345810761301281811260782000843c60707110301d0030004204d6025403030381e40c000034500c0a01001d081c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 730446933 1250 730445683 730445689
    0x507020a0909050c45010f0608061e0d0b04120309050a1b0e100f060504081005040305040b040f03060b040c1e020a0b010b0910140a050d02040306110c0c01030605 71
    0x185072000500c0b51281c48016500900d0700440f4003410743e142c5404090030114441d4501280e840102d41c070301501c5512000207003038200b00707d0a008440c4980c8943c00203564503010000c00407240511001440c0c203044031560540c036003099054003948214441003040c207160404400004186140d4010981401c400c03a001039000b04210003400d0340200b07101c03103104030500d40d80301000c0c10341c020341c61052004d420060440030594490044030045c000c00c40000303032035034400c69051041e8022448203510001c1e207224400519171146c0e034894001e00d0280d081c079882e8142008036174030507440240c034440c0c0081e050090044901c5104099031048604008884502038081c05103000118804942c90064102c0e1380218000d00040d8080c0342d000c2c0c0301e41190368650030315904039001980001d01802054100e1000e941c096140300f0f099a040c896051709019000000f100c095002c145803070113140c0c080c0800000286a4003400742940203000c10300340c542072049142450005640c151038101400d2450401c0386403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 730448183 1250 730446933 730446943
    0x4020f0a050a09021c0203040807150507210b0310020405010e04090b011a1c0f1805060a0b0621010302030d0306150f170403020f0c040501180c021c0507020a090905 72
    0x4a50000158607880e080c0e0b40c2185407100511714a90f480d00000c1088100940780c030080c400548a1000c4050144201c680b417800ca87c021122030b404a11512075200b101700104da494002c030182c030710020848440c004007003410241c0061001c01c20380c1e00444c0a03c801e681003100c2da0700e503000544003040041a591600c02c036446062040304e044058901207130400c82d0b850802c403245a94001414030040b0110314809008203442c1c0442c000e047d24003034003c42c2d100022088000700343d81000c01007c5a86a40c03110308001c00c64012600d83c050020041103183e44255101c40c1089880c0385c841c00040c1d803460042c1801c1c49800ba05440401d46003039001e00080e4409082c1010041140c83e01060340801584141d07100c0f00a440e248401601c24010882019400151045c980c542da100b5107071040103000070300040d1032082c000c00180c81c034000500d0920641e550300664034290184100c070085241c940d50500d038461541c48860024400140c14400d6040c1030700060002c101a0f80100800c3c4082e4481d0358460b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 730449433 1250 730448183 730448189
    0xc0307030e03070b0406051b0c0f0f0a0305061003060e120a1209020402070606030c1a0d0b210c01020c100c0611130f0e060405010302010c03080402060d050c0304020f0a050a 76
    0x700521951a0903103403010000440508107141e00780b642c03a0b44403e0090a2170f0000c00d451410094171181145101d4800314014841410240180b005844a80c003048401c10600001c0f41e00446000750001c0460700c1041510700a901c0074003444105070450500d40199908c0080250552748030b00c070300541c80d1201c1000c40b094a8030910b85448152408130000001e0454110069803060022402206024441d80801c003100d02c2860214010f90781c4581c4c0c9400380062000d4801d0b400d4040c042900c80040740d40007010174001c000d01d0008a0008111202c901c00b0081c56001d602e6031210003c2851560100045c07d82c50000700da900100383c0130440020200600800018034003a100c8004402c031040d4982503460b4014428503842d45030361507100c1c604a1038824401d078000501e1000103c1c8150605104503810380b42c042e51802e80c0745032181c9090320b072038202400c100d0b000348040195007054a111b114090142082440807662424107004100307581c0e14003078482d40300b0702024408200568581c0410303022 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 730450683 1250 730449433 730449437
    0x40201020a030309030203090a06021f2018030a0c08070e042001090801020408030c06100b160819090303022b0c0f05030f031b0f0a05030612070f0603110c030703 71
    0xc4c84461a04a06502409800e140c201720103500200e40160081134030300301502c0c41030340e40003124040341140c0e01740c410f038601d0011070241103450009900c1f184d800900c0b8042100d010000c108074081d000c0391a00004540c02c0d113901050a00030320a034441444400014200c00a22121500702a191141e10f858401240c440d0761588240b54400b50340142406c00c0104244c0000310344807035444c01c1035526544482810022402030500059201e09a588941c003510301174466641403011226000003012000501610020803c3c00104110444601480e43c82d0b48240e07640c501e214507515020341303400c246003030071145202c1c104032000001440603500030124082d4038050311520f0480c18000310308503920348041d0490000080c42c1aa940e0440021406040581e43d80d9864000c1c603400801d0f10701a41c0c03120f07029004204080d4114510400c007840d0809001044a224240d00c07079803a9240c24500c0c1e0201110001c502c000300200303a018800c01094019071a00c031440c00501c600b5454a03445001c0000382 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 730451933 1250 730450683 730450691
    0x403050c04021b0d0503010819050a02040506010c140a02120307030f1b080f030709050a0b0d02072108061219080c01091407051c260c240a05040201020a0303 69
    0x80450490010070f80060300b03d4155032483d070003240f0040c10380d8424003030100c941c400c0c0300030b550422084001074000c2c40e03049006064601000e038200b001405015001c1c0e810401020007000204805540c0c01e89038042c0074008061449085c0305210380c242510b240c1c4010394006102000209400c080e11411000e21840c0184150b644445a6451403076400d201400c2c070203000c6001070a6040100c002c500812550700e54110241d51441004010748040c000c050341c691040c000c0c8101c0d0746068000d031285510454400c4c032a126251180040d007158150b401c0c0000b0307500700a21a44d4149142c907060150000c0b405007204c020683c0301e00180c41c0068600400c1283c00041c00e0100800030360009030f000b0b50100d624452180348114181e0b80300e0050081c50f02c84c0500d070900054003410b6021880c00782d54400310b61851420300001102c2c032030380c882c4101200320808000510b02450300384104410107200030304030200419903a0806050300002020780b5404d9203001c0a01c00503070f030001342400c0410303410300c0c0100e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 730453183 1250 730451933 730451947
    0xe0610050c0f2103090a12020c100c1104020f09010c050a050d02060106080901060311060304170a090603050a0528180b0603011b0906110304120b0103170403050c0402 73
    0x25024412a01489224040d07104142c030300d80c00100784100500007807030840558201540030390443e44410384010b40b140e8402d1075101c0004811003120041003a00f40103a070400e0f40c4020100740340b0a500144000002c0d64a030704c007030411090320380c8089507540c2602c046081603165400028107200305040396050240368079545040110400c8112016980001505d20b5041c24800c065502c407000c0c0921004612080001030010034148296003c603908050b4501c852820f02c000c1c00305591000c1c209540480c488400e1078400d10303211000784541c03121a80d5aa00051030f1031030040440b0b80251202503a02d06020034840035000070f030030448031010380f050ba015003030201c1038031030004284450068009a0a50039980240644540031510910080e0024031600500040705450f0540c212111001724000210034010343d4401d40301c450400502c0c4048a01c1c0503141c08010f41c0302e1006020844580b0114030040c0200503a84a0a08041610103642d030300b01800c5a842079101c4e01d08250050155a0128002e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 730454433 1250 730453183 730453187
    0x20102120f13031a07020c030a2901140319050a030305100f030b01240206040b06010201090501021c110f09060d11030a0504030e01020d0503010509101e030501050705040e0610 77
    0xc840500b18002d841660350340d2850020b00c820f134088071840d59100ca250000702018000706e06d03040e030010000c0c040c0c850058542d507105451031260200b202039641032001e000c0c01201108200703018011030780e4030b80c0000a0034000c0503d400028100c6143c06500800313035400203a0006500354109905007404a119520510039448107482030740b0805075142c0200d40001440b41d065803550594142501284100241d515020074402080c0000d50060380048005400300f04016055038200c10144000f188501164941900303a07000001c1000085500442c410191031452080e404480030300c20f0340c5410507981313824982007405441c50b01c5025250002e000c4080c18001e5101c8010a42c4e0445042d44906100701c0c1840144400c48040300030511301d1841110542c0002041206200155100c1303141d81e01704028011207440242ca03c3c002c10b5010722020806d81c1003a45600d126116440303802440b0b80c40e60820702c0c2541d00c0580464140603003000140310660501403019800b5809a5869407032000713101301 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 730455683 1250 730454433 730454437
    0xc02090f071404060e0a06030b1e271005010c0c06030902040b0907170c03010b0403110418030c0c0b030c09011d040c0918050f1914010b0403120c020102120f 69
    0x1002c0b40240c00028089109900154170540070b500c182e130400e0545448003000e8045400d50444140e000182c00c42c070003840320320748044286c2d80801400c4140142404042050004004004040315800d0403040260105810070448001c0c0004d02e070400c007201d015120312a030003559009207000c06886512950a5440c1ca0300401500d58014040840c1881c0401b40200707103214001c002031404400d10081540480c40b1010349060b291900485450540f5607501c1203841da550303001003a08207840c0ca050503081400b401a010441b030283d01d41c01c0c001d4a01c3e1802e1001c010442c0c1044410b021b0070b01c14000b0684118040e0b548c3e4a80c2801d05800e104c1c60300200b00580c2007e500e94030303802800d288404002c035a1116920f0308036540d030425031280640741160041526000c54031003d48030314040019000d00b0544080b412400852071f00003803004a036404e190721080d0244c0180728401c0000800700b04201c03404121841c0c90042c2d140103500c440703182c2c0c0004e48034140d82440d10b00030140890501c0c0c0102c01001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 730456933 1250 730455683 730455707
    0x20a0917070b030c090118060806062203080301060f0927150801020a0e1c03030b0d05030a030209010f081006081b030405010b0906030601061e09050904050f0d0c02090f07 75
    0x203600c0e0712864803041380003056022204480c0011031060f005407e0b880510341c04d40c150354140d01d4050155071a001071004a41001c200c05012040c01004155114070b84400b44000d035008501096883d814804042c0c010b0055041c81303020040c091104101d0349188205105405091103400c1080d1403a0100c0c003030203024405805500d0002c4a030b40018401e1055004010f240a56110070300c150a50808020341100051201e0081d0400d144500300000d00c0707a030100b0581c50740101038009000b140d031201491a0030111708900400d500060003c520368110f8ad07403000030b440720300e00300c50700b46030140c45141042d00c68803c090903c20b800d40801d0040a00c0c50903c5681006414071035203914003418068081d1450040b50303406085e519001c00c0d0303182400305250381a50b2944e2200701c0114a100c0010070280c4006440d0030030000c4a40001c1425a5a86e070401e0180c0d010f40004c2000d07440f010041400c0003c14030350305040c40140c80c49000182c8400d902e059018482031202c002c141d9038128181c42400f40d01d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 730458183 1250 730456933 730456949
    0x40e0411041802033c1e070e01120807150204081b0a0b03090717070f090b120705010e0603060a05090403050706050c0307050d021c0509071404020a091707 68
    0x15030410606070b20b06a5401024021000c4402040c680d144c2e41000e05901c1e00361032483d0b00280d4142c0e42d01460042c00006210001d000c80300038402005901c0090aa000c042c00309641000000b0480c031030350502c45c00d01400013002c030901443c0d82c80e65003206a03c11100b00900d8080504514026001980d05640080400c2c10503074600c21207090007980c001c0c21101e0b030581704410300180412101c282ca07050300e208114a40c01858060300300510100380031243c54240c1c00c3c42c8030b04400813a60448507880f110041411301404602e04041c24204500d4040d1282c100b010360340601c6042000342c0e48258001218403081d55941c1e070702e407129000301e000c0c0d1215400c51358104081d9000d010401d0b52000080040714020f580800454a48240000036403105a0710303540080c60600c100020300c072035603004140500da044514102c0002155040051300e40480351040c0c10303008220f0410405000c6001d11031007003002c580443c94244281b00240c800012030054150701a451414220450710800400000e8103d070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 730459433 1250 730458183 730458191
    0x5071713020d32030702030d050c010f1e0b0306040c0b0d020c07150f0f08010303210501031211121e0c100507110a032313080106030b0601050c03040e041104 69
    0xf1000780c941d03140011003502052540c100028840040195038215074014003411080314803003030880c2c0a0b007003c4900c144556035041482c1e2350307000c4c44c81040121000010689003200e00682c17807000301c039620804103000e82c0002040100203080c0000203003da460701d005e103079191004400e041c8000d005001c08140707680b1400324003159a01302c012010030303000d4076a42c4065050008078000c582034031001600001069840c1c1c014000a030007050080c032001020700c883e07003e071440c03c0408802d42e40c0a90050380d07050f020f13070380d003c0301326612241081c031540201004101100c5c05003094891341c40340106030b90304c0040825071414110100002c413900e00d40500308a81c0345907015a031b0b010003080103072080408242c020a4003404201d0200301d84050540540789d004048550038101c81c0d080c41c2c20028100710300c0007040b00b4034030340c9940c0c0c02c000c0c064660301000250f16411442d11941d11071001d4003c5041c08003c0c8162aa29100001200d06851404030500c031152924038021541c50701d0703050020351040c24 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 730460683 1250 730459433 730459463
    0xe0111041406070506062b03080117150a0b040e03040e01090f060305030a0c1103031b01050f160e01050f12070f080c0409090c0509041505071713020d 66
    0x59000580305850540d4502990281503400700720075880340c40c900070215005000016407501d0700b451303809400449042c4da42c510304240700aa0741d0b640c0010303804070007040241c0c00603c050509101c0c498001c4103604024203181c0d940001010701013400500c40900207880304081691512103410039041000400d080340d440302e813a00c51105040100f40a40c1c03103200d1418000c3c000e18010340c0960003c0703035080341c00b4510745402411b041786c00381a000b109803424824070604c24a5a102000142800940d061031426030b480f00c0e003092401d455026090451481c0c121040c08007001c2a0b504100245000d4100300c14103003000001601d642c05031140c580000e100c0412011044242c20070311901c41c1ca000c0ea41d902040e07a89000585001e142035500f9403018409201c1400b54420940c00340500c94040d0040d4a1403d94480c00200013100482c2e084075005002d010004580c000e80c0116034001d00d407800c201303030400115102c41c000e5209c0146014012100e00c9402001c0d0b4480750f12111a058012006402d9030784 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 730461933 1250 730460683 730460711
    0x524030703061b02160609050d06061a18240d0e16140a0b09100e03060c0705160605071e0f0303063f0311030d2003040b01180e01 57
    0x10f12600c800c05401071a1914062801c0e4042d401c042da43da0391030384540c080c101030a200c41d0111400040752400d03680c0e0350104840ca5100220751039508164802c41c5d0f0b4040070801c81d0000c0c800c846502e03004400c14000003144040c0d0300132a048081d4010b0071142c58804451014000d4220303000c00104c64007482d48001c4030b5181d10307103d09058a02d05052100554120420300c03184031030910480d43c15000900c055035540c42d244c50041620850391400d1021000c8000c00a410030b1010382c1d041441500000d0664200001801240d0054101855090007140b803d0400fa1036032190800c028203102c02c81401400d01c1102114001c0c40b80c1d04168440d8000c0180c3c60090000d08440c020540012806840120326400030b038110021900030503801042c8a568514080c614000320101320305104009171000c0500b10104040e003150010484003061260042c251410780100b46400340900c005c3c10400c00020525a00200d030468850440e0f00003444040b0501000074081c1c10303c05a21542410f440345100c007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 730463183 1250 730461933 730461971
    0xb071e230a0204061e170f1b0a06080c03061309050a030c03080a060503033c0301050405220b09030f04060e190509010e0a0b041419052403070306 64
    0x42c03098504110b4903440e48204101c82900080101000038004820700c461041114080c2d02c15202d9803c4501070344122115a0524000341c090010007401c001418501d8a001c03840305c8020700ea02d0038000258200284004141d1100901d02d9006071001c0c048a6045030b030580c454a52180c2207020b0b185408030505d402030044c0b034803020540c00562400301140c840041031003180210341303000f0000e619110140882d141c1000c003a026080d910380110b18817210f40c40b054884400d0300002550360a94a604002c100800c80d500039106100028205000c9410500c000e40101c00c001d8000d88c0800c0e00d9504c580210f880c0d4441d49038010f07040400414001040c40d000199a440c51000700d818100701903010b00750050310360341032040c80e5022005200406c1601c0c02081c6958005001241c08960b8a04610224003500c02e0210208002100981041115422a20380b6215107100d00c4041c0180c0c1041d031a444442002141000201180094030ba1a1030781c04000140003164001e50902a01ca00e520304c480c404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 730464433 1250 730463183 730463203
    0x1b09020a09140a090f06051f030e0307020604171c05070c120807080a020f0304030b060906041b030b0d0203010c080403080106030509060a05130515100b071e23 70
    0x12901d06030000c0744030311a01030000c046500240a1605007468851558054003154180460440d503422021819485511381443c0d8072180345104c00341e1498a40005040301d00800741e844840c0c0040c403038040165645030480d0215002d01400202c001d0804041c0b5042c808a0740e10000d440c0500035402000c0c5070070601520410f07000700c1004000c01d40c2c9040000d0940d426010041c00343d0230030410180003401c42d40107009080061303c12a900c0380c00e4403107201d1840e030003504190740c0030482c51304000840c9040e000465200c9016a002c0c046002203507107010500403811403000605441d0241d4080c03a0f191100c1d4090901d8008000780140007a03a480030384050f0f02994160700054604c800420401c0c024001d41d8040c0c0081d00080c5899680e590f01c180052501505400d0076a2500d9110000300c0e10070084080030596080c150352090600b580304195410242d8006c080e038200c2401314502107074020002c40c20700300303680c26050210040751401240c140303450000460f540000001002c1d4000e8006400c48803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 730465683 1250 730464433 730464437
    0x30d0606031e02160b07300b0616170f0f070c060c031e051b0105061f080a02090121050103050c060403020f0d14030a0503060a15050f071b09020a 64
    0x749011010041640304c1c04121060f0048000019000a400c030b1340c49981c403c5d40d614004105821200322007042d001c0108142d40198038401c41c81d65070380800d205040080404689c15454000b4405032103043d4507004001800c0740c0c615015900c0c0f1000440221a40c40641c10902c503034500c04032604071070b95045503006840102c0003c00c0460150b0003020f014024507095181e8101d03c8403012040008141207070150310402a06010310070502588020078050316090b20b0003c90585004c03810f00200b05088181c403c540e40c600a448907050382c014800581243c84814050799440c100801604c0714482c00c401000200e407992089a42d4012550103941600c0c0b007001950546450341c800c00c000d500950102a6103c20720349c0b04914245010812000c0552199a07520484000d2a48040c15600a51a0000800e00000420800f0324145e900c0c103016280c0203091007030202100360000c055000344100d11002c000700007542c2c01030168100324240c10710b4403200000c2035103031118040400b0790024106400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 730466933 1250 730465683 730465721
    0x190b060a03030f0c15150e0703140a0f020d05070c02010f050f07060e0a020a081606050306060a052209240305031c0609050a060501030b0904150209011e0207031506060804030c05030d060603 83
    0x10f03103235200c0d0140040d060750640d200c0c041911110041d100a00c503d00601c64080d40c200012088480765000e0944038800503182c520002c01c0600000d8003030b18081e204601001002c000d000d400c01040011f403820f03242c003c600015440003001d0024038140d60f40d8000b9611070000d120008424000080d030000c9842e410b5120308003540d5881041e10030780019643e00d80d019105011004119100d0009070402c0710441050841682a598221144804039002504d0302502d03200d0604c0b00d00000d840302c900f00c030341c00c5004040705403564a4040e1a8010720299198006a40081c0d20302d084498021601030316040c8010841810034840f41d10003032815110700381c0402d0a010034129203240c00c04400303114076009400007940100200c600c0000f036001090b280d06018000303850300294828101a44081d54040c0c00400b0124114200044480c0480b014000148d0420805010695100080e1604583e05040000e04107490380f078210700b5030181d1007888510501e01440010810790513003240000c4e40074940151 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 730468183 1250 730466933 730466941
    0x304060c1b17160b0c09010306120c151701060f0905270a0e0a0c0303030e0609190606180501150c0809130608190b060a03030f0c15150e 60
    0x1e110344040440c050b010003181001d50b40414402c400a241444660082c4940d1881a0355a00c00154050725582c0c4803d1011030201c0d800d581620031800908a0f64010540c180241d68910034a6003490054201034400440048002030051801d8018500c3d046e5880d109036840d00340c000c2c607201136400c201c4005003c042e800105410070722180a20750040a100b2040d07905c06481c010740d0380101404181e40070369038803004c8904c0380003444000680e40c415011108028990309009041e07400e1904c0c03c1013aa0004014480380000025581101140e0140c3c2001e007100c2c103091000013801c4035484a00e861401e100c9042e0940d20581c4142d050358410ba0b5488510306890600302d5403a800c0e80402004440d04004043c0c036450040b003c0040902c200708041f45860f21030514a0810741103a030788210003c081d4260790200030740d4480e0710b64403030320545d900c500b202e1450310000c00c04028a00100c1c24014505440b01c240031103c42d107641d54400f1000d09100360b090300e071654018094244202c0602010b050041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 730469433 1250 730468183 730468217
    0xc030c032d030f07030b01120903020109110627062503120213060c020a03080f1305040b100810210506010e01083d0f0b0f130c0905060304060c 63
    0x2d01e004401c00003a2404907038404205900030140c55412a05001c04016452900c2e040c600a1180b014400da0001c26504581d00c3c110650122081c1024071441c1c0c01e0040445004c507403040411f507440c2200603000300c0e1300e0200105031340b4454400920f00c2d4540103020807580260a002010080b0b00c03950f110f68000802e04501e10403030042034858074025041c00e1080204a02c104c2022030b0340c900003810001a5540c80e031b100700c02c59010040202001c14040b4403d80d0840c802d80c401d200074402921305001d2803021134005034800242103010014401c0002c003060b464004c2c90740d40d0700a00020815181e0f40550320a80d1100760b261004112054411000049002a44103030814121007254005180254030001164451341d8032240800c1d61850420941034041190700c0040c501200748513000810480820400c01602c2c05000c8140c050032440c003200400d034854142840507911104d10004642c0e902c11030032502a5625070025902c800007200788005c0c0112507214086680f21034131242248549a401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 730470683 1250 730469433 730469437
    0x515130b04170607080603060a090305120a1401060509030604080d020c070303120f0e0a0b1b030a06050109120218090309090a020d0b0108041101080411031605092404020c030c032d 79
    0x18494041d080023002c5100d00085400c00e660b0280302c0d0601c02e09111040c02c2a0841150031115003010300e841d4021401c0d801720018101d400f504007807422134a440840408242d079804050002440c41c000020030f00c103044500d5040c0c2d102d070301e00182a122020b0b9a824014041d15801054104061410341d981c03807a1069889400541d001d9030000d0b001424650321501c1203651700400245411441e003284c4000318407854000e52140440320000203009080400040020503250064841c03c0c000c245400b000d6603811070b24144161040003286a15521111802d04500131403110503044034200703003803040c0804941c0203400740e289905c1007008441c1e4030398011641103205440c09000c0341d500c40009000b55206800b01644540620580403201010002107450580c2e0a500319a5a1446400034011480c024020b15000300c00b00104c040074075641e41d51220b4000d0240701103417040740c3c0021121030041c010309c195400203418100b0f0300d0301c2d240b081a01e440e90100c03001101d10212a0384104044c80361848003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 730471933 1250 730470683 730470691
    0x2060a0327020a050618030a0b0712020a1704031806030b13050118110918040210020d021914070b03040b010801091e0501150b0a0e0a0515130b0417060708 68
    0x88510740f80c504800d0014a034001c1260034004422680b00f249161000c000310392160748101c2c0003a2603807a100200410b43c1c4850381c04180800e004000002c0540d80c0460301060b1150182942c6119071a01c2c50240c561285c0040341188c0d04a440d2400600d80d605680706160001c002d172075041401c030004c002c050485600b401070107100802540602c460400aa20070203100302a044482e103803004c210300003a10001600c0e140c2081e07028440811007141880e218503512034516000031714400501d8123003c1d46840240d0044294101810701070002e2040741d0010384000c000c0001a40c92a940300c41c40c010665200711400d480c54a10000006a203410511646002d50341105200c24281031100b61004419801501030307600b50f40b215550748807140b242018800620311403080329034484100e0400350035400300e01d41d0144a040ca07d802007120b500c9600d811040c420220800580e074828071802c0400080294000020840380894041b5502c113403d100b80801d440c0107000c4511550f51000c080f030317990004403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 730473183 1250 730471933 730471939
    0xb1f1d090721080d060b0702031b0f220f15120f020d020d0605070203190215060d08040b0705070501080115090905070c17030105240a0f050702060a032702 68
    0x1015107410385030100b20703500c1800d103e4030016180403200c03041c1d0030554285821030718588000003820011031a00300000d00300114110103070454490390ba000a2210007042c0030a0f40034850403018031415102c0c1000520710600b091008110030340f500540705004000c07207e281d00c00e98400020200394410651003c3c80651b60041700642d040e101e650900419a608020898104d41403400b10400980039005c0c01348500010303401141c903001940c8a061940c0d11819500040d90800300d80d64200902c100c3d101640444181c40540d83c102c0787e072404151a00c0382e030380300f24041d04001c0343d041f042090105050003154000d070303a1881d0307998032428a244840007456085001c548a03590820602200741c10255000e032582c106030b5400d400130389501c0c210300d2021030171405600c0000018070142ca040c01c2c03100c0c0c00760313020149658214040007200409210710704000c0305009103c0180304000384281c6c1120001e580c068403c1e5101c9840074005800303002508680d141d0141d0300004072640e00742104400e03003900c1d001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 730474433 1250 730473183 730473209
    0x90305030418060b0a180504110405090903271e030303130302070902040b0403060f02040e04030e150c010e06060f060d05060f04181202030f070b1f1d0907 68
    0x1c20b00000b81c2815070b2030400781d680362600001e4440e5500c0c00b800d003101881d00c852900308003200301580030601c285c001c24407507458565001910240207064905079102550a0300e40c0303480742440b01d80b46005249003014281e92003840a200d40d014080c080b045a0710079600070840f10038035a0b000790034114400086d50964401d100080c002c4004480c41240c17940a4015908030b180c40c0c0340100c4c1a640160040c103a0301800150400c10000da61003500325030120003800b1428079082404142e80c110010308003a0401c000301034420b100d42d83c1c1e41c081c00144071a900c00240d8684081484602900221174203035041c0c0186d41c00641c503814004040c03440d40900a085501e00b01d2034144c540000d101c041c08194200100000c111020744491040151440017003104600c012a80d280901d440e001c01004001150014000201c1001414040e6483c41d0303441103d902155882381c0d003c2800810103800382901c045c1419000807200d02c281d01c2008804041d16080101d96142c07611151b83c1d0140744550b060941705 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 730475683 1250 730474433 730474439
    0xc010f140901110303090a17070201020a080f041d090637060f08030c07061803110d050a21090e0106140d02070c092304140c040e010b100903050304 65
    0xc0a0081264100c1414000155003c80450a1450b0011030711040181e00c10901a400d001b45000d040a800c0c1120228038602122070f40005d403640446c010041c1124030100d52424001c3d048415500540120303400810512071002500e042002c040c1e96800e0039000f070350b004c200c060800034211204616070154900c000c2d0f01b8048410710200c2c10840448440d95030311000300c2c01036034040700328000346034003002181ca40310304110090510026601010601103d0740044072200b0036004101c0403a50000743c10341101c1100000f081d8104002c0c80000d005004590010b8100a00078445041c84408454441d03085458801c0985554035103000b07809004003404010000644500708001060b60481102e50820615081000c140c0e00403007001c6601e541001010320007581a0b11581007480d01d21240c51248103918007407a45c0079100500003500010202081160203a000c000c0c0808400f03000c1c0040141c005804040d034000c1c202d455400340303d52005d40c25a0ba015114600c4441a03d030020091490585 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 730476933 1250 730475683 730475717
    0x120e031e0a020c04110c070608010e010b0706020c061f0b091e0d021807082203181d06030c090f131a010603020d0608010e10150e04080c0c010f 63
    0x4000001c110b102c0c4004030040c546843c0505c0c14440060750419442c1e091349000f8030b003484410380090381048009401081510381140049044800c0c201241c0c0da9404203040000103489140c02101980c072403503040c0700680030309a55840d030400c0d44030084507429031107050301c05481c400c0600307c65001c048068405810b5148081c00840303048000c01d03c080c03180043d40820b0072450340340350040040051008001d81160804170444d401040b0018522540c440080704030404551801d01908214015182e503a900c65440c1007800a440d1145491410120480040c440d040c41124154028010391480000700d00340b1500003401100c0f50f0008440540d41d90b5070041d140740c10388400f5030399055426600092a8422a00c040c06841e4958001d6552298010445d003502c4803507100035840da02d41100d02d241c510001c221181140c1005501060041681c070390b13591264000e0f084440e80380080002c3c4800c00034040000d2040c01803200503500c00c0d01e8110015540404102c5180011800395040960006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 730478183 1250 730476933 730476937
    0x60f090a05150304060b2e17090a1104090b010302100e0d290405100e010213060306030b0708090607050d0e0607031a06070503040608061c03120e031e 66
    0x10006024540119590300004040b1107054a400d0040c02c0d0000a020034052907004410411800361840c4070080c20084204008960b2420720001008400d0141040c15100341d012410035412030344100714904007401c8181d180c1610202c110396508042c400d107100ba040c43c0c00742002c15a00811050410b0386590248500140041d00e240100640e004c143c1845950b50490b100200d0300840700030108a064106006180082010305512a210001003100007200081c52540640030742c1008241803d4500c0350314060300071014050441e215010300072540e51761503071018080740d0040d02048507a803104402907440c204207854400407a0030420008808038001c0005003480350031508001000141c00d903006080c010140c420500180d160000c6213180720780b9500b00e40c0c40c01800c4038503500c1e0544664038a40d0b00e2003070f4031a01c8103110315100020500d55400342c09509103004001016030412051500603c4200000c1d600ca080c14644500184282c50000c182e5100281960505043c101040c0d01c1455039 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 730479433 1250 730478183 730478197
    0x901030b0102030d02040b2a0c040e01140f040c0f061202030408071b080d02030f03130f0c1710231b0703081b1201060f1404080c03011505060f 63
    0x1601c400c00c62601424200d05c0200300500780b01c020700d500c031040c1d1140640c8050b03a103c0c42c0f4256207018581003811020210303000f039202030210750004a203c00d03038450501400b12040c064010307442090800819190b0a4800b6104d540b0600c10412207640340c901382051191380c1e00035603000841c54083c6003001c40e1268025a00113009806160801595a95000e0309100505460070340d940003a0040002c10010010200180c9081c0091030920303a240d822140303e0b010003050042c205c02c0b4850039005004101c055120f0050b000100460b02a48401681d9488d49100ca900e004d9445812240000c14542c1c0c4a04201c58105809400c410f400c0c0c0480316441b10b81c00303810b4100e001c0424000da282400404003c2801d1446600e404566151103403072000030620106614410750020858100c12059440f5107030305450850174a81e15450304003400b1100b00d40c804001c29122000018040784040c2c000466205a0804400074001604800100800f019052050395046041440000355440f03041d00508a0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 730480683 1250 730479433 730479437
    0xa0311010213060f030b040506300a05030c0d090e0114042c01060f0b040e250e0906031f240f05090901020316081e07090503210901030b01 61
    0x1c002e004076190b140d1040c950300880c041a5001c5000c1c0c500c681500071345030310640c119002c0103280750900108081060400348845c480341d02c982d00200c251030074800c8004668590007201c0640b0030320b280042da031340d00416150303140348144041e1121091041c246201601d003110000b1880343d00e44240c620fa00540c19041590090301e4a4011604d01c850100700704600e4691141e2901d40101d4040350360854007190042820062401d000303001e0b00800030116011030f02029010102651007401024540000c2170031040c4140d0420321010fa000c1c1c0c400d41e17900c81d0072400c5030540b2003522100c00701541c0d9540000100f103205040122600001d24079400f2180c1c00b05012402a19030350030161507810b014581c3c00030030300c1c110402000d0260382050444680e00c0781ca100021461400d2101428003502c0d410b81d201c008102d8510000f500e94808140100c0070700c03200210003800c5d0f040900c0080c04449243c0a618001c1c441c0e410060f54840e052880e2000344259008001c0ca8030440c600110081c080242c405d41c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 730481933 1250 730480683 730480687
    0x6030a090f0323030c0f0304030c0b13120305060a031113020d0e0609030703080f0403050c030c1b011803020909011b020f10110319180f050c010c050a03110102 70
    0x804110340320485940140b10f03a8030082c20a01c004007141a001c0121030b0307055800014800c0011101000049441c40c1210150390f64a0f0b65440c50219481824807d000740031510072001e0004e08107102240710708451041315018550041c12504408461f0200c3c2c8865101c0d00400c1c040002c01c00c1c1040078040000041c2000035006050070514082c1d83c03100c481c0c60075040e1383d054940807150052003003035003207000354010b507144c110951001090f0340710207001d114010b01f0740004282054011811140700540e0b41090381c0c0c95500c548000c40c0c4411359903002c003801e802c40d481400100d62051080c42e10011102051075152821a024000c181400509040781596503800244d42c40315401781d5440108001c0e07004085643e0400242c0c0d050908095080710a541802c071800e0343c03078110030b040e6a4002481a03039140c10500d640c020034040c0110310500ba80e806650003e07002401040c015206800340220100c501030519403004589444100b540a4181c0e000891030200181c0f103103082200400c10440054 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 730483183 1250 730481933 730481951
    0x3120f06090c05030405010b06070b04110a1d150420030c0d0e1c0f080a1e020c0c0111060412120605030d0e09100f181e0203180109030e06030a 63
    0x80116030000b51280d01065001c0100002c1000034012405010300545e40f650400c10140c1d1001d8410301d006d40001e10107002183d245a40d603c49400c028010111104000800614494104203008003510080b1002440c80c040d004581080c0c0aa0072810030242000240b2461607031030314070705410203400b200790503204000300c10803108c0c01e000d00e4402c0540140549003443e18514034a004456030303100070f410721101d03a0310143c0c1d10b40c10008031940716100e10b03000300b502d0210111800000f0700c13004426001c41e00c0440c0c00703c5284030000d4618072013182170b00e584d060b4583c0c009401c0d43d242c40480700240101e5000032208440342c440d48280314407440c0c40034085655500c50300028208000c2580b43e6002815541d5074a00510f0b00c901e9164006081d0101c200f1420300b401a081018400340c0034604000f21544080c60505480b54403140403280304945070302c0002c240e0785550000e98403d40e9044004404c145041d00e20b80d03410b2003040102507244e00d40240d01da808100f400800e030401011601010340d00c0d8100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 730484433 1250 730483183 730483199
    0x30504050a14030d02150112020f15030106020106170d0f12060806150f0f100210051801061a030103020904141c0801060c030e041a120c01081303120f06 67
    0xe000070340300b44540c0d104001c0003042403629208048200f90215480a15194907810303402c5811070541e50b824018004010031800413604200540a000c0d41006a0761040f40013452490007950590722541e00910117555540170580011108900c203004580005403410051030003a120304561001c1410114040c0c5005c0011500701c890301c1d03000c400107070003a0f8200f100000401659600c800e00454001c1c88003600c80c80403c1d0b00d00c1d0343d0006140a1101a41d1401c8124020020804071802c0500b090040d454260013210344002c22841001180d0b0903c1800f04051060481c01d80d45582818a05811a031940e000c11103c0000548180c4084601d503a4144420314184000055007941c000300124869075081c0081400320164025070820811008400000c1d0707200c18039044401c2d08071000300702026544611206020a031303e40340e034000304140c18012801004030b96418103003003d8951900a40d1507585102c80c002d520340c030040000b1380010611b14003041e90390007401d10112944000031425124150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 730485683 1250 730484433 730484449
    0x109020301450c0f1401090305030a08070e0409240504150f020409020c011d0705030d03020903010b031c02150f07030c090801051003020405130210121404080a11062203050405 77
    0x31509034460140178030407250b0418045448600078a081d040e40340c91515503945070b0240410718030803c00c0721300100700381500c240240c501002c0300038810000a2400d04c2c000e900300001150100080390410340e04901d81c0068030030641702d590000703408030310180d07000d04000c003d00540201110f042e07401d200201c3d0804c218400303481c1ca086170b0000021700c142c6075a0b100c06030544443c2e01c0320340e0b1b03031000c00b040c0140c1d03c01140d4020812164207026860341c00d10300c0081c1c0584004041c0e540c01d44200107002100b510641c003201004081c0d9020380d0064050352000c0d0080d10800c4a04d01d000204038000300d00150700c05d6100c485d001c0003c1c81c040c00550f80343c00c1d5140c00d5400990300381c100840c24110034025440c9c40d1103500e41003481c03003008003504402075022030203210a852295041c081625500902c0b5051a0010090410200d403002d00c0ea103440d15260881d50003224060000500c12421500080c0000401d1400703210180381c0000801c040d042110b40d801c0c8408801c4003000028040040c1031749071204 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 730486933 1250 730485683 730485689
    0xa05010903050901021b15160803270c030607080a0f0c05090a080a020a09150e01180c180b0a050c030d0222030807120915020109020301450c 62
    0x2903042e96a075003c5000a00d01010382c018038680f80350350301444503265580e480b083ca8035031882ca84030303440e510340c1c1070340c070403500403058000e024900000304010500034400c3c0900d44401c0c03400072034112134542d0911307035a0314801c0c00007481c0c159105201107010b05004403521540075441700c00100f416111881c907001038a10402da07000110703101145200c0517150000160015110107001040c900105800051080d90b02e44910034ae01390303407200c0400c0c40000740e04107180541811002d4075402d580d00c1000d50845c02c10620182c52541c94090540b909a100d010002c0e500e4240c0d00000541a08012802d03a040d03101200302018807500308040002443c1c03c0c40941240754894100680381d20040802000680d1003903100300c08002240d00c02d200140c100001c0d50000340d00100b56a5480d050204191059040d039000300709000e150f07000c0a4103180d4150007070a26544254001d110200c00035141c40302d50100840700c020350740b00400b4400c2c111924a122100760603c900c501c1090403006850b100908603842d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 730488183 1250 730486933 730486937
    0x1d0d0306030c060f0909200309150a0506130c09050a0608010f1e0605180a030813060e010c140c060c060103110a030309050f0d060e0a06060b0313140a05010903 70
    0x80010402d00c5611403805005201e1818410301424080400030105480c0d80103891006a50b01204150700a1501c03610045403c420256030f900d08105403510782d0781000c01445600c60511a000078400449801071314000c010182c801011101000710f1440501078003d8800c04003d201c0100160a6854104d00d400074101354030b40001550405041c00d00c4600c0980050040511002c0a102c040469280c04030444c0d8242c9400c68481042036000e40468050002c0c0030b521560f203110200038450940300500007942d00c0198003505554810041c0c9071004040c1802d40422108000300c0049024811403101da00e00b20740c15074081882c002c00003101134000c2d400280441e4024001441042684154a0b16a030700417242d00e800c10f4510740d00202150402c1c01514054111003000d000300340c40e000030040c80315074000000d00044c4200c0301e0007030341c070079401344269109400c10700b00281000d0103004807400351400021120f9010b540d0b8031a52254460038005a8503441169880c10101e1428403907030001c00e2007a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 730489433 1250 730488183 730488191
    0xf0402030a0b1507170f0705151509060102032508031807081b060c2e06060305010e010b0c07030506160305280b0a12060203010617040b0a1d0d03 64
    0x1409481c4656a003c0700040394204078040104444000540d0585450301044c0d549103540400a400c0c0e0241000040c41882804900900007240c041e0303080c490025000c081e941d10001034204070544000381c8a403400750300100442c6003403012070002d000840310b0b940d52452040065070b5401d00780381d004444e400e0004034208512418200c05000d5070004211887c000c0800040e07014221a8014909403c42e100307140c0064800c1d0201424004641c0140e81c00c1d00f205907a154079038545403000ca240c02610941c81c5081c9012a003079000e8801c9038181e40e943c510391074403030b07080c10045030566001c0da2045030f182c0f040c0c4000200149081003110302ca0008813100c81184844c1103005810b07140050440c01c0340c0501182290aa1a0b0f000c200c004000220a004207818025202081c6e0300c04d030f660009003540c460040e0041c10302c245500190b0403201580c4d00c00000258660703118100040c1a103004003401c60041c0401e4140d01d0076005030703030904d6a07440507880301d41c00055001e14284803403000402003611 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 730490683 1250 730489433 730489451
    0x90f08070c050a062c180106030e0304320d060f06050f0f092502150603010603050a030e0a1215060636090203091c020a0317060f0402030a 61
    0x80501d5420003050103480090285007000d00c00741c9140391022030802c00b020840b11442c20f2800c203410011002e04040c10f00c1c6100040c06a104890030f100b409180b0229041c04c4420000b140c002084500316008480442c510311030110310310303240c880c964441450444404d07030003181503528140f104d030407140f081000107804000282a1741c1502d13000d038006440f07000d0b103e62101603512603004801030640100d0300c5034410f681d510300300d12402401c0c0240f03000c0c03800144c101e91122a0002004c1c100805c102c40c16508954a031801c040c00e0391040d01008003141c005901c41000039000b600c1091413228018180d40d4402d450b030b0703891000701c4403640301903480c0d20b1420148554000760380b003148081d0116141c100400c1a2010440e0180100b846d070140741d10307501901e41d60021504a200c07201070440020306664900703111021030780d10140e8003040025079064a50302d0586034000605988100c0c1d050301c407448010100c0582d4145158020540d540084c0500300e03020403955144011446410310340f81c00034003091 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 730491933 1250 730490683 730490693
    0x70305010609060b07030e22020703020c0f03070b070309080d095004021602011404061d01050c0a05030d06050604030b01050603090f010606170624030a090f0807 71
    0x401e81e40100525494010f040c05031441400c1100e02e160703010b00308581c0f40c100840200c1c00344e1b1900d80910408440d481c8246201e0005500280145400f070b5003210944100901003000200884038601d42c5070740305010410103c0b050402500d411400307400c0c00f00007241d850380440d041c90121401c000004981c100c05000c0d20501481000e4206188002c075070040c5561a246000d0500d02d1071040982d614400b100640c5070f1032110380d0a0256000740096483d02c035001c107084071120010300201d01051746d0f26040200096640c059600b1a80142d5a290840d01803103882c010942c0415103a0303041100c02c000440c1503000411084003440d100300c000f103070b0729050040784200308c401c5904201d20480e02044200040742000c801641074400860754a96a41c60f81032603e850560149000b442d40c2d400d003503000601075003100011410a800c3c10501505a46440801155861340c10803e60a09001c942011501ea86400030750307400444d4640c00100c0c40c1880c1c5410440000600c003c80d43c02c40001000c0007008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 730493183 1250 730491933 730491941
    0x729070e0d020f0a05030318040c17060f0409051e07120809040c2708100b09150a0504091b082811040203072303060a17120a0207030501 60
    0x21a261030240d20464090002820400004501070b1180c00c240700460704580c0c54541401c0142001400c995480c0202401c200c1001d10403103940d4481c03458000a4404107009503005c0c40209108031685c0700c1551010700304100107201c400525081992225002e001800070004403d02c8141c454001da02e51520846176481c145141e0480910135109200080005d0390343c100345d41c0044400c0f100410341704c507070341b03000c480d000f4841160408801e00c850911201050380c2c848182036411384800d070341c240c1da440000c150595110000b0503403c580640000342c00000c0b100940508614000c0c00f13040c0172582c5000242c2610004481500c4000160007603540c4040c980c000140101f0001c006030001c60003e00400302219454150790b00380111402d144810843c00c49440405900d00900854884c100000c004200102d00400d11040c4110501c02c030018541d400103903071003002e000344440e01031070030aa0503c05003c45503074480358030300c00d000c04c1229490442c0302605030703a0409d41c02086c4c1c041ca1418414291 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 730494433 1250 730493183 730493191
    0x50c04050f06130b010e0d060b06042306030103110f0f03010516021b010f140405040609020307081b040620060403030e070905070f080c0d050f15060c03030103030309080729 76
    0x503e40422005203982105040c11001c0d03045900740654040703230a03d2806004c1c5071001586c44980080e0201d140340d44041c09200c0c1840082e60301c03200241481c20b01ca4140300078000604600d0f030041c210041c03441c081e40d6404c05440050f141d62200d51103a40481c2c01c0d0313202070750a218040f20301c08808501c1641004043e07c4064500e1480d10b404181c1c800103001c0100820b040420406805801c0004a240d0411140205405071040105582c0c818002c002034000707540c4e0b23100007620306020400e00c1107941c105003011243c06403030503e01483e2110035140c2008090700004000c644404030350024000b4400c840c450340c007a032808a4024003410002c0d04120300c50b00901c00c440e10b420140704459a0044003484c54034240c2c01d080c3c1c001c0c0c0300c00900d0302045c05000c0d400a00c0034100300c100400700d0078000d1752900401c1080d80d040c40200b0310400700b0445000b00d5190300d070341d94414001000400c0c0301e13402481c0f41c4c900a10b202072a2502c1503c6800c001c002414804040744009564040400003140f15a988 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 730495683 1250 730494433 730494469
    0x2060a120c2c0607030810030f2d0512030a06090e0f010b030f0706031812030f051e0c0a05070c0909030f0503060f0d060e011d15070219050c04050f06 66
    0x2142e065a00020041d020b42c007000740820506100243c0d8419007500404050f5800c50015800310303420745040c002e529052030b007104121a01003800280603c04010b410a0103522401400d503460b40071400b28000d4000404036003d4989034040003c03150114440e078401c000000000e4108010715075079180c02c0da1000c1d00400e01960050413a42e990b004c002c5156400d07a0182d00e804204040001000102441c0303c0b40050007206050440384102501544528480030414106219695494040002d2001035091440c90302c00c400b0001010450900c00604400034030382019401c01401e41c4800881c81c200e5000500016543e0095170141504104c051030028502d15040e440c6113042c002080814100c41f84031405007000c0081d90702000001c0c1c01c9607090149860007005240401030315882c00641c0355440410724002d03984198081243c604400d4030950850300289031803450050035044036404070206440318007908030410a82e5403907014030350041c842c030b8000a15034244882081815076a51000b030301 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 730496933 1250 730495683 730495757
    0x4030c0e060d060c0905151e0307090303080604062c0f190504031e1d040212010b0a05040306060f0915061b0305070b0405060711011103010302060a120c 67
    0x1ca503441074441440d80b54403c0d404292840314110907200030425802c0540d0040c2c1a061640c81c0c0120304000c0d00114407141000441c5000e5030110410500c0152000400070729180414804640030710361154001d04090b0000508590718590840ca04040008180c1d8140c031445c102001240340e0b00255400c0f005115020485042034644260a039100341c0b25010b00360b4545001a06040c014002c10102c0e10702c24800b014014401c50000381a140f9404030030712243d1034400201c00740c1c2040d209840b454281c0030501205642810310000085d00070303508010800c00c0170000400003c10300d00510005000b44034150305500d00b03001840c0e0980d955044130505a1003104410002c56a00119424410102d0000c080d541c11075818121004d00c0707004001361074043d1490910042110000307000d8890a426030302c04140148012a560a9546610304c02e604440140010303c003524201004159140d070906042c51030210030003034542515403800308800455403542203269580990802e189409214036a040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 730498183 1250 730496933 730496941
    0x70908070302040b01020102220503070e040b0a18080c06010e01051e09060a081e010507111b130f0501051309080409050901020f0705010c1709030909101203030204030c0e 75
    0x356100594880607100b0f544a8542c0c100d1a4000c0d4101c0710f410058014110740300d00c42d80c0102d40130a25521038580a803040c4000000c0201c00c45104c00c0c041e1f64400201c1c042a1a003c5100d80503006031070120301c404107124024800148814010401c001022004d0040c0351700d01001c0c2015928142c1c811401040c118003044c0c03400400030206c20383c100d0100c40c0420319855050128150813055003040440c3c1c41842c26882c40e5190300455007411070f0008001741302c80c0c2e980c0356003150f1070b0480c002c40d443c05034040c40300b200c0c2c40000013020310b541590180c0720311402c0d2202c0f1110002e40c0c020401070705d0825a6180140641c1c2004407180c40360480041c403d0012246654550303040384520700c1216002c580d14030202d42c07440380079011516030740c4644a2280c0c0b0790203e03050090092080700040c0000ca0515060310410074480f0300901d210f107281d2000f440c00c2c96405d0050000b400e02c0104114100f10103110003041031a481540100700600a542c01a1140d003103140071001070328590021034940ea5064200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 730499433 1250 730498183 730498199
    0x42609010f0f020717010203010e010506070507091a04050a0b030c0919020d0906090812150108010e06030f0601060c0308010b0306091603020903071d13030e10020f030c03120709 78
    0x81484460701c1d14200c40e01c030102d00b008a040c141c82d9001001d50104202040c41c4d0348005401460680f40705580d00750301c50340d803402084068405c0d020020102d42050f1001c0140381400d40c440c901500d0364201060650400e40000340494400721780002d501543c03245124214241040150740c41c2c081a80c03140c030641440040c801442c007170010f10000b40c0d600065003243c240c107190013190200c2d50204051240303995034079208185030030107045803142c4008500083c48565103200318220202043e10f503026280d0901060101c4000f009007165058803034103000042e011380402065000b44015aa040740c680114a0f0040100300e060b44200344900e005c0c0300348211907131740b0f2468039008003000c401d02a2584495009401a004009100d54580640c3c40c0010341d2019807240104803d484180100c2941e4885074902c071440080200580003c40e49425141035003030038020240300b85078500482c0d400e204049150b9245500030341303156006400100741c000040910180c001e800a00c1800e009042c80d061440c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 730500683 1250 730499433 730499447
    0x121b09050c0a080708042a03050a0309080607180b160c081e0a0b18070308190311030714090f040504080c07080a051906180c030c12031e1704260901 65
    0x140307c8403181c0001075005045440030301c90010341e400802d07101f000a0340c0c2805400800b26104181d030340e009501c00141c0180c481d1002c07441007541d80c0351b00202d042c2001c1103c0303450b80110340400b00b100040340307a10f80820900702d015801010400018042007085003000c69000303d81d104e0703268a5900610304a4005802106000c1d40120700382d9a07646846c60b00505949002c03096400a03001100000d04880e802a2451045004400340d4405210351405081c020b81684002c40720000011018554428210191002050b87d00d4004102030b210107030a100050460300d055034119118800091030409140040c010a00209146000b80c03400502c2c6444082d29000c481c642090340da68682d10800c204207699000c03030074290300c030400c1108004a1b4030740200b00c08602d00069a00c01ca0710840000c1000c0740c818001903855240e990b0080d0740044200348048403584055680074001c1075030300d001070850001411449240a20617800d45155884840703c034800059810390050b49081250070850390304504 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 730501933 1250 730500683 730500713
    0x4030602220f0515340506010608090d08071e08041b0501050f0901180305061803160204022805040306050c040308090607050717010f0b0307121b09050c0a08070804 72
    0x1610720707654002181000700140d0001700c2c0c0f003040342101c03c01d8518040040c3c1c1d81d2090340d20940490f00f003640c88003003e0b15000812a9001c003079610017080410480d10912542d900800c550401d5003c080e500010312030041c80900f0342c040094450340c200014080b55a071941d0000189022030410a42043c0000304580700780161000c4125000411000741d9114040321031200240b941a8204a0b0b00c0b46065512104180e0700c07154040c2409185114040000c0101c4d08021445280080e1042c01e0b03609210280d08807214075090508900741058184403440510702d15061581c1e00d136030b903450440c07500d00d044070b01c064103002070003205000500000310740c0790880c1d144050454401d03848810701d207041031400c011a00060041c62040d210000b00f01c0c41508a4035a9180000c014010501c4000506035140c4042c801d011400981e40b803042c020030301c020000790800e400d03a041203143c55204d043ca002950f20544050800c5003001034200b00749540329040c04d0304003400e890000354a0805850700e01c3e41d400008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 730503183 1250 730501933 730501969
    0x15020c1507050a060207021305061e0607062d02030c0d050402030307050d02011b0315120312022205100c06020c07080f061806041208060604030602220f05 68
    0x200c224500c161504140d03419140d00c03004a541403c01072600c40081d4000c040b08a004040800060035000300d10f0045d14442d42000e0209007540d032144101c040074800c01500d99402800c100900d00210b0518010580c2d4904140c3d1841c036904078261809207407440b101c0785e406000d8414014406005500c104568624081460200301c07900c07a800040c0c00d620502c0c600400e18422112402140760701074000b280e200c0b03407000705024030350a0703148281c0c20f55505035040d00415454400a220010221480c504598083e2a0042c002d0550080c150204d03803040d51281d502ea880301c064181c0d2200c0880c21a00030b0310090301c40803c0600311780c030301412141110b84004d200326004513000c416501c00b04020740003000d400084a0f17032039440d000c040752680001d9841e8260512800081c01004c4030004d442c40c01503501a0081038090080d003002c44241c4070180140da03101804000c00008203400d070018100000614091f5040088080b00320701c03071060b00d6803010006240181042207641c2d514020000e18407425 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 730504433 1250 730503183 730503199
    0x5060a0507110a06060e010f050102100e0708070b090405160206071d04020403032007030b180c0a0314010b0306070203040b0d020d0e0304060210021c0c0c06051f15020c 74
    0x8506079000a01c110b00c60502d445100022001d0100c1030b08400101c481505500c021640ca81c059031081e241c560260f2405680800d00345410240075034400f0310300007065425502d09907181e0302154180400ca40c460040100007250390781991400b40b01e095002400704080b2510741c0d69400019454040040c0a80e042c00350582003080003d059017900f0f5000a4000e000f19980c41e128600036006500100020704d600d0340442003ca851680001c60300150ba4011150013200d95407920900c101b40245200e41d141030080012010440c0c9920b4000780140d0b10a1101c6914440d60021a03401c40d070150201e68444c0e8085010700200d290080700300e40c00d0351180c000c0a0303540c00303040d50b18201a10420032502c001c1480c094034a561010084050016201c0700d90030741d500f100e03151806206038040c03c0602d00b1101408000101c161b1901c0c1c0c42880d08210b0b40c00c1812101d40151104822907200b02c80e1300c003d00680740d08458031590150040d1010308100741060441717070303403170074000b5505c98420003124001c1c0c1c64 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 730505683 1250 730504433 730504441
    0x1801080d020d0810050904030c080f0705120306030a1401060b03310b0604270c0320010e040e01090f03020106060e03070b1206030a0f0609031202030f0f27070807060c05060a05 77
    0x803270903841c200039410400003a80e410050f0900c9840364400d17881a00c80d8010083c21003c00112a0116401020014014202039905840344840c0140c0c825860450790359411000980c0f000d0500030358450318118505140d07a8920242c03008402d29a2000070f1441c09120680000240c0c0d01d452413034000c20300340c4002450814110041c4403800408410007450407290041408211104510100340c0f480740d86400d00c400144080181d819154680090101d15950300d010000d041c580d20030320035024494004144030303113a0f841d9522408490803064006035156041804480d41100145690340c400341e0041a05918002031072400b405009000040310500c03c000c00c10540d82040110021500304209010109003850504024611b41c241100462100010001c0403c1c81e031003a6440755400080b50b4103a5642c40403d4001c2c080020800c1c0c00410100000d6160b40003842501c0e6802c0450400410601f41448030b0f56140c91100c1e80700303070100080f0102407030010b44003042017504014a00004182034135 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 730506933 1250 730505683 730505687
    0x519230f1f14120108030304030f050c0d03110409090f02100219060911060c0303011d090d030e1e01020409050f06030d1805040c021005010501020c011d1801080d020d081005090403 79
    0x20820700341c03c140c5091800080740000780440214041e034804e0300c401034a0707000b501c01174600d40648413001c1500d4100486840380740c2d02030741001040b203100c510a2803416844401100c11240078407401d0780d81e0b004000e40402142010760000c1c94080e690b000602c0c1c05080c46001c001039000d90300e0010b1601e6280c503c405c0820078440c0e440005142d0040c15141c44120110046580350000d1054880640f51f103440030b1140e6000c01f000034020841003001e080320018502d003d030050165070405545a2081400c1c0305904520f08480003c41c20b1841c001603a130754a0303c002e00055179400f420204007035006009111aa9a0029250a0091940c02d0208004d029905051400130642d07214036089400c00c1c0503005100d60104d41200844441c1c04100444e90700c0700012a03448400c0101113011810007483d0050440d4840612488054010001d2101c1006d101d641d481810080e4402c0c0700c550321610380e1700a0a0b03014040151804403502d0415901d190643c1d01115101944c410f6a008505a2012038203140c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 730508183 1250 730506933 730506937
    0x1b0c060b040615080105150d0e0709060b0a02160506031f05040507030912320403050111090109060c0c05010503180a140d03020c070519230f1f14 64
    0x1100040c02000140c0c0d41d2056402072030b000820f080001003a030000800c503490101c441802d1014105903003420710840a0f048001000000c0d156800761140502c0006c24a031ba9000d008081e040814101d9261503030074401a00d00540406e0006940ca000d001c184007a0b110385046d254088401700b554035021500803040c4410707a940c0e0704155042401c00c01001100c0e50150445c0141c140325000e04403140c210f07000c04603006058224942500f031010007500d180c004201403080080401c130303e0118505550baa9900342111141290308100240c0403840203041c2d0317004540d140040005040580ca0f0b4181603a40000300c0a55000b030506000000c00416802c0f00c6000e803d071400c01d5410221040b0030304070700f040003180c030100101c03880310302c211010110050304c01d000791072500c2242002407111034100400c0000c1056071008015006948540000b007480c0e804021914040d900750b042500484c2040074007551071240c4c5c0781c20340140d500c0c1d40b90b810744081c0c006a11035214024640740e000300c200014800114 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 730509433 1250 730508183 730508201
    0x1e0607120314060607170a090e0a0e010b010206090304060f12090c050a0503032115030a0c06020c0d02010c03180b0729220c270c02011b0c06 62
    0x155669a00c40d16000303415a0020315041110b80c1c040081e076441d01d04008540c8030752080280110b14a402c20f80b04040f10320090508820707182001091151241408401000216288222a5107801c48a00116004e03c50b5501110080c8040c040c1441c18011290b03076403040e03110741e030208104120700c4400e541c486c134072251000581c42007e011440450034442071143d80350040364466001c818000071715140000c115451880c4000c055081c00c07481d00b44030450320a0052060448180c80107001105c2e90b0284982c5540901c283c00d100e00c0300d800d1000080c502000303110a00d00400c510818403000d41c2e0031006009210307034145002c009072032aa501c12030809a8079403151071249804590082001801650314400c52030450250801418043c10258144030945801542c00381c01c41d803c241c68201b0300c10b000c0042d4000c5030365103115035a911503100c0700c071643c41890003100403d0403440020202d81c00340302d48400383c6100070f0006840c030151000030640c4071107650b405d00006800300400c000ca5500154030b9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 730510683 1250 730509433 730509443
    0x10c09030f081204050a03090905060a05040f0e0a0c030308060f060f03150a090b0f0a0b0a050a0e130501031208160e0d02060d050f130c06080628231e0607 68
    0x1282030916115503511b0081c0300c210041004102c000c103641c5290f118079403085500400c075040a500c1e2100344801840c0000005007080e4840c9203074016040b0030030900300b039584150101010680b9604006011a00284c1013a00c80c801d04003410720f030340e558101034400c400e90801c000b9540707407100407030104060340954020f0341120f4041000106000030b03522107405d500c425a600d0b01d040e04440304200c030075031072030092500e040340034000c504880b44990054a4107506a0074500768070319809002031a0240c032514165503032070700c42c0014410004c00c60312050303091240c0d04000d074160603c6250300b9141c900d1548000108106a1401c111695411010389641741e009081d41d940c586080404c40c0c0502811110404541c0c160404500403440c8042c0c12a401c07900090032608803410503908803402c036800b0340f501d5400702e0303002c1b070711411026490140440796011941001000d490101c62030486104220001d078501d4660170f25007406d807500481c0a08039403154401004e588400300c0010f006000d40400038013 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 730511933 1250 730510683 730510717
    0x9010e030703080a0210020c12210408040f05120c010f050d020723121206060c101b030b010e0910180c0207350f010f05040b09010c09030f08 62
    0x30300900d40c000f00b00b02d213001e03400d68555440c0702a09200703074841c424070ba58031507011030b9046074440d80c020040c0c003041b000e00024034a060103042d140c043c11b00054400307031040c10001070b0800c4080302803504900100804c2e961242501c19100c522500c3d02010b07035085061040010718203001034460310440346c104022040c21921800c043c2024080701d05040e4813250507102c810326292100c400080c42140c0302042c41911483d041000c5142d010140c80a001990001014000900f580405000c3c02c401c4000b404000580c0c2810104e00043c2c0e0311007510300006146ca4072000e84002c2e64003080e0070065010513103520200f600c400031840c850920980c003034403281d40c0405000d0070010480c2c02ca00099806a400c0b0b464007501d514410038080300400c0a80b4020b4450340001c1c00c211407100c03418a0020262066443c080c10481071242034130302d4070301c90700c400d03030754403001c2008000c01e00403038a8000006000030898800f900501401142c001c2c04042c150035a407044010810240f0f03421030301c5441218480764 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 730513183 1250 730511933 730511939
    0x501060801021b07080c0904110102030f070b0411040b030a060b0d0602070b09060601031a040b04060b1c1503020109030f0f0f03090603050a0b01120908210105030f1507030209010e0307 81
    0x21100318403070f200008240c020070200203641240002c8200940000900c24116620f45660340e00b84c010f80320b80e60700c0c15800180807491090901001034603e40e80280c824220328540303403402c2071001010500c4c00c1d200e145000c01020f0940c43c00180c175600d003540100300180708030f2608c00003030b40c15400001c020710582c00021070004008500b40c0d003501460083d01100e01e42d0700e40340e00640589460700d000a11035602d2140401e410300c8e207030300300392800d440180c0001840b03901c5c0c2c0c00c000c0c81d5500140180d0a25070040755403082e007410700d104211007201d0102c0b5030101c907810b59000070712483c2d41c0e00c80a040340c0852842e000a00100d908074210455002c0454503015026107005020050315115030404070349400f00154004006014100c2404030594a001b80b6902d01d04460005240c03500c01560201e07024040c6040c5030349140b0002c20200001034840105614000404d0314051261000c0c5903c0c0d0801207882c800943c4603010641c000c000e60401603140d0b5600401282c2c0e01019501036a0b05100d180000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 730514433 1250 730513183 730513207
    0x60e0f12010c0f0f02151e07020102090a060309020f0402070c08061e090604030e090702070b030a0b040c0912110d0204180c140f10050c030304150c0801051c050106080102 75
    0x561079902a807202d00d0034005161055132090040789404000da003040910040002c88038038800e0340a13528408a1141e480d074030341010700c0e40d84201c43c520702607035000a51000d10324100c1d00e114010a1a4601070140c0c010550100d0f071004140c9040700c0c0900c0d0042007080c00c000d10780100001620302e01080303a24500d040c02141c2000030382d042c402c00c070480c1e40c070300840c1c0c070302602081281c07051b905a01c41003c1d0100400a00c0032132800140543c0460043d418041030a41d0484011801049003032004104284002d003004115945590710109120301c0391000c01491800041d1310815580005113440c05003444808180c40c401e003210000c2d4403034075007000e060304108030044000080c5e018109a0b410107898296038085154046503d9038490b691500c09120b0340f4210000c040c00765002d281c80c1b0300303000d1290851851a0003d40b400c6500ca920821040d580900c2e40c0315802c01c006c41494040050b5140c070700483c104064003001340802121a0100409024094100900400e41e10008550f103c1c8a8040303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 730515683 1250 730514433 730514441
    0xa05070308010b2106060c0a141002030f150d02150a0305010906060215130f240b01080a0b0114210a1407180302060a051b16060e0f1201 60
    0x104402240c1c40200108201d24400190303505000d0303145803003003503090384e80e903020346040020f06003a0b04c038404001034040203009000000c1014803c101c0390080c0c0d9903148455060a0502100319020342c41481004508070a07844510f4200d032310454003100761881c1c280403d0300103415050194101000803c61154400050001d281c402d80c6035030204181c2c0d807203400c040c081d00c00c0342c4101c80059200c0000c0600c3ca00701ca5000325005440d01340a8034240d0f20b16542c403000030f1120a82039401318404010074140c00400340101c03440100c07404c0100805844400044c00f0340070060002002d4603a21030b030807025a401114207400c0715118000094440b104850602c9410b000d40c1c138000d01ca09484030200d504448035010385200015031040440c259622400125520510700455000d482d44241000025803260710082c011a046596a2903a8800311503000d01e503425100707104000f0364030a1900c0e8807000100710000c0180c40c114a0300c90f03641140c1e400094001c0b682c429146a000350030b20720032100d100301588 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 730516933 1250 730515683 730515697
    0xb040b07020c06070c0513200d14040f02010f03020a1e03141006020c040e07050402071b140a15020c210712020a32060c0d020c0307080304180b030705060a05 69
    0x103110410010803502140c180d43ca10f013150080598100c1400c3c50500c000c501030b000345446000000ac030a000310100420481e010344080d600302101e01c600320150751b8030140300040003a05003402d51900c45a81030042c0200b000c4c1c1c80c2041003552401c11103004d04d01c682c01c402c10394541d581c0c18600302d040c21003201981900c2882100054421501458101d04084c010540304c00807020190000500e040180700c065440000300319102c100001c038810601502036030031406848110a2224103d185106000500788681c011085070f1041440701031030280c2c00030740d0350a80038040c0e40f207075000ca58014001a000391458080582405804004520020031140a1107024006c03620a0407250f5600300444e06070b04510919001d00d0780f444040c0304250702c055000345e08020b01620952424014206141c2003401c3c0c03000300d0300143c20000c21a0540d103010400400500b0340f80f0055458a40790040c01e81178036089504640402c0d03141c0c54010300c982d0301823050070004d04c8064102543c43c075840900500d02d82c480342c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 730518183 1250 730516933 730516939
    0x6051b040e1302061810032c1f0510050f0306040f030302160302061b0408030a110a17030901050906130605090a0804030b04030f020303060127051513050603040b040b07020c06070c05 80
    0x701459070740c244a4042da00f01d500000090031000044100e061b03185d456800c5d841d000c60b01c140b102150701c100d005818003540c039107109d03000200d03410100340a5010b4580c0c1e42c0814405c68281128000310350b00400c0d1144c006074441e58015030071a0b0b6160960103030060200003c0c1c040c010b45e18007001e250300811100d100307100d0382c1c88151002d4100f03040004203001c1ca0042e6802d030343c01400428078050145e02c079010f5121703055040781c10b002e44c2c1d50341d28040d07084803a40a12402202009003c500300d0709000b025004204007015040601c1c107022003591800701d103480a07110a0311203000c113010000c180704a804c41900f008a86a56a440382041d10540d40d043d034040300024404028088114408015240a204169940e16520300c06e00460075880c0c200201c42c000800741c8807800110350b0740b00c021008104c00c9040c0c0b225103480d10400103c01c400120751002d40142801c00401000400318040301c1c2c0d00c580c0c401800d05503501c614004920b4402c050717900a410100019456090244415aa100300e800417 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 730519433 1250 730518183 730518199
    0x60f0901110105011a0a03020706410c130801060e040b070201050403050702040e0102163507020405180a0507050901170a2a090906051b040e13020618 66
    0x310001d42210424407401c0e614451500c40c4003100341d07481d0b0091808500520b0b015082804548801341107d480c0c40c00d000e0104035501c3c41a20881280140c4001ca2400b08003183e80140101d4140c194901d00800b000d5910100284010340c2c0c00006402d03034040c0c12550004c21100d41c940c213001d038081e04296810344510702070300300040820f4414000c1d28852603050341d629003480540d030300380000303031429810390704d800e5400707002c1a403822140e030074940c5025009070102400000e180c5541c080b10780c0700c02020f04413010012000456007a801f82114211581558002820358600072550700340d146c8004002000d0003402004014003400141c0340b81950320860340c2c00496642d40290300c0c20203461510400d0315801c00c4c00c280c00032440c000c2e4500c0f103003d90320b0862503c150180481c9203c0180300e0b000b141c01555911049000d11903035102d660381c4001e40c60740080c2085440c3c1c0140c91140200c1c46008010024480042d074410303c041102c100c0c071a40079000d40d4545014032602e403108460300008a0180e000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 730520683 1250 730519433 730519457
    0x1050a0207033c03020d0504050606130209060301150302220e061225081915020705030f070203070506070b04030e15071115030718141c020d02060f0901 67
    0x14034000a101c02c0c44910080c003a071880304003c80c440000091902c06041d420312017107004103158007426205503c0384000d48110303d00300007008042d4840c0d01882d5102841805440b0300394a17a071b02241e054802603030490466001c0403101b20040d00c0760485840696030102c61481f041e40c02607030800140d4051002ca0b03030007940c80005100e000040f0041e084055070000c80d0410072071820440003942003140000e801203c9407902d5030103190000754519a00401102040070003031180d80c070382c1c4c001c161404070001d40c504601a1540340e505d010310f60807236010340000928002150360820130380c00201806050b40e0703100c2000e820320030200c543c1240e00360b000c10341e0b181d5591010301c2d207140b90150b1400b0f6480841e050400035181e8401040d60503510380d4110140080210b88440f0001c051440354040303941c3c80b5190880d50b4281590504150b0000d041c2464800102010380c0c0c95031220b0780c1e1202d401c14205c01b20207843c000945601e80e98000a50010710004188218460307890040411207000e8a4442003c20307 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 730521933 1250 730520683 730520717
    0x61f141906091d0415180209010815100e0403050c0f0a060207060c0c021f0c1a070f0509030304090c120914010627020c150115110f0c06130801050a020703 68
    0x104440080083c9103850f00302150505c20341c40318800c0010f1201d1011101116030100c0c1c41410280c0250000c2c1c0e00c020b48200d46940b181d204580e05c200d0728810399640c240b600d04c40400110014200038140b00340403415240b295030270082100880911003c0b5a8000c036107040c80402035022000603145581000e00d4080054010302c0042e03003c0e64050010321280b84d1843c99a46000005c142142c1009400031030a0007240c03c4800d4000c0c2804941051a003070309013117002a01c0740301640d445801b80a41030041c0c0340140d802105460031a25030843c00f00c2e103400c180000b210422099117800c0d5100b45030158607024404600481075102003543c00800c0195203480c903120311082c0b09840d0041d1a8800d554450103c80d4075005000c80424000407a143c1c140a91142c510b0280241c100c1704020355880400380d075030341d4411241d07038410846001900680984030042a15401c2c2000441d0052100182e035100803c00e40c240d0000515481008000609242e21b400d4007075405a0001d0340002c8544003070000c40d803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 730523183 1250 730521933 730521989
    0xf030c060e0901050f132903060412080a0e030721050f0d0905160305011b05120f060609040606120b0402040e0106230d02090102061f14190609 63
    0x40070090090038107030310b00402c12504554039120990841c00e01038042c850100c5031300071080b541c0416219a00d00b009814040f203542c00401c00d0b600e00c240c1c403440900010620304c034102e8200d04c0491400078401d075500d11b02c103c050000c600005150f4840021700000380700c841407864080c00c1d01c00e00d02144406803150700b10383d203000701c96880c000b0701020041108008019031008103500e00caa02981c000754030841d00e0800c0c0004c2940155426519007290203009600302d0f90500e00100d450500310b0a059034103070303406282c441c000e006041c19a007860200c4e503113580d5607080d40c15000008106111141d00c4030801072020040840740d10000c1d0400f1100000d40c0f8141c000c1d101961002844840c0c0c5a10b440c81c2254241d60b0134448520803400c05149104620720f507001401c000c3d01c98100540d03541281400240380c018000c02240d800070410751360750711080b0700d03004410403151500000410304140800003400d000c02c10302c1140e004080b80b400041c02070341240c030307207000ca40034404040803148495250903101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 730524433 1250 730523183 730523207
    0x411120a140103110108060f0a090e0f010e0f0d05030f061002010e16050102010506030a0b220203030708070b0f1014190602150108060f24041e15050f04091b0f030c06 73
    0x3000e40c227502803107004c02c00c0d4041c90f031041e9003a084070341d42c801110704c0714215001350340c03848401c2d000840c0281443c14208180c40b5007103d02e28141d85149001c42540319914000791149200c2d07481c098401e004a8800d421012140d540802900c3c40280b0307045a01c400c22486201c1d0074055428080090a10310b00031400001030741d0403000c0c011490380d6084400007000752840304603033544100c41b902000b503101000600303041480b4030111070351244941862000760b6401494510502502c20401440b1a1480500c008860160301c1d0b082d04e822902c400135482c2481c0030a000c8582010110000c0c82a41c0060240c40e01c00429641e5a050798031a07640c5900c1c2d12040b503541403409082e4003c5018003410b00744408000f00f120710524401400d0700005010b0714000070a00a122824a403003070360310000d0341715040080541c0740b0020759951600010481c107034000040644a02c2d030b9440c20034140310401104000b211000a2640c00c2c80b601c03020b4004032648580425034888a1042d0041020b600a84100c224 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 730525683 1250 730524433 730524439
    0xb031f03080313030c0b2a03060f090603011d0c2404031e06050f0f060d02030a0210091d04061406010e0d050106170c0f0411120a140103110108060f 65
    0x6940c0d40c3d642c038200c401c0b81000c0200c042090420842000c5191b941d100350040e2640b0041c03000314100c00c5602d03012030f0390240a100489808005105090341c84070218601200140c3d00800c50f95030b19400613004207143c0e49680301240081d00301070319210f0040303680002d0307002c111034801840260882d076005040203800c01e2001488208018400700d142010740d25401c07000040340c400010503030755505081d1841914020701ca4010341c014808211042d14509902070010380781c030980707042c160b00000d5881d403150348017170b014070b60850304451004c0c86950308001070244070510070544100d030100a1100501200d090750b075580f4000061080410a220b074a0040030305035181c40c11403d143c0204501030501503422141503695080c0080c1208a50548654504881300030f030208801c54800d100e040d000038000e10384154a8049000750f03c0e9401016030701e40107046c1102e10030641d01c02030558010810109060340a101c4a000041000b0004020364400036081c2d9a00c17a168481009001c0c10a051206030340d4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 730526933 1250 730525683 730525687
    0x31e1e2f01240b09211c02030c070306020306040e0706120612021813120e090609010807060f0e130c2303060d050a14060718060519180b031f0308 64
    0x9103401d4102030703c281c000c002c00b0700c1050302000480ca011040d1002c803182d4960808922020501c86d40925601e43d600035001071440c003a40300c1d00c542c3e01d52209000090550758040b02203880c1d501e0b168402c2c0c0f4806030100444035490380f01e03000a826601003140c80807000d4100b031404142c100d011154111200da0182050310001100c00101111290040c0030b0512219090004004035529039149803940502d511000d1440300f4003020b2200e10f140c0140003500940310040100250000014880102c0c2c400380303010540d40c6950b200c12940c7d80100c8003aa079200100c1c00380300d2030160495124980c1a00c081d140c600c0b00710582500315840d2040c646a1011070902400080c20f04c1c1042c0c0001c1000910407015542020300036a45c506101c005c0c03441c0c650b010342c440400c110640350400c0400307d03446034545220200c40d00e030078802010781c80341680d407803810351124222860341c5000d0390950602860100010081503265512030500d904215611407066804405051741c19481355401c1d415240c008030f07054 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 730528183 1250 730526933 730526939
    0x2401020a02010f0e150315040228020f12030106260601030b151303060e0610030809010903061812030605010909180b01080a031e1e2f0124 61
    0x1480090a080c5048244a02c031402010290f07140700205400720400c0f140c5c26240d0600031015580c0244250020740100c1c410880070b0021010106642c03d1414000b202d003005141c0840c00701d0138424800309042680c4218070b0340001c00d405030350245050705c441da9240200d400c640040d00710751031304542c030840080c059000860301552198004060240d8050400c2c00c1030070051710110100d81c4408190045664000d4050003084103901590030301452a04c02002c0904000b02d28041c2ca410b180b10080c000e40300000c0002445c0d0055140000541d0042410403404280c8800040c035011070240c00c03603076068078a08403001e00d03000788106402c4c0c0300103a56400640c4c0c2003d096500034075807004118090182c442070b990014404001c0740e030107800e152010304142c06d854900074000c1d51001505124900e0258100c00c0c85507400f50200d0000c4444100d02c0c0100c4d241c0b0300d4180c41c586000c65611081606003c203045a001c4011002d00008410900801218007041030318001945000406805194000020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 730529433 1250 730528183 730528187
    0x11040b0703390209060118170109020405010801090506061905060d020f0309031308010c1b0303062c100509040f03031b0c1506050609060a020c06040e2401020a0201 72
    0x1809600103580c50010080c10b003070360b005140c0d0464110407a0400907100c148003142040050650800e10a09000d040d264055031210b5120ba294007816030101d800c545111030030102500700b00491600a00308000c02d5840d20741c031030b001e00280901070320203228400c02f007840ca060070902084503110980c500c499060925042048a6100515680e400e58080c0b1045090041c86001503015000080c000d50766840c00000c03103082c002580e845840b050b45483d00712000340e03412000440100090300c0c05a680a0164681034008100b1a0460510b5204a00b101d0403003601c9020111440c0d801151b2004455840200c1c070180381070203024113504580100045400100c0104005901300e1181c140418090000741c8098000360707000142500107640c41d5405c1041c8419005014424038160405000c12418080031903c0c621036414040c0c0250000240489140d2090040058584d0002c0c030b115581d6903210f4030224454019a0481500c00030b0449907124266102c00d003040032681a0042c2041110503001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 730530683 1250 730529433 730529447
    0x504020f18060f03031c06080d0e0f0d080c060901050a0e0f0a140f060901020307090806040b01061b020618040c1b0813050907030c0e0a03110f1c0602070611040b0703 73
    0x80f0581500c000d1242507028001d00501c0d0001080005000404c41c4c5800c0707070356180051461a0354140030b452004200300e500c907983d11020160b4141e408680c0722105103401542c0e8820310300701202c84c1c0260018052402019080b041c000c40300f80e2024030444503000c0c026500c500b03004411081c150b200d80020300c00075a01c59505129140c060056400d0340e19180c2819041c080110340e4180965400003c0250440d08160024017030081003008101c149065035070a443c000040c014201440300600c1422941503400802a1005030b02802c195210f41e1703410b804191003041d10b040345105a090800c26844a0700c252140b00f4600704c00e480c02104181c05446113207840e407100302140440d004012011903140c80700584039020b600507582c006144100d01c0d000403c110250040a032051004c25400c20200d560b070144407440d80c1080707a5400c10f200030700340094041501042d01c0c1e6550601d154200c014840d05601400794a0b024210a00520702803010550b1188154052602a46018881e10300401e00c1840 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 730531933 1250 730530683 730530709
    0xb060f0409110c030a181208090d020f0d060501242a0b0115020607082404060503011104090e0705060a030203090a14010c3507021207060504020f1806 66
    0x89168580403c0c2000182590b2251450501050395200310700101110400e0100c020f006045410159202c255505c0c00c440c81040e000038401c180320a5040155910010311151241c03008008031040740f02850800054402481407081c091000782f0380c0d0100d40c401c22068086212156030340c50b550a00310304103c50383c0c0742d05010082c0441c1542010f800140e040a260744c040e2686038241e0349920304002c3d0007860100002d000da4100800780c001c0c400c0c0f11001c3c035a0508040b40da002d036044020100e070041001000540d1000758190308251001c04240c41000003041074400e450414480444000e45a03a5680908c3c0301e04e0f9040312080003002800c91099028682100c4c40006441c111400340d194212010303404003d00d0130310f964030030707070205540d0b001440003005100701149075410103040c62040c07a030035a0300f4004252a03414000084c5170b607842840003054100341d11260176160841c81c01d06030300030803084904070300401803404400501e2503e11840e0450441d0f110551a0f00c0d81e80c0b40900050303840b261 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 730533183 1250 730531933 730531961
    0x6080105060415030b43172205030307050c0f160e06040e010504051b01080f07050a1404140a061b1b1a09030c09130605060f0d0b07030b060f0409 64
    0x44880580410250070320258245044116000450240c01c1240e900b02d01035906c00502610320702003064070101d9440141d12480e100ca01e00310799038502c1090035240c40492001809808000700f04480e1a81200c003900b10f802c00c10045a248800147c50f143d82d94100e4400442c02c250b06407410003a0442944032981d0000c005400480c401e0040e040d04d900791350050740c04403413035000107020075610601c42018850041007441d05c84100d05040c94110100040540754000b04140003455649240c051148a6520300904803520365490355484030000d90700302c1591251103440114400180d86200c0ca4020004140c2c1003081c1107020300230b5541e003d000800d0300c41c00da40c200403c200001d041c00d0542010481503090194140d403504020101420300d1400f896a61242c0300090a01c204072103072030008444942e0206e0002515141c1d00000b81503c3c2e03607811613550043d1070303460311400c001400041d54010303000c64806010b40140c10301004200d010f903100d0f1485a140c180810450f011860300a408864400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 730534433 1250 730533183 730533211
    0xc030d06032111150414030705060106110c130c0207030b010b04032f220c03020c0610030b040b130209010314150c09060d0f15030b01060539070906080105060415030b 73
    0x46d0303280d03e080d0342046500345c581e03401007001004015045800e6400502c0c07004040c0070280f25440025005603011040e00568a0750381c000840310030300820a0700090358102514204ca981c1d18100300031560301c0b500044400c4e81c010909003481d194040389201c0070880028052022566a80038412018030541a05901d0680546a805072901c1d03885a0340c0c03800f516640260741d6100f41210300e0719081c0c0c0034180282ca4190158100040391745441c1584c1c009078800600f2026880d50300040d102103845c4140a03601042810000040059a0350f0001020020100ba81e104061043d1100c003503980803034044003450010024450640b0b003190080c04c804242e48000036040d9122120300c0200c0f0402070615140c80541d26044c0140a0008206401401c0903c0c11a01d411031220010a0800f2507821a40028a4140c00a40c2800b0f179152400c60619100084480c01d41c2d580140a0145c030322881410010752924021030700e9070505003c0c1c400c00c1c074180c0358121207403459079407247c04070100100340002c0b100701 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 730535683 1250 730534433 730534463
    0x3140a170903090109050f101b02031e1b0918070803031e010803040b0f0f07210f0e06072d0606030c05010e03060c0c030d060321111504 60
    0x890503294020304010005640700e03214903001400c0c2c48869002248500c0314280540c000d9994081c00140c0d604262800e050701c90420701c0201810001d0440003036041c040c0308613115240c060804541400c1419a088990402020302d612400352411407189404c041c0f09000203e01c480c0c2c1204107001020100300f160303031a9549800503421500700303440814410000200e01c0c0d01c40d0395080152130141a4200186182c0391070108004510b01c0740a0031051245004252908241c40003001c2d101102e40280f40302d184500d01040c44510699907040d02004104250007191156114412100c2062000350a42d0311389034603515902801090f03070001d01e17840303008181445445209009500340181c0720b402c000c02d02c90b0552074a900d40000540120381003100c2e21040707044503035001842c1500b0400d6140456070368003003880420306611400149030100f1f030070908000308020340d4890f0b461039000b51130600b80c440100c104007120944102c0001c2d03907055003c9803600c0c0b45d0345030074213506030042e01c03d802800c0c40d904 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 730536933 1250 730535683 730535717
    0x305061f260c0406111b01180302060a080906010b0408100b0d0819080112050c040b0102071208120f060307090e030d0603140d110a08070f06111e040303140a 69
    0xa021202c4080d9500081410070155802294503200c17660004003400f036400d00c03ca0200b61a00752483c2c4e07581003094842940e404800b030790b01d102c0091900a094a0b60750814040b010300f100c14140c43c003d00511a0350000501035103000190b9059440070780c0030b441c2d01505003000d08045d04030202d2250744102003424060020311510010024040c81155000320303911217400283c0601c0050340827154451581d0752038000102e0101d4950301d2400200c50009a00320440b00407440c005460b0040842c901001d840e040912600300054404810425020040ca643e521640142150140d4241390554032100382400b850503503410520403011040200d07418104940351a0041d81d06540c82550484202c181b01c401c410307401d020024100d0340d1828200c1c05103000c540380d80d585885210f000b8001c140c01292035401c00c000c190291a40f15001281440804010320541900754406260260047c0c407001d00c0a0301c110052007079404403605501d4030040080700c50b07603054281e0301c003415807800c0045803044504514 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 730538183 1250 730536933 730537007
    0x30c03071401051e0403050c070b0d0b090112082704020304060617071a0c01020c0a060e0615031002090103020918150301150501211103070305061f 65
    0x903001e10011544032600c8014107007143c001030203100001c0b40d0b20050302124190903003040d410a03490325040359102032100295040031810342016024143c0002c220203403400c0758203c2d4101007412034101103503980e262100b02c4405245440280100d03028401c102c81501d1190301110b120036030002038014894130000050072644111003c84020b9581d540a100710f1190355180001b03e4030513402410140d0810070041161034600740f0a2007404000218118003100c01e40540d080301282c0c608031046848145896001340899140440c5e107445908000b03444200d001d83c0404a03c00007501404003020b950714424042d40c01a0111414160200070b140000c3d190100c20003030200801c8008200c1d0708000d480500502c500390b502902c030740c0c1880d04054521160003d10303021070b0000d081c840358444407403080000d00c4811500714012070b1300d400e1f020f0505c0203450001354801c00d11170340c2c100700c15941c000800020f0400d505100750910780c16548490140e02902c50000d10b43c02c0e8038040d100c40920751a01d50086 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 730539433 1250 730538183 730538197
    0x30a1118040f1a070206220b0c0406020d0203070c05090703021b1c0e0f0f360c040627051002071517191103070302130905060a060c05030c03 62
    0x421075000220705003d601070303c0700240125050440303200d082c560402035640001410001e003181e408000c1d0041224403040751154240c0c4130325445040d02c4c1c944030107803030381d0414491007001d4010501c00002c102d00c040300320380c20254442d00391080a410300301070000e5120028440c4050550800c06540310802c84840703500784402034001000324132290078280b440d40b252050400240700113584404100d03a10001200301a0708103580c60721240402200040008001070084c680711040640c0116603d04070000101d400e051440d4882025180c0b41d180c1d10645c0300342e02c0b40c0c000284144155107104120000000c01456030400c0100c50b254507100054001030190343e040e0050b13030080c0300401c20f0040f00c44d5500c0c24400386082401c2c2880400080e0b20483c20024030b40400000b12020700b4541c4502d542c406040205002550f944a240903080900294030590701301200725884040024282c450b801210305c101c0024222041321881c0000c15120000044001ca4103404240b00c84030b5141d804001034200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 730540683 1250 730539433 730539443
    0x60f180501140106270317031b070305040b033304050a06030f031202120f0403120903021c020c04050a270f020111010e01110a1409030a111804 63
    0x142040c500a030840714064404101c441200e030041010300d4000da42011400c00000c40340d14409821848011012416000113020100241c0a10f403107008860103984162030504a14822070360303001c40c202e00703805141402030006178100300920466202002070754000b045d000305100c507203143d182e1200007201103044034a0305011410a18209280500581350003000006040042c0e60031602c03806440c00e003000e4041c00f44400c003070b88600700904607070480790040302c1c103003030301e2900c0c1000000c110307403007409503030943c0002c2d0f04161307848083c0b8580c800e81045d030754140c001740b110b600e0790411030340800c54800040d000d501842c80e10340c085031224040c85205811110380000d00d09084020140c81391a10a01d400241c0d140610030340001e804d14002c9405260242007410404051241207400341030300200c80189542400307003503018002c148014050154260710b8000c6603072402141c00d041c602807611080c2d4035604c25060f10000c201280355140c194a005802c0e040041c10301111003811800999080b20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 730541933 1250 730540683 730540721
    0x6060f240c0d030911011803140714090708070f0216090b03120f0901030b06090315060f0316030809060f0f190801030312050603010f0606020a020a080622060f 70
    0xe4184030a201c070048440705800d041045134202d803076a43c50b0080d500d440300d0511045448000c003600d50a280c85000b56070100e081220704000704406601c503505031003607038254085940301104600d00150342038810b03078040da600c400c103a59200e011210110a0a8803906501810301d2184030b020440e1080c501401503500c3c040b0340702d4505010316103003164502d000545200107001800c030003400e05040311212482441c0215900580500254080c41001c50440e454807604000c20305009244041c1442058111068201c0038010070915407280c2c0242412440170304d44240034400510030341c3c0680000000039010500348401181c85400c1c80c2c1c01400001c00b0101c7c041002101c0c400d50007600303008003c0c58980700125502d140d4024200c0780c055426110666103075000640e0b01c2d01d0035802181b5007107004071b080c801150f4844002c1d454214000060b07005003004000460500300001da400d000b048000034028088003942440700c0c4007803240b8800c40300d0f41e86844d1036804034100c9024504d60b82a012410b04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 730543183 1250 730541933 730541947
    0x1128080601060906090e07090f03060f060f0f09090609020603011e0501023d1514062b0b0315070824060d0905061008060f060306060f24 60
    0x28a0030105030b01c840300300002c00f0800d1000582c04541c1c001268401c004060094071114401d46c1c1d0301100b0307002520480e00c611000814000140c201e5001c118901c4000c00169442c0e441c4102038a80501800ca4070b1040d122041180014580c00421307814083c0c1d1b40010b5050456001400a0f80b00781c3c4040d048030f4800c041e04410141c0749900b18001c0c04240000e001d012250a84540c200220908510000d040740d403440d48141d608507903442d02c04c4400c4c40304001e41ca05800c0034000300d90b02801010748045020039101000d052071000c44c1c44055a400461200c904090000342c41428490024405651202c941041c0303505e04220b0306288010360769440c8010701c0c003498000e01c040002002488141c5441040307400c544a41024000c0c4410190b034503640d5070550900001c090401040700070b000340300d00742c00c1100041c840b01c0b000d01030750300620070b40b0500d481d41506800740d100180d41c51603150700030001180561030141c0c841080b043e0701030100307002505c00004e00802c0f094001120031022400048075 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 730544433 1250 730543183 730543199
    0x1e0310050a0e0f0a09110a08030a0f021603020405060a031e02150304020d0305090607170a20060a1e020c0c0a0510090e150915030120071128 62
    0x80c0c00b410880c11600b01500e4004100701c94140c018019680942c0d0b120b03002e0003817028005484c14454400740040d25101d54802241d80d496102030004000541c098440d015070500c0070903850300152092282d9511310341980c082000620024140315031000d45094000001100343c4041140c0c4400380c6400c030401c070070500612012082e0001022002c003c100100070050341c48400740608103805140450b2580032510203d202c0780310307221000c0d00d042c0e2004c40510450300d170300e8014031641034599a0349043d0010a08003685002c411003a01c0031540001c80090801ca0042d0700000cfc5414080f0810f00c3c40340400c0141d20100e0b40a408002840d801c840301214182c24032030494001000c045e50300c10515092002c0090031714000707008408040403480d0200c2e02440d0204d01c0e400340c40800404096081c100040307101e0f130181155192500a5003051a8204200c2c106000f4074658031a0508241c5032403000d56541c1081c0803c0310000358040c0c814a080d59403082078596141d4012125440250520b00300004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 730545683 1250 730544433 730544449
    0x281202030a0f08160e0f12160902030118050a1815050f0603030d0f09051c021513060b030703080a090302030c0604050d0311010b0d060507030b0108010312051e031005 73
    0x2154184554042440446141d68042d100d504d007603841c0291580e6407002c0000c42070610320f001158024440107007260304040c0880c0f044004e000c20200d2920250340c41c40d460003640400d1003411b5040381101e81c02401ea40d41c0d07801c50390b0301c40104032001504581e03883c94ac24220720801025140b64002c81c1d0590007004c2c840c40340030b40088a800c0189264600705000136540d100b80b07064210b14988442c0c0c040c03441003080d00030110079030b48881514080c061b100519120307582da44440c03100610618070f00708044130701d98801e68001c680c02d02c3e403084052525110100a06506882c45800d44a203400000111f40c0c004040c0608a01c981c0d109402e461540c0105480c080d44442c45501c9a40d080104011903510301245207003242c1d0606080c41c1d190403e40c4c101e03004100101003650007041d6002d08000300f00c0d8a43c080d5110300702e46d444c100704001c2c0c40001190300800c2400000e2085008114481440e0b0082028282c0440780300c0c4041080e0302480c0003a00c0f41d82041e100c03c1001c40101809001c64030340122 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 730546933 1250 730545683 730545707
    0x27060e030c041505010e01030608010c08070f0e1509031e01020901020705030606130506130e01020306210d1112040b0403030206061c02060a0e1c110a050102281202030a 74
    0x20b0512040399600821600da2003d4441d1906102d50000300070856402a04200000c040c0745d0001c015901042d080984481d40c21250840025184005681d0306401000b03200ca010402a00e400c8080b422000700c410264050091268035224908205005145154900340b25076100000940c031105400b002a1910a143d040300340b0030741201d000c02c19543c446001d1590700c2b0000490200f616164140840e40c88800301c02503c880902f410348144208405400a501803801a100c0ca404646e00002c0f50001840c0e83c0ba94841c0c41d041100c001864030b00c181500d0100c0540001940c00114088030b6038600340e80b00303900440748042b001c10200140742e018007480da407100040e168100502ca68182c880503092141d02d00034851607000c0b40d50702e1700ca4484d0003100240d00014082601c0d00170314140b608901e10610f813040703d4180122005080360300b0b04259000840e00107070020428034552504050741c00030301c50440c0c1043c84283c6a4580450210f03400039041d90169009165a2115000b0051003907080746 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 730548183 1250 730546933 730546939
    0x50705180906040f1a0108101d060612010909150204050d030305061215061305010b031f050a03030c120212160228030302060106050f0405060d090803280b030c0127060e030c 76
    0x3200c01c0042710a031040c0c40f441c1400d820b41d84507582d034440c0700244281c059002c103400451030300d40010030001d51552041840c507005509ca21a0001c02e401d04105a2080f0300602d0b170020480d064080000340240c01c40798000100401210314005910b600510f1b01e01c0e070489148045010300309100741820a0f6012400c10368410006024540c103000a19401344800b50400c0f1032041e0302c1c43ea040c049040300c03c2000c05443e0080c90034104550302d0500030035519601d0000c2c2c46c0c040708106c01001c0c2900005061100c00030038142e0701c1c1000a100b4104a0400044a040c3c1e0040d00f900c1c4c202e010502445142d03041071107480c0c0c0c0b001d1210304600f0002d150200580000041c090100082c2541500c00c03000e440071a0030454030725a80d0300c01800131502501d5803610003800c01d0780201c18850801020189240c4408103614604000d04200e090720040e5034030728a1140c0c150704804d42043c0c1d9548903481075242096844003111aa100385005c9040e00000e5038440e0000034034200590b00300380760600006429400131 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 730549433 1250 730548183 730548211
    0x527030702010e1309080301090608010b030d020c240a020616111e0c040f06080c01020304050915010207080607020d080f0f01090b030f0106031104050705180906040f1a0108 76
    0x10703a0010f403090380a50310340303803107400202c551003028203581e08088078242c0d0040201e51a035a6852541c0b010f8091802400165428044160b2042c00c0000703000e10800344a45c020b1400d00c0060060010894000f0020460301403600c20000c40c2e0b240e1a80117005101e020f03070040020386058000c16100d02c05801c0d42808215400c0c68014400c44c00060009204c1e03808030580e21644c8850b1130b650302d0440c2421201d42c1050800d2400c0d5030003201036002c2d0701100c00c0c000c02c0c4d86105500500480e1030744940c0c014039030321410b0701d800b1444403039880410a0381d41206004460445072035000e042e00e804c40031180710b00180e00c05a001600c81e40e000d140030350032510208030032070181008650b0400905050040034403003643c5c0c0f440021956007c00c070103078800b00c0352402041629103e082c07101784040d540e0070150045091002284185126104a80c1c40307466815184840455240402c00444006045994429129042d690035141ca52103010101d030f1040800d108103183c80c0340090061040248103046e100a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 730550683 1250 730549433 730549447
    0xa0e15070b010f0f360e06100306061a1902030f04032402070305310e100608040f0b0c07060203011206060e0c091219030215220b130501052703 63
    0x200c4910000080324102e55036081c0d103032905d000003400c860000300600d1082d00c0a00c08041003000220080d24000c0105020709615502c85461100b260401854000800c2040c0c50b024108a44964985d03075041c41501e00d469241001020541c0180d0000e49510740e10740b070315605540b61200705050701081880b086d030802000ba20090101d0081c1da0f070980101c2d4803c0c6004003200b207005020100c003d40c01200452085c0ca5040f1048500c13012076110180546d0000c02003100c90040140a02c515805030f610182c000ea00e507903540d04404054024441c0e40c009011000c0020018009035000c0d01158442c0b00c101c00060915205648803940320a0840ea1058140248038000c0700484070f07010b0058545541c02507120b0308039440d10105c01c2c032140c140200340d410304042550109040500c8600040e20000503107074404460925034001401024a885140e66940052515210640c0c008a1081032a046101ca9100c3c0c0d425900c1c1110a095403a200d0b1240c110f607101d07004202451a0041d000840c18607003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 730551933 1250 730550683 730550729
    0x1a01060f020706260907090e01090c050a05032a1c050c0d03230706090602030603060c030c04141c06020301051903020940030f02030a0e15070b010f0f 66
    0x20700401d0242d4940c44c010002d80c2c034402c02c001e0030005000c0d40004001001210440600034005040100c42c0f041049000083c5031078100302020940d04000d01405094402d141ca080c07102160310418610101d83e10400f040d9a603561440a840d1003e0381d400a210b041d091070316604148024441500c18074107102d6000100e135011b204103070030a4240e80f292400c3c0000030000c0c0001c1c000e541000340030901700803118080001350340107140683d0080c0d0403514180c44126204525000c00c4a40c248006401e00041010000d9451009000340c000b074070902d46d03804454011000600000001e680203a0000700400450130b100c8609003800603580e60314032850741141e0020701003580240c62029598024080c5403060484403000c00c1e40381e080a00300d0702271030301d6070f050103018059107000c25004206900c1030442c00a0001c022122500641c6c1c4d109812400c140d4100925000044e14043e101c0c1b0007400311900007000031402901034501484000c10242c0740028400c480e084640281020401007280d00c09c10107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 730553183 1250 730551933 730551977
    0x18040518070324020c060601050f0d0f14010b0a02030f13051801030311030a050702040b0307170106030c050105030c031b0c01060f0806070f0516170a120e06090c010c1a01060f020706 80
    0x1f140c240303803003581c80c0c08503990348075a0b004449006194525150880f018070002e6403041e01c035590020440601c0741e0782c8048086076802084840805600304005030010320300d4a00041105030311950524804c5900c40c0041103588880814001c2403c00c02030050080c550002c600d6801440c1c840d004516042e9103100042842c010304000138011900c4000300c40c0e40f0b58003070250303030040c141d4800c4c42441c04c0040100d540c0030f42910320050f06e2582c0401c402244951144003283c2c4210300c0f017080c8500d191141c4807103896441c1c2d01c20a1450f4110180b20481c000751084c024480140781c03810303100c24003900382400f8606044001c4d1540c0b041c004404503071001250004240e0f000ea08004958072144c00841c10240d6403030aa00c85142141480014685551604040c0715614466510400c101001c01001c0e621b61341c03c41503402c0c50b03071a84a2801041c15606c40d401c2c2440b1244100c080703040083e4280180d1a2800003a001080400c01910032404a15810480e48006054a2034000c0c40d07420b050419012407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 730554433 1250 730553183 730553191
    0xf060807050f04051b0f210403080f0405070510111506030a120c1506060206100b031303031103070201090203060a020a1b0813030b190218040518070324020c06 70
    0x14540f03503000034483d845e01c000302d03040e400d0204c0320540c1c0d030b083c0074185142c03241e005000070000c0c2d050307085071070740e280104034032861159916407264022525101081d0944141c0104116101c1c4900d07000890079032580a071109181425486001800c40c07000311860822140095504401e08078004202d140d41d0000b920401d0943c1244111220707071b080017030844605103205009010926074912040e0450742e0b039444001196100da00340c1d025529811b0520b40da890642c0b041103ca10320920220b50403441c6075020080d0203100703040008040e103c2c107441c841250011100b850240c0d44d18181a015804c2c00c4c400942c2c0000541c01c2146443c000308006801c4240340d180e207110b4078105252040c10001d0000490b09160000c400d100d20a590300d10b802102c00b081162882e5245d4031008104c0c140c02124020740d803100f861100d0b2488442101404d00005182c0240b6500007424103585041c0001402d00400000d1805980c85c1c140b005210a5610a0070008102d10659688100070415140c6004680c00c1c0e08 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 730555683 1250 730554433 730554439
    0x30303130515070f0f020102090a05370501200709090305070b0405060a2d091b03031106131a0c130609030213090b010303030b031c030f060807050f 65
    0xe01600c0c0d0401614151000030081038030701103030041c00302c410741050401c02c02c40001c0e039403905a120400320403802d0340186030140750408900401800103103001510724030240d65080c1824070381e1000c60a596030300c4281540141e02c00400304400d100b19680892807800140c90b501c00c80717280c01c107007800c2c2c103a442c1254442e180b0090b40d1440e4000800d403081c02107030f1501d0f802c00aa140c05041030f0403c0394848c002078900e2202245070041009132101c02241601c41c20900c4511840403031505a00303003010380610501102c064601c50b42c860f524030791280c030460245029659039688a07030404c1c80c151501030701504103941500c1301e004a200203200c0c43e01020a0800503003458506d80c44803201c0541da800f640380341c1419114068030114107540e2104901084030b00854014031003502c4c44100c03408480e501000070705007100490040c4013082c081e81000c030094101404440e01021222601c411001404011200003500da601074504030700fa601421001e01051405042c0403803401c0e0000300c0d181001004940 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 730556933 1250 730555683 730555711
    0x260f03070c021002030315010801082517031818070f02100513171206090c040b0f030712060509072001060b0a0f020706020a060b060c070e01091109030303 68
    0x303861080d52000700ca1540600000365880d03042a02944907001111000d40d05035070f0345da01c4251584a40b600c141242c0310040641550fa060700044803049100c41c110107030007101c0740d00000c3c0300810182d903031144852800186440e030400540211004000c20007852003599100700c20169492594807481e00403026080000054000b01001ea0620343c036903d1540d88a498401001000c82699181c40312452003181030030f040c0440708418004a0040114801054400d0000950a0305080103015000030021117440c3c20140e03580318030b049660015501c450360202c04000e100302a0340290760b169480744000c0c0180801810040400c1c40f01c00c0082444003046841400b003013150442416081a00030244004c1c05002d80780c4000c41007a501a074541c10025800411001c400d900c0482c500f4140e8031564040e00860305c8648441c3c001e00004500f0650243c4200960351380390804104110050443d048440d01561402504500310385030110303c01c45800707080000010f00c0d500801101c0e80400c2d254a145 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 730558183 1250 730556933 730556941
    0x5030f1614180915030f01020f0405310b010908010911040f020702060409090b060d0f080306060408030a020c12010606050f1303140c041b05270307030609260f03 71
    0x50720680c02c0c0c1d41010380100c406014440200686202001a44416002c40300d131020301114a900300d11404c80750041c4500705000134401450302801900c22021b9034640ea4446450251100b81c810b1070900c880d1710100e540d4010403419503084403001000705200002003001c0845a116070444520303002149126542c0c81c00e12203442d8280f41c1c1580c8081360040e06a6445d1519110038030001c00280005032030ba240410300141d072030301c1d28141d0309003065030022206161100c0e44c0c1d82c0f103242c0d402c080d014980c8030406000100f4000f00810242a00240960003480b501c2041014801042e8804810a80c0b0340d040185c24410160000c04440140054200c01591031903815009003c945c4290001415682038101003c98010002202081078200b25030800030140480308960384602c8000910004c500d052200d240702480c035840d1007440c1c400400e81c8441e61200400041d04205864004070b40035a03650311503a00340a04c0c0a003000400415802410305510494643c1900d03004100817146090310000001d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 730559433 1250 730558183 730558207
    0x30d1d010f270b0d052208070f06020d0906090209161d040204080708150609070c0f0303090501181a1003150b040213080105060a06080601030b01021c05030f1614 71
    0xb40c01004840c20154880641c03c040d140a440182c511242d9032610720f039100c514070200f0342d4070a142d9602090403440d000070b0795902e41301001d00817000d0702d04940c240300d005c44121003030040144084c400e0310005200c0415104000030707824042d04040350800384c4000c0d1900e40703420030b85207a0070700c0c0c0c0745000c0080c00c01e4450008010384100e401108a0b80951100003545400c002240310301004102c4c0d1a40c55640d03680103005903103008941020001c1c00000064000c140100d0703850091134000e21380412a015540c483c2401d40c0c61a80a428411601d45840014800034090407081201e001c6008140d038180782400c0c042c3c000042c0806008012218841120249035174842c00188002078829502d82288011980003400d1030f124500d44c0d03500702000503500340740610680341900d030181c039403c0480d110600110024100c2451060651041c00a54079007000e04603400800382030310743c2e1003d03a00d107007410810600b004040c1113400f01c0382401d5180004c01e500210321014905012004603200e400c8040e034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 730560683 1250 730559433 730559507
    0x20606040b0a1e0612020a080606030406020c1b100504080c060a051c050109110901020a06020c0a0204050f04110109031e11040207030f021b061801030605030d1d010f 73
    0x80000500c1d105400720201510300c80a000c07901342e80c44040000d610480040c00341c1c03251103005030018811070300046151600c0c10146410034002e641c01814408142807135450040b10403000030a2a03118540008649009510f8181364032191411a007000c1c03409204a95030510b0512851140d04040345850b00130348104c0941705203010000e0b42200d004015120040104000c1c01104030550525002c0318a990b030f08000c8400140040e070081c903552906444190094000c00303100b0300c1c0b41c060f030044007016a03278a0280c40c0c0180d00c40000001c00b81045c0ca015800c0304a8200644d0500c03113100010004a913003d01d14481d0200101080c01d000409440e003000c8081b02d42005e103038443c0c8045005024140c0c824082c18451880360226100c507440309411029651285a0580e48803604008007148c06020f4417032022102c44c10704020804585480c002401d2080011000c400111006030040e00803c01340d02c455140301c002c0c02c125284034110343d00180040840748042c6066008441580c4c504d005200c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 730561933 1250 730560683 730560689
    0x9230403021501060801030b071d300c090a0c051b1006080c2805040b06040f121a0c0f030405070b0415030501140a15020709050103080c1c020606040b0a 67
    0x40082c4a82d03841c0c160241010300207000999484903124002210310380102d203078280c110050031752610200000c50030042c080c500d0303042d412554810107500310b240c9200c48141850020f4100d02500004a000c2c0a01c481076100070b0850004500704040144926040011500c0501c1c0c0380c070500403000704800000b40f400c041e101c00307078a00d00c0c541040045d035101c002c100c0c14442081207070203104400c81d00808400381d000e0085454003441048200b00802d1415034449419401c01612440c18a50740752451807428000d0352140e0921007803180e001040084001188881080840d80100305082c4030a0b500910301a584480f8001c07030000000c103003400f00030082d9000801c0800000c0e5078580e25140e200145102c00448580402e007803200100d44481503455040242d10060300c1000344074540540d0310a0290b011072200d0a5000380715002c1691041030190b2030186002e9180c0e1551190515051840c01c82e801c0c0880b005d04c42c41e1580388a40c1c80e0701166041d007080d0700315004601002100c002408904040e8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 730563183 1250 730561933 730561963
    0x210090e04060b040509010b0901061821030f080f0a020c031e0c0f0c0d1b0b030103030309030801051c060e0309030604050d090503030703080a1d10150923040302 71
    0xd01004208011a04080070184081e281031140f5140d43c03070064203031590840090303400440b44c001807015500c11300d07848158070801c21a05a601e80e90741d941421008a403100091a000c1d410800340c149900040c8840102041e03151446451920369170301d00c0b007108082e18034a50142c001440e14900f00c000c0094948050341813004000e01403c142240b42c260780940500c04a50283c0c0b040406c8001011500c4c0c43c00c01006052011903030b60f10342e030b40e440120703007100c0c8546c03400b1010602140d000c8c030440140d40654400d0b00c0024030078030a410081c020f5101644594400d82c5001200380100740b940780003009066009078046106a04182018158050555582c0d0184500d401300014400b00203004070040c0c50071380b20110200e03100d0007455260320642c00080e021400210109a00c0180391f41b16400b800700071092801c07541a0802410304049a040c424500140c48d0048404400340140310500117100e10f00c1304000900044800c0386412039075040045561030303440d002806042c000d04c481d941c035034051 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 730564433 1250 730563183 730563209
    0xc0b0315011223041b1401021006051f09120803010e01060306061e090f030b040c0b03090a110414180c01020a030c021c05031b16030c03021009 63
    0x4295034400c110114102240001c0c0d0520940401c00d00600c10410500941040c242030350601d664030094045000e071044584d180c20b1010600314900d0b200c002e401400d4200c28400c0d088000c40002444d00207801c41410201c3d01c2d0060400c0300e45d5a1841c68a0008042080600703084030000c030903580c4c54804d40c4100f02980241c403680d02000710400085040e5140d0070b213007291503602c4e1842242100c409000d02c0c00801d980035501c207528172103000200380c0ea050900d040e001d003d403101c103103428000c02c50f4011aa450461001c0c0b0007004282d8a01c6c00142c01590002130542c07424070701c0ca0703558008504015182c40c5256000c41d06a48542d0008480354407040341d48081c50903d55265047c45803a9407800d180c1d4052108010340961000ca6011109901551344501c245015000c002d207544100c0303000c80b0480c04411080b0300042003800a411907504102ca8081131070070103052141007a1400210048400d44010b0920002c0c1022049006036601968000c1040e03070307103080503141004a500145481084 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 730565683 1250 730564433 730564441
    0x606080109020a150504030b04080408010f0e10090210180f03030f020f010b0904021521070906080415021c1404120e0a05040b13090521070309120c0b03 67
    0x2054201c0c054080c425600c18521955600d038400e40c00e0784c104901d5000480411040000c035070b810343c42c141c1140c0500000b41ca881d80d52070b8210b00b1141510201a106a15207840525000b018010311292213a9100207002c2c00303006034009081201c4c14020700c0140000302114104984c0204506800b802c0d20ba09070a14071500c0c2c1c2409008429030075150001441200d62081307100d0f1040c011501846800f401c8144a52280d60070040103a0f1048803d085001c01400100d82045480104080c040280c01032215a4101804000c0c02141c180d04174500784002e050030f02c0001161130b400c80c188500c04060050f00e50001c50341201d810051b01042e0b414480c180000082c04440c025001030040c1d124828030034118100700c3e015962241d20401003a400340090f2030400003400d013604042c0a02c0700c002e00602e203525400c0215000c0312280e0106440d940c0c0b0182e03020311103101a01000f00d043d40d00c1701800e030070111543d5000745034002d0ba004418691030301d4111402046140500d00000d00b50000a107a100d02d8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 730566933 1250 730565683 730565699
    0xe1f110c01110d05011a0403020409030e0405151e0102060f100509041b150512071b080301090617030720060703081b0c0d05031e1602011b0c020f04090606 68
    0xf01d00d01e600c0e00d190400000d01c1800c0c2500d44906415800d07055030500d41341d502004020100000c0681c00c0c042000f442900380c0da994854240700d9800e84283c40340740c041c0b1b0005c1c4070b6400b00041005002444018000d11a60307000600d242d8000f41364442d4484969030f01c0c034400d01c4e02d03c055101540025030304d0f050204100241c0b007009030100b130100070007021584e0b03144d0509a100616607035102117902000642c40d6003444000306944089a402c00300c1008505403c400501528001c00751703080341c0003100502145d4014040e400040c0300c82507500c2a5501c2d100d0200b5160b2280780c5004100da1440c0484060b400b44002400e01d00f0f000041001d9160096410081d003943d00444018644030001319842101400381c20503140d100d40c5110051450100d070f80c50a407003d0384050121010402c01000950480742d412010502c6004d00d0706074003908511034100a400c0d5000b01e4406040c040d08510401055075001d81d4001c4540c2d012184c02c0d580c41c2c1440c3c0440d0041003240d074085c121504080c1c011550758 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 730568183 1250 730566933 730566937
    0x90c03150a05100f05060d060e1905010b120f040f0605100501020c030a03090b1305031c0f08060603071b021f0f090b0d2c070303030e1f110c0111 64
    0x38481060002e5034540c00440003980e054000c0940440e501003050105050007005802c0c8100b068100061341500c0b42c00b84e240002c3d00300c61003299079000107000c20350a520350007034500412201d0308290401507a00e504040b0480000d1407e0300023401c00e0002810700440c04c0d02d00404e82d400600800c036a05048417182004080da0003001d026206032071454800d82400609102030a4042e5682901c483c1428110381003540302841c940707510600090040707582c0c2d40a208201078681002008020304c04103490241006410345003000901415400300151a00d808013140e03481411484c000c081070b60810000c0600c1107216202942105500d40781c1d03007140b506092010050425034031103004450410360300f2542c23540b00b0300030414401c3c42400100350032011600014086150303031520100c0c040c0300e900400600c1c154454401161350041508005040e01032060350300401022000d050502826030140c11208202d0195101d156a501c01300382c1c40c0d01054007038406d00c01c0d1420007400403030b40206c003800040d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 730569433 1250 730568183 730568191
    0x30f120406060509190c140d0501080f03070c060c0f0b0901270c1a1b011b05040e06090709090e1b010c021807020a080301061115010605070b090c0315 66
    0x2403800e48045003510305186114420300c5c209800302507841d6000110005410380e14a02d8061140b00b1054104503403824000d005051102100001d883d032400c03a440f8a0a0440d00600c01da0741c20070054071021504d0f90080344151901810091160201843c01203001400150081d00410145041c84410301c0190440d08128151400760b500700c1d2804485218405c450303120041c40c02050140030803080c0b00d0b17210a19025510509540d0900494880c41001c0c4501140300b100b240e591030003100300748400a040003903803d0f021720f8864105070401189012091000c0c00c07513442441d00900040b20b044c89201c010025041280080c8041d107000206283c1c2c48d40028081d20382094041c0d05e0382c146500c900b4a06240366001040e076260300d44803119402c8500c1014007008114002c0904400200d5403c9000358000c0090782d5421303103182c0b4201541d6003401807038903512a4480a081c01001029803004c1511242d5400c03002d0340c2c003640c0791410f00914041c0d4a83e6106c3d01401a0340c09565041820074480c0c0c82 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 730570683 1250 730569433 730569443
    0x108031210061d040b030102030c070c0e130b06040b04060f0e0109020306061209010912081801090503251509150506060a0c030314010806070f05030112080705030f1204 74
    0x255129044007200404a6000e08400280920a054844940403058049894000e400040e03100356031000f1a099900490344010700d100d0008884c810462014411030043c685a08109007030309205001e1078241c120514041c280c1421500070072807076610f980c00300c2e40c4000010010002907646c0c1c0b00d1004103c00a1007440364015125000040c80c8105008592003080d000380043e191107100d05106c0038510010341030510641d62090074000140301d1a516142d03400840d114006580b80c0082e42c0b0300f9003c040a0710785c40c941d050024070740000c0c500000356140c001d40820040c1b50792904400c40d10100006100c0a005004030340d15231b80c0070f00303804d6102402460103102603c00480c0c0d44d50718a0f069039001e03101c8540180f01000800c807128842c9500c24001032083c41d0104980000a4a505403040281c100303032a946c000781c051000041d004130030104603071302c141855401c561500d045014094420600501940030029106080240c02d008a44c100010300314040e460745400c500400414808a8080761 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 730571933 1250 730570683 730570717
    0xc110a0f180203060604030b040302100203013011100e030a120807020a0507050d0c1502100c020a0c0b03040c0803040f08012003180106120602180904080708070515010803 75
    0x8507007031031402100c0c401ca5003d031100340780900e140c0e0740000040700148280c2c1107010b03d8245403000640c9000440c02402c1720840c0410160a00102101e02d00840e2034a0045401e090140d90004490010041074510102d135185440000f0107401e441108060301d90f96414000e0131000300c208014000a10b5000130a542c0c2c104c1d0780e45c5c070360100381c1c3c0e100d21503038028001d40c0c84140100024a00410001c400d40e02c1181422070ba9036030f5480e5a02200c10800d2003c002d600030490801d000d0000f480340c0b0310040b032284020b041e118100e44904481e41715501440102800020014062041511040c402003080d2000c80e40d94a55410200c0b030001c46500a0304065400c150126070404130502c031401c0100000c250b01c03450354a1f070002da0400b07480d518003555580c0d505c501d80014103000980802d4541c40c000e09015070341d184108010444002011401841241c403142800003140d41d107002c0e921003e034400b10256840e04141411480c103600c922074001e03558506800441c4040010000d850300821940e8840 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 730573183 1250 730571933 730571969
    0x20709140403080f0a091a04200a23030307050607090602010635010e03071707050705010c080412030c03201b040608070306021213020d02010c110a0f 66
    0x50040d1400e4a000d00050958800724411485200c1002e80151850385d002558488603070311100e009001440c01c66002481008000030f0001d619012410380707600018085001281d4030004401c083d00f8090400301c044256801c101c490000000000b080c00001c0440f03440701c04030310b41a0303641c000440317139440050250140065064014001d00741650805c4100e0701c0c81542200d11950300c0c000e401e08950b500d038190491164400b0003032207106e40d142420030103566925120704020003c42022405010018010450f0700301152000c00e4140a40f030702407030a5601030343c050030a0540d03809079810503100381141c2054a000c040d00002d00d030b91114441e48650551910100010207a0030010400c00084d40007500c00d010f0982d00c410f012800400010400a030150b1248000e5284c201d0a070011170740705600040102c0d5400b0f4200b94658040d203002d11135015200c0950106030750aa02c414001d042c0280b42400b181080f14013000380710840c101801040c8003903502c3d145819038103d10b10070360707208009115000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 730574433 1250 730573183 730573211
    0x10e030a0c0203011503060b12060c0a0f120c180b0405060304170403050d0207060e0303130e070207180f0b091315061d0a181110030b060706060504060906050d140c060a020709 77
    0x224850442611500c1c14a207024400352803223710310710744000f0070000181075084107110748682d461450480d034500e640308010150031100c10a0541000304a00c009100405c90f994070807044913402130717010040c0d04500c07405403154003150165800080a81c001c0c00c00c00c851450b0300003a41d00c115102a6907002c40e560182d004d06850f0300c01c41003488c5424003803507403e01008680072401d5802071424411610401e9075654500c11400017501d42c0400b00c4d8132409114034144043c080d0f810010012a031000807403d010100c0b458484580e00014000010340c10a031003a20401e51050000781080e0680403c0c0606d5001301408480044803040251807a00041040240b1540180c030b9510354012400c0301015007400800c00c220710040e00782000c01d6280c00d5000401d80b43c0c50017800000c2d1041c100800d483e41040300308401e50302650005882c1e249020000c1040d03a442c2c00c01240503e0300580c41280e40802c50301041d0a011940d007510740c10074000581d140c1103a600007455421120b54200c10040e6a5401c40c036 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 730575539 1106 730574433 730574443
    0xe100c031a011809090c0306050915010b0901020d0e0a0f030506040c080c061c090c1404150501050f031003050a0b090f010e030a0c0203011503060b12 66
    0xc1514852410003041d038044000d080c42011060144580c40d40c14207a40b0802d0a402d44130380c42c08050141a8160a019503001002444503180c90700e981555205182404501c15440700c000068802d20700054548569050b4090203040171500701c22124900c0003044940e00031050a40003501c3c80c1000c050708000c5202c0e03000b500c079500d0181050202030100b07a210101c1c0b60410800701c1d0b0542c1d41c180440c0c6120307054005003205d10543c801c1c0c00c0b00070410340d0310041c4800584480455007005e103e14500f5600000c0310709200510070390310442d461203010302c265404103100f4000c00c403000950401541e03100d81d1003404400c0c0c03070b070313503500e0b12494007640e0101a83e854048034180809980c003408100c501c07001502c0240182158182c2150740c9206103030411040000300d90000c421580c0c2900010b2604208030710000f540da4503030521200600300e00903c1441f0303898014401c00320080101d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 730395683 730575539 := by
  have h0 := BRFrame.cov_init 730395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 730395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 730395683 ≤ n) (h2 : n < 730575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
