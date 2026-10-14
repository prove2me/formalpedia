-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0357
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:23:35.141308+00:00
-- url     : https://prove2.me/submissions/66463f73-4fa8-4103-891f-fd9b3aa3ca61

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 64028779 ≤ n < 64208635 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 64030029 1250 64028779 64028801
    0x106020607020a0218070504080d05070302010f0209031b030f03070b040c0605120a0c0201020d060902090414060f040b040e01060609080d09050d0602160503040b04230d0f060b030a06060306 83
    0x208590641c0141ca03a604c80344105c250078405801c4da80ea4040d42198903000320b0b84490414405c4070f20000701250403000030300343c40740a5402404241001d41202007644030b40e4a4560b00b42e4040064400074101608814100d0b0500030f05903804082c3c0c04542030300d940c000401c00d44d07080c0b0901c000e04c4100169040d0b160b000f850603050203818502229060041450004c0000484030348503050000e9070391003036045070201c0c0d5148070b040140a4480220000030740000d043d20340160b00e0080450004201d40c02d010f485650018652000d0402070401d2001604203103032020303049500c0d00c50900c404a400c0c054400a40850303034684003100c0c641900d26260100c2d4058100602140c001c080c0440c0d00c0e00714142001e00d400c00d401507981c03203200410b842c071500380d00c0d4042c1050002050210722110000014000c85040030030340400010710007495440c010148a15076440300d0030072424800544d01200661381107001c0c200c0041d00740110380100e8204205d50302c00b1a1441e6442005104200b5039101d64806a8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 64031279 1250 64030029 64030033
    0xb09090c010306140108041412181309020a09091a15150301060915121a04060e0f040303150b0403060203070807030506031e031b01140c160204110909040506010602060702 75
    0x43c1031800080d040c01b80c0540007400741c00c44c60240c013040345000c001c0702c4801802c03034503516075820a1000c0b030380002c100000d040348590f0120143c0c02d111a400d004400010381c0080210034942d2600f00301c08020600000304840c4c032109078071a502410004007181c0c0c4142844406031580800b000b0811507404483c41c00e104020205000510060394402d5041043d00e8074005034503120310540c801039900036908071034400f00da07013020116501c0c2460302d115000d03000c0c01958244035554642601c00380d440f42c00c903a60400b910b1020001400f1a1203900722803488032600c80d0316400c064485440e2a400c1c0d20540080c0d40c615000414030240582c09684103074820b01d00e107010055420403c00082c2c8a005031400c81c0b6400c40026130b0381000301b0003030080324034030720500c3c050710102c001a100b034601804841da130780c5000401d413800140101c003980c02110814000c0100c406c1c5043c2e0250300b00300040800c3c40e00f000034180e00344118201600c8440b85680a9800b40000b4041c4c2d614000c4028074016004041e54215 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 64032529 1250 64031279 64031309
    0xa030507030201180b040605031819020f0411030c030408090901060507030e12030304020d2a030606090b0325120f1202011a01030b150307050c0601051009060e040b09090c010306 78
    0x105c81a00c090703400341d51007450000e9036600d55000180303040c00803d502c04602d00440c1030100209548050400c0d40306e01c01d50700000d41d40404800c11084450048840b0301d250010800180348540c01c0b8000c5a00511031342540b42041100c80205409400907045a40030402c0012007005164002800c4207040504840343e044101c0c508407059242e020103003000b0700801c0c1e0b01c20060308000d04d4030035421680e48804028502c00f000304201444903000c0c5d2009841e040d2a140d008103841800d0f00032040b00480190060000703141c0068101c80c00349440c0045048a0154880810b00a90313103202555024003c000080310040c5500706148a07403505048802560702d05001600e50600038450000c03124000d007400940b81d100500818007414001030f0003401c8500001c00c100f01036801001800300b075020740301140c02c00d80e03c2d5414809040030364a0004045400030400700003141c46403950140010014101040d441c0340e040120710703141020303100385810741c1210f9110b20030b0b13507071601c117000c001d02984682c0522 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 64033779 1250 64032529 64032539
    0x40e0a0204120b0a0f050c12100f0e04030918020a02160e130203031209010c1709030d020309030d09080c100204030c0909240203010608010501170c0a020a020a03050703020118 77
    0xc90300e48090002c10480c0300f5000030707806058503445018001c0100300f0500032031034070b0138140450768000182000c0b60f000520110710b510b42070540500035944c005980401840c1813036000012100028011001c0180589000c20048007440c11440b00c1080300c0341c00750b03d90040f1180a0f05003d0a40403c01407401c02641c104040082544c0b1607421034103000b016164100b032800800c1c11845004109141031002000b8015405815800024582216600c2c1011954000d00100300c01400395141202a07000740102c07130b086d8001c3d40c0211b03040300d40c20701101d03c0c09542d000c031542501d90401080c3c40e070708008508030365400e9050000d026040c804040841c509800c41d550030301000001c3c0542c800c20b50b5200500c904020042000300d14000340c031101d5100300d0004519a034042d5200b405000006803503a400003903654017510700702c0c4401b40311000e5003060f941c50b00740d1917500b600300b1001c030f10461107010303040009038680c605a40050750140300038214003402d41c00050302c80d182200504850700364250382040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 64035029 1250 64033779 64033799
    0x4050705010302130e0c030f01080d021f0f0c080f15010c060b0a0f0f03050c0901080624100809150105210102130b030f0106020f0a24060605040e0a0204 67
    0x6460302420b0068070307181180d100401d107a45a4011499440d6030b0700c00d0064100c040c1c805144108880400c0c0b040a071b1702c90301100d4a0b01c0380040036101584c84419114988401d4030300003c0005903c1c4d0000542c1000301c8000e0341030f01c141c40c00c4000400c807040248103e4030140c0c0281580002c0c0da0551210b1f0101c50700c0020109940c80d440034201580d140c0d00e0a810b991411030901c0105000001d042c03041e138441c521600c07251444e1000f10350078030075500d96401034103080700c040c1e040390544d0300904410f9a40074080040c00c0740ca01030a0f444048038503984455541d428402c0c0800600c5d5a68584c054034010b1041c914140440c0381204054404600412081e52a02c05800c0403072807119168510100b25031f00b55001e03010318403619000284000d0041002c040c90009940700f0800702490362450790781c410080c2d88925174618180c40c1034101180b80c8000c5034800000300c0d01894800c2e4040e00308180c900c2c1500480c0d030303260842d20010b140020108030502240d0071264120042d6182145002d1400030650 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 64036279 1250 64035029 64035043
    0x7080a0201080a02072103150303050301050906030f0106090207060e0f0c061b011805100b0a0b090a0308030c1e09010504210c030501050105101106010603022803050f0606030405 78
    0x741003111040000750250a51340699913110f60060a030b4102d81604440d4031404c000201c0408006413410700c01070301202d0001944001c41c2e801d40ca88601c2c503400c000c20b10445c04002080301c1d0701807041d4500d4101114003442103900518140d000103890381d0b09440c002c010f503440185586950f9100704402c0c440a400172482d081c02c44802c03150b0740c0c0e1329900864511600343c103584405005500c0d24001c202600c0a184041c0c0c40300d40f0800c01d85001c4e60b10318502c0e004803650002c090380c200004e407a043c00134013129401040c1710345009003d206003a9072541c852420341d01c201d82400f54068041103005440c00000d07000c042c111511456a400c00b81d412000070480c0c055446503928000407412580d0322100c1c00841c40684540022050840c01d17103d003411400703483c4c2031040354080c0c21016200b800e614854448142400998805440c00743d00e4044c0440103908100758011850101007008036072001003148510000b05607407408580c42ca00641c110108003001018980a00750800c20000043e6000c1205 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 64037529 1250 64036279 64036283
    0xa0e100c1b0b130c0306060e0f0106020d0801050f010507060f1b05040311010302090a080a12080a060f0e0c09060c010501050a05010507050309040e070b07080c010e16090207020609150903010b0307080a 88
    0x1007089491a0601320400c0040390720241420303142041c0420700310344c0005910710078021122005030320303644c3c0c1d41c040340d80d5240c405c80c0d480044c280d40018021803400f14180303401038005140050410703441c2c3d110341049501041c40310000c40d90f540d80401610115210320f98000c460b6080c00f074146403940d1200614030140c203500504150307001501e6101a9145c4103044060001d0008895031000180f601c80b50b400304000a0382c020920303c1e00011100b0301d0038091441a0340501d41080700d040d2400f030b160802e980d4003034403040c00030303406009600094803540c014124042d002e500200f1075500d1300d814001c0202843c5c200604106d402c02c641d03400329200008031064241d00303541c0090b050780c1100c4143c0c00e01d0400d400210f810400021f484061249070310140044d542e040c8000c01404520110380c9903180689840c05821903244002040030140b81e07806041d4060018103000c1c80c0c901c0c210001082030b00016a92064442c0c040b40e000080d050074450200c07001016001003541c642480d03000c0380c0c1d4035445000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 64038779 1250 64037529 64037551
    0x403080406240303030212060a05010f050705070806100f1208040b130503010e031e0309060103170d020a0c060b041109060a03022203020907030504080307080a0e100c1b0b 75
    0x440404501d000c11250b00050702c00d525910b4946030318009002e5070061414030b6001c1000e00201307250745485c0c814002259030503103c16021052540c01070305d036030b0402c0c00207842c14050300c140040c004400340001882f40110300da1125105003048400081c02c1c2c0c541e0061200e110b82110b002d40002d103440c08407429158044860350b111602000070b01280340340c035001a03416500b001034850402900201902d50210350007518849448145240e40c018002241c0000096100c40010004610010100c40c0300f400700d510824580b45045224405aa0044c100480040c0b903640908041c80741c0c0d8410541242c00407503080c4620030040ba070070344160044c24100761041c0790008010003883d000e82d04448401d540400824810005129001c03078441e031500c026802100108001810760317100e0f10900b8030079076204c0710090941d1600c060483d1195002071460a03401ea940340f00a0041a0401010b0301c1c1148460006c5440c10081d40010809007440061682c0c094070000c117030001600084030036501900300d40c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 64040029 1250 64038779 64038791
    0xa0507080d0b0a0e0a0621060b1203071217060109050f060417031e07030801030f020a090f0c181a090f060307030504030201151d06031002040803190201050403080406 73
    0x71180109a240300c001d501101e00c1000042082014101620842e518001005019610128040d111a07100100d0f18802c04045a61001070680e61105148880141000f001110003a08992555001030800ea50340044502c030840b220f584580941400020000f110003035040030700004c0c010044900502d44901040c650601c2c89446003c02d980050581d07414500e1284003500320340741c50354080742030801d0410b40e00e0b0b121500000303148215104e5652590358900280e1a503220b644446900c02002c0341d0040010400080c025014018500000c5010400213201510349038050050207460301020b401d0b00180c0d40810080d03402000c0003041c42c4030030754050b81d10000b1000141180280004969200342c0c00300500203000d52550040748964800e40080040c400a00b1001d01c400000d4030440c1e40c145216404404044441c1c00415045040901241c003649101c4030f100d01660072640240324594404034a41700910450300301c10076040384600023004030f801c00e51001407013042d0060000d08070303e850390 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 64041279 1250 64040029 64040047
    0x706050711250501020703080d09170a050c01140709060e04020d091212180f0f050d02010b1305090d3b010305060f0f040e010b09010f1503020a050708 66
    0x10440002404005081c0c03a03030b118030740c12840c0031903181c5019090400c0c0b040790049940d500004440050301d400501080c10400d05400c0c0c0d00160140d100e049802c142c0350031400c1c0c8400c41d213101600002120383c8807541c0300e58000385800d085905040c0082d462a00131010b0001c01a0008066400d17a80c00d8584100c85009400c0818003a11a601541c800304e494440f480c0d0a00c5500120040342010b2a910f0040704101a91050150f5086d0015503458161940d020300004d01d071040301984940c840c20085645042c5615014242296142c1030400360351a81d00c88101482c00342100d241c1103104180421083c05c1004c0c840d503868804a4021060041c49101600c5105402c2c00348800d1641102d0810314400d03002042c4160140030092130b602090605010801500e4030100b00055954050f01c50650a9103074000c1101412505070a58415580c4422100b580d45503059140e02030005114015031281c40c2c6044416020f54400d5002e0406205000000d112035221088465043d0004c02054070794502c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 64042529 1250 64041279 64041287
    0x160815030f06040602030702100603031202070201180b030a0612050303130201120c0509010305090a03140a091703070201020d08011212030608190201030f090305090603090705090c030906070306030807060507 91
    0x10303a40985142c4140800c11040080c250021031040029034240c1e00c5512030406d1a0301590003601000f404110200412003c842031580030342402340c01450030050b81c4910315850694440d941e041b110080000000300485100240a894014480150003d10015960701c8080d100c0c000901100d0a854030889010103580c852000d049455800300010024041d000c90054000c0d40001d0400303002c030f1b040c0780000300803440101d2a071420030381640b5068601c21542001814a900c00e0f40c00074140410f01e94040713480e040d2240404442d492040007550b0341d401030300005e442c0030003501c05042003200d4280180b1510707100340b0010107010780c030400d145c0340143c281000350701410498001d1100c2d4030903e103164102208040c000740c000c071f0003a281005003405008080c420380300310746805004204104003980c03603801c0910045900010b000c094507096030312440011314160302914150544940030091000104040c001550080c40c1410b003003004a14613540c12282e8001c0c00c1c000340610707585000042c00c09002d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 64043779 1250 64042529 64042543
    0x507060515090a060302040b09010513110d0c03050a24031e02060c061005060f0405060c0a06020c060f0109021204081324030e060906040f0606050d1a16081503 70
    0x1c0140104000d191519440d0f0040150344810303031040e41002a05002c90401e4074031681a136034007610320440c10807a010104040c10380040707050440d801c2007221180d45401449120345400d519030700481c80d8101212600c2c01d944040c505c401c144180c200c101c0b082480c50131034100880354004204c04036610005000c10140d003c640340a5048140015200804040452082e104890340010f00107441d45410a208548c01442186041a13004000a020b546420710142c001202020212010029255035450aa820180d24070400d540300b2400d10203a407040841443c00b40501c0340307045061000004041440360009000074041d0200015034000711024242e041004c2d1004503404081307200c0d04850b01d8801004c42c0120341c000b80c5000500c60741c00b80b0101d81c00e40102c14400041941c2e840740d1300c03154906c1017010011103880f55201d5001403182c031800300040144d4000d010307a0301140c0303414400b03a4a0344401469060042810035140000c1034105031078541042c4242100140055044007203860018 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 64045029 1250 64043779 64043821
    0xa0204030f080913090305090d0f05070806010e0705070f0f080c0601170d091409060d0b0f010311030609060406050606070206031501030606020f0a080a0e130f0c0f05070605 76
    0x400800041c007803003040c0c2c00400564006407003848000d5440d0400004035a0011070040010360704025850716450100702c03a080d0203000f031302810030381d0320965281c0b031a00802d0348c0204041c0d001007004000a20100740410741c8088a0308050b89464519601d0700c0780501070020003010354140c20220021302094905640507004104215842561903100d03000c00d41c0742c0c080c0554403070301c540d01104910350311a8454504803148036030000c909000180420800c908010809074100c4641c5a0b100301240c648041079000703100c503004400d0030b175040d8204500704c15600c1101e24000c0d401002801003050340000c007a540035401040000300e80e180d52000610341e11900c00e001e544061302105003c2c080003501d0652540c90000d0320104801c0780d5522080c3c1c2c4a040c140c41d200c00d1600900c10b410f002c20110002480340030900d00d1b050700f60520090000790030741120100c0d0300c1d520795103c0001d15041c0551107905041c04031818a00030304804a503000b00244100d0100811007600e5101149200a106505000c829 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 64046279 1250 64045029 64045043
    0x10c091a1602040e010501140f030601031202030c0a061a010f050901030b060903030c0303011d06010206040b0403020a060515010207061805010c020a05030109080c0118210905030708070305100506010906080a020403 94
    0x62041d1305801d019060a01800b242c107009410455a103191820406200c20409009001076a01c1c585594003c140302c401c1d0241540410040707410004824091440042d100f00d80024000b55a2a820305c0d100b0440e0304039a0601c40c1041c00815096080000e03603414081c00d103000301e8002c0c0b03034030081903540c0298a5041e81500c80401c56040da8903010000d075059030752070200b40359030b51401072511019220981d820350258210002003800702d185904076562213800b034012110b503440340e0341c0c0f003504441084a440301c488a8820030301c103196034103109100c014600e81c50294500c40c0d02d148080f204d09100e12a45040c050640b0542c8210b44401000c0001002c005001b00412a01070038000600e034030800c005d440179442e00303076500000010030100da0b03151038122101c2644100f507004070382200801d11558005104c1071801c0001c840c1e908001860180007180c01030041585145401d44c0b80010101e0f4004801c0e041000702f007580c0e640010341c2403c846c1ca03803500303a009865407641030b0001d01c0b85802c0580701d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 64047529 1250 64046279 64046291
    0xc0f110a0602010f0b030c0904020613050a0b0d1401080d0c1a07110d1106071214040311010e060609040204090318090b01080703090b060f0f0d0c0305010c091a160204 73
    0x2550b010342c0641c1c42a12164002d1248021030f100f0161100c1211035601e51184410000c0350150070814041c04015014022507104c4036111000108030881a0740054007203140059031801588031030042c00030480f03100103052910350500d5a503948903c030440602d0104108819000e00303006101c070b038070350005201055080306410701c800000d05450400c0344a8585120300c01078550140e20540c580a40c070100c0384041c00032034803100c800300d07030726004d60004508960311181007010150203107038018010b40c8643c5404c051600c00007885829074a210000d401f50790800404c000c1d00e904c0b11251140d0043d411100042d0019852805581140031a102c07090b0380361600e000416403400542c0071881000c000d0b214682e0039512030b2421020b032681000c00a14803c18000401d002c0c0c141810740b16040c0c440113068030340101081010034001d0155030415910302c0142c42040082c041b081c2302c3c0c007150700d90360318000403581c0c01c201b00c407082c41148100508003028001940125000d401e969200305070b03070061080c410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 64048779 1250 64047529 64047539
    0xe060609131e030e0a0b0301090c0504150c030305010b07080f03060109030c080a060510050d0201110c18040b0a0507051606090b07080415020c0a081c020c070312030203070c0f110a 79
    0x10040b5a1142240468a4103190711000e01e458281007046401d164030585c69682401000c00180092441c00f509000091001180404100181c100d402081d6030740c241c54081710307050007811b0b55010313031000b90590403c000c0c020110300103a08460280d49251001d5969494000040310010220703400a08004603152020546d442c0200c1c41c122140e0003640148646d8907201707203a65203d030480c880c2c2075100ca602080c170741c0154005c110a048160140007510100039080740420a650841108001c50584003803c000030048150400c0e90000c943e030204002c18545064007400900c00c0a011b110101031450140c010807406400c902510750740720341481c0f003c2c18021409040b040c8151011501482c40311282320103024a813003640c070b0400510004000c1c146646d120700c0083e070b0040c29400304c4508800c07280e000044240c0003c01d5000706000040860524608002c45210350151400e402c01d0300400c18004982d1b840b0714003441d1a6003080d100b0700c4440701450301801d44100708001c240c1000d51070200042d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 64050029 1250 64048779 64048823
    0xc0804050d0309080c0303160b04062004090f0608030304150e030d05090d030b010e0402070602090904050309180709141206041209060207031208090703080c0309010f030e06060913 79
    0xf121910701c00c0f645c80f686000d0815869015002e000c881d003044000c8500080340c6103041c140d40080c05070780c00041d004144020450030f1a480140c0340070440c3c001804004070009032141c1182100c0c520420400d09042486031500da100291010348291544001070000c2c502941c00601a40d4030f50003103907614180f550302e00d8003616044424080318011000c800c0e4885000340141044000142d407009004000c00d070400c0007d41240030142e03411075090102403180d45441149500030f500660045490b0031403e4104103a52040820103100c10404400b03003e095500413403543c081e80e05281440407044580000318980e000807000034000e03403252205000610100c125100c02034101690b6028000b0b07180c1300d05a030f849146102c0101081812008142c03c28464a001c54201d0101c000756020580e9032749038050b460300f0030b40c1e03040d4054000050000d21580c101414040d043d0352806c1c00e004007031070403101c10340700c050007890345005d1048400010304080644a06091003540640b00d006001c0b00402402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 64051279 1250 64050029 64050047
    0x7030c050f3001061d010806160c060207060e010c0908060106090605090f040e03070b0a05010f06020a020d081c0b09090102131403100c030f060f0807060c0804050d03 73
    0xc0d001e20004001514242018480d079030860100448030580c0211100c0001c00d018100e0100100355584e0b0003002c503402c02c149001541c0f42e12484a03180b4194180780032541000c0018043d0b0002d03070080052120000e40100040302005c0d001800162544440d080c000e01422907007c50303240075441c2a841405042e0030801140950f403014040b500c41c0c2c0e0304c884c420358000d111401050042001405041d04503c1c0403121000c8a10b07010300003003050400300707002e41d180d900003003030444d02c4400d04810001202240c0c4281c0e4010010b50803e2040d03503151102c0a5251001d604001e0302030b02d4003800780b800740f0000100701d428020b2061070f0504c1c80300006101800030101045010310401d044008200e030f00d5814003c0d0b6400071160b40c2000c0c11f551404140508102155418035018040d80d1520a8041a141718042800b0226140420300064a960b0784080303560940000d040300000400034031194200042c150142c1e500307410b10720002c00b403030304040d00d80340a981d001c50b80c00700c620000c0700c3c10940c1c0800c0c0d01c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 64052529 1250 64051279 64051289
    0x7030935030c01060509100302040506060706060e1f0303080f07090b04060c020f0402030c25060510090e060903040611010b040f0c0f03020304080a0e1c050105100602070e06101107030c 81
    0x800519458401b0040c242e8001d03504172a6040c000d08040c0301503c0c0c20707486280c02c01e600a114500d0404150fa940064803000e90161021051031400c1004400c200f0311148411000140c0e401d81403415a0343c00780850030041d082d02c40f00b0036200300080142d030080c1015001750400b0760401d40c80d1503923003800601000c14401e00321b0051440c500e4120b9030341014000d80b80140301030300204d0705214004141da00c2c0011075106441d044240103002001040440c85514010540c0340402c00240d411301405000740c800343c0c2c000e681c1e0399120400f0441c01540201c02c0d2019500c0c2d42c541440036400030824940502110403401e9030151030720001031500302e0030364841c41d2910802c0e143c0c0402c18580e0f03502a01240000c03680600050800c00151016600c03942130400d2001004003105c0400391440c2d52115020b4000e07904850320b079503440c2888018030307020001e04001c2501e13100078100039090800031003807904003811741c40c021800720f042920101e0003036100014102d2048201c2d01055600d05000c001a041031080e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 64053779 1250 64052529 64052531
    0xf050303060301200702010e0112110d050717070509031513030e030a08040308130b1801110f100b120d03020d06171b01051b0309040f0207030935030c01 67
    0x50603a13228a001c03030313180041e140f622029040c05861b40040d00d4948200a80f0380c10003440c00701c9484038484c00c0c0b05956101c904000030545540c0c04008040403900040c20380c8040c0402a003114982c1c64a542c02c003980f14074103140c820b41b5543c4140100f0300d040d11440020000d52a00c40800c03500409441450f0700c084d02030b6450000c0403215505140d03c41205200160071354800b044140085207044004050302101403a10014140c0d403040c01c00c029400c01240c2015814140c510175070130b580d00c04080803003690302034040d180d5100b4401815a0300d442d002401c000241d10b03002c07098169614550034028142544041e907103a0102040010001c2d40701d43c008001c010710308040400c0c5000310003080c058039071450004000a038502502d4401203d245400c0380d040141c200880980261f4034005c9050402080000f9a19038500c0010401034642684240a1180c41840011301007680440b401041b40c0c50201807001002c418250002c400e503002400814040340743e400b100781600d001009101410030704c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 64055029 1250 64053779 64053791
    0x2030906010e040803040303020c19050a0c060f05040e09010e0a0b070305090a020d060e0708010f0c03140c0f07031704120e03070f0521010e06060108091c08040206070f050303060301 80
    0x5200040c070b02520b016120385401d000007000a40280e0040000c0b0728a0011580d01140741000c04000040307420048903244c200240d1001000f20300c210702d1001c0c202c035082c0b5908880041c2e80050680c099441050250b08506010030b00103502903029542c80b007031a00581d070865655080003500c0782e1080d1501c030b00180ca4140021031001d0045058100e403580180009407041603912140c000e010f10520b640d040e80200c4000080105003403191f00341c4200c5000e0040b0b0b01c8841c0c50f4000e822a496098185900e40880c0b08002c440d02b26502290720041c00141e826071205418281103540c10b881202940d07c0e07802000034401402414009851003d01554030030488054400c2416140c99407441101180e10072400c050040d850300281d4440004010380c0d10441081ca5902517500751062002243c044d0303000f24092040959102e07001591010481c8000c00c207a03441c00b01c00300081d0340c0a07003420007000303070001c049070443d50307004100c03460300d030300300d0000c8119060600f00182c5071b07442a80c0d4944603611b891 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 64056279 1250 64055029 64055039
    0x3030a050a030f33031e1a0115030b0105030408040b13030803040507091a03100507020f06040b09060606040806040b04020d0605090d0e01170c0705241e06091f12060203090601 77
    0x4d00600103880d03004d500c0b149201c01202800d40350000400d0111401540000d43c0d034180d10202c104e580c000c213940001d030b41c200d0100280c068220754900124604001c41001040041440501250300311200000300598071040c54080103031082060308000d08072507000040c0010700c04c1c0002c0c07050a417040084100001c003140700101c5000b00008a80039099040907c0080c10064298402c540c008400e00586512403050700c0d915040000c00c843c200d641c41700c0003081c081603103410011070f680706109442c072604e007908003e4441d03071315400104010454202000042c046440d841ca411120303d9002c00e00780401e041121146854945030851600001c05280303000d4001c2d0b10a4614070b0200306c2495007140c19444101c40e80c0c1007030b07104100503902da204040c240d01002d1041c41c10541312503003c1041c1903040c285040c46800e142c40180c070118801c5074403c00d000b103c1c0c5d1254941c58010008c00c00d0021203503035000550741000c0895001440c21618a0320000030310065800075841107003201e080c1c8029a03225 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 64057529 1250 64056279 64056371
    0x20904110702012028060501050901030b01030605070507020a060c0314040b070b09010b060304030f090501050a08010509060d0803010f03140706020307031409100e1003050603030a050a030f 83
    0x184030083c2c0080c401e21040d5030764100a0921018203486030045c2c40300204400c0707441c0c15215115041e548030800c1e03150408180145072003030901420084610040d00c0d4550b407900c0c07a080c003060001130b100d00ea940000c502c2a034029001c5030646136010f4035005e0590b03603940000d4950416040300754082064510441568151141180e0907189002c0845042008030380750609000030041a40c8a290359411000c0d0f03c80d070360f10300035600c224031075a00d44920f2041498024141d08943d80300905014050000c042059000b0510606460081d038101e5255940c0744000703000f07040104005400071400000100b08450354643d00360559004040c5903141144001e00c1ca50f42e43c0c4035119044c016001405520002071051042544e034400300d245850070441e0050024030307007003405040703080030650380d00e100b030603505003d206144850b216050030010b40c0348c040c001c40c0d100d10801001c1c004002000503901003d901075401000b0740d00405800304031014003803000072031540e90044010b0b651002e843e05004e0042103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 64058779 1250 64057529 64057537
    0x3060f0603020307170304030602070b0106120902030705150d060f08120c0d0513030c0e0f090c03061b0c1e070e13031d030f0a02011107050a0e07140d02090411 70
    0x2c05030003040310902d8098440c0c940361036041119090b0208200c000081409800a00803140c022107010f503055150060142545010601203121282084501400341c0d50115280044507000c0d201c809056035a42c0c91f000740c502c00c40c081c0d145a41d140040204114203032546250a80d007030031003200c0c08454140c096815902a07004642070070790103040c0d1440307242d1040700500105c1450400e9841029101d0340c031808603061941000c20007254030b03c10400c1d20703400d9000c8036330000b00301406404e45070410804261148001840d40c2107500b44c038030701d0380f43c0c4004000444810308002c909480c038004a01c1c800140f4981c0120404403188100c0001003800700500110a008100b0201d65900d0b03410303103990580d400c0540900c030141850288810022a031024000000d203202840003600c2800704a00c0050401054600d240060fa4005002444680c0b40d0b8190b840542d130b82000c640e03295070b8030700d80c044407008105100303951307003600204540e45061070a40250445d80350842d0240b0101503210040502402 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 64060029 1250 64058779 64058783
    0x230103110604080615040b150306031207050309100e0d050a0b0703050108030d0b0a0302100309061b02030a03020d0204080d050307090801020a1b03020c0301110403060b0402070b040312150f03060f0603 88
    0x1000418400481701c0c0c07803a003451134058400b0806540400008003144201902408410302c00020403845280034441302945051420085d0b00b000707125241c05a03680103034100303207018220420313102c0700450007131266a440c0d41c2d004080c000900440d1030300c0c6d5120307040100b00b00c2e00a03160002091146009003e200d0580d03900c0c0d001541070030540040079000d046030740d0003903400c034100050200260300c0d5204061741101c200d80700800c07226168900031003159102c642016100744d04180719000c01d64080b0460749400c000d032070090303268003611001d24020b2045911400d00c81c400c00714242d42907500100954801c0340383d40c0360000000da44401c00b40c01c0c1d00c03c0070240d000181081001c0200035500044c3c007280301e4020b2048441d9026040f01080c02c58040061a00300c041e808030b820020400580615407840200b0344040d800c0a52650380c031900b070400540002d00b8440c0050301003003203042c0b036401181000c46003d5031a0301035548103d601c1c6414600d002c181d56080c1004480762000301b00d0700542040f66 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 64061279 1250 64060029 64060033
    0x90609040312060303050322022404080714010807050304050a030f120c0819150605031e0112060c03090203070303050a05040f151106011206090623010311060408 71
    0x15440404124501400a104600b403111200701e15035510704610440c0003840c4243c44041c0c5e24240001c00000542990002e411405042040320700140c4a1200e4180221050304054202108520070a0034034015500128168400d2410000304845149c0071408404400e03284e4082541306c0d04021100ca11044070003030f01c01e50154101c007001030b100c2d8030b401209562500d054141000750300101011380b01241e8080300024841000c0c003c043e00c2c00446200f0f01b80d000007003041001c0e80003003c0c0b842120148912410b000000c000240d034580b84000c0380f124848050880140ea68403400d54800c0220b0403841641d4941c58034809d210864024483c103500c00783c0040060020914580d401c54140d4845400741c0100101440005441c100b0003a4990190100d26484052000c00900062a411311100d2024155012400410070010300d45c3c030145404e90005000f0603010031a0130884060003001038030f80c20800c46054440b0f90283c0034441c15050724411594180892010410401e07540954040c0032100c1d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 64062529 1250 64061279 64061281
    0xd020c0105071803110f01050c1e0f0a0b130f050d02010f0f06030b06041e060b040504050c0307120b06130e0f0108060c27150a02010605030304140108060a0e13020406080a0209 77
    0x1703480e051108038911881494128500006480160304003280c04600108001004040c0d052210003445005911561880100180300403030303c1d008041b0b20045c0610745110f402c80e186205020a06c00710150f00c0782c02800700c035030040c40004000d0003031004501140a42d0301d000c9900e03410030b8071401a1400c1b02c1d041003180417541c480d003080100170018683d45c0b41c07201c250002a00d40151480c020440189030790030189448034940302c1030200340c91005140c0c00014508004000c80315421821030400b9400c1790100184480501d00410902d2203840c0201800307180c0420000342040d01280807900c0b401c120500e64000d81d982e00c00d0300e9541d620680c0c00c0385110005100c04080007404181c032800100e110031051aa5000100219503079800034031094040480018414030707010f409000380d90007070800744e00a6141c940b43c945500100740c41d210940b410010014003007407090b9241c1d54000c001d40444000c0380024101070000c00d51083c13005c0800c03030190f4280140010b803000b01248484c1e4482e0064110026 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 64063779 1250 64062529 64062563
    0x60305030c061b18040f0f140f2523030115020c030c0f04060302060403030c1b080309040c0e040c02030414010903110402070507030501020a021005010e0403140d020d020c0105071803 80
    0xc000d071001318403900156595044031001d52070b402003515200c900c043c0000c000d11f5032403200300740d000c0c01040c401c800d6007060180f00c0ea441411100ca1105103000811a0302c594841204480507002c8120807540440e604580103da44e840c10000c50484440860000301030300c0d8035809036214420300c8200c07541504030304180001410640210204614001d100103010354590780012802d80240c1c1094000650810700401080040042e0454840181c680030f1500c034588410580d91b4070410788814011034a90054020b003901502c1c2d285a07442c801031040c0000380d5a094020340e80d421078464114021b1750b44848070410f5000d400004141c0b5040006001c0074540b400500c00030354081101214980308000d00040031410031720203040c41503182e5014264036404001100150384043c0c006500c51010141480b00083e0880d00c4070001012412141780c0392054450318070002c1c05518422140a400041d44003c07020042d40164414400c5441d0350740001e0b01032105180880560000910903401080f903141 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 64065029 1250 64063779 64063807
    0xf01031a060c0f030c03091215010302040b040e060f100b04050114160507030b040506010504020c0c01030b010905120601030515190504020307090905010b09060423090a0501060305030c061b 83
    0x18a080360b06040310711811212070010300d1075201219040e41c40d0800b14408016103008401140742c2d040c4800201040c101c501c1a6501d0400c041c80024812595040b05c0c044944a0780c010303042c0c2400c00015115986080c50520710701c5902141c500c54011502000400e0740b413481320130349090342c1040c0d51300301d100040340003208600c0c1e002c00b0302181d40321100080000056800c00c500406541305802842042c11701d480c22500c2c200c01070708650f03c41c1d80140905100440d002a8441d8200001d10307003c991843d02c480165260900d6400c010f0300110b09109100583c03400003076090403244140210740c03001c50602580155200140e40c2e07582c45042c3e5070211001510250001c507042030004003510001c9544411220440c2c015078012902c40e5180c202c08a424501020810350006040e43d090160741d40c0c00852985002154249108485120011504207401000404450765102c4000c0146544a0030015902d4100c0881888944030b40c400181d180300c540e5174814810300324144a5402c0841e02c101c042 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 64066279 1250 64065029 64065037
    0x506040c170405030f04080a1b0b09011809050106050c0624010f0912030e0306090a081903020906210714030109050c0702030d110c06091c020d0501060905060f01031a06 74
    0x180c3e06102c18800c03400c4610340c15004100928a0390020044c00d00d01c0c1c070b0301641c4c00410400d14001160030b40e4040104650010441c0d0a9000918001080042c00040640d4825603504039200840ca4000003003441078000005100c0c5074036503000c94a85540d81071080d00d00860b55404c00450748152001500e040d4054100707489504c0340d508003014140c0d00ca01c5142022407148100354001216000081000d00302806050f4214070b1280c040c044c8000240c40c2c2800c0340c4148141030f81d0b03c4843c0020a10a24845d0b410b450700314200030101952242d070028504040b072008200c0240c1c00e851200445d00c628014008241c004200d044058210380c40c1001000c0100030061049024117410070140c00181c0c0c040c0110300c401603854803920040f0010a910603d0007018131505406107100308014141d6a540340c4d5240e00a100f80320b03100102c2000ca1010540d03030310030300d50300424075070900d04007003079101c00d60300310511518066490080c1641c00e00011801d03240010703d204503140103480700b5403041c03c00700028 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 64067529 1250 64066279 64066283
    0x303030b0105040e1015080921090a17070b030f060907090308030f090601150207120609170c010b0d0308130c0f08010605100e1f0e04050408030403030506040c1704 72
    0x582000d6031050345182d00300c4104c91001c285c2c44505000e0010034201d20010180200d140340540c130f2891f2801d080d6980d040301e180c450700c047c0b1240180c0d82c00e041c20081121000040030f884288003541d103d0899088410070b05285106000d10700f0042460103907581900c4c420001d03003c105185483c0e0006014110302d016010504014201c5c0c0c000c008502188000c4d4002c00b243e214000c4c00c1d03d4240c030b1082c2002e1068100c40000d04180081c02d17006640055072006503244400c09006540c0949080d80092201da5402044c8400200074034a11191100240c202018008006e100e0704140804102c0100044a4000c021a000101007400f8001e200c020b01c1006119520b0400ca81340c071b4024161110440740e000c10403a80d1030320700c240114205500303090f09001c40d07801e01d001054902c0d400a2141018080035009028074600c10010040c4280e030082081d1401606c10000c1d4105414405201c0e0301c1244c0a50120781400040340172820a4450300465270842d42d101c00b100311000c9441d03070980c2005042 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 64068779 1250 64067529 64067537
    0x70b07030807030911040c081603150902030c12040c0806010e040c0e0406090510020a09120209040b0c130909030806150a0c02062a0d050403050c040203090327130905070303030b01 79
    0x45c00c0c080352076903c00d080ba00b0350710b52034010040c03800c07090b15014680689541c0080500f4030aa1003082c145200820042e560043e0b8096101d17503451844a446020381c41c0c000884d61950003e000030300980303030408001d55810f18240c8a690b0f80314092980402e01c02e40300101020315844c4100070910496014a411900c561404a980da4560300c41514103080088450181c9134000b400c91907894104941c07000520306030308440e051020317030740004d615400c00510140c007130055000060954010441211041042e8800344c2c10415214540c42d0003e00e900902140410702c400c0204d462480e00034a2074035106980c0e6199490b00a10070300854950b50791140072a0040804d114103060801008480c60103500002e802c0c0c0382e6248200426880c00e2451101c60b024410108410f00200e000411040b6103040103850140c0d4903250318401c203140d0b00c540300060740396180488a240c1c40482c40300204d4602201242c2c090880d1128000100803206031003401800f41c0c0c00301c441080080d00980000c00c40c0841410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 64070029 1250 64068779 64068803
    0x3070801020307080a0e100c0503160309020907081f030b040b0a15030201030c05130e090c180115050c0d0201140601020c060301090903090b04080a0203330405070b040f0503070b070308070309 84
    0x200070998000d000f010f00272400c08000c10064a0307903018404c040540c10720701800745a4040d00030640091004c0c0400003000002000603500300354030200000000e240046c00429246e40b030420041080054038110344100c101c0021507004080c2d8040d034881e4401c0032405082003442d540c010b600510000080d501403020611180801d0802180000020110003041907400e2801031141c5081039100d5440306e10401c030600c01c501410a101d50001d05644113160790521300d542c10b10060383e8501508984004600c62032080c008181d41c1074000360340c40c1010b84034010142c2c8034500166241c20602010540010040c001041181d80d0780c0c0005d00128000d04001f0342c0e65444507059074a0743d0207030300302d42c40070750104103024114201006001003503032880158000b48a00c0403a911041403007008428811182600070030140401888031744c5c010081c900f8442d680c0c6507a4001035900b01e04e144580740c464000d1900000e680991007007114ad41c0b95250343d81030709030380c1d400708254001d2040607425070350a449a4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 64071279 1250 64070029 64070053
    0x90a0609020a030609060602033a1109090f013606030b1506030c0d0507120e07060801080601080c0616060f020702040b0a0303050316121a03070801020307080a0e 71
    0x8801000440043d81c3c003c500142824801415911603502c041c0441d4010070810708640410700306080e070200741e410b0500d00030903540f0854041c8020148580810f5140c2b0120300c42d01001d074402408011303015190900b4a6a0b14990800c50300e009116a18081c0900340a8040201c220191210031000040c00c0c0c10700c44c41c0b528404001c940d540c0d007007100e110600360240700307400b0420300b210703080c0c500220394091842c5010004134001e4080c2e0000c8110054a0342e020a41a03801913840380d00001c44403c003000002e91110702c1640d203844510820010810030700c0081400c00001c602d0034143c0f102c0300300410312100f001d400e002d065441000319122840c06ea09800c000110307a400750a00400c0000d0300540c90310038500402040b1030003515040e103e01031009080000a8002d019254400c859078841101012804c030181ea4070b09844a507440b201c2c0c94086d0035800c12400101e42c4040040c01d80c00c0729003440d25509014201d2205656400104400e440002d00c030314500c0e005440c02da140a419924150020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 64072529 1250 64071279 64071281
    0x1050306070f020a050a031112070203030403020409030c06050f071d030d0c0302030f0304030201020a030516020c010509040b06070507080c0a0f14060c100605040e07060804021504050d03030c0806010f0806090a0609 94
    0x250401f00c0008881c100d00551000d01048041450814600c0c3e45152444035030000e0340e00d00c03840c44003c0c056030301c90351904141400703100000c1e00c1302c1d04450305010500d405248220b442c032045035507802042c0d003c1941104104000078000a849002c0e0007025081601102a1105c44c4400012001c600c000c00100b030101c01d0301c00c00765004910a400143c0c4810500c0005000d0310380080c06040c51001c2c0e90702180c1d003142d0005514112510a0034015510200100400c000c0d10600c044140c002e00009a51020400f0004542c2c00701c4010ba01070329009420300080102078403203849075070860820b400041c45043c0240e03c9008005800400141ca0612841403a506011460724008105070360f4050070031a40c1030501402d80e4000403030016018240c103201c0058003501010380301038012003400c02464841d8031041d0444010707040050140400b110b0b503240040281c081d002c000b800182c1d00e640403d920b54000d00308840f2001040d243c00e5a650744100500c600540300800800d1070503180c0400040304256 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 64073779 1250 64072529 64072543
    0x2016021c05010e0d0e010f032c060f0604060e0c0309010b120a02010f05030c0d02070c03020402030c07030e0301020301120f02030703060e0c011808070302010f020c0402030106030b09070801050306070f020a05 91
    0x124600210381c80c81866000350503d500a03002138140161582d107000c241e03a2009a01d100c3c10403905000039010a15101e880c6903100344984484040d2441d00380c1460000c00088452041480075803035941e0b9035912007448240e601a106003254200310760041004247e16602969001114400028144400b4800218041800b100ba00000d81146482400b55603100462110089031403c00515509081861020f0340c03250400302d0811030741c04528070307007080445a04034000710f400600c250344906012441c8484c9902c0b002084010a843c0c1c4451201410103000307032812a004040c5e840c0800c1406d1300c0d06000e2405144040b80d150041c56004000141e0510034003005c4181c0c60b00400c4511503020024000521364070302d8100094840800b04902c2d04c00180301c40507250f080c07030b0610710940d4064041c3e1400d034660b440c41d80d0082c0003200110321107625a00040845800311824080c58560500c01e41d6035183c28000c1e1070301a04898005800c29010700000e00e56860188102c403202d02c059203906007440d070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 64075029 1250 64073779 64073783
    0xc021503041101110c1c0c08030a09090b0310020d090501060320010206011406070c080706030902040c0503040312050c09040504080904050124230309102016021c 71
    0x40100500c01800b41e41000411044801c1c00c06001491540d00010381e1091510030051081c08000d1034211008080b00c660000340350b020440100c03031921408960344030b8020b0400d01d0009482c4200004603203101e0300840858034805030143c07407a000e0b0085000041d501178107074005030a860302c0e08480020400d10400009500030340180c8600c6180000d401070000f600590355046502280060003584401d655600403c50110780c0d15035070b10028035040707201c0d0301180c6c03103445640141b01c0c00040c00c030b402d50000740b045403007140c040000e61100c020554050005880140018081e446100307401d900340c1d4800f5030041d9000007203a080c400200c1c001403c0d200122021034820f03901084020082c181030007000e02601c0249004100b60481c04031004417601c0d0080d09000300248561491092281048505c10389440b0400d0702d9501c0c071301298119035520880c2c054510041c0740c081d001c10080e2815100003d148a9640c0907440c05c201400881c40b0b004d0000401d907440740d540c03031003014076201a02040304454 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 64076279 1250 64075029 64075069
    0x515030d0903120306180c020a20010f0c1a0405030c010911040e060106020307030503070302040f120b09030301080a02150c0d17010e070e01050304050c150705011113050904030c02 79
    0x2e086141c40500c0b0515507901d40705150404809000090009400d10140d404208001075440350b0100f04a14114001e040a07000030031840d0714401c8440e860742c010b0203c2ca020f80750704c2c0d03001030760640495615581c0100904683c1d441200c10f00011462038010b41c1003402a07084908120401d0b40b040d003103800e444400c464100340320440c0e41250500d402410352401c90400030344244d604d042000780d1240300d0715000074200180040040d0116019606aa001d84208482a0001519071803144a150f089142c1540c0b101e41c2440040c186000010403a03058940c920083c0a1052041d0b003400120901c01c0d491044400045c072501100b0b42c001c01c1240600d080720340e10040212030381440b0f02100c41060700941004410f8104000c4890f42108200000c40d03400c1c40c10560704e80c1c03a41440c03801e01c14a81d20440d401120709601b90120080745000c0d01d070b40750160000300700c105d00c40001e0792503510883c0220030100781481d41c03c0106151102032154814024141090708404907800200c60075030001c3c010040c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 64077529 1250 64076279 64076297
    0x70c020d050a230c0301020703090b03040303150b03060102010b040921030905031317010527010917090117100303030c1e020d080906040b0604150503030c0102090906010203040e07030515030d 84
    0x30300d20402c15004c800d84203030300852400190b0f841c0145404003601030243c0315040040420304251083e44620000c940d107403424040d864a403204480340b54410741d603c2c0d005600704542c8410501d4544606107403141c4c03008142d0000050300540355031050a5445840902d0354901842000c50707002c0c002001c2c941203134101d0f2120382c2d00f006040701c0844903032105440d903685800c0801c52400440a44104c0c580c0458005146565400001c140984144403008007844d10040ca01c240d00d1002d00007602804500b6210340d05898900c01c4403610110b41100c0f00c00c81106c07002020030209000b5403104c03601050505d01010b0350b0890080355290a580754900c040140c5c8001c40d5005507a034400c2c50f058204100c00050304d0281466101c9100c1c1d0030018010328403a03030b6201c40d00008001c2001d500300003004050103580d00c1d500d141060b28001d41116031501d00581114000902c0c0f0741c4080100e03001da0f2740c10403100c0700c0c41e126018110010240201820b02c410a10000c1c0b8185a8007044420513a04c110740d28072840b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 64078779 1250 64077529 64077593
    0x31113030b070815190503010c030501061b03020606040b030a0c030f06050709080a03210f0203010e0f0601140a02010b0904141b010e0108060f1206100608070c020d050a 74
    0x40920002d115604003d0782009018810a00c1d40c54460b61321001c0310350100480080c40c3c0c0c0b0060180c1d9600c499415031a2441068070540c040c1c00081c100e5006440340055038031007031010000010141c1c0002c005800040c0010507030701c0c2c41d0b8412620301c0b0b005412200e01c00700310390b2000fa59400c1500192014148004506e08000c0c0c2c0d0f01401d944101c007072811a420910300300640d5602c4001c0c2c0c00c010248800d204905100c2c240c480100c10b00e8a045030300603c11801ca80208100a500c01e0080740d40102d804400100c40c0381ea103002580c01150181d45410020307171030018032580764001c00881c1cbc046540700d511405165039030400140c0528001d40041048480888103a40780a03401c1450951104039039052540c0760380c02180c030f010888401c0c03c200010f0390f9581d0001d14001698855585d101c0752208928201440004040e0311800040712050000750f1a00f00582da013a00403143c00b0001142031a00e6001400c046111700078440c455402c44111824941d5a601002c04c0780700300c0c051a019030f2040e020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 64080029 1250 64078779 64078793
    0xb060d052d16020a0b07110a06020a03020c1002040501020d110a0804060806040f0e071a040f06030e060f0402152a0c010f050c06040305030702121204030905180103021003111303 78
    0x410702c03800105a001000e59401d0038001d401454502400070f41050700058400510401a4240e40070358115070340c03404520081c00035000700603058214071600b9000c205032a503034070844054400c160020005200b009104580107400c282c84040d01307020309840c007000200303240081c2000e4a081d484d103401e00e141a0b018801100c1c0300c41c4811500031f040c0005040066408034441040d80e0100380e904a42000e80c40324100144145c0d44801141d02015400103201a899842400b035191b0040c1561001d40321610703002c00c03c003030030340300658070400c004004c1d960003240b000240b402c00b1110b0314005014030118412a81e48101c0d2064801c0c0f03402122206100350382c46a4210407a264606145082a00d0301c8601c598484000708014140b0500101080d007031070080100c0304d01180e0b0a080076940b00110010080755800580703048010034100c000c0800d95107010030040005000c070410156680c3e207541c003040044828405a6400e1540d40c0800715070448248000780520028200559003036403452800ca0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 64081279 1250 64080029 64080061
    0x70909080307170f0609060a080a0803091c0909090606080d09051002010608030910030e030301080d0305010e01050d0b04240204030209090309030d0f090506030106020d0806040b060d052d 82
    0x3c0c0100520008003d480906203c5454101c2c009a80200c07003660307044081070203410f41d07411610080c490040040200706030b90000b180f04695003c107580344282116150090000303900d0703004002c101e05280c00c1c08125013542c409034040b80600300100318680d407a0318140c104900311000e007000900c0b080c420300643c14000020080d0104510003040307007919004090b5124003881d0816841000e000d418001e80d140300b5044075070b60300840d8050b2035495a550311500d9580302904140b030b01084c100b00002030051182d1140700c2c1243c901078103100100d5041e135101218800002c1080f200034402c0c60401c04c0f0180042c0c1c2000c800c03010820010b0b42c1e1030840c010000d45160040483c8a964010016060503460108008425100c981850300d480502c202040d941850141c011540000001c80006a81540002c1401048032242c5404d00281c480c1410b01040d03590100219400c100200304500c2c2c4039446500c1664451241d40303501b040400b41e105d079500283d40001c542c0e40303000104cd091200501c1900400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 64082529 1250 64081279 64081307
    0x4060f141908040c03380705030403080405150108070302030606040606051606021e030741040b0c01020c070f0f0603020a02010b130614010908120c070909080307 71
    0x185003030409281a400c01c0c0c00c000c12400c0c0420024501240070000c40c5607501c0c01a65000c0128103503820860384065015010006540001e201414032401c08045a042e00380514240e950340c80c6151b031103450581c1d00715406030044440384a10101410f180d010448268081c00044015145e02071071801003601d03000b0094811403049140542c1041043d80040896201c01c500b21500200c6540500b03099000780078039140c503d00c8101d1120714110301c46480004502c901d155440701607551841c0b4000101a0940d1240c030403515100840d40c03c445210025500960310f10301990914040e140c3c542c80760700c1e4000e041c20703024983d0041845003041205010003000f03006000200b08016141c105003209084943c8250000e1650008030388240790f20030741111099200191611a1002c03000440138000d103079a01c2403100000c0c2d81c245200466108002140407145110b00404402c9101c020429480d884030620995610500b80f00003240c509501070032604501408010791a8904424042d00145440d03800d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 64083779 1250 64082529 64082567
    0x5070f09060611030714190c03021518090a0b03100f0b090c071502090603040b0105040c02030903060a0b1f09090c03020405030a030305070318140c010806011d030102070804060f 78
    0x40c6503c00380c1e002044d00e0740160020810150640c1280d84c1d181000381840b1120015a2850031440a03c0310800018040328801d0301c122920145c802c00c540064003404501c0c106a0510328a14034262401c41c51068121920210003e203c44910f80081e14003079046400d6001e860710352440185600140c0f00b4034904860a682da4240c900d04003130030120502c11540000c2548055402c8882d802e000f90303054440c0d00c1c00240040351340341407034240120b00079005d01c41c1510640c28156035241032031001c0103072000104042c00500d555100c0c3d0825402800f20740600c50b410000b40e0240700c000882c20326442600282036181c10b0012400c0a900400f030b0750100f4049014980101b1041015480010700711905542510340010320f83c8030900214003603c8081c2c0180404010f0b4595803007170021414865850300b41480c2142c030060340c1c650055403008011110540403410800c01710308040c00342800303003440110090005140c05030941d201134050700300d50480e9002a0601401c645966009203100007141b0030121 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 64085029 1250 64083779 64083797
    0x6050607030206150a0812070602130303020f010f02090a0e1305060c0d0501050102060103022b05070b0a0e120c060a030e010606110c030604081603020106092d060b07170705070f090606 81
    0x3107071581e10001e0b178407001f800490000d000030500c0040c0c3d055030031003001c101100d00c441d607503810000c4da40e0038070b200000055460001c800d03e40340624821141071503009840c03102181e16100c2e80c009002c10083c41e4194019650820100080040c404580300f44000c14070075480d0800a03400030220340f01600140d05541c001401800507986aa13513200e503e01030440c0151055650264600004000301d000802c0e911840c44007080102c0329402030858580c0a83d501c00c801809442040b80340c0a4050303940080d5000280780c000c01f170071f01300700921092801e0b0030041080803511a00c81c2c05c4407a030350301136400103480341e98441540400b4020100c04041c110001d00b03890500391035680d001e219200d100d199003c02c0010f41d4013014002e4205400415441d601042030404c0c04106242c81400e20080c4001e140030f56002442450261180805442945080781d00b07209440c1d59210801c051680b00c108100c80c18480080041d1040204001508004100010140c50721808130141d84042e04141d091008480e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 64086279 1250 64085029 64085039
    0x3021c1d07080304050d120c0506010905010812090a030201030903052b0e0115061d040e060105030f0307050c011b0602030a0603030f030926190206100f0b0909040606050607030206150a 81
    0x6c014005502c2e002030020007420406101515603c007072140007455400b070074000154409080e0b1015040394130003c20307280b0350310045038400d11910416010b9540701900070018000f551090740140e850a1090500c1c614011340c600c40c500d64007150b2440300034440d5002000d40c850307008601422000c019007000a020b5000c1d20b181d0690081c0d454000c48003000f102103420980b0313816641900c3d00f01400500f04101e402600310039680c940c2c609026240c06403203480c40d0711850032000000c0b2995aa001406040d00c01900d40044904c807000e10401c1c040c440c01980083c010820740d1005600a80344108006103c3d455403030003070590500b2103000c2c0c050600d450762200102d60000007442c001d001c240c50449c03110340060350074003035400b84081d03034003401d2099242d40380d810f900001e130b0314020f180c1074028100c1c450342c405200e08855400c0c06101030300f100a0210a0f26400c0c0201082e4005208000214a940e00c0d1008242d150304a50000e43c010380c00001844480c030705c2920045a214030580c2c00540c950700384 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 64087529 1250 64086279 64086289
    0x506071514010320012006010306050f06031b01050f0a0c0203070902040f03020108040f05060907030507090c0f0305060114031005040b0306040803010512070f06050d0c0206061003021c1d0708030405 87
    0x14030001340d4110101100c8400c1030b8400c034501d2602c0e5404420034030301e00043c69100b42c3d864000340400c0300d6151420700841d05c1201007400d00c61042400a0051030001078002c94a032034001030b00103550500000388141600550105c0140080c0002642c64100f035411a00400d89004a40c0e03001068541c4100700138095000a190346505036a020f00303240d0841d4980f4903041d401c0039402031001d07156004101c1404541c000105000c0300b00d80c000d008680005e521003d41101311071a0001010105000390044140c0c40c0c00b0341c000c0d80c2d011905061000c1003640c984d0100907254401c503107a07104160280014840341c0740520822a447d14150002c0c440391815031740c3c24080d440180034407441411031240120f216502042400050f0640d11150b204096558401400b0f07031f0807000e0303108002e9040900c120fa145100042a40c45418000d02d03d107c003801c1c00b142034000758085000007089807150b11100f143c5201a008518031203c044040c12080000c1c07040090034001a90002c0070303590000c010800190f515 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 64088779 1250 64087529 64087553
    0x50a0818030d180206030c041d06030303060d1b080601150c110121020406030203040212240703090c0803030a06080609031c180308040b0106020718020c030405060715140103 76
    0x8040010304958412811100f030540040c1c02581310700300104000000e41c52a02900c2251021044c81c028400f0b400b0a030400050111078098142e40700f4400108bd40c5400320a039401c1c94004d80c200340038010740007220000c5800c1c0e40c000c90790a03880040108003200d10a172014120f40d00f00e150660903030300d10340d9038400180352200c40641040843c103001d100701d202c80004501240f0350200c0456230395035247e502401139001100c0c164400d0f038070180e8510b0080300100b4403101500841d443c0341ca4800b001c01d0021070f4540c001d407aa1003010740d9003104c04002400c5840000c0039110343c4006544900d0010360322005e64849030000000f80d044401400510440081542c00b5081442c0e03c900c502c0c0150038501c0c00a154054403008908403600440c414141c100310340301d0181e4010390084580d683c80b0102603079500c443d44140c86980d03046003520100400c540d07001c0c1c02041c2e20751007585d00c1c0668490016409800140b0203482c400c9041c00395030140c5c841c51050305c003141c1012a5103003403585503450703060744406 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 64090029 1250 64088779 64088797
    0xe0118030f110102030c0304030b04060c170601120209130603020a09060303140705011806050a0e030f09060c0304031a09060f070804110a0f060507021e0603041407030b010303050a081803 82
    0x1d0b40301c00c40c007680c002d2066a00c50038007103046a407034650340d00302001040e5081d142690300c145440da1031134006118610003100c00113000d440d803405031600401152200c94041141e003015600f400705064a42e11441141d41c071041c42100855482d0850042100c45800d03075110340e1000749002001c00000390403419061990780c00c2c1010503207924031800c02902610070175a02d106070421a008101c200082036215074011b035024041003021a1079080c0480c2c3c0c920031072001002100e8148202e03507031803619100400b03401c0351f800c00f9139081c03607075a954110b48081d000011102e41d44900341040002c000030444550f101116040610a41c00d200b84054500c02c0003400c05002c3c0c0d149042e0b68022502c900c590a0000c10b0002c04210040d40d50f54002840303078100c2c0000300d1044481a514982030188680b4801a280f4014009880c54586586401c9501700009800c6894020200000041011000864002d5009440351a80c0c0d280ca40801426100000d118000819201c01e41601d00003000040d00c601340303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 64091279 1250 64090029 64090043
    0x110a08130c030c0b0a030c020c0105091012020d02070b07170105010c0534080307020906090402030708070602100501060f020d050307050903030415020d3b030604030e0118030f 77
    0x80c909003081889a812900003a201520401c00091280c03181d200800107500d069400b041040740c241c208a84466000b04003c0c0040c00600c090f10444c680360200143c500ca0303e0808164082e035110480050782c00c0901c40c181d5082e070105001c01070260b010181a4010f0081c075018072001c80b05191024041d1040c020b441c10880c5e0b80118900b008000c0000700408080c00e0301c500e110161452790503691059039a00c1003900e85400e0400240100c0000c25642c1c92607006141d50181e40d189803d2000e03550006100b43da1501c00c3c21400281c00c942030006c04041e149650180050345240043d0a0589106900035030030040100000300340e066021420080c64919458415170b41d4032404421100d0b40290b000865040c04002000131750f10207890900130b210300c419003c2d00e0b000e40030684c0035240c0000e988200d07001c4031424103416180450b40624088803000c400e00610305c501541000ca442c103441118100c01186541502c004a9030300700c41c010240512054000408508581c1d918840c010204402403400f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 64092529 1250 64091279 64091311
    0x140a0318150b03071205030d021602090106050301050f0d020102031926160f090308091c1a01080d0c0813150816020105010f05010815190306110a08 65
    0x80300d400849010325904048040e10395108a40008020080e402005100344120700000446040c00300440918a0b0444060341c10010220b0300b010103940300c103c0d00070740303440c2c000c41d0707074005030340b42841a03000c1d1100b9031f40c81d51a581444140110400900c003814031a42d8086003990040c0c2c0d0000450344030b01540c1c1540c001c50030040c44103580b1400d00003c2c0e00c040c44d009440349401c018a403aa001e01c030b00182d014401d0348180200050700d00f070b10050b04000014211a0003800402d000c00300401c0145000b604503a0016000175640e41c00c1445400210390030341e020800c0011546003400581d000d0100b00010304404481c405010745040c03500382c030090001d400810614074100c0112000350041c5100d481508031150340940082c05e0200462f108100c07511700b0030007480c00910500c9009e0584581c00b400d441043d040200568000900908082103c224505408500d0f11190b48000d07038821605003d10700c0500750b140000a4a0181040e001b680fa820301c05040c1a607802040181c004403045507545c51 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 64093779 1250 64092529 64092551
    0x9061e010902160602040b09180103030c121101050a0204090b100210240305010e07080105010e0403080c0903070b0c1005130605090a06051302010e01052106030a060e01060501030c140a03 82
    0x303289000d80024051a20104002400216038170050601c55021580301390b842741c5c6140c180d50035401c00e000103000503880004100c00205440c44090758901c05091284800810701c1c2c50394256070303080314011206500810100191361090043c440846000c0315040080c500e08140255950240c0b4108202e050b12070160058000c0302d032450716015803480784a65000d40d00c0e070521501038540f41030040520302c14a48009148101803042e94103031404420100782d81c0e1941d840c111100000030b400050002010440303a6810b03941044494000c1160100d00342e15401140074081c10000102c00c04035040d41050104111009203412812200e40d01c0b6070f00007010348810028610700b600b510401000103140c102844128018090001400ba03c01d907984c0c480c2110100046800e40603c03c00d50003002880c65048500c420104400390340203001804880c1564250784800302520000790130391082c3c3c1d541e007605000c103507814010002c024009003460301b095010700180400600c6008030b50350400d82d0740d4ac00819 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 64095029 1250 64093779 64093807
    0x120607030c0e0d08031506030f04020f1305090c010801090c02060406020703030b06040603151d060d1103150f09060402061207020304090603080c1b010207090902061b0609061e010902 80
    0x100c040400783c0500d407441d1052030402040d03070098400c0c405210400482e201d9602e043c0702141d1051129400851030b544803642440452252644441d40c840c03c0c2e6135044070300703919502c05d2502c5420403400511078034920800141c14510103030001480d5508210208192a80001d1308940181e804540103907a000a824224010011188500c2d0700030780000340050307543e500d80c103d6020146400304030342c008ca80e1540707221043c10390707510400803001c0490300081607880c2200802223100d0060160031003d000413400241480303044c001010ba01c200c41030900001200803e00c2951040c02d85000340700310700307040d00091042e01603414909044000700e0002207649200b8025500107241020050015a4a0340380030080c40d00800d41c010740310720a0001040c50540e072020318102d202410b0b00900515402c194107840605880c880682e008142000f200400e00382840021021100c0c00d80600914241001994100071003d00000207407803141c14800c80160a02c84102d045518040006035196041c502c201 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 64096279 1250 64095029 64095047
    0x1060308040e0405010f09020f09310b01050a03050a081305091005040f0603170a020309120f0f030903060c2a010c0201140f0a021b010623120607030c 66
    0x5085000c04600040d4030740030a5409030050f0312600080c4202c0c580b5800706021210f80820181d40100c524101400c9400c0c40310125401a8010f018140e03044404110704180c2c0401902d0820242c500102c082d040c003107074080c0a4098041220f004034054a592680381c0c0e00d134101c000190131940005480d004441c0d161034040700800014240301d0082c0b40c000c0036100303469924441d40d03010b41d00740350000c14481080c0c841c81c01500e500c840d582054000c01304515256800c00310100301540300802c003100701c69071011140408064104010704504a905018500700621600365101541c0107001e007042d10795020889a0380040001e0026480d81c150012580c82c00c40020440c2512841e6007101e20603400d41900079031146107198000340200c2a4428006880c49021076030034024480f8540800c0f820116a0014a1601981d40c42c0c0c00c1000f60382c3c1c1d1840d0855049a01c0404e984000400180e000e4215155900c7c3d60582164601d0000e0b20a81e00c82d6150302c0300030003500070107945031641c241940c010030b218 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 64097529 1250 64096279 64096283
    0x412030302030705040e040f120201020901020601090e010603061107020406050d0305070209060103110304060e06010503300f030c0702151804091b090b09061203070303020a0c1709090601020705030d0e03010603 92
    0x90351103407c09041c03086014080f0a400d49161401c040551140c0703005000b00c038462201030340200a036a00e84040388004141c1c98500500c036540b6800000041032190080b081203c000d4114550b480b503451042100701c400c00d0703000d54001c0b11005911804207030410107841825030107441015007982e5010049000b40741096500303003503881c0401800700f405401e5001b40601161002121003598a680415540b4040288001d000201080b03031441800a4400c20ba28451000c04126017481018520b004d05a0800c80d40c501805e14045407030f5042d480e21201c0300c1c1c2c4291f2100070300340c504450700c213403040300b004034484050213140c49007481c2c002c0003c80e48100c42d01107034804e000303607410703841d0701c041005000801d0805101d203200d80c01092862800700e440701c1e00c1c800108015460081e0710b80d400d602a4201d44180418018000041004910b0701050f940000948100c841c0e43d074020700c0b0030410f1100c7c0140080c1e04651041006018a80b000503c030743c0c01f48454200b0170011507050000a014010303d03040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 64098779 1250 64097529 64097549
    0x3090b03100e0414070501080613020d0e1c02010506040209150703090302090a060603060b090108070f0915091d010b0a030f020903030a020106051507050d05070602130810060b041203030203070504 86
    0x1080140803403182c400581304e260b1001c0c1d5011aa4070b800466000c03406803007040d4004107604544203030f440f459008102d11520b0341c4c0c010590403108952181851004220f140c50b080c6401c0d1000e07001982885216407184003203a04504200c034103408941d00d40c0e110300408940d1400007036068107160042141000031a8000c00034403441ca081070340940541110f1013000c010034101800824043c0110041da01d10301010f94402c045551903036011070301c52100c10206000d01c00e8001000c201411444021161103000e030f12040302444c5031441c13a841111060304489005082d1070f0051020300c0464088462442a620b0040f65078907800080400910412610300d506100000c0c0c48160a6010340283c3d08445045520030841c240d80b040a001521030340030002c00e00d4200d5000e51005d00e000304040d001850013981c00604102400b0218120b42100e41c108484540c8119540c0d65020007600036000a40101409a03041504e002c1c0c0d80100386a64240040c21b0603000320001d054203220343e064070024808019 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 64100029 1250 64098779 64098781
    0x6030c0c02060a022a2403070e0a0f0303030504120509010e1020061e1006030c050d0203070206011401090e0604090311070905190e060402010804480303090b03100e 72
    0x1058005040307510300c829006d0780b80e2240ba21014100c0c0c0442c00c001182c201c11031443c540d00d0840840e94641c0c0415070550183c0501c902081891a8450301d20181d0310075100000c0da4142401c1460304a08080f03000020420100190081a40e000c4146416040183c4106404a4074400b05030340401c02c100c802c1085030180c0c09400801e090005032140030741401d80d28440c401102c2e02e0710303409138001101c0765501c4007008001007002c0361196226250820f02e0b850701600309213507401042d046c1d900031348188005901090040c0220705500001d15800304003400c0c039907000c034a4488111038664008041c03511590f0380c0d005400a044c007030040104507c44a00a0f240410745529000c0003d102c02d07110740d00703401d503244170368030919070750b441180440030703840e4010822540c03690b004594043c3c00a00444880c1c0020400917080e041c2d118280207030f0900e42d80c8410100c10803c2c40c07001103010341e50440d151034204a030200046904103880340c050310100c40c8240ea803039403807004015070359030294407170070403800000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 64101279 1250 64100029 64100083
    0x12032f07020f0a0b07110f060a0815030c10050903010b0a06111504150504050c0a0609060e03060708010611011401030c060e0901050616030c0512031006030c0c02060a02 74
    0x9001012514800c4924601501506040c410544007500071038085000420041d40403d80c0340300d005841c103e0052510b090700344103c0c04200b040e0010003000c00410b0070002032055440003000030104604054000300701e07444500700000c50045050131003100b07100000820505ea130320207400c600c00c0440c01609001005e660380340020000318030302c2d803000054061001c2c42421402070741c28842c040c54010008a00440d00d020081000344400f03002181d90744908840b0404580340c046000d0020640381d190b124400740f030150054810114024043d01c00d4020b03134104255139421020141c1590741e54038042c003002880b417100e28010007001d039007102c0c0012001c000108100c69108600b05031805544e40790903488040b002c1c0222800e00380641588800180718150382c0c501d001c040d414520b03001e490032f9001040c1a840c1e1904002445640101c82c1100004105142e11007019500040c103641c5401c01c80d10704914401032040c6d001340b400a00ca56000203158009902c2081401c6482a140b251944150105 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 64102529 1250 64101279 64101371
    0x904090804030b1602010501050117070c0f0b0106090909050303070c03090f0e01090e0307030c15020d1514060a0207050d060e011503050f0102090102030304060902041805031c06031203 81
    0xf10b410421202d5044c103484c004600c1800385504a42d010384840d1201c0869150881180c00f000301128208480303800c5a0380442c091410524005014403403854080d4103045d8014002105a0001c0001900b8164914000b070000409c40c0e512503a5460082e000d000b0b40d04d8201e512002551141090b03030f18103400800c0d1707585245d4096048070090001088201d4403500089c1c1c890081180c00381c0424104d620080125604c50341182108144250052611030300040d04802c0310a500a81b80c207024404c0414464040ca811090005a40440e0201d091610450b0000d584a0441c041d180c041c0e140040400100b103003681280750704007a144000d02001030b1040c440302c6d101e0305c2840140d401d4400c007040424400c20610840382c2000341a070241d4555502c0740c0701d003130203081070342c0041360802e550b8070484c628a0045228913880c1d9214a01441c1d035080c901e0048464510b1a518800e512854008200002040800719101c2840e0300d0030041044405c104041d0805041203c12603004c01448503a40d050400d8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 64103779 1250 64102529 64102531
    0xf0c0503010507110a2a0603050604050601030501050a09020f1204050604050d050406020304050111100203010b03180115060c02010c020411040f0f050906060f04030f080912010b090c0904090804030b 87
    0x826802003000d6910701030200c0e482c1000c1e14031020160090160312010030104c1c140741c031030304079000660015552090794500c0010160f0740208002951041402503a1526010706608080c0c246024025035043c90002000c4a000e8843c015542d40d00003126000c0b2030b04c2c2c0d400d840111040c4061288141b4003801e2040d11640125003c80b824024514800785070340c0942e05540030760b1070760790081d03003042d081c9801984c41c454201e035002d2040c032400440c051030f008913000070343c040d040c000c108a49030304042001580296034541d19a02c10713410000e070b04881e40e0104007180d007140c0e202c7c5484c032030039849800140c4900609041c0607401500f048a0410b400f0341c00300c000c00c00c590200c10f0755828255540340000c6aa0214094540d01284103808900c00346056000380103406542c0c544a0300c1e1a980707940f4114002d41350001100d0040b8045060b1105141600403407a443c103115009209002d80c040000e140c5c1e00c0001c180440e4480049009103484d22907034800c00120f40d000e00d1160790344e51641005440c1600c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 64105029 1250 64103779 64103789
    0x1115040f12030911120f060c0c0f010b1f050c060108010b01120207050703080309150a05100b090307030206030c040905090102030a0e0a150c030b0409060b040e030f04030215070f0c 79
    0x7201d06040c01c1c460301c1080c80c0c1036000400d4a15449805040002e981c458a50001c058804d6000440c0114030030300c043c1c1c4c003404291300c5031a41d50f0100c000c094100400240c400103640d14200c1c00c00c0746500e600a032302c805c4a0b104450380c2260212070764140e403039001e07504500b40140b26210022030922070551108941d40002d80724404289043c10190060344a1488010680e1f0070000081000480c283d0246411031110000e0b1202c0c442100b5814030004012507000c0007107521181400500e41d8501c3d50180279049495801c2d250024442c0802c0e501c848607c0000d0140710b00000144030140700c1000e950241078201014031050401d500030a0107900103036054060f140c40c2c00c40f501031035800060b120460b04e0b40300b02c0000c400341e81002c3c002c0c000c1003880d0b41401459260742042c0c04039603961082d054000d1180e400025100304040130b020850742880b40c8481175a000b0802000c249a24a040e9400c6075411240f00c1081c0000700703214103030340c091600e00030251902d40f1412820030401c0040303401945e03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 64106279 1250 64105029 64105043
    0x5010207060e060c070206070f0201020c06030f0f160219060204080307030503010311100f0807030b09040b160503010b07170c010203010e040b0604020a080606070203070e01120b010503030403121115040f 89
    0x10300d40302092810761080d17060082d4400400c00c04900060084103007c107d6600500640d5070100c086404141d081e4802c88110a0781c1d06603070108402c040300030f18002c2d0050031403119589400c48040d400b940c3e50304100c158a04140c1a42110420040c081c3c0407980034207a40c0f41aa61101014500581507400a00007217400d010340c0581c2810030b0070400090701901c2c034103580351050900010015200100007801007820941c580301ca0f4135440c0c445000e000d00840c40703a85000f0180c98800f1580180301c1c0816858030400c41c0c01c0004001c1c4481e0395041e80c0c0882e0300241c80c0314180e1f00e800c0a2245600c00c1422201d0194008800080d10112171611300e4400c0c1d000304900900d07607a603042040100c1c03080b03425860102d07000d0390116405052501c00b40540a00c0a012142403e8075a244500e850b00240c1c001803600c950741e0481070800004c8440c050040c04203800560a150039550b441203402c44002e000400c0000203061102c0b543c0c0304101c01524035900c01035040c1c2a007040c1c1030810b12203144050582e001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 64107529 1250 64106279 64106281
    0x2041502010506061201060f110a0308040501050609010311010e031005070c140705090a02091809010b1e1003020f0d02070305090109050d0b010311060405040f02040812070c0308031305010207060e06 87
    0x7401c203a0201c03981401550050905a070070000300765500f407160300a4230100520076603010b0290f1801c0010a012901075200c000c400d02e003a160490075180000d0042c2e00600004004000107074068402d4071041d002400c08030907003030700c1d00f01080c0790600c1a504441c0031420178051003c541c1d000040c2582e00d601030348200c4410502464403031358800480c400c8940101c1d0007800030700303000c15541c00b030b000c456001008c00d41c48626180004030a002c05a801c0b040c0c0d80d40d141c005490711710b080229004d13941105d00b00c0710400101440015131044844036810281038000460403030074003034401240c03140040441c0c04c54940c2030a090042032600120800c0b400301c1c18001d00451a80b4254100741542680030207102c4503682565070b144a8054540d41030f6030441d50070b02c40440d50382e0361405020420001150016112403900d546280b404101c200740241c00d2904210200200702d81114500560350081c88482e03070f9031030303008c40402440c0c1c010b007003d44070713520104580c0e04000301c5402c0510751000344811100c0d6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 64108779 1250 64107529 64107541
    0x6070503010608070c0204021c0f150b0702040509070e0106210506100c03090b0d0506041a0612041109010902030a0f0e150a06090908030108011a1e13020415020105 72
    0x2140c8000c1c01020301046085000a036501d01c1100070f403e0042c07000e440903052207440030304195102200c25025840c0c0380c441024220252442c03050801e4544006c000078101072400260303e070300d0f225110000c1c0c040c58030b03440000d13506201005188000c256502c1c1d4035106603034829004007404007001d0900440000043e07410310313800880c02135038040c0e88000d00c1c40c1c185540415041e280b1860170a0100c0a00800c1070000840d58000c40280140540a01020503a803511408000031101411240003070392449004214198603408155613481990341e00f2078140351101d041c00000115400e0140742c1c0040f4620000c201015160042c0d4085d0842103400d1203000c00c840b00e4101615182c110780070070355002c4219401c002020341c01c8590420711000c80029081d440389010010381c0d03104801a0f0315100000300400c00442c1c244503c22254000113041e030300c800000000110019101034150b014640003141c12803943d51520700c1d4581c03003007103e40210341d1a07588030071514a94100d241d03c0400b65183c03400141e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 64110029 1250 64108779 64108787
    0x20d030b06220b1605011407140d060e0106091a210406111b0d030e03161a0a0e101a0411090d11030d020601030209040602030c0403050307060204030b01091a04021e0313050607 77
    0x40902241c0e122403121182d03006619249e60449150b40a05546591001446071101c1143d2800307402c1a50741c9000700d0f81002c1e646d1210005288003150790007010030414000d4412105011030307040d00300321283c48a8a40d410000090013030000d01c0d0381c06d0300002400100c140313a0402c6040c00d00030048180c83e190442e0350303800e808440800d00781045503081004a09101131601c84030009940c03240890032500030140c00040540b941c00ca0b48001c1031992010001201030b010040300144041400b024881070907180300c922144400544403e00598440c030704040084558010b032283e4400150441181800c24180440c441d503551402030300034000d0a05c02102c1503c0814500e041c1d0b0f4010300710744403607140c5903a030f4002903100620440a0100511020000030f174144014034a00c1c0c0a0000940c4032030940c1004600e094042c0e200445042ca0810344c82040301c1c10490a85801e4422540148c40b03081c0c21201174041002d0089030810f10200008221081b600e5916604002d4000c40440d200340c5e035850401c0d6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 64111279 1250 64110029 64110031
    0x206010f050121150e220b090312040c05030f0d09030f0606091e0f0e0a0f0c0f060c0302060c03070c0b100504060f0e060f1311070f060c020d030b06220b16050114 71
    0x202c068610301d440701c001f08851500b400c1e040b40800c0c084030301c1c2005040800b03a4400081d1801c0f50030704002282007202e440d00700701c5035190280c00d030050030b282c204008002d040080c4500c001060142d1a00d000300c18441654000b60080140120a026203d00c800d904004440182e0f0902d104074540044014001c55910a480c18400c1460081400c40855151800c80b91280d0344101c0300800014000303d003085030402e03040001c0034540c542100750b206078580a420418003e00101c0e001e1301c00c0c0100010350b544450074040080c1c0048608406844103188118402c00d0380d002240c00c9800c0c0031000514030001d90415003190203107884162140c854100300045102e003400d083d5484100c100144442307044543c04000040c1c0701c040b6180ca408219035458140c079032140001e81f12540d8442c5940e80464051040310000c4100346001c1240210f0707540010028062080808106d10501a20011030103038080d004001d40a00f1710304503101c6868030841c440240710044200d40f55400d12070000c81c0003030891046 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 64112529 1250 64111279 64111321
    0x10050108010c170105010e06300703060806060904030c050c10021e121219091103010e060108071403160801050103120c02030703080a17010f150206010f050121150e 72
    0x1480301590400400038940c206405c809502d0784c0c0c0303034020210400c042704020036a52108404080d00d290078600601210f036180c7c882c01c45a0003010800c6100c0e42c80c0d1803283c5d441541424414a2280c15040080c504109100c84507001119005902c46083d00042c013001040c6184603418084103030260038546450342020758501c3c0c0c807018804c034034000d20020291580400081d040305503d00b175064804080d1a4820800d44e02d68801c4100003102e81800c5c0502d10f10740702d0400007400954580404155540e00c0c40c400c0c051071055160311200f807641c0030300402c80020702240c00842581e0321211524007d02c0f0a00c0b048522200600c8040801402807502c0780c0035a4005000e04800c0307180d501c5003140351703100e2a004410032561078125031038407513070902540c040c00b4076520b22034449040076007240446c800c0c0268401554820b03070042141150002d104010f884c800e2800002e0302d21121100030101f85540c81002c4140d00344007043c014031844070462000c8034240101c1c4406900d0303607180301080c5030b001141 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 64113779 1250 64112529 64112537
    0x91104030204020a0c0501020a080105040501060f120203070201060305060c13060903050c0603070c02090405010c03061d04021009081005190204030b070305190207050a0b1e130510050108010c17010501 88
    0x20000752400da40941400155801c060340107008035079906003264481007054020603c5030300144020300300b40c484d0754050100f0b802d00e2040d80d81014800b0301021200201400107a40010025900030710030b401002c02540e01c001102c1030f40c01c0001c1000e246070000070017207a00740c5818000040091150248500322074000c00640782c1022070300d050115942c00181008140a0321a42d08001601d91349041c611460091000040c000c00f40403000301a01c005a02404000900c105541000c17002c01c06c400390003a60456141250b0364502c03038140d81c000340f03640c440002c034000e0b80803032000c0d442c0c0c98014910580d0140391518044c03020851000490240c0c0c000a0310400d18400000d8866000e0b50013580c020072041c14602d600001e007428081680d01c560002c40c0c240c3c102c190004100903020200715001521240010000e03028030350b5000320804010b144100315107502441304140001804603240c0d6180c510420300042d0384036407049000c0c02d14804c45c140040d400c3c0c0c509a2140c900c3c611014140c96059407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 64115029 1250 64113779 64113787
    0x40b0301060f360c02060105010503070e041d150f060d0c0311040608030a0e031905060705070f0f0b070816090902180607060b010801080a020603062e090f0911 70
    0xc420b2101001c3c0d030a040d0b5050840d0000c01000b440358040103080072044020105a01107841002410a203040e80054140507060080c02400350300402c560041031000e8400140d0381c52001916003600078050a00c9445004d0b06c00d84061520301640c03244d200d9144646201c405850b0202481002280e50030701400c030000741d0b2070510004041c00c14030480ca000041020800940b14910141160b004040d00d1000c50800c0b00d0801c240e045c1030100345911592603c0080030701009486081c0c0706c040052521040160008a840c100718000d94400e01c0c03260096002e400301c52046c0f070038500050055540901242d940320016404041010005a401c2c1066660000491802d04500080c1d08003102c2010b85804c940c0e5070b01016265080034000f50350007590040703140311643c0c1c0007500041060700f011182da0002c204807000350315040112500070600b900c41005120141c6c10184e003a40c541c0021096150090000c0109990b008403044242c640c0c02c034040011719504c090803002c4541e068403450100b98140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 64116279 1250 64115029 64115039
    0x16050d021902040513020a0e180c060712020a14070303090b07050726030d02030a110c070506030c09030a11090a021e0a0302070503030f07030c0507050312090f01060311040b0301060f 80
    0x5013003a078110014603e582249400c43d03000542002c030941101c138001440b482007100c1c7c00b03800c03004000d0f0b524042003d041944e243e0004524584030350040a80401120107100341c8d051310030000d040903039401045d48403003543c03d0040e86407550110320095001a21881e00840d0003184007007282c8800da40040108801d07890b084c00380e866203122a07021001c1f03800000d443c96082c0c1c2c0c140300030300b0041d4264400590300e01e408903004d000c0b42c15001440c1b994800510200742003035400591902600c0342140c0190b240e94400c1c011101c0d85c031641081c3ea81500404081c607040155050300d94080103400c0350b19a01698859056500324091600200d42022080b101000c2c00e5041000800400d4075a11300940f5141c4103884241c40c503031041e030340205400c0301c00b800c2105080e4144038056104407185403c07850281c094444a540b03014480c0d07000c8071700d0400404104c0c0b1400070406042d543c00020000c2c07150a81c1ca003030003807041030800f000038000c0d4108058414103203010300c07401095604490191410394242 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 64117529 1250 64116279 64116281
    0xc0504060507110301110c06100f050a0e0c0d0906020c010507030b06070f020f0301060312022103010e100306050a0b01030f27030507060908091e090c0d02090616050d02190204 77
    0x3c0d2825815540e280c214031030300c40d24903004000d02c80c0044000e103e182000109045182070300d501080042071280000c0c0031640d1960030100484403c08450070598641d9031b1010032902c14030703040408141c94100c0c10030800245030040c0000280d104002c12030b40d92040b00030744c00c1d2a003051800740c1c021020003010780050b403c52a140381460010f0282404000b00e8004a42180ca06802c00c1e00c01e00c0c1107418803221150304004007500d0070441111001d207a080c81c4a8040940018003900030340704a505d000402c4142c000c0c00780d6000f160008020300041c107000344440c00801070000c5032030001e810415640d501032098020007000c40c4242d951100400e00032900500c0224140404074200300d000c10501010a01a000d00c40c951401380503687d50355040e520400148150044d5011030504a9034600082c568039800180d60000c07264201594407056800d03d10000d1040340701690780070401203070907524a001103100f0301010344503000300d41070110a010160790b2410460003000030003840038008001405c2c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 64118779 1250 64117529 64117553
    0x9010309030311030f0103021f0e040e03090a0306020c070b1305220207032a0c060e030a05010612030207050a0b03270a11010305070e03070e041e0302030d0c0504060507 74
    0x70380380020b4a91660500d841c81544141c5080d088103da80005106610b006007a00400c0408074400e9103408003401000b0703103005040340480c3d01c01c640c0d591502882c19020310480f48900001882c08080c17035101d18141000b50084074014174944208000802c95910f0304044030041c0b40406900d1011515010030891011481041888400c1414803000440701041c0040c24065103e51034a82541141d00b43d90a1201c401c507141184a040003221030b80031491240d6100c0980b040307407404852041401011928054647d00d00410b55881c10000042d5140100300a0900d00e10070350a03034201a540e01c0401900c4201d6001c0c01c100c0220400c04916992902c1e4560b61903071000c0000c140b40b48900d2a103c50801d032582c01e0aa40c550b03840c0d84100140d40c3e061013500d6124400d800c20b46040c0c0710074004030b03503240424080d060812001c0e001003000c1c001200c610050180c07520322a03a44130050303403500944039001341890152050804128500d1180a1801c0d42c095610540e55582020f5150300c44000038a4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 64120029 1250 64118779 64118783
    0xf090f0c19090303020c010c35070f02090105060a022a04050108060703110a020a150204030506040c0f0602070b09010302182107050a0501021903030b060a091d07020309010309 77
    0xc0c0401c207101d80161055500406141c1c2916001c0300d0501d03500700a414814006400c1e410010302c078850302d00040c8203203143c0c100c2c9003005004441703800e000782c009001c42002c0300e030100504074041140410000009000ea51092017503906180a903130f10403d01c00d07e405100e0444001d03811580a401c01400104954095025000c03e03d030424040724004c02d08883e000e820922280c0c11107010000c81075014002c004c4200c0700b03191820f24104030342000035154401e0600041c65120b40f010100303d80406074060b10040c582110513281a4241850302c10030b9440c242c4108800724400701700000302940081202c00071141141c44040c0b03000c2c29140114000d52008140b0340c3c16004000058289840e0b0000820170440f14941c1c542420103100021881d010959100c94440d14002c1c030203200a99011030400300100940c003000f890490640b80c00d5018080d40040c05070000c501040c8411300652058580d4100d8017840000780c5003c000d40c5840103100011281360000d82d00c2000013070415403090b030015068034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 64121279 1250 64120029 64120051
    0x2090f030a05030301050d0807020a09020306030f070b0405100309050d0305070f090807050909011b090918080d200304063e0a0216030609110108010f0e04023c0f090f 73
    0x407627160b0000d15801d003150040780d40075030b020040000a050800c807121901203500010701c0b500d803400404145070f124a00a0b02d000e400c110f43d1604025000b50014400f5a91000984080103183c0c040200102411904800001c004440b82680300303015001c01c00030b0340d012002602505041100f072120595015040d00390540d43c0303418440d4151140b50440400c0d1503d03a441d41c4419103054000400d07a484084040040105600c0e000006103cac00b0407904801203010001c0740241003a02c80c1c0b92501c3c03084448000403880001000108511076200c0c0c41c24181496903030b18000d2440c05141464114000701203950700110b5902088450400040c0c1500f402c244126056124847c00300f9441c808242d104a40041e294008041006070b902c1c1c060703d11410038a80301210f17601d08264034401001904c0b0b05d801e014040804607003036464603682c003c200070118500c0c4656481b0341c0c0901401c504e0314844501c80f002950864803135454103041d103c800b12801403c280300354407000c001d00032007440500220940303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 64122529 1250 64121279 64121287
    0x10605061303110d1b0501020d02010e0601050f010c120306030c140105120411041a09090309030d27060c0204060905061e0406051203030405012a030902010c0c080102090f030a05030301050d08 84
    0xca8821040c2e443c103c00340c002c5c44d0702e00c0ca480006842e01888600c3c003029a41010030345100000c00091751411030b40c084904044001c801801a80c15403400c2e500641911f0003c0e10074002560140c0141007284e01c034104d003416480d0b994100100c10100345029500040c0c0130020044080c043c0d02a440d001801000f1603401e420503c00010215030744811004441841c0000031401d40c07074000c034241d038440282d0014500d07040d07170000026150220390800605106542e031038100c2200d400452520714103c00d2400344203c80c4c8810010340203580100c0101d00c1542450400b00d8201540e002d05801a0405000081d07811001d0300c042c0040b80640901c16001035581c1030008156445150740d1110b004032030007860ba00d00302400d05c5800c3d984825005124801443e0031020103803110b800309540b8429034940020010500d1004844007017030010040c00108070321a020911540c19401001740d18022195807490b60010010325456451842000e881d680091004020300c0c02c040490031441441000b100e464 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 64123779 1250 64122529 64122533
    0xe01030b0402130e01060513020301030507051003020f0a09080d020c0102030d0b040207170a0801120201020307170d0e010f06050a0e04111507080306041404150b0307090e0f010605061303110d 84
    0x44404004d4400101e130f4403000100485e090070740c5a0800c0c0c103103c420039840e540c19a100c9540c0d0300441e00c1918011034842c41000e1030075110f035059401c2e11743c1000c1c2066441c28000001080007c80b4005c0b01101d006107120100030b0ba0001402410509041e0055030a020b00084d40740d00500360029000d400640030408900042e02d035003c40340d0344094640d10743c3c1c0c0382ca80c001030007002000160081c0b420080c0c1009080007507030700042951401540b14200809400c180a03441c50b45006001010481e242440c41c041c27410f14042d0040040e00d0000da00800142c1e0b41e8000b0003003181100e1141c100010b004034080f81c0480d8401c0400d4414500280c406942481d80d0011003449900100058038104004001d1140302d103414000e44c003108500406008a07410503444208101d070010703000b605019502e010010b25501e0074070180c0020a800d0000704901c0c1c48268001c2d4070742d5000f2888407019440e140f400304c1d0310715005c000d0322625207824000c40e2046055903155000b1003400b050075a486030010043d500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 64125029 1250 64123779 64123781
    0xf06100504050a151704030c020910090e07060206090106050619141305130504050c04150503030c01150b070c030303050c0d020c030d140c090d020a05060f1801090e01030b040213 78
    0x8004d050803032080c030000c2024280141030039260b103540d0905900b417100303020129038004022070015404560b00200e9403078448494004181c5540840d1840f8146410340b05d4580300418248221581038090b03e400d42e68040c0705908030b030310b14000e0a1b4428002e010a00c0549513500070107030602907504007140c9840640c40b00031440d801c803881080003000703040f6092015003881e1190118281500c0421310060502d0382c0c500ba10786070002c0009005641e03850030b1080e00d0800c0300b80040100302c06400c2c0c0ea960700c690030519019100d50040501008105140010156251402c885440360404020003405080d9a401c0740500405000d02c004007109000c034040320070481c4000c025000d441c5c0d0040d541c8141d0103005070140d0b000c0c6480400810014020040300f41d071250200c50b109a402c6888907122486803002905c42c0c030840d00855040301001c1400341c1e01e40b09101c001c0c0303200d2802900d4800c11200035001101c1320765290064044ca10360b51001040051000c9034841e070001e200074402d0240c80c1c000c5844138 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 64126279 1250 64125029 64125049
    0x60813060204180f020f030a02070215041e15020307080c0c0402031003060b0108060a1a0409050403080619031a0903160507060e0a0b03060f0d0609030e01170f0610050405 75
    0x20082440030f006145042800344141200f1805102e000d5080c4216140b18500c1c0c1d000050403a000c0d1900001d1007021982d0b0310104031a06842d00d081e540c0c1380c50300d40c403400b060b008000c175280004c2c1a0880010030158080d0490300b00c180442d500840c0360000f540c1e00d58440d0740010350500ba403407280a41424040d40c450002c2d610546031004c0389041c1ca4a5410314100f5282c4401056061103090000c3c0030941d21602814419a480f03c000e0150210705007200a0b118030540e480014020310b4001881f040550080f94240030362002c07100c060850400d01400c0710703408090700c8010411400000000c0106601100c00e50b8040500d50603241000f11002c07441c0d560100c1c0b080122516080000b080c0202c0b50070484042015809507003030118941010308544282c8070203402c640c801c25004810128969038100c0041040781e22001c180403503401490041c0890f0a10502c0a01189010088035808138010385982d11440c412840d040950f02c81c3c0c0144004210305c200301104015081002040c0750319000404 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 64127529 1250 64126279 64126289
    0x10021c080a1407091e050306040b0103050c18061017040b07140903031206030106051f03050a0e0a0201031d011401080606030a02010918020702150a08090610060813060204 75
    0x646100e00c1c0c10074800d030450b001010708100c405181d0003400940ca600010040a881d29984103240028500da000302034082d450b4080e6070705110303510402c81041620300c0341a0490380f1030802c646403008950200701003008821501410b403800d24000401c140f4001900c0316804d1054103040417130440b641e040e424503000c11281598052558810710030000e620020300c10120480050407818082441c0c002034491085800c1c2138590007260700854065a03080d031015006003002007a020b030400c0c100c44d07840c545200d598210400f1916110000b034903041a8010380b080102c07070380b002d0f28071150300758010340041c01050038000aa40790b403048951815800d118075200303446107520340c14003985040d0040d03141c00c0005201741c1c060b8000c481e24000503604948808191000d0b200d00d0850003404e82c40e200000d000d14580030390b01c00140005010741213401c0c1b0003003109034082c0d41d03100308654440030603994850080d501050b52942106003040f40f90312401c0101c0c0c00c00c4102102c0c6001007285c1e1500ca041c0d8029805c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 64128779 1250 64127529 64127537
    0x9150409020a0207091109040911030109030c1b05012001111303051e030f0f0d020f0702010206070306080c010f180303030b03070f030b07080a0207020307080c040608010b0604030210021c 82
    0x2c404442030301003094030300a066081040c402c2c0703c400320880311180602c2200074000c5441d1080442006403600750b00745080b0000d0000c201425060a00408010410400756920790781c2c842e8555aa0b000e0050aa0a40da0186c4814560390350200c103044461482c2c014034601956540c08203040400004020708198161000c01c1c0500c5045040080c18030350381666100c4042c1e840042c4002070180881951012047c00784101c1d190f403802070b0040c1d83e0b40300d4202648107183c40080c180949008000c060030010b4001e03400c0740c1c0c059031200c4003034045400f00c1c003c500c5290310000d540c10f010b6102d4015000403401a03e40038119020045034100240e00940044001c66140c46191140d401c08004403402040b9141030707506503902c7e43d04c5803804074070050840420041400700203004140e240c0c044500e841d84c05011254007540e203540d40c940b140c40c0310103260300c958280000055050814010380440420003000ca034940b038616030030040103e0b84844250198000c05510403240314500d8403048513140d042d11 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 64130029 1250 64128779 64128787
    0x110f010c0e0411120a020a17040c09050c030910150e010f0806070c0b010e040206070206070c0e010605040501020309040b0415030b04020102010b09070f0e0103020c030a0306080c040c0c080915040902 87
    0x4100000e071114212800110101409130b000c00116018919810100b4588010f07503861450b501203a01d0f0304083c51003043e0300141d0080c041082044080300003141c2603003404101c242c03102e074035800041c8000d403001c950f0780e0720a000c0d003961698164401009001c3d11301500c0d15413130351081c80381d001050981c00801809548202003043d01c50a00c4055409020351428001c1060f581c2d5520003000f606010f001004d007042400501103480c1c0d041182c18242c1c0042440c1e4445401e4075044d0300481a80c003a403414020ad0400004031140150305032400d458058016600341f000745800d10009201e1202070320361041d00d0310092004600007560800243d070140c2c240d1420352400c0d00019081d18105100d00d4018800c3c0410409016030001200c01c03141c000e40b828101e00900c0c3c1004802a0054510000513808002030311b00140390954860b600701c070041010390b410203d05908100031207038814181c41c0401c0301c9101c0c880015080b0300041040550082c5a809c0c03002414850744441c2d00250803c640d104e034001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 64131279 1250 64130029 64130057
    0xd060902040807120305031609030b0c0705010c020327040f020a020307120c08120405010e01240b04061b05120d0507080f06010905010c030504050315070f02011407110f010c 76
    0x300c9184054580c3d0888041c82c400b844e60010107d2000400780c2100342c0d00783c4001c10031544984040c8000310380040300649141050b40e000e2410382d20414084645610700354102990314008020381c2ea09280134002c00610810100f00e07041c600109040d255801a43c4251b030741c182990a00c05802c46030296070066490700b20f2441d050606e2140083c0113000e00010700c90f42070028550700111800c201002d082c02038152240d19019000d000c00c1c00c4800f0140d401c08204e00d425480c1d400f41c00b00800c03640d07070006207441e60340c40c200707003040c407690007104001410586030001410100b00030000346803052003140d0b800601d5203c070001e280c00c890041040c2070b4982c8240504c0c181d002c0c448075000801060200d80d43d05000300080d103100964070451b0b050210709803a040c103050145081d60f00400000d4251034021110101c1c1c01410041220000c0110340640781c28010305105100e2020b10f65502031000002c0d88400701c0c203803090038910840c8120380c803510040c0e000d140428019084d00303411540b01c1e82e40c0d600b100d0f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 64132529 1250 64131279 64131283
    0x1090b0903120a060302100302180d050c0114031608040203030c0709020a110c090402041814030d0e190308060a170a050709150b03130506180c040509031e0d0609020408 74
    0x42d111003192404c0070000d20160382c0d242007040c0da14655081c010303a201c08041c64211606500f4a81d00c0d44400701701c110006209002c144030507100001d9841401162001e154260140000c3d1110b400300c0402d00c21011390386e400340c06a243c100d0b00080849083c0341e65503901600c1d110b0b4641188800300c1d0007046681400c0d0b0400e201481030074036034000d00307030426200c00481c6c401200240041d01c569214071000c0c41c0c8910901141001c01d0b0406038119540c502058070302e81e254005119500d0f1545070103480d10310400040f60300380c01d4113096840c14060400a0f1411601d142020381410340c450107101c2d001484130b4a00e00f85502510109010340495415414036905081c42648201d44103420300c48000c10002601d0703000e0060f11030b00301240e41c0f241c03141d90009070a0b507210038004010340b05000620414040c0101e10602c2c4000d000100c455455400040c0401d0365401d035103907030080d4418400d9010380b003181030070f603410001d10050386c40c1404001c204900a0303c186134481040a85e000506110003401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 64133779 1250 64132529 64132531
    0x80f0312061c060b0f0301020706050108120f0d0b0105090402030a0e0c01030e070905040813060810050f0105030c0a0c0b070e13020301081207110604061709070503060a0e01090b090312 81
    0x3140d41d00a0b0040e034050b08074030ba52040000900c8aa03541c100f512260361001203500d1a180b01a000715110740c103926165005040038021030b10184640b20600e0317010140c44c0304403801c0c003100703c0001c1c3c100802c0c1002ca1010708110455281441014480d081541c0c9691014511510004101041c2a03001300c3d90a414204650741890400d0708000141d010300c84001070304800c590940c40c2c001090ba4403800c00701054003030303800c81120a00c207203400018800c0c0e0010400f401240540824200e040d0350394104002c0360890703007146000c503009200003003109001e4000380030a02428144008240440e40e00e52004420840d003600100b511560007074091306001c0d0400402540b14501146107506061502c0c0c0d9401c410744481da02c0714000607404040100d62085807486480140c004d42e11142c403518003506084044920142c004006800902c0800e030002d2018111171014014245a448400c2450080d2074a424510b03003645d280c0c1920300010b080f20405500c038101e00710281d0780359521504d0101d85980 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 64135029 1250 64133779 64133791
    0x110f0d0b040e07170c0d120210020412082a030a021e0703020904030c12020616050a140c0102040b03010b070311060f070f140720100912050304080f0312 67
    0xb00e0700c19148103201001420707074140c1c0d88001d003004143d180c403003e981c03402c4420004603401c561441c07400c008010507040084003000c020707000c0e621700b00c4000031100100c1c083c80c03150512148440f48400080780303281d00200806141c0b02c00b0303050b001460084200c010b01c810008c0324660b500024800001170341c1880803d001801403200d68198568031045160344400c6404003038480e4000e600800c0c201402401100034290b440440780e01c40c5181c0e200c019481c0c102c2104c03140700001c0554070b140065807150b0300720350303a031082038803820200524440c6a410302d800541a2076140d43d4208004a020700080c40a14000c003049000035a50341c90b2464002c18480080040e04107a502a82c284207481409801c001d0303020056280005456041d1042113402c0ca0821210583c5400c00080040c1880346170340c0340340002002c00315810042010201403004101c40c51203858000b403000071080c01032002c41c402c05c182d114007031000c4a050130781b101d140a0a0008020b41c5032846e0348005502812400b071048070a034410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 64136279 1250 64135029 64135031
    0x160503011a090103020906030f15040506060d03050a08060411070b0a11030f040f0507050405010602100c05090303040303030b181312020a030e1002011410030309080c060405060a03110f0d0b04 84
    0x520007a000c80c00581e01800000e20400c1004006180c90b20100251520607584100b298501402514170600f540d005680c156250701a8100041d1282003401c821818682e0640c0d80f0b900d018106102200c040c1b00c0603041ca80d000b601c58481c030514519000182c408980142c1207060076040544201c012560680781a503c182828030400000803603181e42d42da030154028000055000c62860054104881c5402c442d5006103004c002180d4154001030814001d803000030204100115040b041d84c03540940030301135a055104100a00000e403098000e05100b001c041c2100d00308a1a1340c4503954443d03402c0710f092a030202030030380381818811032140c0c24880d04190700113006c090b515501c0040c402030b5541005406801c0c58100350f082c19100354448000c5030203421503d02103040c2041c1503016010325203c141c00195201030040703421000480e681c041c01e5001807003030b4034240c86d16041c03201e15004803020805261387c68048d4107500d000b20340208118040400c045e1350b00c01e402c2c0c0e218000ca40400c040341d0701135 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 64137529 1250 64136279 64136321
    0x1c0e0409141618090201081f030501050c070302010b031513030306090c020d02070603140423060403020c0a0509060603070c0c0e01030606030303060e060915130f020702040b090405030403060c03060816050301 91
    0x2d42d80003d5aaa009071448111230540c0c4c0750703c00d280d9506c0c030807a030000740b041d880e080c100308001c400c140250059a1090703009112001d004010903035120110414115103078082d0000c110000c28120030440b51a109080201314243d80e03004a44c121441c034400035001d41c01205410041d541c4c10702c42480507003820308040002001242c004444590001d10041c41e0b00491a160f80051040c0644811441c03005000c4400d1490a0702d0020345482c0e401614078003c08504801168500c4c000001324801c60019003262300310741d6031403400c0b100c02c401640d055402d40850710002c15800312410742c0d5400303140200c0c0040344081c5186001000c80700130398841e24a40350303080140007083d0303035840c10b403900840300d20240d403030403101d0b03400107142c40c05420001c104440c80d0443c01c1c00c180d461900684140340c0202c2d0100090703d0f06009018521030211030040c92904100024800501e0030340c0b0560b40c0300e01c01e2500142140d02d80b20803910b820201000c00aa030004030348100f040745801d025000c0b440092210305503030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 64138779 1250 64137529 64137533
    0x150f0402100f050904050402010c0b04030215010906060210020714120c0d0906080712060f031103010b040b010503130c0e0403031a03071401050c03090418051c0e040914161809 77
    0xb9130040e82c001d103100356141d001003000d5a2241074518503140d000b20402c4c641d401c02d8076019603120140e0038134072490110302340002403800c028413944044855036009070040c101c017088024000d6100d84022070b51402c0303001103810420300401915206800100d15541e5400e828031110340b501028000d001d0030040420400c3c4200e0740d000c03a6154000380141441d040071500c00190002030316203508010043c0e05042d03c00014005842203170302c130000c07041d0001c010400c4080c0c03d01003a215500340c02400304030300700007103820340120142000c80c1d030780502503860020f9103c1c8100390880400780c4059000a4580c4201d88908010400b20344d400d8004500624803e40381002201c061a03030394036068140180401d40d43c6030042c050040f0ba030b80c0c07000100100440700100030990010518401d050700c0c58800c940058640100b069401e00701c46e00c480d201d554404004008000103841f81d500100c0e40004148a0500f90580402c40c090302c1c42818004e40d8030103803c02e0000702d030808429000850041c103040880b40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 64140029 1250 64138779 64138787
    0xf020c0301061410120c030f1514010503040f020409060902030c031c050c19030f0807030204030309030b09030c120a030b01050405100e1f020601050f12100509150f0402100f 76
    0xf00b8900140c8000710b40c0e10030f0a0041d221a2804083c4610043c20040c1074040a41d0588c04031500f0785002204000030004503070030b180308003410f014008085000c0b403290362043d030043c4080d6611a1081aa200502c00d03c0d901040c1990324072001103510507250401d200842c41c00b80100401544c0550040c400002141711030321886e036104003c101440b40c00a80507040400c00e00cc00581c40349503481d920f0700000189402001c01040c0003e1100042c4c0d0f0b42b001c10b5483e8882d0003103c0c110ba030965901380304181591204401918080c10345411444200200c4c2d1441c641031141d500c0051504c9840c9444103500000a020f0381d9440c030704617041250400c001d0240d583c80c140804c1058095141100200f104a00031691070001c880c0150700d034a00740200940c2081d40001d045050314421780326140c0124441080c071401c003014000d0640c1e5904024294491864140e00c0641d210024008589844000481000c5481c03c01c0c0ca075000f03500300c3e0000700000e609004160a0442d00381d481c10600c48003807500c0c024 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 64141279 1250 64140029 64140059
    0x706060f0905090f0c10050d060e0708090303010e0703020a0e0324010602010b010203031f170a03030f020301030206122e150f0903031103040b0a0206070822030813050304060f020c030106 82
    0x10344141500b085400e02144101f041d206586001d48041040540343c1c41d481c0c601c01c00859109000814080c00140204408000c3d203040300c161818038199620f07005001c1d80a5040004510b082003050704010f186035908100350302c01810301c44c0c0381c2a454108001204003594050f00f00000390385c14150b1034101640d0002c02c072070b0700c05960f002e120041408004000100802c2e5031109900656a500ba010240f41c04600100e1052103602c00b0484071528840c12426800240720203540314030706002d0240304903d40e907002c03907110086055002e9900c020b1164155845081a1042d10015468605100310610000101d01054113030410500e8103019643c000d00e42c40882c0002400c0244030046041000000c000740d4014141c8045501d449407450000203540711821100f082c0000c0c1032501160300070b00c0c4140706041d130b044280d1108021003551344050b00c09440c007828540c030410358050107001250060018201408140d660303400d20600720030000b841d0028507080c20f03210364544201000500003010040c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 64142529 1250 64141279 64141303
    0x10c0201020f090609040608010905150708040b0604051005060315030601050d020a12030e04020d0e01150305061f05040204140306010b03060303040323061f08030414150706060f0905090f 82
    0x4d80d0f03218800d2000c140a0003040e0711140c0a50308042422003041008a02e45450207400c071200c502942c0d8030f280855502c0b0080c0d401030319294021000c90b01e91f003400c2d08000e80c0503102031001c40350a5a10f002280c0198812255a01d80800a04545050b40340500007140100000c480ca1800032035150002080581944114088400401e001c80304042c010011074a030318600500454032100c507034058ac00584090250032080b1751801c0b0072681903c5090094609590f01f06e801001d03155600c1c1914251003500e1500d0290340414004002110fa5803400200064540c401d040441d00c01c0b400c051515150307041e00f14840c1c4601c02d00401002781c80005c00d41c1d08403a080081e8203540e050480f00ca460740c1e02d41c03828851a90040d40104000300940c0050740318039900c951540d811786642c0f0851161203001d40e00800c0814030501100c41d00d41e180001c1c00700012540110107910304840343e5280d80854003c0c1d070002002d02c013145410090400248929940029910050001c5026860b401511b8030301c0d035440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 64143779 1250 64142529 64142539
    0x1103090316150f0204031101050304050a080c011107060903140403030e0f010516050f070b1303021009080a030e01090501030c0c02191a040302031212040f06150605030603010c0201020f09 82
    0x600c8052003010380c0c12032003001800b001044070000100002e00130f984a0f000c140c4160f40c0d480b41048440d4421f20841740b0480d0880c000d003005018555400700c40c1e5010412400740d40d0349074203840d640c0c108120018000d0511684000a1245907860041e03c0401c104408040080d004c0c003003080441c0d00080840300c214030807581196036a00c148010780b445d000d41c5807103c0d400c1940c00041d2003044070005040c0c80c801089000c5403c41d0fa90750100615500c80d01691120407446028100700504088005407203081c0542002da010382d4590300b0003490800c1a11055001480f500201100b03543c201c02854060f000a10f0305000e4419514005002c1c16000d5500034000c60400e920292015040f1f841280940303c040b441c0c1c0a070318204048281d0f50b4019000c01d03482802028000c01c90020400200d50341c49406940c19615590343d6140d040c0e03070801b00301040e5203d5840b258603102010341b04038000c000c0c010b10f4582540300d06000c400c1c1402c5480c0302c1180b000352380c8100000092250a1015110f003c1c9003110 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 64145029 1250 64143779 64143817
    0x21003050903040905070c030e0a12060203060409050f070603050105060405092205070605070303061d13031b3e0609040905060a0204051f0c030509030a1a010501020111030903 77
    0x91070700e14400c03139001d00407191400083c0401140c1c05071000100c94002da41d00c42c4030000100c2005015041c41c400e10340000840080800090003c0c0c000c3d40c4c0c858401000010721032401d4881c0360400c5c411013080505604101421b002080e058401e850242c00c0503034415080c1824540464240303030000c0c0108540b4850041401e00c1884600e8a000c981ea500000b664203007561100040e141d5005120202c02082c00c1910203d0020701c000401103107041c1d441103003407007a103480050341d003080300d0490251b040005540c1c03009180000d4221a51311030b440b40b0903a2010302e542e042041d400000b09401413a600c0b031002c000001c3d499071040c00321070741c070002c0300c1c1c990760303a8003200c00a001040b01c010014480c3c0128002c00649060a5020340129101641c44801d0094000b6288100e4441212040e01007a04e00e0131001c00700380b083c400341c41c4000d006400c54080c100700b5100e4504c2d090120065121056650300188440d50782800394500e07200408030711904506283c07140644030b0041082050740701079901 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 64146279 1250 64145029 64145041
    0x5180604050607050c010b0d03110c011107030803060d0c0b071e23070503060103060209030c010f09090504030c0501150911070201020601181104090209030106150e0409020a080717010b01080402100305 88
    0x1d403010001010048c2400c20306005460045c0c0541001c1c44d00b515940607400c00b050f1075500600710314807580d41d59409060080e00796546e08806400142100e9081096528600c00040c0414500406070810030b0800ba15024a40340c03000c0c28004000450304840c510081050008101110403142940c40455007a52030341d0507070125141100c10382c00301d0352505c14800000103100700d680c0103009402040d4103030b070b00000003c401541c0ca50a20782c100e0001070035003941042103000a604c0503030802d103c0d18000381c440c0350544406096402e40401404148604402003001c8110b5104510b0305009241c3c08508001582d00080d41303a14051041d0300d0609950f00091402051070340c081c000e4000500f0416884c1c0d82c503880500000c2d0030500e041030203503207800000b040004080804d4440e00c00d09581d541c10401402040c40041c01220404a8002400035004540c003c001d0150f000030744191813400d822050034904003070a4810019131181482004c074240005612070309a8a10720918600300030510361654 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 64147529 1250 64146279 64146281
    0x110d050a12052508090c010c05031213230105010f0b0a08060301020c0607020d0f02070f06030c020a06020d021c020f0405010804050304030c0e040506100f050d111305180604050607050c01 82
    0xf1018010403542c100000c515419040151107005000ea2030498810034800710064907a09800c4001070900e900903c602c203044a0552101e0f03610525012080310030b81a96901c85050468143e0300d1040d038403044c3c407106050f10b802d104080c0181040c500c90340d031a40c545500400c0742d102d4801c220003040b840600180d1035880940413500c004207014100c440364a441e15009403501000200003000511080c445c50086100080142c10b65030b400b544101040e1500c1400d074001d0010919520650040c0388981c40483c0144c03010f04010160003002503540d9040380400401c00c50303041c141100031031050000d4908180600300351820b0303c40c2801c00400c10f40f01c9060107403441c043c1d54001451050250b4002c03400e08892107d00780600d101b0411143d02d40c4450b00d03d0304a26405000f0000c6201850b00704100310301d451080590741500032489130b4103d0450130041086905484020255107440d00244207008c031881201c035445802c00c1c2c010b40101c1c105a502c0a07217070000070b0032504c20002d011504941010003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 64148779 1250 64147529 64147561
    0xd022a041e061d0412270308090406050d050a02090709030c0f09111602060a030e0106080303100503060108030d360606080106030503040b030711030a110d050a1205 72
    0x2101c200581d00d00804610710016100c680281c609108040310500d848108a485042c01154003058044100d04003a40803502c107949031020448241c01d00020700300182c3d0361404003001e140110003560340c80320b076a030612059481c40d52080d070044c501d5043d49800720380302044140d9038a50403698801c042d100c85c00304490014841e08050402110074400150803c10510380d60201c1c3c0c070f13007d82404503450789180b480b8a80200b00c0e00740c00e03680044800d0001803410074020000040c0d01e040010310701514050b03180c00c440c280c0d0000300c4660300c00014003200351780020b11745004107400c03001004250305041d41d150700d9002d140d5024003625101e1030381c2e800b80e40f1052441101072690080001d0302814002c12900c40c001003101c2500c4151904a0108030700d4418001c41c01aa42c221000b50302d0305207854a8401b0700e80c0000c0200c010002c081040c1c528500c42440141f02d2034080741d99045070103500410940c24441805a40b401b480720400c118042c0640000c42540710600c2000e000901e0346d15100040d1060b45 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 64150029 1250 64148779 64148801
    0xb01120c0e031e1e0319020a1104050408160510060303080405120c100b010c080f090a0806060609010509040204030b0906010f061707030902010c062c060121060905030708030403020d022a04 83
    0x5100214040c02581c0080c172232502c07a015149415102580f4002c0c17104540064502500c0344208100883c0e00c003045001400900b48101c084a00c0094000e004500311921034004400080a101c00c0c001807160420070503102210740d1030301500d84500d02817865500c0c0071140440d8003c41d2150202c08080c3c0c0145c0d1803104658104450755a582004445441ca0750f000005084c42050000d80116040301c2c0013800790b20602001c1c2c5054a000764150040d1070b6600181c405c542d0050b000c010120000d243c00c004107005031000c00041c030700f03035050040030400f4901a81004040042c101e4031b00c0740c0d401e5400380741a00080c841c20f0015171422540012240c140c4c8558018148a05100c080d2201085043c00703500c0d2850809256200400407480c1139450307410a10030800500309140100000000002403202a6889440c0010380354000390b47d1141540c100000989003d030000c42040281501400f44103000f009030f00c083c10b01c0c098100c0954806401d006d842c10f8200e0200410340b0780c65182d135800b40c40c041c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 64151279 1250 64150029 64150057
    0x101d0f07140415050a081602030f0f090a0906080f0607080408030406140705130504090503090f030f0604150b0907091502120d06060e0d0b01090b01120c0e031e1e03 72
    0xb003c000c030f0180076544910001400582c1010009007090b41c00000b010003203206501462911902c0c048424103a084500340f04410f400801c02a130303141e81c900304840010b019080b00420f50327920340203c940c182013001e072915a85070005010031020603030043e42140d005601c07401039a01e0784c0b114101440203100caa81c0128000c4009021320030041e4000c8058041c62107551400760340c4580301c0d018002560301e0b440c4003d03c0342c0e0090104001034581400e04c000e4450000c1c04480103070822161440c0341c084145c2d0159800d0780210210010001c1c4c5d0b0140c074032507040c00e0391003800c01c1c00d0110b401131980301140300e03031281803941d803081c90205442800038600d050705200c0c18a4940c00801d10000092070284180030104185d032a00000608082c601440e005421480e423113103503880c01301590040c01a0181ca10704000c0c5a4031500701c0801d8a03c14412000b90542c0e60660200c01c03c01032518101c001181034612601200445240810000d07442506c150407140480030640010105441c6020b42e0011242279 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 64152529 1250 64151279 64151309
    0x40801230c130608040f02040f050609010501021209090406020702030d03020d06090603121d040c0e040507031107080702030102090603040f0204110f270603011701060e040f060c0207090203101d0f071404 89
    0x240c44182c1200340284000c453303980841e66a94010381e82c6440056075024203010074007443c9803618119140710361050050201519000b040d6001904000f50b810500000c281d000c20140742000440c481c00d409041c0c0881c08012450840d100c1c89003801d80c44203141c00b08888680f40c440031030078654010700c807424013800900203040c1002014100c1000c0841c0709003c0e03490000046c000b14401d0003548824811003060604d0409a40c64600c043d80c0411401c9e6019902003002c02d502e6280c4000461140780030b02c290f140f29100c98070400080c2c890391426600002024031810100000520403642800c0d02541c07100414407820f21540c10701541411142e5000c070012000017002d050110b040c11008100310b008200701c40d110314a40040c42170588020b000250180200380000700c20f6803040005d01ca4a00440b101c880d41c682d451b100b0390b030086980f02a0f010804400b00503602e0400182803e2140f0390441d1017251500f1405d0600d6000300a111104004802d20818019200402240c0242000c41440000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 64153779 1250 64152529 64152551
    0xe070b0901020105060306070f080c041503020a110c011b020a0e01080303060102060907031a0c12010308181e040b0a030602030405070f14100e06040801230c130608040f0204 76
    0x100d4010401480c003550030880010564500400e41a20550b89611500c580703100310030044030311040041c06003030029810000800e800780031141ea05810800d035500903a803050204801026195550703d00002c6501c00b40803182035a80086140c04a9906000000688842ca000040d10300001c3d500c03c500200c5914004101d20201200551003200207808480c910303103039410300c143e0328000c0340300c05048000721412034010443c2d4044555080004200c05038145609003000c00c44802080c3c0c01201e44c20000594118029100904442d941c40100c0f1074001d0240030909c424569500c502040740300e40d58900400c03c440e590030804901654214030115168a42864004d55401071030064000500034410b000038000040103c1e0540f060010b00709019098002105580f50b465161405a010405101c081400002441208039002d2411000c0d4500c082043c0c2c402c0d40845e02601103203040304100000181c03030f072200c0d907210215444c92403c07802035602c0d800c2c0028581024180298400d00b4180d0450f8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 64155029 1250 64153779 64153799
    0x12030b010c0b150a0b0301181e0507022b02061302190e0402040f0c02100506030c0d1b0e16050706020d1406030c09100306050c0705030a0206090105060d020916030e07 73
    0x2c07003102c3c1512424011078562441d8034850000b44900442c416441d6004a200c481d40d811803555400f01f0442440c010014561090989c0c0c8202c5e030140050340080d841c80c00074043c44c503104034a41c100341c41c0702d40c81c0140500002d4468138003c281180f6560001500341c21500c520003080084072074403001c4a002c4c2d40340c2030304d0107000320260380580c440c504190f0f410541d0714203403240c00300180b4540c000700300052280720700d900907040050005a250080f001d88a0440d01d0740590240101d01c5000485c850741e80c4904468100392803a04813200c01680e090811003001000e480a4103c2d40c4035040080d160819850124080e21a040440c40c0b00c41c100b4171804241110a0040d81c0100c1c411010f035041244400d05001200d1000c40714200d52111020b410000b1550903840780350007101040003d803030000107840d11469903111011150040c0c2c014400c01814050030b1003450b40080b012030b494100d0207070710340010f0314140001d00120780805d40007280740a02030081d800010740113201c4095a00c150b5407002462 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 64156279 1250 64155029 64155061
    0x906092a0712090f09060f0512010f020309030a09090905061b0d0f0e1c05040b0a0201060b03040506100b0307020d031e090b01060e01050405130c0203070b0f07091212030b010c0b 78
    0x3e1503450b5800400705d03600d0f8050180c0400ea40700c490036110414504000c01041011041c0b40e50f445560320007011600c0c0e21307680001c3d44034500c0c1600956895601400041c16140c4a80c0040d80c044c1c40d140343d00c07000410200b40c0d0380d00702406c4106400b001d514211000414483c00d2030701520a403400c40003800864007500104a05501c07403041d40c0c1e941d2090f0304502400c2910785016400500300700000d0244807003900180c0180c1101d0700c000201c60361641d00d41c0e0090361060300e00b5611a48031000f0403102640410f00340016203045040c3c0790a47c10054806503642c0c9180100d1014152031741d441c0440c282280c2103440002448803010310800c043c0341040b43c01654203000d0840080c4060b5403010b0b1550042c001c0b2000c50303001030061003200d143d40c401d8600802070740310450110f0104215600108040d09032060045481c1d10a050032400d0a200c00383c5001001c0d440610500c03035106010300410701d000d4240b40c011049042c0840c2d0800000d004958103520803e005052001c24003d00401e84251400c1d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 64157529 1250 64156279 64156289
    0x190203040816050606041b09170c06040311090c0403030e040203040f0f060e01050a0605010c02060f070206070c06230304020f1201020703020c030d030e060a0b041b030b0906092a071209 81
    0x1c200b4038080f001c054060501c41c80c1f07400003117520349804000c8a4049841e8241c0b03e0030b29800d403410580305800150349a0300541c41641c2c0c412291242c060700d441e000341030b240c001d1030301c860482c901440d5507405005c002d0152882403041703502000080070300042c3d14480a020350300241801351203881d460a50000d101454501d542513180c400060f240740010701c104070945074140c641000404072503080000652200d5440e0981d01024030140006032104400303044554440c45202926074104400202501c08a840605c054058050901c2c920041c206c11603400540640c1d2645035842d101000c00c00c1580040307003020345588009003000c18181d003c1070500080720300301d090310949a5110002c4041d00c1c00001024426001100414601c0c901c0d41d000444407040074001103402e02c00e0140b03003d02042103c0000020030f8a41900800d03910b004a07030254420002c540202c40c42c2086140340003024194103000710a030361420100080004002c0503911403030341c019141180001ca0000c0100a42079510034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 64158779 1250 64157529 64157531
    0xd050f0601030c091206020f03180d0306050a0909030c1b09061d010b0318071805061504061b020301061403070e0c09060708090a06030204050111030319020304081605060604 76
    0x204103158864060032030700301c0b015074400e8601800c02244900030902c075501240c0485e800c1010344090045e02016510888003c0c2c542c0c90510302d021070584c24401c511181004040c0342601c10300640d0b5480d02824240c6020f4500090380314a00d150907207800450500203000d034560410701054565081c07807241c055070041c00c1c080c0301a80c4e944018000ca541e40344d100040201010300140903000191010b941e105134a42c00300070504076124441800e00140760801070460102010220389070303a0302e00070703a0f4010000b601d03030a600904940b00b4020a0049024190411083e03031411000580b20210030302050350001c008002d41a078a038108940300303407524040c45c02030080a100240b80c0c0050425244101e51503081c0d50b03d0146c4550410a03ea4040b910898205006000144040e20381c4080761005c0c0c103290300d00681c3d4906202c005000591b441182455075401041000345424000e0600d080320021840056140e0322a0b141c02c021134040c000c2c100d010b40802044030f000b4000c000a40354048c02081d14 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 64160029 1250 64158779 64158781
    0x120405030d030e060f041a01030302160b0c0d11010b04050f0901060602030a0215060a03140105011a1309020304260307030c05070b0f0c0c010e01091a01050901030f050c060d050f 78
    0x50035403e41d402d82040341140c0e00030a001583c2c1c2036243c00e14561040c450030030862401a944000041c00d102a0425401640203000a25004d5071500881010345225465107040c642c90100d40340d5200d2804003100c0c20460440c0c50710402d42d601350040114000010001d1004c1d2a180d1300b080d04441040f18002e10941c24031030300043e81800401120b40b111501e83c080d03c90314110404c65080e9080103401690050012000000458002c03607a40469908510000ca01035260107290b4500300401c09070460005001c0010b070784c5102503943d01070102da58020740507859543d203060581040c9410f0303441d00504001060b503541456022340043d031180c9020b842c00c1001200001044a8600820000800340c490020204401c00c100c0481c2136403002460000620344409090818251202c81c208851b03907a4481000300c04000002e805000c1e8240c041d040350150750700d01400908041d1040c03001030102c5407034070b106030180031040c0814440028083c088d26a03818402220368000e101c1113600c04030001c030880c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 64161279 1250 64160029 64160053
    0xf03050f07120c090c0c060e0105071806050a081803160308070507080702091f080c0f12030306120c0a0b0301060816090501140705070b090a0f0e07050705010e12040503 74
    0x380341084542c0d00003c000001c00e00700100b09000f0140e203003640061002d078141103000101d450084c0c03540208964008196410310000242400d004000101c0ea0202210b409010081d0b02c4000c4e40c0180c1694030300140592550f140b4216030640780070f0240094080094004a003000000ea6206418800d5070f0710700700c50b078421404683d180a10000100007110800070030026140c41a620f5030003130108007089040c021001c1104001a0155211201580200c5c000e11181d15011244a84076281580c2038181c0e415039111282e2288001040c0e41d00c02c00b5140a1003000c1c05003009500886032016150f02c000544411804201d50400d10549000802c00c03000034100c01d05010304002801c9054072034030340080c00c1000555200c07900700394242070a401807010801150040101000410180c54604c0e82c450046060003c42000e54011580076518210108040c040303011105500594916010f81c48014a00e405405002c6101c0d4080c4c1e2881000d20322400c0207d4000208100d407422412950350740c01c04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 64162529 1250 64161279 64161299
    0x70311010b0102190203010b040e010507110307050a1212021c0b0103021611060d020417010509070608070f09080624011b02060f0c030d050619030203100f02040f03050f07 75
    0x500d040350b0068000600584446551041d0109102d02c000d00100c6c94024a07030109040f280640c5603604145e455005220510707400c060040f10100c104c0001d140380241640b1026603694030724200400280000325107805240c481c0380000c06100405406668840c0501700003d0140542d901c520074142c6000c0f050300c1d0703039030180c422070318541c1c00503a40a1000401ea154818100c03001c0c2c41c481d8100104202e14a40c00c64584024002352000340400448500f40040c004d084840c003e02c00a415445800c1c20b0081c80d400c00e010580c0502246041103c05031024070844012040381d100e0840d510885d418818030f4a00701c0000319000c1662070044c49030403440c8004441d10603034400c055101c0d8030051042130250420b1401000000c411030222845c180420362010700c0d550001200000066450301401036078a400c030384601c036041c540c1451100483c2950002034580741241001201d203945c0b401c089000c105650141e4004080e20041207098954900303016440b40c00864003600e10317002c2c0d910040781011728 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 64163779 1250 64162529 64162541
    0x100302010921110102071e03120305010b0715020d020304060506010f0203041a07050708070b0304031106011a030406090c0b0901090902030c0a20160305010c0908060a091403040b07031101 82
    0x810110890800150f02d5056100c0c0350342c1c50450460158500114651456010034105110885040c0c52100c0c6036003416020960b550104004060800004100c80c000030026a2520ba0b00b00f560b4100003141c46003040c000344951181c0d103440314004000c22045c4a444d40c803ca2003803a080e00c0300702d400f6906a004a80300d126038000c01d45448403104c0390591840f8808080e011503032007901200d090359107484507580340c1021907000c04080c3e00300004000406500c00c4041042006642c01002c0d10350500c1c005200301d031000c030a00301410030040005800d000c001d8200301750481d08079281d104800d85503a0030002030351040c6021030204030071141c0040c0700801c034030840b071150500001140c10074003002e0701224405402814030013501c08481000021813018071500070078101c2113034032460003442d5140ca40e0075198548500d10611402d103030100011000820401d511044c0c40030006401500c0d49072000c01c11400f00b01c0d248161102007008a01c40714024024407081c2d010b074807038a54070580740c00c00609881d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 64165029 1250 64163779 64163819
    0x2010b03010b060a03110c032805070c03020904020d020901230a0f1710060905010312080403140c0a0515070305101406031504020c0721020906060c0304030b1003020109 74
    0x1c020414544405d2203540300d01007403130145100c00d24041410115a01e5074102c035a030101002c016002c201d42c1010110f5020b03545d40901c1c200a8100425a212810400c0aa2001074011f1f00c80344001411903640a008a6000c0d50041c55a441ea5131a0310038600d4000301c800c062000c0a80001c1c1c01c81480c645480c40000700e030300100a440000e41041d0041548907008003170741c030b110310400f9160080c440d401d002c1c03c6c01070659010000740561440c20b100c0d80d01d040d41d00d048420301c1400014000480d902c50f0388400f95104070719a56540320050701d4900c1c5171201228028120f0301401e640000170109602815001d1060340e40c0a1000c0d485c1d11407090a640c04030b20810100c8039017001600748500741f00c006035910038912101078840c0d001d03200100c1d0680e80304505905103504440400e0169003081d012482094040441d4802c138013082c0c4c0d02045802d50060400e1303210300004280c9403800c1c2c1081046a020b158420020b41a5007404000d1094a01107400b04a0100b5004080030a4418400c01d81d014110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 64166279 1250 64165029 64165039
    0x501050d050a02040209010c210e151e0c010608070e22110102070e070e01090b0c0703021c02030703033c0e0109030c150e040c0f08070504090f090302010b03010b 71
    0xa20b036820000254001000e403414001e000400c0d0010450311801000304a00c01003035520040c540c40e0b001003560b414210ba00d0f101d07904c0154548111014441520003145902d070750440031540d400036205060050118406266007000301c00715107a100400d0b110202e924451400b42c040d00c40b046035070016000002c030b09000c1c0004001503030200d03402d203045142455060041c0c03246140ca482e480d21000d002100c00f5004103110010002c070550780f2801e03040c020400710307500c241003603003100440c0c0e110445448040d115610210798583c0340311991003040101030b40102280c00e85a81c07481c02900881201c004980e410461308040c0c40003980115850342d1000300d528410031111080d40003510948184000c6a0420900c03207008400224120071760302c0540410420070544940440c1e00a0a00c0c0810030a980110304100e00e0b0680150032203200719804905051114845c1c1d0b644070100d496001d030742d001a68031820700100003104052580000da410f8043d40c000c2c00580c154006040c2a40c1014007119084 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 64167529 1250 64166279 64166293
    0xf0f090b1c120306030506040f0201080702010b0120030d02040e01210503030103150b0a09020c010629070311010f0b01122a17040b01080708060103032307050f100501050d05 76
    0x4210450b00c000401040c00d000841c1c5440b03481d41407400c1401c441c1103442c0085c50601c4001d640e0480c7c0e00c1c40d405803591000380200541000028001c60404e460102500c0c0f0041242404500c148240c0360302c0f02e0740e40401c548071035071200a00d00121081c4a810002d40802d1035855080f0028070880d01c520360000c00862440e4a5070380c3d102c4040032010312580c00d941d55900e041e2a0396607045c3e02c16004010007400581c46000d0214810b0840703482c0d500501c400c2c2d201d00d00550340c0515480402122928113101140c5a509900b002d417014841c1040600c2c10f5445c3c140300a00c440902c0d8003010341c0031005e0340d40604004005090008690a03081210032040c1d5181c190b00d004c0c0c4c800d4092001c41142032138a182c0c007000000341d115928101341c82c1284c202c01600018458510b080040703000602c07440006044551440e2170203040000d140001d22846210b000080b148100140c0c2101c0c0019408000c4644200c8039000241c1c9410b80100325212050424000003804d28003902000f4085401c00d02401107 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 64168779 1250 64167529 64167533
    0x10060503040b01180e01020a1d0f0109050d020103021201080304030b0f15040906020f040b03010e0a050c07060c0311040803031f1d060f09040804241b0c0f0f090b1c 72
    0x7102d13030205500c00ca043d1701d50b00b592102c0242800602a04100c3e511030942c4040d0307590359000c882d005001054040c8840d0b01c0000e00580c3c2c882d21580c1101c1c001e0780c3c04c8001c0304513400120301900c03403141a005140340d42030000801c140004000c0c8204c17030081064030328603160300c0d81c601c2500b1801e5940000c15240c04910b058149020790202048500c00c0307200500e030018503d44692240c200750310594144001000402c4040031407881540e2022042e50204024501840645024043c0c0b4501500c1c0035511140003154034040d9000720100d071041c41045440342c0c0da505410340d5030703401119620302101c4050172195522040b003a0600503200c13000352400501d00e00c21096100c03240f006000d16400319000001c40419141c001259000d11b002e0742c0b0485e40c4a0a26100300c0000030124060f2000c540c4d841c0d03d0302c030040da001c01444185500ca903900801c84c40a0704040c001c0c10038540000b8161b0586100005540d1801d0084070111296001c0038401d400f20039042200c8505136000743c05480f070f001d51110b00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 64170029 1250 64168779 64168799
    0x9060216061b2f011508010e01020307020a0f1406010909140f2e060803040305060c0306061602040914010c09050d0503120601090f080d1416060e03120f10060503040b01 74
    0x105007142c5948034007540c83d100040d41e0940b5040404824541003404040c007081c10280071b0410a4200d90300250b2031801c0025000b0b40d1485c103541c010b8100c8003001004e40070042c10304d108a2412001c0c008494503540c4400c10800102080501150a2525080c0030580148081018a4010310130800341c0001c00c0016449038903060001c13034220140c664000d460200740010711454003d013101d08002d40d102e078190310f82946440c0001e8511084040184100708150350f4000880300340c580d1941d800d62800e0f141d48041400f405d002e0f40010212400c0320381c254000001544010400355a40d5914034042c1d035100203101282d41050b101504c103030000c125680c100707450425004c2d00310300185442c0c07400030340d1030b0f54210500b4110780080fa542c0e00884000c589882d40103404214140c19124800e203030a0314142549100048858020030103615264100b04203401842601d00a80d419085855903242018500000110880309040710000f2640003150440c82481501c0c496540a20004066401c0030f0004d6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 64171279 1250 64170029 64170077
    0x11101090c03110f1216081207060b13050f0907051e06090d080c0307060c0503061003050702100603110406090207020105160c030818033d09060216061b 67
    0x10b13400068030791154080b0f803a220301e0411484240e401520401b0032040100340411140e501441ca5940212818100790780342400311000c2650040001580d142003102040091041400800c081c6140400700100e1015040c40c5600c1552444165a0155224420041d0a04071401c20307443d4072303180006d50302c450708040d0011b261942005021004c0e910155490310701c0395105000e1100300340c2000c81c140041210324000c1e46455422820301c2c50541ca01400460442c510b141140e40405840b9800b1424035130080c010403102504845090100a850381000e44043c03140500c464091440c10ba00041e0f44405882a10b81c001c0e03050750749600d0440c3c006044040403401000c140e0300c41c800c4060002c00102904001c0008007480090149038040c40000c050a01400000400c100341d6403904055900500040748100d182c00c680302c2d02149400202d00701e00420b503544004200310310010300c1c036182c100052211818039101d05024000c10080f140401ca505c0403200140c00498282c01c02020340ae50030110079 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 64172529 1250 64171279 64171313
    0x2070b0a09140d080304051e120904050a061503090203060906060f0d06020c1c11210a1b0501050603070b040e041205070c0603061a0705030d0203071701090506011101090c03 76
    0x510302d2802181c40b041c1c4130340c0c0241e400b1030f101d51100383e0884031001d1302c005020340340f03c0032006020308500d00b1030100700e1403041e500d80c070b8891035840d0002404612a80e000705c2c06401800507005100d0b0000303d0240042004140a074485e2043c84002103140000250710742c030074640546441c3c58084140103002c190aa40141114003070380030b01045010360810002e810f407000ca60001c90604400d10300015000c0340c0c0208011140b50030019490755910708030b00950f607420300202c00c02035485045032012101400c485180071055442c400140040c090150801802214101c05039001241d42d91141e1055110b903215400c40456050f00040c041303103d90039002e0803003200703060052403c0419582c01c880412a03410074070100740c5e00c0109010362203100b01d42c1180480b00b190b00c2490b001650b1140343c0e590281e9541c54014540000000c4d48082c0316940703544075403502c2c02a0f08190f5841e440100041c000480d0042e00145034030b24100441101401082030840e005104205000e0943c2c613091140700700c240e52 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 64173779 1250 64172529 64172539
    0x140409080f070f020f0f181b0c070f060504060c1502070219030b010902090609040c090e01061d010309150906110705010203180c03060712060e09030a02070b0a0914 72
    0x41d9110350650024106148607070244800c885280c030412940f5175012180e0b0380a02c041c81ea080086803203820298819081d4104007948550701c00b51a03803c0e000851409448086000c908035080d0720700000e040094404103520001c0c6117841d240119a14041e41c0309010000c0c4604040d0408214454815042d000882c0005450404a038010680130403a81002c002501c112400c20001d10980c410020301502e13444100398500b01c1d401e00011002d004800700d442c4501c0d50303030721118141d602030088a0020708204440225640c2e42d00c00c081d004a01c1c0c6442c8408200c041c2200880641c482c0c0304030760f03050b544a07000e01c52850414107038400520076240100d90711643e1b2088030070034030407043c0601100fa100701d0002d0391701d03e08031040301209450f50400c14207582c4500016281c0d0758001c200c49601c000c0364540100c0000ea13140070200500f6240d480030401045070300500049203008001042c40700590307001c0301c0e000f0303645020301419407203428101f80020300040018040240000983c071002d0100803d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 64175029 1250 64173779 64173787
    0x1b0906031e050405031903060b09120703020904050304060207051f030c02010e01021305130e0a14010b0612010503060f040b1501050c01051e0a0b0303030c1605010617010e0102030114040908 83
    0x5520202e030029103054499600110701c82081895141240c80c10960030b180900441c1c1c44e24181c000c441c0580c0b140d29200d50448000148411020481c00c40155001442015503040604010ba1241e006001f40c0c801406001d00128190a140403a40d000c1d0740552000b011040c00d160088004150b030300744140865403076400c18502c0390400d002420030103150443c82d562003031130482006007081e4000803151406007020617060700f8020100784841c0082c1c115103483d1014040340c0782917004042d00e042d0103900440c0441c00d440702455103951f41d8140e0360300b9401ca90240c0c883e00c010700c40e00710046030300810000d000400141c0c0042c0c1c2c5500703031201d00d074103062003424484480152825503200329007402d1484100c0508401e5031a50885c0981c02c86060310040000700d50040229451707210081c54030070000c0340061084081c0c0000c1d000c00051a8000c0000c01c65545c45160107401000b03a20f00d0a80c5560920f03000b08804601032085904a0b00441c03440b036a25646001803201602c40400c0035a0a00d000f40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 64176279 1250 64175029 64175081
    0x9060d020a031e0c03150f0b070206040f120b01050108091b0d15020d0b0a080c010e06040503100f050601110c1201020f120601021501031a09120a080a1b090603 70
    0x1e4080207060f621140701040303082d99070340c00500f01c65900f809400c9890700064104078241100007020203651f503542503d9502c00881c008600e1900c0307580e010084244035802d0015544140d5802010401d1180030007403070036643c0398011150454140d600310590782103419582d070310440440801400303450142040002d003500e9100c20041001144a8039015178000402a00c0110a0b00c94100e0004049a00707100b21818600c800e40d440000c40c841c01c2c180030b00403118009907991442614002c2c980241250010131140da0100041c103030441c0024400350501012a08070760081d012480040031400007403412801d010100841040c07000801581c6540c06c11614202118441c0205030510140102040500b0a43c000a14041c20395a18008008002006200298103500c10300120107101518800716150721102504100003111000c4803000d0014000710f4041e004082c2e5445014400002c0003811026101024010070f1121084009442c822060001c00d0081d40001303014000290410b600384184 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 64177529 1250 64176279 64176311
    0x1e02150a03020c010e031204060b0a050402070f02040b01090513091b030506150a060e0d0c051e09010b0f07080d151205010507181215020703210209060d020a03 70
    0x802a41000207070001040c3d650711009010f01e05203841c0302001180341c10b2000700b1400309800d01520040c5041d850300425042c580d904078401029100080003190b80b0119841e01c0300490207000d8040380250300301842c40c4041d43c05041080206e0303001074011000100c8049030a4010201d0310800c4500090b410394010690745003521640103144114001d0859003041d030003108241e0307207000c5818440c0e00302c007100b404041d070300510740b440c048030560b48060008002e00d010000030445810098201224400d5101c0003408243c0c42ca8400744207541c84080b99880c1c0302c3e11902c0c0d1051940308403021008014078000075522000620744c1c0580210005017003140e00c02d0100080c5025407000144101d0506054103000003841420b0300324941d41070840344c00b0002d10f2071040c80206882583d072120b5808089105004c000c41e14882001200030045603241038500d80500499045125105407a80340708200c03188a40320310845d410b400c40200002d04044a60304003401a40c0800c0f0325034105503e038030040100c0110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 64178779 1250 64177529 64177537
    0x90c2209020f0309071e090b011101050c030115031a0d020a0f0801021b010209090c03060301021c020414030a080313080903060a0b041b140f040b030103080c15041e0215 74
    0x20700c0c01d150390b07607081901c049407034240c05ea0480d40f198940c29a10070100c00020500d60100e44494001241c00c8050b600140c84c1007044003014000d40d4200b030200100d520365500214182c0d820101c0d5030541035455401142141c0740e401c40720240c001e82120700a42480c000d00e020020500c000e0107807004545404404010322516800101c0581d0042640841450780380032250001030f0080c002c504065913480020317007140024001c0c006544000001c58099102901101c00841c081d902c440101800303444080c00940c460b22444201e0000c40c200b8243c58030b80410701010342074005151a055886000c0c5040c20700001d124225481d80007000503003001c0e1824054a4403500c1c4400c4006090300002040c0000c0e01c0c2c01b200018590581c200c01c0c1020719030064901c034003140c44c1d9842d0645910503140002224841d82d040900e04510202c00001000803803002001c0307201400301a1803510981c00100007400e58141d40060103a40c4001c800140e000582c0d1500e01e95500041c281076440078811410710f12584 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 64180029 1250 64178779 64178797
    0x1809150c02010c08150103050403050f1303020909010203010803030708090a14061b0913180c1203120605010e060c070504060f0305150601021203090c06040e090c090c220902 76
    0x52255004400c0580a02c2282c540d0324080c180800c41e0f1505040e64084240355040b1207051550f904041001e05104100381c400c0d201807408120b45c1c030003003103e01c40f14450b584d20040f40302c0c00300040040d01104040c0241c9040300c54000041d421515082030603100500020300421961050b000c002c000300d44840e01c420300300c0d5295070241c502410880410607038284038a01c40c0315103101c20800c070202c0c3e0303e83c600c8054260801c1c1e2000105480d0160101d400441840005842066069000714007841080c40c5120160f02c80e80380d1004003100700410000740c81c85442000e001c686105a00da02c14240702001300003c0c00103200fa0f402070740d01c070740008040303031903980201d01c108004040500402000300314106140e0b21942c4594810328008000030341d642c4e480302c0d00c03500c505c03000b0010501c0700d881080f00c030000e08001011162039a4583d85034644084080300c2031110b510544071a114103050205810340214041d41500f403800c0d088051144d80710140c085490340100604200048000161015140e491 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 64181279 1250 64180029 64180031
    0x1e06040f05040c0207050105041202040f06030b06010807020105010e0610030212070306080d0c020303042603070305070c0e07080703050702030909150405311103030c060106080903040f180915 84
    0x140c00d1a080c8401c850350208040150341c4845c406025513a00300f025582103442e050307042c8000700c43c00c1c4080b8010340004440181c5450420001004000000305c3c0a031150724280d803400d400d9580c444040382600c5080c41040080b22250000c100141012180301c4420f0700282005171070f00c000a04d0003100c240048401100082c3d0703036041844201414400448007840c03030710f081b03c80b814040d00026207a07c41c51140d1210040e050004545c0c5a43c42820b85150318495070640361580d686080207016680111002c036100d05203440d01059900c000c4035007501401c0e803030b0740714281c41e5a500020b9006080140900c0c05520060004100c199501c00405105820700c00804210005040512080e590040d1510364100d00002851034412241640545030749100e26240400d0107140c206900b02c4485c03615200d07014003000821000390000002c0043c101c92090743c41c1e01d0390781e640c1c2c403900c6d03100e00a6014a880b0105000390401425580c080e4039003034003102c80d82c005030807821596500741d02040116440300301 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 64182529 1250 64181279 64181309
    0x6021908070e040204031a07110a030509012606010309021207060509030f150c09060403060c1706060405060a030e01180b040510050402060a030c1205010b070203011a0d021e0604 78
    0x1c41e51180c5240303503981c01a1819800c040c11581d0b0111600c13090341c49400103240c1c00d00051f40b80c0c0d01c02e8083d0f0791904042004c0d980c415441d814014484d81c00b00c0f5080340401c401c1d0000c469480740354030f007071700441c440e070301030131016484172001100507048813101a171307001c071312402c031010551000d01040000b040c01c2d403505a0b81e410802c0078107040045007002c0700702a0b0408000b8000c0012040001c42d0b004080684540e556801c2000246060186820240c8024500044115000e81004140c808948800610300c02e139030301c02003040001e102c0e6005080d0882c4090018081250082c4c01000900c03005400204004078040c8901225000c1c0f40381c191208134041c02480700780304091004a100086507041030010f4074107900804c4581c89400980380406949050040c2c0c4548621411080c09c20b4201062045595860310b0000903004003105900c42d501e030081c001a40441000c07400c821500107442003083c8030080d002c112441800103240051617a010364883d41c60340d1448020406014618aa140c0c030f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 64183779 1250 64182529 64182541
    0x3090204020c0a060f02040602060103030c080f0d050618091b030304050603070f12050f01030b090115030302011a010c020f0f060d05070309060e032a07090f0902040506010513050d06021908 83
    0x240c40350017155003000ea204000602c9880d6000c540641925010308004540311107900c0c0800f541d110b080160000101d0108402c41c015440350040c60080340101e0708400022510100c44c200c00e80d080e1980c03d5903a0109101e65400100c120700514046001000d482c206036940c0017042c11030b40101d906900182c01032411803901900040c030b40300114500d4204101f01e181c0054070b00f20280c0180005403050510000181c25054250040038100314107400b404a42562454087c1c00f9000c0c41c2078002c10f5402082040006500c00c03a5029080c42e001050101940310802c1448480c1e0042003580707410040070420001041014040d041c0100380c0d640e0009043c0c603071410300000f12540d02e1600e9425404c1003010f4200702500101c0c900512407900103500c0180c0b48090030781e02d02074031070344006061820702d50403101099a50784080c0389240203a4052003503a481c00011540391003801901329100f5251b980c01e0015040120a01099a08c1400c4c01840c14101c4410304a807030140b0702e01600054921001c004d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 64185029 1250 64183779 64183781
    0x6080a06060b03070801060c0204061d0601021c20011424010512040605151302130b0a0f0302070512040b0d060503060c070204110403020a15030b01090308030408070303090204020c0a06 81
    0x10051101180b014154180600d0052021406118210401891034802019540d681e404040240b0114060340210450440d00c4074040390215080c60140c0200b0240e002d0210503440b1003802140980d40b840701050000140d501114001c106480780d940d40ca01e1041649a41000024000c14113081c0c201000d0700c0000e0348810141f070084141d8100030090096446071000700b180b4680003a40500003080b140d452080e02c0145d2420101c2c0b05901c410955041505100039600805039100790810040080b9107840184203a4400e40e04200c001418441c0c0c0780c210503109030b0140107418411001c1d07900070544404190030070340081e0062448280000b0f540284001c0620800004044c1603014006070300c0c20154800c1c032405480d2001e40101d071584044010710b00c40d0740440e8041c0d0f50003048030301175a4644091b416114507020b0712801003454801002d103190f00541d0744a085940c0540518a155219030b60ba2099411500e012828191503201820040c0d0f10760018280d42d4013200e004150000c840d040c150 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 64186279 1250 64185029 64185041
    0x30f060e0f0717030405010c0204240b0a020f070303171008100b0f0d2102031903020909070e060406030b040207020a18060b0c0a02040507050c0303010e06090603150105090709080106080a06 83
    0xf05240d8401c1208201c00d03600941e07203076906a0100c0300001c48030011040c85000e810010310000100102c0c1d4000306004010798064240d000d200e90803100c2507110910406e99400041c080500840c0140c0c41003075560310380c2c0034825840501203c80d04180c43d03a0340310030703032401da030600c030420996071241d12143c441d05100e00042542182120020f071440d882e42c907104d44c20310101d0708d00c03045032000c000b40703180c0207008104881041c0d001c0b05524081c109004c1c0011300035009410443e209900d00404603030000c1c46014001c241140013042c03203141525103901030b4024000b4020072504590240610005617880200750340080c4101d581100c100c025101e1488100e9a440e001080a1001030000c48507261b0000f41c4d2031155a8180c8000985889440007a5858060751101054a03c000070010600f400740458440c00f50301c00740d80a180b551541d908050301d540c6035101400c0142250300040025150900b0015005022410803030045911003584500f5188203403c102141c3d80408070080402000d84961 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 64187529 1250 64186279 64186319
    0x3160b040231020a0201061d01031b061b02120607020109030f02030708040509091504050106090b040c020607030c09150801080c0103090203060103111305040308070e0405060a030f060e0f07 83
    0x246819048414520103440b4800d5800b20681c04581c0540d101e000358000e00c0a018050b0345540c18509492221112134404d00080b2000e07100249580d984420342c0c0487c1c010744515885032140c2108840c442c8010780441402680d00c0043c5c161074030840300003070280a005d8151a030011400058504028103000541c0c410f140c21503108000d1036010400900035982540c508480711031068981c0050b4601d407808441d840803003116000d00b84000c0001c15402031b01200c00d010000d00280d00090704000450b40702040b0980941c00860010754807a00c03a40c03203031012040b90b08044500d2074a801202c00c16480d0700c0440004107092030700510100408100c80d5282c10340901e418804000c2c40da01017521035106110061050450090b44001a070310341c403c10703e0070801d4000070002e501d050709004010b0241552194041041c40d007040b44103041c28010341d8801c0402810003030b2003920710703a6000140321010a060b80c5640d9500c2404d883e0080520241e10018031410040800390705020b200c402510012402e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 64188779 1250 64187529 64187569
    0x20f0c09060a1206021201060c0b06040c050403020d03140d02040e090304050312160519060b0f46030507150e090a0b0405040305030a0e1b1203160b0402 67
    0x108181da58865401e0b000381e401402181108251925000d80030b40691007601b04400c580000104800f50700159251295001c0d0611300c02030b8854200344422105440c03410000941c0821082c0b0242c00c051440f000118801e01c1c0400c582d070b0941401040303135001948110030781500014100020108079164a4100c00514051803034603142c80006982c60100c0440c0308015100030130641e080c00400101ca260b015041001d5445040400310301d921542124a1304071403203460413140c0003080c1880410748882c0c032005803d1410301c0383c07124058281500040c2c42100960000842030314100302c96611b0604041a080d001102e040c00d51500034148141034000310800c0e010381d06068002a44601da01e90098003c0d07400001f00e444440f00200900842c00317106030824149401e0008050340301005610403403041070100001c40c1c40a044030b80300c3c0ea03401403400d4000086051a501d0b807805500c0c40505c0c012000c103c9103800c40d01c801090a0111b402c0d81500c0030700510b000c2000b50704000260340401441129 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 64190029 1250 64188779 64188781
    0x915170307030804031b06140f040c090e0c04020c010606020106120803070e010c050a0c06020d020106060e091503101b050a08070c1b09020903010c050f030103141507020f0c09 77
    0x10409580340181400a003c104012000c10107050003000c05003ca0103141c900325110700050f007407080291034803a64582d04a00000d000400003070102444a02542e844008040fa076490700040f80c0180941d03662134000c90003200310b0380c1c1032035031503200070540f0303004410012031640d00e40700700a421a005503010203c00311035200c0d443c0000f0310080481e5130011403404d0a409200440b001242c17101c103170240040840c0b1900000c1024080c01d00b603000c00f256026800c0305d50010302100120b090b544640700300380204203400001800381c43c0442d503041d4405010b610402040a80b040002d1500d4484c80302c605205648508aa40c130454500b8250711241c00c505026187c10385019000b014003000a0011040251603c11442045480c001200d061030064a4007241790f40c845500070003c3d8000001caa201c0c0d883c3c4400c94001038000c0301550081d81c501c11070541541e20b140c40d0300d881c0700340a4582d2a81406443c8002e119044510000360185101c2d030f00400c1401801100300e40382c003220307609080c030896080c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 64191279 1250 64190029 64190069
    0x3020c03010c0503060612070903062c030910050c0a0215070515130605070e1207050310060b030612030706020a0c020f15030a1107020d21111002070203030c070915 72
    0x1190315050700795147c0710040d43c803407400301c540d04459000103000508000e41c2d0205030340b04010041d04800c1180c2c5088036012000070303031a500c0c46880d2010b0f81003075014030100340d03041c014405001071380700b003405036107041c1d00650001e403070380401710601d1003900800715548007442020000074201c00c00c0d680d000c545500300810250310b0b80e071404200070040350302c41d00020340180c400c07001d40c0d1490b10040d080c00110b5880142403504e890044c05034501030700c44c403a85c1721200c006c1d0b400380340101d84003513a0031450f54840b8024018603100b8007004070114481000810300141c094401880300382e0f029500c0e40d00d40c0341c06204008140329140760481c40b401c1d00804044a092038002126088112080b00055010105200e6162030040c844042c3d070000140001c03406202c004c6404035440407081301440c0b0f001000c01c4060b07850065240c4c80800550110146140702c42c2985d0040c03401600040803203051184d6036241500e000c0c500e810801005481d030b6a4a40700041c0c884222000e41900880d080c1241150 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 64192529 1250 64191279 64191289
    0x3071107140102151905010807170a08030a05090708030a05031b07051507030905060a020a02010e060906160c151b090b0f0906130803130e072001060801020703020c03010c050306 78
    0x4404542c1040203000c005c07518280032604800b1104200e804113200a40e90340082c41d850b465103105541010110800146003850f0106480b0b10843e8006400c6081d52a45800f950043c06c00505800ca0b03881001e1000c07a0f03440c42003010345202490707580c2d029500d1038a1a07034458016040c2d8181c0e0f0b5591381c10b00c03c410001d44c0114035442c3c1d11444980048050ba684d020480140014402c040c110740221010301c9070300c940341e40003440305100c0d58000f400881b041e031015a5446c10119401569900860045000c4d8100061401d1074a400c1c1c1c500300c031001042d40c44150701c810054122132081a0b9822149245e103074542e0f13061254264600740f0001035403070400c04d912944100407016a8145000454140d60340c0c0c0d4000b40c031654004031020303410140e20380c0740c19a529448401c0110001d02848000504040c1c0f0254643c80340c02c46596516801a90243c07808140c80641c210038155500c1b610701151201c000d20141046a02950041801c440d030f58082c182100c441640d0102000310800801841d0784803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 64193779 1250 64192529 64192543
    0x91116060b010203040b040b03010f05010e0a06080a02120703050f07050307020705040e10020705030304030311040315020d090210020312010801020a0c020d0305130b04080c030f0d03020c011103071107140102 91
    0x4580c02092064203100100e045226680280d8042c000118012800266450103503041c1d0b400ca009402d8225101e00043d139105103c0440d050f805410310380140603142c0f041d14199008181c0d160050f05017445098118014081101e0b002c0c000703075484e400c20240d402d01441094002985003001491810300d030b80c00a40b2241c503402058000c80e100c45030301d0b0b82c0d0301d000c0007a00718003e0400411515141e0340d20700300c1d4a0754070550301900042c0c200011000740310300740c20032507049079840150090894800b062200c065002009840f80c0303e90b0b10306110015071a0004809040e100940c06142c0d503008900808c8100001a00110340981c4140003011096402440c2d01101c160125000c186602e803d01d42190180f044c496103129552490030006410003601000d00300b515910403e9a0206018406059803186403040d44126076010720788810b0404d000b030f8010030740f4280c2c00d000441c015204130052000c80d407040c0c03009400100b0358100c0c800079403400e20800c0050491288111201112500000c1d91100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 64195029 1250 64193779 64193783
    0x2030303061207080a0b07021b01120b040e010e100c030b0a05150d0e100b0102060f060f06040302151201060207120204050703020d05040c0f080102090a0306020a090b07050601091116 80
    0x190042142150890403c070020080c4450400c0b00d0100c9000c0c64245954501a100d21004d845810300702c54114803031400d000d079449410796400c800d842c040e13900b080c09005d1590380190030907960826051a41e100380240e02c00c00304084020280b80135032003244400c40d0300c80b103130700b4040500e031000e10b180a94655200e40211042241c42c0001a0425030581040b48101c101c01c0b44241d00e000c111010100020030300c440c03050b80d42c603402c001c040c04820059884480840e00700340d10381c03c40740c0011041e20f8215a030241c844400352055082c10349aa0108802442c45502d01003c11030214180c080400424103e9000d010b5a1015040c25450940303411303072001491000920480c4c03141d00041050784240d055440d180300d0408180010b0903e414000fa00000b140070b40c0c0d000e0704040c031001c5010041402101c1714694041c1001b1042441c68590b0350094100710b80300400c20202c81e600043c08600c0501500c40580a100074190551404010600310b440c1078030102c001d03107810b000f54500d0504c1120900c007087c0d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 64196279 1250 64195029 64195039
    0x20702090612011803110c060403241b0201060f1a03160302090d0b06040f0507020c060706060e0403050409060909020f010f020a0507063902061606021b010c0c0203030306 75
    0x74a49803400b6000d040c061094010010102030218181a40480c1d410581c0f04903c05582603100d114080c410b0070701c1240030261221b02d03144024901e10310030ba054040e070788600800000e42e40d40d40d007640c6140144601c0202006039154541070003025480c81120000700800b444040c404021610348a0751404010304049406400c55010003c290180c0c0480d80300c820018801c0060040c60719040014031340540c0c2c0c0501843c5002d035444c5a902e1a84a4039006090303035002441122029402c01c020f0b580000c10498480d6200c00001070f40c020000040c0780a1842610340c07644440c20210444100c0302075500c041441d500709403002d005a00d911000142c0020b013840c10001070308000310140d151215400e001000c5100d2580c0000300d10b60700003810300d060002c03101e4007041d5038010461400716401091070031901740b501500500040c6061070040c0060079850b031440b24810102e46420040341c000c03102c00000386851034000c40241d0307003e00c12001c1050a6081269000766941c000c070781c0d6070000602540c01a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 64197529 1250 64196279 64196299
    0x9060501030e210a03060806040b01080607230906040812070203100b060d0f0b10020615010207140919090321020307080103020910030204020c030403030908120a0e13090501060501080601030207020906 88
    0x440c441c6d08a03001600b0544100c07905814545040d10380850f00744600369541c0144404141494461456804c01040c0384041c1594110358801221140d8840b945540d400903081200107512103080c05658098007000c03045985a0304540141810444100d0045040510707003200f201203680d0301c1c001c0c0d6245558542c40050084c203c803051800030207a111040d5031011030040303482d5080f0790006019108901140384ea0301498411801641c3e10505402002c031400c3e000e04d072003012800d02403501e42d809032654400c00c82080c0c5d050341400454916440c240c0c002003001c81d031924404914000e0214080580d40c0c00c518501e050980140020303410300000b44a005028081400000b1050140c0c01035600108110740e41c42c005c0301da45030ba0794018030003100803030003507040011060400b241003070064010000003460216400030860300e80c44421074080d84202860010036008603203215004502c0c1c070030030000800718200701c005403500d00004e0030703d81094010071818005071101b1305a15040341d003d4912500d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 64198779 1250 64197529 64197547
    0x140103060503191112070b0c07031202060702060c0f0304060b040204090f02090f01050a020d0509010315090507090801020306100c0c0b03090303041a060a03030c020f0a09060501030e21 81
    0x50103a9a101c01c0d4948101c100d0321903850034800c002d402c100d11401c0c0c0c00265000030307018002c800c411540c0484017900014400c0041c2017040c002001c10784010400d031103040391640c0c0c80031100100c45106d8070060b40200100080240c0400c07006810408910040b0705046c003c032207900b828840204001d000e503868203a0303443d41d911207030117039030241c410514180041c50000340520000d400850000380314000c21102403245501507401c9961b503c00325405421100402602a03d042d0301040240741003546d0f5000c092040f20350300080381e000c2d00c1d49080c0854513081c0410001c243e403074940c10520007648100248241540c4840c442e41804485041820b0340c520700d420044040003175544040e0850500104101c0941c0340400154419881420f034080c40011503c050303404034000b241e540e9003255000c0000e201007030007004032141442c0b0040c01030341c0c10b0a00c0808140c0307011840d440480c40b1a2604e801b44901c2d80c141c09502400360019004003030000d01159411062810b2100b1a55070410009400301 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 64200029 1250 64198779 64198781
    0x607030c0605131b05060a050f1c0c0e011d100314010306021201060305061503090f1e0c0108060a0603050603120f030f010b0c1b01030b0a120c050303040e01140103 72
    0x9031454000c0410003251614080c0b0700c103c0c000c802c200b142d10704011041100703109603c0701c0110071348001806007130904403410390035215688a002400902e41080c441e03480b46c440c1c2c0440c0a41494400c103000b05280580070405041942040746890510040100084100c0c1480398181c0c0c0050080314071402c00c0000321020b07401070280101ca00c1d00002c42800110901269400500580408a80c08001030383d07240021011160107458680c1c0c070038841703011000c80c840e414018640101280050320a10484041040e190001950040b10b0040070299041040602404074800002c3c0a0070103424a240c4000022005038450044209240c3e81e040802c88545041141342240e46410414580d10b01c03981a02800310b4208940901c02003152900201d01040128260b821644200d8024021601c0205035000302c43c81d18001103040503602d03191800c0658030410100010004000ca03400160940c1c01c19584c1d120440e04a03502070742c070401082141c035159000b0036044620822100460350f902e040120 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 64201279 1250 64200029 64200047
    0x80a02070b010f0f06020f0d0c080405090711070614070f030903080f12010501050c030a0819150306050f0f070e060706020a05030a061509050616050d0918140105060703 74
    0x50400e007100c5001080b03d0310203840200554208035407201d50181e179088100d0780c40d19507504001054114040403c11240182e942138412840b0f602280e04007502e61001c503126180c02c88106c2c001a204100c10528510b013401034001404880c6025946d4001c801c03030091291003101402000b5000556a01050520520011000d9640b20490959400340e801c1c2c401490740000840c44a071224100001030702d50b00490458a0b000c5402c2c0c080c6042c1400c00303038203840c5058024545808083e003c100440207511a03c40c0566100b211b10352149924114101324044400051414401e85024818820160a039240e04c03944a150707031a060381502a0480450154082c054006160034004260345c0d8030541c000c4007442c41101a000c08101040e078170643c6840c0c030041d01d81083c01241100c0818040c0d030a00000402001081c8111000d83e20b076aa42c480d45020706065410300040c90044c002c1c484042c00d0417031030156048084080c80003040320907040c444842c040c4140c505c80d4030300044a10405004103002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 64202529 1250 64201279 64201283
    0x30b15090a170a05060403020d03060504060e010b032503060f0803040f0509040c0902030f06041a01051b0a0203030408060601080f04021507050c1f0207050603040b070309031e090f0b0910080a0207 86
    0x30701c0c2c25040c10300d4060f59808041d4502e0000c00e017880e0001c3342d00e00f803900c1840700b00c50804100c044640d2801e424244e8652002c2e10140319600c1c440201c0c0c002c9001c59102c441a801d040e44c00091440ca44407203141014010740216084c0d400811041000300500c1581e0000da440848010140d03484504c0c022100b9065a030202e00b0300c0380003001b04010b01c440c459105114040a880600a01841d044069903000c100456540459000c0c4a04140c0812000f2855500464441180c4511282d40c0004e80355421683c40380340c0941c019000c01a10356840003080d9040902c0400e8500b407400c10350300181044d00301d0880b0381041c000c0071a900c018820204102440071001420720f0707403504c06c00f48048c0052094645890098801d002c400680e504080040348d20613600900600801d8035814021006026041c01c280c00300f01c0c244150740c40b1070758580c58285015a5640b074001c803092420018004000f4203600c480c0100100380814242606c40418130310711800503140440c60fa5a41e009100024040d0f0100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 64203779 1250 64202529 64202533
    0xc0112140a0216061107140609060c0310050319050114070f030b04020418050105090c090f1903050304060201061e140103050408130305060402180907030b06010c12030b15090a170a05 80
    0x15507204125100208121801030050300f4400400580017948c529040d100502290300c008001000e440540020f960001c01050440e07810076640c000103407401055080d2000900100c003200c0b01004401d00c40d441c104204a280c020943c5000d64025290010a1501100303068445c10321600702e41e16641240c0140519080040c6000544c40400005020034081c00c1d00030f0402e100843ea030035030880c0955a00d00001801c08411640183c00d20074007100c0d0300606941c1250a15020001400500c041c1024007190307800014410724200503240c00016040e04c0460705460b02005018429030464204032034902802c01044684035468007808034850300319109501c2a07181004410000041503103401280215860000b0b146c1c00c003581e1043c1030003601d0072040c0b540000d1040000030100410258000e405040010a4941a48601d118007614281400000340d0f02d860b00c420038a0802c01e2456143c00c5108000e0a24a42d0804542064040c1c01012103186403080031041e440410840c149105d5130000c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 64205029 1250 64203779 64203791
    0x11041802040e0a090303050601050301050f0409060b0306040f0b010f0b03010b09210d020c09150112020c0102040e0403080f0412030218060a0309020913020a060e010203070c080c0112140a021606 85
    0x70b01c0500410b548901100024200002304035550f1064081e070741a694014114101d5018800812000f000010f404442c000d850302da00180c6603401380b000510030b0340601c0310b54020455a2812455000c0140c1210820000c288020b001807050740c81a02e05582c811000c081d5503140800024000c00f0780c0b01c2c0400454900c5000310012000c012994000100003a0212404181008204126220200d400590219580c100c03112590b100340c1c0380030384083c03500c4070051421070410b1003142664400e82000b440b103181d00d003d02080580c481981c9a1146010000707c400e41080d03038070f5007a040071185008080640100d07d084010007604e03040704a1036801805070783d441c0c1a0940290103001814400e0384550729060029a07841840c108504090740e000744800f15250034010107a4189031408449170440c4004e100401c00210513800807009040fa080081800c1140e05000401d0349404075a4420014102524080c2d100b48080c010b942082040f5000b503110100d41854070344402c40340d07070003428140c1040c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 64206279 1250 64205029 64205041
    0xb030c09301209030a0206030618041a090303130605190207060b03070f03030801121415160c0b040803131704030606060306080c12030c030c0f0105070311041802040e 73
    0x406500d0440e2481c400b59a00307044081c050100b14000c81c90500c3d09034121038084001460188015a8030483c000d10320304145034a03c05c0c8202da041e040b40d0880352000c2503003940c40c1c0c18410a09207680689a0700c0210319526048a40c2e5131000030a4100400c002d480d2404281201895032440f81062a0701c44210b4a418190501d04060031041a03824002c0c064000003240c00080103140c030054982580310600701341d2a1010000300d00548138000e0f581e0080e140d00c840003a40c414000240e94811003541e01c4a64207080004440c0510001b500f0700601c03208188040000703130f40780340650f4041d4100500395100c0c1d548161000781b24051200041651032851032014104640300047c20680c0d000b030030100425611800103900321030751030140d01565030001d1000c02d854501100c060b24401c1045050300d003405040e081d040e10f507400c8240071201a410440408085640910a4a6010686140902c41070075000764495161245015451003640340241c80503123168941c040342c00900b0001000c0f00645072403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 64207529 1250 64206279 64206349
    0x11103070c14060a090e0c0d0c0309050105060a080c040504140712030e0102060408030a150b0408010207060e010204060e1c120c0201170603060105210102040e041502040b030c09 78
    0x780140d100755070b840d944030499403c0c07000036150002165150001c2ea80d0404101c0101040020705410f0305150070000b2982c401814000d1500b2603e40b40c4000c29240880d207017890940350018912400b410b11020b04201c09200040c000d44070140594002600d62503e040c030540d0f9502030040b100403403080c080b00140703401d0741a0021141e140603070303200149580302d20012a00c1d030300d00b9140070b0704841050000c070f10b8401c00f590110100130b079440d0707020075001c0d030310150341e10641c2090340a036040d44d40c04207480d004c2c80094041c203000c502d1090021486d241c02e124024001400b203030300450103a413540e2000707000e1021510030401e02580001119400101550300107207003500c2d6010403030004040c90b0740501040005e1103501d000f001d0080c068102603080105010314121702c0e40555000e45004500118510002c3c4014009001801464507080c075140c244240d031640c1c01001500d0140c8100020402d60000406490304084120031160741c8003180c0700002c0c140035980b032100300e4200f088045c43c2030321105 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 64208635 1106 64207529 64207553
    0x10302040b0607060908090102070902040b0322050f01060504110903120a031104090b03010e0604120e0612070e010f0f020c04090302070b0a05070c2c0601110307 71
    0x695203413101030314542c06051750a100b0005982d2070550341409010058800b1f440b00390b00d0b061520540c4203c6100c010325614683c2880080d96212016400c844100707660040308660301c8044d00200540240800c0c03081c82d210380d15213003056500c00d11440581e0079480e8018040c00c0e83e04202d410102d2103034030a07410b881c2055a2448903410307009010003d040500381c1060b0000d0642441403d040c00c5848640c600e000c15480981004005403451014a040c07000e030380b0b0b24100c2c180074a00460080c0c040c600c000001c0102230810440d06940c40070030351680c44403d0340c8040440c0386002003036031080302c07803800780740107030005001030b240d03410980c103d01c020f98800e104a0341e004d5503810520589401c9180d002000820000702c160901c0f180510010242c51445152040b03035054215883c00c2440020419203410300383e1700001c1c01a0700a000a41404010b042566640c0700203107481c0d10030602c = true := by decide +kernel

theorem cover : BRFrame.Cov 64028779 64208635 := by
  have h0 := BRFrame.cov_init 64028779
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64028779 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 64028779 ≤ n) (h2 : n < 64208635) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
