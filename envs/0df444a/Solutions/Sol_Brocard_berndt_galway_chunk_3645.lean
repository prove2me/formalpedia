-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3645
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:16:28.503655+00:00
-- url     : https://prove2.me/submissions/2bdf5362-a332-4acf-a8ca-04336903b693

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 655395683 ≤ n < 655575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 655396933 1250 655395683 655395691
    0x9020c0a03120911040b0d0c061d101e020708250e19050603031e090307080705060a180f0b042102010e0d030201110a020318030d05040513090213090614 67
    0x809203001320045080000a020f115030158002c0903130a03907240400c1d50007110700300034002516842c210503800200d407007510b03610300d110302d2151041e1244580074680c405011000c4400841c0101e000300c1e100d0100744e140c8105903100390800d110b56219401e1b407500081d2090340446505d40081c0003943c441034800b03d4008102c0d0988001e4115841c3e202d10b514450300025040080501506e29203080d40c14034205203440c603004d01c0000c142c0003460140c135081c104405002000c0d203001500c050f509100000b5840e1203035004c00810044c061560f071594020008001008082c84000760f03068507921106045550800d204240f03010030840080b1b81181000c4c0c80884170303640d050359032000303031030348101004082024040c098046650310102e00081c5045600100100a00780e001140c9424604100303002210001d00f40d01c1c0a60080c13140031072029044810358040e100e003102e4040c011301c03050750000000c10035403101039808909400d00d0800b07040c1b01e6010301e01c241d02920091003100300c0c066a846d201d40c2d0940f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 655398183 1250 655396933 655396943
    0x8070501021203101a0c0d0c033236010e040e0a02090906091b060a0f02031201033c0611040504050a0204090e06090d080a0609020c0a031209 62
    0x4a001e0000c1c10701e0080d07074070078440c0c44542501622012a82c0307010200c410031032180b0900060780a0100020441d4507031041d940d252081854288d550020300409a8180c3d040e900b0a2059516698442c2511001d01900b00005c60a454031054151b1020718410500c1041d54080d051a616101c02c0180100c0e00d030080701a101d022031000c0490030711005203d06c1e5040071990040c1941c01c001651030b44113071401000380100500740350411010041c02d00c00c0fa942000d8100607074074122203075620389005a03280500c0a08190040280c03045d0181d0035845195900c40f1100c668800120400c84031030341001c0d9034040e941c3d10315400000a030b682c414484103007207000c080701e14080300f040001d0040e810120050148203035050500d0340e5100850140d51040e0f0b94590075640103d07007804801441e2007420110710b0461f0062815041c02c0c1f21080c1c44102c3c034402042000109400a8003004585c1c100d440109807103d030440d03a68202c050b206407501c00f251001c40018410f0800c0070140381d01806410340c10360b000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 655399433 1250 655398183 655398193
    0x6040201140f0909060a080d03050403030e0102071502071a01030b0717010e151917010b030309130b0120030a090e06060a120902060f041404091218052106010807050102 74
    0x20f80c1003001d080d00c0180303070340c0d4400e0f05200302003080d001c1404a8081000d55441c08145400c103494090b094412417100c0c80c01c0d51f881405000d02042691103101b000c2049042e0040e9201003500381826100750090500c3c030f43c0f0b504070000008001c0c0441c5011700c1803415580d02d8048008081038403405800a00c681d4000858000101e60641c00c4120f9400784600e008080103921040201c8000318072446600410071500308440514540c04280980078200324100d02443c035185113400014504880c0210610005989500d1111540d00807111001c10017a040400b074026607010071901c1d96a844103411800250f200b40f0005454041058901d005002c0100742038100714550400b02c1781c2c0e0b08040500300255032550107060150301c03110010701d40b0200c0405455521070400c22190001c614200036036002e545010441d034041140e43c0d42441c500805464202041203500f0706030b081030340080d080103030310483d88500c13803106680189165249c4031501c07060b1042a03980340c108685690003803080c90302617006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 655400683 1250 655399433 655399447
    0x6070209010e07110f0d030e0604240207060609091101030c1407030e1903200a03120e030d0504170316080319090501020a091211100c020301020c06040201140f 70
    0x181c02c1440c0e01a040b450034449080d21945001e2804c050038100b006039130045c8010f408113981c14001c2e00000000034004003020308142d17481e688654041c8900404285220008200d10030041d01140e440ca50001402d00c0b80c1c0d9204d0300c0404c000e18000608a6100c41111500c119030f50183c0505000d410b603545522031200c0032420b51b100396a011007402c41c108040410040b24543d00d0502c0f038001c081d450402e0b941c00c9801d62a01c6104201400c100e541c5000c42c0c420000702c1c96541090743d405580d0300c4240c0f800c00c0300040e0800d42d0800107603c4c100c1d44c98016030180c114250340c004080c0044481480207041c02c00c56503e121500c2e40300340005046000e2000c07000d10b011403c007600458201c80008010f0055030071001c004000c9902c60070f82119165000200f4651075984054280c01030100c0c3c005412840b000c0307a480031102004440b8841c0215420403800e031219005418900c100c5070007400940d592510400c010b610740e601280d003240030600c01c4400000320b501600c00d850020b034202c40030615003c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 655401933 1250 655400683 655400699
    0x31020907091205061f15120605041d0d03020406120b180c0408070501082206230105030d050a0206070c020a05060d020d0b121002070c0306290607020901 67
    0x50051141003800201070000450010a44004000d180684090403c60030461045426000d610680d107104000f4100c0500c0040c03032004501800406a08203000781c24403d030b055001400c06035005560140ca0f0902c050210b00717480c41500405c030207035015248402890300095040780103a00501c000210040e804a9100a40da0320850b402000240304a03014810035101580f5034404407148100743c0c0340401d007003245190400c81000501000d00300744190703160130031911000701c260120400f1b0004c505007000d806d120b5542d0104079001140c0b220f0080645800c20000440d540078880c0714082d109042024038100c1c440c400f030325160b031000e0f409400542c44040c800c030b55107480b03000280d90042401000160701e0352944000c04180c4220680540c032610344d1b010140441c1d07841c3e059175004900306101040711120108114102010139100142c03512250f0130101c0c003290340d5400040115140c801081c151a498400b0030320700801e00c03115100010490310900c1083e001e104d40080d00000d2040040c4009a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 655403183 1250 655401933 655401949
    0x30708190b040f0b01080f06161710170102071506060503060d030e0d0c030615050907050f190302070b071106070e010c0507170f0703110d1b08063102 66
    0x1500a0200c50005071a070340f51013100100c00e030b1019000350f120b007609004c51001400440d50110f01d982e0b00c440d2964103c0c101a010403a001c007020641202d9a0004050000d0ac07103200000d02511300341000404082e480c098000d40c0200c40603960400201304043c0c00c001c1c0303806400162421640e0720350030750722070000744840d0740307002c9a0440600101022503103590f121140741c0366149006107510720442d07142d41070400889210743e00400c20511481c00c01c0c0102d4440d400d0841e0005a5440e00c0b44d41e5003480e5403030080c1c0c0d0040103100014200c1d0b0110a030155503040d0090300b1868000c4408005503150900300792100c0346105464001c503001200029849801f030741795140400018140351245c200390fa030301d15042c03100d20303008140020801181520203600401403032180c1807254005010310780c2103440c0c20058130022200144120700c9005101c00b00b2006010700c0c034a4244039a0100400d589880d0910380341c0800303d60503c1c500c0002200034445031031201d010507500d600d05440c0720340f2104540a1003541 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 655404433 1250 655403183 655403191
    0x1b060705030408120304110f01170907260c120712060f050a0e0c010e010206040b040206090a151b0201120b0616061e09020a0e0a151202030708190b 65
    0x80d00041c030001801100c207100d54800421301101403903492038580303080050144e00c00c1c000c9005140d040c0b900041c0380d80040c01c1d144d2105043e120f1908aa80329094585001080d0700560b9107c080558800c00440922180442c03112000c0300365210015160180300450300b103032034041095803022400f0400200c91001001c102ca00502010581a0310306e4814030541e042611100992541c1d01641e8100c0401482208107414091800a44a42013000002d5407410042c20290107901c03402c0200e002c65580c072089410414024048200295440b41414560100a0110408507070401c09690b80d0403c40c10700c09400603416142c1031001070a9245140050452282c0107070092002c01850320407540050080c0c1e92680b2820011035204842540540e4086002400100c8107003031100c0480142e40d09110101070300c425420154642d035401c000c00006d000300c0c240d036482d614403180000c0764440d036000145a905000740d08803055190b0743c0c42e0141c2d482c41c00d00310f0010288450100705001034007241849801c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 655405683 1250 655404433 655404443
    0x303050d0f020408100c08060a0504020f041a0c01050c04030b0c03060310020d1e06052d1c12080114011b080a020a1b0305060a11070f080306121b0607 66
    0x800d01081c100c0040743d016400c014126800003840d07800c0780c18940540504c4038410b1501303070010300742480030403a0740310640035a034422500071503c00e81000c0b200040d60001c2c00c1e5000360010504070510000c21741da0101c203140c0407950030180003e1004072031038100d03000c80c0d5200400461a81e01ca145044454001800341d80d03240c0101c2e200250b00024900103485802400880002c41d1103810440304444441c1c0e034410300ac140d081c29410405540c48609825952100a000111b40004004000c00e0030f17084e401000d511640b544c203803212946030360510a1015104078903443e200a040c42041d141c0220910031121203403d655400314085d440394000d01c568444035560402d95850680e03900c0d070301f034000140f04001a0b0100c030781101400160588000d00081d1500e403130181d1403d42d2111070319800d000704040107070ba031503842a04244c001d1200b11042e444e000054a103030340b03a0525101c40b19a10070b48940d80300d4103000704455180b2001040300341404ca1420483c0c4c01101d159000c2c000107802514080e26 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 655406933 1250 655405683 655405691
    0x4050f07081209031f02130503060402030d140f03090303010501030e0102121f031a161d0609010e0414040201080709271d0d1b03020c09250305060a08160303050d 71
    0x44803003c549171604800c2000d0409a252861041038924062140c0c0c0700038400c2d8051002e01c80961008038080a004032a071a04c3d500031001d003647d01c1c2d802c1c4101030b5103580007200003040044078a0040003841c142d4100340d030184400e803140d0742043e080c2e0007491502c258002941002c01d60cd120b22001b007078007140c40c0d0305401007410303034940300d806103c3c400f114400200c0c2c80b220108008203203d000006400c07030b0715003001003a070f01c150300042409104000f443e6000d42e0000078a0001a0b004002d41c01c2e80010080050140c0c0014468144080c3c506407000c90104c7c100b540491040d40c010000c100a844202245098070b4405180551500c02082d00110035940e0f510791302810007041c240d07490281403146000b4400712405c2d90004061b1680d04414645139461184e00b00c0004c2c0c0e004c07405000e0920100c1e003a1002c2d440b0003450380c01d50700401040701c88542900c64206400c03a0942c100d03a10880040720504840f07903440030040d4031139080c45501f0740e803081f0102c402c2c40080e0148001d000013242c1345200003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 655408183 1250 655406933 655406953
    0xf160212010906020301050a0503030403030f031a060a03140606031501031802120607021002070b06010f1404140a0f0518041b030f0506090d0801060f05090405040b04050f0708120903 80
    0x1402c441e00c03050b0a80d502900000103100d98141030380c1007030050009800031890700d455034800800210050f03000e042099141ca20200349001d011050610001000301100d6880c0c001c1c21000e0000c058049042c800d50b074000c00020f91624221041da031182d100c07010b00300d1015040301c0045008180a80d540c4060000128a01c0301580381c1d400701c608200070340c8000345514104040041d00e8031042e074400c0b07940f035070040040f10009920030600a800143c00c1c01e05481015030b609003036480c100e42710804281e914000c1000a1404201e241c40b056115040d03801940241c0c40d0007000c1c04840c100e004560f0003c400b101e10248012030120016401802501d078940d5605038003074201041d03a000d620640300346112801176000d0207005d01c651a0000e1029000b0075000451040150079a64144148028040410303640040d4034050f404503170200e50000d100308200d1900b0f00d0991010101600c2c2a202c602c983ea42c001101040002c021b02540c142030000c001400c0b0318010b0f080582e0003000d000d074250181c16012 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 655409433 1250 655408183 655408219
    0xc240d050f040b091209011d1002060a060b0430060c03020405090a3605060c21070203030a090c171c030605090610020705060f040603060603020f1602 66
    0x40d60107904100c56400e120706260a00c0c402038500030b40440301941000c003440c010f0340f0317108089521541007824000103000e035008011b12400300404079039802c00c0c0b031124151041507000c10190720032400fa240412070103841c0c610101e164010350080082c1501101d0754400555141400c0c10f0b502407046140080504569a030f074020f5038010803586012903000704041c0310303900d0002c2c039a40d03008031028400c0151001c3d54032a00f4101e590a06c80354400c0760004207141440310b60980301e204031a0400100c420f0360034002c071054026400810401d80c10724441c0c152510704100c0e0081c40e801500c0c1ca900842c1941c40b0308669500819158170111424441008005010311282850003041300d030040c054100110880c2402c80004040080c0300e04040c07a104060216540e2004003e82102003603664080d070403200442a850728806030402ca600001c041608403400341e00400070003c3e00c690340d90030705c9426504d11042d01a070090610300d040d9030030140702503211480f5041910500b1380c0000c19004c0110007800403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 655410683 1250 655409433 655409441
    0x180203030a03050103030e010302092d03070e09060702060108060f0601181805010e130f0c21062306010c05100515090610020d1107050604090e0f0c240d 67
    0xc500040b0f42c94000400605400910400c5035020a0030190301e8000e41800040c140441d04407014007102d20214640814004800a185290130260440e00703140c0e22602d1540d600082214403144c24454030000034069813001c20f10340c0c1246c245000511041c3c8540d0005400c110001b883d01e03041010000d00301d40d944040446640c000c08844003000c588544a800045c10b45170160400603c40100700c00780125140c00c4e01d01c60000c10740140810010002514010400c14500e5019000340d55040010a0014107007030308051a0900c950410420f81c0b8182e001400e040260440d407403a1012801c0000f1010b5010b5081042e1081c8030380141e41e200c00e0038282100c12510150303100341040c01d0003e02c5100605001c0d4046401c00001c0700ea000d50280c500794001d603a000304541c044c040158100d110314a4030070810811000e0721000317000548458850099200420402c1c0111000744a40a250f01d4482c6002c80c01000581c2c02030500b4600386110444441040190011180d02841c20000d07034152241c6442 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 655411933 1250 655410683 655410697
    0xf090d03110102040e190c020c010302090a05041b080f011a0c10150807050f1e0a1508060901060305151e030f0309011112072607030f02071401021018020303 69
    0x651040c01c3c141202c0e41c85034400700c421b54204036850f14140c00940d6400288410941e40c0034a00507039581004000f195103042c0c503a00003504a810000e844d02c201c1c0d6030588846041c1901e035a043c40c10b80d01c0c48803485003e0028840c5200540c0c2c4184200d0041c03030004010080100b0210885100c3c040081850b022503207048003030190204494000c2c01401400e1000c00000e0a0890b0000a0740341d07804001040c1da415011a4441884151a9840c6941f0351400e500700a180c040300454030f44807011000303003004108071041c5110315003007000421503a01038441d0900403600509030080080d401024002c181080f6803d0300c0940004200581a40d47e0030000d44080d261000d000d580c0b0b98118070000340000d40d0700021541d2a80100741d2042192400005561119421460700d00301c1550f4501e9000e4140743c441218800340000041034001d168100450000321852a0308844034560344072074241c00b00524159050042e003002c50041c40b1040c2c1600500401c0015000c0317a000c03450340350300203499035211032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 655413183 1250 655411933 655411949
    0x2040216200a0801061d0a09051005060f091501030f1b02030c0d03050112080a030b1e1002030a140d230f0f100e100905090c030705060f090d0311010204 67
    0x1521204003428040c00e004010040310f0020f2250320305101525910301311551a40d02c0343c95495002800c060116001150f4043d04401036031456045c0c820340d0800380c901199042d00036000200c9a40c424108a004107101c2e2940c502c0203600d00500c600110040c007640c5105c014000d84034400c0624180e040c400c2c000085c3d815800941d0340f58510b103805401d151100546400349880e01c0010030051b1110158020b28560101500b965201e8080c0b0980080980368682500900d009007050070403103e0709c03660706c00043d04840346400624802c1080ba5039210f281c00d80800100302d60b041c8181c04000320040c0402c42c0f519800030608005c12015101d2074040912250109003c1d0418080c1d0000d40210480c2c204000902d14205407401c6030b0a041003229500c5030700d01e003820880000c1c2c0082c1c440031008000d441d070744405000c581070924925a448205401c001e21038006e204002415241200445400c0f00c039846035103003040b014000304216258001420303800d200810b260310440c80d40c20303c010030140c5000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 655414433 1250 655413183 655413233
    0xf060d0906060b1912150b13031b060315030302120f04090908190908061602010b130b0f04092112230705130308090d0c0b0c010b0a0b0702040216 64
    0x540341c028860706003005c9900c0e1651509030071407081e603401c10100703080d00c078202c2003035948038103505c082c140c540182d40c00542424201d03c004070078000700110020803035400359020322071281a10a03007118030401e84402800350b403190610100d2112602c2c040c102e2640703040002400d141d0307910040f9058a120b01000c481c00785000501c007813480080c4c180360001044502d0411041e03402c001441d9a1100045c0c00c2c0f14105c9540082a030810707100750800007044c44003030028050b03128030030f0240300a440c071103041da8419001c9140004450401d4400d0303040b0300b600107000301503020941368818941c0890306112403c01c01f4006940350040402c0c006c80100c503c0c04c0e0051005054051107001c1d14030400347c00041042002c001d064000380070010220152600209402d588008000003c0c024441c0c00320700401d00284000005440c206040140c2a02010040240101c16400c801c01160b003140b401a00740c60700741400180d000d81411750142c007511040c150504e04542244e01c031050b96807000c90003a515170380c0f1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 655415683 1250 655414433 655414477
    0x6080906011e090504320c040f020c0109110109080c06190302071a061306060e121c02060f01080c10030f06050d1b0614090111100e1b0f060d0906060b 66
    0x46e440300d8501110000c4550540c015003c5805840741715800300d541c420b6403a03e03030301c102c1d40c0500da04684951003800001c0194040034a41090003180f480540c0e40421780b0303a90001445040480c020070a002c00034002487c00c0c4880031002c0d2040c42041500c010143e0920041c00000e44c00140c2005c0d082900a4018252420b101006080502500408036050509104103e0741e5000354911300690f40c119918100c1d6000c624029140c4090382c000c2000300c2042d00d600c18581a004a6134034001d03008800c10002c0e0360f03203030030a007940e42060b00c4100b608001851014030246101e98003400da138110701000030038042e64840005100900486003582c90481445101c1100240b0781e220300d0040602c2d003480520801d811402c81803e00803624828140009060406a04d0390107000c18030a004101c1001c00100d00c002c1c0e990356584203400703142c8000b6044202603001034a82a01014001c9400400d500e1801c40351030407032400390000c00d00494030709807521804160000420040d240207844002014074100c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 655416933 1250 655415683 655415723
    0xc08060c071e020603010e0604091e0c1a031f351513050f03030a02030103020306180304090b12070303050a17012303241006080906011e090504 63
    0x42c0206044034030300310080b103600180c42e41002d90f81150210311030203413a80d43d81c0011030b000d4110300a00030301d10301a500300300c0b40620800900034221405481c2c0d1140c03868940c01d5007040c0c00c41c01d8a088900c0c100900001380582e44460300c000e00700c840300314408a0a82d030791442c40c000c02110f400c201000d0a20002c004018204d0120340e007100e08292009008070a0940810910300074060700b4121041104111a001d11204001c1d0701c001c004c0100490f96a0310309225154001d400c00e0104034468081d800c04143d40381c10290110421809a10280d40742c01e01c0d1000c0b810003080d02c940b940d500646420f801d1a510754051019a00960103a122903684840c0443e000709a01e183c040741c540402859801800828481c2000d4442c00c0d0b12000030204030300120001a00e40101521003500e42001c0080c107010320310701e0302d0096004103103402094928a031541001d8030220700481c1c440f0441c1d4440401042501c50066062001610100c0840301070341c2c65003d01c1c815034008407402e5550f00503054140812030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 655418183 1250 655416933 655416953
    0x4031e050904050919480b0c030306060a0e09040b090d050c070302060f13090606080601050720060d0e07080609072d15030c030b0103150b070c08060c07 67
    0x10700b0a5003e080b0340425560462179500c00a50080d0a400441d01d48210144040116105110710b00368140140c0201c1039460214040c0b80d01c00c84000c9000c0e0701d00050440741034003502c2c22a880f41000d141566602002e114050b0031103802c034030802c5004004800782e80c0391041c20318041c0380155642141340c6005002c207032500164500c40d0042200400044207101004031324202a07a40c12961943e50785040ba441001724054800d080c091021201d0000078140f00d81c1d4404000c03180207032200650b503030b03464005594500861001030604540c0001c0c6080c00c41800000105d00c2d030307006089608003d00c0806c140d0817039003e206c1500c910340c0496024031094808000f09070307000b0500c070018901e46007040035045403880c0040c014080b541c62018480c220070102d407c440c018000c00324901c110042d890b04010f0141072038920311804285031092101595102c1c1c06000d50f0001801e8080740d865281505801030740d80405016640001601d4012071103400c14028940a0004600c0082d04d81c1001e04050f0180 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 655419433 1250 655418183 655418191
    0xa0e01050601020c0312030c0d0501081e031c0f0905011104080f030717030901020d18030e040603020307051003020712020105070801060305042301090f03091d04020f0904031e05090405 81
    0x590f01c008018071080e074002407600141c01d00c101c1b00302e0b05c81c0c986260401150080c0e000080145080200116128030b0000e036035900e820728105550100d9980220b03003600c901c5640d02c1c250301e01d681d60305400661f200a8100c05948a42c01000103444040c0f61203507821200e40b14528200b487e4001010400359900700402c0e1115003000018520f40030080c1d0300d6500d091040144052940030210010b10019000e40c16204480c0c802e20701400a1001d041c0c00100380d45880d01c0441c007048007c1180d404c282002d20450082d030f5409001049160b007040100107900004400400c10550200f10b072000150702c500144101c0c603410780020600b42043c91000d024910160403503000c040c501002c020100e0301071801d5540207402d4034010500e440c3d210b050b10307002d408980f002034044402c0ea19600109688071200e10308403221500301030040081d5840c51800a03906840c0694001d03055513081002c3c3c42c000c4ca40d1a0013601c64200b03070310b1241e0f04070310650078104000c11030400305002189444650601e409807585c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 655420683 1250 655419433 655419437
    0x31618060501080f060f010207080708030307120513030324030809090702030703050d0b0a030b07080f01050a0b040513140a020d050a020c1c051b0c04061d010611070504050a0e01050601 81
    0x520b1602c058068134001d40141010f1180c029500002d40d564003d020440203800101d054840c9a03480d8103070941d0300c0d8420703203401d800111140b5503002101c0151048a0060302100c0390311150003c6a103048010308241c0c1290802d101083c0c1c4490550030300c001404c0000d41c0702c0c110060321381201008000c041040140008155002000704000181d030100032a40c0e851035644c000140c0b00e50100110782016035541004103816400410300c20080d410150440c0304003520001c00886a8030343c024440c05048074854400b4200003400144101d01d000040e4003800c0c0b04122000403d0058680c00e490320341d00540b40c00c140b840d40000e40345440310032030280544c030031782020003545400500000c1e565551241180c080c4089281101c41c0d140910070310072229040c00321003d07500240b8050095503103c42c40c2102151080745052400600301c0303110f000710040b0401052440300c803a8a01031080e2008001000b1407107031402200800314055450f4405c1c2801601c07400c40010702c4180202c841805c58034050b1050741 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 655421933 1250 655420683 655420697
    0x210607050f0f0c01060521010e0708070308090f0607032c10030c0c120315051005190201020f030703061716180f0e0a0c0906060f050702031618060501 66
    0x10320720421a084500000c08412807580d41d00300c070300304140140000d800140e4881d0340902d143c0c0151206148012246c0c4142c03008005644015154550f42e0b4450307c10f203890b40e00a02002c00c04915094040d002005001e08401d18081e004800502d443c0c0c02a282100401c01d40c0c6041c1c0c41250907040600d2019a054282000e00c100d00400a4a111300317641a1108064841d541c1000c064420021002d005070702038140c1010001c040409405003040e0502c1c13023200d040540d03001416141034503a02e1101c0301d250311001d00e461f006d850f124500d01c050703c01003410b564082000c00780181e205402184035020981d4000740d41424010200100ac3c542031840080307a000c1c51380f942d080180c04151000b110b090f41d4204440303011030740c14400500130144d0211601480c10740c3c2c464406c072020a1040106218200b8003c0da20344403400c0c1d008a80f103d000f410001010710301d080f441c040c0280024641c1600050403a102c03200d40507182c2c4031081c195080031011034608200c2c40d0518056001e10400351409081c141 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 655423183 1250 655421933 655421947
    0xd02010c05070b0a08240607110a090203060f0d0c030f02061308011508030a02151306020f04060f020303011a1308061003230c0418020a080d0909050601080613060521060705 76
    0x198803c07406c09140b40708010020b42d80702000707258020701307161030320140c08007020b140d039140144000d41085038201d01134210300c0c0e01c500543c030302190240c1d00194030105800c411400e5860f00074009c0c3d28070200b2078220500700304c80804140148110f1005142c258004a159040c0041d104900d8010360f00c4560160b100344041c40740c0d00d40110388805800d0841400000b243d69100190303c21561b440c102401d221301c005100490600a00300038010340b501511034000010f03500350220382c4c03403100740700c1c5410440109c5001ca56072106c040c02451940700351a01c804900303032100001400c154ac1034500486002080100b0400c1241c06030503070f030036000b00100c0c20940d10300d81c03030b070309500c5d40c9564811500c00c6580b91155071650400070700364032400340c02610161000c4d80342c01c15240d94000440d00e00004c00e4244030700003401da410b4041d41d44a4070b810796640c403c030b4983c47e0900c141c095100d030400c0030031903d40303501103401c1e10b41020245401e850b6a0584911080201c43c4900307228002e4603510800c44204144 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 655424433 1250 655423183 655423231
    0x706061d06100f050f040b18060c0d030207030c0b0f0402011215060c02031504051b0d020a0e102411070b03041410290a080c0d02010c05070b0a08 64
    0x20100510ba810540c042452140c402c45040c403c4401a03400c8504c08a008a0f40c0c0313048002825280c403055542040b901d00c2e0000f0494907000d100080c4155a00186503540340510940203040d0852117806c2c40142a085c1d6501c0402001d4100e421a0620030b068040000750740c2c0c0700400c05041010020100312020161906c915030b900c46006003400d03c150b00c0c01250442d2000c12009901401c0340400a41606003447c24545038806500c40c62820401d404900c88145050b1000c41c0600d83d008201d00d208034940f0741062400c8800400180c1002c440c410005503101c0c07400140500b0f8901800f0314400c00c4181000a018440281c01e081c007243d024010910207102c4c000c084a8000e40c001d51441c0740303401c04020307480c60091840c004060350360030481126811112104642c04c0c0c0003070304000e590f0480070301041c0441038200d40306050362503004074040304241c140980c1c1d117907030039006150954100ea42521800c2c60941079070700c100c4c04800001541d160b8207510490254010000c0c9440d804100c03580944 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 655425683 1250 655424433 655424449
    0x180b0405100519030f050c030d110a110607020a030302011d070e01060c0c031a0114090f0705090a05041e0b0907020705272a070f080a140706061d06 65
    0x80c1c0d8010489003030410600c82c2090650f0004544c00401c0c4001e8402910348030b40c4510409000074041e10803200d1050200d40600340000490381100000c100005541d16410303502800c52010a420400821080002d6142c1c0b01c1003001441c02a000400c16580d41c104540c13041986000c1d0544a4000303a130180301d0044080c0364681129030342c3c5014811042c4604001c044003246900c002c15100c0c489600c0c141142d40b540040d412624644010385a194005003800800c0b181155014140e110820005a1850280740078001484000e041040601e8588000c1400c03110703200804100b40500845110b4130700d1581c0a2480210415140f0100a0810b00390295a076491402614420841510015588642910038100504052074001c3d81810411502e003804803050600c1c0074800d04400002001c42e01d030104541d07940b40e2000740415048100c1e00c0c0c0c001c40c0c2c1c001440d4441005601c03816003000914040c05403d00c14018a4001001890300701e4030540e550300100012001030340e4408010066036101d130 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 655426933 1250 655425683 655425689
    0x7140906040203060f030709060501021c0503062101020a020307140708070b25031101060806090d12060e1f08060708060420130314160302150d0501180b040510 70
    0x401503102d4039034500050605001905c0141c041c4642c420001780800e0a0b0000d400700e0b8000e03000e8481c061031106900d0018201983c1c42008107030104040340c26410004240c001e104015801015090300120081e82a41e0180e00c40c0d100581c00070403030005200300c0c4100c45c400249008001d00c040c9251168031612000340344244a9402400b0030310303100c1c81c003032080c0103004910201640c1c654000a4070300608184140c0d0700c242c40350361a000740850320f190000b0b055030007240c40f0300042c11540ca03d00411101000140c5100381d040d5140c0714009282110540700900485084c44001038a42952440c5641d6203003540c0305005a038807101c240b0100c2c50308441c00540045040c4e6004c42c00c80011031000e0101c81c0d410544d01440000050708989a0b855500030301c00b501e1080c04019410789148403207039aa07010712605090b80500c0040c04100515010802000d10042070116505013990300132180c0454600341e008501c41d14019100c0e10604000e4414680380e04400c640c01c101034144400398940500c1240 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 655428183 1250 655426933 655426939
    0x70f0906060809150c031e070504030b0a1413020111030d1d060408040303030b31202d030c0901110a11210f0a03081320040603060905010603020307140906 68
    0xc040780c4800307e0034801742100f99590754840743c1810800c1c80104194890303c030580d01c0c0000440410721894860246007050640055004100d4544084080784041c500600324140042d16a6044c0c043c10144081d107080ca8014070001840210000000e2649002142c040410740040d001c120002c0d07500002d88041c3da4240c0340c0041d1001c0e21101040c0c5042d0700c00d8103600c1c501e41c02c1034602c401c00d074903050b0026000000c00b8148500e01000480c115100440544914181428004117075441107526a0f8006580020124008003510303001d04032817a070080c0c0c1c2c25000c5c2080068000f00b596003000c0c5000344900c2c042c005100310b01d000d896004144103210301c1148101c0303a48003041540a0303009000f500c00c410fa10142c880407070300c20041903034503500d40c40102d000c25442c2c400911910782d000c0320f00c2001d0782c105119244121907444000e0004c0f031015403846c2c0c85a915100400410420302c00e8001d8244514000210300b41140109480c000a9070b225100242101c46240c4150300c50044044e003191040e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 655429433 1250 655428183 655428187
    0x30706020706260a1d0a0218130f050a03032306010c03020c0316030b0f010602190614040b0a0b04270c030615060807030c0e12070f0906060809150c 65
    0xb964100d544010081648000f8140c05040c00044040d0394848107440f0020003042c0750344460f01e40f61980700c04800002135072100304c0e07010380d4404a80a400d860b500c40300c0c280300301560507400e6a542d81980000402070720035900900340f100c100741c3c052144040501805500d861014440300061440c808020071080c10403200002c2c000806000304402201d041c0e00030140e44000b154040343c8520039225100941c8c2581030301001c03803100c81c4001105411b84034207902804501c80e5001c54152a1412881c0c00c031071403035641304001004c414041c43d40780030701d224070f58001d824201840044180c42032048a1446240360460800070920310030101325042900300113101007090103040001e0241c401d684007400715810010b8800102910507220707419500305440300034840d100d000085044560806206003c1031050b1602c540c94030384600303400301301d80201c011210344c0307a00c5880e900c501c0c80e940c0d404403008580780c082c01e0006a8000802540c40140d0600900c440d4071a64010001000050305104d803981d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 655430683 1250 655429433 655429457
    0x110306010f1206090b070e130b090705030405070b04060806120601050913050c0907020a0b100513090602090d080d0b011112030c040f06180603021c020307030e07090c0e030706020706 80
    0x10703980000482c1da4000c45c5040c1246009100a0300d6940b90030803542c883c001d405c48400e0341a03003d1240d008074840292150302c05da40e81035002d032029030000d48181c0d158032540c0340000310f0f661244000c101070001da645801242c20501c05010450401c40900c1d0982c4e00300300018010340e00c440804075800301c01c0051122149502d1b051070303030912003000e50140d0005403c808000596400141718220103106840010b4141d0b520310103020100304a0244a6001081c03100c0c1c100c04081507000782c02400d01800c40185449052400201d210600240c00c031081c00c0045680e2010720007038411048405000c1c24102940500341d4451a00d070104a81f041c1300c148004400304022441d0001610040e040382c1400d8986562549005010303214045c80c070000350200f0190200700b8512038001c0e9121a9241a410700540c007010013500c1c080d40000301800105652800c0066a004040142200401c8400d40008409000c500300905110384464480c3c003942c049607082080a80c005122030841d4100c1c81c088003d188 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 655431933 1250 655430683 655430693
    0xe042402090301050103050705010801082a010e0d031112040e060405040c080a0501050f061002030d1127040e06060109060318080d0e07050a050307050120031303110306010f12 77
    0x18035081c0300e03015803900c0004410000000b40f1501500e0090300d509216071707683c0451540e02c0482c50305d01c000c0d50821000b841c0c884a0010006845030324141441d41442d10a0004200720f0b010f4014242d0008119451240c500c1600307201920321081c2c0d40301140e29280c10075040600b20f1030040c02c1d450081da6100300140a0090841c0c1481c05011020240e031040c440070f0405038041c01041e502c4070440445003020681618068000d4400c201182d0051400c2034401050040140000601400600e00400101801200107030590340d0f00b40080c0038041000203003e05000455940c0d010039100c0d6030103403046c0701c4941c1e0052203140c125003130b030300e004111481c00d05e80941c001c500b5400014103410001c615480d001c01c0c00c0d0060400b884444041b5644150b9a4040280b03c0f600d0f0320a054054100203410300855100f51a40c080000c81171490044103044c0b1000c80345550310404141200201001080c8108580410303004103a1400310b0091189506160700319102403010710501c40c03076450800d01c2c041080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 655433183 1250 655431933 655431937
    0x100c020f03030903060103050a1209060801050d050708030a0201060e0c0909160909110405010f020604020916030605030f010204050a0e0603120d0b03060a06050a06050c030d02161712010e042402 85
    0x30b03030203130a94250b03503500e14109a5030542c0c8041110080c085030000030283c1e11a220300e0b0b0840d00141d031640540d0b46004c090101c18a0840310030ba59a0103002000f0a14200810023800381652a41c0009485881c0242400c080d6401419282c00010200040c40b406c0c4e468038512038204100141110940d807003240295026605603000181060400c2e80710355900081c40050003c1726001e81f2001c0c2c40320001c1c032040340c4805d01100d009600003420008070b09021317000e485c0034805c0d403464140011030301c1d20307540042c0c80e040600c5000c0c2c005a40000d07081c0418105002c480d0000d1802caa501c0040d400c094000a032605510003d0030328025002c06c094504440d542c000004841c005010b403019030a0100c00381d40070381628040c55004150034180040c0c214400c500311207000c1e10700300185007800164012803000c1d500075101c0e101326001e40c1c9545030200740710907107100403c052401013035681d543c4103005001c600030591210b0784c044480310412020a101c00000c040c0649006049500710811445480c028 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 655434433 1250 655433183 655433197
    0x303180512040521120901020a0b0c0415080915040206040e1f080d1713050d0513060c020d11040f060e01091805211224100c020f0303 59
    0x988259012840c59050394801041528404e4880c0701c100001500307903d04040300491a0242c541c00035003414190300e950b2018000921052058070760700c02c2951541d00180780c4c256045010100001801c0000c101c1c1c0728100800b100160404200c80d1030301e9914141c40c0c850071140b80b00c4980400d40010304556400003100c001d844500401d5225091810710030660a001d050301e500c100c030941c1d40108803140001101404a04582d40d681c03081c04140c41c5e00c250064000d440400c2d02e528042c50000081c4050011001203511952030944441c404107211200801c1c0c0c0d0b0000090007060250203000d07807105801c1c290526080024820111869004180282401c4455a000503c1d2240103c2d43c8010303005c9190480c8c19641090210302001d500c0c1368848880300c50300500a030b0001c03000d220490010510078054101242c44c039420502c1c0180c00d441148011903101111628600040004070040010100080d800759012114018945005042640c502d503001c0d2084402c003c2d00d0040350f404000315452 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 655435683 1250 655434433 655434443
    0x60609020403080d0501081209120c04091a07212c030a02010f06050f010c05011e1e05090606040e03071202010221040305090103091a070831030318 65
    0x1e41d540c1c0782880000e07900003600442015061000000308610005502d0f080f4048034403205250140c0f000c104070520000c1c01a00c000350207540100e505540e901d209012400c3d001d00301e1200101e041c0c6400d800507843c000c1c0808180604200c09500d840340c0e9480c48202c85480c10000916a00c0283d240d00100800c00c2103144c0284400404040d05003000c005402e0204183d0000d12102811000c0c0380b040d101c06000d55078110b40c40300e404403620f602c01c03003084000c81c0c0590f0000500c5262203c00480c4000314100406090b0f071602e200e0340b14504880000a002070a4100030015410103168a6455210240040344030395101e500b0030034903000c14002c99400e241c0c0104051628200350202034080d40003550cc1e0300740d6000012806500c5402c2c600003601c12036041c0c2d0b502d840c02c0014070066000b0010a01c003a41c260400a0701740c8010316644407224014481625074520600d44000b20055482180452101031140741c010300c13011103205500425041e5040c00c1c0411806a00c424001044100b580c0c0a89 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 655436933 1250 655435683 655435687
    0x2e0f020a0f050706020706031a15071b0608010801021c0c0e1f080601021906050a29040c03181205070b07050c241f051e030f06040b1306060902 63
    0x802c0100014111040340d030603400383c0c0c5040741c0d20380d0261308540e00e14000c04183d40070100f015505180c00300e04240031400d00344c111400c5c28460307107030902d9004000745d542020311040281030003802d80040c0c186c1e00509660b802545481008901b0800d140300c04c6005480c0f03103843d5600c0069050188040402009018059072121b5a000300000c01e0301c50303014000300c0070401c100d0103d000d55201007160f80f134415201883c070341080c030503954810050500074642d140c0d6959a500c040200b01ea00c054040c800281d038691001e20380311940c00c11080b1703201c2c03146501c103051805a00300341901c1001029031a0b45d0300900c0c075809107070132510259610b00c43c4440c000e00301107007041003122140d0810301034054161148122641209048180780b0200d051a909900c1751200720002031080e424400c003100d0b501c400349207031040e00e65a100818403030250310b0355010350714034100300000050504001c07010144000700b00a15150078291500c0c030324558094551041d10f0780070400282070001c2e0f904054001c14416800715 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 655438183 1250 655436933 655436963
    0x20f120106150c1a060301150602010207030f0915080603011d0708160f180902090a14090604020a030305030726070f02060708010b090112050c0304022e0f020a 70
    0x10340201107a000310740d12029005031000d001807041c6032846056601a82e01c0c1042020180e240742c030540300074240c550540d02c07010082550b10740d11103484010301081d0000350f00c1d60a58980074040d59881c9402c03404101410404010300300c07a0381003001b41c0c00303000d0070800b8050b1034440220b0701421601a006003101107101c0c0e8007011010000700c18040390070b5001525030310301030850702c485090494403c80d94200c0340f1004c01c0c003038145080c1388035600750b014500c0020a940b4a078045600c02d201255148050f542c1c51958240c4503060350515607201d850f40c8080d1000d8a0b1990015142a0f510b0001400708100840000c1080d0700420216002d052150503c040c0d0a0002215800f2a8001c444040009101c28081e00c1c005000048141c080e81150301c0302c41842c0c0c04c2008010854004d41010b50400031603980c8c6484200f103d01c140c2c0e01540700c0082d203070340d2440c00d401400004c030302c4002080010601c00007682c0c0e01d5101c18103220001d503850b20f8509000018030500328a006000540a00200c10802c41a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 655439433 1250 655438183 655438219
    0x1090c030506060306090307081218120c16050a031101051b06041e02030d120f020c030a030608070f06081312030b19030506010b07081207030f0f02030c090904020f 72
    0x246110700780880444990741d8814106d5500c900036148000e00400050001d141380c01105c03803105074404007400c20750749041607030100310f480c00c455858003092a1b130b0001500c0340e914405201c0c10302d404418442080669250001207a41c1a41c0303407102400100c40c910007403d10360f100d0f108070fa00d1134091003800801e29495108c1c441c0c66000c16103003100d100043d0401c4a0340005004080c08007141c004010740855004880155800222082000715050f65294124041805031001e030860601402c002cad0384581251340090111071468120000c02c1d4031035441000044114890036050300d03003602c2c0070072081c0c485100b8040d025020840090010603c6003041141c01e5244d800240c480c14100c60982c2c2c2070315503c0018081601500001d800f43c1c01030760050081c407142c01e0040415a03c1850540d2800c0020a5100281d4400b070300c0d540d001075202c4810014188840c0951031b00200d81c43c900310300e5030510b0840494103100b10201d55004281e11400981135607501d4900c05000d00e000351018451150314110 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 655440683 1250 655439433 655439443
    0x2715070503090102100e060a09061104032003070315020c0a0c140117130f050c101101050f0c030103020f130f02040503010f02070f0f11221a0a09090501090c0305 71
    0x54a0300500c150300c10b40c5074105c52400380e1513800742c0c04400343c0f04584414903503001514040c141070342e4158888402500011004008000441c051140300c80c041800c84d80b80030b540302c15402158400e40c4503000510108880b44c03100903804403035810041c0e6803921001b000e0700342501800f02500002040400050740f244081d40001340f2942641c618800422643e04400c03034480541d03120403451008001000040d12440310900303043d00038012101800c3e0030000242e41a02000c2050300051884100c05082642c240a019004042000c1895842c50701e501c070740c20300d80014403020344540c103007010079811510796001c1c2807041c0200560502008940080000282d842071107102c0c065072270503203444da45000034805e4680c040ea01031001c0e80f8007d104e4440d0341c2e001e041c0341c906a9418601d26042c1a485d5a521030380b52050342190b04482d107400d14140d20b5421212220140175010444186159290340c800007402c066507035588001542c4402818800d0040080c20310050603038072040301c08400d000780003030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 655441933 1250 655440683 655440697
    0x120807021518061303082806030302010b12010c020c06090d1b14030f070e09120304032a02010207170304050603250906050f1804090b04020103112715070503 69
    0x31505503443d80701c0c1385040c0c11201003000c1c2c001803041d8003065100450040c51380d0740900015480381c2e1341d000410174000303e85443e4400c40160b035692151488505280303034111441180c000c000c00c0240003118000e074840904942e400e10444000070181e020760358620a0410b5190442501e0b0890030661403250181d15072402410b03072581030440034800340d142c0003030410b654a0380000600182d03881c08450514a2a01500900d680e00420104500c4e0a4a05002c3d61041d0f019030f0341d05c83d00340f03905042d40d1448584541003210301075088031440090703600054003000f102e83c00710020000441310000d6500350b000b142c10555020701c0020600850743ca4071504080c105424044984450304c42e0201a144440700f4801c800c0400c1003441510340b00998600589510b648010025441003144000074045440c03440701100c00300403503420b204c25940e0521031a40010b810200061034517403509070028010442044036a5002000200149180c86514405400c61142101c90751120386500c0e2054481d007002d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 655443183 1250 655441933 655441981
    0x123040504080d09030221040f09110f030a0b0f060306010e090c090d030504050411130911130b030a0e03180405041103190b09030f0d0b0301150b0705060a091208070215 74
    0x1403047c02c0e81184100701ca00b203441d034101d13009043c3c1c601070000028050074800c51180c5002400a000c2450802c00214407550032440f0008920241c03170104000132800340740d6940900028070410001d40d82003841c44041c07071b00131a542181c6030364050000c5601d204051110fa08418000302407810183c00c00c000d04250f6504440500446c002a050300c081c03802144a8064804c89016041013182c0a0782d00c50902041460344452508454403102c5036a041550322045401a0000c108044102148902554031a0420140d45002c095410007030030728010101d0144500e41e01c82c041000c2100340c0035401100100a01640d00500d01001c1c1c00210341a5508182e5801c4003c2e400100101c81c040110f80040310041e44980c2000a0b9170000c1000300315003400e254041d07603a4650040b0260001046500502a0029041e501c1800303140071414810007400c500c400c2c074108040302001450411900490305858640403440f40c0c1d50a030704a00d130442d80ca60601c80e044070034080c0840011081d148029400801d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 655444433 1250 655443183 655443223
    0x60b070b192903060c070c0b031905010e09010b0103060e0c0f073201090f1502120108010204050103380a0308030f070305090a0201080a0b01030e03180102060123040504080d090302 79
    0x3c0382840d2252044840041155213441424002301c08218080c5400c20014489070000010b4071803540c04440c0c00f81c11400e03030b5251907400c000348405d090041000c211400e103024050b4a290103030b64801c1300000f80c11007144807004100b594254070301002303844035145c100d030060150807400d401c1010507800d0141104082240504102c1c1e14240501840a840e0360140780c1202c50a42900c0c0c0200d54013410140c400d405400700b043c1a24941c54200d45c5020b0030034880010307606c601d400005001c454000c00c54108144003907010098103c5a40640c41001860281c0d070f0050060031000a0341010b0181c100030007142012043c0182905076411440c407a800a49041005455040805685099504000740010b00a400081c010040780e0400669401c044c14045441c440200c01c0380c0c1913400001182807110030022091803d076904001190040c004c50300003410701041d961102041303841104800d80a01d88039408a4100f011020803221240b200030300030441118549002520b40c2052060894002c2039 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 655445683 1250 655444433 655444441
    0x2a0c080f0d1116020f0a05040e07052404030204020d180614011406070219080304170d03050c0403060506010c060e03072d11030709060e0703060b070b19290306 70
    0x182c504403502801426550014940700c1e40c00c1003038440604400b01d8004c01d5400c8005603a80300e40c05012907001a140c05052034038180400d000d00804002d0400e00704400c0294062a8030040d07034112819285c0507607001d603448444552a80103080301d00e61a01000c030455910105210040d4044010812010914506070340c0e258130080750103c000044e264042c0c002c0002900514241138508000d02605035145541c1d40d40c2c0c0703005804c5810030380c807400c44240c4030b80110340c44800074007000c0601032090408105078200b62000744850b01460100904003962840401e2607a03001e030003034206803135000b0f105002010000303034156242c0d0081c900880d20407024004001d9041c014001c0c0140000110001c5a00c00d586a10b03004280355403000701c581c05005411020810500d1409201c024011a21840c2e009050a4900038200d44007a40810705000c0c003030040100080040b0300d211340140c80340b03468203030000280c41900300620841400501c4c56800c040316145a00d01c100c0401180302d402c4003036440b0303552 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 655446933 1250 655445683 655445711
    0xe0f090708071503020d060f180b12030a140c070f030213090b390406090b030c07030806040b040c091d090d03050705070f03021608012a0c080f0d 64
    0x1105024000740000f000e182544194440e40c05080d90b03a0f110f0102288485e0750300c048200c0710106400030821110440c3d000064141640a8400710701400d07182e14007840d058100903030702c038040c038104601005080c41101c030031108035000b0b5441000b03000342502d510503a103040b0002d0013400791008a0103490b40d11341028107040103108550045410108103007096403400b14000154421484140c2403400640f41c2c0c1542941000701c2803e41203124050587d1a8280500545907001d50791001c13625610800c20030a5400740101a10300310b60389070800003055200c000005000d011107030b40854101e0324100c2495500c0d5489004c11003200c1c0d0342202704181c15840b54200c40342d03a60440d00304805a0003002080d00840c17003a0300069100040349402d9081a440742d490070341b1800c200d0380903001a40041c81c1108070700b81005555004040384c6008101a40130007802d070bc070541442c3c101c900341c0a68000512800350141040302221644081c656aa0ba0312096284ca00b503040304c02c0c1483c049280c2450411215 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 655448183 1250 655446933 655446943
    0xd050c041503020a1d01110327150f072301050106110d271e0509070e010c02040e0f01020c030d0b10080a020d090b0c03070e01081e040204060e0f090708 67
    0x80003a079281908030711600790705d003401c10103000f00c0d034108074a050000804513400e0000c5e01f5603407091011840c40826828201c0525915036440764450b00078084d00c60080408039003102c0c1c404551103011f588898080c101341c4144061115058403409450242d491402019801b160580f885611032b58085a0b04920859840f07043ca4403034400300700e11116181d03029600d00010b085c0c25481c500002a0992542c0126850b901c0051a0300700030a0400c034240403918044d00e855a0100381840e2110b80b248602c0e000038000c04001801038010380d070b01c05200700c44110901580c50036822010080d583c1e002400540d135501c3e0700500e20114407914207034082c4240e1a1180301d1281d8800b250740e903424551940440b95009520905080d81000c2e600c0b01c44600041c5944602c42c401c4c5100f0285a0700c0c0c3c45c18020240500e000d8055071410400c1003010462009202c13800305610010b100b0041c4142e5546102050040600b60091013a440c1c0d00780812043c0400003440c144143c00200035550040da9a00c4030a03070351 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 655449433 1250 655448183 655448197
    0x301032f180a0204080a0804030302010e060c03040b07020a02040516020114010521010f0f060603150305060a0e0f010e07030c060201050705030109020c1e06150a05030604060506060d050c04150302 86
    0x741051041e8900340300c010034107940000c1c02010051615a44900031494078444070000c035030080300881c0c100705241d02845034440285032107000d000e0a1400d40f11408079031000030401070091040001050780d80c0d01c01c22014035082c0c1c0c0500100194103007001d9812407580180c003403000560a01c801080340e00b5a05001e03504a610160242c4011a180400ca92000050411440b00c5640c0c501081e11200300303e000302c8442003610170300082c0284c2032040090a031101d400740d03101c448164030410400110001002e5074046046100060850030b01e0420301c1c246040c0c040c02021030b40c02c1c000c1c5020649000701d002d00c2103a2103550300800b1556501d00503401d980c8201c41050108405000400241c9055001000800710610a480058200d1810000301c80e0a0340c52605043e44500100400703055072804500c40c2601c102d5001c51654a0207001982c2d404000b00010b090588800100c1c41907190340c01038900c0da40c00c0c10001d01c000d00d040412101135421a00c210b041190100710f5090415000e44225128 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 655450683 1250 655449433 655449439
    0x1d0111040f120819020f0a0602030a0c021c110a02060c010b010801080610090c0c05030d0b010f1b020409061b0c03120524060c01020412141c12020706020301032f 71
    0x20042c00401c40240c1100004040040d030055000898038003800740300203048580308d01c500584038100150702c8000c50785804290400e65200d15110044800741214206070b40c00719113401c91000078800c8049040c18a4014000d40000c408a0750180b001010f40044188010a0b62400c406a9a40100981d1680240c0e84546220000e102c28010300d00e4a4004000c02412410304908a45070b0f950360614540c400c2500060065641546528039a070109214602d82c43c5c9141042a02c02000000880c08105d082c0080c4a41d030303a0000881003000350740121840c03240a121100507100700a40190002c20b180404400181d8800c100506d04d00441c8141c5000780350b4003411031442d02021480d203502800516426038004002d10144002c01300900040001c0e1038444c55040c64100249007402c681490040f62192503081103103481d2112071807801d9070303221461510b0308952101004c40300034024400c500303020340030314000000403003480901211210102000c07001400c840860000031110030400d405040c0d8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 655451933 1250 655450683 655450687
    0xc07090e062a0a05090d03020d08090c060406081302030d05070c091808071103010216231c030b040501060e1314070309032006180303010b0301091d0111040f1208 71
    0x707402e40314402070a5114010b0a203a864610000f0009110013804501200160b010760214080381d50710010a1380c11041941c01010340310540b80008049029034000da000704083c0385c000545a40061040e2490b40381c0150a45880100a1100802c0380d4000032040d50114443e140016141100b40b080110481c550b0b6050300340414a6994508150b01840003130781c035400480c0055019035002c0c402007410354078400703041c0c44840a80c0340000340c61101001001c1807512403038100c01e410030041248504420850f041c0e045070f40401105400400c00745442680140c071b800e0003c0b655580101090309001d03021a0703e0701ca005480d90300c4d8400c0e40e000007a000c084003c0c61000c11074150003500000c1c1082d209083c1034203411455400c6510b4515080f074610a143d10510601c40d0019120440089e02e181c990007a51079581040182d03c0350348810300c10f5800413651440e400c01003222008001100d03000c920005c1c85555401451003400390028024125603814528000541e507600390310200d03040d680840694 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 655453183 1250 655451933 655452001
    0x906090f1a070b010b09120105060a14030a14010b011b11150408011109041103070c0215040b0a020c0a120c05150c0304030305070b070c030c06110c07090e06 69
    0xe04648160403001c03110305414007140d400941e1146680b4040d00810075100d89588480040100350f05080d0280c40e450b0b4907100502040b0348980540303c0c103507402c1c51030702c1c0c11890080e0046454502070060140c03040030000e21980c040801034008014a5500342d8551500d058003007540400123640d8a001449000743e45000005410016811104892171545040c18140e0702ca1100f820740d81e418410000f00da00c00210402c0c0342c0f0381480307910801b62410948031300314503083c070020700303110700845000e403180454024051041035010308850181c4502d1101980ba40d10b0000042d6403540c07011070092050380c9411000c1614800240f0300041940c0101c02442818900002e00503885040a40c008140074100b0804150741e0041008100852082d03541ba5560103150508680421025090a0402091116040110341e1102a03501825000100000e5500b00071522400c14032031210a080715008100000440c84602d034460510001c5c0542640d0255803058801840d4040c401c21f0704103a107595034111 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 655454433 1250 655453183 655453199
    0xc090b19050f0a030e150408030f04081c051614090f04090813030b0901020a0507030e030a20040f02030603031e0c0303040b01050f040603030203310305010c0906090f 73
    0x414110306414510300d05074001ea0a090740380d1001c491080400d8403103c1c0c04040e14410041c040500038204621049800c046d66010883c1c40041d00d0700402c800c1c48000728051007040000c5400e8403511410f84025881b80d4082180070b40022101060081c0070468025050760291000603501e4171000c0b4a01c0c50800d4a6003000300142200ca201a00301e40e43d02010b00000740c612009003040001001400030351880c6190912943e40001c001418a9006201d4818100c3c3c00000781c1d04083e5241c10b01445039500350000c40d01e490408400030f000c012803042210528583c20144548100041e5030a11441508944071416440240c403802d030558808c0202d51030101146c178410ba000050340030003515090303151006a1440d0001e031801c0d90642e01800041203c2d00d842d0190006c03400050301d05100710342c59601c0103510381c002c51034154650307849286109400074004600040140d04602d50003162a12818030500a011101034a8007260910f20041b8070a4061426542120702d07018001a0181c20074034a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 655455683 1250 655454433 655454467
    0x30b1303051603140a05130909051b12060a05070f0c020a0e1f08060604242304060305010506010908070e071808010513020310090812060607080706020d0c090b 70
    0x1a0101301070001941082e482e150000d041806040d92200e4030358801d005440080e440607480503503914034110707924001680c00314101c0010820540c441100e03045240106400207507100c9041014010501000700c0301c1c41c15030100340a003040d96520f8100548501c1c0076602031080c01c0340603500c03158550341040712058611070180c4c0281460320304c2c100582d98440e098103005007030b00003921f180c010404201c46424103200700c1c107840425580c4542800b0703c14481c440481000d005c0e81d4044000c07464400d0301c12513100c6001c00d9043e40035008100700ba542e4244540200400c0d140180000c0300b41100141d500c4000481200361891140859201d4803050380030759205400491001c42c684286600041001080c4600351184c14894121800010789204042c00c001c0d116090301883c1e40f41118181c089100030094cc2c0920300c00d245112415240c07500002c644d4051030348000c286036800642e0800300401500030308581d0700c0041051044c004110350944441d0090b0150b500c0800d014031048004182c1703400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 655456933 1250 655455683 655455727
    0x91e05120111031005030c0607151d0304030c0509010b0a171005040c02160906140103020c0309150d05070203090d060b0a0f0b070308010531180c030b130305 69
    0x8000a4003260400c82e824483e0821103036100e00c21041ca40800c4181818400580c21850031902d0b146040903550380c443c80c1804030284880440da80c1d0100c005894107582c07000303440c1c3d852041241e0301c07180e4a140a0298464900400780030307a02150000401d01400b0040d00c107100b01d01d80743c19108401e05000500b5261005260305011401548001003c1c0c84912070b00c06c440340c0c1907000d4076803118800480c103050803440d03100f01950352601000308810305c180325014500f00d00910b40941d884030900b00041c45c502075000d076907900500060780134883c1c0c411980244901039406101b07200075a6184800d1741c0700e000b5548459049144007600c040021030540c49000840b400400000398117845070b5001d1b59103442900003e51003840000ca01c1c080c181c0001e16180140700446195480c1c00707400c40040710441c08080c401d40401d04003c29224064055040390740032801c42d600700301a00c086030411500003403552105481c04101c1c3d601041440111051101407107802d601d0f42860009521030200b19a4602c207 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 655458183 1250 655456933 655456969
    0x60c130807030206250c0e0f070801030b0613140a060329070c02030307140c180408070201030c021009050106060809061018060503030c0607260703270b0403091e05 72
    0x4030700400040b0b06c40b81d01806060352403918001458054031001110320060122030502c4146001000000d80f414001e960000c5c0a4900c41e4a100e005140b1034043c0c0003002000041c1c2045034100114420550b00680485e40182410301d08165008003024400c6c000c1c040020030640e90b607000940c070a000d0f8030903007029480a42105d183c94003645072403983d20032030900171209070800e04e2007059920705000183c01d000f40c41001c04e4403500709540c03801c3d031921410344000e0515031500c0940140c10300030b000c036040c0040c401001b840307880d1003490400e008208c80d0082a01042003076010645010700041d00d10700c5140c801214048040c1801e0100001c2000c441180e40e410303031039640125440c0c5090015017008803014009200f241000c0c0c8000d02507066018214600940481200903d5181000c00e59080469810001044403c0001e11200c0c40d400940c041d02952000e0f011204020000900b14483c0340640e0b01c00100c0d680350041d6a540290400800c001c0362400070b424000ba03e800300700d4140c581602c4c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 655459433 1250 655458183 655458247
    0xa3012080106090806071404240806040b061b0102040e010b030412081501270b0c0706142508071a09010b0f0f180c030103031d060406110a05060c130807030206 70
    0x1407000c004003d81010415040d4003550027600b06029046500e0517004803048405101c10042c0c003010031f01a0082d045805001000c078103091000e00801e6040303078098100c0310301c680c1003507840300c2145403582d005a03011102000c0818450010034030842a4901034a8060b2041f100c200d5190011100d45508010f01a110000c00c0c820844041c140c80481c2e004010710301e880d545908484c0706440c1041461b0340b02800741300d01c0188041008101d0401c41d05003281031042c0300080c0e41400c1301a9101f02c400b44005004402c00a2104148540d141c41203514081a89680c801561055034503400d9a1030311a0140d0821440031500707295150032500b0b0141e00c440074188880c5401000300d5540c101c1c40a0f00c8850051074000011310516502500e03012030710020141003040d4042d15804100039100c1d9100d200200481c034982c14103010700500c802c1d48619048000c948071800c0180d8101420741c00100c827880c118103101400240a80045030b0344003141d07001881c290420f592290100310705011890307001810000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 655460683 1250 655459433 655459439
    0xa0c02010f1812022d090a060b12060415080705040c14070305040501170601080c07140d020102040501110609030d020f0c070906060314060a3012080106090806071404 73
    0x110540520091100400300e00d85440386005000c640361004511206040200e13442d019175500c01d0400302c006000a440f582c070301e5542c41101900411064120387c01020340000d43c1540b102c1d00d010403e00807030f011502080251a82140250b0303440440c41412425000000200994501a40a00c0329680c19003064515040468110b208942c0045000c030040f420200b802e01403541d0000f003485060a48001040060900c48000383c0000c0b0000d24040c6000e00001d0b2080030000154a088000d0071240c1c1110134040344044042c4c080e4206010707082c00031380311003440e901100340050054040c5602c203001d1403800d1540c07060003019600880d20a003245c1ca082242c050b081008104800091548903030000d041c506000f0010151030701d4452007001801000180000342d520203a42070704840c600b2442020908807103001d0100c482110821b4410150008086001d21a1011144c1107207902613548055a03a00c40101303550b6240c1c640a00c00c1d0b25031140b400245000c6c028611688960002100d284c00c29903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 655461933 1250 655460683 655460717
    0x6050916031e140709150219020d0501020304061a03010227010c02030d02011a04090510050403090b22061106071d0406060e04061a071b030812010e0c0a0c02010f 71
    0x4180902e54a2000f80c502c00c2100603640020184098450095005108584200b00030350711056119443c644800c841c29540455540a01c0a00020782c084002d54492420b03080c084002e00d000041d900320380c42180e0001042d1724041c0308540011080306410719204c5501070400d2041100c0460303c50611040014402c05070380c0800500e106400e807503001003034400f119a580c0030284d01e4108020b0141d0b080404000004001040031070b80305c098260001255912410704130b45580a981c42101d254400162121820b06100d01d540740c082280a0005c5502d40c0d5020211061000103e80c400b4641200b00400e004034800d48091401c0591158102412100c14001400f110620f900810129401000c4150142824000c0c040200b884d50030060340039640321185c48183c407031a40010070901d01441012010a0304019502c05036401014640c0c444090320200070303181ca0f0a024100041c0409000541c0401120086840c00c00c2c640c0d88411103284e0a500644200058001c2e40041c010702c5001c10030300a03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 655463183 1250 655461933 655461941
    0x102071a070c03050a060f1a040510150203090f0f090c16020301151d0103080307111015300209091c02011a09040c120201052104020406050916031e 65
    0x150061010301410f0106281000813503103d007001c419920b041154079081a82c5140c0301800e6223401351804100e80d62603c4001400460603013103a1100c1c02c114440800e10741c2d0004c040d110508041c0c64038aa034520180401000344070101005500c040080c00041003400014003410380e040ca0007010045084040d800a801d4403011440d600815040020800140c800c800c0301d250804100b01c0c2d40041e075419a250b043d01440f0040510703003403008089000c14410f10030841c000d000201c241003003200e0113202d1052402e180d101e1041d2403e02c03544190050101c841c00c6403401d0b81004080c0a42c0011105900340184944010140c5840d409900c0100441294a515118100300303954000104d0500c103400c0410000d114801131401034000c4020013000401c0c0e00040801e0350305400c0c0c0c5142c007410620049501d40301d4174810b00101d8210b0b0401030801000c940809029034401c64080c01102d8a4205002050300101c0340c0c08038540108100581c014060761055080065400c0c84105440324418601c041d2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 655464433 1250 655463183 655463189
    0x5061008210d0216050a1a06010302070b040308060f21010e0303070f030c0509041401081207020d020d081e030129030601030507030e0a0c081509120a21020a020f0106050102071a070c 80
    0x7c0d041c1c0d2200304000207400440340c1d00c4042402c04505010032a201d980c142c40000b4002418403541e0350100d80280e941300c660700c0c28650b000342101401c00400b00d00b10400c0390004480d295940c00c059103503c07250400303c00d0300e206400a586078840600300b50012009000c000703230140c0611200700a150038580b2980034003040c2c00c00f40811480c00394540703200e5078a0102a0030007600c1d50041400258016964400c3c4404625011110004200c0070b50801d03401c1407150030a61580941c01c3c2100361103080142c009107040300d071842440043c10000c1c80d0903510307c21112610300c030400010000605d0070342c06a8481d80e00203112f8500000c010000d4110140b802c843c80743c00341c1e03601d0710100701040b05a504201c0200c0c038400d9201051000c1c144820800da44a07044a1a5000050040b501880d00d9201c0d15100141c810401c42c207085200708001544003d620000f01c0340e0050086000301c2d201544140150800c5420603402003940618000d0400c05020820700f00945500e010003000021501000f01240a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 655465683 1250 655464433 655464443
    0x170d0203130515100b030a18031d060405100302031911181e010f12050a06080d0f02031605150c1c0b0d02090601050705061008210d0216050a 62
    0x180400703810040d01d07040c00010600d075504200d00400c140e034090512070328115020540020b40340d40300c941d040c0018051145040f851f060700181000c052540c04401481080010f5181c200101c08600c00e00c0824491402043d41020380303509940c10080c4039500a581c40160a10250b0b89805140d550b034003a58aa140c50030506031010800c9600031012000b01c00043c0b5040b01c2c8054071030000360369a03a5141250510074180580d65080104943c0901d00c0e60101d8103148404000a10300040d0b200c004008601540c04c40384295145226220b004503414103000c68182c00a505121144044020b1600d00705400c40307044c00b40e0440400c541c030351007108900803984101501d4030b0f66072070048685060348950045141b00d04141c0100c00310346885aa0310940e64041e030341e240c41c96490100596044c880c3d403000030224401e40080204942803011f01e40e0682340b155054855203a0340341c0c43d15512020440c5103c5080600304081040124154001c0240a2401c00e12112a8003240c903031500b441e40e583c2041d14 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 655466933 1250 655465683 655465711
    0xb19030803180c0307062601050a030201030b0a0b03090d030f0b0a0302040c110604080405120d0504050d1e0303060905061e0909010905060106030507090f0b070b0406180f110913170d0203 82
    0x241241c00340d0680c10307c00102c41c130b40c000a40c584400074948050600c8007034140b564504000d03500707454104641000e080d411413400d9072400c081c07035101ea843c0c3c1e0812041000074030b009184072480c00d440c0a1121a42d1000301407817802c6041d80c00300801000004103400c1440012034200c3c0444030184106449140038940c1640c80c2e034030746001c3c41711420303103602c007034a00d46c005001400449405c5400e40d0160368050700c80031044d00852078050741c8000d180ca400107050b494428003a04065064205000b5a03500c1907003030280761200000d01440c405202040c1820b0b500e0100d5520290800098440d0720900b018000f2941c0002c41d1111401d1040c00e030018070010340c44008006030703103810401100c028541120301800b2549403541464082c022000000c00700100d180100d03040c4101a0000c01d000e007030208035943c03209140e181103185c51841b07210032200c074068450503860a1410702d4440d44a0030041c2c03180804252a95542c40c801f030b0580d1400e4544401c01c0c130050841d490a4800b40d0722031444049000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 655468183 1250 655466933 655466957
    0x207150c0b0609070507110613080c03070918110303090406061e020a031b020a1701020405040e0f0703080703020a06061725060e030a02040f0b19030803180c030706 72
    0x622003140040c0b4050003a05004103029520750f11100b10351815800652009980450a00007a468448e07802801e82c048102d86012419400c080f034841260303070f0102c01b182e000f65540c0103000d040c0c9180c41c512914166546c030701c0c0c101240c10447e0703c1c1424000201980d140c10740c2c9400150031210150420400113520404100254250b054501c0c800403041c0020f102000080d50700410f8500301740300b00c4c00507154104210b03045441d082800300c060a902c810b0892183c00c1e80050b02c0c001e411074031030704d8455410032b007480312400f0340460410b4060000b0f8014080250943e00c0d181c0e11030703020810440851192229010224a55104a1010b010ba00f42c1107450216000116450040500c8030629004400d205002c0000b46140c0080201c076554140382101001c9200040d0405940440c069001414110844107010039070f0700045030450220303905021100c1142c0d07454102c41413800010710040003040494080307040320381ca5401089980e0100c5210001c40e002082c00c180d110380c032443c0821281c020381 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 655469433 1250 655468183 655468193
    0x1413140412080a0b030c040b06071505090c0604030b0c031e04030804110105030f040b07020f1203100f080316080d020c0616020c0913140d02150601080f0a0b010207150c 74
    0x942010f0005020301c82e04400c9000240c0314100111854840c544d01c001d0900c00f9242c4c1c1d8150740703103590008186108140c07488008800742004482003081400703101040e500b80d00c6d008064600b42e0b500841b0000081c1e5555101d00503a90020307150014143c4100c00c0550820241400302d44200e1181d40e4294240c141850400c81300404a820f590522000344204001c0700402c42c0f00561054003da400034980d00e86010503404c11000d903500301d40c07038020b0f807640c110b25001c1e0500550003002804200381c80313141e80d484100c450050038000c20744160010007445080c00c5c500b01c492a8143c0c0141021450407088089480890b404401e11142c0e80c2c011004201d881d52a82861000105080c0054890707803486030000f5411440042070668419411080c13442808841030482150701210000c8071040c40d01c240d8080d42d15180c003c1c0b04455250003800045207944107007105030140400b41d00104040c0c40f14000b42010300f06e0140454114407a801c000a40907200c0c4a05083c0c450321915a062002c0d101d00740 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 655470683 1250 655469433 655469447
    0x50105010b03010e0402014b020a150e1f0c08060303090d03110703170415170610021f0212160c0803040c03050a060608060703061413140412 62
    0x1140c50076003400d0004000c2c50007030010300740e072096091070321040d81d0200d19082c41602d01881004445102042d491000c040c15244122601a80340307000d41c0c103144400d40f0220303900c81e06400003c10509540700c032140a0b11094200685500d101001da0703c07030346062071180d04007001000c00380314015111104520500e0f0000c84440c1c012034180e020b141303001d0154012590940e02002d00074100b04c04203a01780070f048014010a4055580000040e150021007003007048640c2241c080d44000702c500344000076240e070152042c590840c0c10300f002031025960f907401b00000f01c02e8445484040d40101400ea103400c070761a140319449141c800c003005840d841480d1a880e1115001031855401448101c2003240003500075620030080e070742c001092035884d074540c03502c40c0a2070a40d50004085201e10202c00007040500c0e007080e001c2d00c2c200000c9420550f079140c0c048080d5040c40c809e0240c01503401c5230008c032500b0000441d00c080d00c060380021400c40c1001030a5040c8800c111815541c012a0f550302d40d01207540850 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 655471933 1250 655470683 655470689
    0x31606020909130507060c0201030b1c03020d0f020601031203140106030c1112090436060506040b010e060d06170102070209010608040c0909021503130209060d0c29130305010501 78
    0x5541a00d002e120394803155134000030300511080c0940387c0d094004681c425002955201d202601c6284c406071a8450154010a4021304030050701540302c02c0001a4800d11407406005c550750f0040c40c25900c0c40e03c0e582003110654202e80201520b5035039000700304020108060081160b43d40025100580c000000c0012000342003442050b0010880004882c41038001c0c0c0701e01c59401c81e800902864070829030f0500c25202c400014035610144100420800c10f61640507a16001d1142400b0569130001000200c0b2004000070740450080524200182130540c0684014040440c00061a03502d50301090500028040541d8290390001b4401045041c02a04580104114209261141043e503504c1024100c10301034219815918144138095541d0074200c511103200704a51582d407410701450315607109400d12000da009880d250701040803420010b80d4041c03159002514421b4860130400d0322404c41c10325980380c9607202800c0151a81e4042c15400519505403000003441c401441c6203441030039500164 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 655473183 1250 655471933 655471951
    0x90f0610030c1e080a0f1a0c07061a040905030702130e030f0a1403130b090c0f0d0203210d0c0c0c05040b0a0f17010f0209030d11031606020909 63
    0x34108100081a007403110090f10390b410b000103410740d07494100000e444141d40c4401d9040c85002118014050f410180304a00741c001e00040d1101e881d410110074400d0b20980b100d1644400402c2444040b0746607078402e02900c00000a2034074810307200c4c40020709440c0d141006842c55000062424114540b00044a407100076008003400306c0c169001c5a16103d025440076203007460b02c002414104644500c000400c1020f158401688a00342900e03140141d0b000d081c6c0840d1041ea094000c00c01607000002c0c202d4145500504040e1042d0440081c41800c90320100c0480c0c041c418207541004040551800c003a103044103030540c0c0d4442c5600380308981615100140c03002804904003903500880e40d50407004c400c0d640700f0f440102c2d0503225400070038161201a4042c2002460410340810003407000d00c40d04000410b480000d00000801a0003a0200c1c46044041581070f44091403802a0700c2c01500740d0492204008240d07410416080c00c4100c1e90240b0800c03c035550b03640000c03105e040d031504800d510b0f00001d4803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 655474433 1250 655473183 655473211
    0x1300f05090a11011107150305010302030c0a0305030a050702060c01110c10050603100911120106050a0506130e2a07020a080a02180a180606050f1801060c020607060203090f06 77
    0x20f038440c5411031200420040c104500d03640301e110042020000000180310480f81002c280c08103650080040c082804120f11034002c4100c11541c600c1e04012510960740c1002c081c40c80d100040d4802c0d103440d48921000c9801400030321208161440a104070b0640c0f0101d07441560740c0d155041030903800c1240b98070003604600d25000901c02035071400034502c1c103840098240090083d0b65814072410038101d90346666480807650307111201d80c4806400110480300140d401616040c2c81c0c1342000890f0044480e110480c0b48107050401036141c0e140301282d008009102d40108034200b4030000c001c4052820340c00c074507100d80010160b046041c5528148014003040025042a0750194001100700d11004802031a0825060100b8030340c2420f41c0c020a5081d161042c01280c1c0751203840d20304040c0980744141c6200d440884100c041c2c03401c01710351061141542c050700b002d090f8200794040e645100c1105003a40c10100c18001d042c00590703144002c6010f02d07a203c0c01000e40305020b071341c000d107840002070000f4008041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 655475683 1250 655474433 655474453
    0xf04050f0717040c0e04021305160807050f0d020708090d08040312110607030b03010b100201090606050904080703030f0609061d010819030c0809060406090e06030c0a0501300f0509 79
    0x2003044d0b03e07825240000301d09850364a403400011085082e0009081c1418a03100c2801500740c51f210300c07041c0c0018592102d9641d6550800d003911180140318189407000001c200784a90740000c0e40c01000300c030340b00383d1809042040c840003085188a40ba0800c550480001031b080c024032046a00c400d16030b100c94549141c44469800b141600d40001821540c05c2c1520342124a406a8003904a0605544082e140c03c81c41110340b4002406000c40c05415504140341c00404201c40c1030140c4014071031074100d0041c07860311001c5e58007100102070000314409925941c1c240440c00036014081d4034002d1010422030002a04c0b010002048500d060307118146c55448103d2240f50b0f840700002c842d00c119050b00704610b045400d810541294403665884590100300081e004c04c1c590f8000900c1003d40340300c0321000c000c0360b6856090694991540008581c40703045d200081010b50301c01c0c0700000403070103110252030f4000d81c12180701100c200c444118035141a1540c1010140c10007621035198880c159100400e003d0384 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 655476933 1250 655475683 655475693
    0x3012d030f050a12050a03060e0103050a030c03020115120302010b0406060e040f1d030a1e1425030906031802090a110c070e07171005040b0f04050f071704 68
    0x5403440024641012040d12105000c01400303241007840d000041054016003d560080481d07200c00754400200786081400301d0440003c02580381606c2d4004014480318411780c4040e05c1d45200c00500714110364840d1102060000900003007401414404003003810302c00c40349006400d460319120b04038000d91905604010a50b41314135034507020729054070005810104a0703a403601600710282c0421035400154038085040038000014100d450107681c5042c9040c0e004c051442040d68643c51010004003d0354003100c101035454020140340e006011100848a084600c48008065508098003c101403074001c010307098050040604a4004a8059401203103130f60000320601005418140f0300b6650359514185500e50400b11140001e000080303c521550752101c0c00740042040323800000061984a083c0c54a506090b5940c0c0254000480b054201d0308080501004200701303001c1a900030003078407810b481c50700c0714801d6900400b12141221074500c0d042c10b0141c88203203e9003416818070080010440410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 655478183 1250 655476933 655477019
    0x10602030c33010e011e03030f1d0d14010509070f230d050c180405031215180a0e030406020303010902030c120a29031e0a06060b0301 59
    0x45a1600450106890b120103680350825414a0a0302e01c4190400400d02e01c1e1220940360495002203600e121010325602100d040c03680c10710000700030440040301900410700a04401c0201d46000f014007030320180c0d580018030a5101c0c4441903c00313210a00b44d25010003801e00960703034441030001c0200300c4a454604865110710107803240030070f0030102102c1c43c040980000005003039904001c00182113000303141090344d102c25680000c0341c881d201c941100d03d0446400d101c2d0790702c10364100c0d01031801d1440c9507500a0103001c0083c820034209403680e00c1d90056541c0c000030029008a07400c013036030302c80c5072032036000d01220318040131025668028041000303440d0740007013103d0640c0c000340009a1292551002107603640600d101300c2c401d1100ca0800c10141d60b6040d400303030302c00c2e4100c0098002a224180304510400300c8402030300d501074002a000c0305007041d040c82040d461204940885880c1a9a40c48102c00c8640603000805049000001044800c51050640c00145402ca4240b42c06003202200c02da292 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 655479433 1250 655478183 655478203
    0x14040c020f07030f1106041d0109091a071709030702010801050a05150c10090f0b0604140109091103071401090e15010804080d0603060b040f0908040504053705010602030c 75
    0xd00144e80804000324070444000c419800703070299484030f45454414100b4170000e2544400705000e8000090300020500aa007030258101005084840c40c110101007921001400881442068200b2016443c1235070b110301d00c0786a80002941d1078504c14030005148840c107038044d80c4914168503042c461562200c2000030b12030420405541e0755000c0390803960404100b1024800c44914010322102444400c00501c1c05c00c0e88201c108910641e03031310301080116910b101003030f80c3c01c0290780014000b480c1540c0c030902d1118000c29100c0a0341c003400001a150619542019078454101c5a0312101540c1000601c40940a82d024030303213580c608200c0f80c0404040300e510540c100440c035004503052250542c00c13210116013152041c00101e44038102a8007406404586901540ca030004a150340e040c203101e14094242d004480c1480c161501c810000074000103005080c4501000c2c05c003055005e190380e40140c54220400141d20840052054102207480583c4154250b41040080100c080c0b80440c444101c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 655480683 1250 655479433 655479443
    0x706080609130515040804030b0105040c0909020d0f0e01020901090b030f1302010c120e09010512030304060203040c180c0201150509060112020415210c08040305090f04020414040c020f0703 83
    0x10740140c2080f91070454441074541d03019002009220034049500c1c01041900e00424400885990351420308c0700300d0b0203404160002400030a020300482e0059001411280791114010481010384442c940407201e010100f9940d581d4002000c1c0c8407941c10001c40070003000c44458190070342ca0680301c20841c202005081401e44003600b4001e00c01c6a0241c2c6000c002d194000c041c1140400070124042c2c0f4034041c851362035200715820000083c552404540c2144112141c0c000b07181181c46698070500a900013a1040b503c02c4804000400e1411f004401480110124900410b403010203840107070845035040c1940d291007031900c03414011381d114102d980344c1000d001c0c45c14014403c0005500e030024044c3d03400c2608007200120b181d40502d54448258860280d80030204020b640395808164100c0707190654070000300782d0310800900400e0061002d0007000b0b601502420401148100240403603005400c02e014045000702903101c6410540311301007091650b40024444021204402031f80c401e01c030300c00244 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 655481933 1250 655480683 655480711
    0x10f031a040203190602032e0303050c1c05030f0a0908070312090602040906080c0613120c050d030327020f06070503040f170d1419020f16080706080609 67
    0x7191801c12542c50401e0f0a011130610302019490040003035031054801c015110164000074440d240801d94000c00015542c101000051950303809a0300c58000428081580c052003680310922580d80c44e004640d80240d80c1c480c0d40d2890070341c85031000054090310640030140707008400000545500d0440f60000d4160622240310b10104286038050b103071602c0014400c42c0003183c00030305c14245800c11420380743c00c20203845454102006200c4940682401d41c40d02e0386c49034500300000c2c1c0c07400c1101c5c0d005d103004101ba01140c945032404580344a0388520103c000950300d000d2481004004110b104029151043d017607444500354000038441c0701600c01b180c0c400e003c0042d6203003c120302002214010b1010141048001d5920404102040302c0720041801502820102c0140c0510031040a00d500300090702a90038210090310901300751840550450a610840c0417000c85801c0030016a00041944812040303454106512142041981e40c1704005009041003408007035a135007840650706c809240c003021 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 655483183 1250 655481933 655481941
    0x140711010324080313050103021317030c0304080d0e04020a0c0b06060c10020a020606191a070605090706120c050d0921021b010c02030d0c080405040c030b09010f031a 73
    0x2010307100c0c0b040350708100d04115000500ca02c800b04c0a005c9640e1116411500c40b5507540045d0241c0c1f05072083d03035101022661b4144485a1003c0e5205609480301080780e0400a80142041c030f07550054100070300c10391008811a901c9513022501c196108025601035052410760f0710040d180b03620044000302144400c4000400584030b076001c0d50214090340044810315540803210302d0096102080380070040c0601800100c0506109400d44442104440d40c044528680910b140040b0000c400c0001c99038020002c6070080b40da58010580600170410241820501d020030241400d40e040d41000401030502c130100c25030701c0d0440d060b10180d207c01c40d0045164a003515000d80804d140040c2e40e440c00304203000300d4000a50001d00030f00290382410320f2a42154400c00150350b14079180034000d41c50f40c042641c2a409174490800848014030410209044c59150400030b41a00d440c0f00d540030010395a1070261103586030104034507006218240480e4651390540d2100418500d0540092942d414110089 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 655484433 1250 655483183 655483211
    0xe0a080f180111300d0b0a050103050609041118010311031e120c0a050109051f0b0f060d1b180e06090105150f0403030503060415060f030903110a0804061407110103 72
    0x1000c41102d6800020b0303988003030b1a085c0d0010b0100d09003082c0150043c60f0702041c50b500a2207084c1c01190300801d06800c564030740d9140c0c1112801041a2500b00545045480c03c03112900c0d4444d010710300c552001c200602035101454a041a041744489042d040b46600a040c22004640d100402080081d80780e6039401c20042b6038030300103232142c0c01002d40d03180030034072400d020010070180b07601c510903003080f404107400f4000348060768010b0140a90244581c1403603038152034507400230702c07070030003060b00202c0c0e4130031070050b040d00c4400c1041040c1d020451a00c07103034503602c0b80c040b800800303483e0110061446040243c08201c030003405000b800e01400c0e020300c04840010100c0c0564961142c00c0ca07c09a645841e86002841c42d04155091800b23907080c5040804408109a010800d6821560b81da001c4044240c9048000c0e0800c007805400b40601086507918440e0140500c660141c007035181c66a680d490a0750042c5000340c82e090030f0308980e20901600000511800002c08054424a804104420381c0c03641 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 655485683 1250 655484433 655484503
    0xc0910050d020a0e040b18030414220c030c030e030310050907020a060204080d170402010e06030a1104030b150a1a03041e0309030215070c090e0a080f180111 69
    0x200d013100c0c072000c1008100480100890310030743d82100b180c81c0c1043c506020950380d0241e030003400c805a41141c992403050400004052950140349030080041040001840c104c500c8001030100103038132417141d0508641c06008503600d1801ca40011741c603610300714112040c5844c0e0f6010f040d11840000b070100d44843e1082040490054000c1011544c840e030724058290355091039207a0030049420340c900304280c0000100170a102d281c040c3c5840803011564410010264070041a8410a41d40c03a9885d6100101c800c01030400345120745900d443c1410020112042c0d001030020740703032054040090600c02211702b82035502c0a00c05c00303818607440f40c6480c907040c0b0040e481d0386841801070056451110505610007806000c8038001d072120200040941c03800a45132140c03a902528603480e4080800c1070f003105600c400c0c50906c0f81c100f95000190240d8400149501c1b05c0c0c81811245004100c880303281d445811400030003402401c2c2210406014400c003038640750801d04a4007440803410a0b14508160714035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 655486933 1250 655485683 655485689
    0x109081b042309160e06122401060e0402030906070c05120c030714010204080a1103101103100905010609032907080a0f0203040f060c03150602030a0305092d0a0b040b07020c0910050d020a 82
    0x50f00744801c0c0e030b0f9180c01010161b024803072040004e160791042f100c00c1c1410b10803640240019000f402131540c5045058a4281c504101102c0612450040c056103a9040000e4803040c050840a180e0311005410000101c807161910602c442e44100b0040101c40000502e4050740782e07100403441062054000020b0820110041406000c3e040c00c2d43e00c941c034000040114891001040200d0b240c58a9100c140b040b50310900803200030600e040c1c4144042240400030508191034039644415401e980040400e55100583d00c0f0f001098a0005003d2488407600070000c5452118404500310b00d465101d0244a04101c200501815510f00400310100c0c070903009084058080e80b4904101551140020f580c1d82c000504000007078505400700d03040c002e0100323204d50141d242200e62250100b85c01e103000201d80311080c05020600c2a5074ec00d000040d000c1c4000ca10540c062039241e101880d1a44001e030a0120500c03c65204e501114208088070812086500a507001a250680842e000784003140c120a8650 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 655488183 1250 655486933 655486963
    0x60902090c09030f16140310060807030302150f01062111190309080a0305180f07050a091517010906050f040606050109081b042309160e0612 62
    0x4000350300800380014000c01d42d06030f00311110101e1003100740762505000d01154030b107001010020480701121101c52a4100310042c2943c044005000314102100e80b00e501224041e00303c3c00c4104145901401182003080c129804a50249415110156800c0c814021070041c0214000004003101d5010580e1046001d02d010401c5240c40e180034604154204c6070345ca1214414181010316450b1090180008007a80118954144070120b0015005440003d20a07c3c20040742c42d0403001c82038042068540c65815503002e80503030b90401b02803280844070ba0300b02c049070f43e040540400c12020000d80702c07000c039264a40c0d61080b100000c940c05002d00912100900303464104410300c0041c00c1115420b9001d0380c442e2804001d030343d03510780054030143c0070740c810503040e9000f4400d00402469070210742800c401000344002084400d203c143c03485451b504110384941c0c00d600c010441131040070004540f90010380d403041030040d032520000300100d84d40181510300402401d00340a6002c5010840d581c840c2d0018 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 655489433 1250 655488183 655488199
    0x703020c06040606090513030206060d020117040b040b161e0203090a060e041b1e0e0909030a090b19140706090f061803050304020f0d212613060902 65
    0x509040d00074013070701c0c0601c0600620740301c0400c1901900c001030b114a25810f0b000350001c1c0c0d640c5420080180580002079040c40400f5017140d00c24010796003040d12881c8541c480100c103080600300340e1025a0014804a0b002032000304030703c04250410140c140a401c5401d2140b0f140c03540840490640c01032166050304890683c0d000700c2c0040c2c02c02400000031304140c038204a1544062101c0818000102030840850358008510094440c004100b51008245040c500c1c0316401c1040843c1c080c2c10100d4800f03603c0e0308049508034200e07901007502801084000e103a1400c00c0d0498120022401100810f0800e00441118428145401109445030350303070072980c204528002402c009032080307000d0108803141fa1420500c000c0c3d06480e5228443c989405684550640d980c44c1c0c2400650020641102c0d4005d550400c003c00147c51100201ca41740c030322055400c01d40950280c0a02200c16071890344841100b02400c9500060f030910800368426a94884c0300313500c0c0d01e1401c041005040300e8201941004207 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 655490683 1250 655489433 655489441
    0x612071403010f0207030509090c120705031f06050306060a030608061e1311060f280e0108040209070e15071a22030819020412050c03071503050703020c06 68
    0x1508149404a08260024052400c3d1442d82e4000c0307201c0c090005004c20030920010003a07003442e0316119030040203407034400d01c0c07c5981b9480d070f80d400030111500c00016000000b01b1201d240c0c041044020701c130003041d032140410300f800005040b0b0300000305182e0043c04003140d04101544280c1081000703080080030741c0d0007400d110741e2034842030100707010001135030300314001196011b01c820485e690003580116410b0f000440d11030402000c3d6025881032420200144175000c0e0b05030030406000c0b5029481c1c0720782801740d00f4900c009403c14008000700c2d418807414004000c0540c45040300309500c0041c501d0300ca2481c940e004005480440b81c0c0c08610010400415070804014058982e1081249048811200b658030041b40500703456a010020250b1740c01400d03403800080c0903941c00c603040780140808107140800030744003800302d811507405031603a050851b02e0031060160622610845070019806060700600749909034001c04509801501010340d50700c009190140f2a50684410b0500f400681d1001d045c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 655491933 1250 655490683 655490699
    0x71502070e160311130603021c1505030c030d081518010902030906011a0703080c040504140f060402070c14010507020d03030c030e031e180405090a0b0a140f061207 72
    0x10500300b06010910b88204580c000080e08203450405680180390300021307081030806c5010b074210103864109a150f489842c15800c040d0f0291490058052282d41e007118600401c2510f0241000c480038060b0b0003e04103044043d60060800781d021581000e030b400d01009207004501019403001100d2021224a000415907c80035002035000303200d050308503000d03640c80700040c401800f0a200b100c501ca1804100140019004031035460384140c0e61400d642c1440d40d41c4000c02c0c290ac004c00048060700b03035080b080040c9400d10340d811507001001501e08505001c3d00e5558440c0c1051f032130042c403114082c6610983d82685c4a40c00321501c65901034004100400c162034040e000d0519403240001183c245040f015030314070000140e60074652184646420804000084007155110001c0d404000d580015054540e4485000e4140181c02820040104008034180502c40c280090051032210b420310b80358040303039412010801d8002c1d404000d080c2d45520740e42c00090090004030706024060084074400a0411 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 655493183 1250 655491933 655491961
    0x9090c010c050a02152d121b030702010605040608190f0501090f141b010207260f030909070c050606090a09060c0f350601020a0813140d0302071502070e 67
    0x100e604101c6906c80320411490f4100c20b6959010600d0010081c0007045044015110803030304a0100400000c041803585200078155004071169030241c0e444080410060801f840b502000b4160f20000c0c0c007a25210f6110f8600e00722007284044c14880d0140242002d0000070f6200c6521240d0108106030094240e107008007180e405900401454000c10036110203000070943ca640486030140d002d04806418030320480700f5040b03004002c090348000d000000c02143d0041100500c07450501000310303114030441040004413140100740c9400c2005015415000681c000341540e04044d00b240c2107401c5503a0880102c0041c0750790f441c080c2100b414040c92030b80d1183c000911004d402029600c0d9940400228056141c4070310303103421a0058454401c1a61460284c001d56540000e01407040e02c0c1020740c2e54132000749071740110081e0380103690322100c00c2000d800d41007003040414405807000040a07c06403006074450100388030b80d039030078003883c8d0b941c111a41c82403141c50f006c1d2074102d004600c81d06222000c0f150903 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 655494433 1250 655493183 655493197
    0x3070c02090108010203060904061815021e040b0d02030411190303030f0908220e04052506020c0f01090803121b132c0a0507020c09090c010c050a0215 66
    0x6950030744000700d00200e040c001c0304d21a1601814071003040c0ca40c1d2b500ca070002c1c0041c5058480180d402d0100e032002030141e131000140c0700e420300409a0bc5160035080e00b40c0c05000408403180c0e40790108410018104444107543f01014400c4005860796618101409000004070a50340d020040140031f4011500d817100d071005490013642c0400090a019200e0750883c1d062040140a0200a00204d4504c03400076070034500e218035401481003042e0b6140c0c4d107100d15090549044426402482101408a4204030101d240380071b450104c1c025180b600101946500403181504d008035010f010004469015100a00c010b148000443c0c0e43c40705809030101700b007901031320641c150348138805032009000310090954950604001110807550b26091441d1070300404240d03484101406003000a0a20407451038051186034200c030045514581101c000381070244c42d0030624419082602071001080b00021081c400340400e00344005840f01d5030a2292402c1c3c03500e01d0095200d0083c150b40180741105401400c84 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 655495683 1250 655494433 655494439
    0x3c02090a03030f27050d020d0b04030203070605070e010801290c030706050a140115110106175107052101030201020a020418050a050d020706020c1c1703070c02 70
    0x211003002810b40c030b900b0144c1c2124031105806070424450b515191005e1140a40f00800d5420202c06640d5a250b280004a4045d00942c10204034081440220301540d580040d00c0d24101071303281020341c0041c00c1d03640c06004403e0f0030a5000710440366050495007801c1d070100a0000c0c40d440c0d408428140d9681d50040d14202c60041c1048045150034801c0d004802d0f40c500d030035810309150307802c1500700c00c4041c40c403034440b004002845040741d000c0f0b602841868080c0c0728120700b0198042060400510301450800342c0012040c90f400b07558400950080b040312400c1144c90080c0c190075545403260309180d01402d0700c0d00c001091100b48640a6080b000500c6450103180016a200b0401c90410009103070912019000d60001d03100130340145426800401004004070318200088590340f0307214641065403000b101d05500001e8401d081d1038040005074020203031403000300070898905010440c4200c2c4d10604140c040d0001c03c6010030064010a5001c3c806e02c48076140751a89400807000704560116002030780 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 655496933 1250 655495683 655495697
    0x61d06090102130605180103050907030f0c03110f030721200103050711100f020705100c0305060a1a0a05040b1603030614031911030304090b043c02090a03030f 70
    0x1106402601918400c21400106e40700446100c0c005402501c401445804035000300c40021000803581c0e40002c88480c000e2010704035540c01c51a02c145088142c5900c10302c580c00000f0707907500756500002c002c81550541c4002c2d00b400c00302000c0e104807009003044004c0c5900405d4111001c9043c810b0448691094241c0e810f00090300c0d4100b0544d00049440c41404040c0c10001242e85007002c0307a0820030307140850600051811107203031202820f04050700c0100d015a901c500d0240e40865040c042d20340c0203c4101e0303c90103498544400c0071000705000700d05000c0c040021403060981d601400c00e4900400c01d9003c03944c1c2d1031100c8407001d114130f400e084085020a00c0c00801080d01040360940a0142001400030000c4110a0407941c00b4200300000c115000b070011150401035031800d00c0980020701d00480f005c03d00100080400040e25191020b403014035030a601c1809909030380c1c1c0007203941942061013603000013421161030f0020380f0030481da03d500f01f4041c1d24004205580000080c54041c441d0703403011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 655498183 1250 655496933 655496939
    0xa0305061011061824040614060d02040b04090609050f120301030b070c15060b090405090a0f122a02011d130b040b1825020a061d0609010213 62
    0x28400c01416a0b8240340e55210100080d00508040458507150303078580210b51202c201449100031198120000e030401000c043c0900003000b9082c007658140600d41d00c4030008903d01800850301c0c010740454044e1240f41c41d0010081552102e50080d05c00d10341000d01800301d8001810721542e60386894160030309030b200f505105046c425988081e40d060303036400071b10f01945803039140b0200d50152441c001980d445d0003075401a00342408500c29180140b054001ea0768035070800c40304000840340010000020390700303e030880328001450707070000100c0140c0c03010705070b40c0625200c0c40448070b481050128060b10400c0c104010f001d14214480d0140c4d03507100340e960b0041c100b00354001c3d10418039011111500141b40d541c12181d500c860380c10003c50303850f018000003920100c0100150060341d015040650000e141e0081c0659680c100902003140c045048920309041b001c2c1c5d400130340d104076568000d04155030791446c2c4401da0b0a50b4400300f000c000041c04490340f0f82010310034103000b03610007905903203102c00d254000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 655499433 1250 655498183 655498187
    0xf030c030b1c0209090a0b072a05010b13060f0b071401060909020f03030a080601050309120d1a06070807020105090d0b09010e06070c03020a0f080f0a0c0204060e04080304150e030a03050610 83
    0x1b13050829840384c1d80c0140c0b48c4981000307a850352040480b601d0684600d2000d281046412080d011030b080c0a40000705003d18448107100c0c3c07180e502028150307240d0800100f4002d14401c0245481100c2c0c10018640c0d8032240390030006801e92038000c20440c254200f00001032868001d0300190142030088481c0c21001a0020403d075581c82452143c0c4046134600000071510340c000c001960340080c00740e068450050403200c0c80a4a41c0c81710340341c140100c3e0344448080700400300c080f10a030461819140549031402645808181e409000402810040c001810040c1500e80707115042c440e55100415080c00d050005c10180078004040402d50070780302c1c1c00700081c04513100f26041061180c058001d012458055201c03402000010841a02d4041e4101305015100341e4520050062143c1c686d07401c840041d031072040006540e6950f103c1d1003220318503030500c0082098481104c2c0c11030b50003c0119148021402c041003d04080e50009640f4080824000b28182e01500700a10500c02143c914907030490303035441 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 655500683 1250 655499433 655499443
    0x14070627080f030c070f1401030504080c0f0604052e090c030c032f010c0f02040e0601030c0e0a11030a09051f0b0a09020301080c1e06040f061b02010f030c030b1c020909 74
    0x6411070f0314841f90030b170211540240d0010f9002800341080c1e0b032420220b901c0183c988032070082e840403180c0c45002040188202800b15000c414200d0f41224001240c2160344020002c06022000549075140024000c000116031603030003d55000c410f103d03400d5079030f080c14413172540c1040d240d0403140801d03005641e01c2010f0b03503090f00e01c465058407021b9450101d922040c100321001d841c03c80c1c00a580d030200c400b99103820080c5900a510a2000c90b09980c1000c110300c01015001c0c051743c4406062000700c00749401e10307405503940140e5a00d0700040c5116582481ca04d401e00c90300d440b20031425051442c0128804540050760594010707140c00703400c91303602c10386503003244001d01c91200c2c5c6410940003030060385800014180c400c2404140c0f040140380c002c001810550040d8085250190742c0c1c913041040e0303034000034243e0100c000503030300b40c040d103006400103082400d441001c1410580da903c0c0c01d120150103548202d141c010081c01d0200c80c4601403040b020301045516040e0b2040c4021000500c0307070240014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 655501933 1250 655500683 655500689
    0x903101e09170f0f030c0a020f07080c060a02160e090c09040804270501081e0a030906080a110309280312150305010e070314070627080f030c070f 64
    0x20070450b8114007400d02c0039150000c2002180806040000510070b40c041009507002e1110b01c00c0e0b4680d1201100c04c00b920b04880c0d00095011604294010003900310b000c581004d0301034003070b50169601c0607070030000c905040c81c801000c50181c0d2404004169a8000221580b10b10000d00c11103100c040f81c402000030312501228000c4c25060100000e01c00c1300341600082088c504400e00c40384121668a0070801664002d810600040c0d202c1c40c0c5a03130b500c403c0c00c0e50015514800c0f10141ca10031085480041403ca0b044c01400180064040880e800c0349043d0f02a5440c0c81c0c021210b1030306c0c2c7c20b0000e2641d03219012094510043c681070308454a002c02107045180e003040d8103440d44202c00927545604000f800e0305070740e4040000d02006002000c01d00038000c001841c0c4140d405000f00c0d03800c5140c10b0010f12801c3c10940d81e40ea0000105000040d0030004503403d1100d428013074030122028244401c0f8040f019044403401d4050305100710301d031520010161865403554000d41d840c0c2c2d501c072401d8001c034940a00c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 655503183 1250 655501933 655501943
    0x506060a08072d23100c020d03050c0123010e0708130c09091a0702010e0c010e0409120206070f1b030342080a051c02030903101e09 58
    0x2080800403d20798610b0351455592010600075409401c1070481030403100c40c0c0c000201d4460030207042c80410080e0880e40c10035807003203407090090454828020400710100400078002c601d0034181206141c000d0b415950761030100402803140d0740320200c4d680b00e0702041b4204071801c01540400030407440c803c8034013513125000e00d80d00c40915680703591521422000d8000d0650b400c03500d5a02c08210110380d40a4410903a00070b4103800d074100031407048950366450007020a000c5900d4801000c407012008141650000b01c01d10b0320b070501d80e8641c0001801018000350050080c0103400840102e2034012a00038031a50142d211510234a042180541b0041d50040802002c00001e100540010b07001e54880740300e00304240184024101c1c00100c00b0940c09645101108400c82045c0400c3c201e40030a2014020b08806c00141c00f66040e9a50b880747c5d22146034000c05903004464000c903844610070001d0b1800014000c1c110364000c4120841c0c000144509025003002c003429060302c0070003c90034001e45110310380c82 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 655504433 1250 655503183 655503193
    0xf02040f1802040b091b07030507080f0a0e090603100b04020c0102030f0711071508070e100e0406090b240f07030305040308010824150604030614100b090f010e090f040506060a08 78
    0x8895030703c086ea40004811400d020041c0a00400314100d40d0240901c848074100440d40c644c1c1c00380000c0c0001e10b00c0c026051192814008020258a001c100c400640d11885400301c5d5050310f00c0005070107405500500e96207036101000700400080003c0d800c601510711525040d1044108018043d19400140605040c20b01c0c00300640d00c0c42071041800540c41140c40c6004081e4141100024031030100081448000803846407802c0114580751103404010074105c20204058008400401c01c0c4c0781c880c403604c40507241058030404c00061444215100c412503410325070741d1040c6615020780240410365061f00014020b50002c070303661100040a1843c048502e400003810b140700c2865610000380106041c07480c2c0041c0e0400b1a280c1c079404083d2002d10300c00c40011544285040c510100f00c5002001c046032510070790802c1280c0b05003c0111000e1050030341d101011454501e0050f02c3c4401c94900c00782e00903c0440030419074001e42200d15025a101d0720645020b5152542000001c8580d40a441456001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 655505683 1250 655504433 655504471
    0x10f03050a030e0f0405041a16200c0315090d030501060e0d030201110a0206090d080c0409020a0c0f1203060501020309180907080f1b060a08040f02040f1802040b09 72
    0x182d080b142c81e00310f0080010080400d4600420261030302500d0449050004030428075000306c02000d9250300040d00c1d085078007008003c0078000d004861402980510520030410280800000e103c3c20810210180454524850303030030070700c0b000380b0044650325181e005001d007407095607119001e80f504172161552007250100d004030030000705441f6400c088007599a10541000003603080c00180203500429005090a460140c61042c1011002c000f88020004080b00300000071007000c4c1030b2400e50b1043e40006845564840e003d0b16090848440070b04603607202001d00c002c00c241080150780c040d10f160f406004499991006980ea80114002e0b590300444d07001c100078080c2032001c2c10b0365110360b207141104c914980c0d44036a0303030900c42c60261180e07041d004000d071034030a4029541089406035081d0b89580ca809200034008080b03281c0600300038400314216040e0400c0d5a11504501d0a0221554040120750101c40b200c5014206414040340100e0800c07800142d149880610280309244108000c81e041030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 655506933 1250 655505683 655505687
    0x106050403060b030705030106080109110a05010c0807110904080418060b04090b0105070206070b01050a1a0304080c03090a0e01080d050f030a1e020309010507110f0c0402160611040e010f03050a03 86
    0xf20480c0c01d01c3c0c00d4451440300042940d001d004d03110080c80c241000113105407150031b1100d0400349076101d07a8080c41100b03008110999000440404003604451005d8498000c0c0c40d102500b8000c00c0300c0f45a201051101b0303c0240003a9034014030441c2d0b00001d1010b084091260018142c90551180c8200c5c1b903030500081011651300d40002c1c01000301403400c5131401c4000d600103607060704994001d07142d00e16a14018081414800101000391002d8207480510b6400006250701c81c0c480180000c0484d070780400d41c00b00310002082514102c410003445402c005071544031720f0000400034400c6c2c0060f48142c1c245021328074094070031079040c1402060a40d255a0b100c2507a80090252483c400300303003004000c0d81c078070802d240c0d101840c0a02003480000c1140e081180c0c008100300100160f50007550000d203944502460001240384e05800152000350710385446480244115000b06000360083e410003040b000c0c1185200014019101c003410548016602d943c0011064003a07400001d205602c4400080b01080c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 655508183 1250 655506933 655506941
    0x10b0d031b05030301121e0503030a0b0d050d02010f060909210504120b064e0322060e0901060c0807020d14012f0f04030c170114010605040306 63
    0x400c01c0a6a00c01680d03540301403440d0b00903401990543c0310745584404001200603102900d15440310030000b600c403a9154151a84009064400c42c00e81c5c0383c40310003441e00c0e541100050303c4d82010686064410082d0041c1c0603004400700d4600f1103141500c04141c000003071044207030040d00030b8036000d282d0705004000c2621048850100c801d011040c400000e29020356003a40141d01d20991100c1820704240302401414844c0c2452144400c01800d000135010920707100301c01401c54100c2c0760003540e1140380400314410b2010703030007040c86020000d65540c5040640100c03aa500319020f001108544d540c110440c0d0018200403100d92142244004016144c403410f402c282d0349000b48a4145880c1c2541c0c0042c80e030204d240400c07070f15010803501c40c4603030721004c0c41a8200c106051080000920140d02d2050030040e14482a52006074041454503020004906a501075544949400c1e503150301c44030140440f41d100109810b1560034604209101700301c0c0704642d412525180c907514101030442e03071041e01030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 655509433 1250 655508183 655508207
    0x20103020c011104060f0e0a050d0b1b03101d0c1209120d1e06050328120e0a090e07150c051209010e040605180718080717010b0d03 58
    0x150748a00e203c02d0001482c40042c401040c29441b81c00007180f034445d01034103e038044407030140716107a5603400704100c2d1100b07200410340310342c442c020010035a00c09502400200400f07450100e900001b208001c00d41e03080c00310003815940c0040c082140b0820f4021100c2c1040e401700d600710300a0105101042e119403072001c00640003891272084c0d0301840b03900104c0f141c8981100601c4600740f07881c0d5040b959036525043c442003442100c11014000581080003007551005000300004410b6009842036020343c000c0641d01464591040d4182c2d105035079420001d00c16920401c0e040e1041070710071400a100746040c801e56421a0040000d4206103180521382d180403500e50f512003007032000360941600020f41c244105200705140229540e190103640d000107024a203070a941c84c0c081c2d40f038031100b80010754860650360030700d408004000741e41e96503016085405414500140c0440c0381e0305080483c2d02440810303003d040d0368078560f403010f0b124200020b070390a880348003100540100c10610f800010030720501c500c4940c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 655510683 1250 655509433 655509457
    0x280f0f0b1609140a031101030b12010209090705160209070c050f07081605060412020a030203030c0c1306030b0628080c0f01050c0d050309010915020304060c091202010302 75
    0x144800a468884104104985214018068045411a158216034040d014100f14001161111030300004910b0814003800040c000d600039a05140490f8420742181d40804800383c46551071032101c6a405001c0d4002a0b81c1c2407041c46140001260780d80300e40191501c1032007003140c0c03114200c002d0f02485289180a0030300c40410049a2481001c9081080301090046c86040200500d51816034041c0c00d04da000c00e50207401d400f281400304210750b04e21080c1c2e41030b504c2c100e05900d142c4200d48001144441f56510003505070002082a0001c040c1c081020ba20070002520513861507401d1010305403c540380780c000145901c134407202040041c248900b0040402203007180c009112215220040d20b83e0109038017000c40340d8031400d00c0b41c096040259111180385001c1c2802c1c0c0c1000301c440b05184c0c076602c070504000200803012000451a01d001d401c80c21009401a044c03d2401c0400071007540030754800c440a444641c289010403030b0070381c031488440302101d6614400007402500d43d80110040e5220085081c3c0f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 655511933 1250 655510683 655510703
    0x9050408090d0803090114010602250f08030703080c25031202040909050f01110406181d07031505030309040902010c060509342123280f 60
    0x1c5649620850141c03036030007000e0f0a40c80b407610501032400d544108148011086015004100080c0c00103900841000820340c00d0010b00105d0001c0009403805920408503001040c4000a400320040010400c6e90b000746d60302451650784068960942c0f040303043c000e010324034001000507110309818401030114480c1c50600c0e0030803c05900101660481d420955480350384414003010070104101d1390340c5001e040f00080c004503005e100035003850b00aa12400051141c0c1903111040001a0101c1c0c102a02150004001750310407030242420300d0400321403010109107859100995452640300200480700020000c513f070005036824000a440c41e000100c3c14030510149120014011380205881404082d0040840c0c45030b840326840c07000c403000c1c910108500c10f10700d42c800340260000d4420a6494008040c078071640c0d07100078486038099008010340b180038a40032030401e18041d035804410faa640d441c22034030f990400242a1402c43c00c0c1e2060110000b01c001c3e25080000c005401c0014090f001e503450403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 655513183 1250 655511933 655511947
    0x904020702130504050616021c0e03030705010c0206101706060105090a090e062706010e060a033e010c0221120a09090b09040f1401020a0c050c0303031009050408 71
    0xb009541c810355045a407504801e0801c854a0401603075028800818401001920400b06e01a05d51a00d188011000c00031458032109140c0c8040003104c0070507a001c00208001140040c0007510703050f003918400f0540307840d000d0029007502002141d00d0481d11100250109071aa400103441c0c84d404034103601e8004d103e4000c00941e0710107a1141070b21841d00800a00b4240c504400400302d10425040e03042800c440301e1003400e41e428000541c8505442ca0a0134044094032150000b401440c010703070000b80200540050f440306107020312940c1d1080740d9100e21540b000d96400b03500040101040f0a2180000d004c6580349005d4500008540c1d04000d50050545407076030110700b15420a00f0520502c201c1950010341111015400540c0714002c00d07400d0410440310008030006a06894060005030a9441404c18081408041c040c0500c01400c0d507802103556060260015000301c003648030030b4542d03000c2c808501302e481c02c5c08011a882640c1e03c140140d0038a081440c040c000307041c060003d0350980401d101e2a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 655514433 1250 655513183 655513219
    0x60f0807211803030506041d0d1d090a0b0907031e09080408070e0708010e0f0f07022505040509030a0504050d030903080f1803011a040b010c020d031e080405030904020702 75
    0xb409540a6a800b098a00c1c29200388400da41c2d850306501720002507500015850346000c07510000c1c0c0d0345540791201c1d450000181c0301e81c024150340f950b9940003a500c4240041c14407668001900820b054541c0590703070b0f071106801e808a5540140135200c03c80380300103000380030105922041c1c0d1b06114101143c185529051030340d1821059400216040c20510f00380302e402d82c0c0128441c1d0050014800284d11031a0030402220030130406854925404680000304070306078028403825030080b075038116040b036540e461081050894810701c80d440c001d42c03418000c600e40c000e010040383c525000075100c180c07030b280c549404c2c4500107d04c02020790800404140100000e41064000c015901c400102c2c1d5460304905400007401d40c00303d280340d61082c0c0c941300c02c111490414040490340003004035000101c01020360016100070021351030003944080c040404104043d0481a500002110401140d2902c1e8070030409640f100800e41e805023959205110300c080a2030282c0081c010948082c01401402812480c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 655515683 1250 655514433 655514471
    0x309090e060106120902030c010818060c0307030c020106030b0f0603030409060e160c050d0e0f03070b07050607020a0b19060e0a0c080705130504050c160c060f080721 73
    0x2414400d4111000410100b64082402d1380040a4080100031940c1c040d400640d8540e607610003d810b200b0120700040c0400910381441e1107101c803103410340384c1a00e0f02c0b00314000c56900031a80080030902e03016000c0010f61052113a4001d89034096900c0c543c98a070005000302c2040000c010356494402004049421029800341c0e40041c140d00c00540c2d014140b0fa500300700c8105c1020303089800c005010501d00040b46000641c4072005c102070506222064844001c5041c080e150b404031780e014485d8010014003440510020102140600249c0d80c16480304c0070201d03241c070002036002d46580000030118404102ca141520303074041041e80001083c80c6d480c0b40c0d9001d0010112340d000c01c0c182c3d4400051001c80c0e003144185a00002600e001483e2035884c650110b52240c187c010b5030b0103660f40e0400a01181014003c5404a21a15100b00c514403000d00d4401c00c40741e07660080800044210815045080c001d0040c2405200fa40d2104202403940745003600c103090035003604d04002c1d030b1221107414202c190091 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 655516933 1250 655515683 655515701
    0x4030f022106070f1106072318040510030c03060c0306170c091008120f09040207140706050304150e015c13030c0b180d0b060d030909 59
    0x8041d00c154030f01500068080d490039141d203000e001c203014400c14294400f050103a405009810009070781c9070849810304940308441d03103080c0c42280005007030203104c800c15503111409008503402e11441d81c8074a001c40200d4004d120081c00b40151400a00010b00d958000100084880ca400100315580303a03060001600601c0d201e4050790000b48107900cac0342c02c000b00030942c000b0f59013440490b80c6262002c8980d4501440d02001c03040d400105030302021494240840d004801e00800664990849080000345942c900c50307280301510854000003282c40c021010303030b03109640108800303002c3d050751051400038110142084449568841080c4003801c41011030501d11601042080c880740408003006a01700c0c02e0100d50b440b04502c1c48503c0c07000e1002001011440c40c21481d00c0381c0c5990084840d145428843c1c0c0000340360400411001c1040328500010f85400c5000902130744c850742c2e0907000c3c45607040c15600054451076030a0b00140c51801c00380c6010384020312a281032803e0640e04c01e20401142d2000c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 655518183 1250 655516933 655516999
    0x20d02040918121d03030711040c0206012102060c16080f0a02060a0503060f0409061a030f030405120304090608150105060a143001080115060f080a090206220b07050304030f02 77
    0x80f0403100c02717007031a2081400f042c0c01350000302503950500700401c0c40c400a01105c2144025228042c0c01151240015074500680001c105d0b2090003504424988038052401041564814880c51a204400020729103107420340240089150054032141126680e01c01000190054000070054400b81c8803403103040423450103018000341141d14440f10040e00c0076440a802c2c86a0300c18840d01d100014088216802c0751811107003515090711110b1198194041c5134001e541c0c00d458080300181d0140c1c04107050001d8030703034116001c3e80c51303032240100041409a10310100c0010740107510ba8000380c1c6000700418078410f21172004110814105410354010709060205658008020010058007400f40101084104140c054404040c01d1240082c40a610205400c0070443d01c0f00105040c0365203544200d12807038028240c6d61362650450240103c075441814110090141464005680d145a4040e40c1e100341c0d004000d907207420f20795142d40780300c4c0308042810303030380320640049848008a505031510140842e00c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 655519433 1250 655518183 655518203
    0x8040f050604052b090e150901030c1a28031b12050606041a09040902060f0a0e04110403020114040e0907030b0705180904050f01020d02040918121d030307 68
    0x4010080a054912401e203880b25001d130b002c2001c8560030401d580300f55454905094119070714401d114803080c02c8800c071150890504000030080c0005480c403802520407180b640505602980a0780515104825a0407408450449940d03c580e0a414240c07000d042c203032801052054541804440b03401040e8480c90110b00d8104180030800c4040c01403e503c920121049402d180c03130b0101802c10000580080400b201000030800f00c6a0781e107500040c5c90f9170b005400e040d100ea4070310140411551003492500c010591100c0d960200e443c050090f4042c2c02d1800007a141450720b95401511811000da08070358200006000c0403031090742545145210316403d8000300003251031810a0071341880040d01c5801081400c024000117400103002c0c0301464002616801110b540301d0602600340f0b000b68001b00582d5000141d11050f6203041d40290098600240c4c0821024200e54900b204450701e40c1d400070042d1001310052240d083c016001c80111301d07011b01080c904001d14100107800c652255500701c1d101158 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 655520683 1250 655519433 655519453
    0x603050f033f0c041d06030606102304050d03020102090a060504060903080f070605070513081606050c0f030d0213091e0c02030f03012408070f08040f05060405 70
    0x140500880060b01820041c200c01c10394450701c640d015100196002c2040050030124000110500440340104200782901c81103082801d0500102141075615038800d22500b408a05145030442280038818400c0d00c60094a24550500f05203480a041008001007401d0000041c65141c415111500c80d200b50300061341e5079030010400c490704c10a41c202d801006030600c0300f0f0024035000000c0c10243c940006440d0b031144c200c0088c040c418403070140000d00050a11040c0224103130094060051240d042400510300303038403405010782c6c40000c28603c100310200070740d04000041c010001131a59041d460181c8881040d2a094170b4659444402c5da14900d960011764001d921480d00c0740140581440c141c1030108541102c47c15603c0944180c400c445d40d1764070004448014020011140c032018103c88940e00c0b903a45401c0304d13082e559030309080c0e00c1312111640015030062203031800921584142d2200103078114000012124154000d10444841601c0c9065102007041004450b20651042d0024154490 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 655521933 1250 655520683 655520707
    0x80c21010501080f13030309170d0911150313030e100210060909020303091e3109120e060f070605090106170705041e050f0114030607090501080402040603050f03 71
    0x3e001480942c43c0c00c00c0c00140901c102e1007040b6512120b804d8500803a04542ea420000d80921981c240590b1280300081d13007080e1400c068001000c0c95015804030864512120184141200c082d000e52168000401c00614220342d00c91800340810b00074642240c006108001040748203004007802400369003c150401000b00c6c80380110341c040d08902400b40b00070001035011940e68014013172018483e0300010b055240c1c040002c8d148000c1100700411135003888130b0f000000a80305080b0700c14580007080c60450b03040d81400e2402080e51035940180714080150480c141211803030108601c0c00d61041003040f1042607282c1c8100a429081d0003910001420b0070001e8155007101c5040e130004041000c0741e1204150702e800810403604407102501c0c081090b107540d44001c010300c9043d42468070420300d400d061220000e4036250f0300e416502c42a101120400c4c2c07590805580b20b00440301d460024030b01c00814019035206010307940d0414409800070aa0a881c2e1b5541c03410507074810900701c8198000710344140901 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 655523183 1250 655521933 655521947
    0x708031f09140c030a0b090109021e03010b1207050903030d1d060103050607030e0a1209050907050408031b240601090b03100521100c030506060306030d080c21010501 73
    0x4144540100b1034800d110450079200b0310002d100103054100800081e00c9440d075a0084404c070071009141d04069030311984060001d40145d004540440301c1d0301809402d101214003143d050ba07001800c5141030680d88240b126048800410140c2003100038801c8002c40d4804002500d20f48108081c040382e0016850000b101081081180c544168071110040000c10404120b2a401c48a40c2c900803e10f118440030140c0341040c840401031442098598a0064070341c816004c074192402260807100541360746078200d5044c007981c05603842e0350f0003c0021002900c0ca03040c8298074045007406880d160340700a405075408070202c0c05505c42c003c1e030520410903250380c8005c2c113001a000c5c4028460460400c2409821941890b015582c050301420100c04810190025003034030b5440e06204031a4854071082e92000504001030802011078100750200310305103030070010b5a01c201005002402c0400c54090120b814810142c0140c24500c01009180d80c4094a004044400c401992011402d5450a03000510769 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 655524433 1250 655523183 655523189
    0x204020c0a1728081521060109050609041208040309120b06040f140109091a010f0e0618041b080106080325030c0b0a020f0a1229060d020708031f 64
    0x40c580e01c00084030440d00050b02d160005900240c0000c6403800350041607840c0021101c41c292017400b011b40319062980000d1540c107956500f801800329031580b50a020300800c09a500405160403810000080e91181c560107a00c40d0180c60161001c6a44030b40020204607558420303030b0510960820804903040c03600614951500c5d074502088001c07424001954014010700039480e400c0c0c1c0301c0c4505811300c0b03074007140c55100c00309144010449594a502030010140d580c80713110501141000010100c0c940701d8402c80c2c100050026084c440c1e503039980c50142080034418014025445000080b4414800344540805000500c00641d0350300030340c040d00c8120400350003e00c0c1411f2000c48800300001c2d4449a0403000e01c2d4000110307080d580f14500032101070300452034030008261022500c00146a4408003c401083c0e0091040080882130004101c4c500b250840c461880b1203c0304c0582000c2c1490401000040c00c0307900014100f00b20350b1b03034851040d407060310300d038480c1100480707100c094003c00c06040d401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 655525683 1250 655524433 655524487
    0x6060e180d0504060c0209061203160506011a04060509030a05011503060b1f260f041e11010c021305010306051b0a0c0f1505040302062d040204020c0a17 67
    0x201407405600820901d84101c0c02802401c03021f02280c0e040c3ca85100310110401c0c0320054a441c0d52031030a4081440743c6004043d5124454000002501d4562107040c0713041d0f100c00b50142d46001c4c01d101c2c099415a0102d6041034240c400d510758000440c000f0b01c152400d038a044070b030019099266041c110300303640b200a07209204800055500c02c100700005851480a561800d28441039110719885074001420315000005604c5d1003070810290803005407003d80f06511800c111343c51083c080c4000f80480b0001580203014000d1344d0300e13850103513018001066804d4801824030821240f0303505904140e49080c2c4c411a0b480c0c3d1650144000441603548200501019000c0581070140b809401020821400d80183c0f03407004107100081400083c9412000e1050481020701050400d898001d6584a00311038070000d0008000508042c80314110344201071521071041c0c80f8940d00d4030303002c010081d030101400b40218030804520074001022210036a00407030285d00750035100d00001c0c44481102e82c3c80c400d2460 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 655526933 1250 655525683 655525687
    0x30203100e0702030f03091c080403090302010e1504090b0a06021b1c0503030403081801060303021e070312180b092101020c01062304090201140706060e180d05 70
    0x246454006405040720000c1d1003401460b12003000683c1540305550070000d80c030100108002e0b10000c0001c4141c00340485031740540c10145042c400700c0b070008041e03400400041039050108055880b03440079540302003005002c0311200101102401c8140d201da40300d540c0c2d242c1c031203a00e4000b070314000e40c5010040c0b09600241c61a0302c410982210f5110740707617590714400c02850110207249003850700740044896029044070b0b524109810040c083c1038003207480b050310b0220308403d1440500180500070469905030000c001c030300d000c4800300060034410b40580d18541b207800d2001001c286030411420000c912600c443c181c40c408040e03c444d00d80c0d00c507041480302d0641000500c0b9152548604c4030101004e0780000c488a400c0b6008070303400fa00c203041c8440c41c070f5800c060002c20160501e0081c1314100d0408580b85c0c0e05554410140010380b480f550300a4040b44481c070002c002200142e00070700340d141c0b02e15400a80391362501c000156100c800c0d1a41440320361442c088109103001085003865082c42410400c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 655528183 1250 655526933 655526941
    0xb160903020102060115030f020708030417040f12051c0906121103060d11150921060105090a020706060f060201290121020714061305031218070b19030203 68
    0x40d40c3d07a14181b041092564508002440f01c3d480799101e50b8851100303c0043d991590036081c40101c5420544040d10043d104d2802688a18100f208903421a0300c81e001a040035840c20070044c2c0c10f9401c5100a0700d0354000d040d400c8100302c42d41c0c0c0b1550b000390000d0b140d401c03109003070420050039420240c0b03a201c00e513841c260003900e111524209590703110004039a5200c44000b1380c9808880c0c00514924280c01240080c42451550400340160506420680d5140c440081180010642058807048a222504500014003290915003041540a1800b850140ca027000c41e540342002c9a003035034400346010881c510107000a6038203028402042103000860840f54032000e85240c00290881d0425040c000c100e41e21040500c2d0548803000c1c82144160119241c0c412424240688922203802c06594041c0d40300213913464044030000788803548c012004500380110762000810040010301170042c1d00501d0103e102c11418100f0800c009041400365030f0b0381711407112580c0a11b41d04003948540c02c0c140140104 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 655529433 1250 655528183 655528187
    0x506040803190206070e1216080106080d18030209070c170301030605150a0e060a09051807050315011e0b07060e0c010c0b0a02030709080a0f050c0d030e0405061c0b1609030201 77
    0x480c106d034104550260030000d4410059181c40807103010007850031490900040e01c1328066101d6402c0b030350310500b580e60000d8002021120140c05128492440302d04c2d80d030074009820300a240c00e03405060707400e1040d404825610b80b8000802018800150510008014405c0051a014840e009010140c14241d07003050b000c000381c00d440b918000e2401480c0d0076000644c299440da1524001030211000410480c281440034070784600c540034503c10070f481900c40001c9c0509002400081d00000281c00c802142d0800c40900c550b0302e0000200c1170100c001c140c0101c0c0c0004c040c1c00905e000340c45000e00044130f4405554440c10041006011414804400017800202c2c20303009110303a0040d0803150059880d590039109461619003504654058450701c4850402c00910048482e5191b006400300c0d01000c0d0440c04101608440d000010001040c0322070a6841d4109904800c0e04181d0060010000b5003682c03031040c039400640101524400c2c085400d0200498100400e403c0d4070380700b854192045400c507000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 655530683 1250 655529433 655529447
    0x51c0305010506030403080901020f041d0f070203030708150411090108010b0a0225080a03080403080a060f051309061a040b0d02030c12071a030f07091a0d06050604080319020607 78
    0x18047c4051030000400340b08081d4121074a000494200580762511482c0c41a801c0010303c1c0000380341584580800c4c40c501c2c50200c0f07144192416030055103140e503400c81c22030350901c1c0030b80415040307420800032400355500c42c042c4d11840102c0305005a110b9440000050018106920900d0070142c1003000c41211980480c5075207076204440c000b010003030ba41c00ea1114803102e45500c4005e040c0119584601016804010a4080c1b4043e0b074500c500c0e52660341912044480f80e204294a5401020041169003015115428407000c020b40004122003180c031550252240585000005814100862910b01d440e04c00d0308044081505c44501500d06039000c269200741180d00c90384101040c10180c1d0f088002004400081c042d5030107800e0b9110310001424801e074000b52808881c80d90840001398100d88103900c00811a613000d1040d400c3c034034a103800b40301c082c1e0103800e034a0029611440049603d458800c000c000410783c0c5801151b44044105008110300320381501c200454121030f051024083d48859 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 655531933 1250 655530683 655530691
    0x2031e010b1516020f030d0201140f0708040312021902064f0503040909060f090302060115230d0e030703050d0f0b1c050712030804140f0a051c030501050603 69
    0xa011010f280c076000103903031200003122a0741d061044400c400081c40d41074210750490040e01e45082002d4441004104259000f02c82c244000364103c1c0014010921402c44080d811081c04001403400002d4503d0f25a40c10100c081600560312a40600c01d2800010500c9040c1000c09a21400f524146a092518042c249071817628031443c4913041c243c060101058406d001503021040303031f1342c1d80c2e65072000c1805440b40b05130a85607140781203001e42d1480050b0140d224095415805041ea60f03003085841e00c1e100060701c854604010703104400701c0c00b000c12021303243c0c10004212074081d00c03640c1110100050741d489540b00312480c0c209020784c0c13002030f030010255400f00040100c046008403840481d54010000b106540d0f0f8042c0c220306503400781070710b003800500c2054090b0701641c1880d5107840e031130617074a504103c000340000e00e00720004020410300c560210003100c0207401e0f1542ca00000c404545070034800c4605460750340190501a8121900038200c0520351041c1c1800d00c90740d85080009909400020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 655533183 1250 655531933 655531957
    0xb0904020702010215010906090b090108210405220e0f0307061e02030f060307050a080c0402070c32101b020a05120c01020f0606030607110a02031e010b15 68
    0x40780034800c41e8000c1c400d4000b079503150402c00b0380c1e941e50f60320000c0c040c00207407040114a9251819250701400d060101c18180c030000c5004020201c0034128250504840b4200314862034001d1001080d00d9884c000ea4941c0c0c801c00d41202e004226402c4215011188a0484a48154081d05041c285010040259034095420035000100030b010707240c5030f030111620400034060301c502c00001c001607000f50b20002c0c0c0c0034100a0301141e210940f94414009010131342d010344a200d42c0300301440b02842c5883d0f00102051880340c1c0a40c00d01e150340300883c6040d10325000ba00c0301c9018900d00d00045001040f610103c850904540191030300410103c0034003034004c0602100001c04d000100c00342552299040d900042c00b0203003940c1000c100440125844100041000e4018002c50251a49910001451030f024030300050190000e526000da01303650030102c5c062104401e004200b10700001d130307400344418140840340f040401000e080c0b40c24424211808600304a102d20038180c110600d800c034003400c0e104002402 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 655534433 1250 655533183 655533187
    0xd02040315020909190906050f1603060305061801022502090f0c0712032415020c18040203070b070803040204061514090105131418041a070509061809060103060b090402 74
    0x88026000c0c06e440c46024051604102c14040025000c02d44a4420020758582c0889902e541c181141038884510003d48154003000110b0000e42c6198440d01d003100002000601d011803250041e4005c805201306000ea01002c020000103500b0300100300c9034080d01500c9203004d14039190300402024028004003410840c603401801c42c28a010b903004082030421401e6a4541083d21090071203450101c0c042c000f01c2d00300440c20b00c0071440c0005030440807040010040c1085000445c0d045006210050042c0c0c0d06100b921800a50801da4800900115010300703001e0f039a074034150062200351807a60b4089540089c6000303110b81c40701d5118100c20107100c0010105580c03425501c004858a010b91801d40a1555002c20300251f00d80302403005c45400d20342610103010b100a0343e290314007180c2c01201c0207000e50490402140032211080920b95006401d810014280080c0401040c4a0f80161420071105030340540f11142601c1c0840900303500000c2440d040c00894140b01407071a6a020308500e0300d0040d900 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 655535683 1250 655534433 655534471
    0x1050913060f0624030f1a060901031404140d0903152c0102040e01081614010306120f06060816061121120c1801081b0d02040315020909 60
    0x79641016000740820301850281d644411030f03030144200b004d003d140101b807400010761780c000c81e0740c040c40341d10040d14441d003071040d000310081c00925400108080e04042c0e40300004500c10488110040c00340b402036407410b856814041060b032900880444c54800c0c0803030039108000040c0c0d150511400351815850104402c00d0b00524284100505102076800460303810b10340b04040f4055003d0b10482c1e0b01621003c4031a66030310036a5450300014514108007144813002880b404c1a034a2000c90343d4007062400190503686c0300c15500e20341020032030031104100128100d105010b1140a014041d19203840942841c0300d05105500c02c0901e144605014010500383c2c548003a5414003001d6040079040b80d171018a4002120300f0720281e840700c01103040c11541400400c551030b0303003101030310541c042c2400c50a60740140340c00190340c940302c010000a9a00300181100c02c540b200718024266860400c48050703142c1d8107615040b9000c910b00141409540d105104449c4240c0d00c001c0620f4100015000c00082c00030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 655536933 1250 655535683 655535711
    0xa0b061309020604080307110a140d03090b030a020a0305240d0201020f01020a17090f060a0b0d1407050103061409040b060d06061202011103190e01020703020306011d0105091306 78
    0x8401e0060361122000c2400524007401200600415210710264010b05080a0422110301403501440301032042003e0481010300b00141c0f10f680c00d90080c24150308042d660090301540b03510403242e001d810b58012031219003081d0907000301d54000344030410700c842c0204c032210740322210046031040f40c5c403458031020305a0559009102d50581d08101200039592003890203405000c40b1111071400d24814901c000003040600c01003102802c000320b9101030310664940c843d450024041aa01480c0d1105600e05000c0c005000c9100b600784c640b00442c09000c0c804c3c5400005400c444a5601c403074902641e195020403541d0302e280d441c41e030255224002d4142a121040810ba024000400c0117050030310741040801d910b00c0c8100c2001e04280b00342c0c2d94200c240f40a0701407070780307901542941c0450905800c0b4091429401142039251208041c030444080c159650000b88c075016003030f48121601158100c24825866002c070810380942020341d00301045041c50100081211019080036202c1540c40c00c0c0307166024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 655538183 1250 655536933 655536941
    0x1302040e04060e0c0303070f1b1508070e01030603030e0907020a020d05060604050a020c0c010c020303160804090507180b0a12050a0c080a0605280b0c0615030a0b0613 73
    0x4240d400300d0941074645803601e03100901c500b40507101c07144141401c1440600c2d002049902c0a0b40c05424043c0c05c0003c0e66500e40c6421110700d8010110a003402e0100345400081400303844d500ca00d64809003c0e041000000d0246c0d000d0700107007410182005018400b19802c0351a00c140345c82c0c00d461440540c5e1760a402241000c1185000a50040c41c41400c082440300001300c041c080c00d8100c4080009417541c50101c000c03882450020700c0d450b002624180d04947c02001030804250010f42501d2829007941d400000006c1030306411641c0c220701143c248585502407141d0b41d405507072424038010b0680000c80c20b1210070130300e01c12811078680009190185500c1001c4054401003252810301840c101020100d02910442c030b40040024078400006d09021224003c0303a044610203010210503942160500c0c40d81c107251503640b07040207840000003070050ba00d03000178070310f2061580c05454181005244a281040c011443d24400e07480091003402180d054503000b40c01a004a55005d0785410150000c2e02038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 655539433 1250 655538183 655538189
    0xc06052d1e01150201060b09012001060b0d0c02070812040b0307030b0d08070b060a1404020a030908041e08010606050f09120a12031103090606040e15090a02012c130204 74
    0xd014030764000540c14508070f103002c070162040d400a0104540395040c90700c00d0300440440d10300140c1200c01e00000c800340301104100c91081c25001040d503d8840050b058164811f10401c00c2c03480e074503608802015410b1000c20007410410010740310b64440382820340e41c180a01c0c0a56844e0b140c000000c14102400303076014001c0384002410440b04e01d21310b42050b51150300042015039648030b01c07100090711450710400903c10340c0c0c038107844100c004080c101480000d40240c102e49040c182da4072409808a00c184014100a107514800903291844220303140e8002c250307543c00401241c1c18240b05010864020741031b628403800c1c00440903201c0c0c04010005541c520040c0411801c3e000e401032400602030714802d0440c00e1101924144000803001468a682d84401c50740140a90040c40c0071411a2800e03810001a01021108542070550b4107180e600201206442d02c0c02ca40d8054900075045507000032004542c801c42c112070394000d50f24103011150b05402c2c00710303a42c480d20551303d2036803085051380d06440103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 655540683 1250 655539433 655539481
    0x4060203180a06150506070201090e1306090c09060e150d0213090528020307090c17131505011d18030f031503030403020d0f020a0504020a0c06052d 65
    0x654119801c01d00004e202941012040d040710070f03008901400c0041c00c0300d51550381a91182125841e010004480c8207000d0311490502c2501c0d400e00011a0450103856080b90240d41c401c03441c1450800c403102142c034298080c180007001081086521030100a0b15400143c041c2d42c04481440e80348002508003041c0c1644044140c6031140307000501600098245105a41c40c500c000540700d46080d803030355041e040c2c00080d071603070001000307000e2400c85170070100030a80141030224004a00c0c9050444501086400e682820701810034402400b0011112011460321481c042010b035040c060f002131624090205081541d0b00c04003c0350760079030783c0c0141602621400c010b40c0c1e16200c8105801c08268015200d4441c03819840f0352105481c5400700849088a500400605401e6501c2e17440c2c00030803440d000b003607034803602e207120004040d295400100507031103d82d55043c1000401c3c0c0340c0710049450182002815402081c61501801040b017034100c60203914034654005a503518128806110304501c0d00300c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 655541933 1250 655540683 655540693
    0x9050a0204050c0d2f0c0307080c060708010605160308061503090c031c090e0709050d030c060f0b090105061803120301061d03030414011101090803090d0302120406020318 75
    0xc02d80f2400000343c220082811824000000390214081403017111420007501d80031442c0201048144020040001c40c483d0f0040da070402c9138945841003160070140f400a00d5400100c00c00100d16403103503201d8090705042c00e0050511644030001818441010001400d10103608085450355403110341503894004001a42daa480c60700781da40302e40758090050102d02910422011800c03c45107180c1034807410b611940d41e1082e141c608801d4208800c0007800c404103100200d02c01007000d440b01c800d032824240c045e8075445084081c80c13074282d08481e550351507260b03180c1c580315400c0c02696038116010304456080341d500f9103610340260740003181410201040d50601c55840d2044450039140055030403a0229190036909605610f400c804022005030010341c0341e0000c00c13062201560703003a0039840350740c4189040407e05400b400154210703070403a181601c40c3c410120410010325420020305030f42c0f030007030315040d0f0400138441070b004c80014002d40018801354000c07001680703070305580040010a041034400c60b9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 655543183 1250 655541933 655541941
    0x30906050c1b010e030a08060117010e07080a090b060f01030b04092306040c050d0c09020d290120010b0a0e0a06090b0d060903030e030408010204080105100b03010909050a020405 78
    0x3141948400445103281151925040b0711000c188200d01c00c21300c450b40594a00000c0303060844043c400240402e0504c210300d1040745450700084e1015000c0e00f00707802911000d007005003001e0940f6600801d00b4464500b05014000081c190303014a07500102e060b11200c100000003001a0007600e454001141c2162404401c08180700d8100c4030850950880f00d000749000764003240705a100e403011907000c1e00100b00c1316010846030074000402644240074008400c441c5459007030b0f8106aa200c1c40e801500c0300d031610341d5050101da41d48103030502d103d01c0400100f090190710340042c0124400e00340c0880d48400c07610b04d5450a01080d048220f000d10700411a2800e603480380c140c858801b0041d07849100e0740c0c0c07500c038010035100c0d00303441450b480020040455548004964400c00505903104044080503103c0d040d96410103c208090400380c48100c1c005a182c5061040781400c40b079000b0003070307154004010000c000c0505400c08590541d03640310b0b804100503103d42000b600e000180100250002d15140400c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 655544433 1250 655543183 655543201
    0x3080612010e150c0906270406030534090f020c0a03051b010504030c0b130b0903040501170705040b0c030c060a06030501200901180b0f1306020a08070209040303090605 74
    0x1100b00a403002803d010607150480c0e4941c01e802002142a0031000412150308010764480800d0f08105000c5490142c83c6208000301e819507c2c0d550013100c00d64805012002804400c420350994a07103040b580b041c1c2091004107203422000d03980b0031595000d68038110300040c100780d42c040341c4540d990703081100c43c024071503d4028450f45c02060041054105240e010032207000c103010707560082d5056074403100d1005280d22240400c2c800035000100210780d104d000c10000d0711070b0700003e00c0703140040043c6442e80d190100141510034140301e41088611502d0400180d660080291801e44102a01440e110405034441c54510301c504c00482555100340c104001207070a182c1c20200540c4e12400081c01000708a180c130041c19117802900450300d62052103120300c1075128015002c2100180f590350010760380d85030448030580c2c0c051a15515030b0000020b00c18403038071903140325034001c1219100800d0612019120380c0349900070140024410a200030109003814072131341214203019040700701044541000108 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 655545683 1250 655544433 655544443
    0x5070902042607060c030806010e0409060608011104080a0803060d060627021606020c01060b070602071209030f0219081e010c0e15030405120307020309010305010b030c0703080612010e 81
    0x3140c0200c041c80340b56000e9007404141e0200312005a21007009003207030340d9419141e90500038035260401204006440a6980e9405a17141c100e0003000001001d504000009003541c0d01c8400151564034200010003608900184110040d501f0403c000e803280c44803400100c0d907801c900c001500c03282c285034011039120342031841d40300710881880707928072051070014500044c0c0c024803143c16151403030181c078000400e0581d0000c1c42c04111410001a40300d849291003078940e040107000347e6000d075011410320108102d007801840150300e1400c029142e245036545000c959140024000d020380c00800300d8500703032880061484080c140e407609036401d441c5000c0201c4424046160000b007150700b0b00551038003c0b4000c241002c20801c1c017070018034280c80c0f00640d0900652015104031414400d1307503031002000035a030b4055402104c49601a50385c50030b100c0b00040035688183c200754600e00b401c109000d21a5242011580c1407981814801090b40d0b4010014101d61600400c499407542010010708001c040890 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 655546933 1250 655545683 655545719
    0x604050c0102070603140a090c080d0c0213051b070206040320010201110a05041406090411070c0b0906090d05120a050a200a080c10060b07150b01080703090507090204 73
    0x802c480c0260fa460100300c06032000079101c6c0d51100ca400700480c0718107080d504402441d41c0100b40064030b035980c2d004c01a141200d403808000000b03510b0000c1300d08501c0c04044030384403406031800034809401c0c2a4498100d614011100300c4081e40001500411501c48070300340c038000e5400c60741c0f002c80a20409461203000001e02e032114019444c101c2a0328065114205450a00c03200c0d0b500c05003400c1c10b01c4071000490f00b810024036480501071003027500541d11401070003a0708004c000f2030385d254140c40c640a12040f00341d41046404620074400e80289407561000c0e184401c208440141c0b01214600f0001d00b030080070303000300c644003800184078084071b80c0080007000162619914182450a21035100d4040505111000d4454126003210400301d02d0382c0d00a4500281c070b40c3e040e50b400c40b01d00130403041103403500d6110f8420b902000c02c0c52030600c401d464a154901c08110340505c14540d0140009040120042018091681c0d03020342000340305c010803030b01000c1d10704118110744d1252070310400642200c03210 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 655548183 1250 655546933 655546937
    0x603060213091b02060106050c0703080a03021b01061220100201021c0b032d0115090608030306010e0405070c0f0516060903080301091a180406061a04090b0f030604050c01 75
    0x50496041c1e00c0c1c043d10011110100c540c09442564200001190316030300000913201c007845960b0000c80404c5698008014042032510016500e20420401c0000120043c811a0316070345000310030410314030900c41d4000c0240e48031070400b0009052240480207500c0c100901178200c42882d40c01048290154010f119603d080e0342d4040e180d142c100410b00907034000281c03950305500480d01c0d0b00380d41302101d0003206801c074501c1100715209144408660850b090520903040750f01c489007080040d44240c1c45079901600c8418061451441c041002804091150a00d68083c640d80e10000301e00c107106a08034010594001d091145100103410000c2d501d401c541441544281078200010f0094041d02c442e1080300d40c44042c250442c0c1c40d28520000820f940b407608426001c40d001c07c0216541e9064990f50703983d03080c1d00b075945141003c0c1499000c803655508030345444041ba072943c041c0040074105030f070f040341c0f80c1d480301180e052081404239030b40b42040307c400b03901031042000703110400c1800701c3c03101104902a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 655549433 1250 655548183 655548191
    0x1e0f040219090f0f18020d02220905160c11190b031501020a0b04110a180c0f0207050303040302040f06090207050a050c04150e090f070f081009020a0b0706060306021309 74
    0x1a03450304013081c0b81441085c1c0d041900c0001e80e84070501d80d03001f504040400c1341005040500603503007035113001240403030544020342c480c2041c0000100c9100322604800d685186142041a40300050400c201440c0c014250070000791103110f995640c1c900000c40e1698003003600610b107030354150080860b04140d922603000418a040480154070004141c1d4505800c2081c42c00c05032210340790b1041c070416146405030850b00076440842c60341146038070400542c1280a0018007241282c50041c21256490503178400c54009000c10026070f41c0000588080d80c0d011100001c0d14604012901d00600055016100305400070910809000703001c00d00c0c0c80503074042c800b51619020400c0402c411509250044480529110424007590748080c0e100d980c0600c19108844c0c01111170884c1c0f628009a0f079001d0400d4030381218040c082c0700005d0140c65181c0e41980001d0001050700c0e400120041c44074000c41d2000c10340800c7c3c500a1200c5904814000c5404c03e004544e180e02c003403b0169000d0050182220031424 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 655550683 1250 655549433 655549439
    0xb0a0504030c1202030703031b0807030f08061e01032c011407140f0c030c0a0b1b0715020a050415050304030f1d0f0f09241e0f040219090f 61
    0x1500c108041984e402009407000500710b40c0c007034031072406140e20403243c4a10a0741d540002041e5200070507586c0c0c02a1101c04044034210030007800c141e0000c003414010702040804a402c183e07440103180d4040c409003004140d01c211002980c2c0181000b0030940400d0500c1070603400490010f51000518035401481600030741d4840703405440e5000006085123000d0010006442c0c4010100041d02451030345205903460100800040c51600c040100e065a000e00c940c01072104040112444038069120a580b081c20400e0545500c100b221005201d40304842c0c000a005500d40d01c80c000720f5002d4010081c0340c030740168a0f00402000c940084804a010030b001408040002d0700408128600c80081c0050416480b460414000d080d03485890301134103e4030001c50308541e9518107034100e11540742c100c4108441c810000e600c841f10a14524680c0c065079a4591100c015600401c041041c0c10781030702c51000d48580c04002c94000d00c03646844840010304400f408110961288400e0202d40380055460200b070b803 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 655551933 1250 655550683 655550699
    0x4050f040506160507121e110709060812180901060507051908192327011205040305041d060102010507030c0215100302030a1515150e0a0b0a0504030c 66
    0x18807084070041482131180c000000c554144c3e180c481b07181890112582c0007110000e0030100d01500c0d205003c600c5c0b228100c03001e04002c1108000811300220306002013454041c1480d251288038146206000001641c0c01e02d074010004c00340500b00010b442c050071507035100340c024002d4010000c100c0d094002c8080c142901d511070803a204c11290411000e030703d070441440c0401c01c81500b0322114018082922031191034404810b0b8410500030604421956403101c0e4025101d0840e511500908080800c03450380010b030740e0141004041480c01b03200010f0680311401c06403070b14020780c0d12a01014503a8840d22500f0701c05421100c0c024182a002404a034880e6030066050b101101d010344010380c041407091059000c201c04c0190041c0344201500b03441d03500c0741c01080c18022881005e840e2580c06204c419807440f10381c4070f0381c2c00601000100c461160b0810071070b9407d001e004a92030301040311703084014941e5030b10620030400902c0c0303414650341e0b0303604000005005030b08144000d890080580034005540d031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 655553183 1250 655551933 655551961
    0x60809010b030a0c15030b1002161e0b07081608040501030b0315280f090201080f01030c120218040b010501120221070c0c03053d05060301090204050f040506 69
    0x941d00020404c000c50904844044800410b0130702010581c031015103604580380c840c1c2440b01903ca641c05040150204840301041550980c008070810250405041c0c180441a5407982034032960140d031175542c0507074145403c40d4006c3c40401c50308000d01001c05410002424010070440700286c8040c4260200c0c241003640f140f00c482020303030741e003603110001500d50f520580d400c0150369450140320000002c0c280c60101103e42001281c0c0c680f0766034018040956030080d207400d03800404c903c002e003015030641d62481203518191041c24081081408080115a102c021040c0a1101400141e18501c0c2c2030806610b031103001c5c421103012483e002d0120443c86214021101500e6441200d075141024010070003076603001c018011010050402c9a40001641c510304100056002d40d005040010b5031410209031614a10800307024030f882c80c4070880c0c80500b401007458205024210020702503a4a401103405400d0000d0000d503ca403412080221141c00003241900ac0c078001c074112503081c1d81d4004054412 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 655554433 1250 655553183 655553203
    0x70213020324010c050f010504030e03070b1215180402040c05071110050c061e01140d030806040b060403030309050d050c1b0d151d010203010b0d021b07060809010b03 73
    0x2207444400320318802c14040c6400c241c407818501086056485d44495042100d00120b10400e40d441b4014041495801100040400740407009401d00c03a242c2a9050054403a100c011949414008001003c6003080b40e403103001c0399005000708045401040c04a041c010b002c640407840b40d8603003114140002c0c407840c15203420541c03011980b407038400e00034100140f4040b08400740301040030030403500e21300c640e0a100890148910f084032844926090b9544070400300140c100a048088103c1640710b00d43c0d5030b69000c0c002c44c2e0903050407041a112900401e01419040100d81d82201c0001000020580e0590113100700c01c0c01401074404003045101c048400d0700c2440400100f40c2c1c0445d440e41882041c8481410360200000c0000074480e4059554094001200541c1c00d8520359520006207560ba10f0001d065141c1d811034001c5141d5810056041e00501440460204169001c64000d64420100e13501219000700c1c3c0c000c4640e803655802c4c0c02050107004651401d80355090000303000860800003074070f0600e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 655555683 1250 655554433 655554451
    0x1203010b07200d08090f0d0b010e070503071d2e170609010608070315170f0114160909050a0c27090903020309091630110705120702130203 61
    0x190090f10b032034006040c2c00400145070320140501c1d1200a0741c0e51011807026252084218800541c980142e01c1c902880041142062003002c00402c841c05900031040880700daa007550040c0d0303810350035000c503d980e40084144102442c4184403101580380e50f0030980004501940c0d04c030445100c240b040b100c2c002041e1341d41e03900061000011311900b806416800e612183c7c03450001803202050110b22003215056204c1c2c0142c1040d10b01562503c4021f00400d505500948e0007401840c0c0c0e00c05440709071440007400b03060a008a0001450442e1084085100811203a001400300341031100e072103001010400c2e03000c804101508107030380041c01d00b0250b4071000700b20340082c020b03100e1414911402910402504400711700080000b4400c41d0b581c918190b0040d5215501213038544245000500001280242c00c0481c55640d00180c0c11034041901c156103a0512034404201c190800880f900380c1d015820009140d4050040301f0300386d81d1040d8001d050420300071a10f51556600040640c1c049100507595140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 655556933 1250 655555683 655555699
    0x306080c1e01030b1c0b161d041e021b01150e07030c09031b03020f030f0a1221020c0d081e060f0a06080604051605030106030e1203010b0720 62
    0x720742c06580500d50503400500a580300c00101c943c1c00f401182d03044412185c4004d201d003440407035403c2650103c2502c580e81044400000c1e402d0120b4555024401c0440c4200e46800c00d81580c0b070b8108280d4041c4d5210b0043c00c0d0f45034003080002200300030b42d46004882641c42c0540b40c100d0030070b00e418136a0441d50640003c511580303841401302d000d045c81c907101e0700c00d100b0209000000110803040c10404100d8000c08058818210300c100101140ba04481c140b003544a88198500c24401040444d00107a100240140340305881340700390b591005883c001144003c1c02d000410309828079400a01161a401d407c1c1c50284480007400e44603100e0030b0380d0b560038910401c00c8a10360041c4c0000d41940140009211204080756480006c04040443c2c0062001800c0c4400303108040c20300e13000e2984c201180c81d10b140303020780c48908002c0150005100700402c050700c1d0002000a01e0b400c0c0b22210040305902c0017a82d80c0c4d0f843d1004110f15502c03100d07007140c0c500a8140040c07501100d94a60fa4142c6000828102d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 655558183 1250 655556933 655556989
    0x201e03040b0708150a0806040c140303040b070f12020d08131122050a0603030801050a0b1e130311090f01081f020f0a0e130903120207210306080c 64
    0x40d0783c05401458030840b80c0400441038490340d22410490002e0007500010821880c1c540b034a04600602030f4400d2421142c0c11310f41035110383d404400d4400341c0d200b0304000c54540388241480000030444400103400396a0000011006030b03404103640c0d107800381e039846808168aa074845585603041103c0d000d8220b04900840038507910f00640301c09020304030052056013071110300203e041152420740e601654690344200070010141c2000f016401884220b80b002d00d600e2400711a4102440303031529664034045000d0b11000303c100c080050f51400d6000340010f00000741c982c54040069080d0f0403840e07200300005000601d00025058520341a03c0c082405031281c2c80032894024241003010549130400740e020700405040903c0d02d0040e115800b0160b442c951011300c2c0409100c50040b10848001c0401c0c01d01221a01007504044012107007500600016542c03889414440124900805007051400c40c14910640c0903500d030308203000f0b942c003450940700c2e000d2350a000c100c0c558440e01284240002486410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 655559433 1250 655558183 655558187
    0x91505030f1f0c18080c01110a0803010b0f070b040c053309010c20040c02060f040f020d0803090109140c0904020d06021902030a02010f050c0319201e03040b07 70
    0x1c0e181c0482504141c244d1226503680c00c0c22954030b6800c0060560720852a400d6507680c0403030460500d900303400240c040071205458142c0b180c401405044030354100094a98840f441c2e06088038251508103a401604c0d003401d1410400c0210319106480c03003a071001051348410000401c4050340b142c4101c0d2203081c80003a042c1c01d405c107030b003021001906002e050001c1d84e0110300c61a000701c101c10810b10b1841818003581c000c010486d071400f1079000856200100700100c944409030066002508129409444d00181c030014002c10713410080141004004024040840b6054206860007807040184048044d0101d2199540b8000f80d101d03a54000d2800c0d000ca0058107010000d01c16080c02042c0c0589025100c1c4040d80e2440d03820407400c00103910021303001182e181d081c801c81c1501000310109000f49c0c00d103103800540c03d0101500c40d00d06030840b100c200803183c002c0c0c0c2c4015204000d164283c1045280d203c0070200e0391b0003800071600403104000e040543c25420400300c034411a0302a500a2141e1696982 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 655560683 1250 655559433 655559441
    0x30f09170d08091014060a0b0703050a112b201506120a080c0708071503021606060635040b07021f020c19120309020a091505030f1f 58
    0x201c1018000da034412112070866010342144840c583c54171340014284981888410001540711101183e4180b16400009601c0700454558254601c0c0108070302401b01047c40c2004414600380a681155055888955460080c1410780c107060740c40e001c0d81075a40c80d520055029808100c581160403034480d03000894a60042c1c60380001d005403020ba024445000c038103103040c81602040c1c400d100c0226108211039410007013034001d0240360b80501105442e19070f5007014903d074000718409068003c07c030800c1245030902ea01c256540c00050a00901740d4603080508080d03400c80802c0c5007907110700b000540c03407444210049583c0c01940c1c20314455030785075141d00d83c003413402600b03c8045001d600c00001c42c000c02501c9102e4140c0344580c006a0780c14422034040c2c54501c02514803401d0b40d500144620100d80701c4c0d00104100f0b030301410045000001440020700c40501e64000881043c5442c020102c0030911280500c00d80c0c41c16003c03140600c080100b0703a55550108891003c40d40c80020591140c07800c2031704 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 655561933 1250 655560683 655560691
    0x120115030b0321070b0112050d090602060402060903101517013b0105270a02010c0b0c04050405130b060d08180f0306090d03050c16060c020f0a030f09170d08 69
    0x10384141840000e54172404008002e030b1080d01c05a007034440c9841803004c1072200c454540c8850402c414407603e07054019488009c01400644100c40114881c03035140c405114240c030a0b204040100007020314000740b8243c09601d0f028510f481c03c2500c03019508858140304140549104000400d0720f1001c00c1d2240d1401618104043e08a90325034240e02601a001d02070305006a0000d83c03c0c0c2101c00c01a005c02c680c2200c074076184403195201080e507101503600310701c41694050304000300f8607040d0389440210001317104036400743e80c0081c584070400240b509080d81d040202e0b44a40c1c01039007291941010040741c11403284018020078810042c5101c00016440e400829042c040d000624817480c2d14000790500b2011105000e90ba0005ea0140181c2c1c0e5042c03003800ea014082c80036107410100480c000701c03016204510700a01349603a420316004d1690003009020000c003402011564400f0052400074a031084480110004c00c07800b420101d03c6045c42c0850780aa08010001003200e0454400126541c5101034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 655563183 1250 655561933 655561993
    0x308090d0c0f031a1509060405100f03050307150b100e040f0606030e1e0309010309211e0518130b120313120201270b120115030b03 58
    0x5000001c00001d490240402107000343c0c1d03100f04407004d01c204120280d800820a011320301046038612007941e1580c0000740c0007030060314006400e540309844060044540d030440d1200d0700c0300c01d50000030484004024440c12384038050107035030580510f444006480302c5403221603016135140c042c50a0244a0601d51005000c0108040762200110a28000320344154010100080c0c49545200d80d00d4010081807000d0b03083c10800190101007100c0144d128040c400c03009040503240c100e408280090414030244290400700c04458119030030340080d020039000d45115100c0301c2d40c02400316020380100d0a4408201d800101d41c5c844851103020040c4c0c11007911440620145d650b080410151694235818001010b00002182c3d29203090211290f800c445a1115099034010003813000140da200011802c10940a50099962540b520341000e01080d1500450544400480d140e44030303080c2d2608140c121205200704403515461014114241ca00014040d50507a00c816a03100300000340d502a81640c0c0400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 655564433 1250 655563183 655563203
    0x100b090f04030c0f0b072a051e0f0318010207060f02070303120e0105070906030b09010f0b030601140304080301051203270402040f090207230c010f050d0f0c0212040308090d 76
    0x941c0e0b4400001744c0644800e4006078241c1020084005214013100840d000744481050030700c540da40700c1c0d42e12000710318000c40d0041c01b01c04810403841c0811218041110041c1030f00d0712001e1450303188030a801c03c081442e0062241e203200207140b5014034129030320409594040c0400e00e0564409032049192500c0e000c01031699060b201d102c0340c41c284500c9008600c107558a03000c4900d0140000c0a6410f96502903110302c0031a401082003e05009001007190b40c8105d8194a070341d190001a00e092106030f106035061a030000411042120001c015410303607504840c0108202003c5464075560f00508a250305207c44081100c8000e81075a11824480440104017614183d210300440001803a1640180345183d00400d40b80100306017900e0b0400c00c941c440e503027880400254113015507181c40d030440441c144000d00704000c041d02c0c440c8040314040f080d0300d14184080311610f038490004240d176207a030500601079070030b100032441850400c5604480d04003c41c40d0038034a0b0441000340c0b0103182c1c08200e51001803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 655565683 1250 655564433 655564463
    0x30e1c020616020d030806130e0303060d08041d011a0403230c030304030c0e061507061a0619020106080609100506030705181009060f1520100b090f04030c 68
    0x1340c500100d154502c03d940341011341c01d041c000c2c01402c81c207905c0700c4084207040c0020340140c0c80000041d42d0340185d040303800a510800c4e508140c50184502d800c4104010007403200030900c03200c4010b4582c12641c192081b1001c0c0b800c0b03030031521024019400014a40c1e032000040d0210034603040f82040c0408071074401c2d00c0b0f098440b1400a480c580c030990044800240e906e0040060449810305542d100d4000d4440091404001040815600c287c1600900c11641c03100000c40b000080102e00154060160903540e5a1414440c4c41c0d01c8040d01e048402d00542c02d2000104801c1c00206034140641d81a00040c15a45202c4401c80090080100400c4d094840d500380014143c1c1c2d18000340c0303038002a08402c6074050504140c10044c03810a500010502810f1001c00c21220005102d810f084880303607000100075540194003125009a00c81d0301141821142c036444410f400041380d4140c028104040421583c04801d0502c021110b0884c1c010111500c0080058040b0740251141c24805108124002154074 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 655566933 1250 655565683 655565689
    0x60103150e1e090a020a030305030c041806141801090209041410030302150103020307090f09020a0801051501110d080c121510050c0601142b030e1c02061602 69
    0x380440c1e603440501c880d01c0d01c040c107940b40c2404583d00590220082c3c90030f900e542d008505086500e200040c104000040001c0604d0a024255030180a4a4800300403800e00030f10104003820032400387e859840b4010b500c070721151030403050207032050042c411051416031070005d21500075007000d9451500142c80f18050142080d0400c5514407443c06801c61805070307401e50070020700d0074004130f55024260040e0703001071000d0ba800080d10740440340c1c0b000307011a1604500403800040d001e00d410003904034140b041d02061003a01900f11521682c2000c2000b00e08079412401141c021107113140b600e0b81c98101c1a01005e10f240300700781840e40300b1104c0300c12038038042c520600100c2e58481103d0b0011031000e5241305000c10300d0f00e0380c424a10030307215107425400c0c1182e2004982d2111418401c540c5d5140c134000d0082d1042d200c009241144001d41345004003a50114422041c41c00b1034800e003100000c036000b408400900e0a1298072298122030190000d6003101e07582840956448a145054100c8005402030016070f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 655568183 1250 655566933 655566959
    0x40c09050406181508060a020901030905030a08251403070905090f04030306330212040308032707031104090f030e130209010e010c02060d15030c060906050306010315 73
    0x101c40b244600000f4034000c40c440040314540021503403203069000041066010010741c1c0e17074112461841c01030799002113100603801000c12800003042c6001c046403c414041d00601628810002c00d1105510490406450700009045130728200106812201900907000c41c02c01440d070240b40c41c18030b60841e42e00d4400103040000d04840d88441c1044090401c000c05030f15020b038000401d0302c0d100301c5404054400341d00d01108003148682c10103040a4801312400d40c401c00080041c82c0e40b110085e43d803592641041151980700300c0b000314225047e04411820781001c203011916145d00000540802815030b074600040c01045840a54000d0712400510f0220b01104003c1c0449071090710b80100d403403074142c280102c2d45525210000716510501c41d000503641c0040345a08400340034a00140c0324603091001980c41e016146515002d2845c1c0b00c00c107503d400c08804040c050700d00407001041d1203585c070720381212259070b0b82c041d200c0019001d101060309135000e038001007131842c11004500038041e100d0318109604 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 655569433 1250 655568183 655568189
    0x3030c031e071701300c0f0b0d0f11091c0209090d030e0c1f020a08130329150d0503030a0617060709140d02040e0601180e06160507140601090f02090d02040c09050406 73
    0x105200240d11071a40b01c49e84070b1000715032100382003804091344580b1203d11900850740e12901a221440750403180d125502c01824215900500e48002800c1c80401650f642201403101c034003007450007140d0031158030005001180c103000280b0040c0701e50301d049080d203510106640343c44d00b0b41c490251540d0004d01d1440c064118a441c040c1c492a01c2d07032850a104205c407440300c003c060709001818408180c010b441d26525404280d10b02c2d0440001000c0d004107001c40303640f101c090700c0c0c0d0002005000d212185a004042103c5990210180200c40050f01b11340b9100d050740c2150115074560000c000700301481c03414031440c0785e0041600d0300f42d00c1140c001c1819151000020583c41d00080014400916294a0a00404c052181c10001c9a400817401a540c83c0054105818060343d00320626000303129000301c5d0030080d80500308145010412204540c0c2d20b40031300400c0d07185814060f6458052000c0d20950700000e8000341400e000c1c0c403840e001d00000304010740c04142048020702d0040b0b02030329640182001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 655570683 1250 655569433 655569449
    0xc091b13150810050418080c030d0501080d02011d03030103110f0402070b07080a020a0c0615030f08120f130f02060c01021206040f0b0303030c031e071701300c0f 71
    0x1031490902c4185860b00540e0700028416440d11031b003011040081001c800040ba40031940c150768108400d51145980540c0301d1078214942410008682c284020503c00c81600704c1d90001d01080303003110441c07a6440c283e0442c03040f1941c018801080403482650b0480d9071094080e2041180c0c61080000c60103a9111b500c9c1502c1740c801c503c0620849076440348141d039000b10186001c508004160710300501d1459010406480d13581c480c0130030720a0314092040d1500641e8881c455112128840c6003d8240d90403800b940d48042080700001070004010b001041d11036401c8902403d8482100e40d540d14210f08410741c2030307811000620400c2440c010900c01450706400003214202c0d03905e8108204000e5440d0441e03a07140e112b0a050760b0324210389001007a65008540403511544a50742c2544405030303411104400c04420f101d420a08c4215a0414a00140c1041d0042d51400d140e03200d00d11011203400d403401d00040c038003c480d11419501c442d4802150107034820030102244503512000003016540c60f400c1303540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 655571933 1250 655570683 655570697
    0x5130c0c0f20240c0304050a030311010501050a05100c1a071701080d0f0c080d02040608240105040909020a05041d0d0216060c060f09140c091b1315 65
    0x98a000c01d0702140c00712003c82e00010500795000c3e004004414810a5a90402010451481004060007564098000501400c0c5000d80d2810700922040080507108180d511300400030803942000b0807468203540c809000703c0c29a00c030a84084480451010040e101542040c80400d4004800740d203050003064a83c0d00c4200d4807540042040440713a06a00074bd0403a0310000c0c059110039080314401d26510141e0501c0001f102260401050358071a03145203110f4141300040105a103900031500a01880c000250030340c082920098956081491444040c0490b109002c00c108680c095081140200c0c40600341c00f80c1607a071940860191000803144095450038800c0091030b1b81810040b200d0705042030300c01004003200c40c804c170070740400190003040c4c10401038035141400d00189401c100c1185841010401110003a400c141d003001e41c401d200030b2494011b44440070200e180c800301441c043c3c200c8028081500b803880b003540308640e00c1098589840c1e46c1e48100020442e24a0054168001d002d0b103401d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 655573183 1250 655571933 655571963
    0xf050a05010509130f0b030124030b0421050d06051206010e060a050604080307210e060a2006160e1302030901110c0a1a0f162f100605130c0c0f 63
    0x1825141d4910b00c01e1411031054249c0203480c4803c00c2c00c8422070b900a03103103504544a50400c14070541110180305044d03c540b14200000701d51050052114481c119001c01c2010748a6041104032442d040202e641d55004200500941c0c5150498640101d0000c04003045590b03900003083c02d0f5006644880075541011034a681032000007081c1e40a6645441c2c42c0d4005041030000103000f41c40000902da001b00340100b02034224070700a0300c044e84944880454818400d0340b050420f0380e01e8000f203902482501101c2100c01c8400c6c010390020000e400000c2032056130103100691480290001404601c440d034848071995024261900204102008c44001d440721501c2410b0070f40c6803c000d801c4d0071145410400070401c83c8103d0540c04c41d0021601000100b043c90321050440d90b0419404566001c00d48100d00300b002c03601c006a52100c0750352100d058079074100c072031492501240d07454442c40390450f010040c0c4506d00c20095228042c444001d0800d2001c4a904e0307100c8008032249140d044030100b140c4041d03d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 655574433 1250 655573183 655573189
    0x30504080c060304020a09090302010f06030f0c06080c0a08042102030d111305010810030b1611120307141c09020f101d01110d020304030c0f050a05010509130f0b 71
    0x4208854002d036071061550030107502040c3c9001c900d201b0804541d989412420816200f03420800700143d90303280a2281d0b580324141881c48010804084401200d07602c80080c549005000300b902c90517810708a03504120340355800f5642d04c00000c1c812618400700c80d6a440084036000da05099803100b43c1d00a540311000c0c090911b088520006512101d070500f400181c0034011405a02e03c02d480e02032800c5540303502c2d03c014179a500d1483d034000078000b20070901005409003441d00d440d003c04880b940d40700031080717821040948a030300031040441207910030800070703d8980c05030044202c910108901c031803070604000600d95066903490015070380580c4811f00f040643c0f070401a0100341480440d14185408030b05c00b00a0011140554100c1c4d4480c00c04909007020f81c003030b0300c4020342c82140409552544030440c10080d01e86d4041e000403102045450301c0450b0300310206092a01303956014240500c100c0c140f000648258200343c080b681d001d840d00901c0c1010240174002c64118494180c40820304000d00710070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 655575539 1106 655574433 655574443
    0x1030f0b03060a0218010e100e0a0306060b090a0608060a0e06043207021c0818010903030c080a0902060d2c060403140306090a0f02090a0303050408 65
    0x3c020000b001c035001045100741640008940c41c2c2d81d280151011040109900d8000a00f40d4640304841c0c0a186089003007280205451482c0e5520b6449a0942d4a41c0d0080302203a1008511802a42061108038015280900b800e2401e450448003090b20142c592041c010480d01040c0426451344540d409003040d0040c25000520301c0301000c0c10b008052000490000707600c1454000a00c000d0701c04120541901d0f61020035000b1480100800c441020b406000100900c150912912191009200340d00401d0300c81d4501141980440b28041d002000003400820091f04200c900c0d0010780c0d5500407500150000103000800104100c0304526a21003c200d0500c0c008600c240184010310010f100c522407880ba030b5442c0786100d088110521103001c1070f03444540004090340481d2201c103540e0404441f0282d08800141018002000940030620560094002c01c10015090094201c1481 = true := by decide +kernel

theorem cover : BRFrame.Cov 655395683 655575539 := by
  have h0 := BRFrame.cov_init 655395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 655395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 655395683 ≤ n) (h2 : n < 655575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
