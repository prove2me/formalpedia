-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3011
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:24:10.707364+00:00
-- url     : https://prove2.me/submissions/70d67397-04c8-405d-b246-0750361dfea1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 541366906 ≤ n < 541546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 541368156 1250 541366906 541366913
    0x60e13060e010b040f02130806010515090d021003140c0c0d1110110403150b131805010204091409061e070509220b0906010504090e0c100e0a09050c07 66
    0x803031000c4100c54000240002584042419a550005e240440c1c66000404d1025a02d19001c1c10b0040c10880004110940c103040c04184e1104800300102c0e400d103c0426086005c1d500c070103041c454103502820340001c5848041000e4054040364840400d40d060b80c20014260701508426903841c1d9604100904449800c00320030f440c40d65002204281034060300020003454201c07400f606920143c071a150a42d91495414000300000c10458002290360500c070800c03040b4ae4541b5104003140c5030104001650405000800d80421410345005140754000b2400040a240380c1d8085418141c01102038419030b510150751170b4441d84201c0c0c4800c000b8505c40a0701945120090307045070f00c03c6080c2001d910b081b0313030000001c48403151440342032294841001c0400b409852070140700d600110548006581d8100a000079002e8002c078010142d041340d4502600d1340900d82001100d0b01c0c1c41c00901500e10100c0301400c01010000c1d0702c51041e00500105000045500c110301c80c0030b201e1140700307800b503003450a107a4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 541369406 1250 541368156 541368161
    0x21c08120105090a09171b15180d090e0a140a0f1103060907110f0703050304060f0c0b061318080703080c180d020112020c060a06060314061908060f0a060e1306 70
    0x341c01d54506a00321182c0514400e0800802c3c20305c5110f148c5040091078611003904007210748819107596a080148481c4981e504006040c080c0c2c0c03844041010240d4621340000000c3c0643c0d40c010103144000018440c141d0b800382d00a01d464500c011040c4a10042008516000e11007a5021030304908000700148005108910186a10100c0825103d0341c10040410317034903006250304250f903140c000203010000701d50000d40c007001806260600a01c40005510b6001040c8001041d030350043c48188000008003103203034841080c0301071705082c0804040b040d040c400c030a0b41250704210003150003040030840904442c02a034000c1d220f00711150b140005114288520304405e208100c0c1841521072001c0a0880b141c0007401c2d2440012000780054502010440c00b9209070781c0c00070040c1880c0038010008240e03241c0307202d40d0200e41907a02c1051030500400600d904180c41e44200c205020306428000180f00180702c2a0107080008018440c00340c8650107840020400d4807803c4148400450400001d0307150b4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 541370656 1250 541369406 541369417
    0xa050405040303200d18240b06180306010e0108060a1808040e252708070602150c0301060903060b030705030f0706030f020a0c021c08120105090a0917 66
    0x81c600400c0c41c0846905120314a0703512041c1341e40602c000f00d0b0120101404e40305980c0700880802c0c0d540703642d14075622603610222044a8031000c01440450300100403855800500f9a590007074100740c0d40f11030745141c0c5043d26142c018050301c280501000000c40d070041c69225410390360308a0180119071140b040000040800c01441c0686094040147c000f244100300500700905004551891a00d800c12040d4101110840c0041d400e0007010074066403035a0100100060b150008800141140228042c245d8100d680d03210800034444d100000c240e5030741c00710f808000c00800c4a94100c3c1c1c1d0725040424005400f0901491b80060300d004800c101041c031680040344d02810244c00d991200d82c4410202c0e081103800075410398180d00c03120042106070ba0520999024002c0a031046003803098400d4000c0005443c0b1001a2082d96980890400704400c140c0f00c0001680c000c0800e1750700e42480480344000c00c0c0900c00c01d40703c0c1d0340c0e0310002603540f84240628404154040503030300305601d00304050181c98120 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 541371906 1250 541370656 541370663
    0x409050c09041a24031516050d05040c0e01170a1e0203011b02100b09070f05040e0a27050a02091e0c1305150a08360105060409020a05040504 62
    0x14560854404401c900201c0c041d013081c0718030788804000401361211030512010210b00a030300050410f0030004a001c0b441da0450340f0242070500c607510b0101c080701d080c098812400442c03840d2000740002c1190401145084808032601c5410307a03130f610109080d0303d0203031120388103090300b03e40744980029403111030b91080c42c2265020304400c0d40b13060300424215800d001d400340c0c45084d90b2813031072289030301009a015060aa4241030000b040d140000c20006030000d049031051100410105400c4c60040d404e44014282c80100c990542c44c2c0700b20b0a801412040200a452141c0750400030035802c1204007132002160440d008001114542e801c0c0b01c15110002d2855121005017030038280b100150b2962300780281480d003a41d5840e01101c000c1c03c64450790640c0114450f4100942c6152103c041702c00340c81c40401c003070425141542e1524491060072150340c00b107d0081400705035400c0c025a88151110001d0415002045a5a01c6100b444100c8444907006035101f1a501d40400c19860260400f0354800d21 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 541373156 1250 541371906 541371923
    0xb04020d090b0403080109090c03020f0312030702240412080603072102150a02100c2d0906030e1f15061d0102060c0d020d09020a0909060b0409050c0904 67
    0x39042026400c035890365000b21140b110078400c1c80141031740043c005016007c040d00c104103a1110796a84000c0d003103540701c02800b030750001c00d60007407599042c06029403520142e20034a54070700d0b20042c025260840b1024200903244802c864800700c00283c03060b140f08603405403c500700f58403030120a480b803400042040c0e516100d1800007142071a030907046881c44050110303c02030f180c0828030400c15405613564600d2026203007400601c42907640000e920303041100e14900001d403000082c0b001c80d0301d09034404402c84644900e01010030000038002140048030007030341d40d000d00d007600d4000c11016a141840940d2556000d804814008480030305600511900709900090300d01440118403800641d96100001142044801d8130050440c1790425207444024400b17050381f4985410484058091400c03404170090b40880c00288080c080d500004240342c0090003103041c180c0d02d041802c003821000d102140c1103428909585e219060174080c08030916840f4001d0310b00c02d4448000c0c42981032000700191180341 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 541374406 1250 541373156 541373167
    0x140613080f060a02090d140c1f141810050c06010f1502070302240d05100302030f030403030815060904050c0c0705091005091012060f06061b060c09050918010506030d120b0402 77
    0x140c800270301048600c030a02860420016144014205085141001101b608100104004803925100100104600300c54400841e100c0741d0084980d03018021149503944902d5001041051180d80d1707280032294a04000300b0050141c0000302e80742c0a03107205c002d402c14014030312075003840c1440840344080103e5138031003814480c46100d080161a07050328001300041602a0038015420305000c00889441c0361402185002d2843d0f4004142040041c9028003200000000880d02d031380314021100d00c1c190050051200703045c00c071940c0c0019071000904c00d0051080e00e00000c0c080c241001c54510a00707420a41d03282451030501031041f4134400501c02c26068124200c041404c01042c821184124040c01000481c140500804412691a0b07002181030000c1310f8000d1000f0725603032426086c1c0300d503c03200210304240c2c080700aa442c1c141a0f00710b140c0c4021903a08002c1a2020700103000234040080300203000ca9141c00d8140360301c0e00c1c00c0741c000c1000100f102d552240001c80030340100c030449901500061418 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 541375656 1250 541374406 541374409
    0x20c06040b04120207032d02090411360a090f08031b03150d080903030d05100506032e05130c0201060f0807140613080f060a02090d140c 60
    0x500300c0d01280c01a5090007440140001c60548180d08100c90004000003800c6480b002d14841a0700300c101843e0f035510082454030a01d90107044c1c0b0599020384040300504091901d100f042c101e880d003013030003003030040303920b0440a01c8080303a42d110280382040741c44410002c5800c95200c0d807004008448840d260413081c0005120048001b03a0640500301c52916800c02048070300700a03000c2c220002c92040d0900511a65403200c8801542154044551a940214500d0031010078024507400303a502d0b020200d22031b103031070300140c00803440380003d041c5240b08262079104000042c0800d03038880e0120b00d840407400e180214882c40a01d80b20320300600e0000f1159940e4002200f0300803202c1c0c00d00c603a940383c3c4620002c49409001e010003501840000d06100c0d0f040541050790703140c040c420303440c00b1410300c9800c0502d42c94420881d903c0d0041c1010000d955030b11007068607501c40e00070b4481c080920a05d4001803c0042e03503c269281c1010040185010308e226072212441c00011294104041c0142c0c1e40a5226 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 541376906 1250 541375656 541375663
    0x20114040f06050304050610030b011815090b01090902120414100c030b0f010206090c04110405061615021c0905011b09090c0e090c0a02070909060203061c050718020c 73
    0xa080319a0b982d0341e2032415180c407c0c02e0920142100340940307002c0740103200240c44e403888941518142d0034800304540d84104282c014010b0302d021240010725020011441c20019000b11008403020f80f516121a99035034580412440703420ba140b03d442611001140c002404452001d048010340c4003201c0803540038803004011a004150250040ba03540c0304c024070981400c1e12005005202400030b410685005000c0341d8130b40040c1044e40340700c0c42c4d9035a814406001c00c101924040e00c0003070a07054480e0743d001101450500308ad0029500109001081c600e084828000c03906000e01081d48100410002c004d450b0184c03205078402c580755500c801601ea81c15080c407104403440c8201c0d0fa600f0041e80d14096404d002c03146a8510304040000c0005000384036203803502410380004d01b0a03c600e90303c400c400e100f00e04150484d080301402604001041c810702000760082c41c0500000c442e1811385412050710060041c010744c60040072078000501c100083d80322400c9180c00900441d8001d0f1901804103052400c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 541378156 1250 541376906 541376909
    0x160b071101030b010c240609051b160b010807061707050a1206080a030305150103020a050f07030e06030405070816080a0609080f0c061008030703051602190611010e031303020114040f 80
    0xb02c84d000e04401120141d0079020321f000a0084030800c00c0507081ca030984010300c19660042c6581e0040020350000307004248121010740940200b480350b110f50f140c0120541381c1300f5a00c1108006059245220701803408038031110300551441c2c845e40c0c541030343d840007501e00003110000d11810a54603d40082d01640c02e202044205129035000195413902520311103800c1c0c204641c2d5810107105011450000760030504803003440110400e00c82e11440e01d807070100c540c02015200300e40c1085c8088244010044000341a1b0300f507c625030180c1c0e480c0f0101040108801c2418402c1300156401200c0400124420707078041038600c0d014181d060315210074403400d0003181e80011000300e40c0c3d510807403c01c8071030700c07014445101030680c14024528000c61500c0c000c04500a0580498513141c6040c1c1c27540845d6079168030101a81c01005600410503511000640001ca1207040010079500b4814200048003002c41245c05481103101808403450039500110b5400d40305001c410b440745010480414018543e115410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 541379406 1250 541378156 541378193
    0x907031115041202010f0206060105070b06040b0a060f02010b030a020108010b0703090e090705010e031203061003060914010e070f05030117161215020403020d171b160b071101030b010c 81
    0x40781c3d004181300041c0902c8034850300500b1900320301c0500c03800ba03a02104544400340c0007a5501065100d0000182c0140300011007954007620301c0400003038440c3c2150301d54289683c1d9400820a0301c00300d4050540b00e410a2000034006002d502c0140200c1c00000c018090040c043d2030004a00d41c0c480941503000c20054551409030751045004019540c0e2180c80381882040030340c0580500c0500c0c5550010901024104034856440b0303840031001035200741e01000c010094103400388268100d007071509180400a018590142c0001c1001400c0c0c00d005102140c4051210341d24203166a2a1080402400405860301960b40c0075110103450250f000e110803001801d000019401c902c001840e02168190075642a6025280140410009690f0b0100d07a042485e8001b80b51101d940e5984010001c40d2081c0001c82000c00c20395000240794100009025003a034407450b07078080c1801d8a03281c000485000d56203008044080a42e40c024555210b504500d94200060428402258841d6200032480041800071f2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 541380656 1250 541379406 541379429
    0x206190b131e060f18020c0316031803061b08040f061a0909010501060801081b040b040908030907210503160c0e0901021903020a050306010e0105040504020f040518090703111504 78
    0x10301c40c0a200c904a072185c04114541140b51100c40780c0f10949900400011f402102c0140702c2e10028503014001064803000400c51551405403a40741c00001400b50101c00c010111150351580442ea000e03019403400703580c004444071458061071b62200c0240200f165600360441d240b615a4800741c0310700714541c0c051840c2d00000700703440d81010001400b00720140e00c182c2e0079900000c2030b141540313040145510501c10685002c18510b06410109024251004000f8100c84002080062083d0041400815a03010100100e41d00245801c0144041c14080300500250410008124003069415454803202e105c1d030180e000b40340d0384d500400d6144404942410141e50000384001200c2d42c60310000d481e00c84503080c11400c0805400c0c00400d980002403286040c007150f00b5044440341c0c051400d640080100070410340d611820380700105159040f600c50f05004a4200c000175503003281211a851080301410000d00798249151204e03101003050202c216008440101c0307120740041500002c0c40600365000c8203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 541381906 1250 541380656 541380659
    0xb0a0809210d0f0219020a060e0d120213080a0c0608070804080301060503100b180f060f12180105040f140a0c05060a030b040501060206190b131e060f 66
    0x3142003480c00e1904050140002208542495542041c0c42869000e600700250251000000c030000b446540929031078840c0c2c0c030204104503030f4001140e0014612070501172205244194040303a54280c035501c5100421800100000180416405040c828a103031156800070350391031a0041c2030160080081e18a9104404140300c21900000c140f40c00c000940381c1418070b45450b07214034284d4003041c0524000c0007000000b047e410183c0b084100702420202d80d046a9424825400305001160168524001c5800001180300741c6040d50a40301344026941c00d981c41d102582c805101286c20050415034141001d1b0304100514500748035043c480d92003240320005018040c104005004c0e0964400700c081d501c4a04110000b40a83c4880c8e4202d55065500307a0300c469101205401820030b44d249160000d03c2c05e0000680258000b0343c0c1d501a4103006800310440f1240c1c4801e01c207440d000414079422a4180c000c5400c1c90400d03511410100342c03500300b411511240104000151a40380d030100682c0e4010140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 541383156 1250 541381906 541381921
    0x6060607080d09061b0915050a02010b031c03060803030118050403230d1b1e090801140105040b010f050909040f020607110f0102010204031e050304030b0f1f050d14070b0a08 76
    0x5c800c0540340c80c1c1081d002ea50f01e02003880082c03c02100524082110106a485969000f500480118440101550f803010401010b40c40300c50202e150b1800000e00701400003802c02008000c8a040c0c8102c0b40550321080303002c841c10b00c00703000040e00481c100070b0000006403071400460303000502f03038034800d4143d43d80748888071300c444c00d96207281b0100407150048018070307401c0d58000c8900c1c0710701108014038846000b801c0c0c3c400d4840003410ba00500e40c6500f0152002c1c07264070f141c403120b4180c4030200d400300800043d240c0111386504900c01580b0108004004489203840c000d46c03103d0f4054071612003808612100d41c04680320307801c1258201c5081c4800c1002960500d0868004258040c00384004c60505103140c5800d0120009050854001e074243d500580a000003030040703c01079501b019003d0414103201040254014040311003209407140000131801e841100c12011085030001040e6940c2c0501d591545001c0d502c1840300e1484138840d03a1030008180c000c1c030014000c0c0c480c1a8030381e01450300d050113 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 541384406 1250 541383156 541383191
    0x30313050108010e010e16111504020913121805150a020606041b110a0c030c0e0106050703090b0a120c0207140405010609031401090b04111306060206060607080d0906 73
    0x700494901050280188014050b03040c10682c8414160300c1f03c45410041e41055907407509040c00d4106500814100054900d01880002d000d644240c034011810b595640301c8a03075200b05a400101154140b9054100b201e200c0e102001015121342e001154a0b0783c0c0f1000280c083c003c0f690030b4002410003141c24071001e81c060212552040050fa030a11940303181e01ca076540325000d84d04850080c41310190a20301000001c03c01140c14503441000c03100d11548a00f00b203420f0140920902c680041900c0010403554401c106031900c0c298181c440c0c01c0940c0c06e000150956810101e031000801c074040f40c6500c903420745401406030082c5140c01030701a06003000c1500000c0711400d11064055414100108101355004095200b00da03004005000040064101140502181400a000601100280f20501600411440030358204541089005011400000945091303101e0a000b42e00000001381c2e05040c0200200ba00520940340c5514000d1032510703c000311991900241c070900d41c1c6124440b6002c1904 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 541385656 1250 541384406 541384409
    0xc111807080f06011b03050409050c030f01090b0a0501030b0f0d080901030f060f06031508070603050609071e050c070806100302030708060405070302060732010506011b120e03031305010801 83
    0x10403102d005850306030300182219030302e102c1c0d09130f024a80c0845042454881c00566001c0c041c041011700c0310f41071501214031035130815140541030382c0458000098005052040080103000506840c100a15181c0194010071042020304d4000080c0f85040c072940d80e484880030307000c0b8440c5103405d440d807a1000c001000c407080c0351008120245014024800c1006003054030088811501c0d0200e503080f01d182e04282e81c09403540c07044003e40306d0780b4000300c2d1030364050304501d01c01c09054a00b1083d82e5280b200403103240c81001c01402001c406041d0302c4100f40d02c950024000c99a171001200c80c4e0540e00d0086a2510800b100d1981f51165003110a004624090100b82c00503d1400f00501c140c0c00e080c3c550685843d0140700c02882900d002500900300300031941d0040000c1c4600310940088041400e09403682c8842d1101001039500e408002800e5600841c0d6540400702c8210b2400c55a2016a44240020038241d901e81c3c24002038001d0703440036640801c014030403040030280e6020301c60b00e00380003d842250107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 541386906 1250 541385656 541385671
    0x7030c0b0f01032001080f06030c060f090103051b03070e01021216050f030c1b0a051509012c060c01060504110c070e01051c020a030b0a061a04060503070c11180708 72
    0xb0b0b444c0c1000395a0f07008900640100d501084070805840b044002407404142da942d5036001100410556407402280001e800051002e032014811682c0b440c1049110620b1408600101101440031420f40b40c0f00d8590000542d0060048074504c411100e4406182c0d0000006480c81d03a1640180c8802c003c000c1c8041000910b20344005e40c24103092252150300c034001d000d40c1c012100021043d010882c2c4c2c1d240e404000038035003e8041d8991480c4080e020209a100903041c5004c00c03203128480010010000d036524400a6407104180358000c3d4004100840d44003007900380d030543d02c0382c0c0041056592449020020075409202d0707942e9511214202c0d044c00b046171f001d8280d010101d00104903544450a000030003100743d1301e1a400440030340c800240c407082c558001412100a8004000c40c0d00f1180e440354003919041401e488203480d00d040c1c881c105104034029800042c42c144040f4075110301483e06d51150500c2800a045020b40074004209000302d00300d860380c9055a15002e000810b504074001640100d035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 541388156 1250 541386906 541386953
    0xf09030114100608040305090405100929010c0f06020a0e011e0c03050a0c0b070302030a0e010902030c010e1512190b01020d200105091b030d0c060207030c0b0f0103 72
    0x206209844a0444240304550901c2001c40005c1c040521a41c22102880b000070020001424280e0310240480c045001e2082e00d1454400b082c0e040f14800103402c00c420110348403910203042d01d04011918016030640442c1c40200344405a00060303060300140001444580c0d40d01c414030070310800107100030789280600c100e01803108a5012080d5118801c07104581e054103080303654200000c411901d86a1981010345070309440300602000503450380085005a4a0b6281448400c2d0041d20050803031b40c10442c000d40c143c2c405901c03403020794020b00c1c6800c50440014580c00440000c081a0442035008907405000002003800f0003040d4002d80c6030a41a07000c2c13450301044409000310000c1d40ea502d9480e606800d2250703034540030322000006180501c1080d0548020700403824843c2c41d032550360680280c600c04e0501000001c603200d09000400c41d50030621917681c03001e1242035803a01002580541000da080064031390035440400c4c0d884140602a00b07008100d81d066602d1428010000c4d091601000d05005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 541389406 1250 541388156 541388161
    0x3060b01140f0a0c020105091903030e15091504050312030a05010b0f090909030c01060b190203130314011404030c0501050f090c0405060f090c07060501050102031c02130b0f09030114 80
    0x240480c2c00e03128030303980a044c450200c00c958001a01ea40c0100a10107600038030240110b00c15041c01c141d0070086038070035110841c8040100c0b08000704040b5840ac2031001d904144400b03005843d00c3ca01c0010080c1075500740d1403409841c0e0001c41d045c07035001043e506c1c3c109800403d00c01612401d2242500620854644038105600c140001c49282b1403040e47c0c5204203400808100d0000b014030440c0e0321040b9450080100035510411001346401c4040d8025110104c1c00303e056607680080112a05408100c04140d0300ca421651016010301101070400040d641c1c5010149040c0c00900360310380914001c0e2107501403100945442d5080d0703800201032104207542e0005000060000161101d980881258041169500c12012810340c4004142050b80700f541d4406111090700040014041140542018000360b80c0321401a83d03203224201e89a0243d02a0200c1091740416a90180c5484500346140e01d030307074a07950101c1d030075141c02c000440315262100203100c503203c4c0350910907040c000d00690303484607a51 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 541390656 1250 541389406 541389427
    0x1512010e061e0105071403030709082a0d0501020712030e0115080c1314130302070806040803010306110d050a0f0e0c13020a17090a0201090b031b0a0c02040603060b0114 74
    0x40c9010b05a65060040104114040003201e103106c007910303840541140e85902c0d02e45002801c0d80d50307610800c1e01c24012900e0f0021b802c0303060304000381e002c2610328042001000d0002840b810100c90001502c041d5030903c06031002031054441003007820441c0e07502003901640007000908440300c45c40d000140704034010741002800f4000c81d04002c44c07002291046000385410a0041c0a030002941d15981410840108440e1f038410960100c0804d00950894465a80382e1303082554400003640d01070034000381440104000f0300d80d40c10854000d00b070f04041034200401580e081041c1c65007520a600d01d15201c100ca03a000902c075224080c400017003000107118010b2203502058104070360070044050075400081550050b40100d48041810808152003a81d516020440f540c50303520a603012400150300402c001400c5244d0b00569001c1c0c0204401c1070004251000080314a51242d84004140310050f44810050b0b42d880c46501c0080d401504040b50700700a01000401d03915401418400c09101406140f010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 541391906 1250 541390656 541390699
    0x150504032c040c02031e07030305090a050a08070602190c1704050a03080c16030c0e060108010806060904140d0207031e03020d0c0c0b0c0a02040b01051908061512010e06 74
    0x50a070182d40000d00061451000c030705510948505407500e98912210b440b1307902c5004028254580240c0e41041a52189003a4603162034501c6005441070b40030317803a0400490424002800d905114040061030f12113076003c0340628032500c40e00f18000c1401c3d900003500780100244210504000020702514080c03e0100094804080780000b17091000c0100300e00e241c4190800c2400c084480803a82c403014142d491411192a0440e4080c2d45000b00c2000081041c03035001d0580281070b10501809014181d0302c1500713104050000510560765007280702c1829600b48000d1141806042013a40136041590840c2410387e59905140d0880001d6040b101002c0c0100381e01150152440b000c52522030000400b41c00d0071000303031009070440903a00b0000251310211140000d51120024429a001d01460098400541c1c441c000c050103100501d0440e103081000718440c02000c1d80c4428000c1c5862014144141c8004082d0440004481a02c0061005100494002c061168054801c03121080c1c030b00b650a029880 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 541393156 1250 541391906 541391987
    0xf0f01021905011d0a0314120a020c120a0203130e100315110a050c010e012c1e0c1e01020307061a0d050c0109050d050304031e15050403 60
    0xc41d5025101070008111080d0030600c000840040c644000c1c2035500d450759140d00301400103c02141d640c1410500070390210050310b41c3d4001c01100c90300103585140c0b102c0040c2d07001c0341c010f58881c020240e0b43d4001000d4200602122407407a8010b40d10345254421000050499070072040c07900300c1d18820001c20981e00307240c02080d203a0200341201300074980300a19000d03098145900c040c0a01c00309200741c0c06680312000d460818142002031096107008110360303007211042810302200b1082d0f03001000003c01e040101402c10320164080b03d040549a80c954808030180260451141d04100c3c085903561410201c01d035849103880740700465a18040c0300207507032449002d40c018191600d513800d0f03031009d030300d41d000b402031800c03002e44000c14002075450915101d404800309540424401000455030b400c080300002c0900e17620100440c0343c10305503258203490350200c86a11211000d0308040d0300016440e42565440c0c4940380c0300c0031449051500e0b0140000f81c60304500c5c13100c0f4403510420525803444010303852 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 541394406 1250 541393156 541393183
    0x20604030204021c0903051218070b0f04030c09020c120408030712090302060c0607030f060302030c0f030c130c03050f04020603150a05030a0b100f1526010806060f0f0102 75
    0x40e074034485408116495000c0310b00030444149041c0170711051603002001007407107030700310003c418007540c84c00940c1042c1d1044440c0c20195a0250034103104018404000740030080040014a04059580c0e580c070b040410550000d420b0260040340c400704400d01080020040d10704164000e003450300300726540f9074a00610344c01034040e44401c10070380c6659004600520195402400159a4442c20140603548542c16501d401c0041e01c0d03c0b0128560625031b10401d019a68020081d0544582c110b0420440315115520294140901d101d5114560f80d950f400070b031000410103011490003280d1001400b01c80e0b00030420201ea0141c0c40801005aa40e203040341d50220740041ca64039030814090101d10041d042d81c002c55010300c02d0340025000e00c0050394515218003940c4980d4861180c40f003c50000b8091903104e11a16002400c040350b009078055500c0b80e02d040d650094036407142c02502070055030040f003a17003d50300f190080c100b4040a4100a00d8128103081e00342c0d6120380202c0c01d00c000079034481a200159 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 541395656 1250 541394406 541394411
    0x20303040b041b0e041a07080c1c02040e090a060b0d020d020d052107050f0c1f02030706060303080402030c0a0807171c031b2109020613030309060912020604030204 72
    0x1d6000c403c003150254003400c040602903c4a00e80391501c96003c001e440d000f44000e14041c400581d00034480c45071a482564071048003810030303a180040c0d00303c080a403004403031a40e800b40b00100300d56410407a40c0c0d101e44072040041040080501b04181101c080c83e103080d0240075810f12900268a408813410182d07a41034403141d01c1d94006043c60360404108800c00700c07854464400301c1c1200003102d40039080c0580500300390741d428540e103022560381d44080180d164004c617130b044480310306555003200601c0419090064a1030060143c3d00d00302101c1c065003045001c103800d4001d00043d41000c000c800d06a1900751000c040403818142c2c0c140d910100e82c0318403600d000b00303200d10072060074042c4030081c200078403840e00c11440b1103d4107000c2c0240081d4900d03c00809420004040118800c41c0d150101c0d06a00c5107030104a2554403c400241803050000d0340c0140042112902c0c16507001e43d070300e000b54001ea40c0c0030742003410002c0041500d01c4075070044150860045128016070303950811181100c0e4101c600 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 541396906 1250 541395656 541395683
    0xd0503072001060e1f1202010828091203151401050d1e0c1b120c15052706010e13020a180b091e04061e0e0d020303040b04 54
    0xc6035070989198036403500715400e0a000141c20701800312070b03d0145003d120f0550026070391400d62040c58000744a2001c2100d44a14600b0255001e54091038000b020f10b05000001c04a4090503c000e00080d10910034032640c80510f41c062010044008050802c40c0c5010701c110003030684407218500281c01920030303040301160302550582c02002181d81c580352160050103030080d040b8031031038069840140701e10118141103244401c40c0c81800a12640042e207031802244112a440b14039980d00c4e281503001c1405228101200490310700802298105840d442c08542c0d4501005400c80000c1d0340c06a0b0506607400700c400e00e900d0400880e085040d40c481902c0304800b0343e40e2040601c0d000e03956400180d000100082e000c520101840512000000340c10000c2c8240c54958007448030b0f0f0502110418142c0c2450a50300d42c891040d003011701e401a01880303011801419107682060300502c00c0305402c2009039140035504803441c060101507219011400554118503050b03c405c80c6e00c10004100500b9110107026 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 541398156 1250 541396906 541396937
    0x2040e010f090f0b0601030b01140901021207080307021c0903060b04020f04060504090614092815060207090e0309060c0111030c070209090c130c050c0f0616020d050307 74
    0x111240218003a007071040c0541c5041c6661101c0c1229401e8800e02000c4c80001c03101e5000f030041d030080c001e040e5200850a0a00020900b503900003520440c118000c1c8000c02256041d180058510140604181a96400c100030060b2505000640b00c0186002c0040d500c940c944e000100b98044a400c010003048980328400080d00034070408244c07601e603501c08035001c07800640c090050003da039000c0b1007c20046403500307d07540403400c00f4dd82c0b483d48010118001004942200800b04030047e0319034003001c1c890704003030050042d41c00503180c1c45c00404104008004066040180c2e00c010080b1030070411902c0c01b134030017942d00c038400c0000044c05514005400c1011003030940c00070708584c24090100c1d071282010701d02200c00341e02440041c0c4c420108100401c407c04000b0581003114400108122410b107400030282024001199441c02404030074058208942390070300c96084d0121181010744041d240c40d00d018803159009181c40421540030032065400e00350040100d0fa0030071034504114129502025 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 541399406 1250 541398156 541398161
    0x1b0c01120c11030705060412050c070302120c15032e03020103090305040e01060203181009030308060d060203040b0108011107030903020f0a1d07110a030203030c070809030a080903010b12060402040e01 88
    0x40c5840e000f8400095500107103d00801d40d14000d40c4520500c00320303046801d03c02c45e202d000720028454103030003c6100300014501140058800c0d91b440c0c06841400c0101000a980302006940c4e4000014001003084a10701c0b00b808504514803140340306d51144c200101a480c0306805a00000f4185a941c0010300c1c02e2600900684006004203003039000b4039a12504001d40700e4018504486078003408413401c0a007440e210b90b03d01041c000039070341c41d03140f540356032021518118058040e51b004201d0380c08800205000c1d000a620071070081d84410169454916070a08403515140820020842480420b000940c00040301007265011a461a41c8aa8100015507202403941c00081c2d00046545600304600700000414458015a00c440d0040510911055290222075800030016002000041d080d042c031074014240d80e500a0708036608062a100200e0704d0420f00e50303c15145040c000c1110400c0d0301e024015050071174010395003503004142d0544511743e21040500000d00c00d64648420b250443c0b005d5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 541400656 1250 541399406 541399427
    0xb0c070f0b0a0e01110c1c030f090305070b15151e0d0c080c041a0c2401030b102105151e0912040303050d0906060b1b0c01120c 56
    0x704480242400740d002001000501144040340d420035210b10022558101621050903443e009000c80314000c2207208200c540d440146800d266903400c101d510980c4078460b503a0540d100c0d45400e5618205400c11490012000b01280310070600b05e181c29249444500a050311400c03900345540d104d4103484200c00d1a03040e0113500140c0094003060640700314074250440804019951100d05240c1c42d2390711100104e120b01e000340000508a00510311141006d00000e1560032a42c1d000e8540e42d14541d41c0414140840ac2030200c0d102d800c4400500078003242c42e404542040f80403a254411520740814070056103080e08d02c00c0481c10310441007030107120040c0403450601001c1c4034902018a002183c122070040e01819509400c0c54400002e42c0030381c000141d000c0c0081c0d0a503406810b251465504642550004207103603680d03034846480e013000075203c0c0103040150441d6020540c4a0300e01c124080e14090441015511940c02850205c1099030041005601b00c00300c5100800c01ca122184140e50100d5071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 541401906 1250 541400656 541400663
    0x60919032106051212090d020604050a0602060919030f050d02130e01180e07050d031103030f04021c030f110316050609010501120c0e150d0318120b0c070f 68
    0xc0c1c400e035004036074250b80b240058a20840e1140e01658030446825622090042d105c00c80c030100b0025200b003482c0c5049101151840204401c1c60183c59001242c0000c950b03610010169200300c051101d2903006001c4c05422802d04048007018a1182c3c5005242400c03c12459090003c00150b00005440c5901196000301911003034582140d03a078000c000308d0074002d100303001c2058102c0071302c0080a4002c1c0100007055086e440101081c23030030a81004121000558200e0034403d071b00e85105d8078000d0500c0518884d070410030b80c2580600d0580140306000060b610600b400b2105041d03840c0010380c01084183c1c0c802880d00d85840e4402544607118034611801c481d50130300247d42d0074904100b040002c2c1503840740a12400134012660380d8005c0c041c4040c05140014461020814140300000d40c0b0401243d001c000b030303410140d0406000010840316140c00c0d8050b0000349010840c06410740c206030245d0300a100c0080c1e0784064031802d48034a085a43d0260240e0740ca00f80008003c0d003840603200220708010340 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 541403156 1250 541401906 541401947
    0x1011070203031c0c05040b032d010e04170c030313031413050411040302060708070302031902160e01050a0504020906090303121f0315090501060317180306091903 71
    0x140e80d55080806240c41041c0c8203d6414084505026803150303003510111611911143e080d40c0b104114003260850324906201a0900c2140441588458203241402400542c2035403001d03003000d08200c1c503220110135000445907020030151000b400000100c91b80046400350b00c110900035442c040b00c2c1d002c00040c0300e1845000c045100c07080c0300050002c0e6802c403401203c3c20080307000700c200008030038007481c8001303075001ea070901400d00424400801001030510910540c1d21342042200c0309100c00303840421071f40040e8007011400400d85810a0003401410800350500b11561418000626203491802810300941c0c0114240780035032100c5003074a80205004003500e4035074401c0080c0c6040c6000445494a030b400102d9561407500c0411125070083e250401a000c82e488490488000079043d00c4800310381942d60340800202098003130107400900c1d8051051550340d4001c480d400c00d80f0340c81d4455110300c00d81003c0c0c103104203800009000103128208007044c0143c414a8242900c20607049407801d00d0380700 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 541404406 1250 541403156 541403167
    0xa0e1306060e010305060a1410050903030403061d0604020a050105132303070e01030803153d020105010b090d150e15010905190b0d020d0c0e18101107020303 69
    0x40d0481010407504000b0384e020417450f512207041080518091046840e00102d9205e00b03007181c00c24102c000c986106034140540703041d0003000460300d140d0255000b500d01a40c4d0700262000032000242d50640d4412040042045040a80000700d860400d40300b014180040090200f03000d0185d4140d01e0001e00c81001301c00395040c035092010120078a0041458400c1c0207031000490084c210120840c144da820081c490b003984c0c1c45100e011081040b8101256004a50b0440802004041030046d003240d03194020b105052810b12031011107461200c030a0606590502d0300602034142400c0554003281011500c1114031245400e021864001842440d5440d03420090304901550000415100d00090188641e0b84ea0ba23a4500c0001140c000340c0e0001c0c80d10340d02d000140c280000a41016440c8040200786800b101c042d5400180340090ba92412100c490b480c0200300a10f0340c41c030010310b500038601e400d035030f4000c020414004d4a03105181040302080e981c1d5844035100c126903400b0360390600c0c0d001e0304a95651 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 541405656 1250 541404406 541404419
    0x92d0f0207060501080c090c0d0911040504030e01110f0a060209042903070609080606040e1c08040515040210050307031401030807050601290913022116050a0e1306 72
    0x104000d000e44c05e01440740d002d0799203140c10544038443c4114400f4015609046081c2e601070050031203814142c1300440d5804400d807030759540d8400c59000d02d01ca51a180c1c0d81c11401000034051100384083e640c12908460f00002105e203011600641c02039100400503039549001c40010010028004c1104040d240c41e00d8034841c8403e10356240701e480c0001c9040f08c00c010360f90541100c00807494080c0d404c8507004000442c0c4a42026001150b0345040a8140c581e024041c10700452180b0710104580005003103001400207218007440f500046010080d0b000950346415008109008070343da081c0020040004005000c9a200b9804910600710550390b60f0b4565950b41843c2004c2e401c09c0304151224040c090001955052281905c1212240003030004491000c050300c04205401080030107400580d800d2042500c81001d02c000d18482e0460640504928801281c040080e040204040380c01c02c6115000f040c40c1c1d820805955042c210703490020804130080c80400d142c00954600c8800d51800c0c143c020444 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 541406906 1250 541405656 541405661
    0x8070503030702122a210703170106020a0f050a0b13210824030715110601051c020103021908011e030b0a0513050307030c020109092d0f020706 63
    0x20140b640c00c56442e035080c010070110f10b01c21440e01e036549524451104040020100c02954010412025a10440038580f498600804502445400e505000401008058200302c8080c1c05a1403160002d041b503042c1203000c0d545040041014103402214000354007040400c00240b100550301120344031a0342442240c403800301465881c1201c0200c2500b134400c2480301a119041040341103544e40c80a00c1e250300441c41207200120b0150014204020990820340d2400c1004200601030004407001c3d244902400400c0401d00201d1107100b50420b900421a40e40c82000445844020304240401c3c002644010f034024460340d640b81c10a8200ba00882491907003100701541281c0c4d14010358140d40c501905100f11a2205010091001d503010010035500d415943c0415802202c260036031312003e40c1a11264034642280c0e1080b030008408080100071964054010802004015402d002c03940c2500503020200301c118180310030741d07a814030070f06143d1145034000100704240f6403011035903901c1c5030815002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 541408156 1250 541406906 541406911
    0x80313050a0b07020a0509090c0919230a020f070b07030b100f200106030f05160501110d0f03060504060e06040e0c0a170c090a020a020708070609120204090807050303 73
    0x881e001c04400000d0000c402402c5602155000b800c034801070341008104038001d90301420202181c861020440540d807568005030f03015a4007018123a83c40c400f1840a507055804200300303103140d14410a004290345e40e9941a0a0b041202c0d40d40140c4c0360440f03002e034005180224a03003e454011804240700d54035070503500c03e521045043c3c543c3c03034100000754030584141216411000010740302d030550b2204041441c825510000c151800464079a507a034650324044100f030102502c540c0c03c00569a10310100002104000b0076080c04d00501c2841d0400d00715807245e000c0311580040c00105c0070229000c0344280e111304081d0400030402c200b10f5481e00000d014504044800502480c60001d82c88680c46002130107c0c102d98004156100081c141804840c2c1c5e40c945070501c044034455901741d95510355882104901c203800290300107031108000640207103403102c4e6501001042e048001c0c180499580100540103a0725000741c1429812041d02c049030003808003d0014015000218540303080050110042d070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 541409406 1250 541408156 541408159
    0x12030a14070f02011104050d110402040909150f06030b06010c0c08010f0c0305090604080304140a080a0e091008060c1b01060303050408060709181a2809061d090708031305 75
    0xc60601c2c617910010451281b80141c6d503120948114041c0003840c034060004d490304001d8005030500c2ea440c001d010a545c5c41c9541214403e500c0207161850b61300b10310074180303000f01000702400b66a1868941070598071020303000f5030400c44401c21104c14800c0482c0c81c80001d24084008010900401103190010f014140798240060300f0b2002144544500184060207150041505450f41d2115950500d2580009000d105240201e0b2080c801003496040640301040c1151200380800300500201311605034000c1815142142c054000d200c407101c0011302e10b0340000c03601c034819a5440b549070000c400c41107030141025203609000c030100406900c50701070302c01c59400c0c0301210020384070144103071070f209241e020315403010703544800c03845d403100050b0000c5230b0702c130041030300d0102d0f002c01d0001040b842e0711074100303d4030042c0c10354400d90030f6605c049421a00600e80d4100130403109080503171001a1b111941ca1207800c0c0c400e804e005c1284480c0a001c5480208400ca045903a5081c4241d42503e448076030b8450300e03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 541410656 1250 541409406 541409411
    0x1b0f0304091128020f150a060b0c060f0a1d070e01240305060414040f141906090c260705042703140417190512030a14070f0201 56
    0x254101e1102e405480441000d0f07401c60403951034000f03210100c024004002c404503c03035120301ca10080814000080e1051280505600c40e01d0301e464543e0030b030385180e031040e240520100528039000c400030804540014642074200361540f10120341c03a0260000c0c601e81081c82c0d64032000907120000000b90b2a04403452071070401c0047ea41c40340c008a00062079044c0310810010907d594802510036400554820303001040061828070340e070318048048908540440716140c0100c014014081d806111248510806004040205500f5401351200480180c0180031a40b180555000c11180b00c18a6001d05088109000c544250344410030100306080c3e00108240296100070555044c1401240c0c2844d00b035110640c410001210840640341d40101c0c2a1304000010882c0c0c10260070b09030042000703004020580707002100c800c18440c10404000101003d01d036141e038034440002c501240030303444069041c0740e09403640e941041d4440a0250104660010501c2000300884542c100e03106240740c00c10f40e4003c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 541411906 1250 541410656 541410671
    0x209010905010333020703050c01050c0310140d0206120f010501050a0507110f040c0e012712080f070f120f08060d1a040b240a0603021b0f030409 64
    0x4100456100f800080c15820012489018058600802e04080345101c400b0a80000241c00c00404981182108400048001950814400f000d00a0700d8001c01170300900ca1650a0045040600703c00c580304425000c003910100c01280d5a0704604001e903150054446556503000c070360340010081c0304445201801140c2800030400f54800c80c2134840506d4141c960a00d041003d81766440d11003000500d15030710400c442008082c48d06c03140104164420180c6460600c1d11152001403e40350003800d0800340401d10740b80710003819610801c9041141c60000c0c0060310b49030141851901c5100c2d07440f000c1d1070100f000402004210f840b41061410600480c036054440c410860111f034003084452902d000070391204c0100b40c423850012502c41d016842403203031018403140d106028410040884003521106800810005c001290031008041408490548030b40c00380003600140c5414401c0c091541050f501181290041c029880c0a00710754802400b168041064600348035035980c410300403100d2140c180143c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 541413156 1250 541411906 541411919
    0x201260402100c050d08040609020d0311010b040203061c0201090b0f030f1303120b06040f090204090e0706320d06030318260304030b07020a03230a0e150c010504020901 74
    0x21503142c070384c420043e080134400c080c0212540c4170301400035a00c180e0790b080741c000180d45003400095500d1081e00e802040d402c070184158211441810914040c500410401c800c0c3d40c3c1d03e281082d04d0078640841c45030461401d0004847caa803158000c0b1200b5440007402d07ca1400c05003024601c18500124492510f5a5002004000c0b1740c135060001c0100c2c0800d01c84010319042d039040640c40701405800142099a07680448000044a500c00c2e100c90fa4005010b00810029000350301c803203407410000f011b04518141000f00b920a01140c002d001c85100541d20406000b10310315042100902c1e0420ba8a81410311208401850603110032004140c0c503440c2a00035010644401c001c4a00100640c1c04801040000c41d181c6141c501460101d400200008000120301c904403902502182d8010000041c583c500a01101d10445070402c03030b442e00145140e1032900c800e080b580040d00c14034000c8050105034010800803000000c0141c070081000c601910b42c4c0c101540054800c5000701ca210949998400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 541414406 1250 541413156 541413167
    0xa0c05130606050304062a1205060102030301030209010611100207080309101503030804020607020406170606061201060c05070509070e010e04020f030f1801110702100306060912020126040210 84
    0xc1090b000c0380e42400003501040b1150700031075119184d0030f00201100903030003604c1a0304940e0405040802d02020f841c0d40045240c2c0b044503480003007130005514550443d00000d00d007540510598003000640309000b40c0c102010b120070b0003058002d0380c055444601c0c42c542000140c00031203208041c0e10501c070f06003d036955a8001d10114120340d1580a01f800d0440d01c04403084080184180e0b00500f0401103180162074034800c210041860806001d100d06550f048070307003085000b929552264a040c000b00c007402c00380708c640d5411103405040c0742084000c0740c81c0040c00c0c0300060380951360065250301002100c68000c03080c2c02c103c00013641e60703140d4001e01400300b10403409038400003245e502c018000552260610500c1c1034000360f08101c10984811407080e2903007500e0145010040960740442c046c011030801802d6840c1c4da400b28201480840d0500100800600041c85031441000300c0070b82050030759000c0c0c06c0c0d4a81e0b0040c400b490b0215514450011403a003070f020f03501207000303000310b50b8586c0e140351140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 541415656 1250 541414406 541414409
    0x11805040c050d0507030c090516050310090522051e120f07030c0b01090f1103060102061605070b010902041a1219180b0a06060f21020c0a0c051306 65
    0x1540c000010b414481441681100340c10111018442c0e4034011010400d9001810700a140740b40d40820f40389005c1180702010b501c3c0c5c1c0a21005c1c03040c28800c0c02403070504184011300742c0e021110b00242030b988104281181e03a9205012851101921410106101010a406041ca00f04810303002081102e41c03003240d9a40d41c0301d5201540321109000d4003e0204856004109840c0a4640640010027584414800ba90f007a40105229903581c840030040c2a49801600c2c1d1801c5441413460440c504040080e407203480c000d0414007041e1112103200d20845c0928181c078505900426101c86a68490034090000d511230f0040e402ca464643c0c0c1e0540c00c03200c200086864100036415400301c01e485003c1280346041d0700c800c4041850303403181541880e6a01541318082041e0081407040c2c1c06051002105040310919001402001075502c04142e005070045c44040c8481c0d150554501441903540c40302c40280030300d844846c01070040a140c0e40612011143c1401035900464680400640300d4845108403080f5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 541416906 1250 541415656 541415663
    0x90c0105040f0b090301020c1e0d110c0d151a15031e04051c0206040c08190f0503070209041401050c03010e070e1f030608010501080a02010c3801180504 67
    0x60a100b41c2141c1005404c60200280015090006544040b130419650148060401556200c1c580b081c110400c0340b05907800301d5040204c0c0c0821007403d40741d224a019100d081c02031300e006540404100000301300da003018007028002c03c94604e4507048848481800903016120303007201c103244541440c7d0081183c2c050801803030164600c0c402c0c0040d42c003032100020010b617094083c00800001c4410104000c42c0300f5509580908840d26152800c0040380b101a00840000d0b40480f00c0034000d00440d1200500b0300b50050001d001000051030075510310b01c13825100035007000100382801f041064240440714410720280c000c2c40580d4500c4c4109006000c248030f82d07010040d43c007000c0742400d80102405100f014020300b080080d54040c555118961101920800010341d4030101004016400e215440c054401c43c0040d1103010040d800007003486125600c0600315030a550744807450580c140030350480040c000703030340c503942480f2020001000c1182441404003e0710840c0c2840e92003007486c812103201d10751 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 541418156 1250 541416906 541416929
    0x121d070e0601020c01180305061017010b100c1511030403110307030806010e12061f45050106050702011106062d0a0807060311071a04020a0e0a05090c010504 69
    0x2140c80045503080551186e410440401000c0031011403800d2040d00e02c85c0c3c00c2030b401c1c00c21003441e00b0392107140c8650502e400c1e2540d914100c0280c000d03580786119541524894030707094180783c0580c04c2541c81503800f80590081980b90401c54208010588051840b0310f00a48030388d20600f0007403410b69100d110f00c140c014009014503001407a40d41c000c0707a00f00c0c003c2c074018003c90ba0100c0d40b40704d640e28101064540341c0003010200c0a000f41c3c800348600c0d6a02400c0c05001004112180c098401c1504100d40100f1000e5204085588c550100180080307400c2c00d0030720310610155a403090060300e142c4c05242e0a0340000d2403503c5600200c800014410f0140501420b0203010107442450200007110f083c2d4140802035142c0f000c441240d5400440c00054031961000e040643c1c81d120015003112044500100a00814402c074004a120301e591201c0b99000031414105980e40c0d44009003c500c00e6400c001078134040035003409034603802640402d2180354814215080d04201c04015038240c0154070880c282c411 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 541419406 1250 541418156 541418173
    0x40e070e07211805031204050d140315060c0303010b0403110f090402090403020c0301060b0417010b1f1b0308190b130906110a1d0f010e04020a121d070e060102 70
    0x1c6443c1c1c00412403140d4860411000d070b2540e80c4540c1541d00c0780b1004030380b032081002440203001d4144001c40c00340c03025040c80c01c0108080c640142c01c9020040c02d40750340420307080c440c088603120407044840c03601c403140c01c1d6170b502d42c1c56114403091908940420340300e2410317a005800351810440810f500c1da60300100703143c502d991154200280c612005004404501941c0b0f1418400e4800b4011800079202c2141c0558840c5e04183c005402403220403201c00090381071240f4001d0300d80740e4404070103074406804d2000c0b21440080209039203010400e900700c0304a0304202403013001c0c15886158035006480d485000d4008404601201d02582d00c5210741603480444c1d20798401ca242800d9011944680c40b4071404100d1031081c0d0801001504004903d9011905040b00180522404442400d580f0320480b549070461100f0000205011400d05000303015550000e455a0498011803203034042c0c080030b0300c00340882c80d00640c0c0c62980c00b40702c8400c0c1c3c4443c800c4000100308038505018407031007100181e00601c02417 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 541420656 1250 541419406 541419467
    0x9060906070609020910060201050c16140f0601090c17010602060a180f0308090f0105040f060507050d0c11010b01080411090402130e0303061203070c0303050309010605040e070e07 79
    0x1684841c0003118842da550b0251030042c0c40745103a007849903103280c3e01043d010b450004041e00b5180018400b40001000704109016224010494001d0a4111050742c803102c050888840c50b101007030807000e10381d10030a000000c6e5540e2503004204c0100181c4d40d100781404ca04030101003803440a00804c070142c0c00a0000074020f205030390040c0804000300c03d03421155001500e0304640380102d41c0b019000980b40c0780800035056030400c072088075a03070300300c2c000c005514094945e09a401c05011008001c0d0b40c6801c04110494480c206644900c428008100010b45220f10040d02030f0032203002503490f95003842c1a6074040d40c09103075420720541d08130340f902003d01c41c44404c028a80070003c20813a0300000ea80041500c0c620b051080c10500585c040c001d43d581d051503800c1103650004840302c13150b0f544c01007060000144283c454903007240da140c144991691074250106000d0810f03500003a07005840d04050300451000041d00303004440e0380300000072094450301d80441e0308442400501d0801340812306040c000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 541421906 1250 541420656 541420669
    0x405040c060516170703080c0309250825060e0109030602070812010f080115060203180f0303121801150b0c010207020405010902090405222a03210302090609 69
    0x20b20280d860b5000c0a02141e960307900040c0451341c039035050814089402810180c10040042c0c0002e58401c038142185051840b16a40c2c2c004508002d80100a110055140c4440001d051019109040903101c1d00c040b10000312410300c1c40c20a20449102c6000f4001880501070b1405015511060b0340e00d001445c150b8a6481c00703980440c1d41184d104008100d450084840d40d034249000e03000200841c13444620340308103d4290380311940c3e00790780502030a00c200442600042241d18520203500b00c5141225400c0c0000d100d080804807441d0180070024440003080e1051030194442e824500001c800c042101c046a0708941490300346901220880f50140700c1e041c0310101414103010854005407400540303130701040c10780e1407e03444100c0c0c1980101c1c1080441c0b425020717044d0f0002030b0010b400e80e0262a92150100c080e103520000c1e0049409030820f0203906081c01d0790b05150b0032303a41001d150155991500746c85400e600401c0c42c3d51105010303003400c1e00910078000c0300c4040310f0050615040c95000c4041004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 541423156 1250 541421906 541421917
    0x270c0305060109140a0e0c040305010b1507030e0315090d02070f06321305180c03010504150e040c0e0906040206030103320d120b0a030b07120501140f0405040c0605 72
    0x144141c5c0c1d000c00082010440340000d106444101c00503807113600d1490b04034295100c4c603409a11518043d210807105201050560f55209e4051a1800400b03c540c0c010900703041c0002680c44614107503c08101484038000352040c105c0455070308440029507252102004041c29005190000e80224403503184625a908100741d000d881d0002820030f20b950140700d0850750701c9031001041300002c0d00307010000ba140070b9540400c1302e5051000024146000002e1010b03034841401880e01c45c0f6a15600c4900c0d046486603400040c194186048019003801d04040c40c01506911070030903501c038000001444a400410194007641d40504000d0440e4219030341d034504502c540e00031180f8461503c0c18201001d188007034000141d61580701510078000c2032a8014071043c020416401d6460a04084a00d2a140c1268140031a6000208000300ba22401303000c41e0f00c008070b541c0707400c0c040e81070000200d01c00404005030354045408662688119980c1800e00c022307107004a601a000288903501086914041d800500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 541424406 1250 541423156 541423159
    0x1050a0e0403021e070303200703060f110d09110a03050c060702180708070206011517091213082a210a06050105130912050a09270c030506010914 64
    0xa0001d410310358201d81d5050000c4e15059103a00c151400c00a150b002265031801d80b0314000d4419416444420b415503a2819200080180b69502400310a40010307078070440c0d10840018050395502c2c44a4142c40207402c07481c0041d80d04141c0045511001d01e05084010b04403903100c0702500c1402981402c000c102d4001c1101640c102c82c0c50004595190307010340e40b00d4480c01c03050312410801e0520090003891701c40145c00280d21001001013018001d03410500c600e0120310031082403407555480c0c440d501c4c200403004488000c070b080080350b81c41c05980903461480c207482610f0201c8940105462042c00c150301541c1d80c5007804001c101250305142405020041e2503043c03074400d0390074001d0240d9403500c0c0c030328000401d44403103542c0d9005000914182006405065442000340121505a10b901c40c40c2c43c0d040741c2050038800001145500d69000d030280070002e00d000c4800c9140403150240242402c0030b07118001240614001c040800c5034000d2045600402069640d484014180f2003000318240e00c004405e07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 541425656 1250 541424406 541424413
    0x81501091a040608030c0c01021b1e04050106050c060c0a120b2b03031a061921050906070c0b18010f020723010204140d080d0f1a04020301050a0e040302 67
    0x700075070321a80074010080039136000550307460f240301a9003410002e184003158110f40218018080c0c0e050404840c19074100c0403580b4401041c04490345d40c1d034036607510b41e13455001814400002001504400a046199035840560b10180d4400100711000d105801030f4002203904000c0c15004913101d42e000d07541c0050050704010401000001c0942c159a407064000c2c010041810303030b801007692502442c0c0e2070807250714070707494100f00030300004860b03004542100702e01d00316a00b40f00041a00c604041600607607086400428501d07800400300180c80c04070380c055071601c10f01c000300c3d403203500c01e007440c402c101d40101c28100c65841d03507004c0210400c00603620030003541d241e846002d0203201d9440200521441a0b154404141d81110f40c1080d401180c040c0101c81d03441031004000080e40c644409400600c11160720700006101e1800c11035900480d07078400c803003030701c0e1a0b440008121954030a40280040780d40f08a82e82018100704000c0e0302c024010550031025a003003c0100c0c42400d20090340092203401039 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 541426906 1250 541425656 541425701
    0xc06020712031b021503090d140a03150e040c03111f0f09031403030f010503160302040c0c061d120a1e05070f030f08070912141006080606040608150109 67
    0x18541e010400c0e0f117903403070203030020900c44a46003c006443c0010214140b035031840380c8080d0060f0035070080101c030209143c3c88101002d80e101c0c00d41c60b07500160907030035840440c908040c01c0104050303146c1d0104803040900c154060803289410b9110b00c1c0790303800c4900c15440307141070a001100e1504c11641c41d42c09001c021080840001c07212070112a00f8072000000b1a201d242c4114602c04481c0182e003c2400790f00701ca136003210302c00012100501034a8044c0d07000300301b03d50501d204660340039104d01c0c09000d440c500030881400083d00400011401400c0c4d003290803140e0712024079489807150030f80700c00114070600c144c1e03210104003020441074402d0350b0410328204800750700c82450f94452108110001981d9500b034417035643d0000c034000d8110705e131031030011711083c01c5c044842902c00c400d07a4040c0a41242c3d00d40c3c141031180802c001c0c90b00340500302c4248452903840700c1140ea210000e4503038510427402d018021801030700008401c401a040341c0d81d8120240d20700134200c00107044003000c0b501c8024a0100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 541428156 1250 541426906 541426909
    0xc12100c1d15090a0314061e1812191d1e0a0f03030f0801120c12140f0f0c0607030e0919050f0105090a0524060702030a0f0c06020712031b02 62
    0x481d90b00950080c0c0f44601c400036900b540a0905900401f103980780c03003121808501c18044c40360409c2d400180803440140004400c0c40441c506498400382070060301c40060550a040400802c40000040316160a10381a00007409050301404200c0c00681190380000a00c0c078040c00c1503400c240c40200507241c5101e1603100c00407056121850f8009401052030509000043d0340e05c410f0b407500410342c010004503080015a100e140070b050a1081346a6800c1d40031041090001c6071401c0001d00111100300c40303e4444800701107071102e510a0a680c041e018159100c0200d0610408031801b0740d40c15950012112640c10030410716520240c0440007100070209880f070301801038403a1602881c2c4190010086624103c1081110040203003003c070281e090000380100080c54402c0b46240c0018a0702c007652915080020070403600402d400654035105140310340b0140b10f24906405603680c0603103c80400241c0b900c8099941e07038114490307214403044241c10b4001080c45607444c0f8500c140b842c4100080c160580c1c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 541429406 1250 541428156 541428169
    0xe0d210908041203020d0912061a090a05150103020c211905030a0c030207110402220b03010e09070608070c0c080607020115230d050c12100c1d1509 65
    0xb0422032a00c19283c10180505030108110040e81c003107840c041201c00d0030014200000b0105400003041d9603103940310084900b5907082c41d0441c400c0301521016a03132911800d84805003400769004030381020760035500d8a1951090080f10b500304007410040c0200403000d00254041d8582e0b080c242c4602c441840b2106a4500410350480380c050281c1d621034a03070600003118002c480c0344211110070b01d44100103941c0000d180030465820f0703035021140140c84d000c054080c0715528552900e1202c0380f680310000804c40e1380840002e1070503109004581140c0f035030354501107651a681c034001c10010a05620024842a100381d0110f01d1043c41603001d00d00d01a80c88960302e29043e41078901c1e00140c1d4403046220780802c03e02c4240d1000b0030348244443d181c0382c0540f00e007904021050b1100d5008540d1803603440240201000701c03000c01403000d40526000c40030011031588400e800032920040609000550703107860320620390700c051840c01100c118031801d5200108504d01000d600d01c66144102071040c05502d40c0c804 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 541430656 1250 541429406 541429409
    0xf0702040b1c1a2502070909050a1209030f060203060d0804090c081f090b040e030a082d07030b0a0312050c060a150506070c0503030414040e0d21090804 67
    0xe00007807542e40d410303d048a52803441c0300100c080e10410304200b0208160f09507840c0c00344070644000729111110450101c1c1001d00c1a084015424140345003001046000519500c06d103004c0c003901860308900c07020403501181c15200c050440da40c548040c0001c144540c3c01150411f03001841c05000307507019a03a104881c1c0280d13110050090355801c8281505400444d070301da01000781f400840300c81c50082c91324844c4065070701840781030550710301c0c5180e41510b0341e90080881e2454442102c0e20b031110060000c11101040b1159110481040307624444189070004118841c0c551030b40070000e55807691811402041c40f2440c065000b0f03589440040456070191850281025541d07505584d5041240c00e90300e0400043c000c02801454207101a85d4540e801d8000e90a583c1c007155040e0b80c48180c1d041540701012250880d9606005c0054001751705032425001d8611000191801d10021041c50035494451041940c0750740450801200104400c204001902420320000c2d400100c15071251100f00464005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 541431906 1250 541430656 541430689
    0x513050106031a2b02130e160e0f0402011806030509190c170f010203070903030e01020a050703080f040e040605101e032316090b030d050f0702040b 65
    0x21100180000741c1c0c507000e07141850035030700c4242c1008015500814884154104520220090218135508203040c04119403040c070f4008000c3c148151207205068000c0180048103003003072040030030030103d03203881d030b840d51045510424075040305903515090321170f80100040040b8100410801a00c03c0c1540c140e00c20005841640d50006076032506a50303403490191483d012888510180010b6000204480782210582d000708150300c00d0007060244035460003003403481c0c0600e194004810000c0443e0b11503001411240260382c0c88000d950700c00c3c01603171901801300014100b90401c4800b40040f550b20700040c41c003c040089154681035441c015400b03450f0050311304071403403520755040c410207614100d040c030064031070b801c3c2e043d40218101015014100081c44010302c40340900c80305800010704116000c020a03055020384490001490308410f40409c01c0c00b072820300500e09069400c2c0c0d42000207410b21048a035032140da00d0b011a0b042c0c1280c3c44c0c0c00005c41268801c2d00e46c8a9000c06454124249800610 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 541433156 1250 541431906 541431911
    0x1501032609032e09020a120614010909030f080c12060105040b0c031b010b1011030904060303021e0106180b060d0908040f060e01050307050a1403011e090908090111070513 75
    0xc3d0540820108040d440c01e2807009040180f40302c0135a45030001c0398202d43c02517082c1c111394645441c208000e03040550b8800095140b44000280c0000c10390048070845110703503a04d0210b4000540d05842e6030600b900e03d2a10030505100b0200001403010403c0d0700424141082418a42c1c3c4484030500342d03110400f800f40301c0e0004140340300c2100c0140d0031076416201c0c81c0000c0c005112040003250000050903081c204005410608151184060048a5124070040d0003800381c00c0d143c0c203010303651310740d0784404544440703490050004100042c4204415104501c1c01d0f5440c510b002c0c01c00c10090302d207680e4070f554040c03420484000b1581c4c0c50b21440c2001482140660389641c030342030705e0300074003815a4440c100340858072481642c16a808411258071a0580c01c00c035480c1d1740074500888021403001804401d5100c00000441d0041c0b13514010311082c40d00f8400030001988400d56201600c070f19520003040303e10240711811066001c0d8a0255040d02c440e800c5680883e40d800004030038460301c2104601069 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 541434406 1250 541433156 541433203
    0x507200f0601080c09130804080304060f120c1d01050c072709030203030c0c1603111c0b010611030c070902040f061704060b010c02060d0b03150103260903 68
    0x1401e20500307004040110190101e07403580d4011421070754000300042220f00c80c3c6002c0404104c4039400759005402617404894803651543c0780176001200c04405080842c4140140395000c6155020320b03910b45070a50b03075002e0200c03582201c134240000c041031840c1c10300c1803d10240a1040e403c0100c01c00070091000d8a00c10180072040040e004076559042041c80f60070407100c1e002103600041140d4100031101e50031591241c0c40c0c14150306185030619200d4000c8001e001c000180000a01c010f0810071040360000c42244401c2c000f072550f07280410009100c1c48042d001000340d9400350341906200c003105001d8900e014250560903081c0f4060f5048180c1c41980414144103c5600e001107801402c840c1c02c000101220311510385d02c0090f00140300410344e64464141c4003030750340b094641c2041283d002d00038548484d0a107182030041c142451009029100e200c0c1e06003200508016441c2c100c030303002088448810302105001520010701402100da482e020401c40040ea1410000d0f08914080b0300011241e8a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 541435656 1250 541434406 541434433
    0x40f05090106032a15050403050d081f180b010e100f17010b190504050a09050901180308130606180c120204050303090409060b0916020606190603050720 67
    0x142d502d140c0304044030161522103222480d00742d010000e517060048010602c0310780140858103403044e500b0090840c01400c0c0710190f02e680110219016440c07400581009054451848409111610440c9520800e8440240042501c2c0d84840b00610040c50280a000c1000c004101c15032083c59414000640300780a950007194405a1040000c05904041446501d0300d599090700307024444d54004078842e0310710038500c42c900400c04c0b49e00420000d0011000c140c0d40d2000d038001808101c40c562419401d0040200d01e900300d0040182100c1c0e41510341c02c4641c2c8907207034851a0908078000440ba165650407010034207040e0f003200c0710001c0c20b9020010440c000d0024000701350310450301030ba4500600602c42400365503404030544454000135640003034110107904004002d23140b09000c55030496600170030f00c090322600001940740021941c0031079a0035150182400f102103a00c803500c10040d81c034407009015081c800c1e0000d40d0081c1d0140740280035520071000c015000050201c0d0307100240e00111804101 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 541436906 1250 541435656 541435673
    0xa06050705031b030603010e0f0309030f0d020a080c0f0111091c080d200a0c020a0605030601050405090a090215090a0605030408121911090f041a040b040f0509010603 73
    0x156040c509141141000078440110a00c3c1c08076022000300d001c400114151000d602084100100c0350448a906c1d40e085409038481e4030400242e4024024030500b10880710340010449006001c82d40101030075902925030503080c0c0c10010f1440100d02070082c4641500d50240125000d0301058034800d030350b82c5410400c1000c01202810031110300c070403007403044022800b208180d80742144105004103073b02d820340c04000181d800f80c03400c1030044040891414146135100741a175100d02e100755542807070f032502c0c0c64050340c00c2d02007101e40741d0000d44200024829400c00c80120f51b04049400c2c00412100e809a0000c0c13400f0820a44405100d0380204440e0b1031490407198041c018041c9040c0740303146043c280c491081f02d2041c40003403051840c0000100301c155001d04940b456203007500504106458030105006550790201206a00c07582c0708101002092825100d04640000368848800c1506421310a11025210210389184c0c8241d65900b0b9070742142c00c0d4000d49203d1111a400000d215040d454580742 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 541438156 1250 541436906 541436911
    0x5160b0106030b100915182c010b031311040212150d030c060209031903020616050901020307060b1908031e0a080114030a081210090c020c09040c0f0303020a0605 71
    0x10680c078a00010b0038450704542c80a040d40c802880d000e01d40307804048240e48201c1f030766511560401c0714000001d00d203d0b44524658403450521060008002c3d00c0790302d815113241c28040c06404030341c01c001040100120400d4a8001481070701620140d400030301c0040e082760404000ba83c94604400204103000b400070301607841058044502d01402c540644000300300c0c10301c14030000c00c841e80c001203c801da9a81004820750320400c0100d034880b50304c450b2034000c2d100c010a8809100a5140010851583e0700582c00c2d902e0161040e8011810f058080e10307882d0190072140021a00241000c00c8042c95800c40130350701001d40f16110003140d03521a800080d9800014444458681e20818020458510b82c0801d45504440c034029101003510500700c0041d0500005500007440b8020020741400e00d0035058144d140700f941c102e2180054241d0710743c3c0240640d941c80c0440401a003003001044402d2030043e030200e8100b8003d0b03100064164031800e0380700082c0c0c002e403c1030b800360703106403480c204006a9009899 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 541439406 1250 541438156 541438159
    0x2030112020f030313061b02040203071d030c180411120d0230030c19030b190803030a0c0c081813180f020d06050f0106020c0405220305160b0106030b 66
    0x519280440000d910324181601981c0f04016800204840b030041185038080492340003407003103542c0d040010010782819990590318180040700d492004c41454085601500e404010b0440c10421480f407202002d088801070044a2209814400c2000c0d0f8039130110b0200c030060118014500c2d4480000082c4c034121951400380e14111003281c81440c0c8001c140c10b400314242c1006241c944a0f101e10380f00c0300890003415514160403060714400d812556140e00100070150040c1c50b840005914102201c904500c03031700422000750f00800c04a03030b000c91158004d1800c0c403000e1814000204d05662007a040c0e90000c40d1300401c40c01c401031050107030324003441803c0364510030381c004100440d116650250340c100481c5024110304207101210055488032118600141d41c80326003080349182688110100c0c070403c1c0150801403103440140851814103100d420300420038155101d020b996140682c0100f40d988500c100e080010a20112030034144c0b403200c081503180b003940320f06c96541c103084000781101d404441d00c0c3d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 541440656 1250 541439406 541439413
    0x1507170a020f07150531090621030e01031d0d0f231303021c1106090913030e06040b09040c0903031b0318060203090306100303020d050c1002030112020f03 68
    0x8000300c41c0c041c0081c002541103402c001d0f8031226080c40301d03850b054903280c0c4000b45168046c4010310484060480e038050351400e800400c40c25881750780440e031520407207044400c4400703030070010408240030307007107014075428145404a14501c903c09001802c50900b016002964401e0081e07040031500030f807160380d241d8458a041c0011920008800d0f410000c51004041c00140000e29266800b003030b030000780059a000f41a01d0300308244855406400d003c803807015074110381c130f04018400c07901d007a4085604c0d4a2008110000c95150b4100c0082c48124410044051041c00200a0540d0b21800040c00049c003111880c41d880301c080409200c02d5802d44000c640030081100d60600001c3d4101702c4a01002030200b411401044c190b107810f42d440d10010345a42c1d2811080030740041c1a0390300000a0241e0382041c0d007a00e4180e12015110302141c3c0c4513000050158100c18003501c004e5108001910380d01901100f01d80c02e05001055040c12684282c004542e240e507820400b5055003000c058104031b490094008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 541441906 1250 541440656 541440659
    0x21008060d06020a1b051011090a14030102160309090612021807210e0114040f0210051c060509162703020405130309091107021507170a020f07 63
    0x180c4103106007a4010841c41c0d0105102000b94410440f20001c08400b4408581d0329029042a42c0c1d00c4855044c4001064240000361280503a0882982c14422010302800c4a02d820001245400607400606642565081c0011508a4445565007078280d0003905c40031311607400c2c031910310f0540c0c55640225029002d280580e10058a40c4081c00603201100c8000c15115141c1000c00c94104610182c0400d5030000864044540002c50740000541c41100c4000c00c51161148080550000222009400213040b01801700260409001424503400c5912340b882c606040340840510308404c800c0c01800403035a5103024885070030b01c50521504501c034400512001c1d560424000e21401c01c955004c0c0508410307150818100010b03031807000241d81e00400030f00c8945031800c904030030405940d2060740008c006100014014074144180708402501b000381c64680055502882110301d0140ca8000040d0000c0120001248403028802c03411a80700d80061b075506100c25000307141a03c100c000359030319046841d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 541443156 1250 541441906 541441909
    0xc03070509060306010309051006140111070302011b0b0a0203012d090c20100b2211070803091b0105040602190615061101060603021903050a02090d060902100806 71
    0x5580700c010084402e282d6030342d02c540040300a0704084900820034481c101c2611080f03e1141c1140c0191241d042c1c40042c00d4020700e0046801000442802500760001001030001d544912440014424030404032040500641c4d00e122900100722000151190b01100602a00700d5a0000c03200c0348000c658110300c040d04a4002c1500001c0c0383c031468680c0340d502c0031079810304c50050030341c031040c05251200d21f070a54540381c4265803a02090200e11103614600070400d44249131004502565018000c0401c4004005046010060092501021b10220300f484024001102e40e00214801d14082c00902454070319030100a410900b04001c0d241408014842408895800180499a2000300002041400003030400e40010328165080c0d103840c604801011601c0b54001c0040ba100d0302000000f040b81c03070b075076440440403401800c10040f900341c1c1325072400b44c1c022310030f030000d981011440714010b151101483c0095001481c458046030350b10b4a88901d10294580300743c8002d4030440a00b4000001e2801c8c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 541444406 1250 541443156 541443167
    0xf020f0604260f01090501091101080702030307050c1911040c05040b070639020601092009030106050604060210060f030302060415060e040b160f091a131d0c0307 71
    0x903102041a948446102c8841e00d007002410303c80c00741240200003180e8507091107400f8150303a0b94242c615403440700c5084581d503c03606442d4030911007a0301030760868407516000c0341d903580f20105a0480384200310f0031207002c481c010034025074140300e1085090740c0c0300040c0c1840140c1e00040c1450b0140f003014013040000c000d40300e0440c0c0055900100c001030750703210030121110131483d040b40c0e04610485102c48501100d4501d14100e1054800d408641041e0b995032240b0058a040c4000704c094040c8196003000c1110b44c02c0c015004500000300041256078407100460316a8009502c0312005a000e00c40d030042c62813051044901404044086003440c40c03d58801a590740390142c0300501d581d400d00c6c0c00c00b590b10500d9000f0005081001e800043c1c60a203814405050a02905c0b600e11807955181a581c1c01d07800380e5000f081d0190541c48900e506482d0544800701d0f501c15058441582904004824224011040030005001c0e194502e1080107900e8014490100f4001c05e4404150400c00038002101d4114 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 541445656 1250 541444406 541444439
    0x501090506090c041a12010b120a09030912030509090709061b0c050105070219090204051c1208072604110603010b031f0509072c010905150909040f020f0604 69
    0x84191005c811004840c0a01d102d001050580c410000b800420310041000007064003030140e26508103584c1310076150704200c03800d0140040205000131410810005071036030301244603000303003021814810b20300081400c9941c1103810f00b00088881c0741c24040640c006c4128205600318038200c04c4072451a40d10b080c018021802182c2c18000045451021907171819241603840000b030905008070740ea14030b155006500540103880c411014101c03054030121f40494903100d5a508407840c648004002c11058604900c080d00000800054010450380d10343d10310882c1802c4807c140341c0c5a881c0c905070801d880401c0428a500c0e100311010001080000c840030144e80d0080c15281b03a2581441d080c2050300c1d0740701c54680c085608072020b0410003080ca9048a880d02c0740c041d2600104281c04840d81004012201070710110707000c1a0700070001d2055040413540c09151300c0b000c26920f4906401c19000981031181180c0842c0d50b079030b100381d20008504180081100c255025502c02d400d048c01c0c0b00e031022a01000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 541446906 1250 541445656 541445669
    0x9060504060918020405030a030801290a0c020102191a0a020c06540d050d09080705011e150f060f020a060c051b06010503060c1308060a0501090506090c04 68
    0xc203c403603100003076040328000d04005045600d0154a032030090803001c0d0920896039003040701c42c10885110310320b80240743e040c0688110646032001d0290b0558407010b02c50b000364110302c14400c503441c035401120b4032100b405015160348880c405014010402075030008104100e410700600c008200c8810014030690014418801071044043c042c8051001d50010101e00c001460031041170100300301ca50700d504d83d04208490b08015000489100743d030355001300310340100c001070041100101e0a801035208044803032144040c60318120702d545441d800e48a00f006480301c0081e882070700350744414051041000c11441012a14189403030810b4803070421200703124030f00500c18108030794200785200388680c0d1901603001c50100041c1070020320040842c3c028240e940049050b4620b070918061000520074100e441c0180280f13032a0b5140c0c0e40d080c0d05038000100400c51b0040f144400f284d010001d1110303a00c9149003100006036985000502425908050200b901a45508043c0239a44102600f2070b0203581740d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 541448156 1250 541446906 541446929
    0xd0206071d060a1d0111030301050105091f05030106170f0c0309030d0e100c030203040c061412010e0a06090c0e06031503030c010b010f0206070e0415030206030f07090605040609 78
    0x400380d081d1034208005258405400615010125040452500000311110020080c511000c0054a125480007141400d030790003480108110361045006121a400107002e052403843e01001100a0000c0c4a04c503101080700800144805588441404c04890369100301c8006030800b241114100780001c1c00802d102d44000000403e1390714100122940300c1d41100c010001540240344098032549084641d0404500304010941c04900c41d00070f80b4003442d0003c901c01d03075182c40c0000a5031044804850740740981c2092100c080c5044d100d0b012180204184c500e240c18510345151403004852454100d0140c991908112164695201d501c000a020007034801c10344d40e488a03021444001650417080354140300000d1000024034064109508880007a2150703294000242c0050303071160401c64003038002a181c250850b81a1409030444511004903c41e9081419103030f4002c10b6456000f100c1d05080036540710180440340b64007030030101c02807600740340140c1030500340f980080400c042d0740b140481c3c2d0034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 541449406 1250 541448156 541448177
    0x10b011e1b1209030209070f08061314040803010509060a1508060109080d0e030105160c1e120810050f0d02010503090c0303071a070507152408011d0d020607 69
    0x9011081c00c50305a90032090458035000d0b1800c00400001c1d00e404203d0083d5046c4010640290140c4542419142c554441d80caa550311030050161005480035003140c803644414420b928419a06284d50207070b400748503050f84c2c0358140390038000d0952000d04814020070002004102c0314541c4441003241b0351551130159410340312072004071111402c5070005e00041c0942d51407405072a81150040c0d06c0b2803004d9009001700d580f0029a03001e0b07040508018408100344281c0c00b00014420f0495103610311a0a036028040c4460b5192410030340081c41d9450041540907040c00380044004480c88014001224441c5003042c09802281c00a003900c040217043c4a804804241c606c1020f20280c0040d00380541107948500107401c6c04403001a1071082041092402808104020311480c100c40c00240c001031822001102d045000000b0122280d070106001c4101001c1d10035000328000030340080c81c84900119107030541038810305801c600552036101990040140d0b00d0103d8001c11841e43c000d0a50a2024509 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 541450656 1250 541449406 541449437
    0x212072c0d0c03060c030f0b0a0503060f191a19062c060f031e060d0f14011e1401051818010c05070b0105031603080a031806020408010b011e 62
    0x300d415000100000d04105d0002445d9505910010410702203001c18030203140c04034140405c4201602070650107400260015060f04403401c40c03603800003402840785403808180740b0702030704035100035400c41001d24007904489000d01e05203002101150910b03406c81c56049c40d0030809441e0b800d00100000e4a40c181900e031008410100550320340f060806842140d0b00c40e010a60704125500072203001440200401c15800c80007800d8828a00c50603014111b801592410380b2071800103002d8203411584190304080300f4142d210280a403411a00c1d0444a080e41e102a1035641010b6408111403051102031000042019656020a918149101400c403014603158101e403032410a68085094a240d800c040301503106560000c010030055000705008030302a601c507000c240c0c4407044010520052410b070320b0248003003270200d801001111540e040001d0b1001503030342c04400c5070341c2c00202a1003195000c6800c0004502c01c5c0980d11111400346405540340000551400706404098181000c000320b08881c820003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 541451906 1250 541450656 541450673
    0x5062a0307020a1419080a1509061401030201030c02031e0901021507091e060c1209051801030b060409151a04090503030709080c012a060212072c0d 65
    0x78640281090080300d459004101c00d04040300c2005000baa128031215000380044905c1c5015521500d01400c00030300380c0d0701c070300d5150040303a01003c0c060313560b23800440c0001c2c01d584a03518801c0344031103c680d5290301d10b000150440b0214160b034019034000304504075180c050f0001c9000c2109644c0d03c080d0b1036500e01c0b40100c1c50141030009602d00c2c99803c10a001512b50440d680388111184981780350341c40e2404c890200c5e0800090300c140000705100c004580c1c00038400c1000c0d40c000d604140742c0320018070303030310400140700c111540c9280c15104030900060090040844c03440d81c6c0038070241c9050118581d550785072601c107000c40c0c001c820491780d02ca80c001f0039110000c4201c89140d2008000b401801d8060401e6501c0f644159134500100c0c3c40c8581c001003581001c41c564400490503101c1413003100300e003000302c1d60f44410040602d9060110900000010b0040e101400d940d01c40d130207050310586080880078068080e1030b10901d811185481e0720003000b403200c0c201d24007551010380d0280020071440c80e0031300d036 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 541453156 1250 541451906 541451917
    0x3090d0210020c0d0c0f1b1401030b060a030b030a1e050c0f0a03020910080703240b0f13060e13020108010f080715021e010203100b07020a15020f03040305150105062a03 74
    0x300318641e181f508503800b407914014141d070907040c54858200c003c000150201c0e502e40c0b4042c0d42082090150303d942d240284c0c040000d101d409401e0310007041142e0355990903031000b904c503072040d480905418402c1c040108500c1540c0300042d1048070404a030b940004819071034034480280328400c42000645c03500d144043c81c03001854100c1c126a00b05880340b40101d841c40020060500303e04505013580380201041c025004c0e090320140c40c04030f4254420b024014403844c41c2600125541d1a0a0001401900f5403030191003003801c540501009111480010521201a0f0045030300001841d014040220042125803c03109400c00c0343c040c512218601781c0c10007900c1c040000d1000002c0c000100d42003010740081d44605912032404a0711901d0756001d11150258042c00707900316001901c148500382c21080e51403000ca2041c01101c4806941c0c1c0c1c940d910b076031f10640007100d0030b03041008000750141141004901524080710b21500300300346040340c6100c0d626950b414443c544860401c1b4100c3c0181030040300e0b03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 541454406 1250 541453156 541453163
    0x2071809020603010509090a1a0403080c030f010b0f0906070602090a12031e0e0303030f0910020a0c06241d2203030b2101050f0106141215040203090d0210020c0d0c0f 73
    0x9e000c8000000c41003200317003c55080e008100742900091500549070f007245e02c104a51460141e0300d900740607480e241500002102082d2020800031000541d444001520525124080241e0fa810b000414042d071400300d40e00140e16204644500c00001c0d0f00230300001c2a4052544200e00b245e48526030488002c441503e6080d0035004c00818007050112404040c1e10825091045442001003560b20408a10440900c00b0005d440c4207545000100c05030000c5046d42c0801c02c84080c0c102907100050f11780350b50350f8003900c0c030245100350550001030310191032944208942c90204100b0b201c00811800001707806001810541d6605034514140c0e00c14900300000805c110f242da00001689030782600910080c1c0752a2001c000110001501a10074120b42070050b40d140c0c42c0f80e040031100000c900500c800035014080401c408200c040c183d0302c991000e5840340c0c907400002c2500c080500b40190401d01c1c000b91102c8070b14010000900d0003040098011440000f0f854811040786e520b04002c20000d40717002c4005e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 541455656 1250 541454406 541454423
    0x316062709110a0905010801290d0518010507030501050d240f0c030b1207032607080301150c051b030307060204030b04020a170c06070201020c09040302071809020603010509090a 78
    0x502090750a9014000c0490030792100d413011521740d80191000c2d1802d20454640302485880d0501440043c50b0502e0381c03217210054103040691665500c402d0f618201e640c050701d40c1064410f2a0106002d004181d0840751a05041040c0d50400000c21030342107036004054100b1002c00d2980507108900f010808035299580810041c00d440750701038030003910055060600007410400e103d42946004081070050b2000b0708000c0c030300c1520350351350343c0300c194100c81130800b550708107016005203080c28000070048e440c42480225502d6040c40850300c1004084952402080102d100d0640080d000040c00a91714103c849416186c10003800040c0c614800d80c031005049a001290010421681c4000c060141e407084884440064480781046030070039000d41901b00c80d03400b23001180910b04025009001e42e0380180f060354066480d0001141c4000409d60f0201d0041e0b02c40031080155015803800074040b08481c0c070003481114040d030001115404180901842138011202180038160300b04840d0110740c7c1e000707400c2e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 541456906 1250 541455656 541455671
    0xa2a03020915040b0706051b0a03090c0b030709060503090712060f0605031c0c02060f1c0605010e0a09051f0b0c0610050d1401021c0504020316062709 66
    0x14081e400c1846110b025082418880702d884104000391416103403200b10f003a080c0325464481c03030302408014000100607074807442542d001418000007850010301c19103000c101c071840c0e4078200c017000e1415402400017000510a00c1910390340000f00404aa01c00e103000d64a80e211014904e040c82c03429482003000301400f028440c03c100c490740012582d22981e203010030607141d41b50309064552200f940c215080e0036104860501560042c40c8410700c0300e0020300740505140ca040c10318102a404030004000c60404c403406403881112500407030000e045c080c80c0030030013100c812002c2001507066001d0300d171000d0784400014405003414045074200a00410700440002e544851481c2e50b40d20402c1d2150a50280d40002141c1f0500c0d0031406088030006000c0e1110381800c1e807144081000300c8061304d94695000c100781c203501e09203d41c050081c50068100002d01d403d00380f0405107440955500a4071021036000204010340d00002404041841000385071540603030300da0103110b407540503000b8800303442c900182c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 541458156 1250 541456906 541456991
    0x51b0a1101060e072a060f021308190605180d0804110901030206030601031a040501170606030f0d0804030903051002030f1305030a0c1406090d180e0a 66
    0x40c503001610601008120407a02c8030041d60301c030b2808407500c001084040600c61500320302c6600748001c1080280c4d500f01032450550b640000e82d140038160032005a00440c00300c00314000b901d1800010000707035000784850908002c10600341c100d05207024013101d40e1500007402c4103c1100d821005003d42d10305481d0309120b042da02030000b40c01502c00f40c0342e44801d11504403032401c007620100e06a9400500003801e55540301c0044028010342d80f0f5005858401c41d030800c240d174886004a5028003203d00c4030000380e200480c0014034003103009024920075031101c10306041c540340103d01e6440882451030050003c0e5103e04050724008a04c6d480106284951800c980102040381d000e9802a41e0000e04005580c80b201000d00c43c010031101c0142041d0000c0080004040c007641c0104200d510030307101400c0351144407d246080420444001c0925040080700d0010240d000c0e00e0712680302408115400c00c00d08180d0201da50f8640200010002c0703030340e000c5408034400300d0052404404010000018060311604 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 541459406 1250 541458156 541458167
    0x120d090f06022107050f0f1c0506010e010309080702040e1c0f1103190e0f0a12030311041212030e0102130807060e01050f0f040b07240618051b0a 64
    0x10180000c03440300160203841007600f098018002e0780507550f4036040080164050545a015031121a1254010400c4024000220200c2d080d0307109003000005581c5480c1c000500811800c1030342c80d040625020421002400200c1590000354058400003010f03120301060310300d840c030881000041d000300c1c00c02652290364090350b0345415011507902c404949440f034100c07659170f000703940002c41d20500c998a20041300e4811907000610a5004002001400d03800003c44d0200c070740da8000740c2021641c04c9000d014140c050040d00c400c040c610040c2450315260031454881000b06c0440244030040a2000900d036504c207811a08480340340c00004c5503901c0c10840040b505400501c5807940310300580000007021030052110040c44201a11010b00c0c1508140002c046644425180032081d0360520010a400e080301000c1c082d660b1141001d1856000248010303196004a089400f46017400c0c0751050004011100122822441035940403500e9181c104985424444401c05018410000b00b44a07032070640c8103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 541460656 1250 541459406 541459417
    0x3061701051005060301050d1403041a0409050606130608070201091202010c090501020115090e03040b1c05010918060209031c21061a0d0b04050106031d0a05120d090f0602 75
    0xe46000c007600f03507203d0030f000f0b0a00007440b40b56071012141a044000c1111b50380403c80c80c0e080c85050382e00e0b00f51034200c60708028102104043c940c010114080c001349900c1c1c4151a0000002c903030883c100841e110503152142154050002001a800049540c3d00d000350085080c0c06e0340007104031050a09034400038003c0541d14601c1c0002114a1000240da5006100320218211075001e4242c001d41004061006080f4080881c03901e888208400981c4640c03241c050840d00b50209a0400c070a44952655010f071507042c0c12681d242803400350711040505441030b0903a178a41d40103601580f240f25681c0045c1c00d0880344011450f030017425018081e0141d034800274104860242c91030603d00f0100c0b0715120022580c0d039000f940340c0302c002d400a0413258982c100180c030308120030a00224055580c100407a050750420b81c03010010940711811800c10300c2544400b4000c4074100b03001803c6c101510b4660640d40d580c5d2540d4000b0384100040d231b91480b07a0881d0010002e1940000c44982031214a161035802036100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 541461906 1250 541460656 541460671
    0x901050703090804060e01021911120d080105210607030f0e06090a081c060602010c0f0302031005061305041d160b09060d0204170a02040507020705010801090c0306170105 75
    0xa1800148800d40a803060541450300004002c1c10703e41001d50076074501040092460542c4107048038414201c841c901160302003481100d03111034040c015405d00c003042c0020312000301143c0107100340030203c0ba48070900a0444078110b030003405c980c000040044000b02404025041070203a10100024260103410001d06411000130800011a2401c40503440740015104103c298108491810100312444040c040030494922103400c0070201041c140b0854120340d0000004d40d460300b10300c0548641151001c4100100760409514501d008110890842c241d40100c6204030f10105012a1028a040ba0071020b854007410400590420b40010480f100040c0390741d101d18410008032204841c1050308120480da00e500c10141000b04041c100300c0c068010010112141d80c2c207000c00140000d000d04001910703880c21015010214007030040c0002d44900a10034000d56004070001c00850340d020a200e4110b40800c00001038455400100304c0c06801e503a4020041900b1181a039101940306500a5000b21030303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 541463156 1250 541461906 541461911
    0x8010e06040b130b010e0903120a0c080105061812070504020d0b0f030115030b0402010c061a010f030605010c030c02060d050f01080106080c0d12090b13080c04270602040e0f0901 78
    0x1207001c002c00d40070322003200042130341505030010803809110341891900482d280b07017a603040a5619800141041d07040324100006603c0d5400800115003012200b4054402521a0351400102100c8003800100010000e80a2005400481500242842030310b014080c014001c1d55501108441c80c0c1c064001c0e0700d0020700c54140c000380c2040c2494140b08980381c0385c0d0f91424400c440303442d41c2c45407a03107007000800603818000301200745000102c2c07601c10b5500c03401c07485410107442d03000107000420030f050105205040c0740c501030042c030040c4c0c1c2240a20303502d66854540480300b000c0610104040c4c0c0104010301901c942001c1c00d12503503645d089441348c10307101c64800804c40c1a5890210307030f54480c0c9010540d6085900922090301003006142980282038460400540c007070794400944a1542c41100750800c0c42041040a119a810034014110111030846050202d00614607400f06200ea401e0500b0b00c42002910b14a02040f40e20303015030f0001c04810100f0b5032607140c4404005145001280d0016541d40b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 541464406 1250 541463156 541463161
    0x90501080318131b0f0305160e1201020f030c07020315010e010608041a0a1b02010b060a032a031d0a0b060618031608190f030503060a08010e06040b 65
    0xc0000540b01c00e101c666401510710741114040c4841e0010100c12800c61a4a440340764200401c98440358002c2c2036503a40d01c1c0c400c0840c2d90401011910702902d8601d910324407410044c000380e031120319100c2c4180102c0b13510703110520388401c050083c81074010b03000750910080104035146051101401600b402541079403a1040203800c0001010003d019203031181c9800c00040c440c0f548a14003403948030b032061500350b19512821013908158081120386230012a120102040003000c20f50302c40310402c0302d600003807220542110000307685002d8004401c00300359943d0320003d0036440704607124840c12400d144d6007800204000d4000c000e00b020f2079251035160014000c0c510010070000d00c2c503078407135041071020046803140e10070800c0e07a45c015480300c50b0300403950341d1036074055505102e041d100d800710070240841c607407420711402e00b000c10700c4000001080303241c80800046044900d100c076607507a05207829643c0755203100026140342030b242c102203881c0d840c00d44014900080092801d0141c2c1c010018a000e60303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 541465656 1250 541464406 541464419
    0x1050c0f06040b01051207150302090612040c05121b1f02030306040615050714070b04090b0f01090b0d0b0109120813090b06040b03190908031009021206122104090501 73
    0x11140d00d50184c0c4d547d104400030440f4804040380c03100643d4540ca0094901039040002a00c03a0300089600040c46228a00740801c1010100c5070000400d401d56454150707040141489031100d4100440c02c1129040030985401c0341e540403031000010121518410501d50400f00c001d6503900201c03a107500036440c00301d01048041920042110900465480c185003d0050f6109140d04900e03002030515407041000100d01890700801034005000800000921507a406c003c00c62101c100d030000340e06000c29400c1c1400100601b104681c0010040800820000e11000c0101d54001142c2d00020386c14054040784420004204010702083e2401c081c18030b082600d41400b5021140c80780200c039030160040008000c0e00001c2800307942e00c6403030640e0b2041c5280d00c0384403103030960750100002c541501c07001003001101f00c3c214048030080c0001704001c5003400c19200d09541b500c1c40140c22244200364403803840ba030a42042000da0310742800101c03006070503039001804003025007180c042d00c0ca03400d08100001c01c41 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 541466906 1250 541465656 541465669
    0xa060f02090d080a021b150d060b0309010903090f06080f1504110a02102d020c0115060206070201110414060c0d020106080c030a170f04090216030f0c02030607030b01050c0f06040b0105 81
    0x4002c008005031500340782026448d600100c44d8941154541800103102c07142c0c00080c41c4503480c2d40e000492001c180c2d103030081c0f5078241c5d5085110720321960300b014443c65a2000c00c10740e1013a2100d8180d061a1200103415070070364148409698454104154440c0350000680540400c100070340031920740702c40d0b803608001568200900d114501024211000c0d40c400055a54400c101410400500c3c0030041c501280c00d481a0f003400e03041d2040d07080b4082100d40e40c10010150701c0801c2d0b10080004810703044402c602d03803140b84142005104200c540f40b0440e900d1804903000b02c46803100701c0c0c2145445800280c00b03440c01b0702c150265401800032480d41400c000c905941d805900c0100380c2640054003941c0f50107030300685401e8180810038480030544007200d20041c00f4802000301c4d48111745e040c0d13150060a03116a52244010480780c03c000340d0042e1130015030250003aa0034100445c0392190840100c3c0c1501030801450100d20400140da081200040f4005009a02458581000b6a240c000b804035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 541468156 1250 541466906 541466953
    0x5010b071101030203070e0306010e07080907120215120a150906030305070b1509040c030c090204121202033f06011e0c080c06091e0a060f02090d080a02 67
    0x300c0d8200070024041d03210341d0007150302c80043d05210721845104d80120b131030058242c02c8292004801010711100070f401078217056101740d5200c0104003281c1440c0d080c0801b501c030354000901820340800d02e100501c92640984600740010700566929142500812018003851f20000341c00d4021102c001c82c29480350b0080f07d003600d805803a40e901c3c1c00307590360b14030440d40e400401d03d078140100f8059110070340d6500303480903010f01d0148030b07008442e5007142411004200d40358054050148104010400710002c1c2c0ca55121040d044100600c80c9191200182d0031442101140101300480440c20040c000307042400c0c01c8180312084035000440d00c4421604c00a0106940e180e01040e11030345600c01c81b0303110f810740003002e0038503103050101c2d0130250359440010340201640301069040b600812140c4001003190304160909064094504c1442110a5449491f100000b60809442d0940d2103036080c800d8044a409260150500c0310407809401c1c03600042e002003a8403001400780c2400d025000000032884003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 541469406 1250 541468156 541468163
    0x10209010c0b180102031305190c030305031b131a1e030c07050d054f03290c040e0609060f0a1e050603010803040909080d02031905010b07 61
    0x10724010661900e40411000030b11078501d007289020854120103080c0080e6025011042c0310001d1109076250050414820354080038059040890306c0e0301040c8240410001c4030b8043c00c050340da039102c06d00403d0404005080c011090000080c5031001010110b130100103c6407100c07228000c01c803240204d54058401c41081d02038602c481d4090b80700c60642d0364025074001c2010b2203440c1c07500301c0301d5a45074106101036140c0c8003c9000424944110381001d04079030104040000340b00c41c1c0b08120040100b032084000f144492440403800e070030380b40304501076246014503040313040000340840a0b41b03903015201007134241c00190111400403941c10070504094a0036100008546540340e40c4200c04c0c44400301d0000c1105074806140c442d00341c0503441d040d0061000c0d240c580c20007200c6990360106885001d9003a0b11160290340200010030000700048103480c1a600c021001084441442c18031200714020010203031090792000050004002001030317a0021503446107024006607036201c00d0a01a4022040c02a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 541470656 1250 541469406 541469417
    0xb031e0723011809090602030f0c0a2012031311060a090b0a120906050105031c08180f160e010f06020d032d061404050403020a08070c0e0c07110301020901 68
    0x3442558050b0104041403422000c2800034295600d584c0700581d1382c454400d845040d40001402451005143d01c2940306010003203003460010ba000e40245007508140d207502c1d46101c000161303a0281020301420b400f044405841503100d04140302c0a840c818001d5800721481e035400f1f2820300c22801c0400a0310501105070716100f0f45146061a094840c0d4004005082040100015242925802d109030301c0118051900001e40d50b0416003030603d00544030844680d0301c481c540081280d0760b4015100c2e5445035040e0514030200488140031407802100d04244200c3d4021803402426100410007000100c8800000d1703640d40c0d036603c01045d0b107a074031240540d00041c0c008130203402c1d10a00030f4200101c9001c11007e00e2231018400301c950524089007880d000710b280c1e1503000821401d540032380a8000343c01c00b01d504000908059402a5a510031840000e00300107020809409011b1440644001000c03446510842890008101500c0340d100d032408440d00c0c03a0480c09501e007400c0520aa40c2000010b8490 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 541471906 1250 541470656 541470719
    0x316030b030706030207110a120c05012c03010204030f0503070c050108071d01022e0f05160f020a0503070605060111060c0318010b060f121b0313020102010b031e07 72
    0x44005e9800400242c0b402030301840d4a60030340d00c0f00300c9090020000000c806044030a51b1410f850b172007442d50f02c40740c1041000000700001c0f10030030404582c44880b008800c08100c01100c04030303000e401143c0c000743c2082e08503035440090000200040c080a0722803c0c11141040e1a40019155120b0589404000a019180481d9a0f101c0860803040b4400140101d94050140e89031156015040481d000101000b090102e166880d407409103a4204c03062000510040c602a2003c8103001d00c1501008101320000c22400c030703007600a210f102a001e4200e0300303807540e1b0411030500c40041c210036226180011607200840d0b0013000301054441c002c0141801e620325546544840c00411740040000607040e5580740e80e401c0345950751100070500c24801000c00c3d03403105112210b8055801e401420145054000e1060b2040034030642c0c11298407440b08030612000c4455800100e0050448c101056054414110034213009243c406442c10280d030003104440115444001c00884044175859006052000d04c42 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 541473156 1250 541471906 541471919
    0x1703030403120b0d0b280e03190527100806010e0f0a080604051c0507050601090911030d0e0916021902190b07030306060c0b04060f02040503120316030b0307 69
    0x100f4040c0101c018003942c5400107945514040100a880a042c0d02c44101c4007400c464400e03098048480710741403410406250001c2807540c0364828241441c00c0314060814142005010b00c040c1c81803001003203207809200c50001c08407000e4a404d030a01c1d45c0715a80c0203581c504014461000a481800d040c0d4840d0145988542842285034602030074607070083c0c5424002c149a24100003092007240a10020041c1401900c0460542d180c0c4032003150401401b00850004180001071050441e0a032150000da15012410a4039140d41c3c60900c45905001c2e5030420040140d10002409082100316410003032a1184400303103500d411744036003840141e0018084544100d40400d8a4060107001501d5034100e00e110640c01c003601c14540e001300404c1c40700844c131303282403550621540c0c014060f241031000215010b0b0700c07100d1034164000d00003400036407212110081881c05030140c8000b060054200c80c80111510f407800740f01d4200b242c0707008200d10428443c4071b50902ca80103c2e08201800b5001d400c40d6803c002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 541474406 1250 541473156 541473161
    0x14130504080c0a1a0705130b0d090602070303050a050705130501050309010e01141e10090e0f030a030c0305090a110d05071e03050d020f030d1a03070f170303040312 72
    0x144281c407458800d20580000110030b10544940b00d108800b00d00c2040040716043d072907144041c0c681004c03c0400c2c415200450b003401181410703503c507a03544503110f2000810b0b20f030181010386d0009001d01c0c0085030010801d40c140d0001c42c01a2000d02d0140069540c50000b2581d034007503040d81400010082c8010805940684000c6802201000002c290311001105d0385095840d803524001c0000020001c020b002c40d180d1007590f0b00c1d038022000c000d5083c100504400201d02c000d000b0925420f030344240500c883d260030041b01d0707907002852003a2a00c034407071110040c000b0114640c250010034144000200f054002041451a41e0350001c1c807440b9050000082c40b00b4080c14601c120740c82d102703616001c100c6a0a0710b1004c008854058602c60701d103030861421906140741008100d05540c0300745a00030b07486601000752003030441031000000d81300c076400c54a1200009034001d1650980550070000c21500320050951b026513003003012403c171203501240520b07580c0c40704844c0a00002c20b2121117401d00111038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 541475656 1250 541474406 541474411
    0x1e0207020105040302090103080c210a08070c0501060e01090b0f15090612160e0102031611010207030b0a0e0f0f030403170702060d0e010c0e09190617010c0207141305 73
    0x42c54100e04094480d8045142c4e00d42c2030300296504200800c41d0b140c0700d0303002c02000b481c5650280d40400307140b00c00980513005000b440300034010700c428035002501c1148106440441560844024410316966030010b41d0600c00130701509030950f0a161080243d8107180f91400045d50300644044240da1912580921a4100444440e07000c80e08018011f143c107502d8100500a48580230749131084070729030702c0103480814a1203205041d50810300c501424101b4031080000e28a1300a20b00c80e82102d9140c00403824046140c0004020b5400c1c0c3d030a0007032803011644040003022640b01256030015414892581d940c41c18030885850303a02c204428000a04030a00c503401e280c1e02103040d14100081d0381e001a400341c00020015000030340d5610090500b00003400342d41d00c00e0720b003410130703064140c205030200d084101d0042189141d009448108001f402056201100602210318400e038846200d0034614003815034040745c80e0051044680128120035006014984408000c16048032010306035086000f52100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 541476906 1250 541475656 541475659
    0x506160e03070b18150d09060f020c1b04060b0d020904110d02090916020c0d0f0c080a0b1e070c050708062809020d0308150a090c121e020702 62
    0x54920100541d00c041000704040d2000b1010103072509100307061820800d0a240340c0f50b1048400b00140c1111640788403c880f841120250040341602c03032420300402030603450110460f042d10019900c034000c04041855032104204851a1103604050020030054400900481080c8070b02006650641d81455006002e0008050700110325000d644041d20b240f50000e80d034100c1d41d260005040f51381e0780b410140442c0d0108900340181c21804098000030350b04c000c4000740d0303801641c503c0300500a1020025680d400c3c9980400c912001d15244d401e087d031203d01ca6041102d04200900100700e89800100702011821040304484400c1e545000701150721442c82441960103000740340c80030030b03d6007003404103502c00d020740110024841ca4011800d08211500201650401d240080840041e9500124900020340600c0c1176611170b240e0720302c0042d90000c07241d1a95803242410300d000540340d28030341094404240c0c3d921013031405c0c0a51009030b000c3e00d144882107001c8280c913040c2c00496004650103000e04500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 541478156 1250 541476906 541476917
    0x506011502161d1f1406040e042306040201140a050c06280e210d09061a09060901051324030512070b0604022b050f07020a050616 57
    0x41940080c0d02030312140c001c242440e82040d0802c440c141e40c2e0803100d4000021404c03003050481c1800c0c0c558001c0c030540c0940c0c20420009001080140e58100640d40604411519005281018505182800041c42000480b5460180207001c12500810780074442c0d034040c0c43c0c030f8249500030a10115544d001c5e18614050280c2070010210b102010402c640c4200c14280000d00c40d403002031007809000709419240f1500d0303400c04095081507480800c40070300e910034140c001e000104101d082d400f42401801c0c4c00025407850400000140a520f4000100640a480d0580120001c42040c4454a00101c4003d504510544c00410490070840b4610082940607400011040d0352018450940c1072172041300c0c1c01540b4400d0f0144244003080c401c0802d01d242c140c18803450301e025a900c0103290940204464811540400c0503014614607a034a96205990810003460200454220200410060303450382d030811454400219030f5070001175009a5160030074010712142d1340304000a940040b805a10904010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 541479406 1250 541478156 541478173
    0xc120103020d151811032103100b031311120303070c030504050319060606020609210409180c0e091018020303030903030f0705070f0f050a140f070b070506011502 71
    0x1081d11950004000e410800c10310f400c0103013091441140e21542d8035200e50010200d00c0314064429003c022200c0c0d50103007c81c1c49584440e0040c04129140d03207c918120400020418044c41440d000e007103061180c0c030a8000b10302da03d000d02c22502031a0084060541c41003000c14a102d000d00e43e1188068030034504507103450b443d0404241412803104100400ba403c080b210000c10505001e20b40140c640381c401881186846541c0554400301640b044240c0d9000383e11041200032208200e07009003000c504180101440d09000c120456036040302610341b4004103001040e5142c01c2d5264900480716180101145e180e01c00800c1c004104010010003043c01b0a00700d40b005031001c2c40990b10605a05010350788a180080701107c0e0004000c04810030003e040180703c002850b0201960b100c503400c50480f0032a4181c40c5031440c40c01d56142c0010380549000100108100d00005001e07903001c07482402d80340e005135220442e03542130180306402411900008018414031591942424405002e4412501d920 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 541480656 1250 541479406 541479443
    0x61b0c0312030e121201030b0916060c060e0c030304231002010b010f0c12050f12010312020c030705091b040e07030207021c020d12121d01050c120103020d 68
    0xc550a01c41004030762100301c2199940400d0200c0ba40c6110514000b51804188801d04074282c00d05000c0140b41e80b0b04000452201d240411900c12488400006100b01075280c80028102481c825000c90710309003440400c40304940045240d15003070401030000d506107400c10f142d0514210382d0392044c605984001040d145a0343d40c0f0030041f01182c1c6140c00001f5040003a070001040068030803d03140c184501101014001140c881c1019884070551604503195079103020b4081c8241301e40c0d41c65401030304240001005100c0390881e40b181c408440c0e02118084044103042c1500d80809100d1325034000d5035240002c1c044900085031184070030002416501c0c0546440001c0301c004402d4400ca00080e90101d00d62046042c09007013641c20300ca610480a44043c0f440c0d00191210304d408000502e01c0c0c181080c22850f03140076912590b0300310f4604900b4480700c2a06c83c11200b481c2008091918550300300804107034900304010448202071401e044075000c50f801d6070240032481207509402c47c2d9a984440141814 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 541481906 1250 541480656 541480673
    0x5040908190206010f080d230d0f021308060c0a0302090105070b041220060112030314040b0f0a0902060a031a0a09141f060809030d11030a0c050c1b120d180807061b0c03 74
    0x20f0ac04801070310f8104265200c200f140305174002109a0744003000b482071450491050f01c2d030100423850050b0307840d0102c41c0100c4035405403c00c014140031114060004110f04001c181800b0072044d6144040582004c80760f40b0170001e44079250f0011341119005004c05622000204c260030f020b802c001c6400e1b0307002c0c010b48015200485040c1c0b4801d07429030030300180901031411183c000079100014028500c00c1d80010710b107031040d04420310034169214494560fa44c0c62660015480400400031a4000e40c3c0310620000341424007600780c199804a00000c6151400e090354140501090028140e040d090850560b440080a0403002d1180700a00c1300c410079507107074091844009144030301103407242001001e440c10340740a41041014400c06001c20f40520400150b0000c070200800000176a13240300e0780c081010141c484601c43c541d03004400800c09030135005410b410800b06e590389640d403055a10070410342c48001ea80140000038002c00403030820b0702800d841e6100124011360061207115030740d40c4c0c2c4030071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 541483156 1250 541481906 541481921
    0x6090612060815070f0201020307050a050d11040605180a0b032811071b050913030e0d051c0e0d110102010f0e16060507080405040908190206010f080d230d 68
    0x158010290410920310b1780442c50070b804401c0c5000a50035400e101c00c018104d80140031910042001c0030602e1450300400d90405203403940380440c06507541b500c07610002d0503544140e94032614000d0414200c011801c001480b41c080f50100c040d03107400c5484030315513248102d0840c4200c0104610034090f901c0104d02d544161201000d92030071a5590301c4440c40e00b076043d900c990070350050106890604201c01e848055807140c0c848200318010f080c405245c40c0079100c2d0000071350783c00c4d00004111181000c101001070b4600010702c10030380302055148514801c48014203600500ca410000041040000a0ba0032240b0104040140008900e014031000c441c012540160726039000f0f513100c0504e0040c000700300050140501440e28004c0e240003000d840b1142036205a115550281d41c0d120943c00501200c801035907110042071042150a4918140007903880d0001e000b50350104d00900c100003200c1100060400840b281922405003115402010322407049102406a10401007008090274a507114855801c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 541484406 1250 541483156 541483183
    0x3061c02120610061d0d1403160c05240a08040f050a0606060305181f090c17011a01081602031303140706090602070e060a03021005091009060906120608 67
    0x3072100e02c1e00c08014408407217900c40501e030141658403031740c4640f10070313416011494109040700b081d4000013011514520942c2108415514584022010086001c010200b1988206d9002d00c2e040e0308101031039450245207081250301ca104100c401d08035030003040750310b138898050144150301002035102d05040c00c3c001d00c802c075942a51450f0510181ea014490203800544180c25900a030388404911541c0f031815014501c0c0c07a8017200034400024510340c200e0710300241c0c465103000c90f81d0b5440f00310458810b01e50443c41c0307031135003030200c0c04400c407680000c03501c90359605030340d0b0003c55125041e484040641940660702180030412407030100d841d003000380400941c4141c8d0000801040341031024200500c2d07401c030004201104c4410464107a00041540603240481d248407120b46030880010300e5010a43d01c029001440b407903050b803015070044060f25940b2020b48070f0003450031442e20119027034030f058013030382c40070070481d0b4014042c9900c01c401d10204202800c40010343c1075141d11031103207000c0c0c0808104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 541485656 1250 541484406 541484431
    0x100b03120a0818060105030c04090c080a03120c020a080f070f0204050705090a0e100b0c031309050412030b03100930090e07050a030b1f090f080303061c021206 70
    0x100e04030700f650025086030400c0344081c040765418a030000383c40700d80343c09100d4032460722030000e041400343e1045004001c2603100101c400b070003400e1030b0250601030032043c0012a21b24001c00303950300c1d60021400400300c6600c8a031051804440c0004100766400082e0207481c00b40c22001e04400686491084601485040d2109901ca244560420680840980120000c28048414803203950320041041060306e00400701640c4989488007460315501407200e50b400c404540140000d10008907611a41c001c90042000d090643e40707140040c1c064500f800c02e609d030980d10220390350940c000c559001036544c51007015014281034000c0c2090b120b0754240400c241502070a040c00800b07151300b0000010062001c0042d251451030a0308014000703000d440f000703609054413011020740c1aa9401e120b0308608800c400c002e4403240144c0001054a1014060300303564219000d00412544400070549105401c02401c07080140880950740c0c100483c0c02c3c4007242c0041c8a04990b5000700c2041c04030a10420045450 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 541486906 1250 541485656 541485661
    0x121503060e011107110108041b060302040f0605031303050d1d010510050904030512060a0b1210080a1502160807030e01260f040c180b0a090e100b03120a08 68
    0x151401c448082c408520b40d40f404100c2c200c0064000341c07111030109000d0800b00e44035901d5046c44010000320180104010341c000b9004581a60954060419140100702443c003c0391981420f5070607100684101c54100b50300044600040c3c0f141c00102900c40e60004041440d90710047d1400001035100d500b01da030759460300c0411050510141d030160081c1000c907152080360a00d610041c20502c0380071400d101c8404e6400006115455452030395000b80000300c801035481a0001100c0070802040d69120b0100c3d81900340001e00c02c1000800460407600550391041c0d0090f5414844029800300145c0150810384687c0140440c00c403c02410140b400383c5c4601c001100900001071407290856016a00b1020b1100040803d849201d1140d07806000d01188488640b91400e15088940d147d511013440c02000110711402d82555401031a249241a102c8000040d101c3d28480155081d0700c40001007580083c1c0c1c9083c0040c5a5081507105840280c181c46038840d036403090802540c0840d07140d102103040c0506 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 541488156 1250 541486906 541486931
    0x12021303060c0507021305130b1503010e031905030a09060e07060207050a150305131b061103030702120f1603090e10080709110c0a0b01061205090a020112150306 71
    0x9900d44a10b4286080751400d01c0070703400507612066032070042207004c0c0c5d1903000880885000a00c01111031300000e14040b09d240c41e0385204602d82c94448424042d500345445664000c000005884801508001d0b2032a4440342400894a6030402048001032549400b020320207c0c44500c6543d40e41800d41020300340d02824500c000e4500061540490300400e48103e04205042c1c031440d21501d4902c081c1390215164a4510080070040241c02000d80414401991a00c800300807071608411902a5210011001c00d0560303490b40707c0c0411a80100560005100c0e0606120341030001e180d25031300070b8041070401c140000b80303210081c0d10080841c04101c10550a100d540095260070703a10aa42407402e07841d131820705a0103615480284203000ca0340d5100c050a60507085a001940c01104000e0304440110b0341034148171003140002c1c0302d4580452403490000c542c004090098030b2141e03541d05c004103100302580d4011248800580d80e002803d61751105035440215a05616000a500520300070440900000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 541489406 1250 541488156 541488161
    0x111201050c1b120408063108070204020702042a051303020d050f06090102040e061f030209060c1b040506012307020a0312081006021609051b040306090b0105100203090d031202130306 80
    0x40f80c010078010380300d035000c0c0b0032956440c03421f542c4d9488201c03107880d64890710228019008600e4020361203401c0035400407440c001d01c00b81045001c407810a050f190780f01e04400391501d20800901e01803041c001007081c03000d418072402058181c2d200c0c0341159080802c4110b443d080203030690346c00f00c850750001340810401c1d480321105500004c04854002d04240e0302455158101d0701c1040c1e800601da0041000c00345941c3d1041500c220380900016a9030748801c108000d01c540f0801c4080b01d204d01e287c100410b01c1548601e03100305900d0f01c031003500204460356410a106a402140c41264000901e8102000045040746403000c8924580c84000303403800d040705151907090094000804551000f11306180a4031000307403220445030701c4000000c86460360301c61a441402c0c109041c000d2100005000400c0103007542c080380801d801403070003400d1a6224810000c52a503c038003c10b00592080c0f1484d24280740c490820308201380302e13042200c0014041c03542841641c119420144985448150030001d00c01b81c4e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 541490656 1250 541489406 541489441
    0x90a1806030c1401200f100f060609050a14030a080703020c130515060c1903020607090f031109060f04060f03030215010b0316020316111201050c1b12040806 69
    0x942e0f81d40000c40080001c11803560109107500b0801c4500304a45455030500610061606420030b98445d82c03103406803600500a4079592000440c41e01c003002601600c22032500095500007060540c00525010b0408190289032041076858002d900010b0001006500142400c1c3d120f5000341c1103d00b0840100980380c00104100301240b03081800b008008000500101c805620898200e0385500b0380300c0c0c019203005400100354041d01c1402c400c20080c90307000103205110702d41e02d03510b2928480d03c681415942c1c600500c40200809107282410b01c00345080052282d03c510050300600d0381441e480c0c005826a50940d0260721014480d48041c02419814010b4007103035040842151000c1d40b5000725080948070082c220082541f09403082c2a12500c2801110008103c03e004480c0550180c140011005200280f45108407807e1410045d82d24042c01200c1c0308010000c1c03054100351a171f03018490007440c10300d00e01b40d081c001d21142c0621200d64002a002800f103140041c401483c0450011055031810b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 541491906 1250 541490656 541490669
    0x1f06080c0d11040c091e05090114010e0405041509110111280212100f0c08070903060e07050d050d030c021207030302130b0a0c03030b01140f090a1806030c 68
    0x518445001180c80e01a40b8616001d040c2e60009007952180e02c04c481044031504200d154900002444802d005404004410b40780100d92102d0030366620307484401411041495980030655140c00b4040b9841d041d48982c0c0e200740505143e117801c821000000040310020101201d100b0110101c100c0c9a580c0001c0c008610454440200012130040400100090303004d042c5010398110250b49400315101d807081012a01e080c0710484000d003100040c0940034102c00b0480410040ca441c9296000d54420308000d80104110f03154280c0e1305003182c40c1d58010340444410207641c0d1040c040300040680324455604070103070103036014050a81e0000c10040139a0410403800007154406207400b00c003210402d0845404960500b0010b035241e040015640c0c0d200c0c0d0542c452201100c0c08a0f2811205400003440025944a41e0b800c10590440000640f900c0a0302c504507048028240014032a0101002c010314030700707400400650300355565043c403c0e02200c1d210a8940700d19154041001006140e040300405040c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 541493156 1250 541491906 541491919
    0x7050d0201060f05060706050c090315040b0c07080306010c0606050a090203040c05030c0907030509010b09090a020109081c0507140a03051201060512070c06140108070f0b03090c09091f06080c 84
    0x11344800904a801004005400143e40e50f0115980348400f20841c0c10422018003640c03ca0f016103036100c095041c048500307403031b0310644000107421038440c071040b41c04144d8030842c3d56095403556001114001c3c0514400c481e00c90391440c02061b10741e03031100040000c0441407030159403481e1038074140c43c1c1090b49500c0301b4007aa0060074407010303640d6a0110594002c956250004644e690411321501601c41201600d1300504858144540074001207241c1031014000e8894900940d650711481d03a40f00c03110f4188000313020a100501e0401032084000b80803040c029142c400d4075200f1142c915080c0804414100c2c0402c0d00001e42001c2d118188007914018500d50a0007800c01220355030b84d401c1c4200c01802030b42000f030030110300c104010850340064650480c3e107800c1845076865104c503a544241900844040106030f420000e10000f502c0704503032181038008040d1000c03e00b540c0500c840010043c0560a80c3d000300501c582e00e01420141407803024250103004134840e4a005080e50820300f090005034007440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 541494406 1250 541493156 541493159
    0x302042f16121202040605090315090c0f01030207050d02070f0639050a06020d06090501080d050a091206140f070915050c031206010e0306040c0902180607050d0201060f 74
    0x71411016401e12a003000c1020300041e031010089039107400c680c090b000d20510206010071401d80c0b040260025800540450f81241020f2111448440049a201c04e5561140d02d00c1d0406e410035007004888840c06041c098182041541e52500382008030b1140d500590240008009520380300e402c1748000c0c0312074200060704107000d00001c1c4803240001c2040928403000c0d821040e80d2103e41c51140680c80d0003800303840744910329241c030102031741c00800e00c001000d00342030340803481c441144990350484000030000e0155079403407074068031190051400c072018000c3d07a280018008008400d41041c0c41d02c00c4d4030000c0c00440c3c041d02e1040464000d0410382d40f500100e01005081500080c0d000103858490301c0b903280f04400090200d5091007100402036140c040840e10b001140dd0750040c55000301002d0300c407800320102c10801d0643c1c0e40d07000c8902a0814002c0c0400300604006076000700340428040c40c02d4020200c0ca0f102180aa50011008484c0c40d0b00020009144950a00c46e44000d0000d0b400030390b0556 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 541495656 1250 541494406 541494427
    0x2070b210f091b030a150e0c1e09070903021c0212030406050414030304121401060b03091e03161115070803041401060b0f03090c0105030106090b03190905030414060921070302042f 79
    0x300d40c00c03818072b4050b4641c1408100824001d944c0726004560060540703041001e0400d61480300c40314104100d01a110900e035600001202000b03403016516903540f1207007883d05e080b03005003028100c0c2032656010b000801011450b000000d070031100701800303028515001c0002c100c9103401c5404642c00320803121404c0c424802c4000b8089201e1100d400803403141140c1c80446288c80d410361140341500102c83d0081801d060400442c0ba000280d840d40845c0c1d0440144540200000d04c2e1080d450020f00842003040000d000880c0d0031818001c85c15151300000b406d5071160001c4400da8410600243d10b0301d070102c02c2140c2030310100010712500d0030a01c0d100b801c55141078809013021403140960302c0d030540040000361644442900c80da000102d1a1024007055030740741401e030f1f1264405d0013412100c0c080060044c000b8203042e011a248110041c0100601c0340403801241c10100d102407210015000f82840000982d882d40a00c250304220409089030304000071031540b03000800b03190b80c440080350501c810380c1310 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 541496906 1250 541495656 541495699
    0x2010c08060d052a0310090f081e070b061201060503070b07152d0203040b1303030f0908031014030703030f02070b210f091b030a150e0c 60
    0x1400640703441c1c04602c42032620303a0800b456078551312010310780c0019840d90110402da40120109003070f81030f103054441c0700042c2c0d025034020781000741c01c4042a54030301001411140040102e080903505012480d404a0062001540100400d56000c0010400e0040d24a0300301c0248000c0701c4900c000300221740c50035000c02c0c5c845407140b1030014a200c011900d03000b84a8070004003030500e080d00404100000300480c6800d5124110a14000780182c549514601034200344200d80c0180d030410740b11019959100c1c1942e91081c140d5074118101512100341e180140000e0181004882c452a141500ca2506800050490b1103e80c009403440b10b45400c0708060340c47c0483c02c0700c01d4a0301450801c40e0411031103010780c54400d580c2d010070707580c120000302001490700f42c0e070800ca0b07001820401c00c1583e4035025501c0d800003100f61003c08441c0c00c4550310840403541c00d152200c1111024040c0c0d1000d07021920f50910405200a1a007207c549400356400c030360005016680c1a048200e400c8a00074060f098510300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 541498156 1250 541496906 541496911
    0x204110313111c0803090115081f29030c0f060d0b0109080a0b010305060f06060a2a0b01240512060d0f23190b06040e010e1c02010c08 59
    0x41c40b001ca4144038801e441c2c28039401c103840d81250056480e89503e1500c0d990744c0d4030031100c028540d403800c0c049002100c3c00842d11403c4415001c02010f1801201c02c0d4035111030894105003c490342c0e02c04400b640c8400e03140c03801d055422214108000c0860010034103042424440205104d2007022011850302d0342d40d03809403202c1c900020400120018a100143c0e07000700c554001c007006100d006c000340304004a85a0a80c166445001550507980707030310740c8a055401081d00c0050344800244540009684906004440e1039000121400c4c0660003105100015106086c15120681610b0041c4803d000324400480302034200c54501010040400b401402405451902503c56070b90802065981e03403645503040010350084e098060b800c20303901c2e1030022914185011100d00003d81544501c0300004a04444040c10002c5040c9802440d5030350310054a10007080c4961144c0e40743e01704c0519801c24850080748142c100e006044203001032020030700d9401c240404008682c140031541038401d510010254 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 541499406 1250 541498156 541498163
    0x405100e060307080307150e0a110405310201080603030a05040506030406060b0f191106011809120302040f0e1501030207140a061b050f0306090403120e03070204110313 74
    0x50141c0700c80c400281030108a80c042d64903880007244440078800b40d200e05c0541804040d00c10040301407241c1c0d00648988540001508070200414400443e040c5508040e5200120425414071244c008050501e000264080719a03185800e00c0f8103011542c02685e15030b00042d048000f10300b80800f142c0000c01d54460703400398600440c1e0100200d4104016030f081400500300401d44252105a244030010081c1c20070030701c14400b1041d441e4913040041c0100508411030100c90080c02c00e5a01f00001c0100e50642c070380384000f145545d81c0e075507008110a840e0070002801e41d030b900035950b04c0c5016045000111075401c41e490021200090242c44400350400c0d07401740200f8240036031252076078102105c16210b040c407401e15500811952a040001c030740d01c0444040341c00c0c800010186001c81f4101ca48d0700030361301d070f101c9203403401c1020940300e107072002c044c5910521a00e001c80303000040c90203050a8406c1240212015031012800300304624160080c40e16030b90300703810542d081d89044000c8030611170304000040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 541500656 1250 541499406 541499429
    0x50906041a0c0604081905072f030303010b04030b0c040803070b0601030b043b031605070f0602010606021e0c0d0809120f010525050333010905040510 66
    0x103824607400300039103242901201c2650814134060074190a254004104511344503888501d15500c24002d5050b0f07011290010700b280700417403202038190384601c1c0040c84066810785801d072195069030100300460113000740c588120344591030351502030052200608030703c2c00c00100380000d0008403800002d1700c42103604100400c00b10b072504c40c016001000c11103045078001d81032100301603a80950340359120390070550040c040205030301000c401054030100665108070740c2040180031810071100362001c031402d00070006d9524299441401c0d003c022059405040940d4480000b00b1060b80c05014030b202c020714a10f5407014403d0b841c508551074100b1400300d58491044074034000c0600010a01f65564180090189500c004020159658420b840d1005280c1582408002002d1018418652014002307000030b85040140d10201520940c000520140e0000c01d83d051140c264112081c440c42040440b29101c05c2600384440010262a00c40c3c00c90b070300407030900040c00000845540d40904603401501c44 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 541501906 1250 541500656 541500689
    0xf04060c05040509010312020f010b0a1a090612151008012d080102040302030613020a060804140d090e0a0e03090f0103020c0a0c0509090a03050901081e0f1605090604 73
    0x81d10680240d41180c0d800c01003650003c8100203041309041026840b6800301c80e0107010000800b8265016040c055030407580c100340c03c2010301e0100360010324410210b172000d428600340801242017a000407420400c4164104107114100d00d5828030256a0368082e200c2174003054000030050280301040c810400388030004c0c0301c1d00080483ca0381c4038400519160b0071703c01045686040c0e03203020390070900041c0e20901034000881c0c502c00450400400c52503001e080254118a007180507510118000e100b40c032100109108404840c0c0d06101c0700c070340a81c1d07903200d80e900079040401e583c28581c4010301281d2000d140046083c81d80300004195a4142c008640c0306101000403c012006401180c03030307a44070b6128048480c0c0030080c810b1356540a8900540d40c1c50516a968001107598046062000d0b01044042141e10b806510400d030669000750300c18298210140080023041c060b10040fa4800110040305040c454011046000e20b400b0b004a8a4914141002000000c4d00c51040384148a0055050b000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 541503156 1250 541501906 541501931
    0x10e15030c0f0d12091a250201090f1e0608060d12020309191703130306090c1d070f05180f031203010e0103060f02030408090910050310140a050f0406 66
    0x101c81921940c0016040d8210500c05405030540c8800d00a014202041004c0aa43c102500e0241e401025485501d102d044e4a59504511f2000c02981c0503170403c500740a01040c00c0c040c541c81d04c030040151510b2a1940e4041440248900034190840800c0107944024040196a03241010b01c4003074214407400d8501030760a805a103944544500706812004910bc0d0b00c205c1c044618003501159041200c000050031101020354803403180c0c40189011005484091021904651000010070f204200084640c0c2d03e41020040700100e04800d201113100b00d0040000c180d5000300000600c0b0b80354140503003403400c17800a0390307940c86544003c2c0d40112422510140580c0e010420402101c0900442656075615003030070380b403c1e2600740010384112f4100041d1050b25803041c0300312803040307030003211860901403c10200306442101910b41d90f80160121008100c503a8180b080e1120381c0c4210030000391a00d90041000e00c401d0004200f030700040d181608000300542401312031580705074400790001c0c3d11054001e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 541504406 1250 541503156 541503169
    0x302010e0f040b030f0f070501020a0305180607020a120204060902030c09060c1603050601030b011a0f030901110409020405041803050901180f0f0806091605010c020f0603070503010e15030c0f 84
    0xc1c10f0070342c14452040c526070f40920225070714003410240b42c1540c9241c0c0c0c075400107a1340c41010403402000554100400038031944140254150030200030b100b540b800740682c00165400c140e6410040790480e442c8205004c41c90306100e0f90000300101c4900354114a07144c030001850740035821075540078800020704810214403d005d14030800b1600c0754650081900ca0610b180d460341c09020481c3e80543c100c00214021170005071042c203140210f000f107450f010342d881849026810103080d1180355134945240100d0100080081c0000e40600b407401a12a845c2004120581740c00c1c800698103005005141c0700443d03408411075071111801e003411040901c2030030000e00c2e0300d03d05078040040e2050340d00380440c03a2000203514208503054101124044c5c0c170ba08000c1c0342c0343c0903016946e00303206002500c10407036940175040b585c10150000307240190022521001c40c14a920843d6005c0000d500000140500702840c1102074101b013003818000e19628011000c00d40d900c07544111103202d0340d0124141a41651480c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 541505656 1250 541504406 541504421
    0x50a1401090f0306021c090c0510021014070e060702061813020705060f3405041a0403050d140d050406090212060f01091a04110903030a051c060302010e0f04 69
    0x342440102107591341003250003900303c1e403510407049004c1a24440c003c2d0b42d42c080c401201d504100f52408051401e1b04103c0e031264580d44000960142e200c1c581010041c51069582604270850600043d25020303200030041b51050122504c6101b09020010250300c40740d041d81c03200101e04481380c24811000c0d0000750901d403c00000d01741d09000145000422102080081c00380300c02a8441c045600c1d520441c080022010a80c40740f01d60358a0281c9456000e001c2038000d102d002c5040161038503840e401400380719043da9045002807800041d080040110400400e40c010450b0f1a05080030b15007646400d56910610580380740f925111000300342032081a600030280f541d801086070420220700c2c401d50791140340807510b4954005088000140540303071402a103038105840622a080c3e98000c50421009210091103203000724002c4c07208602d552001c000600b1019040c0d100c0f50b4460b0941c032040902c000107034000614150902c401000140d07040340881d40d210070104e40c1000c2e12495180458008c001d41c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 541506906 1250 541505656 541505669
    0x31e1d0a0b070f0c0b03060310050601050c0f0a050d171321030f1d030d09051507090906090605060702040e0c0a09020c0111031303080a090503031603050f01050a140109 74
    0x107001d00c2080803080001080c14428541000e04ea661001d0b4401c00740400c503181c0e038040c1c201c0c0640031780d1030b0303d19404298014414104503007010700d48001185840c040d000071500c154050b16683c8244501004490000c1d001480d110f0503000c01c4606503181804044c0c00180c0185000b4500b07010001000f0110a0148000c3e408003041658680b006001d0410300c00c1e240700c4141b0300000c5200a000e08401e0781440b50245008503c1d0800201c0b000c00100078001702500d2030300469100030349c0440300d00c0801e80101550758600c840e043c28240030000321640e55000421340c0b0700c0e000c41005113881d02416a8009501260000340d02c100400c1d07030f5070500022011855000a4042006ca07010090740c0c00340c001003103944002c00c050038100c01711642034841030301d221202034502c82112001a2084604ca90300c1800d980b004504500343e561414959001501c610448072400c110030255564140703c1c10b640841801445c42187d450140401c03240c2100d4050001000c0103c240c004d544c1e4010130064009090 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 541508156 1250 541506906 541506929
    0xc031207020c0907200706050a120603080d020306030d05030105030a0f02060d060b0301080d0215130c0b070b18010c1e02010b1909050105030304030312020d0621031e1d0a 75
    0x6005078010900101e5005c00d580810071595010000540001c8000688040343c890520308200781d00269041c0e07542081442d240f54850f00040300180c01007001d801c8a9050303100241e1203086c900105130a201c456250780080081c02d000402c80b0f40d9001400c00455500300d02c000045c25a94000304200d4408c0324890061941049000900600110001d5049841500c1652003e84581104030385904103110940021610030740401c0a20480d140d8041d0340c2c40c031440d500d13040c0507610311540c1c4160b0066401030718194422400c20981d920106146444070080400800c9000286c080191519008000188a4101840c45010814000d61080801ca140140f00c1034228021314411001c00029000c1c0244031030501000180904001003510207582e41500e40b800712100340c00d41c42000390080319000c24031544820001030b00501113031a020080d48800100c5d0000ca245050190040300c82c0804000c04e400d04101c0203d00c01d500a0300808080801c902c2c5031b4020814a001601140c41e0750040203486c40e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 541509406 1250 541508156 541508161
    0xc0f1d0a0207111807080c1305041802031c08010b0304032f0a0c08012004090908090d2a1d060307170d02192013020310030506010b0c031207020c09 65
    0x40f070100c2d1300784220a02c0d1340314007442d40e800005c58024060994900f0540410700750520451505070481951600840500c44511065800007464006010348410340c9601e50079000482960210301c507400740007205007440c50b508055800500d40c001c2e181e8054021100d540115141501c2010703207001540d0500122008101d080c24601c03440306040c45095100c2d0b02e402c0341d2529204005220b07848212000400500f09840c02d91180c0c0a8031000c0b000701e0303003910204001481940c0320032600c0c56140c01200000149001c071841d0300142280c0844411403003030604d0040020040c080a450801021811f20700c4181d00c80720701181c580411a000a0b2444400d4040941d0420b0001a036501c1007007e83d00300d804903000454408040e50761300308098a40d407811111115003450311100d420a42d107001c0c0013401d01400c12640e500403138100740d65601d540421807101f0424000c080101a014214024540c0d1500e214169402d580f845007990b90900380c505000013820320f600a10010b140e40070042c0c1442d0f01071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 541510656 1250 541509406 541509439
    0x90306021902010b0a0e0412090e10090b040e0709091704140a1401080a052205010c09060509090f0408041206090303051501020a08180406030c0f1d0a020711 69
    0x221030055500010362900361301110070b00c3c020b001501100c805403405041a244c82d00d1354420455034100b1102400204000080c4401e46080312522030000b050f180190181000710740019510100c208601c62410300035101c0d1030f600d022440c3c808171030780710400091b84c8a09141142210b41200c003c1d1130b50b4007001c5000030710500c80c0c2802c040700c00300856900b420345031182c90899030248101c05050018910000281780d07031043e9800613402280c988000c0441601008880802d482d10f404110b816075100c18482907501c0e000440c00018040d181000ca050444060100f04c800303e000b407011102d40301200219040c8200d500488010b40300c031b1008082c501d88207042a001902d514181200040d140c40c00041a510380741c114400c65120503805410f18502c140c5501e009500310500d010b0610924000f02138080c0d4030b42c4500e04c025440340803052a40303407800c00003804008495001031060314100302301c030248408800000390f0140055100685445181c20540e040310046481039401c2074203441589004c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 541511906 1250 541510656 541510687
    0x50a090506010806040b01050a0305070603020a0c0b072c090c0a031b110705120309211005180d0f1202090d0b0402031b030a0609080f0f120c0901050301060302070309030602 76
    0x141e07000d0412104140d23610001d01020b401c143c4005842d64018031400d00c5094400c0d001401e0102c0d0918100003264030503204d40d070582d0800da81010115210701c0e0300c9001e40e072000e010768601c0c0e4050311402c6803a201640203c5c080d400c0c02400403078813000026180e021503010741d001c100102c004149121b05082044809498120707400ca4103091403240840000d498a0148451003e02c08880003560821201209000c2907840c0502e484248048800303990007407420030003100c071401d1400f0f080415031307041c9600d21880362409917548004e42e8001c0c0780c02c40c410b25001010244040c0d024681042021f58207003212000b030281c1070402d503020081403031070010720548109041c0298001c606440c03403801c01c1d078880348260400e40c000d02d400d030b000340c925100801c1c2581d0000078000d00408c2c016240c001c080745404c0c1d4950001c1e00c20240d8130310110384001da01740a800915400780c8014185403410381d400c170004e00603000500c2000c041540001c0d41c00b0416124031083c5c1c0085500c81c00c15501d0305550160640c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 541513156 1250 541511906 541511911
    0x5040f09020906012606210f07080703020a05010e220b240a081906090b1c0b16090503010f09051e03040e1314031e04140f010203120103031d10020d03050a090506010806 74
    0x1d203403207203580c080b400ae5008129074003140c4c0d000300040049031914005540340e25403041c500e58810100700590b0b5408201030303c00180c00e080320a00150300c602d4078081056103840c0041c0c500c072003211317002d400a80c4030740700d41213030300903295414000000c1e960f40d02c4900340b2418551000c0685400c25200103241d03000c1f0340103030100000454200c1401110000e2106040000d80f50107010300c81d280c004140f12410022042c110709005280440b0031603102d501090070344404540206100350b84440400a11034148111417038120010780c04044112060302d11540d80c0600e004001e4218031403000f14182c0c415488c10341041b55401750740380c4400c000084080b612600140e9481e964042940ca1611804811204960540c2c160b8840c04091002c580c0900410300c1103c00c00c0390561104014018071070b03140030001030080d8441c1c0d403003100c2070b1941e20300c3c0b075101e814201005001b110f0019045410716008190841d200c0740702d2500007859607624084201034116100d01a196010741000842c6201c008907c003132 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 541514406 1250 541513156 541513183
    0x140a06090516150905100302040332070303021f0b10020f070f0302030a0b0403030225030909020f03040b0c1c1d0c03030304120905040f0902090601260621 68
    0x20070b01a6a40c844065039055020042e00081d0329100c10301444c80c0090400918044902d00141440e40701e030ba514040f01c0d0413114085210180c00c981c01610401460200038000000b006020700c4ca245075400f0307541c0d80c4048036003100c0e03070490003550440c58042e0380141c1121000a000590007080213030080d407209542115416903004400c1e02050808100c480c00044a60203402091a0469030712680b14100c4064011010140c0803c030850498060300071081c102c54000c10007000d541c00c0c034680031703120340190760140c040d16005001044aa0b00305900703403544540c0016030b450705035841208000c09441295010034002030340140241c190543e685c4641c0a00b00d41d80c3d41911505003c110542e03407003401000041c4e050b481000001c1c00140e419420400546007820051840c070b4441d00024140e0300644000c00000d40e90f144060300b580f50a002042c0c20410a007801680e140f040c05c04041d000c9000b83c0e8018403071882d00c0100b01c60784c403020403251010418801e08a680d2842e1219191032305603401c8000e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 541515656 1250 541514406 541514443
    0x11010f050a0c0e0102120909040c0b0a020321010b03011403070902030a02091c0507170703200103140402030304050609010c02090109062d0e0a0f1419020313140a060905 74
    0x43d0219400083c0c400d5060714003101c0c036800c10007040c1c108014204003c000b2209110003030000520700d039100e4094845030b0384940186441e1110301c0b55007135016803902c1034040c1064440c80104215828102100d054400c000c1041614110020110340380008550102c0207492001081140301440360b4003030140303104100d41d2600b1031600c118044418500e1002d01030843c0e00042c0082000c0001c42c0b510484845190b000c1c1c840c3d8640d81d44071000c1591052080719100144050744060569040c0300d83d10040440540860003405e045d00403d40c0c070302071402418041c860000f03003824942c0c01041c071400d100b54000c0840e1055a1242844000b41050740708400806154a03e000f0600b4254005681c0c0050708000800703441e4a48100c810a100e0042c050086c9656283c0d1500300900290080070398507824605980d4a604100d10010001c000d1560842e03000c03031050013449442018050f9400c03403180c1002d5504003114128006071309100180100402d80c5283c604810204540451351f907407a0100b101c0107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 541516906 1250 541515656 541515677
    0x3020a0c0f06020c07080a050c0405040c08060403021006081f020a0201090f050d0905061804050c07021e010e0604030f3305011a090d260406020102090f010201060b040611010f050a0c 80
    0x116502d605201f40100b036a00180c2e2130055a0a041e4040f0307034058051001070000f40e564a0360903041100a690580041e0005550710500303c1450180300001c044031801055551030024002c054080b02c0f003402e0310780030b800146c0c4a4006100350000c280081d0840d080c0d84200c036891502230744d211103d45490000c17a907a00070009582c47c00c8015201c03140c0c0844124100e15504030b080000408009105c0200c1c1d01c004d005100168135005c0400344000b41c0c41c00d2204000034281c0000d005440d00c01049446000200800c0c800603102083c0d650b406a8000d2103500080e0003c01185541c3c440c01c00412907445c07031503041d216844500d4000c5412594282c010044140c0c0303143d250750603881017100c2560400d951140d003500003a5643c805003d4050540034844d1f4114844003108203070345c4103034402c0380140c2d004500c0c20f04616240d45121082c160900003041928500140c0341114026840b0340c8091150915019904020a41280b00c0905807160100007900d0141089401041a0092071000540c030804 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 541518156 1250 541516906 541516919
    0x8070b180603010b0d0c2114060603060a0b130302042a0e0d030f0c05060a0911091b1b0115090b030f0340181b03020a0c0f06020c07 58
    0x101c2c0c1c1030302d100380115481c0c00305408850307029000d440c00b03460800540610481000f510f03140d00b40c0b4181c40b0310f40040b803010036501003400070700e4014080300d210342d804006000300307030340e40a0924086a04000f021602c4182042ca155581c080307550010f0b401504000502032617103244135100d071400f0b2600d1469607140c900c0c3c0c0c0c000c641c1880c0b40007000d40c1010002440c2404240101808030a48065140068103022035959190404005032640c00840d41c0380c400100c01c00010054600703d0607015660310307801d0b1902250354006038090052143d0705a4000480c0c6009155540380600c0c9400410000d1045402c405002c0020f400340c1d00c41c10600a02d46510300c00f45140105055000302c11800055091400c0140c041191100d0002e007003122880e0031003400c03100b55551054410111130a016004480e03e40003281d0102a81d00701261501c070701c2c00940f00c1500e01c0480c890500d45e54a072030010b03203a400c00b20007555400c2c0a101e000c0c05c5c80d031038818a1003c003c1160003c2c03000c000120150743d070142d92040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 541519406 1250 541518156 541518169
    0x30b01030506070201060f0b0c0118060e2b0f020f0106080c150c06010501081806101502031612030e100902010f02010c02060c03040f0b0c07050106051e130608070b18 73
    0x5031200c0d000000e8010131005080394054592070005c3d1000040043c080080450042d0768004211105a100c28030378000032010b004040026501c0100d242000103000c0a00c001c011610300c00e4014892140381c244143d030710810420340010019402002142d44612042c1c0d07541e0b150582c4030b84500c000380035000400059505a4008000941c01031807680d08090043d100d0b50f00040190001d200c012542881c11202008654054a03451403029460760501500c010300342512400001594001c00500700e50320414900c040100e41c1112030b1024410102008401514000c64141c07aa84551a4480e0343d1980e43c1e0320401241d03100b40c0f60031b580703480c54050590903290010005805600002300180c42d400c90000110f9101d4480c1c5180204194195104039041c1d0054440310704401c0c0c003084130002c100e001d1191402170641110741643c1c540004c3c5949180d0314070a074a030f80c0038100d010b05020748082181c1141025107d1081551041070b2030b502618000d402030704103014000e0500c100c1d000700d4188030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 541520656 1250 541519406 541519409
    0x5010609050a1a0c1f2019050c010c11100506180901020f0301090c111c080c070204060605250206190309020312090a0b040b07081c0f1b0905090711010b0604030b0103050607020106 79
    0x109660511460602c91841d01311141c290009102c8c04006a1444c444203120308140f0200c1a1030b040041c08101400364581440c1004010f40c0514007018070010340e648030710709040c040355101c1d591500e0385e8484442e4003a002d0100500c5081401100119103000c00340c01910151031555079a41c540c0f01040d000c2c3e591500d00d03070381c41c6403c46041c3c2d02c10000c0070712401c02030394403200e1040024600724040d40810112007403a802640010404500d140c540c4100e003c03940041440400f10a5030120b050300010003070b1142d4120324601e01c0d0381409a41c1181e0103a0071002c08290000c068031807100c40107458030903540c06464405d2245c100e2900c0450501c0d0b0303882c242c50644441804103801c2c0038481d071783c940c40c07139020340400e0034020010b1030100c080d40024010303482558041d0001250740c80303500300c003e40314207a02e0b1142c0c010300100304424007041c0c4600750312540c04140c514010b041140c540051b9801031007810760642e040103002a0120900c014586958102da00c210202c55050303a0f0f1100c01c0307007282e03041d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 541521906 1250 541520656 541520711
    0x2010504030f140c1506010207060c0b13020d0218071404142403070c150b09070305060a09020708030f070c050a080f1c0b030105010609050a1a0c1f 65
    0xa8181d5803000521401c402078000410601c3e1500e8420102a07441c42c02c100aa586100c01581004001039540c0c140a0500249940e0420710401c0a00d030b501d9000107840200301804841040004a06540e00c07284411a00e58014201140c034403038110209581420480345880815017125868640907210401c49044410000628070940ca40314200711052403210411021214102d6a15110407030702d05c021f500500c69078842980c81d0840b8030309010303003a0001c00c0b1595201e10741101c15a107a1101d0215a607c40290315002036140e882000140350312809401040d070040c4089012001c01c8200f40c02103000710b01c0100100041c0c0c0e1000c0044a0403003000c2e0b0014850341003115010b00096140e0003130000c2003181c41003c0d09001c01e51103035072020b0140c40101d01c0b04903140c03c9141028102881414050046407401f43c1e001400c0002051903103402e0302c250094030120307c1c6a000b10014000c1602c0350703034031510140c0e46c815035500740316031000e0050301d4031880c2645800ca1079008010180045441003a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 541523156 1250 541521906 541521917
    0x3030702040509011104080a05101b03050601050c0109030c0c051207140a0504050718060503060303040b160501050f091c0c020f04060806090d030b0306010b09060d11040f05100201050403 82
    0x2895420300c00a0300001d00300710b00e5992507000001c4000c42001c0640302904889000304021040c0d801c0007480c001e058000b150780310f031426918a56800c0782165030b05160341242408503883c1c98100c0100c2d00ca00c9402c4184006501c1c140301340b8105075010584c032503641d02442003100100d44a104124044c46518020021a840003808122210680e10030320203820000b03108140d21a0b9a0002c101501c5089802c1c0001560795031315580401c9564604c000503200d48c5c41d00c64114030f0f11202080d82c03480396010704144804041a04610710100c01d8842c48050b034018003d0103d07051013400480030403000c0e43c0d0700344140668124a400c1505c04007071911500540d540c0d001c220303100c039000e02440091084907150400d072900008541040d04200041c000c441e0b1100500801003102c900504445c8411160b603c03135000b1000412042e041c55090740c04000c01101c080c3e580340705a90a11006000034040c401d4414004100052644001d201480442e601541c401c4c043c440030740400c9003241c9040f00c00401046 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 541524406 1250 541523156 541523167
    0x19050c040e090d0f1202040e0103060e0d0c030905150c0d050a09080606030703080c010213081006120f0803190507050904230f13080c0d0314070c0b061c050a170403020303 75
    0x10300c996841450317070780320080c01480c180d210440391446050980090303a506450340e090540280080085100519140c9044660000c555800070f04000c0700d846200c1c4260340d8001400c444030304200440e0840e0031254102d50441c2c00c011009002d0303811041c02040447c00e80900001c556a011a04a2140c58002c002d040c0c210304560b01d80b60f9076004800310440c02c0d9800d005070022400340103044005004408010a50380c04801040401e4940a4003d40680c1200120b54000660240c691124556100c1c007120b1300d81d80e81c18240380398410b60300d40c424155400e09041c00b080c650444010300b1203280540f820f21110b41318408420030310076026005041c107466040060700b1880c00c540c19641080240c020981080c04544030380c5c0013078200074040d4405410020100c4000c90301403040d44442c2e503007001003016501d0300386400380001d00041c001605034054040010342d07c0e40c07059a00e80b40c1e40000c0310600840c0341c05080181e503507070541c541240c58107004501c8941d030740300a02c1580c3c22254010010751410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 541525656 1250 541524406 541524437
    0x2130e070e0628090b0d110409090b0103020f041a0622121a071d15070803010510020a0302030a050c01062105060108120a030b030c150c010612020a030b19050c040e090d 74
    0x14a03447c03c50380c3d181035043c000440e07088282d02804440354021380b80c20145504500410600d1800c0585442c4940c0c549031039003242c1c4089600c0b148580400300c0380ca0341c0340c01d41803050038010101200342d1166000d8150000c0380c605406403540c5800c901134107075001495001d40134144411810340721003000c00d103207440303080b4802030302504034080300b5001d4000303450344240203040780b0340e40c0008008072441407020006110b13608003d0300000d445907861004003811101030318080e407a44941c4201300200100080c240300c18960940000000b0a905008140010010842c00806104e6028215003502401000080d02c660002c0c550320291440a4100d181c0f164a40b020b07030040c1450107045415004144203a0125a10320b42100b090b2401c820880f035440d08241130031400c56500d80c005202500e180554040580c55040458055960204c03400f0071540316443d4800003011000130315820241000100002021403401800c1280c1444c00c02c07408544424101d0390721019007841100008044407500040f5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 541526906 1250 541525656 541525661
    0x90303041a0612010507020a06110702061b01061232070513110a090f0909030e0d020105070605150f0604030b220c0303050a0f0302130e070e0628090b0d 67
    0x116a006040301400e82000c483c00b401d42c0e408503000d03130140c3c1006040000348000342c003940041d40b042c00ca080746400e54950004001d0301519840c2030320130b0407414008404034000d502400150038400f603401c81d03400305881c06411526480f1403000620303490306461803c003440302481047d00c4a0402c0a4900c03035092005120107607900d4081c80721480e03110300000c076180c00c03408000c204400701603454044150405030340a200b2461030344003038a960b250001800100c0d41c0130603030f60140c640440380d00903903290324001200c003401404c102400083c50141444206d804081c41500300030703020307a8001c0c5185203100410081d400b07244009460741c00d8030b00008207170207142c1800d480000c1e400d01076015507001030740f641d49003801b55030400c4010039400101507001e15007149041d0302001203072070103501c1c00e02c01c120780a54480b028400d034041c140720080480c80d8540200c1154070050b00103171900340c8803007510400810311981c0c0d106110041103041030300400d0500c00c01280088c0e6425071017a500d0720700c1e8201034000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 541528156 1250 541526906 541526911
    0x1401020918090714130e0321101211060d0605040506030a05060c0c15010b03100e010b07030c230303040c05090f070c0f06020403051605040c090603180f030f08090303041a 75
    0x20302045d0390024801d00c414520903c01c00c04130000c002d42c0c0ba040081c1312094204080b800c851880e2650804000711000d15480d00301c04d07100406200d004c03500d030501d418800c600c001151103900c45004100c86044d0385140d03002c2d0b4112101141d090006456100501d62500e075a550007404a80241703002451020f540300043c0019101d0b4021075881c0c10186450784e544903400c3c1c0003105a4034000051212001070303105400060800070444482030351400607884114420b4a0b001070a02250f81c9015081c40010f0002c0c2c001c5400b5a06400d220003c24a80300c0d0b26603004441c22540d02c03628070000305d5a406d0449007181316108000c58248552078080081d5411450000c0441c9d05c68024048440003410500140c0019413040d4010249a03048000b4001e884d01682c02481c015482c200f5a084525408401181200d402c4c0c00c0000300260400455030310f24a01700005809004840a810300305a400307110700541c001165a0780b882c4e82c49800d00301c2c1c0c8900c400e880151004445000034070986c10400441074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 541529406 1250 541528156 541528159
    0x207050d05070509040b040302010e150604090303270218060f060c0c150304060516050a0302160204140f0a06030c0603020f090a170712051e0a1401020918090714 71
    0x842e450364031400110b10000c200d4040320413001040c00d1200701a024042c4001e041c800741c0142103e062540d03025420454000c200303074410380d1101d8900b01070502960006c2800096441101c1c2850402e4030841e50621038424100d014001d003200003903e02c0f030300c85112402000c00401d07444e2055102d0b0b041220719000003138202240d00420250354407640d00e0014070200d0712500c1002ca5281d18050a0035403c68400510242c030b0314114201c5002c10542c400e04498464806050050700c0c0ca5144c00c50700b042c016078100c020340007490410070b51a0340548494051040420780740c800c1581e6100024070301666082c0c4001080c3c4000c2103014003400c0c0c080d4015003000114000010f061901c400002045404d5a134801c2c0c101c2c000031403540d4103000050104401804244400040315135140e0343c0c090359001e80d10050180f084a00781c00d040b2024090080380d800c00d0b008140c003111129150103040c000d511000074188615580c4240d111114030260f249445501c0c040c000d4040315240c0025200518001b01e00f20303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 541530656 1250 541529406 541529413
    0x10f0b0901020f011e0b10120c020a17030906130503040e0a111207120c12050705040b0f03010f0f0303080402150c01020703030605040b09040f08070f06140601020114070207050d05 79
    0x31120f025003441000c500c0481d244511500702c13074016080040325100000da074000c14204c07a803c140103411105c2520406c501100001e802c40203903104a0502a0105008150001000d19032104007450009180550424000e42d030340c6459401202021002c01c400050050300240803c02845080060041e40300a0301c20010a981c0700c13419412100341d10001c10780d440c030301c5400103115440742d010303001580700b0746040780800001205010103000c80b5a0b20070841043d6840324000740c1c04a100ea02a0360082c51245e4001d5140e140c03108103050306800034050204808400840050a035001103a100200ca400d92a41c0200707403036907024022643e030312074a4110000801c01120709040024802003080b94000d07900002ea1038109010041515410b0074864802c0080000740000315111518510b6419440303018150740702003078038102d000742a0540015280d01d10f04001d0390b012010341e101c01c500c254400d034000c2282404421b0509040314068401c800180d00900c01071003541061415008128004e0084 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 541531906 1250 541530656 541530673
    0x3030905012a0f030b0a1223030d0b10200703021909060e0405030f071110030515030708071e05030102072603130206032a03090f06010f0b090102 64
    0x400030b0101480410b519070b101140100201c16500040c0394482c00028a82440010028000204c01256a02030498080c01404030b11007041800ca448007800790b50608542d021001203241a91203070001010054030900306100002285802c5580019000c480c1e04d60480c6c0002c0da108082c94004c0040500006100f138100100140c0d8035000c100c400c0c0102c610300e6440032800c0418038416140c0690000b04100080030a010001d8800b0007a555090b00d02259036880b680389044c00c5006207045000c0c4e0f0341140c60041c07101032996040c0c01c264440d00c110f1040240b2020410145a0b81c0c445a11840c1080e41200b002071250425102142e007180c022600c0c070030031403512100040d01726400b00504941c0c44811001548140301c0f240d400500e80c0c000c10345424111f20b8a01e0703640d0000c0031a1a03009202da00000001000ca000d141e9101c2500c1e00e03a052580e41d03c885400303910003150300540d00000544200d030344800c403141000658a05a0300b8412651052030302d4450fa107940e5800a0302c0003419402543da1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 541533156 1250 541531906 541531931
    0x6031119110601030503030109150f0e04020102120414010f170a050c13080d0f0f05120a020c1b0108090a02030a020906031525080403020a170c07080102030f0702010605010c0303090501 81
    0x102c50107903000b40059681d130b500d0075400c071044508940e0790210f000c014640401076020f02401106c100c685880003d4000d41e11440100c0c1040103240000680400120b400301e5902a04103181621400c20f07220442034844160040e5004541980c1010360640000c000500c48603150b006207400107215036620f410111000800510700f0019005031031707030354801200c0c90b0701e09500c401284520303d003600741004250380e0702000038824403800f0028520364403e00c020442c0c4402540c1212844050390094803a40d12190442d180100009500f00703002030b0001e00800c001641c081a821440342e4000e0042c07900c200c0d55801e200d91068000d20865050282080501c0c04d0704a040145110b41c09045200700b050700010700e49850a1114a03402e8104500c020800000075000100f00007615000510442c0f160000c00c012883c0340f09000c02e1507410700440000144100c415000307940a12141d04a940c581d54030280c0032030890380140b1038170740011090000030001c01c2c044c0d8045034019005030004981209807a1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 541534406 1250 541533156 541533163
    0xf0822060f0c0c0203010b090606040614040b040e2e050405040203100e0f060709031203020304110a062c010f0809030706110c0f06010b0405100e0a03060212010603111911 75
    0x1010000b140c0303151140011845c00b132289a410708400c641140740d505003440030481c44d02035800341c0c0b0180082c0b034140d19081101d00c03040d503005200c01c503801c90b501c45d280c00f0740700c14020b0151081802003448000d403003156458400030f01c44000100d0b882500103440c000800c4050700f0090400e07a054011001049881d440300e02600508102d048024994044140c03009440c090005200307108002c401042403002a00d180c15158050f00316260143e101d4845080a440400c9030400895102a00700030000c1d0403038000c0540d8040180b50407002905c0d2070101007020440c4d5400c150b10b4009503913003010049442c003540c203054015512008590a02d029075860703000715071504000d04090080403940d007400c0301c401c000c44680351401c003018001551508001c41042c3c0a58054070384900c09010035803a12a03c20f8002200c405402040080382c190b0303030f003400703002540003084441d4000c1d034041c004500b15009005442e01c1d61100c0340302d1490b0140e000e00c55042c0300180e5100c0d00400070040403014030a2001c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 541535656 1250 541534406 541534421
    0xe1c03020f030f0405060a0b010f1d040c020d0906110606011808060a0902090702190b180601232205060d081902070f0f05100203040f0f03030f0822060f 67
    0x1040d29481410581041450001b005103075015940c02c02d04010310070303688100034917007105039401c1020017004807c58140312080d0720942c15800c80e28050071004207540c0040d84d03184135a42500c4070032401e901e86004554080400300c46109561050f00411520b51040001807001c08000000b103840c60b4076011103d041c18020340c2c0032490261180c0014066240c0011002e4000c01a400208011240340c1403c1d94541c401e4900070300417105c10f00004012000c0c081d42c0104106074141613403159a1501c12005409940606002507210f84580c00780b42d50401d044c00301030240d40318906800301081041c00b0f8021304001030101c0c1d040034500ca03a10000441c007001910029100e0714480e03c0c150b02c00100246422103e9100441d5400d102c507041042071007440c113100036201c041d590300c41c544000388070503455445180d010195000c102c650000c1e034149030210120a9921a41e48c04c0c8002a4420044448050a5540401c04031016411640c003149030051000b01501c59540071814064800f410401c88054 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 541536906 1250 541535656 541535671
    0xa0203070e06101106150f0a030317090a03050414030a12020a0b1617180d09090f05070f2003030c0909010503030a05070f050f2a03010e1c03020f03 65
    0x5a10501c1000c1c034110f86042070007032040c0b40280d40080264126541c0e408041c1240003401710b825000c10341500c0300400c05a0720040503001c9041d00c0d43d47c0c60010400d904010241100b544404003250406401080d0745a9481d05aa50f0b42d0606081c44500c02001c182c103048150f25200d2900180001040740c800d080038485643c01502c42d01c0340a0900d060258802006010b10300c0d607801090014680060b1203030103000190342c03500b180341d03100340a914007900c0705280202d2a1182c0004d40820035071140c06042600c541c010148071455440c8010010760300c0543c0c007080030818414801c1841d510403d0200081c0307100c2100c0100b0480701c10440e904542c0300703031a0060700213800030f02c2c046142801d0350708600400d0240e0003186001402d02d00100036014480c0000c142848907420340050240421a1a0700714100300305447e40300c0018403215034603d0305040d602c0034542e80701c2c1c07000701d50780b5041c46600c0301200c40354040c1003084c0240a0503001c1d16640c41100003416801c1c41282c40c00381080d13000e9480f8944 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 541538156 1250 541536906 541536929
    0xe010e0106020c0d210c0503040f0501020f06060a121514070905031504030509031606030207111e01052104050309030c100e060a0c050109030c021906020307080c0a020307 75
    0x1070480c000c0c20080c0c008800c0380100c14640505001624030484800f54200c0b9048458416030380a00450b10000500740c080d101e4400070074042081655010144215032090b0202c43c1d5503662845950385409045824a40c0542c0349082009400d80845c80300d5105481071610741481d01c0200b0880341103a82d200104181d44021a04000c582a0030884040103000d080300100111070a1168103054602d0040000341002004903c07098a602c0030803440469070045185c202000d601c450004000350403000c0b0981e003515281003411000c0c10b1070304030b81c010320783c040340b48105c0803990038010b60b107a074400502050110307c130074081c2c07080c02e00036210540924420340183d580c5100d081c040605d01081031448074070881ca0306001000103070304800c46030100001504c5090b110f50024605a419120a9101500650800185900305680400661b040502c220740b403020808600f846102c074102e4900582000d64020040b0001182c40e18020304001350002c002c079216000b00740e0103e410100a903010300040d10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 541539406 1250 541538156 541538159
    0x90a0b0a0503010905030412060b0306011806140d30120f0b0901090b0a09050a20030c1c0b0a080604060b030c06090d0c0b0f04030c0b310e010e01 64
    0x40d110240c403000382411002070110541980380d1544034450b520840185a1903000c40e9010420150000340300c203030000f4140c0b941036a403503003a1444103116100307200c401c40c07500e000450028550301c0440b10032400074040c60315015055a4070058464024040d60885070a542070326180e043c11025100b00450036070f650041c00c8603443c1c45400351580d000c00300c0d41c1c0c0340c10480581c00f00d4458002c00717411030380d82840120300d4542000104004c00c600f078020100c0242440104210405250400203251481c4165480c0c06007401c1c924149500040c2e0302002d40c500100b18517a040080c0f040b40c01810700c2030540006800c601c080001c1c600164607440760711690029401c210078030655204070403014100790050400440c1d0b050010329944642000c1c20301c511011410f00b401c0c8181c0c40b200c0409000920750080d952081c6524103007840d04544005c8440b042e1a4070041900b900900603640c450b01c03000c4081411251440101d03940c032040702559030480a601ca0f0004062240d01c000c18000e00034240781040c0e55 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 541540656 1250 541539406 541539409
    0x507090207050f07030f0206030a06031a0405101b030f022a1504021c110d0318050301060f0923070503010306060503031317032109060709080c0d080702090a0b 70
    0x40700f02c803000d075000d400076841000480d4a11070811a1680d0464016649a0350740c1142002802240c2001e02810006242400c00160803421140928003603022500080e41c114004419030300e01a4070780c9d07000340281d04140078540c000d0300404003242c050a8098140401c0c143c2050a0311802c01843c00d10020041c0201051a4140080b115015070046087c5551034182c0210301900f8000f503000070003441c249000030900410031200c50034401d000b0428031902415040091041806e541031309916103c01c240000d00d490144107074412244080c0400700b40b81e16200e1014020400d130b0351340d006c04481e84514131520141e501b030101c3c8510910f440301a1254114240303802140e4030344c0c0006000ea03108111100400c00015082000c43d50880141c1e80d14402030304110b402c50061090001410949114407001c021260304090302c501c0f4140112001640ea01ea0101c03090500b42c86040c000c2c0d00030244001940c100404034084903070068285500c0d00c041907006c24000081220704000e10b56071541c507007409 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 541541906 1250 541540656 541540663
    0xe27010b1801061106070f14190c060c05040f03080a0e060d1a15030a09210503010905250f05070f05011b050c19020d0c03080a12110405040209010903050709020705 72
    0x143c149a4001e007628a84010701408001004a0b40c0050103100b4403d1f484001c02303a0308550041030003a481148004c02e00704040c5c0140c4241000729440f5090124038120030b44544251422a0036010740800441c4c61034852510603840b66100f0020000900c07040c214035103800300200411400705900088441c0392007004595161311102182c03040c0b000e070a40a1102211605590300081600720020702083e9034076058030445440483c005504442c4407248072842e4015020710704841668600b0300c003d9a40c6585526540305914080780c0f152107030100003d0b0503100c4c1101d41c402c00680e04119141ca1142d0b00e46000d0710704d40b0507049039103039110392840002100390031002c0e1441c0450304003c0e080030707031103080b036500d0b45041a246800e60411941c40f00c150b5444a0300c3c0121160804184021580c817410700445a900002102d00403030b01403141e12005000030321542c8549190f1325825030400b41000308000203540f1010b030090420940d1280400031407400d00c841001008075410059603803007c1e1500605 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 541543156 1250 541541906 541541927
    0x804060b0409080906090d0b0a0f050f07020604080705210c010c0206071b020102010f09030206010602120c120d0b04150f17030403030c05120c0607090e27010b180106 73
    0x1e1401c002404000600a8080c1c41c50283c0c1211010b07141c07200345000c00c035500d15060028001103d20400c0c894006402d90162014006031002400f0507941c070b0888901409003030300c0440c0141d03c08000a00404e00440c0648012407061042d20140b0302c44c040a4006190003269030140e50500040c0030700004401d1040d480302c000c1d9400508030710303c0c0c0300c4000b40c465480454001009004050f065085a100394000582c0e2107500703a00f0824101c2e00d0034000e65842090151402600c82c20211004142048081d5400700224070010004240304044070189504945d0400d109a03888010303448440c1d85500541c0ad01849400600d04040e01d0800f035419a00c403a940440c0009030701c80c3c05110980c20203c201c41c00c1d01e42609203501c0036501803800c586062a801243c07414150040b58000e00000b0104000340546400d51f54182541d4403240e4030b00f0030b00780913600510588051414161000348155048141e02c100c40000101700000c0c00104005110201d07801c40e1400007400180a9a0380040500d50b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 541544406 1250 541543156 541543159
    0x52d01170c0a090e2517070e070e01112b090503030d15050a0306020405010201110c0a030e010917010b0a06030b2d0a060809010b091b0313120804060b 66
    0x3000d030501c012600820503405406039040d02d402ca401030104040055070000c000c0130130080e81440301c44404e41161080c41c000d4407000010240c20007112180000d40c0c20a841d03004290417000d0b215140f040d20401c0044007424103000c0000d42e4220981024421848080e12041415840701e4440f850420200c000c641010180f144546091103562000000d542d001503200f44001080d1380450b0308541400d205510640e0300c455050808001c000750758003d001110f2007a002444030000c2e50100640c42e005084902105034402c0c8552408070b0b06c915100842c0d0366060405486140d10307a40001d40c0e851001020b031045a44419030f5903600e08003c20080f004060620302080212041c40000741001e5688607010016500340521040d1106682129021715400a10240489544000107020741c075003128103407a0340d403030401072840c141048413484c1c1c495001c1d4000d550000a20b112008a10340014204042c82c0c0002150f210006039681d5101040c0c0300b203900ca4034020706d0f01c0c0c070308041640e01804186 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 541545656 1250 541544406 541544413
    0xf0807020709110d0c0c030201051b1801030609020c07171c140d0915141009020a02032a070609030c06052d09040b0a0e0604052d0117 59
    0x1102140d8042604415603048110114031041200310315400c80c01800d42039159a0729180c0d0b40c8840a402480350208980b20790002e0004d596480a4a10540d5110318540c41d031030380c204001c10200281380b103099100d4074141400144141c4413203040d0103e030049101000303070780d20140c0c007032180710344600180d41204103803001032003d503c9078400d00e4075001c46c0705900e40901522003000d8018081c4041a5003c8188009040040c0f00702400c0500d000d1140c0c04120b01c000c2c0c40c0c81840031001754a040243d2040c0c1c28150b001548138548549040294021025041180000e21a0101001a0b80055486406500d480800803501c65400720b04105d42503200c5000d10541540c10000108000b04000403200e180c10101c0c6c1320419502c0107220a4151841d05586e4000c2e0505280d041840318003030006607030160383c00c1054051310021711a0791841d03406016450048140042c1c0b8a240c160480c2e0b034051100c2d01040b84e030040000e0041045114103614135508039003c0014060078100c4014100d5603c6400002c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 541546762 1106 541545656 541545661
    0x1050a1704031707050304020d1101140f0414060c07050103090f1a220201090905070522030201083403060803040b1801050c070b031b030112030f08 65
    0x660464403e000820b9145125405680c815036000d48400c14041841c1c0f00c107540c45800712841810081207518084050f00310340d0203007444074015040e4035140c03824401921020405600b115010711030030b1188880000f800204841150003c0c03d001071600e2180c2042820403a1000003c1c0400c2c0459201510301c0c0c2440e4080c5110700ba0105a9051500c004600c1e18910f0544090190010b41050428441047e483d4051900421746007021460040b00c1c91202000d000d810301c2048904100140400555030440121a0701c106020303250340000304460921a088000d0356280301886050b840040e2045001ea813011003d460007108481d180c59072800007048642c411910101c011604100134140c55000d401665030140c440405414001e04080c0340800d10740000348013035580c88003c52a92500340150300150f000e020310941004040c6503a084c0900803500074401c200410140904 = true := by decide +kernel

theorem cover : BRFrame.Cov 541366906 541546762 := by
  have h0 := BRFrame.cov_init 541366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 541366906 ≤ n) (h2 : n < 541546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
