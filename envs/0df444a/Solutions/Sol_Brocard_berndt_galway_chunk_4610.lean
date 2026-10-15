-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4610
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:10:29.441974+00:00
-- url     : https://prove2.me/submissions/d961144a-dd46-4c96-a47e-46d18ed58fbb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 828956834 ≤ n < 829136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 828958084 1250 828956834 828956837
    0x16020f03072603040311071a030106030203131704060206150315090102070501020a051c060806060d0501020712031b020c3601030809040609090c050411041208030103061a0310020a 79
    0xb1840340164041c1c49a400444042e004140c0c08a030354030901e2070500030380e0050701d184612805003200c011900c07035550005014080501d41c1c0040480d10070981c0281560b00c042c0d00102030b8410b60803121701d0714203a801a12403000913224080120380b91194040b504174240e04060014a148841c84c070000754403050280244556540c03c0002c4d0001c03520a000400441c840f80e2a00d80e92841c400c1d603507009074141c14801d140114034051003800b0454020032150340180c0225030b51107141c5a2810400c3c02889000c07401810035089052210200d505a0030071102011000c1d94451011441b0382d081c1d0300d039000030745525844140340f1103c2c146005640d000c01c84484258a51401100340c1c0c0701151020320b4282c0041e101003002184070302c0c1526013405443c002c0c029020f014000c8448a07a10b0180c0b0300340038028548501d4450250821076105542501e004040030340d1000316480150401406551080c0001c3d544503041500c518603800f01015901d9a281020b8001c1c0746e841d451040c00002074000001600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 828959334 1250 828958084 828958133
    0x60207170303040b0403111b0a1d070f02150a0b04060b030c0403020d1a0439050630091606080411040b0604060201020c01140c04150c06090b16020f0307 67
    0x41c1d000c1d40402c230500020207803601c003d21662240b410000c2906056200000201e4905030305100024114441500001c40703040940c90403800000907800c0000c420b42c562103400000042202c0300000f41c00010007280b05890802409171690f040028921045810041d0780c24100310801c01030809221091a49000e00d66401c208031907540c83c0c00c25408140c600b55850400c0e11007e41d124900300d507600480d40b08400081d044002c40c070500101c511a24424075109107004212901c0c8032015880000c440b01c1c440b80d170005840c00460400924041c01d0700c0b8002e0750300c00c50001880c1a0700b4110140300780d03111900e420310795581d2507503002124100d22195a400544900300b44865445400161026107007640001d61a4403080e001c044c2116140c20600c03003411051784c10300c00b0f841c1c3c0c080211400e558813280280d540c900c0c800402d8440c50300c0c001c002412a403404006030240041c200d03100d40512035240d00c241071a00642c1c002c982d0b441d040a408500e640041048100042e00c404110380c902c112000c068 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 828960584 1250 828959334 828959357
    0x1a07051222150506040b121e0f01110703020106050a0e190e010e03091305010e0402060d06050303040b220b0d0b1201050405160806100b1b0a050106060207170303040b0403 75
    0xc8559110ba101d10150903510351050150500d002e0190120716901a1290032106400040881e911540c00e618440d600240c0c4c00c005103481818006032405103e014001d00c05c14404100d1a0001d0303026030000c1c1c0c015440c1c100701107038510348a28110215104040101140c2c1c84040161152540f80040c850f8500d690b07100c1400360020078002d401928031540d01850705c0d00314500500865491025410800518000040c8074100300c5118240e04030780c0648903076443d03040c2c0d50307841c1d001800907400041c1c0c184800701c0c0c00980300181b400282035108500f03507a10004c007846111110644610700940100c2c40d000e10112545661550007004510b600a01d20581d85009000391400c43d001500e040c3d569030005550742000b4440c64400d0380081407044e004144510b0000c0c45003003411014080c0c0c171f04281000940303510004080c2c10101144101006556000e411880c00034001c190341d101c0d11000d4000c010b00007814006404d039900c400300e102c038003440c41d40e6204da4039040030082c001c0c030440911640c803524 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 828961834 1250 828960584 828960593
    0x70c060603050309010e0607170304050a06140106030c410412020a060c050d030b0a15020f1002161b0e090d0314040228121a07051222 59
    0x1004000d501400c055a40ea030344e510b000611013609240907d0040004002c0100020305450441d00d001c100000031940320b4649184c00c50805034043e102404040c240031442c00e41c0c13080040c81c24101c2d030305614100142101694140c0744050801c004141c2c8a005d1026070103107500c0070490850300088169020822030300121031610603009a000300c407014107c1b5124108508103501c400c13010706440d0500d0030030000c1a82e46c641d43c912100c0d02000406403610300502603600c07201c01c20000383c41900e608821407403000341c00a503100c98080802c0000e1003109601101006079200310790800d0140d082038520920181c42d0146034400d005040c400707402c112480001d080c0240b813034240c0141024005041e480c1c60a080003000d42e04d030300b51042d0805042206000c0181d640b01000712400c0b908046807550701c0f2050014240040c4284d00824404207a810300e082040307a0000c007108a421003070003a40701511040c1d4200c07418001c86401c141e4200008020440c6084c0e090f00080c40303540c07901205007402e05c1e103558 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 828963084 1250 828961834 828961841
    0x306060907090b16110402031b090d02101101060e07090911040806190c030b0f0904021f12060e16050c0a020301090b0106032306010c1106132603030f070c06 69
    0x84000413039140c08000c3c02c0042007448501d00007000c913015070560130040c1000a00484120420241150001e0842c41c00d1f06d170481c50034912070f002880800e80075403070f0801801e0460303071002040d01546841400304031760802e0b0300454054121642c2d000c00250078249114004c0582d06c0ae401040c0605010008a200c0d0401c2058410300400000c400450790407400ca1003074440300c9914005060030900860065192204084281441200c40c844107440754008640b4031061000c01415004602072620542c9401c40a0600187c862060400407266104060301049206848000c45503c2201e07038814420312400160408103407840070b4500d0b08000342e00103400c5a42003201165502d015000400c030054140c4903160401400400b1403001000800f50813100602c0104007505115100c2c040105002c1076800700310a80d00b01922181d611400c07002c1c00c02245110f0f00c00ca600c01d9070140c0c2d401c80c88540040010b030800890308025819602c848204000e0144024509410003420703401301c2010a42d03500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 828964334 1250 828963084 828963097
    0x8090d09050f0a121101180605071106190801050f04060506090108091e100b09040f060c020a020607050304051c0b16211508010b031f0207021503061009050306060907090b 75
    0xd003101c042460085c00580074084001c0541c01c41d8262150410601e5000300884512651040d2585461482040014114000e0307002c214020a0503008001c8500d4003d0b0702c4038186e8034101d80d081d800080180800c01920003d02507280c1001c014440700c000755014420304c60b007114031001911070361074918800c0304442c007244094698039480f00900241a000354460a20b240e80705940c0a032151034180ca9201000c880200e00074034071070703880c44003081461003071103081841640140703070942c0d50010b41480350f9650460301542c0d1203500d9207200c203009441c2c030100801c0c031150b2200c400c688a40c2c50303103041c1e01c51201c00112134040c0504608130400c501c0710b14658511140b10b120000070144400030148460f94010f80069240381c0c9003002607101c940d00001c4100010802601c115405000e0610070b030068020f10200030b421511034014185291812001307503206401c1510342180004200e0340880b80700c0c40380d10030160107800000c0031a405040c03c440295000c000e60601c01035495458050004a40c00203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 828965584 1250 828964334 828964343
    0x80a03050904140106020a030c080d1503021242070305040311030412230d170a1a0f1f0201272a0e0f0708090d09050f0a12 54
    0x1503003800303600c1c06110f1800c4401c6450041e402944c1030440c0a03648407001c00700903003131040034110032040001e01d030100d44101c20300e0309084c0a500346901c01d500441006c1e0000700c1c4158100c0100603400700001030141e1800e507000c130b450f141c40a00c044600c00c20b61100c0416034a07400f42044040003010705450443c2c0035030666940000c03a0301e001c1c1801000340c03c1c0080c4244040d0420042000304030000c40790a00c1d00f541008080005644002074042c2c05145456251050301580c180c0360080343d000686c8800346048000c910496944201400048030415400260400c0c5055a0b520703083c10318080d03210072501d02402e8214000208043c106d0400c0d81c040c03c250040c1e440d08892003109281107800e078418014002030380183c52031581c1ea4010815130303980b032191110482586070080302001c2c1d0020005e0030183c440000034100030403192086c540c11034102d004901c1d008003041d180c44c030005484140031032a40e9500400c505003402c002400345403815555204500000100e152000041c484c01020b208 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 828966834 1250 828965584 828965587
    0x150f0206010b030c16030e180f0906150f0307150c1412070303051e0108010e0f03160308130f080d110a0c0615241b050d050723060709050a0b070f020406080a0305 71
    0x300452750101c1c0004005104507044682840b52030008a280701c2e0100c0c1c0202c887d10086500b00d001700707142c081c0c25071181c0d400e00100c801c1051b0301e6820514078680580240d5904284240c46118903964140d442920104081d00f00400300110b48203600c11a0400320809012402104000301181c20000a81007002942d56175600c0c42d48942c03040250b010381c291400c0196041c2041c034400c441c0300748400ba0018090114440c00180f02854040c00d441400d58052022440c000c02800c1006040d0081904982400d14000c524500569407509480186601d9038811454410310340c0c4407000381c00c0a59020010542d4100c0204034148880c6074a030303040400030708803075900115040082501c1c5000e0440c00301c06070341015103404a80040360f2204000d00d2802d116940354410326011040000da494051120381c00c00d0013000d40300401082da030b80910300310350342e480540e92114204002c042081c400d0403640c400c100420400a590b1041070280f45000810014820707954124903414111804030490002c2c03030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 828968084 1250 828966834 828966841
    0x20712020d0e090f090705060304081806030103020916210203040c061e03020a052104030e060327010f0608060a0e15040219150f0206010b030c16030e18 67
    0x90401420341c40d40c85a1502100c145403800100704901e40261001d00d940c1c40301d00018142c3c52040121100400001d011075581e40303058144034510740c100c0320421100c003080b818103100d9850505c068038181e0f600209240400e0311000c40c02501184c8114080b010f0140d08949400801c40380309028100b508000005640c0e4070303207440d04a1300d0040d44d030000d60034040050032b0b29071076042e6480645800300503410016542c061034a03054603280902c260000d0040d2481001802f845460300d0400e0003039210391100100b541540c010007015000031180d03540c82c2080503011907019115842502c0714185070000000d560300070100100706594540e0000e00302a8400800c3c801980316a00c00c01c2c1e01084843d001d0304207021145186509000003800280c4609003040700002e441d42600301c040c0040c88041484010b000840d100076041c14540720f003200242c0956000010030003021f0702200d12618206440520b00b80303400b402c102100b080c0000c00e5040007902140700d01d15840344410100c02d00c001ca60306407140d03d0b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 828969334 1250 828968084 828968087
    0xf0d0512010504050c0a050319020f040302012303060f0a05040603050c100f020d2f060105010224011a040306060905041211150c0c011e0c0f0c0303020d020409020712 73
    0x241a0b000d64041c1d80340004006000c2c24020903206004801c2ca062031350f03038030745000e130111803c030062240390f9892001603c840c2214883c0011302c2240e00c01e884000855601d640c90740000f004880f102c05800000b040090340340d1600a800030704900c2c00401c68844a6181c40229003100c101e500100e445a010f090307144018640380003100205070b05450035001c11201030100944900040c5544024481c0c21600d50042d0041c1001c03055410300400c0c2008030008130340c1e0059940341030a22519001d406100c207071800a0b10b10000210a5a00460031620107918002e0a009008c0d481e0107180c02641341840007000161260080e14010301e40c031100480c0c40e013001d00f0150210441c0348071980620a9032940740402541c00b04400660ba40d0980d00000c1565600710400800c2c401d40352481e24552811404d00c2c04440b14080f41c1088480c103440402a81007140c0041c0e5494029800002c0824040301400000030310a0f0001c0c825071801c0b460140c10581e58a80d41c0701a80c00c852400c0b0f0b004199410041d9409 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 828970584 1250 828969334 828969367
    0x40b0310031b060c030f120207031713020d020d021c050703120306060f0e120a05060411060c031606060e040f0b0a0b0f04110906070312050708190b030f0d05 69
    0x1c0381c2c40c20b146089a00d42a4007500b03200c80d4000040c14022486200803010f80500502d1181e961114000d5568180c6468014a0781440ca1002c180c0d1903c1d00c0e001c6108041c41e8400452015405018103400042c03c4c0c0811521031400308049a1003003103050fa103000260b6000b07048003001c2c801c100030f052103411460410b01c56285451141d04140c6458010840207601c10030500c0409d8050a1105a82041c0000324540e190f105400703001e503110382100e00c820083c0024683c0d100700e0003042c000640241c8030381004458410760321442c810340d00c01e00c002041c0061008089100901c206030025016a884411044a9408a0f0300395400c1004e0304034681442664001d59510005064042140305407910008100074110b2084030f0145545150a000b5016940200c80c80046c000301101d4407000d041c034000b000d9280b0344002e050310030305080102c0ca0890103200d160340122036508030000300244101100008000b0401d5076a4144181074041c1e21119090002c0305010b001170b51002da84000703240f01d00001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 828971834 1250 828970584 828970613
    0x1504031a01091a1c140718020c151302090a090201030510030b19020403080c07060f0c02030c150d0e060702150405060408030c122401050703090317040b031003 70
    0x5041c1080c5141d44030243d100003040d814581203c2d4040b001c0525a6040c110400011000b8120540d130080d02650200c005511000c0710124134002050312400381e0703400300b80d0081d1802544141c0c09160a1180303688440c0d1450b900220241000080b58030300d8000445c000025240d09011a59608421003556458051103502c650985800700c1d500f40365645800040d0b400401601c031007260703012800e0b500c07000c0d90102e074000d54101d80103c1c5c4900084882d41e4440c103451080f800801c1c0001c610550340c600a071000360070b140d002400b610010440805000c003201d68982d501c48400000c0000200a401e00d219200b84050740e64010621880c0032003000e85003c00904d208004440038404110000320001059680181e0003003009441c1c1d01d030342c003000e100c90003401110090351040008002c0c2d00908054481c40300300001c1c601c480204880c0005403054032030110003030f0001d101206c0510100c0d03045c9501025540d8441d40c1c0320f240a5451802e180c160b0020b40305141000ca8030541002444061034540d141c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 828973084 1250 828971834 828971849
    0x306041103090606010f180f0807080a03090b0a090512060103030306120b0411010e0a12030f0e06030a11090a1404060819110a030f0305130f0f060507021504031a01 72
    0x91801c003902e1090743c501c0000d121604000072500b0780c400c511b104141007104210492074030003c8540303449035054003050a014001d030341c1c0f10b540070005101000003464280e407074140c0c030790940705c40c01c04040100340d620042d208028000b1032100080c650326105008040d008034400174101a506518008064a00c1940924032207002181c915000c40c2940d0440e50b003007544003000000340181180140c48804140c0701c07103075101c0002c520015600342c070011180f444c5480780d514030b040300b00b075441b050711100d488542d016003010003070001071041e10240d4000c0905c48408404e207820180c1490014450101c0c1c0c0d04111285203001122030800c1c1418080c00010f03100328405000c104400c89114800341c4021500a401c03951201114005519403150010145820070443c002c1389180b410301500b187d01c80758061501590103440020b8545032046040151b4000170000c0810f00d160031760445683d00201000e1341d00c10030034401e034101e50340060002c20055104507600c0011141102070f42c1c50201d0160b22655 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 828974334 1250 828973084 828973087
    0x70c030602030730180b0f16030c090302010c060e010c030b010912080a0c080c07260c060d020f0f04091b051608030c07200307050607080a03021e0f03060411 69
    0x313a03d20b51640b1340c801402c0300c044002901000c107800901c010400960b020740011200020b03c05a00d041200b414880e22440500300a08000050200c08032003103500a80001401c00100f0300c0150301c10540c00d09414041d0341e02054809043c0c407000d003114180c90518012035900c2d0303502030306541c0150005000304140c12030501c0f290410f45800f01c46102c2c2d01d000e401003101c1482c1d01c008006400040e1101564450219414079480f18101d04034052070107802802044c1545101003c000d000400c400040c1c0e02500c0c060900c10080e800c50042e4000281700181c8072020f00c4010000d24482c2c000c0c10051900c21808103004410071410f01c001c0c0150b510031b1080040030450003454020680005c07007001d6201150390b50765541c0c640900f46500038440d00901c0e1401c041e20903502c11340040480d540a03c0110b094440c00355440c2c040101c2132061000003005d91000f40304500038103010b540902076154a01450918148250194035195071000003800404240030003807000ca4105407148203000180e000c4840d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 828975584 1250 828974334 828974387
    0x2b0f0c0503041e0305070305010504020a0905060a050f010c14060a14070e01050a2105090c030102390303010b252114040e012903070311070c0306020307 67
    0x20380300c0c4528025202400b081a580c3e02d811003104410100650f0010305642107143c0ba80781c514040c280a88090740300b0714829501140b0006c55102e000d0081c4801000340c15510b2612050140b080000481181806003150041020403180c140f0481c41001610190086190441c0802c0490304c4000b035a500c800008420040240e030800c0f4442e103c5442402e1658980780c090104442030000c0070140107234045c61000e40c1d506030821b900130b42e0213100c10b08199640712003c0002e040c200c0c01151a100c2c003a161a44441d16800c40c013210101165445a060039001c5003004407642c074551080e40552190000003481c58a03810040c000506000c80f83c90b040c41a100c07003a212040c5400c0105210900c1c540c0245c44149441c0c0a56002c3d2841c0100040d42c6859941c1e4500da241503160074410080d03c0c2a50f110242c001214094507001030000301c2100c0c508680315440110300829442c034000501840030800d100114586820a1004500c00c0c40d001da07585c90100001820340e88200707150340403900c041004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 828976834 1250 828975584 828975593
    0x50a1205101b08040c090608010902012019080f31050108061018080c01080a060608130c0918051e10020d0b0409081218070311032b0f0c 60
    0x11415196182407000f507221418110b030586010303841703400418505400058004819000012141e001341c0b0344041c60400c5000e004001905a2802c265582210b00701c90000140d840044140601030500542843e20a410040d81a80505005411402c100c2c040201040014202ca404100c072014000c59007480d00c1d001030020400980040d200e8100041c803001c4041c401c52141e00000500c17004c040c0b074907545001c081d0702c8034001c16150b40090f10141c002044014a4028182220466991164103075034480390032100c1c9801030401c56004088803000203040303509009100402880e05400c080031400d03071504506c1c180051442400180e04005025040c9070007003812030503204511005030303450920700400340040c0b4103001e20a500a140074044418040104058452101700125a010760b446400758213040c0380c0da2950340385141e41702c1441800060510907203041750748005021039140d21046080c0c0102e40000e5607410071101e03842c00c8842c000c1a4862401a02d840c0c903420200d080740c080e51036 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 828978084 1250 828976834 828976871
    0x603080a080613020408030304150b03010504080901170f040807031443020f0a1d011409090a03120902060d0b030c01030225050309030706030f110903030904090c050a120510 76
    0x1010382b4454103904540002c0301c140c0c00c84100a00020000c000c949840c1c40c100c84aa04445a0346002030311100594034920750f650030003030007640065a0102665516030f604000381d80140400c4003003100701d0b81104191000000644400000202814444c0a0010503040f111842e0000c1d6100790298030b42e03031909018100400760540c1d80640d0002c20321603846001c83e0061207640d00118841440750b08842c502502640310505940684510705244d2202c08200003070071030f040d51680e80e240c02c4620040002401a0340e50251001000d5010611407102d40019505800c924040300c000c5449405140080c1707018480e41003815000d090450802000810503440318252285402d0400311003401c0000b401001c205907500300a00804660095494070001005401911072406e205401c08288031130080c3c4a0050754203003440a002035003070000c0c04d0208400307050590810b4601544044020032152503ca004501918601d0340e0b010000f041441c01034501140a184250580d00c0c5c42ca421811050314407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 828979334 1250 828978084 828978091
    0x30c0a1503050615040605180d02010512041505090f010506040c0c0209100302030d180602060403140a0e10020c090a02041a0706020909040c031b0305060610030603080a0806130204080303 82
    0x740008850750b4030004a04601100d080c4038810b1140800d000540c168454010700c05001d400c66410315800c6007106000401104000003404924207010030000d480345107000e25889400b402c08411042c00140003c011124142d44800c815000b407409a00191424003036103030041700684040003282d03000c4000070400ea01d803410091240070b000c03000c2000314152805040107140c00505031449140604c0002d40707540300c0d401882800c200c0c2c44c100062102d00104040740301d07603016141c00d80391100b04d0340340040e0307640403e0300003040c001c002c0140f04c01521041204215043c0c142c00820464030715404002a804000b012070100c03c0c01000f041c0315440700010b03900c0c0d01e6911a61296101c1d040c41c40d10300041d0040e850140e800c500e481007044144103580c0003000c11a4021aa82c1e6004d42100c01c0660074030141d4000035003903034820400703c0c1450030f03c1c2e141072003e5400c5250018102c3c0e1030782e94545195000380c403000300061015050100030b15020f1078015442500740011460079280c000c81036124000103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 828980584 1250 828979334 828979337
    0xb010f15181a120c031006050408120304060e06270606131e09060204030215070308010314160b0405090c07030903020f010509100201050403030e07050f1309080c0c030c0a15 76
    0x4203014070140701801502e402c0f070040b400110b0a49403482030b141e520f800481da0f03a60b214100b4000000c030b05018204440c150f034094800f811100003003240700701d4113504c080c0c030882d4029515948420460b0342408a00e0041c20283d1602c6d5100c41800940e071400c0e50000f0748450b0940201051228035903803000d1310250f429044a01184000024101000f01d00d07410951a41c19030400b400d001c2008407903801441641e200f1500c1c018030341d014000220050098040c01800700d060840144081101c00d2035000109a07810100e071012216501c0c82c0d6088180c80c2e110b0741e4204400f240900092406298052384400040c1d5481e08260003514002c042e5101844047d005111641741c05000c0c0e4440d108803080e15401800005841080c600028028035040340e05400092030500c107000700310408208c4404a40d03000b05910ba003980c0c5507013040000013280c2d00c6c490110b0347c0d4080480000c0ea006014008100002c00949107804c00401418244506183e2003886103442c15401e0004002d555500d00305a0401d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 828981834 1250 828980584 828980609
    0x4050d0309080304060e0109090209060d05040620041409060307090c03020d021b06060108060607170c160f090501031e020301240f150f18030b010f1518 67
    0x95080c01d4503544007a030007408140c040000d021401582180d40c00d030008a0030382c1da0056559588071007008031300999910396441603040100034042d480641086070003c0c040d8000103090303488011411031b184941c1c0001d841052002c2410401a0681e90500d100160155000ca030b8034031b003030702c0029100e10b81405003600d07040d512320030b204d0341610a0b0705440c0c030414040003c640d180044908210781681e00940c0703a100340702d5400082c086510581e411802000d001c0d0146080200da0b0303441402001603038100b10104501409103e00d14102004134807021780c10042850300060030486216550349450300899101d42c288401000040c1c682c180745041e042160346004c0000c1c00a10000c0c0c00340101e02d000c80803800541ea280114611040d1141c4119030015103004425176031442d40785003040d4000c5c040c1001c945440000a0301a006075a66800c112350706000e40c0e40240c4903560940074020a030860002407080c80e10070301200d101651034448145640c102203500920010720018058007a00840b43e403020b8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 828983084 1250 828981834 828981859
    0x90803130c0b1612030c0e010509040221060922170705010504140d1103040909030c081914091e0414090309030d0503011409270a02010f0e060405 64
    0x600c1110805800b00d68142a03440d2a502e0b0203000d25845a00c05481c1c485280d8981c0900f24064030a4031403840c8103894100c420000040151402d800518400750000e408000181043c5401005605168403182c0d280520f4100032040c0030000c0b1004003040d8850200c2031444014036401d41c103281e00680c0c032801c0c034004802c60408c155900e005084000f0034070344c20f15041c001005000040d0b8172100c40358104503640340000481c21200a90001000c400c150000c10040c0440700c42904a0184c0c00d000f4200000c0349101950340d104039900ca11103542d08250407410080742e05078004c802d00c1d03554480c80002820940302000094440b44071007041c00c181c03405103001c80040c1e2295044242617001d40460031481c1e15042180c03d03240d51005481920078003039262a03101d554014020340e4180d903a2a03000b440c1c80c00f01c4000b80b101d01c20300500000b1066080b0501e00070340e00c02c42d2500e52118030425020382400c842e2440054108950403d2910034444981d0303644006031a01001d8800701c820480741040c40c001e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 828984334 1250 828983084 828983093
    0x112030507150c1b020d080c030405031b1309050309010e030c1018120317040618060f05010504020a0f05181018080313150e1905031009080313 63
    0x2141c904000e120301400007903005000c01d80d6100c285881c0d4580c07a244201c2503520100c90848001302c00080d0300c042c2c002c4000b4081951000a0301c220b0b802001180d141c6510340002074030b8180700612000084c00305144449640c106420130302c40b042400b450600c4018690b81e00d030740e124042e045800d4108400c509144440f50303020403039490903440182c80059084408580200500540d82d403d0002d1185101e00007841c0489510500c0310b10f40607501c0200c80040102e00c066004000b520036650103807518124203110360842042c40c807d17032280c1d0300010400038000c410015070300142d00c06071007a031043c0090340c00c154218982807004c0d03070b082c80d01698400f040354514001c020301c803010640049040802d01441c982040a0058511a09154451042e038034545075940f0302c2888400d1540e607444070030820a030030140101a04542c814200551021001e1020a06848501c2d0320f28441205401c000c00c1031781014000220241c0c2d04890600081788503071aa185144005081d00000c07024001e449030078030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 828985584 1250 828984334 828984337
    0x20a200109050604080102040617040b0f19050c030a182109030605012702030124022e0f0e0307331b0206040c0603020c070801051e06031501120305 65
    0x1060b00800300c545031626440001c2c000e40150003410013007400220100c01044100f200f030b074495a8000d421504a0341c44880f010f0000350041c040c6000f01c0361182c100d0a45c11450f02070f1a106031402980d20391203260883c0c010301550190892600b1005107601018085103080304005615002d40d050f404245420460440343c819059002600441c1b909001056440b940d0040451060714424103011203a100006902284428840c800b4104404068981005242412800d07201c4c018019943c603c000c0100c0540301b444d060005171110261359003428980c90940c800c000c1040510101000101d0b0002d0906640e88622720002e00154580040e10521119035200e00300c0c4074104100c001400480f540c408405014860414100c0f0304070440031100303d500c0042d81c82d200e00d810040050407180ba03c50150000d60001d9101c3e070a41c020002e001c02d4400d402d0140b5800ba80ca80d6242c0e1440c20483c2000205d4514041d02c034510a03000050400d50003039442e88a2419500656402c0c184820b20389002e0302d03d03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 828986834 1250 828985584 828985589
    0x302071e030213051e010815060d0807030e010219030e0f0a1503050f150105030a050a0e0f061b03010f03120306030614060a090c140d060e040f12020a200109 69
    0x1020802808003101e010f650403242c024240070369611480c0281001d0381e1800882405544500e80c1708001e0a030321280e014100b0780e002030700540b8200e40010f2584881c80c4d60340c01614290f01088502e81070082550381000b060750004103042c10a0b8190340c2540e001003d10180324800d074450125032802c0782c4942c0d5400300000007030002c80b0003a40007041000014011f4041110320f542d58080482c0040e81c507900a914068050f02d05940707052840d6204003280006120250100c8046d9540e94007a85150f1402c1090303601507034866000700402e1600c801d0a80000422005608002c2c5050004101107000e4400d2081070700e51000f0346020030340185408800030400c0d80c1c00549a1350421404201c11070015034801d0045201380e5200c5d411a84440c0c07600140c40340398080c04001002e40c0341c00c000348522603016000c003400358070001c90700e20b81e645501d5003603030b00a58065402418010b0990204a007561f03030210501c000d8000b401c0d0300000c0340c440c20103405402032481440440e408100746180e1103090380902 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 828988084 1250 828986834 828986839
    0x3030506060f0406021b0307120b0a140106020705040e0c010207120f080d02030a0f200d14071106010e27100c0e0a120b2a0c0303060f010503040302071e0302 69
    0x1180c590b509402903481d82c500040451b1466003400840190a000c901042a1031100fa204082d110a5130384850310017400605d060306041c0c0c3c401440356410528141030740200b2840d0f006200d4941040c04120890307030007440007407850380110b400c520266004107108040382d40404420f030b000c1c1c10038100280c3d03508181c4001408000c0000e245c0c0c04041995005d1809204110420000e003130801940d01f08071540031200401440240090040f41200b070b500900882003d2480403138880380800c40c41c1040001514174601180c0c14540c0d1a00c040c8041042900511000c400301e49141001c450004800805151051003c3c103036240b407035000f14081001c80f0900740981d030208841800024000c2203006058844e0740b0640340003c0000b0020704203030b40e01684580051b0070485507168200c800940d082c1801070002400400341c0d03010041110a40900f05407040701018607501d1802c60708102c45007918036003c43c140300050003804042030340000c2283c142c50300e50300308000402c0f160b4500104aa082c0d8402503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 828989334 1250 828988084 828988087
    0x20a060c1703010e071101050f0115050403150b040e1c03110c0a1101031a1f2105040204050f07080610020f07080a0c06030b1c060f1a150906040303030506060f 70
    0x16889400100003481350f85e46694103802c1403003000c0d0b01800da0780c041d1a00030042d803035500180703c800034010950702c003140103091161825a070b81d528048408a401c1e80d011819981d42616460f6040c940600390f00d0401100140003004142000c1403034562504200a0400d03a0b00ea045601925a074400c452601c0311100c21112107031075a19040b9510548840841c0c00070f0b0401d4055070018060100f801960840103243d50303101440b44045150501c5e68498910401803500440450981e0020006100c0c090781e2001144602e413500510050324070141c900b040034040c000400c2801580103000503080202220202040d4100e440200c1c60820580a040c2480c091094009280c42001031600c0c501c030f100b034403610a200daa030b0405908880b4405d14858014503580040c1d06540c0300041451b802d14032907480015035282d1403600f40b04440d000c1007a00903104180a1005640c542800b10b0019081d8460361135187c0020240170070250b0085100050034503403584007180c100c6d5216800c0e60302007103000000d107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 828990584 1250 828989334 828989339
    0x120a18090f0504060e030a0c0206072105030103030e0a0302090f0a06051f0e120309060d0e0d0c0203190201050f0f0d0507090317070201090e0624040f0e04020a060c170301 75
    0x120003441e050f1821a01c0030301d45400c3c0021488048252951004591550815040507400744102c1e5484036034121040c1c0c41240c030a000045440c014140310306600e54401e500c81d03041d40b40140003414103404240c4a40708441c001c000503038030043c2c5a81d01c029080450300040d201c03191740030080c1806800c03440c1d0003c240c0c07000c0044080226443c120718012542c3d0000349402c1001030103000007500300f602280c3c0d0401c21106c58103003400b0004001011659a00103040640c2c181d42c1420000c030210b43d030002451000e06102549030130041d0642440500740e119210343c030a5030000e0040d108040c0a0440450080341c101da00070f01001c142d0301002c40d42c9209000b40d141000d0000c0c420340f05030000311584100055501c403031030a02c40903194030540c1030316900301d5103040c0300d000c1c01d45803802000d1035031102c843c52401c4003400c08140700303030700e8103006078803031740d21182131007054200c80c502da41100f14a686c0d40c0c41000056074841214004441150401004007200d41c181b400180b800400003410080b07000000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 828991834 1250 828990584 828990611
    0x1506032f0d210e1c0506040201030b030f07031104050f070c06200d0e0f060f06090406110d14280b0a0e150906010c0302060430030f0608120a1809 64
    0xc0b2081c0542c02c856003e80140051000c0303101c0161000d01905c664882c0380001c00650003903000b018045001002c59550b4030f1620112880e1400e01d4004981030100c4503640d088a09180c01a50b42120205246108510307020038020030a14900e200034050b591a044660211805514885200140341c1d118a0307031406100c030301c0e41c0600100c0030b014144e403080c2101000242400718506000fa00c44400f10f005a44a20040141c10040a4800d40340d4607aa0712007805000c01d0000181550403030004041003902e414440c06110283c0201b100544098040300780b4454100c1c10000a001c0d880210005051b031451008103082c214150440000c1901030014070522145c0d04600c0e035141c00085500c050182ea030b48004540c9843c803502c000b0007581c000b00104002460310411010940d0103581000c07451032104521900c0e1101b400000000700fa96542c6c410030040490180001426914000304960304010290200501c2813020700020000e200110081c0000e007241170000920040c0002c0c048140020301 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 828993084 1250 828991834 828991847
    0x408070e0919050d05090f040c1107091a060319050c1c060303050d090303240602071508180304090f1a010306150c030203071506032f0d21 61
    0x14900624815420382c0644403084025400d4500d40c8a000791540b40351140301642d8941040d2030344e41c0c0c0042051000d81040c1c41c1c52080007041095692144208802001c0c0b1505149031500203030417003402c042800c011340805521000c10306000342d035041d95a907101c5500c10b82c007c1c1080d0f1200309440c208010711591480840181c6000c0c00c11141100001040c0901c100464805120046c0414000c0c80400c80300042c550000039618040d080c00b007620009144c2d0141e00e42495034156074032071212181800240c1c0e04003d01809014240001001c000c8001c00c06458030000501a8030680903420360903209400134401c2d18000c10101005020302c0058290090103804000204402048480c41500c001e41c400e014900440e8518210020044002c000c12100314001c40c0e0146c1c1544810403525000603a5020380b400d0b541c0d010100000d0071419454240403440b01d01a414111840700e80107042d00c03090040616404120840e03000c1c4001fa00c5103051982e02c1f211240d0000104501141c18000c20340108 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 828994334 1250 828993084 828993091
    0x130f050c04080f03130b07080c070e0a0e0105090a060c020f15150916030213030f05100506060a080a150305010e0f060a09150f0207020d210806030d0806060408070e 72
    0x20165401903411095407941d81c0900d0561804002e00c64500708450001d140c0103251040c010301c4230b82d1074401e51005041c6890f8090344844410700e002d03410440121075030700c03900c40b038002450000d00c03490801214050790b840f003200300900350517036400c9400c0742c540c001c20041103000b000d0004c1d181c0010081e050300c4c4403820101c820351913002c8206000003803490808151403241800e0303841c0352002120381e03008600079040001610b101a48100d03000c8003081080b10009030903071003040144003140e8048444d4080e628050724070340c0600418050403c210f038020710b031664414820075002500740092044440c5660042d80098103c0d46402410301601d04041a0610b6100309002164036031340711400070404560000e07501600318011090485035584158109403440c4c032903940c015052a00e2500050b20400c503015084600703507011201d603100ca1005005803104c86041d410004203d10300003000c43d03200e010b680c2011080005840000d0500d950310816500944104012a41055210302c580d102c210b5040c2d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 828995584 1250 828994334 828994349
    0x190807030c0306050d031d0d08070515010506030103080307050702130f0e2a03011506020d0e0612152b050601050303041413060b1201030308060f01020705130f050c04 73
    0x1031078034020500902624048600150203006004469241112a05080d00401c1b80070780e81c2055030740e070303c0d0351f0742c0000f8800b1030141c070081e95907140714a4010f1410310748150902d107240c103003001000b050b51207005880c1106e4102c00710782c1c1e495036200b104a600e48150f0714000d41c40320015280700b00110301070303000814484031414100700c2c1c4020324094950740c0007403200102240910020911441748512024215040044d0020807040c60a000c81450014190840300040c1c0c0145c0d210501250b00002c80302c208031040d1081445e00244164545402500600c81481d207039a1000080710703602e900c040b003000c40d5401c84038004030562408030160701c00500031054503e80f1402c00042041e01c2c002c01103600325100429424034215032031046c000031480e01c81d25880700594510300010b1500d84040148120481c102c0740307801641c110310b8041e00e1404040c10460050001021520503a600001d40105549048441280000d014901500540040468041c3c41402c06082c80740403400a0b02500603103484 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 828996834 1250 828995584 828995591
    0x10b040c0c0b07030b0f010e010c02030f03120f010803090616020409080d0e030f030a0b1f0509011b03080a020d09140309030d0206311b060f020c1e040219080703 71
    0x789034084094410444a2503880000d0780350306c00b080d600420b040c0c03074900010304040640c10141e030002802e000c0c800031000096080040d0655521058010301a07000405508002680d41096116984c034000c2d00c0015015404c0060150004030065800b0f40300194000d10601c0140c00038540054030b900140b110301c01c8a810000c00310900d10000c02620050743c2d4075690307a8115034806038910090709015002c1c50300900d103030480d20150329085140c00c40e444400d803101d0ba6550b85400006001404500d0f080e4501e16440301c502001960204025403c030604400160f16004401900700c000e0809140c010b01c04926810b450801d000041b01030104e92104506440c0184032005c030a03030700c89104960034030880d044c3c51a0340003001a0401c8100d0252103a000075a16100c0907030b1100d03100600038003107205020207050b040114541c031040c0c603980b24140d44090800c401401000ca0081e41c01545002030803a40c803140d205803a200c0d80d040e10000d606045aa01102d01e590401400048059a10400281c10b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 828998084 1250 828996834 828996841
    0x109020109060f080a0507140a1d0a06120b031c080f010504050c040e071e171023060d090b04170a0f051b1b09090105090a0311010b040c0c0b 62
    0x3d12000c081480341529529090782d2035241c0c0e50001c000091a01d000d100c4504442d200d40005140517200d5601c2c0d40e01d40040c0c0b401651580e05815040800892040e400c0c2d0034280000c40c0c1c041c000c60b09080707100c2c00118442c100400002d040c10302a040c264880e44410b605d40380c2542c0c0c0300c40071340e008401d89000b101180c2d07219401d00c002d6a2045a18041c2d020040108010200011f00156440b101500d0000f00001416540c55100c1d600b5101c0b1100040a15000260615000e5480347e0482c540c074070000c0032286850407030301281074180c404694901890392241c40c1030b1031380001c40e03001c0340d12940100040700851802d41c50380841591b081d00c161300d80850320348500c14180202d505200b09600c54500b640e00240c0d049030036600110316907400136140c045039911a08100b080440000403110258800c006003010302c00c0141000f018803915a05010610042ca800800e00200c1d40703400d4135003000700c00c02c121012401750002031a1355800c6032130010410001c580c41104036001f04d200e200c02880644 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 828999334 1250 828998084 828998087
    0x60903040e010e011a0f1e190816030e0319020f1e070b0a0c0b04080405040b03030405240415020c01030e0607020601090e010608030d0c09061e05030423010902010906 73
    0x31424001e18a4980d880c1030300080050b151009005004100c10425182c44480701e556203402a10310080c550010011845000507005100e000ca004041442d02780c486c1c0c40e040f0705048005101d0710710503040c07541d50a4800e41100c0c05000b19546036480b07941c4079a246480c490000d50b200c81d401c0c41c0c0d14290082a5907994a48034840d00054121501c000428007141010a4881386920010a06060215100d00500001d003805480c0344607902800746a62194030303000610094031020610107101c2e403c04c020034803c9035a00c4420640a61445010252502c103040c92200144169004402225568031461141650004d4602a541800c0e6400d106100d03001d0380d2950f403150165818000b58225100501031000c6030741c0952020f510716030000c1400c1d542ca07102c29085a020b005169840b5480d102d60405098005100c7c400411300c5140c140314030704a800229640201c5041c0c21810408000041070901100a207250b041004c903124208441130b03044905402480180c500b01d0209a00150014a4a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 829000584 1250 828999334 828999359
    0x41d1b01080f010e160e1305010e06060c1507020307050601151206060f0f02070b040b070b15010516110901080a06060b03160309060f0531020f010302071103060903040e01 75
    0x84c2d1240c0400d0105441d420a0706803003086030303098041080000340000d01a56100b003401c2c101c3c1da4a032240050254144944032044407402400c4034050041048400702c020400114400256451446142986c845e042e00b00d0461241081c0a803061168200214200706080444003501d8405c0c1c030380084140140d1071000c2615918400d04011810004480c0c001d2405015060a000740300d205803091952070302c8510880d50455000700d9030000c80803580504001c191500d55130080e68240042c410700c004800001e049101d0002090b003c0300004181c5010001c800e20030b655400c0e401000613949603100e030441a5034242103c0c0030340f402c03810040005802e03d0102e0440380a90300410482c45081c00c154010f4002d13000c1200c0441d901740d40c8055048080c4071f00d1081e00c0c002c01640c1680e40c1000340703070300b12000701e52006543d0a0800c80712801c0c1c0301c0180d8460744004d400c138500382009621944a420100a0318803204c6142d6010301035541001034104000c030091040d0b0b140f62012158503602c0d094040741c1c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 829001834 1250 829000584 829000589
    0x11042306090c04350312010f030f083007120b01091203090f150f050406050301140d0f0501020c01200703030e1606030c0305070507030e041d1b01080f01 67
    0x45200f000148010401010600d401020103d181c28120000c1c00741c0b0030311a03150009662140d00082840311244001030612401010f020000170320b0541185c64001d0a001824801044401c00107583d00010f041c41e030302c1c5549d1410300d08032020340982e00c0c5441d07a1100d80c00c450060020b01914600c00d02c04a6600c00c603001a401a034560f0352050804a4034200d0721040981078040c440b140100007207000d455500400980b0b800c081d410000304140c01d014000c2204902c107501801414002032044c6548030041c0ca044540301c0d181c0626850741c80021440340f61000342e0240064080700380301800c1c03000540080001a405a00030024103440542c00e0700307501083c9601410381c032402c00800c2c004c01d05c25007001c1041c11a10043d90200c0d11510031512031522140c0c42134010a440d144450042501440303495400034950401514006031942d0003040c00f50400550b9100d02d903200c0040340d55001c1d69441c07c1e031050850b070451300ca4400d0041c090b100c54039072203c00e9000036502c10004216041c4002400d04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 829003084 1250 829001834 829001851
    0xe0a0c1211060a02100f06050a0803030405031602060706050a05150303040609151e170a0b1f05040803361008150603160e010e0307030204091104230609 67
    0x8820070040100241d540c07140c4004000c501c03510315107811100c414458031000d0801c100c00040d2185c03400c03051000c140342c250f2141465800a00402011070004000c481614210110240e0202c03110300c0000c08602884a01900b0035107040d04000105407503520543c0103c103003207002007980340321604065484c40399018400016a00410410194a070a21a0260031280d410100701d0702480803810200b003640d201900380000c100d01303089941d01102504851708807440c03803000d21061401c1c0c404103280407204151b480881034103406001c45d4274400d2059030301030721000c2c050325a0748400040100d1405095600c02d54041705141c504001000e0550240c4080000a40304080c00700080c1c0003580c10307150082600100030444401c128144d0348801c0154440c1c01d655565411144c0c00680062258020341c038124140300303060100f018166000103001013240c8e411200442c100d10340e0700c0c0001c088100344420f02d800c03906281c0d040d402149200c030b82490100500c1c001c40e070b565135401d040241e02901070fa40e80700e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 829004334 1250 829003084 829003103
    0x11070605090105090454020f01110d03020702130207030c080d0b100f0206070e011b14030307031b3002120a1a150f0a120e0a0c12 57
    0x60154043c00290104160003000012902c1400d12200000701e1594208034030034550501c129440c90200c4003a1a02e049419075150701e038034404015608501c00c1c504040d2103003030380b0744582040360f104201c0071a5120091041e105d0340340348140d01a0294102440032449040e00c1110110f85050fa842540c0e502d0750103565800058a40d902e800784903501c08652a0802a168481e2002545811030b0030a2651034070780d202d200c10554290004c1c01d26401030a40c13400c00c2442000c07000ca030303a070000c401c030582e034035103044501c118142d46070101403518002d40704075080c00701200300310225030140e1106000041c8030307400c40c20020740110100c81803812101420a100c00b810107880c4100d001e0316408050790120341c80103180c074403400c1455201090444448018176103824800d031072000310750540c2c45440b000b41c50005100142e1500f80c451030180c80c9400400844c08074101c08010b01c60030000850b600d11500802100030001c107a41e480f409100000e48030341440f68400103400c028000c11001d800e401000e442c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 829005584 1250 829004334 829004347
    0x40e0303130f120503010e0c0717030601020102220618060c0609020d020315040c1505190306050a0f091d15060a05120709110a170c13140111070605 65
    0x3400c203003507078000a03a850720038074a24100261840f01001d414150319282c160300c80d850301441801150b4000e0166650318424040700300040c05064040700c91030441c0080503125031351100100e00a000e00c1d200c01e50101503500007101c0ca00c103c45460425103189070340e900c02804055064011040e42d070303c90306000410b002032480c046070711640040c050901c000c10229240c80d6940000b45840d00850007001501401e4040c0400c0004441841c4000c0c41c201c142032005a00b2a140035007140a8602841441c0300c0e00920880128841c0d8411006010010a8900016101c5881c06410780c40c0b030154010803807501c10b00c00203074844032003110000c9070a040180f0f61103200c0307068404503460140c402c642280e4603000c00300d903990390001c00108245011008080140c038186405094440d240384501400c1e8007000140710300344d803102c000c111054038071218041c15140c8130703040e078114400c916201a0108003150080b070482c115600400c2d589000340d88580c1c890401d0b500aa45444031440f9200204c3e4080148 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 829006834 1250 829005584 829005601
    0x50906010b0705010642020c042403051b03060c0412050705060f07050c090c07350720030d18031209031203050f01170f1b0f040e0303 59
    0x2e010081c414000840e6855441110104030940c003c074242151911208100107800b81c0703441058103151007480c000450116000194a0b0b007903a40d0354601840d118138588003038008107402c0d1021111180807812100d581c1c0e040c0380d03440700201d80d02c020506170100000d19952500042c5039000d14681c4213181e11307080c50300c5003030700340401420407c0b038842c000c10390b00040315078555001d410201d1405500d2980c40c0b1980c82c283d41016440c10727403144a1b07103c51003404001c00346101a100d07100c0c0e0220f0b01c8140c0d0010b6000641c1e2195007903038200345094982c0718241300000c0d1440500102840b60354080454010744c00a1800941e0040b5441e81551202c841010001d1042c03a2076054603d012144944841d201d48640c8961400c0b040b41c0404038050710010401c0115040715600c80b00880e00d002c002500345458802e410501c10310441e8111800405020702400081c02044c1030021400c080b65258542e29450840e8644000c070058030480a404403000c0d6403e2a0042421000d180e90180d40f80d03070b952150 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 829008084 1250 829006834 829006837
    0x14040308040509040f060903081602120a110703060603110f010215060907030e03070c1d100306090303060509040b0702070605070807140705030f15070903110f0105090604060e1201050906010b 84
    0x1c01e580d1740c40c28903142004280d43d442001030440c0265194201460250f80d0110b00d2440c0095031300071036010750902c02d14200324009541c0e9a84481c6071407260441011800707498144550800742c5107501d00000001003181007001d0300585c180980f50714081c08104801a0303160f900941d182d9070303c0c1c403068000038894500000650741c4440f41d0b06000440130901c0c4070003440c640180c00d084400b84004802886685451000124101104826144545450141009a09454407008050b0303034550008800b010301941100000c0c25005c3d0503800c0602c0e0509100c0c10401c0107030394080c0513015806010900601c100708407401e075034005030301501e0012959100150600110001581d0340078608003c519554248008550700c00c540d4003c3c41403a243d46402c9400340c3c0054184d10502020031800c2000640f11104614640021103112110092184c0180c0c4d891148900c203a6101c94001004a002500310700c4030007010302e06a0300c881c504046842c429080382d400342c800b0841030b80024010000a1427120 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 829009334 1250 829008084 829008091
    0x506160b100f180e01092303190c02090a0b010c29040c0306050708062b05011b020105010e06151620090603070b090f060705190314040308040509 64
    0x100000c00307503480003082020110b41d0018030403045950301030b8070240798038040c00c0c14155000700200024030407540c070160780d4541005005602c80c488075240c01007a41c203200740c1c6c400300754000380d103403946285070801000019040c004038403811078a0046810f2449034030900e20b807560182c60300e8400003002d40702c451b802200301c44c0441020a25030004107032132030307818203841c003d510851405400a0071072610105032000109888100300c3c1030401c2181c255501da2424046071580581c3c0400200050a4a03c1c0d80a00030b101904d25824810704900946946408019051041d40208000d0f42c907102130036201e031801c2d64115800708250b41c2848074180041c00901281104045041a21101e55184401c80300790a00804802d2114403440015080901d400c80d07005000301d003c1e10405081a80c000743c2c1c0d005900c54240240507502541d1150344407003048800b510340100880d000d000320f00b1030036400411142c508a001485144018818045171425502605d83c00785250381018105030074420450b0008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 829010584 1250 829009334 829009351
    0x2071404090501060906031205090907110c09250503091e0304090509070302120610140a0503161a13120201090905150f0307030506010302060f0f041e0506160b 70
    0x341c00140000b403003440394400a21030794201207105451801c001c1e2101480145440610008001d22816541c1d521182c0394082c0135803c00c4081e620310382d021a442e00540c49842c43d0401c20003810b00c1202075184007034107807a0f480036071409c1100d0802c440458850100f92a07065940d84130066075a03228144002c61342100b504a41140d040540d201900c0e02503c805580b07030805604694410720a5007062030069080c0082c0350010441d0b400c128807688046620351003880140c0e5061901c0789441d07603a45801900401c00102181c024141c0143c032880040303038500c50141320820555a00c0e0100d110f603001e60b00c90811991040071442c2c900080408441031280040341001807180022410304490310800740100c0d694104484128580c0d070a105829001100d0750703100341e224010810026000088283c150b1b0350544803291200c030707000031860060283c103131031000340c0c54045808644240140050301e6601c200c20700f0740109580c1d613003d00565104070110486410b50107400d41c0701052003c0d8402c0d4110000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 829011834 1250 829010584 829010591
    0xb1006081b0c070902040501020c060f07020f0f13270c092007080703022b03021c18150501060509040506010207032a0801180b042f0315010602071404 66
    0x50b90366072800c00c045a00000b0416502280034009560b040200108400c8255410342c98100040d030355030400d018010000f4441c1e1199518800203440789600a410314101808540d00d00c0308511340e54024041000741c404030204210044c1d0702d070380034014110b154550441e04183c0198245030395203000d4115204480f62250f0b044811991054031503000302002801001c0c00ca031240190b24000341032000c807200012818101107040140140e82403400d845a035087e040040c0e98202624041410745400c0d000100c82c0c078500b5a000000401e8244103050340c9210b07142072046644484140c030120303002030050b43e000541c01d10205245041c180c0c010380c0c20100500484070b55130350b0b95903a00104c40040c58140f8005448105020300314408007000c1020b050010300034050700307003602c121810703802c450b0341c000c3d1400c040b14021400f4030041101c112000000304c0d030f0360403103d0303020121084145000e00705580240305000c5603450a41003039800c6410ba4005a0140400a292214030440e01c141c141d0b0459001da0fa = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 829013084 1250 829011834 829011847
    0x1c02150315100c03020c0301060b161b0806010303141c0902180403050c2a010f1101050f0403320901031413020f0d0b070804080702060c0a0b1006081b 66
    0xc90010b4000c1c09030150b51925828155840c0007410465118040c6003e03a0600d0300170300011940702c040c0d403440036500424902d42e240e1400e00480c001500c0321815034a02c040b244c041101c04000c91002d06803070017a2180c180e20a8620003c1480c1c1c030901217102e0900a000d80061048642a000300c3c1282d4001018030804402c2010256180d15040e202240420030000300c00800000500524220700c8a14424103528040c9e0048200751101c035000c594100a8426140700d41e090140c08812884003126000b00060328100119010041c000d03203081c0d002c01e242c2c05222041c89205504806000f45d21540c0101c1d00052070480c68150304002489418140c0b0b0f030075203c000801c246901c9201d1030b0240a0740c44440014014450340d8000362480600a40c010040382c0d01040108240c8bc0d000901444c211007035a0390381c20078920600403010020750010000650664100000842170f880314010b41d080001c80d05c070710444240000482c41900d003c03034241c0001848285811402c40000311290500170314280 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 829014334 1250 829013084 829013089
    0x30a0e0303091e07063c03090201020c0405010b0a2f061501141c090c030803060f04051b0d1d031215010806040b03070503011a1c02150315 61
    0x4004a8101425038030154802000c403d04062005483e80000080c000760790800100600611401303840c103034207210000d40c252030001034103103000c5400c40c1007850085024002100402600c2c0c1d584007039006103c0c55411005c85e291070701c1043c1c100d400b810201450034840c40d0087c1c460302030030070300e0281c507414030742444504250034a2240c04074101100508041c0c80c204030b850548003502080e032810040c034405100050381e24881102d0154880c2007004000003956201440a412803400092500f09005000400c02405001440c010041140d4905144250106000490350b084030050244c800910007a214520914000d0481200040010524401400144821383c00c030ba0f40341851030b40001941400a1400030007180c124010031110400b83c0d8050340007c180c0c40010b0704440c4914dd503054a448144c0e810051200205809002480f611f02071820101c80c1c205041d038014082c0d1501050420500f06004901303001030f90040840303900e400d0309030000c0d1080d00300400d03120361560754191420440c3d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 829015584 1250 829014334 829014337
    0xa050d26130801050903070209040f05120307120902030c01140d0612031220030604020d0507090f0503060408180d050304080102070606121a190912080702070b030c030a0e03 76
    0x409840c20300d1980c44a41e00740609210000c1d41c82103070320380d1600c010312003030b45008021075100540442d205441030300c80d03050000020900c450001c0540c07003800d142641c2010188091845a2aa80c841d0315880e4211386076401a504d403103100030b5054008e40b4107000700c2c0d8041e800740c02d0f400f03041c02e09003414070320f07401005011107640350849154070f500d04d50001704041e8043c0e00300f42625603415082c04a9440c034084c0b0340a0070186100107110442c04400640c507510b8580c1660304200e54000d01303011900748008050110882c0e40a0344000044040000c9064100001e01034001c0740d01c81125403408418006660101116208060317000508500340703000709404201401c050220003000580e100d030145410421150540e124507502035072030349101c012826039012030542000f03511845055940d04010101c0d9507045440c0c2301c2040340380007002401d00040b0558003903001d00300c1d10380e041103886201c0241c2c0da8041e01e200c2d80b011036504000049452700010003641d04105e00c6003002c112480340b085004d046 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 829016834 1250 829015584 829015643
    0xc050d0e0307020a1d06010818030a0c0b0106230c070503030301030b0709140f010c05160311090903030105060406030b04110f07120503060f0405090c09040c0303020c0901050a050d 79
    0x394000b02d0080306600c0c2861564008091030f0380310018203581c403140c42d140d109000300494140a1030300c00180398140d03006441d08007000c014090760740c3d900c42148050b280048100c02542e4002444002080795401400702c0f10003002c1000003502c2d000e28945c030003112580200d9110f0440e0044060000b0b5944041020310b01852007031070b01d00400e241c1079100503c3c0f840254010701241000688000b1140c45008010001c0d520078a8940401181410300501e0000c00c1454034402e10701c07101002050044045c1e0051410030210f6140395103132106e800300d9075039001c00c2c0500c56002c20100001c1208600070b9101d0642645d02030b10116000400d10310036007058000300701c4d244180c0d100040032810445100d1001418841c3c0d030403c1c90860902e00046080051a0202c044c003446d07407500130171007800040000d045100c20007000740380740c2d18103850b1072108501548021800b41c4100c4861a00710702d003140b55a81690000b5100c00307034079443d21080040591103488240e5102e560b01e5410400c1030301601d044c407603 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 829018084 1250 829016834 829016861
    0x6030a02030313090e01060f05010e0a03080c24090613060603060c050301080f010e060112060914030c060f040203100c120501030620040b030a0b03100f0c300c050d 72
    0x500382c0b400c00c3c00c4045d20b00c102c01c00162645815000c0c0900004081c3c50300641b0780078030301040c40030751000100b1203c280c10f81002c0c01850b00442c484c500c4404c005039260b250000004803c81d10100022080d90f00c5000f43c4040150350005030004107084503e9031003007400b81c012000852a180d8903107520b02201d0300b1700340250016200000510800381e0410000c00c04a100e50002c110800650003103945414040c011003081c824240300302c000780301c00ac1d04408026500320f6101e40d074121403504460355990014810002034000c0c003000965150340d48050520850300070b0302506c01c445e145400c4d040100012007010091010020304100700700103501c101400b80d03100302c0000500f680707921014500d0300b8607002c441900407002c04c400d00414502e001900d411004044010a00301480340000b401e24040b4024442c1c05880c1000040c580d40c89500a5211000d842e01d0740302031510103140b0300400f101c03d100200d00e1305051501c06891220380f035010100001e4146480d500b4005d55040e02010396408005880 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 829019334 1250 829018084 829018117
    0x103030c0c0e040c05060f0918040201110f10020a1b03090501030e0106080a021507080d09020f01030c051206010216080a2003070603020915030429071706030a020303 73
    0x82110680c031600180010b000c400c2100d00e80b40d03032001c002d848207001c1d00c5d004840c0480c100042a80c0c2a0903a20b0003074004045240100311000802065901128182d000959800341c114088002007101401d40b401c0c00302821014429800e058040c2d0312101d0b0410810402c8d03c1a45140c080421030585442d1007592080d110600c0c110005056a41d0715400030030a0349003007020880c1110000d42640b80c194182c8140c8601881c00c0d105203010b00941401514500f00003860005012082e8030000246100701c5140030313648400c00046044840480410000c9117007001201d08043c034030f696003940182c0510450784511480382c4406e0704c2492a500c10301d496808441d60004003e5810a81140c135625801c1d600c00b401c50010000340c0d2507946201e600f080c5940010010300e1034494182c0940d2249240c0034075980c81c10149898174a0000d81c520700d49420401290800445900d905014040da00c5551003807081604800c8481d1180700251040760706114000c04000162000d01c0a0480300412800c030300c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 829020584 1250 829019334 829019357
    0xc110109181d0d090608040204020705030c0706090812030606130f090c020c0306060a0605071e0f0b13170d0204050319020907140a0f182306130b160803010303 70
    0x14010b05030303071003921542600b003048035041c055407181441c001c1341d80c2d51400040070344441c00410000d00c1119030152a60000040c0400e8011001925200b00d80540e80c8040c50150f680c1103090b1a4001c06580e500c400d2000c002080c618500000030340200000c00750807031121555072582c19801516039010741c031095111003001e100a40c0500844400c2c10307096010309044d141900001e0121515405070101340400481c203001030154a003100c0d41c0603100760450b540b030b4542c07a040c19903950034410411501601124001041011030382c66a1034203541c0464a68083d51907807200c00c0e030035000444e80e8070f1425800c1c40001001d40e030030130a1480c1c20100381807020b42c495080c014400780c040014014001e1040883d04110402107101c111203c64030980382910600440007001c0726444c2e030b010707202c088807541d080d000301c0c034440781c607000810001e1040c0e4550001100700d801e0002c0c5000301c2c4003007504000029020011010140e000f01518403511050078400d81c0c0e1559011025082a0015030029241080d43e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 829021834 1250 829020584 829020611
    0x603071e09140906090a0903020307061401172e0906061d070207122003060a061707081002070c1d010303140708090d02150720040902010c11010918 65
    0x100e280780c030b405540844952030000041443c40d40041c000e142102d40e90301e0501d0515100b407059800d46a44070b1018011866416001c034003240c0280181c602401566010411404c1c000404400c0f86100c4040c101401c01226031140010b41c9031a10a0342032620382c0b08245c002002d0348240c0d005001100e04030034040745004a030702c0c5041d2000700b5060035940500401e1000d0302e90756017a180b0b4582c0c0509444000c65503204c4101101d26010b0320f89805100e40020310007900002d03041502521816101c008803000708600c400d592314003910030104c107038110516400b41c80001750002d01ea154001c00440c0c038039642c0c8250b0f420442010140030200d58242c40018410503901036101414805003d501c0c50400354181c0b92140e03544908840c040c0315a083c114031134115101c2021409002c1c50074aa8181c070b5000c1e0341494003200a48200c14240004140030810407407070316201e503032030700e80d01030b542c1c283c460701155210703211071240d4426203050018107580041c10341c820062800480035a88804070b00301c885d0307110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 829023084 1250 829021834 829021859
    0x18060206090738070602030405010f15060c14010605030712050f1204091d010e0d02011b090b030a1806060e060a0305060604110705030c060924060603071e09 69
    0x7001e40031003c0041e50101e14000344540c5085000301614941c00c01e41d0109a40500c070300600203003d180080100410b110066100b1000c1d804114000d102ca501d680e0040d940404a6014080c0450036103807a240226000884480302e0302d04150000515646910000e4038082141d4440b02513240c030150018108101030011007200301801008207010540b0492800c010300035401040c0507035940e0450317294030b00f031407800740307400200580004c01400708401081903c40d1203592141d00075608004404514086644e20341ca015111980c0d954019800c10100500b00d07440170340303010145c1e9228050342640b40c522281c00005d20f0301c15000000e42c1d524203030911843d2200281074500c00c000009040001c07400125175290300c82802c1318001004a1703855010b24150140c150701501c00e10000c45c40c650b904100081c101d02622100c0100c034442c448440e0281c1c0419000c224400c2850021400304165080440245801c40d0050515110030391103c5d400d01c0410482c0c00507140040c1802070b041080d0b100542 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 829024334 1250 829023084 829023089
    0x50c01090b0901050904022b0e01060e0c0a030c14031315020711060d02070c031b212303070c0501080a0207021528080103030305101202090601180602060907 69
    0x54542c10040325400107002130244041ca94042c03a00020004a00c00c1c1107140b981c0f0981d0410008808410041c00d65001007001c4480580c00c2d620746030021070391032110035403184545c41c071083c0580b40401200d412000f401e540d5801c01c05005164550040301ba9031a805988150b4a0307003201c001c031041c2810444580300361002c03c9901030b03104228040214883e220145001201903800e655030b099000b016400901c00c009002d0075159060300e001c010000201c0741403180d144610740c00d06040e0344803403402c54212410400789003402c11402c00440002d080f0444d00780c4c3d0f200c1000c81000085684c202250850b030004004070382c0d4800213141401a5070b00005c5054100e048503030304508160156000c40e141c550408100616500040b99151b4102d20f501054001d00d000e500743d4940358404080041e1508400f0300084000c02e0600000882c40303202c1c03001003011a64408039001c858115034091000124001e0f00040c1000000b0608044030864020060003d081ea50b000300864604100400c5c1002c0c003c0c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 829025584 1250 829024334 829024349
    0x1413050601060e060d0507020c0a0b04090534050706090602090a0803030915090a08160b0c0f0409092a060210092d1703010918150c0201020412050c0109 67
    0xd0f0850085031121025a400c50724030f208005081d0310b650000ba45003160340c1440d82e034082c0d0281c0b40400c00d0b903280d201074022502418428807441d00c1f1021940745464002403c0003103a051400d0101040142d100c201c0d501c44824140300b0300c2c0c42d1a0740c0310702c0161800c0b2402901c2c015000541b0716006e080c10684a402400c50401035402e5040c200c00407a05c0c0c9003040b030840c0c0b811900b000840d0b4110018454003414a03800854540d5500c1c080807042100031000f0342c1581c2010ba80b02c005200391346100116028010042201442c02d030900d00301200030038407030005a80100413a201c2000c000091204000d00f4050034008585c52880c00d0b0f0300a2401191b001480d003244c2c185001d05001441c0c48404098540b2001c0b800d0094841d0b03258900349500791007502030820b090401d0040007680810000358181d0701811800e002c40454041c54854000e0b40420040682603009205100c0400e03580c8018483d00b1644009403500307a032480300780100186c50000350354680020904000d01c1d0303040420000140002c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 829026834 1250 829025584 829025597
    0x903100905030f0d0b03030c010e15041109130213050603121303021002030708070b07030b01020a050d050a0c1403030717090d081e07090303120204050919141305060106 74
    0x341e40712901c902540040680740b040101e4130554442858100481010014041300d072103018403805c00d03020344542c004210700c600688041501e00f0030602d0070107200c0c681100d4400c155650420900000e450020f081c0444289080341000059030f603004100c0129184000100b0207040803001c01d400c1c14440121010906000c1100e8180d00c925400360394201c03074044407002d012003902d00050f801c5100303040c0020584000090988200710a48480500400c0d00e681d0410100300f28a0040e41c0d5210041c0000e0481e0303001d2071080700f01b98440d100030710003940613140039402c0a00303035540c01c001060004102000e5070004802c10448c150301400102083c03410100706030007420a14a499168850340d4107130340801010800040d003d00d003000b95840c0581d07d0410f403c100703150800c0020194001c601085001900845c5400c1c80c0315603500948060700e500524000da1030300c0f003d01d4050a48042110050f41c144c0362179039041481c1001d0000b034402c0d03c6035030325480008400d2900314141030b016088101030002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 829028084 1250 829026834 829026851
    0x102003070f080a1b0b15121b0a091805060a02030c0d0f02070803151801150815091f0b03220609050715030e06130f08070204050c090310 60
    0x48400103414440c0c0110b2169650186910100c59a2619003626442143c00130340c0c0100f0020700000380b502c10707000310b05c501501c0030801c410480c0010070341405480991100d050700e04214101c0c14012a8070030300518203040d613139a42c62048146c0340c0e0350344401e03500c48460034220705100d4180640c640c0b206600c0380462651500c0850310025006003500030400c580d0300c10300c4c04101b6003154112265030b07811119880c0c130303031402103801c000c41484160340a025080815491000054070130a050580345983d503d031100300684202149c01c410000c040341101c544800c42d15440b61240c040044c0600030015030050700d90004458020003016907400f28069810801c02c004032117024016596400d031701600c1007a0b600a942c00c10a000e403400307280161a900449400080680540e100306d0600996514140950304842c40f131030f6107400c1c0840d55906078000450803500000d0b4080e5601e0a072034402d1b5400d81c20311200350081030032144102c5040d10483c0c0e0005811069240801001420409100f800e110440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 829029334 1250 829028084 829028093
    0x1e081209030706080c04030b100510020d0f0c020102150406060e010b07110f0123091e0d0b040218091e0a02010e06030c090d050c04060f03120c1110200307 68
    0x10712840307070101300040780d00031903624005102290003c41c4c014111040700e0811220000d00500113105131031103014040300603000240081004208103c03961106074a0420340901520502d01c001803c9045000d4003400321740d404d8400d030006001b180a407200091850524159110584042e0010040d45030148a01c0f40000d00500c8030245040381940d040380382e14a03810058036207030440d2031440c074420002d40042480241450141250b07803411169030071954581030310401c041c0c0c030b00c5845039000040040401c01260102d1901034120340b01500c8031841c40d00074000c2030004141a9284440c5800c00c1c0c0c0c43c50160f200440450b00040c0905000c2c1c0313000d840d0340c1d001801d00c44541c1d8829000e00000300001d180e0380301d5003080d240c44040242c00003a0a81c40351a00035210043d8407440c9101d1890500c020814a00c0c0f150b6034015240d2000101d654503a018509a5001ea10b2800c02c58020145031035528482d120807902c485a030501da1296903140c0b001d07541400000136030071040b0600e94414483e40c404103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 829030584 1250 829029334 829029343
    0x60f010e1f090b0a180b040f0e070504051b0406020105010608010626090f250905070909020702030a0210021f020a0e060f0408060f090616120e071e08120903 69
    0x180d0700d00302d0014000810b4404a591801640e110311410703590200310110258140d0030a0340d940204840c20003d41581001850850b1072054020016a00c8040107100c5401e1a901103900088218240340b2841f80100c1d4120396a8000d4200c0b00060b5121801080010307001002240034280904124000800140d80c82c4002000b00541c4007802d071510010441d9611b007400f0b4000a154030509a564906004c84d801035071118440b40c22000d01c00c0c0000c0003074800b00500c200d034000d2030381e80e0b50303503804a15000300d0b8006034000c1e20040e0380c1801110281d500581e5250b0750b040701180f0a8000e0300d00d0101c54089540700301c2510352942040e80c0104003240039207a00415010320802c1c01c03204603072201c00007800e040c407502071504040303e6403080d0000d1080c1220310004207440341543c08201c452590f03a8009800d10684110301e8003011890044605100c0d0507e5044803645a240c00f0865041980d5401d00c04020081245100b07c2c10070509010701940d0400d026004401d4010410b10b403900d0b01100c0440d5a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 829031834 1250 829030584 829030589
    0x8060405150306071d03010b0907080a0e01020316030c031b0f020a0c0605031f0e0a0534090501080108030f072609040c1b08090402040503060f010e1f 66
    0x25640d5100040c00406404041d8480c00074060116140d0785850f140140810400e0800c000180440d9140501d19250500a261624901a1203a440341c4c54580017942c1c410805486e2404050312044c404420b030b0340900c082c5104444004c48498051601030000c0e04840307030741e07585404043c10041d91134400f00328101d0907001c034121303884e011300c640340703050812400c140042d80010498441201d00246940c0c2c8480a103020300c0c03a108045e000301a246000451020030351103900c14644840c00015040d06e015402150700000001111115810b06001600721400d240078410b4076000c0d0248180407280c0c44035500d0041c00081c00d041c42d947d410008040c0c2c2d41c1c014064100d5201c440050003204100301c007035100c1c801d998943c0807401c141c2100d40404420380c110741e044a0180e850068594007941c8520000030019404956620080505072030b0310f001a40141d103072a800903000c00c800296510b040091f00e2140041d0140000194141f251f0700c03403c5500600600d9070840c141c071107144501c581c1070203c0304 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 829033084 1250 829031834 829031839
    0x170717090d08031b0414010206011508070f11030a2f0c0f270a14060907030b220501080f0705030316021909021b03250804032f04020a0806 61
    0x1c503507031410f08100880031340e818103040206010900050000d030361000561940002d1302650416a00c581a01c1214850041c1e4400054526004103044070702613202e01a40c1e84e0380e072501280c1c0e644691000340c42c40c0c0c0002180c000140242c0a01d00c0707611080c00c01d40000c003400c0101d4500007030f092812107903103481016a481c420180034000300038913a508902c5004c2d60002c2e040e80300c1e8141e64124114800f58040b2041100d00f0b05014404844040c076840c0a8403a120041181c09a62102c9008500a0101008150700041408034440040f04610070101b403142c4e0403d00800d256041c0004281042101000811903a00113079091003c0c2c1e502109441d046128140181d42c5d01c021800050300301c0400304036141c4034802c56030740400e940c0b010307400910300d05072408074103805101c415032030543d07e02c1990582420b403804d8411f81c40c40e5028002c95450780c00e020b1070b415418203844c0c0d100d0085444052900c28442134101d100591500c41b1034034070a0494000b01c8046042c070000140241a00000410151 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 829034334 1250 829033084 829033087
    0x406090e13140601080f0c0d120201090c0b0a0e0f0f060310090504030c110d0b01120303020d0204060c03111204170109051608070807150503090a170717090d08 70
    0x40107001011011180a80c00c07807809018081d01070a41601c51000303010361580e40c000c00b0030681c50f100c0300140f030142e20907000e00900c1c0340d52110b0702d4030000c1078220002d140455490b030039010003040c42d04a58102801d5846905565611118400b4045003e140c0066000e02c4a004d00742540f50741d4031900302d10500d007d462041e40c1c0e0fa1860104507801d1120380040d0b14691501c000d0209060340310201c2c4421500c103140420000010400b04401513501003801407140101e0801407000b104203000c864030040c8079090140c10300b801000f840e030981e001130300000009410309802da010305038400314400030000e00310007600c3d440c007003c42425410710072401040301c00d200c0c0b003c0f5102c0d40d8500b54008024260000f050750400820f4009101a0b906c45102d528a988504d400c0841c0807080030410704129988580c1c0b0014040c5540829112600014156040c0e401107035089804603170394014040442070a15011540d5200d82d2820031920214444950f010700000d115a1500d80c988080da102807940003071445 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 829035584 1250 829034334 829034341
    0x1311030105220504060c09080a111c0203071d1b1e0d2912030304060f20040602070e070f0804021c050604060f0b0a410102010b060406090e 61
    0x8106900e00036144030545894a0208018451783d03902c000403401c0680e6800e00e075260783d0840683d60702e0713246602420012041c0b144101c01d14000704183d03c5918804240d020028080e0002424685181d22242589805a2144280c2c05070541529480520a036081c403040d403000040344070340c0c0604001c151800300c40c0c1c548880080d00c61015200e0140b417884040c040b00320129150a01000041c10304012001c1400b142d0095151400054658511900003541580e40703640796a006040e001e05810940340e0340e00568411000c0c600b0040045014401d20190b40d186401402407a00c0740907030010f20441c20a0301403082d041d5020003c0c01d072000b254a02802c0c00d88a6000191141001c00403400e842d45030b1510640c10071001142042c450350081100708000301006050006440851080d540c0c01010f4903028025056204600c014800f030040d03000ca040c0012298540c90159000280d080080c00802413071140e69090040d2802000700740d440508192501c1c4002e40b0100043c011144040040e0000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 829036834 1250 829035584 829035619
    0x21c051903120e01021c0c0f031a1203130f0e04141f0b12240702030d18020916050307050c0a06020703050901090902030103020913022d1311030105 65
    0x8803607442c0c00c1401d0070000e07900281032140c000c1d80000038885d11009840c0c0c240d1000507440c40b9039030b40f0032050f4a41005e00490000102c00600201c03524140d2802c155401c4101502c3c3c1c10005254400080c0055030785403d040340345044900ea60740301c400e101a07810024001c500700c0460103504941d0140110b402a6451001c1d40e003020750b03c1c0200d081d0300c41d8244082c182405c8507000b0101a2000b5696a00200000503100c0e40391211054030303d43c001c0044000d8603038202091040e42d0f11090910640303007456504040601616040c000c150340c07c022414607071042d403410840e41a000b100348001c0074080c905583c00030b005804014901c10500a0100303041a45850170301c20034407015401034085640320450301d805845e580042801c980003800040000c0b84200c207510849058a0700181019050341c0d4003650064245004003003240c0010103440040c40102564200240140c3c2180646218148000601c6401080b940c6800d45403030400c141c400e601c2107241b0440381554000d485941e4101400c0c2c01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 829038084 1250 829036834 829036847
    0x60a05070212030901120b0901120c0b0a0e04110913020307090b0f030a060515190504120c090b030c0108041707080f031506120a090320010603021c051903 68
    0x4080c0d0002c4024450182452000c401040c031503000762150950309104c0d400c0c240896091481c1240c0013503080d0018482e0440708031800d012544200101803189031140c1d03044d101508402d1030b03003001c81d070702207051700a5280078010031030b0303900f0013421a50405030600001810564000d4009100c1c0d90b000020550140c8652401000b801c80b440c0861380d2103c2c0c070f06451071130340d104440500c2050b103805c0740464540740030048460002c0da1a4040c1d4100140a42e00034204248610003c045c0034080000040740000684040b980c207001e00e00070000c407450703d850322056419a101c4144650000d80c48400c540e07030081511a002074100b04816030507880003004003407030700c105c003001790422030b0102e00000b21008880082d849070100411441d9038500c008180049405501d40c041100c4400030005202200301317030f0003403000a0007843c00f80305452a0b10700320303190041203220f4001c0b00e9445110900543c00d059040c081841c0401c000e80072416080c3d220f564071010030f84658000c3e85900506d080034144100c8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 829039334 1250 829038084 829038097
    0x9090e0a200d0803190e0709020d0609050c0d151d04060216052404080f0313082d040807060f02010e07060f080709030c2c070c0c2102060a05 62
    0x240301015480107800d00031034a404c12500c006113082c01d80c1d41669001080d0141102c4150300f403004100c1c103804c1c0a000406500941c0b108260a030b81c84a0000c1d00302a5402024007030403400a00a5a400d140300e0381d402611501c0400c101d0300440c800042280b150078034003c0e0740c00c8510081d8082242c60701d18020000c1e100d014948400c204456411009001e80422600c000744210070a65102000d00c2c000c2c00500c5008460180c20300409212401d0320088000045601c01030180304100b409802c0d03035400c5001d4000079040041c007940e0703807040c1b4840b40108a255007402000700042d81005c2c68040702d00d0b40d03051035015042c200598036640d030201764001d410000d408075503d01500d04180d11040002c05004510601e20001810340380841c2a080c082c034641015a5000000302c1c240d142401241118640300e0340740010055040c8070f82842c2d58059501c603d00031b04203542d41005103174090500c9011220709030001860313a50001e213003171001b0000403000c4000750380c151440758681d0010314064400d40150b4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 829040584 1250 829039334 829039339
    0xc050415090906030b010e010e01030807061d07090c0f0509030d2106030f11100c0201030510030501090503031816030201080a0906180b0a090309050d06110c0c0109090e0a20 76
    0x60f0084100850100c45a06840d07e16400c210640c0c2e0b50302c00b0400e881c500380320140400c007040000c036010407010f4200b4119466075581c80b180c000c00064070140381c80d40d258070a9a00030390712a0442c0c095a440007610503407500da440d0060400c80070b070300081e403540f0420082c081800080340703d05802042d041d0f8000508501351b03404200c225903070300b1704081c1c485c03451038116070070b002144402140f032a103c04000321600295032289881007056005600500c1c1c043d00382100d940310107400000003030b002d00408034030a01c80d2003d142c403404d01c000549480800f0001107803142d000f079052178100d05500569081102c2e02460300d0442500c9070a4104010080d400f000380066041c2002140c0c084800c00c102211644991b41003c3d43d40d542d05a10710403111010300c0107001034400241080245040d141c040b11141c01507000003031070340303140782152003a600003d05461250800360443c070a0350307004540c0c40020041460103000382c0b160714240c241c8801540c0c400500f04032201c00741c0c2000c441400322050302034002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 829041834 1250 829040584 829040591
    0x5030c0a052b030504050a05010903150b0307091d0105090f0318041b0e010f08090a02010806040f06150206010509042111030a050909060f0a03150b03060c0a120c0504150909 76
    0x110f080003480365029004860142c0e0301c01900103225482140c1c10380c100c0380c00911000804926408003000761405880c900e506215105001c10030240c28402e498002145514018181c03607045002425110001c2642800350403080301c900c01900c0200803101e82d901d03684a03403039400207240b0001c0c00601050400c56000240308809400103600500b0000d0416003d072a4400760b601c00d41e0049540e810100c0c0c0c1d0401c180c003c04c2c044001540120034603908408000e00214940114400c5d08045030815440407021a44002100110341e406212030350240105581488183c03400e40c40b0b0044064032142000410102281c10f201b03464414090f00403c551003d05030b80e641c00c02a080106260494007000d8070803000720300442c0307162400080c064034143d8003910001505265441b008102a21038548008242e2504000980e69605100c814483d81c51003404075114541c2d40d40052a814a829170052079606e04600082e440b600b043c20350301100c03114080700c2103200c210103007110240d4041e0311000110b0304 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 829043084 1250 829041834 829041919
    0x90b03070302030a0f200a0e12060403091e151709010f2406140706050709180504020906100504080313140118120807020303031602010605030c0a05 65
    0x74550000e500803118040d003071104031320014198040311603141201c07001d4039561262541110310f84014000c029110305082c0424409403000c40c60300c121210841c1c1c12600210204002c041d00005100c014045500a880e901000307407040c20300b59030050042203107100703864024a203c40c0c80740d50000012255840240241d062441a080c0a00701c101e88035040d0754104a0300351030340303000005a1180345044000c40a800d910307080c42034460340410088048038607010000c01002c0303a00d50140c0b074001c51444d903c182d80b4524002460466466040e54601068100000c0c4005a62081400e0380c001c001128003107444d140042d0161460f1142e548101e00f40d000203e000f0212003100d80d0302504490b95012540348407808803004641241540c510305013a8503503820301b8010548510a407600d6240308001051802c3c0d0541c00003461504226110030f1201b1628404c450010390a02035107000b081d042d4020001c000c0d542002031508202030003000d018401d1220200e443d9400030603184201d4051504200501d00d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 829044334 1250 829043084 829043087
    0x80f12010515070b0c03090c0d050307110405010e040201080c0c100506211018080304062004050a17192a0608040206072609090a02030c030412090b0307 67
    0xa091080c203204401001102205009071411034a03401d0f402000128a40c0e125400c0840f80d400203801d08071240320311004039a081d21740c8902c14002c030307009030b000311b1b120406480c1a40b945081c010610f80034900341001000b00d44420004503030059824200200b003075035000250a000e024000c03440c0301900c941d80034003d044000340d10141c0101410742e00414180520700f0f54a40ca00300c495000003907a813000320200b91b10004c56002802002542990f00142d61041e1240502c642051301c0030f982903030f52885001c146001141740d4024014080c1a90b40c00d00b490310740014081d44092013001c0300020040500107080a05110528104491070408645013056080c10316414075076819030704441e46500c8a039050b071005007284804482d42030740d45074a1503a40d60300f8040240c005190850711025072040668075101481c031007080740a441c1c982e290311400325408000c0c0c252009403088102070301c104107002c60b15042100f142d5005400404001c0c05904201003102c00c2601d0350301220781d5680c00300038800060f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 829045584 1250 829044334 829044367
    0x20918011502150606031305030712030507020c03010614010318150207031805090412020f06090f010609020c030301030602070c0806070302030402011706030c130b1201060501090b0a1407080f 84
    0x500554210303102c14083d0800601c1e00710040d542907134041414030009000c0900464a80b614910500580c0d00304040e079038504d46c030203c40c006440042500d41d02048542941003023500c1c40c080f0110000d0180902e490b010500003d1208001c41c1055181c4c03c1c0648075040780980012070680c480030201a1400a4171024001e40083c07008070b000500e201d2580750700d81c40c0903034407805954000745803a10740d444130f0b620310651400101ca60700030f6003d828101c080948040c00180c0c8981c2d000c10103001803101c064201e6003101d00342d820040550f881400b0350400340e100002524103507503020310010303900c0f14103080c07074170540384258050fa0451050104000d400d651540241d03009502c04c0e25440d1420f04405240e1001040031622150558800b14001c407203482c0ca0321004440b0342440d44009078106403040030400d680301d026008102691240720401035540d0298260009215030a001c2d410003412060041104034046108803c1132404035842e018000d0301d43c2200c5079031080c1540265188042c01196600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 829046834 1250 829045584 829045619
    0x90603020301111305060901031b02010b091b090f150705010b01081008060f1f0b1306050c0601120c120b0402040e0f0c06070f021801240905010302091801 68
    0x39400e2468607404450f0050940b48680c2c0e0302c4070b030002c80500b04014000c0700d4001c0107a1504164850f40000400015a10f031503c8944440d8004680e003e01481444000d05020388000410560b030100300a22000d540151102131b00308540e042c01100107080001c131851f41d007400303503030a00000041800030090305600202280000b81c17911a2556200b91040307044002c035110349110b40c0c100307000144042c0c80101c0c05c2070b4820081202180d122010241c0ea030035014154008080110001402000304002480340300014240c41c501249050741c915000b5860751410f104075400c003030100c0c40341800c101c13a8403241401390204600e88601d1811074213041d641a801a18242e014910f400480d40da451401f14650103e0300344c1d03078001c0440c804144103112840d40300c00c40c2501c0022951810300e00503525000c0001c076181c149080390603254148251020704001e50b204030030001103020400d6800c103800c4007500040f00c00900300180c64248030004505804a10800da00c48034903402c0c00810303000902000c0050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 829048084 1250 829046834 829046839
    0xc1b0612090616050406080105010302091207080a0b0f070906080a09122006090d140d0c05090907080403020a0212150106021e010b0a090b010917030301060807081308030604021309060302 82
    0x8103c0c07003d4419a5144101d0040c88001031039080140100d5020f50000c003030f1004042d22540180350a660754500b008001c2d000590300c1d0f04400558400e12480003519504558900c0030030310103062000c03001c0c0801c851403040c40709200c0910700169001c00258040441250090394614144412100003030006800c004000d02c21500b0a060191900001030300500c02c5448800a16142c003a10740166441e605140300018950310130072011038400a0350194846c01c0d202d5484d8642c032001c00108000340580000c2001c0d08100402d03040002007580000c010340340c0c5405a4000342c0803014500100c0c10640b00c4d480750b00f0340305480c00000680a6000810007080a091401c640c1c03103107049600c090a0352130401250703501c40c3c00c034103050004100d181c1c0803003810030050410380015581d4000c4448411204d140b691500d07080840100a89a00511601e5002450f40307068040c0707141000c00032094034401c144c0a0700c552804000100f01e03407503da04481800e00c800100c1c5c6005070780c8491244c05000b650004a0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 829049334 1250 829048084 829048111
    0x181d1b090106050309061b0d020d09230d0309080904051509150607080a030b091e0a0b010518040b03030c0a120e01051801090306140a0c02030c1b06120906 68
    0x100c003407250042c0e074001d050b03550260481f40c4505010351020031100807508903100b81084040e105002c0340c401441182c440c5400071902e445203003010080440f0741c21000c2c040c0e4140820000ea070440c0410402e8100c0441d090001e80411141061007c0b40100078000d9041440c2100f44220180c8c048500d117100c00003151030f00c1c0940e898400c0384800841d449015500014240a103070700007220040500780c0b4400340e203400510215410005140301d101542c1700d080a84000852041c9481540d28040d8020080d440c2030081c040f0020008085224031080c0840380716404d02c840130b00e640c854124802c1c000c0b0040888ce2210411204c0c0b0b520b800084408654000d42d80301c0f80280c86000d400d69900400c016103031a420300b0000100140803030030f204482e6041180408011000842503ca001d01d20006514800480e141c440c400c1012108241c040805550060001103030100c03001900442e80d141500b5880055044040403030305901540002e000c460107000d0402411080000d04180308401741c11040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 829050584 1250 829049334 829049339
    0x340302010506030f0d020a0b060d1a0415140a020304050109020424080705060708032211040f110301090c0e06070605220b0a0203070c1a090d0801181d1b0901 69
    0x4c90303503081a4180d400160f00841004400710707103d0700c905030344528050f01010403100c881e500c2c140f013020b00c1d4072082401001c21062009000e000710701d400c403514141c8001c10100c140d0410410305060000c140c29841d9030004001401c01c602074005005080e8054400e0103005205084c0b0f500e0f41000080c81e040000400400042e274010004004003103807c09030000d890181991540c261990006026800000b01c2c880c0b60650421404c5103c10864015941d520442c180c6204002c01d03901400f10a21a06007803000008480e05480112411516401d10019211034001c40c142c504e02090000c1c1a030011000c951041400b60a030081d038400e00020010807500020480d042d01610400c0070007500f40030b54a8009882c101d49075000715000300707041c10036040d000d0080d81e94130704099584032200c5034107100c03009101528504000c0d40c0190651410040159030416401101d01401603282c00c0481d0b440303118200c52140d20042406140e01e1a40070350b00001e420050802115400c0032090b4003455010000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 829051834 1250 829050584 829050613
    0xc0a0b04242003040525140613260a030504030209010815190f060b070c0807180f060b0a030c03060803160602030c070b090f0c0d03051b070902071506050105040b34030201050603 78
    0x40b09c400440512030681d0f12030074000c3c1621048071525200004141807a59500700440400c16241c3d041d00c0703559a02d5482d402c0d0301c14460109410381c0a40c50592100300c21641d02c660782184668026000450268071062400911000d0583e1681c1c1d0707103101b8034044001c1035418402d402003000c0c40c00351180001143d40c8140a030b5482c140e40c8120040084000b6008004160030307001104115850030700429203d4540044940d181d2142c00701c2c50201340e8841c1c4006080d40c05000e294018038a55001c0c60074110b032049003074260302030100000c1110783e0010004035140041c4003564100c0d5081652120785103454218036070f48405504079880b2074030070106484103d20f441c0d5480120140d141d92414103250408000d244c410002840c609654002c8403008110320043d1300c09040800d002e40c091000e10420002840120f54080e0015070410030100410710034030021004403008481031081800080d52001440603642845000e41501e01c0e6a400c0c2c120b0625a054100c7ca006075011800d44603200706c030184 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 829053084 1250 829051834 829051837
    0x1209090f09070b0a110f0616031802040f020d060f060e0d170f07031e12050403030b031002040f0b030907180e03131e0e0a020c0a0b042420030405251406 67
    0x2901800e500c80240c8180d145440f982044550342e0740f2b09039109404502c0e5000500b078400340c0c80680380ca2940480d450041c40d03a51b0103003038020403501022000c10350524400400a001c0c1b514100c0c06800f45010880411801c2d2610400f025040070301107803102c0214480d185c50ba0300c004029000140b8480042800070032603902211030780215118850500d1914035000c019010051007a010b050b80c03024542e4990b00c0901440018032181c10005036241c0c02c01c17a8400810185400c402c10740803090080110f0404001802c00985a1120307040d488220b004c2030510150084440b606140d00011a0f10300c8505148000e134000d0380d41516101c0b0b4400c5807800c000091050b503100f60200c0c80c0300c032004500306070140c0c0e00520a48010343c080e500c624101c1c0d240c0710305a020590b0300701c948e0b00740036401d0100c10300464800142018244821302203905000040319850148800c40c2c501d009000000c5400c1004c01c000e4020f0600d83c1c90040026100c8245a010007101d80380f20f500e685c181c00441c09100c9207000780 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 829054334 1250 829053084 829053091
    0xc02060403020d020f1b01031503030809070e01080d2f0307171c0e120309030c070e07081609171b0f130203040611040e091209090f09070b0a110f06 65
    0x4001d106d00c1342a840c0340a0040c00b105005418950740c3e1142400151000081c40c010318041c2d121078031541000e100c17940c6482070030b92282e0700c0b44400c0f000612440001090803944901d50703203002070340c902000440c01c401310460b484e4044280d0305420404007071600400542141c5010703156405040c058028101c0d6030f4490b41040345240c0740510704961200e0136070342c00b50f052030944008440240351609040c0403036510503540740010342c0c0085203000217440104200009489000403c007142d040401010b054010042c080081d030f408000c81140c0401e01c41c5c000c0360000d001184016410b901100711080c0c948071303000543c500c108007140c8041864101400140041b82e400f9050110b100c020303441d05002500050030843d103980e2207480e51a41d40300c40c0c00292001e407003480c02080442c101025910714280c104500d101140300240200b04090303a8402107154800b425007041807031955a04003050822a03181c011b00482d00340801c4440c0c440c3c0d071203c1440710b402d044500b1201d6000201d10301ca950380b02c048 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 829055584 1250 829054334 829054363
    0x81902011b03300f0b04151a0d140a0203070f26091e030a03051b070f03021f0903090806100512070905040807060f0603080a1803060c02060403020d02 66
    0xc15211910a543c0d100260707256005054035140c1c1850348500300351481c040310061429100e541c0c0008903c3c140c420481034079a40380740010242d1810785c5500c404e040d000751881414001141030400009160441181c040310520840e055191040c5c080000350019201c0000087c800d807403d0036014011100c0c0d800301e075106115030801900381700d16500ca141000b41802c40b14041c204a540300342010005c000c008075811005540c4a58a29000a0882d60010304020300faa00c441c400014042c0020103d40340c00f60030560000748514035060603850911040242c1c1070741c11002401c60a101d005501044486100395141e0780a6950750100c180d0700c00054072030144a00d6000d1041000d40782074501c080010788554180d414283d620b504040444500b20b900b039a180c070000a0120400c410b030321615004165200c002c0110a045032a14041802003200201c24000300e2030300c8100a550b4900c4010040d948408240b2001100403c0251208010344085005d489002d0b4801c0c4054000708040d0300d0000075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 829056834 1250 829055584 829055597
    0x9170a150c03060806100305060708061005032a0301090e0c03280b090105100902070c06080a060513020702030c0105041a1e0a021c03020903060c07020a081902011b03 73
    0x291240000038841c0c605010305040da24800021440700c207001040c4104409441480300c5031840c140301d420000001c100004114141d020841a43d480d608504c4122070303949081d503200d917200f0b00e014000311031420402c03402407118481d0300c3c510000c1800850698032002014824a0703e10fa503415900c10421032140d906800425003820400021407240403103a2000e81d400a03d0100c6072201200760500f960560f4280c3d455504020004060700c10b1030f4000c0c00741c108218038105407601e40130f50b0303100395015503000c0105c62400703e83d48192580044000d0306000740340600d400c50300c0e400d100003984841401c80c000c0c001d9040b501e0256029409880c2194140801e40044404041110b1740c950b10418a000e000325007041e1103220342c02100c0140900140c41d030010003c5400407655200024200505001010700400034010241c07008601603401000d40c047c2c0c16120082ca100217a6030317596a4000c40114410880111500107043d48a20b803c80c1c000e803140100d40c1c0d041d641c1c041c040b28041034080c0100e0742 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 829058084 1250 829056834 829056863
    0x19080708070203031b0105090106060f050a2012120f0c0a030903180e060a0f0b2d07120908061303081e0c0a0207150801031709090709170a 61
    0x49031001080458401000d4900c0c00c11400f00ca45000d81c54101070000c180c4d075070001c100742d5490034861140605420309184000041d00f0710000d00c0e82c8241d04280080040c1c01c440007040d407002c094140d0480400205540c03c0a04034842200c054001c002c8810a4440c050045201c200c18281210701075090340c410386107000304460041c1c0252500343c404404210041841c540d804509903560005480000b83c0603001d401c0080c1000000106500502114040c281003000544420001c0700d20b200c0911100d2f5180c1c1104540c5102640701c0d1070f1140e080780400056000c01c10501c0055880d0045054403801e040984503940c8a546000031650001c5c000440c03041c41c1c001c2402041c00030342c041d59221403460b10110704d00110220300020744102d0506080410f04481094043c45404058440700c940d0040b61064a007004224050602c0082e00d642d10a40030182600c60181c00c5550881c00a0311900850500c29401402401c05100b084240003595542ca4001d80000c21100052900305159264012 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 829059334 1250 829058084 829058093
    0x902240a031103060d200603010e040506070806090106030c21050702070602010e1b0402160302010605040c110706320414030c1503060a120b04030e0102070b040905041a0414190807 79
    0x1c44811b40d162140308030b20308070300e2a86e9800c015030203801800a4182c0030700f4180340035072078110301408440a04c41901c1c00c115654a4203071030b50781110700603c2d0204403500d400d2800c0d644901d1551040c501e2032015a4800389803c2075400c50f0b4021940d990072217502960742e080032400c8030f66038071491003150040c400264451849050745151400c00500041c138007071f6407100010401e1846c05c42180503075103d080420103860584203104e000c415504003002849454540c2644a212900401050000e803191038400d5800005500c4048507d0390b910200b865481110828290400e01c07844c0c0c01100a0301c1060300509011401001c440006041d0b48110a00141111600d030002400d80c0d810841c559000501e981c0c0701f013407044005000e07104021040c03c00307040c024802400701d0082070542d03100d1031f010000100201e0450b012900a1f440c001a192500e1801e01c002800c495000c418100f44d8509000c1440790010104020300162400c840d40c100b070034601840c040c2000400a402c0e260144141c4001c60b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 829060584 1250 829059334 829059353
    0x110304090b151b01110f09060d11161205040311040507030b0a0b0d0b04060605070f020a03020a1e17030a0e0a15090e13080a030902240a031103060d 65
    0x6072004202400b080c240744800406a002040031a000360782d00003500700f10080030b02c2440c825040905078646801c14512808143e031050103642c60141400250760003409440340d00c030105403d02006110b1355070121241c2004801040541510158054000021300500640480381100d0303002040041d1040d81d90100300003040d0080c405000c0c96120f0980e0030f1565540741c1514080c2c0050084152a02030f41d40100c011100c0c000032040c0507a01d440400d1040c15041000d5650507940314a040d6010f050f034ac400704034054165030009400045000010800d0380c64a5503030802c20511440034a001665030303014102903500c40e4030b0f0f42c00d503805c01c02c07025403c43d101d0482c2000c0c0368000380070001402e0b0349881c16424143c00e00042c80010b0000b40080c41515103c4003265001700344c800c0035500340801c9480d0085a88112804041810340c2c4110b090119191500006c41800b012145e220003c40786a80c9440c0d607500c641004000603143c80420610040042c00340ea018000145c22084240c0090f520103921 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 829061834 1250 829060584 829060601
    0x40203070f1d090a06140a030f020d06060e16030b01020d09140d051b030f01061409061201050705180405010308041a0c030c1005130b1512060412090611030409 70
    0x1021000070b0307001195200d0442c0e0070b008003500c640015101d032918001400c04586d4110031441096101002c1000c100d4032581a05400c0e0121903c4184d0400d40c0b030907000500c84c0380e000a170036040076002c02032955240e560200101089071801d210b420300f00001241c6542500da01e140100d022143c3c02e10801c41118443c5031003010140c0380110f01409521243d1414103840c0c040c80d408006510011440c0c201400561040011940203021481c00c00300d01303a4240306c0207400c86003e007030b40c407001425a68407808003000350070400b00200300b60b0134110301c0285182c5c4008071191001450549401c0035003028440c490490382c002038030341c0c1860700b4a01c200d50852440d80001c85040170a100402500303805000400c0c043c3e0345c000080214210398400d11040e00c034020000d1000350700f40b103100c0011030000d0304010b1303000d640710648800940040d00042c144000c2001c0f4004144181402c2008100e015500d21140c02480d071200d481c4c480d41c0308011680d00a103418800c407142c0050004008807421a00176161 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 829063084 1250 829061834 829061867
    0x140121060e03070501021b0f0d02031804061502011401170312040507030c060503040b0106030203090a1203111303060509032802190308070305220201110307061404060b040203070f 79
    0xa0f082142c0c541e9400c0e60402918045600107940d03403e554690204402603020303403010040c2035085020705d8042d4980c0542105800c10117194060740b000340d0750b56031020340984a100e039440303014841040c0080c000c04e860002c18600074800c40000c01c400c096801c43d60600c11903c80114039001c00014058251900940101d034a4070030305501000007161345a40c036000c0c0086503900e070740303074500b45c140f4040640d410b910a40615204005000d0144808230301c140e40c50b80c1245031003445201d2940118014890141d036907010901c0131030f0042640a40501c42d50840e800b502003800103031103d0784ca00c3d440f48030f20200c0d030042110040d402c020ba0f500c11210110001024010348034002c019032014036000c03a800c0001c800141c0c8041c200038403e80c06118445d0062944246a4440074181c40c03400d40445030480080d0500001e034940583c0554100202c0e4031284d8410340501503000c100459194907141980c088034094148010503035241010310941b8032174042561482c0c9141c034403180a440c1141c00d01360030390 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 829064334 1250 829063084 829063087
    0x151209020a17121e071a01060302070c050612012102060403110907020706080703150f0306140a11090d080d11041a090d060c050418140121060e03 64
    0x405a5104100000208a402c4600460900080041c0d003002d90310602070421850600550710010b148110380c848135804056010340c0d59030315091404840c203861413005176003901c00d000030803010ba064019010f25803042c0c1204402c29203407403c02400d4010310840301f00300000071004103d411b0740403d8412000714404134200100645401140b0760340d0142e002610404080d9510450b18103145005070f6001c0c6092001d04045810f0003c01069800f0191101c8201030b10341d008101d28a1740b6900c15001860030621007810a50380c0c0c540f44014110801c44032403c42c5c07601d8001040e603075180c02401e410303119029207149000810020001c5940389058140d0340080180052812100607105591465645012045d01c0b9403500d4040b0501204854403042035000620440c8a00c2d2112080303411180e070b00c05808100700111103021905c501950b1700800c920402d41e4a420b801b51841c1e40405908049560907001c030b41e88030b03604007425004105a03862540e0f401b01c080f07404036103158410483c45a1038016070b03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 829065584 1250 829064334 829064351
    0x50f0705030403030503011d130204240f0e090318060d021c05040c060c1505220308010305060a0509030a030b0301060504060b040e01050f0102030307180e0c030601080c041512 77
    0x340345802070f40085011400c00001070024820000d0145a600d460251508003072600c20301c0d100c4107402c0d1000c024011911203140c0102441c80d20544582991a200b15a800c3303a031302d103001c983c011140c0c031401c1101e03c3c078040442d0402c05d0200450b900f001050752a070a81c0542c2005000c2c072603025558040c3c01c617a0078040d00c2185089051442441c0654031002700d200d0070141030580441000394040300c00e01c2140308181c800039030903840c0c2850500300580c0006041da030b00898400d450f070110711001a071130349544004e020107402038080f40c1641d008900b00c522617a5803540103400c442041c0c8010702d55074414040c0c0c042051007504011100c0340f000d000403a05541d0303080400e040c1c59040e003081c283c0d810046400e100c12030144049070700600e0100d40c180140580940041e40340c0c031000d05844200b001440c070080001c1e03a2a041100240682c01c1c0d08040351a19101c00002e640040d9099400150024082006102500305590503254008501e0503440c03120f040590b00c2004003405041000d4607a03510 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 829066834 1250 829065584 829065593
    0x71407051011030d141b04270b0406061701150c080a0e0a06090e0a02090108060d050a050a0f060b09010609180605030a081e040e040209070e040f0605240901050f07 72
    0x58602030150b400348045d05003801e0700d10f900441022058010110000d1104010303440d41820343c0c1700c90400717101c91201c042641c40c0f05070000e00711501c0c801e03070003500b0420000b40c00365004030360a00d040002155041c80d662034041140c00c0d91004100c0d100050a051040000f0413500001400036400e1410034600d01c0154901040c00c0099a61107040481c800000421125012115903075106207405011440c0a9108002070414240905141c1c0109000450b203401c0200c00c001a620f000d4004040b42e5103144103143c4148628001a000c40f0154184203042805080440b0b015041c2d641640780c03020170710308003029090281c484610441c10952503090006143d1018899040814050b091315640d41e4960302c801224a212007240399100d0030204401c01c205074500d01c4c800e41090b41121500d0041c0c49115040b42e4200f0313100785da10f600a00d400d40703030200e0119580c4402d044640584038841c0c4502d1402c0f8080390383c40d0703642c6580c0d03030504d003081480802d6104200900c40100005042c1d420014603444 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 829068084 1250 829066834 829066841
    0xa02030c0105071e18061b06090b1b0703020604110a0e0a1505011d0907031d06070f020307051509070b0f09210a0f020103021c02071407051011030d 65
    0x1440c3c00828405002c2071000e6a8403800c0700b502602d181480900009000403099080303040f446000f0400481400b18507104099000b5107183d04d4100d2024402e44095082c50a0008000d46040c5180f8408880c0707003803a200410b050721480c0790190080c056070b0b40c4945401c8011883d51130001c2c0c0c00003103006d000c5580701c0141105800769080300e40006d840403107002c5204400c036241d004241440046600300c2c2c52901290082c6117000d2042c0d0302c414140d1030301e60080c0d0241c01c06520480e4403260300312141c5012030000404034401c0800d48d84442102c9140301080c0d840380b00f03441000c0d2440c3c000d48070003181c10740050b076000d8010410008640040342d0782c2c0c10304509500204007a90031300c07400080d00019490072140ca0b88182080001618005000c008055034481d038080d0001c00b01640c42841c0825680254140c0f96821407912151240c0c00d240c010303050003580704020881c1c0340e1040202c4400460000144441601e4015050a034069011103013600c00e550481130104452000b00001011241c9a00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 829069334 1250 829068084 829068091
    0xa030b152103130509010e07030903020712110102010b09070c11060409090b010602010b1504141504060906120e0303010e0c0705011406010f141b0106030804080606190503030307050a02030c0105 85
    0x4003840c1c4804000414816004680d03102c81c5c40b452082006100d18140200c0301d40d001480b0f41400100ca68241c503040e420031119034000d51000300d80c2140d103410311071541418001914260700030040d9602c05401c00803000c1c1d00703803401c82c00100c1c1a03224400182c454540c125034100008c0006003066600c05442c401c3d903103074040440744d2400ca04010011540c0900509003610350844002e0100c0c0384803c0c02e40c1e8903005502c00c0c128046d120301400885621044919000c3c482100c0429944507218500039204d0241c9200f00800214105100c4400c0d4410740301c2c01800300d01c0c1c0e6010318078507481c01c0700c14081214040c3c0103100a8008200e070500003a809d101e5000184c84050079240b01e407501000240000c0d4803103206205101c208000f982400d01c1140c12582492a00003100c40020341d250940350050000c1c0d080180000c40029022550140010fa650f20401040310014420721070401c03804207100c820300c191901030f802840811407030b901407005010503840c0c51044070305105500100609440c8140e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 829070584 1250 829069334 829069399
    0x906070f0905030709200309031206120a05070810060f0e04020303040902040801140108061911091914030f2d15091b1f052b0b0a030b15 60
    0xb003240004400b400060012602813241c0e0287c210315108890644034818840900d00d01580d50b40064125503810f1201036080b0000c40881e5080c06a80c900310380c0d030740381500a81c5c11601c00c28004d19501c3d0302501400e030039603034607040d0822640d240008000da108009402241e05000c01d00020401802a10141c0000c003001e07000414181d902c444080300458041e0440c44164000c00304100305034a4100000203031403846007000440d1003041340003002c46d00440c000a54807400082a040d21000c40710341020503180c000382c2d4045000000b1003015503800c0d0040b03040050b85c00401441044491103d201e808410344801d80750a00000705e18150704002e0800c55104050000800703000e85032408002000811a010400008003040c1e100062144401c0144007242c44851299850303403140f01d503050b035040401d1221401030364040a040d1040e03011007061030728601c070702e4010310740303201e01e04030194104480d009014815039846224503001502c4030110020b40103030030840c02c5004100005400010000170 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 829071834 1250 829070584 829070591
    0x1141518092404020909040b0c04090905250806190f020a030218090c04090f09050703210504030b01060807030b0a06020307030801050a030b1f050a0311090f0906070f0905030709 78
    0xd142060a05482c0001410b01451040c00000071a49400d030a45400c9034002086000b182e442c02c10514140c480c94021000142c186270543c0c0c200440081c66922403120405203100b20422860b00b201103035203600c070b07000e0319501010106000902c90b8100b4140140000340104640c59464048800d9a200825180010358001856a40080c858a0702041060215000e000a061400303070345125002d03a018441d1045d82d206186032060545038400d43c055907001003590112a5242012030000080d0300144440c86d45103420610389034030903009c45041d2603001c030300c00c002c507400c0000882d01706400030200700c189503450301804803e542c0d003842400108484e038000c2d5940e0644d490010070148041e071155001d00b0f41c00c0c13001c0c800542d00c81c0314280d1051407204200785e16000303079100c00e0340e40c102d56114540100041d14003000f804810814010050016215002540c58002c3c980201410443c1e0324040c41c0c0003c00407c00032445002d459201c1d0110f80ba0502c1055100c000080c1400c13800c0e4000c4030101c4c1e5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 829073084 1250 829071834 829071871
    0xf450819020c0109090e03090904060b0108090303160c08090a0b04061202070b0705070206130b030612030703081f09020f07020102010b010f050906030c1902060f0114151809 76
    0x202992481021140c0701400d0700c4451940003030400760503405401ca6803a01c40c1c1e5201400706c8100147d410724080288084041d00b02410040000d01c80501c800f40010700840020f410031740000200ea004d072050300200819000b200c1c2084440130b0340640c3c00c60740c0f500100000700303499582c002c1190150981c801010340d22850150050103a44c03000342c0030080240140100740100d84c1c0200010b90126181c2006070f40c80f1803501c009103080c419001ca02c07100e008400c00c081000381c010300145104070801c3e240c0d090401e07050302007e40d41340a50580100050b41c40d0000400249000b1401e8a140000c4c2c0d0702c8116450721402e84205980180b018100c01003c0404c20005542c3d09010704a1249420308201005100c06d410003040d034031a41200c24098040040401c9000722908101d0b41c3c2010b11a10fa00b020b00c0034650000d48601003039508140c1882024000700f000804517030500c03c00d0000078103550580c1c1150040c4511034020700b0318080788901c0541c0d401c0d080c3c3c481107030b840c0c031625030307032690011402 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 829074334 1250 829073084 829073107
    0x509060609160c060c0201150806011422090305160b0402030c01110303010e040f1202010b0a091803030e010e0604050607030e0c06250516090f4508 65
    0x44020408407a5000864141c2d40da560031003c040c14854015001090b680c85001c402e0307016040000a12490800c0d40c0400100800049603c40c184c0f901205804200c8d4980b008108010410540039100c620076070b080e072042000d5903448103641522a0400a043c40f501c0c1c5507010051034007440940d200404401080111300c0e062000c0003e082003402c06440b036001030351503103a072400705004000d6400d00c0d1501190501c0601f079100491071b540240356045030f00002800034045c250489586000c1c0716880c0000c9030100d00c60040c035010651070702c411002d40d48241c0b41100986481e0303401c944a9503031a00204004642031022900c00c0380140014203580c240041c00804480a50020115540000e0302004807030fa01d0808881800c041d2200d25030000220010056210410150003000c0d880780d44c0640900c8445140343e1012115000300c2080100880e04100307040ea01e11000c68401d10381c1006140069050122090070031600711048242c0c46030115109601540e5600c000f600c6150380442c5200c2c195 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 829075584 1250 829074334 829074349
    0x306180a021812070320030102070c05190803031605090d0b091203040b04030c1506080151030c0e10091a01081504150e07050a050702040203060a080105090606 70
    0x2c51042c1c8079a07240d200c0e4108026118110b601004140b1840f01d00d056421310f10780144440c0e0103030001c0c0210350b01c041a28020301000b5580c450303140075802140711a1040c4220401507421104080051032466076803031000042c84a5078490380091001c14403003a2041c1c0c40f424881c3c15140c3c03250489100c1c0341060700c4427901c0c01406031141241d04104100304070004200448107038015034581450350082e105442d080310201200030f541e0800a00d0b19500081c035601c15088810100d6841d41325000001c0d10071070300600b910031102d02400300c40d5500768030720907603090040e168044089014040d071400d03100c1d43e038031900f01d40e698001c1021009410501c00d1501e0790b0344c0c2060043c1442d0390100100c001030720242100010748404c042c14001d2020010302c40c491440c1e024101d1003c01403003004203021315842d140c0800168040c52005034120000144201d0040c0304841141d100c9449072804c0c00580d5080002960009100582001d0040301c00a1651404d008141c043d603241805001d652400c03a0510112 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 829076834 1250 829075584 829075627
    0x70803100e221401021305090603151b0f03040609020a0e0f0a15052107170316030c15090605060609010f050c01140405031305240306180a02 62
    0x110819020322034400c1480c8003040304212a42c0d9014051030036800c100184407224103416605500004500c0805030390126980140c40702164001100e032601c1307084c9070b034607e1891100e002d88065003020400e403400301040e00d06078410206020b8608210003904518a400950302100c1441c0c45190200071881c00301d8400700a0b00e0007040740d80c00c9107411213000001b84400b0744901440350361741d02c8510004c031280780c444010704005801042c40140314001161a12000c2160100354020001c010615203200044801448120402103080030078841440034182d0f1801411014001d007042c165001509a0320001817242e192107000a8940c00740c1000020f8840003842184540400c01003150142e8204a240e00703005980d2500307a03150703524904d00c2c1d401845400c2c902c1d204c3c0d441c041e04002c02c0203000001428040000c51f08103046941d07600030700c85d5070080708030072251140c006c000306560704010a000d15402a0000d000583e2002080e011004492080c3e500300c0c6443e4000900c5103540b4100c800003c2c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 829078084 1250 829076834 829076849
    0x60403050706021b01050d1808040b04230f01050c0a0b25080108280b040803090d170c07051e01021e04180203090718060609080d0206040803060a0b07080310 69
    0xc0707130301501300090042c854002502c100d180c0ea4100107440c40121520018065445500b1540e01c50315206c0c500117541003441450b001c05002d00021904031010906401000c402800f40221100440019185500700c02006041882030842e580c0108900f1700030703540100e85140c96561496030040c00c20503061009243c01092026078401040b210b0400070f141c401c040b802c1940e0f20a80341c0085a4004e40001d5180060030740d140030b80070300003031040c40302c02980229a545c0c103c5164004006081e0741740203c1c42030103e10b014150001401c0c40303140c0402487c0040c4a882912000ea442c40325011180c288400c8148080e0360104800441c0702e840301041c0304445002c4282800d0078a0840f500f102d046044120359000c98011000c1142e96500b044010054800304280a0301c5030010350b00c080041013188116000107070103480028102d200890b210004540c6c59014021558071030311a00300b2980094103450700028071040004000300060080c046a0b4032804c407040d50713410421049149460550042c0e01d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 829079334 1250 829078084 829078123
    0xa09181a0103200c070e06030609070308090609040c020c030d030e0c040c020a080708030a0c0807050a0e0f060a0c1101020606030a0b0a06030b04050c04240509130206040305070602 79
    0x1180e6809000300114440001d2801090401e410101c4100010290012425400001c225201d14902c04140c89056494038003041e00c01e980c2d03000c2096645c1c5025a0b000c0e020750450b4030240b000c5680d9070020640c0c0c100240c00ca41c684000500410304582e04051220010b80040399088801c4c6001d126080e580e02c9103103000d0107070b14a250002a2174949201302e0500c0345079a9131503025168001e2005001e03041d040038010340c460021b810b204416034011145140300b00e113803c195074015800380e40030a001c0d1441c2e0769058185981c150342568002c40c0700c0812a8405100400c04803196501001020b094443d5641e42240c2a80b91422150100701320403854155000078082200548001581f150490380040380034240d40c684025580050010781c0001c0c0c00011000104410b02600141c00281f1004c1035504003c800c072415070000704e8881114060410060101c0f080000d032800c20016a00500090708001c41820180d0002e02150711560048400350403490041249a805000701030b694110340d031303259 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 829080584 1250 829079334 829079351
    0xc02100206090c091e0f090d0203070f1118131b05100807210b0f0d020906060a0201062301180f030803180a0305180411091c080a0918 59
    0x1a0f0700c1d0758903500d0090140c038412002031300380400140d003e602e41317207103942d8050b0500700483e62685c2c0c2c0204031102d10a0344591002c0386000b600c00404c0b01c20564100140520750501c0356140201c000032000341ca6404000c4003098015400040b170441e0003145202c8080b000b1904616212a9052041e954100300312600311040000ba1241d445050408240d450140107581c0c4002c0c056803000d034034140c1c2a800b9180c15a51140606880c0e2000410350011242070706010342d0501046540c24641d00000d400c0b00d01c4002082581c28610b02422010580e400045481c0d44c40300843c070402424040d101911031401d03400c9464950f0081c0f0402a1104845489000300d0304103002d85401c0070803403000601407a00000015400fa0720f0300b01070000213021500795002c084071ba0400901981001120424125006440e519189044e02c10a0108072903141c825044c021100100720312401c0ca40007407460041a2807503003001a04900041c0040c0d00e89840700d0500e41e0410000c8000303001c1c0303202da0102680ca001e204 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 829081834 1250 829080584 829080601
    0x804050f040e0f0d120204081005041a09030d0f0e1e0f160504060e0405030f070c080d0f12180204050603070b0d060914131202100e0c04052809080f04060c02100206 72
    0x44040b00c2001100109041e1034a24cc400f102640d856132500600124105004c440100803000303003182151803106014010300702c03104008a4841c80c042d403034540c0c098440075004c41422400302c40304010303030420798040c407440411040c103090f1400070340d618030b10b004c0d4020710852a2910943d07015080340c200d207a00503d42655200e540c6d00c1248030400828201040c10810861000d0903030f400742240100745c1e40200400d11015103180140704001c404501c841612000c10340f104d1040a2101e05050300c440030410098003400010705020b0302d0f85815005a030004030341e02e403030318000f02080000102c0000d2a10300e440c03c040100d905011202402c040a07000f8007546849804101f441c5540040242c060700d1440c101c240c0c98203000800c1408090f0802d401030941c8a400b0801045000c0c003510140308540e100c4040c07510151035110075414109007503800c0040c01c4055400100c019104c0e1401300c0c5131a00d0b00041764203136046a8403410008035041c44040850502113000e44910890340010b00484c2801c090 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 829083084 1250 829081834 829081843
    0xc0e1504180618050c040605031f12051e0a15060f12031e0c080c0a02030618010b1002070608070201060f17100e0606010f02150103030201270804050f040e0f0d12020408 74
    0x141000c11101001240030b00141049501461580102b460015691040e1541c01c3c10b1040300280d51030701031840c420700400510f0062904094118002d4101990a581c40015818500800c280c6240c0c0d1608041602d2644c4103255025090010300040381603114540203001942c502f00e207500500b80722101007140c4d60420503240e501a0f01c40a81600c540d49008054642410340c00d001e0f60520030601030024800141c2112158405060000e001d0042003509204250741583c0040d401a4000b1008111140c0b041c000d0703a401c84098400403550700c0c0e90f83c1c040c4046030b01c0c2d600a003507a02c450751030408607040108101d14040c030041b202808a00907003070440384c4600d00140001e060018440c41c4c040f000e0f10902c5110b41c500d01c0540c030042c542d616820001d0003000d6446a90006a00000400c3d4501040c0c0401062031a8000b194902d0541000103102881103001120b9801c1703620fa0440300a8442c09201084021420f500140390b4011080c40c001c10044c03c207440f9118a82c4104014085030030b0104 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 829084334 1250 829083084 829083089
    0x7170d030b0a0b1b0709050919020f19180203070e030d0c110301020f0304060c020606010804050622080a0e0306220b1f0305030405130c0e1504180618050c04 69
    0x142c3d0240c0314030324408042d41807682100310704854040c81d2004113030300401e40c0c00580203020240c1111138203807500341c980e0000b0f41400070196000c01e003002441c0c2903144c01d00d5581d9a1a010035078050566035551400313203000c8601c1090b08425500402004082c0d07611030a0001444011402010701302c03411440540824000c07031000e0800c1c21350958082550304d00f5012555507500c1341180701d50382e01e82401c0c841c008059440d0300000501072030740403800e42c0d8802d424460240d0341010290556442d03c043c903604c80c40850b0000b180c00301001d0b22070804900c00350302900e420401c64032a010884009810982040c000514180c0d1040c0414034100c0005184001412002d610907505140c40d100c0c1c000e04411140c509100341d014804454011007080408400f800071520306561141855000c2c0d032601b8143c035420740444000540300540c4500a1500d40100c001180000740790500d0591210740203200301104d0304042c0b00044d102c81003080b080b40c0390b01e69010b10110f1910200b00f41d04114000e40710f60f11175031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 829085584 1250 829084334 829084349
    0xb01030c0e13020c0a0c0807090626330105010f020a08183c09130f0c0807030b0a02070b01060f05160b0103020f04090b06040903090807170d030b0a 65
    0x42d070240500c480701e5030440f4604034000084a00c0141a4a0b00d007071146400d0181d00b0b03d6028046001900349801d0281c1d4050743c080c01e420b072031461840085000400d41d40708002896201d2502700c202d840b6505807440b2140d002c2294614000c09a40c02407400820040c2c0c025410044040a0200301c1c0743e02060030000160f1041403d96a803807403030a00d81c4032903124600d03994400501c1e0000b4404604402401c11503044030310840c04560280d440b261036055216840c1e5401c44981c500055283c007140c402020540d1045d2040144082203403182102d0040c6500001b129601c02c174028403d21518407140d503071101c00c4c448103620b449143c2d42d0341c0849000621841b018040740010b2a42c071240035406403043c01a24442e1068900e0340da00b0241e40040d001e20051740945210b0a280d0b1940c00d00340500107500b0342150070071a80d07071101404e020080115100a50412038800b101040412060203828010900d049a0100c0803010903035950625064402c031405041c68040c0c0180581c884220100856201 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 829086834 1250 829085584 829085599
    0x40e060a1818020a150215070e0f2101020903070503030f0a0e03100528150b1303020301110d050708090a0b0402010507120f030e010b0609060306040b10030b040b01030c0e 75
    0x2403841c0c4a0002c5203116000754030652001d030102e00c01100d0800c00e040030806a00700c5002c0e903590740000600400554584000583d400c41242281c00c040701e070980d402c1c00140080c030b036803001e0074508c03542c0c00000b010306002d594001424041034a0108a003201070031007140614a4402403a804841c1403040d07410354410700c08100101c080070381c0c00f0302044040a920ba00306002d9031070958042c00d410060342500b480409041c4d0b003102108212403245044410102c042c90398500d04140140803580c00c90340070fa0100003840d000101c01620203004501c03041020810151316181d00344024025180010021801c110004040150502d8006201e0740c01c150803c1510909454500040300d1912880c100513041d441c0d4076030210651036000c40102340700c07081c0707039010042c40726654203035400da42860700280d5011109001046032890040000c0d60003441c0240300040c12204030000c0b80d211a8070b042104086950340380d11550a04190142c104989000d10b8100102c42c0749800150188408281c4240604103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 829088084 1250 829086834 829086851
    0xb0d0b06040503060a0e0d0e22020c0d020c090a050f0114060d0504030e090105030d02030904050621060a06150903121106130212060f0402100909020a05040e060a18 72
    0x39010100c60242c000038007520340c103103002d09512000c0c0030780042842942c419401c04014062043ca804040040010009554032854540002440b03404507095201140d0801c9441c0c80c0c0e003030402c2108092034058010b0b04900001108100c10a0f0300200b401000c181400304008948152900b043d05640000805d0301400b003580d004125940a824620328101c0c0c41c03c0244804d1580103c052444840125450095030ba21001450b481ea0703004214040960b10500a01d041c0f40b03040c2d04080c1d401b0501400c4a014882e40a0001071b01d543c41c2c40740e96000e60032410034015020b60900585001c0d220078185058200c0e1032140007819501c040c4400b03003003c441e0000001032a44185500100da00e88401160b05500380100030100d60070784000128401c41000369041040c0b034000c22510b1040c0c2e14205918401c0d511902803001c82c07091201044104048080081000c45645c8050324400d4403d40e00c0c651145c0c101051710000440c003420241c4504c00c8808100040000710941c0324405803102d90109003010f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 829089334 1250 829088084 829088089
    0x8070e090a121b060e100c0e040c0c020406030309050a1502100522031d030a052d010e160e040b04021c080c03030f070f120c210605040b0a0b0d0b 64
    0x10406400881c3e5462202804400d02c441d035007108000051310001e40d803403045c01180a07822140c00d8001000450503a00c26100d0b00d02d07155110340b202d41354a0a15480950442d800201207610035001180822000182400036007800e14050010741404011a800c0c17603075503200a940c56a040220b0a02951948d000409403451440ca400c5110411030303e15070348070300c58030780a440707802442545403064a00400b656040c0c5400248140d201d40c0040103001c5003030b01c20802141c45211005440400f801d0284007200440b42446115104043c80c0c014120140704283c04403981d103616480005840462420701c004110301c001d00c140c21075411a05c1011802081601540002d00800094040ea00c04211560f001174084015031103944403132001000750391048002d0b81c0d1816051324105c00a21510b0705c0b00c0801205a2145584400500b001641c030680d103240c00c00001c695040008625031940720410860615000d4003010348030845002040c5810140071400078002c01d88400490f6840740344024054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 829090584 1250 829089334 829089347
    0x10b03060d021008040203010b061c050915010303110d03050106320c21040b0304060e1005011e150509010c14060705070b070306030210030f0e03031008070e090a12 72
    0x81e07028200c1a03120a03c00d0b005018a00200d8059000e0b508284503c1a1450108119170560300e90859124100490901401c002c000082070040c43e4822280c0c0105075007100744041d8000c0d0300c2a0b0703d01e4007414529103818207080c01403100509041c200401071040355044080907607010b640c2c0603169510800103c6000c5101070035603504000d140c000540c600c8500d004102c0d00225079584d4007101c00b100c880c50020680303205511441144081c01c0c000703c2c0c000307135498000420103000c00301101c008210344807c0e03200319170707081c0c0c0f00121034000091850031070790300041d00d00010080110383e82c0100010510103020761250040341410000a6102407017041540c1340524203400240d02200c0091a01d504060016400204103450b413440540000307071a284030740501c0c03040e09d5010700207482c41f0003101021b401808124014201c40c64403184080302001040019511541c020703020110072501d4084020300304003068001c140c07035a20107000c20280704800a000b10140b40d004884040400c003901084808 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 829091834 1250 829090584 829090609
    0x10c052d03090106170f072102060d09020906010f1e050c06090604020a08030a020c09150d031d0d021f12020a200a02150a030902061201091103010e010b0306 69
    0x62080100070b00400b030070154801c034283c0d50203800841403007110f2140290b99030b181031580740f41580001c209005501518600414074400c0380b0040c2d004201e40d42c0060031035040551002d14140d5240000c030305524000e140950019001c1c00e02d1440d80040120091000c0440014403081d50301051110680d94417403c11601541c01c1d10050701c8060400d0032030303940ca40c20203440c1a071040c800c030301e0082590b003400300c00ca481c4403226030014110006c0600c14018040b0004004240d444030080458669449141c0000d007a41d110340e0b00d54001d03540080c3c00500604411000a01807070f00c118030100180c580f05019911403060100c1d88a055030104030848400c1d0001040c1c03500d20f0b00220f1400031342c40c0c011b01d01800802c0720840d004516810951000c0e0b40d81c10360513002c2d52203212100c05500003052031004103006034a83c0340115088417540c01040380c50380407000d40000ca116110041014602601c070300c1d0300080009001d40e01c1c1d5494041c040c04910030601400042c003800002144081d42c81150300107a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 829093084 1250 829091834 829091917
    0x7021203040c05010221041e0b0706050f0109020a0c061104051f3c05090612180708420f07032708041a1902010c05 51
    0xe6a1501d460944101d20842c441e01e4003610174440404101c0c00088042c0728040420440142400d16201e409282007501c0c42680c1c19160002c03101050a9100348014006203000e13002c04192418030413241e2102050592000400c1d62040c404c1b01160b907484074142e90216003150001c5542c01c8106001d0603148900d6108035400172012000e6410081340080c8981110300503210550309605000126a02030128910200e909580d84c2001640e842d01000d192030800c1940380c06802c200c0b255021a0050748410341e00c4072300403c06010007603208440810b14900464100c06003218528050703074640c0c1e03114090000000d219110030000d0251080d03818140a030b4800c403400702c405180791085205021003c0d6400019105000d0000c0d10300c80c003034022044440c00004155100140702065560102030002d82261003c0c0c00300b00004908820840040d0780380c000441c201c2e0703140d401d114400c00c00c4084402000075a4140b08100e01c00b01d4004080d01c1c00e01e071001c01008900c0c03000102d900200d41c120102c210 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 829094334 1250 829093084 829093087
    0xc0106080a05060903160803040516060903061817031503011d0f0c06030a090507150302131a0405130207061119020c0a090e03040b0403110f09060307030308070212 72
    0x500c4100014059107007900aa050300c08544541d5510303500c0380b10b640c00301c00394208800c402c81d00007003501c001994014014010b07200720b15015910710f254a0f02907071040e000101820018018404284100060500c2e1055224045078131555090740c90710050900c205070500c0400002d200010641c11081541c0d4014020040c401400c0003a801d11192415148003070f01ca1100c888022760f02c0010000403000d0b0080c011800c41e03176010040c0d0701605000000301c4039801100c50025003003c3d1303c3c0c030400c071100c01760300e0250311500a2280f004207588030750300410b44075000422941000b80d00d5021101039400c140e0b0300e0002d20300048040d00c042c0c412500c1c010b2020380f5200d0700300d82c420381001c0039010b0b1007401c3c64031401c40c0084003000c80c0c0c0c0702503883c3c449a101a03003000800c941c0e103040e48032000300b181580990382001d60b03c40301c121f600d0300b16a03c20350380c203a8003850071501480c00c07681600c101c0e4412501400b10381440004280c1d42c00113400005c081c05003003000714400034020400402c042c0c800c500800d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 829095584 1250 829094334 829094339
    0xc02030307060f0f110324280314070f060309030306030f03110615061602180a050a1407050703030c0201060924080105130f080912010b0a05060405100e060c0106 71
    0x9401842d0709050713031508510f0b100f07641400c0541281100e0041e011014802200200014800140c03040b00c03003030903400f00b4404d46201e1407004052070010030300610320900c0c1e01e41e465800d02d4410b0300045c030403645031500303c26070900810603880d0f510130075220b8915001401c60910314041d001000303182c2018005030003108a007410103a0120110081c600e00d1020f480031a180c0e441010395440c1800c010036070101050002c02401d17154005800d182d140014810305604a00704c1700c002484106441101409458004000185500e405102c0002640d019000500c0c5401140180345001e0140300904251311602d41c591024030035003015000d041000c0c010400040401c0ca18071500c0140c001c80b032035020501d4000102c00c0d0040c41524070582c6081d110000407403c603a280c1e0b01035030075108120741220042c0301d60910b81e120b03500b600d45600070041c0009030151100f810029480050b521076031080c08204003d101c01e0301d907004281881c401305d00300550020312110014043e40190094031069610780380c0e00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 829096834 1250 829095584 829095611
    0x31c050402032506030e0102040b03070203131202062a010501090c020f060103020a03080313081603180b0f0c0307060c020a031706090f06030c0927011b0c0203030706 73
    0x56004034822821940c29501e044910303a801c805074564040f00c0596100f0030015240240c01c4500010340040005141c252640d110300c1458000350791840050344081030318010720509044d000083e0509104008100c1e0030b6500082643c86500c08083c00401c400b00078070701e000f0f0608c084120806450000b0b00a5684036040f0800400d10a00b080c1c005110700c2545610814000c10080c0c140c0b134024041c64001d90440c0c80d04104d0758406003140142c15407802e403620220707008001809818042d062941c07858800c508000f40a050310000c4040c050600100c100040710b1400110f034241e0b4416090b0382c2e00d64224084403030440c014280040c00c080c0c00d2029404e0b12795404076072248401e101e500c4145501c4c042038248001a0320443c0c0c0d40c0c1c1c011000314040f8420115050700716a0040300102100e80301d03005180031403c0c40ea001d4030b0200261014003411310381440425401c189094004008000210501e0100c040e903070400f03d003076021b010100c14041e0554405200312072416402c60421b010308603002c1403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 829098084 1250 829096834 829096841
    0x3140114160f0912021512191121130f0c0905071112130314060f090114041b031212060b041404050a18031110090b0117031c 55
    0x2401000546050803002d9800d001d02c001d142550181c024250305810b0700e0b0300f030004580d1750810704202c0b00000d00400d0100b010064145104480b013110780703403404c24040903510549140320202c0700080070a00000da405081c0101c0c1840c46889103c9000554584520240200307074041030140142d021600b10b4030520910710384003411508000400c200a640340c020032246c0d1341012001e00341c5608108207070342c4401316100143c090768a0603100546429503030340d074800181408000f241496044202080403208a10000c540d118000800030300c02e01d000c1032429a54024001c00003070191a441c2c5296800042c00c820070710166034800000304100125200240c01c0000d00d0307460245187c241100450864140402e0b58111207031210a201e0000741c4c03100300300c0500401000384c851a9030719020400c4c128444412410114025103d455585a118a490b03091407042424440c00908194401d400214810038550460b100030425a8509046281081c150b00c03940c49100030042041d5418844444241d1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 829099334 1250 829098084 829098121
    0x5150403020c131d01150f0308220b0d140703060b04120f05010c0810050d020d0305030a0908210a020c0a030c110a030309080d0201110421020406030c0611030306030703140114 77
    0xc1c1c81c007801c50f940c7e00303170021550141c0401040c012050000380b4244106103906856052520400940d01e5200c0b6418007181e004200c200d248a919a4011442104402822a00306d075051070203000441c20b2910f001c01030301c22842111a280d40c00d01100d400c3c000c0c84440312680d558004001e1022403d0284011701803103081d210303417642c020100c40004a03490304952013103034140d010b01200f4040e022a2010b80c2d00b500010035048403a85c5542241e000036800000070812842610b0701040c0390582803109d0040f00c04020410400c0510410440c01000c4000841d20070a55251600824049492401000d0345d1141c0700b000c2d0304004d43d0500401050341020000099035407003c111a401911078104034280c0d4042200b084000d03004010074070006407044019000506d58801e440c039924540c0d4085011554542d00c01c3d546c141039483e081c0300c0254090704281234108808000d40c10b50070407200094450314240b00040c005d0580384441c2e01a40c0c1c081d003050b042c54140c69440c0d02e481c03401c01c0600d2500003121 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 829100584 1250 829099334 829099361
    0xa030e012307031b0e180403050c070608040f080306270a1112071d1e011e1d040902130501060e10170a1b0c05150403020c131d01 57
    0x2d4075062082c452100d04c46a940c1c80c070450028603040a6404640c0390341038680200c8913034448106a0521500b00b40070394480e544990362690818101da081442d00e8201104110130b0205100202e00140c100d607030310700d4000818030340c1c9484640020310030041d505c91f02e0301c2034102e203500c5104000d156214140f103441f0490080c007840080703003450394030382c0b1800403282a0340c0040c0c1d0200e0031451154030720100c0d0f500c00290314203c002c00c040009001c030119511605840850035014245540d02c0310000082801403014101040c80a8101038007469011000e40c030000384401c0800300983d42da800c01c0040c02e4010b41060620109846410060310090280d4000b044000c29030040b2410b0420170f289440280b5542d8110404180003210705d840c8000d80740316819920780d0582d844901c0071031008109001180c0741e202103150340307240450400c040e001c9a00e542002c120100004203402180c24203e0020445110075414845c01d00d0b900240014480c00ca5a040801149510000c1c150301036541d001e00c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 829101834 1250 829100584 829100651
    0x30c090412090e04032309010516140f07030203121c0c0516050d020c090606070f060e0d18050405191d060a02040504150303022107170d1b050306060a030e01 69
    0x10801e00882901c0741480c0c10340051010000b440c0c1e8010150b0a54001d2031280c45108030bc00700c840b101510380440c68034aa03a0540100600f0401c501e000c2104900c06a10024020300b400650349040160452010040e0f140d0742d1104d030a242035900c6403085a0165a694840c54842c00044c181070fa0390381d5801181101520904840300b6480c60480341c00741c40b500f40103001c645000100d955615403041d03000700403110f01da1140d0003c0e01c40c2400b130008103940d40f180d6a50101c90041d500001540c0715995100d00d00851802d42400828041404003150351a200a00881e4001000d0003d0640d600100c1450255000d418140102100142c0041088503c100ca05001c80f60041460b001d05d0f000a00c80200036900c4200b07041b402003251000c5161040c90400c4103030820240e6110005840f80da607907105d040d4900010a2050050703a03120383d00951141181c5460105900301c000350482c480038100d144150b401068900c65144603401c0280080c034280000d0001048140301080340b11001441580c103580c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 829103084 1250 829101834 829101887
    0x60708010e090606060d02071a0a091217060d0f390e011511060a0f0c020a1a0a150f14010519080a09080705060403020c030c090412090e0403 62
    0xf40c5a0007000d00400d02071034a000c140700071000354020a07044480c0305840c5440c0940b5446014942e04c01c07100a540403894a0003440e0003e1303000071039070440c01804942241104200501c1d443c983d844a8141c51200c2d03000981d0030031028290301d11000800710340034280150b0301d040e2005101001401ca252407a081ca428000140c88054000e0088030b0112921100404c107058030222481e02c4a449030900110a07049030ba21142003110841d054054a40c5034991001090070300d12980205035980d10203840f0b040d046944034100c805001d00c4030345001c40980045042e1690a5111400502c0001e03465044650384088091414401c1e10984280d440407000400e450b5001c0c2c02151003400b1840003810201d0412241603070300034400707042161025910001800020007100040194901030300080a2a241030715000340b0b8503c4020071240a6000642c2d40c001c2c03500c6203c8803d800a9100320b95a40071041524115080030843c1d125007101d14100d0240024580c0180c5d44505440c00a8100041e103074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 829104334 1250 829103084 829103101
    0x304030c0201081302012a0c140a061d09090c1002011a041b0c0303060905040602090a0f050a03110d0c03080d0e12090f040902150d060503010902060307120b03060708010e 75
    0x4010b2005c0d020640c0310802d04e0f62840390003440803603480503032400030b098442c0da2282046850035400c0100c00802a0025001c2c031315194040700b0044c6114074106032045001851510b0551003110700a0044140344042201d9420a2120110100024050b50812400410001d000c2c01a4800c049400080c008060030241454029110840c6d5802d11a040141414a0442d082610301400f41c0406a64040100300082d00740582800b40e8040e03000580c4440381c4a0403c80f407070400343c0c01190380001c030304820405038a80a540004503600b0228480903103140c5004a005410100d00050002040d4000842000b600d4000f402c15400100300c2004008078a090706580c8040e103200f0140400000d10001c4c000c0c0c1381c20030210344c031101c020f400815a006160b0108400343d21805c40704c03007a1280440c003445050002c4c8207000081100b20000d000301d289a0300440c442d4400074042404000314800c0303043c0b4108154000320203115029044466518100200901514084c001c1480d10f0112501045c10417 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 829105584 1250 829104334 829104361
    0x1314100b0414070f020703050610090c0c031e03020d0c030c17011a0a0201020712030e010b04090206030c03040507080f0109060501120c0b0c07080f0109021c111905060304030c020108 80
    0x40422030140e9107490f814010f4640d440340e501c1c2241140f0412034084005201170040502860407140c030f4643c0141400896019640b5240000d0308001c00c0c2240c150120b54840402090410040400f4071024807140c800c80203071107402c03078118505060501c80003545a0542c45515001041c0e502c0500500c04c0754030801c8003c40a209003001822014030410707800c19600002c0251036081e000062070040303c1d64800380400c200300c0c1ea080c0800ea6412104514160038003914a0300305048504000320703089540001d800c1e01001c2c16401900c0000300000d07042100401078800030b010000126640001c0001116000c2d01034040d007220000e040a00029a035201505042e4005500c0384e03100410500303000d4000078541000c1c0407060300d485151400924201c3c24810819001240d80010481415a0060000f0a01d0801e001d1b03101d41c0d04882c054000c259505456050382c2411128800c050290800a6403041c01c41d070821a8040e4001050004050b00001d10312000780c801c0e21200b801c2c0d90340540f40b4070707074 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 829106834 1250 829105584 829105601
    0x40e01050f1e040513120810080f1506010507050f0a0c170a060c0201020d1e0e0607021b060f0a030f15051005090409170c100b0a09051314100b04 64
    0x1080b000c21981c424500e4107800050b8424010b00d503200c810038890300c40810310108902d590700403803024001d000d505400f405d11302c1c0251030030000034061407034013250940c0d07a48800c10403100020304070300100b0030580c4141e04603119650444212850601810840b030f07140c24020604a6140c04203500002d030340640640d00b0542102208060a1600344075107890000e00101810001155804c01c034041c1d001d9a103200340a6064111940c00c0c4d610210700043e28100d030b41e6421900c816921030790400181c141d0020300d43d0500030080c2c01a03001e040300c000125480e40240042180040c2c004a00c500c00d0a905603c00860100300e00010b004808045500380c5c1c000d0170078041c480d000200c28080300c0189010304002c14504038060302c00150440c460305d404880c0c1485040102050790300290341c00e0b2143e410011014801210701c070421580c0144000105202a20710840c03202c0e50700c8500080c4024a580c0c1005901900b044000420034900e0304a66241c04c101c0340003091070380c60080b10301c54034102486458103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 829108084 1250 829106834 829106869
    0x4090c020a2a0302120a020f190501050a03020f162f06070c18150609050603060907051b01020a090603050f040f170d02070b07050717130803040e01050f 67
    0xe0007098004001100c40b00800300c101030710384020002006884030400340c0021a02100a8000301d02c25204214036444198041c41c41089030700d40142e1918507016800080740c009003030980c1d0303811311203000350302901682021154002010440441c41d00c1d01c40b919210003031281d220710f0240d02d00800e00b103401c0055104035051054003207800d04400e080c07050081040500412115030b1740350703030703203200d40b40c26448800301c0c441d456102c11100c0013a05c4840c44e5035004e007005040c504005403e00c00410b0039404020b1140b4400c04d414400300e00d81c02e00078811944211001801050031000c98031402d0f01070341c450b1403a00000b541c00c03200060460301c207200700c42c06031b00041c800740320580b91a10399a100b01c40185040d01c80d400c10304013407403641e10301d0310081813070029048000d030302c0d0740301414842c0f0b401c4401004030061100801c180c2c000200c00505040d400303003550341050340314526640543c1e0300441c1d80d00300325143d200010f00440c81d5900b5a41c2e050481b003040b5400d0b400c0410080c180070107250f44d1008110b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 829109334 1250 829108084 829108103
    0x30c051201051e091f0606031803080a0b0d2a0602030a021207030219110306061e10110d0503010e0a023406061403060106021c0e030709050c04090c020a 67
    0x3400220400103081c4c03c140030208032142c000b0720f072040001d074482d18400818003983d80c0204011894060180424031035070406900400c29003610b0251030824000c1c03650240c00e82d00c01c85503075541d443c1ca80554000381c011481000c10309041c801c201000040c3c3d80209154054800c000135814030000848940d072071241d014059031040c1441641298004500c11815409550b012130303480c0e0080640c614095001e44044684c032401502410704141000e00b516029100030300260002c0b181d80210201c0010703081c1c41c544170f280d01500040754841c1701d040d4100e400b806070705030020300e19178000041e41c1030b60300c2c000d01800d03240c558101007002ca1240380d01722990005800725400211303c46840d0244c1703d100c085038030100c040079a500e0f2012a1140d41000801410b005540446401c0070000c142c0900342074001000c124050310f5040251110621075402004010014040c040c0c405101c004020000ca6205110074241100c4000241e002802015805450491104aa00c0c4001403100c01c09801c0114170 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 829110584 1250 829109334 829109371
    0x50916050609060d022205030123100f120203010e06060f010c140109061a090103020a090b0d14030c210301060e0d0203101a010c0209131a01030c05120105 68
    0x4050b801c0441c0140d0700c110240210541c800b0b59000428200e41d070018840b07046041804862258a1590007541c02680b520f01801c00d51060304180340289040d000c1c1400007903443c991291070705050358108a07000301c08068001010030f1031003100035040d403086000707001820b1280f16060b9902d504584560380114030410902155020b1600d041449029030071102e00c000d142402c0600752848048211582d0360340d00812442e0400007001103020300c40468040e04c640d45150002408454240214910140d0340c0c4400c040c0d5035510449101a10340c0440142103a08a401c081ba40700e0b000b03c580b010302c82c018418008038040000c0c55401c00c2075074200c4013a04507400d29004440c2d410031080b5480e0030000751003070707030002d1b907001c22411740a00c0049a01141003014400000322030400d0f801250305010244001b6001039840c141466408410034412000b890a58102051550011058204500c090070008000c0c4001c003d90302055074000c0e15041a401c440b0300496003281d0048600a21003034200e003c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 829111834 1250 829110584 829110589
    0x30a0804060809100c0806150c1e03090406090e1903050a2303040f11040b030a0210050708040b0301030b0606091c080c0102040e060406090603020105070803060a03060203160305091605 81
    0x30f0300400701c5011140f00002030180803040765064000e07078021800300ca04100d96490110342c8100350703c1c40c07010110700b88980400c0c1195202d0103c80e00c2c0c60b0b04105050081c003445410420f58000e50401001407052560b59071016004082940001220340a6031200180e655209600b403d1410b500d80d6410b4a4084c42e200100c5420500d03405200980d0101c0101c0310144462401950069000310800350fa000c01c01d00d041c0381c2e0f8a0705c0d848501c3c000d504001ca008866074010580c001ca203a0182d4144041c1415540d0450325032140074402480f107180410080742c0ca12010000d141070b03070711502244845440b104200920380c0118194140e10200d82000440748010309c0040e8200d2521414140f400c1580700c420950984e000740c0c000d2000110410308000507840c02d401140e0090080c11010085281550002003082c0b0400401404030480000460740d00e803105004d0744004c40d0040c50454a07818030800c11510480d0581560b80080d0800300403170008800468040c40704410203011005051400e0203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 829113084 1250 829111834 829111847
    0xf040303050a0204270b030d02030a030e0705100207091415060912030a050c0105150102070b2503030b10110622060f05101d0f060d0204060e0a0605030a080406 70
    0x5199098003840001110f0031091480d69054009440c54060508050200c41c1142c84c12011b040c440c0d030044081c00a082c0d00401104d1403200540b60201e1099000c0000c00c0c904640c0ba403042d500308600e44c1e07940080e55400b048000581c1c801d10001d010030741600300302c00c00907131040ea18402d120001103203600b0a40340140082c00c00c0c62010302902c10b80c45a040340c05046030021126031022600015048160340c40a11605a0048510115800d51196400000d5603002c8078007815607108000100c071720341100c0c84a1184501c1d500d181045040170581d182c001c0c0134001422106020300203400c20810a01e0080f1002a00282070000505141d5254001028030b515041d411071095101041e041000c90301c03602400d00c3c2c0c009402d002140505041c44000420056688081c20602281010101c40d50344c84101c96007001c1d81c68210381064803048001101c2e030b00450002980540b17400341c00180c04640441c4944101480d1408010880c1d49a0906469000308000104030b25000c00041c08030360f01881 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 829114334 1250 829113084 829113091
    0x1948021c0e030105044b0f0b0a0204061b0314130b04080a0215031e04020109050303071209051203042105030406090e06010f170402010210020f030105180f04030305 72
    0x340a56141c0303501c501080c00c4490548085d1501e080070400201c841c02c0303400e80c441440380944000352030030340580600400451004107043c5481c00d01220102802007039540960015004646100d141c106074125034000d52040c862407020400c040c08030a8068507844100114980548895070200c655010442c1b055010171a00214028800c001140284003000600068041e81000b0110308009004001340a070b0540d440300c0d9070b000104100030162080c5250a0f190a00c58000c00383d07652540d200582e0351014030f070401c981620010542405002034010000e807400020b443c0d441c412505c030414490fa08003080c0c9000720b075a2041000b00b25141c0800c4c80b0070200e02120913420920109a03031a503045130300130351012000410b210300c00d012054108213055042507007400e10840c0c14500520107001552411002030900440100041c20b59000b0b00c01084110000a021540e503000c11280325000e4100380101030060043ca44550902c141c2c0c41882c5002c0c950000001e41d0035640e035a000c80140400030f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 829115584 1250 829114334 829114337
    0x4020409051c050403050c030304032001021903030b090c160828080a0b040b0a0510020a290a050106171009060b120f010b031948021c 59
    0x2a9040d1840e03810340c40d0b0200c0054150740d9038540e16841d5042c01450b240c64840ca6034840d42082108000103a16074070400c0034800c2c040d409034540804400140d0402002d001140740511520401d0b200b0540d055010380d0301c065049940c0121500ca91801c081a070144000f0081901151405200410703071041c098a001c15151680c8030084083c0b0810900445e110b941000224603050b0502041648600902d24401d00a03241040804640000280840e801d80700f198000c5d18048070600c1124800e01c401c4c010b048d08100c08140d034100740540e420040516410407a0012601400309000b81380c58010141201c50a41c0c41d0302040c0b80b100c1ca9080d561034044c11001d09050407490000c3c100400c0e0258000034070f01d4440b076603100c002030511203079260300003009405400815070043c001c40500fa0240e91b00f00503c80744800c000d80345021104010202501c610001c401c6400035662000e07010410403401c6500c100710002c448498601040d01c20010a000c031016801c540c00d285262070940c420400d0320342c1175 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 829116834 1250 829115584 829115593
    0x1103010618180b0703271a01082109010e041505040c020303061822030807030c180e0624030a0b010c0519020a0e090a05070602150a0207140706020d0e0a0501080402040905 75
    0x1b401c0100001500300e840c01c942c1c0c100f4800d80341d01440360304842980146061000740c00ba03803842808a1115508000c0e461501240c0840c0031522648110756108428a0241040045407800550311205000c1d07031240758452420500c02c60b444a2010080c2d1b8094540030301540041c071488604000300600c020156030011140000b52980c0a010031000310b00075000351551213041c10541c40044c152070b83c6446401c1070040030018640d5490b8818852001c581c101405080030717468000c001a0b1400610001c0c02c2c7c4940c8031009103201c45445002140070b442c101004000540440006440c41418080c0260140e00101c441c02001800d003c071124841d84002c103d901c001e91501030128286800381d40500ca00d03800200b41c0e41c1000020030400005e001070340000c141092a4480038009200003e00701408c0d941c010802e6002c0024400440e003004680106a482071502c3e01402569030603042801d00000b1045021910503003070030300802d4141d504c1a541d000b0140c1e907507028070001d4203c1c410b007203d03103104 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 829118084 1250 829116834 829116881
    0x1504030f0f14030706020307030507110a03081012060f15080318041409010b010906050c0c01110a2420070b1306150f0816121103010618180b0703 64
    0x4060008000c1a4805d1600507203a003440301c4001c040f644000d01075802d12040344040381000758001802000340d40d243c50080f40c0350b40e80c8a040c0541510b180d124103060748c403001224041024580001c801c0c14228402003150800018000e05140c140d44190042c40d0010440350594050031080202031000151011800c2c040c02d43c400100a1740883c0d017095544d41d11101d00007190391180e040c0c401085646401c1e03050a1100e24544c1d04c501352701100038144840d500c4041e4016031309008600f40300350000d42c1704a911002d000c86501c00c42c0505114880300d4600985114200694040740340c1510f00204628180140c40d0790314120389174003510031a694500481d0304800506a0b0140d83d0b0742e40903080d08160002d01d00380401403c3c40303417074118200d1a041640000002c210850980c0211110501d03ea44101114140b1404908070303d8445501942011004208405014800c205610204500704841507241900c01603007640d08000819607151100442c1d092882a00a150341e40c50440701c1d64200d10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 829119334 1250 829118084 829118123
    0x10609030b071403040b18060c0a0f14070308101a03060f180c0d0f051b16081813090506070e180114030d1404030b0a02090613051504030f0f 62
    0x410440307040324203075082000c100f42040456987c071109405034005042c1030816451141842c040d01030010704100207400c0c5800e08a01c9104404003240c418246242e031a0011b04005001d2a0b040b255840a54148500045d0510150503103d41001445603050b003075031140010084061038515405a000c00c1c0d1904000c0444011021a03002d40783c00c1e290540c0d14103a8840c044281d6000d0034a660720140f038481000140080389600403000c90b18003030007d071780f8466008215103c0c1c24208000c2c004103c0030440720400f0b94200c20400404404071101109812010156000e85a9101004040360091800305032100d0284501d180210401800c00812030710f41c1200d038103200c209038010240b00350303c825210041c3c24103002c8180c4108603407504080d01d0301900080001c92056100c0144444015070006041409990582d084d107000101250380d644040036004d40c50510034010148502141e6181704918800e4400300d4040301d621003c80305a408e01d5413110f02c049038502030142d0724088000c10000c40d58 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 829120584 1250 829119334 829119337
    0x40602060c0d1b030c02010c05071a0a1d0a021809100b0a050324090d080117070e01031a0f060d03140d0c0801030506010f0b07200a1502060906010609030b0714 70
    0x802c40c0c4d40c0007400e05a2130f14021b094031485c4100714180901040b4140c0070030640001c0900c01c1c107a009020416455440c034290082480040d04a0001c82541d6512032070b0001140b00d09007180200d50b82003c18158001840507401c0541d50516168050940b00105011913000340d91826002010060101c0c0e83d04003083c1031244103c2c24103202c825900c00100d00c42d4020398501e803c1040380000b0041c0400708000034100500c1070140158221100d045004100340810584000c1c29040001d82c0d0203503941d203010b010440540011804114100001518106110221030f00c0741e100140100c00881c03140d02c2c19200d8403501e4078071852641c0c040200741486110382c01904080c0000b551001910740c51800c1641c10180180c02c030202000e050b41e000c01c82050710006403050941c00641c40c5c00c01d004142c0415a0081c03c0310301441d007201c1013140005403106640500d881000c0503801b60350301c560740c00c05015200c01090003036001040c4180d0081c03010070080104513500005606065480c50000210008117 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 829121834 1250 829120584 829120631
    0x6030708060102120c101b17042112140601021207020102101a0a090b03030403060209040914060a0b09161107120c030c09140c030705040e04050706030b06040602060c0d 74
    0x1540c01038a411030340e03500c40d101c0c5100b07824070000c098800400b40300004008c61381842d68011009034140c0401d0501907215080003813090243d071f001c4500380304504082c1020540c0d051035442640303040b010400d50000c160015110340300580c05401000071030813004803242c100b031400380c1c114444d032001c02d2900303070192203059028030308100180102e1404030700f004062941c6400c107410700c6041000c03040d686d490010999043c0c03030780010050b1301e40c1017000200b8000c01000c40050004201a0705911a02c0f0000c141c01f07010340404581440080c0b154030078401038240645080303012502c2018803107401e920410100d10802c5810054880c0d5070342d14940200d5200d41c5200650700c109000700100101300154404000400d40000244003020750582e265000010003041a084a0000000502d2407813250b421039000c0d02c24004180c0103030419040081d40d0b146030303001d440c01007440c00b0041003651410030190f4045030801d50003040b480da100c07103054085402c15206114600e0300c40041c400350900442408c0316 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 829123084 1250 829121834 829121857
    0x2090a080604051207050c0609040e0d03050a06090b1c020d1b0e10060206131b06030902130203060607080903070b040e09100b2b080c030c0d0e0603070806010212 71
    0x1810103080c0f082c10198656000418200200050000500b0125070148016804c0364400d45440c1144042006403815580f040898050380012641c01a0564403042c0140c0d04401c0420802d503c8044410850398074071003443c1e0110b21562664205150300141c46455407000e80245880d503202e90b111506000f0703241c10015420340c149418440e80c400307800401d80c89507026139420901454007d02a403650006060000107445000062040c032810001c5904c8121540000c642e2880d03a81a00a0003001c04280482c0324444140d602d0b50b282c0741c2e40c02943e0061000422940c9003d00d25582c10a140d4880c0d04100c0e018000c040340002c80a55442c040c0c0010000319005140d1450440e0805044c2411041e10003a50303480c0100d8480e540d11400b424940021111010803035882d0030090240c1d28503090b00c03008052440c00940502446000701c045d01e400d002075400c0750b0012a407400c0c03e41c2e07c0d08010b180b45030807690500014000d18820800350380c001034103005a45166204000c136603859403003502d4040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 829124334 1250 829123084 829123093
    0x30b0103080a110313030f050114010927030f0804050a0515040203010c091809080c070f060f03060e0c030c16030207080d050306090414030d060306060f060e13020a020102090a08 78
    0x700040c0c0c101d0034180201d43c0202c00b451900070300f45000070036103c56000c050902d904410b09642000001d6110960300c1d56007503095061580d40f00c00d5800909100b4031640565110217480307000200a4402c908845a0b00da140d0000d59411114106e40c0d00100510940d12031003128003040224205012440300c4001e4092241140d1909005050035142006002d03000c200d001c01d810810240340c170400d20400500c10720702040580307607070401d04c000340907680c5204c081e030241c1e102c001140700040500340100c4220b510350070a041904c100590403540c051013511211601040002c242440c84402954042c070784913003036810409041a008000b034060f0008901581c001d08081c003011070108041e08000121703103842441c600d00500400c9100a000d040100740f1006a84017144d40e02c2c1c2881954040c0c5442c0d070b410884260340307040581c050030a51003518030302841201c02084040c443c0404030a00603004d4040c003440042c1030750050080d03028510b07560465600f405003451590b600f45501c1c000f0b181800c002c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 829125584 1250 829124334 829124347
    0x30901030b0d1b0e25050a0c0b090601090507050f0706020912010911090c071a060a08190b0105040b03150c090a03082109102a08160203090117040804030b010308 71
    0x41404040141c038040d00d03d0040c05a440718240c11006400c1098070621b0a030351103c20b8020306441d001d0444000800070110441000784016000179018125902044280080d48a625040d1041c0c03250740c5103001001e50070400c06004c20b0142c6c0003040704120240600b40899420b14041382150413031201100c0c200345005040b4440d02c0d0501580d0303040030000401324946400c91340d955240700c070181804e80b01000384900245041c0c1d121010040140049419581d05110300150b90240040d003d00848200c14a00000714050603e8894080e0702500500105051045002459071402d00140107582d918010422900c65444820081d001940f207410710350b03103d40c416400d085821400c901805104104042040044000090300b8020301c105420001032100190b00780007000c0c01ca03c1e40c00542d840306035030304292590384000ca46105900304070f0150b50340140d845040b03071240f04051845000400d464845201c05482101e01074010b8440c1d00484d01d031540d650740f60410390307038242d005a44500380032540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 829126834 1250 829125584 829125599
    0x7060f020d0b030607020a1b0b0a050a0305130b060603090c19030506091603120504030f032006010b0a0e0a091508060c030103050a0b190509061b0c030901030b0d1b 72
    0x16101c42ca181100540064648014003e68a0201070009080b0640302012070321440d51001c0c5a502410740030245035070350303841980090155480f09100c14002442c000c0002d010820701c4250107081607000069604c4c40e200d12041004c10340014001d4895400740d21200c2d290f5a944d03819660310700806440d00304450780f41d03091582c20840d00500004880c0c0001413240001c04401040c0d0042d02d40c4291a0051041d402000701e64a0041b034000a103a4081130269009064001008503150b840803104600c1072840e0321241c503150982032003490031208051200304080790050443c040707100e04c040c00301e1400301d41c2c402018054881d00942e00c3c071418006182800a02e100340040b031b0344a42000791091075949140c0d0399680e20400d10101070701144882010900c06203804a480d0f141c0354907440207000034140241d1003522505e0954502135602074180e003c4048a98901c1a02c18207003240c40038608162031540198003404030546102e920500c0482940001851000d04001080300d0b80c00210100341444c42 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 829128084 1250 829126834 829126841
    0x304061d0c120114060111031e070c120213020d0b03030d09050c0a0f050d020609210c150403060b032a011202160615050d0f050c0103020306180c07060f020d 69
    0x2d1092460b410000e096030403843e083e403659040b030030030b182030314000034201005400e60003008a0441150700011400c11449025805024814080c1d000710742c0440d500e2085580e10006000000d4212070b14121104030a1110b60103050809030140c80032800107116000681145d01648a20040b640d60303001142c00d000003042100c9030090191688540c41c2d0401040b0210a5207520a184c4114007003002c43d02151030303944c151000300002070f000d00a07501c0840c10018086e49050075000a500c11841100703481d20f00b0003410800c0c841c1000d003c500d070604548903140038001401c0565007502c1403104541c0966443d0038921035650013a5213850303041c801d0b100010100405044e1f410300150060243310641864059401c2034994040d400040140b501c00c2c07100103800c482e0f407009078403150f41104042800a50000703044064401c1041d41c801001820041d07089010942c0c0464100a40c041a0740401d03d4103205e550304403200a81c0c071818154150b698000b42d4403090700d1150490340104512a003041c0900 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 829129334 1250 829128084 829128109
    0x1b080901021b1e0c01080a0e01060b0f0a020c040c140304020609100915050910050c10020d020d150305120d0f02072001031e020d020c01060329060310020304061d0c 72
    0x5028200240107180002c0100c1d10107000781f440365507685150f60b0003000035070250300200006443c141e00d030080d140d40c020031a0000ca60300009401034001b0a00b0b589032a00c9910300300c0b5859100c081c0c28040c3e80c0d0b043e4002d0380004000300d0b0420070400041640381d40c1d03414030707100c80c0d8042e9030354401050800f0f58040404481110010a005013070010b58001e0b0303901c4c8800109240c4a143c40c549954a6001e02494501d03c80081c0324480d01c00145004014904d40003480c10007030454052081581c0c118075098100810310000d0240c0c7c0144402440d001e45e201c00811070100000c2c004290880014042022a0322856049900358001090714942c80502d0340300350044402403e0230400745150010030120f207052000030fa800903600003000000d032850395040c2c90404080c00c0c000c22100d901c902d040082e100b0f907003014a92010004e20300c0070b988101840b801b84a86400b5001d001c20312442c00d1003001941010f40200d810035142d00700324800f9000703130111442e0300160100900e0210440070a03c03220300c0000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 829130584 1250 829129334 829129393
    0xe070602010c0206061e0924060412062d05160f021b13090501020307230405060901030608030d0605120304080c09060d14030d0f1b080901021b 63
    0x5624812064010070344680c03014003038840c42000c6680c1b5840e01046148a0251544000840c0903c10030071146030006400340c11035038104980c0080803080050034000c030321812403015035040c081c600003500c030781115100b2034100c00000b1000c004000c0d449800224001402c44e92940d4030100400c3d14500500104e803100340d401d00304541c800d800002503c85000b00d00810040404c08000c1c80349441d040d00c0c000c130414603642e081000c02c9a030720b00359000c1c0d032050710260002129000700c000d1700e40d580101c0929a40c0d800003060325240c42c2c0f0060200b26040340c00440d040c9980d40c0400550104148000d14231003440c1300000407100d051804011030810f502202d450740780e10500c000e20100000040100c0c420008a80303500d0250391302800140900010040144110a0340c40e140f030300c040001010700f00c0070151031000e00c02440761140a0303003150741014409080048400c084205140031b0000c003a00001203600240c94048001451081105200c030307000901c0d405030402d00b04240c50101c07040f0361807401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 829131834 1250 829130584 829130591
    0x3030c1206050f040e0c0607030504030c05060c0a140a020402070501090201080c13050d0f050f0601030b09010c0f030905010b0907050a090503010509030a08130b0114130506011407060207150e07060201 88
    0x104030100394185040f440d0380740101c1c1d6039140460440380400092495079030062015030f0302c450524001f801500140701c01c550f503120542c00454180782810540b980f01c0f82c0c22000300800e400030344500070b8840094050000300d004110309000584c480e0300013082c070180a00d00206000c2c41d00d200050040e1001080348118140a10410342012040004e850850310100d60242440c0c40c0d508110700b41d0140b80e640100f0034071403880380f034105410200b500c1e412280140d10b040c1507941d803082441d081c0c0b00305c124400001001d02c05640d0106011380d02200700c1c0c5001310000900129014045902000183d403201c002c602c0201324903500940c0b00e064580a403105030000c0c0000d0034082200b6a0303900603100020140001840050907104200c0000503136075402001c81c100d9542d41b50082e50703e036690410110b018026140c103c1c0311313845803802003901402060b50b503003001e840c0901d1110010707080360300111181c940801c00000800c04043c58040c107000604400200c2e11860304100c3e02e0000d03583d0040065904 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 829133084 1250 829131834 829131839
    0x4060b030f06104b020d0e0301020f1303120e010804030818070303021b040902060711120604030c060b040506010f080709080105010f0f080604032a0602030f09070f03050606061b070303030c1206 85
    0xc0c0401e02c6c402c0d10f070725410a95210310313110000a01a00984c5000110200049113003c0480e030741e11155021a400303894003e140300100c00040301e18030340c0b10708034601085408002c6000244200c040d02d6014101c040c210000102c40ca0b1198102403450340150016485001c020700401603078a03802076a190f085a003001907041e5503010844a010f4150080c0055401c4d51410070143c40310031418003100c4000c402d40e5024075061801920700c10b5414400e80700700386000c1c65404c82e410140300d200e015940584400c481d40c201c3d2403045a080308020174103000c10102d00000208040c090042c1030180c03041702c0c0030241450910b045102c40c2c4903182c1c803030440c40c3c0c040018031020980016142d400034584001e200300d002107989205507429840407004110320b100004104544101c4650a8000c1c95400250f520307940d03550120006090450102409a0700203001146e00c80c03a20400404121000c512400028404085807a0405000d60300540110b0f49039552540300503441006032a0300c2d04982d208005650 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 829134334 1250 829133084 829133087
    0x7020f0d1803060507030e0a14060601030e1c11102304080d050a060b0309010b120303070e09041e080418050f06131b05070204060b030f06104b 63
    0x1074881c400545541d50311404140410300c0f07601300e02d84041407202180d001d07000310f143c00560601204070f154154060300c80842c5580d8800d000c1c02d10000d5441d00149421070700c10001500c10f00741007a02c0c01c1031101d20341c40e003450014144545c800300f050f13401d0005058000000c10090011521070450842d449003410440007c040cc01603c00039455140c002449548102d0074800610a5404c01e41600202200f04000e1540542212045100554080d0704908851405036030720301098070a9400b29001c030200d1602d906020f50002c0d4400e0084008000c4900c0191a0704820003004806a440c0a000201800429034041184030042c0e2412003c1044e8940b003c00100707020409002a44a000c24040f011030076000394000842c0d41d8001440301301202003024025055520121049028500300440020881141c806a80c4140355140b40c0405a58880c401c200d01441c040211501380001c1224070592000409001020710a0382c0001040755000b460040807807200b641c80001f590000c1583c0760348801e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 829135584 1250 829134334 829134377
    0x30604020303071b0e1602010c03060609060c0f06020705030702120d0f0c0f0b010f150801080a140f01020a0f080610120507050f180a0f0e040f030e0907020f0d 70
    0x3c6030000090300e40c4029041c3c900311041540d5124892210070281800200e0782403e5101d52991940c0e0001c2241c040540c5007602520070f680f24a81c082030035081e00300000b80c000d95000031030921403801c8844d503115039628101260041003094401d5071000c01c0441c01c60409584060341e01200c0c400a0181c0b1700c11040003014403035068503002c200034043e0b450504000034036070200140340c4e201100c8100c0f5a1560301e0040319a01718811080c45243c0b1640889000c0c0c0a40c101030305076040500070b480000d07095199601910500003421403c5c0c03050010034031701d02b00d00b0300c094028480780f5a07410340800303080c102c0100914400f0700f000348a001d52600c03200c00b287e04600001038114111001064503500e01c9400c0d66240201c424006480000050903851000c0140c02c00b130310303036400325450408651185e030b2440d60702c060390003040c241c3c8440c0c201050109000303012145e1100c0c0b207032401d20400900e42c4085800f280341598a200035a1001c0c1600007402428440c000484409203411808480c5003e0441e444 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 829136690 1106 829135584 829135597
    0x1e0f030c11060c0712020a0b071b1703030411011b03171509040303020903190f020a14150306030c271605070b090109230c030604020303 60
    0x680b800006031424030070a0002400c0980c240403a0044410b160302080e81d02c09088100041c15414500041085600c240c001480300c40d00c1001c00c0c1038400c40d40d00081c40e06201600700c02d6031604000207695101c2d8101841c1d245580d11200140c2d10107603d080c3c25550006440501d8082c940c01120320101d280c05c10b010301c2010740d0351840d603513400041c445003940e119603440d01144c0800d200c0c0d0090400740e1001400d840441c44070000501c1c1e00c074800b08040340c032080900140415407804403e0800200103100c0120b04940c40c3c18001404010300c01c807550b501e07010200225580d40c404001c0310481060140c8452008040742c04680c074a040b050394410b540b80c001400107888225550041809200542c40b0107040440996440b40341101c000c2000c00c03d503503148102d40200b414039000d0794203280358500746459030704a0b042e65401c0c600f2502d140c80c040c0e03003d4001d0000580740001107800c0f = true := by decide +kernel

theorem cover : BRFrame.Cov 828956834 829136690 := by
  have h0 := BRFrame.cov_init 828956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 828956834 ≤ n) (h2 : n < 829136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
