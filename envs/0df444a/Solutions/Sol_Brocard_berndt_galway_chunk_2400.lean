-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2400
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:36:30.784078+00:00
-- url     : https://prove2.me/submissions/910c7dcc-93f0-4a05-ada4-79549e4812c1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 431474820 ≤ n < 431654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 431476070 1250 431474820 431474839
    0x507230f030c10020f03030a06030b0601020c060a0f03020f070f120e030a0b04050a021206150f0609060a050715020304030e0303031b030603251706010807091805011406 74
    0x101000a480486080180e01d90300c5802495a541801119629510742600554145031000d5040900b035500c1240e40c000100d640702d80620400c5480c1d8a002e410050030b1005123112000c50000c988240f2030000300740213000f40070a40c041e9851094040b5108480b842c04069280c800c1898031910306100c514040300c001841c02c00f40001039101b020101d080e941d008008040d88103440e11441044000940192002d00a1081c05030141e1283d224188508184400034111403409031844000300c41d076034012500c07842401184100941d80c110550324280411500d896803480c07800801c1c0c903a031084200050a0103003108440f034802440760301840c80360340240c0314600380400013020940c582c402101c40104008c0b964814885400c0000c005e0341e40107101408039165000b08800c00c21640244c0140c51100010b010400d000703155000300213a25800140c2c2c014401d0394180442c080e2149110300404403036070340e10850200b00d0100c0401d09a5010f07000030081003074110441c480e518101040318000c3c010208031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 431477320 1250 431476070 431476139
    0x1091a040213240806040c0e090f0106020f160b0901030617010c030f0203010b1611060c070f090207030807110316050a031103180103020306030c15070b01140603010302010c0f0507 79
    0xb040314a031001c00715621411683d9031041003000400620110b001045a03105005d0401d0711607841e2700380940c0101103c00030641c500310000703241c10380c020080d4505400003180c80000d640550483e5064030021031015403286101030048004194660107940d400c01c6422050708011010340c44005828011b540a11080480b001c402c81030b44400c0c8620090a01d0420055102c42c2508945821491107240c06056080b292400140d594102c400040281d41201c1c0c4200040e00d02601c1d08001001d001000f98103298461305d0150032080e0080010b814804c020400407000c141c14401c42c0c0d011800500704100418050400c25074500c1c0c1d0000440c085000c0d4102031a602500006403100740c24400076021902040c400110080d40000d40740302e805124400e080c0e54140d44d022040524045611002619030000782450704030000103078400c0c003001800251074011a25120100d034196502030030029079441c150300d4400002001e150004d49140991480441c0540c12041840503000c0420811741c0c0c0000300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 431478570 1250 431477320 431477369
    0xc060a0519020304060c02091308041e080d0f0c0f150605010e010c110607021c0f0203060c0412020904020d12020c0406051804140304090903030b010801120201020601091a040213 78
    0x817802840c002c200072040102c0145086d4030f074076600640d030111107440111155a4510960426003040046c613100000666203290700541840040c000358008182480079080c0c050030700902c1286640812140d811414144446642201c40040c1d00808414410500f6a90741004100f14003c1d10300168800c80e9400e0103602c54a0650150f07500300c040c100d110507800c0304200350ba03480028101d8000504d10889403c4000c241d509000740343c005e440c0000317105128810141441c41c024030000e40300360180320521414401c6405c1514a69040d5940c41c42030b1101c0c000914081c200d41e03130044c46544c02001990b10f140c0e003c5100d440d07002083e07030240302846d01c507070802901611121209480000741070000c0c0200d414030a0303103400041c0c1b95040e240782503150030581e0300b030b01e0001c0001d0700401d880d0b0b001000300e9644018260700405a50940d02c046140550000352211810b1090702c034400e171034200a0300b81e0380024003030900380c0000401c110b5440c40b10308851114000d4074812170085c1c0403014000b050b00c81c02c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 431479820 1250 431478570 431478577
    0x40224040e060909101a1314060105030112110d060f0e07061d060304020f0a140108060406060522120311061b0f0a020132060105040b12090c060a05190203 68
    0x10b007000a00880405c1608040c01050140130194010b00b81e090840026220440f41559030044400049100700c101820b01002c5a40500010304008080004022000400080c3c4040e994041b16010390040c0000000380808440d29002d4030442c68180441c1d00d01c4c50661040c4540c02c1c42c942901c3c0c03400e940c0c7c2d0301a00d0784100c210801c10f84181011241c4078501c4e1840040d94080d200415030b1103940d404001003140c00582d0740000300d000d088036945880d15038000081d190320900455081c0482402d1010081240c010b4100405480c0000075000941c9c84e6907000c0b80024045508481600c06140c2c01c0003421020f0303007410102d280c01080c01161043c0803c50f01d2111030400380341d0503440c0c441d8a01c41180d02e5030100c0c0740380c403c5541e200410ba10440e026200320142000d000c032a102c4c0d0005001c01d11894002c082e0280e07051143c10482007101c51160402d07640e440c0340d51584c0c411540d81e0302c4070660031b108aa4440540c40302d0001b8005070740b16000310107032112001c0c41c00c0c1e421403e52103150036031781c910 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 431481070 1250 431479820 431479831
    0x1506010f030b0d06020c0f01050a02190309150e010b09090c030706080a15150e010801030222090c06030504051608070509090c03060108030c0d0c020d0209040224040e0609 75
    0x1480c905000500e80e00035004500442c001410700e00800c042c50311010700700c0c1c2258401c00da541d0418220180c07441001d006258120300c8031023045141032122030000c0b020582d10f03031084040c1600d401200707003482842152255640c1140806025034007c02001c50300800f10303041e83d5441a041c60001c285204000603503540941405801080b07118109001500e07c02002003e0440701d80c0c0316600040103e29a602000c018002d41c40f4030644c18040c1c00001c0c108200c58048075040000030710040001da59002601c00c00e04a103114041009501070280102400c00e420703001e03249805402d0005250b035495480588503a00a400b500c90366000940c5801d1040800d00c10020a80d10181003446145400013406070021178000448400c6004100402d051542c268031000c0d031a00f01280b44544000c0a03c8103015040c07180c6005001c440c0702d503000800104452001074050980c0300d00040c110745074031141d961800c2410000c10b040c540c1c016400c1266030304c2400750860381504100444e07068240f440138035000c3d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 431482320 1250 431481070 431481077
    0x130603020315010c142a0d03080a0f0e0601030507050405010e07050909070507020d0b06010809030408070306150e10080d03060602060f09071508010f080a0c03060e150f09150601 78
    0xb4601a001124400d0415105640030342e24420b5108411400b0400948050442c0b410081c0424014100d003490300004401d040c054400000447c000036400010164011a0b181700010020540c92810000704041760003241d00d4407540c40040305101c0c0002d2044111542120103006030b0f0b80303406200d802c1004c240d4903c1c011a03028008880c551038422085940540c085c9015414500c0d1500001c00095056100b238075490034500500015507807010303a003580100031200031032a042c504003546540311410b20024054943c1d91b0700c081c02444041070f0f0702c0000e0218006030401ca05140e5000840d1a0700c600c01c10311544907506011800a02034059102210440d0b0058003403030b65009507000c1e480303900601414075401440c00100e04c0310700c00c03071418bc001c0d001c654611740780b0760408141003400e0050f5001a885544030804074000030f070000701d07100140c035031001000c1100c00c9010401460003040000c40b2068100d10004c11000c0e9003e9002c140c8690588001c860b5907190000f6401404041583c106000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 431483570 1250 431482320 431482351
    0xb10060306150e060f18010e1f0513091407030b1503041509060f0902040b12070b0a0203090303030106030b10080708010b0f071a2a071113090303021306030203 70
    0x2c072800b072050385110007005008103281610b4801e84200e00d5002c204200586178403840402040e580c0201d04c0d10074040705407003205007144002108198080f00034400010040000b0b50341400701201d50405006120080d0240b01c1840d5040e0880c40a080840b50407001a10f04500d40c40e2a10f0240b0703251a01d18850a445850b54803213844504000f48041d920031a21629110280c0c00030341c60b441408680043c4500c00108090140304000560342c07030150b00c0d486400024611221040041109400c4030121504103654580303082c0203038214094440e00c0c82d0701d804044000100c3c02c1d0980c00c00e020b50481107a94082480c0399034000d0324940710035030385003000407090401805100403180c0100a900215a40a820301c00c1555400b020740102d200c07000c0d4019404c40c01d0007161110400781c464582c40e0750815191680a0095419580c00b40c9540a01803051030848030125444013400c41540714800c0c2c00a106660700d80c103010f40a94044c00d05464401964030000541d107210348284c80c05481e210180020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 431484820 1250 431483570 431483609
    0x30f090614030a0e060108011d0109120c02010c0c060513091a041a0904083705070c35070311270405070303170c030a15120b10060306 59
    0x1a4100603c404001ca0741c0383c0c4014090761007040f42134000c000d03120011407401842620029500c0c40b0442040e1503a04045d20540064038203d8040000005440e0401800000d070004968012112001422014220390301065003036001006100301c121854071545400d542d04100c1089400058610308240b0681510071250314054001a40c04142d101c4181661443d040000d1220034098078210384a03e0700040714183c10345140c1c107170111054030410807844030750580d000107400c8a00c04041020020009071002c200448003144801502e44840c004030650301040c5401180308414000801c00c1440640b045200407000030790b00b0590781d01071200e211140340241488100054060385654100b0341c0b03024003031108440480d140c42103024400070041546175050103000c52540040d00040300f1803841c01c01510fa114003003140c0d04407060160000b0b824010884010703100199802c2584a00e020b8030a280a01240018180c007030041c0c2218a03101d550b66200035011514180700b03050b2280f102150407032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 431486070 1250 431484820 431484857
    0xe19050f0f07110f150109140601020703060504060f0e03030603063909030a080d060f030201090b03061f02010b0109050303070c031202030d0f0c0e0d021c0f06021303030f0906 77
    0x85405000d4129810a8241e00c0941c1c100405886421410141440100a00081f90144188089a2a040c2034030f0f4144140004d4071102e050001421058450021401f0444550302c2080c0b4a00d400300c040181b4040e00480d15165401621854860320800c004962001c030003442909400343d0b0a0859061087d20742c1000744c510310503000994010f6002d00071940d10751801d118075407002c0d10400c1401d075a03080c1c40301e03070b0030803200a42c000d6503d641084005100513600101d40342e060303945644105031617548850010320602e0b45002650740c400d2500d1142d2000603015000108011401d03280d402d185a15081415035034000e6010141c9214640507003040414100e04107001e14290314410f6074504402c000001081d40c555246c1c850515507182d01209003d580a2652901000201c880c00c40440e2140c0015005d2420800031010f4108024849410807040b0041e0392840e96020000390f440c4d8880d5080c02213203000511055000c02c4404078441c0c6900d200c0c8113040165006600c440082c0b00d640d440b0074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 431487320 1250 431486070 431486087
    0xc1b0509071101090204050408130b04210503070606030b15120c010e0328060506010c0f031101271e050a0f030c14071502070e0109150e19050f0f07 65
    0x20b010702c0d5038036464400562500d0040b40c0c8614024801e0350b0b0303508401116847c07940f81c0e0303502c02c010000701808140420300c2158006100c500e0b01090001100030f042c1801410b41c410301100500003440c18078000100405005950b20441501c8001c80340011194140030b80d4000242040000350080f281241e155070044101d01084080039084880b007071107071100e81c20300e9144903200c0030a6100032070a031000c110300c030302880341d00c00c40030b19202e00010000d030740704c011102c660b400c02070074003a05084840070401c00758422441d40d070800301c000c400c19181210303038400001510320603640200c0c40c44042446541074200c002545901c80300806800d03c40c0d1f103950316942c401d060201d0800c4400e0b9403010203c0d03400030340315190361078079805400c0d0745180c403c1c00e030040c40c810511403082d900b19800401a00c1d204200340d904581c00c9503000316000380c107c603c0c440324010780c0e0050303910203182106000c0c5001002d140c81d001d03003040c0c090030062519500c030007a03d500c80c202c3c1ca402c2c03007080c0e040000c5c603500e11a6544 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 431488570 1250 431487320 431487347
    0x10302181201061203030905010c0e0d02040c050c12040f05030607140306130504060b040510060207140301150821031006110a0b1608060904080906030408070804060c1b050907 77
    0x2419540b240c100d842c160328041401d0300000c0e118001f20b02401020b104581d080481d03800c2180214400002081010301c94141c00b80c0f080f0764503d182d11600340190101d418203061030055941400108120300660341150060b02d602c071503d0b10b0007061506002908501032003d54407003003c1010041c110003000e82c0300030550741e0028980300c007840200380746001d2039011764030030f40000c107580400105220032a135000700350394442c8841e03050410071241c0104494080c2c481c03482410106004440c082400342940e24104507601c1d0404800081101c1c000c20900710b107034940c0703030410780c0b05414002d41c0595000c15214201f0100103160100075040c0071b1116080c100c004581500c45202d100d4030352180c1220126200406e05011a000d2007a0f0369210b8126940300710111240c145904150b01c0c0c20510b8000c0104903801a10000702040a206e020310036100a25881900166a02e4032148000d02c8416028012504c0098501c030004100c0201e00000080c1c1c1c80150660850b60394026003147e40d00703c410329 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 431489820 1250 431488570 431488573
    0x1101020f030103170702190503010c0f140702010c080a08041a0c040905060316080c120307120c02130606020706030e0a0b0a0c03270b070908060f191406030c0103021812 74
    0x130290040c0c0ba07d0107a895540c400140c4001c100e4a84818103080d83d14010780317042000541c104000341a0381000b07454410300845031040fa15421079100607100654190800b514100c000f045d1680b0f11503101c520301d03100d288203084401c42111542645450103e081c0d5404020190a00c0184111901ca038002070b4440001000c440e0b00d0006041c80040c2501d01e60001c4046420080c1406454200071707078100c0305e28400c0d100451800d401e988030320644040b00c2180004020038015a08150350b1000d540341c1007000c141008001c400d68814000e5030300c082910415001c0303400d1284010460802140442103560040b01101240c2d6030400300d80e00400315007980e101810340c0c070401d1185449201e000030002c8224204036110400345c6041c69500e80d40002c0510007040141101400b4805000c5105a003044611000c1c04040c1c07500031501c0701c000e035010008c865040c03a091a1407400402c40568034024441641503c40050310040110168450740c0050203c2045c6c01a16201500300340c006803400c0f050410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 431491070 1250 431489820 431489827
    0x302030702190b07061b0f1205090307120c061803020a060c02281704031e020103090605092506200c030a0308040b0f10030303090213110a1101020f03010317 69
    0x60040c4081d4201d00000e17100250780395454003c24002e4210110309188500b46003200c112030349002001d86000c0000041c6540c0c4500c007040c81c0c1241003040c0c07620141c0c001e103894000e010304d0030010811614807a040d91514207142020300400c07050201c905509825038087e041c0502030303481d014058004007541404500c925010700c82012200540b12107240c1c42c0c03541d5040090700c00d06081c850329000303603104500b0003002c100400016810301d05400a040e401c540c440351041503800142c1c01030021032405020181071200b00f246064000c200041d2403070f80d00c0c181d814808802d205142250226001c2c0d4404500342007288100040042c90110800e001c40048030000d000740c0021034103042c0079039011004a801601408100080007030181da101503000710300c2c0340d982742840400603c04110301c405030615a4910241041d034607074400004051181000a00c0b24619503c407245141c3d00c828010b80c0090724050614000307620600840381c800e441e01514a0944c5d003180c41e4142c5008129424045090080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 431492320 1250 431491070 431491079
    0x90703021f02060a1b08040c05060714010e0a030807140c070b1c15150509031204150504050901030201081008070e01052112090a0906080105040201090e04030203070219 74
    0x810045071521145100790040010200043d14004000d40f61640c0107043c18002c6140c3c50b02090400c100c1e40c0c040c60411840d0311141000981241d280d0080e0381c00100028103141800003050b050a00600860000c104800030f50814075100c0c0740c800d0004001580b0840842d61a40c42662900020050f014a051408200122051615220703920500340d00c0000f284038554990300001e00352000d108120103002030f02c6024103400c00c0307080600402c1d241c2182007540c07034000f40c803c070f0030380d00804006403c0703482a02c0030441c4175a40750407501c40d18035000782c001c025111491150003a50b08860001d85201440c0e42075500641d401103009015462003480600001480d010070040f0741c0060514032810340c3d0319410441885103680700d00c085041e03030024010090b03802c0c0f407001691940100d410a08191a00e00341d4000030081241b41d802000e1341e41c01d02c4000b01d80c40006500140c0140d100b600e62604581ea242842c0040c644112405000340e0030501030b100141c10716815015405400c81007948040340c54 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 431493570 1250 431492320 431492329
    0x1c1404150204051c03030e060c0f1602061305090604140115030209060d0e0c0402270a090e0114010e01060f1b020901080f062428061713110909070302 66
    0xa00120070b40d401c0c1c0c1d1a9610b0217058040c42560200403144000d030140c0d02d01040629414882c2e2400c1140c00d08001402541a0304a040c00301403290340107001542c5c0b40207442129841c1512400303101d00c0703815000301040b20317440c217403046259030b09103080c046903103038a04406602c0499042c00801c0034940c00b0086404540d540d1001060000a1032500291500c03401409618106140790800c0c0541d2040010260072914600c070307030740d40354050705541b26140340c03180c00b0458100d0385074051460305007000300d010301042040d004507044849010000c1000d81c2e84041a5500c08028407840d8040744c0d8955240c24514840c1a2030070b006049031a2009009140f90301064091900368840c00c019000f8000f121014031092200c69081921482c108034040c80c4550707000700d202c2c2181541482070742d07890f07191503070003048000801711400e0500650704d6542ea03410f005001c5a1a80941d0360841c0b42d980c000680c00320b030300040c40c40c0c42070300f0581c04c00b510180d400034001e1181010b0040410f91003155000401a5203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 431494820 1250 431493570 431493589
    0x28020106052d0414070f0203090a05040b12030a050c163b0705190e01020c120f01050a050403140406020c130f060611010b0312090d03051c021c140415020405 69
    0x1e000350f82c1e18a1714011300003c0840d030281e0800d00443d0420441111107941e500990030981e001282c0002e5000800c000191000810311403c04c03550001043d03180d600794201002d442200204405e0301d007002c00184078124140514012854030b4030b01c2c1c5001100007410001003d52107108034420020300204018890090482101c42c0400180002080045811040404000313100e503803c00c4510990b01e02d0020b07488220301e8014230700440c40c0d130702209600c0304204900640c0a950724000c200c5814000c503080060034080781c09030045240c0c0c05005003895440821501119607950141c100071110b4010003c40154008020f1109922030001000d0344495210307440040059444509075440b9540d025420f4410200c0c0d07007403107500803100e102100c00c1d2910898201c030700d00b1106100c1c10f801518068846000d0030f400d00c50440088988050a8443d0350700900850f0407041c40220100a40c0440784152511000350304d0040c0c82e40c10110b800201301404001c00c030344075108051305154030b07500410180203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 431496070 1250 431494820 431494841
    0x7020f332701020a0e06070b041103030d05090c0f011d04050a060302100e04060503032b091b032303070f0c0b0a120b0a120f031428020106052d04 64
    0x250300007443e0b030169030400c5500c140045e0070744440e820039030b0548402c8800280280041d001102800030f02e001560300b441203d0700c00302c400f0001c124030b0801120442c0d0765034403001154050941000c81d0310156002c0c5120107079a40750807094200780e0680d4000d200242401400414240b6114807005c001a030741e003c041a01c0194560311515603a1848003080142c421680c0880c0c06500200402c000b031346503545040303800c0c40402d40148031080030305038214000c100702e440c007070648000364506540700c2d052512507030101e07400f6500d2000da5000325062002c60300d01100700b48106910402115001a02200a808905e4018999000c82076a90300c0840042d81c8208801c00014483d1220303024014050304c54030114074410b940f841501801d000907940307803c40520b03020701540e030702c46c011307008051042084036100b46c0b21040c0c1548030b05400f40303602d007002e0491189802802c00d03041c280c203030103105105050844400030200308200880d090403074458801003c1054801075095600c41040d2164090301050300c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 431497320 1250 431496070 431496073
    0xd03030c030b15040306020918040507080c010e090106080604090b07031515020606150702031b03010c1d040c030212010b0c150103030e060315040507020f3327 70
    0x102210340c0090468140070702c00c0f48203082c0034400401840404090b501501d0b0f000c840180c0d10741c1c3c010005518202c4072035241280d024128200400c1200110311101110741c0d4408442d461041d400c010758039003241010090704485000d004001c074920800c40103412807005040024140c1b440d499040110500300c41c3d440c0845e071154400e20801c09a142c3c47e200030581411899910220314400a40303c0340041c242600c101016400c3c10060703000202104d8405500904030b0340d01d415003e484256500120042ea4402c0d480c100c601d0076100d0007124406030065242d248400d102902004100040100d001c584d01011360a02018001d82503060360135029000c000c10240d103e030801c5105a1a20b0380f1281c1c10400c1400140c0108006900303e0207407203007080105d422549079592703000c8070300107200f2600007240d10a0522050201141d000f080c0c107010310701c0a03001c1d80c82c0305c94855554064100c40702c641c010600f00d10031100090408200c51160400251003081d5054100159600300041080c0f0011015 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 431498570 1250 431497320 431497331
    0xf030c07122303010b04050f030f151014030a1506080a05061f152d08060a0501030b0f06070c030507081c030603110f01051309140c0c0d030c0e0d0303 66
    0x14280380000d031000500b180c81d016499907040007101501c030301a40c0300f44e60141c030411746000084d50b018000c482c2c03908820030480c0c500d40c994090030181c0b00400d40b045900c5070408100070801003140400c140082001030001d01134421a562500422130f50b44104000c042e50314400070031120000d00000c082d00f0700440c0200702d242480140c03408880c01c1000f8251107085580703010080c4541c10040c0629884660400c142c43c4030411000c80c042e030b806074400058030498003005440040d080840c050083e1016180007020b1034440006404655000000d0b035071040d60410021001e1601e4001419820311401940321429500d0b52814a0203425802a1a254204c00e000e0231032948461103004100d03140c2e00e820312135140743d81ca42103440c04103a28101d010760341c08000d200c01a402541150900301030040541002650380c1510341c000c01c400c000306441c94401c01c010551200c4000b0a450344c095030000940900038420406a00420002c0d0510301404030722850001c00c4e5460400255000b4001d4502149 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 431499820 1250 431498570 431498597
    0x50f0409020405040b030105010302010c030c0f080a051b120d0203090a050d0c1101020c01050307031505090907030501230c0a02010609141e0910020a0c050106080c090703060b0f030c0712 82
    0x2c1d02d10178015180281e02d4040101f01603a8040d201c80c1440790982080310207109181080e0491540b603503409411b02c1c400081044910398010300401031407030592105030740800c1c40c030ba070141c035422a4002111192030a10441c289152954000c5030054081c40403540c070011169542400d05c1c0800700884045414410300304140901641201c900c11006d01c0500480703030620b00041d05a01015009000300365950780d81034041800c42c442c60000d040c00410703c514034900914507603584e01c80ca0004540b15424402e00c5840002c12811410588410360311403403455a03a00d04806042d04030306d030944210b43d2642d500140c0312110b40705070000031083c0c1c054040c103803600420360501400304010009403880c0300010086c241d440071400e60032032641e1180140e03546522400c2281d99041000018202c5d52034007100298105002072198024042990654069500e440e410f0381119607501c82e84800c49403c0180b00b80d51180c44008603401840c401e600380c240030f8a5101d403180103031b441d00c4110211300412801038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 431501070 1250 431499820 431499829
    0xc0d0b090c040f0b07051b04140f101403070308090307030b13020906031c20100504030e0102060c0409090201260106020606060a020c1203040803030c0405010e1c0b07050f0409020405 80
    0x3809000c05484e500e00e0110243d032015603131042d2004050300020034140b503980a69581e001004d00010444a4480d0760a241402e00b14826003a9030910040002003000900c69401c50450410510002d02a00740103140d926016041c2e80007144590b03140c02076010110000e9030400b8110b0290543da0000c0284c49c6803407043c440b40002c081d100034441e5100303200b168810301c4100c582c030740c131003010346031130145002e0070041d1940b040440c03034100d800c0d80690880501c0702c6200c0c1d48800d2142c0c2c042d9580100c09200c050041e03032508419511404072a004000034843c200d029049590f13031500c103250000d0b902410241e11000036041403024140106403500401c1001e904201d0141c00000898605203020700c00d25000c1d644d01002030b90180540f202c0300700c2c40031000091042e0740c02810b03100256641c900c1e201e03442030b03940e1740180966804116164034010090805039100c06c01c812011100c064061000d03120a56459002032801003003140070441c2000419155000d07100800c0340050240c1c0303440c00c240400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 431502320 1250 431501070 431501099
    0x60108071505030609041b080a060203091501060203030f07120c120b0402180409081b0706111f1805010204120c140315091203010e04030e12060c0d0b090c04 69
    0x2108200b014410b2248a641d0030608542040d0301250b00c04080d11240355040c61040f45601c2980e003400b5041f22181401400e800841c031501020f402d4801d112020b081d8400c00450030300450006902c1400010003c1404217003507074000d81d150610100c4480c0014210307050702c80064080e0001443c00d44003214003c3d540c020000f1803c03088805508040c000041da0161069520607544900c0c0c0720a0480103028111044a080c00c40b0340d0300081c2c40c00040103802c1da50f91a607101e02000241c4041c10b00503101804189244010302c68240c0310790144901c00000d01524250460308040706074030160341c00155003440140300404141102e00c00b01d01c1913007415035910140e039010f41510058881d154565982c00f288800340d04010b03e03540320706a1114881940740c00d88100c40c1c1c0c271800b08000000300c2c1560011252610881c480d5890380c215191003400c0c80000324410a14941075406000072032420b036240b8000e40b2182c180014000354021803c00041c4103c20140c0d8491055007001400b44206290358005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 431503570 1250 431502320 431502359
    0x3040f03020607030926160509060607030c020310230c030402040209012f010b0d05072c0103150e0f07050913020a090606080c0a0503010605090105070b0709061805010207050607050304030506010807 87
    0xd00c1c161a02000c40d64070270000303211500c2040001005410140100c9501e99030302d801408580e80106911404001801c00d1440d841700368624581d21491264981401e40c8900c056000c040e0441e04e4650a00000c0c0d00500d00d034a041c80050380481741c0300c203c0c105510000381c01d40060465801c1242c41c080e421070f40c10b030003218081e110b45c020002c045100001d8200c111203c0c059480b400007a407826459851081e080c40c083c080121034000401d02082200110303010444510410600b10030104103a0b503400c07c40c00c2520300340c018940421140c94601400d80d80084013150480d011080c0ba030003d81c2c0c0781e9494000902c085d075503941c140001580100060385c06070750641c1507490560243e0025016010520030300c4204900001e07010000e0344500103070b03800d403684031150101c10f0400ca18080d003168811300855002540f82680d1a501084a5412100b1614180c000d404650300b800e06010442d4814002510b030b5110401000000460800c019402094401e01614915013011001d0350610480341c507 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 431504820 1250 431503570 431503603
    0x306060c031b060b19060f0e09060f0109090c0215060d20010c060608010b150f0a030905030909040f0c06050f180103090501020d060306050903040f03020607030926 72
    0x14003000094000301102c94414001d0920100241c841c5041d1010303002000e000b68000c1e5030b4402c02c4010011115140f0241c0700152134041c06840500c0c0100d0700903882c021a02c0d40b0801d10f0000c5005800c003880700c41d4524138103244c9901101e4030381c1c1c0b240c010b8545845a880c01644010f0b112580034210f01ca01a801c10b4040b038030000158501e0f183c03810341c001d040f602d2180c41070000720800e0403a805640c54010306684010f00b03001e043ea48122050082c100b0b0f64000d400b94020101e4000e503100030303101329110011907200341d0781405240c0c40d0480043c01460783c2280c2c54030040246003816030701c40d28080d20441c030030100d11102d40380e1031500d22581c003990ba101c0d0f01408410302c610007102920b07105544e21000d003a1150b501c180840c8004070041c02c60000080c0030b1354800071304e1905840700c941128090b81d0040780c0a205644890a03d5a501e206910a5026807020444180010318014004184860282c580404031a403a190b440d88101c0030041004800490035040c2c03000e00000b4040c060f01c0c54407915 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 431506070 1250 431504820 431504837
    0x301061a070b0a0c0519020f07030308420402040308070803070f02030702090609041a010e07030c170c1b06010605091807090b0c01061d06041107050d05072907030606 73
    0x21406400d0340100103070300403181c00f0050140c500340c2c802c00c08e0000011181c000c498501d6680d04000e0640c039429546261a0a5803070940309046078a68509421010324290f217140a076064081d401c00d40c0e90320f02a16920030340070000080400c4641020b0a4898040d150540d500c0c284150007038804841101c4a4080d03402c00c1c000790380581c3e40c0c0d140580e403100b020703a0189100d583d54036011000d000e18480c050072115141002003400d00110061501c59a02d80d00c1c10040c00300c480c0010703101448964245084546c04400240e0707880a0b0350040d10805049803c2d003400200c0c1c02c4105420070000740c001c80c1c0011030101c1c420303015250003410303620070f04c4105055501314100350704024a08409401100c4511400044040210700250f20500081c8118221032130b07854205d043c4001440b10a4402c60310440c1800d100e4401d20f4102c03021203495592100003041080180c400a607129000110240d903800700d0082c03120702d810b110700100c108840c4180814000e03403400f5003000d022110150080d104121520 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 431507320 1250 431506070 431506091
    0x103140c091003140f010305010e16180902060d0b0405061c230a0302010e0c04020f04091a0418060e190611041203021f0b09010b090301061a070b0a 65
    0x9004441110303000b81c030b10b034410000040050300503003010300540741c8100c0c081c4c04200b4800201d001050503a0312510003400040461000306550b0510180d480380e9244000004210712006c1e80f0107044000700c8000c01144000041d000640540c02582001d980141c540d4180011450940300c0c041d4410021a00d040a0318400c55000485840249000f00444422001103103040380a0303121100072002203048030314503209440d00030301800109440000b1440f524031242c01350f250900a8460070440d0348aa00d040a02e4a80c0c088061305685108401c9556001d80c0c042450b1200c0c080e08a0240300800d0711013000c2001d1a003842119241611200c1d15040310f001d2075240e111a203a0009d07265000603020940c0038450403a401144100d501000c40b1108003040c4804150300400d04100c450740c03001c450441044449a0681900e60701896181d016201000500a03000b420020f803154482c0500001107454458030f0307074441d001c80c0031081c01d03007242c0c04030b4100108080180b03402e40c0950b0101c0c0038840b59070030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 431508570 1250 431507320 431507341
    0x70506100b0a0f0c0c1409010e0402091303090e070f0806030a021309061d010e0f0106121211010509010219110307063c0f09020904080d020d0614010314 67
    0x40c0b0215008102080360090b8059205003260920160480b403817044a44d40d6883c445a004414140540652500b60001803900c0600101e02d10558014040c005140e4800100d0314420381000d0b0101e0500c0450000850030718600c0741032500c07400c500d2f140e074500c4405103013000c0c0c0700a10080617070380310b81e000c0003050005803140803000c181c0c031801107800706075124141f03020005005140d40bc3c01c0418211050741f24101e6054201c0c48405044905480c842810211041e09031121401100d1117084000d2118000520f08400b440564850303161110f5a180c0c1c00e82241c0c00c0d2042a150000c087e074000c903928402541c80300076007130158510700702241080f0040700c110791280506840a414542c0e00c26103000303031a0324080f603984440c084550070340f050080d5074075441049402ca00d03000401483d02c6400d11000426208008480b500142030001a540e596240c1c0160741c006660300d4001c0c0d400344042041f00c0180d01800020b03042c680a51460351800701d00050460308049402608960b519003848800c1c0070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 431509820 1250 431508570 431508577
    0x5030a03180201090b0c010e030705010203070f090e010501081902070c053a050c0603070906031404031e030e01060e09100c09090c090e01120c0b030603030d0e010b030a08070506100b 80
    0xa06145e0340713444100b81b2482a004000942c0440d40900000950310204201907000350b00c921401d8580c80c1000350295021916030200f0b0181c280380d0030810f00107008541c01021055840848122030341c024140c0c8217800c0090b81c0040c0c208072114580c840b824000351030481c8a00e945400b401d25801d0308130a54042603014004854500f81e03603415041c03601d0051280a100c1300e82401000303498241d03070707080400d4010900803080c40f400000a2801c20310801c1511190340c1c04d40190340690302c403d483c0c032031909a07080c00759a202500c1c1c1030503a98448024401028002e44000f0300340045451020b10780101500e041807558104032418529021720104010b40096268003562020540040e400d00c05502c260760b802030036080b101e0600140c4000140f1001c120080c0000300d485644500c83c015178134207620b81e2900041d01e11a500d60020301084000100c2903200c406844090320020a2204d422804a070400d102c540d410740b04c0300400525481400820407106402031850500303ea80c1038501b035040401d500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 431511070 1250 431509820 431509829
    0x103052401080c040305031210060c030c0201080612010f0e2404080c0f060f090c0906130b041506020307022103300a0e1623150705030a0318020109 65
    0xc0b800030414140c820000e4134003441e03000045a0303940600c46100200c0e25800c031041040c840c89500c02241c074520038241a0411949602d840c4000034070f130fa0054a001c5002001c840c0c0180342e49485140c400c0c024042c60201e884001d40004031042c1e41e1407000c0c1010400502d52450480c00240c181511180d0f410869020f034000881646481c180043e00d401c14150418205040c400e41050107242c114a0b01058050340c4944122800400341c0c00a000d50800c1c03c480803035002c40c1d000e55034605070000b9007000c412040000c000240003088c1d4039080020070000d420000050384007041c0e90045007016594011541d0580c4010452407070610026650b92040341d0300d0300543d000e00100c9480c084074100404502c0b54550402c071200307141048003140101925074180d0f44611900c06000940009010174900387d40e601842038107100d0356403040f0600c0e03030804407405130412890f118400c4040016400f07401154810780141d642c8a4040000400369904d000d00650003241246c0c0030302c0141e8000d5903000403507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 431512320 1250 431511070 431511077
    0x109050103200a0c0b011d0f091203060a0b04030609141b040b06070212060412030c021e1c0305060901090605100c020a0812131a0a0e0301110412020103052401 70
    0x100c000c00011101e505244d10003c100b041c100b80040fa07017800c1c0781c1b188604240040900c80d11a40c2d003000314003448200780c034482c009400880242d001505003070001c55002c4405441c41e505980d071240d030140690b00c50f0f88107880050b500d11010f0700b0441c090388100d242c80c03e500001d050034000e64010340002800c0744078482c4901e80d44d0302c0038078486d10707550309841740d150700280729591300002540542d464a000b00c4044400540c3d801000c2e0301d160003481800c2c031500ca19402010410301d15881174a0010309096502110722818840c8003144041801e400d101c1c000c15035001c1001c0c2030900610885000c10b800c2444000e09280e4144010b858044100b541681030f440c110842c03030441d0000c907981240641040e0028060000380341c42d80c1c04070000500c001540103014512107a0f49410f06110203401d410b4841c1d000c40c1c00c106542441e0f201d0039908107240b500900004694030940c0c0c081840d43c0c040d9001e010080c0143c07051900707542e050b1141e01e07446140203a6000258540903400725180c600f031004181030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 431513570 1250 431512320 431512327
    0xe0708060c03060a03020a0608040302251a2818050904030302210c090310090c0b0304080c1006051806091810140609010f0e0f1810020306010905010320 67
    0x1a1341d6144400005540280c031103525140c0362800240015000c680580c0503100300400b0298951b4040b00f425286105c090314407048605020242580021941c04981d24020502c1401d215000845030060700044140104602c400c4241e4041d00d200e50800468104580c043c200700400d45451903081da205074540340050351040710519890210402010418203080c403201000003049216009101c00c42d42242203641100c103904541c800c1d01c581000040c990a82110100a206410000785412078403440015040031a1001102d291114101d21032a0440d03d5072000c10160a0201408410f003403020b082c00814a0b00502282ca401c0c0c000c2c1c40c1103a824020303200b240007079005000c142201c1856031410312120410801044015405550052280c5603c1c000021645086500202101c8042d940d18505a82d00342682000315001000e00002c490003890301014404207010141101c50074080041e140d01b0305c3d07000140521100c1e08458181340c504100600c561264150022006842a1030a0755 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 431514820 1250 431513570 431513581
    0xf160e011e0e06041407200f07060f1710030c0b090d1104020c16090b0909101d03030708070311091804170705030910080c0304060510050d03030e010e0708060c03 71
    0x50014421351780302041c4c030708203001000e603003d0052081000d00c0116940507900075241e05441e0907400100d184184e105850402100340910003126450019082002660580b07032400f84511504464008c0209000c1c1d1080c420400780c04c1e10b0320040c280444c070b00303801c0c01404004904024a0420302604e801c1e99480344e4161a030b1a0b404070b400c4c800c403200940b80800c18003505081d01d03140502039942440d040c018100250304040c0003e9200c0d500c0700004050b54020282000c00070030003090903550348808240440346101d0208000c50007038a150351550041e00c2c00650003011502c001031080c03076047c0100308404250759103804421034031411030500c001580300c901e0405551105c50302d5003d04071002085100c00d000001c409003c0401c0300703a45d007203502040d040b0b0844000400301c0351044900020302c0400d0206819500040d07000710241c00040c40561a480060500a103045c41180003036103034091400b02d081c0a00074040241d00500040c820a0f0412112503203821000b01280d01c0c52102000055 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 431516070 1250 431514820 431514829
    0x151b25080c120903010e0102030444030a0c080603031209010204080712120e0901180f02030a020406113004030204090605010305011503080313050f160e011e0e06 71
    0x501d955824400c452459100d0045034180350800030510740f0035460445039045501041c000c6920a550003050b07150305076030104500c03541e5001344100310052101400313450205010910300b81032110303240d408681ca0707242c24114141500d0b0722644202c20410800c090001644000003586c0b03070311522108a4065035100c014003802401640e115859030b202d0528006061740c41072080c03091083c007924628241e5201c0c030606a030326410341c61145803c4003c074070042007240e91040640c1000c030f409040c0402e400301060105410f0740c00640d40206aa60300080c20012107400441d60000e064454014060500c90300481c00601011030035400c81001804070802d071f138030b010a803c42e4041d5a0042c810800007416040c00300c000c14090000701c60702d618140600300d50054610041c0c084903480754050f45140d8660321740d600d90102610f411595849200721118000605000c448a203005c02900700103000d10749070b44004881c0d01a40140303074140b00d8484604098452891341d2059400050b400c852070385a060104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 431517320 1250 431516070 431516077
    0x10c0203031b1e090310021204030c0203010b151323010e15040803040e180a1104020702090c03040b01050d05030a030b010e0301091a0709140d0309030203151b2508 72
    0x89101425201d200e40d0741c1d00d40d10001c0c0000f044140c08494071b004070485050b04a1040980b04000701c18090001800a4812006124407520160000c2440d5026001140c903401c3c8940c1c2490303004d0302c0415582012000340d43c10000410202c0300b0709081e801c641a9042024a05c50140e03030403c003014030302c01c400380c684076480c031410108120303407541d02e65450a00d5030312900940245200c017803041c800300d910010741f40d0030080b00e0042403010308580410341d40c0d502171180e085440c5580040e0240024800760b66420300c8c89220f034103403644040d641e184c5440c00c0d4034014016004588120014036401c1c0100e68000107907001c08140341000500725064100694000408a25280e8151b091500c2030041080e80c0703080303030b050764041c450420182e04c2c0d8181c20b44060129004e4074081e0b07800e0a408980380d00d00083d500440302e00900382001920784a0700402d09000800c40c0c0c0240002804003404120b406c8008007902009110325585d04002c5807000425282540ca0707401360701d041e00400d58805000c129000ca = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 431518570 1250 431517320 431517337
    0xf041704030807030201062411160609090c02120403080c010605101106060909030a030506190e041106130e04110406090c1e080610120f020702040e010c0203031b 71
    0x540c940e541c92400c007040341c1c42039204800650900074001040e403d052251030000342c0d41036480462003c1f0081c111203c0c008400c1d0450140729000d13210482c0c01e0301d00d00020150240785c0e40d0f074031202d08240daa42c058480e141342007000c540c4400d4072010029075800c240c6090700e03800038502d45e840840003803150142089402c819800b040040c5551803240d0408540ea0404a401064411a0362010704001e01100211044030254008100d0314556a00c66400207a0000b00204036400d1031240200c03200d980c03a400d801c02c2103660120014002030220030090101d0408044071400c1c64401180d42400040d24544100000c18200c10301040401102117080349041c0c80107030041000340d54860340f14000d49040d80000d03020400c00000c00c041841c0e0210304400c400341c41d0702c55407001d4481d241807010f00704003032060f8003c010340c11041050001c514003401d40f0880c110705015031502400e00400044419154620510342e140150302c03e941600441030702e501c40c05400d581584000903034494030703440c401c8140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 431519820 1250 431518570 431518613
    0x30f030e03030717090c030334050601210804051002012009011b050a11010c060609051008010212160302040302090a14130302151008010c120b030111030f04 69
    0x4001c00705604c004420320041c40d6111000329900ca1a9031181c41c0c041074100d298154204004c0c60f0026241d030581c0b140300400007000c0061702112403040402c0440d44542c110b48a0308254010041c0100341e0201d1203444a030130070036004984065590950500c510301c03646e07004044070b0650811042c004c3d40310240c000d810010284608214224032901944081c10b0f0324041000300d00100803c6600550310000f141d48140140074600ba00d49071101c505000b055943e0410100f500300c48001010360107010000d003030b01c580128040c24024805508480381c0e4025081c681e20500c4500a8006040c0c413140c2c11103004900c0340800c032181d2404038064800e03600701075000214a800d000c80c408561348424110182c0349400d403e05d444103007102c502c826203004064016440300008000f410390b140e0900d074011440036144e884030b6550ba180765080d200e04141e41d10108164010321052004507004191541c04100c000f005400c00804207a401400f01418800150803200001000c01203205600c030700c00442002c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 431521070 1250 431519820 431519827
    0x12050d0e010e0607020102180f21010212150d0b150a0f0e0c07051b0105160605060909060106050a12090503122505040605031003120e03240103030f030e03 68
    0x50302036010300150900c10003036106101c00150715620601c00d07581104c01d03440c141a489443c003030402007410010340c005503200141c2c191109900406410a01180360024005621201c03901d010b1440040000d040e5003181407980603820003942d03200748500311254044e800032600d49403964420f07540b1110019541c1c100c1c10481002c256800d851a503402101e2042c1e901c220b2640e200800c4074250300902000a0082e030280d01201103441d001003605900c0b5034189451410903d095400c2c9000a04d002d509555460707651044c03010700d06203021810392001105008181a526103080284103100d120300030800c022183c5009602c03910301c1c3d0800d20b402900202104e072520310241d00414031810541e2840228140c2176a01d440607051020031100300c624a0f02c505090030315001c0251101d900080003900e1030054000003200141280154049805a80d941c04100e40c14007414145010b68511044e404030040064281380d01500c03e501c0780c19a5803610b006042803111346010b8002c2d000c1d038031310390465006c0417 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 431522320 1250 431521070 431521091
    0x1413090203060c0c070504060506090d030c081606140f13031103130807270b12070b0a02101503020d020a0b0409050a060e100306020f0904060806040212150412050d 72
    0x10005044e070641c80000380c0b082d55507100108001c980d41e40c07080d180c010405001000c0360b8138200340001c3da12030107820041a41c0c40c942d40ca6542e145e22007a001003504100c2141f400130300c8100d100741d60000001c52071816190409240c030480e40c200080482c0305942c203803403a03e010507105811407060079040c1c40449031520481d84a02805041d60b0103048072910843c1000190300c01010301c0d80203020714030850103030029058442c910250041c81082074000c00d10b01106c0c030301b04604010074402000310703035616521a000300c00c0083c1000201d0441100640c01c003030644800b0695540420202d03503046840f5241d941d032070f10101f0807150a95201c4003231043c000c280061081200c0e000704d032140c0d612900801c1556160702d0a0308080c441030341ccc5c500000d0b0b41400180001192a03008040011140c2503030790600c812100098280c070300300c2c0c00442960b0003078400d00045080c00c00c035034a01d00d000310000c1d01c01c0759252100440b0800d4010000340260041006200c0d00720700031003c852152035104030900c07010841 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 431523570 1250 431522320 431522341
    0xc0106120b1602150c0a03330909020f0409020d0c080a02030d0305040308060d150608150c030105030d030b010302090d0b060909030405060703030b190e1b0301141309020306 76
    0x403101860422012048280c00b14800300300958038500c030310401125030712541042841c98120703801d11014159200710040c03412061280d40302005441d20340b107844400769200c0b01c40680d4041da009081084c100340207440180d0b00d07214454800141a1400104002140001381d8800c0c04c081020b0401c0f407228102180d032020101d045001940245e085402e0020580400c4048907005c96000c2c00045000e40443c88520340403921550140c040c4201d80f0150040e82c40c203e0880e005d5030f210602c10741c082d003c0c100c000c102c92545907500142c5030303540500b1580340c00082602d50108074002010541c0e5051807107002c2e8082e40c107170ac04e84c007400b0301071304140203084c940300c807102501361901ca10030300300c200000b2100b0340300104407426103001509144c101061590154068440b101c04682d2040f0b54030891556558040024002005d114080200c9410080e1042104887e80325007010310342e03c2000140320302256855a88403110081d00d401c62030061107034401c0018042e0b1440254580030340010700c03000511 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 431524820 1250 431523570 431523593
    0x4080d110a03050f041110140c030c060108010c0e01050307051e0901120b010918020d050a090c060e010801140d0b09010b10080402091b0c0706231c020c010612 70
    0x3040d4034204041d03101e00580c0c0d041c2d410100c400811b000e280415420141c00c04449095180105042201c281c1d03400c0d004240154010300000070840e480403684448440d010030403680102050070007013044030840c59009203043c001d480e4080c10f0050010104420703c0c45442100c00c0400b9032111416074014500703072462694040044280010001501d41d01d00c2d00d014030034905540c1050b15825510303407030130002041c05d072054940710030300c82d909020030250103c1501886100d0040c909000078807000c40c2c500550f40c58043d4101134100042c1c202c903003490b40d800030610f60568403420302149070f2042d280b001a0b8603c001c458028030b94a81c21050000e041c4c01500b20202501080b10040c84e605003204080342d8010701218085d42c80000080400c1e14440a80c051244010f4041c00491400d0040660341d840d080315580501c00141e07840d00552510008007485162040000c0c04040c40d151380c10409481c1d460604810103095507000036040f14007042540920010a85034164074180300107428006901c04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 431526070 1250 431524820 431524837
    0x30c3a09060b120a030e01020a0506100617100b0904020f0d060611010b1f0306030f0b0103032607140412030c0b0c070f080c010b0a0b0d24030b04080d11 67
    0x207040c988a640c01e0b240c1150038040243c50000140112440e03620102da02582e00c0b48520306600400c000f11004c210140b24030ba119500185c0b0890506142520003414400e040110b0042c410b084824080607500130322a0708201c9800c406119128a03540c40080c009104010800031a01000286c0030300d40c1d80c15402200480318181c641142d500030401c2c0e00c90030b03684102c10840e8450040b1900d45c0e041c26265201000521661500255680d02c0350303a5000b000d481c20034159500000e82004104145d400b2083e07100842c0d00d181502014501d615019100360000b510005c24400d0082c000900d032440d00c0240c80050000c40c90042d180f5030b4034100078020380103881d01075a40d048030400040c0d4400995080b10103060740004141c1009100ea107450a440d00007400c1d0380059500c034504844103170766031901c0c4000342009452865407100703000e030f84604541401094610724890f07010484240b2003456601c0c0d04994001d80100354940c0c0720700d007941c0701b07125151100240c00d1410140c44c8038444107001400411 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 431527320 1250 431526070 431526083
    0x2130f0b0a0906080307060f020403060507081b040e0f040615090b0406050a030c0506030a0b13050603150412031d07030c0e090a15020a02030903062406030c3a09 71
    0x98440d007000b82615014060b00c0180d5000701301900001e9500c0c3d11811001842d403000600b000c0d1a960b0740b900759081038603682c00003942e00c003d0150f41098a00480c8108100308416481d0610701291091801401090509c0500c068800203091103070710703080083e0410303009241d2035585489008080080c0100240c8500403450030710007290701c3c20050360000550b40c005c6004510149003801300211640014042c540c02900d03441c00d0300311901d074650070700da240352604c0c00402d40b40351a005042c07400010b40c2c5911018000c00c07080c800880e004c620024085d003030034503004c0b501000168076070521040c141100d04c82442030341000800c0c005101c6690003a1543c0d08030751070058442050032070fa29102c5841c080e00403940040030099096559000f440741e01d1080c01500e003001d003444002030500800f100d40000ca401c1d440c101704510403030704060350f1040800311030440c19401c1c180c40c030131041c0c021842e41000604203c002c0384154043c07541629150188549565102e010790741c452005020b003068111800b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 431528570 1250 431527320 431527339
    0x15090310090605180a1e08070b07020a0311010902010801060f0309350c0303070e1318050d05120a05060f060a05040603050a090201050715060b04080615010212120402130f0b 76
    0x4d030b00002ca884415103420401d1901d001c24498900b10348080e05280860761040c1c01c0190300300140328080602c0c840d003980c0d00540018010340c200544100030800d08000b00b80d26001040d80143c0e00030f04010706440d00d0745000458061030340800e80091020300400340c200e075080d6161032221001000d03000f00c0c1298401c94030070103001c5209140814002c3d5441755a19410500c001000356210302c4e089810004000d241c0c9010412076215903085800c50300d42405034050aa6400003444410800320b02c522001c1e242c601e182c000c0d5914000c100841c0545803500141e19400403c0580c0e503089402c480e0040001c1c821a82c079140c000380a003013940039101e030308003290400300003c3c017016180c41a6000103130182c403080d14051071540c0d142c004000c9000c2d080b45d2580c0d42e410100c2d9500540001e000a820fa8400070640c9003402c011114841c4c4140d1080d90465020030040700c8416040c20540740500380000484001d81c403203200144c485058964104c1a1078602694000a820540c2004140780b10540e00c00c0364 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 431529820 1250 431528570 431528611
    0x1e060b0711040917070303060b0c160806150f03070b120f070206040c060309140303070e0405100f031407120c03030305070c0c060e1909052415090310090605 69
    0x15908203150181610034400300344040c0380c60200017800c00503c03034500000e040d620340c0719039101c5400000310442c0301d50042518815864120034448058801d050017801c02d4a40f000c0b070890168134550340e80c0e002d400c2c8030455080c240c804210300c90107000c0c0502103e41b04c0034000000c1251220484440440ca1811030200c0d00c040d002241c000e024a8010340d00000442c213101c01030b4040e08203140b00311351070343c5020040a0703407103814005103010340c00e617a503210360700c20304002000103036413000d8844d00c010410031301d003080804c1890503480200e0b40c0c0543d110169000c000d010f18102541d540c0580050403030503291034102710025004009881c800e807801c000f03545031001c04880300050390000801d6485001000e1101764050480c039500ca000041c00410450495104a41244c18591141c100d1f541c45209200c41d58010a0750843c014003400c0c4021041400000003444030101011398004503a000520001991024090440c98541009046c4451715107440c0960082100703d4005c40c1800c0700c3d000c10034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 431531070 1250 431529820 431529829
    0x3050304021801060206060d020d240c031e0e03040f03060f11160b0603190605040308070c03120203060a0314060a0c020c3006040510110a121e060b0711 67
    0x2c3c10790b0160341c010103450f580c40741409105085c0b42016a4800b0114640700006003040f40780c43d544a110400141c1550721188002090311042d160000615080056040501c881c036400d012000031004d00108144900100f4941140710715041440300e06804032001c000e203c51600481e200014410041004a100c0d4520188034003c40d000b0701c400d2800305811902243c0441400740d00a00c0080c1920200309004007401c4880b408850119185600c620420040c150454492980600903041c0107081c0091560018800d4100e07420b6a9030f010380c04030202d402c41e111031001c075020f541d00400b0300850b00f40ea201141c1e52908200e6007000020b0606082540b03841c404685080802d402801400c141c406207001e04168002d010482c000072500088141c100e42010041103020314001c0740508a028261000714054070019024248210b208024010440b90300c0713050000c03105d00d001000901c921118040a0300c0f00600b412a041c4203042840100d945040b880003008010301c600c412001d207190502c10700 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 431532320 1250 431531070 431531119
    0x7030915050c070504020319110c03070f0507050109030203060c0c0309102003040b1b0111120106080702120403080307020703020310060e06090f040b0a1407030b1003110901110115030305030402 85
    0x1089005248e00ea1030180c08005d40103000d405860103440c50404092105092550300001000d40303400b540000303501d00b0300005201728005000c003860101c500a056401003a07644001420b6880014070010310641c0031542070040e0394403404024010004088515001040c1600002d268101103000b031707506c3c0034006000002c40d000c5a0701b09902500340000b01c503c40d4117a0000600d0200c0d19501d600301c0e41c980310102d0300280010184942540c40c6941006801048008000c0c4900203562082c622200d40055040545044a500000c0c903590f81d59480301c22820150b655100a41510803031822040c0d94a0503006842900c1c1a0040d0300895034070350003040010407080d21071821310182c500204000c076074541c1b81d0310740c0044c04000124079840e441c4052200c40a0450340e1000003035a5106d000094501194400c001608034681808240d00000b02c01c651f43c440c0b039070760a040c0894400305c413554410070341040d01c003d21080c1001c00c0d0140e903070401078019030044400324815202d00003850b1210b041c82c40300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 431533570 1250 431532320 431532331
    0x109110907090608060d050c060f04030b0a09051e0a02180a0f0603120e01050f0712030b0102030702130515120c120d0807080a06030b09070801050a02091507030915050c0705040203 79
    0x500303040b03072a10030034041c0e8520030b220f0039101801852074900c1c850701c492000784404035289920ad96642e1540c101800c48500c00743c4006516401d00850300d011940c0041d089c40d44044280c441e1324000c6620a12500d40740d4090b0000350480c542c2d003800c22085800c0c1c81070714800c10502205000d000c94003a16913040381c000b400014010041e6070143c0b0141c52150000046050043c1833080c548811000e000c0078940100404175140501a068500c00c0b5a0500031104040400e000a40c101461680041c503001c003a0000501e506650f0030029100189020f100d40d014540a4191003c00ca52050340ba600c550541d400c4502503810501c3c54110701000050034041205070340d4079080c90ba12000021070b13a0260251002c10905e889800200100e00c04000c00ca010b00e422600400d01540b51103582802d46100601c2c0098003441400122410f48840844841005140c005c060395103070705107000d48a1802d2500600c01d68005001d207010825040401031004929000c00c0743e1907141e03200e0402081e880308454 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 431534820 1250 431533570 431533577
    0x270b0102121e040806010312120b060702040906110a05120105010c0f0b070306030c0b130e220212062404050c090603270313080703020a05090907050301091109070906 73
    0x120710028094018020040981c2c1691035140555409480380b500c1d03020780059815003014034404c2e001a0300718030280c4010103c20740034480075400c440001c0c0386010f50750002c1e0140d51a0b102e203004020080e848124100030780c10400c0d45802d08484004d0049d003048140c03604c00e83c075180000c14258000d07a09107080340d0b4001003101c0901519550142c0c0d14102810b50b02c1490b0b200c00d0040000b039401d800820240560005240d100c00e0074948441c020b4034035a00c600c080c15241070034001c691210b5028201743d107581200162409a16101180c0d00d611251380700480d41c000c00c0c052203050b401e045c0703070482c40c101c2060b21900003140980c2040301321007083c0c03081c4e08104010854010142080006940d0122a1644015070810306203034459500ca0300a041c14210b8100041c0d0100850342e1022203800f8100d00801418a9401c50380401c1040d0040d0160502c100c2903900080d0a196042120201814001c0c1c000d01481d40b06291501005418200d5640b045000500080323409200d091090203c030840d98 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 431536070 1250 431534820 431534827
    0xc1d0a020708031801060f060c11090702100c021e010221090606040e030c060103030809010e0a1a10230103231605120112050c0910050118270b010212 66
    0x40c0c5944542844c1c5400c00042d500c61030002045200e118041c0c0003841203072540b607404680c07031404c2914a100c1460592084614a0034810516400100702210311100783c000a103001000405901e4035200300c0340030780f504030307119039400c940001900604071200010946a02100c044011079402940460342c4190b1940824000760407881c041c1c005049a0403040152458400052003003414600240c2041e4046500f24042c0080301e81c0c00d20030300c0c074800740f18006024094a559524100182102040c81200c101c0e200481c54602071682600c0092004422400090441c100c000121a08815040380400c4c946961703001c02610035040110565840300301001150745040f00d2000d499142c086603002c010781884081401444820200e003c4c0c012840303041080d0740c2074030f4803620703118101c0d04050103a0342c08400e02008188200036402a90000d00344071a0314a01ca8561b0601f0380c05540c0040405031001e4030781c101c0810405122032903403403603040501c042001d200041e40d440a402515100700c62082 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 431537320 1250 431536070 431536081
    0x60a1205040c030602071a090c0105030c09030f1f05010501030e030304060f020c072405041d060d02060f0306152106131d250308070f0c1d0a02070803 66
    0x103a00807a8424801c0c80402489600e9868040c03c0b030308207040071501804c0301c07405441c81491140140358001444001840d002c400e02c0c0c0000c0407404050003c40c81d0450104104d00641e405105449402001c0000c40b48840c034045100c03d04070020f103180309a90703490301001194a51081c080d140d00a2540d0f0001c5142d0b80759544c0d00b8008004414200264a03424030000141100c2804007600404541040000130840c15211002d44401e24412006000c4104410403842c481744601d0010b123a46010b080720580d85000101d08900070044009600840c00180850304102c010301a500803001030b582046141061801884548100e90b0207012201c201d5107070032551005802241c0c1d01407809170150b000e58000c1028441a02c9090040207248036404a280c4801c80e0300f08444511350b95500d035000c1043d00c90a461425080702400040c3c02c03000f000074007006000c1c0740e185241600b5442215200310139036030001c560042201c503280300c0e01c3e10141c101107014002e09000340c0303105980003101285544c031103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 431538570 1250 431537320 431537357
    0x2070206070f0c050a150806030c03150705070b0a0204060e040b030601180605030102070c05030d05090904020d2604050103140103020612130f0501021c0c0c0b070e04050c0a0e060a 79
    0x41c0e0b8103e07103480300c01c40041000d07294400014000d06500140c1c040c80c1d14880d601404208000705a240290700c084621403d950b40000c03030403000002c03a0a00c02242d1102c1c0001c07210b500c110440501012419010300c40782000d198018401c031003496850040c142d07140d60410050700d081e0000c1340d9040d07006400501c0f500c460000310031852100d04400042c2c4665480101c0c1c2643c0048100b0fa071540400c90041042d410301b80070f101c840000381d250042c541382e01c48000652105000d00040e000340501e02450f001c015412910034030001541d9403c0e20751640d01801180142d1040c041c050020741440c0d0211042000d51601038103803076001f00180e0408820702096030b03101d2401401c85d049a20440c4081d80800c4802c00c18031304c4180a180050707521400c03061008a441501c0b031591b011280391444c0141d140741c0c000c0301d52107c03d41c4801c02c06407035103400100b102c0b083e090b01c1402e81e000d80b5000501030000c0091004001448850300d510103030580e20800c200d40c0d80200b81002d0b01080e186009204035891 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 431539820 1250 431538570 431538593
    0x109090b0301180b101d0c0f090d061b031104091104150206071803030c0303051f0f08060c0406091701020720090c270d0b04030206010311040207020607 67
    0xa000c1c00004070640359000b11a03240341030f40e00c1652141101d009008542e582142810040c00d4888000c00c49400781c4804c0740c0050000038410580040c1c041441041e03c05044204c81101c0d40c0104220899541804c1c400c00402102c0380488001130484940803400d4046d009610b005122000441d0401d0314101144000c7c00300350121520f01042048003160a800410301c80307411411583c010801c9113802c0741d016010844400301d403900020f00d5481080000d07884901d9941155041c43c010401d0340362842d104800b03264161031185580301c0315102044ac00303030a20540b4100c0326010308440540d200c0c00b110400c1441507001351000120300c1c0134103020000c0c245011010403000140010701c1d141031a00c922010240000229084c00c4100c0c0780c1d0041441c6c10104560000030b51020340c2d00e82140549116041108403000550104c25941031221659030b07450304100d100e800010790742c0d55103803a19009403100800d0004844003400589142e480d410a03100340c4d002c00b41d0141c8141d18194064940001405 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 431541070 1250 431539820 431539841
    0x4050f060415081515220503031903051003050d18030b01140111011e11090925030c08270f07060f0c151d0319030e030306010909 57
    0x404000000710042e80e071428001a401950f10b6401508010940403410710803151803c0c03040000f0f103900d0301d01121070012a1524101d01500d000d02078810f0b0180d0318040401d60105506003c0854076a030303140c0f0745000368854503010740c0e420003040d0b44049000440c00441d0001508a030f2100200544141c0a800a01160240440c07030301c00040e900e948800300000709801000ca41c60240381d4421555030410b5080d00e41070311000007070000072941c01c0380b601c0019001c04010340c1d040e280c2d5100d01c804114901200c0c880346002d00341740341c10304c0d0002c14800d0070540c1c0b02d800c400b600455100b69264612911a503c55200b007503607204407503101d256110555110b004036154048110501700ca003192003c012840c0410b8021010780052890060060024200302690809016100c601000003910140c43d4080305502e180d00024016001003a00c41103034401849140188000501220340001c0401200782d05031031aa01407105109145007036480340000c3c0c520324082190b0704400e000c01c0c841900405c5000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 431542320 1250 431541070 431541079
    0x605090c03010302041d0604030c030f020f06070323040c0f0b0f030a05061f090326030105120f0a08120c070302100902190303050d051305071719060c120b030304050f 73
    0x10007000081e91f04001050b1412408181180d0b40801015040a05071038100c503140003030710441031090442034580c100103041c441019a80e410648840680c601d80b0b0130790b17403901800841185050326088550380094003a1068860715458000341e51a0b201013100c100c41034450410b419901c45000d00301c080e000213000ca40d8030550043c07a5041d01c00141d18540c000c081a60b031140000b501d103040c007400491404003004400d50380c0400e11080002d120b81241d04441068a1012000c0010798450342130a4150781c0e564031900480094000380400c106c0942700403e0b4041c0c40303002c0c40c2c03200c2511300d101d44108a401000758225401540500340280c2c0000c000c1c600241c81802c1c0d0003000d090040c0500c0190b04100c01290010500740da1307580b503500c100c0350b102c2e061004c16042d03801140c84d02562600c040c49603203600c9101d05000071428400f4010380c41104400c0500008000a2349061000381981210f100c00080c401d09440d01021110700541d221214040d001c1c516181c00c00d02849501000e0b4209035801 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 431543570 1250 431542320 431542361
    0xf0a080714030702100e010615140f1605010b09041a060a0e010b0a020c10051b120d0b0f0a060909020d020f0c0601050933010c1b090605090c0301030204 67
    0x30780000000307511841440d800f401d040a007a110503001c541100c0f0000101d0303031400e0010b01203041004444a041c407180c0c01c0a40b47d002c40c40349400518400c003aa441008400410f024034100c2c040b00b00009168031401c000c1c0891188030044c00340c001412500a40700040c10030800b21401101c850f00c1c0c3d0805000303000c681407a51114940e01c941d40302a44903820003600080c104d610f4550502c82c51881e00d8003120040480e080d041c000400034040d000c0c0e1403091004c049103110b406541006801c8001c0114100f239a151070072816003500800b100c1a29500808106480c07056514045000700c1c2910056105c5401c541d080035a95802500145502032115a00300000d00045072a000030344400b90f2040c00400311307581000d06014840101400400c2c0403030b00c1110751000400c07050f04c4941e50304070b51500c030782c100b400010040303412403030300c20300502200010840c0c1c56904594020510507511062000d12110b40e550003404104030f012110b0141801e4140300510041c6802e80007284031a680d9883c203941c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 431544820 1250 431543570 431543597
    0x105091e0702060a06092912070b040f171c09081f15060507030507171204030f02030405011b020d0c1203090909021011030f120604050105060f0a0807 66
    0x2450099400c0005a40180d08002c60412540071701806005000f50520501c00c14880520302d002d01400701e83c08089011076903546c503442d403034490b464804405086440490f6250305c125184e130300070701600c04481100d039404102c10600c19503543c40400030328020b04c22505054680c60701c030355a00e92040100050a1400a9518801c01402e1102400c0c9101480b03c030f00c150350090110780c80303010440d10300007c2200400845801006503900c080d010708000b60b90b2604c918040e00b442c140d089486111000202300800700081c981c2c029031055101e615442d04c00403101009994038003981c4569400101516041d21700072090152007080c041c4003500352070075400c0c2d40e80e03441d1790000d05810a088040101001c80285540080c00100800d0302c01801c00007400e0640204403000c00c44100747c018085000601160310000f041154155002010883d440d24154103115641c02c500744c4009100e2410040003080500d0501c0032100c00381d40f1191824948400040c040d51403280040c40304051001c43c28003001d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 431546070 1250 431544820 431544871
    0x40f0c08010e06010927030315091b0e0f061615060b19050a120203090f03130e340e031b130b03071211040e07050111010212010509 58
    0x1c0c00c0c0e602d180040c060943c141001802160307400c1e00c0641d05680d0703064044034044101c00143e28265010320b030110307072041030205d418a00d200343d521444065203008861018500c50b242c0b9000c003104503a0358107001c61044410042c6100103604110340c085001c0000c600e10100c00320540000034480d150000411044144010485245510022116000180d10283e5108400c0c8007444510380741015410002c0e0120018411440068240009a400000300c1d106000805c901e5510200010483e80e55100201d5608111441442014038030501c22001c1072040840307614001d140034600446502e000f4071240c0c20001180406d035100c0500041c400c000700d0fa40c40910603000c200c41c14503503e003014442403042c007041c52251005a04d60346d2a0030340000b0700da41d000c501501140c205040c100500801810000c081d01d12013003800b98090700d010000001d03500b000c91684100c6000740ca60340045203482603030600b41e1061003040140c0000e00c1c001032180d40b500285a60700b051464039034a250042000044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 431547320 1250 431546070 431546081
    0x3060c0703121b030e010f2901050f0a0e15041d090a030903150b04020706060501020d0206040f061505270c0702011706060c100902040f060509040f0c0801 68
    0x84150200068504241500001180004100c41c10104010001c0d0620780705075140c800126010107445100890f0b040c5000d4000741c0400d202120100240031f1003610b81440380180c42014400e0342070040345402c1940c000c01c00c1d201c0b100d00b041d21580c94240a49030032600003000701c4ca80703070340a07c0780103459401c9a070fa003001c1c201404542c210741080071103c003400506514000c0040501e075100e5040c18000036805417a00045a41c44203003075814401642092000c0c4c80e40441d920f030030074404070301c81d81071000c190030010407141c0a8094441440b100d0504036152002150b0103801081000f40c0d5500145043d031100d1504600c0c0b80c1c600104135111400100480001d00183c1807610900c038090302d02e4807102c0318044c0c11076546101145072040590001c0c0034901d096010301c0b11005014005007d9480e00c1084483d26103000043d00c4000400100c103000030821294144d001d03500d0104121041000d138442c0780180d42c80209546540e0380c132541c960510740300703460040790340c0c44010a00166080c000d0158 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 431548570 1250 431547320 431547331
    0xd0905030c0609010e070f0b22080a030e0901060f080f04060f11030405120405030d05130503031b071208090d110316031a0f0106050a090b030f041a09070501030c0c020306 75
    0x800c81486030101c41b86021a00c4e04031a00b24070f8044001c110080040c01110148595005015021040c84211404080e038942c4450780d00d005000d65070040685c45040c11141da2400c803411354190746c03034417402c480d110100350200b0041207120000c90107141281e404c1c158068402d010201e520b651542c076240030340b0100707110b446100c400070081c80104641403010302c5840d904450524205840c0c000000d503506003080795081404800200020a080e115050802401c0e015040700e90f10f420343d0b051111039030940424000c0500a03034802050b14160400f104001d250450044d9090148210810640950140003220920305a0811074100e45040c0030ba080e040340726847c400089403071030078050380c007200c004464201003208904026810301054030860565420380b8156803112041403065840e104c0300d07080781756011408001c0180800d500d00c69284118441ca403c00c59101d81c0140382c056000060710342e0645d0b508415000d000b83e501ca50f10101c054800f80ca80030400320b0068022034102041940c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 431549820 1250 431548570 431548573
    0x1828060c050319051b0a110d0215071112032a04140f09010911040e01091e0207020a090f0f050108060402010f02160b0f19030e0d0c02060d0905030c0609 67
    0x401103580c0c000700200000c3c44400901303121500e400c54000e1080014400c611800d818040f03142d65045220f01d1603240e0000092045649056940801a68400d0364003260716400c142c00b40003602c414464140c0e0b20000742d40100070003600e10300480a0310282c0005220044200c0d828149103144c0d0402ea11a101d100340607858190f40320308154245000b21040300a0ba8000e680070584445c0303503242e0090040c1114070144001a9110306e40c0703c80c840d28880d03907100e203407008601000403030b40403130f181d010700000f00c5110a010800411251210180d0180b400d010b0340c0b00702c00c100d00304115009904210702c21103030f0300c034000b416a0341003049104440d000e070008030080d40888100700455030002c5a44000080a0008003095a040568401680c01c40d02900c2c450002c0401d98a40e212607010a4840d01c4005240a401c0e610b03c0c42c00003030042200640c060013a22170070211030f1145000e036004400c07044d009081d82e0310f0300f44862010340140c0014070302294148420015102115000e12215015401090 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 431551070 1250 431549820 431549827
    0x81b15310609030305030103110d020306040302030c160b071506080102070302010b0312040b0f0d1b0c03090611100506030c04090308010f050901060c0f021f05040504051828060c05 79
    0x36204440559041941440101c0200b4004070703401905481c1125409114031100648030804074841c0410304030000c0d0144101c50506c01016008005803680d0b0000c10202d0300f419140b504d040d03154582c90b00c00e084081008000c2440440c140e42c101c030f20f85141103440481e949642b1080982240d100c200241e0050359124804c003c503241c00c0c13040032070010301100100c0c142414404041610701ca01c4040c0d45103114002890b251200c0543c1003040c02103100010f20303c8a0100b0880a46560081c24044000550f15003003c262980101c0d000b41911034181c0040c180c00050040d504001c1c81c020306500d86c1442044030007407242e0358501072209580e10940d68101554544280003902e00d0480d00400d01ca031301c0c41401400780c1503000c0e03400c3c2c00c001d40100d880d0078080201c0c00030503800c0401405070400c402c01c0d1449200c11640040c000d01c11200e00307903400c1080381e49138003b12008855a800c00b42c001d4000c0303081c4900e607c8405200d94000d99000305880344404065031000304a03907140907481c0101c2d0b000b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 431552320 1250 431551070 431551147
    0xb150a15030e120307140c0c0d060b1c03090501200601090b01140702010c0b19090602090f0303120f04231b0103020705150a09021203070c081b15 64
    0x340101c1811444101c500f90540c10201780c0075141d2803060b4071482000a003c9500d00b10032904000c0305045d010064540d80340f801d00350405002030b041e80301c80741e805803840100411340c4441001504800c15003541d02d80e001e090500004450084522a10703440565800101e200e0030340f0b007804010300a00b5500ca0000318441150000f4101c600401c69000444005001382030250741c0090403850200d900403040011036840250842130b0001110269055070720302a550010005180c0c000c240d45102240e0900070200d070401015035a00c40d0f015004176040742c020215800c08140d2803819041803090480c01d440030701c4809140018038220481c1c110030351003564415190180d841100701403400a02c0d0030b500c0d00b20562129540e400031481550400c1850a00182d14001eaa40c0070600383c5038000d1030b00b035400244501440d9241c00c1280c0c10ba840c174604020001c0c061900140d84549000c1c1040c40140400b100b034100a02d901d0344403808043c4082c00c000e2103036858560541042d0300000c1203030140010505 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 431553570 1250 431552320 431552323
    0xe0c03160807060908070e181905010b04060b271002061e041e0203030409090302070512030a02060109050c120103030809071a1b030f040308031807030b150a15030e 72
    0x1150b210b5428450030ba5014000c114020401d441550740a0240403c551581541c0b024031000124003064a40500c803030200449d181e4510014000d809a8003d004022800c0100800c40b90603201d01400e01c01c0811003440c407c6440c503401d07248041c5954001c09200d04e2140410031076003a0004140050700f088007000b010701c142d04c4032284522a085480c8001e4506a502d01303210072120180c1100180e241c003000011560100207c401801507140305002140d02d518019541c0c41c3d00c0e000e014818181002d20440c42c0030000141c41d0b810066500800c00c03a4070f01a0315100600003d42003409110b01000040340c4041c183c0c1015000350700c00e0f5940780702031501061103414104141c001e0801759403c1504011944802026161003025034050a4621b00300c0300d20892943c820640380c015240c60101700001401200d0029521400300000014491061100ca0036155251808001c10804041c80400c030095450b04030502c80201c050705500c0c050b42c5803110240304001072420000000d440300000401d0100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 431554820 1250 431553570 431553583
    0x708070b0a0c20070302040c0f0305060d0309052403040c062007050f060d15031202010203070f080402030118050609070e060609220c05040314060601120e0c031608 72
    0x140c0480070000d001e0080b0300100211600544216082c2c41c004810121001c103000103c01942e00500401c030032114001c01802e00740ea90000c1c4004246464006403150078a02c480d000d0780703a810756411500d18140010011561804c1d2841c010080d0b0784103064141140c40c0e802580241e0003408120706451420030000d02041c0010300105100c409441ca442c4480340005180058543c22152005c040e204031021030340e180500002828400e003001055015a64949424802d503030060741c1f440c00405050605070700381e2009441580c0040d08a060114441e03220344044e5401610003400414281404c14520510503221002940c1d01c1d005101403003504107082082ca00100300c1141904028074100f400036032207001c1c4e00141400380710104610030150440e42034014403201347d0401080101000b4400801b9a0860f0108455050070f480680c40d80740c1300000c02602c10070301652801900c450721a030328400347c9081c910300c0b2400e00c21801008c641c0d40e0184071190001843d4428900b1080c500300d4a00d20b00003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 431556070 1250 431554820 431554831
    0x314010501110c1e03010f0603021504060e01121107060b0a09060807030b090a050d05030a060b032413020d0222030b181e0607120509150408040b0708070b 68
    0x2910000e40050b401d000715031812071040c21035062540403002c200b0100d05603042841d69600d541380c411054503159040c2e1020f800d607070007070352044404021848a05c0e5184031f940201c0f00851460144e188031584180c0c00e840505038511004a41c00060303609a00c1a07400407031048805945440340c028035410840c0c10340000700601d81301840140c0c81d0410440d00c4600c03034040502030381c0c034280008d01100810071441c800158003a04950b454281000014510341081d200061102d040490008404203d41c003582c0c061000d60086c4560104000803200900c2804901d1542010200f010703010000f11900c00380082d203024010140c1e58052448080c103480041f10440131202c4140d20050012665000c0703466440303034041d1203100d80a81444038443c80c0c442d030401c910140e805000880000c0a50201e04103008100702c2d00c4032584c0031015140801500c004995904050344101030350700f484490800e41c07940060041e60a64074184c0c4411084183c0c2d030014000340e45820000a4090800c4480c030380556104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 431557320 1250 431556070 431556077
    0xe0916090c0216050604060c0804080d020a05010b0a0609050d0201030e25080d080c130f2402010501060f05070311100c1b02093112030b0a12031119030314010501 71
    0x4904100010b0b03c24000c0d4040d01c008c0100703440422041207104801c50f0081c20489007140e49818a00707000960340c0b143d01004858a50034620321035518100f013074000d0150f0399076869002c00c180c00e06c0300f80504034045c1541039040544501051203511401d00c045d450408071070310b003000200382209104882500ca64801c0c2c0b0715a103e11900907401ea0310a8000360407aa003144444da42e0000e0003281052303182d06402002e1040e106050005008941006805040a44c1072141c00180030700102a4200d82e400d116000100d09500202104544a040242400c07807181c2480422a240c4aa0043c1f5203460051421480c982c1d810902502c0b0780c110000d0302c144c0c09030388652a9403940380d0380420303c86940a013425880c601c1c54a0003070400303000e07541c40440202c400520003664099a080c641c0c1081420f40c80e03000030034a00301c58242141050034681c01500c10500480c1072556450745c0071200790750460680e201c01d010302c140e0500c454225a1201c038010780030f541c0c0410809403806001108e504103a0156050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 431558570 1250 431557320 431557363
    0x20a1418090c0103020705150c03040b011e0501030b03030c07080703050115080a03031a090403080604062907020102120a020a0605101d0a0b13050a0b03160e0916090c02 74
    0x107003500000c84a800e44402c0c039000d41c4602c11441c00510b80605d00285040d042c1c1444208500740b040400a10311130341c040c508100301a666030098001d0649032260070300081c0c03003008040c0b06035406a001900c07030043c040d080700e180c40201c0c101d4a003807007403d800030005604129001c0081c0b0400340562040c43c0d10012202002d2498406103560720410818024189612400003415140014180580d8060064900602c500e803910b401803100c50100c0d02c09110310303e4080701007242c80060803e03200b8220089030410310704e400103003246c1c0b994103c560120304510a070201c9041281e140d8000c0d021a8000303400031f102d114103902c0c200003990340040040030240e034400400c109591105c105031101c0e501245420a59840305003501d03015040a094841e00b00c980120109040c0a150344172520642101c4801c100640d5074004040d02c85685407956020032180789000d00c40b50300d817004401c2d00041083d080b43c0c81406101d50300c00100480e40c0c04440016903a100300110240c060156810744070414500481 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 431559820 1250 431558570 431558581
    0x3050c03010c1e120c0206041a06010504090e07080307030c0b06011e050a0908030301060905010305010f0e04142407030507140301141201090804180902060d020a0c020a1418 76
    0x41c0181140c00f182d1605802082c0580480c0500940400c04040b41c006001c001c60181000e5074944d0169412a030641032681c0c030503038180070300f1801801004142d660b940342c5440c00a403030003e010010241c2005029030400020001c504100410040740721386c580510603c1d06051210480400a24030741c14407214074440801c2d03640942c00680000b4042c1412511350100400171500c00b60720340c000c20b000384800000410010740207400f440454400340d80c20700c03003a03890380400d0454941e01e01c036505046a40c84042400203803c90010ba05045010f811103015152030784402c5901202d01c8482e600e1010042e040c45211580742c024a42c3c444d02c1410142d8017000c40c0d080110052005126114000001da0f9181c0c1d03050380d69207510750783c025080c0020b12540f02603051500e81075206204102d1028514104c51942d160716005400c18a80c0003495a8180606910705030040c0d84510324600400c09001d000800603034032200c81c10050303d2051420f00d208010701040c05000c0400b2908504090144d000704071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 431561070 1250 431559820 431559827
    0x80a020f0901050a03020c010606090512120d02091c08091e09160c0c030605010f080a110d0c03060911030f12180d050a24020f1e09060a020703050c03010c 68
    0x24001142031800f90741d1035048442c1100240922404c0f0000d6500344500000d10076032110142082c6c54003182c449810018009a45a0340d004c14041d091000006011150070003840d6800307055a00300c05008000b042d00008801020034540300b60884030729202080010141c240203500c5a0f440707105005440d0001c1c240320015400d600028180c0b11040c81c2004403111082c0b00c0c0f0300c0d1242469020042e4000c840d02c0385050405040300f4062135a8090000400007000100011125039468104010008a604210500100035900c3d1401d85104041c3ca00000000744144500b80109024040e1851030070f0032401010b0501500e40340034041d60303102d00307507032120000c49600300e48490b00c3c01e640404a101100c000709048904070b2001819900640c1c11940c203000142c491800401018a9403841140c0f607a40c00104038003550036074020000c2c5c18010720440a001a550300d140e02130150410f402c02a50800140d26640301c0d160080040e00411810000c01c40100a035244d9100200c0080c8462482040020b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 431562320 1250 431561070 431561077
    0xb0a090609151704080f040b1804060b0703050c07170a0b100f050f042705010b1507111f0e04050c0304050606061e03040309030302100525140a0206010501080a020f 72
    0x2220441c403000440d0400080400710b40c206c030600490b4130f40342d40d03803034100c08060341140d81400180100713058104110b240520864040d55106614282040c03141d84045800d90405240d24686105122012075004207511903034080c0d01200006201d1144185402030800202400a240c9034036a00c070306100a0543c0da00000584905441c81440c4049000004014069400d9a1601d8203c400d03c1340000c030350310b0789981c10980e014500a22600d54418107012103202c1c0ca5401e03175241e90092110ba00006d0121042d40801c21005016801812580e007442d021824560300c99008141607050302d00f0f5508003030041980c4000c444500701c2c02c6240c19211b05859103402054203214140028001c0c80780071210700b0584010000c0342c061910303440c107481d0185c103001003800280c0140c0b14610240e22804514014103225000c40d16000c0360381070010300091000f95003556649c2c24019942c40e0001120085800f5080c42d840b142d0080145524000000d410038201801c4c500d0003a004000302c42c1c101d55200c088 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 431563570 1250 431562320 431562347
    0x501050c07030314151509101701081c03020d1407020105090c0a0b220e0a05010e01170d0f051b010203010918030f1803050303040308150f09040209040201090b0a09060915 75
    0x51403801b07141c1440328581e8401c1400c00d941c48100b110b180b4030100d0744442e1100341c01d58181e04401e039690302c6000b03240d55001b440714030f0340c03402601c001103d00007882500504110010f140000c15045c0d8882c91010711880111400c00050f0354078401c210000360204121070414a0030348640148506203143d881041c0325280702402001110001e41038080c00100b0990002c2010340700501d883e060440911026007401e06c540c000c24482d0000108001444a040d01c3c04140e00400500552441c0007040e540120402d55800034403a00b0b02c0383d0700301c415980310305901e49090b1800060b520744c18010030404481031550b00c0ca007003012a01c444000260802c1c01c1e066001003078100000700130b010395254120700c01ca41c0c100074202d0202005110800d5000322680d8001c452031800003408000c503500b8000d40c501c20000c40d03a8000c0440d000b003005418140d00c6280c200303006142504200d600d42110101561050000b10001481c00d00304126003640050000041c040703e004480d12414040401004030122228 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 431564820 1250 431563570 431563579
    0x6090907171608040b100e010311010305010b21040501020d14041202030403020a060509040605040603061506050315010302071103010203100305070503160b0912010608010902040608010501080703030807020a0501050c0703031415 100
    0x10807850306c014041c4400070a100026400301750313120b103031810340c01c080800078a002c0381c2040b00204102c0c81000544030401424900c90031048d110000c1940c010002900c1a111950300300000203540d5070500541c0807420b0300c11b51045540c10640f0b00052842031045240003190005d2005100580d81c0b81500002c403091071510719103c081c0c0f280094001c026540c800e0354003901c0d1100c000704004480e044104158090300ca900d1550303954207006d0300c0d80e01c000c40d581c41c2c020805a20b030901030b6000350301038403095006042028a002000c1c02181c22a803043d070302a510075209170020002c1003010411072000c0e110580c00741040f481a50268442c10000e40140c082d0038402080202c0c0f1030310750038004024101004003d00ca03581d6620300b80c80c000c1003040020f9005505142000c01d50702414004c1e41c0c102c46280b0000c0034883d28540302110305180c06000300b02103000380300440001c140e00b401014000c0b03015001c860341d10f40f61854083d0494946103405a50b5a80d03c00c10010208200500e0700b090a20a49 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 431566070 1250 431564820 431564843
    0x210f0306190b220e0f0c1e070b19060501020c040c03020d0e060402030706030b1c02010516060f0e030702030a060209011101020a031b0f0f0f0507060213030c0f0b0a0e0609090717160804 81
    0x141151a0034000c0c0004502a5a0208a5500703001c055070009014250712031032b81c01d801446007441c0c01134803118000c960150b401084509250704080e40441300a05081c9801401c00755a2180a4295880d040044030142d204501b031100b0b501e000d02605000b4980d604080010f9040c400c00310f418144e900f41a20b031a0001d034800e120559018408030303141c40c00e80241801d06021580b41c0b010060419000001d00740c3d01e021092111028000200c4486a400600070300c0c42c2c402c1552103101a5000c14070240c10801c2c2408070f903000004c00d0014114805c820744010442c035641c0d2600400b08009149844100407800020981c0190010300b008000358140c41d00c21583d8001c080e0503030b035901c15541d00801d0284001181400c1c00800d94071700d401d40c8e10460170400c85035520781312340402d81214003d101c070807801048140d410078002c40011000c840054491410030401e0300000d00650b2040328008045820074400310210400d1580060b404164035216080900380303c00c1c014184a8000c200078413030003c40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 431567320 1250 431566070 431566087
    0x60718030609030c1202010606031b020a1509080d0b132a031d0a020307120507060e030c060414150a0509010311070209040302210f0306190b220e0f0c 66
    0x48900f40800c0303402126254136102685c070001d0090a141c4520b1001030b15108454110100013170a26040d600325500038010a28181c42c0c2c800c00c400c5441c8440f00d820b60351030519002410100c0a07040001c1304000c001198911501408841188190300d64105882c05156010061000e00c607a402944182200400e50b20a41c4060300144090200141d2b0f0009010103004018030010b103003480c16100358280c405640d035071403102d1402204060010103940002009005991040520105000f802021100d042540360046202584290850a84010040d203802e009090440301e07062420740707403600340380780801542c001026401201c007a00e040640310741c51188445010020741e00d41d960000c01103a400e00300f0f032034069a6244018400310078103140b603640d5800304e49210160703034421030402070305443c5a6885080250001c0398401a000d010540a4017144071685c6038060042c0d04010490700d4401c070042c10080b008603480b50b201c0c07114920740008108200004281040d0070071806404151110000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 431568570 1250 431567320 431567327
    0x9060d090f1506030201142d04180b0130020d020906031302010f0c030906111519110405030703020d0519030e0108060409030804080a111c0206071803060903 69
    0x40e0400a442c01e098124000548480c2e0740c05401168401d890701c414090601c0c0d0a07024500030010b03c5da00d03c001000200d03e5200340d04003a00c000c03800407000c00b0b103417688039043c80703140c1c00c0b00e000500e44d03050f600d425420043d43c000380c5540140041440d8007100817250707100308880014501c842e1921a0300401c42c25106511a015211091401454541c91b89004c14141c164181c0481040e40080c1e0082002900310703001d02e01c0c1d0141c60781c143e6189040a4200141918828080345045c2e0b101d110701e02d07200103800b164a8186004681842c0b5065201a1000103070095889080c550344040c2410031042005a4000139141d04032035058400036003959541c20070506000c404040780d50700d01151082441010f40c400704008a0030026220038803551150000e00044601400004010804c0c0b100032a0114201101824200e102c61400d0162200c195070b0840c1002c034000b5401d2444035003c800c5102c040c1d014041c0c6540300701c3e1032400e038004511040041c00000c2c6184400b910076580c41c1011300a0510 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 431569820 1250 431568570 431568593
    0x91a19051e0c06060102010506090c04050d03110f07050112060e0105100519180b03010305030732060a0f05071b050709020a05030915091b0a150915020309060d09 71
    0x710340d40c0c03041e00c480400304800d40301c0004842490042d4a401c0000310545410f1030900d00480303060300940d041c141804140020184201c0c01a0706008000d50b0905001c00100449008080654054011a80b034200050214101c40000026450401205200030103030420302da811540103d58807105510b101f031091320948103035440b00075480304132600310130415000390f00c507a04200c900412020741a41c511050300c0500007800b00404d183c101f0030515001c204a03624944604e4550b02d60300e8001c14811104c8400040703922110500d0340c210004001c1c00c5160b0f0712030880000c81c8400c050281d482c0c407038001024652a288040d80c0903403c0030301201405420041e01019144210701150f0354500c2c40c40140883d0411154041a88940c882c0f80555611804401d4002c003000c40040c410007202c00e2504540c100040c0443e41c10842c581c000217a40d00706008196840301c09030301c440e1116170400d081211700c502e000e00c2440035940100030240060b1a039504452220310b0407000094400381314a8229502c0341b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 431571070 1250 431569820 431569867
    0xc02062809170a0908060c1305100e090a0603060f0504170c012c0c030a121b060606050318060411040e010b0a060e032401050d0f0b07091a1905 63
    0x804515600b803e6000466401034031030210440b00c0e255100c0b618041d503449158910300740300e14001d00806c054103152104491503882070071b000d00c0e62141000030421064040701d0b415030240d212001002403103e40c0c42804142a01c00c80d0620540c501034456031500e0085101c3c002e5040710005a6007241c050030360010303401784203115400850540e20140320518141e1100300da0014092941d240c90180347c00030781d142d42180e21104c03c0d04147c1441d03c041d41c0c0c0304884040d44003100340c8811042c000902e284213110190010f0748540340ca904000703011100b003201c0c1232440420f40c0d1040040c00089072100a4140c00032034102c2e404591521b40c03090303490141c082c1f0350f40315030000c50f201d03000300348540c010081401d060340c00d0381100c400070311100720340030035060a411041e01c0ca00904014044d80c1881d2030303580b54150140042540b9000d00e035644040001c02291074070005080e9100c280135242d441900d0444000d40c03040110300f41722080001c490340d950791920b4641403200c00a441e84040c10056104d056aa = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 431572320 1250 431571070 431571113
    0xb1f050c0d081503010516050901090902070f0308060a0609091a19080d03180f05030c10020715051501081b0c060103050706020307050d03050702030d0204090c02062809 74
    0x3581c004001d061a01e058502c46031810000c1c0d140c20b140c0c201445070f070744250203d2440c0385a222a01c82c007515180d0024101c10704110032650041a00c0c040c0b80014000d6038401c1110310441c1200e410002c2c14101d000d05805e210300c1108500304046944100b004050340d9001500080701903043c070440207089050924517401442500b41c1d485081c86a0b000304049a00700c5041e18180c1c49480821000c4800311000c0c00028042c0080d0680400d012421220354248202c0485e8685007440700c5041c03910b140d244070480d40c69000291142000600b0422103000e00d11444240100d0402011421400905c0510745040003148000141b05c429802048e012903502180b140d80e8a0000880c4035444040900003030340d0502c190000065102e100108a40b60240c00c000541200c0700e000c001203000c1c04000d040c1004505c02407007100ca40741c200d44000c000a00640707000241d80701041c20080c1c01c02000601900c000e079080504404007990300b9201001c03408a4060004400025245c06040b0041c2e807405032508 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 431573570 1250 431572320 431572333
    0x20a06050c13060521100e04140712121b0f0c0f1205010e0606030304060f0e060a0f0305090a0b150a030b040c0e010b0703021b0621070e01030b1f050c 66
    0x45641041c01411403505c100d80342c40351406440f85030700d10200240c2d44400380c00388a1104006e0711414101442e00709200d540140d46a0004034400351510100b0b030401d20030100c0030301d02e8a04000e0b1513507911401c2c0c8118100301d40c00484981c0344d80c0d1003000082014000d04e100c2048201000041808403003d08008440092640d840d490f640c1a1070110610480b0a07629042c00c2c1c0c51a89400144a485508020001d40c81c080c1071040840701c0b04083d0a10b00b06010320039003001020741e10b0304050071180b111952004204101540300030241c5101410000b01e80c2c1201c00440003082c0820714403a40310080342c03600760146600b10042078140b06c1580c809440084468244020403810013541c0e011540500c00d1007003240d0325010502401d100d1707c00000c0c0582c0c031103000c81018030070514002c13810036002401107040c0248540344070040342c4110040c0c0e00b104ca440040160306608090840c031007078028641000940710640200d103850740e0301d1400801846490108010441c494011030b0310b0390300c1c100140e464 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 431574820 1250 431573570 431573579
    0x31e0c02030a051011090a1a133b01050f060d05180c060f070308040606050622061404051c0f05010e07120f0b100801020a09090f0606020a06050c13 65
    0x131211030f800d14200d40e10742042c503001045d100c810240c070051070006100154251412400c540780e1302186c1c021508818041c091040892100c07a42000203003071040c0c11450319409005070319103090581e0400b003141a101180c0070114040504d07601e041d18130503203094020205000008405002e402c20040780582001c017006030400e084080041002c0c2982c088511b075035500b20410641c1d008036002140641130600c144000700b0b2143c0e40052b00540244400203900303480b1b10104035580c2c408101d205c0564080c01c8031400800d0520341d89001840c86140c8807082000301d80d000c172520b120b00e200d180d02c16622400701402c42d400594400003260b51000c1554650f4205151890191204040407841400744200026074281000d03606c043c0c46900c034544100e25074040c1e55820403640003500c0751480b2061400c010510010074401084802481c0e118034112500d04940a0140c403003402803400e071282001c00401400c1c1d00001e07003000040e481a0302040700d95803890100058014040802d42c0020421030009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 431576070 1250 431574820 431574823
    0x2070803130315091a0417160c0509060303070201080a0b1c0311030901050f07050f0d0c0c080c060f1e0a031e06030203120c010b0a0303020105100f03031e0c02030a05 73
    0x741268072460803080800c05801c60703c4110b0b04d0a0902510740d280310301c8001c0d040070040d0f081a6000b03200d40c201741c83c404c260000e039240741d8000c0d140301441c24440030480710500c10000c076448010502250088000e1404802007504c03030160501c0241400449004540c41c50010340051002030b03005040810300e0315400c00280040c902c2d090301034000c034080c4c074503500310800084110380b144901170315654a0240d507003951a04a0f0710108003541c1c640514020060b4400c8140903000c2020b0503503841404200321414410803442581d80a619a64040118808551540805d8940084445480075207030844450900152001d0720300311180361100040484420390103a01005e42250580400842d5100104000701150006c1c04080d5165100034101c1410342c4045c0c0042003014400750001c1000300c40c410200b40100320641049000d41d440d0310402580441d111030301c5000300848d000319052103103183c8000d06446503580c500c208401d000e40d2801c0c0c540d402030580c400c10342d034003500700c0e0013920b101e04006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 431577320 1250 431576070 431576107
    0x1e020a0501090812250c080705010c03060f0806040f020d0c1d0f0903030603100c1b08070302150f061504051e01090b0a1b1a010b190f1d0102070803 65
    0x1d1400c02040202e420303030000010b000c8002d003810b0012680351700484000e032060002c200007129111410003808001900030300440320610190f48020500c10b0030035103403040307484e0950045440799101c0c1c0104030211340b102e0300210010f80c05442760084419581821402c426458000c2071141e424401c8584580708442d115500c2514116030002c141c3d151754040580364070003070700c00503407540c060003503500041c0160340b028021406500b0410036644500000720301540c51010103407101c54002c1441d000349a01070040741031728828041900d0071854850112119000040d1840f4003c07030701281504c0100b01c0150454010300401001001c03a000c0f80c1c0d210342c000c9405408114000384602708009102e10015050355021601070300da8091842c00b500041e0a201c1080b9020766a021090017654600c95021010300e018001041c0703c40d81e291200e1040c80c400d419059607900401c504821143e40c40ba42c402c00350f0410406554018801901050040745003d03142d8000b00700d207010000326071007201c1c0e038a0701d05d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 431578570 1250 431577320 431577337
    0x90e0a1b020606010f111c05160c080c0f01050706090302010b06071209170703031107050d030504080d080103020d03030203090a060e2b0905060c01110d2304031e020a05010908 77
    0x70b07141c540307102c000100c400242d841126251644021101c800c40480220081e84a441524001e8144441c41c80c4404d2010340c85a802d5900ac0b01c4c00c071061024050070300499403400070a8811a032000030aa000802c10b1183c482c010306100d684000391000c03d4801e402c1425103c400500710b948401d094100344994580c40d04040000c5001103000003001c09000d0300308005154002c000d001d0300c1d45161001d03221203079045821880c42c060100b0218007607540e0368208440c2406680c8080e155820402002c1ca401020310000003802118001040165545406021102d52500c1c0c05a2243c135844403003407400c0740900d001400c16060003c1240d0205c00001c1d016901c0d182c1c4580000304008540c01d000c11681c842400400080f4118005d1081e818110002c1c5170426401000050054500c000840d0603080000f0450303103140c5600710340c044204d05500035451044e15640761802030401c0d641c05040c000081040e540005080e0803030390700f000d009110810881d50000c0c009d200c807520f140303403005466110000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 431579820 1250 431578570 431578577
    0xd020d380609010305060a0b031f0504030f030209030309120312150103110c07090c0903050f15071b20120709140403020615062715070201090e0a1b02060601 69
    0x650601c1e124011504a03500000541b410f0b48a01c00088050a65030030b07900e401d445451410341340302102500e03659580c8440400002d5a040c285030042c010180c0030341c881d00301070043c0041d884968001c011256151000c5032403e0400b4006a007250a5003e1031780f0007561103000c0d408000c1c2521009641258010091381d0401c546090b400915a0901610151003d11742c4864014071008220f644410b030b840d429802c0c9034901d00d54907500d10381f070f04454170b00d6400d03d85c112003043c941301d031155055142c00031454203100c88240200346001401c250740700406056600045645220384031800040441c00001400f1040410480b2010301d54a9840b84a041d200b58503085826010410800100307001e184d240c0d001c0d06032515040541c00300d00192030407256011404104034902c91031840d001d00c0300030440002491441c0b1584003000809512652400d400050070822440107070703480200c100c15624000900211904c40420340b00040a209000241c802484044100b40c25000108544190340076079 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 431581070 1250 431579820 431579933
    0x5031905090708060603070b09040e07120c03021806030d1d03160f140303070803091501080d020c062b020702100c060b1807120f06060509031006050d020d 68
    0x1003d159031601c117846141044081449000490f1900b41c0081440062f400c0c21107859588076100c0041951003200c045404880c1c00a041046043c2140c440e29102c1040450740c1c0c02d49422310119443d04010361031241040240f1a01751907425000e072012020030301c040c04903402d20314025031010518000340101c1540084109002440c0d03070744402950110b800140246040000a41d14040d5070380000d070180845000f100c0b0035500c140300002800e03000b40300383d50040605078660b0b1006400c01c0c683e601c0701c0740610300c20080c4c0c0400c1084000c2c4220f4603042100507418664482c2c180f00002d000382c0c5c0000f0742c46540c50f0800b01c949035002d82c0801c034032030040700e040040d030490713104001032503072001201d0544020100004480e01d0003050078110500e00702101203254949009500c0498406070072410200d1004074071110075040412080700c5520031080304021003401c00c000103003201100c40009206903045c030300b18030030014106103c4c41b03941d201032442ea0302d441250b8600201074100228645058600700f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 431582320 1250 431581070 431581081
    0xf23030307030509010f091e091b09120311030d050912090a05060a0c0c0303050415020a0b0c0705100f050a0c020303060901050609041814070f0609060503190509070806 74
    0x2204a4140c142d0540316140713000c1c6100010360f80d240f44c40340305e101072002100c40022800c0e1050040000c0d2001419800c00090804016200301c2d81074100c1d902680b24600003141040e0341160401066403c40b083c6480118400e00c0c0868181c90b10621141140c00301161701c402c0c032645908064007607411a41900e03070400640301310800a010b040076130760f8030245214041045042500003880303182c0192a001c09060865120141c0134000d0b580f040f000541b00090030800610300b8288040b8403419031029003184001c54686403060480a40060b90862000402400300704041100c01213152001000307104803a080d0784900010001200d0101c095801c00180a06251006c41101e04c1504010300d448810f034244424400984c112030840c80c1c000d0f0b901c80510000a076450461512207110702c150f0074102044001c200d04111855001c840511100785052100641081c01076064490900e002034403641c0d11060052607001078581400300314607120510040d02d0700403c0890699040c0001c4500c0c0e034481 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 431583570 1250 431582320 431582323
    0x905120301060f020f0d0f1b0b0a0f020702400e06060a150e0120010510091104030803090106090c1115131b031b080c010206060108040201180f2303 65
    0x10341c0c4d0042c403034018140c030b404140d007c0c0d860510031301c0003844c1c0134140c07a51f1078900540125001106683e1100f00e001001601c0e11030703000d10711700b400d0780300c03402d50400e10f00740d0129541503488640072140d0f070000c00c0503010701b030610b01d04128550880b9003070301136122900c104500109004404440d01c2d0043d9000a411803c2c2100d904044a2183c810581c15440c101e50495a40b88c000545504000451101c036001c80f00402c401e54041d0003010001a50b414160745034007511a1980c03002c080d003401c00c036401048429110581d4100e0f90442d10f50b6a0381c0e524150024010a03045d0024000d45191204e0040050f51221780d4911800c0c00600312240180c9000e84542904411100340c00f01e5040c00e0f00d0309002603400c401ea01007640740c0e940511f01554480c1e07141d45c11089004041d5400070112001000406400c011101036603a0a0000d1b026604014000074000000140080e06210007006a54401560540342800900700200044012a25400409200c003441c120300074012181d00c400381c145150 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 431584820 1250 431583570 431583583
    0x4060e010512011e241206080c060a0908060f040605150f060a18091b05390a11010f030b090f040c09090501090c0605091809010905120301060f02 64
    0x1c2d075000100c29030b8a0094242c46156a03401c8400680c00ca0242c00107103003082e60150502882a280104840701c0c1c4d003507004040303d00101e880c0399144d00300b480c1008040300108695801e080c064602994503151007070240c0302c41d05190700c40d04031845010204005048948031503809075106107801d208a45070070f14228000f03a8002111031740b1503840c0f036110b40d40d4039050b0010000a0751a04040040c2107144c104403d442019603c1032021949800321003081310807082e079488480340d40d4140142003480324100d10884e840e90080400702c022450051a21a5904400c84916a2152021115004070780e2401d041030714403c111150210300c0041041d110b00d0b000c0e008a0705160005003840d1055915141d204107140805007042da026071554101003100b4107140100c00c0d4085c082c40c008100d44401d0310304189100e0140c1d1024040080a00003d151541c5415402c03407201c1c1090007095080c0c803610f106500419103071b00c0080c9240300c0d060020850301c0005025604881c1582c035200c1c8000030450090780c0319007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 431586070 1250 431584820 431584837
    0xf071e050f10110f0a060b030601060804030207141f0e0111071406070305070c03080901140a2102090409030e130507020d05070c030c060309050609011a1311040b04060e0105 76
    0x90200210803000d6105194000b0301c3e4a2400850740741e410380000a40c00e0039800340b015a2015181d2020b00e0440c14100902d60040a480c030b0310742c031986420340b0300940348d9a640c0185c0c4100031260740c500001d551488035080456600740c40030380c48850110406800384120110460101c0c28480f00100e06180101d901400c58003000c40002010000c14200017550380700c0070048041c031409001e501d004c0f0b400b88181e40c0145200720006503a9482240000d406024602c000021801040012455032070703100d200f03900d650841040100c400006000c005000e40a030061091b0041c1c6070100000a241c1e0202d441c400c448401d81e07400b0600704842d0803820030f80b4811104807000d40c0c0505480b2031450f1085000303140050151110300030702a280d03600e5006550780c43d17002d8400252518007085c14090140b2400c0c3d0084042c000800c1802c1c2e80d58885c80a5060680321184151ba802000150365203050300945c1091540784241565581c42e4502c480d8660030078001c08002a0781c0719290002540503504031010384 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 431587320 1250 431586070 431586079
    0x601021b03030a1b050313060806040513020904030207030615030201110f06040f060f0606080a050619052707032007020a05091509180d090b04170f071e050f 69
    0x9100c682070380d9480c1004200c106132001c119250300480d406001a0001d0b03e03144e4903041d0341c1450114010051000585071030711540c5008180002070f441041c20303800156055075004419600c50500340d080040f290f0015081c182001d50442c3c01419002e60602564801d880750240440380c0e0b401301e40e81d184849140341c0c29900c15401300380404d55031103245010074440d003808180c0344240300451003554426449040411100400d101168125000e12a032116040d00c2184804403200ca440c0c1000c45544507240c082c015208100e511171040300ea11007101040e481c3e10b1411410034801c000d000380b500000c01e50320304880141c0164101000703403c0710343c000d1b002801080100d05004c1041815080944155456605840304140d640c84081e03c0f01d1103011051182007c0c0d07101401043d047c07241c0c0300f007400100440108107005440c600d0302600c0a61715003250f00e001da401c41c40040740c03600b400d4540f4425548599040081c2c401241040e02c1941e840741842d0900e003030358940c14000c0f0b0215146a00d50301 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 431588570 1250 431587320 431587327
    0x12171005010503040f29130c0b030604060e040f0506011d0712090210080105031603171e13091104051008070201151d0609130f08090a0801050601021b0303 68
    0x9600c070b4005907820500031801d61268242c41da44044464003c81008200000030003072008442c010402025480b941e01001c1c41001310455840d0103024420380110b208000700030010580a0322a80d101a02500f40c0e00901000f60038a800e0202c0e21405511084506124540020440302ca682c10540381c4085460060a05500c1701e02c015a11032001140b480101d0390740320024005640c030400500048036164603040510b5062500b80b42c01d00480c2014130640e01404002000003076074641001060300110f541d41e9448140340620103241240c00100340c140100003140c09032a41c803001c1d206404450300d5110400c00190600104071301401148106a808500e0759540c1103018018013120358042c0c030901c00001c0000e82085189001340302d80c0c000f4126003210040e452601070300000c100b600600c04070780c0428103107085001115948000b0394001d2a42610001c01070030815101c1c01c2d5823640700000d0090030142e485004a0340240b0040340d40600500c2074404280301d40d00f4180303c00c0400030026000d940b4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 431589820 1250 431588570 431588579
    0x50c010e090c091516030f0f0e04180c0e0f15010f031d03030a0c08010f0f0b0705030c0105041416051e150a08042d020d031b121710 58
    0x70a400030360040d90020881010140135903000c4000303100100c040c0081c90003024030380c01e0040c13101800b8010380c8240940f002940b0320941c0c000b4031010708000112004101170a58202200c850f4164010003040c03604511000704c1c1004000340d11a00c80e59440546003040c2d50b40d03622b00c181c0101400002800316149500540283d4881d0300480c0100c1e0394a4441821103203d1b0345100d203143e00032101c0c90030460b82c480541104650142070313140106a801e1400401c0d03030510007000b042c1c00141c13250b079005820025a880c104003040c001e480d06101903800810651600c0e0400250752081c410404a00e405900c8080084901082264042d0360703020f4000e0040ca1038920101c0c0ca0b1a00c07590b00c00b80c1c00303031402140b00d600140910040c0b45c0c00140c0d560700303401c1d1700301803518540c51401403a400c0c2d01140311340120801c1c03200719483d007005c03550111420700f2075070003900302074692956424403588455041c40c8038000b40200620707842c0740715290350340304143c00c400d45101b100903002c141d40b030180301c0c071100341c0410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 431591070 1250 431589820 431589841
    0x30c060f090a0f0b0c090a030b070f0201060e22062405060a170a0b060c010903030e030712030c0c0204020c0114011205060a09020a0b0a0f090f15030507030b0d0f050c010e09 76
    0x6622045e18500c4515048039a00021400441540202e41c030703001081c2000080e42d40301c0c4c0d51410100c0b5600080c41840d080803841540e8503c0149000ca03d0240200c0c1c0030000920445144100e94100804204811015003180f0303060700c1d1451a02d901c1d9008000c006107504240080710110103e641e00c1d83c11604920100c0c203c0036101810645034183c4685000f009903540c3c100030883c2454050000450050510300542551072000c0c194a10381c0050040c000440c007800c400c2d8482c0c10991a00280f4085a5038081e10201b0140c00e01a40261010440348035410f015804040d0905416032084140d03a696909451004ca207030800410940001000c1009c501c82038024843c1644010881c4401544de1b5000384074540140d00a1000035002c80640161a0782000814000e0f1044500080d01c46041101c01c2c401e440c40f2440603820590303070b0b40008510320b102e1b03848940d8114004082410344821410040207203085000c00359400d010b81c0b52100032a40c0107640b180d2a50b0006401c54009179503580111 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 431592320 1250 431591070 431591093
    0x1c050417040608071d03100902041a0105030c1e0703020322180522030f0e0a031a070c0606080a0209180a03050f090604300819030b03030c060f090a0f 66
    0x500d01704008503071009075010301c1600011610f40c2000a0710307114a00400c81580c0240700c05252248840b0b01010169a0060031a50300c00740d4012016a11300e1a001c032554004d075040260801248042402403c050303002c401000114014000c40006070391480c01038070040b07420f1040406403001c500030152050440c2d0022944a4000c95064406191403007031101d079090f0300707030342200000c8142244c113000c1d5802803442d4050602c2900c00c501c030507095a403540d482e03403110041e8600341d9000d07200180c000e51140030b4224000f54001030a014007a5586202d40d6210900074007244a260417800041d1004035002181042034042002007880c0c01a6440036036050f4048650f0840440c0704005060b515242c6200800091005280d1141c900942280c50380818030700c80d00b840c0090680708a400040b40e95601521881220050314030b450031202c190540c0184a94140300b0703003501010070700810380e00001c0348852160481c6206003941c0c3d91a00700c0180c444ca0025130062a86080703914500100310723a141d05 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 431593570 1250 431592320 431592347
    0x5130c03061a04051219030302072a0f0501020102030603120903250311030f0703060b0a09091401050108030c1c0c021305010503011a0f13021c05041704060807 70
    0x1c18a0700c403000407100c090580074580c20004006420411810314400700ca5202c0c0202c5c01811300c0f2420b1900b0340184400002000d01090340209001c414040f1500c003002903154541c1d906c07502e1800c0e010044403002d5840c400d104a0301e1691703100003015401802140c0c4590b0b4014080c0506160365411241d00b601700304545a058410400c42c0c0c8640200b4000f41543d20b50b003000018491032035481c0c00a110180290003074080d801c44200c0e0400d10000181da901038030360011010401e56034000200e100380c00582c0c003200c4101c1c00d0011080501c41c1071500d0603040f0903000028031190b80c8a0345919603d1040b680701e441c1c281e211584a2507801d01045c1d8a80c1d10300822f06d00f8a0303054403660002420301c404980c0c2c2d1009290780e900100858603091154114401c8421210703a03a04e1a030000048100982901007070049020244035100f401c1c140d8115001030707078041114009500030035010b000910003190700712901560340c042500041d000300180d80448d222550790400507910601c08913030aa051110 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 431594820 1250 431593570 431593577
    0x6080a030203030c030a060f080f0c01030204060c060f0b030118021e100f09051237060504050c19031403030c0405040218090a02070c0e040c0317160b0901140105130c 73
    0x8070310400c0c15560348c2d000b000b0f03060081141e041d03038107146814039640c0d407607603410f05204100800c8990b07000100484010340014000030003404440d504800350030235801c450f516528003003151f25007243c3c00c594075002c0380c0255440991414030a07071a002d4040c56140b440c0d48582174001c1d0101c5144070303485140c403500d002c0c40d0a01c074007a951800f2801304911075141102e10341044035607500c0d8810400740c11540c1985036804050f00307282200d10118011696002034051030701da90000d0f084c020200030740d1804100207000c0a210b86001d940d0b81c8611209030004445a035044034082070718040000c2030b21301540c04100742078605460300d07007040000e500c850322500d6100c604074840010380c2e540f820074510942000c80301580c1c0326924030348004130030540e40111a280c4010414800881c546c5072103142942c0e8401d84507160ba400a5000301070394001c403040544945400150b241c10480c10800003802221410000e001c80343c6035000b00c46044009000781904900c08642161650385940c01160b5203c1c250304 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 431596070 1250 431594820 431594831
    0x9020f0316030e120301081527070e010f1703030403050a08040f020d061508070e010510050408062805130201051e0f0306031c0c030302090f06071506080a030203030c030a 75
    0x40d009040036a130301c00301c0c8003401d0040010000f100b414800003c0000071494080850b20f007081d4030001e4030810400c19921859a210705c0801b24104100e41d1000d0982c01c0b6050a0940e0340c1c00042e80c0c000780c1d9024290b607002000340e500b21181e1001040d02d0040794036884280c2004c1c452241201ea00d04c00510917240300c1c00c3c601c0f0150141c0c9909990250f1140200404640c0b020801c8032000035091a5200302c006511501d0104854075680c0c0c040c40c1501c00444440c0c05084a44004907407d000e00d81190000e8082c00d001e0050300d8041c80c8442200941d981185150b061800610741c4c11208121040741c04102c1c80703501c0c0b200541c422001050307404076501e031a007c080d080009410705a040360ba27044001c11303800030920005250401030700b40c540d2000c401d050030701180100e0040018561071030090030b254010a204009641d510041c452036480681440c0d00c40466042501121014148042c1e40b00e01c1d0403004201032074007203510f41240380c2640040d0300d10340781c7c09140101640001c10940c03406907a907 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 431597320 1250 431596070 431596091
    0x140f040b1c1b09030b2503050103021908060c0a050403080a05040608060603010509180f072606040c06030b0d021810081204050d0206040504060b0a021b090106200601061101050109020f031603 84
    0x8000c0840c80826a560020fa09d604510500c081c0a61411422002c030902c0c5604210205000035455800304070214516200d44101c182500d01d030180b034000030f00c80070f40426003900f140d0784540640201d8045541e95102078517080203000e810311080c003455420119803c0010080322004c98000d00040070344044400c15560120b850f805c22080c0c1d008450864880000003031140ca81c014521ba02c4076210700a050681450b54980c01400d003c1c0c85000d06164031071280c0302c1c030f0345e441e050007044050b0060090100d02241c50000100894201c4540380c41c000c0c15580400d41c25000103c0145600030009407d140c1402d140c20080c0307090025800700c2c1e001d001008040340baa1200d0041200078400380c860140c61f48059071000c1c0c100f0b440c0b80081104060051140034240c0c0e18110b840341151628202001101000f580c0001e5460b02940d5980301449458000074440364014410000e481455008010b0f0303980710401803040e0f20904540c603a12600600129180240f044d00403840403000d803c0015001050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 431598570 1250 431597320 431597371
    0x6031824051513050c070f0302100f0509010e0a150209040905010908091003020307020601121406150307050a0e0604051807030b0f07020c01140f040b1c1b09030b 71
    0x4503002ca0000440703816240b614202100403e0010a0b8202c0c14401483c1c4641c0385580750003180c0c0c0c003401a043d1100c8013020715000f88400c41d412040c3d850140214139034114034030003418055400443d42e618120080320100c0011400d000700340d6001c0048503151400549090184d04404e401726841a560784805c2c3c0002d109100b01c0008511031007055848180d65010801c0c80440d0800143c180350040003085000e40d400706503141901c01c440c5200e102c0b011340b41440c5041c0007200343d40c01414454031051054003607281c1025600d5440480444001c55191014880701d0305040c440c03046a880c82d100440d12602d03140e0000c641c803083e000c201018150780c8000a610703000c1240d20689150214405000d44018592481a8884028002407641ca00c0000000b00400e00902c60040d0801000c07078021075400280d02241c0080c68580f08403a2558445540480c0003200c4d0f261075040d0600d010080410300c150001040040f1130541c031000101031139520b41850a4000034001c01e05601c0c18804514080e50 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 431599820 1250 431598570 431598581
    0x20114090f030f010f0b0604030b0f071202070b1009150b0f0c06040309051804050a020f04022b1a010f050a02031c09110108162601030b09060106031824 67
    0x20b0300c3d0010441c41c00280070310b030890700621041070044000300130034000315505009058010380018000e030200e959040e070443c0c00c0c030750b021712401c0410700000e0648103000b080000680210181d001c1c140c0515a9840744c841141d8184a228028403107400d02000542c1510015003445c200a410081c034001d00c2040d0781d424440103c0b000c5001c00d422180900403402d041c3c0c0b185000c13644101600286013003c6d1140745c0c2e51000c240001384103c07400207010070302d91103a030142c81913100c240400b42c40941c10310419444108400b600c01d244a4541418800700a8210503180c080360b0040e1100a07002c1c2d80c4602c1100c142d400242c5900c00c2d1321041010b403400710503001d18013040f00400d680002c0c8202c4149424800c008600800c541000710070814070414000b0710311200030320b2801c0d0805010004400703901d061051001d010a600290b0030400010500c500704600341c3c491340840043d250685e03258a0154210780240009020441044500c000014503046600c5d00810080c1404040a035401c000e136000d640 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 431601070 1250 431599820 431599843
    0x3251403030f1909031e030605060c0102041d15090403180f0302030f0d0f0e0406050603010311090a15150e040507030b0a060203031302090c1603021501080a020114090f03 75
    0x151042c100001000380032245502003500f200144003c01ea41d440007099610000b06400405104030444c90700175010b0b138072030f800804000c0c0545885007160030f50300d4007c0d00240b00e06644d9940e000c02c25110034250b600880d116240c0141d0f012060007042080c8000d6940c010012400d0013040700c0054104102c864244008000440151882906620500d400c148122407072904039440303090100ea8652b0846501402511079143c020714000608001502428075540460f400c264004004014862071600c1204411001c0c0e44c1028030f0b0b225865100b049865240001808000500090103800c0c154503812884800d036140246184054400040498100341e40340c6011941d42c511490b03003800c0003c41c0e003004101c54000b80d0300f1464592040e83c00351001c0000203228084a80004054401c81800c0d21a00e1841c50f080e090b841040d49006944c41000014409111010304000581d0090000c0c800c0a1603034182c1d43c8914001d0310b0880c980954010200d29588002c005000b440141c60800400d000306 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 431602320 1250 431601070 431601091
    0xe100e070311010c03090501030c020c06040b04060908120306060306120f1006061b080a03180c050406090e100504050c0d050717030306180a11120f0106020325140303 73
    0x11071461402911490a0052050500c00e01000c1400400c0e00305188030203c50007800c0c04070b41d042400300100c0c01d0120305251241d01070404a00820720400210140007607550503102c2080d00d0b502c9102c000e0b991074115541c0070700700108000080e42410000050b5401c010040d01c03000002103c000b00a0800d001c02d44045603c1c3d00c400300844000006011700401401c0505003c42183c480030130126481045800c00381954200046010215210741e2203105000340701000c940300c0d10310b1072a00700c00c04a07840c4265485142080d1020441184502c501103000540900804240c21404805005818002d1007554140039036a040e0342503880d840c00f0030b80a544610302034480c00b410310043c100e515816071840d049aa00510130084ca82c0c441c18000c0c04a0000261598210fa8071400b481c0d01178202c1c49034000300c040e000708501040c6807a0b40c02c0580a445140401c0b00940e03294101241c6da40610f4aa0300021208900c1c150800c5020505014001d8004c040c4052581282008986107074001d49001855 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 431603570 1250 431602320 431602333
    0x2030f04061a18090a1a0915010b04170f0d0302071e11010c260c010f1a060c0309121e0a0510020c10060f080d090f06030e100e 56
    0x2004003900c905049015a450300180161104001ca035082d1440f0790110382891004020400398001007010744141039001050038030f500c0078480120075058058400444602c40d20320702092030100b90412606850594000701e0a2a20f0220440c0c541c0c416800c0c3d46446001c0e9210940810005001d01403030000c0e144c40c00359445c942c900c0c0c030003a6801c4074400648a00840402100054160408030000c41d00929043c0b107138500e181071154140d05802291080030102044100180c00c00c0e2001d480c90544071402080102e4140c1c40c2e4006032091003103c010701c4002728000c0091071034000042c0c00c0800800c4205c0e0309000701400803842c01d00c4091503400c202c2c2e00c800c5050342c9401212400c0a00b500d030701030140c6103001d1180d841580d81c1d4111440081c2d00e076000328424065000c10003a10402500548040c03003056900e500c580b104400310f010700b4a0382e000d40c00154030824040c4040100311400034141c000707005e00d0107404800a00c3ca001400246006a00040318244594001c05001c111302c00c003d04035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 431604820 1250 431603570 431603573
    0x20c0d08160b01140906030607051b0f0a0308160801150302121504051e0703051e18010f0c051605190c05100804020906040509160b1902070f030f110402030f04 70
    0xd50703004e42c031030351241494000704600d1b42c071b0214407940c001a060800d1520740610b000c840080c880450300841461184071a41a00c8140c0007400d2025940651509062078603130b081c011025500c010000c0010a100c14010007801c200001c00b05440600b601c0d0050402d524402d4800203a40d06a41c00a0122100c00115080b0324081c4101c83d0080600032040e4180202d10008042405000304600c00381565900051503a001044c1500003481c101d510440080c0380c00c144143e400c24255101c1d01d65580392854104d424071030751040b41003844954940300d05181c1020f0180d002001d178008212054010a010640003030544074007440214032884041075490b080030f091114480d0b15001010400841105200160700c1d400364403600500140c40219982d40c03240d86203407420700c0e0018840f600f40c850b50130015028000e40d01404d03035000030385070302d00400015400807030751261f6502941c042203a100d1410000140c20283c40d20040d4451058146469418030004040b03800464010222410b01c008220 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 431606070 1250 431604820 431604839
    0x1090302011718030c16170d0c020d170310140303040504050a06080d170a0203040f080a11030a0f0806100215180111070201020d080c1e070606120c15020c0d08160b01 73
    0x30040e1104c0a58500703100340040205a50310f44107407404003400240c051071025501c0b040070004946800c6003003411040f20b01c003440305459000711a1500c2d2040ed1420204480c50301d00e0840300309580040081d03040a003401c0400c002444090400086580d440301e00058580e410b0001c445000903903122501191442c1d0941c021000c2c0092031300c07961b030f80f0400400001654980c0c0c10f034482c0390400400c58580c1e642440685542d0b02010034402603210210f00605500d0740180e04280102c003507664003190340c50b4101403105051884110301c0c00b58209081d9013500709800b004c00b903849625003c440e4000000090f4503400c440f02c0315240304440000007440420755804000d080d03d03081c21885c103000c07039107010301c01e9081c64007480c0c415802c0e0503a0b282844072510300c03120583c0d0390103401400c204081544d441c80305038200d00504086548083c405d0300000c54005500b10030004040a4001d00400c03074000c000c0006802503158101d80560f402c3c0003240789110100002941c4510a050b0b02c000c4e941004c1c2c449 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 431607320 1250 431606070 431606113
    0xc03042102030f010e030f0a050c060a0516110604022e0906171003080901020c060d05010f080604081206011209060608010e19171903020d050601090302011718030c 72
    0x1140f0907810308501c0001c0240020854404c1c4801701e002c41d4542c9041c0304101d0300384c41040e21005140c400c0c030041c080c1921166021902505050100c140c00740300128003660000c80c3c04000c2d11031500020005009400d09030022950340c00b10720b460b0510080d50602c00041010407805181c001420400d05000d16600944003220344110006081445d20f09110254a4030000340070044c4100c0010400560b00d900800c41c01500c440002d00c004e4407090880c0000b0001c1509104015802c10722034000940181d010441d03134050b0b030f04050501d15160580401c00f10f000310241c602410008810801d40f84000c0c28862400128070a1074045446807411034841c1c29135070f01d480d501da0b490b000000306c00d0464038007001c441c400070f5221038004050340740c4001700069801640591080c1c03d5440b401884a00e034198001d200c3c0c0030881008100c1a110300004640380c0d81e1310700000380452000d0901c28a003050011545038450340a10b0001030009581c000e460031a003051145d2101031744220060000150a50042c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 431608570 1250 431607320 431607343
    0x170d0801091a06071101020d031a130204121104180b0a020a050706050a0f060f180f0204030602071407091b0e19060c030207051206010e070e0303070308040311120f0c0304210203 78
    0x901442402a2015030740a440e10034ad42d20070001c1e950f0300003801b00b25405480c000d290510241c180382801c3d08081c0100006007103040d03c95440c1900036010810f0651103481115009140b020300ca903103100e5400025400311144d0b40c1401020302802c00094264003a881c441c241d414400f095400d0181030038402d5412301d4100e80d0541440304424010500c141c0c481521102e030000d40410070004900c06003000f0321544d000030344041d00010741130090208008261200b004010f08071031400d642c980c642021a521311140c000324100301100a502240b1035260039080040040c100d11f15800110084a4601324652000001c203100500403028550103000910041406070780b14418900f0945005860302c205018001d0304418690108075060b00c02c00006511002c0030b01100c0c0d55a04608010f840100112000c0340060070213902a600341d90046a40481111943c0001d0700341441c8511070003581e00b10b502e0f802681c0c801030100284042294140000340c001c0400c001240c40240d006141c01c18001024 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 431609820 1250 431608570 431608577
    0xf0305120714180406030b0c0406170601021902040b13060f060e0f090405190303050a06080a0215180315060306060604031e020112020a0207170d0801091a06071101020d 74
    0x1100380080390b2801c1103800e8945501010300411441c28005402030101740c01c0074002090b00410490a808518002c2007a03c0071601c80441034030f002c0e42104543d03041105d500b070040c1c000030003481043c0c1c242002d00c0c0185100810100386c0501500114140c580c085609034000c548030308003081064407200c54a000740c0142e107440c03224410788001103120003642c07002207030065520303c00140a01a003800100c101200d51480384020450900703008000d40020751704102082e281a000256100c00020048000b56000c1e184140c0c10b40a03e1404d45950080142411016150360f551011560203110794501e0b9059001c51406030b040c0b00b0241450001c004040e1401040c0402003440864464095203103203212607680c4155a08061004a03000944411440384080c0041094a441600481c0d030710240c60226a1142001403ca4005540e0311812107114012614802c0144040718441d04034406410706a103000c059240741101045407540401002d480003010546200583c0d07074180304503100e1035400c3c035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 431611070 1250 431609820 431609837
    0x20c010e0f1503060102070302090c09040b010c1212020d0216050115180f02090a0303080601020606100f030f020c03120f1303080c071109130219060504210f03051207 73
    0x70104886081807080c2c40d06580300440081c2d096071007040020091a17000d02459147e0038403800c9404660000310381e944c819401c104451586520406001041581001852250070120202a5100b5000000701003450790200b000c550b07085201e00040083c4400b4050034a0800b03150309000c2d084442510301100ea00c42018004c00c10030020252044050002200000c4d007071052104a00c006c0c461480710a8221100010000c141a0040121445000c00303030266015a0384003c10481303510301c00c050110200390070b0494a03006074400e13481501440c402c20b80040c07405264082c4c1501d1500100301324440380000c0820082c40765004c5404640080102258041c000800d81d17001d48003d600410304d60ba2150081004810301070400303844404400040c11056450407e07505010100a40c4882a806503884600c0c1888042c4503c604c1001ca441540d035503801d150070301d82d084591100000801803800750341962400071442e54080da040c010720944640d56160b03c251042541d9004c010005e0f01132001c0071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 431612320 1250 431611070 431611099
    0xc04060e0f101d0a1401020f0a0305160807050a11011202090a09020906070b16031d0715110f1b0108040b061306030b09010c03140108030d050a0e030a020c010e 70
    0x790008a8824480c2081c030f801d000d05040c0304a400d405022500d1344400b03d00d50015248003c02c0e1114665074080c0d003a5400c05118084041d514a0b02c0e020007400241c0410605040042500f00141e14074412800603180282945940e480d00c18190f0095818880191560440d0342e080300d04888002d80b252401c0d13003495000d800003250508580f081c0d00844ea00055907984e0703a51803800711072019501c00310703410280c28400c1900001300194580c1c0710104c0c1c40d0ad40d014124007a40c1c005122184501001403000600300940400e80d06224020003052008445401e040f100b03040c407014407111400001000c1c0803010000e041805031059076054180315040c410301010580c00c500d100c4e484030081d1b404480c60441801e1040003411181d00241019041400f400103071101900a145100c610755420f00054807018003966030315000707118204150340300b0819140703016065000745030f200340c480e007001540b11800d07140141158810340000e40160000e24400d11a03680000120308041025181c502000805c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 431613570 1250 431612320 431612329
    0x10e011b06150531090c0513020f040608040201080f0910090c0803160c1d070c0201020c09090c09070e03030f160602120f0703020a081303170c04060e0f 67
    0x190000d031009031181c0d1000c542881d0000990b0003840060003070741410741d400c01c0a458a880b082c5a543c0342c80b201e200c1ea007096041e9800340d0b020890300007100c0540e5510701020408944800c02d0040358442e001d000440c540100c00f800f0304000c260310744a1060340d00c1c00340300041c0036000003481e41d06c0040000303040c040110400a02c9a00c40782c00f0341c00000c0c2034011030030200c1001081e80d0100569100003c1d40506542500c20f045030090700c100c54904000d40c8555030003143d905c007070250701d42410f518400540454450700070680640c3c0180181c0c0d0001d18401c000c680303034400444500400740d0014420111508080301d010703500440d079240140c4a0b900203c0001e440744600341c003101d00c4600c081032600d030383d00f800d6080c10a0140c0c44182150781768100740051011140484800c95072515400004408a00038000c840901210755247e440a5a400b208100c8005d04003005504000880007001c0207000d09000c014010150b650105031510700d00b80300104103100c5054a039020794000c10211059866 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 431614820 1250 431613570 431613617
    0x40f09060806072717011509200a0e0303040609060e0f010f0c0813061806020303070e04050a0b030a0b06040b0418060c120213030c050603070c0b0c1b0309010e01 71
    0x4c240014108480e03030303920740582c10340d131a081315903140c0d40030000c1c40724648158003042c036514403518107114055962155108441850508160b8503d03407100e043c0e42d45003043c0007480c208a1300d0808005914002c00800e185d0707003240e0008400f290801409200b200c1d00f1081c01d03050894225442c40000c032440300000c0102c00340400c0c0da014040c520f1001d10800a01e00d065420b10040003403950301195907030300300620515000700801d600c440f1800e40403912610210807a84a000c01c2e4075140c8030700c00501c0a100c02058010b01c0c2c03501c3c151740c0d001c03000309599040c4621421075000e080e00700d845007001002c00c8126200005094401c0b803400201c4901003400d03000c80ca00994010038001810710700441c00717882482000c00d100000354400506464030400413a20101036034080e2046112040d101c600303011040c80103559040c045000d202c13400e8009400d5001030b6500483c602ca06c01d0400021213120303001484a00c000d02e4a03500080b038404460350f40702c0d805090b501001d00c0c1004501e451210144c000f281d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 431616070 1250 431614820 431614847
    0x30506190306110715051602030c0d1404090507021e0f1c11070e0103030f0f200c03101d030909040303181401050a0b04050c0f0d060308040f0906080607 67
    0x362506a00302e501c1c1543c03c10f5801403904818080c00d4400f4400c0d01c00000d00c0c2c101d030140080c0c00300a03840c983c1c0324400020340f0801040c1c90001c1c4495008a201035641d0f1004442844031035400300400301c2c0a8402d0f0007180c2c000c00c02c03900280b1007505040704039401080307c1d002034480c55011138101a1803080001c0c410ba9004039800141c1d507074040300081103071a0350041c4450071441c0324005001484894400041c1d040b00e02075580c1210443c581c0b4030807529809000808000101c10100ea0301e4640ba459070105490241001121840341c101000300341010000c8501d12002c7e6905d040b000784084101e42c1c0e540303c1040c0003001e146050707028000500080000340014080550b200c040c0c03502d5801440c3d8180c10300b500074501c8442600040181c6002e03160032204422001e041401407483e82c1424041c5a00239259074409504011001801e20b907182c02070580d030b843e0241c031020000b000ca1342450003800a00341c0000626a41414400d0800580300c2551240407164400010040c500764408004031241 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 431617320 1250 431616070 431616083
    0x1808030a1b0c0504090c06140703080f131407060e0402040e18120f25080d020f0f0406050c06010b0405090a0f0902041d191a0702070f03120305061903 66
    0x908010550b8001e541105802c1858000700c2401c0c0b0003030b05506411a0600e0fa6803911011542c1c0702c120603801140c100034045030082340460300341541082c146502c0b02105c00c408032982c0d0786031959940b00440080c4d00105400c8440180511a03105940c40c204082c01c2d00d0541c6450718200d02c0c0c103209070f0300170940110400700c2c4400d880e110348c092081249840c1c0765402e4940781d585001203071065604c0141c64120301e0500104401190140700005100303180c205200c07900300720b039403207003034010758070610700009001010400c030448028081e001d8000342c801a40e0359074450401c00451403400c0d1040e0440c2c1d440940034403003009242d44a01005900c50380310307440402c43c60b8a40206901520303005030029400b50401d50001000701ca401206880003800c2c0c4103c4103200038540200000c50401c090281242005032242c842038090410202e400c078806104603040701d0317903800b41510702d18400e8008131028041074500003a025414081e454002d90229001c2e494121403802c484c5a0004611004100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 431618570 1250 431617320 431617367
    0x10031b051305060901181805060415060323090709230103150209031f1a0102120304020f09070801030303142503022a0118020105180a03020d031808030a 67
    0x49910921440c07840c42d094500c030210241d00c1f40007458501c0c3c905003004074054503020016240e0300d4180201c3d10220050003280c40c486081c84d600701c010702504510135a4455640c50b81e40c2038404800300b42841400c039907000d0300781c07a400c1200d01c00988105080ba04c100204071a480c1f0b001d50140100c40341145e40c030010200412440b644c03241c0290040f0388219034980200004c8034010980c600b4800300e075640080c000c2000076601c01c088008541d894003101e005030b00c0081403964150840b0021604140018413031301d41e0610580014205c036000700d0f00400000c485000400801d40c043c010b03101c1d0025841044078240c0f40513450015081c5600b400c008400107158a84401d071070003035041341c5001c0d00d00200c12019168082503c443d050010130202d01d10b41c0782c0200c60320b04820103041c1c400021382c143d54044c034084907805000e807000d84040324503070b220010b13050000060755426030700180caa220317864560828a1254000040c070415078010407a40e0030801c01105a264020141c02d108007000000343e0f034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 431619820 1250 431618570 431618587
    0x3030f0c21100e01090c0e010807050d090204020c060405030d0c02011413060e0f0a0b0a020301030f0f0825022e181a070506070c050304050d02030c10031b05130506 72
    0x41060190f44410030310801c800000c1010800340d00640c0d604c0e00c250700e81546014154004546402040303a610000034000c2c4400b1440c442ca40d0011281c09000400c00360500c4d910f1178286052000c00d035000c40392544006642c1c021900d0034043c5c0780115070709000170000801455811491039400810344000c0d0309103207000d4410088142c1c01440e2504480048403c401510401c0580d03600c81080141c0da0414000c0001e00d4480c0c20b80202c2e41a25400110000107038925541d1945a46403041c00300e80004090012901500e0740c10f180c94001242c800000d031401440740103000e0512442280007108050245540e10039460000282c2c1c1d5182403032400700c0003400240311803001c0320031540043c40b41646041c0c084c1c00e44605080039201c4540240251802171b183e04a0a403048c000540004040f1740042c0420052860002508101103001400f139400d82c203031000004010394440040e0001185d41c550040d8804030b000d4614110178440d5007002ca1401c0058422203076488070ba481854481c0b0000101500d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 431621070 1250 431619820 431619841
    0x90b060a0c26040f0b0f04030314041a1902030a020d0e04060302090c0403210f030f021606051005030a02030c090606091002030309060a02160312180503030f0c21 71
    0x480c03001400000940311840d200b8020896106106000c1060000c80000c590501c0307400c2210016010540340300e00d02451980c080d0f40034203080d014840140414040002d994440c1a000580317600341b590090b175900c0014005140c4100000600004c543c01440100105c9400007129044c0040c83e0034800007120f1032200045c090886900001d4008901d5000d0062041da42e0000d00280c82c4110510780001c1207a01048030b002803002c071f511001602d04d644c8400464003a901142c00c0d8181140094139003200041e55101401c0c5071501141c03119034071401c20122000340b100c0c81024100171005070070074018075000a560b41510030541c40c442e000c4100819041d6807000116001135101620321951303807041000c06501ea400480d55080b141c043c50700000e194491a100711642c03000d601c0400060340c10180c8041320030120429560751441c1d9a808560000306044e081e200b192442440116664903040d030000e2103100011780400e501e80c1003402400944007603d0000055003a201194008503039880c5640d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 431622320 1250 431621070 431621093
    0x21e0f0301020a0315120b01030b09071511010f0203060a0b0c0f0f0f0d08130303020a02070f15030b040b06160318091b0206040b0711011b0f09090b060a0c 68
    0x10340d06600c001422020240c25400605e00301d0005410019600c0d40da40000054814403180240242d80180c018000104c640307001035003010241007103d804c3e0340ca8074400d0290b80001c0b00c5890100341c00328510024170b1024012040107103441a010740c10f5040c03500c08244002601e0140140308200414100345a0008009514002492100301ca8a80c4842003503a80c0364603e551014040740681c070f800b60750003401158014000c0e1030b020f81c1c0c0c4c40101d090761030407402074101101400440c0188040064001039421500c0094007144107258941024840c016007103880c001c0445d030040b4140400031a081d43c1e59415101086414075011209141d030303140488945001118001074500350540104842c84140e2002c840c200c0710021a0054514502d01669941003c41c1c0040c50388001400050b10203104410322592120200700104034100f00e0291030241015803910100024084660748101c4d581c0440302000400368050104000001c035400701d111480760070f030b140003800b200c0d0000c1300c00c000c07200e00107 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 431623570 1250 431622320 431622349
    0x2040317310504272103020301080a020607030e120f1605031504020604030602030c03010501030b042a02070f0b031b070b06090c04050402031504110406021e010243021e 74
    0x9813500c0d80080c44e165802c800f22540c0710f00c0d14920048220380e024002d200302c0b4140c0f0515002400c0000090782000950340c82020b0807002c0203034041510300350ba02c6104092580c0035a4101404113506003400061034090450701c02000d0040184042200e501c010030b90060080c80c980d0b00050555581c00400c005110381d070300c000c1c00507100208014421111202441c1a20826681885800211010002074444424100c140c11200040075a485611084a480c001120b401074401c090340d5052003e00e408041d03441000302c00000000c0001001c05512500313145001400c8490901c41281c49000450000410003800f40340e0241c0844c80740c20025050314000c0c9401032065540380b4152800a1001d1340e0083c101e03019600300700041c0780303032f01c01c0f04165000c0d03c54950090101c0c110402c08031102007403000895800d554200820a04840401c6900074002c405115000c50b010b50349515040d909001c0d20407101d10300e000310111300140d840040f240d134140380e010540b0081581c144001a040d0400168 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 431624820 1250 431623570 431623631
    0xa3303060e153408061009051512071106070e030a1e030807050408030a05160c060f0206060409030806101101060602070609151704050102040317310504 67
    0x80001e40c0700b442d0f80b6a560406a000301e03e2809114440f903184000500d280e03038002c20107080010f82e036030500010711159421207141c000a0349984801080c5140d03940b40498800500c000b42e02502000b00d8900d01350400440e1070503d01c14502002c4c00c03629220041c1850b000c020f800c90b06589030f84c0e82000100141a000040c8100f5848014802d0301c17401c2501d141280420040b40002e607204c0d000750240c40c2107410700e0015501d480d917500c03000c44107170703001100425410300d0360a0300c180410001c182c000d000c2d120030b85030703240c40c2420a540a450880c0041400d4451824482ca54000075800701001707801c01010346910310001e42081c400c0d82c161070780f005c080d141903103080c80c00203c06500103170140485209480d50b00c445606c0b0801c1092083c0d00d46840c0c008501c640361402e84042641c084941d025026000041c1001c0d04d03036aa41080016619480c0450704010802d0040c0c0d0079000c5141100d0300c000180709000c040e0354141d1603124802813207080e00c00c1d0781d80e2541d2040c0c0110a0551a45c0110410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 431626070 1250 431624820 431624863
    0x20d170316020c0405090c010e010201110d0605131a101211131403070e25170601030b0a060806040905030d05090118080720030102030a3303060e 64
    0x100c8107100700d00c0c1c0401034006100d40c6050b101c0c81e040c90310031030f4014480750700503000040a00d4010341e08841c04003c0e0031304541d40c0344414040c01ca07003480500006e2650301004907480e451f050401c220562280b401c194440e203007280c4260f40300340e4200c00c541000400c0c0c1d851000c028880c0310031346a90141544038503400e410100b188031810b0000000f001c941d41042c0ba4140729503242e00b400485290000c0070940c050740000d81c14454244203411143c1d02003200c0308000080a0507504104001c40340000707610108160342c1e6007070840b01789051a42d84c407030001e10f420001101e4400c0042c40c460301c10300c00e050030701a181001c2007803a01c1d40e030400d42846411100700c03035503150302c035203003034014141199251015480c1440170000002041800301100350404030b260300384101900c0c2d0000c2074401c40c1c54801103084501d5440c10649003030015511070110001d0004c3c0e00c1484500680d100081e15940c540680d01000059152411500004082d82e4004a00180042080300c00a1601e40d040340303609034404184 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 431627320 1250 431626070 431626081
    0x4121110030b03060106050903060a1505060c01050a1413031d2e050c06011404060e090a1a070f110c03010603050706170606090f0a0e0a1a100c020d1703 67
    0x607041000b601d0000e80c01c40d89680c1e40c400713089402e40a1440640d80c1900200d0100b207084010360001c0d0450490401405000c540d500005041640205400b01c441c0e51036404010f10100203220b0380700c81d840c0c080c080c1c0c1b45910700385006000c05801c00704010300b4007489051006000144540e504024031014009001c070a542c48a54060700c910440c040c518262011110310415200e4000d40d02083c1700c080033400c040c4d080c008ac49100c11040e00d0b0700c40e00966505c1001503031503100c4410354002c15641d001303003000040d281800a20300402520a21072444a0310501507500c5d4400710000d8a4000c40c94162600181c10400905000008115170b0380340d1300708800402400804140003048030b07040d40b5803000d001e80c1c02102d0b21141d1802c96082c0d0703001e181804840b0150400e41851805001c00070107001c58903407903030280107480d4410b440098409030358081020240703003c844080c00d5203400b100c1d00c081903a403440d8010100708101000a01948000c00342004001d2004d184040d54030309803e02580ba4680b1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 431628570 1250 431627320 431627327
    0xd0e040c030f1a031e150903090303030109140a0603020a050d020d0c0602010b03060f01060c0b090307170306010e150d0209190b12061c0201140c070b070b061504121110 74
    0x843c40340c4a801014020040f80d10281d5080c0c1c0107801c1900039080c0c0740c201c1e000007011264014030303c105c1e03030100300b052181543d8144019030103000c0c08880010100c43c01002880b03c442c000380402c00c02d40c640401480940c3d03902090000311001101c130b1004d910304134804207502110b010310003481000c100502055054042d00031010201040e01100c0c0950b84030b00b91800300e01b100307102e61804031b0300008103032010908950400e507000035540100ca02d8070900f5900c0b8100112a0002030050703c4011007444220742c2e05c949030054070002141c0006003902070814818013441010b000250440d0f00054008840e00e803061600030b21088a00130300101a0f48452218440d0300c8007400c00240c03205d010005400d0f20b04143c02107181c0d01445200e00312888503a0054503210012884080c0c00b05060000c0803680d4001c010720400b4080c00000142c5a0445240004508501900092140d130700200c60442262108050350210b40040703800d400a00303e14100715581040034144681c0040c50320010f01d140540 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 431629820 1250 431628570 431628611
    0xc0d140601080a0b01110a060b100c0b04120512131202032104060e030d0c0311123d081b0607031b0b070c11060a020a060b0406080a1407080d0e040c030f 67
    0x800d2b500880c244001c100211201c11034101c0041070314141202003404140e04214404441d41d41c0d041803032914003400400070103444204c030f4405007010a00f140004000c0b07982144254000a0700044d82800840a014007040c15540145040080014000350502c240d42d0480141c0131003100c2035075920411441c903007010f8080010003001003401c0880043c1c0800c9032904079003024040190208460701c40c0840d400c200e0904007110311000440f2070b541d4164070389104020b00b02c89440500110384500e810b50040c10b0080c0024a9100308140c4050300089440f01003c41c0c8a40d5450314000403007403858081103c2d0100341c000b0140c9801c0303098003045041346c0c010250b40030284c011038582c226003130514100050b82c81031405580068200e80d039a0400604e0301d80044480210041000c15565151b41e84030740352104070441914508045014400140d50a1014002600003c000341280c400d44807005800301401125690085917110400242c1d00d01c42c4e40004410608040d0500c45040c415400808114 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 431631070 1250 431629820 431629841
    0xb07080114011409012607171006020a08030406020c010f0e0f070501050417120d0c1106060609060f0c010e010e01060608060f090c120c0d140601080a0b01110a06 71
    0x10380791074071603042c0d80980304070302c14010b00d9078203645403034990710044811000075207814000b4016a1000ea101741071072103a10384201410394404181b0640d821480300074800241403003044240004050065560219204144540001c0e125070b0303e89581c60070074000d200c0d200307c0705015444c01c2d91a000030f00280d00103240c00c58003c012100d1441107818420703158100340c85a103020413810881000021500090101b2502d10201600c141c260088803140301c55200c41c4110388050350f01c0701c1a001064114070446003284490004200074a460004038403503225100303030940f0034880170541480398840c020455150380c0c4084000c2c0511022250b07003502a20ba9005000c0c0340d5402c15102188080c4142d40c55441004010308012143ca1000300b400385132600648440c40c294801c2080b00e203220403c06906000c0e440c40d0100c160f41c1c4500300ea07000100c030b05815080407070784444400c5c0b01d081c1e0b0340400641d4010f0051000007a1010160006a4401c0c03032103042c01506004849014003849101c0e0b11803510072 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 431632320 1250 431631070 431631089
    0x30203071b20040e1b04060e0408091c0c1202040216121d01050d0b030f1b030106090603150509160303031e09020105041e0f17011116140a0b070801 65
    0x6500032410441a40d13943d4102000c140d0007071640407056010350002442c403030406440050000d44500000c000c0000884064444d0700c00005c82240604084454140300036513138104800900c056621807034010f4491107000720302c00b02c100300c100641d980c590480c0c0391f0011101e880b65000600d49004020b003101b9004e084045506080d060008626001150181c000160f40f001d1420180c14041d41c010a00c4454240d018880c0b0000120011410480501e002001c0c510044001e51031808260a603902d0b034010a109900b4100100300041c50014428801d07003004101040aa5541100504c0d0141c07844c02401c011030400c000000381600b5034070104100c914081099420049440400e00b40d9007102c6000b4006042000100038030741412040c880407021172540409103070b544002002d82a80c4a4002890300c1d0441c01c0304c1d008041d070922600ca000c840b81c080300d60a00c22900300304d55800200d1039000d04000c402211024903450709120078120310b6809643e40c581810100c4000300210700c24062034204 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 431633570 1250 431632320 431632373
    0xe04150c0207120f0503041a030a0605060403020a0b1e0d0e010506030a121d06070305090f090f062403040f02270103061a030d02011b0c12030203071b 66
    0x14030105880701620340110009201514a42d40c13a14401e18404c0706807031600050001261403043c0c603140100c001c44201c4510b0b21f0781003540e1090100c1359554030444c0304400802c0208016140e500800c000c840100741d0007030f1a401d80b44466000d507001000100702c110000240401120303101d500c14031004032820b0003040b40740d48807004c3c1035036160440c001030319019134a0362071801c05104a40e151481310305204102880007042020444030f0b000803030210003107070000c42d04c50207605101480c07641c44441218030855a0800700f142120540010340030328000c0b660501d00849040710b40202031040307070914000a0341c924080c20320b0583c281401d90101e1050b5416043c06900c034280344c1c0046501e100342c009903609070b4030b5a55032400414031020360589030050742401450b0b80d54144100f00e0000743d1034001052010406c400400460b0895000031305008a00c4083c0c8003081030075030014410015403d0050383e9840f0a00141c92810000e03e100d10981e112078505d8041110600444020b00462210401c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 431634820 1250 431633570 431633591
    0x21010806070e0415050f0303130b0337020a05070507090603170a020303150a08030703020d03050c0c0304170703020904080a2a0219050d03030b032401060c03090e0415 73
    0x4e94006100350782110491400500c2035243c6211440030015005044900d882e1040d081c06450b50140c3d4800303e800d00d4044100070a103162416807846d00306004a1000c46201403010303110003500349003181d508080d400700708284828010703800c40e605107030008115011240d944c0d200c03802800700e5000842c0e6070829090b008040d50300b07007002e80348400310a402650460303036900c040001d0402100030366540b100c0d201c000003c00040900013071080b94003031b9000e000e1f843c1500030090141ea002610140c0017101c204000c80036903d001c030079101a11502401d07510300f000602400c80c0703480d050341c0007c0d41c4507490805020401a2001c02040028103d031039124095a01c90401c3c00e070449202e1418000c00d424a203500b0041c43c0513550307240e1000380c10688120b02520780380400d01d40281231408a010a5840b141c041c4d1703c2c9020482d50314180c48801c00c00104d041000d42400013103206101c6d04086c081318684040c101400349485c0c001404203a4001041c501d03081c10710142c840721040008243c140b50a84809 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 431636070 1250 431634820 431634829
    0x3070503060708010b1e0712020601060221030a02041e03060c020601060804060914010e0c04060f03080a052d0d0f05090606010c080c0f07060f020106031721010806070e 74
    0xb80310705600d4880940c160701e410b6100d005540542c28243c9180c2c144c40d148a8a100f14a001d0a07a49014071044018007807440c202030314000068001c0c400707543c03000b9072003111500c142520700310300b104400c0510344176100c00070034a01070300990300160885050300070710712000000b071051074041341d02491040c08500c030700a900780c1e11000280142d10007e90307440c00080104403250840c3c821039100b0341001c0001503181949a08652850504143d0303900032140b290010b1800c0e000741809000b11080e8104002e145940b019843d22074041e002042c40030120f01c0e40040c240322440c0500c00400c0c10b52190601c090800c2450741d0b588002034104950b03251000041c0e428910b4440c6030300c184e500000811450f100d00005542218881c00b0440d1030f10400c002204d0070f92814403141c0303014100d09000b400810304201c005400c6c661446102e1045a24020341000843c0580c40240241044124542d0b582c1c0c0210a620710000300f295421304156000000000c2d42600000d00a4131558055544000b140c580300c0070032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 431637320 1250 431636070 431636083
    0x31101020d2f0c10080a0c020309030d030e07030503210f16142506060b13090908090d050c030601090e0705040b1c060f0b040e19081b01090203070503 66
    0x50364a80004a005140c40c80e00b2401030745912100b0100c4500780d4507100054400d42080c48034000051120051080340c0b0b000340a25207190000d40007a5080c0240c40d00031994030300321203103040101622584407041754442400244082c681203016070b9610b400910fa51505040b800c40d01c00000070162002940f080e0700110018010944800351428419080d5400c45460440648540e40b26404000c08039004081d01003143d410b1001e1a800c8181c07040031700740503040f118183d0007003d2040c4108405840110541c4021041d83c00882c0001881c0c03000d420b26080310f002c3e031001503402003000816441403141c00a0000d10b1102c04030301300e030000d07a01e409028090310704006002641e540b106c0d60500071458107070881103084001401c1c2e0814610448444031881c1c10265050398501d85d580c4880341d48070081d010703620b4050002e031342c00d110b004240358205540700441d04150205d0520b150303004c400c1040150850740004503003030169070401d07586005a8001c1c140c100c0124403900c1038500000c2d40303040c007003140e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 431638570 1250 431637320 431637347
    0x403030212181f0609020c0f010c0e01120f110304060207050f0706020703030806060d06032004060b0f0a0c0605090705010207090c02030f03041412030a0f140109090201030b0a031101020d 82
    0x68010001480d01d40c01c0620003807048080c3d000c0c3c40300c1c400f207801c114034030142525007543d000030400001c01041c400d085132805a814010410184808030090348c00c1900e0016040540000148031942411450010701440d480d01c074400200005000600c00d50b138018061321030281090319042c000c03882a140e40c400a612401d00541c100d803d080000c00c3c000c610740b07031b80054040d0a203403a224074204640b0480d10b483d0400ca4034840080e42d6050b004039075072040c9481c04000d54041049900385040c1c81000d02601c0c4d0aa42c400c0800500c9000d294031440740c940030740da40194203010a0070240e078001d8840f5144c2c0101c40c010b126150b0b001030346a034a40500c111211140d0099403030f0908010012509600003803050780d01c2e107405078520f4031042041040802110328648403940f24244400f280041e6225180210f4000f406c02500c0601c21642013803c41c11108400310010b0261310310310058015003a01844e480e4020040b02000003440007480c6448241f140982c03e4805280d0780718002c2e100e110060b10f4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 431639820 1250 431638570 431638573
    0x191202010606120209040b1002010c0f02010c020307330f0b0f102604050601140d0c05060901030b0604080d0305160c030833040b10020c0f06070b040303021218 70
    0xf451042002c03940c010201c5050151011403079103403203408206022021549040140c0d907134000068010f03032260310740d10204003610090003080d9807001c00a5580c0a40c0c680601000ea40320810103031040b0b0303000c1d01520070304c009560f41c80d80051952144d00a000c3c00207000d16650a1042084481c030300242031a000711402401c07a00004911481110186c1111500399501121101000d008100c1074000622682c400c40081040758180100c20402120544c0194018403080040a0018060a400b00e0a40e0300595059071122200c10040b000340c050010203a400040004020515075408030303074407651821589060015864085501ca154120000c8100004a0801100002a110321140344d0000151065100e02d00b40c41250181448061503502e004600c400c04410030381c2c03c01d8010390740c00d40802c8505014951011034080d4560f46a00c6140303102c0c1c07596800c0d01c1c440d40d940074185c400030f540050211802e840c1600c2c0c00f9000798002da001e00c5090380080c000454403c40301841d40031074001c01c0c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 431641070 1250 431639820 431639837
    0x30308071e0f031b0c06050c040810050402011b0302030a11010209100905100e03030a0c020609180609010b030106120e0703060e0a0318050a05040509010e120d111303021908191202010606 82
    0xc841400500d130240440065448c10440060102c03400c00000100350440340c400501410300b440090100e0034000703c0d182c8501d21034042c2402094022060311140602c5c0e062071038010031000600d0b402031180c01442c0364000c00380d12482240d1070340000302c1816100c055412480808200b6000c1c0d6013403200c1c04016525034810441040e140748600b28441000c1d2010b000e544c18210310b40c0028038002e5001c4403c0d8024144041000603524000a405005181c00c218482c91541000802414a007042a4400c41c02c3d80b660800200340d242041140001d44d00080c0c00c0216a1581c0d02081d11018004015030010301640b40c014548801a41c2e1041100c80040400c0c9403070385018184000351000801c082125580c8100301800310400f40803a0700c641c1010007011b036542180708409400c40b4400c6640180305130042c0315003040d03000100d9019040c1c0b90112100740d17654207034001107140054240c010009a0055060040501c05204d0758441118030031042404021455a422401c9039040d00c505000648540c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 431642320 1250 431641070 431641073
    0xa050103080f0a0c020405040602030f06100906110307060e0115060318240e010516030603020a03081605070e10050415031e17090901080601030b01030308071e0f031b0c 74
    0x1000404800d2400d040c08900004c03d50005401c8840450341600c41580010803c403044154034080b941c85002159540c0880510303040042101c0305a0045000307101e0310011509050070201700703517004581c0c041d130b080c40b0449103041014068500c03180b214200c0c1815150100e10750b4000d01610030581c1038061007082d5041903850320f03800c0900742d02940c031181c10080507060291006000d408411066400003040b2400d001640d0300c070840c45660f24030100b618000302400165903510602d01141c0e004200309403505e10307101804800700e105000c02410391040c0900024940e08001e8058030800403800003e450076554000c0c002030740e081c41eaa41d00500e0401070180000b0340c81c0703d0481c0100e0100381840a807100182c4d6100c3e0081106038269680c1c01c0040b55503481ea280c1800c3c000c2c050b100e0300c40900396551440c0d0301c04040403810300000f401d018200c40020078840c0710b072440d44000713100b0050141c407046440c88090194004845680006070a0060540011400070310b00044040c09075189a40c04115 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 431643570 1250 431642320 431642347
    0x6010507210c05010c032408060a050405010b03070e010f0512030306010c0503040803040b03040605062202090609090c34031b06050403090e091b01081302030d0f080a05010308 77
    0x410001c4802d0080400070040441c60901c81c910031004503031800515104000301c916580d5584076200c90342c81c248020107004c10540400c201d50444014103011900352600d1400f14090175507100b41070303054803600c0e5000076084007042c64603041301c082400200341e140e114030038041c00040710100d40480d5407040000c10495486002c00203078050103041524246501d4050603419a17001c2d5028107c240390103c1484240109882241e400110403503039100240042c6000040164240340059031465020441035140e40f2030204a5075190760003000c0030402d00c1e101d000e1210a070020881da01a090351000e4101180025841400c1c00d03881401400540d952981c1d012074001914040100250b1030002c1548001101380c0500c80c041e80c843e884060682e0304103590400380040c000c0c2044401e902030711601c0c800000b6038201c00d0140e88286012040c0356180c2c000c42150303100d900c00c000c4d00751189441c40c0785556403250302e00c40c200005690f4100c05880c0d001c0c040050707500a00003d482500c040044410b010359 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 431644820 1250 431643570 431643623
    0xe04031b020f0303041e0909020d021c0213020d0c112e1104170304050f040b040b0d050303070909090210050a09080303310c1703040b0d02040e06010507 67
    0x200904220869400b030010906580141e80702d650031071125024017088006601000016040090041007205070395000030f0040814003002030b010b4100c40201101101d031494504403415006800b00003c400c40300480b000a51080e020310501510f40000200100d101c3d907036648103050301c60014a00c885100002c60544580198404511a0000c1c0790000700c0100d07000d44000d0b5041e803c4100c0d02e9038506000c0348040c2c40d05070615149a0820481400709a8542c010741801500641c1c0002d00340c42c602c1c000c5030041110010a80e4040703402c0d44e6410400400100640c402c0000b43d41d00c03840319603107403002c5c03040d500750140080d8050402c0b0040307001d4520410181005602900c2c02c201890395403c1a54210b83c003d40d03620303425982640c190709079010103094180001482c805070b1001c0c02c84c5515034401c15801c40c0100c80031842e080c242c48140040c00c00948015200760514955200840540381000f58003034030441004007070b03240c001216580a0000d0707030401e030b4001100362038807600f500314000740c0341 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 431646070 1250 431644820 431644823
    0x90b0a112106130f050106020d081b090d0f050a060b0f0f1c0c0f03050618030d11130906050a0501020c0d06090317010e04062a050306060d02031006090e04031b 70
    0xd20b03070405803145600f10700a80441c01c00500000030554140710380241040340c400500803d0146060902401541d01c503003202030b518403d20300341e4a4036031742c0000600041a111016081214400b4400c082c04070128075809020b114048c02c0001c181524180034035610380045030740c0d00560f5080b40003903904041c42c0071485a4001c00000e0300070581691150612540ba400a00190210000600802c242017080580208448100d0f10400802d41051956031107013689241009881d840481410f04205e010b40c0c01c9401429240104161640d5002d0000c100a205440c400e01c075401000850b940046041501c0700d8018017240040803464903600090800700004500700114006699251914241c65601904c10344a8865a504242c02d0440075912058404d10360900101c2008078800d0803801c600c03c03801d4185c00d0040c0c590b559100016018041c424002141c5400002003000c15114440c0b4941642e160b0b0720340951441e154a8400c0404000316801000f02c0d2150100c1040191014030500707449 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 431647320 1250 431646070 431646079
    0x24031e050c0403120206010303020f031801110a062d06080618070e0423010507091e09050103110909010507050706020d0f090b06010e01020f0d050913090b0a112106 72
    0x1943e00d584060480300007041201c01a003203040140105941030007140c001c0300d4190011801c0c40c00e040d000c6004100160611410300100c0c2001c1075205200344001100300f030304800d0070840403120700e4000b95203041c0c1d6500c0010b40c0308404c1901e03006c0b42c000e219050517a5034a20041c0410fa80744074400b4a80300815840050300d100b03849001450702c450741070040c851441221601405034081c3c249035448126aa4401a01d03410078040118195202100c074084076005961060413402143d038083e007403042901320141c1d8900301030010090140c101c489022150098544008964680000500f2203406403088000a5030800100012500a401604200f080d40200150040c9016410000c07203407407440440701c0b1003c41040010540e00240000e400c1d500a0010703029424045114039100d02444030305009100c1c020486001030340340e1449654132000c941c0b004101c4080242411a94118200e409100840c20264441011400102502d0702390b207484040307480f8411484103c1d20051001400395400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 431648570 1250 431647320 431647327
    0x2070f060f020405040f09050c10170f0906011a04180b031f06080a1e1a0705180d021008041104090f120e01020a200a24031e050c 57
    0x8186503224034001040c000720010780e99481c01007488161003a200080c500d080c07420103800045500410b0b201d0008408850030712030091050000e43e5200001d00400c80424007203820000001c4e40e85240728002d008079821504a60707030300ca00048610401c2c241d80d030032142d000d000c02c221000c1400c03185200206404800304131048400082803030008401e62020003210465481807104030035200e02800390600c01c0c007a0003504059200c0c003020040700f0031082c81c0d000c003101003801402900e840c0f20140c07983c01ca142105905019000800c03a0700042c0017040d282d481021490024a0540c0f008404c0943c0270f03055440890200d10240e42482004000380d03418005240186195a00c40c801c5049203486803000003200090f906003c0103043d929041c12040c480048881525a0303000241d046410790701900c2c00314403498680d41040c14251440900f900401c01c5500400c030500d035501007074044215144c4213683d40c8e0380e030803086054403903240025007410548000180502500c1d0820750b0301819a0070340c20724 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 431649820 1250 431648570 431648573
    0x30f030f0509010b0109090501140607050102040b0a0c1515092408031b030a0e1504030b0709030605090a0309140109080d0305091009080a050c1510080706050f03060402070f 76
    0x1034a000b00e5900300030365500d0070414415a0072030203000c01352181c58020401d6604000003018618a881c810a20a21012454608016007501204c000e00500c01e2203580310303095082d01425420f20701004903250802040c2ca07c500801d14480c00c0804422100035000703c62910403010020500940461500d988585130305c03185840445105004160450055540303c40070705141494420703081050003070f030308100003051005074040d0414120034003ca50142e4010513807000c1031440e00c1664401040300c00511b08006989400100c0b510440e07009942c18410b6544002d0281e40300d003d607180060100c2c04000081c84070445400f10305e0020001030400130725250b2210b204d01e1602c1c00925510f00002e0b100d07400c11550160a20014480140c003180501880400c1d568190f81e500440303440c1010000041040280c0d41380c01c05c1070044007500a9411000c60814502c0b1407d0510b40f4000c5924522412038000361130f0348203074101c13004500301812003419500d880003000080e502965040e42c0d40d810f903050010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 431651070 1250 431649820 431649851
    0x90501060803031e09030304030e0d1515060503040512030a0e030708070c060908030a0e0103090f050a12020a051b01230301061806051218030c03041a1303030f03 71
    0x3009048070000031916840c00c00d95082c101d0324a4500001140851800d20051204c00415241c009516007021030243c014180032680704c5540044c081c007100c60019822042540942c0034900090000b07031a410066112030098815100560f002003a0394003401c500b03149140020301075900480702c1d0502107190000000b0140c5550070503213007602c05500c0003400004001c0c00c1c1207000010702aa0a100e002d56141c0795000b901da005400d105001c0c000700c106c50707120a0b88254002c1d0301c03c1d40d0200c0c910740a507000303090140c0d56014a043c2150b40854000d5294091030001a003401ca87da070250080080782d040012501034218082e1406040c04030708540f0b102c00c60a440320300d0009481b11138074541c0700d600d40480200301c01c0101c050641510302c190400e01640c0d07817190803112041c01c034500c407008680b503540c1d8800f9079050f2041c8a20031800007041100c112000400100201c1c1d640e00c1e024042602c11206c140024400d00f24110100e16040c002000024010141c0342e0003c1c130a400c0004c0d04105020050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 431652320 1250 431651070 431651081
    0x1302060f0c03030f13020a060302070c0e15180c0418090203030a02030a0906050906070b06150c0f010f0b180a14040b011503091e0c030507030c170102030402030709020c01090501 78
    0x5541c076401c0401040454030401c0301d07050344940c0c8400ea40ca60aa015004210095024010241010780000b002c40c184510074154500500190b078003801907180100305e015144a110300c2c1c0b540301e03458540150580c00051544035000d800c020701060b01c0c162a1401d40c0b074941c0c00c59900303c510f10345c64171400307800b51b5170600c05810b002065030045c5035109500e00780148100760f1600158207001041c80a52001d0f2201003e407160140e00030b0400000f500d4550000700b940c0611b0f294501080b600042e0703400e1400001c202035030745c004035400074000c02e4076501080d4280c49210009980040740c0f000d0b040c522070b0744111125000b949403c80000c0e1111090021441001c0c1201e0070745007181000010031008510207504010040180b404010303a0050b550384030842c038200c10704100d20350010080d641c144000c4d054014000c4d036100c0b0485003015600d150a42b4168000c0c402c0b05030007a03a034845880c21160600841c0c5c41140c0c0100a040c8943c1403100310030007900052888070140d961540508001002445007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 431653570 1250 431652320 431652337
    0xa030c12031a120132132301090c0902040f08061e040f06090f0201260a0b03031605010e010506030d0c06150510030501081e121e030a020a02100b0303031302060f 71
    0x5e50310307040640e07460100c0d1100281150311340c9410740071000041200860300c04e001400e20f601d4403028844030080f00740582039080001e40440c013030303d0b40087c4a01c03081c0d0041c0116040d0030f0108905a90344d61043d43c0311042120882840f060020300341d0320704550f503d4940d030b201e0301c900b60f0030740441c00d42d41f119821030f5443c4c80e0807901101c451a41c0e606540c0c10603681c100302e618400210b4200c0c4a5003081e001d41d200054142c004d0300f522249038845641d42031042c5d41d0460843e01400d0440956800d105010f0400f46c892200305520b4000030641c0740c240031440d0350a4120503100c40710030a607607545940c010300c00d000c0b48610400d5640000b1845a80d5240002250840c6640c00308031941000d8030b40c0d0038490540c1100c4412000c102c0203628881d00071601c0c00e40d1540304100c164803050a520105a541b400c81004080e840000040250040c1c00750f01418542245900f11000c5400716400c0a08480b03042d01c80c0d0358140d009100203000b0f80c2400844001c840d1028140c03d00300350241302119480c0d04003210 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 431654676 1106 431653570 431653631
    0xa02130e071b2901030b060603240a03021c111909020c0f06100e0708010b1209010b060a03060603110333030a030c12031a1201 56
    0x148400410024140003d55544160303c602c0801e824042100d90500401c0800d80908140041e2803090b020107c500c1c007101c90500f00341100000070b0a00c5540280e942c400400140c03603244000f480440c0508200200c40c0f04c84c0f40a46030f1880c0306100d14052841a400200700800c001444000c03140c074144016036490402e05114201a48050300c0e444911070b21013070100d03e80018010204541d00500c4219280d294103404450285080c42483c4884100b40f01d604224800d1500c01c6411402c90000000c60322818000b00c0e40c00d40003c00c489000c0b03a980c1108229058150040000d1070305003600b046d195240190302c0070240302c000401c0f0f454115044a80c2c0c8940e00c0b04007000d50314820002c04886184100d4640100543c103844801c03580d0200034507000c1d82050081c080d90031001003848600c6e80c1c080e41403003427150414141c04e41090350b40d201c1d0b4035440d00740d20660505081140640 = true := by decide +kernel

theorem cover : BRFrame.Cov 431474820 431654676 := by
  have h0 := BRFrame.cov_init 431474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 431474820 ≤ n) (h2 : n < 431654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
