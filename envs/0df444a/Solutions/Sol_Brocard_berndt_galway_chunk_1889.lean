-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1889
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:02:38.145541+00:00
-- url     : https://prove2.me/submissions/153f4ed4-30a7-4af2-a8f4-93156c9273e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 339568345 ≤ n < 339748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 339569595 1250 339568345 339568391
    0x140c0307022b08070c062408010509070311041103180f12090103230a06030203100213090b061b0105091509061b0c160305070b130b0c1914060c0307140306060c01 71
    0x101f104815800103a5501c140b24141c89007070810085d02c1d403103041d503036500b02c2c42e41810211944582c4400340a1490480d010045000b0000340c400c0d80d00150030501801d00b441c5100c1100e0384140c101c8115604d004131004100c1d1b403d071000340b80014504083c0070600ca201110780c003c18441c1c01d4200200b2070200000c0e0310601c00c1d170b03000702c0441e0a8585020305440c160b1240341100b5106040c8940700700400c0c00d86030031443e0342240042c5403d04042e91402811205084980203d40b141c0d1110113024081c07405100040a220030420144e020b45814049690340d40c101400d10b070f00da00c02c1009021422101a01074440580380007051750074498040020031002c10290200783c0e401d000d10400043e1110b85d00c0101c8240b83c90308003071040b03028500300c5020341c00c0d00006c880744014000d0360482425129021142d101491065000790b442600e1b000281d45012801031000d00e0101003003003400012608401d10341c4038080c4c80381040d541d035601d207008503440c3d00583c0e80ea8211b96081c0176440040061007003207100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 339570845 1250 339569595 339569651
    0x2251208071a0105130f020c010510031511160606170304030308010807050d0b0c0d020f07030305070c03020304121a0108010516020a0209150103140c0307022b08070c06 74
    0x3101000203201d00010034001e02c15191700ca001141c08568002c074503040340c100480d2403c0f0042c104006248a642951401c44801e030383d050407240d00303000b003004610032489c60300c11200301003110714144a80c180c031038403403006402c42202903004101c04200c9141c2241014101c81210346950174002070015a880c0c0080c002100403905d401c002140e0f81000149410854200600e200c0140205458102e40204007608000045400300245010410035000a11b080441c440e446541c0d21201e00340201191809450300e0100700340d18820f04046580007013600d0544010a20b00d6810780180d2414600341820000d001d00602c0141d000000c4a45066120f80e22a80404448041a100031402240c0300c1c030050030029803050861020070f84880302030290494015040c10000391000000c0c0808090110407180c0c101d841200200304a0307145e505001c1064100c101c0003510404e044980c8003825041c142c4401d650402140c200001c01715446001c10340300c05908498200102c95400f03a9829245040c1d4148030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 339572095 1250 339570845 339570863
    0x4050c0a150e0d05060601030203090709060605040515070201170c0706050a0603020102070b0f040b1e07060e1902030a15020909040b0f0f15011116090524010225120807 74
    0x118050800c1c0243c40e11159111018000c169290801500250005403c0c4034851140d80d2011a80b04118842e40c2c0c00f51102c1d49499031a98a803100f08800703001651506040020184007550042c1d0308000ca12203642c2e030007039850003699981c22110030280221040074001078101414010155040d0f0b04c0001503038001e9080c0c0b00042d480e010b81c00c2c4a481051034400641a08100c2081402c5420380502600b00d4103481c0e074224450b00c00d00c0c401c4582c0010740280c8421f40d650300c40b88a0070030104516080802c042420540c0c078130f1183c0000303444660140300034107641c12141c0514010b8643c0d50480c2c03031000c0001c00c1c0384070702d08003410180c0f1400300860300d8180d10782110300803c00c00400303c00ca55204a14928801000c004000d004484604824800f40e2843c40f0304e142c0d14811640e502164009456469000180b92502030480c10720007100f44488120106040400b2a0a9034080780c0302503885291507c822551085404280e0050007660006415880c02c42009040008400040c220940500800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 339573345 1250 339572095 339572117
    0x140111120115020109170d1b1d030c0d030c1a090604120e0f010c0c0513020a0315050a0e040309051509030d08010608060d03030e01051611030a0e0904050c0a15 70
    0xd80c205c9841c010050a455480c403003442e03034100500010050302c000c6440100700480409042509124440100c802207425280c8a50252962900240c16071808030024104c0708034620204184186041d405820001001000310030711021104010071407490040401c00761401c2c07040192145000d460072590440701c040c000400511862a602c21000001e21030f0820041c864019210362180c00f0044400201d125030001e07071076a480d10b4020031005181c4c0d0140c1c0d21661220001c08071402051044244081c1e01414130403512039014620940d01d4444d0a0490fa0f02c89040603102c00459921150713001e240c09507450b903405203150141071240c109070100d8004100d0b42c001685d02030824040d4100092900b80000c03a0740ca84210004100d501900740007500d0b1400d01c10a500b0740d070307003211410758000143c000380442c03a07030002c2c20398a000007540c06907061280b03100004108200400d0103921580078000440c0500c101403065071a49280104a0078250343c1e9440004c802107040c1c1c20b84400b0640c02011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 339574595 1250 339573345 339573347
    0x3010303111b090606070203100905100e3007050f07030c0e06091611061f0501080405030d230f07091401140a03090b011d0a060b0304140111120115 65
    0x40d2100341e842c01043e580080c1d07561030074450f0a800c50074059a040c41101e00380c814610aa11031030202e540204042c084401503402c401003502c01e030307114040c056404031240141c0760200d04070b11140c0040c03121220040400070000310665015414001d0194041c114142054180000e00c08044a00c01c1081d13201441c1d8800303020034840e07401c56540d50004c01c2d0b03a00150306000034920701106180300342404941403c06680d401e20b000c004640304e0b030030000c070440c4c1c0701000301c00c40418800402092801410602e0035a94058607400f642442c5d802c400e44079881d201e2041484e40501501070307803550082034145001d00c4040400c4806442d4180828000300002c10303e4075480302c0340c0c201d019060311600460384102a034821554080302e554410950f880d200c172000900409001e5000700400000c1c4c4260455070803610140007000b42c002241949469002c0120a0010090303035401604180a030f0002d00c0f0b2402d01a02621400c0b800801c003640000d2a051780150f0103007040c3c180c03070311400a03944080300400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 339575845 1250 339574595 339574633
    0x509150a090b280c091706090105011707060e0109090f050712021809101d01090c090f0b1c06080a05071e051207050d0f050c090f0c0a02070b0301030311 67
    0xd00710f01c003004840c500000e80b140c1350400b100000352841d080001039a03a20026040207050a40315460342c108400340140c20300c0c01d0140da80902140070002c1a80361600d0b04490f030301d6030315101350340a010301540700104680c010b1031084020005820305110706071104d0703075242c004c1a045902c10041020100c0c16a0009940d10136945200404494031414485150800c44034030301c0107092001001040d0004650341300901115032400001c0ea1a0000039418100c065095800549001c0108029920100550741483d58510225010030782c139107a40f0026108210280980702d020115100c0c1042d2000450b18000191025968000c0c02034410b803603101d9480b1030f00e00c180014a1a84000c1c801424811490422032404a001d0b01c2003c4406207a52400400c62002030104141c880900c6038200400f800800e204440c91902d04558034161881d20076000300c0c0070340300508240802080402c080c0ca619000b0440803018000501d40d4a0f140e69403072800070800c0404040d40d4541d80141c03500010b038514000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 339577095 1250 339575845 339575881
    0x507050d09031202061918050f060f131505061801060f020d170a180b0907090b060c060a0c02010e0114160f022a10030e0f07080c040509150a090b 64
    0xd12440b125103c494803d00181107284400e881c7c00d04440801000a0b03020041c40c00941d4003503000c1d10451034914280803000b0300c001c0c64441341c0d24410b0031080019055100c0980b800743c01e8030002602d6103448020451401c071040d4106650301441c000403401d04d4201c0030382c804d090325990031074444544c2050100c82c003086100c4000b40b01102c110200c1d0304d00b800e43d0003503c1e404400c0c40203c281034801c1c2c1c844244100040d2240c0c0c01ea500320300300c00d000075207542c000c070207200c1000d8550380d25000030070000e581c0d80e043c0144030b0151182d440942001c800c0c03003034100d000101d04c400c0080c0a09101e95450500c0c0040c140ca030406120301c0c65180409050299031454240c0031190060b00c0500c800904840710b03005c60480c3d60780381e0859050740390324030b503134400b01c284104070560f03400a21501c2d00b01c01d0030f144c06d41c1d40012003600c1e40300020070444e200300043c19651800c001e50300440c4a45419501600c5e2007009074190325280c909000304140904107510122200d80500d0954200d500d8142085410114034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 339578345 1250 339577095 339577111
    0x2070305040911091005041a0c341701140f13020a0e0a050405010b0102120f180d0503030708061e06181509040506150405100507050d0903120206 64
    0x107000030050003405a1100b128148600b40d15442c1c50f034940006101022082c0c481c40c0800d40115091007682c1400e01104004000f0505003807419115070b480031303030f030310003041c100411380c0c0c41100b2400102410344822900d09811400a003a01341d1109a401c03415500b40c91401c1c4190319290652414103503002130140103040c680a04031060712081c002c40e903150403100080c4d0300a01182000248992856041ea220312484400007450307041500d407460a44030007030801c504642c400c80600200120200c101c40c1ca80c5401c19000e613407150030060300320507440c0003c1c00c4c03684890001e10b1002809030200c00cd43c400d1b1040d035202241d6581e0b8200b040300320661106c40c8445c0c0c1304803044c40c0d003150509800405402492581c0158072034103e0700055071000d45560100c842e0580429004c01030b06050050300e800540441c0c4503203141d15000140c0082303003e18480c40384181c2203552407010607070150040f00c12040c0c0200560701500310704440501606032038070080340c003c446992451200d40c808590b03e40076080f0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 339579595 1250 339578345 339578347
    0x102180a03230f06040b0601021c2703080a09170312041e06090c051003060e07390c05040b0904081b030714152802070204021606050a02070305 63
    0x8008109140207082d010b4103030749481402c0c1d4520000c1000c1062078819071140704260307040e00d0840d00085c05c1408103c040c050001c102d42c4010403440e046003803151b0311144940f10081002114081031183c1d078466101400203203001a003015402e40c400e0004c0c1c2a150002961017a1910ba1443c503643ca11510468601003131007080460f0005501140d2900118010a0203480c5110325032900070403584c41100032658010401400c00807400d001115503201911810108542460900a02080c040041c015400c000381c0401500081201c602003003803401c1000781d0040b00021502f901002c0708405a0151000f0301049000502e614260041c00b4825801800b01426034446954506071070700a000518005220446815401c42c010409005d1550060f41030702c0075032070245242800e100040d034541070240d00306801c201500101200001c0641d02c010070b00d0b03054500440b5260000d00031a840294010b00006001444084c201217002800d40244001c2160f5241c240a52040707100e52a030060129030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 339580845 1250 339579595 339579623
    0xa1b0f0512030d020a03060b030703051f08072112020303011e141909020c0a0c0501030b1804051f0c030b06090112020c0a050a0c0905070e15031503030a020102180a03 73
    0x4651300500554401350078007160340c64aa40003264560000c8803500002a070318010045810550808901e03050103c0041800083c00e0424440c0c03030310014000c403030051415801500804900066940d805600203540d0101010300120017503ca0340280f0640500751b40445030290103000c01d4040d00100d40c0246000d8105035041c0044c40082e4035850121600070401035000103a40409000070160b042071078029020040d4030b45001c480f041c441e900564100b40c905003441d5555140d5220300b10400f01e01640048036582d5500e412494581d14007100d8200d002d000100290440a0350450141080d070340d21f0901c10f02d84607205000007406005941800104000c00303a11403284150f00900c06100914240c41100390140c442a14004030404100c400c85001041080010054425181c1080c281d01c1e00c501811841c40010740000107410044500c2c2c04000f0104017500703148070800c428200080d003607a880f10000c00c03001e8000e4000c2801d802400e03142026113191441d00d03044002c250703507018000c0d40e4030007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 339582095 1250 339580845 339580867
    0x111040501030e1f02090a090603080912010228110615010c0609020a17060a060617070e030601090509010f020f0a0f120911040b03060403080708090a1b0f051203 71
    0x403003a40302c0c4490f180a21101c800c6080d90328000078441500c06030700940e17541c003580c1c180980c0e42c545501a2400900c1e00c841480010440070803210028002c980000c00002d004c90011b009200d10284807006080081b8458418004c0140503030400c0e500740c4a0b0f078151100890629245c1030101d13955965084c00301070345403003980a945c500c11140d018090000f0701c0e61060740030401c0e048160b000300c40301000f410030f0f900b4410b500300f01c4c003617000d401d1440500c122890309102070910320140c0f0800e043c1d5003031800045c103518400c0000107041c130001800c40d00c66588d55801700c001000103442803103465080c8030000440a00a000710380108404055291801c02d2060007141c000c0080729408080000d00c0d400502d40e50a11b01070b1300101401042a0704806100004120482e5034005c0054001c0d00101c08100c00b10350440308142c4e00c002981490040765984884007420400c064030002c18282010107680c0100200a02000550790410041c1000d1900c0d10200000381c04001c000a44507801000588801 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 339583345 1250 339582095 339582101
    0x501060905010e04051b22090219020d0c15090203100504020a05180f07090510020d08010515031803040801150509060a0f180209040603110102060a022a10020a180503011104050103 79
    0x80c00c940e40711f501c3c0c00701440b80c60001e007448980c0891042030300400c6581c41d801c0a40b6181ca08001c1e1800101a07403511940c000c2c0c00c018000134007a060b000404c40303203070010700c0d02d42003901c0455000302170710840e60995411200074402501c060b80140d90b107040124840c00d003040b01a070f41c0704240320003250700c1e52000040404100d000344031108200079081c0006081e280c3c2c188440b0b8a07202500540703c2002002e100620742d8005900c120304ca200c0c4e8030b41d500d4003c202078040340e0b0040905040008001d00d038888092030b5100302d03486406d4540c6451030500d485009055180c05036a003c50703c03203400d51506000c00040d200c85009900100c000a03030304020b0b0458025291108500b46500981880c3c014070006044903002d500c160769034800c8817070008656a050140030385c031401e038000031810700c044d41c5c0781e079509a540302001c1c440d0f010100d1074098411a041200f240c4840d00301c1015561849440001014201d001c4220094105004c201160a05e010701843d00030104060b011820940b03040011000703 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 339584595 1250 339583345 339583357
    0x100215040507050d050303070305150604140102070f0605120f060906120c360907090207020105122505030603030307141c270804030f03120501060905010e04051b 71
    0x140b481503900000b21038641d07440008140780038001550301d034601800060242c541c002c1015140100f003174500e1603039a60303030310503141030780c0c9000000c012200e440b0380142d2030110542c01920890418000018a440d8030400400c054003494007003041c45d0b142c0e09000700380010300b41c2d29254445c4115001807424109803a40f000140e0303410040302c42c2040003001050100c2c50340844111840e001c044c5030214011008102151205504030508013032400030a02500e80f200c0b80502425190001540f2065a10480136117036040e0600d6900d918a08091542c0c8400c0184420394107540228000d070149100e021300183c034440c80010b8051441c0d540c480a00701e0700d44c40301032400d180106060100c003081000050505c0321044030828005000381d4590030126219446160300607c00c40303030401c1000062100d07000e65040b2a802485102a04c920f031070301340e5401d6440000c41e0000b40c945400020300640c402a000e04541c2c0c02c0e00c0d246070001d820700610041c1c400441d000803003a1740380b410212052601071300501c1d03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 339585845 1250 339584595 339584603
    0x90b06040b0a03091e02130e10020c0708070b03010b070b0406060e040b01081227150a02010b040f06080a02151b0a110604030507180f060b03100510021504 68
    0x12030a9240e5021a09a41000c4880c2d40041da840030407004201907641c503109110080d41101c02000c103e41e000810030749070f150041060303170b807030b00d8403440304910070003400c0c405074071070700d801c0d5124225401529070702c07506882144042c1c41920800107103c128003040724161242c250f4074902d0094951603035004003001600c11540d0760341d111800141010312481c150f0040740300d44143c1c08154544011149002c100090825070000d04100208bc07019040c501d0031038000c001141810b0400e45a00081d0b614000080c4031483c2e41e0b00041c9802c101036040d809543c4802c2c2c221010441c000c80312a00d070088510900410409900c40308002c005468001021039080d5030b1218003501e07140391190301c3d0341e40e40d0080c1401e078000c2e4841040b00080001034030b200d5990460540b49503003400d1071340d101d5a45c1c0e2403692064128003401d600d0340f180700c2151030308190184c8001c202c09202503542d07020310655070703031003101c0c072800001c1d1045020645241c00034045402460641c001c0901030b40144c00d10100b480c1c060800c403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 339587095 1250 339585845 339585847
    0x8040602130515030906070306080d030f0b090c0c010e0610030303050a0b0418110d0305121003021512090d08060f060903070f0e07020c010c03050d140a0b01020706030b0307090b06 79
    0x146a40e01d440f0085284029280c0b6151203090a02800c0d1500c80c0c0508002c0070700d82010741c180001100020100407044492030049001c00c400032040005103125107211f60032000c840304001540341120000c01010461000810078000c1d030307a07801900c65209441c042d1001da512203080021a120307030480740d00450030b29000902621580e00280484034016100e091501c45041c0000500990a10b4041c80328001d441c4141d22030060b5400407d40e00c9841c12007180e41d2101e40206900c012842d0b0884003469002d41403140c110310500a443c51500203081c507a007100c0302000000d40c1024049405241204242c413a00c00c245c6892041207003010b03000c1c1540350042c038103012b0034002c4e50342002a000181801c001e41e41d121403d01c1018410340c00b0062001c021356001c002e42070203599100c1d9203100c115806107056034480440b241054050042c050504080d80703925014080d401100340e1100006000907002c03105815543d607020790a07075110512a0303a042d00880d2003004803900c1504a41c6000200819003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 339588345 1250 339587095 339587099
    0x603110103090311010c020718051e2a030f0105010c0b280f1a12030d09030c060504050c0a0914010510030204050307080307031728062d14010804060213 67
    0x580c21200603100c400010b903c40141040328410279903c4580c00f10f04404288028075095014482114030b000401003016200c40001d807810218015880b0500e9510200b1341c000501c407145071140350000e6502d8035948002c2c2d80001a250300074501800c0480d8414403690583c2d840300310380c00c1002562040189048601800f410500c012441841d45181181d400001c1d184a810302c180c4541c2400480e035406554064842c204400000041e90680303c1021000f20310b002051904a9104801420050000781094140300411102080000e5a0316003618428030160b0364110b20780903904000600d0407059082c01c014800f41c20b001c80442c04018aa0801500e0b041e0740300d011929040150b4000d020541010802004140d4040490708416003418109501420007002881d5071004003001095030300302c00492046110000c3d086100140904028440030046910506d0840d1040c8e000038110450204c0f004201502031001b90066a172040e90303080c690b55560398602d0000e50090340034142c80d00c480c1d100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 339589595 1250 339588345 339588377
    0xa02010804021f08010305010c0207121401020f03040b061002010c0504060809030712080f060411191e03140f0906010303050d110315010210061404091502031302100306031101030903 80
    0x244142d078a070ba03601e0b2211907145046c07c500f101c180095100854020030401c1020002031642c424189400000e002c0340d540c2c00400c03080c024840ca800070081100040204014068825101b0384103580c1503851219405525900b2404c8030341b000500004504203010174050b9a218400440c0c0c080c803035104480c90560662940070369a030222404a00140300402001000034650710300a8018034280c41c01d21104007858681c44150054240c044e07041c08099080765110f5100da01052200280452007402a04c0300ca0001406404284240e5907042c2054011410340320311844d4280c4954440c4018003802d90a643d0111a5540220407501c01c591b01c50100000070028000214014035011246c0010664000006401c0001d03014000c1c0c049464072508201c403040d0000d0b102d44d0445d044800207009211494110498401407848864281c4040100003040c030400c020900400d0003203884a0300591841e50460a564080c0401020303c101849082c80a500070740016049034400c0c1081e160000c0c0b1111 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 339590845 1250 339589595 339589639
    0xe1204180905060a0c091401090303050903031603030219090305031209120a1e080405060106081f0b03010e0903032206020c0d1e020114060f030a050615030105070c02030a0201080402 80
    0xf842c095501d17950401008182c1e00020340a0003440d54004d4125600c80040c0003904a084600c8081c042c040001180344207584d00b0700c202c44042c416000240d0059a5600740100290400120f00072a4041030010076400d03070003075120000700d90307101008614220f01e006078003180c3e110203020060a0701c2280c80c044003681c03410300645210141c644c0d6149841c0c403080c80c550768501d400380703a070760501010100780000700300c01065082c15101142002c8a9540b2904682d4128100c400c41111103000415400308440113101c000b107040b03424071206080a9114109155101d10042c1d9481d10012541c0800e8400305d13a1000f000e503101801041c006041024400340d0f2800c160441d10000b00203507942c04c0d0340c45000b203102c2003004080d01754802042100000c0454903280000035100034800e05900c5041d510f103aa0030400f4280042c1e000c015101e1908000715000d10109410072414880d50900b000507014138802c180328102d107a00240100810072803a00103494040c0c02900c00d0781c00072a48102104d40c0c5103904 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 339592095 1250 339590845 339590851
    0x40902010e0a141011060f04030e0301090804080105161b08070c1503050a0204050a052101020c061005010e0f0103090f0605150301050f0103120f030f0914010e120418090506 76
    0x30070f0b0b410484400300600150b00b0f5990310f05003c4820400020b42d1400200c0640c00b182c0126109016202c0d400d0a41d591785400310050707815820000d800c000c129813107000d0300460340c40300001d001c0d070f456008114135044113411480c070001d04c0340406803504e03045486108030000c1c0100c100e81c0ca402000d885a401002c065040100c0e2400106042114281e05118840d84280c584c0b404508041c14840024000c1c02d40c1d1050b50322601d00c2100c41800c6201e02d80310070901c043c11000841d612030b5851041619a41c08848115032200c51260004a950268901d108100e80007000340c43c501c68110015402451200403d6410703584000305036000420324440c441c040c148002007042d1017800b0f881054203549004006d004a58024001000010a009120103281400b4184041300401c003100c101c0c0203150400394804150b0030051340005001c000f0a201e10a240e1520082c0011410346424503940d0050034030102001008000400140b0002c0340410101080e103a0701003002c011035120146080025 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 339593345 1250 339592095 339592109
    0x503010c090302090f040809012106060c1202030703020d03020d1404080322080d0b06210402040606170a02090d0812101a03040201050a110a0f0b0907030f02040902010e0a 75
    0xa440c02d1081d803400c540420740c84140e000503021035207807039074039104a40103280c1618144a10b807940004500051074100d0001102c8450030001c070303952400001e05100c034840041d02c1e25040d08482204103032002c42100c05103a00368000f0403180c008100d084009521142c00e41c00c0240ea500d0001c804c80030640b8406010744d000b83c2e05241c49013080124845450505100d140081d2400004440020941d009035500040c3c0ca5100280200d440c40c049000b612030b90a040620038450007018945111039400c03c1e002d903009a03000c008080e01c9910590f500c1d00c04a031800406040c020002d001085c4540060502d90005820326141d000c6a80d02d070b5007580c002c04202808400060100a000c0f282d0040920003094502d10202c4000445003041c487c40c031002e0006030400c072001808590b2103002c0c040c50260760000c0401c49154000c85e09040161041215080300c82840303070400300d04e00d140d0010f440415a500511203880c619020342c01c00c002010a61000ca041c014000c01c041102d40d07603410508018507071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 339594595 1250 339593345 339593357
    0xf0306070e0109050f03070b030c090303070c15030203040f02090c0f040f0302130203040f060218090c09010e190504050a0e0d0914180c09010309022701080a2105040503010c 76
    0x480c1c0c0003422103107507900320b28000d4480807000c00c0255000108481103880e01b800700340d40c1c0d03222921520200c1c0b00e5410026018440001c0c03080407c4030100c28802201d461500c05002c0507a0403404509034841a10040c04c000c4c40a8507400161812082da103810141c0706c0b06175441e0002c00105d2845e19001541b10703150240301044200151300303008903a2080105c140c20f0861035841c259a41000e41d00c4002c1020340060b80c0807c002114040303014582120800c020000440c40c40c081c60318074903582c00f00300c5a5000a6080c0048115401d0003618000c40903c620300a4040d541007070180700082000500364051152201c200702403280c4180b11100701280503550300400641407600c0850401d036010b01050082c410319440308006070200d28940e4000e050130280c1aa65500306004034050011204065440441520300480347c2000b07600d00c5014808513034034090340d0fa90304d030521500c610084001400c52041c112010742e00c03c5599040c5034445490f41042030a29031500003090850324644544004140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 339595845 1250 339594595 339594617
    0x50703091103030f16111909140108030d0906150605040f0b0c0d120902090109050a0c020102120a020703020a050316030e0607030905151b010207060c051204110f030607 74
    0x1211101d002103807040c0e00442c07030403c220441c0d041910a000c8903c14100c04144a00c0c03c000e0103690741500c211006215044034401c28404840407601c1b80304141840340f803c108200800c00301d080a5040303c69141c09941420041d44110000d04100d94044074078942c1d0300104641c014400d4446805042c0d17941e2004c2d2a031341401840850b40300c081d0040c8030844401d1040b040345140005880310380713007a64940304090160090426024101d050402503002861000101d18481c040e03204510883e22240c06010507009800142c0c200c1c480c07041aa078250302180c000880c200119002407240314481d2045a101020316220282586c200041d4100d01441001d8040189688460794113010b24040303810a140c41c0841ea00a0458180b42c4682402011001103000c080c200c4007064030f40c3e0350165544078041300115400a8000e50180d503084030014584540759891500c25011303a50442201089080d0b140ca56455682c0c03405500718400ea407001c0c80058000b4203071020300a040c007035199a282c1d075400c10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 339597095 1250 339595845 339595853
    0xe0105040b060a030b011203090e070206070e01090605040308070c05100f030b040c02030a080a1e240317030919031101053702070503040312142106010e030105070309 73
    0x39002d01d03c1404003203420300c0820070f00f00701c071411100c01e01945c840a01d050314082e1410b400c55408822460100c2040250300c940110f440752140485681d042c03004030103000190b4111840b40140c0000580500c424000919103100402406000b01c1000880943d00c00011340d40300010f4849400007030030305042e42c50701c0383c150107044205c2004070f40500540c81105c900950341d0140014210401c40042c000c2414051154049480e031404201c8901c40490854485d60191805122810710074108207660440c3d5101c080d48941a81e5100902d91400211410494074580000d046003c05024100c44100035008400310040c1c80d078400c0d22954016003007080c42508640005149070315084016500e08200005144007202c101000520310304290342d480701c164000d004418000f40140710000300441071000180c00b2040b1043c5c00d40c0e0740140f082d09080400c1c602d000e035000218036a040340c104409201441c1e030303020341c1c000010314040080c1000c502c0002e095840c15522000420b50303502c0c20754248 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 339598345 1250 339597095 339597113
    0x50a0b0105030c0607060f0e12120115021903032d05091f090302010b06030109060e100b0a08091f05090f0f150402010210020711040623060d0902040e010504 69
    0x400c0110090080f0240070340109501d4402c400000303005982d10340e5820300359105030b40002c820003072040440d01c003000801010880f5a103e0714958601c45c540c9400001c81440d05500c0c1d980244556010b00301c0e00310f69904100030440002000c0b000d05880d040d41c0390020241c0400f4015645d040b683c0b03d0909a40b0f02844000c80c4c0026081c10402d81140030011407048540440001c5143c0b14440021058661300301240105271442d5116031224000000080c80170300b5402c0642610002d00180d4941e0b1501a000d810002841c41200510b5200b0300a0002c000d0060f00c4459001c02c0c91419144c115610030310106000c1485800c00420b5681c1c0c20500c01c003910204554000382407a04024680b00e00518010740e0340300107010504014814401c00541164030034844d03600d50180341d031025500d881c0d842c51b201c4a000b9500c4a010f01583c54402c00241c080c40d0240c000304183e01c9110f03c20002c00081d01480350303640c843c40000710340c10344032401040161160b1007411200c050301c00000a860030145818044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 339599595 1250 339598345 339598349
    0x30b0903121033120b060d0c08010e041a04030504080f070303090f030c050d050a08070f0209130201080f062407111906050a030b120d0909020a0e0d0807050a050a0b01 73
    0x1110f000960500501c1c80d440500449521040c14442804407628100f00043d101c01070071300f9080702001c55071040000c4103800c201e11003800b03500c0310b400720781c0c031980c10b204050b208950103040d4800030400320744035440c09003040760064003030304c0c050740b5180e1221940d80c40c0c11424444401283c0c0008410024964000e00900140c00c0e150741c41030001d861a110b51510030368900a203481122206400002c02904029030a86164000d004c03d03294a180e0070030a5144110203001e900030307400f0100180c03d0310aa021705000d1168144c50301d900300e8a40c20400008098014100358028045841c125000c0e8050f45162041c0c04800740ca056680026213410f40b180580a1801c6001e400c40340c200c0342040c4040e0a42e030064884610700103888150050045015007075045a0b190030100312401285540b5000c1110820810b0300d45801c40b06556402c9090b04a00c10422484001a45550890800d14014100c4003010f402807044506048907510340c6030a220100750100d41d02d80c8841c47c0c00080100420306540 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 339600845 1250 339599595 339599639
    0x803040308010e100b0d060323010605011e1b0516080c040c090e19060e0f1b45030f28031101060303031a060310030b09031210 56
    0x581d5007400c1400e00244c440a0003001820400410207800701c074620340c042c80080d41c01c04003003845101c4480100d4003440d10010100482d508200020403554010484003021244100c605410400342d20301c11995200e10f0560480450300078003a05002c02c4080001e01458a01924a59000b83c60103c5213440e00b202200c01c40e01540c1420030a51903e5002403401f002c80758803814894065aa0350001d6210041706017810111518045002c1075a400341c0040380e1241154401d605440d071a40022518001d22008002c10101c0c020003a14103a070fa1001c1c4103500d9041d01001300941042c41c0c0a80018120110121008104021010320081e142c108500b050023070350350029007028010700440c16051178200000e0100c40404200a00405205680301c401400e10400200541512071900802614001d101d030700031007000c020492064600803084900400000a508010351328596601c2d081c0d050040c51052140003c1c4500c1c56210000200c161103540540b2103080d204e41000b080000014031305207081 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 339602095 1250 339600845 339600869
    0x30f250f0f0905040302190c0e06030604020d060b13050c12180d030c090315050106030b060c0303040b090f070608040b0c0423060c01020c0a2009070e0319080304030801 74
    0x10124030100070320710a481d0400d1000c0358507540d90070f0603441c0c9206010030180d0303e03e4044000040c0590b00706da0030140d03801d50a018185403216020540d03120010380f00a9840030b0488103400c0060040d0307202104400c0c0c0504040b02c0300707111240c2c1c90300b11601120020007041c00051100e0b0810300041009034060005050302c0b80410070000000d0761504280d04402c24190349100e4030000c1130240882400965125070710b08d146180701908400503100072300c604000b003420121003803139078605032060700c05d0920550015800d6980b107845d1031800b900c000d010a4082c3c02802450f9044000502044028050545810b0030500701442d06401e42c0000502d03040c80c0c0c0700148810f01c480e01114260a00b50f60341040540881d03c905400260940314180c5003100c0d035032001803085040c0c071011400d40b44540c00b69842c0f102024042c0b4030808000344104101c2d901964a40000d1216070046030b820146640181c2140e48510103c1d140c1c0f10003075141c40d0b06a036a000003000b08400c1551081140740501559100a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 339603345 1250 339602095 339602099
    0x203070503040b15150a03050108010509121e030903190e01080a091b08010b03070801111204080c010515030d0f08220507090213060908060114030f250f 67
    0x80c201d0002030b02c020b100c4203201c004141d00d01c0c4107070908860300600611070780b2244641001c0c45441d40c00000c00380701003810000000359940040c80313801d1207055040003400041107445031019566228082c40000100ac208015100321140c9001d10b104003140310040d07954105130040c5070001d101840c0440101300d14491503000e85d9078081c11154000759045030210f010180742c681483c95070340060ba40c0c280510007610018040405400084086401b942901c1145440c0d0101500762090001c003c00010000c010011140c48081c641719401030080790748a09020016030307001d003540e009407031090121000c0c08404072203160074448848811400e0904004211000d0000391030350350300600e000503e014460b02d00ca10380c0d20a07202c6101240d44902a03400301030321541120000d40000f4550b4942000444001c20701d180513646600c1030360103210040460ba8602010500e1404003400a070f609402000c0713440b0700002007004003040c00c8441d2012003903070100724a00884240b00c55071180002e07085071031003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 339604595 1250 339603345 339603347
    0xf041503060614090a0b070f0605070e010306050f060301030b060319030513050108040b060f010e0a03050f06060a0f0b0d0204030204020d050a0e0d05040902090a080609070f090b010f030c0216030b040c09020307 92
    0x803004846c02800c50b0380d15a40b04e0301b00160400d41c40c1401400190a080030002240c0e030040c12001c500200743c0b01081070344e8540d400d0024007115015a1600190104018008160a908440d611890040440701c03041e5501d40d240c01041030750342c800c0340407800c0440c040d1042d10b651100c00c0c0c094002880c0c0110b8a2409840b2100141c04c080c184034069401c41448075202e9101d40d00610071010b0190450800c2c40d580e2411641e1031204848000041c00f0f254003281d41d03858003d504404440101d2164000f1606218641071198013844004015640c01c03c070006c0162240d0020305480d01550314005103070725200342ca0a06945013041025078a401c001951409260020165001c1d02c1910390b0050702c41820b04049150010103412905135442800d0411101200000713846054400750440106200d6403054070b9402da1301103030851070205a0448000001e81c0c801e038000c1048041c1441158000e00341448200c60244003508184c0350040307020b0400040c040d0781400031004141e05101186107140c141c0f0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 339605845 1250 339604595 339604609
    0x123150d02010201110f13060c03300903020d08010504151e03020a03051e0712110a03080315040b0f01140f040e010b0315120c04020f04150306061409 66
    0x1109210310648400e0906591003548500040194180002e5844400d40d64403101904426240b8a0304140b400021403101e01c154042042c1c1035040e1a01141440c003080602030013900c280000c15004030340841105000007900810300154041d0300500369410f1001c000030450358050b0081401503050a40f5404c03504c0f00042c82e4070484101815074109440308540e19400300308694006035109003143c0011050140109980da5030300650704100c05584054441e9079104c99145c41010900880c040c4a80c01003000d00d581107110880051080d00c10545943d54007031150001d031008221a00181624055410141f04080380d034002161a88070000c0701c900000c004400300e2000c0b22464070003040d07842d07200101100344c030060003040e41520050b60710342d0007090450b041251003607841d08070b502001c03103039007448100c1c031043c0c810b110040d00e043d08941040c0006533001c26007060b104041044006080448660668003c00301580c0c0415510324194006140714107003000380b521000200109255130f41c0d204 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 339607095 1250 339605845 339605881
    0x20d020a08030703020a02030d060b120a06050a0e270c1008150127032402070b01031e0b0408040816080c0d110402072d0203060414010612050123 64
    0x1c44c000d80d83d0000e205089007180135040840049504240e070106150250f003002e08820f0600461000403035641c955104240c07000c1d80f0415400608421042c002090190411580030f0400d54041940e0b0760391310455100710950500307443c0250451500d5000a1034401520b038200555840c203400e01c0c2c2440f081d030210004000c0c0c1600d0600c6441240e50001c10009440a1190300c00485110003141d902e041018256002e4407440c0c480c040c001d4030700e2828140501c00c0e9444941c214807606c80c1603085544060700d9002c0b07038192451041c80844a140041c00500207684030324810307480c085e1900e14000d501d915280f07183c81480300040300e4402c2801140c3c0c00141c4032041460888140300c4064281c10058078400c040d481d040d40080c000100c984c28442ca000d154800940d02c00050255403c448001321180000702c80c0095054000d500468042030354402607407040805071000140b0941d840c440c00b11082c21840080312071740d4407000710040c800c4082180e5918403c0d4618401a103240100d00c442e050f103649 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 339608345 1250 339607095 339607097
    0x9060d0c14120a030815060a230f0a0306090b0301020403021f031b080603150705040303032a0c0b060f011b1115040513090201080c37020d020a080307 66
    0x64001101e0a507581c0d4009110b625207042610802e003002d050041c443c020440b803158001c400c1e52065829070503c04101e4461000b91390f01c00039145248c0c10543c0c280d800492810036030710801d01203400b61019240007000c3c48049a2000210149030a1805064543c111285446a44103100400c05612444502003250007144003488403031f00c0c00c0c3c0701907001f0a00c050142240e030403000000b03955150400040f901a2604408030f4044400c2c1c0701c00301c40a500300319248000600144010000a806504108600e40c4400003202d80307000b040d900090303448c4240710b0240c00100009140d13018041c0c0c0d001200e401c180c080d40c0b0010020035110020b03101600b07541501600e1910119100d0a01c0881d4481c00709100000b01542c00e10959543c80c140342d45c00c01e0081300c1c880e82d107410604940791000d100c0c40b540c165041e16400c03025035a403201c01b081c5400c03c00c58491000000c6000007038860b036555548041c5950400584c40781900840002d10b09100307800c5000c01e6510007452140452118025640d002d240d13 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 339609595 1250 339608345 339608369
    0x4151203050a020313090902010809010603080a0509030309060a0302040e1008070303080c2701110102031614070c2301050a02060a0b010e031c1713020108102309060d0c 74
    0x1c4070030120310b10300c42c1001c00b031051035074000302141043d81b80c0c00045415000366554030b29512020107513400c96032207200060a01404104e0210b81500800161694100040659081480031404619103a0001950500082d80018103006d40310080041d03680160341103c500e02010700b04580103540b9012400081d041c00f2840c0d0000701386540700b50442c2c40c1c0b4001418446284c43c94201103040702c0700844541d41c04070f60740b0035150344c100505100396403060959078800004c0f000c244105641c040040800d1420480040000901181030700c1c000600400740f0031500340d1010b180750740c52004501c20706a06410420f00308180d011503540012100d802c0241c1030303400104502e8580050315845050749880d0f80500682c2500010f504061101d805401d0241e154610310a841c3c040751031000d01c00300c40360110100102a043c01551007070760302030b900600311980000050780300c0444000f003580381c0c0c400d4002078404000159440c1002c1c410f243d0829015180c0e01c9540145070b0740c40d904400c403070003030710803000ca = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 339610845 1250 339609595 339609607
    0xa08071823010807021b0d0303110a0504030c09050c070204050c0415030f0c0f0f08040318080c040b0405070522030206120702011104030c1e230415120305 68
    0x361806642005011401c651041503078010000310640d1640111140800c1c05603000849103400480c0203805940151340b141600b5044808108450356001001e404060356078588030a8441d514004000e210b1564803003a13111491480c003140145050b4200c03c0e491803c03c010700554206050540f41c115504071400305659807500401280c50290350f001d043c0c0c1203c03580300d03110325503090b0384034501c140c19000c1c050120411600c401e966040617691400005450b042404000903c10304655403c24400d24015084642c21546104c40041a400c050065003009410b90840c3c03800e0710400d81c4141091b2814001c600c5c00d0321001e00180200780052040641290f00f0744c4604d031041012101550380140170ba0f44030070541a01d9421040219a030401541c0391104000407810b00c1c4c010f4400300c9911003104000c0c581424000c52581d00c2048a070400600c2080c008103201c1090102d540c0c81c01c07450105907140e09101c0c8100300a03a4a44503000e03010f0007107a2024000d1503103117510b07400c1caa5003505045503110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 339612095 1250 339610845 339610877
    0xf0a05150a0908190216060f08090105060a030b1504060f081606080a1a030709151a030a090615030803070e01080c090603070c0b0103121403070c03080606040e01030804090608030a0807 81
    0x280041d546c211009181a50220354a9000b0349410680185581c1c1c0001c142e5a079951a803c0358400e90700c1641c40142190f0810000f0110303034025601c102c100781117005a1a030340c00490b0a68045400c400040c1010720800c2c0614001040b00c07100003600043c030300170524905040585035400c00761004648940b5040700d0400c00003103413018290390301c002e000c0b11360065851920000410000b03a15060307484000c407001410848980c109400501d0a910b0342c2d24580b90844031301d0040064100c11604103443d1003640078030080c1d085000b001140a80d03229507480c40d100c070000f000e0340203c0d10518107215100041c0480c400c600d50036106006019115181c0e00d45a4607400c2d07503501c2c1520001003007060303c0d200110030020100c420080c13001d8940c0f01c000e0315948110109420b4041161920000b4201c900048080713807242c8010b035000310000d0103040c5400d49808892105185c242c000b80d6100318001410000c6029030b104200003032040f0405113045c00c2410500901e04003024003428200b04200c0c2d00d4406003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 339613345 1250 339612095 339612103
    0x604180320150108070f08030703021b0a05180a0506040606020604020d1110050a020c10051801030b13050117030910080919030201090c06030b030307140f0a05150a09081902 76
    0x901c08802580103983d46913000750b650040d500840482240d4160001141e800020680304142c1c2d054003e0316a0f030694058010303020300180503503984070031002400940d03078891000740b00010002000c8040e80f45004500032054a10160006d40510b150400400c41580e001c503110340c010754102d40c5583d031103109084c0010400d0068442e00e0f071000c10721a0f0150520341040040c0140c0c00c02d5020365007a00074030810051941c01c82680000803031810081200f4600c84860040425041410009031003502c100c00b240d00c012903104203d503440c2d620b600510451240c050082c800452401c000d519140345c00b000b0851a98192140c6400e1110394804940b50a601384030483d4603001d0244a003c5442c2a0304000303002c0c2c1040d10b025601c99961041c04200188a80202d145110015009500e041010b80e07544011303040d000601c0d940750103882c0d58200003120078044c8500e06805800105040146926101204070001c2c0c0070a40c0710b4908442c2138001000e04c0c043e2108ac55000c0a81181c0078943c2d501130b818 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 339614595 1250 339613345 339613363
    0xc061a0907230405060d02131a09090f010803121503060403030203041506031205070f0b090105010806090c0904020f210d03061205031602130603030201050604180320 73
    0x880030100d01000401c5900900340d4080505060041c0000c11000c001c50b103451160f401050380100c4100080c08400300b450f0001d21481d01e0408107246100c1c2e842c582183c3c5070130780718400755081c80c0c0010381c1c18441ca0070501c0d96030058104100000154584500607540380301c0c209a61000270711b04800030712400000010310f100f00d000901a50a145403e290046c02948115070494459228003a10070407090039200e1402501c0d40101c1182d1020a560b030144c03115045000f0880c6ca524915408800003520701d49802c0c0941190710012500b5410001102e0a240006060358190385c8000c0651791a075859074400c80c0c000d90151080c4108545a0021451b40303640c10480c20b2030741501400660a54800007000703a4200c0c51079030100081d07038848c03015960042c0940e40180c0a54001d110a4160031040c59100008910080082c8140c51a42c0c0d8013100399000c0d6071041c0c025035500d01c10001107080c9805003038000d02a00285000340c3c159603501500301080d201c0c0c040090700502d0001000c2c82c004001c0064 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 339615845 1250 339614595 339614599
    0x30e03030f0a0e0a120c090e030c1e1504082205060c070f0501050c060c03071e0903021302091806150c011a15030106050304031808010f0b0f010c061a 66
    0x6030700e01951102510781007041071164084c480030140024169aa2003070520101d600540c480c440718503006030364014144928031424940410401200a984100414000d01a01e0b090900704e0300703040c1461a0400c2e001419507440340011008001c00907030b4110880700f2000340010300c0741c541e02184281c4030304880c1981103e90041d00002d0385008240d00000e2a800300c80340b2864035400140c561004403034074015002e4510856020070701050300d50010304c02550b031149162800d080d20305c410078220515441082034a03c0401d4241c1414015030404410f408841e042d601010b524001c00d490100705802086158010000001c50101d003807581c3e46d801d4810a0000f80c240c0c03646685d20400140e0080c07182032040e9901841c410b41c1480e20f410704040150104403080300d500d041d42c1c40d005082d039103580000c004074108406211a01032014003120000b01800da6100000b8469034501e010500f140e0103410090302c03480004081c0e400503a0300c102c180104a5005c1c602240341c11200c540c104002406000682d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 339617095 1250 339615845 339615847
    0x160605010603050a2d02161a0a1b0c0201080402010309021905010306080c01020a031803051212100b1903020d020a080f0f0105030a0b0c071403040503011401050d030e03030f 76
    0x1071040e810f0300240d0264421007800c011901a10013610042c900c0d0021800a8201080441100c02e560398050104060908400000311400307a40d4250001040100320048501000510001c200f181c4180641460603010148880c180c008000c3e1595004610080c1000b12600c00681164443e8210100e060350181c1101090a0011420110580345005040c00a49000300000d1140230001d070140789114107802804070316083da00c0403241c0c01d1081e104001c070054004030000013b030041041c0c00450002c15144c41d2600d00a5140000c0a400a44145841c5200c4203090125a20050488841c5541400b1406000d2141c070420380c06402140c0c4034482203440801c00707610080c1c10401080c0324a20307290b100446562400043d41460100b0300a068050340080b440c02c000074018014281c02285a4805500b42180b80d6140726008851644421854001041c20071044c1424018200e0080842c0303035802d115030511011070240e01801c10042d0800405101c030b03441c13684062040b10b000c00000302e00c0c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 339618345 1250 339617095 339617099
    0x11060318071710020304020f0f060f0304050102030f1f0b0310030807080a0f09030b01030b0c09060a03060509010f180510030206040603060e100b03070c03030b180a1d1216060501 78
    0xc091045800c08850342da5001d9121401180c903c0b902c00c40340f080740d00500c078000d1100514103000c100f41c068803e031500700c9002c0013032004401004001e184910312400016a50f880c102e003081102c5800648080c1401c0b20f104ea07090324070381e210b000184c242ca80080800e03450355141412034004905690001d041404c00241c003d061158100040c020001c1070f445d080c802e0400e1540c12a14606644000303440d90820200500005044600168010201014843c01c3c8080040081c48950040c115000401c1d940d0703a0030045401e007000900c0c01001000940488580303440da0040442d810390800400040d6182c2c00284d00f031001c0e01c101d101541c0c02504450b11587c88800c054001d2005009060194881800003003000880704030300800d450340a030559055480c0c00c0f00541d27410968400c102c05044c0c498954564545600000803101c007200780d808885070600c0a074100888901d4400241b1b8490601902c400101000880d420b94800c1001102d40d214182c01c000f0305d59591454000705018140400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 339619595 1250 339618345 339618359
    0x302181b07031d030c100e01091d07020105160e150d0c2c0a0302210303090a031d0306011214011803031523060702030118030909091106031807 63
    0x60419680001e11030b030f14811400c5010540c1d2004501d10443e4026860960f00c4003282c807c00d03080c9140f20301810040501916a640c50350141294022000d01108000801c07005a80c24019690043c0004101d41112444040d004104101074800d03a0f00a5030700c0d510500703d1008400407505900c078514010003814200c1940140161294400340d00016801c19407a0384141001450080d58a80102004030262841d82804040d0880607980c01c4600244070f49528444400e00c002c2d8401c407102e40c00f400d041d4108d4540503001c055851350341c0818010500800c001901c0001314141074601310341e41a0140d000520340500b102c00d076480d01802a5081c1592040742c0405003c000004502c682c40078030844940d1000c0140c04002c0b03104281e001480c08000440104819244c0000d030301000d80200c0c9040b155030046400d4407451800301c210b60400d0401c2c1c82c1410383c8515040041c004080f800d000460054440005c10000e010540388121000004580145060751000880354440c0c0150b9548594401e9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 339620845 1250 339619595 339619607
    0xb0a0507050d0503070923030d05030109060902030903030105061b16180c080601080903070c03080403031b080d0b01030605120d030e010605010c060c090e0c07020f04060302181b0703 80
    0x1100700c40d184240754000d02c40c9402541528800e200c1340ea5409041880c007c80d50011600060340b001d40c16000914000003902d007801990b682c500e590301c6155880d450280300004589840d40311006442c814014050310380804000c60341107039000c40d0300503100e6900c49544000c245140986640302c0c42505a640f0240c101e43c21940225120bd4a0b19204108075405080c103030f9811102c16400504400c0c00108558001c07900030350071241c028212814410940e9600d44031003140d1300140c5490001181c00c1081550144684034020f07500200008c441c0c0b00c070350b50410030703024441c032049072140c881150584691196004600410700241010075100018203a80c0c0c0f5909440ca09000103402c0c50104c6541c00d070140a040c2c00c441060755000d180f0a401d44450000b0542040c00d1403c0107001c0e03a0004100760080741290083c1c15400515a031045584100003000306440607180c0a071b41410006c1015a841054044561110f0010681160f54407043e0f8041144040d070807003140d20300458408240b541c490 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 339622095 1250 339620845 339620857
    0x170403021f051501050a02150705090d0302010605040f020906030f0a021c0902092d0a2003070207090908070206180301020f0903070509060d080f090d11040c0c021e01090b0a05 77
    0xf41e031488000b01200011501442801800f40142e80038a0740580304180900410f03078422140e01d1700034103003150200020300e4407000c00300035801030b0f444900c00d00c018a0103124244098860100c218a8814050042801c6000080011150b01038040000340540800c0e0100d4036120842a140c90b01540036014003401801724042c26409500ca500c0080c2d840100e0800900000240038000e01e15061801c0c104003401e030b002441c03c0303403e0781c41c1c00584c12002c070698100d01c600d042280140d5124a00040d00a1034080d0551100c04a01d040000030804247d61504444640340c040e41c150f43d580d00d088140200707080005083c103401d50310006a0641c50070311800a080d60035400c50135a070705966200b080080c01c0f030055a00d264008442244a000981000000d20390315482901850a0801120029112101808007902c0c5170071500b0501c40285000d210764070300800c4508194000b40ba5907000320300661a86040c1d4907429045c4003900906a024490200c014440c0455040e40d500d8402c00c0149150008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 339623345 1250 339622095 339622111
    0x1602010b030d0f0f0c240e07090914030a0917030702091f050f0603010b0304050a051c09060201021c020c030c01050103080403050c03070612020304140f0f07090606170403021f05 78
    0x1c00c15039451080001c0d000c59504249402200d104050541b100340d04944440716599a55540038003221009000307040003000900b00024100c11117003000320202000414214451300104800c2404541210700f841c196407903901b00c0d4024600f0313645150b20318801e111029500000340380401c22103e040c3c030010600150403a41c1c9940032541e44050040d50945540c940b58400030900050241070480c6000e1640140200d0868900090076141c4500340341c10445214070611890b0031000c0f943e0380010444000785100d00c004c6107059400b05a664442e40e403100090801c5400060095031504200181d0301900c0409008000b107513076a18140609074450b100c21200e9020741d026005d9545000300c0d0341c07401c0780ca413034407506602480c4050250007580010002c65541fa1454110300340540c0c200070840d03080d640704004000014019010314545403c69101c242c3e814204802400f0665000b03014a0000c0003241d02500240c40303c1c0b41c181d04203911741c2d4022903201c00d2062004119445900414050404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 339624595 1250 339623345 339623357
    0x102321071206120b040c0b120402030c01090305060f04031103180a090c210f091203050907050d020915041113090501051513090e0708160e1602010b030d0f 68
    0x1001c03111001e036100d501c0b40f0216a20a80030f00c40c080740855402c0e6601900c103140701c05442c0e444200c4c40c040c079041010225036001c660010030003181010000340d12810424200b480485195544260f6981c80c01000218004a07034008182054080d00321424054404804e03280c541500300c1000381c004034850703402d81c45071040390b01c00501340c4070034812a25144d28540d64907884064406100c028880602c00d40442203035280c680784a00075170361013014401849040c6040c402c0d1b401810040917200c000d003c084858001c090108650f130707101c080f000700c0c1c4ca0b8150f0301b1303110719520803e6000e40622402c80c070b15089410808410f05618003440103100742454071107101c035010b44613441813045500134069550400e20f1030250401c24010940501000380e40101d18005890b01c0d80301100607204d2041064805601003041404502c90500101e15010108121a0181c910309108104075000107807a0000e152802425513070403038800e400c2490142c8028048607449041c0d5900201a00000b400510006071 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 339625845 1250 339624595 339624617
    0xc0227010e160c0f0c0b040e06040c200a020d03020a030809161221050301051518040221040c03030e040c0207030213150306020705060610232107 64
    0x2407128407a0701400303008403609040300c10300c076003078071028250384055a1a154040c2a140024128a10710b0302401041d1601d17a01c8602d004580e80322001d0140020740b01d81d090000030451285c5c00b01101c1c503c0480c240f010250031102d0001d440c01c214807143c0182d005245d044c4901309040e00003801d040c11f18807030307a95103216582d551101500d900311500c0402d261100d03450100030f89086210040040b81c0100324103050303c0081e20500c2c03040d448034403040740071a9010004020380d1030321040c0c2e402c180c082c000102e0314181e4610840d400c4980005e172000d1145a0210389111b050000c440c1c0c2c020031207c2c00b007a20b0443d003010f08003001e03040ca40c0c1c4400c50004060808002841c141801042c00c140c50030b07001005050b0079a0f0030001c001c4101500811001d070f03518020086040318050000c0158040c4400598920003400c0081c1866402040b00b0f00902080b158014040d0384003007801c0b03488040d90843d1030012088151880f40b4800e12184c0c40c0e081c401804410342c1030f1040301d803150140c0382580319170303010074 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 339627095 1250 339625845 339625859
    0xa0b0d14030a081807120204020d02030f0601030b0d050741092d04050f160807080d0504030b060303040b0703050d0506010801060c060b130608030a030b010801030c05040c0c022701 79
    0x3a264413030990304548420032295130105080c02c41148028009801e0a0b1008200d10498008a40500346492410300b1301a9039600751151281540c811303201c04440b00301546500d55201c9640c0f03d0b1491000c104542042c0c03205203900a0301c0111140c00f02041409a0103400403000124103002c01d02c9000d501011034603031250400c0b00b103556a88915071400c0c02c2d031030750740302c08403c0d8004105503001d0040701c54540c101c19007802000d151b201000c0e042803040341854140c515041c60380d008110154880004503807800c0d0401c0543c5d00300c039489080c2001ca030755104003003800c60040e50b100e01100b80000c960703d41059048406041041801e480c1088103a594200444030f2000a100d210041040044200d0102d0f565410101c070116002c1c140c9040703207028003049011900c8583c072042030b030b42002c188004c99507450300400092503000d00c0e0491542d41142c0b1031100c418001c0c81020300c41d40da1f4801c0d421b160740c0950b14940b8083e4000f4a40711211103c0360340d46403518031601160303e00441c50000402d0358 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 339628345 1250 339627095 339627121
    0xd0b030115031b15030b01020709050108070906090c0207030f0c03080f190905130207060b03030a2604020109060f17090f120705060403030e070b030118051e0a0b0d14030a08 76
    0x300c4c552020042880420301e0203600405490f103203103046018007000810040042c0c0106402001d0b004000e0100394501700c5050125149a0800d0784405d04006c1c500390410380c002803400039260040302d44030380410540f41031030f1007a056500c0113240720b6006c500d504508080e040541804075030000401941401c0400885007103000307010341ca0303000c400d003c251920240d166015010302d40c8101300018010314072900191031904000840700010380c440394003544c0300c10140403007280c00000c40390708140c1b030a0070b50002c0d1081c8814050340d801c01003c2c1c031002c0e0280e441140b421348210f40d00301014586040c003038111601e0398200303400c20440d07100e45583c05601034006402c5440c1c2a8000004d00f01c140c48940e000c1340609480328140401d44901540880c0c4103400c40300544c000d040d060803048100261a2141096030f038010000210b081e03600f0f0007409460a1041b006910070980c100008180300000000303940480404400390071000c4001240320540c4c4004010808806d0980398161140d60380b180107009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 339629595 1250 339628345 339628349
    0x509010e100804060b040b1302030a0e0a080a05030406020910030e06060303041d090c1206010303081e1812042d0302030d1209120206101a09060d0b030115031b 70
    0x22030b5400010b010861542c000303903a8000c003d002150031414180050002401003c0f450721a0350b000052102481d407a12a00742c015221002401c00e692403601c1d021b6a5025989481c02404000800201006078960403240d03842001040c0c108543c011000050040840c82c0100d200d510544002c03030140d02d0008140c5049500101c00c10144800b03030b901c41024984040e00d101ca41c0d00c00c540c0e010b0701d642c1d10980c1c44222a01c010004000c15071442c20000d0064030050030001194212090035a92046041d0055030300002c1910004912a00205960b01c0c0c5108508032680c0740d800410081409504040043e010391154201c0c01d02e811004c0c02c000b0700c0c040b042d02c4025030591005103284082401a01d605030008103a20000402801c143c0361400742c0004117980b4001a04050300708411021818280b0026007540f001690141d9030f400300c100d2062081c440140d00c03c0b20082540c00d801d40158100c4020858050024403c100510b1300e04010490070380002c81e0111403002c03003c406008102110700c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 339630845 1250 339629595 339629597
    0x60212040f030810140120250b1602040b1210090b0c0c21120a0c020f0d0504060c11190f0909080d050c0c060414010b03060402030715021c0509010e10 66
    0x4070005d5040055484400e684100314070a500e15504050840d0b044c080d042500501e10724040e01c03554040c0c4008070003021500050030b811410310500390b0340c41420304c1c00700e4690390503500081c00e111400d000441160005004044a03c00d05822107503a0f60340f41c020000c0c0342c0c414030207150303180c4400c002a5a540561003085080e940320001140e42c500741365030024114040c0c00702c6070b8a4081104c0315492842001c0f501700c1e46158503080d112400c0d9074104040c40e100d48907a00546003062110341c004010b8803d601c200070402000d50751b0354007400b500d8008503c450704014190311000041c0003601e000c1040912400b41c02216540300024400d00714099012400d9000400b02d240041315504040106000707400c0c1d200088040c000c80c10205002c0104d1b03801039004d400c0c42c69422035050030751070a40e5800b00031300d8040d4016100340320040e02d0028074403098690902c181c04002c440000100c1c83d20802c552004208482c9400048041c1c0c0c004001348a8100d080c1d030707412400130a0b48140071181d041101140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 339632095 1250 339630845 339630869
    0x609080c04050705191e21020318100510080307050319090323060105040e060402040906020c07030f021309031704060e010e10060f050913060212040f030810 69
    0x100c60361910307a2100d82c0c401101d0a001e0700b40500d88003895401d00c0c1a110a00208407400c0c19000780c102c0401c2101d1a0301740902d0003100904e210f82c0005502e00708680c83c00789182d004000300b03124600d464480005086680c00b01c0d0b8100a000c8071100c007504003500c14204462041c840801c0d04e41010049900080d040001036140036119090000400ca550010004100c414180400060001180040803c00d0503080c030660420341c2e0b86940c00c0c1001a4441480743d4540186158074000204500d43d005e501110000342c0d0b18034908140010b40300308015a41d180c095081d01004204007440900d050074002d8400043c031500c0c0d4400b81040703824001018000c0f130001e018000343c000c0702700328240d403061041d40040380310104588150700b0358042c0e100301c2403213804c140c4003607034807070014031400b070040144080c1c500f001841c0c100451038001019147e007050085020200c014012190102c42e40c06045688500c1103150504204280000d03030503003140011030708804195415a61110001507900d1560a6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 339633345 1250 339632095 339632113
    0x9090307080315210c03190b0c070602032a0906030114011215140a030c0308070f120804050c0a0e0118060b0c1c0302070305180612090d09060908 64
    0x340c103041d000102800801c035043d035820340c0b49450704409040740c24100d8489008807403c0703401c1142404103c102043c040c0c1d200d0301000c075910030042c010340413103600224601c5032625031800c013904c5c504ca040c10183c000740c0000140040c0c4422910255121403201c14099082581c0d503403001c08038490400015806001800144580c00c3e02c0ba51092072080c050400107010705481e02c640003618192911080613200700642005584840041000c08000448000d02c20380c2c1160740d074481e401e1840c080a05441400700b445400c101840e282c0a00d0640c0048040c80452409400203050801c1250111540e00408180c0c00a44c28095001c009070380c030017079013100568204940504181c4024000d190103913140e2070001402ea1b41b480c02418209601c00240603210007201204c46850401120142014030400050022079441400c0d110610b40c60454a50616613450001b100e41c0103410318070005a10110922454180000b010144130038035464201035269a200e0542d01c007442803252100c150040c40385 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 339634595 1250 339633345 339633353
    0x10509040b0d060510140a05090408090a03080409021804090507090b06070605090a020a0f0e0609150603100513140c09062107120b0303070312020d11130509090307 72
    0xc150114024040410724001926400103492041d1520803000601d100244055400610000841c45060742c7e45030030345250002080786400014805072017501c000c02c01e09855036454502c5801150040070142c0c03220788605d00507009512100c812130509280f040d060301942002d0140340d4810750020040c0890501e00b10858010703005a4078072030351140f001c02c0b0220000f44244501401209400020000c5a28500c1813111000c042e4005c142000140c140801641b04000092984140e00b82c42140700b685400034040a4a20312010702c3d54820030110070401c035650034455060894004407403144c05900c001c0010320480b2112030801e5042d50000c0001249855890002d0030111380c05041240f0703040c0d11480d000d040b0044440348000c068002002d2202c100d0f44608840320386190a4401c00500080d9000280d8a02c5901c0b001070900c00302c218a5540e0342d449078192014004142800d0002c0b01034104540c24a502c2511903000000e401580401d240c10301506c05031007001000001c615048080d11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 339635845 1250 339634595 339634601
    0xa0315080a17130e0906010603051603090507030b01030303050f160c02150c010603140d0201150302010c021f120e0601050306041509020a0312030e0c010203041715090c0909060601050904 82
    0x160900554600b0051181c982495403207100041c615a030381c58600f414090b0201b802c00c074047c1d00c001c0805041009004604e503d042542c000ca10507410001440f9030586403260600400d03500207408004180000024190140c10180c400d8110030f07400c00007541c41420300401010504040c0c07000a085208078070041c244100f04079070b08100451090704020b69915005d007911001c2d00704850f0280380b00e0360107113030360b108000b02021403903540001e01c00b8030809000107902e5026444040d040210303264859041d500c64240c100c1c1e114240d0000000046420000600961002800e55000c541307080400340d03a00c0c0e00032130118103940c0300070080e003480d0721691540701c0509554410000360b10358036001c038801603072824100c0c40154401c44449108240c40382c00902222140005c0d42c0c45c98000044101c846e0380c0c003004641c29543c60400c00317215112010351152420380d650f071114907061000d2007402481100022004180b000441c1c1240060340d59560041e1590425030f0391501103102800b140e51a443c00750 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 339637095 1250 339635845 339635873
    0xb0d03090620030409090b07050f0a030b040f1506020c0a081005071407060c0e030316021306030f0804052404122901090e010b150904060b040b0a0315080a 68
    0xb8441e080d60031030288698110b50050b401035246a58030210302003001090390701c40e03510074aa0700b80a824680d00d03148484083c03042d0108041003550f01e402920f0b00d0395466000700d42c81c2264034810008105400c084a034000954040e1401502c074403a0b880700c4501d0590800c00a503040b00014290300400c0c0500c49001d800e018141c001404010000500317006100f40c0901652802001c0110300398100310b0f0083e11600c20141d20a000782c0081080e20b011034226441c4043c15603042d11100b5441c1c82500c2c0400007820590001490300010070030130303801d00480e840030b0800d40313808440d41c6110034006d00c1c10002c5044a2031882d070b084d2030180b104000c02d51a01c5200925640100c3d0044c0f01d103071000c3d00381c0e40c7c1100130104096080e104140144160f03851841084100e40740e92008120030600107000920481d8240b80c10f4045410000360309001d80c507507801c2400107066180e41c440e00c40b521054456181c1d082075000c000001e250101221605c502410b01900b103441c500054032040710300d0707101c8004540c3c0341 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 339638345 1250 339637095 339637127
    0x62d1707030506091501050d1e03030e16090e030a081b0f0c010507030b0406260304030b0705210c0304030c05070f1401023a030603020315010503010b0d030906 70
    0x2000380080428420b0051510504e40007014005070700058455040c0b10350183c1029003d1860b821503c0c000420a02c01403484103e4034030a00d24404240c54100d02400100450341003c0c0282c1a102074441032220703039807042e6146140144034001091841c0c55880c0103101c403010008190f800404c034003041c81c0454a107140805640d0301d00c0e01c545c90244c2c1d900c2780c0c40140d140c1e10980d541c0c420440341a900d403155051700c40f41150140601882c0120b0108400468294840342d5000c0e240c1b40b41c140201042154015036110070010018036100c20042d010303800520410601c00c00002c504c400c0c100590062034811100946401d0840d01c49803811241003600781d10803a00e5224022000c0b810000300520000100b0b224040484080003500c002070a1a9490903100003020410390440c850300d02a240030b10258403110500140e408040394214090a02507001079014010711044124590a0312107003030503500c0c00c0d4001c2c0130605146091007008c0112500140c00505000700900c0118800ca52061440306d00c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 339639595 1250 339638345 339638353
    0x10b04151a070f030f11120315190e040b01080a08040315020c01060f05030d0504080c0409080d0f060510050c15072303160503070e1302040e0a062d17 66
    0x110380e91045074403c152010742c0807a41d001002084141d00c1030703c41240514200242c518101141b10045d02400301900100e10150000c2c500c030341030b44400181d1070707d0f02c0044841d0311015580307504010380c03560103a40541d000d6103d4400428007000009025170b09592081904c0c1c501840e5407034521202c44400f18007680035408100044082809000d40400380020700700904606142100b010316160207003203140306000040c481040301c0c21020541307803d44030094401154015291600764410b2003449a0120758621f07040140c2c80b20390325584500143d400640302620394401c850815241400307007207101030701c96006000c2101c4c0442c0401c540781d000000d9003060240c2c044400149581c050400c10940c40c285404410042e00f8083c990847d06e4226690034110701c4c504282c80002c2c61009904007043c050b41c4401d003c1c00d511a00d41e81103800801851f604018a41800040c41c4041c00042c442c030b010020b040c804642801c816030f08103403800f80316420f034208041d148c50154a405c08041c0c40f092a2801 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 339640845 1250 339639595 339639607
    0x411010e0907030f051302010816050c100506030106090612060902040b060c03180907020706050c03120c1806090109180207080a0207082b08150a1403010b04151a 71
    0x550007007103030107804151804200f1500d030f105140116a002003601c51044201001c03600542d812214141d0020101c0100c2100410f0658095aa030700c14224419014450140c0b0007881c03240c1a0702c01070003000110000d0040300c0d81c03401c4a405a400b28041c5041400345622107000141e805d90000c454248003520100c8c440c2c645074001000b40e08410b0800395141c100203050300024100d01d02070075106908980080c42800c000c4c01c02035035602240030314010311100085001580d0000c03c191080a4076000401c1c49528100346480055080200560070b4403c80021a000b180340440c02d40d1002c0106075100108285448141d0000c0710384602440d24499081090001281d05800181401042c54008040862815400c1c51410000d1700d402202c40c3d1100b42a4100a90a41c820800d90061803030000d28545444079103401e80801428800d0388500c4041c40042c21681001143e000c40c01704030001c0201d580c0e039400744401c2d203099a0488640d03428441c0c00b80100f01c80005509402c46e90a061030341042 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 339642095 1250 339640845 339640849
    0x201030b040f1508010203010b03010e04110a030f060e010e0d051e0d050105100f080604020c1c02010e07171c0207091e0501080f0d08071209060606110d02060411010e 73
    0xc0c0441e02c1100c0120303158070810a1845401191500900000000b145150700d008001411404180500056207070b0001c089024841d00c00b01043c20400014240d5205d40d80d85d02e000040b1a642c1242210f0160a1440d01d8003001d0f8180301d1070407007400072005884184400f44084036940e00590342841001409800c5109128011024144200141c0340001e02941454100109400ca07055540200103a8005011031190300083c019009403046d036025848142c01114503003441400c0124402c140c140f05900c1042c0c40e03054003c0c480c20902d1070180c1c0e00181c0c40d1105004100e520010b0840e40e6407007500900780c0309036040031070a1040064130546e0343d50b5403100ca402040d18414003070300c6d000969281180c14410114480c09004040071001094071420044000da02d49221040b00014810305000290415020340b80c0040b00c0b129046082080031511f260440c0240901c0c001c04000030100010740c4980305000507030a030300d00c909400804540c1d581f584c50004040d50301c0d1081e41040210820700403e5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 339643345 1250 339642095 339642101
    0x609030f06010803031e150904020d0204020a17070c0215030703062408060f010e1302090409050a05120901050714010207150c02061012141203091c03020a0512040201030b04 76
    0xc2c03e800c0024603502d0801208100d4020f9003d40515007000c1c503a800d0140c1201500d0800000c1c00f41500d402040343c2d940c0c00003854030071312104041d4001e8000a282e4403c1c650007240d2611841000b811381032140c40b454001c860040c994000250881144000650000c0484010310350000d4286404079825882c4c20b441e5100c2802550640030303030005a0030300098180c002c00091340c030030b42c2541c0030700050800100081c003205948600c9805801c95a00d1840030400540440d60f46010140062101124615201d60382e0741340040159141e0040b1b550000d541140e4404650804805070344040c20702c1c409480d45150395041c0c002c40410741d03600700001c0740040c90740300b582c0450b0001c06900143d00d101d82400a4200303080108980b070340d908220303c203008485003940310318542c641100740341400800c0c44013200d14110032950094240312000c02045011000002c00c130305100c0340c100e03240300b40306c04842d800c1c6d0503400341e0f06c2c103e00851400d1010445030010298403a134424014540070424150800c0800c0403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 339644595 1250 339643345 339643349
    0x9010513050d03020f10180305090301111602030c09040b040212210d05060103110f13091a0a0b070203100c020a0213050106030b03150403140d02041503050c0a0804020609030f0601 79
    0x3d604080703240340c40741a01b80117540104045d80d000f40200940511aa031000b0200040102403103c00f04403040503880950002244d10040c500d00380d0364905003054400501014042240f003032003001c0c0c045042e4105120118069a0f0019a04440d515603500b008001c3c0740855582d02c00b4810b10a0180580c100305100c8100211180e54007030303480c02c0c80821030003585c2c0c00820321410b050030600e11480d0b0502c1d4070122050560307000e1199032280c802100b580d64400d00340c0c0c0138011340f9040c101813031306403800304074062100300080b00c44500f41c0da80d5102944450040352000f0398035401190005901c2515504000c4591482d481503800d100110350000ea5442558400c0c01e5003280e03168018005960035204100800303901318001d2103104142103028141b41d03001000102004004000301c99010307002030640d804544c05c560159100e580f00c002c8500441c450030500e0780000d0601e0702260b00650400100c8200140c03540d00c5c21a2a590b580a01c041d83d03000c51001905841000f100468110080c002140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 339645845 1250 339644595 339644597
    0xa082b05040605010e100509070504050306090c010e03150f0a091e02040e120712020c0a120b070c08370c12050c06130f080f0307030509070b09010513050d03 69
    0x300c6041605220080b140141c00804034200c11409021a44680e10040d0f401c1300d00c100d031201d80a6075681003c4815005592000e03070148915405d020780324202003080e094074082a030700c103000d140034801016903542918172803580380c1003004d0215001c80f01c079001c0268040c00000c000309400d131031039980c0d100d8031165610b04881421200034580c11813400303000c0e501c5503d04840041040019540c140304640c030500740c1c0202000700700904068603178024130802a4140004000b4840e465079600e143d5140312032003004072040b503600700004e00c0150080d0300c003100310707900015090b00b8148030041c1c4102c65140507030031580c4a85004480d5055106001d55400820020303a52403404914070301c1c1c1800300c1040d030b902180c1444018011004811400a00d00340d006050181c440301c41c19081c202a03c505245d07540241c641c10700003a051030f0301000741000754050911950100556502c0014594031207131917000c0c0501100007001280992340c400c0c0c000c0c002c103811411514401c81da491000540c46a0340d42c400b14 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 339647095 1250 339645845 339645851
    0x31204150219030b0339120a0b0403030513030914040906050a2702090708070909090606080c0a14010c060209040504061e0912110312090115090209030a082b 69
    0x60203400c0c28444008442d00710314071200c400b084564004841e0151a640c141c1441c8469a0140c40f60307102da031104401c1ca404000c0e507030346108d1828906800001160182c2c00700b0f003040701080d54110082c00c0030a409805070703038006500e42080c200b030401c1c5646114050340162145c0043c0c001c1031440c03160700c2c0a01800d11001406413101d000820558040d80d40889048429420300b0740944c40710030b1040e50140c0540382060103942c5a00b01503610400c80d0b0000c01030540382c4be40340810040c031640001b0a54001c10102c840088080040100c2d451840c060000104800c10709490b00d940216241c070300d41485484054140236071000840c1c00c40d0070458044d6035143c2c840507941601c0072038606a805002e0340c150240700c030654a40303a003c45440d0f1f55400000300b0030303400d018a600400034020b44040e4450071100c0041c0303040c0f00342441c0c0038082501c90400141e4540e1800541905181300700d40e10140007601512483c00c0b0307900c0c3d02c8460340115841008940038484280044107001d900c848007101c201c0b03400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 339648345 1250 339647095 339647111
    0x2d1e01020d08010f1e0803030c04030201030b030d0c0b060604050d1b0b0c072319170a051e120301030c030b0f090a02220c020307021203120415021903 66
    0x9141c205681401414403000600604c5a0804101c013102541c42d41c00c0d04d04031002c0420400c40103440c50354031921517800f002c8284030044030b05030014812203000341d0f414802000c81208141e242c0030300d0b06495001c80e101e14005000140c000c4501e640c4184001d140c2401c10343e40c3c40103c1c803603a040550445100408510120004510074101d1000c0c20301c548000c2d0600001c801101d9485009008206a41002903182062000c801480da42170500150000c500c3c40c60781040c4d07502182840c001c500f41c5611a8524040c038500000711408410780000080004c0545100507606100f410181d0040502a24601362044039403080111300070743c400c5040c00c0505146040071030780c1170409400c105004900c1002e00c821002d0001351031a2094048420a6804006984108040c0c0c500c0365614103040c10003050390001900031010b40800b900907554240703501920414640c4074403903040c01182540003940464082400708500903042a00c50750010f20b030003105a00060300100030150100025250307601 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 339649595 1250 339648345 339648347
    0x303040e01090f1b05030a0603060204031103120f1e13170709020406052205031f0b03010b03250918030e0901030302060723030901090515062d1e01 65
    0x26030103e20510704003c1004e01d80200e03500d180c0ca01900c80080401c5004404503004480b00d90080c2c004540c40301c81103540700da0301c0c54422066501c04d000507109000d05103d50100003c080700b01d49091503074a080c1072401d5000700407140803030088006182a010107006202c00b018000754100086d0468060302d090f00e000c0340354454030348410358115010f4a4010310080141c540c00200342e1741d0b4407015807004101c00405900c8a00c03c1081940080d42c035100e40304580061490100e050b404035101620180050030703411060600765007a0200141d05940304045100900c00c0344411110980b60405000036442d5a444c900700076034032802200b0700105608070703581e01019001340c881c0f1404202507502003002d40c0f46031406501d07804010002014440d03c28130f000d580f030003c12842811401c20a100c40e40300d051586e0828002c012440d0111074511600c6d07c024003c6042e01c540310b01c5110020310080103109208485501c05100000c1040c0d10024a100c4240c10750300e0a23850602c000000302004101004900 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 339650845 1250 339649595 339649601
    0x5010302120d0503070e040b04090311010f090c0506071b030c1701050403020d0509030c1c0b060d0b010603110c06070206040209100b030a020703020304051003020415141605010b0303040e0109 84
    0x7a801850764030a01420074100e400c001542e90200c0182081c0d00ca000c00c0001217005801054034240c0c0c03042c6003e542d0010103411200c2c042d040d4503400020000300d909203501c8000c580e940b10300613000c81d0307440608012a25050006020003803058209124040240341091520390568004859010407541c044c4001c0411021811413450080003d12030350801d914040d4039109550292420440009206419528100020455208081c03c1e6188103042e80b00704080f944005241110103100c2c140115083e03142c00c1450001880d00485070182e2646041e0080d0014400c0200c800300e8404144600d0000f160140812032180c00d050b0040e020510305441041103907540204a1182e80e0003500b000d1082d40406e00680e6801207032440300594855860405a1442c015136001550021002600b00e11030b65064001e00f007103403154826400d00c2c11103140c0030340318000101b55103030200105110310958111030b208424102030003030000080d58442e02c0046400c541c4260031040152200000400a020441c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 339652095 1250 339650845 339650869
    0xc05010504060212071703091b0103050f060d11100201060f09090c0b1810050c1507321b071505270306010b0703080f0c04050d14060a0605120c010813050102070501090605010302 78
    0x103e401c110920300601d080c00304031301c0985140d000c0c0200c10340c03f80c100859050f950715a0078000344801d10032070442c84c00901070000c0340601c14800c41c0540000a40e0540342c02456543c03607110010200e41403d140c05114240c0060030782400c4042c242d00314610f00e80700c1120000500c3d502c0c0d51590340e50f040c0c00003c2c6207000950b4210203203000741c1c40108007800e81d1006140c02e1900c02e00990000d004456100d1494202e0640110b070b000d21400a503418002c420052a0704c003018000f401da071a9130b030303507803c65501d44107849005102040080000c001000d00408416094a480d6080b081c1c1c1031303c2c420080ba00d0000241c019031004480007843e60141604000260340c4190030741003200852801c100070180d00d0003030380714445c0a00c50400180c000c00c01c0d00b41c0c0c0c4c00c54110b103070b00846080d0f240c00d2841c0e6024001d0b0788134050050441e61340d0341003544c0020070719006501040e1108030f9a92600058480030b0141d4103410b4400755801d01418000607805e001e40d0302c0c50b40c0501c102040b00d504500402c62244040c0e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 339653345 1250 339652095 339652097
    0x9031e03150a080309010c0204020903070f180603080906030604140708071407020d061d120d0e0f34031103011104120204051e0a090c05010504060212071703091b01 72
    0x1468003044043c0c0d0000458600200a00e0144100e003114404200a4090b0311711142c1d05014520000c80e51b002c1840071802141c104110107a60350045c000013400311000e81c080500403074410040c6000c94101100203542105019100140c01071141901c00740d007100565074403000800410500c48a00c0e44034501c6c511300310006c9003407031914010741d00241c031403100040700030161034840e50240c0c00d01c2d1010680c601c0d6540314005540e8030010a4140c200183c0c4441416600c0c0c40c904281e1000c0100c4c0000c90000441c10b180080c045020103507490114a090400f0075603440700c8804001d54190080d00341800118880d01d140b0900384205010182501d080810107415070308103010811281f10310084084a16405890001d003a0700c03507000422040c541c10744039480400001b0103015a00341c043c0d0000318218060754843c48200d4030b0310300441d0749115900c00c1d580180d00c14000b00d06400486001000003500c2449094150940c845078240f1075003044420084540011584886001c1401d943c00460361023 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 339654595 1250 339653345 339653359
    0x11100e07150e0f121002030403120203060913020604090c020a02040e0d020714030a120507030807021b01080a18031d030c090424020d15050a03050d0809031e0315 71
    0x162200081100603422950383c8240c0c100c01101445450f0240041c420302c0500042e103180781d0000071a03402035030040e10100d0015080c003450555008240c0700f81d90280c00010588070300340c1c40341450042681f02030f02c81a40d115904100c00280040c240c41520804104c0782c001d0503064180d401000116803011000d40401e030040740d06400c00e10f501103180c005403460008104013458590000c0380c50108203a0b0028410400100c1c50056650824094461640310342d42c0e40f041c41e90f8000d41240c40d20794906030941060301c408901c03075941d0302641d80ea41c0e00203204400000d1985140313108185500102800f62b011070071346000340b1882c40e501030000c0c1180768190010304101e40d0103400f0506400300200007520400001903000568000f8940d80c1103081901101135484090200850008044041e043c407400001c0000001d580d0502011960880383c1201c0504601d00300d803030080d41c24180003000c111050008111904ca030303e18613030310f03200754400700701da0f40340c072440c0001203041d000d008032f01513501c9000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 339655845 1250 339654595 339654629
    0x1140a02060c210c030103060f060f0603090201020a021807080c0313020402071a10080c0906090a020a0903052d01091203020f120f040204180309120311100e07 70
    0x600090160b412602c02414281c1e210003a92a822403088840e01d0480c00202403003d00a03140750050145050728040c550030000003052040c40c2040f5002c0d4460303120180d2018008200703c502031b40c8403007007881c018010390f00d8a50480d40060340c120020702041c00d40c01c01d54010310452a601860659001c0c01903240949542802d900304d1095501d2654001e00c107507000680d08081040348001e51000c0000c1c492844100d0400350006000304a850090520714400d01d440c4820a1800400103801440c01810403049501ea20500c00e0180d8000a003030760501c824000300100088081180080035000c03a513020842c41035042d05000300710100e00340301d12a03a0404041e080440c0c3c03a07000f030418150326410016a1940403288425007801807600101982036458100301d0710b000d0701c86900380f255101b11010031044144214003c4a10000040500003034031389003080c0400019040f8000075140641400c103c40d200030f00120b454040e01101c8002c03116160a03017018900f00400c81c850103090701105601d0418 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 339657095 1250 339655845 339655847
    0x40b03150109121209090228090501050d02070f05070b0c1e0d080a0e010608011b1b08090a1206150605040b2d04030302060f0c03010b0924040f0501140a 67
    0x14003600003a280c0380800b05049811400345401000400c01040150744510090303440849295079040000c034401c8c3c80428001c4080c0c410a049410380d901611414100340b00849244000d402c42d49084480300c0442c412a0085001003105000804010850a0340e418443c0211030030050350f644006450040c2c40400c0c01504004680100e8020461810010654642c1c06a001510703114550342020351a00c03d010890740c0041d00714969802e03441341032803d1061842e40884001120706070010304d000c1600b5202d4005840d03880202200c580040a4034070050301c82c51000c610041800040b10020350700c49a400c1040321041c004c50007002c0c9400c149041a2070b1400006043c85000c1d05601c44600c9050303c000b9522401180807041c494030324440c0c1d00c2d0f0b500d80c07138082e6a41100b41c610b110301081c844006910300002d44100d03810303212709942075820b10050301c0c02c3c0200c00300c0c1400800440c8610b4000d04800412102c064002001b200001c5044030f8035020000d0207030244070a100d0040801000303485495 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 339658345 1250 339657095 339657119
    0x303090a060809010f150603050c0306030c1201320a090b19090c030b04030801080f0703030c2405061c020303030411060f13060807030c020d0e0109030503040b03150109 74
    0x241c1031401c00036255502c07809881e00412403205800440d40c41c00c56482000c51060800d0710540d17445490400040e19070400035200d900080740c4072030385036100c1b0800301417505013009110954038071180041a03000c808403070344982c1d003203000042041c5400c0f1252401d5a00c0f201503820307001140c0351402c0001a80a44507044a0840109107500c40d48074201011000031176584443c3c1302c03640000311f10703078000d49901c1d0031121010151400c1e00001c40f0a070021402003c0460034400b4490740c88001d1500300d01c0c41e0303010740310312180440645411741d4230007038003603c9854211092669180820002494500401000703030004803a510510401d455507805030068600004a94015403c0090b51801500080005900b0711a031048500312940101d9401000182083d080c07090b50525100c486d81c540ea409821030407100000e0407000141c2c4005203610180740a1418503001e040b040c94038a1714107460b1744595103913038070950111290080c00406c00002e010900004a68907200f4a8008031403883c00780d00680b8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 339659595 1250 339658345 339658349
    0xe06151c052a10230408060a0506040b03160302010c080d180605090102090105030402090a0b1302070303060b070812070311210612060c03060612011410211a150403110303090a 77
    0x484c1286859900c8008014410384000341540000c88010b0725088504501070042600c406002d46d06003802c040c82c034a00843c0c50f0040310314505148121900d540c004503080e500048040e0350401080203a541000481c0c043e030000f00e540001c2001d0a40960300e001c40444100811a034a180d00c18407134264280c1e0721904481e00310703030100c0c0e030010662901c50301c82c0020003849045980c080031182c0865058280782e0007500802e400394808100b03071a50b640d58003580d07104401000b020090100030503492b40c0313a02d496585e0801024a00002c61480624848440c0d0b4410740f40c802540024110000700c800c09170030016440700094560641c085c0804d214240e4a010203010341068142c0400018244c0e143e02054403180c5130040c403070b40d2a40d40d41b908502041030410800700e004a041d0425540b505008811030315a40d54018400d0042c0e802010144000b400030300340041903040200c2600110f40c2d5171070020391000c00030075605941ca629503d0010b45200e01d242003c0c4c020f0308140306403d06a41c80c6000c0d141 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 339660845 1250 339659595 339659627
    0x1211030703110f0102071407120803060103020307170903070c09021e071505040b070818190f05010e0d0f090501210f09030f030e06151c052a10 63
    0x140308180d0401d050300f000c2d401c020070701c869031003c00c2480a0214142c9605091100d0b00c09444415072070704109514503400b040c001d4000d600070004a0203031f501c07071fa00841d40306400340340c0050403950038a170103043c506050b034460460b03502c04503140007807200c0840c80314010015034000314541203d110615071002e4009108039411030003c01c01200b4003580d40c061400262405004015a00d4503203884654841c007513a2410005a4182c00240c02e01100b05807640300060f1a0010a1a502440400b0040c0b43c840300003150150a00e001450001f842401030300940d049400c00b42c0400c031144a001001240c40c0308802040040d203000400107640c0203140d00055103c10340c1104500030b18034086402401050010510075460101600249548141410000321255406006aa40f0046407e80e5030708240c0d2020400707003002c000441c00d0702c2c00000c015544451030220081c0b0040f0342e02c4103070038101c100c815000781110081a001e004036076a44148041007044908406828400302c00900d080740d90b40c0510 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 339662095 1250 339660845 339660857
    0x20f04110c0a06021e070f060e032a0c0d0b07030c030b1c2f240c0607080f25020c122802060a08060406030b131211030703 54
    0x3203622a82034044030014000701046030300c218054500840258440140480f60740842d551800300390444204032440c0580010a42e80c6005280c3c803076200500c07842c1d28a0b542840204150384c99020040c50320103014046041c0c0c004211124001c403400c00504007070440c45403181c1c2c42c0036000074005440c000c0c0c1040e498540001c003064003142c1603000388070f02410541e12240c4240039440340c0382000c2003580b0152040e0b10111046010b19200c0c0c00440710300050006100b08049120100d0a10b08144054541b9007580511032041601c9900042d42c00511100101d410403420442c842c1c0e040310f280c60300300b0703440341c00e105141c500410304058400c4401c4040c0704041c00000c0c0260b5047c4200b2202c442804020001420a402d110000c0d540f0318482c0350321001448000320006180e103454804120460f0043d003814a40300c0340c0c1c50116100c0030b004251030b86c0165940e80204c003140c00d40c105240310703c402c5031000341102914202040010f500703404000800c00e004240100030030022003924141a4107040003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 339663345 1250 339662095 339662111
    0x801110903071a0d150e16110c0d0f08070803010305160b270d0b01181803020d0c030306090c11010b0910050607060603051006030c0803030108061b0c070303120b010804020f04 77
    0x1114503003056000403100c40d40d407820301801c828080003117003501c504e540350001440f490f021a542ca4007441c1c4201c0e6449012b0424042c00318021540c0320700410b1003044003500d05a059628000c054100b031300107a501d94003650080740c9098036240c445000d040d030426040e0030701c00401010b041c09060726030880b001040f09030440a040c0c840c00c00461925510a90007a010b6031562040210301002c04110b050742410701c80c1d00035544480914010a50350140d018005650b00b110059442207607000e022801c06649001c005842c0e9054450906401050307a1101ba000300b007086800d094072401d00509201e141480c0c240070080c04441c4110301100d074107031a141d4849580342070100c010030103030388080d01902400b180121100c10545c80070081c1c0788100400040c032a103030007540380c0d680424040c0d40b030b8603031101021607052490075403500510505504003501e4418000b41e80c41c1419410b030b00440104034a4a80d60846911034007445403402d1007860300c0e1607640390517000582003046260050340140c0d03441c041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 339664595 1250 339663345 339663371
    0x90a2913020c0a0611090307210b060307080109030e090a05060a03030806010203070605041b06180b070f02041506031d15061207140306070302090d17040801110903071a0d 75
    0x500b0f40d1480d00004100402c1c07009000d0030030580d00125285200e070180103004502d41d402e292900da14540d5500d20b05001c0c031788580d6941010300380500500c4d803511031000e0000741a10b090044c220324510030341c1c0d07007040b00e0001c40502c020808003405104420f8141010004243c503104034100c2182c1e010300d0105202e88030240140c1c00c43c41002e00180486041034100414040820039800c00e82c074100034081d40280d541c88003180c05038504505900760644485041103101003080c007030803c99004660b001101a9194002422602c0d03103200d450303101090301400c00000c0e41511480300ca070304514441740c1083c402094041d40311341803140d03403001c080b4109000c19941d0302c5d5500600c1d000b00f416000c49203902e440b4401018803201c080f0720b5502c40d101d01070006906510900039201c010350f0190070b11745131403400c0c2d403014001d4100f91b4443e20b00a42c18040000d40310024094801300340001ca80c91a80d501e1400705050a010340c0b60081c004c0203c424001b00d502100c03400458080554208000440410141c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 339665845 1250 339664595 339664603
    0x140703060605100c03140f04120c0509040c090b030304090203011806080c030a080d1b020f010b011b0305030612010627050601051c020d06090e010f060602100911090a2913020c 77
    0x100c42d038500c0c1e401041c04910141070949c02c807005030241d00d20307044450784c80d000c101c4204000c483c02082a10210030811448007070303801c510302d00b407001820707070303007880e45400d03048040360401d0740300c00c00451031a4103d040703a03a103a1050001400501014007100380c0020040303503072201a0705004119540000d000d00e09419203601410540010280c0c0300092401e42c98025a01c0810700600c40040d4603040405d54250300894004c540031540410b6001d1014485d01c0941d4140c00060400350490003c419407440018280b0900002c0d00c1c805d06400c88020004003900c185420312801c002c411071510b814009107a03084403d0300c03010070684141c2c3c480c04811a150744068000e410b60318410380d0500801040c800c4442c1c22090100c1e030044001c1018007900c00030300003560031034400c10000d82c101c031024016004182d08915115401414a03000b002c80481c040740c0c103001f08407005419150740c1d60095905000c251440c40282c071000c0715510710072501000103500085505455118554002900100741d10148 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 339667095 1250 339665845 339665857
    0xc0901030b0a0f060f08090d0c030215090607021204140d020a0909080904050a0203070e011202040503070806010608092a151308010c05041211010309140703060605100c0314 76
    0x20b4495052180d64248142c2c00b10007901440000c00c505c18402180240b1450065100c0c0c60680c004201c64a1180030955180070b0048050302180610040d40808076521500203005200c490010050b601c4c00c1000241003c5001d50600003143c0c08010030805820700052202c6034201c01c4034680390110b00d910010b411200240d012076210b50510504506220004001d000c0c114420780b4207000703d6580322000000ca1000b01c41c0035000c0745240c0c00140565200f40030209412266080040c40c0645610010b45450880d61020700765500403c01840300300d40c01000d1580240d50b01d80188402507420710b45803502240340000300c408124400c880106682c841c1003071000003540241169580950f80510030a0310749501400c030726582041c0b0000b900b54407410840b0112504055060a525102d41e2041001a00c26454604060300c58400e0310101d2810341030244402c00040007130040e40d2461901c0e1055640c65030049206001840003c5400c0f90031450691106a051a1080c58481a40e0107680e1f140152 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 339668345 1250 339667095 339667099
    0x804050d0f02015a0e0f0d0b070e0a0f080a120c0f080a02120d05091c0f050c010b040c050c1c12241d090c01090513110d090b06090705030c0901030b 65
    0x1200012105402c0b5200101c02607050f0342c8101602482801c1c04221068447c0c0207260b21444000200c100c7e124545032070100c0e000610640c2c25036601c030400a030546850700495400c1d004a4070041c1001018642504a07581600300380c84d51605948a0307440c0384203c070001074105c400c00110350000d244240300344600f43c0244000c0c40c0d02e8043c10301c1004014502203940c0e50305881080210483d229095008130091181c0355034000d0303048483c11007111b943c0c00900c180e06c0550b40f901c0000751585c0d981d0141151848050343e449071601006001c0342d00e000c01e40c004600300800700c18074006013145e0203c03030003e6070301917400080381124410002c501c851301060b011501c040c004203000b02d003d220364858104e40a5000c5410380c02922212081600c408500e84580c0c041a0640f004101e0ba040250103020303004540070740010046120280c013040c80d48400790041ca903d42e280fa0300300030041451021a04040240e552040c18034105501038060712002e42403032278129010400d510140c5c821303000f401d100840 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 339669595 1250 339668345 339668507
    0x1020903100905061806150102070e01090917070b0f040503210a0c03020301050d020f0619080105100e030c0913050703060609050112080708070804050d0f0201 70
    0x30141101d030041c1040b00d011a800c0c0920f1011814152190851040324503180c0040c00c03070f0703440b1010112940846102d002e41980a029400035101483c1c4041a001340004400031401d59841c0c0340c8080301c00d443c03840d20400f801041c045180070031901c480c400d5001103640c1c043c50725a115814503926600680c0c07840c0c0c8040b01e8103422590070016100520f802406919401c0c8182d044100055069000074003a0300d41003068049001d001d8a8285914400c285002c0e20301d5242c80b026446550a40d0f03101628080810025401000746003000650a010890325290a81288800c800001d0f240c0103540c404a110f0b042440c04680400591904442d17090f0b8800d04540106035207107055406002c0714071503010b1061400c1c0002560207200300401006540c8800d01e01c0c54200580c2d20b081c543e400103070742a82c4004c003c2c4070104040c0c582a000c000002d0290804100342590f920004110b1059000012000ca136042800c907182187d20000604c0301c1d8012015115000215404212042d0404200c403500c00c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 339670845 1250 339669595 339669613
    0x60304051b04090b0f0403050c1504290a1509020406080603060f0105010f0804050304170c040b0303180d11152232120f070f080a021201020903 63
    0x4001071101c00c0780d40e2620700458800300c518208022110280c0c40a80010032070400510b00820303040700385600900c82d0a205040251f80d655941c6062248020100f40284000a0005020200c050803c0e205119030911106c40c10344400b150180d10003611280d0016110391194140720a6203482d45c01600c0c2042c4119100c96944000078943e038010341c1c00034045d0041102103041080c21000380350680b10f0603107960300b0b01e65103a0310403180200c0080080d100e9000500020500c20808407055901516110007410040ad06a04200c104c0750039541c102c1c4a40d20820802d01e401000b01d5104840c040100c4c1d114803440740ea42090351024a003c22641e501442d803c0d06040716030402405401c4146a110040e03408034030041040203641c2075406030b400d4034001d090118403000d50721400d184403001d042083c801200501004255025540c1c008401140c200030603050280c030040010340014600010010215860302c0701d580c0d101c2c4840400a07005503e12051401105d0003501150416040030b070450716040303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 339672095 1250 339670845 339670853
    0x110109050d2303010e13050f0d09082b03020d0f0c2102160b060d0c03051b030c0a06030c051c0203040204050c0a080f1b03010b1315021b040b060304 65
    0x14000d00c03000c6802d28500100c1c0402c015110050b80e05840c000100340e8040d89a081e00d142d076a10440b03030100c900d4411b0b16a1030303001d2001400490740c0f0100d65166841030608160030541004031800c8014524418a03400785050701d80c54256581001c52070a0045c1d4540494010002a1404a0051010b00d0820b02c2d80c050195015400d545407400001b0002c1d00c40d801074511109a00c9180f4003110041d140201203c08101200081a0440d800401014180c01942d66244100c1603a50040d0780c560416444002d400e0004039010030385030000c401504903001480d0000349080258006c0b00205582c65030000c54480c0240f0880f000c075034041502254520500e503407400a0b60045401b02d005909020201c1c4c0d1503450602600c1c00900251170b009000d030b44040d448000305100400e14003500c04040401c00c061000031000314040e1060342a400c0d9940e9800c48166880651030b4400850b140d00402040740e0550b010401d03800100f9070094596040090800103000303044c03015001a070010300082440204 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 339673345 1250 339672095 339672107
    0x604030806131b17010e062704051b030d0c0b070306080601091a0105070305030609060a1d2403071e0b0409050a14060f060c010e0a0318050d0c0501110109050d 70
    0x80b640d0b03684c44560382034100c4c0881102250038442c3c0d0380708407010000702d00300d4a05900d040c2a15500014928400c00b0980907070719204009031801d4030140c1218140c6c004a50184a04a42c209030907001808000e410b403e0092100740030040180c900701c81c040104440c0c91181d04100010030039801210280d50b115044000104440c1c800014603201c1e109005d00700d0750107202074801d40e03074158441504503130300c440900030070341c0001f03008650201e014000401d004400400303c01a540303c4030604586441c1440142d16031103c001c049442499543e03002c0281590700145217000e4031000100ca51944d0384031a9040c08900c455040444880f1000c180450004029441141b00b0449804240910907801a019041c4102551120740107481a03e6a280340d00702a00108100450240001104028561800d0914104c88401ca000a180152560b010b80c01140307000c0280004071030b420031000c099628004080640e100d02d6050068010b841c0032401001c0d0312100e00d0a401c542a56001204988003c2807 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 339674595 1250 339673345 339673391
    0x90a0512031801180311070305010c05221a07110a0603020a0e040506031009032a031418010305070216030503031b0f0a050f0d0c03021b0f060403080613 67
    0x21090820480d5500e014050040401e144c1c5a03600c0c0300c14007121528111103070f48240c50a4000f9110b94a00040080d00c00d200e250340d02e04013030342c0d42034540c040c0c0003804500c11008029507900e072520341001c1c003041c0c0601240d2100c3c1014000d0040d910b4070702d4548a04030b00400c42045074014800003001a4640e01038000308080c14265940c04441c6144004001c1240e006a6045425a11001c81a120241d036684150282e50290420140c7e801a240068221842d440103203d8003c2981c44100304154208480f40c00320010700f00c0c080c0c1000300c01c10070903201c00c2803800e01c54101070701c6502040e000b900a0129506540d01d12011520054480c10300990fa41d2041d140c5140c1c203420040805510344440c1c00f69a030040340e001c0701c1351034410706510403100c1b84c2290283d03c2114404100081d41c48445120309100c00e4030f680c40142c2c887d2900740320304009114141030701100b13030480550203030100b101244940d88180c0c14240508140c680c0b1011998240c3c03241014100540b420a69000040c29510780c058 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 339675845 1250 339674595 339674611
    0x3070501151517090f01090c0f0602150c0a110d080f1305071a040f06020601080c040b0d020103050c0d020d1b03090c090c02030904060e0402130e0312090a051203 71
    0x200581c2c0b0040341010000b0001d695000565091080c02d400c1d03c80220380e6041088881200d18800049904508440140d10100c9400c05011003c0050320982800c01c0010402030024016032280c41c110345074030303100081407002140c4000981c00782c81405900540c503801015011140903580c60300c40944402c5d002d942030400280c0c80c0000a09020300e09e001c510340f840d88034014202291602d02d1002c11540c0c0c800300c4c00a408004e200c045103401e0300b0301401000342820340c000c1442c1d5140210090a007021201104c0c000ea041c0264402c03691560000c0c034056650a180004180d5a4100611101e0043c0e07281c2840117400052040c020080035040b541d2072008030000100c08800034034040c0c0031140c600300010002403146004101803241640708450a00c214010f40c0e28007000000010b0440d5443e07044225081054002c2c00252305011404901c803502c090300410450030240d4002c1d03600d0082d10b4005424006c1c407400141e8401051000c5d012240d0702600700d170580780801351883e51603001120684 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 339677095 1250 339675845 339675881
    0x1207030e0106080c060715091a1603060f060c0302010609050c0a030b0f090115300b0f0102071401030b09040b01061202090a0303110f0609100e03070c09091403070501 73
    0x42040f181c041031501140100500b124a409455980c1030420404031040204040d503d46207040410700a8881c5000703444801340c0d010a903e002c60504039018010701042c01007614204c0184200540b0400100680d0030608103030100745e515190072030240242c0d8000134215404c18040c4400c03010020041d10b00e4030600d46090014010107828040b0300100c000780c080c3e01c410301d02c0c010040e0a0341e802c2c036180c0d48410741c0b400101244e0200180c003000c1ca01000004221103440004044103051449216545001120f0402c5150152030000350b0310041d0b8010704140782c0312020701c90200e138000d40c04040354150161668600c0c2ca05401c11500382d1a0034801c00c0c01240074442a040d52604503c219600319500510b000d040905580302180e883c0121440c41040d80310b100030708184e240c01040841d20a20200b0300800800060041a00c01c0d04c8112805488551051081c600000e2100e1716a42c04e59009000002d990443d5007445044ac0110948001c46400005111000c4c404107410448009010710840 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 339678345 1250 339677095 339677099
    0x20c0d03020906070206130306020703050d060e131202010e01090506040c0e01030c0e04061e0603110406030c0504050c1e040e13050303060405040620130801020309120d021207030e0106 81
    0x2502684100c0ca041c0f0340c490803c04c1400700601d0b111002c0e10040b4000070341081c040d9202c2d682c50007203911598007074011075804034150300415140e004040213482e072200f0741429070a01142c002c9044c00b5144c03004194685800781020b01c24801d5003c40c00c152101e000034012002d030780c20984c0c0c4030f44040e43c065800801c0407a020034440c50740d034000c6040f40c0d80300200c00115440d049003034000440c090001c503605515505003841c400c04500e540f0800080c01c18002900034507600d00341ea1a2a40955020700031810903c0c10004500a2002902169015200030030303555160103c7d4041442a40404601c4001501d8002e401c240741d18064415a0041c418039000c40c0c03501c00d04203c030305402c0c0f4001091a84200001100d41c2856000075400500c42c0d5004104003050701d80c1040104294003038840040c50125a0311060b13460a290b641c01085101e008519600380040e8041c0c41e4011280c003003144400000b01d078204559681d0403100189662011041d2a00300014028081c0440503406a40c543c02d02c500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 339679595 1250 339678345 339678347
    0x8010e06042003031209060601022b030902030319051917070c0f0501050705070302060a0204030209040b0408070816150b030601170106090e0d081303090504240801020c0d 75
    0x1468040d9800c144440740e00308800c03034002d03a01d5a04440440e01400184a0403008414801c0024000e24460010700100d10f0003400080c0380c01289903038280700b415100180045e64603c0041140700e51050301d0081016082400420701d188a54098020441d10800c005260254094054501103880b140d141600080501c4200c1340c0301c48500340b045540c032090000c2025540201c4504610398820070714000000740f039407105800c640048460b403011510000744401019418007030350741d202688a204508150842e00401c000ca1402000203001002403404541440314840564a01590000780d095031927070081094108200c10410860303990752640e83c4070b0707160f07a81402402124107015004004581c0703011542d6040701d030083d0b1441c98030355031180040307156201402070042c40c3c441d00008000c10361000320001c095100c010302001045c0382d130207180c0c0d001a501911140031644c1c100c4000ca8070702d0911030300301d564016101c00d107112411800c5001a80140c10f40203420004a100d0a41b1a01c1000c4c0c08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 339680845 1250 339679595 339679603
    0x70807020706093803010f05150a0305180f160902210604110c21030f1504270209070f02070312030b06130f0510020d030902030c03120408010e 63
    0x900c07008126462402e00400700c124013104c0020204002c50b60100800b00b07610001641203891900003420000014020181000f4842000700015104a100000d0404900184d80a002860810561640c01190079850b0003c0c644c45810f2070300084c1d800000204007029664141f0307005049030345511440c00241c2c0355440c82622040c203030b1103030704255078040f807845000c20340001012941d1140e03031034003c4451107110b00098101200002d0040c2031b2210122200415003054803c05205410204200710114052031281c3da0003039420440202608121030020b4003401e041145103501040b41d0201603580310640041b01c0c800340c02918020070a07100c9800882d51190401030210142c7c2c040c03102000018500302400c80e00c6405031400090481240000804a034468030f440100411000c0091045403260071545000f003030125101919000c1c40e201c007035104c0d1b040407122014590340e0041c104c107544003405003000079240102074412002041741c0c1001c05030824000c0c81c0882d0301c0c1c41c8091101d244002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 339682095 1250 339680845 339680849
    0x110603101e0f061412060111010f02120606090607080708190203121014010c0c090c0f020f0a020d060513060e0d020120030c0a02070801020301031a090d140a140c01050708070207 78
    0x103102945012200255503110b0f80014040034104a07440740c0c03090440d2004e1180344500f2101000145e070310380000c0ccc5d10114800b0b010300359601c10b4904003c424059907883c002c82e08859803149050752580c0740c505042c0303624000c4011a18500e501ba0074004010748d030120041528143c40080072206484910881c0440c01300c5009204601940003003199581d030242d102c110b4224411900c465a00d501e03007003060f05891014886c140442d250320040303003070389805102010b104205480108100150707500028600d610110020348055030320340c00f003015080704010010a60b40c00c00d00034800d007401070206959070a00e0f81078500040d4602100e11401e0901d184483c01031010700965642561140c86031100103900801e000b4007940b0034200006031694007800170314025030281c00b0792003108210010030f414440c8010201c890681010916503c8030340c000c81c8082c0038803003450b11262031700c41254099030310441d640284a01c505021030004840a01504054450a195543e0030241e03140c0440a0346e6402141c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 339683345 1250 339682095 339682127
    0x200a0605030402210714121b150715090303090b0405070501120506060d0b03190b060120061609030209270a030f2a060501030302060105010c110603101e0f06 69
    0x112000f0810000144051246c03a00700404005050340300c07c403220f2418002d81c5c40d541d01e0003442c04400110f03180210450550220301c609280c68403078182d5a4500aa8004a440340c9036907840f5241c5091600c00c0e0300a0344000e50040700b00101d07041074100580c1d1840b2a101e07160004645200340d4110329001d000e801d00a48010b440141072040e40540c40e009081c0c01103e45e9014480c0c040092038080e250000c0062850280512407020f041800004008141d041c290419240c141154040900030010301554803102e8034082e010540e1140c81304665040d070550010754440c070040c046c80341035404501162840c01501303004904020b10500d00c07944486c1d0168001d401700e5681e294515a480c0100b0010442e40d03401c820884000c40403007100f000111000c28240da81607a0350380140b0802d41c04104081c05080d00b4240307030058038030942c0d400d40078501c48075002d07010314004400704d103400386c2a441d0500030348614050302c82d422946d0228000d220900b1300c9000180e55524000161841c05601d80955852038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 339684595 1250 339683345 339683353
    0x7050303070b060409020a030605011a1812010e030f1801080108030a080a061505030f07090b040b0c070b0a02030d0515011b0f02090a0b0102070b0f030103200a060503040221 76
    0x70a4a03182554103008210704d42158454940b4001a999004d041010794819100050254180031224503074005841d501403114000b0000c0003526444078005c007000c04030441c5c0c6001c0e1524905c0030140175146036406181184000b21360040c2014203140a8a00c0800342c0001c2101100e4000045a86100c01e20401119800c100314240e245445840c0b032691206940d01d010820941e0703501c1303410400385c603d640b8400165000c024814042500c0040c1d503000082c2d0301d4010000303810310518002c50b00c1203200b20a000d043c0007d20041009007405138800030404076100d02c0c2c40352020000a91030b0b90005005a031181d2901c0000b80c400b551080020884030010b80d6003074829000030286030707401d1083d080b09880c00b400c0d500c01c0400503950100d05600c121403004020a0401d030303080c00640340100640000c00300d40307014005101c0b801010703425681184e400030710a01c1c004e501d041800c000034095042d25a0404000c88000c510f0030b420100850180d442a940e00b88880e4040c070701122031203003d070201142504 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 339685845 1250 339684595 339684607
    0x804022211042d062106030507120b1f18091a0609180a060c03090c0306061703030f04030f0903080a0503040b07050a0e04020d020d0603051e120306010807050405030115080106060207050303 83
    0x40314a240705e440382c1d140a0000b10706403292540d91404a0650203440e06c1e030030500c0ca031403c2200301000c107500701c1e04044440030f40300d110340d6140c2440031050007900e1070145481c105182c680a42d0304800e07030198110104400e845005003489802c1c80d41102c6030340c00703a594000468880b4401404154a44a511002e028110400d94070f800c080c11810000a04154803015007601090401103600b00940c41047c0c0000c00910f010f0140c10f42075010602c41104d41c10900801c030808403101e5142e0ba100794940f0f4100800c0e8441d0784107980d5500d55401c007902c04500800c142103103581280065000302d0141005941d280c0d40c5080c02c4446208002900700055000c40d8201001d0805030081c081c0300c00407160141c100b8040e0b0964004a903c1c81d03009840591080c0c04071035088224007042d05641030b9107400341c100c20b4207010003443c8510028080c181000003c5000500300d510130010344016000080003403115006490301403681442c0360041e141380d94a0040009011400050020101c9a014002d14204030b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 339687095 1250 339685845 339685877
    0x503150d03050d020d0608011505151b0304080c04051356010b0304081209011d03030402010809031306030b0a05220c0804022211042d06 60
    0x2510104118203019082c001c0000f00d05181c0050540041c0f0840e0014600d07280081c844d0954004100800201d201c0c1841070050b0b8a8500088081e0204070a40582d943c2000030b41750301d5800046038583c540d020124001c02c8007240401c00c40e0541e9001c0750305211540f55220141c0300d09500c00030003480c0b20603188902840050301040b080644500c000c50144010b0b0308007441810102550010308010b00c00c1c03200c41954004000c1d580c3c00f511a41d11028190326107542c1d441c0c0c062180c186048117901da01c4c1c00084035050b01f500302e6000e0074036409a450200c200030844542da50401e44040f030115400e00c2c00500b401000109a406c4207495584600d005850104190000c0071001c480319004003141c10040745585a0722035000311084941100880026503150403001c681e41c031958a402c1009640c14040542c0d00c898651080d0901600c0c024100c040c4a6004401000e005503006012500441e00003420200c2580c3c0e415100881030100c2180170b0000300b480380d002d10501408002c80d804a02e000e40381 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 339688345 1250 339687095 339687109
    0x9090601031e05100303022a150c010204181d121308150f070305010312030c05070b0a0b030111090901120311010e01020901120b010f0e010516060f0b01050315 70
    0x76100d8418004030010050212819103c084076440880070b05624204101a810450410b2031840070140c07403c440000c544499000ca00340202921400407422000c80200300e0034202c03807192034480021940c0f1651290506845c0380c083d447e20515507d40410806c08080349d1034254a4003040c0c1c409001d00003150600b100e003542000e20b6440c0342c00384c2c9100119040204000d89005000103030200c01d01464418010b6621102c0140301008041c1080010000560000036500015006040100d000140d1407011200c5004001c005400e00005909025149180d90b201c1101d0410560090003804105178100c0e04600c50f41030b6094009408070b004103e00500ea00030010014820314040d520004a094070a00303584880f01c58070000c0c0d60000d1894407a40c0c00000c450780c030380f8a07544180048400c0b8400a8112921015904240000e070303202e5540e00d82c4113004035200b0b105400042035a5103c1424114001c10803941071008807880e0034281180356001d02c09485c07040010409414244050100b48400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 339689595 1250 339688345 339688361
    0x60601080c040f0b09190e0a050c160303090c210f02060903060403020601050319150b030c10091827020415060f0e0a0b041a040306020403030903170909060103 70
    0x301e041c1070201080f10140341186030300520b0078646603500c9001e03000c1040520361a01c000c801804908500410100c59107055956225441c6c1d00c0008140e59904c0004015219980d86211525190382c03c0034205a0583d00030150540203d2201060644450002ca020918030754800903c0c60078941000c006442e54160450390391016241c00d00300005000800e1070494251411000758101c070b4018403050a00700914500c0728586800c000d02139040c0d403544826450f40303031010f404040c3c860207901810b850422001da844040a41000000403a0450003001010a13005584160340c050415001101d0f16010344510301c40c558200031070321216100d90901c0c0416542049811a850300401544080d9440c0c1c1d8400038a0283c41c1d0380707503008503d00c00070800c0f11003c0d003451182d040300c0428010070400c1c07001c0e1001d9400521400e01443d066945c069140e01496000130280fa00000f008401c2550081c580c400b246c0c030450360940328403103008881f0b07864081da01c0c07500c0d000100c0000048440d03101ea0071141c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 339690845 1250 339689595 339689611
    0x3120a0209150c011104031a060409030f110a0203100f060806011a0d060905040803071704030e0409140a0606050a090603030e01030c0e100e010f0203070506340f0e03030c06060108 79
    0x4082c00c00ea04805d665411643c07064030540a02c2d00124440e0001074402c0790720050445041014586684e40070b02504065600103040000fa2007503482042c008104a141c11900101100d8440080e5084030001e0100b072040c101c9080d09080740010b5450700060114181d0352818440003440070781c403002084a400c1101c0b094007507038a6020010f03640d2001d2160780e00a5005200d0241e884c83d1082c409045000c84842c4031040d00c0300002084082a485000e05110b41011240440c0801c03050400410400030b800105140380142c40c100b1f000c0140300d6110a00315201924181c451a646400c08000c0703400c1d80c440900466a840c0140400f0361003075106c02c00b0f500f1030703041114410302201c021984079941440ba82011644c030101c848440d41c0c001c81581e001c00c01901c001c40c5084201e51f1a50b480300000350004045118150995440608070990024110280b030700320303002e09801000042c000701000e144100400c1d00b401902086060103c2142c3c03101d9a0740d4000c0103540c81e070000454a6a0005100308 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 339692095 1250 339690845 339690851
    0xd051c1205070203090109060c0c051c02060c0d020c090714030a02041d0415020c0318030f06090a110901060503070e01050412110a0503030702101202040905010803120a0209150c01 79
    0x10024a400d4456035004204a034000e6031203903c00c6001416060040d0002020300071170746140f4001885003440031042c2c44044d16182021100d03440400070312640b00703900a62020000c03600c03c483e40d000107007001103c1c01950884283c10354030400c0c040341a1099800000160314402c0021030298484000c41d01300108540040c94903903070740780d018620a0354900108603000181d00303000c00d0010002d4401c0110704005002c514111007608680d0f81ca100c0e03c044a0064281c1c140100101da070184000440111003400352020b9140c402500c0e91a400c05e81d404842014041d408030902e41040031982c0d05a518580700c4c2840d64603900c0046c0c890082d400035840c1081401c01000c102c8000000c10310b428184036464800700c580340303482008106502c1d40c00c1640a5441808030304056079500b07206000c41129814000e00d6010107000c064003910554000390340722410400000b560744400001002c02c034119a80e00b11132529035190080507449516070850340311883c8030780b121908680000900d6182d140070000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 339693345 1250 339692095 339692117
    0xb070308092404110301020c0712060207020405270c181b0d0614030d0905012d0c060b0d0209070e03100509030307090801021201030f06140a0b010e0d051c 68
    0x142035250030714040c07840e4004105000400104e41c111146100c4210f0080d428040700e005510794541043c0f06421023280703100a12004d00a50f81e0484400d0fa070081c005105a18141009a03002050b42c00e42c18001007003016408540e040104903c01d007004010000d41c0a034000e464814402c1c2d00182860462040c00b000440c0244501802041e4610034140e003c18054030300340b200c000410000a031380e80a50882d800354503500d1f45c01042c3c07905603038090034102400c15114040e00080c403014203ca02c03807000003000c20042e064110030801c100e40c0c42a0420b00503038428500348a91250301c024000c0d00728580c040842c40385805a140000a0030010f01150140d40000440380305503070068604c0f0281c1e802c000144110300b42d011341d6200107829040001d6140054100006011140505c4041c161700e0301d454080040101c030750405a5041108801c80b181030910300400001000042010b5002c500b01d255000103500308074104003c00740d080340140c003050110b5442c801e00c00f13990f911a0020002540b4031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 339694595 1250 339693345 339693373
    0x30706022b031e0c0e0306102115090b0109090203060708090a0b01030f051c1706060c010227030c090103060c0c0f03050301180216021002030c03040e1f0b07030809 72
    0x10206000980c4202082d0481603580207840e1086400a150007900147c0030410303e41560404c24084490600c9107240d062690b5000140641481c00014000c00c90095003503968170040c0c02041606000718510940b50341d0703884018044400c01c0c00029059000a4009a065805407050ba43e100890505403403283c1c2070b0341e8030b0344076039000ad0300100c88403980b511420b01803040030070240380400c4062810440804081c3d4015020030340b0442042c580c100c548000a096480d144c003030f16070064944000f90340fa400700c0410944150303021207240e404541010072084036464001500b920000000d450711005909640b1040c000c2c04103002e640c800e01080e0042c00c8000741284c4111902c5c2400f954445480e94106406007091002c0c54443c0c610850050109610345450040d8844556034122502c8454582000083c3d0842c050b40001c04914000410000340c01105030b0903a601c941c107407a0343c210190150b000c51419450b11405080a1a0000e00100c400607000b01092900003a4490881d05200d05a0613 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 339695845 1250 339694595 339694631
    0x12011508010e010e0610030609020a2301030e071d15030303010b0d14160e0a0e2703030c2502040c0c060c0f0e010c060608100b030706022b03 62
    0x8066010360390b44090003451110284100c0b5032013000343d070241ca05401c14060050380741c2090b000240c0000e940300e0344d03402156150343c1c08200406104105170116500a8108110559003001c030f01e01013802d0510000900300040b0f22501500c007102340c95070340d400031038820040c1d0680040c0301e49034a80481241c0301c0c0580d0104042e500802c100d10103d580c5000c2c0d01d01c44400c0d513200c0c41031003040105040c10312090704a1021441020295880e0000404070780400141d9800c44551015502000c00414002061800072610a0307016203400e8a020500d4913200c0c140d500c1c4800c42c1d030141807001c10300c07680d07a0082c004140d980e0b00140c0804104d421495940000303003125101480030001c64540c058000400110340541c0480302c0d1070f0f040c03140058607101d0010344004410380b040303810081174a622404001d010381c800c1003d44911800c030303904800c151242000403da0802424402c2c4540c080000d00b85100003900c0c0d40600b5007030741d800802015201c8014500d400d4030141810306403901c18003c03101031155 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 339697095 1250 339695845 339695849
    0x6030501090c08070905010f05060c10060303030c0f020304081203040c1806030605090d120c0909090f1a1302130e03070b10051005030c070326100605090d02120115 72
    0x352010240b81c0c6001182031500301d0341d901214002d400c00f0010494a4101201c001c1103400640d203441e551080c2c0051181841c07148000712088515248001c0306069044d44603c1103140141c4500410b44c0e0074940683e030b40d0040f4840c10b801b40d4080c2c0340690a0101d170001442d0018803139004e54100c15103a21507241500409151040741640d90002042402018094103802840400240004d81900c040041c004100341648c250890b40791404410788910030350010380102040d900c10000500c3e240b800840c0c44090340000d40fa0310700c40c080c1c01e030150080124224098850304800030a100600d600780001b40d0000000145120303134a03002c0241c43d420a0000b00131040c8100c900028605c2d045180301e8051480b500170034090f12000e02d407001c005802004498100c3c035030800c1d8980ba03003020301d000c6901c51400c810043c0d0384050305440182d02510718446d0303801486400c800010640d202e0740d00b11641e00070042c00301d51010b428505200076051000700c00f980ca4004000104800c004058200c846070039903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 339698345 1250 339697095 339697103
    0x702090a0e0f030d1505060909060f06090d0f050d0503060307030f06141f06030b010c02010813020303120a060602010b0f040509120f090a050a031a0705070210050a08090a03051c0603050109 83
    0x340c0481c602c020151171420000d0b10040707079072a0401c2c064901284c50700c040244014041d040c116000c1540d9620386040d07400700b01d001441005052160b00d4000301b811040300048906124400c0011201c50044041d03e20440e40035004001d020700e15105c0301070001700801c0503208103a41e039101c41100c2c103110710313058031800c1c45400f048014480f0030000306e01060243d201c1001c00d40b6148449629a03800480b07050041d8091809200b01d072a00e4440c01189082e801000394144000260742801800582e00355100d1080c07080d0400005544001c243d0a841011040e0355105030302601100e41403030140d0180390007000c1c4100b1512404000c05002c4880e0784070843c5059156804151049039140c50115603029000540e10f005946145070f0796250806010078150252102101c0000e4000388a0b0003552501038008110010320261260060310710380c13010480d030b00050b0703190300054441c40c00002d5180b1042d900d0354070036140c41c0032100b00c11150803c568520b80b0040e02d1fa800080071074000d000364102e036405 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 339699595 1250 339698345 339698351
    0x17070f0c03060501180e0714030f010c0e01080a0b0a03081803060c0d1d100207080f0a0504030210030c020a0201180e100e160e0f040207210201050106050702090a0e0f030d 75
    0x10181c84500c03e036210011103103554244554020b0004002c03880d14101d0f011585001e031030316080d50000c1e0501c2e2a40654ac86158a842c401c0700650f54000d0440da840d1200383c80340306040d100c48680030213490048002a811102c01c0030300304000703410b010060459803501c6070741002c5c04150000107420100142d4821151000119001500100341c1c820f410700d4260b0442070004104d020003610762901c07103004007106500ea010809a06200900c000c0740e003018680312200b5900c40d14080c0140250b041800142d01810070f40303100c509254085c0c8940300c0140307044e40040c800510998011207001e25003801e1200241460400090003018070303070364980900f9050040d03031810f6090507010902c2cdda50007400c50500b02240340f035012815400c4040c0000503074050740c1c04c003640d414580100300a80304510000f001111103600c084200303c0e41195909049a01350b00910541e60f0b00e6200304d65901032104041d51128401001c00c884900f5a40702d40720802c0d0b600d0a848910104000d010f056804c4500c0c0040d00740d031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 339700845 1250 339699595 339699599
    0xb09100602010e0a0b0114010201061509060f08150409050f0f030d200a050c0715020d0f03021c0b03150c130509010f0e0612030d020c01060f0317070f0c03060501 71
    0x14080c0104083d10380083c00904403001207466040c0e00010600c00d2105007115075541c2c2507664400c0d081803016120082c0c40590005114030300900004451041000140ea0b024078402010b200b0540b0b64001c0300c011800c0c1c0d42c54250102000000d00401038100c41d00d102c0c010100c0168001440031803620829000035544a501d040e0b140c10540c0c0d20703520010b0b010b0340b4010700c00d2a071030000f80941e00042c0040c030744280c6a0aa209125251140c5904203c42c3c00480e1444500340365070000d08040c1022103591078030070400d6102400e909030702079080c0d00c3d10194041d5800718812150355100c1010740c0401002c442d40c1c191141c110505102040d00d00c5091a007000809080c6442809000c400170602910761038240c0d85090003120914155000b0314100080d140d0200b0542c0d5210030340d0b82d003400710740000d0366a100f1001410100a500c2142c0461565003000b000058201c0195007407400c80c4d801006900d080d031509100c01d00d441d44001012950303d40b06501303003004501d4010b0b900c4051841045c001610754 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 339702095 1250 339700845 339700847
    0x303040b070e130f090b090106060503070f03020d1506030c030b090a020708070f08070c0b040e040803040609050d1107051507060908120f06040f0c020a030e0319050c120a0507180b091006 82
    0x180080c10340842342c1c100641000780503808030031a580414545003080c00c2e0b00303000c1001c8010748111031011807a5401d00c072440d2a5007110601c200100c1d03015071001c210081c081d00050301958900700702c2d035620500712000181f0702d00998004118103889002c0381440d0031180e546030b240304620280c05a800b0400440c5420070408181648000f4241040c80e6038181450b14500c44190300c00180020640076010020508018251704010517291b40301d015503200d4a8500d50060860150100c803202a2080140004150401c07207084030003400421851450596151103100107459000c0b8104c62800c410885481c0010282c8450b5002c0c0d6002d64a00d101070a00e4130820007951070912200742c03864504032400c070140380c000030300990190b41801c0030300d800024a000a420181d14158071802c0782e14000d4210b04020001c903280169030421100200d80c41c01803901d032560b0304030820000309160700022091080c0d045114207001030700c545500203e101002d44001c5031038440190341c282c8014280410a0040c0303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 339703345 1250 339702095 339702113
    0xa0e09070801020309030334030b0a0503030c10051803040519180902011205010b1204080f0c01020409060807060909050901150b18090c0d0504060207020a0e0115020303040b070e130f09 81
    0x600741c810178504041c00d40310381c0d40840b54500f6404061694074401c5d04892f0f141c80c042200203000050582c3d4803001c0411a0584601c2d440b224100000c1c076180c000380200940d90b0180c0c18016400c1d00441c109405c02c400c0c4907003c42c4169010044455184002a552003540844904106070100103e02510300e071001424019260303400a204078206401880b003031401505550610384e100d00300701c810f62545d0400302020703c11002c11340b414980c00541ea80a01c00150001c200301c480c800c0e410816144d4500005440300d18a014030310026035418001c000424440c3c0200d44c000c3c41000002079022a4801c0304a140c52141e0303c501d03c50361003c1980c0c1c2204c440c101445010030350a5405080500e01802003012034810145055206951000414140100c03075064441446d4040e1900e00080d4846c17107800d110380401d2042e9000c0c00350008021088a05c04001c1e80d000e1540000005c0158a84070340c2510200c1124000c0ba40010a42d012040030a5050003200c80e0003141c01c80005850545042c02645 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 339704595 1250 339703345 339703381
    0xc0a0201050c090d080d0e0102030a090215041203120612120f08160c0305040f030c17010b0303121302150a0f02030903060615120705030f090a020a0e090708010203090303 75
    0x30000c0180a10040d640b01d895542c40744ea680809016a0780700c1081001000740b96081c6030b0981b961010040155030b00c5242d201c944814001c03114080c50003200650b41d04a4400e5018441c2900c0c0250f0f17080700001e0291002e000c14110440c0b010880d551211100e043c41b4000c51003c1c2c5a40f109000c01001540d023060814407070008901d4918038510f01b01c44615180f54220b070802e0204441c42c000a414140b00310700340e501914042074100c0c0c50555904203282c2801d202c0c0603500c0504a0492a403117603070814420300c410312101401842c00c18480302d4a82d000d440000302040c00341034140d14903c0c01641c4501041c405c0a038110b03696070f12012030110040c005a0b100d070700102036500c10020601c0c80d950000300540d1100301142c404468170b404130407010050240c0104040340300c2400e41488605e68001010318841c04a464445495503603004030b059640125110294010940c14000c1c4000d11214003603c0d4801c2d000002c42e0416950361b15020f0883c1d00454010f08583c00220900081008000300c5000b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 339705845 1250 339704595 339704611
    0x312070e090f01170708060901020714070f0e04061407030515011103070b0a0908040605070521030412050f0406212903010603060c0f08060613050105031504050c0a020105 75
    0x440c1d00e40740b04001404081030080e000e07140854801200412400c02100000e0030304502034031060f04005441601039002104110f031142c40c1980c0743d80c990131001480404079020710354485185d03480c0c425584e51031a0060003e44020340c44e8506c13110b00c59042c400c010300400565a0000725840e040710818000002011a2410005150a107885a00f000410340b03507055000614150327562074859030390000f861400070003440c40501180002d03120783c003c030103440454064019101949a20070301d4144d000c80c0c02c1c040d02814802800802d000c1003030110180130320315280c00e00b40d00d064200145c500c1c0c0754001d907000c1c10004503510b07e081501400d1413000c04000030200300074411510001e0802c44880d0b000464a4510010145120120381e4250044002140c2200701084000800e2000030b06100b21603c041011550a2000c01c1c90707818003a04442c42c100d0700301e4a1030004d60901d80112041c2d400503190702011003030801821282d0380c4602c038040c083d1002c20182031b955102c02401038251107005180709 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 339707095 1250 339705845 339705859
    0x2090918100218240a050912070807090c0903080a0e0d02040e030c0f1b0d1b06050a0f1812060b06030c070311070503060105091e0c04080c060702100c050a050312070e 73
    0x100022131800c1c181c03400381556090050721103409030082a900004e803840451540b03e181000901070402041000c20f94220100502c0218418102900c3c20111840b00910356801000480d442500c14804000f05a1000b4522003000e217641c0c0002d410f45a8184141041e500006010301c5104010441014a0100a006454106071005c1c0800100a103081850b01942d081c41e070580411682607000061600c40c1d4403003072425529080d000b802a00b00c0035121003c1901d0000203410b0b80e000303401041e1851450600f10030641d0504450000407082500c0c02c59625840b204480c10503500c52000e18892144001010345400d00e5041c000d190200c3e4003000c0c1c0b144c3d00514014802610042481d038191503080d01c04038170580300c001c000849801071140070318001a400c070500c014101098000c004031100c000031140700172042010000680328010000b076215543e2940318104500844002c00c1c0e5900450039545141000e0720f916056501100c45441c1040603401000b507902d8100b05e40702400031080e1a50 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 339708345 1250 339707095 339707149
    0x13031e03021801021209060307090e0907030b130c0b09030f0316060501050603010b0d05070e0310050106080703020a021507050c07030f031803030215060a090c020309090a02090918100218 82
    0x80b070721754815655001c0c0142c00c0000052041400740101d00000d0654070f040260618041d001c00703484450724082160684840f030082070032855807165404205400c01081080c092404001502e1540003c0710250503010340102101002d20501c0945030541020100719070b110700700c3c500b0030101d54050f00000d101d91424001031108041c0c100035210b000301402800a80da413141d0800f07581010703046400a40c984205445170241101ca42c100d00d040701d01940b40c032010350b21002d00c15416800b0782c00c202001a03200c0071041e10704060310202d8030b4118001d420000e2604682050403400c10070150415201013140100d03400400d640192401d0020003007902c001c2035103003190f40003520340c1c1030406968041d090000201c1c015507502018040148505001049400140c03040a51a600840301e000e125800800c00120780c403925000f00c0300340f10401002c5000f0f507502d28030fa027072003044181d40d14204d074441c000220042e11801c0c40100007694605021000b180d201c0005c100214516030300c1421000040194 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 339709595 1250 339708345 339708373
    0x50a0b010f03081c1508010c0e09060105180a0b0c030316020d05040315060806090a11030106080a02060a0c050d0e030c01020d09060507020f0303071b0611030313031e0302180102 78
    0x140c0f03581c0030f4202c91484c0030b94050000600980340d0081a09111a900f0300b00140c0344005500c0034061400302e44554407542c0c144d50030000f4141e8200c0782e40d808a80104071505d100042d001001c0070601000b80440e403d551903001c0144607800110381c1903c560b00c00400d01ca00d40958a208000143c00303440145001c0c0c2d900c0341c0c020603601591100404000c3c0d01c4041c4c010b22400d0b40c200c48040c100d141c0c120392061070865005aa684000c0009071550801d0000c0b141d898103041c060710703082da07120340000c080b4401580d0900009074860540101000045100c90b8001074050200040003045d9503a2a1119030940701018100410701c10a641076502c040b49098403207400028000c200c0d04a030400d207841d4900c9001140e9844800400c041e0306000014000040142c00c0151221035440c800d00b6020f9291202d4065030b424410a0201c48030768428000900d601e030032600322034452403281c0787c5a40c0142d10f080c00d454145004110103404250082422050b02d00e01c0300a19000b40b500b48000d0512041d4120 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 339710845 1250 339709595 339709597
    0x31a180a0512030712150f1212110a060f0b2806030c021905061e010602030711120f101a0a090c0e100804021503010302090f070318050a0b010f0308 65
    0x40c0c0c540b0600c004800130b004180218a075003902d656440c0c2c144520001d0042d21880b040c4a0b0007081405083c1031000700b6003d440d90030b800c4060354010040440b00b66020350603109881113070044d00942c4902a5040005415805204200c0d2143c01001c50400d58003001c0007000000700c0741403010712070141d00b000c1045003442203a004a603140d080c00200308030001c00c01c900701030840480c000721005441100c810440c0c001403241c4900d4044902c0030200062890300506500e0a1203080010790051101001198010340c0848401000504916002c2c2280c0101424418018407041c0b042e000810441f120300c0742ca00401007600481101d00075034122000002c0c51092803406014001070b036510039110428020b2407441c182c058000e0900c646000c034504002c0c4003070011202240103095010b003080c0410380480030b403410b0b29802003903150b5517500c1c01640081d119005224008054460300d03616141d0b03000c8800746424500030405000803214074104000c050350b040c0d2221074400200d800c1040481e44100c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 339712095 1250 339710845 339710863
    0x50d1104050601031e0504151406030607020d0c06050c1c050610110d0809160e0108011413060504050c0406061107080a0b06100519090321080a0213031a180a05 70
    0xd07400286d1911141011816002d200e151000c030f881c07519081c0e10705114050002c51007650100c0c116113950b0313030700b040490701e42c0003031008c00c0040f4000c011413000003011900030b42d90143c0c240225038105407150b085840602004407640600c19680c105014803824410901c06608003e8103240903c0d500d1480640da60b403141d103c0400c104400c04002c2996400140000180d00354407401079000d46840d0038850b4107170369080c03049000b150310b08102100e900100407006403041502c0340000c0003041c81034a0b49800703481c00420442d83c5000d110442d0280d99102d1013080040c01c441d5035007403406000007591901d00889600b02c415140c1c0030012803800603118940e040d9220805490540760075602040a4030301e8050a02c40804041c0902d146101095000158804980c09040b143d044241074160042a2803807031404100055864000518a21041c1e00202030401001c9184640543d032034032000c2c00300100c105a010285549003e105407005220901810504590054110304606990341c9a44034200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 339713345 1250 339712095 339712151
    0xf01080c0a110c04050906100e070e101107030b18070f05011404030605010e07120e250b0d0203040512121609030b04050f010606090501200106050d110405060103 71
    0x501d0940242c5803051003010b0f0102d10181c018400781c1002580c8944a0300100e402c904c1c0c03000329100014007130160020300c0703025003220303241c080c5900e61400621503075a0800c5030180c148100c0e403400701c030400303000c00a080c000e43c00f50b40035843d141404040e50000c110984203000c0c143d40203207014000d10400c0c0c10b04404036102400e124000012101a0003214001c84c0d10141c841842e00c0000540c981c40340c6001846455981c0c0c610368440318000224048070f0001003900540d5104100141c1980c0000d507105d4641110455110221341da904081e00003513001c0a042c4168980101c2070104214080022840390b8440c00021428100204c0b44035045050041420702850340303a00c0f0202c40c05008180c240c0246800c81c4221070310340b500f0304180c0d5813000da0708200e842541c0f074114001541c0d4440c01c0c0040a8420503907621107088020042e00c1690314440400410340e540e900c8000481d907550035a9610100e00c03500b083c82c54107a0308010442140d100402684c185410314007030150f1000a17480c0f801980c011 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 339714595 1250 339713345 339713357
    0x11505040f0b071a01030303020304053a020709060602010b030f060606070b060d0b0a02071a01050105040509090c040e0d08070c08041217030c0c06011d1b07050706030b0f01080c0a 79
    0xba01304640c0d4651055540320a08980300008000d15905800842c410f038082c07000c942400c840118240103240014054505258030010340074a4000311640e0b642030401903204030b440b45900c6128490440b01264458800341c2e45d248034416103402d0a200d140075264518000d440286088001b00e4070a00c00c6120040c20074a070310000070b02c25078078100c08800050700913500c81000d2401e42d000000940c03104806030340d8502840810710b406003084003514161081a503130075090610b04414494090b00191101e001805202005201504e980c400c000c190164100100210300f001000540481800381600c010806035114201c0403031010300854040f285482d079a03103952020350403c14070b2500056811801694000300b40300310403446101601031407070380c40243e03600340c2d0b80c3d181082030070091100f02c0328a000e40303440051a450240160143c44020510b9031500e0084a69582400c1a48540103040880c0ea10601c151160400003020324891b942824807140301d0a05d2444801540110140d082c10805 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 339715845 1250 339714595 339714607
    0xf010b1606060b0406170f04050d0c1a0c090a06030204150c03020c0a14040e060105030c06091206010308040e0109020a0c0b0606160804171c0305060a1d011505040f0b 73
    0x2101c2d4040001000c00602080d100c81e200c04004100031101c0840f52407074000107000c81c030004484142c55006070b9001c00205030102441c501a90b003411f41103400d684210040c1c00403100441901e900e03030322030903058840f81d56504884040041404594200500301413044c081806884c200703525000e501441c1c0c0c102110043c1540c50103c4c6003103403944000390040341d50728002405c2001c2d00c103820b0020030212418000003d403d0911a03955209101d0b05505511001180a06041400051007018005895003074141560140c0c02e103030080030790089811000c0000c00700403d62401d90845c0c00f4140b26a41589808440d4400804000c00c8203800303040d0720b0071070020600d16a6003201315070036034038070b135003034844814460a0517582c50300203109020401c0500b1000d011003000c041f455140140c011070b2507600b407495621044000307010041815400a0b660000860b010b00802c400c00100c4c1804a5840c01540c1400358030801d40146103c84424404e00780428841c055400340100142c691105090ba1070304 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 339717095 1250 339715845 339715853
    0x3183008190905030d09140309010203250b040b0604050601030e0604170903012301061701090213050603130c0605040b070615051008010306050601080f0403050c0109080a020f060f010b16 82
    0x1084030b03008010303100c0014112002c02c82c54100085060055886004107210f109400b512480740001160050700708200d0007000450600000c1840c0d203410743c4031011170b0300699801e8210ba80584d81a074820707000a04000d968505030080f00c1d072180c0203180a000c400070f0161815540c83c40034200501e510905400b0044003414882034861000c40280280306040c0300d0826000840c05000509100e140290b0020600074000e07000c00240e4000e035110060203a00e452004d1000b500290300050b0603092400c80080c0650780d0714082c40c001c1d00c16907000102c50321a86040c000c03004c000d511002c14010140300801031080c07090162118a80c005002042058040a54225000d03403034111300d40c000c0c400e80131a840f15510500700b83c140c80c483ea17400c0101d500c5490055414a80807104c510b00030608500140000c1d1150b40604000c010801c00841e56514a80d2030f601d01c0d0b001035102000580c0f0038008101050010071000380c00c10030164208020f541000c100c0b10079031058500395000d50819280f024100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 339718345 1250 339717095 339717101
    0x15090207020d17040e0f06150f0f0301140f030705062d0301030819020c0a06110109020a381b10050f010f090b0d11010318300819 57
    0xa50100400028048410903052180c0003401175aa007604c07010000340f0908024115140210001841d500d000d42d491071214032903a002c0e40f0340140d0f40c042400b03046500d892440103507001c1d0481d164031113031544206e010302440c0412034210324402e07442004c003004252210000c0340d1061038011a071812806003206a100603400080000b114400f0000c00002444855005058460022902c181040868610417642c0d0180f81e05c1c1c8603407100c24400104450b40c06451031080e07408005002107101c00c41a00020309a1003264000341055001da90950041d0401c00c40c849c06200c00115422480401000c0c41c54160190168400002403002c002101d800c804008419a51403801c00c04c0c42945008408102070500c00c1c862028150800784021031003001038090380b094200007412800c000c0000d500d401c4c134000903000c2004d0515945225441451420200318885140682006d162a50009040e00c040340350a0000f01400e42095150b528110352000180e0b4209006055240640b84055100d04c01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 339719595 1250 339718345 339718369
    0x20d140106050a0306020d05090f060c18030a050106080c041e0b01020724090b0702010518010e0a0801090b150901090c02120706090506101a071b060203070b09011509020702 76
    0x400403d0320800820807416400803d802c680c920350907c426112907007483c0d80d03100c010310003000359042180010803010700b070006080c0209031030000007906803040012a04205194200366040d9450780024030108800704840310061605031820840802c038a180c3d603140c0f09542c4150007005480d04498000ca0784200310210190500c03207003044036030f0304912403001078241003400740c004200000b0000940480c00c9055804158040e101c1c00d01c0c0c60480044040c00005d4514414103002c060700c086000c41c1c407804120380c09000321000004070103065007800034104800520500320304180b130851602c1c917141c41001e141141c0c03d42d440458501a610700c260700742403041e14550120b5802003280c505000e03003600000d0700280200c00f0749034a030322529108418680f03903000e0980160880610380c0c40801c512401004468001c4409d05a1000801500b40d030009880d4040401680046078880a02c607181c1030340d40d085000700c0000c008004009002601c910918845c1c1c02000ba8085a8001591580304540c01c1e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 339720845 1250 339719595 339719599
    0x80105100e0d0515040b16080406200f07051c140703091d01060e2e0e040908041a0415050f12180c04050907140105071b140d020d14010605 61
    0x245001c405080d404d14071000700c0707081e100c61049802040c10344220420124015881e1b6840c6959661740d80c8901000d40065245483c41c0110011306848040809000e48400242840116500c0751241009486c0c800945021040ca03c00c00b401ca440d980d41099120309018129800c0c00d0301d42c1c545040507200b900240e4022410080031541c07981c042c40d610001c25058801a840e082013600d1400e01340b01c100705900c2c0c0285c0c6200491001003102e4407602c403006405003000d1400c01c541c0d0040c600070506a8800072002c44004031302140502100080990848030240ca07050f0950406280c5840484036040c0c2102000900800003400365118034081c0465100400701d1040c9215030070a60141e0100340600610003450740224008c15546107418001c7d2401061043d004140c840d04001d4a8400603000340140d45c144142048013800044e448000d541d61110028410300f0341c10714003181d101d0000b89002e40b852044450341c02c4000103a50384000110940d400c04008140842c1c00103c15005080d43e0700320b25 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 339722095 1250 339720845 339720853
    0x504110408032d120a0e1e03070201110307030801060810031e030909020711060a020f06090a1203050103080a030c03110c100b090f040803070e1011010606080105100e0d05 75
    0x60078400c00360b00c40301d80748202c1c0580c03c250f41e00c0d060208190181990402804400381e020541c90304058004d200354180c40030a0f12030054000b0184907001c52400c2ea4500141c0000c1129030a568009080350021014a00a14a030061a030f800500c0d02d0014041c40c0c080c003048030081400da00340c80c60900d014650203e66481c41019400920403100e400d00300407000648c1da4076010403440a10300a41d408141e03c80b12110b444540282040400d41110802000f14420703818910f0382100c0c20408135014513000000b49c40d1000c0981030518120703003104044001c0c54202001000080d40c500100d4000002d5450b000501030401354040300601604880034403802d402084510fa140008600301129a00c841420001821346c00d0a112141c41d08903505a460a40c49001402082e005001558800701c80c1ca03101d00d0f5142d1250000d0031941608a069000940700c0d09103640d008801d1003400e010700b0701414403441c2c66240c076000556808488038044200b00310406401015106e40c910a13961580c004151 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 339723345 1250 339722095 339722107
    0x6030c1e0c1401090b090c1011031e07060c0810151701060e1e0604030f0c05040f0b01020607182d06080402030d0903030903031409040509160806010f050411040803 72
    0x55406801980e20540c2c05010917000300f01519000140405940c1003d0705501c140590f04c030042d00c060600d0403000301c0900041121030101030201040e4120351030a41c24441c0c07240c0301c078102501103031155000302003401665424010b41d54040550001140c040da00c500c400c045100908948039074104400f0441c062821001090b4075030040380d11242d00a003030b12800c0c44881004644a8241c201c500042c0d00010308100510110b4400768040d002e0314000d40e401446e1943d0344000c103040b0352040004440b0300e641c50f14480c030550381c103101c80b9420006500e840c6c0404070b21610000110200c0744191001814802189100c213102582c1c0c0b1080d40140b0144a0342d15543c0740f901a01606080b00d00f02e101380201c603000c0080c2d5004080c4d010540e41c01d80d5466841c0c0d0300b16030b130644100c207804081d1040d04005000c50401981c0e940a2030f84501c500710054041e45080300d0414230780c458150410f1103550401c1c001844004090130182c41152801c075804941e00220b0040113802d8810b540101140d80400260 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 339724595 1250 339723345 339723383
    0x1020d0e030a030c090e040b0601020f070902090a05040b09010b09010e040f050402030c0a0605091309080a0c060b040b0306040209040609051b01200a030c03030605100c0c06030c1e0c 80
    0x160210b4803007920180050020401e0031030b01c00085001e601002610980031030003080410660542c0071806004440420322170300005860710909602c100207950b00043d03005401d081c82801c403001031000352024411000b000c0001460001705000d032200314400841c00111580c4144854810900064030400c00c9058582110024050855042e406482003445c00311903810b1446644084448668030703079007030030f10600c01c0200d0003100a050800ca2511540f9600c08150400000d00390018181c450300c40c031400d03074030b008000c2d5250403604070b208500e000b41f010703280c2d1000701c1e58550190381214040002da4880c81e21382e000300758502c0054000c0c850f03426142c25060b4910941c542c030001c02d803542540302041250318400f1191340f400303130381079a0072010105001074054240c08400038441d050210707400c1e03100e50103ea44240481901c00010780381004d21414804d101c808000035000b1482c080c0200780840c00054813245400003111082c0b017022481031032151051200c60f011640c00a804c80000c00458a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 339725845 1250 339724595 339724597
    0xa03060609050906070503070813080d0209010206090304080c09101d180d1d0424140307080703022407060203061002010e0c040f020c0607021f0213031401020d0e03 72
    0x16551901c1d01e00000308215540000f40301c0d20504e1181e44407851a941c5080c1210713141000740c20390030510404d44c0341c00001085813001e002c0740c0c24080401030b201c00d05403000902d4400064243c2c0303000d030000c1005000e09030700801c0040c2c03400d81c01d445000c029100c201c41080010f4580d03000407056112816841106169030050714080c503114030f03c1c2a03400703505903071241c0c81d01842d60060010840204105010030080c14100044040041001030942c7c00b10410304604080d0341c0e12226025a080c60500c006407041d40c5108045409030000c112003070030448c0c96035841300507000180c841da01c1c90320500f60b0126007a204104540c031313030402507448142c3d900d840b80282d08141d07240c1e0302c00c1c02c05c4560113000620507c11074900d080202d008000442c0a041408000e000c0c940300c818446400301b00d804000c1008021a50141e13403240e008100080c818018200580d00702c0c100c2c81c20b0a4010000c0c032500b400700340c0d000000d49401000d20b1104584000c01303940203101d1164454401d50070503800c580b02c090040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 339727095 1250 339725845 339725849
    0x100c0203042105070902090a030b0a09060e240108060106031508031c0e011401090b01050c07080a0201020d021902010f0c05100b030c060403031d03151305070605040510030c030b0a030606 82
    0x2004132030182c2c2d11103d010f810781c0544043d054102e0002c410800c0412240c2c0c5015400001a0700300103400c141d1600d801c1c040e5000480d0f080442d61000c207250328803d44148413100700e1800c03503400b154254101188180c982406100d9a8101521820101003011040322180b004043c0a0104d0f90340b0f0701041c0486000d5103503140d80d03c0985103091394502a02406004414120000b83d070a026240e0038003840c1801040e030a40e100d410407205000030146903500704040c101604a4000511082400d03100080c40e28210040c40c10454124007040c02001d0441e43c05d22610581c2420603100d900010755040311110304009019045105d00c544a4103800b000764041e1056510580c252240312032200c080c80101d10942c440100002c201c00c404441e5092640e00c070950700b02e401401c0e43da12152001000d403140900f91000709496580c1c11848003042020410303c4010f00c80c80c284a42840d29000001e1098000507075000145500e50140d600305d24401e038810b01e01d02e6801030808034555240e0500c10020f004038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 339728345 1250 339727095 339727103
    0x506061210090c0f08160e040207080301081e1b0411040608060a0512150a02070501020c1b040605101d06160c1202150c150a05040b1503100c02030421 66
    0x20040f04800c680c450904400c00701d61070f440b81c0e502d6441e50130182c841038140042107004c01504800c000720341e80c3c650004128481c001c82c551922035050040d114141840350684000141c8411000e080003c0f01103402c0d8034812850259403c0e59488030040b1b00503004041c07010b4044100020045105a00a507405005440540d41c00040c592502d041c04214050b0b03800c02c044541c0400d4508000d4070b0240c1085038010a21480035003011603a43d2042e0aa0b00109226511900070f401c081d5400b0a400498460700001150705010b110700d4000442d10b140d88204c2e0017010018001c00082100c100e21501201001020384819a10008140001d10170300c40220201ca04e28003401001460504040104c054150000c02c1b050140d031400b8034001c440c1d40305510780c0c1c0d62409620084540d060f840c41c2c220344903004801c2c02203400d140c24503022080e080000d00e0244040303040c1c13042c60099240002c0d4005042480c4c0b50019011314818026841c501495002e450030000c49250b00f0110201e60702452841442 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 339729595 1250 339728345 339728351
    0x1503140115150215010819030c0206030702010903110a08070206070206072012010608060c07030903060908041805151306050603010f060806030703030f080705120907030302061308040504050606121009 88
    0x702e0681343c2c404c410a11a0a4295108082c0f006011801c45941e01c0680d110b81400402411264040b80440e08100d81d1100542d665810722001d2540000c6085405200f0b18080c000012441c0e84651460240000103406408007003850783c1107403526402c40b004660890765200c035003180c506440d0f00c41446105907600485905070030261a14050042c1cad000e513045000500080c4d44d800070b0013281c03908840000e50400c80c10260000110f0694031445500c1070003407a04940c0c9500b0584141004890440907400c103505c0c0001308000d0341c1400b0040b410380340c400c0b680f1407594292004540098003564119688c0440300000000f0b03101c406802e044212002074440700481d0ba103250405440704445e100107400700308d1517841180ca081c80307106925406a01414401d0510b40e00460052200500f100c0c0700340c0c5580409018000d06804019051340a502d94080102901d940c0e510300d5054003580c0714150040e61200045219a61441c00b1740c0c4813107061081000e00c038a4100c50f0403040140c41e2180700c070741d189 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 339730845 1250 339729595 339729613
    0x18010203040f061d0a02120102040b0c030a020106050609100305190e060604050901060509010902030c1611091f03060e0111130306052d060f0301020a0906080a15031401151502 77
    0x81590004c2e68600361200a00011070050f0203100c02007000c0d640e0f02243d55420000415155103d0000d40340342c030805401140c42d99001c0b00042d084500d545c00c594410f0a05009841295403520001c0b00c1c207603502c6c517010480761604511400d240010f000d10b03003441c50805e80c20080340d420010b4201d114007002c071000d02894907a403042c0342c00c9404c14001c4981002c115001070000e00559001140c2002480e82c42c40d14001410501844070b8003000400c80318042c08504e441c901d89414524190404182e006c5016109006141c600c50400a40700c01030440c1d8951188041045081d440915040246000c040d61500342203030190780740325079000c01c0f01c101b482c000c04070b62541080079165290810315000a2a200002d1032042290040202519403200368143e000342c141c2c5007070010782550942a218215070700e08141014148440050440c56000d19054290208401800070207040300e40100000300310240c20301e080c80c05041e651518403104044150700040350010300d0540301601c001ea60a442c0052 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 339732095 1250 339730845 339730871
    0x703020a031b2a02010219030c0c140414010e010909030c080f0912030306010c02132a02070905190522050a031407111203040914100503210318010203040f06 69
    0xa641c03030f14040d00590140c202146d002e842d5081808005011742011101a80d4a5660020758000390b045120010380703450701d000302410980074a1407400b14100c5000d0300e540c10000107040003501445070394006078030b89040c401850700a844000c1c100742c0001819580d8044001c0a80c441e0380601c036282d0064040100d60b4015440102c10f50703008403816034408100854a40070001d0840c2c2c810440300503155151954032106680c2260202c10740c495881d00c7d5080d00418001070308001d0f10b6401105100c0c18481046000b0320070b2858a0300503a0994400501522240e008443d807101002895510f04040c0340b82e5014030800041148146120769909184888030601045481c018441d0045c241103111a0000309031805254942888805000b101e09182d0340f10b13442c038162080351071244021250030042c402940c20f8001440090007007a401404c14980030141458040d246000c180784960300030001c43c000a442e002c0040468055200030b54403400c0609050950304c006080443d201840c2c1a0384c01818 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 339733345 1250 339732095 339732167
    0x11e05030607020d0806060f0c0c0405010f030f0f26070c050d020d110112090b0603160b030703020c07030c0905091506060409050603120a0f0207050a0e0703020a031b 73
    0xb440742640070300b04020a01005803044400500525401601403126003910540c817006484000d450b000240031000d5000140021a01e06800000c00666403007403c5c40801e220b546034950050b400510081d540e00c8504150302549603070b58100710f011305903210f84d9100b6400e81c0050a0340b0b134044d078500e580c825503440030861a00540e00000390403403803007000200412080e0b03010b5500c020042c10401d40341e0f183c9101c64803ca62551a003250b641c08000280f29260604008030140d50015020760b109a5041007030320006804024508400c068000510b90745440013400804025a03210030804200c0f61501c1452020340006c5825030082c0c828070031001d19070801da44800e0f0051202403c043d01d07060501030f00e040a02b0004210325011702ca00c26101d03804100b2200200600584c0703a03513240020008020003424491180e210b41d1181e03150420500c51246400720643c2c001045040059503422050b1041e80600000600396581d511080201d028460300a003981007000c1071184a4400e006d840080b02c40c0c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 339734595 1250 339733345 339733351
    0x40b011401080c09040906111213020f101707030504032c010c021c0602040509010803070209060906030a0215041707150c08040807080109031101020702030a080a09090203011e050306 80
    0x64100d01c003203020f006146000b002e0048029002084050950729004261652038580d0075807024006a822417034a01c599007182c1080034076042070b000350700350340010308440c483c2d01c8002e00c80d0100001380700b02e440c001c40e1000c203003000143c1089141d2900710405401804102c90540108d400d01a10715410380e02c1d03c466145480da941c0030072010240b660011140014250404c0340c004000072580032180280c40110502548100000750341c4500b46418800d003003030306901106241d4401c1c404900141d881c07035480c540c0700b407040e55581c4283d034540000a00d07011050b980a0340098600409044101c0080001c10a58036100c554166089c422000c8540c2c2d07c810f44540400300d0b89142084621700e00c1140d8a029250180f6250b07400e00c1c0d210300e030040c2440141d5105900710703903403a03000f2820141c00600384400307410075400860501e1000d402083c3c4038129000b00030030088000465141c624014070101300903028541046403070707607118000c2904000b00802e4100642100100019142c6400582184 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 339735845 1250 339734595 339734597
    0x130e061e0102071511070f06020c010206011d0604020403020d0312050c040501140c0309031501051806100c0519110a09091e0c0308031f08030901090b160203011103040b011401 77
    0x56054513108010804542002c0120200300340100e141012000411a60700600098926000482d24240700a803a11220701a03407415904400c00400141000704030098003e0b403440c1181002d0b03030303500e800a8001d109981009602442060b010b0041c19440360340300c0c820b080070040412160f15462002902c41c0120701c40d035030008600440301c40199100201a000da0300c03151003203074201411840001d0924200d07586840c00405584010001850600d081d800703003c130102158516030418001094907070940f4003002040c01170312003002041106c10404401581712030a1a02e95403583d0b4603001a10440c50318619208a03000800481d8103070817846418511035202d810f08840c804988000c2c600340710420301c19a9242a0380340d000000c100c07418002c42c840d440036207411aa03511141d0041c128820241c00407200c6a02c1880101c01ca41d801c50f4051082d10341040340c050301c4614451011100058100c0025015400c208084098450b10005036004a1007495010340301c0c0c0e01c034022110241c03c030303a00440c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 339737095 1250 339735845 339735853
    0x6110307030c170f07060b040c0504030803100b041d0c0c0a020d030c0b01090e06150123070206181f0c080307022a1809030702060906130e061e0102 65
    0x10000c0c0c0624100d6035000e01c9521a61002482c1c0f0040254a0304135042c10315040700c0001e417101c100a00c61060510318581141e0801201044900080c01c40c000e6020090448400102181c008a01c14550f40001c00c07444e132a950303455441d02041e4403984100c41e020031045800001190340303010518256a1402490b0000b040610569001c101061038659015410301c0340032808000403905060b90203001e44070000c40400d8403400140041e20348203008003c049081c01c40c40c6146110381c2e02501001f1a03c20710240c1d1a41010350780ca481600c2c0c800c0c000000d61103e4000740e806071818140d400c400c001201110000c400c1009581c00701280307010041004002070007a00c01030001003010000c2d54000110340304a60f60810814460b18010010030310540107110600b0300c0800303030b151440b090711a906107010302d0105403d02d40082a031300d00402100a1044202281c943e83c51b850f940c040e01c004001c3e548100c0c1d40155514100c2c124501d05807107640c0603001c00a00c80104903140381034039901d8041a4010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 339738345 1250 339737095 339737107
    0x230901030c0305010e0610090e0c04262a0a0909020103050c070f0609080702040c091412150703021e0307030f0204120b04060b21010509190807020604150c020307061103 74
    0x806241287c0110500780208420041042c100840c0041e101d01121040d403a0f950b42092750800581d00750301e181c030500b0046072070743c40e416200104a5441c1c4081400301d002a103000000b0070410074440b1204c080d080305a100c000030380100c05401034980a4002c2e00c0802c82c5454070711000c20b43e842040b01c0a172000c50f0201c0e000340012215800304a025006080740d50a00e002c1d0340c0000e0650300b030141594000748592805001c10000d0803102e950f50401140e00350f10001110340b4031602c0d0000c4161102043c86910b0000d410036002c1d40441b40b00d000c14104502d0403a540c1c240020243d04142c6040e0700081c078254481480b04058401ca500f55190f4034500c080d22802517450840d543c6005100721100c0d5200e0768000256120424503003018003c140300c1c0d010b04801069074a0846070028440d031302c00d501181602d1041c00c40181c11030300c09500840015910b20b0030f4008a181c40c40769078042040134102a403004c0460760310003499400743e4402c40589262986d119030031603c1c9101856030b001c41c0e8100301f100d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 339739595 1250 339738345 339738349
    0xe06040c0314030904020409020c011a0109090b0303041a25080706021b010632151b15190e070b21090a030f0c051c230901030c0305010e06 61
    0xa030580c0c501040040fa880c20f2000800308043c0d820031761207200c2d25030300402d03541c8050b103080c02075454200d10034148402445002c000200307940311a2107420013070741e603401c80041591014011500a06201c0d5840d81101004401646a540c004804111200ca44000c2c0c0710708503d0031280008029000001d45040c40c01d5521070100030b501c070030300400d400200980d90080b40300080c0540c10007800115100712082d000c64020001c100b55440c00c002862071503481600865036410810385500c01e1400225886040022340044041c4503070b644111a417207100c8150b2052a1141c8030b4900c10131039445204034043e2456844815141c0c540c00d001296080100240324054024010300924500a6070403a610b101340d40340305045200c00c1c1c501d425250807890300305051503040514210800c920345005c0e0701031052900c2e00364591400c0c0e4191140c0d4072548002a40c0640b20341c850680028102e60108107404200320a0b41c42a80f00c1c94485004ca401d100300e85480602030f200d11412901800c0b0aa1400d03a14441 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 339740845 1250 339739595 339739613
    0x20f071b180f0e0f060912031b03040305130e10080a030e060901050d0504050703170301060c12200d080127090602070c060810050d03050712022104090e06040c03 71
    0x301c0302c910296102a00300094070100704071040c521040001d000c90781080d090590070081e40326040c40d80150100148030105122024900d20349807010307012030722511030340b03001c44d0b0030f208040c031403600c07412401000700b2101000c21510340641702c0300951070001a552800c80d51a49580031004d0041603944420007040d09100b002440b0316401450300340d00d0444a6400c0e0821154291001e03903156000380001d1040200d400b40b004144980e01c50a9400c5625020300108440c21000340241081100c5900440450203903004c0710715244c040c1f072603000409000e80303190703a6005442c00c80c1c00041e0010000241111200c8011044410500c558802c0d160220607070b800944a40d490444d140c60742004040c01040f0201c0c0c00401611050703480080e81e0821550606032842d880d00700c54410b00c1444e0755180000d030843c1c201d4050a41c80490120122000b070300980c180906004035034610b00580400c01030a0320700c007006006407000301400304000401ea80203183d450104990007081c034907620000b4408117001203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 339742095 1250 339740845 339740861
    0x904021509060f1c020c030a031806090b190c0f08041407081e0118030c020a03140d020601092d0f090807120315051203090301020f071b18 61
    0x45000e500c0c241d4004046110355010030f240d001e8140c008500c81c05800e4040404000c2c1402c48242542416102c00c59140c90303200c1d040d12803003410703500c00c460310040b10001000c01c0308a4100f14104022141400c200300c20f0882103c1c01c0b01d2000c0d5180004a10b8440d0b0b22a181111655613103040c40700c40301c0101a5a01040a801941c50903845040000505070030030081c40544a460080c02d00154501c80498607442c0c1c60407410b4039641000c501c110320005178189810710f140c0500c0c004001d0701c06400421121b510070781014002d0b80038003119040340324001481a03010b0040b40e0880d62079a0b0b81e64051030469000013002d0b00078024036115110204041c441400b049812580001482e0908050100032546002c1c4115021840865607000740103ca042840c10002142400d00c0040c1e8030140f2540440051700486208180f4923503070003400c5c5400c000341d03404200b014000319a0b1303400310009002c40350002d42c0c0c200d690303004060b1043e42007490044c1c0728044408519041905400701f00103600900300d04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 339743345 1250 339742095 339742129
    0x130e0919060618061a09010e1e120304080607121407080106090902071a0c21070908010b090601050a02030d050a050412090b0d0c1b061409032109120301031b05040b090402 75
    0x42140a43d9a27031a0810b0f28015518145a080c0701030030041808101c1d041400c102400b80c0041c0001c0010700c40100da410f50080381c528000d04100c4220455200800d084240381c40701000005c1000551508072400505845580d180c8910480d40e400391081a032058890003011b1800c03c800101c03008100540881e04802d650603103a0070803181d0b28021002e6045c20800b448022071160601550b50b8210a281e40500291002413003040e450740702094801d20040d110904200001400803003161091041d26480b0000c03042c18803203401c00f41001005401c040d14261030060758040700c100032070b000c2d44281007220b0842d00300904182c0040d96600013000700821850502000045402040b11603102000456101e00c40000d07121241c000c0021140030020048082544104051014907403505144804a02d0a915000040c0e43d80e1146504025200e04c800d210303400040004000c00460340703911801d01c070703d0700398410030136503904100300545a00a41070b0f80c004d5540c40200c0c0250a102c1074500040b414 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 339744595 1250 339743345 339743357
    0x60c070f080315090c0406030506060a0206071215062102090306040b1003080a0302070b0105040b0a030b041a1006030c050304030c080c0f030a0302090411130e0919060618061a0901 79
    0x443c0c001c242103003400c41e0317104605480018180300300341e058890260404400d65145050166440d006542c0f144017901c006c0034003d0150b050001240c807034103d503018605900142c041982d64503c00b608041452901c02c1c600142d015443c61341001501c02c1d25505000100200520380b142e0b2111130a10700050040c0150000c0d100012000c07502c00d0004100004107a9001a6524521300f8401c055030f1040e08102d20443c140701040c10156924003091090b250040d50485298032a843c140c052001b20181e10f816500c00078080012000c00380304003208480441d242400308452046040340c441c8812500240480c89161a10000c501441c0c054502071041c0c004880001c944040c1042c610341144070721b0700000c6d0b0005609201c1c2e041501810402455100c032543c1004c0340f6101302c001c104001e0042414078081c21001030701c1c0300010030483c00410402006401464601d08228001d801c1038020f54881c0042e400d40b40048580902c210803c607078020510000d110120070007000140d0080303100d9410084 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 339745845 1250 339744595 339744631
    0x908120901090803010b03071818150f030b010f270911041d1b0306040f0201021203010f03030f0216140301110309010509010c050a050702040c09030b0a0509060c070f0803 75
    0x2070000007117002c3d0a85020842d01e9182c0f02200620300c01d000400c10310642c0e103115081105442a000540610b51282ca0104008007404000481c1901d680d1109101603481c5400005200300c0c5007003c1e058a4150700c29034005503c80c500607030b811681d092042040181b04001e948002c1083d40301d405120300c10807140c85179001200001c5c4c26101c1c440c0100310010508800120802030800148807034201c1d0301c0d400780409001100003510f9500041024040485920b031040071a842401441c060800400400c0c2d107a58440b11500b040319180c0c04110041034228040004582c000070751175520030b02420075041e50034108039851400b01c209c1e4450a40544d261ba00b03204070b03a900d140c0a10300c603041103000007509240841c291400e40d10500741c01c3c018487d013080050901076004044650f415010340300441d66844a0b102105c800c01d545d40040c204100150606c24800081d421450182804004440e000e8480e00304d4441e00b0721514500500340c80d003964a120020b9084005160300c2130703428a00c510070b84 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 339747095 1250 339745845 339745853
    0x6070c0324020a030c0e0d05150408070f051c0c26040941011a04210506090601050d111201020703170109111b0a0c080c0a0801090812090109 62
    0x41c03c1102c85001290b1038421050f0100c3d402600120b944000f10340340240c4070b4854031007945030241ca0050350000c0c0d00d9940094280802c04e012109481da00104003c540640343c03d02075100c1401e0030000c90940c260b04200c05031140710f9841284d59907000003642a9059110007a15440400400c03002c81c0c0e4242400006003901c014401c2c09061414104030000d8072058024400308900050b180084030b13094405011100e041d00c41c0510b06480da0042804c1104085803400c99003070140e0f602c049803190014034500102c010209140031014070401c1150680d8464180d100c0c1ca40509020303440d04620314411400128600110b0085c0c0500090039001d52140c80c00b40440c00d980c0060b000343e011905031100030980f01901e481d958010400c4100c200134030704a05004586602c29a645100254041080b05a80d40030500045d8580c80d403024800c1c001c1d82e590050940c0350311920072120311507400c40800040440041c043c0d20f40751030344048120329240d800317260031b250060040c03c2000c0755988d51404000007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 339748201 1106 339747095 339747097
    0x10f020301080d05160602030a09060b01030608100f11030103030903030215040c0e0a021315030c0c020d020108041a0c121e012d1d0606070c032402 65
    0xd5040c05c5445005144880c8041c2c00940b00205010129610790f100010075803091a042c07001240000040d411104540300315501900a841003204440f21540882c0164550f90000150702601d40c18510f8960002d0b0000c4000c070300021030503c203040e010050f00c02000c180f00c90030b904504d42a039480c0803003483d51142d521117403016008600603000540503120541010200e80214960700c214030b07008807150a1080c008286054842d0344464031481c80755003059005801c030210a03140380e0044590f08c3d0002c0c82507604004070358109a50b842061160b03409103292051603a21924840030100f8800340c058076800071041c4080a1803103c1118007402030445064083c0d8000400e520001c03004506040190801e080f0105c42d0003250301c24049a10155240003009190215900d441c14045940318508000c1e213208215071702040015820496207002c1c1048030b06007a4400c5401d0007100c16 = true := by decide +kernel

theorem cover : BRFrame.Cov 339568345 339748201 := by
  have h0 := BRFrame.cov_init 339568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 339568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 339568345 ≤ n) (h2 : n < 339748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
