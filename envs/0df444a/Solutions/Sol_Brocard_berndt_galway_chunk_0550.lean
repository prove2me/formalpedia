-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0550
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:23:43.231968+00:00
-- url     : https://prove2.me/submissions/9949a583-b9d0-4763-b3ba-cfe00d2adcf0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 98741007 ≤ n < 98920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 98742257 1250 98741007 98741021
    0x8030301030614060906060d0f0b030a030e0f03070609062102040608070e011110020d240e010e0408040b16080301080706110601060c020d051c0e10080f010605090112 73
    0x1800b03000c00c5000f80d4032035100c03001d1409800e2620803c44132062003516a944801c60302c00922090700442d001c40348491210041440060068150213401c030a1410564801441c00300001e040300c800c0400d86c0c0705824036588138030501500c80401c000d46000d115081c0103c10099184924011501d40960088121070698000340e0100300403480d4802032040168010001000c0f80c8428070740f03040e0000c0d01c0c4d01a135940c1c281c0e0200300a1160707400200703004002c40540000b88030400050b07841e0340002e1039005501c80300009101d1b00230510564800801d00905000c3e019004a8201509904280c10b00c400d03035185078131845c0c62100c482a03a0144000044880d00a140200801c02c00743c19400d01e440d4024288141c6034066800341c2d0007210050042039049400d0030400b1307406445803080c0322441c2c94110310f852540a06880440b0003c0b1002c00603a42c00140140440c0003a541d56410201f0280141c4416800350b480c0912108990018400c2c5e5221390045d2402c000145032071846500c90b040303284110b07924 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 98743507 1250 98742257 98742263
    0x30d05070501050a051009090203101d061503030d0b18041202010e030702030307110604080a0807030f0c170a0513090b190e010b0f0405030f0c130c05070b09070803030103 75
    0x201140d818144082031003034030360200554000340002d250800c5e141c0040281d5000d0700e514655104242c0065440070851203140d0408214100220494a05c90507408441c3c2800c1103414403a07100001ca4000440d00c0e00c21401070054002e500780f11100b005200036003c900072640c0c010b117610b0409000e5240540d602070140740503025007a110554088000c0c00d40d6040850800180d20403ca1300f001620004201c0d80a80c0c0c0141c410903800c4000c00020b040c03845503900680551040e140c050b020302c800c043c01049060320030b0b16018a408091a8107540943c508200504400071903501030611104000060420100300d02c1c003e46031042c0b11900c191007050300d400100c0d0701b664808151015003441520405403030007400115001500d800e60158080105000301051906c0103e03500c040d151800781501c1c0a0500201541c0c00700158841640d6940031f0701800ca88142c207008240038080480780f081001d04900c41e40c0d110b242480796140d103a21600080d22919003482a00b00002d40b01d1424006580a90301c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 98744757 1250 98743507 98743517
    0xb042403030e030a15021b0307030324051804060209060a08060a08012705070504050c0a09050a050102030906070c120b040311070501091403100c11070b2505010902030d 74
    0x42103040040c10b0760b0745160054001c0c1e10140c00d020118244503404010f02e00368850240e40d60540c1880c0102c11030810300320165900c000f1800e0030405415030404210708450f8038080480c0c429920013407110b07200e1480360641154820989001940c0300710f41c0643d0143c0661005460000070001095080d8068181100051100c10038010030b0b1a000580c2d8005001c480000d1103c13036a5404e6041242d0070368844419003140c407a040d0810060700b0b01c0501c1c01818010710400c1545424594000140d200202580000745200d102003a1850b050b0030f0001038904c1170b070056043c120541c040c00f800d94480002911111542d080000d0700d0803003090b600507464444c40c0a1616400d240c03070043e01c0c03d844600811580e80242d8018802c50741d00508640444a001040900010035400031034280841d0304040a038040c00c14484114090300b040212031204120000c031103070680e691002c82e0640c0582225905004288107030300b00010707211400220b0344ca028400010301840590300191a100c0c1c414818008a4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 98746007 1250 98744757 98744759
    0x4170c060c010e011802010516050a060c1d040c090909110d060e1501030506060d0320060907061706060c1005190506090709180f0609020417030f040302040b0424 71
    0x18a01380110010f19602e403c081c00401070342c6d4001303040b0340200340c803a24000c2400f0b21010309012081007031800141d0441000c000e00b40200328010240b07a2030b00b4002e64080b00781064072049080610890701e0160f0242d40b0700c0c503031500700f9001c50060010100c0984000542111784051551a43c424038035807031203440f0000d4201004000a07040c049060701c40460300100100400200c1c1010589640c002401c0301c880d200400c55107400e032111403044507000031100320003504c80c1170700f10005041c9001d48483c208444499644a008440e660b405510f0800406c80b00343c0425100d04044c000303491440134000c107031b8520082c8440503104a41e4101c400d10f8010003c0342300e520124903244074994020f801a10301c44494600500701030080000c03441211071003030b07440b00b40048550a41c0d00c4100403005000302801201c0c0e44200090184d0424000e02a5003525840140e08025002084602e088040c0c06200e0409145400b004005e28101074100d0304152a01242c840000c40d80c7c0040042c070391081544030b201 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 98747257 1250 98746007 98746031
    0x601030507050a1a09120114010303090803130b03070e0915011403010302010203070312020919080d18060f050d23060102010b061204020a03020612041205030105010504170c060c01 79
    0x202030300354002c600810740a80148105002c4132840b004181c490fa2803190746401100c041209071003c4020b410039946040030f1038046144101c0644c0c103c81c003d541e8102115122031203540c8912443d240071700304000c001d00c204004004a006140e0211690800301200124031022800d4900100c61013140240321901c080c03010341e00001501e40b43c9c4407114100341150304643c000303540c3e131040031409001d0002007031a808042c0711a40403035100712009031003138045a0701040080020344050291441d203019641810011070701c40c6441c0c803040e5101c5c92062240510b442d105641c0f000c00e185206082046c2002062020202801555a00c844181c0c81098421040b1200072488001401b045e04590511840041c035a407450240e030504c005070b0036211780343d03122032000a0103510590f000a40020300441e01c80d840300000c181d05403045000351400106070480f0081110035100134007640d40420f000380300034050380d82c002d2048410503c0d000100c3d41c203100b03654002a0150001d406c92a61a0b4413041038000c9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 98748507 1250 98747257 98747263
    0x80303070f1107060c020910240e0306151c050d09051807020601090e01020c06040506060a08011112092506030b0306040f060c02070905040b01031101020309090106030209030f030c06010305 83
    0x103410648026102d03040c02c0140050025059a030003034410980f000108c0c0480780c001c4085d1006002000891254803d140c0b6004614604081e0620115002880c0300b1401d080201e840307489400101540d04802d00c495042054460b0303203011003510600c010701d0001c00950100400c0307480804c50380b0791450b4545480d0400110780035108100c40200085800d000f1502d4002070b00c541900c80440003c03076418001d03800b190080c018200d1011003480f80700c00344818087c01007032590042d2019541e41d00015141c039495400e03031f090341c002980000000c110001c814601548415000b0076194156018001d9410081107621b40c029513007500200c0c840c1003044900e81501c2503020018003a4058003062500fa241c00004000380703a005099951030340c1c60141c40c01c0c4288211005020007040801c0075081c41c1c146084088824081200e0980401c0816007880d0700010542390300c0c0304003c0802c1410703030074800202d0180d00f09066954040c456a200820b02c62000c4c000340001c050418002c0c482907256041c040c0ca = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 98749757 1250 98748507 98748527
    0x11b03091203050a0b060712081305030a0e040603140d080109110f0703050f070602090f010305151014040e0906010609050102100203070903060e0a060e0c01021e07080303070f 77
    0x14103103842818000100002080c1000c0303080d0b41000140da03603601ea10302020304a0720702601d030301c140006a14010441c2c010f80c450f0304a8071a90b036140d60b69441920385001a01c000f640944994424408001d49510400c090300140001400c00718500343d032991000c001c505004003100083d041040070340011940442030a006000340750b014015500303500200e42d03440c440c22004100030b0000042c00c00a15005600312070703610b01c80300c0206035a074005003002c90007900441c0866105040c1c60302c00b06159031090095502515086080000b0281000100a1044130f00f01e03100080c80240360440e0028014407004d48010300390f90308101d103a413504002140c1840350582180c011701c0428001800141d90008001160058100c0f005980e0307150501d041c3c1d0381c040240c1c40144040d01741b00030700c00411800304076990306601c2000705109a0301462a203a84501c080701c4228016031000c95001800f8403040d6910708822069401c1c0c03a201e58440c901c00e03086900c101c540401040c15816040c141c0356101010176 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 98751007 1250 98749757 98749811
    0x20d0903020c012a080c0601080303180303010b03060405040f05010e0307030905191203051c0c0e030105010302061c020904020310030512070302100209040f0f0b180103050706080403021204060201 86
    0x1454410008010b51004144840d94070741c1c91403c58441c40c20170000d1030445484e603041c2c00444d115507075200381c41c0d5903d500888000a41d0b80c40840c10311181040002500d050340d90f110400d5045948000522000307220061003528901320501d500d5000c03407802c0c400d0b2092542800003031581d031003180c280238000300e10940c030103401268122089110002e01d040c1d0b020944480d00301060076110141001c0720716000e46295221001070740081c401410209500c400c0310342801d80c0320044400040b504050807543d0910000e0b4101004010100201d07008148020304402401030060402e6043c030041743c02c907001220100c065140d90141407060103c20494a6510709841c0c1402d8034251081e0743c02500e940c2d403504040c070005d0300499480010b65803504420340b03201c80d001d0200203c032030080440300a055441e035442e0003581d0b503141c41c3c9904100c6140741ca050380d070890018040c80b490035204075803d410080003038085004036402d0090300207601d0b0040c40204010b5001240c404000c030000030f0422080070700e103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 98752257 1250 98751007 98751017
    0x41e140108030906090111010c0906090902090915010c0611070506010b1602040216082106030d020a0f0812010e040209010e0906041214130906090603020a030f080904020d0903020c01 80
    0x108000c41c1c0000858050070425646036032611100e10042c2d55600745c1013154902542000b19408150358060f0001c4100c03051940c41141241d0384054000c208d100f005005074100c42c0c2d0b103000400840c60148103001c1190180341055142006456010442c3d80503070b600032031003100081390f000384a0100a02401340040703c1c1c400d4070709510403520006040d10701e84028010340d0003140300c03540c8541003049116a250060407c1c0c1d81c0d050246032001c0d00f00580a8409052000080030500c02d04001962200c0c541c0e041c3c00411000742c840d1626421702413a8181100e84000070000d445040000b46130080c001d101004e0020f44504061040200e160300580000360580b0040081140700030b4006030407030300260060340a030510b010240080701d0300442058000c041110024440d034420040485540464460060801400d601e50400300d041d901c00b440080c1d40682018410b0010882480f03640d4152031041c080076203801740c3c003030114090f60000c20034005250ba4070001802490740500174040c84010900e04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 98753507 1250 98752257 98752259
    0xf010e100e0d0c06060306050f0604051b0a1101020405040e030a020106080307030e0f01020a08030c0c0106082116020307060c02190b1605030d18050f0607080a020703020a02041e1401 80
    0x1d081c1d4480010140004201403400c20030706020480d80550003542c1c00c1482440030345070000302c06030341c0001541e115008038948400104601c506154158050040a0620b0700c0d1030019002201d401e13000c1114248995400c04c00029107944911400342a410100301a644580c0c0500c07000e401c5030b00550281003990010024000000d074050720184080000b2194420300150120040345004605200100310001c000103203c9410482d0014103880c102d8034000703200c0c05032500c1000b521890704d01c494204115480030000b2040c0c1c40c100250401c0e216140200c0c51803001038002919140f43e582c00240442c0c450170140d010350034151008002e038168000c2c2186800d01d01281c0c0b051500c9003040c4629812443c841ca0001c0090600032110060380c618010b0090351003a41c84a106807400c1c41c1c0455003441441c000c81621b02c0c0206116200304040d0f16010556901d03404484040d5004c1e12044046020702c052090060b41c540c40707001802c014002440c0d904820300c500741d40c1202c1013451060300e01418000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 98754757 1250 98753507 98753531
    0x105010504060c030e03120d0c050903150711100f062c060307170d1124190c110c041103060d1e03080f0a090209160207080f010e10 58
    0x84400701c42443c9080000c3c1441c2d400c007100c8121001515130303070601552103950801d2180740080c0c25025407030a000c00c45441c0481040d05c480c4202802140c150b00140c4884030b00230036090a5590000550400c3c2440d0216038141c1e50400200721038441d400c035501d001611942c9998418100901180846010f46030b0220718003581d40c07c00b46138224946010000060080e4405001c41070060454804183d20310405036103c588070802e1081120015000503006040c0c1c00001541d82903030a124014151902403030b06080c0c050090003050841403000c3d040342c10704442910710030000003001b030b9565900300c1040303255101d0600300d064001d80d10482c10180c520035508090411030f07411500468003044502c0c03030713440d041140080300c206c91158803210f5002c203030600d50000202c500ca10b21007100c3d01456503600d06918210390b80584007075001480100060410032000c200740000e000c2900480340c943c0d0380c500d109494407021034808c890694492400e210b054404200106030304da009182403014a50314a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 98756007 1250 98754757 98754767
    0x6050d110907300507020303040c09020c010902060a0206070f08070f031a18040312090f060b010c050102030702070612020a051e090306010e041104050603190305160b1806010501 78
    0x44503940c816003103080400d14032802a44215803040407110380c5a400021021040715010324801c0311103030242400c0c0000c071071038404011280714692020389075140c5030602d01a84000e411035058070700e15658404a0b0001b5958200203081c100c0c5441d401050301d480d02000052400403c01d1400d014032000300f0a02c21740315005403c01c0c0341c0c2141441c0000d8600c0204198248540041c0629030300058410100c00500e1081110740f40724a000383c81d6240c0d01440c0000c1503007294100440505440c2c4000e801c00d00089036600240b240610503d840e440748191a240d0508a034425030f141c601507440290b040140940228009c0c400243d003010450400092100c050001c1c450a4200b001d10107800d0805400465610b05503088010f0150488030150307151050038a4040c010703101501d200000c442a48050300e014051144910700190140240622074640058083c2070789000724184503013031210a0112144224254045004681051081c03d01010000c1b502c521803a1f0360b4082d801c00001448541d07044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 98757257 1250 98756007 98756033
    0x90516021203060123070c030c120f020607052a0a1a0403030311040305010c0e09220813050306092103090601050f0103060b0a0801050a061719060302121006050d 71
    0x85c2010b590011016009201042d1818203400c00160041004c0050000030400102134034451603821540c19102c1c0351840003801c680b80d00400c030384c40d044100c0006040c40009414110700c91021140d04828440c51446c0869481c86020f0202500909101d210710346a43c0c614000c02030505880369051203026103402c10f10071800f0280c207040d202e43d81a001b05a00d5003c40d0011500440204082611100d00070480e0b080c0745031080c030410640000ca08424503946c00b01003489044c1c01c5007080101da80d668039405400044138403440c00510b000005890710300340902403203000230b2005815040303a90882105a410401d00060b03c04d2014410420340490000b6120305440007102c02000010b141e10040b00035101035040025020000720b187c46a69030000c00f5581a1601128041c0c8210b80f1000111400c04840f0b861010071070000010542119003202c0c01c28403035500000100b10b45c2c0d01d80d00454202048502d130b44000d60b000c40c08071018641c00748200806030804030303215515002c05403201030b100c9240c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 98758507 1250 98757257 98757259
    0x1030b090604050402032803032703031e020c0109020306010e0610110a0c06031d033402060a02030a170c03010506130e0702253c09051602120306 64
    0x42c0c2c4004c076040d540e040101011441c041090300c00482c00100d007034040c03c1b10072641200840d0610948405100e81020848404003601410000b04805900e040380a441500096607120070f9043c0e2100c0c3d070240a0009080454141d00003050000003031043c1880c00c0b01c1684050100200f0030240152540c400012201542083ca0b04c01c8000c0104108141092644e0800600c000743c41400094681c3d0550040000300c0050004d1040c1e4a84004680d42c8901c2030100b14409516003105031800040c00d811109241700c8003c480c90810b50a035404100e550344640055400341c0c0c40450911aa95803281c1204482c009004800d110317800d207001800020b001c1806090300c41c10010070b0300305c51000c45a81050003440c456840b09418180004080e444422040b00d410b0b24001400d004c12001140c0d42c000002c07600c2003103151821800200c00040d05001d90044001c032524000840040b020b80c3c2242480078054400f000a2942400080300828155150010003907400110b0341001c1c220f5180160b03580140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 98759757 1250 98758507 98758511
    0x30304050c2215180912030c020f0102040e1009060506040306240b03070224041b0b0d02030106030c02010b09040b1017010b090f0c030103060c1b06150501030b090604 73
    0x104141c845065207404545480c502407940c1a0f0b42d02000f400e4007100c5211418001000300e804055094401190014140c01210242030219600c20703030200307111009501c1641e07012010056480d003642d219034403050607842c4d02024041c044c603490003c1002486007480400a40f0b01e000c0208110f07000707501c4090141c0307541e03203884070300c0e0100d10803000c0c0c5003a60304c0448141c05884003994446500241c2d0340200511804440c2c2c061404003030f200c0d800b0000c020050740c10b59a25580c804800020407038600001013050b20b000209403c80201401c55000350800c096141d43c10060000e007102c0c80c42400c84210780c1054030141440d1030740c2c1049c40d04560064804d000c00e583d140420b02c1034515541c0505280700308156100e0300090194400308805801b143d03135013070715200e05081005400b13040c0c605055080c410001040010101d41c002c01d002412810115100a2610b54607400f520041c0415112903858500c0f8802e00c001c13401160024040900301000200c0d2002e000c150010001404580159 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 98761007 1250 98759757 98759779
    0x306010324020f0d0f1a0303070b220f0201020613150b011b05031213020303030a020a03090b0c0a090b03160c0204110f0c0105010609030b0f040f170403030e03030304050c 75
    0x8841c540441d0160302c180c00e02c2c69681e101c4841214010800c080d040e550561a00d6043c0402000d03070306241b9101c1000400450415680c0e031070740408482c01038400525502012441e80784400c3d040703400100315009050007482c03038001c0d0001a00b091401045110801c00c0146180d0001d010810105020101c070301c400282022610010ba41c9010341c842580801c150030040e40e410400008014905001c0280a10b25680c480074000f105803c08440c00035819001440001e18250305503019102c4a2198540441c00b1135036a10b030700e18080700641310000c2c41c610018030b0200700d6400c080c080e8000d1016260740b030f18502d400380342c040d0030030301a80d4820308004040182c8415542d590700802588000081d0107175652000c403441c0d21a039448150328a0195092500002d0b01a01481440e0122a0041a0030803c0d54544644890100c0c1c010811034800000f0701c07404010039000c1a4204021140a14260780c413411800d000c0c02060307044481610950007041000002100442c0d0307124416400d4031300c01d01507 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 98762257 1250 98761007 98761073
    0x9010c0618020a0915050d0b19060321110a110d1a131704050d0b04050f0d0806030118020f0d03110d02010204090f0507080606090a0909060e0c03060103 67
    0x4000710000c0c2d44100e40440c00700740c806030b6030b102d045c44559185480291507a03601c244800c0081d90071000d4110b00c682da0020b0603c44003a121205c00050b4030741d000411a403a6581e29840003d000031684403101b80c04014000182c014091501042822004028000007030b13981c0c510a4030201d81c403a0003040703100d0300c980030040d030703070090141c0765400850031402880c1612410820040c0042c0c29a1540072241003d2500940a4222000d036900030708400403008080e00c1c0c1c04a07040026000b2903051050f10004132401100384a4072091100c503654442c2030741002d04c105030a5802145580307802e044100b04a00050b510a00074030360000094417080400368441c20140c030f0341e0005003913140050140c000e0000010780d0640c000c000303441002c10100100800460203000315130b011540200820790002c08a0303d646031001c007400c941140105566801d1740c817940900207a40c0220000c42e500b90321034921448900041c82481c1c510001900284095859600d40e11032107800305000c002c59040e4502102c2e84 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 98763507 1250 98762257 98762291
    0x6061c0209011e0509070206280924020f07170405030a0b010302090708070e01031e0606051b0102030705070303150e0c0a031d0d0311040504050c0c0c0609010c06 71
    0x826034005202218660395503090380b0001080c241d0704000c1e6800307440040342c54a00380241c42e0013100503600a240f503560b0440c1001c10718007807403c80050803001c00d013000c94002c820302a45003d9403092800c003001c00940c06400c0e1081190400b11035401c0d00501100c1c44070401041943da5581e00822402800018025454620721440d0006c40e018021010b1010920046103982412248250340546a0303a172144002c6540035070a0302c00d01c0c0090703490740800d8120749c82508142000300300c120036020000041d101d13100841d40594803c00102d0340c0800ca6080d21200700c03202804554500c00251300d5407400c210002c08a11400c1001028503580d0a0b4804404d02c46480800140644080c001014104440d84040e56000114600000390801c4010400c500c0600855844015103a00900390b5a0b005141030300600130401c006984680140300c0043c095581e802514040c0c802406400d0307540020710542814100f007652458081c050412100000b80d03808501c00001035004180010070307010004036409 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 98764757 1250 98763507 98763559
    0xd0c0308151008010303080a02030114010e2e140a02030a230301030f150b0604050111010b131b0503010311042304080301080106080a17091c0b0f0a0e0606 68
    0x42c00c24200700c0e5810102e6001074205041e28000c0e100c500081d5244502602a0321007400313001c03c8103140106649865014100402c0c1001b4006d0441000c480103030550858203402208241c070a054403580d040d905500711850380c5c06100c288051500d80401140e02940d01d1089841001c20058101c030450f40c2451070400181e003500020b10142c0da2075a41e8189020b0310f0401646c180c418410028400040c1c1d5034901c0703901a20b04000c1c1005050602c1d0100640304020b140700e8280310346d52071781c04400d281e03600d2290294015105180c0050880d030f10308510100b940805c00d07002c0c2800300400c010b10206242c080020300c01d507822035002c588180c441cae00f2055188403640303404042188040501042107510700103981078940400003006220ba48990341580c078102040c1c0607046400b2001043c251140c90402401030f0040a020b2402a0429020b001c0c00388015080903520154201c06001403a140b20341d03c207802c03a001a20602140c1c3e58560b0258540b5400340585104202c814078201c070000141c4000c003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 98766007 1250 98764757 98764759
    0x103120c051006080a03111c0f020a05160e0903030702070b0d0608061008010b01210506010207050307080703030801060c031706040f0204080c03011404031706030327120d0c030815 79
    0x30103c0d0390303500c10b01c50b030380c03202e4800c22004103610116a5049010015103e4a0213030948004a920045520306a0340400ea0b03421400440c00790141c0300c8003041e000c02220200400311010549040d242507101109034101400101183d0820006d000a10750b0022300241554200e02010365103a6150f81820010305003944600418041d500402805080010310768040700c440100900103440c00c50011a030740b519140c41541c00c2000c1c100e40090755402c80d03220aa21490600407184640c4e11740002900d0640c003644850f007658020202803003019409034446004090b83d00300b903048a0303155a4007030900b4064803102142030042d0000140182d03166006200b5114520b6000c540d519200e440c026240c0d540300d00828000c1d0700340030b400b0001100190106216a80542d520034100c50140040789024202400580e4140300500000e000c1003103108103640880c40450682c4082c02c001400d0000311072944046d111036411150302500c03466001b441e0320401030391515250000d547c6904981001007034482c0d8503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 98767257 1250 98766007 98766011
    0x1081b03071809030315050319060e010509030a0f0f05090105030717010b09010206101d071229030705031f0608240f0402130f09020d0302010b0a08060103120c0510 72
    0xb15101140540c005114580641e605004401c035507040804609024403900b034140d4010010100ba0090526105495a2042c0f80101e0008a60a03500f03094807000d0f9016a21034000003035048010ba0003000c101c9000c0a00e08044041660310740c0003038114006d4503603d6040c80070000020314440d01c5a0015052200c406181c0b0ba0156100e00700f03d500f58100c00e500741d000d445000085102000c10704080000c0320381e402c00b0102c00c4071404a090300314100151070304c0288100601c81800c4942c05006080810b140c101c0000c03042c202d00c1500b1100301c41390b880c41c2802508548400e120503180800d4001c400031000c5011128400c03007501c103400030600e5511440560041c540e81e40d40c9642021152002d0300d1140c4000c804548412540980030101514000c0d031100c01d001c1c0e460080100368019540391101c0301c0001800310a00d402180c0e6440b8005801c0340180d545444140c4a0310740122148090412500203064943c1599141e00a03000680b400e00240600450030341c0400800300a882802d0760345407c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 98768507 1250 98767257 98767289
    0xb011404020c010c110106060203030f150102070801181106120c0903070308070b042303091309060905070e07020a030801091104050307061e0e0d020904080f120f0a0501081b0307 78
    0x34078540b0a4600030140794205140024018400022f49005290102d8034500c0c0e03441d164a0174a40d01a0740580a05600828000094800081c2300d40c0144850851441d030804c0c081d4504100c03016000f50703c940c4138042c240010400e000741000035a9100c40b00040550391444803100007440c2007010f030b0006280003000a01d80080121225160b400f407441405401c1c1020240042c01c03c03000400c1c000d051155006012000c460329050210705401a0084000142c4045507111101540e200c41020380329680400b0b03041003511003902c0020b5201589101511038803400340d034014071208043c031070612515260807803080d201d1b88040c00c480081c040101180e0400740c0e00d400c003904184141400400390150800801c0c00507014001714554180028043c1c02ca03050260b00304040801e000e80140e610b50380a226100b00d150014004160341035911188070720b10b00d0551034040307004100501001c6100d0400b001008050400506214a510045000444940c3d1000801e1408117242d200344d0b05401101341d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 98769757 1250 98768507 98768531
    0xb0a05120c0f07050312130b04060203150a150207052b080f3f0c13091a03101109010c150612021801030c1503020d0507030b1c0b011404020c01 63
    0x1c01003464480c09030310641280d4803104947d0350f2018800c009801c0e40d40c40300024001944d2a4010360b4840b60b4001c1c4846252002001706041c58000d03006980003600f290301c2001d03590740400104004000460b1a8035189240c410070314140030b142d11040408940050b007100401c072220082c4c0700d0441501850588500f44178070203040100b03650301c10325035000c01c0041644401c802e440505d1000403480840e00940d8070746484510702035005e07a01c102103400d82c201010540b108607000314401051209506240712501e1410141010041c400c00c03600f492911a82803100d00d004d07403d89a240009080c4550b450101d4203250f54806001c0c01040015440c005005c5201100003042c58a031a00035150b085116000380366001c01e0060a00000c0c0210090036001c12460780e8602c11288096082d1030f01604000e4058200003d841e416202c10b408207840706481ca01d2400e1500c400c03000d40101101100c1031030110740b0f0f401031011060180d4040450f100f03200183e16116501240c0800e85448001c11040081031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 98771007 1250 98769757 98769763
    0x5060a1808010902090f071b080a020d0309020a090b011205090303042a1a0c01050103050d0201110f16080c030706200408071206060e0108010f060b0a05120c0f0705 72
    0x2840d1038986a14220110340e00c401441103590031640a401480c1c19241c0c100c2942103080002d043c2000c01c248442aa50704104e04141104520310600080e51981c4c41c03c0c1021341420014003880c01014500b045c08400741c0d03541c056030400c40d9442000054402017550040b2803100404000307004150820040c01004c1c80b0010081d40310703d00584a921000440002c883d0240b00102c04005000709072610034080d20408190003500c680e207003200a0700d0811052103860035a54240d0068419402c4003464807042c0b9020300600d07005c1038481810354540100a180c001c82c0e0b0081d4015058104940c5040c5000c0083c1d0700121500070505a048944590aa1410324058950500f05071402c82400032248a00e070b0101082d6020f540c40a000f51410034185100c04005031101b0006940c500d483c1c4000040040350240c225010340407040010038220002d40c6800140d696562080c460b84200b00650301c0d00c40d40c0282500d50604450311110050f48540300d600d0146d015841401101c24000212903040103000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 98772257 1250 98771007 98771027
    0x3011202040b060a051b010b030a060203040512030705030c0c031e0315040501120602090301020723070501050711061606061d0f060306011703072003061602030f0c010605060a 77
    0x1c40d0103100d90340401042c4507007401000e4145021850500c564103102e50340600b41c80401003020700008803052440c0c000b1b46004911141542c1541e07000043c0301c14080e080c4003aa11120502c01c05034a1410030f4040280540710042040000c9100801e00c641c1c2011b0500440e1104281c80c2c2e130040d0f2000200d440f80800b9803003920078204462030200e00155a0500e0f0052504807616144200140081782c0c8031000690b11441c00c0c0ea525550810203100001d5801450705152400700124000c00004d00308514a0200150425414840144804c10016052500b110350b180410341d125600c460f07160f404031200e0740c6031410003071020f400e2800c0843c202100305032909545076009510402d903241c20000100980d8282d61044d05500450014440c001c10041d00045d0b0907402c50803645800195190181c00074150200c010000160301020321040c501042002d400201c1040c200061040c0c4135006540e80c4035150747c4599802c0f0204026000c00020352107c8020400684002c1d0b46500000c0010284000307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 98773507 1250 98772257 98772259
    0x50601090606121104050103180b0a020333121009051f0204231c0605010504050619050f12070e041a070203070312110703120b030a0c091a0603011202 66
    0x11034000801c85002c1e03007072044540903030146170130300f4940114050540748c0da07103603420309410003881c00083c1241d0f06184280440c020068a07403e06041030411144042850f1500081803614507207070702c2c00c24a65200d0101c003250780d0813809004031105800e08241d80500b5014901d0041c0e40400c0c443c0c003241620140301c4103030107039a4010745d01c072140e000c900031130050f180714280380c1e14110b50740403d10a2100810314020840744c2c020881140701450f041d1152000c990494641c40100400d0406000d6180c2254088405041e04c20001e00007841150841c41018824582603084107078a81750014090300f90480345050303c581549072141100c03410416038046400521012000c269640c4c0c004405004405541c00380d850007400d40c50440c1c000e6001210900d205607501d86290980b070021005014462013a00d40c6501400d01114100441c0d030700001c03150203904440c041d10001003000394802d098400c00c2c0381c001075000050070700600301c10f0f850b00169005600040046a01d0a4014211104602c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 98774757 1250 98773507 98773517
    0x4031205100b030411030c1207150903110907030e2b0906140922150803030105060a120207020d050a050d0906050304110d021512090a02030604031803050601090606 72
    0x4555441c40c0c1c021505210301c28454505001040000b41e0160b42a10f07900001003c48102c100c560001842002c000c0c210340019500c6100c1c20440100002240c956081032414004140c529503101c0d070b5441a5a000789510500c0841c000508040c040d51001403041030850449440c1804040401d4040c2d500310340c00804211418603140d8108d200389001c0084e2444c540d2030074200b2a00116980f203d0b0810381c4855403141912003248460000e119103200e001200083c041040b0032288400380c40e4201e59004540c068004000500131034595a084407202c01c41864449485484d543c00c810090058030802544400b4250640c001d11000049004010303000301d0a41d242103041d20320a45003d0020b105920210f00280005408079a00074540161410094902d50805d01c0950000303052000105a02010340d2011480c3c04c6c10500b140703451903010784400001e0401c1d00c1d0a0b000070b9074400d0300610040800050304504901002d1035800c4400540d0b0150480d501d5507140d28103a405000c9501071400068 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 98776007 1250 98774757 98774761
    0xf09030206060d110108090f030307120f1401140a05061b0d0f080f180106090606020c0102061b07051903020303040b06180106050f1c020c07080a0308130c030203010504031205 77
    0x114040b807554841c1c640c0b1042584c604070240b401900c0310360f00184000114001d6210b0410001000d10095104080b00e5a451007005461064402141c1506140303098bca86082c4a00c01c04041d20700310340303056528000f010004501d8080001c0d050140980015810110210358141654581500507103214900c0040e1150307034013085d00803208855103140303110004000e40302240060741c2a0443c5500210a805480b1101d03110b0049079007928803c0e80044802d555603041006455410300802c2142a800d00c0079003050304169120102c0701000d06201d021003140081d02800f0404104030086a052001590800b40c41560802035141d80085800340c03507441c00140010020b10700088407070301180240340155805d03400d044040398150065004030001c8002000041c542507202e0075034460303440b0312450142e581c0101d2805c250409980ba031152403103522038100100020341004070301754844400d1201c40204501c0e410082c0306050190b001a415501c4c2070184401e041c1d200c00c81904011000e60180819 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 98777257 1250 98776007 98776009
    0x2030a11152808040510020703050d0e060103050607050c071401110f01270f03080c0d2a050301050904080c0319030f0516050a0c050a05120a02010b0108060a05130f0f0903020606 78
    0x2281003104c0003001da030000d19414004105540c054410385000c0c4c907100e820100300c00c030701c0402c13103408401d41c1a43d540040c004000f04041042101d03445442490040c0c02d00c1040d06a0a60f034842c2030140c41c0b031418044441c02e041d40d00c036007804405080803004946420b11103d03651402881c1c400c01d43e2400304244003021810800b0102c44095240e404681f841c1c40d002c050b1001ca601031000340c1902c00300c40c810024980300707518030f025006814035942030380c10000c0070030034075000c44442032410740e0144507090004102c40c1c0d503900c001076880b1b07400c801025502d0210210090562094420050b80ca907024005018000d40c15880034920700d260740020030044c0c88854440c4a0021136075800b00000344c3c10030098110358440e84151039203520070403c4610b038141d240c0d211814202c4076802d08003980ca010409990307003035090103682c800c0c1100782441d244505000e0301090440007240a0789000d51110040d0303402d1000590310140200b040714004021405040b80c2100140c450080e050b001840348501180013 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 98778507 1250 98777257 98777267
    0x3150102010605010801050105031302041d16030c0506030a0e01060b04170c1c02040f0f2306030604020915042d020f030109111b03070308010602030702030a111528 72
    0xf521416101c404a507880d2400442d196400104416081514440c0400c0140c690380910b00c60382d15001030f03030810000344404107860b01c5282c00700540c0540e4000001c2001c901d050001c441900c03019034046075295900c15034031028011440400a0750f40c41c2c0400024441041005082a82c4040715952010f65030186a42d42c4c03400001c240540c480c400c1900f07411003450391404504891300c050804035070300c4607130522142241c0f610002ea9110716114038211790704807511404c04060384407000c0e0100c2e440c200180465615140180028010418000480c01c0e800c000c00300903244010042060060581205820350309040d003502c3d0020b1203070040001c0f03084250f80d0082c1c0e00103241e86190582507038a080303644801b4140c9804400120740c0c00704004500002ea6045014800134100020b541d0307007400340303801043c1c00c005078090011908240600c00050340c0205d08508020742081079821071166140c0003801f00b039400d0104041c41c280000341000310000004402c025080072000d50700702042c031450700f074038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 98779757 1250 98778507 98778509
    0x3120411010507051e01110d0f050906041a040f0210120e0c06030a090f0f06050105091810150807030f050f0c0109030b0a0603140a0c06021f2708031501020106 70
    0x529084130400c503010004114000c502c400e105ca0000c075100c800040c42d03404507400081054101d944480d64030b040d103019030090302d410480030750003400c8500d41b07611a850388070f0000c202a0f281d0344905000c5001e01241103082058660010143c0101d00050f110280c0004080d5014204503420085c00040011000c1098103c084000e0019840c55a8088205c0000c1824600c12900c1100e01c403007040101c0c540746060740c1146c0c4100c100207440d504210811080e8a0300800c1445000f0440180d4220100046030704045809095008900f5250700003a000d081c010a820080c07a6102e8070324000148800000000107480c010b0054a0040300d00000c07083d1030b184040c5525000c280d00600c00c0002801e0703440c5096119141240019032b02d80c80e1755500f0882c842c41d07540c01c206c5601602446082c0f1192041100040c99280014145580401c5120310300d00c1e032003000107244030b81e244050001254450b02101000c01034550110b0070520038504101c45030001e542e2a194940701110b00003442d401445004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 98781007 1250 98779757 98779763
    0x23070201050a0203160c0c0b0c06190204030809120c1f031a010f080a020405061b011a09010b0d140406060812040513020c0c0d030f26010905090a0503120411010507 72
    0x581e4900b4041d00f56418407041c14100c03254000b07e0301c001900b1040d82c0241c20320807a040301600450801000e404801c20000f40b03c030448900c100b100302b000421041c11203030040e00a44441c019000c040917100d0230301c446c182849030004500030900c042541d0030200285143c1050714100042072002140304442c844135003030b2601007040d00c41ca2241d054020042e20b54400003000c030241c601516100801c005420017542c4026030b1044d10701903070030010280260142c0c0c1001041580c3c10000c44000284010010f21981c4000a000190000d0071241504400c0c0300d000465100c2c2c5079400c103840d08100800251143c4500c90085403100d0f40c03814102c03022202103680040052480318a5006e00744020340c480c02c1c00c1030203032003100f00d540040c1c3c640403030300e0150f28080c1d114940c2c1c40d4100c42d0003400f120000700d480190100c0f5001507907035030406210801d041d201040c000003600e42d116901b00349050b20f1890b000d0610720000c5065034030103012000e0f440c81188500c804085855105005481134020326a0003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 98782257 1250 98781007 98781031
    0x612070f0501180f0b070210180302010e1206010f03120f020c0405060d0219090509030406020307140a0f050d09090b060702310204051903120503040623070201050a0203 74
    0x401c40d5620600c0241071000500702c000794000d90300c04442040500950001001d0038001c5105000d628000703125004c41d4445042103010f50441c5611074032814042e000003410b0102c41c601603401c0c1e8a803191042d4a01c91120100c40740365840e41d4408580d40010300c07084498049228003e00094403451071401864035a030010030342141520208006000000c008540000c0840b1400000d41c0d1607a050103004803150f1a4010445c1c1441c1c40841507030b8000f802c0d400c0301d6004020802110342d00100b00c800c1250450f080d0074140c0b0501c00018200692103030003a1904920403003030741c1070150124840040c83c807207845809116646411510582d42110300c200e070300190074031541015052402e00b1765204210f891036403a056036401800c2592401806141c148550f02140034492410300c0001ea410313090340751070300410319031542e6510039440110218100412101201050811800d508a1551940025110032403a408952605051802203922a005601780004201c08a21038802c9074081d100040300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 98783507 1250 98782257 98782259
    0x5040e1203060f0d08090a0504110a0309050309031f051003210e060316021510150504050d060c02011d03030c0702030c0306040b0103021311030712021c02030612070f 73
    0x10506058000800b00341d0400e0302018804816980da840a1142612880840d500c88416405012140009801c05401249400a58040001c0d160f080e034020b88024a804185200540741c024118015641a00d0f0140310340109520140d0b00700000d50842440007101f0003003075807940703403c0380290102d1001900c1c075602140c000c01c0317405402c1e000442c0c0040394201841b00710042030101d81250f00489203100c024501c2c80041501b9513040c0100082400244641c51050400c40f100f19034203001071041c00000f0800381c003601020340c0600190b40003048010010ba00e0082d460502c6000b5106104c0c6410040d46040850001600c844154410f0456007800850442d40c40200e280c01aa00226090364903110b50080d00c1c945580c2041303500c0c031907071088225600651440c81484884154107044c41212801d00c0003885a4445050a980c1d0000d010700c1d100c80c04101c4040f40c40002d1203034003500c070240342800c0d100b1001446281c009500402054900d92561000355920070346424240c0903101c50a035007400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 98784757 1250 98783507 98783533
    0x405121204090c031b08220206160212060a050103110105033d0801060305010b15030402010e0a121103060109140109090c1203020a110105250305040b0a0801080705040e 74
    0x20240d010030929044c0040d142440b50058880c29056040610000311120100641003000c501c554602008130450341c04e0b081855400200540250a101841007103a048003e0540d6078100340c141c501c00445058603304d0070110032901c00340c48240410b0f104012030171000301c0741c0d501c1001260f124007000742c02001c01c0c6e00a41480b90300c02c030901140c00300d64a540009881415a5003d0300300042c14000300000380355103503141840c251000424250f02c2802d10b01503016482102c80e0480307a200e42e09103022078404000400080301c160b22078000c9909003450180403010040d850b030358814100e1088040b0381d01c607a6684013040a4075002e5500d03200004100c0010050810950001011240300740400361800e602e030020803c0d102050001030f40140d1182c0480002d0054854600c4482c81d800e01e001807414002c0c030102041c4500c0f201d0a05110b8250103100d1341410301c0354095601a01e2100c610598550812000034402c240a001703260ba24000c1c070500003510f1810748641080b1000c01000b0b4104414554 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 98786007 1250 98784757 98784761
    0xc090903070609111c0209010501021906050a1407020a03170c04090e0f0d180504060506040e0702100507020f06011d160e0a0308031503070f05061602040501060203040512120409 78
    0x1000c00c8403043c131a100032881c590346002e0848003020948140b0342d400070300341c01004402001a4041c41c1550810b03107200c070040100c0e5000b0b1440f1030304801ccc0030683e901c0d410500c10060a0000e200c3d007071594120103110340c07580e011680b401510300950300d5095507144200f050450b014142c494040b0701c0c404202c10040c5060b15005000c0002d400025103410003105030149040100302098400090f54419126030203005150010001d00f5055400308940e505000110780e0903c9030307020704244098220001030100d4400c2205094240c00c04409100313605003c0b001960f035141e90303010398401c3c0c042c038400822107061044051941a0000711090140d40711f50220f00402c1b8110500c000400201505010b000d0700d1b00f600e1200154425080c9694a01d01000001003024600180e584250000f580410501640100e088140c9204035102a514103110b0110761110000c0700d4020342081c1001e000250342c60700840900111b500580d5030f881c44840760224142c44941036240c0344000380c4140000d00460460b9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 98787257 1250 98786007 98786021
    0xa0c02010903050a05070611010b0307120503091f030c02010506060403061d03120105040c0c02010c02011b02090901090215070308011203050d1805070602010603080306060f130608090c0909030706 86
    0x10304101c86400d48989506042100c0318000752201c0d4410101000b44030391005c40090801c8516008001d201d00d0180040d481e80340611488840e90904c4048209028003802221480c0c280100030004040c0005044500e6004c1c400b03e24001c40c0c0307402c030b41440340d90040c003c4034410440200354928080c20340d61000004c21340b100b200c2005800e2800840d500c80000c200600c1400404582c40d174242d07140800700015500e01481510802c90701d995005d0060344c210f03000311480c640c2420700480154107901c44001e02501d40700007031f500c49610014402d0b180419800840c0c070500a0b10f582c0b41512400000e83e02a10072640003c000070b103408010401041c0045d0b289003200d11a16215280c1001070510006440750f2110380c1800200202c52401003100810020b002040640002d00006240d0b4a032030206001c0180310324000c03080012888140b82004040311800302103403000c140e000740c8a00000741084401c40d00c41c0103520030741c00102e02602d0720f030280500c00c4030400021480d0800d684d0ba0304c8081c6c025 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 98788507 1250 98787257 98787259
    0x15101710060504051302071202010501080c010905101110020403140c0a05031f1d1c03052e030816060509030306090402040c0e21010501091503020d210512060a0602030a0c02 76
    0xb0a1041d0000100842d01c1650703000d03404c2c2e00100321035041c5404142049070ec440c0c55070500082c40b01c200b1031900c44000c075090781e0041d82000c600d1074080000740c0d800c041c41c114840708014400a80801001040d4841d04500d0328000101c0391140c0000d014822060a01c1c01100c0d0b040c6c1c40b8103c64510245181100000740e0407120340030441d09050340441207410030341e4954a005030003042041c00181c150985141040c10740c4e240030712050400c000c403030354030103490301c200d441d0811101d550444856450a0190066501105007a910401e070605e02c5c007100241401202c4c0e4a040c038000c103041c4a00003060364000c21004003000b01d07a407200d0742004003c0c0b0b0078618074020701500410103142c541d00d01c40362a606280b0101041c03041480c1002c1d40c4d0841d071058019604d00f900d041590384400c001d2440c2402541c0e4195003030920b40e0101c0c1000482003100f401c0a10300c3c01c00f000300840800c1c0d0b00101400010005114255842d21848100000f4203400e0141c1c0005910038845059039a10a003107540038140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 98789757 1250 98788507 98788511
    0x5070515070b010f03060c030c080105011805100201060501021b060a031e0e0304050f0103230705070b01060302070c0509150609130504080316020610030308151017100605040513 78
    0x80340340e99850400700d0981c8045100380070213a041083c010302c3d0060358030000041c5410040c1c150f1303028010b403a03c1810b028840c10000990036200814807500200c00140100400d02200390301c9000000340680841d00a0b02d005005000c2146001500202c0d02d05010034010032060910300107020860040612890100106000c20145400620740d03205102c0d40010b640055980d0302e0410041c0f1800c2c02154103800d04052510300000310860030b40c1d10302e011a23561071401c01041c0c0c031020022100e601900d0b0010b01031417010000051025015070040010070311400f07070a400e4554500030071407140000ca0304030a050b000c0541140540c988000104000000100f5084625885180c084101c803000c40b02101c051000000b8409542d860f840c50148090091000700414a0140d070100205078807803100a091100300c0c804944610b030522900740b5001301c050882d40c2c0d6003003e000002d01d105003032101e1031003040214002c00c210b5010840040140c0b0601e8540b40e01d42441c020a001da0503002c0c1d40500b140725 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 98791007 1250 98789757 98789767
    0x3180604081c050405060703030605010306051801030b0c0f040608190c0f030506032a0a05040b1003050603012904050c0a0903020d14060c040e0f16050c070b040f0801061205070515 79
    0x2641b05070141110034029500090041e0a20b070014040721078a801540c440c1c80300c01c1d42c899412081192150640764401810b5000d910780c0d208641290041c0018401d1146002c94007154803944420fa540c421030340642090200d003800f000c04000c80303600061000010700701c16154001280260040c039000b42c405404c4411000200d004a9a03803004c00c5c0140e41007032509040d6015619010640c40c02400b03044030100450940b0314006544e11040c0741c21a0185a107402c0081c03416602136200140c844a0354040444400514441c07840241c0c44041c0e1511483c40c0c100441c0340c0c1300d00310040d130303030305410a40b548000301c0c0c01d42d000c101801c804400704840d0004c000c42080e20035030b0107000c91401503014925440e00c690600c0c1c0c0254141c030008241c1c0f034040c19540c0401c06908100c072102115211b013418010b50340e50300c154903e42000308540042e03410340b03000100010040307a1129070a0858403044020041603032030311403160540018090140c581d070302c600310503c90392070a150070b107580384d2034801160320349 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 98792257 1250 98791007 98791009
    0x1120309030506010b0d0b030c010207150c0204090b06040c0c020108070c05030415050304020114030717060607060912090e06091605221502190b060d08030903180604081c050405 78
    0x1141c8240c05c81d2480503000720f00c200c0104e0050240300300300c00046018010390916800000d5580415210b1030240c2d4640004020780503028903000e030400f0f600504240200c000a041c1500c0010b0705030785482c007031072418491b220418864240d1143d034030350503500d0b100d01c2d44402c041262203400320340058540c2c2c001048002113000305070095001e81600ca031100ca860385480d000151141040f0b030546011030700304104101d0245d902002d0000f8944280107040301c180c541d2008a00e144c01014801803080d0302c3c00d6010802d00000101c1806820f109a82d0001082c1d21419140c0244509980040d0000308d00e40101e02c240d01002c1d1001d0307101c1458a0b04074246803c4c003d00c80002110b40070800a880d14599050100001c581000f0460321030394001001a000c06009101940310745500140034041c11401042040c0d03103900b500001540c0028240d43c89041a001c0b2513207030b500074007120740e0b130880e1410513010a0a000098908880900d07000c0c0c03034420301d03a07003c00d016902c02104070420028108404582 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 98793507 1250 98792257 98792263
    0x9050705130e0103020108010501140316200106050906030a03080f06030312040b091e0606010f03020d090318080703030f0e030109080d0504060f020903030901140f030c03070f0512011203090305 85
    0x400d00b058902103554914000508079031010b070003850403c0400e00c03442900100d1241100d030015110000641c02018244c0b0446c0c3c3e880603180d601180001c007000120809405402000035954101c2d1003030800d45580f030402d45e131104c0c010002004990500d00041c508206000815880318000c0c0682e40707801801d000b1040c03920b030102c804541a05210050128080003004201d920b0149001285100c0c250303111183c0d40e81c0d000404090400480d48000f5422038030a405031004a05070340d80c10b100702c0c86c0918014000c3c84803910320348580c0580d030000040d282c0b00000c0100c00ca98141c0c8a114940242d80c8044403102c034800c8041c0d80540d202c102c54030001e4514402408102580c2c800012a410985840340c00d5484800d2000c2c442401488841055503000c41194604802400c00810340e10003031140301554040c4c00c00702200c4500100400154080b8140250312492055482c1d2209602011080c0c030b60f8001ca050034281700b40d102005110503060344c800b0f4540c8600030b00304452195a2950341e0741c9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 98794757 1250 98793507 98793509
    0x112051b0a080106031401050d11030f10020903010e121213020306070804140a0b0606181e0306010902040f0506030405010209030f0c3c01110706090614070c0905070513 74
    0x2c016000421802d0b5040c40342889001040d41e45003107952400d00021402c00c50040054110284c9407080c5941d6501000300111000740c038820385010171328136400e04000350460181c05009509104407a00340c520040b03904418a10f000c5181400e01c4400d40500b0000c40008015940182072140b8410140e13908118141c801d4a01d03590b07052651600d85040e01c8203d0300d0320b001c0c1a190303001d03100100c0001c2c000785489500090640b0540d465001c8590f4105a03100e560001c41d82001c206120082c00c02001d2000400d08503081e0708445440e6a500300002c103e1085224210750a1044102400030745010ba00840e00035020b10000760a04080340c00290408020440b01c40c60b90780035042203060f03400e02c80904c03d082c0340c41c3d00800c0700c90442c412030b03982194000d0b2040103681d007105844070746030fa00410025284e008200b00712190715444000c0500801c04a00580e000300d140c1032540e21201c494001180c1c50140d1000709028031620b480c2c0c3c0140a41000f50414040c00b000b80070050b81e207000700030294 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 98796007 1250 98794757 98794777
    0x6050a0903081207090909020315090a210908120403020f15180a0602070501120c020f06010609090b060a0c060b060409150f0509060904030c030e0a09021b0c0112051b 73
    0x2060800710006030101e951541b1124140b401c0c00380490259a000c98803d00480200007241655550401e045080100500c0001d02201d0100101203845001d4107454804a1040c0c886296040d11140c6c2c41e991190b24149900411104110500c01401d10303103000d00d80c1c85c4c4060000540d008884641c080c2c69040002e040044a05450b031414842c40c22204402c010009400981404e41c00c040000b002d10654100c05411561610792803c000c900c200701d01c1c000309101c90262821942c42d4900207140b00118494000c1040c20201090398615208044071106040d03510f03070308614110356988101401180300300c980d01600c2400001a000000d0099020b22602042407800c0d00d41005a50000c585d050380041e03003c0c0402008100b0355407034465010343c100341c15050501360212903180c00c039881251100744541112441300001100310060b000b6006010802d9250307804c090b041003405d81c0c4c5e0000c105a842c009812003111901c40d4803141c0c0300700d800c500d0300001c2c0d01a1000005400f04260b10801c042 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 98797257 1250 98796007 98796037
    0xb090906040f02130212150f100507050c040204080604030e04050106050901080907051c06050a02031b0c01090f0c06081302030303010b0f0c03070b070207120b1b0d0c0206150402031006050a090308 86
    0x3035441f40044200001c0001201d400440b510300d0404070300820000d600321814420001082030500004200480c594000200295030b070313075100d980340c503110f101c1030b50300701c004c28800402220f4070724043c0100c9041c2c0e0102e40e01d441c02c01c01c491004441c00e6201034500e00e114014a100401d994444030303100301180361300c03581000c1c080c8081d140180c02c1b100d0080c480e05c1c80a2061003030003008003684294a80501ca8003c1071a250340003e2044c0340100308030000203250040140481c4200b100e0f0000e180d00310740300ca8981b00c4e400c0e82e074a814000c9840d031000000790300d904108018007070804150003526000034003c41c0d03282400340849902d49594007110055410204680800074015410040000580310155080041c1c082998812218180183caa00070740810388050040b0300704c118096411071207810b102030214602940000c0d440c1c2200341c940b0100440000e04008070350425000301e900980b484000b16590707a1824108880c90703000640380004000b641840080400d0100c005410703104d514000c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 98798507 1250 98797257 98797261
    0x20105180609092806081009140d0806130216140703020909030c0607181406070f0c05040608011e05040201050f0d05251b08041a04090b090906040f02130212 69
    0x2d19441081d04c0500d03c107080036001e22078a1008640704940640000700440c04011a25000482c001c0310180442c041c0310344d415816040340d010301c2c9a4000c1c002503410640b0030001d01c0803101644503498490001c02555546503001500c28640a98102075060599400c5510780d800100d2070300055501c01c07080e45c000b28040700700303101c103200181d000704403130501c070038005c42c0e85c2204482c1048500c1490350100900000c6000f41c1c1311402204c44550340a100c1100400d003915080040100d1401080c2c0500e113006004610500c051084031840203203482c4400c914052091420060180208201d04000051290307020b04191103014040405030880c0c04181440e00c04040550f040c41c4803c5030410007100e2410351881034001c0a009180c020071b0902c082e1a221500700f0010307900ca0395003c00266189450b40f0340b880f41140e8050000d8410001c42440b15012641c10007060b800180c0d80d041440e044140480d00003107441c448642a60310203442d41ca40e000000c4100c0080341c00035035500c06014800e0302 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 98799757 1250 98798507 98798551
    0x307080904060501081b07050c04060b0d050106030c09050f040b040207030f02190206030c0a0c0804080102130905041e05010e03070308150d031202090604120f020111030702010518060909 82
    0x11000540828a89401d0a01e094206000014440c200500f051507000a0748000d1180500c031402070828040c109111650b3345e80302c11441c0d42d210100c1302a00610300b1001050b5544280540c85003540280d56944e54141400304106484101400b180e40c042e588200f401190386035400902a4903011752180701c000b940124000c1d0804d03030411180001489102d01d1000142c0e0782c002902d070402e18404030715803111420003080d144401d4840d4040c00132030003c90005010f0405400800500301c0a001141170992344220b4981564001c1c1c0c0c00400c10007401c040103180d0b003c845007605105018000100d204205c041c015421a8000031061b800141c80c107041006120004a60188442c0c042e1500942600300d910001c01d10a40b5103405111960001007031929503907202c0c01d8802606050320a01d640c007409281503807510301da101c000c80c041156200a000d511031b01209460035590180c450518004a01103040301d00107108844a40c095410300c8001e106403640800d6600c1201c0801d541d00c0000300c01a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 98801007 1250 98799757 98799761
    0x1210030507060f08270f072904030206091c060c0f020312060108070905040e070801150305070e0c040902030a0e010b04020c1c031e021309060e1306020c0307080904 72
    0x50410310038054038843c804125680600800d0303104a11440c500031155881d4006a0098802c009246a81c4900340540d05002c4002c9034040860b13698100503000350b03211040704000c469030007000582c03000d41440104050b050034001480c04a034020718001d03a00a008148040088044500750b454555592015031419000071400e866100e080c0015800d141e0916180410018000c1c8800c9c1048460400b269605010b02403003000f618000b0000c0c0150900c40c0d0595980750380311b1045110350b40c00c0207000400706040010b2041900d030001d020348030603420580340102e144005421100c07290130800c40010304a8140c40914060b241ca0000071400c154001881403e5501c2e101210707100e81c1c81040390700041940010205000264585982141a24548240d0040288140300003000c0c5000001000900491340208001c03016460000f5002d5101d00424040f1003190080030881c0c40040049040700c0190021000502e2051402601c1c161800d030350141103410a0f07038101c6480c000401d9021081c9031074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 98802257 1250 98801007 98801009
    0x807030813120b0a0f06170610120503120630010b1c060b1206040309180507120f15060e010e0607021c03050903150702100605011d061210030507 64
    0x2207200b05032081c88a450b00b0030f000c00040c000c076000554501c0001d414102640040000340741402200715401c0c40b0410158451004039160181d20304a00408500509194600b800c0542c000c030044d81410020302012850312006000700b80c0c0f114601d40c3c01c1c400c2c1c0c96541016481d0200c2083e0512205140802285c00d41b00d10041c0a48100420990203601c2c4420710b07030741d880c5181c0101e0041b80c0585040042b0301807105c4401081801d000c1d41d010081450781000c01c3c5421281440d00c00354146018204080480d0130546031400095a07001e00000030030900c2d0021100703c404030800140c1282c8540720f4511103141a44680c0224410306500241d56800c0080441640c900340d600a1404145038000754000381c21a240c208001405500308041c0f51044045e00d08044000e0102c8164250042e5030040010f411107060340103209030740c1c4102e000300d240e001c0c81c0100c80f0180c40c1c01d40480c2c072040c00c80e883e1440250300fa54024030248070010909042d50b51090040710b441c0383c180c04150840c10002d0800c000307 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 98803507 1250 98802257 98802269
    0xc090606020616120b040f051003170903030a0c030e0904060b01020f0a050a03051b07030b190c140f0c0105010f0503011d0304120c081f0509010902011211040807030813 74
    0xb203000d00b0005641c114104400c104c5000000154a100440000740102094041c00701107a1034a004c20103040a080c0742c2d5420ba030f024030790307a501003042c2c20241022480380211454142e0014030503607101900410701448014442d0a0010354012500045102c03010308880c1a10f01549450088945580621044c98400714100c06004200b030300d40c8550780d0381c01c40e4503801002c004000a00a2540c8994804d1080d4100568181c412452390781c20a00c00a000c1600c80c1c00900100b00700460700304166210705041043c1c01e441d1000d03468103020245d4000c0c5c10120441c5c400f080704006c170f42c10b41c507403e100340ea02802200c8040c221503030500f0149400c4138510750480025140034a051016032000005940c215104090f05000400d0580307020031000d0780c0d0ba0b22681c0c06110381501055030f011140c3d81616004040d840410080e0381d400041400d0b1940c008001c0e020030284410500e21401980007519014003010032a45031a5176003440030314201c1d02d50703c140c0701c100002c036800c01e814800000000080030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 98804757 1250 98803507 98803531
    0x4050f012102060403120203090607050106060212090904020d03020c0d03090e01050306040803010e0601050d0903020a0201110106060c06020310031202030c1002040b040501030207020a0b0f090405100b03040209090a0c0906060206 100
    0x203401c2d408500e0500c43d501001e01140600c00745900c2c40b510800c203c40700c03c0c4001d408192211941c0c505903006c1d111034044c00e4054010b024000d4680d41d2020207407419a440280002080c0d01c0d20307003c1c031100c529002810784c1140540d08842203551240c108a485403407190340c504e145c0da07207480080d2040c0d81c410703080701d4400c1d00f0440c2480003040015054a05664810340da260a6032909001a5400d11514140c0c4c441f29003880c62030401c0c95000b0404520b010700030381303039801c0415055000c01d00301ca1a9000c1d02c400325800107104004a10319901842c2d000304060040e444c0c054507500c9080f0b061000d6644440143e000069042911070140580071b41049207a400354101802c00c03900d1900c601030350050030304240e40440e0a905540c0c0f15200c48000309203a907040c0755258005820180c4a91194031414012410500800c1d55508420900c0080344c0c28a2001400e640b165802c011101c10054181c0380d1501c100b20700c0c0342c0450206040b00b00100300540d000111107150540187c04c0c000c004042d8151a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 98806007 1250 98804757 98804819
    0xc0d1407030804020915030a0602040603050601020a0c06032d02033c070314160201060f08060c030603030c0d1701080f060711031b1e2109040b04050f01 67
    0x1e5000002207400c01e03411100d03041d560382c1303c9017900e0315001d9408120303602d03106000c0114144681603005206032803007541c0c1072120750303108801a03035950b04034500144000444001000810710992010fa85410500303245501591000b00c92a00c100050b1007822525034000184094040c0910341001c9599203508202d40402c1d00c004c0361503500300b0f101c800301d21034144100090072851203a840000100300c03e921000850900040402e43c0c072484036101805586010008070b284008151801d007111031482c014842c40c0c1d204402c52045401c0500029010320040c08000c0d43d5060900118010341c0156880810780f04081c00001b6001d030042c3e00000c1c0c1d0f0781042684900800c00403480d52ba1008050510308030320100000c0351480c40c03081714002030380b9044801e54551003050218030240070700c0454451a00c014030f1945500e4561002400e08070b0800305040390844481404005804669001030000034a41c9140c03020070242e4901f114070420070b1500c80d00601083c0a4003400010328100311043e40d9481d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 98807257 1250 98806007 98806013
    0x1201050d0807030302160f11190e0109020c070503030c01050f060f0d060b0609040c080a0c030605060a0f0207030f08030603060709060203090d140a0b0405070509150d0c0302060c0d1407 81
    0x41c401c1d460040c0030150005414035413510030f2001920740e143d010f540e00039000d0190400500c8c0f0786c0405040c0f4490600c07032a6140d6015844d0b2075000555000da0f8628a41d0791a0200400c0254440042501c10f8041c1410000703036690140041d10b90000a600045900d1406c601d0601c81b90800800040c41083c0f180b11400141e12141019098103521000000d080d132a00301c0010414080ea45689034814100100454501c0d40304010320b000f240780c0d807014000c00c0c1041000b98159a040d000f881d0308038109109003285107202d02543e910900580c0142c075801034590f2140d03409207012200999040340c3c000240301c00c0d03040800c5200d91040306403400700b0300a420224003c0d2079101d141241032060038910711080038804c5481100b034694910604440d40c0d800c4615007a20303036410031182616a8041c0c1c09000540382000741d045446904a10800c11030040d183c0c0c20070000e410b5000d0103a074540511540440141c45401c000c2004140c2000149181d9695aa00800c0004d4070404142103070000e000c0c0f0000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 98808507 1250 98807257 98807273
    0x601031511130306150f0605070b0c0304240204090c08061009080c041d03030a090309091802010f1209080c0706050721021903050a03050c030f1b040b0409021201050d 73
    0x141c2e41d0102000ca41c051758181040708091044e00400490320007003034000365a40d001001012018421481c00e06189d840200b0b041c860b0000710740c082c00200f5600d03030940410302000081c0c081c2d090021001801d2035264180c131805c440c0d480b0302a401140780f210038881c407481c004d802c0c1c189400403440c01c412120304103100305844582840141d0302031516a03032006d007030301840c10036955212145811691a03142c50003000002d0300e1000b00c158049420010081800348160160758103100360b081245110090725401102c200d40d420503280200054140c000d1080381d0b01e40a03607800b05000e465260345483da4444454100034856101c103042c00300c1000f56000240c0780c4070311003c0721158618001c0b820800faa60581c240720780500e82c0e040b44e580d150b410004158000001d004000d070f643c2d8003003015556800c40c10402c2d00c020b8500e0b80c0a07149120002c0c03400c01ea0504800400d500c1e054582c1d0a0555804103c81075400139084598050340210f0a04003104140070440d00400c0100c603070403a4580b00f0740f90071030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 98809757 1250 98808507 98808509
    0x1b050f12071a0705030723070b07080a03020912070303030c0207121707020312030a0612020102150402010e13140a020f040e0606040f17010c0519030b0307030203060103151113 77
    0x28101c0100c81c0301610702c40402e541001d034018090f650785803550324140f501c8142d94120341d03a40400e0f0500050441c140051030300203640100b8100c0c1d1500300c0d140c44005031a0040381000042540130003d001311501d422030804c040000c074070001e002d5581185805016241032034148411507114120400c604040580740c00110364100021100340c0c1d00d403501e001022310601201070b42502c50100500c500f02e102d0750003107119107402079003080042c0c1c895080f04107620282c44040e0045c0e00407007140c0c00b500240840643c02c06d03c14100306030325a82d6400401c7c00e242d090f009005581f56a0240c070b4a02092078400554055400c1d0000c42c903144c0f0b41e542811090003240a0a440d101c803280001d0055100c00040305d025102000b48409100da03030f1903401c07080c0b130820703410fa07200b650030148c00e04900e0340070300d00f601d0520503901c2100311100d103c1c1c00c084000f428000308040d0b0501c100e590000150310b050001074065805824981c2c034000760351f48050305960703086089000b03a0608018210005000182d080 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 98811007 1250 98809757 98809769
    0x120b040b0a03020d0516080a03030b010f0806061c050a0903110105040b0708040302160906080c010e0f0607020a050d0b0709080c060415022103090c090609040b131b050f1207 76
    0x10100c1341c0641002860207800521540f000c101e806008a805000007996040309442654207100000071080110b4640081e440c02c8008220740b80e0100700c4a141260240180215055815000410701d150300402c1c2e42e030903600740100c2a603801042051550080030030290320640b500911050070140d881105000005051504114550003c181010b20a00100240c0d41500f2150344426885420420043c04248210000d600c81d0141070200381d409074021548080c0c00801d0a060304024106004140e400564120784c410f10f88040811581e403141501c920890142c0403200e92131400c4040034104400c070703410028140d842404984442e0780d4410460b0241c54100e14220074100c600102a417500314441900150882030201c40d001c0301200c40003440c0309042c14000c440c2101c142e0403d1001c9200d083d90020342060241000234040307641005c2994102d50540d803c01e500314100d855014540d03081e0111100340407a000000c001d185480346205043c4001102c4036442c00c1c0442072000d40c3e800c047d100b15 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 98812257 1250 98811007 98811019
    0xf060e010812030915070807090608190e010e19020a05090c180a120308070f09050d0602031b040305010c090506270a1802030108011b080406021c0903120b040b0a0302 73
    0x25920981c10300003480124100c40b50840381b0300b44014090200c4030102c405d20b0000d454140000b900302e114641c80c1d4040c01c10030041000c6c05207900c000e41e016007a248401d951543d00c5821111003d1410041134080202d88411a66050641e104200d4410b207298082403085480d0310034405518207080413075841083c5c03417542d07294031401d00012603142243c075801042c0c82d80320102c3c1103040c9038000702c14510402050381d0320014521800001d40d105091401490742040300c0d00143c01c0050203c1d8011500009400781e610505100405040855400380e08101c2e11070f511003114161090300074038800043c3c01300711200c1d428040311079814840c003200c004034400855914100c90005484207503080024107100d4903040614000b52600501039402807080003515841c2c418804010120352060840c070804568441242e500c60f51120000ba41003400d042d6040c081a2403000c038803400c148203042d540c074882d40f18850510b4000d182c1d4002c4403281c6030454056810401c61648a0b03a4100c600340c2074035412541 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 98813507 1250 98812257 98812261
    0x50919060603020a080a02030d0216050d080f0f04060f14090405101a071a0106020601031b050316031e020a05040f0e01020c0f0d0504030804060309030201020c010f0f060e01081203 79
    0x41000780441c0ea00c080d4001c01c2c074600128124402142c080701c2e160003503040b40c001c2807660000320b80e14081d103400340340c2c00945840309015624003140d20349911402102c01d14101500b0140807481036205000a015401c0005410440540c0102038003280c0c0c0aa0304000104180e11001c60030039106007400b440c480d030350310800200d2078151012168040e28450880310107540c1c00d0030140c051540000c8080d103003808210b01020401d0214490541652495400b501050340703140d4412401400100415811112010000c91180c404102000c1d140740d041c0034002c0329038990705148000d43d80901c43c1170915901d0404c1c1c4005070f125a86079504461081c0c0b40010a42e0f83e500c0342200038090403000c0b03a20b84d400059803141a010010300e03040c207076100c1003d48a4001e00e111703041d50f0520403880010000c03c000e010402c200340c0a5803100a480c0d000c3e0001520f0b21000c0b814071070031114032a400c004c0e031599541115840b10100c0c440d0501410446a42c46031650400c109030b540c540302d503401c2428102e00000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 98814757 1250 98813507 98813513
    0xf090606040b010c0b420103090f0807120f050c0c060c031b1b1008070e12060f100b0901020604020f0d020604080d030c09061b050f0d1e03050919 64
    0x10282d04082d400c408001611304110300510700340480c2d40855450003045c880b4044000905a0411000118805103004880c240c3c17001523000d01880341c1705070b07490700a45070030b07130b000c100c02c50014140d41e44102c0092174401582c02d00641014400c02c0c030403081003010b12400b00c416030001105280d00d5001c40307800340c0752034101c0c28040c9584245110145150350208803440d00c8500041c2800742c040507000340f8500c01501c40240506608100c08800c005000000869929802100302506072b000103098040e40035003011025180110541c3d80d410464041e0042120b55411441d014010f000c545410a241040c90301c0000e50b1740e10085c1029100b480b010400400d642e69181c0c015101d00e0740580482c1d00d50f40d40c1c00c0000e80710010007040c403011a0900e90000d00583c030401504040e84d400347c03120010a03403910544850b80c03903c010200c94134420402a040364a40800c00240310452698032503c40f515014000c01445018661010a060402d41800515070300420040341005041c40c40328004031a0382 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 98816007 1250 98814757 98814767
    0x6080c0918010f09050105070f050714121902060f0c1210091415041506080a0b040612030e0904050712050a020a060e09160503130203010f0e0304030b0f090606040b01 73
    0xe810001c41d42c81c101c0706110581c1d03d83c11001d8114000c0c8000c01072550b440000b92241e00c1407640f003000048003000341c4400948514441224060b03050100c440d005e00c0c6040f501e50f190300441040c911000c0e0310b80c61020450381004035a40c400241c4000541c0c2d410400c0044010340911411034040082000c00115241c88100d08100203010b01c80d010f0240c4000443c40d14111042907503140d520302c144485040e01418180038000800c01c1a00303580041c0c500d842c03400c40b81d00c44058440840d0300c1d1507281c60081030b5039501807017014151a9000d01301140d590300d409401006000481d40c05840c42e0800c001c045103010803208104d804d040c651082c02ea00b14a000350a11313469501c000c3d8000c520000c0810b2641d031200c032454403040c2c25524000305031543c2d01000c0d0040245010000060410400200c4e0000f2151003044e40501c043c00119a0704003207002c3d201510780b0441c1c0103806500100e02041409488400143c21050a10300080c1505182154070b4a070b0340010a80e90095884000002c3c00764422 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 98817257 1250 98816007 98816041
    0xa0507030e090f1602060408092206030b010603140f071b08030705031b07020d030f050403150902090c031012150c020618030901020c041508030a03050a06060306080c09 74
    0x402c203090703d14004032210700f800b40c10784005074151500c54010b440d55000090941c0a0307a00015980d0501342d0080400c643e0340c0c0e03c00c1d900741d1007041404c8a61085440382c0242c0c0081c51003401d403006c9560401000400712000c01d0b00c510110b50030030081c0f1070400d40d24502250021041e14002c0403042000d10501c00c0360b20700c0d400040030b4540010402100700c0d0312030040d5020b0550b00c031004020408110980c8581d000303030080658403981c801e081400007030144d05400801c45044c1815070603d81e0300e44030084401e030116800391400d07484213603550840c0380613450b241d032040c02780400c2c60450038101b00185086015003d800038900c0580010414407c201c1c0c070320714081103e29030a000048448500a460b000145c1c2c850450a86000e43c4981105000c41a41c00c1c840042e801441840040004c10001d070690203042c2ca02da1018030700c007040340d0a060001b01302d0b403013003910041034a0030103036101c2003107e0b200c0e4484c0041502d801e005000d09000428500000002214020b50320744609090311560740728 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 98818507 1250 98817257 98817259
    0xc02030c0312040b0c070312050601180902090f040204030f060f1506020a02030f0708030904020904060305070803040f050312030a0507030e010606120f02281404140405090a02060a0507030e 83
    0x20100d040e00b520050038280390700c11449510a84402d8464204002da603001c0c803140203001c901e24901c001005000d550140398031120500d000385280c0460f2000d0030800195400c805900c64000a0407055404c20744055500e111043d80c04502c0c05285458421212039900c00082c9000e881e101a0f2400881640007007520101014105d8412556846d0103992103502480481c002e000303602d02d0351500760003c41d076442102e03540c0c0302a519200c00c540c10400254000c42e540d0350b20aa40300c0010012502c10045113001e8100d5800456842e0705040c201c200d41e00e41079011510942c0404c0c01083e0040c41e0030300fa290008021000403819854101050f4080e00161140040f158070700400042c2455100f0b0740d000e01211040c10812041c25500d01003401d80c810166403000e50036554400c0c40d056030741c0c1300380700304500d00c60f180610000900e4802c040080c0c0c80b0b0350122103100e003c103030800c88626051081a17080141040103044080c41607020900303e014030801c050600c00045180001e05002d0b9402d0208140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 98819757 1250 98818507 98818513
    0x30910090b031018051005040c0203040b040801140c0a0c080703030902031005220f0b07050d0609090201140c070501030b040605040f050411030d080c0304030e09090106061103040f090c02030c 84
    0x2e0314202c0c41038416924400d00359803000c1213254040020f0144035890041d050f2188006072036003003109000290085400740d0046102c104000604c15000c50b01178002743c0100c10001c60f103030040d00b481c0e59048401518540d44c400b010491240e4594105800c041480e40c480c03501c903103d2040c1d00342a0700515912002a4250262910906128481e6030003070b485070303178035034881e0540040c00c0b400078545131008038004004000c801d0202011400c072411946c3d10000901e0706034030380a0030244200581d41c899100411f1141c580851000715078000050000c12105440400c1c28000c2c070802540d0b5900c420b10440341807642c2c40660320b0003a02c4603080580600005042801403a0905240900a02d4211801c1d0390000110080103940d01c4d010a4152503903202d50b43e070a0050701d071100c0750b51a6600c0038108500740100f902e4002940c0d00c865107854170841482d0b00008080317251000c06400d0034480107000070244c01c100018002c00103081900360a441d10340c0c80001c0c5c3c14412075000c1e03113140720744e071030100d41c0b84 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 98821007 1250 98819757 98819761
    0x90a060b130c031e110f0d09020a030605060a05010807051c1b02100e0a0308160201140f0703050708010605070602071502121006080123030705150a0806060903030910090b03 76
    0x158140d0422000e040780c4d000303454490480c605018040300e0921005548041003002100740658504010b03180540522100161403502580080c4621120354001ca0f0710700d498400304481c5103009250003004001c00e09180b00145880c00c0000c040d80b0805c1110314a008450b035442c08100d805030300c0035008442d01140403103e00340c7c1c8070000c3d60780c00c0c040b40b2003440c40c0d04001c4e140d080420f0102d81201500e9040e00c89039010380314000240d010101c0c0001150840d940c0d13441940d0301c004440030481c000d0400000710f1300f50f030400540040030303224010011000c3c414624010440960301c00215000103801100044e16210b8525007170303582d110303030341200480a4000700e12036200d14040d140c0e0600030320161009000c055503e401c107582c251401d101d080e904032420000b80c4078141800d080d42082c00b10080c02e890a0030307240c4c0c0c001580803c015003c00d00800e1b0100c0c010b89840e0b04089090b0300700c0d4081307035418104031074000029038a12900c0075690168406806100f03030342d030181450102800c4411407142e224 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 98822257 1250 98821007 98821031
    0x50601060e030601090207020f010f0c021c0203150714090a0f080c0102150603030301060305040203010f0f0c111917040b0304050c0a09050f01031b0503060c040f0e090a060b13 77
    0x162114605140b00740034080000603100c284e0f108a03160284d02400c007038020041c020056800c0703903a01c0c803a0300c18000c200d165600166111380e201c400368550310001100c0301c01d20b0300500d03282c10b054010074ac40108642003844001a0859180b0040d1089848107698450b501030201e210718001d0782c414401c0300021440840c01da60046440c1c3c1d070341c900c03c0c1d080315401d400504ca1044100810b5400d250190010001801444d21a8001da07520500140000c10030b643e07007401c1d5500300d030104080c031412165901240e1403400d030b00c8088001e48640c008000c0003001604001103980500225009100d0f810005100d6441d40700401603078001c081a100c0c0f0382d01c030301d41814000d0b04c4c2c503084001a80320303891001e80404ca401451007032a0217840700041c0c04803607a0840c0d4030700715030301d1850041070100c0c0c40209000610355410003181d03200f05165500251110b18001215900082ca600074907900300c001c008111a0703a80002d81c40f944103800c0880411461300f5900405c1d204d640c4408601840c034140103058a00b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 98823507 1250 98822257 98822267
    0x5160530011e1d1f09141006060905030f15040c050907020a03091d16030b0d0f1203050412030f0b06030c0c06070e0f010c0c0b0c06040c080a0b06010309050a05060106 73
    0x1114200c040000b840c942000425034032030f50a100f82501c4400300d940304900e1a03d41c5d60008410034482d0344141401480101103a1800039a0103a2610aa8581c0e000b403003543d0b4801006002042d0aa008103103000710a1f500d552101110480603220149220002e02440103050781d4a00414004d852901030b4207007000c000751507440030002a80800da06031000210321100303c0c004102025010f03021440c5403140c00200d540b500300ca0102e4420151900d10000e07066840650454500d44207298500300f502040c034084e201100d01960050516250608100100f07540f84c0340036000203040e180000720210005003000013005103035010780d042100402041491280d000003060707008016170468400e03a40d400c00c100d9a906002800310340203995000c54007490350107030010041141c800c641800401da1280a0188680c000403484409584603c040c4414044c500d103191000d0940359002c0c040c1c107203898681500300030300502410704050365142d05200b48a03092056055041d40282070360f0385940c0da0080146 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 98824757 1250 98823507 98823521
    0x141c110301080c01050301030f0809030703050106060e030f060f1815010b0c061b0d0c030b060c0307120206060105040b07030c12050a1b02090403030c050403080705160530011e 77
    0x60306108007242039030f5540c05041602d040325440ba03602c000e00491680c0341c410310341100f401c00303400d8401c100c00400052000e000c1c52016003100d035946140305005408143c94149100b1070340c0c5094010030181300e07407298403800e1183d00107211800c103426918000c040c10319000007244440203c0302c9500012500e08644030090000161036421680d8a4840d039540f540c181d200d0a8680d0740c20401000207031410004e94210b01d03551611410000703a610786d44404904103a01c1a800713007006800c0040c000302089213034810600700e1945440142a03914082c8006010351245014a031709002020501000b0180f25520b1a51100e910900030b2520742d5440300042e00e6600901403400104404203200140d00c0d100324206c2d408190020841c04803510345403400c1d00203004a40c84102040f00400c230200115410304010250341d44190001c0201e201440c903d52108001500300c1ca01c204c0c0d50001c502649500f0584440003254200703d0103201c517001c1100640100032000702408410400040c1400c290703480da102e10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 98826007 1250 98824757 98824769
    0xb030a02040302120606010c060b030102090307080309040501150903031b0807110a0503010923071a030a0c0302031905060303091504360c0c0c03120207060906141c110301 75
    0x44251213004402500c07071104403481070004040d150951b0102e0320b290401e160718040640014989182c0d40042414044c0642201040390f00000729160281851720800e0f00400c00320100f0035000010240080a000b0707035210113000c0009003002900030110207a80d044d61603500480701e503a90001490015149070050405d030b4468180d003100080c035401e0600440c0c0d1601c2d4088010b80994004040c0c141008013a4110101d081c802e0020110b0404d908501100e403030100111025140e1a20b02c60040076200102c50708810140180140040c0404032615600185603540d00450103542c0c2c43c001c2031950058000156202c510100720306260b00c0c01c03400600545001e81c605034944101102902a213181c0403000c420611900c0c070101407184025400300f032241c46546044001c0300d04603124191f45002e02d40040d1b4603071406480150381a074040003144000c04540c140640b10030307e0084040d1100c0070242680d9252100000c45200d20385071a0145110103003241800c001c6e00c000e481c030382c44198000340160 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 98827257 1250 98826007 98826019
    0x1140112060b090c040b0f0d061206060909080d09060b060d09021e06071712040606170607020d05090402040f03050a020918030306010c1a070f0912081b03040b030a02040302 76
    0x459114100f184100344120300022090f45024641020421503074001d081c503000b514404e0180700c3c4080c03000d00407023000f0004a000100c401d13205051010484110b540308950803032030071946800141c544025100c40e04000380d0000f41c95803490400d04003611200b078001c1d503c80c3c40011442d1040c0541e40c800c2c0f115a00a8900c000c000320b034100440d0500a035111603550000080c0003100003d11041020407600d02c01441c114181800d1182c0740f070f40b407042642d0480302591200003e100046501c40c0182c01d10b0092001011b0f241010700c00a034441b8940083e0404010700001c025a4644454040b140184119511540c00326900d0070202e445601da104201d2242c0101404038001311421206c20304c1e0101c014002d03510f141c44400064540c1031505000700c07424001112580c03a108010000c1c1c9101e9411602d55215840402500030404141c94110070682c0c0c258100110110b0380b0101500c110b01e54444200304050140310302c0c2c2c0d146002d01d03030000d010440f002080000c9400244c0242044078429900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 98828507 1250 98827257 98827271
    0x150605100e120f0f210403021203071704030605070806010c02040b180c0d060602030301080304151205090604060c0f0206010509060109030b0414010c0c02011b08090307080c030f0105091e0114011206 87
    0x200c0f026040c1c5d4065040301c41e100a00082c809468104000141c3d801c030b0380c045130302e00409980c42400c9020f51222600d0800c1000c14200140728180c00352540c02a01c614202c0070078640000003900c0c041d034207007000c0d010b5980c1b0141020951203198121007110b07400b003c1c9010314074141e0b59510490b400b100390040114140302c40014458000000d903416595090080c40c14039081c02544814880350100c440d08014580461244070a610304c101409503088034040c1501c7e04d8541800c0c0162480e521501c42003155074413403110280da0100f212415a03404a410241c7c0e03845a400403540300007140c1000c1c0580c14054144410007113050080c50346200103000a0011400d2003a06468018855201a012a550b0242030101d80c15102c46400224030882c6c0e110305080c0342030086441d0020b141c100302000c3c0d00948900d0414a0100700c640f201d160707044000c0c000c61403c80381301034441d2030884014101001c07880c1c0c4001c910500390042c2c5030110326103103016082c0d07a45803d120801c00000005030b641c0740c60494 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 98829757 1250 98828507 98828533
    0x60e0109080d140907030b1f080c0f06040501090302040203090a0b10030c0b19110a05190204060e0121050312100311010801030c0b0c150106080103150605100e120f0f 73
    0xc0c0b0f083c400d4040c140540020380c03031a00d812a10352001880b000b11682100c0b00c2c0c014079541014002c02511040e0000c1a804d9008005d00c036440400101541c031070b0006100800440e03a00802450a60707a040d6005602c0c3e4403052592072030305818040c02022501020100280e00304011500303400c41b40680070181100303a841c441200e4520035141e803141c80c902c5566404081c5070190007128012140b41080300d0301114580c45090402035011564000134000d40d404109600d001c1c00750300003405103000340000e01c2d450031000c009509541415100b000c55008003003401d2050901c02d9410000c0d60101c03003441c5143c59601c002c12008207000458000390814507200c4154801c0b000241a20780c8202508038050511040080301d40145000c001c9a00c00c2c404818603102c0d41d50344e014001c00d110b07100c0554950440ca071000400c8034440b40c00c95100e18103801044641c1c6ca26000c500d0f202000c0c2482800d101090000c1092291480c0d5200c460348180803401ca4850f00005865001501d40020f42d4400e0101c08 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 98831007 1250 98829757 98829791
    0x11100501060203030604020703020c09091b0f060406030b0d0606090f0608030711190305030d02090306130c0605030403110105040f11030d080c0c0a0b070201090c09140a0504060e0109080d 82
    0x70207040e0042c1e01c240000f6056086c0765004150240c001d004036100250300c4800500200700c1100e5010b81c2d0b80100017a140c54442401f0203020b65101280c1c0607a50140800100390180598440d44c804c00d51992000c01007501c41d0000413000c00e030400000d0000c261982d842e02c2c040c100c0226023404035880c003040050341da00c0100a1b1080c842e40040302501c0031803001c040040c4820a0551985040b5481c0c400000080c0100f0080403041d010f0f060240e150320401040504041c0010b10502c2c02a02d454003c03c0017a0f0140001401d0300d0550070081d85076101c1d804c00b103130040b45d0040c0080982d8600010300c01400501948107220902c58403180c0003560315082415115070101d42c12501045103903001c1443d20f0b0044010381181c100b103400303e0f14600c181d038a83e100402410b840200142c0d64070640007050000800100300905489030080c454034a607a9000b40921200621048a85903908007007000c11103560031940000c281c040003441145400c3c14a00d804d07501003444241428540788034292141c0040c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 98832257 1250 98831007 98831009
    0x30308010605090906041e020c01060f05100203030c0c0709140901061a0409091407031208100b0405091302031b041803081f080601061e020609190503090307030311100501 75
    0x13030450f50941d1210018440500f0100045030340100041061618084052004d070804200c1d02c0b0001c1030035440c0c5071011b0f603808100d410090040450030f000e01d041c16000000c80b82c001c800c500c4425500c1c00140d10a42c24004283c00064280c0c0c144a286030080700d6039950f050241b0000f80081000a9441110001c542404ea0f01e603202e181040c4420044501558000301e0b06602526034180080c4200034018107081190300101d41502283e51b8400f0825444020207034032a840300c001218040c10542403500d00d01840c89518415000344d4002250790300320201034003103185c0c040c00b1a42c1c00e0f140303071005146000d08102c04c903024516145101c03c000c22088951000c0301d4050300e03404600d880700001c404143c2d03200005d44201018884001a00b15002c02095000700140d646454540c0342c0d44080800c440c0303c0c1c41550301158401380c01e0000042000c550690000000c6600070030080c1305103003040c1980109602c0503450700904070f0003c00e00da0010014400b5140d10010b4800c4120a1149201100c4003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 98833507 1250 98832257 98832259
    0x70c170c010219030201110403060903080702010515041a031605030c0a05130c0c0c03030e01140304110f030a050304080606040e0712170d09050d1206050105030a050a060b0f0403030801060509 84
    0x4020450f920548140c0e025605190081c030011800c1c03080504d50354403580c4940c2c01261780c140e440080c1810316601181294210050748000d000c1030503c09200c40b07060140005aa202e90380d111040620040d44e42c0b01c042c00980054144c070750880320f030200c80c10484402c0c443d4501078040e4000164440c03070b11500003001d44200400c410807c4c2480d00040f4000d241000c28201030000c4185a035000c41d1044c14450021440b81d6100702c0780012803800104126400b0841058440041c814000080c01c5640c01598120056607081408000400000c2c0ba01d40c000002a00c02c0c00002800310f0304140c00318940d80728807000c2e101889040411840c0780d42d81c0c0e442e44203011223540000100c0000452149214030a9860b050920342413a070071000d901c0c12602c1a0383e00f1902c1e41d10401240c0d5085801c550641c0d10922400c40030001e40740782000281031440020245c008240d60303640000c0320742c50030354000b501600c503103040d4030b40362441c0d01000003140c0d0003130206501041301080000b0b01548280d04582c80010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 98834757 1250 98833507 98833513
    0x1060503210d09020d0807051009020303070b0901020d15031103030c0d05070f0c060512161209080c01050903041805060d0609060e0102030c04090b0603060105070b1506070c170c0102 80
    0x203114084086421090b400c0040984650603880542d40380d164070b03c400e07030060001a9846031107181062421012500301100542807800d9080583c1d004400e403100290407010021943e540c100581c3d00a114200680110520b080003184205140e80541e60689100f00400c400d10b8140404040e0341c0d0003460280c0c105580050194195603115101420070305208200e2000d0000e02c0b0345e5909040402900060005040401c4141c811807600003d50740052446841105041800d00300405446903440008030480d141c0100804101501045940301030300000200064200b00c0342c020745940c01403061a030744010342400d4103404001441114011103009180003462000395640e0409081004003d450040d680c0208075540002030000758801c404030300306142e403070b810100300d04112546403d40030701801c028410400c035039070060111005aa0029203664695465070311a80d0200c5c0c1d4158510340205c40800c04804001e403042c1120213442034010000080d5000301c44413036945004803207160050b8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 98836007 1250 98834757 98834803
    0x10060e0306061c1113050603010f060303020304090c050705030c15240f03010e0d080907060302160308061504030b071e020d05211602160311060f090d060b0301060503 73
    0x1c902d0684845210f208600281c15880039400243c800c180d05d482c0e0184060b100c00400c40c45180a10824030f0008800d40100101801c0d0b2314025030700d02890203004560395031a00d004850031700540540d580c1c0c981c40005c4030395400e10012034585816480002c1401d080000001c00e41105482d040c0124081a000100c9143d20883c801c112161080034003041c0c1655868410f40c44500d401e0103030301600003054607600480d00304005aa440c1980a0b4001c808051041c40044424041c0390400a1066014941008241c030b600c40000c101c81c4021340c0083d90b600300004c00001f04007031985100d1061030039481d5500d21908000c88004c48900114000c00103800981d41e07200c886002d100903128209008000180050107503e041ea0340c07a074265200c4a990600e4001001115810000d92010101005112400624540e500c1c1001d441d207018091040602181c0120541040e000360b6440280040c5526100e41c03690a2800007060b000303c1c0030380a5400c0801c041900e060008820704003200052000e0210 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 98837257 1250 98836007 98836039
    0x1110d050703051b010501030c120b060607020a051008040209061002030702011404080106030c1a0a0c14120301090902191208090301090f080c01050906010f050103050702070e10060e030606 83
    0xd0381c4038120860510000b0b005400800030a000c0d001120580c4a00004a039411030902a1a8491541c08440246a200c5c1107800185c4d4000c10250040401d0f201c6030b480791240e100280440134540c0290b904052200707407200c030940d88046d865016a0082c0c5a0988549031a018440180c1e00d03600301001590040014400651060075042d685104404a003403e0580b1850020300307441c000d50003640c00c1900c83d0340c24400a184142c1c840d440d03c0b041c0c2d008503d0003440e1280908050b6910002510103074481a10f9507800d00c1c2401000c40c04042038040c940c0d00e40e100e0112600402511009034001c2414440d0640d50359601545c000c20381b0005283ca8101c01c00315540d0040a9000c0700742c1d190503540303840a0300000f4054603400100c05100f0344549846448500c80705084980c020304482c0d00c0c4d4481303801000b81001b600c1c0042c0030780d9001c1ca00440d56684090040c0c6c038003409680003210301c048110402c010900e1710b003050030544005644600c03685011004040d40d900d01541c0c02035108d10500000c50b55 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 98838507 1250 98837257 98837267
    0x3180309120309050910080f0a02101b05060c0705010b180a090602120408030711120405040f02130906080709020304080409051b120406050112240e0f030901080601110d 74
    0x1045100f45094000c260301e89012501201c01a16803080c00c0b182414284800b40c82070203000d4004005000038507040c46160005402110440e0f0b0f0030050140c1c4070041210110180000d41406070480210780690520400b0b010301c6a01110041e43c3d95482c106880440307103055180710001c0da03812030000b4205d4840365580b0004142a0078216880b07917082107e011a803030718480043c4218005d402c2c407610303031921235009852242c8281028040d40c00000c001c5c41507a01e008103070b40913241d0950740040e14a0555248400038410300c1d902140c40401d2100c00100c50030a40c000300143e542c0842507426065641a0300001c0c2c2c04169801001c00c07105100c140003092956004ca940039404582c180d05071071120741000d002e60701c0001c207000c18248203000c0200340320741c80c082c803030042c8208442044400c030640c40e002441c0c1c0c4401c41c61302c0040901f0303040b00c01c450183d8001e1045410300000b5100c1404459050380e55a5001c0c0075074034045004900003502c10340c000c0900001081122029210618440d0b0303040358 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 98839757 1250 98838507 98838539
    0x110d030b06070614010e090703050a080702210d0f03060806011701060e010609050a0e0105060a0807181d060907090b07081b03030a06080d0903020108061206040305030703180309 78
    0x14111205000c00c02c0400d48500600404266012801006504182004041c02d800034440036083d071220008100041c40083d210032440c0e041032020303803034a400b440012860001d40b2250f588820b8840c03a41e0b0311100020903802104441d5850780f8022a03218041078040e0344080c402e8040035004440104220b00382668805181c401d04800000c540c0c3c1c1300c1d08003a81c4042e081c0c002d0400246a00310500050401c05440030240100080c242c42035894080041c80e28072840b140202001101004200c1003805200301800c2c4500840000d0b501d240c5546410601c280008196078690b42c105002c0b032040d061150640d80980c907140d540004071402c0080501c5540d100c1d070400c0368210010002c22440c8440e00d0543c441804071030340515540c0c03c0034031441c0c0681c1c00c181c20500036500496400800c450b00107002c00200c990a0070b12880c0d03547c0300c40008000c0b4181e540c80f48018050502000308255006004510441050318104103040b400d064003242103203074a100401140d00c94a0500c082c0030140c000314 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 98841007 1250 98839757 98839759
    0xe0a0b10030804180605030102030c03010605160210020a02040501050f012c04060311031c1e02030f03040b10060f021e0f07090606030f15050d0302100c080610110d030b 74
    0x201550340c1e6840201c2644642e102c64201c0c4c15003c14450005442c0c0200c01c003c0130110b0081d0b0031f608001100301c40a00c010310880301440340004001030000602e20305015038a80083c0080c04080200030081d40b101e1141504030b00c41e514010001c1114038045403815201c030410b035035619003007001440b07620103c0070003050b19608245001785825550349a01400001d944070300c4007002030800e0f400600d440c024048030b001c0080396144c1120f40b051907101d4049005c0751500c14420007809600c4200303074214030480303c1d550030801000041005019000c40c1705401501406c1d01410342da80e603050116000645620020b005802c05081651841c1d040103120b030100c1440c10a0303c46804441400d140ba021181c1c0c4080400c5450713900c04c205040e014400d00b1095a0112010b1156901c0c0c6c000c420800f9802e8050144204000d16140c000d05100700042262002400b20820001c5008034001e40b551700700316461449400c003e030780111709920800714480c0b0400b40c0c100802000049101c16805446103541032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 98842257 1250 98841007 98841031
    0xf0207030605041a070302030f0a0209010504050d0b041106030403021005100806070921110d17030c13120302061b0906040f090f0207080301030f020103020f030a05060111010e0a0b 79
    0x2002068240c032840307000c0c0b4400c0994134184082c88940d44e458443c01007004013071610620402003000c181d43c201692002c07080340c0040ea00d0260100603510b80c05141c104980202c3c90a41c0d04080186c1c1e00c04d410301641c09180c1078050a01d07980100b2619100031039000b401a04102c2c2580061030090300709580000c51494844c010315107642c4190316250040301c41c0c0000501c000020040703040900805000084a02d0f00c2402215030390711495501c2050070b280034001c05c110310040040c0002401d0812001c0b0400d54815038a040040d841d012903080351000f0b1817104911080000e40010f0240d010440d503501d9009451103540300c3c2404e407692048401e088048038010000143c06907103000c0107001800340101c05c82c240b036007401c00c2d95040b83c60b09001c01151510401c2820b02089400c800c1d6411654889094403503600b8910048010b40a2a031300e03c01e440b200841030005405081c0c00291144a080e43e58428881c260410b05c0d00340c4104945c0d104450304121003c4000c0f8541d04455680318048001d2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 98843507 1250 98842257 98842259
    0x6010b1e16030806040f06080c28060906020d0206060d08031005090a090b0603030406021c031104060903110409080a140702120703020910080304060507021306030c06030609020f04060f0207 83
    0xd90759601880721030440004101e2030030070015150601c940001d0200c082c2040010600f01043c05640d1601c031603c03e84070f560a404c8039500c0d04080c11103003117200000e80d0700203510b940d145009071030b111a502402015000d04da0324484100c0c40041d1076481441c00905104035192107454014403580054240911071140030000300715901d6101c4072078060b19820000207042c0c4020305000d44c00d042c5c0504400d200341c0080004206561b0b00007807000399408032100000140c100c0c00419001001014410311000b10f000c07800040c02500450900e040382c0c080c00b8080c840c020200d08010403a01562401040c0f48424030500c11010710131145502d800c12540c7d0258908034241d00001c0d0400250400d200c60740d84244810320071400d0140c2041d801c420341a14018001d410900500d03264002d034001d00b401c002c4081001000c0d59500040000082d003a01002c00482d42c6a0810200307648950041802084c10300d0400540d4440c64400c40301c910440c0c1d02c0850034107060080848000f07922441007001c601c10020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 98844757 1250 98843507 98843527
    0x150e1b0409050a140c01080c07082b0603060b010e030a0305030907050a030b011706040b0a090201170a05150105040819060b091008190f110103021b060402030f06010b1e 74
    0x2a00c14060041d207007042c4c3c98a5114009280144c5071000504108292040c000540c0000c01034031070340f651003c0c4e41d503115a9a0803a0b0350904420a016808500d10b543c1c00c41407001895002c5400d813409201d082c0030b4401040015150700e00d918028540503401040e0401c0442e104501554000c0c0003501501c59076617035a800034080c40610340099a0300c1c01e05600403c03119541c10310000c00e410b40c07440034264915154482d5400c060004080c10421615000100c045a210349144040c4000d01481102c190030710301d8541e40182000c545424601c000c2c0c0c1c5014a09602610540d01100c007280010701c4820a00f010124040031400c0c821102e4a80303c0c020094996280d6203a14030403640726079452185860f04200c585018603140ba141c69004080019001003405d00c0740b200324558207c030008030480c42c1900120000d104809511b800398614132565042102d012690310f011310b000301c1c221003a40c1c0c80440001e072140c00c28032403400c2c4a03134104580b01d1a0078004640100c181c02550303810341041e80e108 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 98846007 1250 98844757 98844763
    0x201030509010e070801060513050c07080309100f0c0f0e130f020c03040803250b061e031b09060306090c010c0305040b04090203071b0206090409020609041404150e1b040905 76
    0x1402071760450f51110300c180000e00780001d074203110340c045038000e103c0d504007480301c4a02c80c41640f070003070040d030030000001d0040542000808030045021204014403d2040502801001c211b03c500c40040e1801101a80d028416011484009001046d0004007042c1803602d400401c8841c0a20019079024003035a40c04180a001510003008000c001d595900d169402042020166001c00e100060504a40c040411a0200c940c1e0f8000740c00d662505036181c40400c401014049001002e074144101c0c500d0f40e050510200c4800e00040040d6501160b6403280c07400c03d030316410f04903500300d900c0e401b414200030107604c916540b8411a009040c0186059181c0f100700456034019006110740a0300082800101c0380d00100d03148144e03102c6040e80d591014680c2c0002c01d03500c40c4601c001d105503210002c800555079150b00307c03503034020010010405602030094402214030100c07400c1d10005901c01c0380d40495221401000d10003456000580204850f1000c50540b046c0e0b202c007420b800550b0b0701c8070300000030700030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 98847257 1250 98846007 98846009
    0x120c170304081209010516080c090a0906050a05150a0e0613090c081303022a1f030c090305060105061c2a020c060f090303070f1103010b040c0c0201030509010e07 71
    0x28000080da5001c9510b5101c0f582c44024107075807800d81c1b60208119400c0c039a144090300f05404e074600300c4466100c0d0510344031540142c000075a40005000d01c00119030303005601840c1100e00540d0910071640d0b85804002c10f13050203006a00400e90200584642548501c40401000d000100120704100071601112034050b001d0700b002c07074016920700caa100d580b5080f00029510200c0d004112030300e500255802919445070b6022072190315040c210720b04203a581020140300400001e0128402d900e00c10b803d07900044222503031a00820729140c854844c8a114540315400d60f074201c1d0051017649d2a000034420f03240d104c06420023422044495080c130821300d5008051101900c080032001480d0140c8501c4a6900040340e404259070001104402d1515220151400100b09100c1c81d85c50700c618402003801d601c11804001e0440c402000c52404000002c218100110000d40007001600c40c400244030844002502920114018000c07030801503210703400c51540004907600120324125091003451070b0a80c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 98848507 1250 98847257 98847263
    0x1090501050f2b0e010506060301031a0603010e010c091509030f1101031e1e1509050402150703020706140f03010302090402040f1503031112041a0408160905090604120c170304 77
    0x310313400520041800d0150a4000c00b044a1061031540340d543c1d4810080c100300c00203003504240c880050113542d429803000078201c4c2c00034001e000c016054040141054050f002e0100d000c00c5e0b0074514071540344142d840d40c007038176803241038805101c1e5140c40d405802094900c6142c101912460b4954010500c50001c2c41c1c0042c560401207600c9580140f007000e200000340aa00ca83d0b0f18201e0b079070b0030003100680403800700d801002c40080ca82d00c0e90700110b40e4600030240c640c000c10900260450426034005107100c12680c095035400038407555820080324a10460306010341480050005001500c0c0007884150018802000080e00303e2850039818269040400704419800660100b0401c2c140c005e111090040c800c0005030022992a81030280a80a180950f03004419412a0110a503a26604440140c41540c0403610500b0f10f40301052061050380c050707420b50f42d04090101c1c54903040051200d0180b07034001d030080d244280c15441116041c030310003420b80b511b502a003441c2c0e1050b8003c0b002940130b640 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 98849757 1250 98848507 98848511
    0xb060706060305011407050306040908090a0f05090a1109060a0c0c060302090f0604080a0f032715020c0906010305132301060509010b0304031808010203190b01090501050f2b 76
    0x302d9810090308550301da034400700086500c0810092825800800caa50114003160001980702660130060700c0b900850764590381007041e0910105100030308015802c1200c20880b120709240e0345490345641031740d084954130100c524041c00b00051920f071620251010f0300305880c00340c00910711a121959850415804000400d43c0000c100700b89092a0051952103881039402500d480d160021032640c80303181d010041c00c040300d4150b040040510800c025400700d40100807140710070703800500384c4044850921680500e690760b500304040c0b260002c076000000c141c00030711000c62a902d0000540103410014035040701d5680000e80e0030005250585048201d103140c2d84046424001d490710a4210749441c0c200318410031007600100585041c2c0c0341240c2d8819030600d0490076201e03100703404506244445e00a41c2d4a54008400c01140d03401c5c00300024420031402c40d06100e41e045080041d94a0000c034099180022410030000c05124a20f800504807040b00911b11000000b007000808034248040314500c0070a5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 98851007 1250 98849757 98849759
    0x30c1b0303050906130f020f0f0306150a0909260904020409020d0f060b03010317070c15080a020c190c0e040f0b0c04060c020f1807090810180f05010b06070606 70
    0x5070b4104841176100c1200002242440d0850711480041c0301d408500a20552600d10804510f840b080300d144044c1c8000380c211440c500701140c10580140303101850038000e80b8401c100244018580c05590903817a00560318064202d0754078a840041c42030300f8031a185c1e07140c00304410101c5813502c0c8000c00003095131a40058850b00e003040d8541c107407041e404620720300c41e0400c41c0c2449000c1c1c1e500101c0341141d80c441d40388003040d000004050707058016510040c0c4041c14400c4009685107402c11104050102d654070a601c5030b9818a0072022030003261050500c030350010b00b9102e2607904c0c0c0500c084a180c0104d0b070000d1465900e24120818060846040310301e0307040b8500b003008104881c0501a049240c961425040604107000180460a04e103030185c404ca11908034a0b0301e03074580881c10b45290200e072003001114070b03111a01800044603403160902e00d01c503103400c500c2081d0141c071400e01c0c0c1c1100640740c480c1c10700c1c0c07135103d07420012000c403425200c07550380301c4091810fa51803100070300704248511000f198503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 98852257 1250 98851007 98851021
    0x110a03051c080117060705070c050a0e01090b0a080d0f02070b03151306080c0906040207210f1713080c1b1002060f010b0f040506030f0411030307080703030c1b030305 73
    0x2c0e11041c2e0189103400010840d00c0100b000103d6059403045c95407601c1501d40882d421b0801e40000180d010300e4101c8028040810000c01c0486031a041c1d903040142405422489018011016036500c503284035508504155420180f00e075481789001c542520459011986440c21000c081d4000e981e09251012031400700b5180e4105a80340c00032404103118100411450503145036211402401514450707012600042c910341d139250706450400e40c010003410154100800c0821008500060781004601445890750719640704400541c05002d002c5000b11480e141c00016004032040714000311110501802400080034ac00c00041b00c60301003141d000300c92214520f092121140c0752580503011500400d04002d60000107041035411140805041d50344d074840da2440010502441d00714550010000043c0414031380000c2c01c003400ba84c050908404031503814410107917030f4404d541d40148103100134404034010900a03448000c15a095003070400000700c80b0600400c0c0e40001c41000c130046540c031741c01d224038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 98853507 1250 98852257 98852267
    0x303030b0120060114120c0108220302150a020403080f0a02070e0702070609090605060315010201110d0b09130308130318060305040c1401050d110706021303060b04050c07110a03051c 80
    0x40e034001e54551041e08102e0348074581f83c8a0024405040c07045c03240205070030401c802d030365031804a911141050207030380600e0001d407124012902140c107540014040360141c44240300701c804a03680507510340c1c5088220071842c0c9498000d5030052066008040d0700040420103112590300c9000700d03602a142c2a41044400f41c1310809640200300224074040050009480303c00403a60801040b9522000710118603004074007500700600d80700045040405e5000c4500c030070317070040c085886081b10419056613441d809050320034115007001d00004c01d52008190906d5880c086080000c1c020310f0502e095402c1401103400074150b80d40b002e070000b56210100414005004040005003c1c400d071014500755590300001c10a00441507491400c03a9070f048a0a90200740754110f9100ca94007500564540f400460314800040301d5100550f002420245c42060615092245500c42e034110710800d81080c45544400e80c088503542240b54100c0038854010002c02c0c13040000078100300c05403e022120007090100108 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 98854757 1250 98853507 98853539
    0x60801091103061005071b17150402030604140109060614031b0604091104170a1403041d070507060f0204080c0117040b0c04030f05070f0b12010303030b01200601 71
    0xc0030a06200b884402c4d0f866440807084207455203802500c3d000c0d2030078003041c0418481c58948191114040004007142e924404030001c4040c08255018191042c1d0081300110701194020340c5904000001000602d5603c00401c00d261540d00000e01c1844070f0751918102d580319002500480c0b02030f13486070f0051808124072034040300101e2510544a00c4100844c2c03140c040d500031052500d40303032401d80c04001c000505540040242c108580e0074010003900d0a84c6480742e0301401e0701c0d280b0b0450811a60850000212811100100441c00c80305d24880012107450394040c3c005810441e082192134085004d0340142031001c10504401a40c86142a01c6103141100030120789042c0190081d0041510594040d0711b544281c0000058050baa20322002407414821030f0001826100c003048024203001001030500103030ba1042084d0804070382c072840d031121a4040c448000d4002005000140002032090300301000c40c00040c10492580210424000c0d465400381480d10304550051004118a0043d941144 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 98856007 1250 98854757 98854781
    0xf060510170319050d230103061d03030a020a0909140f0a0b01050702040b0109080d12050c04080a030c02151804110f03010603051012060519110a030906020405030706080109 76
    0x9460328200c640d2040340e0403d0ba804100611501142041c8a1403054000c10b00385c1d0140c3d170394003c4500c801d86c00450f200c4028001500c41a10302241c03494401d030040c0a102c00018050004c0d0305650341e039101d0001943c0000041d0081082009000940318010300444c0108036011010000f0307494146d07540000000300911034404181024840c29160360808101d0389400c0d01590085043d035200c0e40161011121540001c1a500c1420040001d807030380300c0c895030507180324100140314a4540141c03d40440c090340c0a40031003a08206d0306100041d00660b80103240c0c500c050444146c40b03401d01c40820941e00645840c2c0c2002c0080350102c501e52600b07101d205950200005c45a05040c00000e0304200750005000340c0c03050540c1c0380041030182108052001c01001e4840c0400c5105c03070207140c2140908000e0320701c1814801e88880d60401024a800741d03022441240a01070700742400e090080700a031200f86000d44030144d0800021a0701e071028401e5101800303468480c20a5940341030104002c8602ca01444 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 98857257 1250 98856007 98856013
    0x41407050a1e0e09390f03070e010605210609060409060b040e0304050310020307050301030f060207080a03061d0103170912010c0206060907030b060f0306010e0d0b100515090103090f06051017 84
    0x14002c900910f143d2440285060795620302c201d441101280c940540c94010300d2754500c140c030000400c26840801455034400e6078031039600d1003089046514070ba00041d50070310740c40a02d610001c0d02c0b0782800d03031190400d035004480210b0400f0002010404440c04442c0c1019181c1000a0a011b94101084803000c07242c0c408a04518601c1e001900402c94003060100400b82c01410181300b0070f0000d20340688100c1a0000718580d501c003411074015000380418070603215100300d803100520b982d210380c00303806049a80142c00d5400d250010405181a580102a4103900c8074000404400000e001d10440c1541c500c10f400400d201d081c29001c0141000f0010120070070541407007508000c684895055410030b15590241c252070b61a0a0010f88801c0b13180b100558019030328071611011300c56480c214074004c8204021442d241512101131141625024650714402c0c4010059070300b49501c240d0142185038020315803581ea00489644420a55034251490620400301d5941404215064003940700070180315401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 98858507 1250 98857257 98857333
    0x160c080d0203090f0f0312030a020712030c020c1009080f030c010506030d090b03060402090d06050f0a090c05090c040302060a09090f02040e060d020f030d08041407050a1e0e09 77
    0x4c1c001e04201d9070301c00c1c000c00d8080640d21180d1820410b21140000003c0340c60344a02c5c1200c1894000c0d00001030695050b44184a9a526540203218a04600255901412034000f448040c41504103142c1c0403102080005400041c1184090018082e00c0c0c001c2c9002c3d40e640d007000d601c83c1d07080d202e01401c031910940002008000e015044001c40f012203c2400990740c903130b61014000b40003800b880c3d10040d04801c118010000300151540000e1054044800c0f8024680b56120000c0031603003403110052070003c51003c02c2c0081d1a0502e586d541c007400d07141c9041c0c034194880d40401d602c0c6e00502c8440003c240b02400c00d102e103500301d00503480141c404c2c60045003045e2620203c005042e07000340c51540a10015200032066486090000e01c1c020703000380071905001c01880303009220b49400c4500351b07800c0e0340d0b03d00c034181450300114a8104031380303005145405050a000c4540000b42c210740b20a2418520751200044204030942030500c611144006029607a000d4a4076158080100c0240c0e0146000c0c009 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 98859757 1250 98858507 98858509
    0x5091504140a14070906051011070e090d080a181412070803070e06130b1303051f06050a050d1e02040c0c050609011103070c0201030b0604081e0105090a06050c160c080d020309 77
    0x140f0360b8030f08c1600d0085119200416680e04041c051b42000080489032030800c025000002a920051061070f954410305542e04195a4110380001205030202c68800b0300b4040452221482c00c1c1c000d250040c01e80701c00d0718141085024541c0301c180100c561400110401080540180c41200522002d07500c2624000c0e00d12215074901515009126100300301003005640c600c0c0303500302c00010750f034007204440da202c03400c0c1c136400b24007462040001c1c40103050004c0401c4608200340c0c04401c95001030441e255840c440da0b104903003540c461080b00000034202d00094056075450040d04640007058450040016607400e00c0e90600800a00b01e0b00543c0c1810420741580b002402104c2c1d00094030315180010758083d1004901900d00c49803090f50040c00411701041e201400314440800318810402920000e1888400e64240e60046503401d006400c24a40d01c00400c10a4008640c45a10740d00503601c0e1402c8104035002412030000300b40c4489002a005100792101040f0b4000300303003100c2c0001d41c1001c210b40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 98861007 1250 98859757 98859769
    0xa090e1003050d2a240e010f200903030d0f140f091c050d06090e01050601110a080319020304030206070212071e030c0503031501020705010305091504140a1407090605 73
    0x868404996900c03480880a0000e62a60f1020080c4007884002c0c0581900036205c020b4201c11600715041d5290034180c00400c0800d00c40d40200401d10080617a02d03110501c180d08640c0c01003000d05805020801694078110100e102d44203421054910004600781010f40043c10364100908902c0b400042e0406c4c0407a642001400362480c03a0f080340486c00c0d90801c0c0c80201c0382070241748100300c0700381d041500c04181c400c1d040e0040e000c0b550190008000c01d0f40e510004607120a03543d04620501d07000000e0050206031000000c541c0045040640e05007800c501c00303c007007264000c0758240c0058201d542403044141c0d05003d5006200041c61200f81800b8554650840c26000030000d40e280f6904241c0c043c04260041c0c50f5031645980200030f5a880307113481480306142c044c01103611801409030175404500c640c024480c044c001c581441c02400032404440e100306965102500035141e4209090310800c007410104560348006208800100580c4039000d1482d203007001e160450350615081804c24015605ea01c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 98862257 1250 98861007 98861057
    0xf010f0225050304051314070c020a03060c03060b040e160e03030a03091703070f090b1216020c04020d0606090509040b2e120b070908070b0a090e1003050d 68
    0x30071114441d200991800a01e18499948040d800038600c044030f03e0300f4040355011894141200c0c01502c1d085d51018400c50f101a16854020340c0a0250301007480855001d9220b07041091031401c002969580740d0f0780f01030507600683d001d00b01e83c0403080c0130401040c582c0311500001c00401e00300f0342840004040000d440340985a0280b04060703480743c101c030500030315000380400511540e040c40d54038100001d00510030b10035000c0c85c502240d01f507580020303a03000e00d070102d90440c4800c18000e15162150758000310b040d0100c2412108500c140b50703101e00c240d80c0d180b0040c41c03410702c000750000d00c403460820050509c503015881544500e00ac0320402001c04d01c8968280da100d410104e010310f80c48501c0c0040c1c40004400b028410381c04401e420081005e030360f8000207548aa0242031003070b00d980e0714907200b1142800d041c042c00c00701c2c3e0400d000400c42c6080ba180504000306150900e00e40303940e207074884d0078002d20b02140d0b008800203006604009001061142200e240c40d0303071038014000c00b11015040b0550540c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 98863507 1250 98862257 98862307
    0x3070b16020406090e0706050702010f03090f0c0609050f010e0d0803180f060609180a020112020c010203090604170a0e090c04030203030d0504050f07080c0d061104080f010f02 77
    0x400548030241aa0103034250911960082003000180d413a0740d0f02900401104012101c1c502c284100422000c1c050f42c199540150705035280c01d1081ea09500c110050100c040040358254841c05103170001441000035800907052582c1e6100246140c9004c001e50969201031182c103114038062429020748501c2213603200e41d41c0082480352340c2e07280c1240c10141c211954240b00c00601540c03800e40000c2030042141801a10b0403541560151a849110300c0c540e221484541415400030b640d90006500030b0840c01c00d103103040100141052502e6100d02c3c01ea90040703d01c03c15680000342007000700007110341b02c2203003641c4e80f0034080c0c00e0800381c480140040c0401401103100e140007000090004c2d0701041120302031a400707420b03291906491000c02c4d0113410700b0341d4105d641c1c0c05816000d40c480040024840210f0381000004e00704203031291305000d2403001540c000c0da0103a031200c2c0503014000c40700000340300811a05000700300320b4420031140c03400c513541c0701e451a20301c6004121344440c9900c010340401c20211 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 98864757 1250 98863507 98863529
    0x40608010b0306010504050a0f051302090d0605060301020f0c06010e090d021f06120803070806031b04090503040302090c2205060703030b030a0b07030b0405010e01050303070803040501060803070819030b0307 91
    0x3c1c1c0c800144d41e980119880107500942d8034a001c1204442c4100700c7c0100d9209845034248550080110230503405100c0584e90450b078641681c10102e82c00c0d40046030013020190006180250500310b0302825440f40440c034081d43e001c0d0004010040d00385980c20b51082c2903d0251090034407003c002511241d4038044000007424000851f05c0c0043c0315400540204112207251005000502d40707015140c10071a642e001207030718240003410901700401d020601d503074503a0314502c80742c90002c208001824001400e9038648000d05c0701200580355010124058030000d4081d644a400303801d887d540c81c01180b44042d01d40c41018204100e40d459110580e4185580350501240002901c0042807411503c03a03400790568024005212465406502c41c500510003920140044ea88032840385100000270720a0a4050780308014041c0424021005103070070500c41c20000c110696908502803554224050680b6500d0300010495075018002c0a00c14141003542820310610700e5220000761076526501c0b440c80215 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 98866007 1250 98864757 98864761
    0x20904030e0d03091e05090712090804030302010902030607020c090103023705010e090114210f010f0c08040c0303030507030b04110a0905150f070204110c010c0e0105040608010b03 79
    0x502076980e56029480103412000d4001c1241002006580c2510904800081c05c43c1c10700000d60603600a80c0c2501d4015000c450943c0f80c1500480c0c0c90384041d14004440c5644003041d04c0002c030180001d000a602960001c6051100c0740105410003102410020940d80300c00440402c90300d0749400f6604583c2c044a464181e16000f44c00c6050040ca040c03104410307105400119400b030a0b1015511003512000c1c1c0c1c0f49039030001d2010910200280a0013080c200e002c2c00d0548820f24508407099010540740341d09801c202007008071000c0e10b411210300c80c070061f07079451f540c0d049650300d800d221309600c1c0b01c030b1850041e201741005d84618251410600000e410180c40d0400100040d0003900311032808a40070304200700c0010105801e64140d0840800c40c8001404098006154a1b04802e40307110702c460358608038039001605080c004944e000f0354040360090303100c0c0b0b00d82c5141c10901000d001c1c54001c4c5400400c0d540344510700189601e2601c410309050040a0200740103159200c020181074030012684180d4035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 98867257 1250 98866007 98866013
    0xc0c150c0807200114160201140f0d0f020703120914070b040312050306030d0c020103061a09090f0106020c0607020d1b06140403020612060f3c0a03020904 68
    0x844140ea4041c040000018034081044801800d0210721598203960841c40b0400c400110780101e040b04803800071500074400b12010790403042c6003500c2c0900c141000410b44690030980403064004c541c001d610300707501048001016405021784888540390308421443c2c0308580d580a44001d990900442246590784000c400300050f80500300880940c2c2c04c215044a40c5d0741d5400f5145500c1030000f01d403507441c005400480c45000b80141c902031078008010740b10040c0300e0300d0103c4840d03d1000d003d81c10903132504800544003500c2e00c002c0c60301a40d400710385550f070b81349032043c8562190090300a420354130411004108499000c00d0800444a0880300c0a03a290503600010307540d01d91121010b0181500c06140501003507100c203c44c400c0314050f4450030b03040a0b4121401c80140940e10010750418410026601c07522070a4602d1a4490f00c0105010340550000010483c1c04014480d41c22803540014503221100400d45090301814031801101c9540c01154000b08840390b48a00c4002d01503a0300c58041410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 98868507 1250 98867257 98867267
    0x3120f0a11010f0e011103070f11070e1003120e01080109020d06090e010b01020d0306060801090f200405030c04060f030b040c08030703050d0501050108040f080306150c03040e070c0c15 81
    0x141c180c400003403082805251050f802400b9990344002e541d0310380114000e4940c007075800d41307100e58440d48a00c907001c16a4138060300e448005405000b5140140341c00850301c9100008000c0c0940500c0c140c513141c0c0e60541c130700815500d202c180600c1c01d00054000705406a03074071100041c152480703a0005a11151500e04400281a140c0c0094040c40d00b4103c1c031b8030a4210550180c40c40130001d0b401c482c1015152181036003141c50b42d0051000140460005000700350305034000c1b0303a0306460300e42c0c0064480118100070709c070038240c07021704503540380000340402c110b2404220750340d01d8190481c0e00300f01e42d91400e0000c0442501901c401002c0c03144507070015090100f0003125000810004068070394804282c5001016580414005da080910301000843c2d103520406c07806100760352040c0041001e2105442d509003d820050686034440300703205155001c41d0140c005031803020340c0c400007036031120f0410749694a01d44006040804025001c0e05080220b1048103160080b01c420900c82d6410b030400074800ca0f4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 98869757 1250 98868507 98868527
    0x1104050f15030f0a05010c08131509030507021f110f061603090209040303060305010f1802011805150c01052505030601090506030c07030305090303091e2d0c03120f0a 73
    0x3c554004c0060850600c1019003109480c0c500b05c1c0e8909503183c1c1c520440345101900f001c00a070580c42810060803005009511500f800c0c0d0003070a10a0071329803160700280e240c2c1162415218250030842c40c090941340c0044404074040f8401014101d00b001a520749130ba13503000181940d1008400f00488ca190324001c1e4481010980c0103030a0308128581402d019020700f040d440229065840c040451521440c5449000e0248100c403101120020702500110b69240c40071a600040c40203502000403195103001d03c089501c40030700032564503014064201e0382150002000c008414020740003031100030802c40aa04010768140c2040c580700d484140048542a07026000f15800c41c07400014008081ca4040140400c10b209640501c42583c034400c2560700c034001a44d050b000c1d03501500c524440c05481c9003145411486440880300402c1000318041079207008161850f410401c18114202c1c080d43c1444400c1048900760000c16a1000d04c40d203042d014410300310808150580842c03000045441001010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 98871007 1250 98869757 98869783
    0x3040609060b010e100c0812010b0318061b1c1d070806130206030a060e250e01050f0705030c011802120a2616080a0306050118060c0317070c1104050f1503 68
    0x2921541c1c4900340b2b556a64801e0f104c0c44a2082aa80b1044c841d4100180071449070348c0100b696840d5203024410300ba1143c0203c000e107000c014080362510020035443c444c00b40d480481c0c1e01c1c0b002c118940c040c1004c3c18001075800c8041942c00c0002000102c0540090310400d542d410b0310400d54941e60452210000c042c0c039084004030b07c1c95142400f03610041c410b1000346400021a10905090503000f050b45c9050513205c0c2140495000d201d01e0b0915035205000e04400b501a038103807403400c18660051421200441d00c02c45074400b20608200a5040048c0455a91912440103000641058031041304c2210100d500c81007291030740ca000ca003858208000d4842c0e031200100e100400c00603600d840300c9250042c1d81d011000038070340f000010303466110321821481c2241080c1c180a125041c50f4040700c0351582c000c029000c1c880b1800800c0504011040302e80d00c1602c1d00e40c0c0d036507032040091900c2d1200f04d207142000c5100300d0800d030034010000c28450243c1e401c151210b020320141c400220109003400e078510b00381 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 98872257 1250 98871007 98871037
    0x601020a0f03080a1b0e01030b0402070807082107020a0b060f030f0d0e01030903050906072901030201020601061103191b060e0d0908070306020906040b03040609060b010e100c08 78
    0x1800c06412161040c002d0801c11300502480308042c030041d141241c04440c5400041c4204070a85072540071f40e100d02c0e29000301070805440d01040c2e8881e40780660206200b140c0c5c0240c00580b0a14500780c006202c00c018080003141c4c007181c10020b000039565012910041c06804004001c40c449541e01c04c1030541446001c1c003a00d28800701c1400441c0c4407001c4020310b80c003203003041d05040d0721503100348500e00100c2d44c142c0b18241003400d540107215082d0800b680c12030f5454000c0c034a88400c1c100d040e0f1500c00390380b0b40f10100c0c4883d42c1580300090500034103900c0079042c4208464078036a40c002c040103031030500140180d013191a1098000494082c1c4080c0040000d80e42d49a40d42c00c01c0c0300c0603821180c04071064201f122818054208111070341d040600c01c1078040d4004110a1002171030540081599960013804d10b0708040e12603d4404d480c0c4d100340c0342281e001d80c0e11005141008100e00032007203500300901706068105110000710b000304203400d04010402030350301c04940070400302e0010358848040640213 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 98873507 1250 98872257 98872283
    0x3010b0603072d080411010f02070603090602091207150305010e01050d1104020a02030901030e0607051b032803051b090f0301020d09030306080f070303021f1404030905011b12080601020a 82
    0x2004c3d1000a0948041e1400c4c0320542803001c8550164501020f0940c060340100000c0b03140c480200c00034011038204075041a020481c4c10701035500d00c3e0700c0903e18100d000140989501d80520050490f100100c1d0405150038080100600140d030b40703880741114030175241c1542c940702a14108140400c2502416486440031402d58501e03a4000702034a1000000e0300c0400c0741e4204039045940c0d8042c2207482c24009101008000d4a81528204001d0f210b000b0340c0c1200e05120481130807054503001c000c01700680585071028188100d0b071500480760451002d0700070104149512065006502c140100703a405966100c04152590300e003541110419441c00301c0800840030700c4d2400070050101d501c070f00c003403900c0341c0403190041c96000700c0c01404495058008000d6880702801c1c5d45404803138200040c0001c2d03a10700c0810301c0d076181c19807a54400d9100395112182503040000141c4812041c43d40420400e10030103000c0002142d00444845403407050030105007a6407441c1c0100d03d05810904010981c0a0000f2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 98874757 1250 98873507 98873597
    0x90b060301150e15042306220b0703031e051302090910020409021201060521100306050f160905060904090c050d08070b06040b090601110111131403010b060307 70
    0x1c0d00550350303c1ca40241261801c1d150201c1b20920611b452a4000020040a524049440d40c11720882e031000344e030103000a580e4501c1d1000c58001140035000300e501c43c0b062001b1041d545a0720b85030609001420449401c02d2000d00b0030000381e041c4003d008400d41c0e00410b040d08010081281c000c13440d554155640c0d502c0c0c0366090040d40120081c2014603800200104165001d40d0a892410751402c04944084e1141606429258005401000e00b171000d004d010020903214000d00b413003036050094190320350914100048903501c461303d46504209100c00144110b964507000c5030404501101c02003140701d49030400c01000c11466001076440110003a41d0000c0280d20800351102902949840c0000d0383d03030f80140000d94503804059540030000c84c000031010b6000d034401252410b81e0f64000280003800035115440f80d030010803d4214011030745010800e08809921004035050280c0081c000c2e0000e603c04220703540006040355080c081d91080300b1244c074042c0143c801c203065102140e03a5500304019 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 98876007 1250 98874757 98874799
    0xf020f03072f15090f060703020f07050a0b0a0e060c0a030206040302060a140105120c03070602010e0f070e070503090307020607081c06080303011e080a03050c07090b060301150e 78
    0x780001a64840e200c0628082c03042c80c40341c0c1440940141c40310403480007460901c0400e5000044580d4000c3d50280503541da622040040d200140c404d0b00240081a00205010f02d028015401342e03100b50000740c0c05128285040d03090740c03400c400a082c5400501c000ea800076400c0d010b040b106c40f040d407003409115014580e0000315680228029020b5610030b0311120403c100341c480b00030f5619140c25a00d8010451420200d44029182101d4025604200a584002420320419612040042c0c0d100d0b09101c08185046c8262610980d0010040000d580b0301000c0783c0717003200020702e84d0007400008000200c047c141413040710b0010b076008140740c1d640c0440d40b40c12102c50f0084001d0442c10200e941001e80e080070644240f4050314008030046080d030b840d09004000c90310b40e400165001c1410b022000070a07401c200f052000355440b90715410b40b6148140440c0786007182d20340c0305034200c6050103040882602d801d405c9905480c0b1245810404c801c4440d01590102c4c07405144642200c0c0220001e25122272034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 98877257 1250 98876007 98876033
    0x31407121215031103030904110d0c081303030c020a120815031501030b06040905060c0d050c03360d030e19030203040b0903010e07180c0f0c02010f020f0307 69
    0x65100c00000403075481c160000c8807a868841010541c2c01d107400c1c07010414102502200250040840380340052203070109054441454030200034143c0868440001201402013840c0d01a4501e01000a07103864481a1031184c1c54150203401d1542e54101e0014451083c0080015541c009401001c51586808010a401400c65203580c2c0c00013841d143e0046454040b900441680550808000503425521603d15500001e07200e10380c09507990800000292052000314450600005041d4507107403888402070540350300400c9001507074010002c12140c00058661403041070f10741c140d030f05003100e450341c0d581441a50b00100802c036403040e1030315400c0742c81d41a044030030544a0b10703058800d010080c103c0074200506250340100560018401031110030003a001404414000a0000c03c5491881e03068030b04007c282c0d000f81c80d007001c55017000c244010160141c1c08490442e85055403c0c00740c0c10310010031581e90050f00a04020b510030008a40502c20042c1c0ea21610300031055a0307950300e0030b00c3e02d29800c2c601 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 98878507 1250 98877257 98877293
    0x50f0a080f10032103020d06030515011a120406090b09010b030f0304061706032b08060303030601080606030a0b0406140307090b06090d03020a0804030b01030224090409031407 77
    0x280c0300025886482c0c905400c0c08036540301800070104100c00312207005460800e102081003542c02c5c090800c42c0303200350041c00700650184c0d000e0500303c10f00700d080c0c05000ba0142c0004410405601824141d0724039032049442c00c40c03003003050750005d4440c0e180c5800a0400882d018080881402c140001c4007010352011072342c4e51044003180c015416100d0003a8030f0780a5486800e0110f000005440b580032000350415900490003410f03103400402c91a034030b030941003a542e10b00d414076401790b4a9242c09504242e43c203420080480080d4290710385040000c0203100300a01d010300640c1d0200124100640c950400000c01b480104280728041c0c44000b00709102d14115509031087c820700340d00041490365031180450348c88000c3c107040d03c2d24030580305000074030310030803001c40441c4140410b00c4041055040504051031046184103210b516500400100d06000310720440c5403500308d01c5010000810804440500c542528042441d400c2c40c1000e460f60680c0c00e401c031400c2500051510200a50503042401e000c0e4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 98879757 1250 98878507 98878531
    0xa0b1807031404050d0f02100912080709050f150d0e0c0f1c020909030706060603050703060b211503010f24080604030c061d0f01050603030708040b0a050f0a08 70
    0x6030029112034014016030f40a8400d0700001200a03440303100d2804a0040d008038011910001c003a8420b5600b04c03015800290b41c4487c1984403000090b6020100540111203860155030765801c05e07001407140304a070310010344502e20034900b0f8500b00300f050301a00c21182409078200255445081c00d43d48070751080c08030521410000700c081d035040c609100f43d8021080e0441e441d240c1e418266007403103219503001e04205418401401340e000007865034028040030305010358012425041c406405016031701c0a4001e034500c0c5c003091082010300509030482040302c40f1000c4c00c081494942c2050703074012010405281350154204030b21140031450316041010300700e00b03180c0e6052100c1c04400542d08000038500450045400190114010a200e9944599128020343e000500d69010a8025456a65070818443c280c0c0000080010043c006c0c03154591200066002c1c51400d28295a07921492041d406646181c07140440d100c51901d1142c01500c140c0c05040b80e101d5580c107010200908010030480d02c40300845 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 98881007 1250 98879757 98879771
    0x1e1209060a140a0e0a0b100501120522110402040608190209010203120601030209040c110d0302030c0913021e07121e0c03020f03030703060f080f150a0b180703 70
    0x1400b03102d691081400b9946580c01502d0b600700402c00340281c80b1589506114401e00800400c00102100c2d01640c2c221405201c2a0328110000d00041c1400c2c180d00c051500d80303801c01404c169120b041034003840482038184113851140c541807202c00e008070701d03042d0820700c04a8080781107070300404614001d0900d500c4c403100c0000e059840d5001d9110f86080b49006030000e02c102c1500740800704645801010505025003400d42c008081001c48000c034114000090051010302c841d500c0038000c4a540c103000e464150710b14075051110300c2c0c4c58030030020058080d902e10650f11450407401e074103450300d03e0042200c106061200300381940f01c0d9005500140d40c20444034002d865124064000d5079854403044100340d0400d02c0500081e40c414039001d8068040d401a00c4a010004906000031032181c5c089440000d802400c0003c00c0070880502c1c0c0107001a98131524000c2003445001031040c105115507032f070b00d03d0590340d140240005400300390b0020ba000182021400030348507180720710758800c001c1c540d0100881 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 98882257 1250 98881007 98881021
    0x6090504060302030d0807110a08091306050108070c05011506030501051302040f0501030207050a06050a020c0d02010e03030622020c0c0f030d0e060a03180f05071d010603021e120906 80
    0x30760302031200940c180e0150441d181220301601c2c2072030b072007070319030a20b83d10641a00590301d007040d01e03001e01203030750f04000141c5500d10314010800c0400c0140ba1141041010308100000c3c00c0990040c020400340010011000304000d825044000c0e0441100d1030803001c04d58441c0090040c100a0007454400c000501038180700031010300c2603c7c11160998907032030f0018a0200150000e50024034203443d14003440300e03488003140c240d00889004182d207050042e0b032100e5002015003018460080d0300c085904001a40a40074000000d403500520203d03420070810882711a19507190000c3c510002c0e8950010800d040c44180100d08a4007401d4141c2d10700803407100d14420151245980e10b1090f02055000b21a540c450620318040c000009603400e00040310310b044c120b0384894840606003122412040301c0441c04009040c03151000a010f81c000c44a0940c03107000e41d001100d407050003000c04260b804a042c02c6040c0090000c50030382400b8441ca0741d510020f060042e4503521084a440303d452090502165603 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 98883507 1250 98882257 98882261
    0x1803040e0f0708040515040f02041e050a0209010207050f01090e010e0603060c0901020a0611090303040e0907080c1c1712040303060b0a0912080403020414070813020d0f0f06020c030406090504 84
    0x10542d400b0000e46451b0070a0030303408440040280003900c0c0003002024507001601d40380300e4050b1302e5800e03091200780341001840e100d080c0c54000b81083d03001da00600c41800702c3c1e41c002481c601a41c0d8100c9600c3c40f06801c40c00100c810543d268400c036468151140002031500300c841c203042c041d000907000d0f00c0c01560352070721003242807049000c090b0042e805103510002140b001c0e4081c544031140e030400719151140e807100007071035500300b0303006401881c4030002413180d1a2401c000000081c10024041c241c3d106a0100056004803051001120084040100b00400140104403d000c50003869120707180d03500901c500d42c03003110842e0300f140481d1a000001c6021070044041e100701d143c1c10364550a0711f508100d151b2800100d200740445501a0500000c001a0b480c3e000e00c464104855080c7c600f10303d04240010525000074094443d4201100d1103000541c80780340c0905803160b00051400a103a1091401e6103002070040d60241c50300e031006c42c0074490386e58040010b1044803910b0361001d080076221030400003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 98884757 1250 98883507 98883511
    0x102030103120c0f080c0708010608010c0c14010b06030f06010e04060f050103091110020d1e0504030b0612060703050702011103010503030a0f0207031203090c29031803040e0f0708 79
    0x1402e01040241c2803442140780c011058450b150301c0c0602c03140b66941007001c0c0c0043d80140d513182c03c00d030380034024500c0911821008151410003030100142602c00901441c0d60080c003d8405041c035140125901402d400c40404624080c10b801d80d41c0c03800c4146036032551010341e4800c4c0042c030181a0411245010b0086106650030112104102890500150010102c2582c100c0361031403040b801010b81c1e510f26841c80b0209400d5005414400c2015200601c3c0c1a00e64960306001d042324888440500e5000050b6070a0b640e002d81c1d00b031074648174680010300340c0d40f058100040780e11400003000354690f416040135006180c42d8000340054004a45122000d0000b40501505640140000030800d03104125403107807189580140d0b00c103551280c44107018218603502c500c001c41d45500443c020010f090501c41c00030604410001205803402007009441460104011078014000c00841c20046040b1700c0030154092903400c580d0707030756501c07121446070040c111780302407690040a00040703403e401225030b14 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 98886007 1250 98884757 98884763
    0x6040b030a12030218040e0717030a020304090f06081b030706090501051c1806021201050d030e090907051210050c0705030412030e04020d0e100b1c1a010b040602010e0102030103 78
    0x1c40b050312140102c0080d04040e02c003842022035040030041d5500ca5202d8920352001450280c4121810324880000c120103500150720103038010000b644840e03034003105403000ea6a8122000c21070200c02e101041c0900780c150010100c9016204110352124107580617081e052000b1f4003030300d0405640d2070064070070307050b14818280490020041d01d00500c01140764159060140c1c4400501b40105801c01c003a03540b030504044500c9640040c181ca000034620b91210700510b01100c0341c0d00c1c400c406940003000303c0c0f064910710380a070b0205e50105180c80b0701801780002510000c1d2042d101c100102e00700564030794014040c0b04403a4a803801183c0e180d0140d038116955580c0120046203814a00070a120070041d000609508101001c54895000e5a850000306910b99030300f28040741111012034400d0918500700a24040e0034644000244540c03a0070340f9120b5004010300880b0902505801c0808000e04215922400044d011002048860307100020700250f522560007044a0000b501a0310300300d2100380006 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 98887257 1250 98886007 98886023
    0xb0f21011a031803070f1a0402010c08030727090b0607020105160305090301051008010b010f0f0e1906030204181a0f010309050115150201092006120108010506040b030a 74
    0x10a50407070044000e6400c41040201c0d800254030582d5500d003190844482194641c2011220704107000c01846411840d500d882c002e01064117090f40040c5c80115403a000800b2202c0220000d8030742400f880322507184d0b0288140201180c10302406400e60007050b8040ea9290505e4400340d0b101030b06218094a03502035040c0c48091a011503010b0018204448220890400c4410415540030303031003c2c010a40621403400c034a002d050300b449103a81c04d48a03400720660400490318526000150b204140c22025a51070819000c921030800100d56480700e0b00011500c4c0180504d00020100d601d81d00400c1101c040c42d004400580c0030600300000e076544070040801d0b0549151903a000380c0b505441c0c0e04020181410001020f008954689081d141c10344101888000c032200200840c401c0c0602c21202c40d034540c40200024441036441c001140412032440d012000c1f152000c60540d211042203840801d2144d0909185d507070340d0940c1d0350113000d040314000d0150f07082c0590200c0d24123002403030f000219480b20f0f40d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 98888507 1250 98887257 98887289
    0x1020f0906090a150905211c090f0b070c08060103030c060b0406051207050a0803090102100b0a05031e0c0d05030304020f011202120a0e06100e060303040b0f2101 71
    0x3040416000040100d91211202000040203880f45100d60394001c0c10f07403070b85c44090b03281108121200008405000840b6502e0700c0464008001007075480006059074a06000d0a85404c401c4031161619005104c01c884441d1020648010440151038540e200d03440d11107529403a020f00c1603c450080c8401000b0403800c16400000500e81c3d0440602242c025100181241c2e417040017504440044400e4940c60f04040300501c0345d0704150a607003000d012120010b40c6001d280200003907031801c40044900d030440d914103000712941d450b040c1c060000c003402030480700528007041c0d09282003010b40328031201c548030b00c156203003880c107000c0268480640c000d0091411640d581d02444488044000f03d28100f02003a9030400050a15101400510a1846409401e860241600030403224180c0c403426140d4001030400c614030540f20305420684002c00c020300500e0b00c501c008241345000c1d94006000180700071802d0506410854007405030071385a003a280c00515040015490002d0303081c0596080e200300985 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 98889757 1250 98888507 98888509
    0x306031e030a032304060b0906040b010e0f06070b19180f03050a1e0c030909090b071407050d030504020f1203030a1e0c092606060d02030a0203070303050903010e01020f09 75
    0x800b9a01000640c130520420091402030b2a1094208440072601075550343c5043e041b60a2480310940d104000355010881c3c4220040081d00c1c4c0c3c0000c942e140e115075000e08080c4a252148000ea80c0015484542135040d8140b2103111071860101006122000d407a00d6401e80c1a000610990045a270f00f12700038409280b00c58404a40070307401b1000103400e000052038025440f208031001071002213110b50f035014088681c0d140040c00c80c030301c81d80522440341c1400008004119a02c1d500707a0040c0f52030500a40c0b0a1240702c250516026403c005002c3d030140780c1501c0f08851301038000c20b12880c402c90b10b40048494050802c00c0c101107050b40d80d10b10307910600000740c0e859100e85c00b00c00300d03507a039401c1c40c2c0001000c05820800d4034154500c510000722183c50030002682c011030110400e01003a01c0001c0305008104400c0c2d1b40304001440b03144503041c4d140d88001551403e01084001a40141c00c1c5d8214640768200a4084c1e84403e07880c502031340c40d001283c0046041131081d034046c4480800400d20b0540e44d28 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 98891007 1250 98889757 98889761
    0x120a02090910030b04140c0a06120f0e12090a0b0304240903080403030506060f0304060c0908070810090602040b030a091101020703050c060304061401090b03120711011206090c03020306031e030a03 86
    0x40586c102500c14540c6142c1036554413192000200030340d586e0344418071940341c0000281e880c104a05c00b165414803590240080000c600c41d144101c03000440380d1203d10b0f02002822014199004128104001051209006403a11030810760780d02912038902401d0100c0e20b0380e049a0a601c8045c0000703261101290000b4425080380c0e4001d46c0040c031407805d220f6000d050445a510a540485120b55a40050724416800103400d000411042018055643c034158169071243d19090b8401403075a5503200400420001c0d505841c003400901c0e00303891b205e1500c281e4176030003001d2172001646e5513030f00c1d0078122080390320001301e26082c1c0303500c50041c14000b011007040c41460313003000e8401c071200764960740340c0306198942c01e15003402040c1c0b4103808074031942104141802c0c0040344583e00040382c070400010000c02d50075282c0009256082ca061155190742e42010b0300101410b030803505c0d48500303026102001e640e164000c0c1d40100f0084050310400b0103034140f0125413500302c10000c42107030414015502c0840c0a5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 98892257 1250 98891007 98891033
    0x13091416050324100201150b0405011218080c010203100f050307060c111002070e06010f05090904050709061202090a02070b010b0c03070203120a080708010e160203120a02090910030b04 81
    0x40100d81c3c41c9071000e80044d84c0311142041807030041c0e55545111902e07440b5040350600400c00505c0c524035090170071000902040c001070202003d56140c28403006100e0303c02d40d03402003164002c8601c6031640032030500309000c0c1d8400e80c3c14036603050102e140443e940b403e03c1074010448800500403c482c5144c8902034504050940d4107030794041c030a01520900b80c0f548001c0030070580b02c1c0ea011780036860802d0b0108503003181c068200d9040003808648200301c03a401c007045644414080380c907280c0300d03510352409502e40340880e000303030441c2c508208002035000700e06030080e04c4891003201c0c030074419a0b82512642c1203018551002e085041d0000042000b41840c0004040350171210055078607082c29078000c20318184031003102c80c07204140007a002c2101c55000c11929044603040c90596410752507c600d40304d01c03079005417284072012000c0009541042c000c104030b46100582284801c09840d160010034029006452460b000f118040300203505601ea00044000f500d500c0022aa00c503240d545940f4203e04407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 98893507 1250 98892257 98892301
    0x61d040f020412170a02101a0d050708010c0e030a020405130602030702070302041802010e090c04031e050d08040803010608040c12050a0507092d02130914160503 71
    0x25850103503100240d5400100041e1541200d8004503921a10304107002418207030510510341d02c1402540312056002c01d45840300700940001003505150802c0740180303605103454040e408102c079007138138040201c042003820440d07160030300030030501d90030803010b683c01284601c0c580d606400909108005181507401550000c0160000d200c0c003480c941d8603c8120791041d135256002d40c1c03040001300114540350084032071100e440c00c806406564260b0010f48121030003070311240718400a40010701130b03a000c441913800460b0002186501030010004c0d9940762103140d1402d81e05809400421340c00c07a4015003405000d103521001141c030751b81c41c224040341c440c0c1000d0f0040720304086040e8000740b45500741080140090080000e0544100c0038070341645880b0455101584845c24020440c545080a080301911180003410340c0c101c40320380c1c1892030001c1c8600300000e903011848280120380103405a01c17007070700207102a02204080d2035004c01009402c9060100b0800280100002030400007050441014000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 98894757 1250 98893507 98893511
    0x503100c1b03020309090c251502070c030b0106031b030c0302040509090c0a240302210f07020106061814040b0a1415070215070f0f08070615061d04 65
    0x4500400c1c150300c803418200a0380141d0000c00c3c007200074a00855103070340041800f1035140c6080c000c410442c40f1102e07d1388a1302c101c1410083e09400b4081c641611000361034103140c0440d40d4182a00e0413002e8950a03000540b0241403000000c2031060181c860312840710340500990150014145040b000b034540c0e400c400c8100340d020302c0002000e031115401c1c107008140c400702074000d1480080901001005552200843d0130303d055843d0140c00b80d0300c0d00f04002030b446290250341d030629051013401c03101c003080d45903880410790000c002c402c0a10b0241c19000e00c0c0d05070700a0044035034940089a14603030501c960f1091507000c1d40100003014802d4083d105c404005000401c0450700d08000900c04505588800c003200001e00f80d10000d481c0c20070b500c20071000206096801e0231032035008030780d104a40383c1c20300541c44000120002445006152004c8880d400308030380c142c07146d03a032400749081d400812040740c0039400c006107400148110503881d03040e00c60729501e502d9203100c800d100445a0542d0210140c1240e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 98896007 1250 98894757 98894777
    0x10c1e020a14040c090e01290a03050714040f0e060d050706050316031e18080403050309010306050d0b0a150503010f0c0e01080c040306020a170a090c050a0503100c 72
    0x38585200500051140c00c0707449480060803401e21007a0713030300340c0104010020012014002e415080d580c150658081e2003d082044041001c0c103110003074200241d01c955000411446062507050b04558410086a511040d0309010310120601c036014500481c1880d00e41604244102414044801d5102c14002c00e15800c44a16480c0c3d0360908034035801000c00120000200f00380f90001d000d030f010158203586003c00c80038404414000c20740d45444a0103e40a444040440300c0048402c1310b04170700c1e0f400804150391346540703142045d6a680980b03410380c04070f0b060003c0003c1529001881039041130f004903040840e0398846030080c0050440324090b42c0360254900f07020404c0c0c0c40034400d1159482c801c81e0000748401503400064a01a002a445810000b840c0b0130403182c00d04e2070040c1c800300c0c5d5100c88096214000c01e6001d80700079216088001c5400401010091485a150040100c0c03a01560804406903114818489000c1040c016607815901826202d960a00c2e282e00101c546461850301c01049 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 98897257 1250 98896007 98896009
    0xc11060307030605030606060f0316031b020307020405010e010b09041e1107140708030f0f07060c0e040b01020316030806030106120b220309050603060f04020301091505090402010c1e02 81
    0x103400a5404000003039958200784120b003020440c0341d8105038102c442070b044c204040750b610040d00c00240707281c4414074004a090700741030207500640c5c3e404070300c07001c2e4030241829000300070f589030000d00c0280d1145092000005100c40c0040c41c0c42c2c10b84100b139100500e85070042040c04007400085880c0080100050301070031900300244940c3c4810160001480e0340d030200b50400c03114a400000288615810040c01042488400012640481c14010403181c840c10310005031501e03401464005403080d81040d44000079075a0200c2402103928040b40c00308014030302240126968015000040400e04514008502003401130140310b5118600800102c0d082c0c1d01d070340c406040540405070880b503010345007060001082511040b021194001c040300034000d69581c0b002404482e09200b4180540c600001041603034946c0d00c0031500906016006555030f50b0746000c003200800d015200024061191400400d2519012440c180a160140d41d0811110030944503001581001c081d074646203c2000b01345001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 98898507 1250 98897257 98897269
    0x9020d02061806040b070605090102040602071205150f0603010f060e0109090203030c0f1c020d1209110901060f14030c030105041d0109081312050d0e04020c03040b30070c11 76
    0x152840c0d007135864554a4515144c07003915030141162700264014401844501ea0025003002100c0c466070b80d10940500300e007005810075041c1517078034403009007950070004004014400503000b1041940200103e03c04100071804079030850007410310105011004010762000c640043c41e205d0b000030f00366880c00003c09030492501900c0000d511045d04440003031040c0c00807101040f403040303695001600c507112200c50001e01e082c403004034984007541e5480e10101407000c500595114403202030802c0c181d41d40c4415001c0c20007051211102c002410000e00020000c1d030075010b036030040a80e403402505503400c0000704000b92a10b200418940c500d0101441c0c440d20003401064070b01d030302a05140b0f5494010069061207982c06800900109102c154048e00080000546000195492402d40340c0e0500707110008010f0311a80d1101400c501c008074000c152100c1c004000c2c0468076140f219142e0580c0b00c80980e03004404545500c0740a034803104002400c690256004a400d03520840c008c07004602c28000240c2d03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 98899757 1250 98898507 98898509
    0x102070b0109050c040e06060307090320090c0f04030f06090f03080f010f080a060525031e0603081209030904110901120e250506040305030a08010909020d0206180604 73
    0x114049480010440040c0c94410f040d080300c902d1500a00c0c5c1401d00400552595006d0000c501a2600000185086c4e1040d0f1138030f0069a03004c1c80980c502140c2307084503900040104000c62041020501288004c0e0325801182ea0b85180b82708401e0401d4038503150304c2d4403036207100c8007951000d44800c01c030000a02c21040607031405104e0344850040f404c000d120700c824040140c200740d040510100c410301a5050025960341056803150020581d82d0fa55210104510351208464030b41760071030001c1440a0f50140c0200784100e81107030340da003511408601c0c0d0301c007528800c1c030000c1c1002004100e907000400114600310307800404002140c0c60710040d00086000ca032880b001c00d020303600c004505440b080d0303403003548004c070803014003400c1c014a050800e0458a84040c003654440006141c1c4580000501e00c03891400100380007003065071a5a640c0c100203407030b07034408411000000c0d007000001c14100c1482c464060074a401800c0355a40c0041c0741e09004041c0e200402503800c0703090414034507040c0e40d1150000c0c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 98901007 1250 98899757 98899763
    0x7060207090c020c01210b0603130209160c02090c0c0a080c011b200c1201061a041a0319062301110622140a0c05030d1202130503010207 60
    0x140491418000d203046850141c60b40c1c085411203e0a000c00380e074422001040361168945d000f070030f009002c00c028000c010300450755130003180100820880c4501c15425001040c0242c1d04180b01e80c0d01c0b00c0842c11301450145c2c03000c022502600b091009170400d55941603001e8022103405151150749a0800d00e8040301000c00c46003100001007802450b00d083c095a540b031403000d0420100c504007480050030f8200c08143d030701d4070160b20401c6545003990421180c03000c4000900301c1c1e5403440495403200c4c0604441d010b54000c03400c04540030028040c09004640c11203081c0d0072072124881803c0c202d0050ba600c0034284584903d401034204082082c184102e500030119030b2201c00300c2c1c010711a240c00c43e0901900380da9041c40018030750701618200224005a00045a00c4c8140c1d0100c62010f14011081040754041c10082c102d91041c40481d000254400d041c2d0700034070003403150310390b20b00803d56034401c448108000154a4100840030b10b026070050062030391a550b0314a56142c8a001190898208000c15 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 98902257 1250 98901007 98901013
    0x307050f07060e07061103091018030204110d0b03070b030403080a0605030f1609060311040902041805030c0705061c0c020c060c010b120a0503310902030609070827010e070602 77
    0x2c005250b004055145268075a2002d14141954030002070444500c9c2543c0380240207643ca03004050240d010400d501543d4020000c00c01d00007607018400c500e0300802040440e25161500c00300c0076140004403030341121751646480e403455032a40c0e000c0305c40030000b800c001201d603110070020501d640c09001000c1d541e84050001c1c500400340c1000c2c2007104100e80e00444d00e107840c0071420700100b424841e81d20400c000a44020801d00301c00e1010130010305880c3c0d04030071030349108440c030000c110001c0300406424900700700725003541e80c8500070441d01e480342c02d107807000c8280815100080381086070810a0541c40c9401920741c0d241543c800b0074095440f0742c16601071039544640c0f1500501d8201040c504058042d0018110b6059a0307840b02d9403031290074228410a048809580c03030b090103220401102c003004d04810050255960340541c0070b500191001482140703c0300005180f14483d2042d40d1180d010880011000e012003081c0b103a11880c9220214582d540320201c0092083c410010340006001513401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 98903507 1250 98902257 98902259
    0x1214160602031306030e031b031608041409150f03010b100504050301061212051303050703030806010210052503020903010c080601090b0703020304091d060c0a091a0307050f07060e07 80
    0x42c0310700c1c0e0320a50401d405140c50301d0f401b051078080000a80f98013070328482d0030304940c00a0000310740c51030090300a0f071740348026210b050a041045000145c411107011000d810007002d00c5804008030f0b514219054011401c031a501c061652801e1504107188400c050000521810310001050b41c5c4914000348074080742c070019042001e0b050911035140144070815004403ca00d19035a8150144c00c13070100d1408120020036108007200102406100542d400405c0f1000c1070b40d00c0c6000b80010074202d41c1e00340035001e0517240c0400740d042c6000701480780210720410b20a1882210f81d420000c00e8101c00041090360a00c29038045803000d00c41c001c011625511182e0325482c0140006081031119040080ca008060003240006900082a81c00307888a546010995031078400c0e12144280d0326514000ca28801d5a0070b00a4004008000f0010300344180d4840e4503164980750841c0d10980c41e0f0f00954141c5000700000340d4694801d02c05000914100341c01d007460140261074450582c0c060890f2000c2e05d0708113103c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 98904757 1250 98903507 98903527
    0x40f031b140705030316030e010207080f060a0c0c020a0b030c1204061a03150a091e061d03040605070f02120a0501061d06031b041b0206010302041104121416060203 72
    0x100100080c0f401314011403a102d404240d41115080312070005080c07007800008004141c0c02841800d02518990f4111854040390a030700546c0c403003051380d44d400d049203440c0304a14003512859215011540252481101c03d140030140c241583c401001401c04403018402e40580c100710700505c6000b00d01890004c11915400030114090741214140750344294002e04a00e40d207c005454059841310303580d00d0004820242c0e040141c5912070f815450021010381d02512010030040f580b00c8000e0035600040c09081c0078204010b241e0782c2c03140703000350303004500180a0000080c4a000640da0410700c06030950140d4281036410516103400f051085400341d44410040c40034003c21a00c40812513954503c142e11030030040042600c4584c0c0c00e21103003a54441d000c8400b45920b032600101c96281410288449a802c800c8000352075803801e0008a10880c00cac40040c0080c0742130881075609a03850020030b02c02044683c0d0712035811000c0c90314000f04d14042c0c403c80d0b6804003500d405440c004c101c1034010f155280c120070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 98906007 1250 98904757 98904763
    0x70507060201200904140906041713170109020307060c0b0f01050d12021e01060e010e010e070f0903080706091a0108060a090305090a1410030e06040f031b14 69
    0xe0000d4046a24040030205803000080e4000034080e600401c0942d16115400820041d0000302e04402c0407503621018008480d00000e0441e20460190403007404100c40c211540c4581e104840d681b400407003141c03005108000f50f11010f000201400c800021b010f12141e40031900705000ba921000114180309403400601c61000c1009501c5043d40788841c1556044c100001c490400186024115403100404074554500030840280d0a06080c160b026000c61520034480c0642040d01803904001404000051107080e02804103040e40c241b000002d0f1190782da1201105e21880e800c440c441007154080000010070782130b40c0141000ba02840b80824804005c0c20b1400c6c944040c2c07109032950001d26401081001000704055401c10000d22012900d0501c90908450b07034003409402550220110303100003803100b1010f101e00041e280076100030854001040003070f0708035003c074000781100e82c22030000140081d0056001c00342d468400d05010408101c1801156800c120945040314540d0700116824210a010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 98907257 1250 98906007 98906009
    0x803010e22060c170a05060102070515070b0606040902030f0a11070c0302010e0103020c070e090f0a050c060703030e1b011e0c06020f0f0c0c040f0c1e02030c0111070507 74
    0x110140700c000040d100804601c81c007640c40150040d41d0b100c6100100d01d1050074160720b06030800c95a900b075400c154403581c00406060302c0030780c050321410303400044c24106010f4000030700918088440c14460651101c00c1000c0009101c503034011400c20010035904518400303107014000c040c40d00b4400b440e003401c1910885a03049645104000280b054600050980d2500760a881c1e0a18100c0b48240c0179000603000303801603c1601441340180f000c0442c0350285041e0780c5d807080c0c20210445501c1c02450b00c03400d480316800407000d8029000981422042e050590040c0324091003483e001440d030342510b000a0924070044c0f0b500c10051110500081d403581c0c0101c4004244801d4071201d0145491094040c7c0003044c0d0b420002c0c0cc440c5c0109408076016040700982d0307400303801165003da0721182c28500c030b502c4041d940042889903140c0101540180701c0d501c6111742105540d01e603904a009001000040190a08040310841c80100021048203d003809505040b40032030b2101c03500ca644601c1d0842c204100d07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 98908507 1250 98907257 98907271
    0x80714010b0d12030f020903030412060b040504020d03141c09110102061509090a050102030702030406140a0507020105030a0b040c0c020901090e121b0109030c05010b01020f060606090307120803010e 87
    0xc2441c40003c101821905805005079041c00691120303000c0c50030000e8002c0090681d4907000200e40041c0d801c0c61184451411485400308100d808600c000704001c6810a680c003a400000d8118281d0000e800f4140203c0100861080c05080041000305101d1140d84107038144202c1c1e8840305c0c624200441d040740c1504000090001c0c00345841c0141e13181580503d200941442180e0780000b1440204091081d207640c0764118001713545c0c030314081da000382d92030b03000384280c4000031200100941041c849034292041910503580b080d1600c1d425800454140d0005006541c42640c0d541240301ca6589034825901050f085440d80103102c90180108680304005900540700b00381401101044141d012072400e4000e00c0a10382161941c944181e590000c22040400e00d41541ca00240e2805054002d2141d0105501c00c0009000109486004a840381140b080020b0075a11180c00300d0710728603110026040e2100080e007114100c43c0c0c1c44100c01d00480c0c5103001170f562841d0000051000001c2c1842d000e91080d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 98909757 1250 98908507 98908519
    0x902180114090103090c030503030c090306010b090904020904030509030a060c120603120507030207151e03021201030605060607060f3e0304061e0c020601080712110d080714010b 78
    0x120450910301e072154600450405641e50602810030017600700c0340c1d0140da0403500300c80e241c0c0360001910744154000301c8150720a00c43c0100002c3d0221a02c4210340500d000582190141e0711150b007480300400018004509004061051070a180c608200425005004420120b40c0c282c80ba4806000359881018031a00c003420080c050020a9400d1740300c100f5207901d8500a6540c10403400c0c1281400c445811011800d0300a03141f91521036808040403540205120a84228107200c0409900320b100c5d040e1805489030f0740c44010004111140e122540c0220082c01c41031505410b59100000c0316580b2040d0104d140c0c0c2d41c404015819260302e0000c0484a80109008030903102800034800403441e0240003124070340c0080014208840c54120807458100d0760301a082800381c00c8034a0700a08060400307100144500c10002803403460000307900e41121090b49046246c40016256000307548956040c054202e0310300071400b0300240b400c034002c191460043c900000c0c2c5052200595080d6420074503000c1c4142 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 98911007 1250 98909757 98909777
    0x121d010c0b01140f100e09100e06120f030d2f03010909021c0305030906150a0605070804030c320117040302010902030706030c080609220309090609021801 68
    0x10355560340d8a81900d0510014a406000040008404000c0303504c005411550048140d0304654114070800c1c0240800c403995411503603078031500c5d4105d4059108101008014070085030060500c003c0984035000c881c0261400b12030101c0c040d034503540c00344c0410380915541c0d55000d40841c2d035020f0887c940d00e0b0b0003401c0d0121034511030103541840c0418011014015a034424490440d503c49060440041d0000050303020f0a81c541800f4105820841d0210000e01030200000c100e80011107030030064680c001d000402d00389c2040421203035034204840c100c82c41341c010040840400c0c0b20b12044d07801840120071100e035020101c0c481140b102112520000c480303022031202405a0b0700500180c01c0a994030047c04110740d5541404c07400360420100c041d4050142050104400d03901d41c100843e5a9400d48921801d41c4562040c48000482246c007030701c034103484421000c43c60a4800441c54040e0107442c0259010b901c0e4641002110700660090907455030000d090901411082c0104c04040000d0a201d00e0307074 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 98912257 1250 98911007 98911013
    0x501080a020a08010e070c050d0f02060739060f090210210e0c04110d06060908100e0f01050702160b1204020f0103020706020711120303070f1b121d010c 67
    0x10f00d818021465840c0c04240014601c0d40320f00400c00449410408488480f942c4400141c22a10740300442c000500800700016034482c0100108400d01d601d86110315510455442c41c1211601c80740a945004c0c44011650b00200754140101c0c0e2601a0040d00054600241d1041004201b1101c1e0350b142840281d440409198200340c104040e000c081c09000b156a207086128076040c40b150040855020b443d2514501d50100b000c3c0c05001201083d1000b04001c42e20743e43c040d15903160500c5500056030019050010441442d01700c000b0901c1c051040311402c034440701c4402c0c01e61340115910303c0140d026a12103d0a0540c0c840f15000810108030707040e04c0c086002941d44d96010340248080d0080f0090518500b242e48254120f50500750040c2c011921015145045000107070070007401e0b40f140c8203242004c8007a40000c000c59005401d251908101d0751500320066442031100340d07803c0302a032070106204000c951b990340c3c069641a0180d0759000402240c402c41c00e0000c10384d0130024100441c0b20044000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 98913507 1250 98912257 98912267
    0x206010803041a0c19030905060405030c211c02010c090b0304030e030c13090b0a0b010f030b040b060408060a0f180b130807050615040515010e1201150501080a020a 72
    0x7a110b10f4030105003612001102c0c00c1e20303841814200c01203071240c40e007401701060300c0d098040025031007952102c44d210340e1102000300500690241c1a410b0308500707226021490002920040a844100610320205040a1040c102040c40c100c0c1700c401013260110158032a8280714041c2c0c2c82c000c90074806c0d411800c140401400d804020001414800b000c07900b00f605070340070000c0002100000b011503000341c9000c407001010780b0a005048500b20702c0d42012445441d03c5014507007002406a5400409004040045000d071101011082d009941c07145840d505072100002080903001110080080342850080381c01207600810740c52001c1840c110704001400590083c885000e40c000f0058541911002d50940e81c0610001b002046483d00090b00303001c2240202d9100d02c030707171144a03500541511000a0100380e070f4040782c24140d140010f0754080c40c0796014201000708000007515101c140429036940a007196040c1c41c0c00c81440b00006030420484da440300009900803445401542008284503000d40703 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 98914757 1250 98913507 98913509
    0x1020703140c210a0e03030f030c070c0b0403030e03160806010b21040c050118050a0e0a0e1203060a1406340b0712150b0904110415020607020601080304 67
    0x5040c0001141a441c1204110100b00c43c402421042030340420300240d00142d500001c89103011401d440114401840c0100540c0c0110b01264402480c666504a100700aa446038108840c8041c86510107d0142002d202400186110f0b84584529004007401c05160902c0300004c3c1600141025081c007150f10701007440b07811070b02d01a00140d06c1e80258006003400e480f14144040c0312003500f404001c04d00c040700c06880c00312607080c1c13145400c944110300c5590a440306806200e8002c40302d694100400b03105c000c50740b40d00455a40c40050721544500c01315050111648200c0014480070051081514044c1c081d00d00030540d0780484038044040c00046041c5010300350404190810142d0340110003407414807900001c0a1040300e894902d2400c0ca48014040c106a40c0d02c00029010180020f40c5505403082d4200000c4290098400318540f0040b25a5a4003600d9916001611054000c201c0c0c4140c00150029042012201d034803e8001ca60003450090f00038166021580201d00402c40c050010003250 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 98916007 1250 98914757 98914787
    0x501050f1e0102010207060905070f0b0408030a121407121b02100b0328060b100210050403021905010509010b060a0c0b04080f031503010f0c090b0304020d020303070b09010b0301020703 81
    0x4407140c03680c00180c2c0240030f250006802d41d42000c5003001000408a19001941c1c81e04401d0a80b090301d901c45003400f80290b00416940c0d91041000d058031030300519124080d80410400410407010301940184014001d48001c80031950280e80507000d4030190050650080008254640c4034440c208000c4d500d01d0740414107040e071603440025094688052115800082003550300208020030203601072107080803008240d4000c0d01d080074240b0586010400040c20001c25802440000f034550031800081402070022019403040b001021450750301403a01c6c1410b9030051000244034a400b1511a0954841040e89031080340d081214020040e001051020340b02e804c108410913544c0c1d01e1404894074425540300c4a10031a0100c10041a0703900d240c000403151740160020300611282c031071a201178800034265080402c04010341071164441d4030b806558480d0000b8181c040c010b1040c2c01007402c41e484201b045c0c41c0b203540d60302005a086024050004078400c00c0e4000c500d0481d00b45c400400d44801d00400ca = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 98917257 1250 98916007 98916049
    0x6090a030c0606050306010b030405060106020604080405040f0605120703050c0d021c0f0611040305160317090a0f0b032a0415031d0d0f021c030b03100906020a030501050f 75
    0x200203101d0385500481c00b400010701141d01c6075840c1c8e015111244c1044404803554401c002c004a0312070b2000c02d12500465101c1f0605042c50300703100c03c00014050195490070308940e500300c005016500d6900e41c02c0380807c501c0207041c0d902c1c150309065003405805600b02d8043c01010103c0d2005031611400c00c0050682c0498400e964074043c41c0c00c81c11805800ea01030304223820401600d034941040720040003280e100713004075001001e05400ac41c00b6a0450b01c0044c086005070070400600c40b0102d00140f00c0700038010306500d00c0d16101c12141159424582088502000210401c000c0c18005401c00d00301c54100c1940045449510124150a10446c069034203600311054262120742e000707070000882c507109880c0203031114030042944c41c0c1c0e460030038a0302c0c400644114124052103001262502c07000d104410721121203000030714188c4c0986440041c2c650948a440c41040c40c0ca003443c17142803000c5100d050003682d1000c503244024107481040e009140306030715007660b4a52596800002480e00d0386000e0b94 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 98918507 1250 98917257 98917277
    0x21c0902060f0d060e09150c0c0a0b0405030c12180409020402091201050402041b08010e060307030b01060215070e031b0a050604080708060709030203070317210a06060206090a03 78
    0x4a505030003000c000c0c61010b0808a1807654801042d040366060743d44440543c0125520600d4042c1d030340700a02c2400011500c0d100100b81034110000003003044202840c1290249a21959184c2e60300c40125425180340d0000300d107885481c1c005011075050204222943d60400d2001d1011001c40415103c429206660715120a01191900e4041c0c0300324100c020201c1c0c03000c1070b130200c400303000c0c00084034228855450030006075548890031126040888842d41c60128036800c049502ca981000a0005039051003411000400680180d00030f42c007a05180d030180c03002c8191850240301c03021010b080082400000c031400e04107920b00054184042d10200c44030034155101c08080f0f01c503030440b03800141e040580028040398025000401104031424441140c0d12503032241c004031741d40465400000e5054101e0503041000c5066815240d0080c2e0360469218901503c69240c00b450b046216400d0003e540c0308403c0102007140381c495003000f003100380050151880c0c1038a8494480c621440010148800040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 98919757 1250 98918507 98918509
    0x150301060c0c0e040f0209010f14120732030303070c080313050d0f0905061206120115060305010e090f07150908010e0a1b050904031101140403081801021c0902 70
    0x40c10380000c0c0240f04660245081c142001c110035002c20406030300551280d000080d284040100d002e0445491002d030f1004598080104020b1100003101000c1c144103000011910904203000d03070301718402640c00380131a0103103242d5400010034100c81e0b5034440d410601c204200d160b00031003e0105d1aa005245940d25035903428003080c0c0000401d406086441080b400643c51500000e44051041707140e224100c5c0c0965443c00c0251034490425512103c2448501098090503c80f624100e0396a540c000811512a40d4021803224101e40d882440042d0701c480c01041800d219071500c03a08004044e0140c011500348140c3da0356075607218400c0c40d41d02c0441484c90400c01c2c0c8141d4080002e003100c0c1c4000d008a402d14103c041d507072402110103aa0507800c40c8240d400340d07102d4030000300c00c480015096600c5c070b0752039460a483c41007068564010741d54a528003401540f4140c141d6a129a1107500c940009090491001480000400c110315007a8810406017030480d50443ca04003149541050204041003648 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 98920863 1106 98919757 98919773
    0x30e0f030a08060112020304050307030e03030a0903120e060c011a010f0e100905040e06010e241306080708031809040b04170421060b150301060c 64
    0x115041c2118099040c2c580c1c405014101034061007041c42c0035000340ea20032201291a900000b4400d800c154020f10300e00c195200035401103041180c00600034040c2c12482c0005000440900050084944a041000d90389400940201e07140c04500d62a0780c040e0110480382e0800384030b07415400e4a554410b45140303045c0c1099544007070070b0b00210400d00500d694051031a004000c0b404070045403070780b210300990030945200c0c80140801d40c5410103c0b00d1000e406070481c0c8400000600345d40e0151040c41c164182c48908a07a90b04036503c5004800c0000c0283da8440202e03030142a40010b050400407001e032500c541c0551318000854040e034104a0418000c80700100310811040125001c600c18401d0b401a000d100c6448500e8541c42d0340019040c05459400000358618105d403174802c0010f0b5020702d0f041c3c80343c26189000b90fa00c40c5142039100e03020500541040100f050a1b51060207080 = true := by decide +kernel

theorem cover : BRFrame.Cov 98741007 98920863 := by
  have h0 := BRFrame.cov_init 98741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 98741007 ≤ n) (h2 : n < 98920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
