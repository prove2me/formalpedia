-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0580
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:33:45.161399+00:00
-- url     : https://prove2.me/submissions/b1ebdef5-b5ef-4313-832e-6205811d6cf8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 104136690 ≤ n < 104316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 104137940 1250 104136690 104136731
    0x30118120915090306020903071d01090b031501061d04050c0d0e0c03070605070c030606030c0303030e0c030c0609030304031707030f020c090606160501090809040b01030501051c210201 81
    0x1402903048100c02207101510030300f1188006400a900064030706200d81c2c06110f88809882c0281001540e25000d8100c0310a00409001d01700c4008c0c907201c0b103100f0134900005ca0b050700c5010708140c10700981c203001c0308680c9012005106241014fe4103940401d40c0d50764042d01c3e100341000d03650a5101d50760700c1c0d164410303900780c00d0081149030403640018041c2d03280400c03050705403441740c10000d80c1e030f10700d070316040c0c203804000da1000d001149800000b00400281041c01c2003100e01a54051000091800c1102d44500800640b40da050340503da1000081c03c10b0409403e4030fa00040603642002d89d17907203562071464003c08501708003100016007e020182c000c00b00100b03c40c0c040c070041441c2d01c40b8401044152a014003031a22602000c44c2d01400c9030020141e141089038400003e00c01480c3c00e00e044852504201410b920581c02c1038124000c95120b441510b040342d0b0000c1c01ca400d000c00c444c550f85010f00f100901602c0e072070708124000e102c1000e02425410048402c0d80001544d1103504803040d00e081 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 104139190 1250 104137940 104137949
    0xc0a020405072a0b011505190305040c060e09040210030b0301051503070b03011802031302100f0311090307031403070506010f0914010b0910090801090c0806061f0309020301181209 79
    0x1d511481c03002060548404d40d0650301c5001c0448140d406030381066429020303101c00845168a00c2450114003030b490740049014500c620000c0707030125250ba80a5030621103c006080e0027140010000b03000d441c064104002c1c0c0600340c20005000010341c00400d0035a6011070b000141c042c4411880350032400c0805c070f800c000b0085c0d044180d06550501e45201a03800705d502c0091000d0b500840815104400050300074600340d0300400d0171400281005e030160900d0b0100300b00304007091500c0044914680880304441802034018040d008442c00c2d0703070b6410303e110352615480344180b205100760400220204000d5002c1c26014206907201c5180402c1d60080d995040300c070040c5152200700404c00c0200400649031045000c8410407134607008042c045840412583c0035420300e60810b240e490906c141003040400ba120044152149941c501c001d01441302d04c4040c105280e11403040d4040402c500c00e0340050010b52004001041109484051304281c819000d0240c1d51080c0b8031103509112500203d0220040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 104140440 1250 104139190 104139257
    0x30218040201020604260d0f0e0c0105121b0705060a0b01021504080304021f0c031214070804061407110f060c0f1806030a150b090a09020c0a02040507 66
    0x145450790000f502c600700600018940d00c541945420507007904042018406043c0c107959444d17840302c88118000d00038201724230702e480e8a00a480407c20746e012400d5401000c068488503e003904685002e440c504c4010162104021103011043d520700b0720000501016000348000c0c0805e0508c00101012101184442c0381990710041c1400b10811200c40399039801500584071507240d954500120340d2a25100e1072944001441132030034034078140c11010000c0d00c0c5000c0da035940103000790010f0f11f070700b00d03140000304294030b042001c00516a2480f905899074070501c184804203003400d060340d50404107803068490f40045500c001074040c0709c0c101000301c900b502d00000e008010328141003024520714400c0c00c9201c444414001040d10b440d50102004135120b04026102d00c0d0349151110740c000081940f01d48202e01d81e81081d034000307501c503894003d840d40000003d000b002031628111801000b9404170103856080d0003203140c4000569500d100c1c46100f0211511945c0c141c2e01a207208400880eaa4290714890 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 104141690 1250 104140440 104140489
    0x5011b05120a200105090f0303040c1202010c060c03050106140a0c060507020f07030f0506070f2a0b0712110f031501020a050304030818010305090a151508070302 71
    0x4140e000500c000c109410607001559101c00c81001c84110b01600c0480004402c01c5140340c581890552040c3c3c440d03284003041d04c80410a205000da2644402d4a0241000e015a04107001d0042e01550b05151a441418661410031095580600369500d003806040402d940700010403500380c11580c07000e1680c440d40e007054a04005408040c1c018041e110b00a0105999100004e003007900800180640e00341d190100da116070358920740001d0040740410100d505008900200e44183c0c000d0b42c440700040925220100444490b5548203488111110040d480c00050000200030901600d03525018001c00e0707650b400f0b07100308400e0203419a2400c0701400c190031030400140303090310320501c10380c2c0c2c2144070342440902031010440102e286c0410050040e0490000040000401080400070b101c1c02c0b9501001c1030800382c480005408803082262010311a801618062000540768400000b000003100340020301d5041c0203608103001c4416400050035603110b44020301c00e42c94145459005981000c2040300e9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 104142940 1250 104141690 104141693
    0x180d08031302040e0f01050405010c1e2105090610060806030a020904020a0b0f0a180b03040f0606080313180506010e09190906020324010212090303091905011b 70
    0x6251100514182000e81e0511800c4119900e0390400c4490810a0701140d04486828440c1c9001301404c0d0f400b00c0d00c41d844d103c029606940660812604900c00c00101540d8055911060340e8000e00d51810030740c4d5600b00107c8126407056841520300402e500d13801018203151006448561012035003001d02407000400070084240e50000e49445101d84c1a1241d8015454030b1001c112560b410383c00c00410642e01207850744001c0a90000340181075026500c12900300445400041417200600622040c003408000040c080f03406c1c4001c803000280b0442001807078a50b1210220708540003401c6613500c52020000030000144038445450104480380c0c81001242484000600f04880700d02d07589008081071000203155038101c1800c06005404010b06002010103458000001c1d4411200d680b10881e0300444c07a25882100e000c100c100301e006030010b0090220488109806810446a269040c4010003024400303460340c4801c505a0701e85c0811000741e007402c100000d0204021101000820307021401c0340c40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 104144190 1250 104142940 104142953
    0x9140a0f0909050304080a0b1f03020f090c130803040906060801080d0c020a091a0907080702251d16080403090b0d2306011d090406050c040e0c180d 65
    0x242258540c5000140c000702da443e109003940a598040c208a000304e035010010b2141180a41d8450413840018484201400d8250414480306000c040e40042c6648211704860411031015034115010708842414046e6920915001d00300f02e03080003503903410216042001c0780c81402644d01030301290a1860807503040001e00c9545041052102d0100720494803a0740135900d50410100c09000816000d00c40d8030700c41a403504901038a034405d40d00501000c400150018869094280155000d501070011414222544500341c1500d54a20100c4140648c00280300e1a901c0c5800c0c647d0032281c4001c0b409440d21012508405846504031428004103100b0040040d0b807110100c0c042e07d40940005840d041c841940000605038003a98050a03090104070010b0500385503138052240101345e955050081c00d074190103c0c2c040c62100025004440100458000342c1c094000740d5201085030740440c1003ea803004034080c03c003410354158245d40b0380041d040d020940201032007542000140c6d0452444072460780c462 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 104145440 1250 104144190 104144219
    0x603021224100f090902011d030c0420270a05060f0a0918021c1104090e03090d0b07111f0b0301090c080d0306090608070302090910060609140a 63
    0x4040003001e0001030012031540302c5100c040c041c41c007080240a134403070a24000503c0401401e0340420403c40106014540103040305048500c082e000e0100d113054401840b018000e200801190860070960f4828024080003360410040c070514031803443e4990b401d035850128001c102d450150340c46031070505c09a00d510b411580e181095072105507550040740030440782c60415401114104100382612200141e664000d0403901c0c00341228545070401d4002008204d0b00341011501c400703d818042003050b40242d50111001c2d080d00c9003620328202103000006c2030b410041d402103c03450004c806112a41d5448140d402c3c121882000402c004280c06100c4201c47e0492901d03511080d8071409003c00c251400e4000640c40e070344c0451002071302038860703c8040e12020300d070795030b9000245881e0000074081840d000d81000c903140d000140c000c490841d002d00140c805c0c0280b01146a1117a070300b5005582e0b0442c419040180030070303541d400307609013006003451003607440d101c40c01c0c86584007c4060007101c03201c0401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 104146690 1250 104145440 104145493
    0x605060f0a030e060c09092811072a0b030c0304060c030e120c1b0f040209011704080901090801020a171005120d03050c0a050f0f04050402070606030212 67
    0x5030780c60340d0310548100d0142007a4402c0c1140b0340510001e0011102440c1d0140442100440b00704c45035a0b0b90807100047d00c032403407400d090303110880c0422940130000e80e0710554280440d00d40079458071405848101150800d03d00601308601c0c02c0e401c0d603401c0500552404054000500168a103090001101806000281c80500200d40e0307500e01c8000e8a010741e108202c5c071180b240030b41b03445a40300c80c030402050700807008c160501e004100301804c681e0880c0400c40300b2550010300901080e006201404001d402c540307003441c180203400920070820780390090820301c12841141550b54611850000402d40c001da6031100c2030f143c0c0140700410019802c080c080007242d0114000d4038459440014031801c03e400f581c0060f402001c40c080362051064041160f003445049030710184000d0300d0700c03e1440e015100d403004c0e2400160003800800b000003c0c4074014141801c04c001c005040030b49590001d022030303202280071146255250f508000b1403c013070b5941c0240c203045101070540551004151000c05151018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 104147940 1250 104146690 104146717
    0x50a0f0f050120060a09031d010203070605070e0a030f0c0f0e15040f0e060a0c0503271c0305091018080d020f0a0906090503030f09010c15050c0406030b04060506 71
    0x7080c100d484500d1103e0840380b40801c807134241c184100d0b660020070b031440d0300341c0002d10100720309000c80316860509400c0c0c040c103a00552a181090315010010400034040b9000c0103802d04c242403059031540c900714051401074403a400102410300e84520000519400086d140f010104108480c65204c3d01d540d0b4007400c144d0f80d000c86041c90400081c010300300103a00300d10b507034900400c0ca0b00b1414005141071040e81c14003810040030015107010b846c40c0c00219020244141d00d0301c00e02442095422100c2d035100034403412644012042c04030640074010391803422000a6480f02000103028080029503402ca0601e00100120b8040b2400f02010301240e21002d040500d001910302c900e015981d04499069070001c403096200d90200340000d150803c64482da2000a0070000d000c00c40d40303004011181e17480c403081c0b0b16038980042440151030600500005a61040e007910714000342d0030203801614420340c4140e055650301c038244400902142c821104d914061890000c0a101d280c41e030000b2507155026000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 104149190 1250 104147940 104147957
    0x305070f05061003060b120c12070806070309050c090714180603010807030201080901020a0c03080408090409050f0708010e07030f02060d06080705100e33030907050a0f0f0501 77
    0xc140840d0140d0840081203441828100100c1428660343c5206582c0b00e0582441310301c860304104112080002c2400b5034a400c1014a03030102d00d04281100b8840455000740c1d0242c6595205250810104441020101e41c0f1616041c040207028400d20016940841d10306402d414070640c0100512f00006643c02002000200020301601d9041c403900c100720000c2251381d880da10740320781c60380302c0fa40b51008901240720000810030580341030081d203104080a07614190000015102118528405003054841480c01c1141a24544582c05880390b0340b40540300030000403803001441c07841c052032a4440e1103180d24280c0701702c0f011000400c8001c11a608400d0b4071840580c24000640907104000d00c5a014601c0d2440002d0000ca000c11614100d403000c031114052030f80303071110076100c0c0f4000b030102d41c0d4880b0583c440802001840250720580300003a03840e61090fa070844101088503031041d01c59802c50ba00c200740804c810b140c66034001000e41340712807144222038500f01c1804414511030191078140300055 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 104150440 1250 104149190 104149193
    0x2070213050f0c1b0604051e190b0601350709080616020f1005010e010504050402063a0905160e070c06111c060b1306030216050717010507020c0d030507 67
    0x1581354400e480d891010f80c3d00b1070525182040e612100054200707161521410281919940810b002c009881c000743d41045101301913640641140d00101414103001c4001c00070100c00714084030000420214850301c0701d030005881580000007500802e10b0040060104051016641c00305040e600184e12940283c1c40e5880000c1c03d038100003808a0014881c81a0004908112502e40000d4120f0341045094243e0b6601c1c0d5003800f0a84100319400b030342000041000440c2100100c8100d40c0c0c10195010b005100e401d2400004481541c55036505030090b00c9465120601c04103111031468450704620000c0594034051212540d080000d24020a02c0320074000e0b1001d100381604824031b9000d44c0d40000b5035030780002070303034070302084040d103002200600e42080402c22850601c22135102c5818a004200a203181c40f0703040b4040d42c8070702150100c50b240c950303d000001c0e0007040309001508401c4105411141022810707401c46000a10000c1117501905118030540c032031090225000d80c0529203a6500c0015 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 104151690 1250 104150440 104150467
    0xe010e030a1d0d0b01060e1917070b0d0e100506010e010f090503011e0c0c030e0609060c030f0301080f0c0d0807020102210d0b04110919090203090102070213050f0c 72
    0x2041040d40e0030441441c2524200000e150711309050714010340392444002443c80c00c0c4095040391580c9024994041a401d00020307e80c800a0001c0c20400c00c01c40b0b1890392144210400d542010000c13041c8a41c4641e01c01084903024001d0300d282d078080080812803480c01c00d000030540e0403a404040c0c1131101010300303400c00c24414486080508070280003070200f0081a410300040b8800f04030b08031161407034110410409032148141c1c03022030350150b8504c80b140328400b0800c041940301060a59001404024901c02c105042c4094280d0512070302000391290302d440480c07820000400103070006c5401540a44034a40e44141103e0401074001584c1030300c81c9038910060380b60800c1c6240950038800c4402100100030312040c02080380396940d00c03060007021505070521040d141004c0250702c5902c2c0622040800f400c1803030940c94001e82500c0350072981c2c2c3da20039048040343d1050300e010a15940014800f070950511901d0000c1c030104280c810030032031801e0390103c400c42c000604502160800003554950401d035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 104152940 1250 104151690 104151737
    0x70503370f05160503150403080907030c09020406140403050a03030b040209040216020126010905070302090a1d1e04020d0501021e091305010b030c070f060609050405010e010e030a 79
    0x1800310031266041401d042c2039540e285982c032000c614501000380030800d404e010402c4041c0c0d15460400044580390741d5010354400d18000c04144107489a0940040403070030f441412070050180c0d800041c0d42c1d904014005103071100584801842c09001c02c000c01c0042c00014250032841d404d85030020f000e65850780060081d1040b40c2c09181c5c010700115490082c400d0f40b4a02e00d0030700f8801d0321010135200c014039000540004d41a03000e1110f0b207428004001c2e01200c1e0300440d500100e685801442c0c007841c4c00015040c2411a0003200340c8800e404442e440c0100210400b80d0059440b0540404011003001071074218400144000d010f80f8400c0c0001c010403000b50180c0750343c50704080c5805a20114503c203503000d500300071255840341d00300e1803440728454560320505060340e20158040b4915030b00d480c00c80c0e020394084481112074060310000354000ca8090310948000e808541c00101d1703d0706250502300d003500d050f0781c98460a07900d41450314164a100001305c4505485508025070166610490040c1440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 104154190 1250 104152940 104152943
    0x9050a0b0a141002010507020d18050607141207080f07021203040b180402030105090c07030909060605040303021506010504060c022103090a08070e0103020402030c0d0f0b0307050337 80
    0x921a0004100d0700824945003081e21019140600b0000c0ca8100132170a0b681c1c03d079241030140e000703030b80c500003c24402ca0740c1d440c0404407010303c11825661080811030540c800801500c181000461900c00c05a0a20003018024a01c0012508044107078440060380c2c0700750501800302010010702ea004540301c3e8501120f80204c11400d50783c440c0e9689422268a40c040007403801d0002050014950714501442a00d05a4201030726044450b40d405c02405030661022400b40c05100381032030006079421160003501d001d010349683e681d0326030340785160283c074012600c1d18009e480c1c4452003c000c66039030301406485c02c0311024504124106801d00100380c1c07000400019005440c00c001844008001c000010064840141c40302c0c4070250fa1983c2282d1900624014403812120445c0100054034080c1c0186070050040600b052070544603007900411100403640c0851966122542c5904a250510104000b400254003428442040d030b441e01d2a0719480300200300d81c104840c03018402c400541da04590140303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 104155440 1250 104154190 104154199
    0x604080a1b0f050601090b0d0f0201082e030210051801080c0f03010803030114090103050307030807090e04110a0611030304060f0e100204050306010b040302091302120a030507050c01020309060409050a0b 89
    0x382c1c40d03030070000d46940c424058500e05508050315842d482c14003081d680f4007541c002e14104071140c65507004503560071001e052400f100c1c160111189507000000d4061312641801010362076110718510511170441d03207462480d02800000e000040000d00074114584d8100c0003464900500e603100071840f134144c040d039400d17020000343c00700004c5140c100000055058a20203440869903d024004104540c0320900005110390001d21101001038040c6280c582c004040c0d041500e1041d0302c134407040041d003004540070341705000300902c4108242080101c030b402070143c1d1310b007005c0802c070141181c41d9030380b1020b08024804e035915074044254030fa0940c08807080700b0701d81c03080d2080003ca4410305801f039049401010700c83d0180400010b00d2070044c9048408a940c041e24840f065611094541c465002100c016a0441407130400403a813102d052000d0600240f094807050b4680c441420001e141c48808115281035500c1041028040e0b0346da04103590407038041c200041881d0b076030810700002a10504c05440c1e0003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 104156690 1250 104155440 104155463
    0x30f192c0c010c0305070206120403031409032d0f040608040311010b01270f0602010903081012080304050c041a0102060603071a0901020309130903110604080a1b 71
    0x8034104900c403556120a48022081540c14030594181c9802480010a000c28448035482c000070340901d000d00640e5000400d26030900c40e00454030320390b8810890f422000a581c1d0a000c0070f080d20590444c0d90000b034400c00550030246900c8103a0380001c0c1c0e2410003100c44031101812240f40650804030380e03042c40340b00d08141d1110358480d07010340655000d803002ca012400011464a2108051003000704074001659050300000242210a4603001800200c5000f854000004103500e90140306501c0102101c1d0b000064030076071424014100d000180c0203840002c0c80442c10820000d60050007942030340c000400d9556522185003941c035250810f040603030401d040505001d459602800e190030240b4003a020b40f0410394502040603103a8910b80100000103403443c0d4080680c5840101a143d030a00c180101c928200141001400b400080340240c20413035107400c00710707080503844007008801c02e180000414250400382d6407114a4003580707200b04104642c0d20b648aa90306182d0151540658001c0c418420 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 104157940 1250 104156690 104156711
    0x160204060e1801020f1611040515190e0612031902030d0c0305070206041104020403080f07020a0b12060402070c0509090604030905010507030e04052d040302070b030c030f19 76
    0x8440008503848106034070590094640b940d418021903036510621218103250900c00c1d40c40414525100d03006642c40342a048136508603440302c4c0305990003040000030710382c03046140c0c0c804c01010701c070309601c1800446a8078908002c1c400600c40c0c8150000d5044a03011501d940901c046442c2d0b00800700c01c00c240403141014038046c2c0c0d0300400140700c11010700b10706125101200c01706800750b44e82960007800682c003c1000a001c03801c0303074071180e01c100c100820252030700d59a0380324044640c02210b052100c03a038001880b90210700d08228264000c01400c002c46080c44804250260360040c018091070040d900010100200960341c1c218101074400102403600c14103040b401c050341c6002c2160128003003800340d500030030998000c40527203c02030b030f00d03588101d442c182c80414080941130140c20f0716510701019549102c04440105000384003880c08034070240c24541800d00070310780456036010142d4441d00700180300b40c029080c03040f00d5000801c8c05442c03800352100c0d4810b42c1b84d0411104d00303680c49840c0094615 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 104159190 1250 104157940 104157959
    0xf0902210c0406060c0210120606050d0e060709060e19060c03020714060d020d06090203130b010e0712021b0f0f0105010b03010807031e080d020a020d170c16020406 72
    0x2090385400200e521052182042c0421100c0d6030041d0300102d440c20062900601c1c0c01c19141c10180c503039142040d80300041c074010078165900390300803902080000c074441070f450002d4410304526804800040400d4100307106c0192840115004601c00c10064241030443e685070812040541510020320301480b55403040010201101c4c681e04400501400070006107601110072100420036000f00307107034901900401c40a0081d801506100c048580300c100001c0c0213807991014502c070b0200000b15802280003487c00300340300141600001c11000c040e4052141d9558000a10020540b1804006956604000302c90440309051401c3c0c00c113a00c5542c0c0c0e80c40803520085445060b940080000f848181d07220201050365000901620038980d00051040005c6030580c0e041007540d0f5102944500040c60b292582c06c25a0700001c851120070303800041c1d0031002036040000251a607580c0c904000542e02c81c10344030352240c201415428105402003031107140d0f02c50a01007941d650354010300400042d5a1040350b403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 104160440 1250 104159190 104159239
    0x902130204211e050f060c04051005040f0605220f05040f050c03060105070f050d080103110108040510051009021210170601060c15020a020c03070503011109040f0902 73
    0x4840501181c050741d031500309035000d02c02c1d0703030b03000c0c001c1d810111496503c080d400740400c1d000d0311244590305a03440385d1141480340138065041c140c0459540c030301f00303410b00c20307400210084941000401c0204018264659440c0016201c051400aaa8000c001480c1000301d140c0250b030b001300c0c410002e0000361329080a101c0c0c81101d0083e1030603c0401000a8000c04484045a80d01d640c01020000200e00b584a58018044244185c600c4035450326503448036454440c40b114800c000c10144e170010320030710a4124803400e1440c0709181c04240c40c40c295a40030b480d03020814100690311b8858020564032240e22400001509101e41d0840d1607542c022115a540c00040c0d07480b03032082249003001f04000c110507103075100c01000d081c002c001a03403030300e403040314254682c86050f03c003602c000c02d406045410300d000804c0c80083d958001c0a00d10405820541407003960360169210f60324001400c401000c104c0141d40035240120b03000100c20803040071000107007080410095005041000c141403d640308004c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 104161690 1250 104160440 104160449
    0x50f0d0e0106090209031f0608030a0206060109050d02030a0611090d03020a150903080f070201060302040203040813050f031e011808030f060402071e060e0618160f06120902130204 79
    0x2480b92603900c1545104911913020001c0d095000034920101075041d000c1e510001e0750007003030300141881d41c170109941940c000303910032070040c3c01400900446680c403400c24005084121961080c0c20341d9031340042e40c0c5194401c2c00038040342d2100845407442141105407800d8000180c0030206407806031038029116428050304503621500790031100c10781038080c4150000b803689521243c1c1103444d1243c00040b0030b00020401401c45d1b40345e140110041e00c40c1d002550040e4800d03c03e00c2e48501100802c0b9550754804e801150144403a51018141603800148035130b81d00c061f90310280500c107650405940541100e481241d81c0340201e18060041200d4540158800c01001180d4215600e0362410030050303200b890300180507190811107a60300c0401308440c40e050ba62162000140d00d4911050143c20400308941c24000a07010100d10840c81ca814088482109109820900070309c0c00c009080081184900503c0d040004588a056944040e0390100c24207540052290013a540b1116960020b541329005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 104162940 1250 104161690 104161693
    0xd0501110705070803040f0302120102040b07030815120d05070201020a02090708010602060a0504030c0308060d060e0c010207050d0803040b090f12280c02010e04061a090f101d01050f0d0e 82
    0x51aa072010081d1011385240310721844140b448c6400b040155160f540c41c1d01a40d540c20071001442034030074001042150720030340303a1840c01e207802202c23000d41d0007810000ea8058a00901c00c0e051020b0040b4034064070b41740a0a1854031052a030004030316003ca0100000e400813104014400e526400041c068101d41059086032480c1c1c0e150320440307040d175409440060124080480b19000a40150341207503000001602c000c0205440782c40340020b844c00c08109605580200403c0000c80d6810700ca08030285c0f0080c0c801403c1c125103941c035801740340300082000e08018400c00200312260f40521800c86003440d8101103c0e60300030007914101603a442940c1d124941d107014800002180710a150b03140c00c2c1c40c40b45d181d584401e0348130b40041d1448606201b0700d962180d0f0311719012400800c099503415007500c10640785501d9074102d50038031503034114081000e80700d40403007000c2e01e540a501c820003c2c081e560003904003d107070802400603276039405a40381c4a010054046a0460310108a6118400511300c810 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 104164190 1250 104162940 104162953
    0x3090a03030f09021216060f051c110a03060609080102070c0308030402040603080307050405091b03041203060b04090f2f0a0c06020406031e110405040203060307050402031e09060709050d020d0501110705 89
    0x15040c8e9280785198084d20124070b06006011803104141d041a209000b01030011a0030700e002c01481015a00080325000801d5030743d41c05000e0039500c00e41c82005032130401d000710b16000154680305c1065942d0321000b81500e1000002500315102c1e500803800641e804a82641c80c0e003003d100191260300a405958003e40908000901d101c0b80d0b24446500c51015034505442c1d904c8944032841080880b10760303001455251500054014031010082c0000c0a0040c0c000a030b17160504840f44c155100403d6000c0300c00c01440f01c440c6c4418001131088003840c150842e580e41c84c1c544036815a103035810000040c00306803010a0000b10260180c1014204100084094038074040700c0d400b103000c598217000340402141080c881400305061640c01103401c11801812079480e83d69410002e401d81e80201c9400075800342d8100641c0c3e03e40440c2d078003140c000348001c3c0070f0b02d03841c504030f071008100d0901d600c40c043c402d180004941096444e102030ba030f20701d10b4001300244140003406210302c655070b0150600301c03114071400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 104165440 1250 104164190 104164199
    0x3110d050a0e06090a0506031008100b0609060304060b041107030806040e07090b010e04050a0c02070902090117070507050a030e180105031509030c0601080706030b040203090a03030f09021216 84
    0xc0c01111080807241c0c0b0b41c90b5801e20b1010500801d40c0100c4d507a03070380080320715501040310390702c8002451080140482c0011500d05010140d4106030000b10000c6540307040c13a2540b0010b507036801c203449804005032007442c3c43e5031362402c043c005443c100f455140c00c241340c06100c240a00b500d00040c504580243c4510503607071142010b00044a1440d141020f003500002030a00102d66103801c503410010f81490031a0104211900080c101c440c282e403007000c01c950716079050007915010302c00100100311070035085060004100c0060840c120035800d458140e40b0000000b0042406032050b100f405401808130351640e41686070180c0104030030700c0ca040c4a01c031031882900d44c40c1c0c29040481e05907100a4003404c0f88400c02850020100000740013800c0c0360000f4001c0800c1b092003000704a0007806c40e10001d2031010b00d40b100240c110b4400c619581e000e1801007040010707171100003444407041a030501d0000b030302c02d07100c2002c50000c00c0000e0303000b9400556800003854200d0002448000700302c80e41e4020340d01e00d548 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 104166690 1250 104165440 104165447
    0xa0f0e0309090105041d100b0a0b19030c050f120405071a071202030c0a0b0118020414090406060902070b040b060a0e0103032609061008060907050609061603110d 71
    0x280c004155000d02c10300e0040c0110304090b045001268003e0a035120b0840d031076442c81d0b041c00420400460b03880e555800580b03035440d120350507070010000c60350603034a810f0707149a0500ca100c030340071800302c1455211241203c00d603100b901241c07061540c0180480e11056200000c404e55503065509031441e1103103940106000c410b403069441c074902003040305403501c5815600d060580300307006041d500f5800b080c0305e5640042c6003400546c00d1a44242c0c03006001e98145403c0c1e2800f00c01d810700c103a001a205000a02c42500091050390b070990b4222429051355032245000300152aa0b50800100c0c180086091800c100044a569020b18490351000201d95680428400f0001891240900c9012090300400c0864014910344e41e40d49403c00c1e1008a1990380040c02c4c8030600c0968860300203030b01000c10402681c50869019000e080443c020f8681070070240e0949542d44c826000c0d042c460f000000702166140e036001c1c12201c45c0d00a49104840721240c81c140544004c60840c00002e09004035030700e0a074082d10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 104167940 1250 104166690 104166697
    0x180b190605040506130e01022802070909020105090d0f1203020a0305060d0c061419120f06050102071e0e0709060f051c0f0e0136050a020907050f030a0f0e03 69
    0x5d400c0032121060040c5000c090500c2008203503e40d58200310340552000160269180700c62100d550a1140c80100d50092501650364001084d10f40340c0042c2c02d0050ba0b00004844200030225151013104c0020300b003e030044102083c009180c920034100c07034200c40d03030590041c00404040b0b803002c00032a036402003800032582410390010703d00827180d40c00303000d120b00503681c000b104101411800d08148507180783c450007501c00f00340e04000c50040b900740001811180165140204a00400c0c01814078080002c1e503610883d011703d5a00343e08000d0781c80d0341e11482004032802801041803118241c03c003508054450b5800e0700070300300050860b451000b0000c0c0114101c5100007600002203038000000390102c0c6c0203000400041ca83c060f02c035202644240b40034001c0786040e1002e02400106055030f42804040680036405100f104000c41c0c1c0700c00041b03500441e403900c05e69015144001d0703658601c4401c81700d6110307030304e114400240c01105010366610107034001c48604d01b0300074040180c2121440792580da0302 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 104169190 1250 104167940 104167951
    0x1090e01030203120f04081b040b010e03060115020115090b010908060c03011e0305150708090d02070302060306040914030d0606140a0c051908030406050114030d03180b1906050405 79
    0x3d02510004c030461103c40010890209031445c00c85c00c00341c5890302c2500300000e43e4194440001c5d240c1c1070700440d11b0a40728615201c20242403c01001c0700144c042601c0e410141300d080d15030714001010207000d90007900a01c012441c1d00e0303400810161580d07400002001b40d0040c0600052019a003c660200e0019015010b0780041036640d0840e841c226a2000307510406500c001040b1a170f4000100180d010001002030048614039010b50b490300740030003003803147c1c010690801039020742d9800e50203039000b04e0203805917a01030303076025503950f42d01000c01c000e031045c00b4006100d04010441010440c074040040e04281003402028414140d40d218121203c94000c1d80c1c95032400c0f4200a40c44103a80510208400d00d8032910a40d0809009803c0648854581200c1507801c1400082008104101c0d48911400340601400c00524009104040f0381c1c0c4040012050050590b50380d00c1e03850084064040042e2030390300c081c80a00324940901c1094000c4103140001c80c0c22401c0c6035020070145028000c180c4600b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 104170440 1250 104169190 104169193
    0x90c0207030b071403090c120304062102071b08100204030c05090907090213060e060403080301030f0c0e0403050904050f010e060d081c0b0a120209040605190f0b01090e01030203 78
    0x6045032552042007030042c05203403c1c800488604e90b40c80070002c01940c46407090801401000d02001c051100c05c440700700031201c4982040101344440d40e000b01e00e40076010180529400c00d00b81d0341d1640320091241020241c1582079481c4032608500080b014842a02d4001d416a0340e4502c1e0b40d440c8009a00071408010b0841c00c40391818080345c00c04030384071a48101f0000481c1c511039134481c840c2c0e081740d000403071025080082c5c96040c070202d60032140c400c0c1c2522040d100203281a1440d29900154001070200514002070460000207020480409101070304003422141c1c902c1c1058500a01903512802a00b4011405c24002a21144c1640c0005048506941c3c40c0580c03035a507030302040031042034000b0807500c2d40070502c40040b65211170b0041c2d00300c1d000e441000044464411041200c1081640e00c030803180c3c42c0e00c5103c0320042c0c4400b503038990401c0d800500410704e1348030719190f1451400408219020a803500071040402d00964121340c03040b480c20b032513104002da25407a021401c20424007029426 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 104171690 1250 104170440 104170453
    0x3160e061b03090d0b0105210304051504150206040c090c0f030b03190f031404120f08040503010c030615020c060f031302060d0905010f050618040c260106090c02 71
    0x70081d840400304004418080c1d918003420b4000003040d2460154042e645a5686401400b040c1007410b002c201c0c0c902e08014031856102080c0200fa40c0340b05070300480c0c1c06440342a014203c81007c01064a02070840d850340b00d085a000c1010003503075081c04035170698078104804400690703045144600301d030002090751250211600303030700b0030360192403901c510755010711500800c01216070390030000381c243d24802c0300440158815800d00524802c446aa2840e50100400080100c0803185a99548566100b11041c0103514242007205180c001d03a4022501542840d00307598401d5807551080e0142d0303584050480e88031900841c00ca07603410644c20951b1700003004000000000c4e0b50700002e540c0c04410480c50200d0300c00681d000ca91a80c200600c8520103989500c4003c0c2040000c1c0100600c402030030b0000c10840c0f812400064002614218a4030001150408102801541764a40c4080c00c0200e900071105c2e400c240200c007505000d4403016040354a800b40210701100280a40000d1000c0c0f580101003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 104172940 1250 104171690 104171707
    0x1050d0b01050c01060305010218040c08010e070513080a0210080c0a03020f0705010221010602060f070c03020c03010204181404080702090a02070218070e150307122003160e06 77
    0x400d124204141481000c0c8070400780c2850074013030321001e036200d04009038072613480e45000710711943e00008035881541804094912164448512411908105078107407045c2c80d18001590070744100d10420b00403041441000c1713941c003400150f0b01300d021300c20790300940b155041c90030032150706606844003c01c059042000c0203550380300341c0240c006040340c2030b6a640b8007213a569034182240c1c40036402c01c1240c4c4c1c00a03e00310003503808006040c0113002d00e0014012a10b0401320070fa60b5228010282010f0100310090101414402c012001884a01900865940c5d403100c40c02541c0120003d005502a4245a450301a03042c1002c640360086521070321160a0821940c20001c040784002c0c0590a031550900a00c00941c1c1d0b5210381f14034800404c54551308905107140001c0c5500744401c80c290041d10314410041c4610170340c60840341c0c094118a40f140c90350252030000d901030410070044680f115514003080e650241103a005600030180d2503168042d4001d800740981e281034644c511107521040038883c501 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 104174190 1250 104172940 104172967
    0x200102150604020c0c030114071b170c030d05151e03071512020301060806130203040b0406150512060a061703040506030c091c0510020c0c120c09010b09040f0b0105 72
    0x100e13500c4800e003501e003c15540000300342129804001082602d5610080c400032035049500a40f6184000c501070407122660740b10048421150000724251342e9002500310b1110905100390b5259110a10040c42581030514650340c0d4078511240c164400c000e80c181c100c036052444280c5680c0300d10054003406030300b841d10703a0308075140300542c429200740000c0719240c4120140c20700c000d41c0a80142c1c3c5503600542002c50500031040900222034205a204005200c00b156190f40c2d041d62203648190301242a0b0b45484056441188581c04250070185110303207020303c44404101d0324801e80440008111081d03403003a50700c0380350b5158000120940c10801040c84182005801140d0005103070400300c0c0343c819600082030710702140740349001340e1542d403034283d200704039040c80440d001264696080d400c1445451810351542403a21010307105904031611015455014007540b1800040100821803035a52004c0400b100d074803614849104503e810f01034400d24066100c0c03503902a034183d46450614146000b0311 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 104175440 1250 104174190 104174197
    0xf05040806131425060c1a06030309030a0f110319151103131103030a120e0c0d03020d0e0105041206050712110a020106050a050312031e0420010215060402 68
    0x1943d0700302c0c604808810154040029908040100340c29854101c00c11891030341600c03681c0c0025040040312207032030022560040c0b2102c100c05004515010580356000020319500c1203003c0603405000301e001450a11041032403444030580207840c08004484180105034590303c080c4d0460003d05200c0c24041c0208148a0f10301c2301d41610104005080d2000161b040000d410445000c001c4241300740c1c3c40407c00030b03a01405815a017040c2c0003503060142402014007411030781c00c510b403011981d40003000404d1234100f000c041c9000c00680b0a08540c2c581e030800075100c80a0002c80700109410b0380e401050380d40b090382160708841d85c81d400f0b440c40f02101d40e41d101c0982005032484040000c618428150f54607184124000080c4e03064003543d8680d00814003070f0070b558aa40c0120300c190300030f01d0100b010780c0740810240500c00d04032446a941703950740525958001e0f240d04011071000e0900c0e04110800803d9003500c10055014003441c0d4400f407622700120b1ba202c9030314460500303110144000c90b10710304154018 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 104176690 1250 104175440 104175443
    0x903080705030901061208040501180503070501030b030a080d06030c120503070b0601030b03060a2405100507030c0b01090203010f23092802030a0c0207080c060702130c0c030f0504080613 82
    0x10030156a201c250b01001000210165040080001d02704a20341e0414041900b503840c03c41e80110031807600b0002a151045481281e05141d158041c0004030340d000d100303034a001030303020500316110103d82c01326500402050200301c0304000c3c1014003156449210f004d421045500c54001e614140c880e94034503201c0000135091606040c1c4401d0b00300303002d42d8244140c4c1d05c18480702710b0000c0d640011040408803c0f201400c0d004002c0d07103001c01031040f030301c4540083c1741e0b400a034100300d070b980c0e6070b54038084511801e56400500080003040022694808a07002141210000580c10882d540c880110080809000c2c10710041c05607480000441d0342040380d0241c0d0300c0225038102c00a04003035640003051450400020412075a40081003040f81300c0244112100104c162006240e29414608119540d0100382c1030b241c4203800104400c02196100d090b410352035444100705010904060300080c00c0d03001081d02c100d000c00d07400c88512a075a4480c0c41500c0803181e0044c0104425290004035a2201d0b484580 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 104177940 1250 104176690 104176693
    0x806070c02181303091a070f03090b1c0f060b07150f0e0606030d17280204031b0b090d06021b0708070312030603170a090806090a0303050a09030807050309 68
    0x80b00764250750086554840c62940c40c80c801c4640300c91400400d45665500701400e0322003100b03041d00c1c0803d800c0c416603505039072054249020a4040c1002e4991070382583c054050100c00061000742c00e0005040c0c1d02050520b07200900c459a101d0202c0c0d4203503a1507000d141203108050107040081088131444090304040c0000000785070740301e207203840181c40a00c010340c90f5a038083c03810302c130442c01c003000003c42e1500c2c1840c1c1400d10403003050b01c035964030501070300d403031084001c2186c6821500c0c21003849442c1e8910141045548030b03600d00d8a030008080110010703034101c07022500020000044011a1180305006000c40a903a80c10f41e5400c00a4200c2800c4001c280300c0c5184660902c41c0401c54903028211440040c00d400e172641c42c1c060500008410480c08240c10250300f000090002d1000c28100502d407031649461b020b0113401110b0044290b03102c2102c0c3d2040c041031003d000e00110b20700808070f0099605001e5a501e051069080e00c440f801d004000170603170b0001545081c4544055904002200c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 104179190 1250 104177940 104177959
    0x30714010623040e010c09080c030c030312070e0d030c050606030d0e1215010e06101b060903020c090a05011a09031c090905041a07030e070b030c0f0d0c0905010203040806070c02 78
    0x42404c1d0031250545a280003165480d4002e1025070410060024902003c900900011490300003117a1a40039198176151041e11070070200f0b00c01401134840d0903001101500c9a440344142d03040080a289403190107a50303a0140c400810b400d030030302050300d08100d601616050300e088042400d0204980e0720a03d25480b500401c10701e8142c4d21121040d8500800340902407400508001d42048280c006c26038142c0140180144071100e55680110041d40035a0000000a0a03040f03d080580c105103099011b184d1149910040001c2a0300644c4114141c03000320754910080080b69038800140d20440403450f50641c0503202c80c2266a1200c4180303001c514091030006007040d03070380a0f28400e41e00c040d94100e5558039012500740c4010300c4962002d82c802e41c140303401c2c440d414500d8030b000c2d1505245d000b00300c1041c0300003000803050300001c1e040324030620302c1ca00382655070311070480024010883e2200b1a0001182014000750561000080d0340035a0f841c840a8001030303c3d050000d4804004c0c0e0314049030800c81c4403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 104180440 1250 104179190 104179211
    0x423070e0405010632040b06190804060b010f1425060504030e01080609060f010509031603020a151205060103060b0a0f12111c06031403071401062304 66
    0x44042074050791040001013000c42c01c025a41506041813507011a4081e221566070312155440b50207008000320913200040c070780881d4400718803a4031403d12902000d041000110040e0381d4400051031040717024000400203103811000454503104048108030024080e42c2441c122109100000e105c92140201d842c0c0c0000319060340e080c0210907241c0d059620550314010001415000341c0d1a0382407a00c01d1030522000d240c8400003c0940390081d015038011240700f1450304d0f280c1d000f0b00807101c0941c8000d0490b0b89c5070410701d40c00144101d81c1e00089000d900301c0b040c00207040c041660758030300c191002d48480c0354100ca40341e9188000d2034010300c07550425444143c0040c1c46000c1034000c1c500e12040b0b0391490000c00e80c51601511300e00d0340e130040c214401c1c030706854001c1e000c455400b80e0300c4482d4a0445100144524200c5201824490300054000581321303014620000002001382812882651100300301031503680c0123801c0340d031284181d49000c0b41c003030f20405e40321011050a41ca5030400030000900e0342001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 104181690 1250 104180440 104180459
    0x11b1b0507080307060510060f0f03060f08100b030a0b06090417070b0702010e0f03090609060d05010f0303141201120201180602030a02100b06090d050f0d0c0b0f042307 74
    0x120341c410209504005034070014417806005843c0d114640034a40d910103458903038020411080002514108018103c15a0845100341c100d0801030400d0b40b00d482d41d1546500c0d100b52616290b43c441c2000c21728298002070359040100340501c0440d0005003540241c1c0d9100c003407000d1040014012282070b14100481a400c010480c0a0003d250141c50700f04182c0c43e02440203401c440c9c5e0b80c110443c50b40e00400c440815803100000300c075148101a14520740702c03009031001c50b01714003542d80314040203401c000020802504818040080b20b0181d510391411000304100180d1034454401040f1440c5540c0e80148000c1102c0011b450b181d61061411305011600c8036800b0701c00075002e81141c0016000011860000345d8100806030104140d100200a8141c40f9400606503100d9100b686006e40c5078030762a5001c2c4003090260b2016003240405035668021801c0000f07040c04050b417004ca0300b14001c0e0010650b03080c9400078075445258080710110928401d8a01090903014010501c0b00e50f00c00d00c01e012404107038 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 104182940 1250 104181690 104181703
    0xb090f01120207260c07090f0b0a030605070f080108072304090b04030906030e0c130212040f15020301081f02040f080303010e010902090d170f071109060102011b1b05 73
    0x1408242e2226614511007202810041c01d1803611041c06110800c5c0500b0003049200803606584000a070b1907005020301c00c054000c503d44a6400701d03020b0000410f01c019900a64890f400c5541d510358068001201910500c41c207006503862540405402c1c400c00d04856080105010b13500ca401100c0014400017400f136403460502100d40781070107410721080540040c294005000c6605060202c8540500b5807aa503400b4210480d104840c1e205103200b001255504560174030002900354022031801d41009200350403045000c8030020030340d1403d07040f0303061a8820340e81a684030384094a00312300020510505407501e0503002a103aa401c00002800c20404540780d802404a0005551203616050122000c000c0590050312001d004003d10001552003002400701ea513442000d180343c5216000800080e40602c0092040c030000c006614810300c01c4402040c080c2c80300880c0d18004c950f4031013004900341c4005202495007038248942c03205440c0d02503940030204150700001d41c610912142ca070a0302c0c145 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 104184190 1250 104182940 104182943
    0x50403060f020906041d0603010203072c0306090f06150901030228080106030605180a03110a081204210f050c0307060203010308090a060e03030406050f090d050705031005010b090f01120207 83
    0xc2c105c41c0d00e101903046c001940e00050807002141146440701d80030b44130b0014050403001403104501c10705000007100b4411100380320060100d42c1285402003a1303c1e914100c114240001c1d100e24400640e02c490149030345615040040c003450400d900e19400d11134040841f460781f60058200c10b0300903454401c030392195401000000004614185541060012207401418030b8a001c0d01c1810000780100c40060161007040c1e0500e4410030741644840344601b0440d5201d00100400300005401c0310004c0104101c5004a01606000420b0460340341603490100c2081200b502082008031590b40700f60087c0054040d40c0150380640e460030f1900d50310402280d000340c000f2945500c02003800c10003800c040200360003504803030910144040c2003074000b90b41e031b000c0c0d1b111355400c001c40024010880d41c0e5000580d6031070000030349071030481d40d594940540c4178052030107061301a2084a50364120700d1001e0180758121200c400c00e861500745404103106014266030200e5051016039000c100c1040c01900c010140107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 104185440 1250 104184190 104184209
    0x11060c0a031d010c02030d0e060c030703020c1329030c03070e100b0715050c070b073204120302030c070b070c120210030504060b030304061106090706050403060f02090604 75
    0x41c98410500030100140050b45040200d18540c0300c0058038001003402e26070400d401c15035140d01e203080010320075105102010780c190001150710707000c01d5000107241c5086641200c07400460140c880004045561140c40d001901c00d969018200081050143c0c0000300760240986110100343d9022034a0304e40c3c1c0390b0040c803807107441204000e2040b1009811001070702320401454600b201c5070f2142c020107211580d0181e0314594400110318046034803411207030065445000c0c40381c1441c00e0074001d407552461080c12911040300d0748100c01900d40300c2071030008550102c0607d9060070300304010200524454407046040d84000c01842800300c004200d00c40c014030758070f014203549290600c0d10082e48807855100d0040800c1071982c0600694460b04003244c95000c600d00000c0350342e82d80c01d1850190000030070454040c04002000709059a100c810b204813041e0402c02c1b1039058440268840d40c8606a00c04c04000030030602c4240000790050300504186014480d015090a040000051042d480756100c540003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 104186690 1250 104185440 104185457
    0xa090c050910020d1403060f0904210801210204090813090605010c0206040e090106170c0906030d0c080a03022209050a050708011202010c17130f0602030711060c0a03 73
    0x4070724112800b0255800d052000e84400382c1d01300b101609890b03043c0e0091550303100100000e80700341c48249049095500040c585c1c0420b0805041c01001040c1c2011610801041401e00c605801d00030142c65040f0380205a14a4410303003880207200b6606c402e21030490f80303e51207202e044e0100d042c0b100548a2000d271104000c59071880c0c10b526070b04032800b07540f1541c140030a8410620241c1d4401d002c2d902102d0a403038040d01c45698180c0924010620758010324a2103010006200c0349000c006500c50601034240c65200d400d4a8800405607240c100c0341880000403e1a0302410010b8500d801810074851103082c05030030100041145064400e0100d030314044422640f00403c12541d40b030086030341056501c6010025420180402024040e05000d40491101100078070400c41e482914040c20007034002c10481c80d801d0708084184003070ba004200243c42001c074000d020680c0c4aa18403d00700301d64082c0c00035450301049507107400d1503054201000798030080510603c46204410310540122318403907601e200701c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 104187940 1250 104186690 104186707
    0xf0601080f011407030b01022109010e1c0303090309170307061b02120f040e0a02031b040b09040b0d120903050f011a0f0321070b0711100b0a090c05 65
    0x15181c0c03400740c0c19003540e0601c0c18a90014030311851541e0003900d1890041820765076076006230320700010064140f400c210060009040410558007400c40c4020907601c01d0040a1003504209a2200310a41c03000f0101000304030b500042c0c02613120f80392040c46802c0803c1229610002013620b03120131825580c240d007000410204102e580e12941801200d9640e50304d4001340350540003582d03520644400b0030001000a140c03840440950280c170010104041420242c0c036091a6a90180d0001d5552094548554005562141e40c140a0b0f4007600d024000a604041d0040c0801015080e1800155004040c2c0c00c805000301d40031b1400c910644c0400e480d40790740e00d855803801a1405640c4592005164588070b040250818a0080100c01d000c088607010703001d400c8400068140200351441488101e02c402508200d00080b5000d01030303031030158544504a554199003900c50302c4504914a0068101d01c5045d6110182680564403400d0082c0200601d5500c07444010101c070b640080b8100850704c040380c3d080c07 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 104189190 1250 104187940 104187943
    0x2030610030b0f1302010c02240d0e070806070305041e0503120a050606070b1b0a020703030f020303040b0406090609021e0a0b0a051207021c080f06090411010c050109050f060108 78
    0x640081c1d40f024060424030f80303070840c4004241220070090410080030b40401c155610003500a00c1079a000d14030200391503032100030884075803202c1c01c088a814184081042408008031303101044982d584050170256840c80710423002410010002c50b40090441056840039140302e000c151928400d000550380c41340755241c44003602e10024010140075080008001158a40340244d4458560001c0240040e4951725602c44030300014031210111844041041d40090340d0000302c01040328040d071114140d211b0b078820226100d01c070450380545048044408100006c0666100d0804280120030001d42d030703c0716600189001042e024a0703600780300406604e08035850f00c00f11150080c85420754182c80c080443e03201515a016400760444180c0080c00040c0300c0e03500901020b4400528000c854031080b0301d0300d101908840007030f074085400035a190005036260800c10105030041d500810090200300410300115071b001c4044008442c0c80d5200c1c0651400030340e08001c0e10740d5403034038440603005a605084c60309 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 104190440 1250 104189190 104189213
    0x50d150c17060d05030f0a030f1104050a060201020a020c120c0d03030e0706170c0310150503150102010903021e0c1801060311031504091e0507060305010503031e07030c0203061003 79
    0x9109280041c03141c3c002070000401c840c07030300880541e901e44840c0c21303030b405400403d000030701c4000c803500701951248882d03036041c000e01c107842c8102c0c1c1d01d030503564440208900300c0c001e11310303200d02603400a141403070340b482c141f060305440c0d1400c10121141d19030b8980209040c50101c41d021400b0036114440f00c00e034034034184030703140180940346800052409003010101d08840c0240282c1c01c2c0c1c260000100d4110080ea04214000c1e09506810300d400090584005000303a00c11100050f0346008050744580d198418014480d10b640c06034000e00d0a20aa50b140500401840d00b401440c1d11130422110005e859007501e04000c130907940508030071580b40c0303c401303400d5441e4040e564060340010800c1007150503071000446071226086d0f0b000a0000c01d985414a541c1480e03c00390710070b2533100f0f030800c070410070001010420303036040c1c0d601840180d80c1c48090580e42e005401c0b94540c403041290a00c14008001009007041b03a001c0c0c40d040709403030695000f090034080d0a40d1940c10003605840f0074014017040c1d9161 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 104191690 1250 104190440 104190451
    0x6151801020d110c0d0206090901030302101401151409040903030603050d03020403080d05060a17010f0b090106020706120603020d050f16030f030806040906021305130c020601050d150c17 82
    0xd44150f11255014584403001c281c1c00754400d0032190311307250554a800094501c05032015040820550316810301075501c0c0d1403074000803281030502401d94180c0c004c1c1c0d0004dc1c12154401c0106206a10881c0f02743d8202a18101d000e020407070500c02d080321690765001b58088503001c0d450000d8101c0c1181072180c00c1c03200c1c4d4a0114185401000100001003500086030111581c03150005680d468800c0007a441c0c000a902c0040514841a8801c1d070000065121215805d00000704202c20540d07501407000a8400b4403031107001d600410000c0140300d004080008070300c6402d6500083c5551a0f0b0700040003040c654009030b80d540d10000c5110f0660038100020750340200c0b99103070009040e117140c0d102020840061002000c0205800114032181c8850300441d4103070b07910010a5464000c04980e11541021510070300f403054040000051015545115000c0c2c0b01100e0b5002d01103582c20403080c01100d00c18035034126a4030076a8803059000f02c0c43c81c4200506c011b880e5665400411241144800c240800341c00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 104192940 1250 104191690 104191697
    0x14070b0706110a090501050a1e2006070f0c02010201110a0c0c0801020c070501030b190b0c0106090e0d0807050c1501050a08160303030f02040b040f090c08090a030806151801020d 78
    0x43c40b0f141501300481c0b10446a007441c100f5520064071208507034001e5a4031490315041c008421095060b904102840c1054240d013010314502d0704159050360b50341b801980d0b0000429404414144801d00c81c1e08000b022074018000450112500805040c40d036116545d2039000a030741098040400000c010600e0040003240000e5052594280c10a070b117480061160505060740c81d40c1c0b000c6680c40d01c1c1c0d040c40e410303115003500b0031000d907545580700c0e030681c41840309164a51070f190021070300c013100384102001c0420040081188a4403480c00761000c61020b0300703050038031000380708800c080d5004002c01f44042c000c9806103803030b80d490700300ad000540e1410342100040d50410034807540002e40021416007103d4040c9400b042a800101c1408020b1040c3d812a594580d800a40898280c060f0707088681222500320701005400e42c1c050381210002000d40324a05039801035071056010a20a60502d81c021304010484401d081c401ca80c6280c191340024000c8042d0340c18031001c40e84540e014019581030000d20305 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 104194190 1250 104192940 104192947
    0x130e1e0603150a1a0d0507140a0f0302060c070320150a052b060909020a17030301030f08120a05090d080709050405040c0902120a050a11030402090414070b070611 71
    0x19100710300c040003c0c01500b46582c1d80341c858070b40e0b201c00c60203c1d4103000003404c030300318083d0181440c1d5210040c2d0b00031000030005044071060395060040c00340040780d06282e60601024116400c02c012035001303014448181c4148078010000c20741d0f0010f09200902d100500c4003400101900b03000b4444050b4080d46c8004105001d24140079070002c0442d00b10150005040c0a2501803808100c0c941e068030b184150700d58039103517011900d40c40a60041c04400c0c02200c41c525000c1c0c0e200c030200c7c89400a40d4401500350030a00040000805114070945c1e5030307204922480c02d00306101629549240100d551612490f00d4005001c02d1860a020f40c000521151030001075078a4126000303448164076115140c0500d0b921400642480341000c40040175000318041590f5030341d0044101c110034034094800e014007e01c0c05011412a55191049080f9011800040d508590300c41d004c101c81e8190080c4140c660500100d45441000c100388540c8001e09010301e911034075400f03642010b0044031520b000d05103100d035082 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 104195440 1250 104194190 104194213
    0xb060a03030e01080405070806010b070b0112170a05120f0403110604020901140105040306090602040e130b0402010c030c060f0c170f0f06150307030501050f010309030c08130e1e0603 80
    0xb6100180000a00388500640c549182952034002180c2c00320040d4001c0070000b041103240000244580ea00034085000c0d1030762100311701e1924050310308000300108894a0482952200c240145c40d50130f02d9804c01504107110781c51091003207641180d00b003503001c00c2230080000301034001c5800e8204814920040c034203481e15030b010070301800c018040c0c0e100d4100c0700740f042226a8403500c101d81c040c5911002c01c1c40741080d24605100a500035005045c1056010400038442c461005240141c40b500403601c0341042d00c65400659031201081c200b602042810150341c0c003c50030a024072500c060000c0c00004110410500c003d00c0c802d02d40c000034031f400e440e1030240005082071040b1035400c807003096010010307519803800192446070b490340520725034940403007001449c0790103600c001c2c101c620079a51000340c2c0308004011000c8440103c0c0090205580704170001c081003682024040051030004080401c54403840d60a000b00c0d81110002804d40f80c5c2400d400c604031000f4501c0f60819070070380040c9118680c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 104196690 1250 104195440 104195447
    0x1308010b090a0213050612040308060306040b1b0904020a09090c050f0324030f0d141c0c020106080a24022508090a0e070206010806060609040b0420070b060a0303 71
    0x19081c0710b09a500071480303040481019141328001d1100420040e1b42d40300081018500e584112415030100f0300c201c001612504001c500184681c1c1e02c00c0480310703282e8841d051003100c856009842d00c50003909000c10f10444d15540b00034010030300c0d2901d40710802c92404c010341d4240c6607403415040402c64103000e0711203000050340c10341e40c201d41e44080501685408443c522180604d9101c41c942c5442444070030001c4c2040843c40740045032050765080101c1c142000300040a2180703800313040e401e10761244c0003000d460003540296400b00607032002244540d41c44d60100d05d08140300c00207942009080074804105d400d40b031003011b60303035841e0a002e604203210650405004003590144080d82d01004e03503003d0401102600310b4040040c018a40500f00d40c5818914410340307130882d652005031084070000b103480710001805a1080c200105070602d817078201d81c140000741c25100e0b441604162a00c4505d00c80010707084104d207150407816410703500c034034541c14510b400703407000b4084038002d040807002840402d52 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 104197940 1250 104196690 104196709
    0x1201050109050f1212040b04060909050609040f03020a0b0901140105040b101409040c03050702010f140705070204060305011406030d1103070b2706070f0201060f2601060b1308010b 79
    0xf19103180300d1091004d05681040100110b64401140004001c18902901401340c01504c03156580c0655036074695813030104460b0165015903002d046580050001130441104007400c510a1060307070b0b001251541e80318041c00040e903035601d40d81d44580114107050780e140591401084202c1e024040038004001051003084030050803001c0081c40044a443c21022500310382c00d0000241c0200308806142c040240100310035101c0c000103500704849022107040c42c0c0038503110f0740d1000800783d07040c0d2603845003640d069121718801c07a005515080000040340c401e2240c1c0500740c00c09030700c500c003d24024041501780300d00140580c0c11305ca02081460501100041030b42d00003039028503c1740c000c0e190802c44400c25903400710f0b0030031500070b0008140c040c4080031804c14050b0744107484001c6260b41d000c000760b085c4c1c0c48901400b2000200c0c90345c100b01c0e00c240000c184030030a03050f84000500e03004058a640c2940c0c166081001c800744006080000c1c101d201140d9001020482c00812101c80d000000401550 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 104199190 1250 104197940 104197969
    0x9050d09080c06031b030c070c0626280f05040f050c0102060f15010c0b04050109060f0605060304060b2701080709020a0e012106060917030c03160f020a0902120105010905 75
    0x45d02000150000c0d808030216846903803c4058030088542d555001442c5840e02000b015501107030b031100802c2040d04d010708500400c6030b556260300a003c940c010146003c40010402061510340b0302c0c401c0344030050311415028a001308100702c038849007401e00310b00d8004480c500034110350041d01082a145110600c407500071b181c80a503400488074410040390302c000704040c042c010700c045209004c10828150b21010140d445240240500001c0c101d26a08540d427a10400303401241c20000500001c4644e8400801c255005002801d400000701c544040d400d910340c2400c020101d03240050190b08030030400d10000f012424002d6113483c001c1140100038420703119056051000710440154442107070000c01c0c17510b100c03151341086043e0740c50b400200740b4455031182080303691b024030103e85000c0d0048100c1d1143c2900301e00a40c42c282d100800007840c540b8884042d40c0030070f501903134180140d58210b60100100707a140c03c090f807542c03103000705581c00c50760607403010341030141c240020012515607024458a04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 104200440 1250 104199190 104199241
    0x30c010818030415051e1603080a140108060414031806070507150c061116031809020d02030a0506011d0d1707030c05060f10030f050109050d09080c0603 67
    0x6008085441d4514000c0d6004461450348400f050440780b603001001e0002084041c01513913146034210038210007403103040c091010000301e410582003c0fa014080d03035604a8003000001512011003491902441c20a80020040d60424001c1c4020700000101c1c3e07880005d101400303585400c01c54500d61400210302500c2c0d07400f500000c0307410703002c1c414144034000041400e2100044802c07050300d0028080548043c0480300145024091207100c1d50200c1500d1120b034a4181c0d0184051503070700c00351846040002c0310f51844907140c07408540302007203001414503031055481c00b60700e0307062100d0b1020965000408480c1001070301d029061080740421a503280d114001e5a03921602011410420511214040d107005600000118001003651014031380740070381e025000381c0c2c8168456a1008000c0041603988442c1518004000d001242d5903185440880f889400001901199030b51500c0c2052403030403800340071a034050300400c254641800348040c1074004603002491032500c0c0803851008403184c0c5201410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 104201690 1250 104200440 104200471
    0x705060f01210f0606090606140f030703020c0f1914010902010905010e010909050903030a060f0806010308090406031b08010f060302060f090a0e0406051b04050d02040504030306120b090c030c0108 86
    0xb0b0003646000c841400390414014003001b62602d00d4080503040301e01c1140002091b4402008403620414140c0b04032000c540002c500e50b44923408220f01940040b0b00210040c054903040b200d211004010981d003542d20b04c0320500d0208003034144031040380b1380d40310b45003401e03414801d241c0700607030b44202c072101a90800d00f00510700300000c41c01290004900c0e0804079a1920300014040c00c0d1100202841c8100c00750301060000c01d48500c51107c0440c014440c11001364411001800001c0050000c0c12038130304060b01c0064203030740da925080400d11320500380e00c0c1003840450051100340303c00e000d0240204008041840b0107459503010500e9031060350b03050790f04010b02080d40400e03551084074010041c940403031000da0b241050704256004103400d40b541040e80c0e040940c0b0071212120442514100c5500800c01d0304008441e0b001e000161000800440405640c0c01001c20300b0280d0b481000c80741030241d40051001d240402805143c041a8005503100f070380b00d24400c003460381e40a002a6403120400c404080c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 104202940 1250 104201690 104201693
    0x424030b010f27030c240206040803060102121803010606020c0618041b080f0f0103020a09050a0e010612020301050112020d080f090301091103010c0f1d120d03020705060f0121 77
    0x80c9840860410420000c1000c0004144161740c0b4407101178580329104241d6544038400c6070380c29401c1c2403841601607000030340000e010451000145600c00c2060040c1e911440d102c0d143c845250388002051000d888403500d0200150409201d0000070303105600003081d90b03c0889000640324016204072021040040d00d6088150700e035508015510024019810101c908610002d8440349040340d00c10b060405000010720489400620981202c4e0080c00c440c840900b010100c0c13016010062280f0120740d1104012003052000348151001000b003804600007407080c43c070416096440c10b070302c00b40d2035030144042800940e58608480c24810b6000209076070362502d11403011050302940d0030341a403551030517a034202030020715848142018401c80080280d86400314060b185081c241c00300c1e1000450711702e11703c1841840091030048604008040300501c204910b507991800035034004050002e80c020480e8420898200301ca1a041942892010041e40c1418081c0341d04030100c0850402d182550090b410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 104204190 1250 104202940 104202977
    0x5030a090f06020a02061b0703090603020304030c020307140102010f050108060703021c0f02120a05190f09080408100608030c1c050d020c0f0705040b03031b070b0424030b010f 77
    0x504250b02c40c60964540c14410f50103920303808200c80380c0d11404a0645481d140d140070304d048032103c0d40d2507254280c40d5814920220029040200102d007071140385000b44000d82e90800c2600001c0065144821600c0050000203094401d031700c21000c007240c14076005004140e008100b9a0307200140d4900180c443c4040d81105001c0e603c8101035a0809181c40c03400ca098002580050040409045604034151118440e60302105d900720b0703a4814031856100444090351058000540c00003281d400801d01c0210b0762104400307640990301136001c0e03500610611403019002c1c0654001041191b0103582014217030310010f0740362005000c4994440409020320b00c41140500181c45103c400c00d581191205001900c0303903034916124502600509c590580018245040d0113840c3c0005005400b4500b09052401030008094200004007094010641d011410a0740c1ca4080c20051018580080105c0904055251002c551072488002c00d0304141d246140d60b600000340c21144442840c180c49041114000c51 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 104205440 1250 104204190 104204213
    0x20c070b0c0717010b03010b060f0a030519021206030d0309020d2406080307020a0504270f14061509010b040314010902060a0207050102060a060806012105010216150c05030a09 77
    0x5180f6404400d010102140c0150700c0003854060079402042010648010046c0501500c103800c00103890420071a01403912076000140c10100a00026280701608030f4518184d8001c00250646c50346440100061441d00300282e080310507190a040094030030507008200e011045c800080d02100e100390803809248400c5001080c0700010321000c01c030050f2650f620b551240d121881c01c1c0e20404a04401207028541803040f03001da00009049100805d1250380410341080c8140c105840418100c1c10450202d007000c1034441007810018090000d40ca807a10318801c080540042580c01041054010300103841d1040c2103c0a80303030000e0301c11345074440140d0011702404030f10780001e40148001c1601d0705142d0f00000c0c0c4c0400e44809800750741c46691200c8159003118031501c2030400302c0d8004001003059000e450700032910b00039030311a042070000003915007030f0070790348070900c00911610703840e000703070b0600180310214159813112400611000c0b110000080160201030050b403d4107544614840030400d00c10482c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 104206690 1250 104205440 104205449
    0x903071a09070e040f021f030e0601050307120201020c06030403080405060703050903160501200a0e01020f03041703040b210612070e061311040806010506160303020906090303160510020c070b0c07 86
    0x341d145060168054910111720b4107c1300042820b00316010300c0c20501040c114182e64026004201c124605460706a25080381001a030540c0140a030450300c3c0d84410300158400e41c0292505c101a09151400b54075081c0024680000c0603d08001d00c009184040200c4654a15010042d011171380b982c1400c03401001086550080e00900d1004000364400e5000a800301c28603545680030b80566040042e620303414201520342042d0000c20060104070b1100c1c4030b030704005c01c00000301da007010f803615001c444560003450310410510340c40c610704100d0b140d48200039900c01800c2d11401616408440d145640d40ca680c0503054449410a0002d8000e480d04036103100c09082214052041240d036071030240d080e500501a42103140511000800c1d2402c02008541400c82510958601c26410340c404800070341081c01e4895001a0800030300e102e41d5800c001801d24056110702004000407a031520314034080e40c120174100554018094409a150081041000c5400b00e03078080c1e036604d83c40c0c06040d0511441d500b1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 104207940 1250 104206690 104206699
    0x180c070b180d020a020406050a05060403060908120106030b0a0609060e040e0c0409080315030a03080705030a0216060f0b0a05130b030c0306070815040614040b01090b030903071a09070e040f02 84
    0x108010b00d660000e02c5680e41c07402039600304a025211b10a20a508601d8005e850b0044000c220030000940d150707010541450041c00b134035082007140c5030700c044c1c41d40c02079100c1800a600c0e41800c03251460889813410040200d41007003050249011000307440200040e4205214940c2c49041000c000c50a001c0344103a40d03001842040074107071602d042090390304283c81e4841040d1092094041038140010b004c81c03242d0300360700c41c503c090f500c030281244c0e103510091a07000359079028070901400351805415410b030a441586d020507011030001821045500b039040301881030315250b01c1002540c0f99510720318102d1030010400701d014460100420300c2c1184129036290540b00d00381c104513510358400c80c1140101e118800e0520b90302c441e0344c10001a11030602031f5101034503100c1001c0c0d03013900e0141d00100c1000c40606258010f00d95543c019a0540c0084400c411309410015000d810001d0800107100d11456074094100c0c0c0c0d0402d090fa0b07640e98011390045140d66240301d004501800780c501e0000501560060 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 104209190 1250 104207940 104207953
    0xc03090204020d1401121109070e0a0f091518020702061201030b04020306010b07080301050108061c050c01020d02010e1005040c0807080114070f02150705071a0105180c070b18 77
    0x20103600402c00040c00d54904d009040010500d109400d07514401181c0040c9a00108091034080041803200945100306101d00707000941c0035038a40491000040c8241d00380c030011549810300e0403040d84c03581650441c2401081e101400408003030f0a014200c0404450016100c3c0700c1032010034001d11844007401041c0f8071000000041000002c4040d01c220310075816181c80c1d9988100540080c0120200285001800d00052000f5403150158030f178020401000c6c0d5141101e020482c10503654007400603690b54001001410702035804008020411201c0c2c0300800000344080852034840561071600e40c185500c90021030180402403450380041c0c1034850070346131100c0d0b98080a900814812491621681c500c6001072045030080b103215003a2030040e00641042c00080f0079140d04104024200410f0040c1404041c0104081d4503030580d80841c84a040d08031075042004000c1c01d8440c0d80804400c28106208110901c0c80c482c0944003206c0c5c0c000458515605e900707140c440c641e90304482841013840f650 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 104210440 1250 104209190 104209207
    0xf020c010603020301180f080f0403061a030d0e0d0b060d0804080d02070506071505091f0501330305070509060304061406030303090a030c02060c010c09060305160807030c0309020402 80
    0x1076001c0d90841c1e02c200c0c0200200c4d25904405100864218005002241c140c4a11408103070914014501c03020005030b0149041c2e201e5503080304a0705c2c5020f1031418000e400031301d1a0ba40c1401c1160b0104500e4500348510b8100b010000180840020400182902c0c50200800c010741c440c1030080b0034082d48041c880d82c4541c6c4540714107954004071404c030001403007400e0001450781005812a18865080316040d102d031805002e50358090940903004034910b01c548411f0701658424200715150341c414450010585501d02056425019001042c81040c1900410f804454000c80c0058002c854000d05011030b0780d590310f2005031118012600f20a4200e04004100320400ca500d900c000f442078644a84040075131558010703d0b64a002c111140d0030642d00580101011900552012081602c014881c42c03401844c00e0307a890958408880c0b00c00030400511081c4019501800f856a018161060004078880541d500030300c04407000c0e08005c24196034952040005102c4d0304150381140d0098000e554400ca070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 104211690 1250 104210440 104210443
    0x105090d170d14041a100e010b0a03050105030102030f130804090203100816080d030f020d090b091c020a0311010207140601060912150e03120106080a0b030f07090e010f020c 76
    0x34079100381842c2c58502a04843c002c00b414890007075030030206450540e00328110782050070a000d80a550f458407a0300c1c002906085400c1114040c00c1c2c0041641e48400c08070708094142d03a01a00a41d209074010f00820404040341001c007039000c0702800d0444030200d00303414801480d10550300014440750001041000c0301281400b0102103840399400c45a5400794443c4a501c080c515005011441c0c02429486075454443c0c0c11180001d00c00400040c82c09042c00300440484040f034008880701c04000c03003001001c55041c018402a500039024420903800ca40f01c1c029156104038500600b4080d88107100701215500750705540341964450044001d02c5c080c001c01540c0d444007480f13900001941c414000c149034288201a036105036205240c8404061304a50b400043c2540000c002290f00c0f040c0a500c0c00c00c82000300080c000c00c070b252640c003518100b00a03100f0645a01c0200301d40298806030140c0c0440000040810031110100d20000ea03900c5180e802c1e80c0034042120080c01c059001241e09003a8440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 104212940 1250 104211690 104211697
    0x2030c07140a02130b0103021b0a05010b06070b1b0d05040605040506070507050606061608030705040e130201021c02190305130611060403050f040f030809040b1507020105090d17 78
    0x240341c96600606510700050b03076451031420000d4000c0003a808240344015280c01425012205050150400881206051412a02c2a40c0c402280e020701106000c0c8042803040c0144684282c0741d0034641480c580f50206a500090040d40b10003182e40ca65540b816505000c1d100307864009e100a1180741090306085c0082e080c160703015240b5004030400f0840c254050700c02c46403c02e6010026001e569603c00800003960448070072069041440c0c1c6c080d400141c280c000a51055034944c640b035480b50305200d81c00392070403401402140070484100660b00980e8000a41c2004090040d0814161260a030000c03410701a83c442e05010740105106132004054000c0060440950b2017038200daa12031342c2e00b1080302c370281c0803003012095410840100380460321410040040100d00744400e460706030340d400041112121035000755103225020903c440c080c50715000d8084084030481d030b40300c09040700c0300700e81040c1e00c2040c3c4003e042c8100044e0030750380d0b52250600450340d5500030602c03103c01d464203103004440d6071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 104214190 1250 104212940 104212943
    0x309030c080604060c110a02040506121f060501090302130506040e010507030209180709030b090a1b0320010e010c0611031501020f1207082101030501020408070605030103020d02040c0c050102030c07 87
    0x18108240c5095943c45814640b1106d010207000b00743c107512507000e0000900340500b13207940003805403180e508014800c10260503c441d084c00d802043c258011401800c807803064001504208861200701b000da6a2204014103002d4000350000d001e4030b810000800810fa2010761011650900003000845d9805134040c00001c6c20130b41301c41d400c0c0d0b101c0b80e039000c00c000811103158001c542000b06c1800450a00100154080124021a0360013011034680e48c003468a0b0000000b05801400c20a00400c41e460b000b483d0078205400c40c1c200d51148007000a410400c61040b440c0c1080070740b0040340b044c0881034000100d1000284e405d280e413428600c0c1c081e07600001740011540544030308a41c401d200307500090800100c55030125402d05201e041e0f0760700070080c1d004140100140703416540025120390f005008a000b58407580005076520310f00a1100d080217140d038040c00500c10180010000b50712410081e40207941d04407400190054088015900d0031100c42c005081da41c804020009140100301c001c00b0312a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 104215440 1250 104214190 104214203
    0xc0a0e21030408071a04120201020f070e061216050f030a0f15050c03090307120e04050906180c1c0503040f06050409060b1c0905070b0c011401120201090b070309030c080604 76
    0x76803038460507034120890001000b0005c0d02040100084001e8030310303c1070000d10500c10340d40c0c10780c45c40da0101d00d40510341c2c0000c4612060241031100c02e2800072104800540004080d00c811940f51420b040e48019a120790b6010b1a080d080c9040c4136038003030101442041c1e109200624500b914142510007400c0c7c0c4c0e0300c0c180f0903490100410a035008034400d4070f214030303480c0340158a0002156128802441000c890b003050040d01c50103101c4950b180d015240c801d100e1140200618907141c000d4007454015201d07801d2103508603c1d086003181e115103600800c41400c8142d580803103101c40c5011841d41c442e940c424000c5100040000c110b0350b0b4420b00800840b041001c040c4003054668031442002e1040b41465042200120803003030f003502854200b0080a40940180e50506503903000000c804c0c3d122014440031039554110b00340d851015078041a01511402c00c0c030765052511680080c1130410b6034058400c50000228003201054450144070015550000e0304882c82980c03034a803207550f0380c810384e0200d031036 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 104216690 1250 104215440 104215453
    0xc0d0207050a06140d06060503070210020306010921060204080f0708011404020405090a0b130b0a0603020102150c040f030303020712031103010902090103020c010c05040302180c0a0e21030408 84
    0x11440000c0d0039058400051101e086946061001e03035021003a041080d440c21010320901d1620703405481176030700074071013501c86954a180060b0000c0c20041407101d07100ca16441071090200b56644055171001740c0301103c1100e604140c1070080c85820000110b0000d1105000040201d11410045424542c403e59003045820880e102d03c102d60036030300700e102000a002e4508000a015181c250403031900f2a001e01c05660850355292030b4416050002c4070805070000c002e422440800c008541b40e01e91020140718100001070035540000d4450018030341e40754094a40c2404500300160180481d0001c00311010301d0303141c1d990340349400340c042d41107100140d0341490b070884000055806401680000034044640c28516800e10001a0007034220040750382c1019802c4c050b01d400d0720750034410b51200d96a141c0315251524078500c10402c80703810702c1071b04c0c0640399440c02c28031182180346400d44c3c96214141c2000e001d4000c800000c292040c0c01c003d050509658182400c402c645070210051059500b0542590035 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 104217940 1250 104216690 104216713
    0xc080c0d0f02060103050c040c0c05010c051803010204050303040314100510090e010209090604110903010203010306060524070f021c030306030c060f09030f02040b06071101080604090203030d0e1609020c 89
    0xc0781c0f14248800307072181d04401825006031a01d5130007108440c2503070411582e600d20540740d103400c56410f840100d01043d0000744521082071880094440510102d000350b14050410010a407603018910000301898801a005804007009200000c0c0e18407e1080803c528941010b0241d504400340c0b10310120103140c83c9041c070104a041c001c440d074000c4058080141a00d400e01884020040f0f601c0c2c11020010a01035240113503001c0c002107000394050303500480d5050074a010003c40d0340391020b211806c2e00501140403519000030040d104480e400c003030034109c0088140041ba4070390303003600c0e070f0010307142c008000744010140c140e40100c0641e8081c003c0244032544801e01591098915415040403950032003003000015107003440310448510103080401c11415000101e00b054000b590120354070344040300e03640d1903968001011540518201c41c24451110f0b103801091700c0b0302c41d0003180c0b410b10362a00c144010a1a00700000110710703c0e44c418030352002da42c40c00044020341040316185014003880c0400320 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 104219190 1250 104217940 104217943
    0x10504170c13090f14010608010e0c030c010f0801060806040f05010e182404061b0f12110f0304061b0201020703030614220e010c080910060b09100c080c0d0f02 70
    0x10f0071940115148a1002c0315200c0030070707a140480d00e110301c1d50348941c5c000c02d1100d401c3c0a07244082c2c0c0514001c21f51068030034101030030980300381611030400010005a110042c1e010300c03080d046840a0615110a403640404135010b0180340b00d8048009041200005e680700080100c00d2040c45884201078001c00492000d585500501100b0342d441c5c26060401d4801100041246400c10702c54a40000c070f0004450406001e20344c0c2e25800710220708003095204a03150001c105030f1800d0455201000760341c80003c4004806d00446000400b01c070000700000b400c0000d40c5d403203500503e080340c440204803440750700020f01030f500c81703c0e0032070020b403c00400043c0381d00001c1381041094401040c0d141014484030b80b081070107040710b04074001c058a520302d243c0c141d102032040f614080303620358610942c1d2801aa40e145000442400c038041d9a01d03040301007000070308403015070b0748510301140c50710042c28044400315000061002d000d00318800025200c054024000b60420f500005520707440c1420200d000240d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 104220440 1250 104219190 104219201
    0xd0605060f030117060714180d21020d0219020102010e01050c0d140c07020d050a151401080f070608100e0f0109050f1501180308070507050306092109010504170c13 72
    0x1a00400c1d50f00c15104210024900a03144100c42c8e80d040001c68810300c2c0c009030451813250303403e0f034400292040a000c40c11005004444902040c0020a110210800001d40d0781841385010600005244020400c40e03200790455804000d200c0d0007404141005580c00300c003544941e4040d12000e24040c03030685409020040c5c0c0d40b18102074102141000002c5e000d0006606c408441200c05014840a010004c0d009203001101090214000140c1310b1401d650201460780681084610b80c1c010a4018400000014008165821860103a1040c1c4961151540d4019a83c00a0740c0c0d45151604101c00c040841e00c03224100c40b070f50b0030705105544075204208410841a2071450300303003000a6030307460700d235002d013035110904003205a00302a841c3e6039031901c400c01c3c1c01000c002c660f142c01c1450100b10303d240400240350800722581c05020b5035a0f0b001c4d2140e0080d241403810031641c52020401520603070240040d60018000f903800310380001d880302d101c181c071000864505481666004100404600c05200d02d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 104221690 1250 104220440 104220451
    0xc0114010819080f03041113021804061202150904180b01060305040b0a09030e060f0307140405030d030b06040b040807030501051b030a0e0a151505190b0d0605060f03011706 76
    0x3c00e45850412a07580c01694001082074070001d002c8074080c1e4540d224004000806d1401400050310f03141d149282c103c00f004210740e294420350608a06104504d80c0d50184000d00c0c0c0d0440b04140103411f0302d00354015074020f1426940e401450f00982d400900300c000011401540b0032000b4015682e00c4a0090341103d6007a10080c0103072041c1000610313070003501ea000c040c0341030190401300d41c03546000c4002403103548011200c880720b1074003005200f4000c0d00a6403050030301d440c840500b1300301814040842d54602c0000c001404058855103032000c251500022503019000c000b8200d6030701c83d290191550307600303010321040f6900c4d807a000c0064241c1095248003004d007107000012904e147c882c0c04c2020003911031440c4211a5006075038001001404100685000c0c08114001044018080b89011030103295a8092030091403e0030303c24151444c49035055003078070700d01481c04c0d844030407480980d0300074141d9402c03460b0801c50024542400001d450302440c102d510174090140000189810123440340d6050b40e8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 104222940 1250 104221690 104221703
    0x20a140909030f0319180f0b070c020919180302010e120a1209030e180105040c0c05060708130611090f010f08061c02060d0204060212070b06060a03020c0114010819 72
    0x11444e02d01810740700c80310b10710351000045034906c50241d0100349038115060032200008520003d0040042101000f5445851414030048101664004c41c103002402450348004a10440a08104001c039a2000c0f2814201c2002e000b8100258a400390003051000810140b41c4510035a47c9001020700048603034602c82a5607600d0b83c2e091104130034024194582e411005e11001d030401e14030f07a4844010100c85125210b15100455140805000c115941c0003285410490071108610100d00006800f613040909441c0c503038001c0c2d4400910450b8040803036001810319081411003a03c840550000d4006460122260030002d200140152a02c0e2086503c840109035403c001070700619211080440b010320b0f03407408001e81c01c0230381c1c0041c515502036440348980b643e0200d000c0c882140c3c1048518112140740c1c0b4210300d808050346408050343e0000b07101a200300d5000489244203446030b01500d440d14520402804007030442e850143c440102405101e10a20642c101190002c103816003262502d60842c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 104224190 1250 104222940 104222947
    0x1e06051803090108180a110f062a03160b060405010b1606110c03041d15090c030a09060606030c020c0103020f0a140c0703080304061a060409051003020a140909030f 72
    0x15541c4441c01441704032105100618581044800e11404028034481e01d9070307c0d0700c44d44000c00c01144202c2c415405d8000c4c81c0c18088520344800c1e90f0300e076900352041428603080700c0b0100b9000500c2c51049400c0403520b05410911f100c00c005100c18960300401c021a004d10481e80c03548829589802034800d81e28481074a090706201198081e840011101c03100010249806604101c003860b40e4016444010440350a00f20600c180c10b11a0078240c00c15840c00904400511351780014254441c090f03c104240b6074000f004c951030042950080000d02d41c0840c0900c40749541c0c0d0000784c010205451840058080d4103810111980709100729906656041c04044c00e1240524040384c00c062000303407803042c5d000108144025a9820043d54000350b12684100f40c1c1c9242c80c0c60004260380030341c0c800414080e803880420040303640300130a0b2070643d642c04000040c5980c95011209003001c4542c030103500003600c01c101281503032400614045000b03082d14003c0554481c101207955900c20b14501000f41031052 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 104225440 1250 104224190 104224207
    0x90b100909031b0c050603070504080c03010203060607080f0d0908071e030912080702040203090d090f05010807120f0e01020903010b0d0c030b1008070f03020a08010e070303031104031e06051803 85
    0x43d0449030240e802014440100382c1c03a0004520a40c0c07050390780002041c400300f010030040f0801c1152094119080d4003d50843c10010301041c6030b4000c00310010b0205001080500c0c4007141401981c003401c2e80ca0703000384070a20441c1040e000c10742c070410040c0c0c1c83c800e0b58142c141054400d0302034413941e580e00d903950792803881c54288030b00f0b034050700381e0022140030808126800140e5610f0001e1402103040002900744100c003584d010f4088926507210600721181c9810812050382c1202406501540d42d04000912841c18a901001005124541d047d030618001e00800d119a05602800354004141c0c02003201c134180f10100b15820f401054000d0620f904001d0500c005808004c45541003080102c8a621080d150754625007000c050390042110010492810010340ca440503101e802008d240008124001885a4254071480c8602015007450785074185075800341000012180110b411005961071096825502102e02030224803d03603030346003428042204060454032924918003c4002140b901c03110 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 104226690 1250 104225440 104225477
    0x203090108060915040504060c03061706161b1a130b040206070317072609031602010e04020d1d0309100c050c090103030503070f030501061409060409090b10090903 72
    0x1000d89402c00c40c03842c415607017030701c541c0641c60045104040119904040300d1008003202d0050703004842c030001052210001c040d000c81c5132600f2a49400074248130001101007035950003104000c041840b0070450f000d1003881910700c1001c018402c1c005907055503482c0c0c03000d00c2207000030409000e4401079980c80490010301d4070740b00410031103100382880101311550310024a03c05400b160160042044207000000f034030350204002c80c00c0e144a1a10901909010250302d60f00e0003411540f516010102844400350380c00b8281510344850001c106560352407807a45058090151a00c03442c2c03840b8100440c0394860307a0040150350381010042c01c030b040c4a14030050101c9200344100c0c4191220700548400d01c029840d00b00b5000d018600076200c00d5600d091981c0014250744c200503155003014a800c00601c4031640c071280b2140342c41034451110391a254400c001420300e1049900844065203000c001004000c0382c1c490040c4140b2001c00c0d2403402d503603528442015102584002070006994809400300081d6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 104227940 1250 104226690 104226709
    0x90a0c050303040b0406030f0b060304140d0c0b06040c020703050102030709050a05040c020a120e04141609060e12120c06091006050f01050309010209030106240309050303040303020304080c010c031a01020309010806 94
    0x1080d07601041540990010611980c4140c0d003e4070100703c5104001c4142a0070040b1040ec00721501e480014a0719517207a03400403420103000d0b1481991a200000011031081040102541d04034008541e44d081c0a0006403941d00d0300d1050f503000d00700d968000a424036051203101d814502c0c54000d4044a203440d6034008609042e0f151000c20700030b84005102042e101d0384a601000c3e011982200c0070f03410b001030f0410b45034110360032070010461108401c0c0500b03540032001041c081d900340d681d208240d91000b01c00b410405140010703041c00d032020640d0a049640020f03000c0c003a0180005a40610381400900e0050344d103140520f5030008203031080913502c2d5110320010b5a10a4100c800103040c103604100081c02e45005500c0850310032182d42c035151a01c00452440f00e0b03445800d04040040400541d1b400b612400001d001405146d404000142801031403001c0f20380308003d0000800c50f0054442020b03009203034404003004e41c0c0c1d90446504070954000011141c000c9070503107590503d66a00c400f000003101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 104229190 1250 104227940 104227961
    0x1d03031b0f040306091a100b0c010209030105040b0f09071a09040204120501090b09010212010b0703030b030d080709090b0904020d0203010e1209040c090b0d09050114090a0c050303040b040603 84
    0x1080101d10303440341003000680051845200c0204001402d41482105010074246103007203e5203000901c469500410340301d40488111006a40d194580748402d10700900483c1c08a0382c06501f00800c00041140041815208020540064200f616900903d6540b404c40e4040d059a4002400c0d2800580791020060200100020805454584c842030079140c50490b018003140c603a07464541314020003004510b8150702001c40d200031810301c1000c4a4691120350107104080612100003140d03428548250040c0d40c4090011f03040791424180c2c500300801c41641250311800040045101090300e04881c0100b1042c008020308940d05915140c0030001034000c82c0004a07415035880c1940103403414180590708a41d200340320440c0c0c9544040302030205585124407504200700402d40c0500560035640d041d40e10a035100d5030000744500da1403a00c1401086d00349444215002044100001c2440010303400652900c2401484502030f51581899900d0081d400f858a102e2014401481100d119070300c090b2428 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 104230440 1250 104229190 104229241
    0x302280e0613110309010c050a090506070215040b040303120603020a050f032a030c0a0501080103080313080403060504051b10110705102304060c151d0606041d0303 72
    0x84a80c2002d00d04544407050801d050320300100030484908402c0c46003500301a1141412450200c100703c00034101c030000c1c05110310a00d00403520009540314070510402c90380420300540d0340d0365101d94a03801c05400c030784400c03000922441c0d081400c00d8824001c90045907402361183c00007030f040004114a54020001064243c8175500341c0d0410041030581e828508030b1040440c41d5000702d4641814107140b00b2044c0680120100e17442004140da03c408200d0440342c21030740040c4c60391524603285640c10364041e0050003050000c1004810f00c8440e600050207544520200c44040ca486009110515681e07505642e01c6800c00585001590103800c24844210b40744041c1e42d401c1c1d440d1000070383c40514190200000074065010071070044483c0c005500003041007801281040d1400300010f046120740800200313203501031801510b40e514560003944049480c0c000040e518000c070144140c0e0343c0800c0b038402e40300f142051810501900e407040c403400403100b1007005d103186966034031181076007440c0c3c1d2000a000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 104231690 1250 104230440 104230459
    0x70f08070203010501090b0f09090303070e0102160f0e1602061b040e0408030105100203130302011206120f0b10061707020c09070c0614060f04050408160501060302280e06 75
    0x142ea00303100306400780440c8100000c0713907409641070048084507011658001c403850f905020300d01100201b941c0d44445180b6001c2d4150b200f1200407802c11201100c50049a0391013800802c04103645840130040c2e0701c002c4001c1c00c0559411404102d02c403094003081c0096008074020031518441c8070121040e201c49a00401c0c03905a8541c445103490000312401d032800840840140701b28901154400000ea81ca0710055041c00c4c5070340d116400d25101480000d0520030414202840c40842d50001c5006101c60071054070182d9250904541c178890710501101d95007001d50018541160114000d01900d186954000901d40d0a00c5001d03101000513003500154482c00d95540c02c15036441500754410030b561382c2c6258004440703142c110b06981039038bd4010300c003000450802c07030f05441e0b45220708500c0c0ea04850200702038407503050009940c8103440340360107441050400d88082c00f40540000e804c40c0e200b80c42c410303014070408000c0701c0c0742d030f81302a0385454047c04c0010401206130300c82035594104070002c0080f0078 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 104232940 1250 104231690 104231693
    0x80402041104080102090f03010b010914041409030307030c02061603020705030f0a05120f280b0402040807030b0f0705030105121203071d0a030305031b04120501020702100302040308070f0807 84
    0x740d000307940401c40f40d07900003070500c0352410428040001008142c00030f001141c1d1140029000303d55170701818460700700340d5440e0700d074075681c40e040380e408400c0f24580b013000e60609101d680d40700d80c400c1750620042824035601c9426984005000c40c8580e6028070f1400865182d900301b20040d600112058840d031001384600390210700380358002c2001400310340b07400340d4407040c041e00d5a43c0c6800043c121200780400302c0030004030b0340c12012602c0ca454030243d00300c0174010342c42c50b11000400e4804450b542062012a01140a05000a620066074001c038055001c0340c1c0d40341c0d0000300b981002c5074500d0020704288010000790500000381e08288000d0016a00e003155400203400766600115505800664004081e0b8181e40e002c041282c60070405841041d00170b802c548001e0418840076001c11103031001109110380380f070420000c0e40c018101c9030503402004240340c200140070b03400ca079405034810620400020080c034000c1c800c69003201c3d80070b400389040010303d484003146050107039019a5568070030842c110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 104234190 1250 104232940 104232971
    0x2070602040e04031119080c16060203030612010618090510020f0301150f0215070c0c030b090712110103020d0605041d10021201090c0519231908040204 67
    0x805420b241c60070711018941070030001c01d50180b0349811003164100303181a0302007000c00840048102c2c0c00c0103849550b9000303510303c80e04c0c18005a01002e0407040004020512a80c04002980100001c9505000600c1500552400c0700c002e441030981c003407100c480048034800c05800c0450040e004100fa90580c0c1600c601140a0f80d11074400380305a40400401070000030015403180b20720304451b1914038000481810042d40e140010448203c0b801c4640001540d25840703020090701603039000c030782c24010740c2d40ea15107030b461202e06541c909014015a8000b203100c5942d070603201071058010303159000140e080c40054009521283ca00d04516464040100b51791700c803805456600c00082000746500c6000d4082c26003403038000414411580c0c0100030841c0383d0124000c07014155507071a000020003800a09080d1418840c003420361940e00c0014248601994200f210b881d0851402490140040c25400c401c0403188030342241e182d91103e818a0084500b0b11900d001d0360300a2015100061140d04500085c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 104235440 1250 104234190 104234197
    0x2120a05072d020f0a2102040b100f0503220f14121b0c090c0a02010501060804080409020a02070f1502010b0909060103021002010b0603070c020f090f07050a0302070602 74
    0x900031400006a1004100340c2107181d42a020400d8520031103a1521080400003880d448030181c07003074181d00c4c05196107540b18901200280108040e180070705800030940d86103584402c806900c202e1070000c00d05407908240185c96001103480d99142c139520b030141c1e0240c4280e0400350100714076000d0100d01310001c250903280700403d40d001d41341a241c44a050700d007000302c104424128075035541001ea0050210281d15060725100f4181c01c89030510340c102c9240103441c016600d0790700c0e03900c41c0e043c109102d141c01c8040001c05084083c0d0b40240900c0e1380b00c4400351a10881554001c0411008100412548000e13030b01501414030584144c071070881e6214090008014150007804044d05000c6203460f495809100d403034109402500c0032040c0d0701c3e0900c1c142d038507408148006030142d001c1d0420491440d1003980510001e042c02007000d6102c0c20301e200d000b041003003801c2c4200c0c001c56105140440c0351621407040341c0304072495144802540c0d1600d104540c1500843c200300245502480103500045e03007030014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 104236690 1250 104235440 104235457
    0x10240e07020f07030b0a05100609060e0f06070318150e0405061c03050a0f0315050423160305090c0d060c1103030a05060a0f0b0403062307170603010b010e0d02010212 73
    0x5c86a80382400802c840841f403010341031100f55501b280c0104103003038000340008115416800c1c020721001e850b402103103c1d200100b011070313440000000c00c90101a00300f011402c11101001041c0039858a0714012481000c5c068000000705000300d480b200c1529064024607400a009422900700c2c180110b0000050403040904a021501c0824224000350b401140d0415a04036032405001804c0c0349444030010035000d00505001c1e98981d0300b02680403903800400f01403104070b6000c02c4071602e04508400340c52501c0d40d003400300090400340440c28141c1d001030044240ca0004000140d10070090741c80c20002d000007800941032206903001d1001040080c070246205e101450008a0fa6182680403c82c54200e90341004001d5900703007800f801110000c100391340035680d21480000320a10014000c203c0c0c80307454180018044107160412100c2d03039105a000300c04980010f421402902d95108260076213078117900c2c050010356544150103141c07400b60701d0446217a0060054407280c0c0072a4000b030240d40c0c0b001d1130 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 104237940 1250 104236690 104236703
    0x2d07140c0102010513110d0c080a03030e0606090705120402011b0b0105040506060f0301061107180903030605061e0306130203040b0108060108010516050307170910240e07020f0703 79
    0x200502107580a003c3d02d40e001c4d81010365640074440c19668910103a0030440258045d081d00540241080802001c0001519050084654442d16450012b0140131101c0c0c1003852405000046402c034103200710200d0040c40c66459140c1452040121180b2880c1c000300240e0401c9402801c09421610b0303407017040180d601407004100c4e1981460284016148054015802003908003c2000d00e095200252815180c0c0c514091000b5901c168010f8602503403034000b640f88a2462582140c0b030749541d40700556442c0300b5142440354950b6041040654000da050020038000540200380c00804410029640000014681004c0104c002d21f0603040780c00442d0102c0d4885101c40050000311800c12010f401004410024085407078000e510300079410165005400788000840840c1806000324054400c0d60b0401e42919014600013540942d10021403190705c80007850900703244491020740460060000d003401180301c0c1945800540d0400210003028002140103065044450980900004000303601407003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 104239190 1250 104237940 104237953
    0x1303120c0306081506030307120207180504051501050f0f0a091d0708030a0f0c0206070b19060b13050105130b0307030b0103050a05040c030206030604150b1902032d0714 74
    0x2d421516203c444d580440342100220304104880e81d0000468202c0c0b5480030042c0c0000d41100070584c90310400733400c440d5240844002d8162401d01c55070000b84524081c0d001c51351040c007a0600089000028000c031504001310000c09880e90030101e41c001034288000d4107101000c1c0d5a0340e4210f04442e440001c0402c0140c1d44442c21001000411004c3c1c09010b090000d1450507400d03480c00703405001c84e6141c40060145041c1e102081d95500c50589102d80e8102e4071031483c80c60066000310701d06000308000c004641c03500301c0100e41c652100d030546120f211841da41140c82801c010044d50282c101c0800c4400842c01d0700004100103d0030030145004e00b0a503100070801c500888000340544400401c1001500e180008020100301a80c00c43d601b140e0f0181c076440d03925100c000101b00900310255007404048001103000840307540c038400800211014108000c00d19102010482c1c403449203d54540341800e5828050005004045001c0d25203088050000e03c2d0182d00c0d9110a00c494429016200070740000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 104240440 1250 104239190 104239199
    0x4030503120601080705040e0417070303140709030503030103230708010c090603090503030406091b1403070e010b030712020d05010b03060f041803030e0a020d0b040c060201141303120c0306 83
    0x124005030842e5090a085089141c01e00b0020b010340903601c130344030b015041a40400d00380143c484409222050907400c66944070102d040240c040d050b000786490100d81c1000000c0c03d814404d00250003039070303802405940703103074031b991265100c1c2c40a85460340540038000c00160b0b0300d0801007000400a003904030020400c0a0503110262802045901c2801410b041943c180b0004001104807a4080e0b8848800100501c44e410403021000960200003c030350241c420100d010513251006420b145e60803011105995126021480504020300c90445042c00610109001d940100e20003252021140030041c2043c810700302071740945000ba8002e940c0d480c0000240081400d12440031070300711200751414044010948901002d802903c50302070100b5540d800300705031910302404810a40303a002003501c410b00c0701505200d4a940c80036038080320911400000041c8080c0180150155550101c640300c0341e5644410701c2031451603074280200c0800c00201881d01c0505035074860080c7c0000306540005169051 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 104241690 1250 104240440 104240467
    0x100509160e0105070213020703021024090b0607020d050309150901031b0e190305060106031d010c021b0d0b090607090801020702060414030f1b01080114130c0203040b04030503 77
    0x7001016040140400140c4c0143c0c596941c11080c0c20744000c0300607a141d4040c02c1c201c0c00e1030591010f4080043c18419826008404d24071001803080c007040550011658400602c8116070381ca0300005d8000d07405000c424017510f44804881e0140c1e0080c01946e1600200100141042c61003a41d0003002d114081480070003940d06108040810244001c04841c0702c4031810040c04058000f641d041c459601480d02003840c07034481000d0b0005540c00b0089500651b110800a00540364030381080a520540301d228034404a0140115081d0060784d8002e803081c098100421108503030801c4610390042501e00190001641c441c00d940d102d1104100904a2401c1c0510000c207520031581c0a02c4503680107000510143c0c1d038030320803141160000b0b0f140c09a111780e2400401d04201c2100c4481d060f500408040040003605840c00c441e014000b66140f0720560f0301e60449500981c940070b4100d0b0882c01c0c42280a0016100b80d0210040d880346004a034108be50320070070962103a000b50401c071050f810114207401003402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 104242940 1250 104241690 104241707
    0x7050703110919020a020106090609060e060a140f0f030a030e030c03070807090207050106080a0f1104110703080601050c071805070509130902010504030f030e1306060f0810050916 79
    0x1040711110300758180509a03102041034000030386000c0b5130001c1d00c900d59070300035403189000b8104c448082c803801c1c4d9661000d400500b8680306602c6078145c4031000404a280412240e001c1d03842c1d50390700040a0301d501c4240500c10201030003c94000d201c150ba0006960b030200503000f420361284d5030310103000130b0440031f25040400c10710441d4002e5014000a0103c2c180c0400c0003000e130380034404010303180c006c1410103501500300d561103150745000e40c89031042408122111051014010000e2851040303104041c00202e410702c1c4031640d139110091101c0400207202d03946142c0c11100500d0301c0e03401d1440295009090107082c1c1c0c4500a10030200d520208205424054030b0b62117552400c02900303007036410700420b2044c4494054055850340c0da180f15011a8082d0017550060758000d90b5a801d99042454060005c4139102d02c018414041c6030900704100050b802a8015103034240c2e10001c08044541055610003070103010a049601410720125070f94440b20282071040c1031202100c0805000c00301e02801020 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 104244190 1250 104242940 104242973
    0x140c030d140403020411160302030301090b060708040909060b09010f0501110a020a060503090a0605010608071704021509040603120f090e0108030f0a02030909010303021e2a130207050703 82
    0x10310704034811440500003055600316501500e001c601035040d0000c2d9104e0380301d403020208000310f01e040701505243c1d0000c00346050b1803206404004001d115810003245000340103000b09090703c10070003400142c0b0f19801568140c1c0c42040c0c0417030400c2d00f000010b1000c1500f40c004004130410828100101c0d0f0b4800e00c140800c1001d00003801e109041a004503840101c1030040c0010b1040020100b02035039810402c00c6400c80e0800410000c95071038000c003c000707a000f40d134600300141c00300c401c001c160803a5202e428040c50b4002c1c04903401e891041e5952070690082000d0560043d0f50721400804101d2000c007810705040710359201511012001da0252500c903440d040402040101c100500007030400204071890f51261250080e11104c00c05001ca10750b204031240b40380c11900e0440000304145c0c000a040369900040d2902140c41c1d141c1110b090303662490500c0c14040008000c4400758604d02e402b21050250001070702c103009040301103107a842a07034010101140d080d80186010814004150442903522 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 104245440 1250 104244190 104244197
    0x91f03110c0703020f030f1501060915020d140c0a0606060915080705251a01080f0318010c020a030f0204050c031e2505030420030307031407140c030d 66
    0x8010101c1c42d503031025800000d004503039641202e02c140c0c0e810008080024010340071a10488001c00080450309400c0c825840070841e440c4003c01e50385207040c13003a9401c00d210381c01040a0001550101d0b0070790060656400701c0c10040100842c5840144030b00d08145002d1000499003602d08400104141420380c003022040074042500c03918181e00091560b0459241e15055840341602c10140610185014140010490603403883c1304014000014880c0840ea07401100d04580e41c40040d607844141c5100c0da100035400400403e941a42481d00c241656481132414007000c400310b501003104c0c035603140c000340d50b00100624102e0441c580f50003000d90042030203000c20305504009a004910152040c40c0b03510320f4014200140000440f101464a07420700864030b400188040754001c3c0c620390003920140c81200c044450f01240c002c0c0d0a05001c400a8040d0040d0310b041c01c03c1c0c0742201d2120703442c01c00c28001e00d0100451400708031090b401c110350f155000094418500203108251078003c80c920481d062 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 104246690 1250 104245440 104245447
    0x309110a060801210b07030207150e0c011815180e0705030109060902090901050f03010e12070219050f060c100204060306170c01091701090b04030906021b06031b091f0311 75
    0x42101d5405c503045469400d000d40c4901642c0307042c80440c03107070207240342255181c0750480d5022000003a8151118100380ca618120701d981b008890402005809000341c200364480401c0300c0b01c1d03c58200c04001c6442d410352840c04035100c00c01900040801c0e44d05d44000303100800140500c2c5001c0c0311b20001040c11120440c41d1003015004150200b20521441d44216038801c40c3ca81551003c0d04104079205601003518441c00205807010095004003005074050120b1200f95411901c0e15110700c02941c00c02004600e00015800400466600800f040d071040c2c00b4480c0368000064050000d0b00291029403400f107401c80c24045104841d280c295000c400c0c1f41d2240b158001681d80250000301a20b8041050014109201c4840c1e0b001d81310b00d01004004e0070050342000181a441000101551495800c0d21018140841c3c818101400854010b078031040400208100b01e12100c501602481403060040c18800c0800000f0816485a401d090000d510b108181014603414459055011409840d0608 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 104247940 1250 104246690 104246693
    0x110102040e0115022b200307140a050d02060406051614090d08030426040b0a180305030a020105040c0605040305070b0a0504030b0a0905010b0607030806010309110a06080121 76
    0x11000410b1080c041400f5800c05251042c520070700810640690380e201e10b0110640c81640b40b00c0300c89120700e200c00040c0f804844550780e1307142c0c4550761301c5c9403540348001c5003005940d446542901d03a00c20310b10400381c40f0308086400016030502080c0c40c0d2071019000b07010309103054180b8505903a0300030411881e07660b01c112012031003900880000d280800044815445044600203d82030005603000905109000f108010800c11800c01e07101c2c0f41c66089011511007140b1390401c0b200c0e4003507401031400b40e03074062040340c4045201c2c0407001ea00c1d04071200311041c15552600da01e030441c1d008030802001031f51210108001c0c401d4079691f0a0040c4801d103400c9207464510f440e0240c0394015401038050194000410500d0309210301d003179801450704181c007500641080a1840b0043c2010740b0203c13215400d012100d43c3e18070700002640e00480e09621400c4031750b5100c0b0b00440051100231011120540307560146901c03602e4004255002d0001521401c0c2d80754184174108554015007040c0541e03818405c1c2001d030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 104249190 1250 104247940 104247959
    0x20f100b030d08070329030f06040c030b0a02090a080604020a050f0f04091110020f01110a080406020304060e1204030209010503070f06051605010906021206010806031b060d02040305010c11010204 86
    0x50b0452810300d0003d002da00c4070b030400c6002d0820400c1031180106500c0316400c040481d10000c41c10154100d00716840c1c50000c10480e078403100100c501410180e6056020004181540e48880c2e000e09101401807401d03d00314002a2040c5150704810b6482c0d00c200108006c5050016500000e498202c0780c0221101003403002605083c0350034a16400b40c0e4441d40c01d50204043e460312920044401032142d000d041d40180002d5480c3d100c192601020741c240500e110300700e0303200c00487d0900025951411100d070340ea5100c500c0a0750000e0003c0701c00555510000000c03034001c1c8110681c0040740e0200c0e60399685940100961080103030001032103070f00500000c10110481c0328400044500600b40715880e04104041d1410008529102511039420a11400b003000384030342c01091a030320500e02d0383c40c883d142c500c011600a40c04481e8550954098120b0f0514000254144030074800020001c81c940851300717a0305c40c242d070841d50017100c003030b03464000c94106607400510050300712003620000c6003006e240140d0721 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 104250440 1250 104249190 104249203
    0xd0503072c01120e0a03050705070f050319020105070606180c0509030a021c051f05090303040c03060e0a020d0602030601030b01050f0a030504030e040c020c01030b10121d0706020f100b03 82
    0x50503c02620302a107880403858101c828440d0f40c18050320f060b10042e00380500150b00408044417039014490380802c071040300f0000d060682c1d80160003450300b07900392214408428200d5009a051117424010540003c41c0340c02010b01a041c802141c2007000b41843c0114180c03480502c40d0824840c080c42600c0c41394800098610b4115012240642d05c0700751488209000c1c5140b03100a00a4061038100f1026400c0c4017000c06440003441c2010001c2c2e070b580740e164944900060b0382c000c0030201440b070104041050f54001341295580b220548801c44055400603511400042e0111469a004000c01c409503030144560810346000307003803040c6018a101c1210710584981310500e401c0c56610b0004ca42070500c1202c600014410191040140d40c1c0205000780d0344151908055001906007002221682040c176038905060001c2d40315a24941000f009550240161011500b160016010081400342c010130000009054a402408500e002e485020381810048803200524038202400c0c18072988000444 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 104251690 1250 104250440 104250527
    0x9170c13021c0b04060f0b03070906030c05091207090f0b030601080106030f1b0b0a0201020c0706050a0f0e040e0706080f0c0301030f020f010309081b061008150406020405030d050307 80
    0x20f211001a400103009205541068060000d041c02c04141d5800c075000850044a180d01d80600d080d580c2c910440944021200b00c2c40018401d014200a03414903000f006a44c070b2404090301c003550b880c0c80d1494115155952600416501e03284000e02e142000d00801c1d02412514000b84906421512811410182e206004198400720b02070031505013070140300720000c0d203861081c19940c5c10010a0080c040d40000d8a0360340d4a02460000007441d501072400c646c440c0d000c07074403502c0362a01081401c3c3c40344d0001e403008a400c5901c1d00c40c140c044c99018802200500210307207801e492130400c40c0902200e41002040381c060340004000510110b0510f18107851580d030f040350304000c400b1882004070040e02025000620144010032050200803180b04918890100c4030110f030b0203550342480454100700d1500c0380c02580d802c001400004980e070007001031ba006006560240c80d2030b680d0000b107032421102c10a5000010070210038000d0301607200c0000c0b00501001c003445100300540c400304011401c0503054 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 104252940 1250 104251690 104251747
    0xf0c08040f03050c070e0105040b040e0d0e030109020907170a0603030e0907030213080d020d080609060108090f030703050a0e030a020f010e150c03071209120f0309170c1302 76
    0x1140101031141c1c2c2200d1004c852101903e0b4070b1540c9070744580c8100d0003805020312031400d0400c485071a0620b4402d01c0e4203900e072200103040d190003505042e1124040b81e04403603099500c03180e8650168554400c0c440c01801103a41c0c041b80302c8001c00d820700050501038025400c050500c0c10400120f17620640342f030b210034001c441400c11a141c4810075002031051100c0c012040042c461300107000e410105a0340003013161a003e48800d090b00900455040e54102c0d601070307100c8612008035082e944502802130340940c481084403103482d646244540b07103420819040b00020345c00036901440302d82c409a0070401c0705003a401019481d14990001d1160308102c200b080c1007013001c110380040c2d51707102252100c082c00303000c00381580d607924848200e03140d5100807402d80310000640342d201e58851194180c5c0044440c4907880c00980d98181d030742e481d032003009484140c040100700600130804080d200c04c2d40c850024444000e01c0d2404004042c80300003603040070b00b100b0903407050040450440c60411003074485405503c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 104254190 1250 104252940 104252963
    0x111120d02040e041b0515040b0f07080714010b09010302100806040b0a092f0304030509010212030106080f0105060421020a122301050c1204031707020c01030f0c0804 73
    0x84610300901840e40082e8624120380280000d1000a0400e000420700050304040c03104d0700c580911003480e070f00d00144c0783c00310002c101c20000308101d00003425200d06060103051a06100c0e48070300d5a2a00040001e5601204ca4440005104000d04c00c2c94075000050740c5900c078940c91500000c10204803d07005d80d082c0701f40c0c580010a69616580920507007003000b051803d2240c3c81c1c02a080040101500329858403415204a00e01100c00340e0001a58100b120262807659030340d0350301150300d900412407803810340c0329001111521002620241d0701902c650395505d60240341110100c101c40e131040c3c0c0024010542000180407504010901801c0b00e400085104081034040c03000c43c48a44040d031001007100010170100003002114101107030010320802d40400b207092809040e03401c03914195004d103103182d400c020b60355100b0381c442c0a160344075000c0c1c2080c9581002d04e000141c05010101c80c03400058100341140402c5603010700c01c1c41c0314400084803c003c9001c5030b00016010940c050000703414a400103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 104255440 1250 104254190 104254207
    0x60705011409010605180604090c031b06140f160f020616060506040905070510050408010203040b06210d08060d05010c080a11040503070506090607140105010f1d0c03060a030605040f05010605011112 87
    0x1032b4280000b142e001072408071412900d854a5400f440714015040040ca11100b41c000044044040c0c42c3c0c80021480344c01d00c0c1020b241c154048603100100b0442e001c00a03d0b42040141e540c400c00350281c0400e07211000e035001c12070715000c42106d00060885119610f020030f020b0100360005008801d4070016111070414242079a020b07510b9002e250301c1094207600000400c81040070b080f00003405183c09070b541d40503583d0032601042007203c940e10000c1050b80081c030345c0c070025407140d00c515401c80006454042d0605441e201c0f20709650000454102158401043c080484000d20a444c07030240500c0f03415007071a0078040005e89811152003464469407000c2244011962490215410349502c4121442c880315000b800c14043d04091240e103000302440000040c00744034910089090148814030f200450703950b11100b00c03058101400081e000003401d14080005222885a02e0065018a5002c001801c0910304142560500e81145042100710306420080c8c04001074003440344a40007107810b44543d400f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 104256690 1250 104255440 104255453
    0xe0601030e060c0a031407080703050c0c0a0302010b031023090312070f0906030501180c05090a030308150a03030f120207020d0b19050c090103090206070501140901060518060409 78
    0x64080784a60241c4024002054032140041c005009652030502c500e41c12000300c52107403402182c08002280d0240000781e000d5200394031041c0e110103401400f83c280003003c081c05c0c0c0751440852046026070341d52041407089103003c02103480301051221040c002c001c0c1d180c025080707181110741884d40280100d80070910701901401038078a0030703403800c001103828a800240106100c2e2064007400220303002080c0852a207201c2e000741d034140c03510500001d4000180310048801030404003030381da08200c0144600440e9944042c000343c003d5000350344002c0d060400490950b100c0a540703005505c10081908100b0009030450348041c2d40b201e107403d00704002c0c0044601d400217445100d4000703500108000da00000c00c44181500c03401103542c54514120205101e82c044c0c02c4907800c3c0c811045145d01030050341d6566109800c00c1c3c0101c0d201500640c100549581c50b2400d442200b50003070310f020984004c00c811740400344502c400074182140e010001408801d2400080c1502802981c0035949900520090244 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 104257940 1250 104256690 104256701
    0xb0a0909050c0702240705150106031a0d02190b04050a080109320105070503070305130201020c100201060f0e0412050a0804060207020d020a15031a090109090c21060f090c0e060103 79
    0x341e011000b0f5481c0321750300d00f05031991803d48c081302400304013070300104400c2c1c402e20440800030f912038a229440c02c1c100b02000401c00750000c089910204548a4100d00c40c0c1c05a0313018010004001e440e5200c80c2084104103030003c560b001000560705d40303039401c00440c88070740301c10741007a46281b620003540c103241100d512813aa6440012210358200700901000383d50200c0118071403642130b501001942c8400c0e030f644000c800956800b034016402000710b0f20780b500d0000c082042c03103185070000041c120b9480100d20700300f91199015103140ca002c002044180085001c60301136118240c03406070300d8488880c001911841020b00054401a13000c250340c4119220f00e001c0d4040240c00034010100e440d5030305507510080484283c000700103030a1440e582449001540c00b41d144801c01044100507a0070070260030000c081004d030680f16021502c13000141c03059070100315400307a84501c010249107001070600b94180c80c50403003031020251512000101207540685050f05a6404102c41e841940760700c1e004802502 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 104259190 1250 104257940 104257999
    0x30c07060c050706060e090709022505010b030c0612071d0904120e10050301170a0b2511060402010e0102120d05010302030c0d0b13020411040b0a0909050c0702 70
    0x18900501c85040302c0c2c00102408460307124010610200381c0f6414101407506c000d445003621a880000f05020003a86900582103514180c00f918100c95909085100b00c01d110b1502500c461350b41c0c4441c40c03032a090602001166440031b0360703040d18020500182001250001b00000d0401501c44800c090080384c0014005c80c1c03c1c0700038660402400d203404c1c0484025010707059200404d01004500c5503e0401c0011000300f004a0b0712040e06580c68041c040d000398444200325a0140030310f40d04130340001d40034142e090080401804450720040804804020600000624014450440c403081005000060034030390055083c60103410548160005034039140c2c00055014407074802041514200005900581c104c0e4000c0341190344403c0c00304140851481c40301030250034102101c0004400740c1400c0c01c1845207600c098070000300c004101078a4000d40e00940c210700120b510000b84035140c0e03940b180c90a000f070402c000080026080054003404c0a101d0003000901801d0003008070925107a000e2603555448 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 104260440 1250 104259190 104259203
    0xa0302040504030f020708010e03040506030408120907151715041d0c040b0d1109041103150402010810052101020c060a0c18120206071511040602010b060f030c030c07 73
    0x2e0800f883c014010031400d130b010000500c02d068001070032190500440d02022100e0b0091881d06080c8018005150310091042d5500e0004120f1580b540c41440803091241d1010ba0203040440e04000b5465446031021464a04000c0d1404d11241c503286040b170300940003204921035000000400c0049005880c09500c9200440c2208070b082ca158480030843c0c240344682190b003080558010010084000070961000c0d1202684004440503401c109005e150414050141c4090f600d40d1400060f24042c0000c9202ca11a60381d4001d000031940c20204168000962510420b00b003810a004190302140704100b2141020420404510650080d412200c030030003c5001e03900246056011744c1c3c003410b051441080000c0444070b06000e0103034141d07030000941d00d45900d004203010403034081103450381140105840c4044101e1060104003114450603501d141500c1308151102d14188001e404c5482c7c2d860f100303004450401100e07000b0b00e10601140d034040780710040141c0b1ba49402c0701e50741940c0103101004040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 104261690 1250 104260440 104260451
    0x14040303060612090c0e040507080601061701050d02150f04090501082d03030703020f09060a08010e151c0c0b0d020d05011203020d141e030a050c270a030204 69
    0x60540c9608510103071880c1d502c8110314010688a000d0440e0b600c408013401c0c9410003401406a61002c14030350382c005028104440489803100192801d0050a921000201303c50418035186103014541395801004110750226030103480f82c02241725181c0c10b503011014400700040d0a8250b101444c19100070300050f2400708070a60b15001d040e96103404000150b10700a004c4008605094000d00d604028903116030041d42c15500c0f8541d00360087c0d0400311010500700801d000e40400c0341c480d43e0103040208100d645003045940b504d08800d907140800b03000174109000d0700250300d0080d01d070189a140354120402200d0209003090924082c030410542000c0d0300054001601c0c000c1d00080e03005844000e0703103d582000b042e40e03601d50301e04000d03030080401000758010301c452000c101d0041e000400c812800b0051a460040301c07881c040a090b00440b1941303050708000c01448110f1103244102540101e80c004c082d403801017284401c8400080f0702d0314207a40e007e44402c0601e1b03aa1180700d01240210341c098428047d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 104262940 1250 104261690 104261693
    0x415080a0e0d0c05010f051b030702011b0201050a0b031204030f050a122007060f08190e0106090b0604030308010308030a06080a032c01082413020903060c03040510050a1404 76
    0x7803c4080c88240e07010b41c20124010700c0c010040c403c090007a202100d80603407044040001d090346400082c008019135680c1e07000710440d01c000142c01e120706000c56000044034503007590b08008841003003040038000d45c4030611a4102c00c403040c00f2102501c1e04000d00300512030083c6092490442083c0f402840301109940c0b107070750f1075005001d0249210740195030b158604050700286550308407511440c0005100a010407a150b806591000d420000804ea200b645881d0040010700307a4a960154202981d920102084500c00701e12442d040010100d5099103042d00d1a03c0c000d1003200103000240c48402c1c0000400c28038a05540140e00a00c0c4681c19100110305504010300900c0e140c8100c245081d21001d080d00c0c0f0f141500c1010302c1c03112016102c81500f80c8030503980300310f918034261070010960300d480040101d940c2c8000381b40582c45038403d03015070b6400a0906050070300c10041c3c43c102030804d050052100160340859950b100f60300601c40000e00350340c0c00d00c490b0054002d0000701e01c01039084106000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 104264190 1250 104262940 104262947
    0x70906020d050c030706020d091718040e030d0911010f030213090c0203040e010909020a08010e0a0809120f0703031b03231c050906060613030b0403110304060203090f01050415080a0e0d 81
    0x1420720b016100c0110384004414803070b0000d1154240c041c1c4000005500710bd01c5140c81d5202c40341e1130102c48100d03401c280c00303030f41180202c90700700c030f425640100140b91024107076902ca0102e141d0f24805140a604050100a0040315586c2601404540360744030000400c001d40300300141c50040542c00d500009550350b03460323540300030284001c0583c090311502c0e8010070294014043c040800e072041c4000c00e00d1a080751140e00c01900051011030f8410010582400c951500300010070b0a440f0541c042c04800d4a10329014001c031003805840714124072a1141361000c0303904480c0c1c910002500306400030f0b6803900ca26070b020b00c501ca0042c0030111881e91741042d0381d036032503582e00c018855180602203860549032201080781901071403a540c110340b80114410b0001a090164080c0c105100341402402100001621030654125801c10700050b800400c05c11058030b060710b4009140742007800d140703142506111031034004101a516040c280a8020045142d0408035070040d0540d0300784e0700603106150150365004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 104265440 1250 104264190 104264201
    0xf0b0a02071a06031b030705060408011d0c010f0f090509040602070204060806280204080a0b0403020106061e200106060f08152b020415030b070906020d050c030706020d 74
    0x26034000500142c5090550300000515005800c001e005188058000c00403881c401814912690140131745100080d01e511800e01820240c950300c00041400b13864182d000038640c10359901c00394282d20030700300c02030180d13000034440050184600d800d030f9208100340c506440c008542c4c1c2c08160042c0390340d0200018801107130702030708203144201c0b0180412031307483c801107a0301c444c03e4500390b845403d031414070b425400000a400bc0c040504601c0507081c2565081602d040007001041541c0c00c1810308100000c250f82031144c80c014000506100c00b0802141c0500520007001031030344010302407a104904103817801c103500c076800300901500a00c0300b06d0301d450000303001414400ca000c3c0404d89440c0850140907001360703100350a030009040500c4200160040d5043c082c488140301440324500c1d00701034090b807114024802c04925488aa0000c50300d1031600c5c044403500200846c04000802038148040e6901080c0c10308078040302c5c6402912400442d41e502c1c11480341005c0100541c0c03000881880e00e51158220 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 104266690 1250 104265440 104265443
    0x3070e0a05070206060108070c050f06040309030203120a0e121c03020406021005010b09040b0a090e0706120209010c0611040506041e080d0206060907030603050a03080114040c08130f0b0a0207 84
    0xc1c001c07526007400607030b500c2a040d00c01074049150040082c00702c0384505070503c110360013401141c00e1035000e180000e040c040107842c1500007c6000c4070610550400700144d43d008551075500c00c0c94102c401d6001403008040622092140ba40310186600110b010400f0a0514807400702c00207605040801c041e009500030300c45c10300503005000c1c5602e0f1190140c41414103d4410840a070f15000c2c8680801004188150800380e001e03150480100b03481c202c0d0701c80d034500560180c00901c2503c1c100f50000d010304900180d000100e40c010441d1103080e07607212480c0070340b0540c004004282c03c115004c103207078107001d680c01c035681014000c500003503000056104000000c0c8905150b080e410f072100722954446c2030300b440d6000541d0004001c03c895042805980d6401000792a001400b15200d80d0b4031400d040c4001c200b40e0014001100510040111110300b0040b858100e8082010140002000d0b00707509000340380004a02307c2c0d0340c1100900c8400c094010116034450118036852510030007080094000010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 104267940 1250 104266690 104266711
    0x2030a0b0f0a030506060607140607020a0501060902031e07020c06220602072409032f010912030516020a030c0f0602010c09051c02060a0c060b04150314070503070e 72
    0x70001442d040050010b030903030783c011010384002c1d0380358401d102c120f030700660003250441030b21201e078805020248246806100194003921281001d428860700790382c0f0f5500326801d918810801e00202e00300e04804d0540403000c2c07540300052541d0307009069061950701950582c1024001079000c3c0456062606c140c80072281c2c1601d08d10031a00c0b5801240e50300c8541c01034110740e4001e01c1d201d2110103043d000b04951030f60503150603030784140c40c3ea030b0f0740543c049044074001d80784030099440403c0c902001d640222401080c80c00340d04031032410b2848600703d00d22410142c1804000528074181c1c5100c00e4402d404540c010700b900d03034001c0d664035040d12a480c491203500f04c6880d409801281c01881170144102c02002d5568880e02541040708201e0030703581c04a00080300b42e91401c141c00c01a10f404000d040c8660981e03c4516480f081400c1c40f07401d0b5107100140c0c42c421450880754000b0451412022015650088030004d01d200c0d02d02211480d2280540050758503109124001a9621030303400a5489100c1030725 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 104269190 1250 104267940 104267959
    0x3010906210b060127120b0a0504050d050a050f04081c0201020909180f0601080c01020d0512040b040c0801090b041101030905070b160b090304060905030607020a0b0402040f02030a0b 80
    0x81c80144550161080100807010340c00102d05250300c20103c03070986250b0041c0c4c48460001005540c0d400135000d9006200b0100c80004e28014407200b4440c2d1548805c1c041c100f4042850325a58061b1280c104980301d0301405000308402c000c03640708d8000c3e106036401d8429004c0d0350703645a010582e941c1e11209803100d5200c80340c4411131100d900c10300a0310310f1002c01815588040e244d41060310044041d15850103c1351084036070345c2c01a482d040120318020940500942400340c29400024100b09071518201c05105003080241c196041703e07280c4940c4035410480c1e000068032107141006001c8241c1d0322503040c544c20642502c003845070b5680043d000d90311a85004010a40b00401541501c13040c1d400509950410b910400c0b1070b406400050044c0507500c54a03d151a640b9075644072644030079070740943d1540c4045820720580c2e811486000240500318010042e610f004a40255254440c000040811401e54041004c545907900440340d0040856030030340d142d02d400c802e4a8018240b404030188900c190381c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 104270440 1250 104269190 104269229
    0xc050406050102032107030f02160203010507090e0411120d080105010e04140f040213020d05061203040312030e0309040f0209041d0307080309100c05040801200306131103010906 78
    0x3100c0303d8101205c2200462004140d510018410080c4018145901c6407541c124143d020b20090100700403101411040f007825006050840d4070050114041c403010100c103015228040b40459403140c0d210702003000b03541940740031540003040440c2074825032080100032001e15802510141c180c0344281e80e2142d18051500401080d1a079003d517020b0794854107000300340264118903425522034009400c03900803460001360f98080ba0701500c004245c0b03640e10300c1032064a14111101c0710681c1400e1004500307050a584941c1e10050300e425113001419030b619081c0c41960014405c1e6240300e2001407080006071a100300500c0078bd4003500c0d00074403c40ca8402c80c41c109000d1685600c203151038050084d070038a0383c0c0b903541c0001c07548050004d035100d00c0380f00f04080000c84030b03008603203060003140d45e42a115481c10108509480229103000d11028000002d00743c00c0e0310110030f4aa100b041200c201d8aa0240c800c20980149903003800c820400b00c0000002c503041105030403110480b1541c3e56445101603a0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 104271690 1250 104270440 104270443
    0x40c03031209150b031203090a030e090402031c021005010e07020d02011b0c02060d05070306050316080c060a050c060709080d0806100e1503011e080a050703060f06050604030c050406050102 83
    0x10070002000c03162001a100b00b84003140c1d104098102000d81203a14030100f10803c041d1071f80046480c0a010350240da0303c101056800b884025040c1c20a0f02c0901c0c0c3c90401e640081d4850201d0400503000000c14841640c00910812111260158019042000356110030070307600b079000100e48103000752241c0d00004044920520401c10b4a8240e1107460410011308142110041032914003a40d01c17210a0085a41003103603489180c0c0104125140003483c94035002c141030400c4220319480684800140080000301c2e070101e12003441c1e040c1142c0e45641d6038401c1c6003d580324082c0711003400d45881040c0401108540009089050343c26800440303950a00b1201c0c1164600030454401e60000342c500701003403196001e405200c00024000380b0b0040031140c1100004c5035604260f10406101d0007200070142d0b200c02856540d0050000341d006001d034038095440c0c565848105100007403e8659a0036819040d5085600440c09808011f0540c5e03556562402d148141c1c3e03456014651182d4606840016190300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 104272940 1250 104271690 104271701
    0x90c0b0a120c0509010c030e120106080c010f180509040f200307092d09170909010905131b120f0204050a0b031902010c021003021c0c121d0303040c030312 68
    0x80c1691134410346c0700507580c02c0742c94010041c09240c22147d61401d0541d40c400a000e0500a401180014590542800b00052a00303a0203610141800000140080072012050318042654800d813408401a01c5600c2c0c440e542040c12800500a0050f01215080d5041c2d030342005060340380d08404881240d501d540d1400b007110f0300080c40d0120f5021443d030001d00c0700e451281e240401900c00e07900062100f159118043c070300200130041c5c0e80e48800015640058036041c000306000d0302d8061800c0127545031804861451269180001d480300b1480300003407020660004412000e000c00003500114050107140c18200101603201c03c0744228103000000d011011039100340e0320382c440000c000307108548810081c0e0301e41d5105107030181e040003000e107800b10268035030141d0010000e1300c2c1c0d6030050351400c1c1c00d20030100743c41c1840c0304c0d4590700342068505003040340e200c44007000c503031071141d03001a0410307120340090781421400241d41214000442003005000c041e60150040701d002e912a03180764005074040d2002c440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 104274190 1250 104272940 104272957
    0x60402090c0306060a08040203160303080a0507020a0c090b040e030a120b0303090f0d0305070b070c0203010e07050108150a0f0603051e0c030403050f0c012a050f0d090c0b0a120c05 79
    0x40e001d02242d401700784524a16500540081c0c00c0c0d0703006056484000b060703414282c00a502251810041c80f044005a1040b59845405440a845c8216069a0711000b050492042c000034a0712503002442aa455501c1110010010001c41c0e90b21400c821003c1c2800c10800c00b54122140340100b4031805040100880310072060080c84c81540180400c00c01030703003030658617065042000911180d400540034500242c000c2180b0f80f074200080c22144101801c0da4007414a0403002d0b0091301c000c00150b6045110301c0c0e0082c0b142016002c0c00c0c000000401c00514103544400d08203401c002c00010740c580c156001a028100301c46034401074440140d98801130700d0b07060703401083c00f0b54200700280110f442040940141e102c1540c100d46441800e81c446401e4450f05d08190005030780c42500000641503642d0020b40c08192400d0103410b19480100d00390443c020f0300c8082c4141c80e10f40504000f001400e541c888042c1001b00d12030f90300d0700480c20f801405c021003441c0000c00d240c504690261050700807000d944882 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 104275440 1250 104274190 104274199
    0xd0e0f010b10170c030718080705100c030e0603090f0307060b090903030c040b0a03090203011416021b04091106030a020717040e0402040903021606051e0a0c08031017060402090c0306 80
    0x1501e8010b03803030394240d2004054901f00700c0d441e40b610311814511201030780240910320081c00c000d400c060070401d001480998020500000f28040d000003900085503003803000e41210429240d94480c203c80341088104140c660b264000042c619040000562003a030107401e0a0702d01142325550803d006541c1e110580c1c50040081e000c0c0410811000c41d0001801490124a40810304500341e901007070035142049602140b903000e5074104850407c035088081802c2c0d250788001c0c4614000d8041c0316a025000c520b0150182e5103c13102070701800746040604045032006090682d491401c000841c00a4110410441d013076210100b02204074200c0c03405031400c0c1d401d50001c45840351126420080142a00300085095005181d0b0303401c080c920040c544401489983c4443e9583d2315000c0903000400843c076080c0200c05030605c960b9101c141d0104800050b02d42c0101100d0380da0b11503c0b81103012081945c003143e084c20010541c41c518031808100ba6000701d10039120081c454a551401070024003088a030385811 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 104276690 1250 104275440 104275487
    0x30b01080109051905010e040302010b010207050d0314040806010b0703020c01082809050102030a0e190b06130b0402030109060617010b0913060e0f07080708090703080d0e0f010b10 79
    0x31042d154401d58100c60400b100348010000c103040c0b20140c4400b60700c03424035502c1560400043c1602030003030032114442407010384025404c050000b00006001240a0104008840104603040c0c144048030058000030f0112252980d4503043c580d0140d000c580308a005024100769400154010090039002e54400c2109042828440400c201081000901c0e60b285036103440100001c19420310055010703042d071981c00f00303040300f5541010b8a000481002d030142203e540d002c807404145072000464121f03408403400c88001c0b500c071070804090022030f205203900034400000024803819960000e400c81d01e07261951840c4816401070740200390402d10552026400400c40c40f206840c151050120028280038005040c80c0c175508900355105080b559500300b9640384042c81840341e00442d14980c458494502032501d40380c40003510381c03507000500c0300070407485000c01d4520b2400700355000081456082000c4400380300b04a004903028003000d021850203020302c1c0714000c003154405e8110038004200c141c00c5110 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 104277940 1250 104276690 104276699
    0x150a09150b0702010519180e09060705070c1512050705030615090a0f0902030603010b0d053304061d0a0f020910050a0b0309070905040b040b040201120603050304080d030b010801 78
    0x22a0742c000342040b0b041100400c07200307100071003a4010541e090469035504051030341c009500114619190403600d44c1c40c2c0380008000c080c070030004500e42d11054030328000c0d032140c900745800c2a891449420001c3c0e208070084004010704c0e0b0120040c84010b050380c00074840f43d01d0f045c0341030b80e0510060740c140da0050011910654240c1918009003180300c0090a0100304559550b00302445003640e4104a644035000010b001041c9801d01505645a0003101d14100100700d541d2400d550744c140b44055018851086102648640c50307000c2621000c41e54000c4000c20b1400746400c90060075403000103e031030030300b400100d1911a1b0004242c0307501544840c03040c1200006400f0007480110080885030000781c02c540c041900d07200d0740d50072802001e541e01c00549a00b0442515828544940c020404081c944010007004c11208140940c03c1a0800115441a203880c0012105c0102c0000241c100504102000040000c000010821120500107071540d014024400300d0607100c5076198075000a440c04014403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 104279190 1250 104277940 104277959
    0x60703180f03091809050c06040503150901150e07020f061603050c090a0f030309050f0d110d0b07110f070b07030f0903020d030908210d020c01090803150a0915 70
    0x400b8003d0400140450740c407064098508003195500c14483c0d11000300e0400c0290401298090750b0b01120381034107203410400880e6035003c5454200c2c0b40c8224134004200d100000390f1241c070300300a1400052070740300d44590600001000903a03a4000521070850704c89030100000c610329004040c000c00300f901400c3d00c250200d0241c00058400300b699001040110060740e03030800c03050010002d03e031119421034950700703014107440259070281d03000360005099030b48113544140d400c0303500e10343c08004404c1440702c00c40031403120711250741d0060585010b0707403d00414a8004400c184504010720440d654018042c45454903240c00d4803030811034000c01d20044001070f0040e08a90004140d0f032034003043d5181d482e00019050700d007218040d00807561415040c444280103020340e1022402d50003900c6442030130b6141e00072242c425240c0a0840c20f07804203422840341801e4216600c11600004219100e082540f000d10405076903441a0b84241980071001520030340f0350060000b848020011070850741c0c44c0c82d0101 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 104280440 1250 104279190 104279213
    0xd0c1e08040b07021306030308040201080c04080d0507050102160809040b01090b0a1b2a05030109050c04110f0d0b2407030c032105010503070602010614101403070c02010206070318 79
    0x4c0343e02480d04010584c0c111110b01c03840000394000d03994100c660606000160080e0350180103402c00c08410002031091120015050348943d02901e402952020b150a02034028010340f59010811402c0103808018001198041d00001000302e800300002c0781a903005440300b030361a11075121a117006028815000b030040540120000710000180c20100060b030312941c01108515040c01c1051401c0540c0807030011240048020306801e8000304113807241c030748400795200c541c4805607118546650b0510420b11213001903d1941c0b800c03000392920f40142868a401174820b00e880103000b004494502c807d500145101a8490000c410394145002ca503a1012503200c40c440009030180403910109d5000910001c008a08040c0305050000d00c9506100c109801c00c031f031560000d0116810030100380451400c03141000c0b80b8a000302c0e4030103e038865031141900c20650f0780b0044409880c000c810006070b20b03080b075410b01046100340c3c2a1401c81e81c0d0300e80c065003100c2c45403500c3c10100c400c804200c800200c000b03001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 104281690 1250 104280440 104280443
    0x3020a050f04060503070306020d060e0108061812071406151f02150f0402030708061b1c0c090806010b070b04020d0201020a0b130213021e07030309050d0c1e08040b07 73
    0xb00e03c2d030362501c000c240b81c01000c2c2d004990003980050002610f842c0340c400c86024104070529a0275551400381800c0d82c40d03c020b40042c90f8040c4038280214400000c0002040c0060184900358803006030307040203050305555007244e041c18041d0500003110310501000401e41d050b1300070a1040c8002c800400441604c40901c030b400d0561045110003264080c00e00341c0305100c0c03006014808443d03d490f00c140750030481a179000000c19844001407010032242c84a0700d20808400301c81103a00c0d601c5844041d80002011143d40044514248041d8216503020507a0800e40d80420103ea6443e640c07000c00c10014841c419010740203002d03502c0400c00501e4a0340f003140c9036038014070498468901a807203801000e0425205200070b155400650b00841c10700c1000c40034920402c0d00c045050942441032900440f0210075020290b800000f808020140039a010a03500c64019048416142400c10050314001d500f070405c1d200300290f180305030440345400c0d80384560035511080d05810a403a0103802c0110703400c140c40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 104282940 1250 104281690 104281699
    0x501020307150605061216020105010b090f18010e0106020d09031109070201090b09060106020d020102030c070209040c0305030304050318100e100917150705040602060411210106080c060403020a050f 87
    0x11039170740b039201500c01c00898040d81d041074200071280030080c0803011002010359042c10010403d59540310b00707940341c890b003d4412008044e039000025440e00d215044807c80b910344440081040d401c8a0f164a06071030071602128584598014182d81310f41007840006d040c00402031440d8034600300303d000d840d04040c0034000422400789a43c3c48144040c07040701d401c5801d80c0100010010030b54104860800212140000c620310300b00480040039900c64024042d0061561078081410441104000c50045811400713a039102d0034645881d940b240d200d09044d01d06003142111104181c5040b050150702007141d070b00d400307017403003405000d2049074014004d81c030050040c2403100007814052842e019460711028030180250980406104204000180c0040d0420034184420320009400141035900160000321400c0851013800008508010410541242030545141c3e20924030054000400f951851410745261046200034030240d802588030107903004a004c03004110743d040c0440e101c2e081100280 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 104284190 1250 104282940 104282951
    0x5011805030a1b0504060609050d021206070c03030b0114030a050a0605060f190512010e0603010f020406081015020d030b04060b0705100605040203070c03080a090b0903090a0f050102030715 83
    0xa007000400c5909964030602001c1c0c00006592030103c60014201c202c0f000c0007400d00307011004121801c035010316030080307410142003401e5654038041594211000d10450311a440c003010014080f18144030b0860129003050140c240c02d40c001d0030401c41c0701c500514035a055541d031015034800b034440036010920300e9940780404541502c0d0b9038014500c00040b044940e6039810001156842d004104180c401046810f0201d8580c1350101c074401811940c8000340c20f4200e440e4400040c0c01400f1544942c02e003544000b40c0000e0264100c56018450300c0003902501341300703541e6404e0301e81c00307268500b43d14010f8000c49001159903004c1c0e1302c4414130300409000083c00b151648480c88a0ba40035400a0300e02d6403110284011105041c0500381c041c000c280d03800e50950516510103071200d1b035100c01c0142030000440010718010b0343d5621030384040f5005a0811200d05103000700c95160750000072014050080301201040c0201040e2a000c2110fa0690040d0b00d4042580c503030381411000001e03420300c0c542d180c5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 104285440 1250 104284190 104284199
    0x120403030510080f010903020618120f1c0b041a01050a03090f0b0129090d02010e12100c03110403020307050f0105120a02030a0c0807080721090b040b060a030c050118 73
    0x20440281c100a801d000003840f11310740c1c07c01038684400280075059505440000074001035000c40c154030070113003518902e62204d0b003083c50990a4000c0300c09100c50329800e2042048442c002e44c209404000c03080d2002c03c50140390001d000a415148a412404610200005070456101340e02200c440c0380100c4085841c68866901c2408801c001ea020704864500c81c1090400d10328803441c20b51103603c003180281d1a00840002058030a41030103030107414805d401132105100d071030343e0078030b0407007107a20200780c614040c03002003014002c0c0070401d410400646403100c00e9214983d00412a82600d4009004000a07880c1100b000401e1014042d01c0c0d041000030710800c4190070003d44880d000307210f151b001684900e040d0030358104903070600301c0c00b0081001e0b00050020135504002030b660031011a180805600c903003802c228102009a44001d5042c2e46000d0703015040c00821060309000d2807181078141d000b916404200700480d40903000c003070001c61904000b001190300622144424165000c00310380400e030359 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 104286690 1250 104285440 104285443
    0x61207050909010c090605070c1401031d061009060e010902160203030a02010b10210c11030a080a060e0402090f06030a060615030608161820180612040303051008 71
    0x3a0b07400d101c41c1c0e4441c541210650b0300007291801400b000d2400c0307030030038205445281000c4828807400c03004100c2c06d20359010a0b4442e030804000d06807444485008040580001680c2e240215904103840083c3c2001207146c24850290300c0c01c40e20102609401a402e00035030500940c00350000218100000da203000042c0c034103102419040426800000b42c405504062000340c568011107182004070006101c4c0c10105a40011144d20841c01030004160303000f031400b81c649901e218903c503001d1002203940aa455448840c3c184600310390358081c41007640d540e024804850381038800075406498a400501e00714002481964405801400ca80c6624101c2d110001110344a0b00b000c0c1c5044001620744065035054020710380105140001030203c1c5000ea05900100346a40c080c445003450342c46041105c0c4902c0c0e400144c44042c1078564078240309941410396030164490158543d20760301500e24240c1d1490140142e030392041500070580110390380c55400b14002c00004140000c00c0c0700291010450000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 104287940 1250 104286690 104286709
    0xf05010f06081609030b070c081c060f030b07051c060f0e06010905151c020307020303180109030f1101020d060905100509010f03081b060403170c1206120705 69
    0x8040c81801a46410312900800005005109801c1c810324030108400e110b502450076004c4a03084070300d04400d921a28030031a0210340c500c1d0050450100407844955034480c076042c07600d402d0001002001703030703540c0c540d0803281c1a880b6203c0540b200c018000010207c40c060001010704210b50b82c120b04540880071584401c95120f0741207445003404200041c0950505000401d8000c40c007400e1142503d49028000b400c0a10a04581032907403c0215040c10305030b00590320140e581d800c141c8199101e241c8000000d5494104903030200700710f00d0b1041e003510b0001040c4a40f85007223400d40e4034224046410b400644a50500030803a01a66500300101c000d005164030842010b80071840001c212810030588000c1c0050799508454400c02c200801080366402100d0b00b601100d44c0105000c0d1500c110038065030103140030b01c94070085030083c141000704040d40286c0c03019a110f4a81c030040f40075110260004458000d2001703054840403084040346540c4bc024014050301108181140c0c5d829840b03802086e1060f4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 104289190 1250 104287940 104287949
    0x80d241511030a081005010507020d02100e0301020c01150f0803030604050705040b0c0d030501080705130e03090d1505070e010f1d03030706060302130504020d06200c100c02030405031f0f0501 84
    0x1000101170021480c004101c01c4001c04092034101c0c2844a950001504421034500003071150a544c1d8a41d01c1e00360043c0109250031800030003c40d203035030300c040066018010000050f009400c1d191400316036a5140d100d10307410b95050400441c00c651b107607024000104005080070302844401d000004401c1038040042540c0b280b480b015212000c8449030150540781c06800240300d0350810941030006480f003144103c01444244004150b00c504070b0080c2d170552090100c001e40082040c0d08101c18081c1040000100c0d00824408000c241d541100403514a410304143c18001110b141031002282c0c89000c1c3c12641d0125520050801c110030400a071a5502c03c040071903015440307000030825440c010640c403c50724a102014029032810341d002403c0000c0c898001031403150b41d200d41541010b418040300709418027004206541e030200f404415611451641003518035070800117402c024510210944040701c0c0064002d0200d09507200c84806a03640040320100c002d030350344403081460000c9004003030081 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 104290440 1250 104289190 104289197
    0x2306150a1205011a01050a140d140405030c190c0b070303060e070e0f0405010503150a020c0703060209030d031b030c051e04030b0903070b16110109080d241511030a 72
    0x601c0c081d903500503804e5a10318002d050001c10b1060098041d00074149940418100601a507510f102d15203000050031b103602c107500300355101e408201c100300f0004010001d48201070100e64801c0107004040c440000c103860000e0242d03108540c200040708084000d040140e20a04002c6113080c0c854500c8860100b0803611a80029a44c3c806840c95003015545400b43c40380994003440700e9070424021982d102c002030502d000d09c5860200180b921500740d415580000e1000d429900210340d603042050180d000400060300c640120f03041a1105070081c442e1000d80000d2600c000503001c4003031001e034007c1c00e2039200c0c01e052080401c141e6181140c121210350f4164070b4032040316121811070419401c4054000c2890801340c0c0708200000204840e191015480b1200c107610300c100c103810301e004840242038007524414560904060008011001c405003034102445082000b1010481d85140c581d000c07082202d50504413404c405021050302029522a015070740d0400860902e0030003100c6145501c00f00d03000700007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 104291690 1250 104290440 104290451
    0x503070509100e1216050d05030d05130209010e0403081503010612050607020610060912080412030806100212220f090606021c021b0301200301032306150a120501 71
    0x41d403074065418102d00032108010300d100150b0b40c61750341c03111007540100b52280150061030001c1141c00c104a8500072070344a030901190410301e8900d1082d40156400300d200385504000440d80000e0010441d10890300b50750703101c209886d420103001110000001d030541554840b500410410b84158a19010740c0c4100003c02c2c41d8544207034000c1c10080043e1040507550618001080000c2c0c2c4140c0c41c006071640720f62084084003407450416038510841d80032405540000c0510410b00d80c128152138414041a07948000903c07100340101d88a62640c0040143c4690602c96101c0a002c22482003904800e0340040020050b01e401010242010b15802210345903220001842481d40c1404580c1e1410340f071451030180581002c402075211042c07030304102503201d40034003400c145aa00350032408241260f103010012500802640b8038055109000c02d980b00001000c194901070002c0d903861005000d9103000d4295900c5004030074020500f180c58040c7c1c01200c0c41ca02146960500d180e03200c0c01d51140000194 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 104292940 1250 104291690 104291717
    0xe060313020105090a181103160509010306260f030906040e06040204080109050624060406080411060307020309030705030705091305030423040c08070203031810090c0303090b0c030a050307050910 86
    0x1901c07517a2945600384030090027400070202005003525140304990900c1500c80b140710300100c006000b43e40c08030b08442090070b454180101c2030f114082405200341d0566080c03046400009036a0302c11015280c4e0401c6081004110707003021580b009401031030042c000744c42c007541c44a032242903c548400c1681c690708001c0500841aa400300c4510030b00c0640321102c04000c140340e00140080c09988603100c140000400010200905034480107000200145042c0c1c413410110300081d07807500071803030f114001d01ca2108041098940000c101c4200d94008152400964808504446001306900101c415101c02d100100d441e03400c0c000031042c03035007103103816100308060001000280c0c3c000c0700201c41446a5001803111407035001c070459a0180111441c2c842281e034520304a071800151140340368030a4a40156a8104000340300710b5000c50b4069540e45105075100e41c05a541c6114122141d1a260f00c1001910b00890041001d141e0000f224100903080c40c2141022034520307110100c103240020b40d603001420307 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 104294190 1250 104292940 104292989
    0x110f03030c042301080a1d060405031c060506032701090827031e150a0207061409070918020d0c262a0a0608010501030c0e060313020105090a 62
    0x14001944544000c0c005843e5000079010080240a54252980b0b078a00705281e4800b161108101580c0c0808494562800c0e051a40d2260041030b8880d003900c440154800c203c502c00d01400090300e900800301d03031864440c031002e19101a2100389441d4490013402c24100c400800f8450510150b008280c11680d4010300c0615900740400c10a180009516500b07014225860000f02c00c4400ca05080442d155945020442c1d8900035903804141c500c0040794041150f45142500a0035100717106200501031907420025140d40b8802c01c90b40c15a03164051441004039030351681040b4000c0b4512041c20061a0040c4c020034650031007500c041d602449220400c00c01240e20103080e280c4815038048a1240310f200212450310790301c0c0f24210340c0100d42007100301c0700450b11081900304504c000418060b10035540d500c02170f110350340034462140401e103800300009255001e030200c412880b10080c482451030752503808400801080183c141d0411009000100d801d48030140c108004d001e2004204038022800e0032007a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 104295440 1250 104294190 104294219
    0x90406060c0f0f08040b0703020c0f090403140a03020d0f090b0108010605010c150b0409030804030e0a060f03050709080d0207140d022b0b0f010510031b110f03030c04 73
    0x210100300e190401c0c1008142c0a001c8400c806500040380c5100c051581400206030103140c02c14620302c07000046030010190001400e550700c401c10380e070380e034009000d500030004c4507001110080c0100f81e0400d070502245490364000d21407907482c0c0c1001400c000620340d12104442c1c0441404140c26038400540c814440c1c48030020b0b005055040007444a01d0400c1c000800503000e080c4c0051500041e401e9215480840340c01050004601410410480440342401042c0344000e58082d4007203203c2c0060f01d00142001817584080d5061a01c8121a1160104040b0000c0c00c0040000d0b0401c09221000301d03140b0010700503482d01c0300700b55000f040000d043c45c0c0041280036044044510442541c4183c2c40141c942403414182d00520750f0b1040224450340313900340442c40c0d4078131004041005003000c0120b001d0040e0010750584605a64204210242942c02d50071601d4214002032900c46200303100c01420311600d042840c0209450940c2c280c0c804405105141d41c2081e5050050202c1c04642407108000f241e551 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 104296690 1250 104295440 104295449
    0x7020f06130201020624010c050307062d1b050705150123040504020f04050c12040804090e0105091b030a0b09010605040516050a030c030902030d0206090d030b1f020109080f090406 79
    0x30381c550441c0318030700100303c0c106003144981845440688d41c02800818800d2b6800107801c1803043c020704902c01c4490b40e5001c11030408010a0881841100f50407038140702c1d0700d41c0ba100b5040300320800641c2a40c2540c2e5038000c10422543c51140103142c5040080c0243c0e000c2c02031489038034a1480c00c640039043c040d41e420240b10b040c000d5180008000150b900c0c0490210204025140040c0940320301b000f200c1c451244050140708030700481e0502040282c4000280101d80705000d0800180070079002440c00ea074001d40e4021040d0740502d07006411400301c1254880160070040c12a4004880e035598142200740c11a80320409942d6030008100b03071305290180c9944454410400d200c94003001c4070103000e9001c0c04000008140c2e543d0703801d8060300d0080c0d010b504003d40047c01c5483d40302007020029170300c0200301c503102c1040c0600d910b04e41102c0c1c024003450807840d100600c0c3d03d6000c404102800340030b03014100094215925052543c021580d544010260200103a1409030348010003014003064800344d520 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 104297940 1250 104296690 104296711
    0x30906030e03042d06020708070509042f040c030605100503010b0703030c2010241202030c1206220812100302030706030c030608061e07020f061302010206 68
    0x11032004414000c01200c050740c240105851480402e60f0804800c61419100404d00100c01c0d08040f50142c2c0001c0d198040300c08a104a031f100e10744981c1400098981900c1c001d04c054a409043d9100005050100c178108030050041070b032404201c0c0010b000d41d0944001000842d41c2e4440611260a004907000c140c0d0405040086c51540b401000741c0c624460900013a08050b500c0c52003960403440b4080e05803000202c1949030b00ba04a0321302c001d9881d00d59a2104510485c6400c800c1d07010300b2018001440366030751000800401614000d4501c1d140840c448040380d150083c031241642e5a56108842d4000c40d5040c4001e052030b01d051004030520509005600d0100092070021800044082040318903c0300c0c1e4542808154507000d440da81c0e1200b29400007549400317a1200402d500e90306520000c0c00301925036003031014640c0c52400a4842405448403038007900b102e002092075145411446070840840c4c41120b084042a84889003070480c00c3c0c0c1c0c868201e868040c0140c00b0356a04203c4a0380142070a007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 104299190 1250 104297940 104297951
    0x1050612040807030e0d080409050708150411040512010501061b0b04020f06070f05010c030b1f050a1101020a0203030612030c0a02010f02100f050615030c07150f021603090603 77
    0x100c010000c400000c00042824030005080004c040c803c3c0348200558001030100205180f0a14007604c25400c58010b14088a00d40400500550311820200780604c84214042c0c80380f089071000d1101030154086c82e200a070301c04202c001880c0d01e4024460314035a18060001685506101c2c0040060541c00d12681400c40d07068041004188102c403943d030031503412980d1580305404032020070094003400c1d401528404044a0000c1403203419007000703420703e10603030782040300348031280070060b42e4106004021010040f0148410b4281c1c001d00c0200860f10322814140c1944401903000b900703a80c000c0a0941c010b800200030f21486080480e62031141048180265044c039241040c1c4503507403c00f8510183c1000a40305403500140d0081c019401c0001601100380407000510340010094203050342d880380224408450001c444242d04166400707100240001444c20840b615415100d000900f6224501075841041441c250035a10040c54809c6132011100701040031418094920305d05607210509160904 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 104300440 1250 104299190 104299207
    0x21806040e060d0c120b09070602070b0d020d1d0a06050c07120e04020906130e060603040308180c0d0f061508030702061303020918061006050729071205010506 70
    0x300516407001040e00c544030107914030f04180504a140b80c1c80114520482c4c0110811b000b18400b13002e10071607000040750041ca03550041240d56045a205002044100f03004000d03d140d05a0024060f408945c60040b804910f401c08507041c207440c0302207005a81c0e0180c0707000380800116005003a8400f91300c0000300e02f0100d95440300c5d40d02c111000f44c100700f0400070004000e001ea596906880009001400807600c420401d41c041071011140d01030f221a100782000007501c0d924140088a1080e40c0c55070303600f101a01c030640d42e150044007400b05510540140c0200c4d45075515912064174045010b40d0040443ca0b2082c02d04508035000c081c0c1042440362040424451000008100d950b550f070705890b840e669a00c00380030400011907603000294864845018400000d040c2841010200341100c281d65082e120400707286030401c1c03144200004920103001d00000f05044c02c5880b5801c0c044ca0002c04412004003003011f00498041b11034001040f0000702d05003a540440c4030742405400d05441c9a8a03103901c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 104301690 1250 104300440 104300459
    0x518010507020f010c020406031e050105010b0a021c02030d090308061e09010605090103020c0d030219080403020c010f030f05090105070f020705030606060306120a0f0b060d02090a050c1303050102180604 89
    0x107041129041c032416110321011504c7c0c40d4881d500560f0002d6009280040d40601c07102c0c4041103080039605076082000228041140104446428009800a009402c0075070f00741510360740480c00c100250b003c107101120782a87c2c03078000c0c80c1819101e0740d10000103240070410841132654050003070090311105203c2110030f4990701201819901c890030940d84030050100100d001c0d12404281381b07003078011040219062a055009410442072a03040080889200142154008030486010300140c0c0b200100701180c1d4040c2c4a140040340017840c02140031304c0301000c403405441d025640d081070750f9036a008014045a00c458140ca0700403036072028200141c0b42c00002540e5400103010b9078458940000400c2c061b6076034400c03141c1e00d641640c042d035030704203047d083c400d9a4039001c41c1d00b91403986810000550074903056110640795a8010002031460300c4800074035009003002030000749280020807104e94882c4c540c40c442c0700194818400543c0d1880080c00340011004007424481c0291010300040c0082c084 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 104302940 1250 104301690 104301709
    0x6150e071709010914010e0c061306030902120303040f0b06010203070503042c010902040f050901080d0c050c1503060a0906050607080d090606120501060e071202030421051801050702 80
    0x282441c9405090300c810320050700500420740010030000c8078003140300d445407040d00410318625145055841143c1e456060101ca44202c1e1200d007015070400c00c0034031882c7d0103a80a4200940041c0240003402a540142d030702c0d50340150350036074091350040f80e90010442c00542c0311354045428405541072448a6580315500d004a02850780c0c004214090380c0c03480341030b0040c0e401124050100c11041940d5039094100290300c07d000b01c8030500c20342c0c03101140034281010442e04031808440140501c2c8d10051044888143c05201258580079203402400140c3c1d40300307403d003120750328018183d950f410000104241710040340d1180c0162420510700301714903070706c0d0019151419000130f0a56030718090755138058010f100422000f000c1d2844c003a800b142e1103010710343c54048244a0402000019111485041c40d103008440f24400101170b00110390000701d2030f0f000395404c5031280c1681c040040c0c00b00c4245070400302c3c01040000050740441d5480b074a0a130503002852030030003070800c14074020468020507980b11 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 104304190 1250 104302940 104302967
    0x603020901020a110d050102033405090d1b0b091201061d1f0b090414060303041701090c15120e030334030609060605030f01030b1308030406150e07 65
    0x201d1071044005952503001900000b146d0041c0210341d24505031282e00c90342c0c9042000d160000341c0080045001c0da44d016187c2648000303944078581000040c0c001c0041605410804840604c400c0d0510302500d900305017554007400814000c40c2d100c0400d00184258450080704428244c1e042c20790401006041101c140f100080c0e40341c480304140d0340e00214072410b600c0d04659001441c040d010000b15000c0c0360010300344041d0111824850040d0465010240ca0029950a035168000700020020320756482803582c1d2840c046000403461280f96150600454040d42c0880d82c0700e400d2001c0358070705c164804410140810420350410603010076002c103542d0380c040148450500203510030031800d540a0344000042e2121461004002e070952500010045c24040c03082c0c0e0f807602c0c1000c0c404601540244203803841040420541d0700180c1c40d640b5040310002e0094414a410b190064285e4040f9404100030361050f070158201140b21420341003414603406160344510450030143d800c1c00000e99029920b4100038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 104305440 1250 104304190 104304203
    0x40308070203031201060f120c02122505010902010e030d0e010e0d0f0c0f080705010509060f0f0d1a0609060315042c07140109031e08070506040c0603020901020a 71
    0xc00003880428594800d030304c460800031032641c0000501c183c3c4110500d0210700304d507455080d41c0007520200780c20788100121503005600101426015020b0301e40c054110103041d64200c00e690300e400d10f0001c070000c00c03030041a200d036511103005034195600111400d021100580080580480070b507401000580700e241c103241042003001038032440790740b4080c41c1031840350400e40300d03906002d0070300e4415130b074002510840c04112551440001d0360b81020416204461041c2c5035245401e04850030080554014160340921980500109020001c000054400c102a80c040005c0f9420390080b4414562000c0c201c581c450f103000c00c800c00706c5841740400c0c0c98011044245c80c1000312406800500a0040103800200c4110702a001d00208545540d03c00b454028100907078420517100d4485081000a00b1241404a14103201c1040000c0d42e0316450101407a000500c00100e4a050303031082c020743e21868040e181584a0b40c14041401140c110501c000c0c102c50038210714142030800046d4581540c140d01600c2c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 104306690 1250 104305440 104305447
    0x3050712030e041d060903190c02030312010f0305070e0606070201030518061501081605040b0f040812070317010e010902070f050f0f1204030213020a0c0c0303050409110f040308 78
    0x300741c0100700c05400b10b80020410700c03880f14440c88810088074544424180c0b403140c48081036894002200700d81c2c240f01c24403c843e0f80ea262902041e14040c40452040ba0503101c108103046100c0d402901103030181407a041650201072450038801d20389242e5421502c043d90001e020700402d82e0703131001195003207a03080c01c010981da650b414800c2c0d009500e0b940d060405010f81c808010491401c070401140504098845000701c1e1591909031070040c141020200120b1001c00c824004c3c84611405000c80d0300c40140d11518043d00da11035a42002c540340c81041e071142010070310008041d04040c50280c1c0d00c0e214002401a507140c401030440c810418411142600d40c0004c035402885903140384c620071241c00030300301d400340070604030410f075951240c1a14451a020703800101e802c030403c15040342c0440c2c0d00240f0004100d09000711107002944290210b2003844884280100011100030102000798040c1d19900c2d121407506031844207a4008072251f010703100c0108440c0000364443c200380c80a0f00d402800c81601d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 104307940 1250 104306690 104306693
    0x120203010902030a11130902030c1c050a05030307120525030204091e140c03040201030b04060e0406140106050a020703110a0506030a1a0105070302030702010e030304150201050a0b0a03050712 84
    0x5107500000a501409000c02c4901401001680042100c030182c0701c114103086100c801c00c0c120351225400075816040302003d00d02918140050841000015000c2104510680e0b1035a00d0310000102c1103503d03400110800c500c0d1074202400d2070074103007031b81810b0109207009035116660240c043c80d00c074910794120b0502d99038a0302c0b95058130003404c01d01c2d0701005101c020304860344420301055008800e141c28070540c083c15003194520b0358003680c3c461495a08584a40e8010740144c40042c80c2c107034100d551000300041c40100102680d01440c0100710001d032800d1580c41d11680680142c01c42404d11000f00135080005a000442104490f04032a00811500c60080010100c132026489954090004000c2c88003050142c0e21074103104802d044905030100440005460b40d004244e40076025800a00061026500a0604e0310580030001d080d240b40548650f105100031124594120042c3c0d512020058a240d591041c140b25210031a14021560316603a070380c90f0b03184610300a14801d42040c545080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 104309190 1250 104307940 104307943
    0x301050f01200d050c100e060a230106030903020607090f06120213030515090c0f090603010f1a010809060402210c0a0b093a15020a02011e060e01120203 67
    0x1202c100d100b05072028145100c2c002800e03a04010030301c50541c082c3d40359014004803548500480401101c0240903a03603a40f08502009120104030710300380d0201ca18a82c405003009000840c0640215100001c4e00883e0b0700b0300916242d401004030080c0304001406000100150b069001201d8451601c200d98040b4425243e0290148a1809a80b0700c0f00603008410840c0210b0000340c0d148424110001660320007a8856507025030700c04458001ea440d0803000454145800c01a510840c003800120340c4104201030402110f01024840c400c0c00c03121700f0f02c021150ba01c00500c0e604080ca100051140d41041d4000a2a034808591401c92050407858000307002c20b000c0c041c460b0100401811820b4641d500c0b0345030003559010070020f03403150f0710040800b03140c0c0030008900100c084d40b04400c02d081c2d00031071500354000400d5500955142d00d01040c104510a810b000820a510143e4008100901c1e1800500504040329070001021803d16030140700010040d69200e04459880c0021050203040c0d00109 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 104310440 1250 104309190 104309237
    0x21c030203040e0c090102240114030109020d0c0807061403070e0d08120106030c03020705120a27090b01020307050a020108040c050315060306070f080f0c0c100f0506060301050f01 79
    0x48404040c4810480402944d50141c090a0020f03000d844410f0035603079001d481d6106c060019011500c5000052010164490055649000150001442c01e0b6590000380d6003115108048801e400c5410041c0803840c4240083c20080100b4203200c201c54071081980c07080e60000030560000c02070800e0040ca4a03585d49400030000a0f0411031550340c0c0d01074002c40350f820315000d001c0c44012034140b4040481d001d02ca84211110542c1003005007064070303902c1c4460410b6502c00d0f904d190400c0124210200b0216038038a00043c10421480105809403501e008202070b01c151901041c1503420a200700c6001c03c030003282c0406a160709180049a9a4591804040c410420780000fa0940300300072801c290310061440d4603001d0740d42141180e0490b03a0f0041d00302c409882e400d03882000681a40041100780f41588151600070415415036070078003d0004040f81b400fa0b003035420704601600e42d0440e041c15140ca00c00d8503044201a1078440c6598106004102ca502500102d07604009080c1310b42003c2c9000080c54 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 104311690 1250 104310440 104310449
    0x3040503121503070f12020d05100e01090c06030b0607060504061d030a0201140108070b3103110402030103120f0e12010b3f0a1203021b060103021c03020304 69
    0x808642080c2c2403480c0180d10040940d03010744900321021a4200320800120b00310380d44201c0b40c0001140039400e0005840906004170b6080c450b58100b80400d05a900580c9020b2542800010340c12000c0d0030864601c0c0041da020505061401c14003042d261144401c0755010b40c0c11040109090700c0703601c0d002e8010032003842445240076502c0c6c540713034480001000070907002d052030713000b807203804a001d41030491400280324540341584a040304104c0e44818002802d034002c803128101507140c11008940741c5155070b800e0050543e44a07510140f00700907500600c445d03c0e2005640844c1598119510120311043c00f034850707010b0003400b800c946101031084528409801000d0203040302000340703c0f030311170181495030b040300e11a1810703190046e501e0200281d174546151008000c420a2403507011110802000e42d4910012801003600c03c8020441e6203c1c0710901000990380140d07642c083c50350b013028012007103da041c2c00c2e400c0f200041001d03a41c5e100205244582d01350144102d4030407490b043c0c0c60340c89140d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 104312940 1250 104311690 104311717
    0x3080c1207051e0d020318070b090f0f030703080a02060c0f0406030e031314030f03070804030609021f170a020901020601091d0f0109030e09010e011214010e060a150602030d0203040503 81
    0x40015640300c84e600518015001400a00081006aa0740e40d4030b030714250080e000030305400c1c005400d031850f08441094416030003400d520606810180403c1c1025895082503402e0b00d03001481c148050341c10400d541e8016000100941004615840c0311700314031036407042d40205619400d0180204200b070048803240c5010182010116580e02103a140076540d240c4040d20900508c0c1c0304035544d171000320031660085e5100c1600c1d842c160551392107030f0060042500c1aa0011408040e40b12a0075514052424805054880ca40e020116140305690407400801c600c9000780107000c0081242d0b000100a0f054425040780402d58080c040401c0549048005120b0000c8c0f05508149800100c194420103c2c4c81c0243e0300d801442d0084e506011060358203100e056440300240740104000041c184003141558400d00c807101c0403103107401c8a2801d5031800f015040d519000324042c4040d407261845040c1000c0d042c48401c1480d84e00c1c0c514042d449001e01990700c0d21481d0000001410090140201e4817001903441 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 104314190 1250 104312940 104312947
    0x9030405060d2a09230d050a170408010501060e0603161103040306020d060e0105030706030c0e0d11011e021005090a06060609090501091a040e1005070c03080c1207051e 74
    0x8000010303980c039001504001c644c60746400300b91001c07135002010850100740b03a03001d51010064248250219921429107407401a1042c00f000034040300c40c104440a283c9440d9a260b030f040030140d6003150010b0380040140034484185031101d80356101583e03840351403d41003d092110503100ada503200642500309405000018010081100c55401b404241c99400c00400c2010340711440f514120340b080c06116455400070b60b00f00681c1e4400d80161a80e1000b41c41c11890309500302d000303d204400034070310407036640ca20210000001d50b07100320b10b120000300415100f4480035030b900c1d01035150340781e040000f10159111800504c5100040180740c0c44150310550422040e83d48410061106425028003802e942c100400001c6964403400b841b07a1280d40c1c11480b00002600c081000000c010420b520b41f101d0040008c2415000001d01c241881099691164100c07101245030013801c1c40c4005000070940d903003e0ac60090a4200d640d511540300281d401c0c01640c60a01200c0d034904074a400e411450701c458000f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 104315440 1250 104314190 104314241
    0x60201150509060d0b07050d11030118050f0114032103091002090a05130e07061e020a05070512120a180806090a03050d02041d071709030405060d 64
    0x154816445108000c0012450a8450040240908003543c030164407000c054140070114a05030035050f00084641056445d1099240d0000192410001c000e9883c80c0003000400c010104d03914504150903215004102c103281c45200c0911840040c065503601005c8004014100d89003089105844560000101c0180c9144901d491440d403088401080c1400b511060b00c020700000d009407007030b02c400144554030300f504100c24404508071044409144d40d03150940580d000c08184400341c06000e8560b1084001602d171400c4852580281c046107085511071075031000410800b0a04509640c412504115039100c040c00c4c030b51410440c80c03000e9805000000318000a646c0011200c40c01d1701607403880e25441e9a942c0b0100742c5402048582600c0f17500020b84c1c04000038460320092802c50003091006040c9501c80c0301a902d13041c031180341005d9503c010f100f4000e15a400600301c5c03000502e2290700144601c1d0504210743c03240264403955000f5035021464a0300d945860704840300076480341402e1200e900d5071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 104316546 1106 104315440 104315443
    0x90303080f060d02130b01030b0612010e0c09031903090e040809012a0807060b0904020d03030504050a060504080706050c04060e1314042a14010e03070305070602 71
    0xc0c40f0b42001641c403030742150400c1d08142000540150701e00009002c4a400e0758901d4410342092102c01c000c03124405032281076400034600c00f80c0c50b4403003003261881402503074100380d8076016030401d004c4a10710301900c003a04030b030196507000c1c011640c440003e0725915083e14041c040c0c010822807035445502030804100300e49105401c2d00c00c070081290040b6404a4070480886282c840001c8942c144440c1d40100e41140c40110340441003803c0c0341d4002200d084040b00000e083c152180700060611200340407440d0102c0d040301c400c5c4418a054a491803060303010200c110384151412010501246401302603c00717803200c5460b0356100707234848410044c070740e1000c0300d407000503070b07120340061044005261a46000d94810700c800b824001c91540307a001d03040f0b040083c03001c001d01e61820801a5010000c41000703480b40a0900c0c0c1546000e1401203400e1070950381010307080344941c01000520a03030 = true := by decide +kernel

theorem cover : BRFrame.Cov 104136690 104316546 := by
  have h0 := BRFrame.cov_init 104136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 104136690 ≤ n) (h2 : n < 104316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
