-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0833
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:03:17.87126+00:00
-- url     : https://prove2.me/submissions/e6218edf-40cb-492f-8dec-0ffdde0d7643

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 149640287 ≤ n < 149820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 149641537 1250 149640287 149640331
    0x308090d020a05120c2104140d1505090c0a03140606030a0c06050306010e03100f05160815180c0a02010b0a060e1915030213140603071211030915 64
    0xc002094541e50540008540c00c4d45110341808200d181071b040d440d80755641c51a40b1400130459020b03100d09808044030481510040c1001426408104d4118a00c410a041e4a0015101510000f004c054150048408240b06507a03003800403409140100103d610054180c503200b40b5020018007414030030743c49a00309500051610072800d00740d4078549403403600d13511178000595003502212000c6074503004000424024000300d0b804001d8444a142080c84142c80b4007856810031200d40c000500015030610028250345e02445405640b094090000105150596141001d001c0c050300c1180d44488005042e4042690901a04c0d103020302c1100e0314420b903894002c01512203c0da6480c100c2c003c01c811200b820085404074456401071140001d0080d03000d40c0050014000e42c064075134038141c3d039403000f800b25003002d50904410701d4040203082c0d14a503032290700082e6914580007140c4143d05460740d0003401c038a03c854000e58001c601c1c000052074195608010a880040000c215009840440d00180d0350 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 149642787 1250 149641537 149641543
    0x61c0e1207050f15150a03020607060903080c09030d0e0d0c06020703030e0301060605030f090a080c010c080a0902030304060818190201080906060616061b09080d0f210b0901030308090d020a05 84
    0x5c002e4014601c130645000d0710118100e83c041d03901c0a540408086084400c2c400a508101d000c00c2c825501d1400356902c2c0a0390042030b000d1003602e660160300c000c141c810001d00544071400b22040040865443d80b8081e0750715506200680c010320011303082040104201600425081540300c0c0440c000c0c468903040c20001400c03808020544501c095030300002c12041407040c484040c940ba0401d40c010703030f07500341c02d20310310f0182480741e910400040710f580004401c80f000c0e220b100036031a80140030318134080c98980100c8010101801d4511281c02c1c003e00785994900400c503802480380c004514010100070780c000504401c3c4001e102000300e0300900200500d40e51510300b203440400194001c4080d403000e43c00d106000b46044401e0000c509201e424400250b80c006102e0800c540b41c000c1180e407494000081294401801307048600441c40401e400c1d0030240e421381e02000b0b00d500c44040000c0755909040010303002c440a038000d0300400c1041e400c1c8108c0c1c000c280f19114008501d0300040c03c0c22100383d51200c6da = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 149644037 1250 149642787 149642791
    0x6050901170a171201030c18090506042604090902040b120a080a02210d0c050a0503010e040614180601140d02042003040c0612060302061c0e1207050f15 67
    0x855541540e00c01c0611081105561540750361301601c100540c1c4900e0202c01424190003041c0301a094180e07445540b00c064010404490f5008003e048140c850766181e50407660381c0180c0101c074007415542402c003022001302400080406840c0030910f030260b801800121100154458001d04a4103030500c149440020f0044c0d4241d072100f206a540d41b01c1142c228241061320b04005081d10084404181d0b9204403000b500000b40c141c42d04200710360039507505484500c1001c19640100f00c05000402c80c4da2040c00d0243d50144c09684042094010800c80b0744140d503044601e0341801503d080e049140d258100111809030070307102c0100c0084500390000494080c482c80e4001e10442e00d031141c004032000d52801611000700380703094054481c10613213808608000d060003408001382182000c82d070403201c03034080c1d0011070340c0107031020313144c0035080c0c8041001e240c814200c480281d4941148512003030080009110030345c0c0d0701a0140d2030f100c480c50400d0410f1400c2540c00c0302588050300780760300320020a00007a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 149645287 1250 149644037 149644043
    0x91b0306060b1611030313060c0b0601020307120809011506031406060408150612060c070510020901080106030b040605033a0e060307022407030b090403050d11091306050901170a 78
    0x31003003040d001c0005c0d2940c42529009801840e680c503000400035002160400317018407540d82102c1070b64814004981e45d003c0c4000141c68a0580b217410030030680600c903981e801807a02c100101b4203030040000380c404041e4660107800042c0c1c0d281a0f076910140c524642c10340000d400c80c0d10313620305071820001594811104280500710344402000c245641d80c0c0c1d031110b00942d0208411f840c1103140c01001d032451900881d00030380d42e60081d8900d240c0b034003100e817084030038212058541102d240d0902d0011002003803040b030a1908140d554001040690382001400c0441014508c0041d82c401044440101c9811809004001c20f60750381c060070131300d074211110440054040d2201d035140c0d83c65043c00c91038404034000503c2003110402114441411411404d840740c04203440501c040400a400d11411000440307010b000284c00340800540e00d040c94120071200c0f003c54450314203048520000400040d281d00c000941c465035281c080002e8209850b0f4140104140c52503890b0081c0943e03201503e41440c0d200007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 149646537 1250 149645287 149645303
    0x403030905030d09050f130b04091109090303070c0f0203010f050a020a0e0102010e0d050f1e0d05180a0b09070e0907060215011d07090b27060a021b0103091b0306060b16 74
    0x141ca0383c101241e01c08240c1c40c4d0009c0060014007050f0a00c1132403880707001c18042c010f16481001600317419001040300c0c0a11f0780e5036940e0007040e0403a1602403244c00c505c00100d9055480391786404d1100054001d45010760507109005aaa109540c80905200c030f55a50041c156410010b1420480d00041a00f84184805040c095514034a80180808a1080701c1400400407014142c2d00840c1c0c0300c11000c3c05107000c0310350080206032600304003807682d2000290302900e01e500c04800c0c200050b504000e084e80102c0c1e000c1c11035401e9616005d140354409003c951462565001e9403042283e25410442c00102085a000e6000d1950422103c81002e42d60a035901d1080518540811341040c481c407003120080400c419020307285c0c4c1082c0101d04081080b5840c12204a920001c0703251249049012180390107169001016941c0206001510b00c10900700841d050581c1c0708080c1c0041100405095856441c2e6221584524210b1801c00110384141d048215800d81c24411000b080b0b00d0880c000072a540c0003145 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 149647787 1250 149646537 149646559
    0x150201150b070c03080703080a05060609090406270503090a0e07080a0207031202030a020d060905010b090f040e0a080c0609120f0309010609061403060105030303070504031e06020403030905030d09050f 88
    0x203031005014a13400105150030014040080c0342c0e100d1032882c02024241002d0142d40c9456081001c603009401d81ca560094102001c200059040c1d80107183c001c0c4404544215640e00c911103441c1c0c0614120b0540b015000025a1006450b050645d00d01500c01c2201c0b40d42b07a400c0024004006840003440784080c0c0340c2c00100e4109050003009030303542c00310040c90150b6892900e800c002001e50010010031400508003100418404400e01a090590f061020450f00f040141d40c2081506c2540303042e426042a51600d021440e10418000d1012880c054040c1e1540c9035800c4003503034a48040148080760680008040045900c1b0380800c9550b50003502400a890303444040c1e030705e401040c2070751021084a00d0420005000070042030f00c050050021410b44146a80e05c5040c5a03d80c03108481e0700c0c001540802081c000618900440340e18120400b0040c3c048000070390f5080f0403a8802c0d081600425098841003181d0b00d000c2101c0d2001c40c2c3c00b803820000e01071a01000c55043c156002c071356442400f032412 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 149649037 1250 149647787 149647793
    0x8010b0307050c0613121706040207080706020a081602011b111504030e04060509060f120f0609030301230121090203070b0903070519060309020112050a06150201150b07 74
    0x350703142110000281c0c4c569040900521004072000c1100316180f148580480301c616020300d40e048030b8a1400500500070ba50f803001004020742c88514112042c6009100103408035219201803e8030205640b56110f003400d0403c81c070310400f1080384210046a060144010300a0803104002c10b502c18641001c2c15115009109139080c103260344001c041d4440d1040401050590005000b81d442c54169000c0002035158010311100c80300480780290810b4001c6030351612414403184100100000206542210394815042805c2c041c0a459105442d40048014800d00c5045c0c007440c42c0c0c4014071280c4100050706480081c1c179140500f803111240b88010070a03e549001c0c02d40060a0303c503030043c192040300c3c1d00e0700340f044100e400c580c442c14080c1c400c503030000c2002d04081d114050f0403541c004040d2605481c1040c100d0103000200400c904001c240038100c4080740b070030302906006858182c3c000c42c0e10bd06204002054511030005c00742160304014602487d4554541920107072242c0300e841070355808040c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 149650287 1250 149649037 149649047
    0x90e19090204090b09070f080309010e0d030329030606040504050619150b181002030d200c0a03020c1e0d1403070804091107020f0405060d05030301140301050a060608010b0307 77
    0xf038000340c2040c0d03144080001030031010613290191882d10a90342142a01c03a001c0760b5880c00b88050b107901049440c030080040d0b280500c07250210364401e20780440c280b4500c4218055800c07202c0000c0b00e280c10a907080d5285494280070b00c41c0e00c004107071401c000a00e4980c80b2986c6e11803010304000c032640000c80d00c4e0403080d0006d8002c0c1c003205d84075003801d05481e17070741d08401196640704d050181e50303152800b03c400c6403501e0007002c2101d80030013580c01141407410158540d0010000804c460300f100d58201c2c1446090790f03115015015211200028061038160303800d0280c18440840e185c2071103030420200c0c02910141c03404c0300c0c0962290035158400c01658502e4510980401c010304050684804aaa5000c011400000b00156181e00400380b1000900c9615080341d0b01865000235845204a1102011418030342d00c8a035000c400284000c00000c0e80f901c0f512b04591081c1c129801414441c20b5991050909001c2c0079080420076100b0031003a4078055005020000c1070242d210410400408201090f1043c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 149651537 1250 149650287 149650301
    0x170a0507080c100c051b0a050a2409080903010e01060303050318070306050405060702070f03030f0e04090f03120b09010b030411030a060c02010605120a11091008060c0703090e19090204 81
    0x9510f080000346040000a0981c2c3c204907100c00c25a00f20154001040401041c041134a641c00002000c1080c00e0340d41d0122110204000031070080000c18080710701203010700400500314081c512482d130368007984050509503062040403c0c3c00d81c0c101401040003032b03030103821a0b03841442d10002c0d0610020a80c903280c01c0c40425800580b0b07040c10310050100303010b004a4194041c0303440340c00b01d5651665441201041c15170301d1202034085244103641d0301d0018080c5034015002140140002041e4110340d45d824500f840c105404d80000311440280f0b048c40401d8031503480c1002d03040fa5545250742c03400a0710085d62000600c01030903c1c2101409110545040110000c080d03440072052008201c2d00034003d008005620071315119410901c41003180e0603012072106d4540d034100359110012505d1030103000f0074840c0501440d08484c2c2c2928005003588090012a0141000003020707036440e21942401440304e965904850103031100a4280044c5184984d00e56140d0014510041207610390342c0005801448a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 149652787 1250 149651537 149651563
    0x216051507080708181f0503060f0904061e021c152103031a01170402030f0d030b0f0307050901090b041107060209010809280203121303170a0507080c 66
    0x7010420804000c1d0b04006030105181320710100078940b200900308a29100c41d403100c1075500d42c1c907620300340103244147d004643c8202c0207000c4600840b240030207e84600d078100c406075001c079a02c051141c3c00300400c9100d0300b4100380e1100258141000302c90911003c40413a1000100d40d592107240d02291031400d180035000745002c03010032256101e4120956803044811200701c0c0080c1c40c00c1c2c2c04800440003a41d015411380c00683d51130002015201d04060b0b00040500142d1780b602c110602c25208071000c03c0116800380340c0f650081384d0114460b013072120381144202c595110b908070300c90034000ca4680342c10107411100103480c0801c280350318101280c02072142c000361128104e000a004401e00c400d5030001d000e5880203a03260a4075036103081c01d42d87c45200c4da848181500701c0001020000301c80d85d1301c5d81c07031202e070009003035131900c0310720200c0400c656000c1e2040802118110f5003c00c02e11054604006d4408552510540b81000c9400d00a00c2c921820710b0040500c0d5010911f00521442000100c0051103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 149654037 1250 149652787 149652803
    0xf03030c0705010e0a0b011e030203160303170717071407030804020f01080c031801020c070801050f0a0606091502010207020a06080118180605090f15160216051507 72
    0x34030500010469200e12010758107582401c1c0315507040c920004900b8110780c0c002560040170307400c22000c003520300c0f544070051b412071100e84008009a501803004034442c800f00014581d1161071807070b01820704042c07007103584a4040e0310010800202d81004403908c48222285040f01345680c0d000081d0750401680e0254500c0d03800c040382030010160040d80c92400341d4000c417105c250050180c001180c6d4030704100d0300f0080d0b41005101107460403800c0000c0710140c22100001508280500e400140303041c1301540302502507912181440703144040c601c601130b0400c108410521400e402d000014040102520401d400c50002039101c0300141d200f0b606480c00316a0080c40e4084040d95590010a660801c0c0144581201d00b103019a00307010b286d103d0b032072502d50b4002c0b800e160f001d2917845100040c100200010700c0c5000324240340e51580014880000c845480c4413050a40e802c005001c101040b42264000d400e550043c1e10035081211441245000c1303810441c1c4188500700c41140c4a60705000d40840101684 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 149655287 1250 149654037 149654041
    0x717220312030608011802100c0b040b061014040501080c19020c0306060109050d11010c051002192606040e030406050403110a0302011d0301090807080306010305071d060c0f0303 78
    0x805600590411082165424084251150074070703401c80f48038500806c038855501004100608007028140310b066070780d0811144080c1c0356110628951000c03103044480c040c5030820800c540c9071000c2e9204201c0303941e00c2c00d54030301c0c110540c401c5500c0c030903801054103002036100003448001c2c3c1c202c02c031640c140751a2500f55040741b003400040c0d13440c4408007545200c0c0c010b6000141c120751080b50000d088480040045014200b43d458040581c00c1c00c0a146041000d144040c030040341b41040704180300100d10707a006070743e000141e409041c5541d0728140c400801006010100d01c641e8000c0c1c0c00b910380c8a10b450802115102d1070700213130081c1003030601d4094500000c140010ba60350020050000c43c0e0140d4040d4a009060804000e40f00c4201e00000340401c255142040c240c0c05010300300340c4103800241c00081d0140e8140c442644a0700700e000216100c00d400000c00100356814003480360080c0381420310100d110350700d1402420842d284191a8010000443e415641d41010007042c1020f14125055a81d68 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 149656537 1250 149655287 149655293
    0x1c1104020c01020a030c0534081912150b03071826030309150c0f040e07110c0a06030b030312011e0803090a1211040507090807090207172203 62
    0x307508594205001720349060101403419010380c0884183c4d98640140d0144410020101d80441001c00246088001a80d0400340020010002400103421203544040303074981c4910300601030600201658000703400c010b40080180341c03405450084d1510700803610303229502c0001c2190071a0040c109a0000f40700a400003910320130701e92000380c440308403269000144009481081d605c2c4002c0c0c50249140d80b0401703640e55400070a0708096000780c0d030000710614062460018056a400035004025030303840003014040f025810680150b8100c245102820b10009050700240d0803024521a9100f8103407500c01082440d50148203d5003021403a4880524a50b100c0e000c4442000403034a10102c4180005004038040300000f0980e034440a0040010800901f02140c080761071401c0d0004075140800755034000a2a6240e00816100e03050f0355550030810b501c0c0900b2035103860300541c009480d952041015101041210405040500e68040d90342ea44850f94110b91010410f8484e11901c4040410404010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 149657787 1250 149656537 149656541
    0x60c09030705011b0b0f0915041211070b04080c120a0f0809041503060b1c2126040302010c030e03070209040804030c0801020d0615120f020c0d030608010c0302091c1104020c01 77
    0x2812684106c401094510048d003041c01d20640e030190003041e94080e11100340c0d108520f201409007010042d0350208c1e50713420700500d081e002500001071603084000600700c50304040701599060b020740304c000e0084580e141c070b03018800040004060400000022007000640300da070040080d6600301f6042d81c500c5581d0b41410b41c010440400c81a202d0941040c1503011031800c2003001c0281d0b82c0214450582104a00055501c20701d5007500c0424003404116a480c0600d2078540680c1043d9010460703c0725103481d290090855541d508100185032404c00345a11442c03000090320460359055440040c3d1f5112400c0031240c0740504d520050142102c1300001c00d0703008042d00501009a21200207001064460204148400a40e04001d0000b40b0380c481c7c0100011094104504200301e02c54018900385030f0035403180c1080640304a86d008070340c8505007000548000d2007005180c8440340b500718140701c20314000841400130310422003004c103051f07030b520014490507444003112820010021941d42024448040c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 149659037 1250 149657787 149657791
    0x120f0f01060b040b0a030902040b0409060b0102060601081005010e03070302120706080a2003100f1401120c050307110f010c17090c0108060105130e0103050f060c09030705011b0b0f 79
    0x1499424441c001401000402c140c50640d9001c1c2c0d800e03030608400a0302140113040b480c5040e68044d0302c40c05801042d4880c1d20070043c402c0d003d1000894030b1802c0d0b800181c90309001a1040c0d0400c00d448040160b180c111000c90320a403482480c148246c2c0072001c00017803402c0e0700c41c0c02c0070358810301e41034004540e40e500085a2040350159140c00d002c0d60b0b03402907800e0896052201510b40c1c044004610b01056014074011a07101c0e10301c4041d2604180c82d0141503542c80503e0304108142c10f04030041e00d0283d82c0011410620000b420340a0000481c03113074004160b404007034002c406000000110000485003840001185a107100c0200400b950a4000825040030401110008561080840c0350b5100c0800c0d092200c13241a119034030f580e00c0d00d1004403525072041c90702998241e052000412032000380100c00b4025402080100340800810040d5402c0c1503000d42a058618402c000b18012070303e0200b421000c6030400d080c114080c10841540d80c4c00c94080c0c0c407000348281501010414100b4001d00780d98 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 149660287 1250 149659037 149659063
    0x100e070308030f180c090a0504060e010903080615090d080a110d050703030605090f040305210f04050c0d0507030204020a09082a01020a02010e060d0e0a050604020301050c09100e120f 80
    0x580700c0c2d1000802031303155a641c0007040e402086c0320000800d810006c0c2c1155070030501c42c1c4030004000c5500c54a483c01c4540b6050300f180003850181c1800300f00d2402c01070800101c0214001c0c1840c00340544001484484501401000030a01180030300301c16014214014900842e04c0640b00884822500200345500c09032048010a181030004109400c040081510402424402011644942d1010346036034005492034400b0000464502d10345421035100315000b01c0c0719200043d03a500301480e000f81080600c2084a02a603141c54040006c00d00028141c4212601501e0060b034174421264110b603401d4454000c000e46d8400c0e844183d031012048059090b80b850854848488a00304600480c8c451002c2003020340041d100c001504013a18240d4010908007042c0d0000090958000d140782e410000c2d0f800064420750031203010071003542401e0084541c00076241c0491813811184500156580781c03050042c0c020010700e01c2c07103c0c1907600c440c5c1c0141088105e0b80304464081c03081821035030341d13901409001c2c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 149661537 1250 149660287 149660311
    0x90a0504051e0618030415090e010b070203070b0a0207120b09010e010b03070b18030106330f050c01060503160305070f150804050a0b100504050f09100e070308030f 72
    0xd0104100c0b06810780440000c0d420190003240c0300c0a108505850030422652a28001004006000a10796485000d0005151540f610035450f02c2c16600480c60140e000945a1008026100c016075010842200741d41400110039142d50710910101d01c1c03c40b03c1d410a00e61011021180c600740643d000c4001d22881d007040007805004203021051b8240c070700300108560075500030003080c040c0070b585001400c451418011406100d801c008000ba00359082a441054010b80c54a901c00d048070728500e10384000040e0300300012442010082c000c0c220301c01204d48004108001c03d101a40e121700390410801003800800b2030341c4045110141d0250035174980300c2100c80c1e1040c3c000000750fa00004d01460100d611023000c2400e605000f42d81541c181c2801002200c50b0300802502c003000900c1032401e64050728822225180d4103062a0601040341e10290403103001040300d10402022541c0028050b00c0358039400c2e00814180d00d65041c80b480c18a40d41c0008101100100401c055002111211807080d01d0110f00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 149662787 1250 149661537 149661553
    0x11060601020d08011214060a0506011d01080f0406020910030c02070905040b070c031e03020a030b031f0213271d150c04090c0c0b01050114030a0905010b090a050405 72
    0x6a0307480030302d40d285901080314403004001d174221a0811001041c050141c4614001011245600700141161101c0032070366181c05004a0756441014100c244c10b41c682003a011758041e400107454030800a240220049107400002d04014890701540e04100c00501541e02d920390300c2d2000303405020b4240100b4014072036540c000410040a0140034080d42d04500321440a072218a412500b4400803941074040c007901580c59030422070b40b407440e0080c0d01c00307980d0010b1315003900701030040c107640c0030420a62196110302e1903a060400484014551249a840c0059030303003c400440172080c801c941d201416008a0341c019008038103000314442072040011004100d5003803c5540380320f0b815559840d118060340440420b82194403401d41098002c21030b141c039035080070380c2d4161000c1a02c0710302144600107070f694a6003104100b0800c581c00e0241c042400c0c1610f03424200e1241c1e2145d0301008000c40c01e5a030719000031106110007035005510031000a0040340e494a0800d101101030700040d107044078103100c0c3d240 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 149664037 1250 149662787 149662789
    0xd0b040e0c0d110105091504030b0705030f280f1d03030103051902030c100c031205060d0305160218100e0c041e0503030418051005061603050405030d110606 69
    0x50400100c0c100a0407510344020300d44420b0030744107182c3e28180c14080100070840165035503100ca64100075500248030340d203038118038085400c080003811450600000f4400e0128101c6121000c076032044801180c1030180fa151480400101601c03540c4880c3c4511b46504200300b40e0707654200560303144c000345512405003958074903540d80b07200c01d100103041500007419031541c005941c0ba103d41d03d203000a0031a140036980d81e0002d440c81c12211000703000304000100742020160070490407100c5000d065010080d61a0013400700351003480006009007000000141101e00504405001e402c0c26009020116141518230108880300700a4031583c20000703d5590000c0c4002c0d161380194401c070522034080d030600f841c0800390b441e291008140800061015440420103071401c0020b0401072240b12140d42502d1035595090b011960701901e005070001c0b1400d01409252920340c12a034a00c98a8054403241000d242001c45d40382c05103401c107a80c940104183d4103c415840700100d9000507006083e01e45985031a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 149665287 1250 149664037 149664043
    0x10204050a0f0b0a050f070203030319140f1303020106080109060e1207080414030109051209040c081b03060a1d0103020a050f0a05010324030521070b13020103110d0b040e 75
    0x40302c0c2c00012801003102003100741c0b142e0080c011840070711b03040750b05290301d55000034150f400448060300000d03003124680d15005900d00422020300c00c6c203911041a4100b464040d5030710640106400b50b00644c0e611403400b014801d610280081000e0f0307001304060385042c41c01c1d0016089030320b00d80020788240060203080500c090304035800d5650144101c0d1415142011400b03010111140b441e42c5035688802034804100203024035882500b6162410359121074003002c0000305c91400310900c0070815400200100c1c0c002000560b03c40c451440703041c5480c2d0341d88900084202805410021684c04d04010461444d0a28880740d41078a04c22a1021111038407602444500090303042d0644e44092146410400e550180d80400c451005c0d5a4840201c42e40e101000710407410513500032110365000b150140c24000c40030015182403004001c0e1140f9000711606e90b02d0401001600c40c26050410822007003c581c00307980842d00d000800c451441e01c501035003294000404410030407a00580c140324409059074804 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 149666537 1250 149665287 149665289
    0xb0423030301061d0a0e04030306050316031a06041805010203100e061c031b050a02040c03090b0103120e0909060604050601090501050a0309080d020301081f020a0c080c070b0408010204050a0f 84
    0x80d94800c58816480b6440f0105504c0d50f04a1607082220301300c0101c1e82c0d8008281c8a84524020b8801003003042c034003824103142c12076034440300e02c0314190b4141c103000040031000d0001d110900e04000b03125a84440c40018010801c03007000541c0605070321250030405c0810f4000d988a208a04555076085590b103400102e23040040b2181c2c0d17400000d0324005458003084d0300c0080f074000d01074609560008074000e140c1901c1100044261395590144c14084110b00d070600800b2101e80052900388012100340c5e8403120203007018000144010414032407200003900c6070070040740b404001042120b503800c080380c0090729900c0036140300c1e000c0c0e030814000401a50282d0040421608103079070b03451804202c000200c1c01440d41e000102ca001c40708100c00c07514001a40080e50103040c000002c0e1a030050110031003e8101e4824030032050080c0188450200103410038005a50304c1d130032000941e502c0000c608011305100180d0484c042e40f90012a010070480b8056000c0c2c8161802a98261003140e10750b60691142c400b1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 149667787 1250 149666537 149666549
    0x9010c020a0b0a050403020f07081e011104050d030509130207030f0f0203180a09090506010f0603051504020304050a15060501020c01020715051303120e010e040c0c020402090307030b0423030301 85
    0x980b40030904121590b44020b80c814024411b940d240c1d20781481c81800c2a0003940240031aa000e440c40514204600005955a15a084c02042907400d11242d04025014500c60030b4407441c5d45402140a16008800315552401300602e890812400070301010000d401c00e04007640010a00061451207a01500c00d0303c1c2410202d070021070404c2d001120001507803494070080c51b000441d41d030b00012258141e02484918910460240c401036040c0384462411203c50f078071207801c2608100a01000c800301c134100d44050201079901580d41d0f0743c2e03824520700d03060052000416000a0807811500c2c07025580c4081c0039035100740c2c04d5451680300b0800481e560007860251649040116580d0001c903402a03004100341d54800c043e01240a90b20740342c030b800080d1100700260114100348001d0308150380c41620450004011501000b58660b010b40c002c003011400403000740a190f00041c142c034a07a408201040040d90b000c4401c109600c0d15241458090041d0800750402d41d1741d5a4907104031100210580781a140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 149669037 1250 149667787 149667803
    0x406200702011205070212070503120709150c030c020607050a11150301150905030607020d1214060f041b050c0f191205070c060302130506030108100f0e01060e09010c020a 75
    0x35140142c58014003029103805c00390f200304101c400d11403e281b005030801a000c0d401031a04c941408440c0f410400008203101c0801c405030798244000e0203444500a0035090514094610020910f0103607130f400071500020758000c00205409082040c0007908000851140c560426000032100a1000c03c6041403070000707031a0428401403002d014214040a00c0c00c1075032034115445aa11800309040c01c900340c1d100d00050b00040c150b42003103604405180c500208080081080035540c1100c2819813102421040c4141034401d28074855a0307407030b0001c4039001c00802e071001c01091003d202501c15849088201c45a0040421602e10800046406800011800000c1c0719030826983c8800e01c04080c0100c43d024400305002d401c010804880300c1c81c0c060f28054400594511030319184c00321b010019407043d4814441000140007141d8045020400300c52031043c0442ca4001c03000e4201b0242c042c00825038150341ca405000107506104182c0e6600400300080208450038140e00d080f41c81d210301940c0501044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 149670287 1250 149669037 149669057
    0xc0a0507150c06180b040804030b0906010b1c06080d0203070b0f0417030a0f06090b01081308180f120706080c0c060105060c0c180108120928030b040620070201 70
    0x9946400640014580100740d01000440e552141160351064401f52641c86001c1000d00401840030f034801e4101102d140200303141d614064403040c1ca0f02c111602031442405586a00314510402d0700704502918200c2c0c1940c14100a503407000350389402015091b20394031b0020000c517090700f019070581805150003c180300102c060030310305500c142d80701a202d540742c03a6032002c4600e404501c900c82da0000d4107902c8808680c03824500d0004009810117421001188120070030600028102e0080f03d81d0541c5850380c2d41c664203042e00018103c000c1407a41160408119440319071206004030304c0c401038401949a01c032564540da840c1b003445006041c0540300d107a1108005100354a40380d80038080c0302c500103040300e000c2c418010202e81e80501e009400c0d803207400c00070018030041000384820400b0010802685090a02d010001369000f00d02c080d159039541c03e15014007104c145541401c8000d19004107000155080034600040101450b1490b0300540f5a0b8110003184401c174201207883c402c2c1c0503550705002e8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 149671537 1250 149670287 149670293
    0x70201060e013602031005090901051509060a0801140609010602030c0c190305031612030b0a0509040f0506090303040303060b030103020603040b0603031314100f0210050a020f0c0a0507150c 83
    0xa058040c80700f4860818035081102c4040940000d5100346d441000100c8524581000e1012003078004e4049070545c3d040004200034181d000e42300d441c5164045036003c9003134030341c00c0c0401d035003240c0c40d0001603441d400c0c01c2c0086004484480042d0050b00e040d0b65644403aa030b80c800c1240c80c0d0150101c3d2508680000c07122000038a000741005680608c07034003512046035500e035903039481d540c000502c58494040f500c41030f00500801131048400e540c10390606000300c140f01f10004030b845c20350b4055207201e48299000300b402d05c2008001c0c6c101c90341d40282103920714144429526900d400031502140002d04000010951466220a890489134090492070450f02c03660b841ca4031454000f060b041c0c04d40320601c0894106190242c00d400204100c051040383c081700c841c01d10400b0b0303004403410070a2140030805000d807a0360006440c0d5600500c244009502d440c1d40800c40c019204503512082030f1000070884003031400e00400c2d80d41130103200380304403040e07990b032841d4100300360040304540404120700d051a2404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 149672787 1250 149671537 149671589
    0x2010920130e010209100c0c0b090d0201120e06040b1504140105011b1e0b0109020f0702150c0a0b06040e0706080c0702040b060406110d030203240d0210030203070201060e01 76
    0x480c0320b9003000581040d2501000c0380c4141094818000041d04503041c1000303000c0035500c1100503000380c9480d5407401c040a80424540101d07803100034100319403e005501000055440349415054200960301c560905041c4800c800c0c42c00d80343c000300c4040560030a00c052826105020301800c2d241c05e000b041e84c2c41c2a00540300d21004011111010b0629000180000e49190821250301540c40107400900400c0c200044014016000400c010388100481c4230b01101950640b580381ea8100c0d000403007031030004494411401a00042101441500401400c00000600c0d152180500759030400800400307010b5607030f440c800c5105000109401c800494200740c1040d00600001d0300181000c29031141c050040b41c0c0543c01a8070a20000d202d8140c00c131200401841680a03612140c603055041d82440e40003991825514801c0084052a0311040b0166440d82c0d611009090340080c010030884917410170140295100702d4100e0015460140086145954803002e64103032130302d00401d18456040842c1c4215 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 149674037 1250 149672787 149672801
    0xc09030f080c1c030f021309090201170a020d1a0d030809031c060303091e050918010504060e071512020309070f03150506040c1b020f040c0201092013 66
    0x2258003040100071414a001c00107811610401c440d007407065860703e41e0040844000481c0f4000040c0100114440090a06031410541b1103800c80040e40152900c0140c80e85c00c80c003e4900350001e080c504205081d070155004d4004040002014881c002ca01c0c14104021104d05140c507600841d10b80e0080086842141d2055010180c2d1049130b01e1f01991100350440c031091403020b401e1480d01c5480a00401d80d1008480004100300c0c407c04c441c0d200f84040780100c1c103d041c000c45001d4005080010003001c02d80510f407030610761a100070481d5003020704014002d401c8621402999100342c42c4001501c0b29500380c80202400d2950321101210855000c00019610140c40880c041c42580400b14900a0040780301d001140301c1c40852001070540e5020b80160781c00141010300c41d628104d5030b007020940005102545240300051200485418400101e012414080b0190000e29008006d00da658055000181d560701074007400004003000b280c01031200ca6200c50094100900c001c80034411400e64110f41 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 149675287 1250 149674037 149674043
    0x2030a150f09110a0f08030a030236010305090309010e060706061a070c060905130f090605011706180316060b090717060102061006111e0d120c09030f 66
    0x7103507082549031400c00396860481d003a95010b12044401e003052078204e00c014000d10400d495240268500000c807501c902454060b00141600005c0c4034503400200e00c5800d1005042e0500071009a00c400e8070104000c0440d200c2a010a28040100d0700b07503440003040d1020a00160342c0e04203e080d180c0300380911508050390443c0d00c60307251440440c0c0900005503485038000001c4016499440f00d060080c8403010a50104083c400c03440020701c46038603009500e5a468064000104002c00101c605000400e4414030190040f80341a0001c141010203c1c0c0c0c2c3d4040240300d0007120125298544a07502401100c0580456940204604101849080450a03030742e801103800284142c03986d40419a02d01b401c0300c0b140c0005107612a800103040f00320351010340060f000c1c80200460700d450341c80710b024040c107405243e061104c3c1d8401207010143c2041036000d00410000d03030241e10641c00e071080d50741d0014120041c2c0420b9426a01c080b03032428503c540c0e4240c01e100e41e01c0b640c3c000d00d5900c80c0010002c1b00c500c15 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 149676537 1250 149675287 149675291
    0x15011202011b0303020a12020c0a0305030603151006030605011d040e1009050321040506040303050c0f04180c08041505071407050d0917030f090406080703111c02030a15 74
    0x4422401c40c800b894101d02039203002d41d0303031000d403c80207204140c03800041c6417091051081c001000c40003c2d08200107036050900304e84d262200c0001900c0d00131001c1204948590480c2007103a1000c04503000b00445502d03480c01d01006882e40010348200109800d1080c0b0a40f4150b9008000d00e8290041d40380060b01c00151002c00c9030004070b000c103a03111200180d0311355000090f10340f40e00602182914442c3c4103544000c0c0360b800d265460503150040984081e08040d119004601c904480c581100d203000400341407591384603520f1032220303103103084000703e11509442c0450754032505000341515445254088190032031001c6005091004110103000102000b0004107800000078503080108401c42c020b8000b0721880c203640900620440542e0002403c080d21803803041c1820500000703903101c80c81204140e680364101300d400719004110360b5201000b2403292117000800e0090350052401819825540b003180b40304034550a00206c0508140250554885c181d2000800d00000e5603900b4000c01c0080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 149677787 1250 149676537 149676557
    0x120c0a03090203191a06031b011e09051305070c0f0c0306020f091203040b18040e0a1a060d020f0405040201020a02130606031404020f102106090e1501120201 69
    0x801e10f0550081504400e00710b007805200c050005d19043c0d522070000306200081c9528224000c2030301c4105500304010345d03605224140da4281e01603148460246807515481c0003810150000a00095203441018002e18940003903052001b014050b152243c0c000d0303124540c0008ca569600480b00000060a448a003880c08001c00056a1400140881c18000800742c4e05c5041d0724042003456006002e10b034180350700400003048510389030820b6400c02100001000c952441840100c4c0c054140e0715000c41081c06407003002c00401005024000044109110351a25a6202c0c2d0a00120545110000c1d50011440f4901b50f203620340b6800507a801841031068410000903603011a03c40038480000905591301c3d14030601000b645403007950324100d0740d0b03681c84000e0b007130a8000c01c0c001c3c1210f00d040f030f005982100f80030301c0050040c0440c244070f022211010300711202819010008100d01d0140210680c1803004009a4540004d404444540720500c00d0307105900e40000b029422011081c12411301c00035800f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 149679037 1250 149677787 149677789
    0x30903061a0f1e130b0306090d1806170a0e011a1c0803062403040f02040b010503160e031212011a0310030303050a0e060405070609050402120c0a030902 67
    0xa0031505410348101e40d0030008000304000744151404000350040408000d200d4141c010b0040031007000c441562803a10484201e0001c50140c0311308040545c040c400c010a00c50030309070010340c0c4c48030a60260394610441c407810004c1d0792482064460540060302d91540300c17491b10200c1c6900b9800c00d2504200007203d159080a882c2511032a20081c030800030b41e2642040c090a0003900050758012400280b000d1845540c0c1c0c9070314500018051901a58040b00c80d01c3c45440100c66014000031180c1e0455224035051500983c02d400124049001d2801c02c0c080c0442c035401941035074025101a1605c007810320170010100c46840300c11290607850312901c41d0408003000240c008040c0044d408001959940c1000f08009254814150364600c2e1304080040105244a070101ca0040d640c1c10324003c140c82c1c0351f4002c0d15003d4000e89070070405600030141407004005000408004035009512a41c0c0c440e90fa070401c1104900540e07040340d0b842500e110000c0e55207200c44c4001c103045600b40c1400641281030390 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 149680287 1250 149679037 149679041
    0x8120a200d110712090302010201050907060507120e0a0306021c09050a020d0219030605160905010f05030601050d061403060a0b06040504093210110a03020a031b020c090c0403120c03090306 83
    0xc02004c0c0818000e030005e00540d642800b4a988c000b05420007030003800d140140c002c11910030300b030026200c0300c2c4200d810f05102e44074080741804140d004240d074914946074105500250300410560b01350043d00703d60404e00dd00180103000030540c01c1070160074050711503000e1050807a0290340490b4400c400c0c10760b4000e0b0202e1a02a200910301980000405180c042c0461414140f0341d1740d41421304c8a24141041540c4e03200d070300900c2e203400c185800c98030707612508016039031801442401004141420b03000315401c00f070520305141200003181100c021b0f898100480b41101e56102d40e550300010308000910a508264006000e034034442c0850020404401002a1000b104101c0010400441444a400d0307850300b04840b098200e2103020030004d10711800700041c00c6109401e504014180c0100314018503c7c0039070b1045104546a400c0121100c21562009448148040b0080c3c4642041408a002c1c09000400d441c00e9a40c048203644000c01c2c105403e40701141d02010480800c4462900070002078414 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 149681537 1250 149680287 149680313
    0x6091112030703080108010501080303011203110303010303120f0b0a0b0c030705031b060c0903031206011b08190905030a0b18030705162310030908120a200d1107 71
    0xc10040c6440d01d24900d00181082c2c0103071302041d481e1381450014008c9210100440c1c2c110780032180500e0305141c46203400d5805c0c2500300d840c0300050001100001c280b5400051501c41115010020001410207079007050883d026024242c0d00301c4900343c000e0000017594402050381c2039004003206d08054055841c140303142d12503040740c14007004003c0344401c414404c214890300001110211820a5100784c0425501d01a202da41d4405038a4800480c5450340107070300a00c12000c120b102024101001c0c28540e48650100401020404c0500f4480394040d00c21065101a550f00070013410300501592500110100082c00060320300e0003c11060140d2003040004000c0c551240700540b042c090054545d019004890f030081d020114a154060060350f105042080c0f020002c9440b01e00d4091244000c0340202001c000c01449008000307494542a00f140160b0f034829002804c080c0f06640c400c214001c18840c0c217103a02e81501c0000d1020380c0c1c040001d90401d0320306449485e81d40341006241d0700ca03000300710b100d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 149682787 1250 149681537 149681569
    0xc040501090b09010f030b0408030703110c06070e06040602030d02090f0918070608070e09150411030114010c0b0f040f0b0f160e0d1112011b030b040c0507060911 71
    0x34600b0018180e081c40d940403801480d840c50f07030341c2ca01451515040328003d8010b00c0108001000000550110f000343d02045080c00c102414546810801c10300b43c1d80d40c642910080041658202800b04516001c0200c40964032960701450520b85c4c0440800043d41117003407070540c0410078604142047c0c544c1d0f81942e00c14890030110501604000c440303d41051100d40048042181c60810848099081000d00c40d038180f0603111400241e8540880e080d00c8075056403c258094201984400c4001c50000034505030f4248110b024900c1c12003800544481d82002c400400c81c034081d81c0010038070800e4418059101c1c2c000d110341c02d0500c10035500c461417042c0c00c44e115002800d000d070034851045031800c4400043e400070306009100c0048500003c805c0407007207000814060b000c03416021a0780350340425600d5110383c440280904031a00c9800e80700104003c8030b6070006450b000c0210b200b4034180c0a00388858a094655515120381a2940f202070000d40106546041c0600e0f43d84110741c9903000500325041c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 149684037 1250 149682787 149682791
    0x80d0e030d050105040209090609060a080d120509060403020d0f110d030621200f0405010801060503060c21130b09011d1b0d031704080405150c06010b0a020c04050109 73
    0x101050031581141c5044c0c00c107900591043c080d802e02620350300001500440c044030301403082d0340c031000090107000072070b00305036164024410a14040f0350444c03200382d000f0b0300c074810500003036170b070307040303a580e9603c4100c1d0040d0050780b01004000d00c10b805030021842940740c0e45011990340c85000c400c1440c00400c00f030920002642c898040080081c500018201e104040b400800c4000d029107600c84006044101c91005c3d00e620000c4512540c2d4042c40c00d41540c2c00070b0310501c0307150303901ca103003a0003003000d442180d0003030086900040e01d5048040488100c010703098280c03a10f0b11074400004103440c00c001c200d4503100840d402e406012680200d0518030a240c507200225220340e48041c41a08120618096490b0754083d1701c800c0b6490841701035141c2c0c0c1070015148041540d101f03050496500f10300c0e0701d0340882d6800b440e0a10090254031740003402034860030788021148580804108926204e000020355054119074014400c8100d010024040801d0714412036480502500005088078020703409038840319 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 149685287 1250 149684037 149684047
    0x30c090a0305060c1e0901020c1003020913060602010b09040b01030b271b011103070f020a050901060804030e010f080609090f03160215070201090b0d0609020c03031509010609050904080d0e03 84
    0x41720180c00100b0f5024110045090120410001c1d41e664014041c2611418140030540001442a8183d4590010040005004c245103405401c0100304601a24005500f0041421034500704402c0c85030045a1002d0030003696840d40d01c91903048140906480548001018030324580138030064402c01101081026240800c04135118002d6078890b10303449030502640c0380c000440c0c01d0b408820b840708240c008440702c40030707c602d1002502c560300c907401c0720780d1200262002040c1306901c0203902c3d104602c07944034a040030340c0210042d640c0420200a80e000a0607600c001100c5003850800c40b80c114004808130340350611099400b5085401c00321002c0e007400301c151520001e61404000c00d034800b02d036200c00b03580317413840c45d4000920104860080710b142913000120440300008a610020042c0321a800864403032070b40d6a803850b10fa52042c0d800b40035800c80c451a0b107001d840c00d01c0403107040320101d848075900b8074035000034010305090041040e92642d60501241c3c2c0c02c1c0d500c60142c00501031009025554030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 149686537 1250 149685287 149685307
    0x304030806030d0e181305030403140106060e1f020c0a081b100516030c0c030b04061d0c010f0909060f0e090c09061201150308041401050f030c090a0305060c 69
    0xc81c04402002c000c00469007074030091350303d410585400704000c40c50315141d240d8070040089104074003504000c2161100140010034448225000e46207407804100a00c900c6130303282002c561642400d4441548502920121803113003840941e511440101801030382e5a80301c6070300001d0100d10321580700d0b00131900318521401c01007054408582c0c0a0300c3c00c030317182c0071200350802000b0b1907802000d80849210303904a0140c0103050141c110200c4c0d01ea0300c121f128811503102c1c60700b071942000c10f03a0100e41d00c5041180781003026000300d02d240c0b80303511040003d000c1c10401e10011aa0b04201e1b00e13070704c8140a05100b000c00c2964180c059800946084400d170b0005600e800d009a00c2020000c241da01e81e40c20092020035160b40d813407241da820040403106040d80e1540740b0b801900614200030031064000d5040c100104000b04070001e172040301d401c80c0c1e031107854110450041da482d00c40c030801d04034442c1c800c100281080c40004050031020308081c2818403d02c2c0c0342d546032450550265840c204034680402d0304600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 149687787 1250 149686537 149686543
    0x6092e0311160b0603030c0105040c050a050612041101050d29060307020706180810050702100603240b061204020f011e03050703020c07140a0503010504020a0e07050d02030403080603 80
    0xc4001c00e10039051030403481412241c10700d10081002041c403655440883c0c02640d0800507600f80d11020802041039003010300e058400440203124060044524482c0042d0501e4036000340d031241c00c9024201076845d0748036940c05032404000c880d6141070110034840c0c40080e460074415000800c034107c0503054047c060f10f403000200394901e003603135105400820412a14950200c0e15070704503a01c82c00c1030003003e044081505240e900b150000503080c0700300590400c207610182c02c014098005a0291034080421018000641b80c41e4040900000ca25081e88655400c01e1540d0105140031020009a5211800000784c4d490388007445220040c03003c00240015442c10390b111200c209001d0030079500b08080c4080c0401e4455118000e2028569100001860325000b601120f504450041c15200e85a4a42d810b030f0814203504071701c1c140900360b030440128407810148201c03405035070014120100d0518143c0038080100d0024402e400300b04040c80611543c4926001440c0a184a52109455454808140341c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 149689037 1250 149687787 149687801
    0xf0706050109050c040f090b030c0907020610050306091905010902120718020319050a0603051906140f010b0c0111040f080f0d08061002010b100306061803030e06092e03 74
    0xd030b550402082004042d24031b2118226506100003040c40b0f85440006030a010580e006290000c010504000490354040b400500c1650358909490b070650310340080c1640c4890803079110b83d8039030000b00b01c030340c0d002003d01c42e114403c3d10034400802e04d20100c2d80820503c0c2102c540038043e650015409000f030150b2902c3c11035428608420450840c90403040121214100d01e0074202503d80d500046200c828072074109002035034000301140d1354400c0c081c1610484c0d490300c900036101c583c90100c88480410b1103615060040740300340d0640e0202c1c0d0030003400d524142c1c85408040d9007507580303400c00b943c01c20a10b00948024241e4651010000d07140032009410b010f40c5a10b02403641e00800310360b07000e958000e01c925030000c4041e02e8600c03d10300038403004e0380144640c03040940c0c42581400c40d00318155154110406032030384c03903482950001035111980708850141c0030003404920b000c0c41c16012230030080040c11450320020042c04a1104c0136000c108000c8040b8440c14006118015441c120354060040030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 149690287 1250 149689037 149689051
    0x120f0f02010905070302040903120c08061011070302060f071a10090207021008060f09010e0612060403020307080a120911010e03030a0819020f0a080f0112120e060f070605010905 78
    0x4010b4071480e07034440b80c841040b400001e109690300d174031460900d1310510281e560183c064804200540310781101826003a821241c0078440c200640320b2226941c891804c450800d034001008100300c41c159420170081e908000c044001d5001d043c01310b600850800d4100c42030702c1c3da07802c812080c0c5040c0270880b0f04505038640c12200141d40100481c0300107860380e4282074009141c914100744641c85e49000100440718aa150543c803035070110001c9805c1c88180790240c0102d6044801a00031b892101c112500d07001c04660180140c1c00c14840341012030302c0340c802403500880300d18101b0990f107800362105044a00c0c0b600c09456602400c910402103580000c80c3c4221a0300840046040c15a13200d401482084014510034842608185094103980c4603010380302c0034044a0800307500c551401c40002c1c0a07480880b1102c444822a000010381d020046545440b801d411060001603040d40d908240c0e0f03030314074000213190041802c0029001840900303002c0c00025100300b0b804201945852107250035070b5000f070101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 149691537 1250 149690287 149690291
    0x30b01080a020a020d0e040e0102040602030d05060907020a0b0415060b070201081018020702060705071e0501050a080703020304051f0c0201050c13061112030103081c0905210403120f0f0201 83
    0x5210341a00064200801d101516107141441b07030100110b0050507a446800c81da56001060105510390007001800034519868810001a0345541c1006800c250540d840070160300030a44500c0401d500303a1200358081d0281540100c442c0b60000410100d0709070741d004040507003011403400215039114041c560004850b10141c000c2500340b00f4140c1030003418540a1200c980d00140c3c2c60119126803058481054201c000d075409030781d0b24100100085940d03004028002c41d44000491190f02900079100c4260040e500c0c0d56442c0e44115056000354001b410540b8284a00c00d402c5050b0390fa0440c03030300c1e001d034114180419441c1d55070708064251007000d808400882014040f500448c000000c3c2801114058500040c200e080c600280341000d82030748951181250000010003070201e20030040c11032881c4541052404020b03c1441012510300b4000140a60481c2d2031883c114401601d030030a0724032141c5000c1d860a5a281da6401410482070354603404200e903040a5520581c11a503855098000e90000b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 149692787 1250 149691537 149691547
    0x10320010207140105090103060b0c0102030115080f04031d030d03020d0f060302030c01180e04030e120102120114031218011403010e010b0f16060902100e03031206060f0703030b01080a02 82
    0x9032030f0642d8410030350b0a04210300400d03001c8041c1e100e074011000030302c021513206a503034100e205040e010358006d0245111094000e0740c00440c0034411700c0b041d485070000d1120725909440310340d000c40362504921100072908191003001c041c107a8040c0203031a40c0c14419100103961359400702c982c1c0f00380c7d4060303091100220320700001000540c402007003038012103000f40391422022408010b0300585042c0ca070031102e803c0e5455000c2004040d0440210b1400345011200c051044c50100c03481070a03403161884040a844400004001003a41d2000d01294420010144d5241c04200100348074241c10408006441c00030741440d8000d9540c1151816015800070070801e407540d0b04121120f040b080040c03180d6000000002240b880c0003014200707492601d0000c0481c020204407601349a40a00003941d01a072194822031594408540564002e500151000c0c01a50a2503291032441855280084c102c41d003250303042186020305e98030702c4002c10015211707440c0011050107000004040000c0107103810559841044 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 149694037 1250 149692787 149692799
    0x904241505030d0504180e0a05070e0f0105030d030c090801180204050105040504081917010b030a06090507090315090b180f0303130605100503010c0905010e031b01050307090e010320010207 83
    0x3c100e170203440040290414001d11111060000d1140b1a12808980119171610080040224402003103c68220b072005590b12003600041c0c4a0b41d00384a403980c142d20203c3c07905200350003600060031b200f07a5801c3c040d12455481140c2170a40d101d1150380c4503511001030307013082140b402e80b003400c1c050301c01514200080d10701559503000c1489002c0c0500310036801d0540c10b08400b8450648103d0b00c125642d510401075942e0242c8400320740060f208004e5941c202a8042040c003c0d0f03101d02d0380704005641d40c84d00d80b2441d42c0c035107407001a101c083c4143c415440300104000f1411103040d1501911000c0320000b6280000c45026040c13648a01580720541c0040003070101060b03480803802000d5130441c0c00003030b45072200b007846a240b6807260301085d01035003000d0070020703031541025581d02154400c0c5c81e40700f40d1204810401d9102c0fa00c280c5000440501100e600415501c19000381d61700011074100b01180c10b45500d080044000300b640115038551003842000342080c1c1186001c00b080000307000508459051107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 149695287 1250 149694037 149694047
    0x4261917040201050301270609020a030c0c0804050402070615030516120b0109050a0f110318031c0e0a0606080105010609061e0311090409051b01080408090904241505030d 75
    0x8440c0e0b1184850031f00c0e128a2546c07101600203000c50b4402410001c032962030481c00c1c060f400451401011030702d042c01d11138400d8020245901c90a50000720f19251074240070030000250880042550f00660380e9204003241e125803228040039500680043c0700c0074404250604a11800740c100d64030102c24080e050b0001010455400d041da840b40d007010079150b8034a036810303004100e10308042040c5400e00c000320b111594881d009500602071030a88684102417840c01980c1c03841b41e82845a440c030306114110a480e40c450344010008001c81c1d0640d980c015035516840103891098001c14180c0e55214010008260003910071001441076040a0030301003c0f150700790681507013017030221042c152540c42c007415600c6a001200c0c07404800078000c004030070b12030070b025550395100c000c640852035520750420100c3d07000301050f901c51a486001e0300c0c40d100c0d2202c141301342d05502038421615101481c012802d9004841540c05c06034024103800100009030115542c404407841d40254003a81201101d0b000036580a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 149696537 1250 149695287 149695289
    0x906170d0507141b09010f0e040b060a0806280608030904090302030d020d020d050708060a0603110403060c030c02010b120a08090604050d050a05010e03030f04261917040201050301 79
    0xe03003041030301e84040e0705000311181100c04074640203000309122841c22a00316010082c12000c1942d55603510782c0c86d01900d498251583c011a5612118140040d00250782001349552080001e040000d5069650800c24600030060310700f00607540d45402c025110f2440c620401420070444001444100d107800741282e1a07202d0498503a0240f40c86000c031406040c020401c8849400e9650300c110742c1c071311010003643c009401684c44031062030f0821021500061140740d04038010a0010b0618201c81e15268007035000b00a540d864004108041c040000031422900c03c01c0ea03030340c110f41c03404600088a04002404c59400110a40c030541c05004040380c0c4500016550410b182e21100803030340c585100f400680303680129806194010701c918036680030860b011a000d5a03051003070740207004c0068a0550b5075200d02007100c02c2d0071102a0100041d020500c600d0008000c3c5076500301c2c48189541c504100b6a041c3d010340341c3c0140704440e030011401c040d54008810155801d04116803042401e203640000d01034401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 149697787 1250 149696537 149696563
    0xb04050105061b16060302040f23100903080310080f06091b01090b040308040e0124030506010314310b0106081806010e0708010510020601090f0e0601030507090617 72
    0x1ca90703c3d24001804104108019401c071001ca4442d950b107070801006544a40519160440480000a0b10040d118903880c0c0420f13480040d142002c032142c09200e08000c00000c00001c10030038440c004041111440118000c2c4542040403000030704100703042d071a000e4500000c40c915802181082000b0b9400700700c603507098910302030071606041d1890048420380c940da007000c580d40c40001400020800690005c00896624003101c1510342c1c0e072600c5259650300c081c0c40200051003140b02c0910700170300c0707548803a500c0b08050400148004e294580c5581d00007045484070501e041c0582c04110381104100c0740c0c0a503030740c1c44180500c640c5050b035076003081402c103101e80300500c403510001c9141c101100450104140d0610121492581c1d01c0000041c0f20b541510400040340f190350000c03c90342070201b0760711030310b40c49038005003040c1e4a001c01d0180148090021084003654401d00064581000d010b024020b40c0520000d040b80c904211003102100c51591112401114000d03401c142441d02007242d02880d08 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 149699037 1250 149697787 149697817
    0x507050d0c0f0f110c0306090a030e120705010f170f07110307020a0e04030908030c0102090f1806221820010c0b0702010f0204080d0306050103060b0403020405040f050a080c010b0405010506 83
    0x1490b82030324034084012405c02d50500803207081001d1002c00080d4034481900a80d01c0c0074600d10b4003424080e8a4194850b03461241e0440b0400340855401690203180d84125458000944241c0c840305580e0084160761f02081c28440340c0610155541c004000c030030750003000f8065860112283d0004400e800d262086410b2068604000390070f15016003022002000d0000607a503541c180043e140703000754000c44050b4030956a40900c0d00031406c02202d190f10303229002c1f51030100d03520b44a0810003280110181f00c0000c8010300c60010a0100d18010304958481d40480000b09081610b840f041d07007407184030321242001c1e007464810180c1e03034440d2014205980003070180c09551540d1030124007525010044202c881e000040000701801c0c006100c6041c0031503583c0400c070868441004406039900e0344240340440c2e4043c4001d00151600c0d60040f40c2151192101880c400065603440f420a00d4402081d580c00b003000c00c1c49000184c0038040c02c0c00101d003c5034100125070601c80029014007844000d0104c02c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 149700287 1250 149699037 149699057
    0x18100c0b040c0e07020a0c0609062a140d390303090501150302090f0106080106031503020301060e04150b090403120b030a080406020d030e0303160903060507050d0c0f0f 74
    0x4844090004090302000070589510310705004c0282d0b44698200084812020b0349100064803842001180c01740d403041e40c1c1d58410001c50150130030080400210b115001c51074482d035400040c07050114103201201c0030014003400c0e0611350025010403d200114044118030b807925040c41d6a2034204002450404041d0303100390091414224010410250002d200e980707810f0100404c9070f14603c0e00c004881c8222044c49040e640d16220319507112007031241101203000140141300c0113000740c00000002d00f40200741d90741130b60340b231b0006401d543c41e81d48100300300f45401c4184810305c0704552001d01c5400780d4034000d100e80300d6800e01091011000400140410801c44881540550b85401400c03082c0f82c01000c4130400203040c189403809621030720609015101c0c81214000c85400b0303004102d01105600041c50450780e400341e00c2d0035a1280c807100c2d1410000a2071000c0005951751181c913000780348680d101500e426039554480c04a94250f60300c2e0301030150003612602110751002201d00412410302d8040022 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 149701537 1250 149700287 149700293
    0xf062203090e0c04031203020a09060e0d06060902030901060609060c020402030c0408030304030305090606010207030309051908150108010606050702030d11073b0f010e250518100c0b04 81
    0x14800395041400002d0811052000e142010f40161054074040c041c1c820f101103580da0240c00700c1c441c0000f100f000c40c081c0d140401002e802000310114810000e083c8541c11021070f078030f400c2140c91507001605c8540e4048140301c42981c1c01d10480f0050071060801ca40b80c00e040500281c0030b00d41a4000910854000000400100342c0005503801090900200c03600ca09142c82c000d80901000c80c1c01e4102031044000041d555840001c42000726909512500b0038070f0b00308014401030800c2d03c000c54a080c04045030016403042c1c10811105c00740c40d03400002d081c03541044a5030b402d4030b0540d4041e00030818141701520142ea00801d04214a0489050018060f0b460004c001d0822084e68000e51b00c1058021103130050070281c86411104e992407840e01109400032200c0f141c0101800d40301042c4070a400390040c44025450403105030005e01181145a40c00b40c200e480950000b0011602400101c0104410350f00100c7c030b901c5219035800c1182c0a110400e6110401050010b00c200040c1c00f070441d210118044c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 149702787 1250 149701537 149701547
    0x302031b01021905011e0b0a140301020c1606080a05070905091527060405010803270301060303050d050f010e1b120f06030601080102040308070305070516170f062203 73
    0x32040380c0c00d03d40180b641641041e40c001c00040c019020801040740d64065424903d109410031444002d04148510341804200c0e861180244621605036600b0004528604020080b100b400c124602d4030041c9c1d80e040150051101c40040c1c001d060b06070800701170180f0f01d60004050003d0f28070a8881200301d42d41c031807030504807040c207400807070704080e20f0071495080a0000c0c525040c1a01114000741454940405000407110b0134803807468150010700c072100012448812910070310104410003000c070b002c4140000c0c03c40340c0f02c0d84110007048002a1700c40754000c4d039000d100c4d407101d06501c2406031989406400366034900e0051440000b5140c03885140c40307143da03400584074020000c04500d1194606107403002151b1605407162446441104000620a1414000c50703065a80c0201880d04280c042d075029161070b005403100b2901805503800d500c014900050700c04008080c031001d590034610f4041c0b01c0030b0030b01501c0b50103e005900a0420001c4001c0290452010228000c4900213070b41900c1c102111 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 149704037 1250 149702787 149702803
    0x1309020f0f01211a181b0f0a030603030f080702120f04031407050f030d0f030b040204090203040506060109140303160c080f010207150207020f130209030a050303010806070203040302031b0102 84
    0xd100700d611040010381c020070095191940468104e00c0c00c0c420072500c03d800c0b207200c220310089080003401c4a42e007410348040546820380308608000002e103150300560089400b00e40040d542d41820028142e00c880c900e03024030041d003007182030350034070303000c000d448054180800b21040750005018013a030013485c0c1254000c40d088075859003880b407a600303a29200e403241d208451150340101c0c0d11014514000c19600800407150700c500d0000d04506609030040c100a44901d9481a400d10001800001c180010f5204501c02c00241c0001e1401d10005006400603401c14401b42c44200105c0d03465840020850319064501300038428680700e140707003681c60b101c190303004207100d401004807904181105401400000d071044070842e0304108880105012801000c80180d03100e04450840e80c036034241049a5a010440d08202505d000c0000300403e14209094504440c180d10000c01001807440a100443d0011030394405140b41600d035800081d55002c4021804294912810301d81205a0003000000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 149705287 1250 149704037 149704067
    0x501030b0f0402130903080105030d020d05041509090c0c140f030403020111030702040c02030d06060e061c11041e1a0f0309150f0919030f050702060d02030103111309020f0f01 77
    0x40101725062030000e08501007842007a000e80b1440c01c150025500215000c03842c414103175195401e103032814240390525120001e1601c140301c00b8403800314580d411400351407202c443e00d0320b80104440c1c052401412040702418035800c9600584500300039484044200c50131a40c0901e80076120740304403500641140301d0b0354402980946018101c0c00c0c0c454000c40507045902c41d080c01003241540d07510043e10010041034120341c1c0000200001d0088008a10006100c00e001e0f01000854030004041c4940681c4240c00410040c4842d600030080241111070034006085440d070618851100300664009501606884100c4c0704000700004108000400944244484550010300941403425100210a074162145084d601424002140d8111011003480c185540f60307582c0c170a84040c001048800e0340140c002243d10220401c4081205501400075501a41c003034170800508010080400c0900111000c02d1a4402d0a04a4110260303a6030019100e1200b0152103000001d82040c004880e2105014200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 149706537 1250 149705287 149705291
    0x1030c0509060a170708040c03151b030b040e0705061b030c100c17040b01060818061f051507060f1e0c0914030604060f0b060d020310090501030b0f040213 68
    0x400d03d26580040d281880262502d020300780b540b14401c0403141107904407006400d14003020400c10006070300c0102144400300d4600b0010f00002150b0140b0b00d4418900e005200003520303405c1c244030508d00f0740f00d003041044480780186241840c200110342180201d0071440448a095844d0310701048041c01155901c181600641e00400c01c0741c1d845070010005030742072400043c1d95400d804a058002c4100c01e000c0d039000034845036240e01e86501281c2459000304601002109036044449007101002003c1c0107103c078883c3c0303114080c1200d400910351f000b5644214890447c031440200e1610640003110180d540008000c00c414545803601005040c480901e2190f18002d000220303c2d8503841d602008000e185503580d15541e036941c0e000b1541000745202e11a9040d044900840c00243c0650f000c6039400c8071020b4041005400000081d0841e000002520340e41500081000b060039442142000504241d000810055045072900c0c440300600820203104480070001003800c0d5035070f0500404841982e00700c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 149707787 1250 149706537 149706547
    0x315050703061202030a12021e03030f0a0b011409010504051c05010617100f0b0603010303080708070507030c0b06190b07030801050d02010206071d032b0c0305030601030c050906 78
    0x11000105412503503000000e24096002c25001c00b526076a9066a4006000b09400705040c1ca0343c2e2203d0303440582150075446018006010031412180b01140b215164025603203a150010031480d5200c0c004080e07001107480d25105070080d80c8c200b0350004034180c0070f40711591106400c45c01038405104903003089074840d15004060325801094120fa1410381e00c6100240555130742c80c00c0d0042405030302e1204207015003001c0007051400100b540000c1050400190124102e1078590103d42154000c1c0c0080d8000b500c4181000040c64000d01c0541c1c0164007440c10f01d00e000310b1034400030b00c85520705c0001002d8850000208540ea900c880c880d403041940c10411303199007551114008215445400200d010443c008000942403410340f05ca100d0580e0180c001d070500d1350342c8080407902e1510940d40386142c000c0b98200341c1c40c00c0e00c0400880d144801e40555440b12512007070300080420343c6080002c000c01c0441441c030400030350300c00b0649400c101c0c203003000309294090940582d02400b55070324040d04020040b038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 149709037 1250 149707787 149707823
    0x160501050a050703150303120e1e010903020f12030604020721030204050f010810090b13020f0a0311090a090c26150a030803010b0306040207080705011a04090b0a020304060603 77
    0x40070720b0080d4841d450030440d417402c565041c40c02407100e1101801240c8000300012410206800245065038100e0a40700d0b21031f03019404014100c042d081300c100303581d50790310034504250701080580150401e0500401080405a0001c0c0711848000c03c1d00303004580205050082006140711401c0c0f07080324007094650303000320410050003508544519071044405d42c2520352154010f542d004e001d1380394580c10407041400c00b40c850f0040c00c0041c1815411291000000740010600c0c4051f004590a995101c1d0f40d610403400014203440042c1c841c0c41904a00f08507524490740c03940c45400c100c03001004003194061110030706944100410121000d400d85d0004448a0300c00500022071040c003e89a04003401d00e80c220a205542d191800010704034a400c20061005075804005183e000030001c001500d4541c00e941c07410980d821000d000c44135a9107491507001d260031030310718a58550100f6a42004003c1250311240040c50010b00014112a4000042014044ea40d00035030013654000c0010a481e00341c405c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 149710287 1250 149709037 149709041
    0xf080702120f0105010b121303020f06070c02040609050c03160306120302030409050903190c0f1e02090f130b0c0f0403080d0c0309120e2107031406010f0b160501050a 73
    0x1c901074401c0d51800002142c910858802c4d40c242040d050f01f44201c907660142e255483c0780200005034103500c0340d180c401c401c040d41044824402d024a507030f92041101548140019544a074100c505600e0500f41040f84104004040d80d07481000c0304014a49018083d009a000740704503003200e10301c1d99800841c0c40c10706400100030403c40b0003820017001281c8d1041c09458030b9026444112020300c41003d07401007464030940b04c40d080c40b0b00076603490750114801e640b0b00f0905070b031142c0c1068892660054501c06d500d00044443c0d8490210701200c03600c0c2c030b070400d03940200e850780d180d0040801d01d004021820740d40104041e206241001a000b6660319100c3c10034a0003600b2243c0450852800d1115414041d8402c7c0219108168000000913102120140655100310100c83c401d4001c0b40b904469a0300701c00d000f03000b007001c4040d42c0241c40340c181581045040407844240d84041c170b1b07005100400094140104540c2201e0307103034003000d440f4842c0d0751070300c5500400c42402800642c280f0090000404c06a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 149711537 1250 149710287 149710303
    0x30a0515090a14010e1303052115040f05251205072307031d1909050a200f03041506031a07031b0509011b0501020702090105030a0f0f08070212 63
    0x1e024203c10381c1e0f10284040381120131203001c500d00c9555482d0400081c052005401070f0402d00c0c2c0da0b00390481c03400d10382946a0108807a80e5094a000c0d00184043d4109445600f048c4203595009014525104500c82c0c0702e0505401e00b03072107000d4103001180301e4a1003001c00041500c1505014030103420400e0700142400082c80744030800f00807144030000041c810300e04076281d444e4140c07074031500213400464100c0701101e0400030640080c180c0000d4090804611103880c05801600f5000405007012044401162010075100302c032a440b4139107040581404209a46044034034a01103980da0b0340b1450001c0e52020807440009520381410000720420400802203040c940300080750b01c1c010360b43c0303213002c406036a112850046c11110951588665600c0380c8003d02c041d40040c101450556a1402c0107007020f61a4401540c00c0e950105a480440c50706904190040c4002c800401c1c40020984901140e0302c80d00c280109106e4100c6403050412882d281500d42d4650014045142000303c852900d80310307104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 149712787 1250 149711537 149711561
    0x80309010605030d08060603130221070f0609140102070b1204020f041a01030c02160b040504150605041e180c080a020c341205160605030a0515090a 65
    0x800728003180070b05000410601241c0d0a17511115940c0b60002071000540c00030701a03503034884801d2104000340e190210415001e480004c00c1145488082907140c0c2082c0e4990410340307500400d80170401c021030340803a000c4140c6141843da8140140003c005070716007840355104590700f12012404460158256202070b20541c002e44031449910504010442156501c0103400c429001c0c4141071219944250302541d210702d110300450b0304400d503580c2c90003088043d960040740450700009042c065070805001d1504142c2039199401c00c40e43c00c0079001703070081c040c50080c10320408140d805d02481d100c1c60f1100d08024a42c900107400b9100c202403082d0003901d02400004041000b01000c41c44105440c8202e078084184800682a6050b1029040b105102c403212070040f6000c12014440e01c04c00343c142180010510030000508142d92450030354280588046603002d210407407a800c00080b50041d040300d038486a5890700140986d152a0b4040d1240c006150b040e40040e0001d040207600c442030f9100c607a04820b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 149714037 1250 149712787 149712791
    0xe03091f031505060f1803030c010e0c060403051507030f020d060302010e0a0b090f010c020a0f05130204080303010b03041e030201051b030405070501050a05221a03280b0402040308030901 82
    0x180070b1410000e5480580314068000004003c600810034003031020309000c540401412840030302e0f86000034036507000040c2804190f5500c1a80301c041d080200110410b00c8030982d1200c0c05d0034a140c44650700c0d051440d8071503092414039000078034550300c254004d00c05111807860840d15403000c030031140018031740307800100e010400390303d03e6080e03c1c030300b4a031000201c0f2800004245010300280030701040020f81c00c842418000054086030050740da100005020384a90b542207804103151004205c0d04070448024501e07202e104110602100801008a0b8156010582169070301d8440f86058030f1102054000165120060050b890815074190030441c0140340d603e040303a0314444811011070b0390b44016600181b01c0e91100d1710030045940290050030300b107070060074003030700780380b031440700d8245000f01c5088190f51450741ca40140302229002d0160b140c1c044184174010f0547c64a42d12b81c002d1f001c440318025098a103108114680a000340d0003840c82c00310060000d540721030340d80c81c005c0d1190f0010b0791804800c1d4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 149715287 1250 149714037 149714051
    0xe03120c06190504021003110f070501020c01051e01060c0804031a09010c050f220e0c030601081003020913020406081b0f040209101107031e05070501020c01050901030e03091f03 78
    0xb010b5000311802a5001800f9003507101034404c00394001c0c1213070414006d400c80240044c041414010020303007036540c010380c00945c0c5d070200c0f10042405c490f4010300c92520991640c003824101101b0028140c10b6030914184070507a80110708185685001c2c60b8002003840d07906c0c5050035030140c841e00c5550b000d4103078a0020301001040c1e50040c4e074203004010901102c141c00b4421100d03a846260b605880d030b0500110b0000f11143c54030348007040c00c80d003143c40b480042000020b0000c2035078080b24080e4080b2001c06500b1585007141d00180c0c044001404101103110655240130a40d96a5030200d00208002811105400b00c005201c0b102c0c0d800940c8040d118802e80c8514007a5806c05008840001c000242151401c03800903406852881010102209920a220700840000c248440000a4403202c1c50b20313140805440c9080780c44c0c00241e400080c110742101e440c1d06800e0340c03c00d041c0c61141c1c4003424040b4015003154005407460040e829050741c481c0a40c9131a4810102400d06000f014100d40e0f803c1c8109 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 149716537 1250 149715287 149715331
    0x30b041a07230408030a08060a090207030f1403150f12030315151305060c010207150f05090f0601090c0507050d0e01110106050a21060501060e040e010e0309010e03120c06 75
    0x3d009a20035100710303400030010605038511071a28964408001802150b0312621800003400300e811401044020403441046c070403040703800c0501403a1050400807801d28502d0f19040d0107414025800b141805503020758202c0849030355904581d890050200c0031282c491408625001030303414080a000c2c001d4190302081041c40d407809048820000c2d5204a50203003a00e000184481e50340058800c8495560900540d000100d90b949140c000c04074040d00800c0c1141d02c820404101ea0002d881c0e18090b50212340115940c03000401c4160440714404000a1845038080c0c058a051040d0b840040c021700900300311100c0960440d4011125101c02e9a8001004000d407440740c1c225012030080ba548008804020402541014407607030080301072a40080341740c0d0155a5070300503250207030013400100d402c1c82c41900d03c03806c00d031044c0d40554043c803001348680b441c446170180d00d0f84140001603040200020422000f80c0341000074030f40c0074030009a17103540c034080195950380f81c200c140c840c03001e50b100740b13840000a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 149717787 1250 149716537 149716607
    0x3010203130f141609050919060b04060302130207030e010504080601030f060e01020310090e01021303140307121106061807110708070303020709060506070c030b041a07 74
    0x2203074000290350369141060b5195951405114201200c901500c2d5555907070100d010700911900c030044032114402c41e414010604140c860003002ca2105500c1201c80c0c623040c0c43c1c074200702040306070040000507048a494010501030a10740c1c0001c4e400c96040c41d21120091300c2c0340d000b032000e28029543d903607a900600b001103d803842144110b1134280e00a000500c08540e219030107100c82c52190100046940c1c92451250982c7c00c03c4030880040305115204108085050051081d00c02042008514000f10901c030303604950701e1400064481d00c650901019044410421a11301d00e4210103540c107440ea00703200003040010404035103451400f4401c0800c2160400201c44143c04002101300111503584050881c0d603510b1070380791070406105200d400100094144060809140254041c141e0b031030418609605541c030540c0305c170f4005d180070412500865148800a0156544a014618162541c0c00e20107900d210264000d941e49540609000d10f05030801c800d1070280510030902c0200c01c20450700500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 149719037 1250 149717787 149717791
    0x1006090e0304031401150e040201020c03120a03050402030703060603080706060e01060e040e010f1104050108010b0309030a1b0602030109021c05010e130f0b0907031515060c080720010e03010203 85
    0x2038258014002400040c00c000c124030b210348400400001e65022401c0e003042c00c1c5c003441c0e200f007204e810851700744019035a062202e480448820341c020440320207050310200a51050b403045908041e602c5000c00d086603014090f0200443d0041d1060040d01c0e03c030308001020350312106044410700c0c5808400600c80840b125024101e442940394507041c06030b610b0034032003c0c001881981c070142d5650074030030302071030300031700ca0003501201031540700d41c49078100320015003442810f030400d040c507940a01c104510701e00000102c5d07a091070a4600385800c05881808c020380c09011600080c0444c0c0040004100360790b544c0c0c0588150307500c1d8010215240030500110044400a014898240d8200340000382c204d141e11503000741092140c4080c03044690607840340811070500b524034006913003110008100348a888031000c3d4418074900e00c03c2140b04400b5071203981070001881030405021007526000107105061040d03d201a402030110710b5424611314003070040500c1c2644c087d002c03848200030821030703080502c245c074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 149720287 1250 149719037 149719061
    0x70507181109061b06012c090c0d0201051306020606100507020d140a02091626070c11060c0705190b22080a0b0103020102120307120b060d0204030302100609 69
    0x1407800b002c11050142d103034400b052208120f15a8032440c01e941c2c404100c0c03c1c1c0240051001540d5595840c3d00c55040c40c85509804982c1915280500502d1000400c442d025a40304a4118000c020a48016078450040c6000c4880b1024003c2000654a4000c21820300c600c0341200c80225644180e481902c1c42d004491000e50030004a40c8000e000810760b8041030b070890351000850310900d01d01e07400140541421101e0301142c404410a0881071b80c0c20005010761002c03000a502e080c00000801983c002400800700d10420020325445014401d090b2004019450040c10840c0e5807500c00103c955540c000c1d110303d278040c80044601c1400444114500d03410b40f1034616a00d0300c0c00cbc1103566120400124060030700c4d8100c0400c03000299403801003203030700304a43c032a03107524044c3e40c554000a800c101c224410482c1d01300c420010440340d15405100c80c4107030304003940b0000300d100343da2010942c00e010340520401c1680c4005801b0041c1500083c5440c880920051f0500201313860302d50940a0307400da6003040c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 149721537 1250 149720287 149720321
    0x1030c08061e1005120a050c030c030a09060e1e010209150c01060509101503050f180703021c1103070f030b0408070c0f0302130e030414011407050718 66
    0x8540589040e1118166400010030030242c8070020700005070b542408007401c0c4000c2031000a0605151102000482d480102d240701004145045d108000486c800102010400301d800000030302c0c01d0a07a0f0303001c11095504050b0401c0b00c14181c1c885541e49244229215041d811480b034410b02615050007214941d90000c0c00301d20401e40301215102058102701000074055403039000110f8103440e2056650302c80d01010740d48410300d5152030400080b805600300b8417401c00d13051104022480041c200c01d030340c01c50305800b009100000c00d250340034140000303600001d510200f00e60411920040c483d00700203016008400c0c05100c03407000d0040583d1106a8800d90095100748101000400c001c2061f80d40d11a004060755840e05c0856a5a40460a8550801d0b81c03041c0c0c0001d030500560500d000080164003d80404200014090f54840ea42e03010700c1c0700c0da0100303c40171208040d150348122040c0314174105801078541c40384824600f50b92540381c07a004940e0007101000013850644202e0184900d44a8030b5200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 149722787 1250 149721537 149721541
    0xc030705011d0402120c0a0f02070b0a050903010906290108010806060103020c0f1f06060e01090504050618090102040e070206010b04150306031e050d0e061c0e030409061401030c08 79
    0x2668040a010002c110751040d03003400741c3e5403421241040d580c840d42074910000d0351603517540d402800410880d2448400c542c80020240003441501c41142c0398541e09040075900c507216800000e02400d81c45200030303c400d08080708000d0700130701c840c041c160744049541c443c08048141c100464103030909100d0219a41d00ca10040b51555009034001c000004810302640c1400340781480d6149020003c0014005805652440d401c0550240c4100703030140146140c0056540c0c1003c0c0020030511450007854861a40d550110750156258095a0302c0d8069400c0700282a140c0300360712b035000390024401c1503c1e030001d0358001220705c0d10106460341a034150340782860615040c802440c9a02c0228000b4400f455510307440071010500a003c0d00040310000c103e120051a01d918115041846100c145010f0022811006503a55100000d030340340c45010703c0c07061071001e9207850480c0140202c0e8950800c1d6000015011030302a103c0d41280095480c40c510742108000c0141c0110f0486921566036000140c0c00c0c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 149724037 1250 149722787 149722817
    0x1e0501050420030c16050705040501140904030e0a05030d0302180103090218040c0b0f0a0207080c011b051207050604110d021c0c0b040602010608070902120403050319050c09030c03070501 82
    0x101440d04200d8070881c07641030000d80b10507111005d0488106541540c0941810042d900d0180a41d03805040d981d0f00c0d034010b9250707040201d2507026000e00b00a007403154403480300050f40c0300d0700511401060014201c41c2001034040300503000f54451400803c05004201000050394080e0082d8032546502038801440c80120418000c00150040c00481d032051489000040ca21041400307014866881c0100c00e41c0c2c0c0c0c5654001034a01441c0e54070040e0180c0100d000c0b0f226030ba0704060204602e0540f03044404c82c1c0056031502a0038690000f0300000039450201d0b8800900a00040143c815445080383c0c03460900b1000404c4141c030b1401d44020341c040604448150990101c00859007802d224243c0c01c0c070050784900e6080b48a400035040500181e6449404003c1480d003000190005e01900004500c0c000260802c0b1180750710040c000b9003413080000100c0c03907480c0030352150346140004481c2084103040c105448803a41d171028501c14464880c6900b40d103410300c1c02007800011180c0503107074502d403a1701d03c003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 149725287 1250 149724037 149724101
    0xa0f030f140402150409140a1401050a170c04020c0f0f03090d060f021b0318010809062e080303070f050306090a0c0c0b090a02010212030906010b07060e011e05010504 73
    0x40312981c60603014040080e501c0c1c4103000d81101f0700d0b9150700041071031800050a0040711a4100000c218108d4040104202d489130781000041da212081591031128072605010f14140182002d00c2d0443d100090540d40f0300004641039604c0c02c0d5120070740301c02c00c000105082d902c0c002c50501030362200c2c01c0d5201c1400140c19900c40d225403110b1200140c2015210740c0c03a40c540500c401d01e00700590304000b901c0c8000700b00300f50501c00032035000d0070049400d0400148480c0e440f41d000b4145600c00601c9045c91000c904c5469070400510504038091521036100d0301c0680d100c0e00f09940690210700c4684281c2081405003058030312418002d0703d201d02541ea0680c03ea8013604042000c202800016115840896803005c0d40d244520158401031a402040c1c2c400203280450f406800380c03100800303000303005c01100c0c0070400504543c5c000515545944907810080010044020b10303040640c80c0001040e440e1241d840c00c1fa5010111080402090707a941013804107903406551021328002012101440c103441907 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 149726537 1250 149725287 149725309
    0x609090b120d030501140109030b06121203070201020d0f020405010c06050a0f060b09180f01030303110f0304060e0705010e0a05041e0608060f0a06051e0112020a0f030f140402 77
    0xc01141444110851650070403a09001400003e602c40c1c0050000f020b2075140d01094000a00c0c2c9481d20900c1c40d00c1d1141d01480107000e031441201300610380b41000c40104254503805021030001030340c1c0e09016101900079030142c156420f94a0904c0b0901000d043c880c401d540480d001030b19140701000044d501c0700c00403c0018011103846a440320314003c2c41c44588920006014032408172640c1c4c101160811520405151700601d8414100f41044440c0180314603460449502d41808210341c102c1ca074885802d8026400c920030503440110400051182e1a04080484000603060391041a202e00c01120400c0891090302d4001c0702045041145040c56400145083c5d40100c80320000600d02c08000155401c42d40700e60010741c010402e01081801c8082d15a40000325840d0402c40c0174030302008a0381d4500070315220a8465822460b040d00d6901030220907031056503403802190382c2c06511502900c42c400840c10340000034504448102c0b448914411444c80c58181ca408411542d942c0c0d003045126000c2c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 149727787 1250 149726537 149726539
    0x140105030406060e1003020109050f0d080a020a0b04030f0809060402030d050d0f020a0305190905070b0a0e0a03031808031c0b03030c0609030304030e030a0c050603100807141008010609090b 83
    0xa6500001550000301c1d12a40c0100298409101704610b14000100500d4451b04882d10172800740035110801c0c0c1d20380813898030260384940b1040c3c4445c54240c00f0380c2881d451010140055451000708010568440c1c444d119403d00380e01c41c140c040d01d40d018030b5a564001118000e4042d80305c1520911624000c4002c0c3c00c2811781004013240141a80708140706a0300070411000c0400d0b2034000780004040400c5150100143c200f50170820710b446501d0f91030b40c1d650941f0030913508c80c40c0001d500304007070721404000101e000040c040b50600c542c1e03454024021003120794441c008481981c40444c5840c404070031100307c020b4004401c540c0d10800e039100e40082250800c403517410f00c0200200d026015080c404a4441e600c0c0074003035a1240341500b0054111201c021805201390044070321030300010303806030b5414169041a01c01036203aa03140810440307044411f410070012840349500000d0100b600c00555240c440d01035400e600314074500d080580f08920203005100210302c182c0f40074001c07850b5642c098050300b04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 149729037 1250 149727787 149727791
    0xa0b2b0e0304090e1507020c09060609090f07020708030a050d1505090103050d0f050a0203120712021c1103041e02010302130e0a14010501020307020d020d020315180601140105030406 80
    0x21400d224a03603480707644054a0740741c4818a40d00201c0381070008120791a03100018400d00c0c501080001d40782c1440c21045403007450100302080d0541c8031101070b50b43d420700140004266080c808413040c030960040b54050010302c030300400403461030f4001c0151030324042140c90b0301c0d04100311074018402511400030b403203034442d544010004141d5a0005004c9c000e50142c40a09205060240005d0280b014128400103002040100b2040c2c030740d000046401030504103c103071010782c84000040714140c4030303565003000807030001c6020310104000240d40c12264001d0841082042e4044501c03400501045030081c2c900701034204141c02c0500c03208407813a880343c8145001480d004c01d694545803c00c540740c1140c2c08520003041009503a5109214244005000f107a1000d140c0d03141a000079a46d00c61800e00074043e8076144203440071501d5407080d4280607540201540c554000c0c0b0403a121403100c00f1a42e030a9281d294100d02c480403030002c41c0181c16906440d02c20140014000015a09ca5201400841d80d0036 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 149730287 1250 149729037 149729051
    0x3090a050a0c0905010f0e0412210209040b04050903030408030901090c03030806030d030e0705040b060d02030a09020a1502060402010e0d02092a0301080c1504030b01140a0b2b 77
    0x30424069804180c0c411006440c030365041503444800c03102d0503008950500000343c4240151218440041c1c0e0066001080c444000d00517801191403401c0d1142c06076450902013403400c030822094000c2c258941d002d42e81000034812000400054070f10a44034445190000c10100e00466a03850046521201c201c00105800f401d80e9248182c85a25030b100381c0c001411801408880e290a208214070740c0000d1509214081900c10f0b41516012144202c510a80d0380f0340c0c460395180c03641420b4031040303041c0e0b5004549900d807036000318002c0e0000c00c504030702c244841c800119001807400355103010307440c0940c0144419038031940156890f0071240700e0540c0c0018544031500c0103039240720f1080d21030b904041c483d085d420003286100c1c1c0c1540d440311403541c000000744014052040d00080401c06820116172280d2101020400c2040512882c1c10141071708510900100c0d4601c000154009100016150700c8401a40d40f00300c004140140800001c0e880c041303002e031145108940c0c9042d0742000c0340c03c0c1300054030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 149731537 1250 149730287 149730293
    0xc02030f0d05010f08011407031a0a140120032502090901060905090a021c080408060a060807060507030e04150503010c0c0b010f0e040b0405011104030515010b0f090603090a 76
    0xe500055158200c090b1104014000000380c8a807070001021440d00034004400311018103c08110000c3c0f560003015501c030030300c1403401c1041002e000b01003030207450709046d25110402d00b10394811000f40305012076500064110f03600c9258000c000b030a0707034080146003005502d0740c00368801411800d00d8040d041c0b82c8004000580e6418807100d00903100722000090091400c10b4003019614000c00310304958000a0700c000161300d59580c044241002c588000c055040380e854507003414011504150307070354450305c0f007009118016903000350161038260b403c4a203103a0b07503010215514454a40700500242000600c1ca203070b4246038001140900564503c12095615580440e01b168a00700803c07001500b80c1a114061007440880e43d401760440401c8603001900703045621040c8000608020030108405000a0602c46d0a42c82400c000d51020017007565a640c034288107a5660f564401c0d0141c0f800102c00000b0140180c50440e00300427103402031039003003030184e40420020380c0005000e00030700c0c01414050400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 149732787 1250 149731537 149731567
    0x71101020403060c020f1b030309120a080a0815030706050d0216060c050703090f14061c05010b0301231f0302070204110319020304030c06020a020a240f0501180c0203 73
    0x41900c2030345c014142c20050401c0180b50140010051080b44004100d9050644001c421200d803414181d402c031070946007040d020f41c9081078481010300442c0c000719400c2c8029510212090103010202200d0887c075401000700b5449450921498010400801034815100d80c981c01500f2241060b64020f207200c000c0b6200d10003546c0800c0040380001d00c00044031402c0581092005000d000b40070f045817a0b59041048410604207041d1000d481010007050400305c640d03010001d40388c01c003440d02040c4090b587d514a1801c44d81c1080c056180110b07610030070b40c00703000039201ca0751016406c004c04020074044c0d07810319034203d0984401c217001095020060300c2d0268865003e103468041c08420201c0e941d00c1c11000078454600c8401100030010300400c00c1c400803d9004040342c50a6400020059441c00300301c40680c60286402402840410029000b59a40480081e00c20058071500002d100c03441841b09410116002400ba0f6041c001c801d020360360110700d039540544048140c0f40100d07480c1100d240e00c9200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 149734037 1250 149732787 149732801
    0x2090c030a0e01181e080d14251404030506090322080d120603150e07060903050303010b0d020f16021825050412030305160c050607110102040306 64
    0x62442000414064420494400e0b072038241800b03002000f414010400120754200d00c41c00103440320f0141d8002c00f10564084201818040e4826070607546c4480305003a41c2c01a041000009801d4104c401c001000054650441203183c482c1c00d048100b0740003002d000b034908410441111401030320a000200c00240d042108a005844101c01507071100c220050350000e48002e1918544a221003005c01c0214901c001840c6540c5c405134104000d18040384400d05005010039480900703c402140c000e1100040254020301d00c841680e001c0d10b8207d52502000d0b10341c071045100081c000c0d4010001002002c500f080584450400c040c4094503102c000c1d40d9420340d80e008012008544514681c0403801c601c0c1c0340051980d60100016a00440e2500e84d01740d90861080045100c259100f94151101c004d01c621708590107030101000c80141c507007690038000c1c0281801c64000120440361905203140780d004103070402c500b40d44040145526568200b044681c8420355203403c0d0719640a02001c000950b650142c0a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 149735287 1250 149734037 149734051
    0x90f06151b0a0b011205030d050a0209061602130612020f030a020a15030e070b041203020106180f0b04110f0c0c061b0c04090201050409090515040804150e010c0f0201020a0209 77
    0x100b407101003418008a50078042e40503c404448882d0000300046003c8203640203c09071090015040e50341c00c4c1048043c5c0700e070b00203080d440314001540403c45000390b000c0d03d2900c2e00903255528030710110b40c404801c0310814000c0101510084141d58018a4445d80b032500e0108081c2c140e4000798002c3c1e011030700003016504079107860149810492000d03a814815103c100468000404d02da0b46404c1201e00360b44294001c254107041c110045909040c001d4005d24018106182e0701465a8861004207000b41a00d106c03030420141001100d80403407505004420711418034515051800e840c10629181ca0b40c020203000f0500e015051069106684280c064441401101c040580c0356228072400340c1046254030740350780b159241019510143c1d034050300342c41c2034801000002031002e02d503040480c90006c2082d443c0c0c98640349a000c1004110800e806402120750b00705550150305001182641e20350a0310095500040c1220114401704060030440600d140c01030043d15801c105640110391044070484001d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 149736537 1250 149735287 149735293
    0x3090206030106020307050d170f06041b02060105040c08010506030105010e0a030609050a02040e19150608120417071d07030905030a08090c0a08030f031b071203050105090f06151b 79
    0xc1c020b10078140a8584540c200d4a001a49e601e05c81208540c070300c002518061078400da0f500000c034a034403164046101c1d00c1c5003c0c4a0141e440400c1002903580a0034018a03015070f003031100d10891240240051810303150000c1400d0305507070030107004554039015501015808403a41d400003022503054403c0e8000b00d80101c015004c001e1082c01803004ad50450070540030b490340040140c40c490016400300113a16130f8810300c040c0048540100d050701802941c2c1042e1075038060020414204c90701c200090003200c00f0900c03110140012416199150180c6118101c101d18036040103505110304034a0107030b031203903041c100081c2011180c1c64191454001c1a417800200302c0203024010440070410003101c82c0030342150b200e0070702400c0031055501c0b40500803200f101281d011011610112400b01c000601122050007a604d81075035080001d0710a00280400340860303c4c140c0086014180048007900c540c0341d00c411000f160b20b884003800080c2c10408280030183e03600744500c040c11035440e104c1c0349554001c1801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 149737787 1250 149736537 149736547
    0xb030408130f1a0304021e120d050309150105060a05070f080f0d1506020a02011d0319110307060c1e082b02130608100f0b0a02061602030f0901030902060301060203 72
    0x203000b0090121001500880c2c00502c100001a660781f45541c00454540314890b80c1610280040784240320b1080c03015540d8003071000e10720340c2594400007640c40380d4241e004030f507065083d0403050360002200303000e0b85801c4031003007200d1303126140144028580544105c001c07240c0090141c4030b000d159000590031540c4842d0010728195090480c3c043c400302141c40c2c4101a114070329190001e541c5d208140c0000b8140b200022421a0b690442d506800c09000098299420200d00d110b00c8045c11403520030031103100e0101000001c841c00c0006a0170103646554a07038214400e82c50711100c41c0b400030f012903c018140034489a0002400c0031028004044402e003e166000c041ca80240380e80d40002d220200e8014418030040043d000400700d070204452007400c0030826038a4203032b044280028550070101c05c694800d000080e00c09810801070980306210b50070756049440b9860324046800c041000c40c801603009000080d14800c00400800e096403050500041c01c6410b54085440341d0400d0b40038101603000810 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 149739037 1250 149737787 149737799
    0x30103060c02150a090501020424080709030210210f020c0d17040206090604080a0c0f060e030d11160306090203010c080f1612180c0f06090b030408130f 67
    0x4903480d800490000d44281c070890303ca00030200200070401c0801d151680040b4007440020f6044401403c0d5201c1c03605013400c2c0308103020040e085a00d10380e00000c0e807a4000541414851101d51007130300d600804002420030895001c0341d00300503405800c1c00310251483c000d0341c0d8000d14130440c404400402c40241c3c071480500c00030340c2007005d10540f007424411000741414030030340c0c28640305a103da1f041785d10548804032980441d185002eaa00900480d20554070703e0f00500610883d81e00855020841840c0b0b07164940b0011500d40700407403034103505130381301000d41420345000b001c80d05000c49484007100c141003802000c0250409456100340c0b04940d4903c125025030400303000340a4450541d04004e9501c0c1000c900f0788041e001300510040510182e09032800b10a0f110300301c00005150600740074009801006c00490f0100b213030401c100d4511291190020710484514451022036030f00f40c0701c1c400b40500d4602c958811b980300800480ba240703020003500b0441da413140c2003000505407081074410960705042c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 149740287 1250 149739037 149739041
    0x606010210060e19180305070506070e1309170a110105090a0c060e04390e010207032004240902090f0105130902040b0c06060904050604020d03050f030c03010306 71
    0x10070340310210307414501c0c1800806020414141c1140c21180d1041e01030549401d0000284200419640d00301d11110190040c564404064904a80624241c03240d40d140e158042e10b2401030901d0503038201c05914681e544084aa500821000e0301514541007a41800650b280d160ba1062105501299050a0307140b02c100007403149a61100456005168030180c0c2d0301c40a103101003911500c000c124044003240c8042c0c403070740c000c02546210000c1e6902c0421400380341d080c940001c035195031010304d071044100321002e00c14052080009810303005010138034155100c5480c0400400b8001c00903940c5101d85950343c1d12140306d402c11600c1280000180481d864501d4214038440e50701160080f401170022181a1380c03070400c86410b083c401d003000c1d42d41e2580d00d00c076054000150340c8140b10f000d00c045000642c2401c400010b00c00039501a06076116075880030704102140c00c0540d4050308950144001600604181c2c1041036510b029050103401d10300e85440111550b0305c01c8811100554010004204000e414 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 149741537 1250 149740287 149740303
    0x1c0501050d170307021216030f1706150c10022107170603010e0d0806040c0912020907110106090c0806010203070314090607080403060207020a05030714090709080a030206060102 78
    0x841d00d00003000d4a035100c0b020034480b020707004690740c0030010101e0403441c0200100b440b450300304c00d00ca42c0c0341d2105d0040d040c5e0f101d41c0a142034020601c04010846954810402001000740c0e450810260b038840c0002d000083e5040007503803200590030408285421010011034282100700391000d640c3d8102e0384003c00c0c010469540c0070180c5084102131002c002e402292402412500c500450910303034500b0006805480c400c00140e4050154010070711001d680440714074403c40c5c00b40c40a121106006c0011a8000c5003807050b212050f00c0602d0250042c5020b00740300d5004081e40c688130300e00507015030002c1c0c00c503003142d448407100941e1042c55825103600110020303800f140900146050203c251006403600301e04606030007440400280d014020390324102943c800e03640080301151901c0e00ca14002c00294842c00040e0712544c1d034120b0000752850f001506100340e0f00501c0d84d1000c0c500b495010300041840160001c0701b448220003000c2520300b4100066010a40241e00520380c034141800007a00b001c100c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 149742787 1250 149741537 149741539
    0xf0302030f030708181c1a070203090109051005070b010803040602060105010c0f02042a02010e070801020712080601210b10050901090303051b0d020604060606031e02090307030203031c050105 84
    0x42403000d103011586010546440c4c40c0c10440d14000e204e0054005100c10007000346c0f02d00000709418948081c000c0000000008140c00f00c42d800079034480039800c0e0b03964010810440c1c005461038074140071a0400c0c00d500032444586081103410071210365960503e00e80260401c003016030001c18200f00c4658108a154018642820140405502601c0d00d240d8641071800280c051034980d005080140300341203840190341e100c52660b03120300501d0300300280603282180707803400c15100704440401c080c003042c4210740041d075025040c031020700000401610a0400107002c40e0500051201d070300c1c0421006480344592180000000500522190401014800340c800701d10810030280040344151340c01c0440501070303179050f041554850342c028158180d0401482083c1486000d00392006605039000102103001d00e118136014440c05844403011411151020050b04140c3c40305c7c40301d480745d504180d0040240280c003405584110740c0783c0c1c020030310350740c050610200203a1402d3707a0380031860303114441c050141c80 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 149744037 1250 149742787 149742793
    0xa0506060f0904020402160512042408040b15040c050405040513080a0c020d02040e071a0c06130516030803061203030c0702090601111f0615140c010f060f0302030f 72
    0x1c81800032450000005000a00a40e030000d07040807a890501240000e0550040440d110071100d45240700058005104074421042c00015a1625440e401c48060440d0410b035a80350090340e440d26071071a041c5003c1c0a0260840a03400d0309821501c4034000c90400d02031a4840c2a80d5500e4072003440101c51008000011046000184000141c595021110f01403a98906000c0162003400007687c04440032100952007403401103c95084500420300070b00f120b00400203e440e142c82001504180d209030044d65289810603c001510b01960f51021001e00f1b009030308030b54100001032000032882c501e9402c15600d0380d1003c4100700051422401e48500348180c0000745056082c0f07604900750900800030000d00c105914000206240d11500e00ea50340000e01d0002c403030040c01c659410b0404c08a16100100c0384a01305940414506640140f0b01c1500003c0d5a880d10b54000000d0000e032240c211801c2d6603110b540342c02603010741e0030450060002610b84001164581465413041500d404404414401650 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 149745287 1250 149744037 149744059
    0x20a0b090d090303140904090f0501051602100c05040e0f060f010509130c050708070606060314071706121b130501080d0813020d03031a0a08070314120304050a050606 73
    0x280d002c90000e0840c1c2d4181000b40000801c15102400b9004a050154001d80380848900034000280c00d10100300c0c2c0a40002c106a8891114007240814801e0260003d0ba21a20305002030464030360141c2d1848845103000750a198590b403124008241c184c550640300580801440301c1440c103218003241c5a2002d0920310700d031408031004941380c08400d15807240d103585d0360b0040301c680500401c2100c1d981940b0030072041e030350085c03450020020b020f280600d1000a207850410580c8819044140780500926165210824010014460b030260001c0c056504800203019140034003004122842e054000414600c1c200d00000081c000b02d001e0540e1040e02d000c1c00c100040040301d40c081100c146612140c81c08591030360750641407061410140f03000a412100703008031341c402d0541c9540701c40b148001b2038511084004204042001c00e241a000b1f400c013503000818100b0000740d66860035001000f2040c1138440c01d00b1100103108858204070f50507075440c0c024417a0502005018000303aa07024004a444132048 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 149746537 1250 149745287 149745313
    0x180c0702130e0f240a0e010e0a03090603140a051503030d2f0405011d09070504031110020309040c0c0b0708060a210321050703060f0f05060a05030402190303020a0b09 73
    0x515854091015441107902017840003001d608005600301101d002400002d03020100c080d5510b401010950010303060141c0418443e01c203000300b4110007100800c60b80c0c1c03a140c800002e801000040c1c955501c4107aa80d40e4000d01c1d031000c1c40901a100c10380403000038030010003208032005202c043c141030761610b40c58194400c03d64100c01070ba01525000c0c82c2021018070000c009110f903166002e941e5520419180400c990a54804000c10651384200c541a2000f03002070306014074807a00200c50000350b041881798043c20300b09a0301000c4078030010b16007080c8158440d200c4105ca2760702034505000140c0400104030a41c00c080d0604002800f02c944182d01300b180c01c0c000f26100c100c1e42135004003003150804091102e0301504c1d02c1c1e9060801100303820002402c1403d07014004051764420140c1070521050300082ca2144001d058089070409030000f0710301500b81c03808035500d1f031000f0801c03030b030000c80d0100d20b040950a0003c03001c00746d842a002003000e03100c80c1c141920811401030640680d584800040c05203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 149747787 1250 149746537 149746573
    0x20a2c0f0904150e10090b0105150a1403070512010306020301080f0604111003110c0f0106090902060405041503050f060a0f0902010e090403030b0d0f0c05010c02180c0702130e0f 78
    0x16855080800260541c1103c00e017070509440c011801449402d02c501e00041c00b0b10380344028100c85044440c900341c020f0001c01e604c035034010445140081180c02c0300319680440000002c40c0e000342d440c54140d2a0400f10400501182400e0f041580c13055030105c01400344240401034920303545204030051450389010340c1c3d8482030304c0004421501a40f06103280c1689640260801d0720756241d41180d10b80c4034a400103041d41d4070320f0307200c0020280d9820004001480c41d95841903200103034020b41900d00e00703410002407001070201c091040c1c0d842000e013140000070030b1080c40340d480791142c0b601c050310791400c0c804c001d10700751070f59648082201840c0c80f501400503a08002d034a07090480a80712104140c1c0c0d00d080170740c002c1c04807141440d00411856286800c0207864003013038128504c1a5080c04c48580c946004440c4000c80e1b00000f07401c6403401c540f82c24084481080541e02401c440c158070301e00292540810700d500c110040008800351103503030507c01c0303031024800d0b00e2540741203000400c4104c8030104844c2c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 149749037 1250 149747787 149747813
    0x8030a030c0e060c0607080a02030c090f15040f060908070605191701060e0312040f03021e060d02041d0c030a09020d0c0807150203040315020a2c0f0904 67
    0x814160344003588400d942c050392481e8100c07580144440e449511442c00380b5218401181c4a40c0014a4040001d0461000788280c90142d00d0050701039040c406003105006601034103800041d0300400c0000482c209412480042c805007980140d04a111450010050701c2400f0300e802401650708501014041c00d6446020303200c1242000294110001c0140001e0354020400d451603040181004004200540c1050318070000d90f83c241d08464102e84c0e44414505140030f103024000c5a00e11422041006d4540207034961307051045200da41c900554802c001038501d1340000c03400f908107500803801700603004c2034011025901211100358019403510380c900c8020351100406410a488e40e99001800f9500c4492800c8204c82d4081482524180c42c2c00810b6aa2500c1d4880c41c0048111a008c1503807051002c010f03a000c90b03a20070356444441d40d42c2c07180c01020390445400002000443d18030740d60b082402c2c1c00e40c203d00012090610107600c8140080c0103801c900f8a11713040c0602c4035081031000054401200380 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 149750287 1250 149749037 149749057
    0x307080d0906020c010903050414031605090c0d060e0105150702010f050f09030f01090c060c0b060d170a0914010f0c0b07021e0d18080a0b0703060f0306020c0105010e010803 76
    0x7840c00c80e03072800304004d0244000d4000d441d07203010302040c10142c1160080090340c550342c170382c0000d03082c1107020155039001e8806a4050320042040400803428134030303141c070f82184021074034508080050040908079883c0c0d070f010a0100700036100410076818002e0304005000c81e954151407402c001c1d500060300d109a01c49100c401c129000400103004402030007030716100913006082d68000c1d800001840e02925800347c00352000c003172480b000142d00d40a00c3d080850360b584140714080301d03a900410000c800407160b8042c0c0c0c0c0801c1d24030600a0409942000303100205003500d4040043c0c0c140810344a100081540c014184002e904608211503003000e0069512130303101c0d47d50200ea541e4100100d080400d064040e000c50f007491070030760401c1c1c1c00c04150141340302441d0351410707044a00c0c14420b0b0411f0180e0b120750300554211402c020003241200c9078035540041da504004c0b030020f03940d07809102074910700e610540b91150701041035a001c40086c022035005240c0c01d00c40d195070754140400300c0d8483c1320f565040c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 149751537 1250 149750287 149750291
    0xf12061804210513030b060f0d0201080705090604050a06021e0102090f19030c030c081c08040f06060302122104150807020c13020a11060705180f041112090307080d 72
    0x148030043d03c504100c400c503109449400d4240c5660b890081011401505c00500c50b032044c049484142c2081ba241e4003102d038059407020720325100d0b24001e8a0b258010103100e500100108400320301d0340c80d819504002040185e0003002c00d2105540c2d6050f4051105500754610b0f4010854407aa039582c160a04881c400d045a107481910010100521800c0781c0358002007110901382000414044001076150440d0202003d6482c000414004a608090108114000310741d04c0404200410f491610452525100b44000261962280c0004002e0b00040019100d268003e10030507902510714890310031245403603028241468201011800030521040c1c140040041d070701e0000e107449108018062000c88003a2a001c003da0102d00307680c020790b103d40b070340f0004944040203000155200007000c81c17003030302e00e90344140c00c1c0301e81c8400405500a54910131035005040c10501c100517941d501c01d060403900c1008296036100c1480c1d440c02c01007075008044210541081c0700c0c0d540840d07840000c1702c10554144c000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 149752787 1250 149751537 149751593
    0x103051611070f0b0406020f07050a0b07050f07090e0708060606070219090c0509090606030402010c061d0102130e070912151e060e06040204050a05150f12061804 71
    0xa0380c2c945450303503104800044010300c0010311089a0340c020010744d003031542a51040038440d41c1c45c5661305410311400b50803803045c2c40c00b00503500e505005030540c14410020b64020311400211035180400d60307004080b981d5580c408202c0610401c0194000915205001c0c2c01c5902c0c03e2400500309008a05000e0b0003010750404100496441e1002c000107002c4244c01086081009240104680c0182880340e00490388070707000ca0390720f151020580c2e100c0d5078144c0d6091200c003066618a40038103507403c01c84420318022400c0d040202d10a0016141c0915504000701c2c030725140c00d944000c0010090a80c01c1030203076041e414061480c0e000768402d032160b0001a04c8410980f000c01007002491490143c1c484e103100c8070491406140c0d06d4004104440e00c91240750903e4039420b04203c2244a244903181d84182c56100c200726a041400804002a0b02201c0190030102c42c42914584c80e0f200b00f0004082803051030410840c2e282c50040c2c184030410040c0c032241140b81680ea01d003050b41084049807611179551031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 149754037 1250 149752787 149752817
    0xf0f0201020c090f06010f0e030303060d0821041205070b0c0304030e09010b030f010602010e0c0d060b04050c0409050106030207030806010e03070b0a17060301090201021f060803070b1501030516 85
    0x70005a40c40c00152070f100d05850700c3c508482420034281c0340140001e0b68160700e0030506d07109600d50b0240c4807000340510b103551a69010490300314104001220790550920020a4421307105600b50805060b6095200480c5420318000a40c080c03047d9800c018000240602c10100700706004040d408244000450741d240c544c0c0c1402c1d103510032032000c06a8089003c90003c24145119400366000c1c07000c1c18510051640ca40b00c00384e0a03682c034034141c0c0307030f2603441424144030520b0000b0110020b6070107002c00060842c4444041800e503201107400092420001408201d1481e0521400d40144110b14086090440c035640040c64050040c202d036041002d140c100c2c088a903010b021110003800c080c0102595160b400c803020f80000c1501080448607071003400003445038141030242c0403900b98140c0c080c0410089681c907c0e00e905c00d0151071076050641d00c05010031002c5041005000c040d00460075100c903850320502e040590011174520034105420001880100512128541c07c00460707030030403030b201c803074040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 149755287 1250 149754037 149754043
    0x60f0a2001090f02040b01030e03090d080c0f010207021509130f0b19061407260d0606020105060f010e0906040209040e07030f05071a041a0408010c0e011b0f0f020102 73
    0x3020180d50351900e001c001c20880d036004800109482900c0078000c03020b82c0c400540031207940814084564204101003100f602d0203000703020b021031040302014104081c4204491038002e0f01c680711965070790700092032002c0d0b14011000c0d0242016a10015103865040b00115070352094409104002d161034610500d1000d400c3c0d001844e1186010b841d01c8a1080c01c0d1103000368901d8103108a00c0400c40c051500388080210030300b142c2c4c0c0c540d008000c561000025404145442981c00e91100c0140d1042c04003210110319030050500078107240c1c1c00881c8a06001e01008012600c007a8000d050112442d218000798580710621a4001000c5030b005840e40c0d0840c000c1405032055003003600c0d060140b00b2006c4100000303a42d448419500410446461a0721411146541c29401404641d081000d00040203160420003071048180043c4445da81401d9445186a00350707292015040d0100e41a8102070b902541e20481400c100d80401c2c4004070888565100c99117080303050300000e084018200e1500c000e59000b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 149756537 1250 149755287 149755337
    0x3010f151d0d02031603060f0b06071209050d0807030828051b04080a0c0b030405150709090204090c0f02010213030303050a0e1608060906010e0f1e010803070203010605060f0a 77
    0x50196100340d0426a090390aa0030a401b0444150340707481d1109464140c41e120301031300c221010740314a203880300640760f8581a030700d00d400182c10131180c102d0100d081d40b19031303406c4130315148501c10f12501c4d1400e0b8903018000c2d41b00146150401801c4e003c11032052008801c01c6c8040f14000c2c40700141d10344800105031a4850400b180001202c0b0010f4002151180010300c0d07040caa028460036100545c840600041a200550f0058103e070b00c00300d041020304c15074261454221080f414224103081e969000c1030145d030002c1e88101601039503400a080d00c0c80e040b0440b00c004644510085107008041d82c100d000022203400090101a900d0000800d000e603250710442428902108071070b4200150728611040310b105000f014a05c0c02440c1c04904401030010f0b9541c12707540042841e0800f81e82d0b40c0841c22682000420304503500d0001591090908208460301d03002c0c2000d807025541e1500039005044c00d4848591040d03016000400140081c1c900749015607800751440d2500c1c1004c01d0104c00351041140c10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 149757787 1250 149756537 149756539
    0x603090c030d02070911040f0b030702070503100218030a02010816120f0603020102070e0103120c0501090210110c0607120e060d05100e060409030f030c0504080601080303010f151d0d02 81
    0x284501c080720080d00010304c4400c84007401400e12480d1291071801c5150300662040c480d01d0f40003181c0074080e0004140103154886984e104941040d95030308002898640d0418070219055400100d03d001c24041500a91000700140d0041920b61410b5000824000009104000300088090001e6042d44288022010f4205240c014494004003182078801000b140c40101d000d840745410009850881c050218100c0c0c0d04005890302030651107000307603040751041d501140c06540ea011824010b079241010609162826911541004003810314540f070521031081c06486a001030003244009a001110901d44490b14a4006040c2408401207a6a030060502e41c2c0c0c805410041048504030590790380c101129400d45420455490b0341013403101b2144c45a80180001e41c11564041142c0d000749c12041c0410060314180d0f10702540d40f44250309050003070b0041e070181e40000004200d4080040d40756005406c0f40030004910303403101b410182006040c144021319028240403200300c540d07601ca0302d20f100560 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 149759037 1250 149757787 149757793
    0xa0c03030f0b030f0d02010e120703080403090302060d05040b0105010302070b0105190e09030a0311040605030a0506060d020c1b04060f17150a0209031e03040302120a2f010305040206090603090c03 86
    0x51140300e42e030384811200740390354019840d290800d244402d001a89d0a1107a4098400501d00740080e2021940c2001c01401a014407507075101c00001620380c0002040080860345001545062616100050761b0045e40704038100f500500600e000b24902501c0d103811103504030307591545100c0070038003000100e09541c40745030321040010401644180110003041d1020b00c03aa020441600c0300c41d00c10000c0c0c0a9401803e00150341400082c40c0201241e221540020b00140340c28200304920924605990000c0c0107004260001242d144005440d1100341524100c01c507402d008260404150784528002032041c43c1c000300c00c45d80024041142440a4000b0180421000d1114940320345654042c0d405044103030300a120300d94900c54080c0d481c061044400002c04040d5240c24603607000c2040400f40c10b15131981700c0c050041188001800c440d0030051421070b80350f100801000d00c2c203855a03071035801e00096043c14200020040141e03140c0048407190384044910a44903120301c5034251501343c0d1003407007c1d0584 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 149760287 1250 149759037 149759053
    0x1081045061509060b070b0f09070b0a090603110c0c0d11040c0324061e020312040f0201080a020f1213020a4e02031011070c05060a0c03030f0b03 64
    0x885040290043c0c804159080c80510364503521106144a0030202902d540280301c0841c040c000800b1a0075001200c090031070303109680340c6030980c0650380310107003c001141d01c1a41c00c11145415014031781d001d1412a40050503c1c0101103565103950408114603c100c8041d22800c0c208030003114506042180900f0400204542000107002803400c1042d221101d40040c04120b0f14074108a40f0500ba16900d6039440200d00240210781020120b00c502c54066002c2408541c0d07a800518086a00c603c0c014400324403095018000540307c104040d021181c210700400c03c0004001c0c217901191149001207115900329602c00e2004c00303150000303120085d441403586e1720016a80301c022112900c04c203c28083c0380a048100c1e10103080223590582c94800c1d04940c0c50081030a40e01d0041000d41d014005000c1d6406020041600c0045400d005128517000c040490790303206118001d160741c0041d080035246a4078094015002520100340a01f004003015201c01880783c0c80c0240740c119016600015044650107 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 149761537 1250 149760287 149760311
    0x3060d0c09020d1d0a14120d14010b07110d0311060708041506060905060313140f0d0311030a050405010b1c1202060c0307030c090e0108104506 63
    0x60f40c48044610701560600d4018010080e03054202c50540603d0b1008021402d080e83d51188420b406150000290181880001c0c500070080002c0404902d01440040d01d1a60700d6101c000303120307060f00309104040d81800070341d000071141c5024000d1040205c0c0d070046250400c2c0380c02c07221515030306902c40e40b500070b0100744189240c2100c0e00c2800342d0301c20341d090750282e442c00c240502101c0d2144194800920007103070810190074040d00a54001d650711220340c0320b814040c4c80310001c80c6440011442d059000590a40c9996400d20101c01e0016040c40d043c0b03d50340e50040c3c040480e010160600c5481541c41020804001096000c84800e840280c0f52448070105ca0b40442c40500349404291624600350303514026961010400605c220740d01041d040c01c540360628120001c0001554090610800072000300388060180e1810b8000c003100c00007003400807404004c04042e2013940301324005c1da41036200305e165003e010380254040100840c1220450a04039044040b1113803105c40090030542c42c0a11076030301 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 149762787 1250 149761537 149761541
    0x70906090c020714030c0d05010212070c0b0906040b060f010306030c08071703030c04060804050313030c05120c010e0d0611180901060f02060402010305180706050310050a030203030a0503060d0c09 86
    0x4882240e001e9918044d42c2e412001e00c80700d00c090000b40c0c1a0400c10002c02c29182580c62010540d006400041c10894180028402c0b4242581c004c400b18207180b04000400182c80c030425840140e50f006042c0c682460b036100301c0540d401815082c0b00700107404034946a42d04c640c0c00030005607001040c0189441e030300c1d0615500d0b0303545401500862080c420200c14120f0001040f80c1c0100601240c0f2460b04d86000000c071008200980129041e02042121000c0c0f080018142006903000b400c00c01d040301d1400080201c86d44607004501160381140818100b40d0380c000d004603841e84c10940303400240c000720345070042c0101010708008590f40d0000c40c40d400c02903500740059030f061100f594488051b03600ea543c10741c0c005591002c4240140d101200060055200c3d8010395003001070070151016003014241c0e49400d003a03050f08440000b0b030021082155070b800485403c00141801e50b1105034142c21a0007081d203030300c00c0c0c440100510800001107603481c0c0314101105080342c2c00c070720044403c0c0d4540c1d4071100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 149764037 1250 149762787 149762801
    0x307030e010204030203121e12011d071e0207031506080d020303090303071d03060414010501050406050d17040e01030c0504142211030d05070b0106080603031b07090609 74
    0x289400980c4255050520842d03050300c1d0014010560a402885031120692101e10a0f2122090118154951138500005041000d0803e8400da41560410b01e427201d11415070340d8110b00c1120300d80c0c00d010880b078000c00c010303491680b5200b400a0b05081400180c0c0b51160a9000804c200d0504e484820302d00b02641c0420182d07001c10f02034541c45c00c0c0141e02260380b80001d44076280c45400400202e05140c0c02040c4402d41046001608c2d85488815400030382007034001c850546a0340e014406450050b0790a102d01130150408035410070981c2e041c480030400d83c540c66034004242d032010064a00e000e030a8007003614000c0083e00a1802c0568513890412030204071842124040c0d030074100300500202c0791101e8035105000e5421500c2a0750004450003400403115001581d110701040021b0205d51400e01603c8504115034403280d645001c0c40c50403003140d1505038400c104000747c0c4d2061021a070780210845020740702d104a0300101c10711000d6a5810326180307a1215294610b4031000180d07410f610f0300402 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 149765287 1250 149764037 149764051
    0x6030b0901050d0c0b03130204020d050402040b04060f0303030e030408010c23031b070c030501020f070b0f091c17010f090b0307080316030909050f240102030d1d060c03 74
    0xd982c0c03002804040e0424035001003508003000028030031860107201441d4011410302ca4800341c4211500494220383c801512070308025140d0041000350708150140480c810002e50b03040010610f450f00344140c0407041c2c0801001c1644581034500c04550030000d94010f456018004c018800340404050315500e20000c20410b41583c00c0158503030003000b94242c9205420030558034109503000030805207503500608007102c1c031025104010002c90400d00c007502c410022250046c0e500c49031804d191845010040603400c1c84000342c0200012044089002c2400d51039420800c0c01c09290030800b07440c600c0c00c03650f00044580d4102c00014503030000e070100c0c1c02190341000e02040407443c1c500c245034072800c6500412070b2a500400429014066809043c1ca0460003442c2401c160341d101d2038214107580c0151096030100103d00309108004281e0942070070900d21100c1c5d00e0942180d02030000c0d40b41d00070411508922030f9540012400306100e04403034022448900190350707080c03800200c40c08068105030303002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 149766537 1250 149765287 149765299
    0xc06011710020a140901050c060a05010f1719170d270201080f0a0e01020d06031209140d030905090a0905060714070605131202070305010c09150f02031306030b 70
    0x42203820007a100710b48024181d640d401040c0507002d08580025800506114100081000481c41104041c0070480c051551000080340360b5160000100760000a50042e040b8441040e141442d04880040e07a00d000c039070401d03226001021542070000c10900d2080304043e45410005003410031840980c4480004170140040f50000c0049048103052101400310003808500040089035849031034070343e1958021711260000c00ea2102c00205182640c001203000701c10640c075110309208018818240d901c031a001071800fa208189040c50802018081c2c480c0c0e64001c0340c000c03100c102818070840c0c0c0310018000103000c0039001e081500c1014003c00404100b9a1140652404144401d101e5041c41d8950307c280c00780c6906003000398461000a1101912001001e40140013203000200710b51240400381d002900545100c40c03a605010782502c64400d02070080184140c410300c80c4500000380220552101d00d4401d40c2405010000c2c1d1852190404a00024080040000302c0d82e034140c0005000b00303c01d47d24 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 149767787 1250 149766537 149766553
    0x50f0c0109090204140409020301060f03260306030307060e0a0602120906060301061203110106051203180916030203060f0603090304091a09011a0702090a14090c030c040c050c060117 80
    0x48200c0c0a517006400740071504041c500724070f15040e003001f0003050005000140741c1d6640c0003c60004096944116080f42c0c0e149079a0030801c014921791140c00b8400d400c158598035064000036140e00c9030f020300400e02030b40d503d0050785c010b0f41000581c461951146c0219612001001103090980046a44c1d9420b03100f8500062003604060040304201ca40c15030030501c01c5082590255013100102c0d24440c5150f60f1540b0000d816901d81200c1402c8048140145507500b01c40c03081c070500b100028910a0207581e080301449003040c084907409080304843d00d001a00c0740c682c100021085240d83e030000740d0020001c0240300c08c401020008004a8110320410441000391048103003010031345e000002e80c85082280100840000140c50040d0140050380b0285030420719800500c5070642502e20074a1030796281c02c41c0d00990402c3e40000d801105010052043c101d4450020356501c0090114501594666610440903801402600e01726900041921015038549a0b41094165000414a02c904c60255 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 149769037 1250 149767787 149767799
    0x607140d1107050c01110706030b060d090b07080f010b0306061b0f030c0d080c07061d0a05031306020606100f030b13050901060f08070e0c0d09030c0c0b0a2a050f0c0109 74
    0x6e5002c2ca100412000e0b0040502d0094140c00030b0071510903585e0040c20800108408952900c242303445c1c14841c1440c00051b00700200c000740301c40c4004007189200c46001d80140030200043c02602d030301820407286180d0741c0141c80404900c0001649805609205012005524030070200140c08111004001c48000c82d40b800ca0031a9a00404d444990044104102c0d40b8003281c81d40d0000140e10086000f07500706048180b40551602505480580da56000442c80c6100301c4144032100c001880f080c4003d028900b00780c000140ba404a00400c14144484190700e010500e01980103401c0c1c0c4c801c014510203140400a03007010182c00229801452542f07010b0011035494034812140040d1703240c7c60020480c580c14050300082c4c448002c0d2800b4081902402040c2181c10389004a01e81544661b503070060f044038900c0c29104410440e01302e10005481030241202c4030354000c0009103610b01c1079400c021080510180018104030801c070240c02c1d805008260b40a0010005103505082001c2c1e8600c40c030385566503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 149770287 1250 149769037 149769047
    0x905091e0a0b1507050a050a0c051806030c040b030c031906180507060f14030c09150f07020103090c0b040605040602060a0903080708041109010f03061d0607140d1107050c01 76
    0x41d0120fa000b243c1850000f400703c0c64001a04510344900c003151007650341c0c1d4031a0391078419240c00407140c4000c0200c040c401c42c01c001c030900101614201c0352120341c1c20709800080d19528800f004030b004039511148803003c2e0b90100114448858040c007614080c164043d07112042503a0000203846a9040880c44003440240c11030b106c070074a800c071010b803601606060b070844081d00c9041000b010440500c45004140403044000c0d401500e1400e0200c3e514028901070009003503a8601020468200744848400c450500b41218002642464001000082441c003200c0706a0a40c00600030b0100108004c1011504440201b054610720740072511a0f61f590078103030081c2d400003000280041c84400220f02c481c4d004000380c41d0000e200c1e0784091481146c3c2c2c004070395040c60980c421410880e1f1300c10100b003801224402c50b9000800c0032050314009801c402410340c0c50401034240d50802507100071480041188205980034400700780400d100c030100803070311f02c0c1e0160040141980d1901540f18110b03010f40c010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 149771537 1250 149770287 149770301
    0x22203020306070f02030f1611030106050105090d050321010609080f21190f0f091212020a0b0a1e140c090103020702030109060f050c280905091e0a 65
    0x80090010f640d42d21012241d150420402409511060051021800d030b01000b80c0001c1c1e20709642014034440300d0400308a0707404840728844c001e03450a00284626648502240ca03443d41c1910304502d820010700e0030701c0ca10f205900c040c00e414068414020500080100400d04a50b03a6030f41d160710701070300c45910030745a49907030070600d4040d0301c518581900038030441595070210565002c180e003050300004195408030200a148800507a4501e00300300c0b40c6401c42610500001c103071400300d8009042a2107601c40030b0050b00301030410103030380c00c007084250f1080002c01002035011040c04054103110f00c03203102410b204400f19000000091808115102511610700c241e07880d2010400103841c0c1c40000e407610390000c41c6160405800b000010056102400f035540310500c648030002d8400c55404440302100d5000d418602002410800110755204080500d4503c10b80c012880340100c000f00c005495940c0c091f40050341206d03c003020000c0d064041c14000101ea040e582480b14250b0b036100219080b0b03101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 149772787 1250 149771537 149771539
    0x906050108011104060f030f0b1009231e031609060f09110702040902010e04020a0503010f1d0411010513150f030509190c0b040b1b0c0f0621010902220302 68
    0x1411b0303d050750741c1d2003908114040b03030039804006020581c08000c15000030741c28a0300703030200d181c00c90100b2400f62905891003504480700360f0480c0c5c3e045190300048002d905102c0b0485800b42d03006000406a0b403e0081c0c01da45c5040001107920540d1b00d07001900075000e00d11030300f0741c070b0404e00000041034a018002c1c41005280e8031011840c04d00940d00700402044034050580c100700c0d01d5880381449032160b200402d0001d400740c4a40f0780b01d601d0920f00c00c24031030041e08814100101e02e5150301a03800390011464001d540140801050644c3ca00126654020110186400e4200c2d034000200c41d000d500140c02074012903500c100641004030015015034105860620450f40701c00ca03440101c2005480740c3c00343d00d2081041d505aa6503071400d80c64250003070b8100c060007620004081e0700c1c1c1445140030500f0300080c1d40151041041510000d501d017040941940c0c050400044d440d500720b0145010852400041201f581c0103513140c1001b14020b4100400c0c0300011008140e0300341901c00581d40711411294 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 149774037 1250 149772787 149772797
    0x20723010c120309050d030b15070f0816050a0602040e100320060c01050708010509090f1005070215010f06030b0303031012020303190513091a0f13090605010801110406 74
    0x5807a80d2600e01010502c03050804240c3c0e542628400241d00707009600400b501c0d6640450310038491000c104003030208090000d59200104810000200700c40c519042d9217400071000c54071100c0c0e003400d201c1c1000c01c001005085020366100c0c541004003541c00380c0155502010842c2e07269413a886100e50b0308005000261000064800c442d0042280710030200180318040d0030780c0c4c1080d540700e9125003034880039030700e0401043c04900103100c0390070300c00c4140e0742c4481c80d013004100c15030a10583c99201c010b141e401c07025854981001604450082008456005201d501841c1940c0e440605e100101720714024040081e0619008245a00d00001038a0080027080c0c1e1802c2114030340810b18246000000089825000034001c01020360100e44550a11420743d88415541d01c04d12200104103070307042c0d0003040d10140f0b01003403c87c111211060032464290140e9980940140380000940400c2c41c0000b2811480d0609444404000ca01d42100d4121095100240400504800040c209000718012080019 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 149775287 1250 149774037 149774057
    0x8070309150905060a2003031608070e091015080106020709020a020c0d0f02060c010903140415120e010e010e070801060b0a080604060e04081207020609070e0a110a02072301 76
    0xc50058000c0c01d80c40c40a00301400306d202400030100001c04842294011a0404001c00201c4038180700034800c420841e10b4128280d24011801a00c40e014404045000b6824440001d100ba00b41c50024006003e84502c5e131402504455001040c2490900801300180100c2400050400032130094407025002d41c0c01410f420f620b0402030144408c040002a07895800343c403c0c007400350700c4180c000c2c4100221840003082c0d1a01e10305000d803508000e4141e000c0c1c2184100006c03c80b8045d210321208400d0036a240580c0154000c200c00c1e4098403801038080919442c0152101e44024150702c402c0800300321a05454200d503460b00300d1030886003548150400780300c0410940c20320610801d038466010340c00030400203200e602d40d00000894030302101c1c101d400210004000164040500c00c03140c3c04481440204100d2400c51501038840c0742504c0748a010020050101d03003100c47d240c1040340c03a070744082c04040d1240a9448000d60312001031044940108a540508000d0180040403070000c2e14181c4444d40d0350 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 149776537 1250 149775287 149775289
    0x203041505092e030b090f0c0705150709050925050c07090216031b020105160501061a1207030b030a02130902030a0309050406080a1a090a0f08070309150905 69
    0x240c1c0020941c03903002c400754022100b01400342c3c00c208001640c04a4180c01011003020140403564449040c602c03980c0d51804020006e000026900da02c12840500582c444407540390a51414040e02c00c0f810340c004101007040500d03170b800400c51007142d108440d0103e00741c03a404c1c1f03c1c2c680841031403800e111880341c00009060150146005018064481c0204c6581955400e620001c03a0001080041410a0024910141b55000c43e14803411640e01d03150000c0d80a2550011382103120f11109a90118080301120b000e106080d27001c60002e0550301c071450303c00310340c050241d540d580c02007003c900a02d2030600800e0005200b0700c20000c41c920b000d0001c02c00070780d0580070801c0c09a182c8070340720400c54861703d0150040c3c03030500401500700d11a407212020340d8140001c000580300d06030003102e000d9106010034000300b0101c4618020303002a4000310103842d1101c0304032a045c480c41c0c900140840440d01111070420280100400205009550f500411500c1d00072101d4480211803c9a0008403561020710103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 149777787 1250 149776537 149776547
    0x41e20090d140a08090f011701061b0506010e161b0803040204060918060608010c0c0803040212030f070507050d150c0513030303060302090c040608010b03070306050d200102030415 79
    0x30540c010380882c0780308101240d00c10f00c0c1c042e6040089520420108140c1da050a00e00441480c030174003400c11002005400c00f50b00714100d8148074000800c074461041d2895a080500400b0070503820909440700c0b5030b1101d071111032141701504c0d555004002401080f01c1d40303200c0c0307031036580c00841c1003440c0d0400e412645821130325400c00b40050b45d00030750b50300c80003910100700e2281440f0b4903940001c4010920260400800710780807580590301e1a418180221001035101d034424507100ea00500c5a0b0300e94440340042003064400c562610110304c40060354900b40c0c000c000c0501142c40c0314034101c078401a203440c14001140304180c0014001c0c41c1c0442000d08aa009401c4030030740c80c21500d0030b24100140302d40000d55481043d03200760301003640c9060034025410300c541c1d07040d031010076090013510b05854544000c19610341445503051000b0003002140040b4826000080100710007031030481c610b1881d0038807074440414a404c5030890b45d07048550480b25400801681d0840d041c80400034100300d1072070f1050320 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 149779037 1250 149777787 149777809
    0x8040201030b100f090911040e1012150b0d030f03020706151401080c030f0705070c0e0c091003050c0f071a0901090b0f0112110609041e2009 62
    0x814075445450102c0300e074850001100c11142c0f075966080e135200c04004050603001d4070b50408072186003400184550007401c03000711070442d40149a611015502e01200c880e032030106411601002088140410a0082001c012181c1e000031200810042108200700710500c0c013803c80080100b84944107251406010782d000e80480c500403400411032030810300b5582c04503d9540c00c0740450031021840310102e540d00c4402030b40c2c0403494400c0301d4994204460084030404004124000300b020004181c4104603007004040004c1644140170b031420f003080210406603412240150b4064451888030070b00f1144a03002e00c9003c0c1c03843c241c04500e498113228030454590700024040e6540039001c0c42e0b08a030003021058070762140c020a8000034164a0600d0300700c040103405040640e482c4403020041c041031944018074040941d1001780021280200b1000c2241c1d4010000030f50341c8035240000350321802551054641201640c55000c000e49041202c030045601749101007104510700074403000d095800c182030440303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 149780287 1250 149779037 149779039
    0x5010c03030525021b01050c0604020909030403051204170a020901050402180a030b07020c0109030b0718080d11060709030308010b0307052502190503061501030e030703020f1e0607080402 82
    0x11048242021502c584000030481c2070b8010b80c0455110014005c01c41d080c40482c2009190551a002c1c0300842aa502c41c2c01400103031054408101080c25610208110381c0116448400d07100307854001e82c000e20141d04507200b01c10204800d0302e04066070120100e0483e0355641e000305034000e0740e400c0c1002d00000703411403560106400701c0c085284240b84c2d114003800d0003c2d40700b80d140c00b4483c5003d84001307007088000501141442800407090000408104a890f40940c95150180241c1c48c0039030b80b40c02400700c0341d00481040c0600302402c1221070b172041540f07514420b41c0e02143d00079110f100080b50b111119201c0a00041c0c0740d00d0050010405007001160451098030f0510300348154180041c0340e80ba140101c08080b41c5500c85805d0450801c0340c07050204c02c151284c00d100451a06021a88800f030081030b107141f00313020108030210f580c0254480000954079001f00c0391502030700d103000ba54407075180c06064510f1046a80880304048042c1c403980c00607084c007000d451140c50b8540e050310960b001400072 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 149781537 1250 149780287 149780311
    0x1515121e080c010e070f0906050607060b0f04060b070606060207060c1118190501050405040210030203092805060a05010302060712210204140d20011407060608120405010c030305 78
    0x78244501d03003401303a10400022a805813590301c0c0340040d00d040c1403d85602041003241000e401700265907401c2d09450700755030080c202081940000000030101c076200001e90340d210b46440c4012926000060152603c04c0c8110410084c4603160300c4103aa070740c540d80c880c80c0b000509a019003000220300c00179000b20304c3c40280c1589990400c10800040109049511041c02003101c80c4a1020301c0980c02114010041900c0400c45c07420a41c010943c01d1149900141c1815000400300345050f0703003041188254204101e0038030031407040803000980e40100c494103803214814500401c100107420300c103041c101d80d8020150f9150018650302c1940d010904049482408501400c041d0180994200821411812a00140d6a509050040c240300e618988818020440f0000c14000107515142800c1c41c651105c1800560b00b81040040324000150701004541903c0400e0040410015811010a075902c1009451045030300076210180c2e03008502c14180010802600700c000b1034000e40c00903070030800021701 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 149782787 1250 149781537 149781547
    0x60c1107170f030d021c0603050d08150315062404031b0b0309010b0a06030b0901090f02041707050a0501020a030f030c0e33070506160302071515121e08 67
    0x1600e0031500076043c03a503e03017900000c0c050714000700d03514411591042070f5030400c21141503440d01e55942c02031640030002d01c40d9003000300d11000070b1410381c03607840341008080707582d449142d081030050500d05842d014082c8402e00740f27611031a0300b01010807258203044180c16050a181d500e407540c1400d070600039002010301c0b840d00854142804c80045100d0030549001141d01108c2d6000c1c00f580181907442902050310b00043e0104940d070b801e815030b046442000022400c040083e8800c030091142d580a01a04400c04114055001020070a0411514215174000460b80d0383c00040e41c5589503030754001c000895000e1300d9145503029911001600e20700d0300e440342c400300b00000881d10211030b00d103225080c0400b900d9440c0c40c18100490702d00d509510713140c2c0070f402d00c0020b54132386648601c0504a900030b0b494142042004500c6035040e43c000d2600b01c540c4030132205040040c10020040640115800062190003007250500452907404141e400001010760325401103101d00449a0010111085281040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 149784037 1250 149782787 149782813
    0x6060d210804030215131205040807031a09070612020a17040b0a051807030803060310061d060f01050304032607090f120305070807030306030b070804060c110717 71
    0x14662500510380c84401240c1010706000c1d1030312007104445c4070000341c00010011031a0401210812803070340408500c011882810b415212401035401c01c3c0740c1d83c82120f20010034040b014610904184034604080c943da156000c4080d158110b034003441012481168840c0042c00d080d500610001040d49801120f900070100c0d4958501c906441c01c2d12030110303950620144011920a141d0400300d6081440b52010000000315110b448910004c5c162841c04400035100d9141401141c01c0c2c484d0480b000c200043d1245240d0108030800500c0f031640500c0d801c0010040d0030404004144108161281030035955503a5041350820f08959000c4000c0c4843c1ea4071200c0410200e1400b8000c1d14180c451045a0b400c01d03035003503c4c002141d0b00031910086007030021b90200340c1013004c0b95140c5400800442e90b503901810103402a04460388000c016612000c108140c083d4840000341c0a10321894082c401400d000c24101d40f40c121000c5035500503000300f00e040007142002011058081469402d452012568007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 149785287 1250 149784037 149784083
    0x151a040923030d0f0906150608071808010e0102220b0d1109040e010f11160803180d081005091b091c060b1005040b0a0e0a120507091d06060d 62
    0x8042413941540314108141084100d0084952140c0509441c440c22850204002c02c000070142c004020711903815041046051f80848080c041c104c00e0b80240000260000302c18000e51102c102c00041c03550a0a4018006090b00940c0d000c031400c0c45586410841020300c01d4008001c0e04003660840102005180c000b61502d0050305000d4101d2400040c3c0841644059419100c2081507900c1100040012030090444010203404468100c6203c42d03c1c0c1c0e41d0784400084020100c80659200e00c991030b074900349594020040c1d0312500940d84030441c0d40d96180180a032411080d1000041c98950001c01f4118481b80030107012898002440c0d00401015841d51703500f01c02444100342d91858945024a005007003002480c00f03200c10900e001440d00d8034000c40040d1078000c103025001000102c07468491346d030384d07030090180140c0345292000c10000c1c803a01d891681c80a2520404007000d041468051120407044550040743da54080903203695a100810040b0039000d510046500b054a900700300b03941d0b5001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 149786537 1250 149785287 149785301
    0x61d010c020d1a10030f0f14151b0c1902150c03070501060e061c02010c0b0108060a0b0f10030207080f030705041703030103120509030703151a040923030d 68
    0x14040c1140c050200b68200810075400074402e544c10f15200004000043c038007040c0c0d001c115082803840040207854035200074240745511049495109641c281440c1d101e103100303c21302071200500700390070041c49991303080c0050280c1e421050740ca030004000c4001c0c40141c00000a41079100420a0039264100341140800b07800c01150100654804a030300c0080110911441014104045005800d407a000002980c046002032900c2200d8400c040c006085900032600c0da4045a03011030741c61a03035030311684040d82d2850203c0303209090790b08050101c3c2060910842503805000050162a074001440205034007940c03004400b1180c403001048080c9039018110003445c01240b543e0b039099541c5203029042041001c0505104043c0c2c0c04c10001080064401a040e000c6c200030b80c2030450321000d14000090131710150b540702034104e140ca5901c4280e60b0505512200712184514012041813404038107200c202d03050340ca0010b02d581220310100c0c4250904a01803400c00545a084a28114082d8151b506441342 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 149787787 1250 149786537 149786543
    0xc030f0606020c01090e1003080c010e06070c0201020114040c060302160210050a090902040e06040e03090315011a03150f1507050c0418120807090909050c090907061d010c020d 77
    0x82110f070300c152907034000264001090b10a450b03440508011004041401c81403100405000c00003401950450302134000300c0c410341c480d1068445925203808080c1800e05014001c84c0154030342405030010250481c401030145811500341c90001f410000190b00a51101b0340c1c0384407000c00501c2030300c0141d0b0f404810078004c003a280d64080e01c9045c025400fa1070559203810241d4858014007050014080c220300659204204940103d0b6185a901840782140308000066401d40280c01d24421a4441807000c40d049400c40d01d0816148010303582a000c5501068034810700c9510f02444100c214500005406007500e40200b81031104181c4a4a416190b17003c82010bc501c0d4201c850300120a02d403c1c42141e91030b241102400c1d0824000b9651410300a800c510884207020214011508003440b03100341502400d0344190400500005040c6940e45a10031800144103032810320004400c1c280214000b4222801c5807100341c012111603051810200007905c0711810052080740c50400f42e0b90b01022070810b280 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 149789037 1250 149787787 149787793
    0x61305070e0f0d14160e0c09061c050a1a15120709080a0302010c091208161b090605121603080904091e05070b03190b13110c0f06070504090c030f060602 67
    0x6204c202ca440d060403913012955142200040101e100860000c44404408c02c80d034455841d80c0c081c940490320906104520101807800b07082085020141c5c1c4201d4198030010031850707840c49180100400f0740d480403103441c8041e00c2441159919456451502e1f00611541411b81009488000c07103403521040e0b8078240c0060b912440c1c41c0e2200c0350450981c2020b04104420540c01d10929220300d1254840c0d044070002c2c1c3c0b0b91801c0b07003100748400030b026042101d03600341481180c20790380c3c2814006002c05001e40b610030045036405205940001981ca11102d1080741d807034244d1803035501c4005072078000e446500e402a803955486800503040c14052144000d07020f60358039120086003029071610206800140001c401041481408010003042110810b07808001080b4115010081540600d9400c003007005c5609100611a24491190141c00d2000c0d000c8210b810100484e0350003030365150159550400300d40208020300c06a0030f01c1d04489140d5105003000f26600100340310400403585558401001a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 149790287 1250 149789037 149789053
    0x30405060711070b03010b09040f0c0e040501170604150209060304030305180f030912010b09010b0901080c0711040209010e0909030405030d0306050310090317010b03061305070e0f0d14 81
    0x1500720040081c0da40d402d070014070b120380c00c1100c283c9013840b060045500d2040c000c28211495a5280c0003924008402501440540c6603c0c5010388524800894544144c1c1454000b0400000e88200c09191260312801000705440d543c4403c1c98141a84040e00001d42d020003120600c0c1e2150001540610300ca80c1d000685440c09288140f9914008480c0400541001450f248259000001da8005103030495120b034694910790052801040c3d114020794100040000000c0c49808a030040c2c17401140a80381c40c040382d502c00c030308010a131191b100e00034210004c80c810404a81001e6025002155060502d0064554041d000481c5032000716400d6030158000182070015003010302000010182c282014840c15083c840001c0c2c40d84900c803441007500d95200707080d800f814800c20401a125440e103009035034658440c1116116644100c4283d4003916007461690802d05191194a20480203944d0345812030100a08008005403001803c5612180400070030700840d40440c0308200f69011a00140110 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 149791537 1250 149790287 149790301
    0x1403061b0c03130b09040b0102030c0a0308090f0109050d09050a030b04060b27060102010e0a020a14012f12042909120318030d05030a02070503041203030b040b0301060614031b03040506 81
    0x7d15a400c1040d811504284440401444000b40034200e0300e0b8541003a8950350ba90f200540e20b000c03400c116501640d801c0c00565030501c280415012174001c5e045e43e44c203036034a8503502800b450407d14407004052664200008021815075808896400c1000b42003843e9258402c080c8000340b40380708500001c002403030040c1300b01d660b0240710b201003081000340a84400701040c3c0001e0900705051050041c0400741030030090150384103d040e01c84c3c1480446403205402512986983c10082d05070071030280b4072030550320390309030150403080e202100c41c840500046500c00b8034000e4400410219208420780d0240a10030702c81e40c3d07665101100450740c01c011500c4844010b20004030100c4408000c0c040e400c10a1941000390b07000044039400450040003595510a51070554038610441c3d220b1801301d0b0240c0c040104140d8141c000c84101081241d040c4002c220400400d42260405c1c801c60003c141c009000001e0f03229001c01550b44031010030022100c1c00c20340380e691195030f80100d0f000c0394160000000c100f41 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 149792787 1250 149791537 149791541
    0xa091409010f1a0403080403050c09071e08150303160c06081009020c01110a020d0e1c0b0709050d2a08031b0708030714070608090a06180515011403061b0c03130b0904 73
    0x110486030f28000dc25a07102c0f010300c40c010351840300010104084d140010782000b0608141c84074095025040700c0c1c0e034100c4901015903141b4824012550044a80c0c03000901c1c0b03108896550042080d190b40121032450016944000d5004506800c6a5500c82003154002038040000c0e20b00700c503698016241c051403000e0028041100c0d0190148a40444050b4040c0d4480f0a0351080c0644c0d0f0006003559181c40e400420303510b0880300e40c80300d54040031110b24401080040762410115501c60010780c003410380c0d002013480b612085800366542a600900030ba56004401005100d0603854040a9580790303502d81040c7c505681c0400c2d0309a500950441064041e140100500e00051541d0326040d689030407e885a5502c1b040b540102805844d11030074070007204000c91410f90b03401d40e80007049440303034101d019038040303000f80900c10404000701c40490368040d42800f10728148a090000d810820152810b0356003100754204245091642c4010720800c01c440043c641518098040b13804080c3d00e40312400d0402c07003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 149794037 1250 149792787 149792791
    0x3160f060201060b0f03011a0f0a050913090203060613090b10210507090906060b12070201061403061918050f0c0604060c260a091409010f1a0403080403050c09 70
    0x450704070405c94a003900d15110140c078103550180c80c030746c04084100000d076000c0340500f401c0380c15074030000139940103559000401040344000580e10b28a0700c0c40e003115604100c03507a00308040d415030041c41c00203205181c1800f240c00703c0d0b1001c0d01c0000f41c9050030380b40d265081004490001454182400600240b0a85403000ca41b2000b80c1c4c3c1c040e6083c0101e41e48042c7c44400500c107844115488200250400034990040c4018010035000c83d07456105030a0090202101526100d0240d480c00c00c01042c0800c8190740d904c42e06202800500c41134a41e0781405502502c03800360410302a035942c0b0740e03d583e840c498004590b12802200140304242c404400e6a04091350003c00314400c21040204100c0aa081883e2500302c87d00021540d5a80e0000081081c00e001c4985000350f000100080c1c0281294100c0c03421410740350484880c49400d03003000244442c02e0400c1c080d0441107090b080c4100103803401e2044489030107a01210045c01c0960701d5861000507042a00119100d403c18080c951160401410240d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 149795287 1250 149794037 149794049
    0x609010203192712030b0411040302150d09030203040e0c03010f120218010f08101109100c0c030b150d080405010c020607021804030f0509030d0c0203160f06020106 72
    0x1861410b01c010070442d00007042c01c952141c5602c40c440303d1001c0910300903440144003401d8000c103036203e442c58035110304100c2e01c0040300864039000580003d800c15102d0a00c03000200300b001e600e42801c2d9002c1005954001d10844903202c400c01a400041c9240c0c01a030b60810301c41d800442d2a981442a0f81e042030a008282220040c0300340010411028069a0781d411a0103401110072180100c0c00031420880c0d06001c6000c0c1040b0440001411000541c04d0701c04940c01c60060304c03820405032001905495044221044080003484480c00c2450805401c0c9d600c07c11a0800284a0b80d042d500d107800310703406034402d84480c201001006a121844116201d4480b000c4460140c68509991210400d000c0d0b07009250421418100c1030701151102011101c40f0b0350010841010180c201c00d600c980310404940c120000340350043c800d00460b00a40c2134410001005000e82102651050304495905040c1c00590740b600c958440030000308072540303c00020b03140c188502444c2c117007070040107402d48500c0d601c45 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 149796537 1250 149795287 149795291
    0x3050f0a030e100c12180509130201050c1908070c060c020a090e031e0c070e0f190615021c0504030c090509010e1c09060e0d140313030b0405060901 65
    0x19400107a8040c40c1c165824508840303200b04840c01030401c540f1825207101c01882440c0c1c0c0703c205e400d0039805c016110710b41c01004c82c180c81e001d0740b00d205000500e036094403030b0080d81c05007110100044d070281000d840c1d107440c0901119000401120307954110402c560b01a00d490340002078039000d00411a04080181a507400c0c4000f201c02c05a020441e0316101e80701e0172140c0f650b6140404212481841220020001140c0e454800c80d80c4031a20300980d0f0002070f41c0f0301e09102d01311001501c0d04424862503c6070031a805002c9031039944503403041c0b00e0440881094500340da1950082905504140c0e442c50ba074100741c0c01006501c0b01203460310f010000c2c1e24110400c0c44001c1c401080043ca20100820a0310007840e004945501c80b03480050141518601e2500c448c05540880344140000d00b00c81c1603002e14a50b00c20241542d51a029203144102000207034001c00310300c20314008500e1000c410580a821441121b141080d019004045c10019800846240400c4030074041800030400009030005101002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 149797787 1250 149796537 149796553
    0x90a1203050615040b0d151a030f100513020c0a0606060e09090c0607020f180702100c0f09140f040f061d0c12090a0501050103030e0907020106061d040e0d080103050f 73
    0xf50740c2c041c081d101d07617020020740341c0001d550352100c5801881f008207070111024403800038104031030103203801c121500e5070414a4040010304000742c42d00554100c42020b00807007503480d0414000070107076120303044071700035441080d41840000d0320a200d454010702c2c80380d5031041040c0358801045070100000d01120100e90248000c030560317030b0b215070468903000e0b4112a03454040b1542001301e910100e2030003045446c0d41c2c4910070001000c0d00031500622142d0136820400081c682c03002c0542d40720501190040006001990500c106010b81a401d160140014182c03e0701c40c0900f0300142c01d880b015500600078585510041006408074209402a428406601c025070b181c1401149040d0150058a040706c0500c0760100c0c60034031081c000005c0040d0442d0003030210b036071241006800e01e13050320030040c01447c00c03600160300c6030703c1842042c080c0d8110341d8540c1700d640310b90f003e82c05204243c19211a442a0303203c0700405600743c01c1007584011203a03929442e44561550a2080c00c10102d82016483d640104136 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 149799037 1250 149797787 149797799
    0x301180b090f07180509070305060a080114040f080d1d0d030204051507150507020321040f06020d0209040612030e090114010318050f070302090105010c0515090a120305061504 77
    0xc080b552010103031400002c00e200904490603201c1090740607541003000c000070f121405a00d600001e10821007641c40311001e5940d0b15650b404c9824041c0640c007003950b000041400100c0e200340159900b400ba070001350030300685c40b04104c2250901402610003098800d030180320103000740509102c1c109641001c60500c1d10380f0011410b609401c1e00703942e00705000014444100807043c403030b100c41400040c0040209d1b01d00640083c4d5079620801691102038114a8a980040c8610031810b210303a9100d9600c04031204299501c0010350403121500b4481502800241e503a41c84504c260310050520708400d02c00c0d0034190801804d140049400180500443c10060004030160341c114010b2200a18000800c0c51305074903140c5c128031916400a145010b21100b500c5211000680f00094900032900c00c11a41d03603450054075141e4000350028590382050481d0820022050742444d803201a040549500d60701d203075209101c002041017013a000c603603600107001c0f55007044200ca0100c0c45240703900500c0c1508101d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 149800287 1250 149799037 149799061
    0x10c0215150a1208031e27251d130b04020109440c040b0604080d050c010507140301210503030a0b01110c10050f0c030301180b09 57
    0x20480d596020621094410a4454100a00081c101072591045400f66442d0040d501c2c3d0090710b81058540d404543c1507400707440d00c0e40f100c4c0110728200400b0310101c4030b402007030350340b01c0b01704060030303071801802d0082c00000b10030b404132405a040d00c47c0d0b6292150510800c00d0300c0043d180700081105004100b0448440f140803680302c54640c0003000c14003599154401291110099040f10800b42c20050001480d8880c0e0b4505089a5404081c848050002000c87c4440e0b036500c0801e28040d9031001c05000e5140c20158030803500080c01400261410752103110781071801234040f200340d001440000c0c0c40c5c0140746083c0310700354015040d85401d018808a111280d04180018003800d51451031402a50f011042c012068a03d50356000094a07164540b0740300320b070000e015015410b404181880c0d103c1d0b00041000c41c8854600c2c0340200022031102c02d100049070300ea0007a4100700d4014008020151f407035203007017028500800c81c0480000894081c503a044003a03840130178031a03001d10130800030320030008000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 149801537 1250 149800287 149800291
    0x20708011b14190c060c020604031b150c0203090901150815010c0f0804050f09060d030e190e0103020f0405040c0605030a09080d05010e010b04030305070206032d0603010c0215 77
    0x10b00e4030980003007141c181c0110600c244490030150602e050300c49801181c100d0440302c0700360300402c2c0801450801c02c4090781c6489007190000c00003201000b0054220351185210742d4010301420010359940304c140881000c0710010300440c005a8404641c8031514548944088c1c0035240a8455001d04002004064a6039170b004c0e04036200b0302c4291450780001d03481880d0100442d0307081041c0600b450814200480b156005000b0741c1c1c015400c40715040240d081c0b50040600408003d4148046c4085c141c41c121841d090511840341d000c180c0031515840036030325100400141051000d8948154910b20400c410356003008200c40c065410001040301042c80c4541c0d82c8202c03030140c1041ca1362992202160001042c1c0c1040080c071200c00800d10b04100c00c059072215060f104d095400180701c1e600c4804202440c02941f000500160082101000605100c0c0103150040d1541c1c0000303400c3d1801010720280c0391564105040e041032210100b107220b2409008100c14400700e800a81842001024006800400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 149802787 1250 149801537 149801591
    0x307080703180c03060c0e0105040b09011704060510060e09070c02011b030302040512070b0f0706020904020703020f1204080a0308090f01060b07151401030b09010b030d0201090302070801 82
    0x20110008100300d019402c10810098040b19924070b082440c50460400343d420300060b28031070b15280c101c0300b015018024010070908141c4940c0c0c2010700e40038400e2402c0d807001c60302c3d80c108103904526a101d02103000300346003e1032080f80c002c201c5282078048035903103446d41d60104040107411241201c1c141c48000744030390440c074070340350900c101c02d01400181d030200c00c1003104c09112608817103100300741a4940c4c050010784504584250000d00d40780c0e81c0a68805480c01048102142000502c40c00d001940c001c082e0240b20b01c0c005802c4c060080d0009003240c025280590168000103190a1020000d00510712100090f003020781c2402d003001501c03139540c64019401010700001c2004610b21000c200102140314203c003000b4450141ca5028100f00c5400803481191502c05105281d00040700500440418020810343e50115a1954481c94003501d80a4000700c1175560740c11044603d514140042050482541c00128000d01c49140003454201198031400c6c059140090003421441225848410040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 149804037 1250 149802787 149802797
    0x30c0813110d0b191506090e100b0d05060f01030e0d0c06020903030403030f1101060b0d050612011b09050609060f0702060d0606180803033115050f09070b0307 70
    0x1580c60101d003141c42d0b54040a09801c60748801c2000c00c103540415840340c041d1002082c055858444e81d01c0c40c011030320380100d001080741a13900b8044905903c01f0954050155107844181700e81c1c03044216003580c40307185589550b079141c1041100e242040420240303604001c0c6070410901d4003410307a0070386130200b12054200704505d6500303100a104c881d030140c58809200400707495459980e4034014106505801d4418041000d0f0364050003a80e506105101c1201c0a1204803850140d41004600042c1030007001207501680000d54051030308424812585c1c400b10000c05800c06211043e00500283e5280c1e000034402c00c0304203c0e4030040e0312040107948862840b080d56588030807541c0700090b600d01604041c252901e20349440010303059407020340e0824502e001cada20b0700505038845100d19100d1004480c000c2c500e891440d42c00b004180d10702410505404083c50000300c0660301d036612051030a8091089450741d40794000c5c003243c2c105503500180c00c04502c4009088040c07804c032494000e40001409101404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 149805287 1250 149804037 149804063
    0xa21020106050a0e07030c0c080a1803060504030207300209060a1206060306050c07020f09090f1204030c0f060815030109080c0105090115060c061d0319030c0813 71
    0x24000d40046010348002419044415210070a41e4a403000c120703101800a4108003c14500d80d004045030403115030000c0016143c03c004034019150f0f2603074002000003101f4951800070100c0d01d40e01c81e403402148280c3c00f6080c41c1e45001d00f2800309600d80300900020880c0c401e09807014001480301034144030390655460005956100000d0b440924a612220240b01e0030403040080002513031000d41682c1c1300300750421054603480840803160248039802134010711407555805083c581003448540c09814141280c3c02c2400c807440311030401c3c1003031802d0042408041000c0c000c214008035010040e00b0114032110100340303056170040241c40e002e05100708600c2c8045000d800d5460a42000c41c3c055081110182e4035580100c0080c0289022166456554a0b058510341441803404040c0c080b1001987e4100011800d0340707808008010450310a000c40321450102c882000090010f004451800c00c032000c010500702001805590040c20248104500320082040030301d40a0007480c0750a820116080c548 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 149806537 1250 149805287 149805353
    0x3050901060503150f070305040b0f062b050606040509030a110313030309140d020108010501110102070b040c030201120509030a03020705010e07030c1a030609040209250504030b090a 80
    0x5016941006030075010308100948074266585086004240010b240d6140c0d580d0106e04074201c41e0306440c01403000f908400401d0394601d4409219410050081c10000780c40c11500000d030850005078034095501440015400c1403240a011980d84184140c40a00c507904d0405203441c0c0b00d00c1005040c2050200c0540b1416030148100291440108540d5520503842d80b40c0c14040c1c00101184501d541000070325403200301d40c0c1025180528180d9040c1c640d071500f07074207220055960900364200a00d1075076080c45002c001c0b8080c0048140200d0203851091a403034118000145900c0501c1024640302e4140003c0c040005070010454030403188515005844960901e09140544202903c441480c400c1320800710074025002e80c107100300c0c0d00c00d621034100401c12500382181d60004036070055100010500140c0903050090301542c0c0304004085098001c65140c3e9905001c0784281c2c40003002038004a07090080203450701c007032342c0c1181a42d8010b202d20f88455546500c2d0744541c1c4589016114440b8514800c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 149807787 1250 149806537 149806541
    0x30b07091815060c050601030b060f060315010807020304030c150c080a02010b01030e01060f05060c0f03040305100f0b0f1003020904090614010f0605041203091805100501020705060a03050901 84
    0x6001c0c4459403010032020007110001902568210000d0780c00081000252540110899004c084d03200000d0b100ca40e11350345400048003002040780303400a000001a40a542c1d4042c001c40c4518114000340420000d030b640010221100148150b055520821060010600100d0900300308c600074120500480380b404011101c00d42d0440c0c0060a007a00070a8110316a40c0640013034401b04420f98041196041380c4194a0aa51285c03140300c100340380d801c0c0c0030b200a00300304d80107040911800b002c0b40d10b8800f04100c894996880755000382c801c0d0300200d420080c00340090184903145e2041240a0044008010005244d50861294244108146c0b0102001c2902075016640500700042040005098606006000d881200e860700b4400044d507001003402070a0f101c07020180c07030306940e8250503e8100544a008c03d16990001c0c2c05100d0481000130712050615644040c0080d003400114180c01d1030140e07074401d04181d400003815500803032400c2c00207454420554403404803910303001c189620b6144003e80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 149809037 1250 149807787 149807789
    0x50118050a29090f060c0a0e01180506070308040317010605090f2e03140c0304021207050603150f03340315151703070f0203010216110307060c020a030b0709 69
    0x3582040b50381045100e42c0c0120768a40000410016240305a8030210015064454104280b0105035010000c1034076500c14401c441c041404620440e05050301c41d8002640b5400c19002140060030348000c1204042c0c0c07040020707078044440d00d5010b030340d5410248068000d00402c0742d244e01484250200c8035455035084110b00c142a00070702011030714041d004425400c0c00c07001c190000440e0400b540120080d0040b4107023481030081c40c003220f0844d143c5508000c040301120701d0761189032180d4603000c101d40d52040021402a400f40c1c0d54184514907801c10b00450012050348a841b9409c541c2c000190603241405180d0307425824040c0314240680c0801200382d00366070b6040900391980f560a00c8c1c1490a0980c0005c1c940c90000d8030b400302e025521040e01303c2409000b0b5440c2910b0b0130911500c000175403400b6100f1001c1744014005800c01c25540b00040d14445450000e4801e03801c1203400700610b040911012011707110131318000f40441c146e03402248074140b541c407004080404080010b21002d00c5014100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 149810287 1250 149809037 149809103
    0x504060e240c0c01110d0804080d0e0304170303150405130b0901020a1107060c0b0a0e160e010b130b0703030204050907050909010f030537060603050118050a 69
    0x10000318180180291550884800c0820740d2050f0340c01400158014042c03580248584402060744240d044812a10650050011a801c520034000000405040c2c02004d050391074644c011074031685001e001480b044401c1031642201d03041041404810240e503424258080002e59020600c2d848449020703024131200d00303003c1d003412034400c280410001c0640041019800c95501d0300c03d885580076101c0d440f0070041c031480c0046044200740400041c0030b1211160b00070400348000401000701e1008506042c225215070501e466210410300a06440c08900c5015200c2c020b4100e0401c04c0b01244410b0040d410300540c041030b0404a689000c041c4203804440180002a054090505000d90090704036004022898480c086a4001040710b5120607031180484c1d801000400c24100c0c42503090180c161030203803025602a14510808507140a0101d000806100e4440065102e180d420305a0842d122400030651201c08000e08402051000800c1030545402c0038002807913032000c01c001d441003080500301e5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 149811537 1250 149810287 149810329
    0x6020d030b13090b010e0a0209091602030d05040305120c030601091206060503150405063103030b060309030a1202030c091005130b1801030b060a0e010207050310021306020d0504060e 80
    0x3901c00c04c10307134411450413104c003a0140d800544172801c00c3d0081c2d00074550200d1b00702c00080e002414002030034403480b014100a0050341d18001c03038044400300ba0742c0c003101d054000c0395000a843c800c0174266403180e60301c40000c1041d9070441c1400f00c002040790009104180440c119175840704280110342d0b2100c270007440002e003101c0d000240401641a9400103d038107a50300d0181c0c0c400200360003a404054405043c50b842c00ca171240b90418881070307101070040ca080e000c050351011080c00e00d41710840158062300e00000203644a40000344020300c850700300f40000aa190040c018030545410b80c409851020204170f0317101000d010f4890301120140605038018028010412000601c9424171000741103050182e20310740c1c0458902401581907501d507030341d07480d00b005040140040b0184100441542468144161103611355620b000900d031143c05410602c010b64001590842c3d0049090810f004002d03600141c41c449608071000703042ba0056229910a000106001411996440f0000e1550b0a144012 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 149812787 1250 149811537 149811551
    0x3110f060f0d0912081302040207060f050c0d06080a11040509031e0a110d0e041d1c200601060503100902070f15060b041a07080703170106080106020d030b13 69
    0x401c501803d0b0b59901615400e190140044009104103807440c0704201c80000714024040903402d20000350701018050b2100760340c1d056410103c001030b000d080c0c041c030070740054507485e1907200300d4920481d04168021802e9a1000b012540061901240d26051510448001038117a555081580c15031143c900007403c1014200c0c00d40c448003c1d82800740c8510440c40d52100f00980119007982d640e850a9401e40000c030700f200616000900d0582c004c0803d800100301d0300740500700c2c4140c500f4980359490410030600c84814000d00540d076401085c8901c00000710780c0544a00c12011030703860b10f8240602401c030810000200080c4500c0100c00307141c0041600704c108558864a03418110303c04480454100c0d5010704140f01e10f92081d0302c0e40203c8040d0ba07071840b0030a00d03191070069404014600c001d0259440d050a00895010a00d00300c00f515040c0d00035180c580f01c9158107503c249040da01608120140032a24005020940d07002462002103081405c0005801c1c120700c0c0007407100d102a410b101d40e0142840c0d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 149814037 1250 149812787 149812807
    0x30201080a0f09020a0b2d070f050102210109050604091e050a082b02030c1c091b06080702060f0f060f10030606030b030d0e130e0a0b1501030603110f060f 68
    0x4020007c20071103201c11404045010142d110b040d000c04800c14014070207000b00008104801d41c030703100c2d00348039a00052400403c034102802002800104207000d509401c010020359881d401150390014003201e042202020030364400301d811703410341e25609000d41c8400b88101002010801e003145650030925041d01d9090340600418020015079003020748036000396000701002114001e880c000e00c0c000074181d0400c11baa90144040c2050424060106c64607004e441c8007140c4d80b0340054041c0c3c0f20005000c280300340bd01101500c1600080c081c3c20071584a0003c00400300c03001c000c02c54125100040c482d202c1d4858030002107001c1c0000050581c003001004504901c150550701500450310f880d2000d0010301d134401c040603111502c2100ca00042000403550f4001c500d003d060040102c07450002c00100803090090345480c0c1806500226050003804040c00180380ca1000e01c1e00320180309207420300070b00e0705680d6541101d04600b4101d44c050982082518180e40d1813109035180151100351139500e0302000307a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 149815287 1250 149814037 149814059
    0x408030304080a12140c0708091011070b0304020105090d030507060e0303160503060603180f07030f0303050a09020f0603060d2117010f06050a03090f0f150204030201080a0f09020a 79
    0x603e8040407504118040801122074007400041420480903044169150940d40a09500c132500071030305a070080080310311590729800c94070140e01450f600c842d0f1100b41402c150340340150a80180a2440c014800c01c00140e07400400c85240401c20307554200041101c0c41c0035a07041c00703184402400203081c4912002c42d550008060352250602a414610302080071205548034070055400c503030022010000204403050341070001402500744e104031007244811601260408810782c00442d5210442d00b084000d00d54140a290380258026078200304e05921079000400400c15810010f00901003c80020003aa4444030744401e465000203c080310038544100000c1c000401c040c40360b0100b440c0d2224082d0710580c1190341030580c1d45400c3d42409490409005a540d42c202c001007004164550080200007165604a214500c1c403640d005d0b6150103903860507094001c045c0718010b4490344140010030150ba80b002c4040d402042e12440020000c03c4410400060581f050002c1e401008420000480b04845 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 149816537 1250 149815287 149815297
    0x50d0209030d080907060f0219051e0d020106140d120e12030301030b010b070b01030609170408060f0105040c02070b030414121905070c06051c0f0605010e0a060903080f040803030408 80
    0x201707554203280c4560090341e03540400d04c0c004005030f000b1a000c40c1c4001d0542e01510b5020b004a0480b030010400030300820b00d08a0741c0b1950025031700085180c041542d02400741c10080c000d01c400300d41b200106500424001031025401038160007004a10388078084c050005d564001c80050b06d040305015640d1480d5a582e03100388812540903208400000365001040182c6d0000c3e540200c00000907482c50b00c5110142c07821030020307552010b01d00108100400721400400040044002421191034004c3d0082c100141c140d1009004505101d01610b0b6140c3c0410240160fa0190a48649944607801c0c004192081a4002c0c0018440c1d080080c0030f001003900680881030b030040c3c0ea050942d103070400c11200c502440500515151111400340405805540600300e2811102c0b001804240d410389000c0031348400300c0c641e44c030036039a40c10144070f05c0d40d1012800f21002e03000d44100c280d40f451700100514000e238510004d818403102085c542208111841118018103584003103036104e040c141858400b079442 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 149817787 1250 149816537 149816551
    0xb030a1a04060b0a090f06170a060e16030b09190c0203070c0905041e020603070c05010b130b0a080313290c070e09160303030c09050d11040c1e050d0209030d08 70
    0x417214000541c60a11409a0146c40460b640c100001e200e50f0001904284041d007158448c90700c81d4004101d100841c3c610304d105110004c400301107042e01c164050219001c40305214014041042004140c22400d14038074bd2040b216500011084400e01c0200c3c21409031820040100210f81000111032046822160060340546505260035651444400e84048152002034010074240001404540100500f01200d1f00a00000c542c4114070b10024000400c500c8135241810781d07032075041c405c9050a1740c074035000c0c0000100451034031401d400d01585030b400c0c80c421130355498103a070500c07030031080110062886610ba011406491310060b2400c0c540341c0015003c0c045030071860340c0000ba1039403000070341c150740445c00b141c0200950741951001c40103008250b2008050264004000a583d2075030706080214a000d0044554905c030540d0400080e0341030041204100034055001620801d00c0e85610b060418aa04000340d840b25a4950b4102030b00424012030307414020341c00100702c000d801860751881181 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 149819037 1250 149817787 149817797
    0x1b0312030a0219110a030f0306030b0a0501031e020303040e15030318091e160509031e0d0e011d0a0f1e0503030309071802070f0302100609060b030a1a04060b0a 70
    0x440c800302c400032060a9130788501d60003001c104010a000744e000c980759000602d408140c0b191a9280c02e0003080c01591114081e698400042041c09003030103e44a02100c110f24a0807103082e02d400103a600c0c01240500b03e003014200010031034040448200501d6410094140da40300e5030000c00b0102c07003440003002503008071480c100007074402c201000c0c50950f4101001c10001c194a49040300c2e0000f60314910f84078107204080000d140a0b030b4081004110b59031043c42090124101c0d01101c50418009811400078000c251500000580e0040c1d4a40e117908403903000c04002180c143c00203000320b02741d6403120072401d031100b1011800300c80507808281b15509894030a03986a98a00038103a8900c01240c00b042c0941100009100d0780365801102c01c42210350102c0075003080103549548092804521049000d40e0040e60301c840c00c10f0300d40c01080018140800104042c501c0c01c100702000307101c01000c4400d290f03510ba00c014a10502000c0d1440308480140040160607242c0203a0f42c05540076842d420003040b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 149820143 1106 149819037 149819077
    0x82104091a060d09060b04091a07050d051008060708090c1018060e1203041a07030c050a0b09070e1909020d12090509060d02031b0312030a02 62
    0x10091100040d0489141c40d1107800c1794440440c5c6d5000d0341c02d04441c003000c00d520070344050701d03c2610307510400c20350386040040700d103445212108c0076028a4442840030011303c1985004c10780c1d51160031030740580c07500c0c1015100d0107812980354080e42c0c0702d9514801c0b242000c0e0101c0f010260300e800c00c922043c0ea003101e090313103659540d0031600000f0316142009600b07103010b0402145c1480450003851803c2d040c2040710700c15031890301c10090410b8000443c003003018802e905c0c1c17020345508032003500c1d000314881c500908120415502c1c01b006208030840031070804070354407049014001c41050064250401c0b858040605694942640d005440540c3d04001c07501249801e05c0c100c0382543c4030200d4609013000c1102620740a03244900841d441d00e41580140c40001d2181c2120a60355550452a000140080d20702800004074000948010040c00002c403459000b6280240110f50902d44407 = true := by decide +kernel

theorem cover : BRFrame.Cov 149640287 149820143 := by
  have h0 := BRFrame.cov_init 149640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 149640287 ≤ n) (h2 : n < 149820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
