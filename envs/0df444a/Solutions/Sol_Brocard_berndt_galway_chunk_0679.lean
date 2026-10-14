-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0679
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:05:57.86248+00:00
-- url     : https://prove2.me/submissions/39c9b1cf-b620-4873-a8fe-28278c50a40f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 121942446 ≤ n < 122122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 121943696 1250 121942446 121942459
    0x507061407030503062b03080604060807050d0602180a03050f2a01140c1510060801060503040f0303061a0a0809010504120c032109140f071401020c03010e061b0c0303040201030203040f02 82
    0x389030340654460701849d0306071000c00c4515111801261a02007602031a0780113403242002c000019902e038014a49200400d520984550b41c001c0060106841588184c1d83ca83c08242c22100007401442202c104030308036000b90398100c0781047c044000b6170b840110a814070800c8100b04074022000d0040b030341c85183e020107403800150a940000301c1e40006542c0282525403200002c100107000f20301450503036465480305130035580c3e2a50750b01120300c1c24280403030425441c2d01c00060840300040f020003e1450b0000d0310354413100c290400529000005045004c81c2c2c1c180030912010400c00d6115902d0300304640b505904450050500f5500b010700031404949007503102c4201c00d1280055031103d040d440c4100d00503207503d0250031125640b20750310f442e0203030560810a41005001940c1c541c031402d841040c0181c6031a6040040000d00316580018100fa20b0b412100800040c2c80c401c004030121400c000c0a02d50610346c4d5001440d23601c0c000140002d0605600201082c28008002c910750310f00c1c1c0d07008042d03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 121944946 1250 121943696 121943779
    0x120204060f08160b030906060d080c060708061003090c092007062a1202210406050f0f040308150409020d0c0806100317090607050604050706140703050306 68
    0x2e07551605041c2c500c100020b080c01000c070314202510103c074040c54070003004140c980c03100710402216801351402100c4140040001e080c02c014248030062190286480721381c581e241603414000241c4580584e00201440d061207400003c141c118480280d1321000400240c2c1e50054548201c0781c06011202041c1d68000700704042040019004661250038140106051074101c60110051121042145c40440c03501200c40041501944c06803058020190001e50b00e074130340c03034202059107900303940580b075807030302c9034200061003501c8484543c001400303207880111894580c83c000c1c5001d10141180700741a0304066121066540e603084040c1054000340004280d4a07140b510b8000c04c1180c1c03080003590302074180010089a904a0900c0490340c1004000300e111916813a50010350707204100e400e0740181c040c04800c0118500f00141446540301e800181041424100054102d203000460401c020300108503007000641d00a05480c4c01480680e8030500541c04560b1440302544003200190300080820324 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 121946196 1250 121944946 121944959
    0x50312030a091a130606090e0303060d150c030f060b04120f1b06120c2303040206070609080a0305090c10080613020a0e0906061603080411030604060204080f0106030b01120204060f 79
    0x300640c08905c159800c1090b65542d070a076906442c140c0368144540d0300144001607081c00c01549615006104050401440c04c0050400046482c141c01341c01c0026664201c0301c1154102b0b100e4000a0b2030b030072914509151820703105440c4080c42c0b400003081e01c5003d032140401c0040b20300510860140700c81000c1079842e1034003c000c0407007014528038a00c55041c2122811524060004010001079426100c2c11046010b500100c56501c040c00c12038004108106010204c1d1040c442c046c080c41c41480d0342c0b81c1e01c4d0307040180101a02c3c0040c1c548103207a04400041d0740503980700b0b200d0f0220081e6904110301036030f0f101c0380010740458841c00090101d07800007801c203405982c8030f4600f06001e80101c88040d480e031a0782c0240030384d0f1300807140310203245401c040920b000300740100303900c6a101c1d1190000b482d00c811070101080c00c110055508440746500494280300320340040c400c003c2900c0a5100802c481403441d1500b030000403043c03003040020a100d00d940c5c800c0d0b4036550442d50103800340140d00042580e9405 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 121947446 1250 121946196 121946221
    0x7020303070308240603010b0a020c0325081f0b040906050c041a03010e0c1b011a0405010504051b031302040203010e06010f020610090218040f060e01050312030a091a 73
    0x3c42d8481e0b0b03100d05400c400c00950001e4068a640c1300080c2c551402c0d0381c2411074204182d40b002c0b03004011b41c0701d031617640e01c000c2d07404004281f0000040c00b10010b01110b400c1c1101114030881e0061405500706080038044130709010100c1c01c0c3c1c070441100103c0c2004090001c1002040d810314080c210a0910007004076010035800200f086032141842e00c503103980000c2c0513000900080c010812451200404500b10581c00b2014040300ca01041204030201e200c0b001c0c4c5821542d00e05160f401603440e05100044078502485164010705080d1030500c400d28085680d00340c0212030000042c40050f010020400d20045c4000d1202c130310703902400440d5a1b58507102d24210381402191410b001070f4405906840c05440801c60300d0240d0112001c070329265040c07285032006034100607400c0c9503100d031203100d0500507580d43c000c01c0b101158040000881c1814124101c04030704c0140c102ca802584114807410250001d1402c5952083d00107000040032400c5141c102d0203400d03101c107440940c213546020301c080c000301710 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 121948696 1250 121947446 121947451
    0x813110402122d0f060f060720100509011121091c0f03080603150a0213050105090303040918050609030a020c01030603020a1203030906060f05150910050f07020303070308 75
    0x207075001448150f0f00300d808052016038918818298021402003034181201c0d0720001c0e00f060f001040710346036035a130002203001c035086403a05482c200a071406498100390715031501124031405940409041600d100040c085100d0310081504010314031005d03c2000f0004e01c800d91070705110350744a1486041c000004005a0068142d0500c03030360700f06c00e000d820031826980398074050754040b403811440711203074a0503500440018221034041c02403000126078903500d20a26481400300e044010b88a0040568850012035a900079038103006003005003801d280d41c00002c0c0c0e000c4070707101c030070218024031601c226000d84130801100500c02c8c4200020310644c02c0000c8060000440142c1c222004400c5900c01101520138074800a90040d0240d1401e112005084a8070811180641070204900c0c00030f90f1500c0032145c1c00e5114420b103900703840c818000b37440d0006031103210a502c1c5c072071036007800c40c3c45001850489000d8110814018001860f403140c10300030050701e03000d68005041e280c40d00c4450402400083c0c08 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 121949946 1250 121948696 121948711
    0x4060305060405060109170f0d080f1005130c0212070606080d1701090903020109050717150f010902070201091211090117070603020a0e03061f0b0a081311040212 71
    0x2004006501d0b42400e201e4144102016507903190500d2410b02000c2031181e80e061004068000c22108812524080110003202d040d9a0703120a40303842c00840c81070340722002500001c1d08000c40c07402041565282c1083c41c4042c1c84a81000a1070824150160b1414195201d541c2511001003883e03020f000155010b20125003441c0141c81c0c14003010740c0101c42509124049041d861403107001030004030115408804214820300000030000f805440b8242761080300e0f4480b00d282400c0710b0b5400b510714014410722021107600b03403000d0028100300300d4040c402401405074030101a40801c100c0150fa200e600b0000007028440545149418181803a001620555a0340d50042104078000505d1031101240d80c084c854003840604905401c2990480c00b0b940f20038111410058004a1054107507400d000090041a8030024101e0302031041900c001c07000b0701603101c02030040c4140003014000c0d8000781d61a07807008526920200300259480c1c02c0c90420004100c041d081031010482e061440c00300044280903442 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 121951196 1250 121949946 121949951
    0x30601033306090b071b17010507120e0a0209090c06041706100506120604060f080105041a0f0c0706020708030c0a0e0609010c030e0d0b130c09150302061305040c0302040603 76
    0x110381c0003c2d2110000d500c2180d01001c0d0800101002c218813103094001c0098a0419811300c980e961040607018042e41c9108030fa0341d544205005440d40c00266454500140000034040311034038500c1951980d90305000039000381c40f0705001862428080c003412911050007840d5a0300c85840e4100400b80b45512200e0161a10468012845041c1c20081c44001c460005009900e41195142d09440080d8042c154a0f001034403041e010910b050b500207080302511809000007034a10709418003005d003200d18440b80007002c0e800070903c8ae038008d00c2444e09500c280302c03050240e500c82140c50310310300900c101da5010300700250103c18031406c03e0f9154000d00c02c84a5566901032103005c1441085900e20400c00b85501048a654142d03002901415500200c07010041c040d2542d95034039103d074069944100c0d40010580c0c50315900d07008020250000002070540c58008000f80b58840c00c1c510304a594502010b44204004103054030040a0030200501803d4040e000f0711021006040c064060342182c059507010030b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 121952446 1250 121951196 121951199
    0x10501050105070c06030e0c0310091e0209070c0f050d1106060103050c1b190807021201140114031e0705040606020309030304030212240402091810020306010333 71
    0x622542c140e03281d4541003180c1d51285883c100f4140d006000e1039606807164003a080e08020955001e00c01d50b00c40c0d00c1c0d0b006012641c00312520f0802800c0d800100042020401c0044039009030b21507800d065404169070030b00c2540c41040742001d01c0060654507000700940300300d02048444a82c01818003022481920440d0684d407954401581564005c40e14001d4404062103004450a4458661031045481c413003070720300e603042d181400400d00704000d6050b1140d40380040c004086003002c0d683c0c0c00000c80110000c002c450090355a6108803001842030304442541c52024003050303034060254000388594240c0700316100c03d00c845c046844651510595200d94940f03c0c0026110307001004503080b1000050266103024110b038200301c10706840311242d0b1550f118204410040d485140203500f4003043d155281c00080c0b502d481084140d074401800025000b2301c148841d000500c000500400c0300c91120300140e1290341d6800100c1c0145030001c1c6801c035042005aa0a501d000c980ca01240c410001009060049 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 121953696 1250 121952446 121952449
    0x11030307020d060b060405060c010c08010b0c070911040b07060b011202120c0307021c0507200607230a0b150102010b031f1e0b0301050f1009050a0b06070804030501050105 75
    0x900500d4000780d0440404540480011a55408041804801084d1500342619036010540070f0f0002030030144669903c0f49440310712500425414014800504d03141d1510b0a0030340041d071100ba451042c1000725498001803104402d107001580c01070210200f4040c2c507200e0604110001d8000e1440850210b440400300c1034080000c0d00850706040d881404100c0c040d2501400500a540002c048070214010703100a0b0203203141c250403440541c1c0096039a1038440e44070341882e541c806902d003403c090500001c100441243c54170800d07900a02d8011000140c140a864100c00d20003030307402d500c003165000d00c14034542049810301c11940900340c90444031145005150040e0300b00c0f080340e144035505501000c21904150a40c1d526000000801d69020820380340035032440e60003040e02159441200c0e100d00f1440c0741800c003407003485d901c9010170300d01c080b0038140a803d04a80000c10300800070b8081c4c071800010201440b60b0003110101f40007909055940c1810309040b2800d400a000845255007004000a4903 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 121954946 1250 121953696 121953703
    0x12100501090f0b0306040f09210503010311040507030f2c060f0f0a0b0405010b07050d02160b0a140301090204051008061804230d0e01030e0a03030203040305160804031103 75
    0x40c0c1d045510b1802d4664202228030f0756640000b411564091303115006110342d42d0740c9005040c05544a506028207106240b5011020f11460840310003c00c1400e1004002250b403141c9604a131145c240c0e00007580c0c0c2c5a102c1c0171009090082880f07100d60341003100f071400c014109651640b107100429402664801d100281e1030721020151130105240684001042c120002c2684040d004541c4150004a0004000210f01591000d0b406520802400b0444000b0b01c00c081c0034040704c4845510103452281c0b0f000400f4610140c040c020003c11100103d41c0803c91380c080c850320100d07034000c02e003030035101d40e500c682000282d401801400d0140c1d0104440000c40d600030300303c903030265032300401050031040c140300c003603005100042007602c0381c4114541c0201c9000920360b01e84000c6403101c5c0a03040700703000110003410b804400c80d4a541018900a106200c6060105141d1259503151401583d60380329820210340038060707040c40c40044610780d5610300400854100500171240301d05c6c80810700c0107c1d01d080646 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 121956196 1250 121954946 121954949
    0x3010c080a0b0415030209180f010c1d090415110c0c01090f0e040b06150d090c05030a03051605070806131115030a0506130e060919050d03020d020d021210050109 71
    0x41d164140c0d05000510303040380392641c00200c0012210034000c0d00e01481d452708c00d0300f180407007050f552100709a40c4554041100345001c000c50111580210140340070400003000103002410b201c5a00c8801000b402540d0000034052a514a0040d128900303082c005454800702010343e408038680007c005901540000301400f10344074498510800e6032140c45042441500402d40c580c040c04000d00e481c03003c1c1c1c640340945000340203840002140c002500d450f1095429507001980f003903101407428000654420700302d4a100761020b40aa2402d4032520b4650b2400b5043d401c51610760151500300140e43c4030310850500a64040c00032003042551070340902041507a0701c1901c0c107103440d08100066251200d500000d4103d4405000d21044507080742581088450b048540b40594000f0024000c00413030810034160b00c0e181d04040001a15825035805030b995400a2001c01407540116103624082601e07815140c1c40100c143c815561140c50300020f4503112001c0b40c1c042010294414085800c0d4402c218100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 121957446 1250 121956196 121956221
    0x10519080d1202120f060a0f050a0b13080f06100e0c03010519050301020a05120a0e1f0608030a212007020604180c0219030e01030507020c03010c080a0b04 68
    0xc5002000c640c121030780d1101c2482d06924607002c001010411040b40c1c4076901c6002d0b10074800e20036007482c10421240c02069402018844a6140103105030390b00c621040048404140380f04d6071707a20701c0341c900c1481217141e03500c00c0200e401950307200c680f058070100d007032441010204a02c54842d03850f4200f44070103803c203039242440400e040c0010b00c4541048920080c2070480318001601da5a0303610300203422f980c401d01034240001c40108040340c110703081e0014140c00100e0105d0621017407800200309c50752508001c01242d00c4443c0c0390f400b0151035505500c40d0740a08031200a4960b606c50000015210019080300943d451699402142015a2621801d06012080407844005402c0159840e409420188059900500411001682005086140300c1384201c0c0c480c0440c004040c460081e0403d280c420305031440a10a0000ca40080d0b40801108c075401d500742800101929602d00491400084281c0d25415610f01805120000d4106070854406c00e0181c40601c001150041440283d440f06120384 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 121958696 1250 121957446 121957453
    0x106031e020c0c01050c010213091a0102010501080322090c030218180a020a020c03011b021507090302061308011a040518031206060f0403110301060501030e101109030a0b01051908 79
    0x99070f8961082005002202e1500005410001c2d0381600701918040c0e5844980f4607561040502050031000d00b007800d1811003400208440c0d03140c07500340ca0b224410001701d40030381ca110b1103c91100100032507120f005800101c20402c02100c07a5400903000394403014000b5000c450040300b00506e480e0041d001688044074104944850703d42480040103500948264029801448001422600c0912903c9000c8904d20f01f00c5201200c602c5010f0f042108015201201040b906c080041c411381007004081102e40c152150f90303580c50f6281c0d81907804043c54022112035400e00b000c030f403461b008110007203030a4441103908014a031130f407080745a6481508070710210207400602080e0980000031024a82c042c0300a00750760b1404420014074031240e4880d820403101e0312034101941109080922401d4090b000c2800d0402a9205032003605580f10000002400d6540d290039030900ca2050a0342a141101005021100e0f001c0c0c6500d004102d042003409410300800d203505150744514a2100c4800c01c444911024 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 121959946 1250 121958696 121958713
    0x1020c01030b1c0809090c0306011d040f05130b0c1603050c010e030301030515010807030c090e0c040216140105131b1d070305090d0905010c060f050106031e020c 71
    0x6402416910b801694000000d03114054124000800c110b085407003078030300b10741d640189400c000911101030080000000b007030041214603604851541c441c09080a0400b08418090000034050f00011000f0071240d82000b05200c00317116040b09000742070303102d100c0003000f50366a80a2a551401078044500c2c01c0c001c81030560300400d0258000309400e061110001c2440042d1030046c030310b540d000ba41f0480c1c41d9404000311840307010701c1c428110301601c110300140c5107552440d1144403141c2e225001e08525690740b0402910f00c0c1030200501000a6005031056440e42032035000040040010070041e240382d50b007041e0480700644188500e91040b81814000d541c0c1d0350ba20345404c1e040e032250040c1720362401100c8001043c0c2c03005c00c80c00d2201c000390b000307012006880d000320002d09848e030250001500d50301000300e1200b0300350010124800e85000f031030f14495081050a1100243c000d41f00d940403924031b004004030394540c0c15007161400c0b161104c404000124000c14400c01c0b4461030403032410b1608040017 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 121961196 1250 121959946 121959949
    0xc0804050706180f032405040503030601050a18140a050d020604150903060203090304033021020c0102040801060f1d0705090915120102210702120307031a040b01020c 73
    0x80c50141400403d03100c0041c0e440f250036038400080780d0411b680d0b40d28084442411a00701d06881001d105205a0a002506281d0342e083c2c4d581c0000350010341400804150810881d21415801e18000c480c40b1940e0400c0d5642e5a400c40040d232401c5001d0f0013a2010711000c121810070000c051849035010300401c0c5400d1500795403c80032011140450100030080301d000002c03510303500242d401046060065030380d66240d450a40343e40940c0c06e515452510301c0780c04d034400c640e03c0c05092200742c007101c0c1032240c0e00c017a004120768070384022030029800c1c035031000c1110400c48105601910586250400800c00b0b5512800d82e810500310f184143c1035079580009021542103104030040b9003001190403c1d50070a076a400c0041d0490008941440c07111103101da2449883c0b03050308508110f600c0100003145081c550803c00740841c2c1c8004030000d90b011460010640a5208001e1a0030300031049240301d40b24100481c00602920710342100049403c031100030303601c1500e064414203810160507001090741101a40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 121962446 1250 121961196 121961207
    0xc0601090e03090d0c0f0609030201020c040b0a1703031f0503030d0f0b0402030f040203100e0d0e1503070207090c02072411010c0512090307030c0206030c0408010612060c0804050706 80
    0x100d0070071050006000700591a00e50320140301c0014414002e1540c4c2c035041903c0c0001034070803640a0f0317080044c4c070305c01000940d8010504000a034000c0e07401203017003841c0402284080000c0d50101c84907030007110050381c1e45180840558000c554400c102c0310130113001e00c50351581c104240142a40b58008000038086c0340103580c01030003004280c000102e11800c080b800202284c1040340c1582c07100d031043c0c041008515050007030761400000020304022603403224020b603941d0b03400c80141d032007402200c10b0015680e0b500c8150070100c098290381c0b0581e0364500100c0c003e449461500c02c510146042011410450380041120f130140c40081450038095030f0004034071551104c1409464092141100300c0814a060038001c6519414490701c510f541e030041c41c600e0780c000c10002000f504480c1c00074403003d4000f0380c1c012041041d2a0301101e580e034403501c0701d0944403a58421540448203d43c60400c0004a440031811030002050140000304000c108440c0b040e01d68800c02c5900a0054101f103206001c01e60150f07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 121963696 1250 121962446 121962461
    0x303071101151d070311090d030306081209090112080708360a0e0103020d02090c0f0705010504140607080708070c020607200618060f0705061006030c050c060109 71
    0x200000c95041200c0158154000a0341c0106a0007440300008809084032080f0302a0030066a14040000c1d19400c500320045001c3c403138045e40720b1011614600c0505210f50004000f80100c8401d6400801c030204a904065008074115801100c6401c000266050000e198031079050b0080c2c0140e1428110307503102115079100402131441e52800f01e088828000c03c426540310a4080c40690792200000358040101c403000c2517110002d8031035014010b00c0180c80b4002400d101a5064845416070b4681910443e40b07030092140403840c20101040300d200780401500404e001d14040c5101000340305070647c9058641008540b0308000c660b07401c2c0800d410b075200351019070b0300819a00e0280ca11081a500082ca07982c0b215800351090503400702c03500c0c6001040200001d405070b080354414903008907460407a1098100c807004c0f61050b0390200d00071030b128a01030100c400b2143d00c0402d48400740b0f05000403200301402170140c02d000a1030700b5007480184d80101d0450f0310a402c40b0005106c1030f2704c1c2000c480041c0c04c10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 121964946 1250 121963696 121963727
    0x50c030d1e090b0703110f1209090c12090d03060e1611030c1002030a050105030304030b0112030507060501120605090304050d0b340e04060b09091806010b090102070e09030307 77
    0x81c02d00010640c20341400b41c000c00d40310307513151448071212102c9145400c4622502022a0b0003104c4140711003030b00602101e5506205440680c0c4039541d44072003103038a00902200c035809102c0a010481c1d00b10b008100044801c500307880c00c02071710781ca69000e52100b100803a485071501d030201a030240745900480c121001c2502207003ca0f0303d004006044141044100380b54040801e4000c0280300042602d070007182d01420341603004500b0306142d510703110222401071080f40400e40380a411030060600c00c0c002c583c0040d070422014019075a492a034642a694030702d034140c1d41d0920b08408114040c00c04000c46040300c4004090b9030180c24075403140000980017034800380b5640c079001c405910064524603c00c0c1d0f001c110b0303480c503206440c51000103003480050b00c284078411440c00100340142c5a2140036030301c00c1c00c019074410645030344510007141c00c80e9104081011a2040e84000a40c035803021008041c10003081c0e003511040d994038080e1915061098410700c2a94100344009044540b044101c14030507036a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 121966196 1250 121964946 121964957
    0x1d1e04081614070305210307051c091101020c0d05060106050d02210402031c05030f0a020d06080c041103040b0f090319080604060e0609041e06050a09050c030d1e 71
    0x1580d0741c0c1e09490310b04a52010b0a900010343c01c00a025040c000703502001d03c00c1440166494110f102011544070041002d401e201010504070082184010940c043c0342e0314003000c100c4074031b0031300b80b490341a148540c00c64010f1290900c2c107407080c284511500701440d4880001d15042c4d0038031703078280c41d035410000c20190f0686c0e00307200504600c031003080041210b2880c0c20401c011401c1500506003401140848444a9812070414124240d8058201c0e94403103141d20146010751107201c0d035040648190714081c116641480404a4003d030082103080d8900f00c21100bc000b818101d4400c102240011078020f85001c40d5580068503008110b50803542c0184008180da2602e0302d4500c0300242164244803800003d4040420000941818881c107009840740031031292451400da000583c2034000204000d2030010031000c0315140351003140010040503840360051105182c1101001e005100000e4262898403d00460041500b40407410980d00d5046a0350b2090307c2088400903141c00000c0440a8108107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 121967446 1250 121966196 121966237
    0x3030f0507080d060609080f0601121103030d0b030606010c020607061802060a08010306140420030708010e101109030d03020f0d0608060411150702040905010b0402041d1e0408 77
    0x14400c0b8010324a40204000006200e414420018010130389500031a166030300a00c1c40b10b4803414001600c50440b1214001c0d413803030f80c040b07140034040754820121f4503416102c00b04054882c40790a8010806124094040f502182e503000c0044941525840c00a0740205041200901240c080d40250f100d004817442c41c0e064408240d030216215a00c007045250004803980018070401c0b01c50700887c0c0070b503081804400a41d0904d44c9031b00c3d990b58001e40c01c144c84c0b82100b916407855a103041c040f400c018000301c8001c1100356003007042943c44098441001c1c1200d46040c28400140c0c00c4e95040d00e490071006802007281031b6404074154002d45c8100011081d400043c80308014480311802040050292500540480c0c00e0610303040d070503c060591443c1c4100340c044c040904140b142e20075108030710b80484010549035170381e0900900600c104040b1076040b900000c4c001c1101a83c40c540c140d610843c900c50480c80c0d81e20148039200d2035a0100180310a0003e02d07010070301042640c80582a001810100480040c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 121968696 1250 121967446 121967453
    0xc03050d060812031906030b06060304030c061505010e060c030306010c06090c03080711031506060904090c030803010e0702030307020c040b1305010f0801060504051603090311060c070b06040b0a03030f0507 90
    0x3084401d03001400e800020811700b010810080c1186122507207043c07041300d0456440c0c006401000703211501800002c03001605051140684660054000c00e0070402c503ca92140c124101c0500d0094501144420000228504ac8041110710744001a009941035445640c01180d10740d096500a0f40c400e0303118810580800c2060b00c00100851080c444540c1d1454549005440ba0b050480e0a81c030981190950700c0410350303050696030b40080c0c11580940c5e030b03440d58030000b80105400000941104200d03800481002500700085040c2e6219202c2480c02d40d03101c1c10b00700c0e0b907440100c4410005801c84030380c81303406040c00d800240c52003c0c003c1020a01e05000140601295000d82c000b041000300e21100700304080c02071186c1c5010b46025141030200785462440c03c10101d03503844403042096542e89014050503ca003160307405d180400710980d08941050044c020054000c4401629044400710100d84d8034541031003144c2c00503c000c0c1c2000c0826285403415180f2003190101c0f03c0074001c04001001c0003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 121969946 1250 121968696 121968703
    0x3130608071e05070b0f31060b121f0605011106010303031508061005040e0609151b1306030e0a02090f06060c0a08030f100602150907050d0602040e010e010303140a020309060d0e0d020d0c03050d0608 87
    0x1103884140c0c0b00c0d8040e541400c40a00f6103033384d5480703541070011102001040200110740705040d0ba4042c18086440040c03184201a00c1c041c5034094582802100c0034010300b042611054011110200c0301840f40089001c046502c0300410388505003142d00074008980c0c1000721110b1140d0151501001881c1c2a1309180059960b80c0b00381c80385804c90301d01c080d081c003a054261080c21200c00400380104100000c0381d000c01c46000000d441c4c0d13500c080c070060003d1080c3e56060111201940d06805030760044a1318601101c2d40c1d0016103103202c090b000c1c4000110004200d000c0141168038503801042c01140040c19030140f030a0241600e0b25900075a18003140350b031911610740c001140314400041c2e0f2786260562100c200403060b002510780058100c0100082940300c0c0f003030700304800d90100c0c050340c0b200d03181e00a91852040d400d11903041100800c41004510300c40e40070344420382c0710320103580034101401c1c130403a110b400d0100c40e41c3c00715419000071030109104001406c098041080002070185d00c0303a51040c42c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 121971196 1250 121969946 121969963
    0xe0c04020c0c0102060a05090d080613020c030d0605030613120309050f0f07090509030417030d050403080610030b030d0c2303130608071e05070b0f31060b12 69
    0x1ca50b88030b024a0000e95a0410189500c541c0c82c0704104030600b02901c80c191038071801e5a020701088140e6000c598156103a07044d540111003484402c40d03961000c1c160843e101d410071001941c0c4146406030006041c00d000c0ba0ba40d00c41d1102c60540218212b040d034401e29405941c0c06030008140c0d0b11700c00000014001c120507400d4662100c01054803a40340d480403840d008180e045240007608100038405d400d0303030000c2500c0c00e40741e08003540841100c010b45180d2030750103460481c04189080100f444145508000464043d8909494107200c40c01c420f50190265502c4000c80c0d509a8020780301184000d2180c1c021075440d40c0300300c3c0c0ea01d8030080040c0802c002401105543c00140c3c0002030410720303400d8403005c0c503401801c880c10301d101c4514081c0c1c005002d2101010f410110101076104080c0d000344140c04075584181c4c400360341c0e9400d04242040214004040764a0307100b0040d01e480000c0c0d0302c25030081d069103503544c1c9204990f1368507055840d4009003500c02c0c0d00c29009103404580c008940018414500d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 121972446 1250 121971196 121971217
    0x31101060b0904180203060c0912010c0c020111030918100806090c0a080604080a05030c250201030513020616110303030f06041a060d150b16060606031b030e0c0402 72
    0x40d115142daa00700022280c0584c0d0542d920b0416540c1880180c40c086000c0f580600304c06801a140c01181020034003941500c26404110b528000d02034030816008412480d0740341c003c0c4e88645920064000c1280d8901c20926029400443d02e2404440c10f02c10002c0d1a500449203030281080d40d9403000010718240084d525105903410125104c5128240b0700710300d100404641c0010304007420151240e142c5803003a1200c400c02c10100200050072030050800b00d51070019103048040c401126007942a05114501c00100e00090070a400300340f2030060242d80c04503480e00140f2881c50314059400858020503405d004842142e42040356168540c0e050001c1c3d0f00c42d500707080d0482c03040c0c40d08908001c100c859210380c0551030074441c0c00082d11507c643c8166000c0e06c0402100003440242205081d0035260f1f107520a4101000009120941c4030400207524840e07441194180881074039824260b040e50042d203144404d01c285001e0005209109411154042c0c008505403101395800c0d43c0810241c1c0c0c412000710 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 121973696 1250 121972446 121972469
    0x40212010231030c0e040809120c04050a0c140705070e0403090306151503090c0b0c010f0f020c0c0126010b180306040201020309101202030103030801180207170703110106 75
    0x1c00b0141d002e20040403501d095856000c150764190360f516010402c0600415030004005000102009607807422208070800082040c500d03046080c4199a40d900c0c0c112519006509004c04600100c00502944003000001d0b03c650f1015200d0600e410400e801180c000e441900c02c0800018a5200d86075507a4052030081c0c1c0e0304c004450841c00c00340d0585101400401540f411120104203441d501800701e01c000503607181c04200e0908074100103001485a422403680fa40c800160600d0350b40e0154010071200e5480c0790140540c0c03281e03904507012405514604180d03034114001507403040d8402c220341c0152154201d0070305c41c01c101801100d031b9214400d030000540c2d044002190020b020240305a0001064210f000b031032030303107850350000303441c0e01490b4010740c05805500c1d100c02c8041e000f09080502b48203211800c540b00d42c1c3d05e08008003181000e01c1403281d00c84000810708000e15081c0202c0c1e01c81a0090355a201104100904503010b501c0004290100320602c0c00105e41c1c03000a0003101d0051111040d403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 121974946 1250 121973696 121973737
    0xf010c06023403020705011407240b0a03051015090213061403060a030602090105071415060321030a1127010504121202010b1f080f07080a050402120102 67
    0x20030300c41c07442e482c0180c120782c0e006940d80c00041e600203011000d8039402c1c44d210400910510840403540119480280f03410800c40001e4090310b0074841d8650107c211140502c801c20b005002d10001100c20702000e060341c0c0003103042e01e08489890b0030000c000b0a14403542d12501d5982c0c034450302260020f102001026402500800c1759aa102006000300c00d40420000c2c90f43c04c0540010b09581903602c802001d054021a610b440e60303005209890141d03030007000107001038804042840c3c4403803142209a14006220002c00c0d028180005c0908540e40c0c42c442508034118410708000035600000c180440f00c940322141c0b11500fa100d10040c01c01d001903c05520004612070410350b940b56400c0080904110052101f04491122402c02c0d82e58160010a50424114441c4080740075010315100d00340c0003e4800855102400424440505481150b0320b060107601c03044003003181c040090341c3c49070004498070b005c42d10f041a141d2200340c00c02d1005180300514881d005609007660060003010040d40c031900300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 121976196 1250 121974946 121974997
    0xc02031902030d090b030a2004030c1502030f0f03090a0f06140708090c09041b08061005030d0503070f09050901081605060c150a020c1603030f090806060f010c0602 72
    0x40f52010120380d0034103104031400c00752000d5081c00300134109041d40c0e4407004031b84a2890a01201d9000c03407013001e4020340d520303102d0070701c4645517215102d0710348104011104101403d2012050750760321510f094213540f503c5a5110840c0315a0405445400940640101000001c603415152009944100d2002c9610420002d4418580d030009101a0034043c1200c10014a0355000c5045080306c4d0f000c0700d103401d6588450030302c0360f14a04841250800b680d1050404114461300080051081000528041981fa00d800c240742c0c4912a04440c040441c43c14000b1075440d60284220801060340c070f1030900e091680d903400080710741c00280e00028494211415076250070340380d0b0048801411050b0360b410301d054542104035503075103071080a050f8104c0c4804003240c01d0301e8064048449040b007100c1142c01c40c0e0411996a001c1482c80c0c07004802182c403203407448942070301416600f422a5400806000d8640e40d01d014029118186c0c0c00281c10404409060400501103101401e18201c05552142c0122440403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 121977446 1250 121976196 121976203
    0x1141b1b030c0906010906211d07120206030112020102030d1103090c060c030703050c0f0f030406030c030e0c010e060702060c0c030f030c071802040902030f06010815130504030c0203190203 83
    0x10074054071540f0200003950b42c0106040040320541d140001c0e40301220410710a0182200119184560611016600c5020752418407249907100005a132100c0d503903010320b010341e4070f110074000750801c4050004104100013254210303540c600600591b440c00451440c3c0c48110385602000c04400c0b10040305100140b40c040100c841e1410301038520514164a110301aa628015800b0003020002c0001d50803100f40c109000c500c11001e202400c0718480f0920850140d12600140101e00000e4544403107007100d18400e0062000f00c0da1030b2801303080700000030001103030405240f440840d004ac400308003500050703e41100400800c980500a4544588200101810111a009036082984c000c2c0044020208003213950780032207520368001c40328600e54051240103400b50341c0c4604465403000c400c010f010402c1200c0240b20301026605d401c001da40d100c1420720704c00b051040c4a80c0201801903012000a880d52015401500030708220780580c4160740001c1c40d22444018502020501c164403804505041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 121978696 1250 121977446 121977463
    0x60906090d0b160306030f061a130504030201051003030f030b1507050109120816080907030b0a0c0207090606050a0c0c0e1303030506040207031b0303060801110405011d01141b1b03 79
    0x44c0f6042c45450306d5030711000225491130300040d00d4240c3c3c407840b1201103c00700046030722052019200d070503840e207045078103c0284412102500075500740f5001450f00e4001005080c2501c0c1d140e121181601c6440324210001c00b0b5191000d50001303402018000d060f021800500003040c4141c0010031401d4043c030740144403212849007041404516070a1091144683c1802c02810480d440c000400340d88155500380b42a01c9a400a0100411001404909002a007011000d21426021907101507510720f40c100c101c900902c51480016001d0100200c290720031500f5912003801500510601500d8140c60607189000b42c9403001e0440c02c4c03514441c205505405400d501036070443c0c0840c02c0c00c98507240585070f03020005104102103244100201050300030f51056010384075090003004010141003c80405500c107025090104e007081104084c1401355002d0080304070300c10380da40c200300d6068011001c07083e0401107050030500c00c0800d4403150712008000103000b00e01c0c1240c8045010b1128402d060130129070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 121979946 1250 121978696 121978741
    0xa0b030708070e040b0c07060c0c050c0f011e030b13052a07030507140601081e0a050304120c0306020a210e061914010e010608010b0a020a02060906090d0b 68
    0x42c801c10010129207401d056845500080c0c800c50565507a600030400344500c0600800c8203280c501205075581e40042d90480281c400c3d01203500c1d161202040040c1c020814903940d00043c400e9111a07803401421044000d07160103401c021480c0a2078400107040e07020a01a090400c9944408105684800c650610f80141550000301041980020404810300c1a6000601440310000301c0c0c2e000c012031040304104078103065003617411035616181c0580d1142054101d0a00d410740c00004810304000104a00d203281d03500c0802180b410349021140d030a2a28411b000340e0f9081c400c03290000104100d03000400c007502c0700781c0d16010014181100c50300c004c0003a44030150414500b0407100700f088000078440d0f400840c0c00f03608102c0007a21798580c0e0003801d8900b02c400c55400d9100c00015002d0021081107042e1005031f2200307034060b80c0f590400b24050045100400041c0c2c0b1108404016081c03985c000c0c54080c90150586251104000105843c24201801140d25000c0c640410000030880c12925503210030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 121981196 1250 121979946 121979953
    0x30503030a0903270b0702060904050f060406170a0f0317090c090a0c08060d0c0b040602100c1b0803060109031a0403020f0705060409180204060b0c1006060c0b19050a0b030708 77
    0x100200c0840c001081d000d12091700d4030000d0f500b0705659030602030710030b4031200030411b100d40e203086003008618200070b940140c051404e01340e001c20480c19042d0901c0c1000e4216005026003485a10344070303005225000c0a50038422185440c0c015180c801491502c142011402440d0400ba00030a0104281c40240300ca00d405107032101c881c1500e0b600c8900c0c5c43d0000011201c1e01c2c42115603042142440745260320604040380c00140020344c1d030b5000f040101c4407513100b50080212007102d0030240c0d051016015101446d07518050f2b0640014594006107402010601d408103484d9242d070745a10bc0038030100708402d00358071804204010183c4c10003200014501c418050a455881d00d400b143d071074000e5010b60152a51526418140a00c81c0c66114103d036800034000e128032039840d10501559444181c0d048290700445103a08081c034549d002d0541207429666601602100544604628000c0549007580c4a448101e50300c845c0e4000e03001c1c09004a2100c0d0001680180ea01c04051510f0100d5119510307942 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 121982446 1250 121981196 121981247
    0x10c02090708060102100f0c030501050f0901050d0302010207080409051f080309120a02090408120c03100303080702030c01110406020f01060807090b03120703030b090606090f040e07030503030a0903 87
    0x315035546254022207942000d000540701c1c1030060f4201141d441c0c240c1752251410100802140c0541c0141a0061554900304038903601c54051280d181c1c41e181c1115000700710400100150708051a01d50b810303038000d1000505091503643c40700203d9015a000d81c841b07580316402d2044551441ca440c501c00e00d00d5441903480c1c40d01d846010740e1030b401001c180d9842501e2036208080061828400300b42c03059030051900415103021320707040c3c500c1e411542100326140c0001e00001c441c6c5801c10110303030040b000040d00c6044245195001c54480400030310700411404284080002030100b4000d0032550441440e00f107840d1801c01c1c60003864205022807400c1c2c030340e0400108114a000218840043c1d82c0c042c10301150041401000c41c0c60321071018845045a04005890404d00d585a400750311456800c9881032465100d910810101d401041a4a41d100c800f03190880f105107000e0b07101002c090301c4801038808007642c07600c134542150411141d40d10700a4840451008042d44503401c3d10010440f40190714548 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 121983696 1250 121982446 121982449
    0x140a090c080711030708030405250807030b0406020c03030f04050111090906060a031104080d0f0903022101060510020a0b01150203040b1809040510060503010605010e041107020d05070311010c02 85
    0xc0708080d0032a828001101204aa0745900784200e91465800c41c0c041642d904291410355a60074440c0301001ca1590804800e40022400702c003000201c1c0c0800009044e01401c6881303003102844098021134500703a0030001c0300b100350001d2001c4c6104481c0d14503042c1c641c4c9400d06005003502c1181420403180391041040f6641079560101964100c0c20a035480341c0c540241c00400e8004045083c032100900340d01042c00240340300700140540144190341e840c41b081d000188001d50744034119000096004005840b9140442c0c0c00d0010701611144040004c0740b055a600702103070072001640f05640050b001241c448040c03214424903070703006061102c5001100600e14400a44a000d14082c071240400000b41c000c000004003140c82c0c200e904024229045810940350113a51501103035040c2c1360007070500c140001e00340341c1841280100d0fa01a141e00880c40d054408000042c2587c2c091900b040809100c0480580c43c0c13814107001203031051000700502401d50608034000552a0481030400c0301140e40740006 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 121984946 1250 121983696 121983707
    0x5010b13090e0c0303030f09100203040c1404110d020a09080708070e040303020909010f030204050a0b010813030201090c0b0c0601090c0509010302030424061703040302060f070f0c140a090c 83
    0x115041c1210000c0d60591002980d4102a00000580d40c1440040144440149808091801035034000f045840d05840e241c82e42059000890740505504640c0c4020041c6a4101800d400d0062006000261362016003800800b0742d0002c55588480395030200d10f034408960020b0007a030280520300018601e861800390f03196a580c0c0a400303009002100c03000401c1c1010f0080d01911721914000b440c908056855100c008504030040c1700a034482c904007004540e459409202d0800020f50607990396074240d8411a0310107024164100c1242159a00c403d01c5c4041800704501601414101c000d184c1d0703804031211003034507241c03068000c5c074400e1b40740902c604c81d0a03800c001120451402804d025840303944500f0b010303079018811885c207000109a80d44501c1461020303485081515100c030201400c0860486c0c2c19580d1b4012400700a421902c1005921000503024000d480d045125203003191041c441e079a100398100210f40e009190b5040c03260b00100c5180341099842020341042402001841e83d00d9400614 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 121986196 1250 121984946 121984949
    0x20f0606060f0f04060509040b01030212070f120e01061a1c18230f1504141f0212010501171303030e030a0e03010c0e030a03030218130c0305010b13 65
    0x450000014007900c04490320b02a01e41c0c0340000d090058540c1d07941d60019041d94440b416044c403480c505807043d840b82d0301920030345c1c0f00e0a60105200e00c10365510351060780e06a81c40d05000c03040c403584496041050000740104065000c0710800800c82d5442c0542d20500c1040304891024a00341c24002c0803006c8070084115280034140b060f002c40c81d007464540c0d05a1100c0903810250aa4442c515100080304074020079030590001c190031100d10701180c54241f070b103440e000c2c2811149c142644010501144090000040310601c80301560356244052131101c0d0094041c1700000e07141900032440720446080b001e5803074010a0300723080588203880101e0b00442003100003440b410000c400040180281446940316420800c0c2c1c401c100c0341e85089100d0090418141544240c0c801d60034580c0c90140b852082030805d240d800c011b4014082e01c2680c2c1e030283c0c06134100145840c0c01d0100b0401406482d0b0301d45441d091810090f40002034041500341d0000e0a0350b03816000f910b106030041003000e0071510001400c1c070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 121987446 1250 121986196 121986199
    0x90609070807031113060509010e0a0b090f03100507021507170a180b07120f0903170a0b0a06081f0b04050f0a0b0304050d020d030c0c0b06060c0109060c0f020f0606 72
    0x640b46502c41096005019040c0c4030092201020b00c0428001d400c03c1c01021405c8c8241c80d01c10400d003111041040052050243d0360700640248002c040d181020150344112003c010181c1d0300001b41c1504400c11960101d8550006a01505a800b07401c3c0311001100c0c2c10002a2904600542e141d142280b80424054468024140d40d18070f0000302c1c01c44003105507005944200060303414113100c8401000000404030017a005450180502101c0029202c1d448445038940c50b8595030b1280c07102c42c00450a0000c0c14000f502d516000d981c9503d6071003500113000340c407107510350302258101900e000c1aa00b90705222003508413000c800500106400da02a10121342e81100d10801d0206c0080200b0744801c8542d109840d0540084207001c00c0000200310b01d0013100c9030b94222503166080c20004c81c15102d010200c4008910041c04070408a400c00e40690303071024024084e540750141c00074040c0c2c00c403101c541040c1c0d1016070f149a4203458030340c84804c1c00e000c92030620041c5511081170300290340b184000b500e00c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 121988696 1250 121987446 121987451
    0xc30070c08070c080d030c0c050a020402071a04060c09080d09050909070e090d180e010302040c03020912010507110c13020c0c03030403030201021809011809081903060509060907080703 81
    0x420400107500100c84585034042c10030180140d82ea00e500c0d60700c80426101e84003090170408140d00491142c2c01d82090030b6006001042d02c1c2e4025001d00c8000d43c040803042c0c5449080c62000c0039501c8542c8005401184610000900058004001040c00d00c040d044141c55410594001a120380d201140000b515812030b020300300c2e62218510189440e90503400b03a00d6400c440c204010340c400001c030b00040d02c4d08281d214000e034500101c01110b06040c00740a080700f0074410600510160a003640314a0711b400a9040052600390142c0020350a4180070582d204d150b9100d800b009002c0794071203078400c1b90242c0307800104a01e1140400003030340c400c2201e0351aa4666400b00300e550501c070040258480e1090050192942c030b030703180d00b0028040c1d0b01083c0f481c24950028448102642450941c444c12500b2205101102d582d000c40c6000181490860a8035043c10a021040301040a0050b030810f8000d1502e00107201391400d418000308980091080b4402c2c00d55404000105801101c15a441030051600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 121989946 1250 121988696 121988717
    0x30c0b0a1706031005180d080910020901050a21090b0402040e010203060d0602160c0806071e0e120a06060f080709020c07030b070203040b070b15030f0705010f050f030c3007 76
    0x99006c108038210503074024802e00e0b01511a0f1500401c3c0b41d030280544106030381041012030f050b01300740e110384604a40010b0041104141591040101e007002a4140d00d408480c0400280000d05a41c00f00034166032400c80d240c148001c51909100d94102e40314024029801c1d0306d050000500f26030311050020b407100d500060004000500301168680d0150301000140d103c1e62502c00315551154110b0351031020955418040031800c200f0340807552100241d54424840400b0071080c07190740811040b001590344a80c0075403100185141c0101400380000d034410100c2c162822018603c0c1a105600c10f00c5031510411a800010300040750500503680c11a8030b230092903c4000c0c5c00c034914810b40c1d104c00450710000c50500100048000d0180c0a550a0740b480ca458004c0074041645410054108202c25807006508100c01d500403400c04d01803846904050b8100102a84e014400f603004488400c070b5048000790209102e4411104041200e003107050458440000002c41e1003100c0f07010300204140720f8103081c1c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 121991196 1250 121989946 121989961
    0x80c09010e070e13050705030610020f03161a09100b15121902030a02030f0f0610030b040f060f0503160f030201031107060903020715020d0806090a06030c0b0a1706031005 75
    0xb1003184c1d50000315410440e615000000411581041c2ca0702403094400c03d8086a01c10310000f4422212020480a1403401210020210601802c482c007100d8030324050781280c1c00400883c900f94800c980441c003400c850f460342c40040044544401c002e0341303ea44458403024545c005441550104015007000707155680300c4113001403020074405240c000042c000802c1201c0a4010b801850199490405801094603514802c0c001c0a9080310502e400c11180c0c0741f40c02c0a6442500300c0302e100b12010300006034401c480f1300c50006440306134212100f1500411000c2110341010015000490f420309041c041c10360400d4501042091584400303030406440c0d240900980c03034250201d0b24115031000c010400381c0341c1441c1c0603484a95901c51001c2042d12449081102d5002140f01842114039a403071500c070b962424100200110090030300701ca5680d41c0c0d1008800100401d043c04050100c20800035112240140001c10300c0040c030f016504480d1400c070900c03000d80c0740058885c1024035650f00c0130809940c0c929 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 121992446 1250 121991196 121991209
    0x40e07030203060c070c0506040501021c031503030c050c010203070c060e04060b031302010909020306010c02150904020f130605070b190b0402040b091c030c030c05030f040e01080c09010e070e 84
    0x80000e0340c180111400d0090102d6040024101c41b07100c0c080e900e40300c0340d4900420005000754420319001d81c0042948144c0c1e540100720345008403410741800100642800042c501800741e0741c002b203001c203c200300345c0024048100103030321010409100861034140103581d440c1100304248a04410700c10900c03100700c0980d4580e0030003c0075080c08101c003034492810081c0000d000e801e094042c0d003c50f41480000c91001424000c4911a20068440c0858400c682c0c1c20301c0511850300d0b950070f116107000d12140707a29a603980020704035061b082c00f03603580b104504220070100138071343c0c0d21020900c9010441103000540d028030155001c406c20b601c149080b240d040c4550082c01100c80a241d1041c400507001c9a407000d504064031030381320f09540c2c204605000c00e110701da00c000015400740c0400e103c240c50500207032103020107460051040c4183c0741020f0802e05010f0741130b0032640085008141070300c01072110304010418030b40c503004201c540c1300355540340c00440301449902030449400c000301d504603180c1948880 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 121993696 1250 121992446 121992449
    0xd0b07020f06040f0201111515060d0e0c01140a02070e070c05070e07020c0f0d0f020d0804030c1404050f01090f020f0c0d090b070b0a1505030115060306170c040e07 72
    0x24000e850b428545440c001d05680150030b03007240803a40e06000d6203280c03c2c1c00102d070041c0547c000b4590700e00d80c560b5500f01c803840344001c803040c0d8000010070096542c503219002d02e003002c2203017038000c20014111600150100d4080d00c03210503e80c1007404450440e681c0090003204484038039a501200d40c0301ca2200f00e41107940500041c01920400b04001458400340303400a00c151807035400c3e914041168020089080400d8000c0c03540304ca1100051004290141d00354031049200a00194203402c26984101007074126500544203000c0340740d010003140d21034140081000c00209c50070026480c15480b00200c6660600950410580d00c0003403010a881590448044034400e002d03150700d0303404807450765580d181550080300005d0039100d80000c904001c07a05407004980d00c110382141980d00c8248880c000c041804892558115844000030140c80030b11890071a10081e02c2c92428003070030404c0250a0f188994811586810030030041410104045400120341d4030488000c2103407100402410301c3e21445 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 121994946 1250 121993696 121993723
    0x13052218210c020d020d1208090c010c0c0b0a0504050a0b040801050a090201021005280608190213051b0a020a030e03071a030406060902030c180108130b06040e0f010f05150d0b0702 79
    0x44096900c99904100034609c1415000e044034a00c14611004403141c0e150890018215800e404003404800c00200c013078408c007001ca20304a420103990b50009000b200c055486074616503000101404125028002c071031388500003c0d0706214182c2e00c1d600007580c0c4c0900d44600342d001982d98000c0b502294840010300c0c41a00d035512500d24800090080e00001e0040d40710b41501031092050030b0030007140d0b040e820070031a90014400707501850a250200c0141000800d40c1202c13500e001c0301c0c01c0c1b9100029024000e5148290b00411040200b4034000c2c220f078202034000d6201e42e001d100108030f4100c5100d0002c03100c4200103003680d201d4440c1d1500c10301401c1d090300103030308140c000f004215189050310054a00503140e41145c0640109480040d50500390640b49401d99041ccc5680c4100460a40d04106410410140000613030040009510f401e2070766034804040c099444010789011005540502c0d5001a4405202c202291a03600010701044038914001c102c20160780004052900034805502c14241 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 121996196 1250 121994946 121994963
    0x12050604090204050a020c010e07030803160c0203010f1b0905090a02160b07020d09060309080306090603030c010f0b010e040e071208210709080313052218210c020d020d 74
    0x4104a00c10065080b0940403485927181c9016204103010000e10007003120b40112031613140d501c94a400d480d1100501c0c6030941440380c012441d00068509200302d03950b00003451000a609603460001c01c5070014109641c00030028648002e000035aa19942c2e1900721045d1140148c1d40d00c41e185982c54103c0410740d01408101900e01044840c80c2c0105204006014541d40c82c41883d440740800d4048441c1d401018003e41e106200003101c2d41000c0755150340212000301105e0509180840301401e403448200100703030701511442a5480380d60404000581c20108640500030640d1089115035035460a226907001c002002d440c440070b0001c810201d500b0780790602c605030b485131040b40d041500d40701d05440b10800035a1801000502d42408001d0b100b120350190804c180c520f1074181002a0740904440c00103003603200300d004106d80081840303020000c0014400031009032140d4104005040181c0303503200b009514548582100e02d62240c40c1d8420584e04680d140d8580100d0300100781c50801c8000d000305240c4c3c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 121997446 1250 121996196 121996201
    0x1061205030a0f080702072106020a0f090b0a05030a020a0908030309071d090d0f030204080706021b03030c0d140f0f07020909011803050c0c03010615081005011205060409020405 78
    0x1000700060a0000c2c654840300034075088010129071a01045860b24010303000b445007030180d68171004005196188180364480041da01d91038500480c1e105070440001729080504607820729410650101c028561201c83e00d040400c1d40724054010701c001000d190010741d0015a50320300d5801400040d011f40242c4040703c1c1c90303103000054aa600d90301030040b03920708403940e08010079015000071100e2280071021b010380134000c4452000d44065200c020010145a000d02011461210822100e0014202503000304080c214400501c4110702d42072401c00e00a030005c00c04003201e04c100003001e10032403000c0e240100200038031021040c55402010602082c00340c1c000303589000640c1400103410218021561040983c81e00c088180c220390038152410003006410000c100406d01640c003070300d41518800143c504601c01d040002c3d003141d00c1c41c1c01c81c40c010710403112180380307203540709224070360050089041002060500c030018100700c9000c401c14601c1c6407603100058140c0c60305d800507540306501810900160 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 121998696 1250 121997446 121997453
    0x16030801031a150906010201090503160209090102040605031612231609061121031008070b0913090f08190c0209040f0201021203010803030f010512100c02010612 71
    0x11003840180c40d400300c4042c2102030101d02284075070040314603261840d4019081c03800d200e010303440180002e041d5582e80303051f40e001c0f54081c0010000c0040307420703040601c000f9a2040110072031000e80f00790082c1c1e00c14030003031000303e40040c00c03250400400781c030600b208029800212158051401000c0e0340e20304109550340e0182448012080350403000034121442d03602d910340e04088106200c450400110440c80c10051035008080903c8034810340c80c02d485c80001c1e0358005120740e03001800c01c0040761034000208003005050b45002400f0b000060080c204051030849001a9401942481842080303160480349488800c1c0d0301003804d17181c0c40b410a00103000c590520a00c40e07040720486003425418150800c841e6442070181c80940d80c0d0080031108203440355241c3da01c0e1b4041a0100324154803071901c42429821640c4003840c000e16035040115624a09500d81046011040c1d202a00424210502070901c130302c04224081c00c604e403450005426105440c0490143c802940004492002d40b038891091 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 121999946 1250 121998696 121998707
    0xd060c02010515030c010c03140702090405030a1b2d210e1002060f13050f06061c050309150d1107050c0f1305040303060905070203030604150602211603 67
    0x2d240034101c040140c0c8a0318245915031705001140b40c00100c0c1c1d0b042c03082c0000e0103002c0141071343c1c102600d060b040503c182d0116400860640c1c095600d81e10114a59000940c8500b401ca400c03821030211004455481d41c5041200415100880c034a821a03100c0343c07003441d0315460308a0480e0308000b440078150180301543c0240c1c101144034500147c00c2c248101110b0900c19904808030506a0040201d50390b901d04c1d40a0604024041c044080528518035021900422940c4d2003c824074029120300e041c10b40411100d041040d407462180c80468540401042d404030548000750403d4480340d0030b04036070410704401407180905034181c8500d440c01c0304018035010340c007904805100700d00301d0740003000c480c0c00c1180b01c550401c4039552120082181c028100c1c5903800154105105c0d090104807030351039000c14019280110346140c01688080100040c51400380191005828209041c46815051003802500c6803408225013041800c80c0c0e0000148880c0c80b4215001c08000708a601461b612a01c0c1c0140b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 122001196 1250 121999946 121999951
    0x1b08070e131401060906020d030509100e060a051b041203020c0a060c0c0801020c19140d0302071208011815080a0b09060c0c150601170108030912030f04060c020d060c020105 76
    0x40038242c5400100300940117410002c292007842c1c0062480002d40d4008601400b0b00800382800c500070080840308215480c020f02145c4120403000d05090f1900002c50422100b0081202e100385c0f03a0f0803143c001e02440c840403501640c0d02102c900c0450788181c101646130100e6130780e1094020640080004055030320201c00f40569110b43c10069900f44e444591034207034001d084001c219600180a4010012208a01c2d0642d0700e00c90140d601c0000300009026040660020060000c40e4000801104005c0c143c10844c07020350403400c148910b1b50628004510481c0040c0c400783e0403c0d035a05041170710b400c040041000403e40341040f80d00b1543e1901e061001060f081d10f1315100d81c81803c0205482280120545050060501c020060000c401c01c0300c44024030007401c01c40c1804400380b1810780a008180d8402e028041900045035110031040a001250516800106040e0418844001001145030881e03080303074000d01e08488105041d0000884c00a011300006118502c2d0080010301d00e07070103401151 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 122002446 1250 122001196 122001221
    0x91119021c0801081c0c060509060103030905030d0c060b0301020705030f090f1507030f090e040302011a0103020a0c0f0c0b120a0b010903020d0b0a1b0203090f041b08070e13 76
    0x1d014804009999002c1d00380624002604096074041c4485070b603c05d40000042035207040c0612600d242c84210417070b9030a4413100c1441e0051401401490b0300490181c0040030250700912900740b04540c01000c0e04a1030f003000f00195111500380318a60f6094041d1042141c00c0b0007525030f500c81d0640c10708903592140341810f00401011903c1c140070300c1e11000013078840d40c0c0981814986045942d00702c4070b00110555400c288041c041c400304100c0c190080d203070721840c401e4000284c103082410324081840c6014580c83c1c10540100000201c10364007005042c4525408080d503030361111a854480c3c8128450b030816044a2004a00700340c180109440c200d004540300e0302c08001101c8401d004440c1602d0750b000c0a5044060100044002040000c019a225441400000c0c000c0380408880d00c1e034503600c100d4500184d00108031581289090801000d03040401c80b0200110000d0422404280c40581d1030f00090024800018040b1809031075611075156008091a45526468603000000c1885880310b0703 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 122003696 1250 122002446 122002483
    0x1202090c030103050601031e0606060203031e07050403031d1503010f080c100c0309080601080307060b1014030702120d060306050a05092808070305040e09031309111902 74
    0x60500d510900440741600d030458003901c1d4903800c6840b0100002085400c034020319554036050404110b003441541c01410042d0b0103144d0b1707824200c07550f48c00e01407646c0c00a410080c88000b80404d040d04601142c3c11650316042c901500c1313040785444508180d01c3d607929508210001c460f48004e80c0c014004505031207510043d4803002e900c3e54100e035a04d8500e098029008805c40301c4e0503130b08a0260740404000b074420f19281c1201a00c8405990400360203070321a0105600103c0c6880c108940c038000e003100076809407a00788080b00210f02c020844400e2501c0381070301100020115003828400d1158460b07080351a1076042d5142c8046007002e00a11282c841a50000e18000210f042c991543c0501c50040504100910034010000001800c0306610b48908809296103100c140c0068407000240160368021b032203240c0c0340c5243c0168010740502c01030115405800c100201c054280c011a4054160344c00c41800180607506403510300349034440c00302da42c00004264030782c50002543c0080e141c68683d0000c50390 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 122004946 1250 122003696 122003701
    0x10c0c060206270604060b060c0d03020c010b040905060412050c0102030115030608031602091005030a0f02011b081207120905011a0a030206090402070305070b16090608090c04090503090604120209 86
    0x184001801a90422144c1008001c2004900b0540006031070240c0105410b1920342841c001c42d00c0c04100c407070340f02c01280d004201d00054550a20a08080c541c066406100511207031707540c1621000d0082004084040d0a21900c01c0d4034858000e0703d40f0450004002c55903961510801c03841451451402c40c00241006e0001c02c0c00354011064641041c0d1038040c111400616600300039440c2c8001f0611445d04480c034000040503a03042000c00100345c0a9000c108000115000051080c240c10301e000000ea13400c007903000001a0400100d40e0210308003002c440329900d580320221840d000780c4c0700221056040180071814810190b214114a81e4103a1000403503c441c4418005014111710020358403c0c414001c0d000320742005d8004000b11882450b04610b0041240e035981300c80003041e40c100303200451510b0340d49034517504400148040c081600700318505141c9904c2a0796600141076180d030007036465450260030002c0410a075980c1540c011b141c542c940b034071120110f00c01d080300f243c180c2c07260b20701130003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 122006196 1250 122004946 122004991
    0xd0804061b050901140c03040909060c0806090a0c0c0f0b070e0a050d02090603070902040806090601051503150307150e030c0409171804020409060501020d0f021b010c0c060206 77
    0x2241d0080622600d8460410550200540b801c40d0024600c1174503440421200c0b1200b00c0a00c010400390507201c1000407102c426003004c204442c02c05406509000f814403d11505a4035407042c00d60184c2c0014010445a009080840f96401011401400100e4420884080045072807008c2d118103075954901046000309400c2081c0325040c0d10405030000c02440035840541010000668000005001c8908940e9242501401c07a441548041c5454100b2003d2003038000091142c2c900401007150020300710506040d90740c20f540b201401001c100130940b86018080d0f201801084000c259100c0d4003080308040c41000f412495030380d04a10722901410785404401d16003403040e000340c150443c0850038204c61a000000055102414603188a148082001d506603030b10300062001e08181413003c95014944800a850050320b00030100900c07054040c451016540014140011540011001d80500701d4200680300344034440b0015100010458011a40321380001c6c0070b03070180c299004000b000420f03450 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 122007446 1250 122006196 122006231
    0x703060302130e030f0c16061805040209040b030d050a090f030f2d0c03020f010305090d050307050d0f090212030c030f0306210a0212010e03070b04080c0d080406 71
    0xc000c2d0701c40782e02c1c01510400790196001003d074070402c50440380750030000c1c03109a030326400005200015a000c140684940f042d1078996400401d0300f410141c100c500214209600d8181a0041e0382c055540812030040c16656500100f242c00005003d0784c00d02c0d281e01d032008040e54802c0005101041d100d079400101c0c40050810202102c0c3c000c0c3e00c1c000c0103400c1d560780b040c00c80c5031000341010070415428102c0384510007800c2e010006100e0310362141c00358910310601101c0820141258140343c6800100006101c01144100000c0d01c20720303017141c2d2590b401c071050b00e440c050001c020004034030305500402020005c0d44030722441741c0225184003005140f210741603664420340807a89001e4200303210700b4094074074820246030060002003400b910720940c40f0b10200c0c00c41203080d481d4050b074490131958081d402c0c40840c82281c50900d20080c000c040800008598034440e0190003081303210404001810703c052482591080506e805c181d400e1911400d4004208034402d503000d40f181d4cc68200c1d40310041b103050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 122008696 1250 122007446 122007449
    0x180a09060524091315020309060a0c0c0303050406020d061d06061c0e1009080a03050108070b07030c020f03030a0807021903091806031b09060f050918030d090b0a05070306 75
    0x503128810502c00c034000b448003030b02c00504071010540940310f00c000015200326107410003c80c0c0440041c0c0702d240c0044110b28241d0050052242e19190502d00300800e41c0c04244290500e0f0941800308141c0c0300c510b0028000e200b01030843e20b07001e18102c00403854020440c40f20305081300c482c081031400d84640342049120700c245006000c14a0341c00c0c1018842070015003000c0a600c0e540e03010b481e00030a00c4e40750302098542049040b80d0050000600008880d00352003014007608103a8010302240341000c001a045218004010717082c0186018503c00b1965034089404117450003806483e11890420000b502030002a03540f503004d03005448200980c0c085201c5031070310300d54040c2e072814042490040f1800c034503200e50951100c01901c0b80c01c0480031840b80c0442860000d030050700203d41a01e0a9001412140303160000d03413112031203110802003035490402c002c0d000400e0910100e032900c83d03e0b201c9881e502c90043d24220344d030308018098041c44441c06483e441016422000c5c0300ca5614150103c080f074095 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 122009946 1250 122008696 122008741
    0x601050301030f1a0421080405071a0c03071115070c030803040516030b100e100b09030a06090b0a060e0405071a1e040302190806010311180a090605 65
    0xe00040000c01c00f4010b40b4410b85000b400c0c144203400003c40b01d0785880300d0442d01a42c00403011200c00c00d800b13203000b0005141d0351840c9405c440b542042e548450b01c0704110f01c00c0091090320107000e90101c1c16884101d42040d4101c0c3c046075030325107561800c40300c00d441d80e0480b0b620030006c00c0f038803140c92000302c0203c41682c0c1d80172112140103070466542070f0b481c0d003002c1c00030394052042031a1004000a6002400042e50180110f41c141c0d14001820705a034403495006008000614000c0c410160052000b0030240c1c0c0e840c40219881d44040c0e4003280c0f800c61072840180101b801d00d074040e030500c030b85c40c1d02d210b004510b054000d202c074a8a800540e003190a00340c500811903806040300702b285c410a9015a02d809007400c48035072604641740c640020b090b013400b00003800c0410000b820411840c01070041d180f0004035548000d0800d20b031401e81601ca0005100103000100d40d441c680b08540e071403884541c0d82130603003a880049030030b140028000070020303000211492072404000c105800c00c400c50b0302501c00507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 122011196 1250 122009946 122009957
    0x70810020d0204230405070318022803060c0305070c080304020f1f020615120d0806010c06020c0a110303030603070314070b0403050312010501090e1305160f0503070b030601 76
    0x518101000035800395041904056007070201003040940080250500f5603654000031441c44088204000c44401622000038107213014045040a4860600b0070741598044a040e6411740c0170951141d0304070030000c00700c107400318100000300c104401540400f12101c080c0d0f030b04125964984c0030903980014001c001515900e02400002c006180c180707103030441840c01500481c44152001100100501041041409a0405401c100c08107500c4030b9254095081200da039020001003141698403180076200440402c00c244001410036406a07141d08c0129038400000c6550b0020200c000342c031101d40103000ca60800e40e0303610180c468600002501d005244c0140640310461444c0d84002004e54040014103107400b030740c100050340031403101c0648001d50140c00955a03800a41c0c0750407541070700507004035043c0040400107100740a0080b8107598400280742c0d8456421b030f4142031881c0b501c03a402c110041c00c0c0003c40d00202d26824400350110880b00d040d0700321a00c0c141c03124941406404100d440900154 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 122012446 1250 122011196 122011213
    0xd0806060d02370e0402040b1e0c0a0b040201080702060f06040b04090503030708040c091e0203090109020d03020c030706020c06031513112a0a02060d1e05010f080708 73
    0x80d95402000c1c03844448100303814002c0480c0e0100b15418440c03031008142c8003036100781031905070004e86103010204202c800314640360502c520404c040c051441442e40e96610f142d41c035190f661001d000c0301c850405004c102c91100035286003802c5662011501240080c0840c004125102e0000852a002e2500c055074441e407030765101c061000800c8a80d919031391058484000c42d02007601030000b54080c080c1540e440c43c8a01d01400c2940054103154402c2d2200b52829004150301102602d100f45000541c90700583d403600c0e4100300501401220a0282d031000e1005407039800c05400050b100e2400d103084d4141d0b0896680c0c2d8000742c1c4c0b00d204101105400c80c00030400180700d4100080c10711030320f8000070000e116800c003601c501422900c0c41c513000c070003503040041e2443d6031400c90540d801500c428a81010504220380c9002503c858982c04003d02900c4007003035082d43d80704542c0040011150303031604c402159030240040c20181c8420b1007590354111103008041000c09010031a00240c0320404014010721 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 122013696 1250 122012446 122012467
    0x603030905042309070308030420031204031509060c090504050901020705070e040201030e0613030216030210080910110909090d2007050d030c060e06070905040504080408010507050307020d080606 86
    0x543c00145426214050514040002040b00024500030b13030107100d0504540009042c016176003402d41c00c5c0b241c801c0d4444640071040b01210803c41d410349a0101e481d55440d042ca09504001d08400140141403500342100540856404802030048540c112014440c0c0c4e00c1c0d100b145803c0740701d0b01c00003a1554015a400b400f001454250309604031344103160004440e000b030300d2003500303081042e80c10300011115081450b05041d41000300c00308904400c200100c24500c0c40c0c0c00200c2c8148c4011210062144100008202c800e05102465030203840d542d049c0842c0d031118508444551086079007621401100000c2078030420006800100080a074484040e4000500e011160301c400d9460f2480d51403207054404207481d1500100403625030301c0303070b212008942c4151400c94280c80c00040a5815a844242081f10860b40588101c08941c2c0582e40043c007a19281001112071149400150041d0f00b00818000030340da001000307522628056080d102614404041161b04050607120103902440612601682 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 122014946 1250 122013696 122013761
    0xb040e0316020d0f050f070f0e07080405010b1504030b09030415080c04050a0f090e0c090c070305040509010f0e0114030607030506030f0d02030406030b06030603070902070c03060f060303090504 85
    0x1800c0c00140b412010f20940d036265040c07403845020458041c0c0051283c05a140010411140075100750643c0090341400c1500591520038024031403400c0101c0800480c00b40002940000c1000b0f03000350009221b0107900e82208a16807080c40119141308000c4009400311801000307a8081e1391089605804032003c0d0f100c2111649405030181c01407140c1004000740c150fa036003510000520041c030b1914403480c81d283c5588101d81118107400710039001521444429505c1c1102e481c2d2101c1c103507002e140c5032000ea0808030740c94040e03900b0064202c1c00d80c500100b4a164440396800c1103071041e4400b0125a03803100b00e010b004c458042100c6805a1001e0701184c14070b4040d41160383c0c400e1010b01100c41103404481401d180c0740c00d170350240d009a000018140314255040c003a4103035942c4240d903803600d1410a1000700340d584050b440b44442560340481c4410030022000d81c000000e43c0c01000c1409243c100c0c0300703100028a281c2c4002ca01050840d08009010704081c05a0700480303d4603c003220804450b01d007010305 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 122016196 1250 122014946 122014987
    0x110a030c050c0a0f021005090a0315020f03010b040312090608010308160609120f0e0303030115140304080d060f0506070b1503030c0705090106050f0715060f08010509010b040e03 78
    0x5210741801240041e12003004014076031809501d2501c0304a80728014001c041140a00f81800c001c001c01443c1e106440d40c401c40c6048079401000c0c001c43c8464071031b0900c000e01600c07003410101100040009400c0a50501070b0003034038022034010b08070b01d215070000d0710501c54501c9640301140008004002080f4820081c00e110034120448040c0c042c00d50b80c41d132080780e2a00d0012144004854448811264403007241a071944182c00d00b2800002040d0010340d0368041449520a41c03c5486045c0071080e114040c0c17078079510034011105449040515200d038070303504410708480c80035142150015000003400e261004441001d001c6e145004a6500c4150031030741d000780090140b0901ea80104102e403801c00040100d1425000030300a210304010030400f4511701a4050420484240f208001010022085038000ca601880035642c0c5820107090030007502d10703940220080015840700007009441904540e10070b00b03008000700040344c4001d0412085038100000038103ea4414090f039200e00340000070300365 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 122017446 1250 122016196 122016221
    0x30709021e0d09151a0603130b0603070e040b0901140606030114030f030f0409050a02070809060a03060806070c03030c080411040c03090804090b09130210200a0b010612110a03 77
    0xd4440d0194880c041c4c2520038083c0401482e81c3c0d8030010b841602d44d1000079658070412200e40d440d50a04d40a12802c401d580c010250403c0300307030400300749c6030f607010007c04008180581c010b800b60715040c00c0c61400040d01308e85100441d424040c5000c42e55880300c140902c540740041910f800d590030031755107880d840c1000d604550584200e0814029504041014064450240c158955110b0174540c0e00c4060ba4009441608480d006100500c0052040740c04d4032060710302994560346517040c0440450260081d5030001e0518002c00341032003030300707948400d1407078804d40240c4013800341040340f40c41159446030448001d07082e070b0314104035901c00f45481c0e0081000c00300c0500c2c012550100300d0b00e41d00007660140d417140c0350090f40e682c20b400040c1031044103e54010510a40302c03c206020f6000310b0b0400c3c2ca603071002070410480310040d030b8030306040c844001c01c803000d0031045440000091900d1243c0507028002c0e0fa021600d0840c0b00d15014410380941c00036155098520b030300b003540900041d400f4050b408001c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 122018696 1250 122017446 122017451
    0xc030402030a061d0106060207050f06031e01030302011a10090501050a0207091b0e010921020117040f1709031f0603140303040c051519200c030709021e0d 68
    0x340124105008580c0903140d84c444500c4200319582400e03007180c0c09a8007003c155048020104440d90711402003550080d0300f641c150390340755280c2c29091000c0000c201f40d0107050020400200c107050341581718501140c841070301000d40d0110502008002c0328071030706c00000968500004d022a502c80c00140075061440d004a804698461b1403850a680008107030b50701000e4020342c4210116480038a044840c7c4081c01e004261906202c6c1c44060b0ba800780107420b240701c0d03d1201c0303801103912940071050031044600c2c4a02d2181001d1078000018032101e00250f60802802e400c1503c1d00300510100c4400d00070040c001e0500d4054004109202c1800790010f0700b41903a65440040072803a0310040d4000814504e02031a076915240c9003401000c1d040f034000600801c816050700c143e104100f81221081e510400c40f43c600e44004100407a10f03800c1080d60001441084102e1a04a200011b035042000004805850810342c40c0c000032400c0740250b0480c503601c8030101042e00b050a1445009114618502801 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 122019946 1250 122018696 122018713
    0x90503041d0f01090c2a12030b12030301051c1a0f0118060b040b0310170307051b0901060804150c0503060405060a080c0105180d1103150f0c03040203 66
    0x1207494200c9420020390400401e60030050311854840c03805004d0401c0710030070024600e030010300405244a003203084050300342c911b10341c9034141c807080c06482c80b1507030042c1050090702c0c2c2450024043c010300143c0341e0141d445480300e00210071000c42a40c2c144c1d030b405840520f8440802c00d0603400810480415200c1c0915032190300c0d110102003045a11408600c200c4441a501d41501030314030080a03840510141c0ca0030106200b01601d00044500301d601d03e0100326101c2c0c541d002c01c108084410381c060b0000317008079081400c0d60100400940000d44c01130b400c0d68451052500d4128502640031003c6500080c050018091580141c6109070807a01035032002e059801e2001000e0101c640c1c442c00d050115401104218951600d4041c0c1503201000391002e00c0617501d400011a9102581d02c0c40906002d40450394684010441c0080074000c42c0003403140b19a0032143c102104c0400c2c0300681703580240900d03d01402089002091140101e1240b01034004075030f0f5145844c21107810242040340d060243c1b561 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 122021196 1250 122019946 122019959
    0xd0f06020d0b1305040503040306051f030c08070b121303051c061502030c0d2003040b03040204050117030a050a030f02031611160909140a030f090e1909050304 70
    0x103440358005500000810114810410002c0c3c0920001289400d06000170000069400f01c2642d0450b070b8002c0010403145c9540b103c100b088a41c80400c0359103003030041000010f218040b07413600c0840b031440c1c090712003170b64440050308214410b5100c151810611480440d070010361807583d0800c02030203803138001d0a0012501c600c801e50300400310a117400e16158207051000500c40e05952101c02ca0600095142260340102c4030b4491110201444c203000d03419201802e524002e04032141c00440e06000d4070341e540c0d00c80b50300c0c81c029041598164043c034540800400c0051100300000e0900340d084000b1810035580c224201d0300da62044484004140c0c4520024880c42e002c0d001031801303041c0150300c501d210244604010030306605d2003010038190b0700c43d8148260700300c00ca00d003013400d50340c15030004540c052140c10b018507100e465100c00945c074440d0800701004d040c0d211081401c4a6444e644441c03801c0d40d202c1d14941203040071380c1da000c2080040060324000c03002c03e510008800d03100d5415207080c6996100c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 122022446 1250 122021196 122021201
    0xf010c02061803100504110918030d050f090c0109030809010509060f0304030f03021c05130206120108010506010e06030a020703030906061404110a02060105150408030406120b0406030b060d0f06 85
    0x380c000c1111901c9200c81d0300b00380b80c14000034414500901c0c0030001441c040d100c4010502003452a075003e00800008100342c0c07401d0310305400700416000101e82d40c40340141040801841c007111102c201480030781c082550054080740000e00224140c0d9417901440c1552600302c84d981c8051442410f004c2d041000d10619101c0c24080c050f442c9106c18240d840e46014140034200380c0550a0050400d481040505040d02d24400b8141400d015884e00083c00d907078a1024101620348502c0107540703c0350205604c4105190203407900d060b110210001d001c980c803001d006641e45051150300e164444420300c006110400345034040c0003030500038600440c84032807035207401c0204c64068020203850341c10945010b48504145c020420200b5442140324070744004010002d45901041c011380e4401c0612078500707440031b0604800c0e1405092a03c003a20381d00c1c0d65616010301300500d10040b4049103401c101c0002d501e850b03d031040d0b1084903000700d1940550313500e8074108072101c540410115070400606490f24040780091 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 122023696 1250 122022446 122022457
    0x60d020d05010906080606042a0c02060705070501110a030f0503151905010f0804020f0d02060f0a0804150c08070e04090605010806010e0924041505090a0c090e07050f010c0206 77
    0x41c0f4002032094200050a0700f070001c01000f42d80903900380012003003c4841c485000845040d400c29000c04201c8008048955040d5440007942c03140002c00d601060000101d551400c81c0e07002d0b00c60980c20301c03e0140b101e44503058001c01402142a0358002c810080c014801542c0c0b007042e80940440311180f21000070004840100231124050100c5818051542c019011038040c181c0c5d41003071803085c5881e50016002d0010300801070702603607030100c80b1021900c90206072040c0000b03040080340c0b11102510b008100040407174003510b50500c44003080840503a188148110510b0701d5440300c5955854000c152500e140100b5142d41103a61820070b10b0110341944a264045c084050150440394504500f0003c4070001900a11407a0030800f41d0440e80b6a40300341480d100c2c0b00107440c0e08860307a0369003049042000811074a0b0030860902d010411014000b166030140e280c42041842480ba031205070700303403c03039014005040c10790317200da0001d103d00e00d030440c1410041c0c203051410406651295000c900e164000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 122024946 1250 122023696 122023709
    0x181d1e0601120507051318120e040e0a02010f1209080903010e010c0c030e061606050601030e0d020d12021306050304060f020310030219050306160216050906060d020d0501 75
    0x20058010001605000c95070040c004200c0d05948034045403100b5407104090300c00c061003034518a58405400380c07240c11541d5440d0503e00141c0a0381154180102180307942022200000e5018204051030301e45480781c1000e020911000b031140c192145e006607501c00d04c4404074014070694108140c00c0744014050364000346d22035050151288800170605013035031242c031002e001b2a41040d0b880b0480d503600c01080240300760145418140c402900c0f0105107944070313010343c10003582c20009111042c05900e400150048000b030b43c0400c041400c400ba8981c0712540c6400030001600219100541c03244039039515250340301005c100602e1b0070408106031402d00d44981c03004000c508040100700501c6810b11a00c004400c03001c00030341c90352030504420402e00c00c3c940802445080020400c040307200407040340301c02a0101034100e0300541855002c0c1d0701e02494150701c94006106450680710480c804071003403012a4006402172190751260303810010185c0210040001d0140e0a1041040c00c0b4480d02900b4002d099 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 122026196 1250 122024946 122024983
    0x3020f030c0f0c0a080a0b1302061306020d0806060a0c030e0907080403080f01031a04080c070b0409150e0109110c0a1101092103031505130b040b01020601181d 70
    0x40d40b0706090705001c50a0046885000f0400c0100f00d601700c0400c0c40444c0c19405030224010343d5501c4040c50103074001c40d0019422046c003082400940c0300d9121060155030064003100e900520481c0b04440c000403c0362040d400c05800c3c80b41812407400b490410741c2552103810312640d016075000114078504403c4900c41c00140088042c401459000740700340303800a0342803001c5406503045856902410b505a07004002400d003000c009410710500c0001c2d034850034a81d03800e5034001540c80004d6400c0c2d405c00d0140f0829a031a00780b00b002c90913400d0b11030358221004206140060780c64208010020981c6004071549083d040040d0070a54074107000da00c02031845400500d0106040d140010a8000d940d08102c406502d1101d400340b502148250042103540e040c035003c220034110a002900c4c000762944025088100050045079034002c0c3d40041c40c00da0002e403402c00c503000d00746004981d645020311405507810745c408510300c0803104a8109409441710b4492500e8400d00302058a03242c090b9007001d035400d0702c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 122027446 1250 122026196 122026213
    0x304060506091303021c0507080c0c030c0406030c030206031f0b040603050f070815010504090c02010504060b0103051b16020904110306100614031e0405070816030b011203020f030c 79
    0x1409590305500418611a081d11007810b9039000b0796241b198011005c03440b44030f20b0280c45600d10480480f80c05a0b440008140c6031b140740c4859039075920109115a12074041c005000c551750905100e11000c6030b40100203640c98520f1364082c00281c0d413015040ca050102508200c08004802030907801c028110700200ca81d840f80380c018014216040a02403c2803002076a050005050313102e0011034014980e01401c0b1100c16011005995620441c1e103d29203440c2007203000e015843c0c040d80180c2c495070240506000030341200004408841c0101c5500310385025005240702e1040c0d00c0303805442079041100782081b41c1003041c1c000585a0740304450455000c802c0c2d20f210202810103100e07450708101e50081071101142010f402502092244100e8a6042c40100010700b01b0340103060003102201e43e13a07841900906003400d0858488080707000c0c80306140700e0916880c022a40c8158484206c80d00040132418503402c1820680b640000780c030080d01144607079000c61008250900003002c10030f0110009000c0c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 122028696 1250 122027446 122027449
    0xc07030b070507020a091a04050a1d06070503130c05130603140114190609060803270904030309020102030c100617060606031825030309080303071e020c060304060506 73
    0x680d00a011404200040c0589401038403950308800681d0884c1c0c4010552000c8030b081c00540c441101026a442800c000500c407048006611003600c1403c0041c1d04002c030442c801c000d941d01c0c80309441c00400030300100002098558007149145c00713540f15020240420f03907505c00058140707031900d10f9000b1807a03881d4410010000c80c1ea4a00b141c3d0000e8000a0140002c070300041c81da0828000c05107041580070152225840c0140d5100314050a281e84e01007244a0b1a008081da4a070800254002d0100e400e0003510141c1030246022120140020099501603669503003c42c064800e01074205c3c1907100c00d0200c000149400e2000b44407100001c48005100351030180456545d40c02c090280550b50824014060141c80e214102c80c0e0114100b09218024010012801d160107580c4801c17003034000303404064900442000c5d020304d0480e40255100c0c503800f911500f40c19220b10041d596000845c20400360103e5044080c10324000440311401647c0c40d403140720f408100c041d071044408684456507074003001200e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 122029946 1250 122028696 122028713
    0x2010213060314010506031302090a0203040506071106070f030608031b0d0504030b130c080f030d05150d1205040504092405071205090c040c02030306090606030c0a030b060c01020c0703 81
    0xc01c0140341c184404558100d4841c4811010301946008100010008280186041d140d00d462070b03000d05508001d240200c4000020740040d10115164003c080100701240d209031401c1c0800d680e024081c10003900c4030407082c0c9880007121000400e00d0b80b00d59002846800038006401c91414500504110400e10030919041c641c1d031001d09020b01001340300a001151400c1074090303004948c0340030013200740900d0605215403502644080070600c545140c81c0010a004000383c0740c8003a4105081c050b0362250542d01c20341c8089507102c2c0c2c0d0400a0081a400404c455988495000c002c1d41440c1c3d01c1c0540343d40109007aa1940041a100b1440b00308140e8106084945080c1c00b51044c50401c000a081c031400042828140180d000c00c46038807a0b000c103071058000d1250a0b1540c07002031041000074020000651a900100c0c4c0c0e040c8525100f0700015800d081c903004aa00c00d991002d40725282ca00e940c107041c0d00404090500a41041003840300507143c0000348028041902220014104c031461485d16004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 122031196 1250 122029946 122029949
    0x6030b0a05120d030203060a091803030b0906010c080901030917040501080f0c03070507080f0a0e030f07080c010513080d0c0b10031205090f131a0316030b0903040e0702010213 77
    0xa841e02214a606008040b4050b040d550f0319140159982e00c602d000241c6250341c68100c0101c992030140d54869100c1001082c001c00e07840394806005100150317040145051007207928901055100c100000002d20500c003c006004050400044d0186a91241205030b549a4603000b074201000400b44165a001200d2650013101c014150000e40f601c1c0403c403444d404090103a07001e1220100300d5404122244003aa5030090b000514682c84d01105140200324059005416009024013040500307080e40c0802c81806480071070008180c031032601c6c001107840768002c0403415202c0482c00800301c2d511009200d1142003218907030359102d441255007400000c104014010344080045001c1c10800034500d030100004070462414160b4580d0420004628000081140032f5401301d0071800701182c04089038400010751404c8140b803407010070074109140e0b0b941840c4620034200b1240b40001c00021b03008101141c0e000801c03409507030074142e0700c03c0c2c10300e58142c0942d440000340c3d4011603d03440d100c2c1500389000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 122032446 1250 122031196 122031199
    0x6050307120e0a0308060a03050105090105040227010b09030f0f0f06010e010303090e0406240f0801021606020c010b060705010b040507140d0c0e0a030b0f0109090506131a0106030b0a05 81
    0x1181101c694001c030ba0380c0d1443c000003424092118001000e0b0394901c50208010368004009024501c2c00314140342c000d100880f000c030320800b0192455000506908020f81c0801000e0304106d5859007001e12004040d089045556454854000b01c01d000040a00c0001c1d0985114002400044d10740c00040d4140348050700141d00d1980e03210010130100340d2011000089030303500200d001080e184d9080090181107040c00142c0c80701075514414448298141124040f151a80303e112100341d00c038505a0300741d10950040448150549526901051140e0b00a00342070018800008080c90010302088039608031030420b8942d6555400303c801c40b401e05000320769006507545020035141c84c030f83c8514076187c005c070007101005030b40d54500410664000c2c12003d10090340208120129540c03403901c2007039140c0498070030120ba0079407000069005a10700135412119403010250240b50b03241e410031261000303030800c20361300713060480d00c0d00d103003548140ca6150182c1156030700880d98019980511000311041d0344090f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 122033696 1250 122032446 122032451
    0xc02070e13050304060503100e0c03041401050c04050f0a09060b120f160305060102010e300405030a03050a170103080a0305090a0203032d0f03060a08150a02071505010605030712 78
    0x128000b4001004030340582e16503081c100d481e6101c50603031012000940e0040402c14000000744080740d403c180180d4481c03489028211600e022060390b580c00d87d001903403511681d00c010710007804589402c504a05080f6000f60561a0303255480d04554207072803031980b25a401c1d140008844020f4248541590b500aa20040070701140c10962202000400740c2c0040d0320805541d0030100d445a0b100390000c0e45030020036002c544880440a6103040740d06402c501d0034126865564038030312078002d89000d8800300da100030050020419181c8041d107499110281103400c0020b0202c00c01ca4840c000d801640c0614081c0c14582d498035143d640140440f8400f61841e410f551000a4450059400004462903141c926003440c0c405071408600050031404c05c01e0341201d462012402c01c07103130f0403a040654850482190f0452605541d020000e44074a48088080c0d489104880018200101070300181445481000e400008440b0040001c00b110001c0e004079000030b80020a1042d0b00340d01142c40706aa03688130a04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 122034946 1250 122033696 122033731
    0x10051806030309120a060501090c030c03052208040b04062006060f060906160b0a1404030f140f070b010608010b040b04030204090212100501080d0906120b130c02070e 73
    0x65603d0190402c91440303080c015101214089003844505902d070b0b40024103204950b15014034902a02d021007a140c000303840e050001001c0d610030300440e405200254403202541070b0201542040c06040141510b018004000008030300701584018001003080d60f40300ba04c00c83c3e1204a8045150090310070102c56030102c0e041c0121542c071980000990380f0220362090351107080c0408508940210200c980703c80440c00d0301e180c103000400401610817562041c0410070030016044410005409440141c00103c150f88034244090082183c10406000154518101081c0c121520f1140e400000700316510800740c401040801d8124100f280034008211400e0304003420840580301c240100d00c0041e01c255241c900d00386c290b441c2d12080c0407201c22f581041e00d0148100b400ca00001d050207224a202d10f01c10510fa00c07058a00c80e042000030b42c0d0a81d95012807018004500030068811b280b4030b950f000702c000300c148006481604c200b043c2d10b9960f1b005010141c2c94850302001e0b00c0d00082106c00c03102160f055 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 122036196 1250 122034946 122034949
    0x11130606050d0e010e0706110616140a03060f080307230c0f060f0c07151815020c031b0f04020909011e050303030103080d0e012009031510051806 64
    0x7075680100346503000240c800003c02003a40901680440c1d4800f0b8024298046106540b10740300510010180c800c03247c0ca6124052918842141684a00005401402c0b03000350402800d000308400101ea150200341d690300c421421200c043d15600460030f550000a0b03030000c02100e882c445031041010340b4035106260b17400c0c0001d600c49010b024154490084000c0a032a40e60f690741c10340700301c00040f0011944403840c01e103610b030369143e00c0c0c0a64158405140000c14690b4410b85943c5090210300c50b0500443d4a402d4104900c461601d403243c041d4010102d108219460030031170a0b1000c1e414103c994040c410850a010f00030303083c0446203005900401c2907401e04d4485200290444419511408078000349800e01e228020043d00407681c140000400001440070b15806424140101c02040104606820345a801c948903c411880440c0e00380c0c0300c2031100c0c915a8042c0900c45000303419030f4601100d03000b1840c01404216858180b04c4000d4600340200d081c060b003034204104e403c00c0d90052a050400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 122037446 1250 122036196 122036207
    0x20106060801091509090813080a0f0222050a020301061106091e0a1202010504060f0e0a0311010f02210f07051801030603140a0b1b120c040f0311130606 67
    0x240f0300b02c40e031622000c41c80302c0400d6105000a0503104000c005403655490007402e11b901031500d0340701d03004007110003143d201e0f80800d4582e4000e40c0582044904203940d424881c20148202c40300d0042040710880706001c100354010948100543e42c8011307038a44c1408006030107044050781070303000d640c0141d01700724201c0d0317001901800240f045901e001d00340581e15842c81c50110140c400901c0c041100c18030401042c1c05401c001d014900c02c14090281001c5411603000300c440000c44000ca550140d407c2303202090040340e134010000441130000c21905416a09841a40d001d04101e00216030508101c0c01032000340c00030941c00c0307104000410410705001c440100030380290400e400c00d0b0555514140d6140e8043e50029004503444002114a41c004034803254a0f80b02c801820b50b01040028002806901c660401507142c1401840680c1000e10000c421081c0f4400101501941d003010080450000d801540c070030011440780760b01c40030001c0f001c8103001441320880c458004190415105110450300003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 122038696 1250 122037446 122037449
    0xb03010e01020412140f07061206050d080a030c021921050f1b07150f0905010f0c080904090606080607120204050901030219170703051908070b041a15010807020106060801 75
    0x5143c0080b917150f240d511038108520b002c0000000e00c5039120004070310b038210101364805000d98908101490f03a03002845540d4403030300e00c0241912020800a216513000740d2002c280c0540d40e104079030350720b075141ca503c0344110390361102620b030085442c005203840f9a500d40302e84800f80807450980c0c14000c4003540b86089008039085003054859028000c001c0b5001040158010840c072104084400c00c2c640c006895000c0c0074075200001000f0388030104040d405030302c44000004a694511038603181c1915800e84940114090960080c2c0329400c860110b0a60300a00010b45180409840c40342030032840070b0120f20607282c01800c224018001040150741d040a220b04580d01981c1d1510f040c2480c0215031500c1081c2d400c0248a800912001d109002001803d08140e0348a00101c3e04505190105605103569100c0010b01c2d0344000c005a100184081c14400d8006218800e1420410190380c1c02c1c417034007102207c6001c4c000303002c006100c0b41582d0000c0200e4012503130703000030081107051420040001e50305 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 122039946 1250 122038696 122038703
    0x60405090609040303140c0301060e011e03180f14070e042f0a091a030a0803070f020f0601081005060603040c15050c01050906040b0f2208070b0403030b03010e01020412 74
    0xb000101814003e4024115100c038038400300301c851910115048050b0003e01882000500c560400034855005a958142d0229204034074242c01c0c065440c2100074082112101c1c4580d0000030302c900c006a403101c1800850343c4102011490800304480440c5000300691024689516103418840800c51441e50605200d403c01101800013407600e024080b821740c41e045054002220071303c009903032040d071340c084551419140001110520f000c4100350381d0f600c0c030300000f912084040002c1510f682c0510356518000070240141c9640c81d40b910103003814800d00346c0c003030a469040001d010f2030303004c164440c9903848141215032a0071030a140e103440d01c14826500910700a170490f1008008414010019100c0040391000280100d107443e600154a54406540c202c0ea24810180800c19003281180f18074880d202d00001c2510b00c01c48003800750711000d0700c000d042d68041000c101c2c28020650588200384030b14000e85000c14819040c2c4107050031038001141c0b00c08541d1052100f449203410810844406682 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 122041196 1250 122039946 122039959
    0x2a0c0204050606091305010509070c0b150d14032208030703210608030c0c0f0d0803070513090207120315060503040206040b0318010f110307050a030621020307050604050906 76
    0xd0302c0c80418000c0c814444156070048503890b802492403410380000e4141d4000744c52a40440c0c4070500d0a840e0807a07550401400c4142050001d4020700072040400900b90b4000d023a030b503440e1110f8462290f401c00d00038a032021900000b5540941000503071003090b52030324004a4955540c60706006070380304c0c0200c00008040003c1031200f00da204020030b40c170300036551410008008155842011542e20b92200300171301031034000c0480d2010545030183d60640e00c0b138000b4042c40000656696016010b030310060900c0c0034014148583c46114684464220152200100c01a42c50000342040000341489503071540070141070250501c00100341402030400c4034141d003441600e9450391b03c0028501d000d203400c06a0000300100400c0700c2000b4400c481d402c1041c50341e0082183d1542011b94400b603500001c11400b200c28104042507500d8071a01c0241010001403400054558680d403c9412103110149a040b8400f85001c0b04429480c061096000030841104d01510301071620001c02c074001ca000308140d202d0003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 122042446 1250 122041196 122041201
    0x5101a18060a0302120726150903250b06120715020c03060a02030103031101021303080901120507050a02011523011101020703080a0b040207171803030d2a0c020405 72
    0x11a06410302001c0c61307000308804115040d442020740c1e40d003120b11901c0d00038402d40b03208480e01035542c1c0c854011610090302901c5485946c07105c01041500151405050348420480c000613840100c01d40c030342c0400e24450318000c3d2680345c100710385400300c09884a0321416103403860491206002a209040780d03d01c04010140102c000c4007070b0f007869001e0700d0440c0c05020311000c0040340034a9600030b606882c8aa01c402c95400501c121072801c138050440c8501203201791031020320110b80f606029240d0813034140b4000961b25104c50800054075020780f074541c0414004039104001c16028000e43e0300d005504000700c0481407070700804480e05410420001c20744641e0341542d60b184e910402400504110080082d595550207140003050780c0812943c9a264610b81400c1500030716060003180c54070394116100c034508107030407140342d02c0d5940140080d00790041d0980d40e803900368400f800500340f601038041c0002803044000000400b09890f04000620f0010400c01c1c4040c174a03008041031407007580540d800a42603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 122043696 1250 122042446 122042449
    0x6142715060f150a020d0c08030a0b060c0d080a0b01110c0d0f0c0f09060605031509190f091211060406020703030605090108030a0e010f09030b040501021605101a1806 73
    0x40107402c07125802c82602d14240c124410007a0040103a400140e089a20503a850700b81103c900c550064020902d60080000c80c1e4000e140f078110000303011000340118907141d02212214507000c1920400c1000c10038038420840310030640e2040700c007200c1085c2000250710b180300900e152a40c11500c4000d100724030b11503140052003200032550207440e51001003025803540f5610b0f0305500300b120344a149105828214085180c900ca00280c1e4000e11100204007600380ca2001003040c001c40040200c03608090a1104850800d1140591840380c80303180c20029148000d4201800d8003c05610000184505070345100391150000540640c4290490401038640c05145800c034054002d030f13802654050038010022420140200040c81c04500f203860f4445660510001541c05c4441144820b0200d500740d03008102150040f010554868409c00005140001c0302c0841c5080009807901601c0b582d0043d81800d58000981c82a86070680e1880c0361b130720b06210742000164200c0004204400380c0e44040000c83c81c075 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 122044946 1250 122043696 122043709
    0x3010510050d031d0303070b0405160b0a0f11120a030b040b0307030f0c05102007060509011b0b1e0106090305060c07031b0510200717070614271506 65
    0x581d0402006c1c0c0b42d03249210b00f09407292200950702901c02c0e000b2203005090b8040101c2c10002181c0c400d0340210b0038180c1210099503410000d90301d0005001c0301603201c0542c0380f414440000c0c015802280c19441d4044000700504036000c42c044035015a1070701028642d41e9074005005400c0340e5018584000c28401483d08110004050b0710154014040f40305c0390140c15046180703600c004d10b40740340c010301403002503c0c540d41c0c40905200d000c000c1041009004410752140d0300d4002440448218511200019994950610000c442e00c00343c5803d089182003c11900c02203241c018100c5150440245003151501e40c1c440c00003804481040350001240800c0502950b00380c800c8040391134075040e20041d80d04000c0d848109020800e0001c6140030705e151002c002010f0381c003841e617400d100081d0030042e10fa034030311044083e0400c000d600301c2070a03c0781000141e0345000b104403411901408020a00b0b14000c02403040e2542003402042c0000b05501804500c000200c0b40d034454805400140e2544500020815 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 122046196 1250 122044946 122044997
    0x5041d01020a050403111f11011514040c08010f060503060409080c0109050d03140109020a020f03040b04030302010606080105180601030b03030711030706020606090103030e01020c041a03010510050d03 88
    0x90550020550782d00d00d580102c00303030044900582ea01d01c20414207100b0010750410102081c0c7d44161200140c220b0b40b84031351110401a1291b030000104803440000a248806490b802440440c000c1c1ea1120f19608083c011500158118240214254100020f4010340390140c01144200400480080d07043e0350b594004403c0d681d003005602d5528481d2403010740c0a0400b402056440b40305a0b891126054401d228219071086600c55018440c0d00300030080d00650b0015003150118491030300e031a0666501400180000c2c2501060725603541d10314034001c3e094650941c0080b090101c0080100069152040b071101c048035480b911181175901e107001600100502c011454142c407011a65201b00002054100d080791300031030407940429602c500480e5244001c64900313070820341f020010000a8001c1e020f0b40d07940681401500c2a018104003c9400c6400094100099000320704901c9079904080c071038182c0240c0c1c800707440c43c2e2180c100004907805d10b00d5006d00404001c00c070380d0251111340c0196030714103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 122047446 1250 122046196 122046251
    0x21060305071a0f18190620030903030901080a15120b010e0105060706091704060504030c050d050c09090a08030f01060f0c03051902070b0706090b010905040c171507030501081002070c0504 82
    0x1170503911000010032282a001040d14440d051034404004044008182c40d00c02c680140110720b4000c0740302c01150702c800b01510500460740c941d42c3c000c0c510740d05421800041c114102c400c1410302d8440c20301842c0950182e20006c1c1108100c401805251150300464030030326042407000c176030f00b8807901e0104c43c0d00e400b101c03108a05c0740700442e000c00c810707a0004c01881141d0051080c000219158020400d1301e04109100420940c80b40c0c8403000e8606103c14500d6004400005580c03003000d054549240d10f0340222841e400b400303519801800110b0b04483c960300f002d83c00d850700072690340c12640c001d8914800c440c2d194403100b00d41c541000405200b00a25400f0300a0300b420a40c84030414503050000d0415250220f8861f1440e50006c42e841d126403169034440c1e60440407281003e45062014271114a200760802e19074084e5100840312381c82032100f441e0040903a650001990342c5401c04140c00c152070400e100604600402020340450b45048403503080c3d031822280010088550300c0400c50385440b07200e260 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 122048696 1250 122047446 122047489
    0x1b05030c0106080c010e03010b0a0303080417040603020306010f080702060703150801060306090209070215060402032d0f0105060a0801140d0c0602010b0906010306120321060305071a0f18 82
    0x80350418001c070300c2c1050350800703032506d1b030500d61110201404d03201601043c0342c00503040107040020901c101c1d03100d80c10134082c4034200b889200100c5994090352183d000500406d40000c10b020b6256417210014829041c58600400ca60410040c02926040054824001c16440d204d02640700b10000b452100144840402040119502e1400c000540101d030350603803150000d1400a030100340041451640b014112980c24842d41c1c81a0401c0b0080d003004e8003200d926651800440030500703e1103076061030b1a02c2c000c00326109123001204196036800580000d402604148240b006094021041e941500c0b4942548904082c2640c00302d00d00c800d09040180038100100ca0002e00180c040d408401045410f0f65039102c19a914801075040d02d900303200b010070100d032024650000c688141c10044e80c181060304040344400301028520241c070190380040d1030030b800403030040041540f01c172403094250350400b00e6142090400168481700e4000c58034101c03400758281921000a9440c0048000000e0098010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 122049946 1250 122048696 122048699
    0xe01020903250b040501020604120e04050f060a0603060b070303020d2004140906060d0905070308040923100317040810020c100e07060311120106020303040201140403031b05030c0106 80
    0x601d81420314a0304402d0500b03410784012900c001c1c14003c65041c3d55042e0014111500d4682e10f06100b15824942c40041244504a400840e41c40f8018180a0001155100c0301c41c1003000c00c01261600680c010b10a01d4034110080098507215429513860a805041c0142c40389914200c9a001d400c0a07071543d0502544611800a513a00c0d4001034002d6482e1030000c41941c1062605004c441d401c00d945140d8000c801f802000c2d40c4d10155000005014820b01c2610805aa240c2c1c0303160395a00503070030120034130ba110040200345008403034140010305c2420300c6614190420081902c801c4146009c0980b40d40251000e0802000140049400820402003125002102c42090000a411501001545000f170310400048042c4038022601c0c40c01005029000c8a4508401540103140c00a022960a42c081c8003903400b030800c80201c24000c0041381c010310b80c2d0b460a44001001da181268408d640b403070301484140003095002c2403510014201400003007000034070b400c0c001d2542c0500003001c1d080c8d6081040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 122051196 1250 122049946 122049973
    0x309051c021606080c0702151c0204170105041a0417070302060f01050603091f06050301020f040503070609141c050109030c05100c080609040201090b030a09032d030e01020903 77
    0x41000b030a1461140c4010119203a001c2200c10030700548603032501e03400c2400090702501d0b00038040611290080411450b0090f0103581c8040d08c0744d4054180e442540c04a01000b601d0018440125041d403410000c005610301aa5007040d0807100740c1e40c030f04189407814001000c10589900b908429000039902e16114131991800075602c5c0383c211900007040c1039080000507181000020380c0c0c02848120003030042d580e070106c5140c4420350b4002281003001c1c2c6aa100140d103031000e1006100d1884908905641da60400080c1403a0822070f0307101608201c0420001c011460441c03c40c869589021140b409422001281b21030a00c218134101404a502e0700084204258200700c0e00740c05244aa01a203000600001d2210304882080c45031501084010000603560320300441420307401441410040785607a1241c00041c115002100c03c82d28803a9101008028590400801c00200c0d01d0009000542c0c054030f120b40c0d0540360f2000340d080c181921003495000b2004290150f585140307000c3c0480d5650041c148 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 122052446 1250 122051196 122051203
    0x150a09051507051c0e12011d06100b070c120213060801021201050303031003061104170312090d05040501180506191805010c0210050c030d020702010f1d010309051c02 73
    0x1003045411303105040d410641a00110100d409281040c1ca8040b2210310300c2081c0944000950240512035584d090b5a1886000b0300040b25120140c00740200214a00000c007210804510f4202c182803103403d119030400600218090015a030341c5d5194203928404510208401107114843c0b01d103c00e00349600442c0909055003d400b580700c0d0801c1300003490b43d0310401e054583c4003c1d210070010000306034062000c20071580040c289a007500b241c4503d05070f924010341000c1690600c07040c199800004600c1d00d4156820f01c1583c020000748068203804134081000b41c054400c6200b07a5050010f0900fa1300c44203502c1400c5100103001c0540b0803503983c00d8800b034140f40032404841000105d04515408901d0482c03189484060b9501038582c020390403015000c1040c43c096031034088041120410400840301c0c400d002800b00d09656003400740e11101180700240c4600e010b02c50503400c04c04010403102914250301900b8048150a080c00545c68115060160a20640301c1102c210201103107601180d070b80c0c1c0003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 122053696 1250 122052446 122052457
    0xb06070807030f0c030509040b010512160206100501021c0203091306060f0918020306190603060e07052110030206030f04030e060f0406050f0409050f24150a090515 72
    0x381d41e0340f01c60748100102030350942203046000d400030310305204030301050815a000d1903020704141007480c1440c080c1440d000002c2e0381201c80e140e810300c20406100c0c02c40d40401600390804054005110860b06080000f503882c0110042180c041c0000b11070126036600070700450f1540480a411003942413003000103140544132a11031000001c1140b4000000365228500d240199404c042d444c01425254149800c083d4102814181c1d00c00d28044030312041508807c2c4410090429443c040b400364909100240c44640040c105024040200310a149203010040318040000204154088036243d802d81060320011030341009400403800401c0c00b5040c234140c000c4030310462096481034061090a011b00c081800381041039200e40c0c038107002c2800381c1c03800f80300602030058000400c1d81c00d0564902d840404d640041e030708540d80c0c0041d0740c240007406840aa114400d5950710501c9204d03011910003182c8071005400c1e140c04c180304086600c001c0daa01c40d91051000f0200184581c8010448590102181d40031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 122054946 1250 122053696 122053703
    0x1202010603031d060d020307022806140403051204030203090303070c09050c0405011d15070b06011d0a1206021b03040602011a0a0b0d0b0301050c1308012d0b06070807 73
    0x101c28140c036007a40503c3d041424640c002e4082c034107110301900880040d400160005055000d071139044107a00c09540041181c41c240076481c04101e4150307041210440d9203c4c65202c0ca10040b00c0100b1000c07075004000c0300c0704c2c4581251f0400396591181405ca0542c050140126030500000900409000c50b140c418800d481a81208000c2c03030303d564a060040d0320892052501146a96150304500c442849200c1071064001c3d10045051286420710b000e01d0f8405201142e902180c002071202d156072080901c0b15001c01d0720810740e68a05800c0004100b0407191040d800300c00904144001040f00780d80664100340c280f01c45901c1d205503200c45050b144d410500500e80190700e40781c41c0700703d1001003010034940140060501103401d802c0c020042c05940c4111025101c007030300d5406009607a1802d2242e10700c40d601c40d0921580729240800b0b40340456206a0009c01168101f40608902d061030040c4456804a18040c10440945510403403000d081d01c0c1100c01e90009000c01c80340d041c40b240200a1041911 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 122056196 1250 122054946 122054957
    0x80d140112050d0f02010204050301090f0b1e0c0f0c0304090b031606050d0203090f0a050106140a0308090f010c050a0c030308070503070c06180c0b0408011119050a0c120201060303 79
    0x8a4840c105940700c000800500503a00600e41c20308a5406001c41e1104d45034130380f00141c6041d403954042420f43d01154812100b5140780f404070380c14418880c0ba081d4000310f10030303440c10903100b003c0718103080914003405d52590320000140400c4e61407d1003080f5550a030100050780d44503070f03540c00ca860040840906c402c1c068007407001c9880d440741c0c408810405881090f221681400036540040c002074100910785010b40c070441121317507280e106c104212145240f00702e0000c07a03820f0034000002e1005400780c1003280500b2907850140001910181501c8a503807007910f03040d0455000c2d00040712007424030395020740b0b02e00a042d180c0c0207011516007410262070198580030026161010b04a485100445400b80040c81c850b511000080507500240701d14030300703c071034000400b5103a1a2903d0b0040f20307a01269414800040400c1103c3c0d0030700910604004401c0b009041503411104003070a08a1240c00c1d200b0441c000441e00a503600a10f034055a15401010800b104c00254402900800c1c5601081c0c02240 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 122057446 1250 122056196 122056199
    0x80a0204061203301a0f03010c09050f040605060a050c15090a030e060d0f0501090b03190f050312150112050705041a0c0a050709050a0203040201140a0903080d1401 72
    0x2081d00311002c10a40d8541e840b8401401c916000c65400507030f03e0501035401e04034401d680030104480c0513941300c6021003800502041c41c3c040c1041000880310000c41c3c0203274180b82d29080c030320b5007083c41d220895005554084032680014005402071040f0703001640e20035400304010f000281d03c00041e1a507002000c040b03c00c52110951034191000301211982181d078821a03000000074400e5052801d86c0c000a840c15042c103070b88801c074000313a8a100d042c0030f400b280d0301d1004100c02d078154007031044551010b4005c0d1200c00c0303885106400c50046071402514030702d003145002040040410460340c1a2200c0d04440080341040202c094039660300c6503a1500203000304c21849405000303441501c1c080d01c00c90f00d03040c1c5450310b030940706034140e24000b120340749291090204920011043c45245a803903c94405010698101240300b822214094651510315105000308001070340c00203943d03000d036041200001d0b16506011422a2001d0f2907070001490740d0360104000c95038400e5034010f8a15043c050146d5449030303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 122058696 1250 122057446 122057459
    0x706050f0301050f03010e06011202091003080a08090a02030d0309020f040606080a090c0305010c090f060206011406090316060503161b06150314060a060501030b01020c09070216080a020406 83
    0x2806680142001188200010000c0d49888018001394181c06400400d4000009011504141d4240d0014280384500c1001038114030303014401e6a031201810300d01086150440e1911031590040143c001c003880b00f4007001c1800b402081021007512a4000c1c201c55200200003030080191007e82400c074020800203050015501d4035020710400c0e10419501c2070515501c00b00303288040d0054200545120604080100100f0828041c0c414544121344816104610344444808402910b074005801c54000b60014850240381040758030032044101d4810742c6603100c050029050401d1805800402413201c01d00081c9a45c0020143d40328102079010032114020596050f0b80ca1001c40c00910b800d004e09040d42c0c00028010b80c8401d8020291074058040c032030700c0e81d41e50142840c1000b01040c8560003203041101d907050501400e80900320a2805024070049400003039580c040c0304480f28840e401101c0011645807080010306451fa100d60902980359682d0800e0940307890707841c841a40114204080450341 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 122059946 1250 122058696 122058707
    0x7031514010504200a03140f070206130c05060f040b0d20070521190201021201050414040b0702160f1a120f0705070605180c090129090a03080a020706 66
    0x500ea045a203c4440b00008184e0041365005403002410705584000d10443c15240e895810300c2038201200c022100c1c20451001391912400410b44141c0062010f429070000e4000c45810046031350603540e1a480e0300700240301003498001d6070801d4031030720300219000f03551038503941004840d240100d200d00052128415840c640c1d01c80d02d04042c0040d0321100b442c030201084000303003e6082103807a00450400c1340180184001d88a001c00360f200603900401d5070b1045038840600d941c010101200d003005003100c1080c10810020000b00003514030441400002c161a0007400051403120007600b200743d0054403010b140c2c10b6003806000308049000b40c84c50400c5000c4848081350102030904012740300c15642c5074202c41507520002c0c442c00801c182480003000003007050007464000d00e03805c00c5409490224242c850710742004810403d2240901c00010080d0312106401c0010a9045011001c2c00405400541100c0c5c0301c4c82276040d401025071000001480b800320054030302c49603e94243c0e14250f5480c40110345 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 122061196 1250 122059946 122059961
    0x7030e0a150e271306050606070201140304020d0219060306080c01020601030f03030b03030f03241c020409050f1c0203032206140103061e110406030e07031514010504 73
    0xc11990040600c00c0c1c07070444160620074000701020040b505001c3d0568440a1007a20011048000a0a44800c0110034040c81d5407108050b9607480c1098243c0e0002080d8045007541003101400000c045025500d8071411100b1654000e00344d0070500d00810482e0708203503014070410300001e01d011400714490b40003042020054005030700070485642180c8402180207112401102816541d55003911a52810310103000c8d03440613003403c079450b403034440340d50b020680e00780d819040140c0b11000e42d103a03140c0c0c1c1c1403010044083d1a508906140013140b000c1402414805400340c100c0c80b85c909071802c034510005081074040074050604050440701441642d4900055501441c00c59004545c2c040301a0a0005403420600074039001c03511110f00001030060316800c0e007040c0c0c2c0c01912140511002260b100b40740840c8005244100308046880d10310880d20b000350300501e4101074441c002c004c1c200c03004100c3c10001c8d40e0080c001c1d580120140f0b1504000302050381c00c030240b45101c140002041c0c542480b8066 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 122062446 1250 122061196 122061239
    0x3091a07020f060c100e010507110a020901090e03070501020408011b0207080307020d03030f020a0e03011104060e0f12100c02070605040b1812030f07060f05040507092007030e0a 78
    0x303681294000420030143c00c404a01400744c440c00c1c1105400f15174500030843e8403c0410700000b03040c10714040041030142c42210300d10080d885225580016120103101e241100c0c949400000e01195200707580b070031889580c074003030819800410040f402c1031040d42304024603402c00c1c18406240f40b0720700040c1d8680685119a540a8001744001d0000d401c054140d5040c241c400d03c0c0c00140ca800001d0308008a8000121600000304545840400c9084c01d10806051001e21042541418039108004040311101c041c203500800b4034000b880c800307441d03400803c00c01e14496800c1e5165406032041070801071881d0030154005100d0800300052180c02101244d058485a0700c1e154a045005c4030b1821301c02a0041169801c02c0f0031803591003068605101400e4420000c4606507565001d44c24108d0640b02c6422600c0c0741c551078001800f0004000082a40890307140c0f81000c01d84c5855001000c84c00c00d0750241d0600341c0400018410109944201450082e03842100c943c11560f460354280440000c9075003500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 122063696 1250 122062446 122062459
    0x80d0e241303030203061903111011070315140705070c09270c050a060201061a03090a1502070204050f0702190209061c080a030606020f010207110105070201050706060303091a0702 79
    0xc1d03000c2403080e0020751744900054205c006c1c0c00d01014012400440e5903000b99510f02c010480b050a603d4100d01c4c001580d400f52500515040ca1034074081c1e2a05c0003403000400385040c0c1d91050420914036040540d003a0720305103110000c1d2610581c042d0190740580310846032682c000401082c0c0029600c00d01200c00386125141800c10240303003e0101205c030100d42600c0c90000340340002015925420b444000d00440d40c00480c029207002c850404125443d2140d1840d00d9007407003000880c1c280040c19020481e0411050b03c0400b00d50001d80c0000e12403440301035001400c00c002c01428400144180380a03000c00d508a0315040f60803002500d00003c2c00f8002580440020007062042c81c0015451107055008039907428840420b0381c42d8581a0700c00403458004c030351912420456180c05114100c034100380000203602d0310b803075a615200c003080c1e0882c100c0d0501c1004291030f000c2d64400c0040c1c50080303600031820011292030b41005808012036110341c0fa8030340004504000210180000e4881031940035225 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 122064946 1250 122063696 122063731
    0x160c0c140a0902071a0618010b0913090206030705070309080d09050f031902130b04020d1b05031b130302030114090c060f04051314040b10050402070809010c080d0e24 73
    0x70800c0c17001c0036140307079800800041964030000f8007440d124000c003208000781c0d0360b81408400340800700d1500b840b07955030b45240c0070342c1c032004d0303104e2104a0382d00518610708240d8800132841c09444507001600303d100700c2c1c49003002980d203081d005480401514003c07144503000c3c00c045400c02d65548500c1c2c44000c2c2d890b03005c007449001424000a00c1c7d44282d20300300f02086080440b000324049030040d03080350300038544850300002400c140940c07940c0c0c0e40005151181c510301d403100107401542110501c1a80e210303400126140002000603c2a01443d8020028070500d076048829285040d0151071031803160181c3ca00b400c010345015800c503080c07514481040b90034103240504002c0608403a1030a0710b51583c4407025a2110310496084502c10341c8074800c900e2a40c103005882d802a4170458200f0f50003980704120003004620b07820240c41018a007482d00741c103102150301d0018003a015080e0704d11801403d0041c508904400403d01e6a030f40c3d080c02c2c1348104180c08455140c0c0030000281d41a000542c1158803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 122066196 1250 122064946 122064983
    0x905180a060e07120308010311010c020306191503031215080705010809070e0c04080c0108040305030406051003060608100f0c0c0b040804081b031014160c0c140a090207 74
    0x20510b900d802a050f2220f041c0d444054411501c0560000c400007186071005004011050503d00d81c90340c1e00780380800801d80c00340c0c0800c2da19840038185201c8850394000c81601c406450300910300e000998002040515540d140c041e15054014008260003800c00071110b01c1e44030044406011a1240380042142920301001510b0a06000d00f1403401c42c00750210104081105078943c60003880070145065a49260003030050401030102c0c6003a040155020900011075404011307250010f803c1140000c0903110099496250752140e44014605402c04000065030140812540c3c11042c44200901c00f00c900000c1c1c40046805210000c00403d8480c985240812000e0b02c0f05503000b4824980c0354a440e464011480c5400200e507450a40b51507988046843c504062002c01d111101208090003600c1c129401d01d12192401001c0007d40c40e81c140c0d007088a0382c0b007204500c0e0780d40c0d04104d48141240d00d0301001e04552024910b0303103000d10000d12000841034598400c80300c0d080e8001c01003a200082040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 122067446 1250 122066196 122066201
    0x105060609131103040309050108100f03150912020c1206040c03230304270b150f0f03010815070503070e01120207140a0b01150e040c091205070905180a06 68
    0x214080b100c80d03a5114088003140c1e0b40c03001180224080e845100641d4503140005080d02002440e8821310080c001040000080001c0c04106070703540413095054820103601072000510052002900f8542002c04044040d500820100c00261342a0343c03000c00e03040200c40301652414107580c001d1680302498010804030b110044c110b410100b6403166594106800c07501719180d43c103c0d0300f101407071546442152080700f003651509014100408410b00034560400c00052040050302c200b841d414800144030003078007000d001126000a210340c14207840b540c5680b18195500c881c911240d94100740180462000d178000c5082d00d00c91810741d0f070380a40c0000500c004480b8021801204599560240200c1c00041d94203401d81e8201d1010700c1c020550313000182070840c2d0903c0c040c5c2c020b07012064250b50900303040354401102d404460302503c01007040c0203295012148901c003a03000e4403203561001211420440c2c08107905045408010b01480991254188614105c00d070401c0e07170b0a29407142c0000c0000903642d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 122068696 1250 122067446 122067469
    0xf03030c1401150305060a050a110909270304030c09090c1a070c030b0a0c0302090102030a0302070807050601080312060303090f010e030f030d020406090902030402011b05070909030c020108090105060609 89
    0x7900115100d107821050500382d0030315400460740c5401c007108000c203100040c4209507000b0064003051002c048000111411441108403043c02281c9080c001001c0034cc07000190001c00e002c001040412400b0007940a4490700240000c0b20011312a620000d0701c003134a80190410240c1041003a0500391500314590390341c4c208140d40c0246030405100100c0803c688034610b40040d40100b100301040c0c03030403c915800302c2d0900f0003140c05052047c008905a664004299040344003103041c01607545210f81081d41050181080082083c441d010006c50201004000b82600f05020315100b078050f05c6d004205520303800b800d5901500214030f07222070038456104080c074004190b00542a9455007501000c2c60b4155801811803421003900045c0401806170f201602e00300501403040700b142141000c1d40020a5649503a140d03014401d0100e41da40c041c000c0a10800740101306c0c841040100c52000c0c9000340c1140d1890a040e400b20317030100700140c016501800340d2441104024255813908045600f00190070911 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 122069946 1250 122068696 122068733
    0x10303050301050d0f0204020a05030421080106111e011e0e0c01050f070f05060105010210092a09060905010608090a0b04030f170408130b0a02210906030f100f03030c 73
    0x7029174260150322644000d058161560780c64036580e00d01410151611031740c40703101c4145200201c0f03550740b04582c40001e15055401901e404040d1072944d8001a1900e400140c001400007420070007611600d10546c400da8190494480350503c3c140c444100204031003106d0301601c1d00b40c10240c0300c000d03290b03c1980204013182801148500744840d540355409840044102125103501600060019603010443c41d07007c981e42180a01c407040c1240d564000c55000b01c00e2100101c26440d41050000c0c2039804a000604200e4004201c0030740d544c00201d0183c80d0038807580001c01c6240000c948641c1c00440e5100090b5008400d1040503180d0360740496200d40310000e80410401542e4500508000c0014464040c5008016140d203990b0040345028000c49190701c40c041900f006c0042441564020400c4007401221f09940380c0c40c079000f034410307240501c00c000304a5072203040081000b40150340340000c540501d50600721040c00680b035405088810042d0700020300881c0c4c01054000028103114010151400d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 122071196 1250 122069946 122069963
    0x3030f010807061205130f05010606020f010b0d0f02010e091005011d06070b0402040b06070606090f02190810180905010f11041707050607140c0102070f05010c03170705130e010303050301050d 84
    0x183d5840d40647d0070b00c0140210781c00d0f511040e04216070360b4100104142a418080204004000100001c028040300c200080400c0701710f14644007075a018001001d040c1d032000e0700c82904e52808100b1450300207114086c183c08103031801c54000300100c85807898a411321000c1e1146241c490103031120700728004000d004136440b5442d0080f9111035220b01020300032041c842d0601281e85230600c2c42a0090703c02480c0340210301881804001040c0c1e0314144000d10314240c0303080c4505151152a000e0303026022941107541c18002544a41015110a074013140b04517001e00c00030800e440709481710b103094840c1003000f01c032460b2043c481400411900e00ca14034100081000302d42175550b891002c520076421000c0d041e11011318809118401250074440849a00402d10240100f2410161100308801080c00b9070bd0421200d00300d00001c15024140d001500d0403910400041881c0a1900503c540c1c010f859040c0d840846d02ca00146a400c3c2000c0103040c0d80d4940c803240c1c01c40c1e00b0202407044d003c180583c00c0e5540751 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 122072446 1250 122071196 122071231
    0x604061103070f121b02010c020106090e0705122b0f0c0c05060d06030203070602061b190c080903010e0618010e060c0c0304030c0b04090b0108070804112103030f010807061205 77
    0xf01207207040c0c50a0905d680002c030749400c20b414041c0c00c5841d540d00c9108041d007003a2504d590707564041621000c2e5002103480e4044d401201d40c8144ca410070120400420002c400800c082c90a0b000d2081640e006d260703a550703403110081d05021104000c5c04d4100411442540505001a04e00340014090b020500c040001e0b11995940019161010952210025810980500590140901d06c410f00c5003035100310f491a14081d1110303031815045210840b410441008124001c221603442141c440e2079000380203220408040d00f12648440c000c0e038144007951031080c042040f205060190714040307450744014004076035030042440320b1584441e445412034007041101000052079a003605020b40310000c0400c1c2c445080c01d00712421100b40841003414000c045041003041c55000d46110360080c1d00c09020142001940081040c180d000b250040c603a000c0203050f040b0400340000a148110744006850580b0399942802c191120568010540090b80d04690800081c015802c80da4000c10743c1c2d584001c125 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 122073696 1250 122072446 122072471
    0x3c2403011104050103050c0f030a020d060306020a02070e090d140f04030c080c01021203161116090e0106050103090b0a0e030f0a0f090f05011d0a12050604061103070f12 74
    0x41e0141c610010703044030041000c1c005540c0c9032082c0c50303000b421800b00502d0400d0240d0301c103800340402071a0743c20403030300040e640c020070a06410040007142d120b84199101c0c071421b00060340704c0c051400340d58100c40a1000107803402e0000074a0805284690720790203c1c482c450550349a035a84100042d800d0500c0411002000441c450303420001001000c000d1700030000900f00090400140d192048509001403051140300442039189d04d50481d40f5040c580c025014003075486007040259404c0c1040c03580c05550000703c10102e9000599242c650400030001180c5643c019411108128806003081b001140000d0038503200d64071104540500400b1242071140c12000110150b00c03000c3c201c8001400c02c074180c0320081e00010070101920078070050503840340c140310000389110716031261040409400c01c0c100d0301c0c81c0c9414007000e01a080400a802809040d030078000c1c0c2c0c1c0c05c030645049401a00c1c1822521103611b00394241c03401034826a45d44041c7d51083c84084844041e148801402580d8640e014a0741c0e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 122074946 1250 122073696 122073701
    0x20402072901030507080a08090103050702010f0e0706081b04061101021204030903050d030605060a0f11030403060902030d080c09090a0b0d1b0b0f07080c070b033c240301 75
    0x125040c211002035503055280017410510700d40d009000c0ea038002d103a200300140c2020155901d405e03003883c00280c50b81d40c034002280901712420f2450050341c03619210325180e07080456102d065648503103e8000c41d0f01c40c081d42c08002040d5100001074031100f8803041c042203105d00b0b0800412032061001600f8902913401c46001c0d84000e480c01c5010402080c2c04008200c414851184107000d113080403c95649880d0120340c4901c42c01c50740c03c04028000061480f1203000d5a0418a88040700b812a0785031900c2e0b01c2c0802c01440c032400c007079109105500300382c011548a0072559204d642058440307402c0411135414002c14003005800401c0c45500c42d09030131001d84522201d030921300e0213820096000c14039074000c810300040e41c0c1c00c40d41d4603200c104101e0f0594143c403012103607903e0b4400e071800e903102a030700c001e603040c084036402504d0281400014841d503050300e00c2901c0d081a0303410200307810030051405041503405045800c0c40b0302c00105800280c4035031000070700080c4c0d1254030008002da010705000203402c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 122076196 1250 122074946 122075003
    0x10302040902060c1b13090507180213090203060117040c05010c30080901060501140d060503100209010e1e04050406200711030303010608160203360105040f0302040207 74
    0x50b80d1030125640f042500e4000041071030b01c12001820441d11285488d00c58071100c45d4014128a145044454510006c50b54122100f1615010300c3c00040c0f0f0316081e1401c042e500542e0154001340002c0480003140c0b040c20802401158458417103580d40c0c0c5010019030302e01d81c83d004260344600d0390340030700143c407a007040300c0034100c61368810032521903510510040e20300d20015204110aa14003441031250f80d0300a8960160501c40a5040b902e480440034918080d010640015425018a0108001d0210644c0151009074000d0f2141021124458140540007003811100c0d100e07100c03440451213230740c10694803241d00140502030104c4d0795403c0c560200402125000410700c02c4100103002c5050100f68000111215001c6029524552400c0da0081071104060003c0200440e510b4038082264020030444420980d0510f04903940d040001220042c50b00e0f01c4072001c11065541c4c0014890342c480d01c101c0c5c0c203941203500b84000c4039085809100023900140c6044407500041c880701b81c60300b40d02648012 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 122077446 1250 122076196 122076223
    0x21006080307020415080a061109310b0a091d1902130e030a0807091503020301140f010f051e070b010501120212070e2409100c0803010302040902060c 66
    0x50b522007052051200311101040e130445680c0210b901030004000c00b04590707000e40e400c400040b0796644404070710380d000e206002901d640b0031611203910b01c81c07207000441030046940b80410742c4003041c0305086103801c2d1500c0c810410340c440d04500c8188800807140d4018400700403000744480c80f0004d0440d007a0b1034000519028a01c03003030490400d608502d85803019400700300c00c8010031300100c02080d00181c0e44e80111700d40e0320180003207400042c1c00c3c1c46c03068894400505500710079004005055030090000d51082c003556012400c5000080e40c9401c162900e410040c60696454280c908a95011501d641000a00f00d01405101c0d55221251524802910180740034112501c10307545014000b6108644282c0c0c4481014014492565503100403100c00303034081c1a9003000380c2c0102017000010310070904030080505c01601d1000c0300c0840c3d80303402c002c0c002c8103c05803945900c406400700151120614454001c0c480c2030304000601c01170616400c212592440600a2410300145410303040c10601c0701c46128 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 122078696 1250 122077446 122077453
    0x18030d1401090606090b300109050f0106030e0a0210020c040504120315031709120105090703050c060906040b0901030204050a0303020a1a0606030f060111030d0b0f150a0e0102100608 80
    0x511500342c1501c80c0000628103410800081d40c0f8110b5154031030f00415421a600b44882c2074001686010440c080401081d401c408880a41e10b400d01040244001c0c1c60765102c41550000100703202c0d001e07110b0340c104000d242001300b03101c0013103a0810680402001c0340790f0440c0154403045115403141d0143d40c2c001c030301c6814031002d41e2009400003011101c0c925680c618203d0596002c1004c13070b1118010340c04130031031058040c0c0c1d103141007404581d60040303122103450a503103480208035110a000c1443d9090b2445182a00d111441501c00c202d168061110b06a0780104104402c2000303114480c0286010072043c1070260401d43d83c5d1700018580f905561042e030250304203140c01c1040119540e1290500107500d100701c039107400c103800407481d2804018616a801034240c004031303c07203a014400c821105244101200e54440165010750301030200c1034141c9028481301c0440156a1521030701e0001d0720b0290b9007105080456580c01110380003601c0000505501811a42a4101507107004600180207160b004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 122079946 1250 122078696 122078699
    0x130c021606080f09010c09030305070318171006060e0f0d05030a110d051303020d02040b040609090b09280309030b0411030c030a080412110907021e010e0618030d1401 73
    0x20070183d0081c91007010b40d2411102c0c01c00b1540081507202944e405107007490300e40e0000d18080c2e505050514010b0841607a1402c001180c6810a40c401080c0c91480d09480500034102220340036200140144e00c0443c0b00c0c1c4030304650b1400c11031b00e44020058000c180700d0002d400740d11010b0641e4000300e040c00000722401c041c084440300030040b0b969480c081c0c3c5803031440c000000400c801580c3c107e0000030711803000b1401006c2550348581004c882000c006008001c0c03542c3c0e9041400040c418030400311054900300c0001030217030101240324080d50603a00700303408140006807a2068040500702e0b04809000d9019008000305096496040c465881020300402c900125010140703495001c0c8400762299000550040014a02406840446003000caa003160700078071349081d40c4040b00c0300348800d80281c001d0081000903907000a9000a0308003009207801000d0f5075500441c240ca490522114241c1c1c80580800c0c09480c04540c032400d01700c044415281000c00f0000704c4001d6070082c2058042a4001000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 122081196 1250 122079946 122079961
    0xd0c0e0307080604030c02060d2004060207060203030438070215161d0f15040f060c050d0f0e03011521051b03010b12030307080a0b130c02160608 64
    0x6400090002e8800400b040e2400760382c000c003801c4569800a001c3c04001c210900c08140c0e81d04080701d6002d280c0389400710754882d03600c61501c2d40c200b8890345005218204000403c10700100c1264013494000044807060651010b040c4403042a0303010076032840003c1c80d14030707802c0c0b40c42007800c074090011640580449403a2001586000d50081c14600340c05448824118070550442100d1500101c90040790740c12700398180c00115a042911152500060745441040707074801c1c2d0000810686a45803120040180c8400088645002915005140780e010032690308180e4040e0350050702c00c24092810b01a149200030110b801d40754107840d100703858106000c040c000f10040c45905d501c4044104001c6405801503103415503100210010405401c18401800c4100e0700d003900701b0172919034050080c10030441142a555641e81c011600d81d00012030100101d109103480b27010710741001c00000c100365900000001000018100c000c03002c1f0943c89002c600042251010140034000d00303032901c54030f01303a140c40030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 122082446 1250 122081196 122081203
    0x90d05071511150601050a0e0406050303121b03070203071b03021c060c020309010e0405061305100f080705060a0f0306090c1d0a0806010e0703060f0e09010e0109020102031c020d0c0e03 81
    0x4010700c01d40502141003000c242d034420b050b0340c80e14025182070303002344050340081001881a60443c42d014000010946041e03003500d40c240e809031605c001d801300400c445a6031245940000c5c0c03100c40050700300700101008603414414505008a0250181c1403aa580c1d07800105109041c83d1703001e80213102d010182e4240a080d12440d6055250f81c00954941114000000c00c03a800b6410a603218503510b001080c4d042c0c841e00c100d80e4130144508020003c90070042e5501e6102242c82c4102d80d9221020900425100c03004100301c012500c01520441c28610303001424ae603d404544004010075036581000500c00d02da0380620400f281c419104e07282904c8441c01c5005070a000f03d4030550059030024030400020ba00015039504651040201d0300d4591500101100582420307404a40092804d17000441c081c0f0801d002140601e003208000c018186160340410300781d030744810780680587c000388020210000c0d4480074202e2101240ea0051034050000c102508882c00c1e1104600000d900d91100d112074207003007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 122083696 1250 122082446 122082463
    0xd1b090213030b2a0d0603050a0305070c080a0506070e0d020d0309051305010b0307030507020a0503041d01170718140c07020415080307020f0103020412110a0b0f090d05071511 77
    0x3c42d1000d01d0942090703100303c041016020141c805500c0011004122561544501b02441d440000c2d24079464050038000c0040d044010140c944a081450000b42403e00098190640b1b0303004000c1e0559a80c2d80205540c0c65051804607a001000300680703000581c2e40180001c1610f20030f032206101c950520040c0a0514440030b860290a072801d40144040c403d202c00342c0c0d500c14480d150100d81503640700d0041b4207010140c0d10040c081d200100b4080342c03025028040208120420102040326a6a8916080048120b2040c50650780103000c052201402c10702102034445150040410000900840b0b20078954013210203500c0010003180700c00c11460140110000700139181c0740e00c0c140b07030b003042181c507200d01c900c45009110b0801107801030a2a40a90150780080c1920400a1440d001c80e00309610f0180f281010706100350002040802c118588a003900e40ba504210301b05420720100e44207016400c1184c2e601518140300d14400000d4203600030b002076489140d29030351400da401c0c1e0345454900e40140b2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 122084946 1250 122083696 122083711
    0x10501020f0703060908130b030603060a0504081e13060503010e070c03020d0309060b0402030a0b090901021806160507080a03091a12060f310501050d1b090213030b 72
    0x908640303441203800210a0190f0ba0024000551051103140130141d500c03030442c0c001f0300361303940c0c010002e450400c48006e14810941941590308581d100d00d44101111001c17034004200500034071015403505125021031000b980703450992442e0962400748034000501c25407110000500000051018030740d100c140769080700c0b050a040d110f4040070342c0d000e074499050440f507008055481c907540d0140310080e004102d82c0322010307000f10341c1d0f41018042c560180c4021035201d8051802c030800f1a0b80c00005208440c2c08100056103002041440720030805107030b01003621055032813003502421003ca10306103c044020072410b001040510b041d45809400c8038080d5010760007000d5885000300289541300110b072020a240090f4654558807130b40000c0000195032009a000701c0d40a40010440040710424001c8004000d40706440d040041c0d800c0096940c24091286c0080c04da004400000b10540a02040007143d02c405140040c0c60f41c4c0f0180480e00045564080761000060400074412800700711784e0407890 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 122086196 1250 122084946 122084953
    0x8030d0b1f080705030901020919150c0209070507051002122a0405060705012003010f0509190903020304030b040302030d05070206060312090303040f17010b0901060215040303060302130501030b01050102 89
    0x1007501014108480050611080c0480040002c01d8134000398101e8a0025004105101410160840410b4040d80f4001c4040c01e400081681003070328007410018075410380c003c041007240e07a0760f0a001c851542046404842900c1580c80b0b840d100425400035160714804090314070020b243c00c60300e1003012080700308001c070011000080350480c00021001c81c0d0a480003540c00d01da89040e85d103080d600411000440020840588410760702451f00c8000031812940d51000503c805030b02c034420415880f0082e1043c840c1d24100c0a410091080c031504000b10040c000c4c0180c0781416642d49580111043c1154100d00581000801e0403007039946205107504062248000d200c01d207040008a07940d40040c01c590051244041009061a601081210003500b00b400c44020010b41d52084894055a24046550194242441c2503c14200407910f00c0c100c540030f60082c404c074481070220807031000010b44258101922604003102680f00d03003000104c0300d01c0d503000005040d855800c3c440301004040c1c004071304540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 122087446 1250 122086196 122086249
    0xc010b1002030406210c020d09170601090c050f030f0115030b0306070e04021b010e0709090b04030c02130905030a030c02120702060c0f060711070501080c041e08030d0b 74
    0x1d03800000e4400707480031410826050154154810304000b49010b65514050800741c0c40501a03901050300346907032609848540900381c40f480000b048618615090704603900c0728004001351659074001004502107814402d146c0f040c0081c44214030303842164025a044018001001038500c4507a00030301d181d4040c0790403c41200d01d00b00003520307150301078101001c0182c8005002001c0d0b41d03560454120311072400150040c2c0065869050181002101820090050050000d02c5200900602005d6030703004802e034a455440740d500b40e8140034106030a903042181176408602c038240602ca40c04a4600070002952143d80440000b01030340c1032201e02c032045400081003000c084040005490b103156040f00c1c110b8076550108000d41c80d080520003960014807402c1c09000c22107401030741c0034070391100450684521a480e14015030710100c00b602e140807048001c100c200310010b1505030400804c0446502803041ea55500c00c01d0740380d604003800003901e49a175200b000100789400300c08144070303020365206e0100f030b107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 122088696 1250 122087446 122087479
    0x717030115030b030f160503060c0708040b030403050702030102070309031401270204020d060e0619050306160c0b0114040605090f0402040902031e07031a040c03020f0f0a03080c010b 80
    0x2030302201454014142c546008030100c4c0d4081c010a0502030000f412203d10035001d0340c1007070080c1c40610030311780a401228041507103002c0d4481228400340d00054243c0c9031524200d0304800a0f400140300342c08005051040030f005a03400c0c001004c1c040d01a0740c40382c03542c2d03045052400302c4607981494190075038506401e86203050890240c4001802150358001a512040d001003800ba100d01c6c0014542c0c02d16181000c2007242c850100719010b0502034a003540314100347c1c044110130b40700f580030b6903a05a010400003204880c56030315160b40c4249518151100c4512540d41c034200c1e0401713820123942007055002082c12410a40701c0c2c00002c2600711034900c2241440951490f10f400c01503c0a40916180c034602030a54408003d044004a0000715441d8080802c803c0c550300e50340c46000c01c4070030740d02180c09140048000705481d40034641101e01d4404040c03460f42000030f1001040d003016048034154803403410551307901c071081d0000e50140080a0b03441d440c0104103400c481445100900c01c40c072410700310000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 122089946 1250 122088696 122088719
    0x60d05100507030b0f0a0b0f0d020f0a020c060406081f030803090a150b09060d060914060403090608070503061201150f09050a05040b010e04060b060d091115070b180106030807170301 80
    0x88803d01f00502d0f5072401980c0100720240b16940b0078440050001459040c032074514401001d55280c280d080c0c85404a484040050900c03403441035030300052244010510f1445815107181c0c03200700d00143c04002c0303a5a541d43e01e8294004590002c0c080d04031000c48014030400d0198840f50543c804800c20040302100c1c009a42d8440107010f00b4014904403c80508100c641e074400b0f8074039600411499554510328803925034039501154120001a0015000035083e0300407403103a4080e140c6500c60794110390392001070121496880c507a00441d0341d200e146038405403c01c0c000440c043c224582f042008075052481403400e980b0054040030308145003404102c046031414150780d05450745411900640d456509120002d0240004896807000d80001c0c034490000c0d10390b0000b40e0381841000d04020424410041000002e550002131f080030104024400c00500240d00c441d50041c11140c940710f042c600c00641c9802c56200e5081111040c1c0001415803e0109200030000320084900109280d5810984103012 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 122091196 1250 122089946 122089949
    0xa05010803040b03090705151c0204030f060216121107080c101b060c080117010911010507050a0c0303081b0901140a0c02040e0705040c05031509060d05100507030b0f0a 74
    0xd20383c0088042044404d0500000f0010a0000c14140054081115020041c0e00074161045401c040400b0342c002ca810074002e0b80c086a40000910b644511680c981c2006584000f0305c05580384601203039080090050001c84035100700e1580d44004074099010f0b12441c2040e250000031140e40302510380e20250b65a10880c078070048581c600100000065a1000d40c965a10100181145c0c04e001d84910213030340c0490207604075403520004500c0703110f5420201d422074083c0c04000c0c050b0248006507054650081c001840c01912076070841d4501e0000e9281c580ca100710540080b00050074003010b104c10408803055202c40100341d04056407821801c0c1001074841c0d1074051600d034500314042020240140100d4445070f08540140007801214008542c0e292607100a014a07841580382c5403078001c400d4859130542e48544010040038104030340040400c0034100008200c181e002100c51180c1c03000520611045610992214010030241010030019081da02204030084c050700300d441e291800c0d607540041500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 122092446 1250 122091196 122091209
    0x90c03030717342003060117031303051005012705150d0f0c060203090d02040902030316140c010e01120f0e070f1a0403080703080c1b01090b0a0501080304 68
    0x1681c50f2040c0407000d45040c41142c81c9000900141003480451040360000016144980340400704000c3c42d510b004c00d40c041d40300c10b05800d64010001072214440c05200100c003104154201ca0400d1002c199000d410303e40340d00304a490390845801e4541020850240c2c0f409040101d456003801060a10884074880c00c08150342446a16080402c20400395008000a0284060010b90050304039041041030700317001000444400708500300c0015080d1001c8165107440c00c0c014903054020121341c0821000c0e00d20300c181660706000400c24100440300c0b00c040d8152481c401c1001200c1280115609801c000814100d98180076100c900d2284507a0300001000e0030b080d21500004a0465403c103030801410030704070421140c42000b42c089615110400d019003110301c5001000c4581480901005d4140158032006080d4041400942c00003400b840078941e115800c04079843c00c04425001c000e0210818401290083e5500c500d0303101030214004650f0b900c000c01c580c05021552408541340c1e40c9114a20418 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 122093696 1250 122092446 122092493
    0x3b012003060103061502160b03012d0b1c0e0102030105061603030b10050d0b040605010c080304050102090406031101080601080c1605030d06080d12140103030309081204060203090c030307 82
    0x203001d5038000c0d4000b0001d4641c000e4000050080c902c00a591180d0b03010442e42d43c00100c03440001c01d004510300312810785501c0d1010040c5203c44441e49030b0200200391901541c05030300580840c4806c504406400070200b140380c8481d1244007689610221203100c0032280d0755900410050041d500c4030f0084802c40e0411102c80c034045607460504500074100d40c1c0030560311425050354004078a60100103007006000815040080a4054040004449140c800c19012800f1540c07560b000c20501e001840d4000c2c0a03000140c03030a0b080390300040c12628642c1045601d040c12410a0325556885000140d00400a0030316910394242220382c42018010807441d40421b031003040340070040010900540b03101e07034180070042c082c0325100d02c3c1043e242c0c14032103e84000030380820001c121000e940d020701503502010304100b441503401c5440803005000504800d0b103003400c081001180c0415a05849031265018110040e03c9050500e038a604013050292140e01c254018070084010829618500c4400c0300e08a024 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 122094946 1250 122093696 122093701
    0x30b15130314010e011a03010605010903052509050703020d110315060d140411040b060406091406040305030a0201090b060111100e0f100e0706050a021c02013b012003 73
    0x50501604d00c0700200c01d11075081a2442c0394000f003000c0c0c2c00b80e8860048000744981910344004442111042c44060001c0c0d00c258030900e060003105104070b031003120003071802003180c4e00c0f00e083e201a46c600342e41180010b640042c501241207103074400d25028003000c250305c2e490350030419031400c0c08984180c5403030310075200002d52850303001d11360380b14444020042c0e2160302d0500c0d0500305a0134030703071040c000f0350b0246040c045c051030f25103822000c4030150303403803601d0f00c41c20380b810815100e80b5500300e0484150080703030400011000c501e0810140000100303503030011403092000c2c40c00c0110800007526250501c00300d0400c512440342c012038a0140c100903003c00299022090034494a08540301a1001582c050b145400011100c40c1d00f05030040d10403101203410290307423000c01b110705208200c1001d005810441e1150b1405004222100340800e103440003081d040d0728005036800bd10140c2469000c00038142d2900411003410001c0d50103050301130002086046610354500c100208807543c6900c183c0b400100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 122096196 1250 122094946 122094983
    0x306010c11010e042301050f100e0d0b0c070606050a050607060f021204051501050d030503060f0d051c0810030c0620060c0306042a200607030b151303 66
    0x401c40c4580c0760044c0300b80a040d50025104540c2509220f0503031609a450f40089010b041404d01d407100000c010700121046202d000040381c00e5036403000070550160207064003034045003074051120302500202c09815600d84151405c0303000c95140d40e001c64001c00008008002540d42d4400340c0f099175402000110342c415114060400a01c9000320030790080000e030f0103000901100054000010114040b400340d20b90300d420030840000681c000050004100308005515030500c40140c0440b40d01c090444411911035582b29400c091583c1c00c0040384820002c80541c00e1540064aa0307000700a035407440040034107580322180c98000f140a0101880840c0e444446040d4041c0c2d03545c0303604003481003030768001d08045101d07040380e03031043c0d800381c0c0309900f020b00219a92002940401180840c0600d459004e01126400e0311a80011a1710511619042c00301103202103051107568410710b41030341c3c00140320351900104005100300c2c42c5c0c400440700060060300b400b80390168101e41500d41056000004000e07100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 122097446 1250 122096196 122096207
    0x21908040801020c0706080702070b090f010e030a0602030604060f080709050c0c0a03090510051908090c0402120103020102390a0503150703050901020a020c0f0a17030a0f050306010c1101 82
    0x10310541c0c0035840021281c032002c40110300e507002d807402071340c414081d5100d0350300032a6121100c1c01000c0c8044000c011074410303490049503458030200107051003a00110340a0020f401c2000d8000e00751100354000003007000c3c5240170310a20703003d00107000e0020f14480c06e05140301d0f035030900c5010360720000340c0e600c0204540c0c2d1650810380383c9140c1c1c0b10040711520255840c0007442c0d45494810640078035801605c1c801d41500450640b036071002c483c00302c0346500e00140004c0b1078458010304041c2581c024015140416280c80c0001c00507458103a038848a40c0d455440028a01480f06c000322282400d8071103454034401c0001145e036000100a429100c0c4d012213a40090605000790f849198107200d203004900180d01c0c00480c0d103100c7c60440e2410481c07503407032031480d50903445540081001604042440f01705460302076120f21188902a012800302d81d00e401c16851018143c40e6240c1d0755500110701c098189601c080300744603404003480c00c2820340c244880081d00049a2080060401404107102c0c01a070b403095 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 122098696 1250 122097446 122097449
    0x52b0f06090c0f0f05041109010c0206040909051b011b030e06090a0e060108090c1005160f0c090b0105090a03080903010e01020a030b01090806070806011209020301140906070e0102190804 82
    0x6841006550f8407107010b10405018440d00c440724180709000203207407070b113482200c410700d00005081c1e151103c120011a500401c55108030b0f0700003c14803000c0f400d412180f01c1d00c26001e100d440100102800c002c0314031042002407400504100c4800d040c0b0408079009000400c0441d0b050805c1c0c01c0184c00c1500141043c0503d01c1803541000304800c0001f89110900840c84c003888003a26018029111141c560b0744400794003000c40d0700100c0c1440140c1d2054400d000400f04401803071341c9100c0c9941c0603541c5164401242c48107035201107010302e00f40800c80700392003084907403c803d0070410b04e81110100861109080307844090080d02c0046420701c025182034100751141e40d00c54000315920708522a02070014100144402c0c002181c031100401e001c0800918640a002140c41d0031000356200d100456140c043c03198002d9056449a0106d00162801d000310072202030154841c1d41c241ca001e90100d0b181090041001c070401c00316000c40381d07499802058001142001d11003070703800701c9141c3c20030000502c00d6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 122099946 1250 122098696 122098703
    0xc0b0705030c1504030e010f0801060e0a03120302030403140301150507020d060507020f0708031c0903110604060506010e0d0210030f1413060e0f0705060a170a06052b0f0609 76
    0x80f0f100c0c0151010200c00034038810f512030384441540c110060011550507081c0c040220115289400510000d40102c03010500d881d8010802d641103522030380e9480b41403030003030000004660084140030400d0380001150088500220710642150300d420284503092001e0b82560003409400262402591a410810002c035900310b4014004d90601480095551060024100c000c1c01185c80100724048080102c800c4640071980030b40b00c01c0c030b0f00c01e8124002c01d400c2200310140300c1d4034040499002c600388400c070710440c0103d40004452404100140c5003903a10680b05100e0400c040d400801a40c592400c040c80214910300010848a0107107000c0040501051450741c00711624208000c2480300800800c01c0ca00c40d400a10000014680c125656048104641030316084504244480d0501401611544006140911008034840307240b0041540c151400700001d03445220920150800c010f41d50a10266410007204501003020b00310400804035500030400e03002555003500703000003a040020816003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 122101196 1250 122099946 122099953
    0x304080f0715021b130e0f0c0402090306010504150302030d05040503061303020d08070e0d050a060b060903070308071704090516021c050f04080304080d080907120b0912040801020a110106030c0b0705030c 89
    0x40c0313106c00994644401e00380d21803505c10002c501000d41824000c0e42c0310782d40b000c0e005000c141d0810082001034443d8450503050300d008a000040940d404005c0381e80c1071a2242c071650340d00e0f41008103060616030300800c08213110511501c298000b1b0f0380019548029101441c20441c1519014800c44080b9502c0b03940340e61042c0c021018006200b00499080704007485503074200001455035042c040e95000f440c40d20f9602d40c0295604102280b4508000e0008034410040144040020301158025130402e4219203110381c0e6a90802244039880d0780d0b520705400c0d05000500e03030780c0848440c1c03604612211460354100000440d054010f01d04031420f940c00340100c8400c0d00d45503a100c04940c0c1d958009400c3c3c03200043e0410300403e054030000b18441050300e000644041545800d9100d000d5503610180100c00d05104035040e20321152010340c0908058034800c0c1c00940d44014103500101008400b00003081c10f030749001000c2000440e0703c840b420450380200803054890200341032003419401070421010b81c502 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 122102446 1250 122101196 122101211
    0xc080a020f0f0312060d17030a0b040903030e0f060408040504022a03031f0303020615060d140105010311090f0f1f030b13090b070e0a03050304080f0715021b13 70
    0x26000c0094080c041c101141080c1300d50b107020400840c45843c0304090045030340c08050740010700f0020000e43e40641c1204000c102d000340100401e0840c0c0010b030084d07001a590b4610704086140504c0055a8445140b00400c41c42c00c003034444051502c41d80c032030944965400190014020f05c0d04552004c3c1c20a070131400380c007030005200102e890364400c682503405031444a101c030322000b101340d003810150ba80581c01006141d9a0002407a0014040c0b040700343d00103002d00020701c2c034840c1030059070548174a010200646514250000d030070307034081c40e030448043d4000b40302c0c14032140c80780c034419480524200c8014104e41550004038546007000030009000b03500300d0107140316032a019041901d2002058841c841d990048038072050407038095072002801c0b003003104003044803144100c0c810705e01102c0003086041c9156495a5403855540290f000c0d000035007007101e0310b80e4002c1c0e003845031400074070346a03031001c60000278a040291504800821141703401180f1206c1d100548071018816501000c880080196a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 122103696 1250 122102446 122102473
    0x102030a050106080603120d1e0507021c0201060501021c0302120c09011d0306061509101d0f090c181002011b0e01120902030a060c09080f0304060c080a020f 69
    0x740340034010500032403000e801040c030342c1c100040c004481210f40d80000e81481d1000c6e40c034202a00070210241c0484120642000054030700c1c0c85854054403094000f000000c0350003244544083c8901681010359140c80c1e420805a41c01241c0c10740002c00301c0c2d05e141d000700c0250005500038000d6803c00c04001e2552410080140300310001045080026202c607813441e1441800c10348881d02007400140c240d00b018004c51a00e00f414540032200c810960352180c00d04a01101240b228501c1c944440e0000c3e000900140b5038200e080501165554195140c4080200e00f60218090342806090f1460010002070403440b80c40800c0320002d61601c0007001024405846440280a4564000c4140f41d1909420502c0b20a9001d00c1592034045010703103c0455154071119480c3c010300c075540302643c16000e803618240c0024042d1085802c181c040343c5800eaa45414900b44910b861820b082550040d8420001800743c641c1081c26a45180d80c45038456580b40302202c801c17030801c100d201e0032442c0361060310a0700717000303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 122104946 1250 122103696 122103701
    0x6030c0706021b0c03061905100305010c030b04110702030604080a0e030a12020105071805011803020310020319020406050f03040212060f07030c03150909050a0c08030d0b01030b012c030102030a 85
    0x1183d040080b121443c000070109a250001584c90000c09549000d400c0341b80314161f0402d95110b03140b14070880c0425625200e03642502c400c921103800191792862101958070341485071980003120035a1841c2030581c0f99000c01c0c3d0340d5601900c0a80b400d01c000c5000d858107440f50044203085a405070680d56a039269280120700c00c03004082000165003041d0015030300c84e1203070703003040c0c0d4040c9407004141c17109181c4001580c00075503410a40e601004484004805a1001c00000360341b080c002000580d00c1c0340420400d810542c11112080e4007a0040208020455101054440b40303020031020a60303a850b00d20000e0100c2d10000c5000d612030041d1b20408c48910700398003456216200c00c0e10700b807150003001d09044086540010214070003e1011100f40b0030300d8101d502042401d03204104440e001d5203913844d0b05280041d1548510859800058060480d01e101d00070455010420f080611031090007000207081c15101011400c6c5404501c40d81c2900320308043e112001000c2d003d0002c65880c00c140911001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 122106196 1250 122104946 122104987
    0x60a0e1c0c03020f0103020921070f17011d0c090a020702090f0907081513110303070c08010b0603010e0f04080412050606030d0e2404030819030b1e06030c070602 71
    0x10070444c90441c4841c80d40a07008a95145400411980b541880060316940c0c85810700e1480d070311072141040215924640c00c01d02405400b070910304a100601d80300d00c203801e40388000807001d445199401c01400300400007440003000c80040768205c0440d0b4031580d5040c000c2c02012000b960000c0301e0b10910400c0c4807001c001074060f2680c80c083e20161503c1d11382540c0d584041d04003100410340b600c00002c403050f03000c1c803c800556200d02140b040c3d04001d81c00103895030f001802c05480300c4503a5a410044e4081c01d1080300300c0880c066030a10305641c90000030454499000307103906c42640002c1c0010302017104480445000e89218035480098a010341041540d9020480c0c40751300a201e040d00a0303031003c0c05644d0611311404002c00c62914a0402e00c80c01c20100c0d0031a40e0f100000c0014407010002030f908802a001800c0061401c0380c6884c003401c1c009080d2422941c89078018400340a00401e485580e6100e00c091441c01d5038599038170340b500c18071080d1921600b08081c00552000c9040012601e203040d83c401c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 122107446 1250 122106196 122106199
    0x1030f021e0102030703030b03010b12030415021c050c010b1c0c080105010b0304031d03030d090515010b0906090d0c080c090f090312040201020a0506010905090d0e060a0e1c0c0302 79
    0xc152400181115070210052403000e0140c0c0c414401c050001c0d06c2600f14102c1e480e005000030a01c000a500821410318080c02910039a8002240902050300303c041000482012031004008815203044104c4015032501c04440405c0b50000d4140c00200b070941000d11303060700107004008180c8910074031804a0161400c11106200100c100240844050052906860303480e00110300e10b0712680d9090722404204801804a00791000070840255010700140c0000402a0404034404220349000ca0601c0081c0d201d090703030070010324014082e041d4250140d600702c01c0d050b0760b40f580c0c03451402c001861060031140000e042455000d4046030600c808645038000c6503090365104035903118003c0440196504070341a016540c4203000011250309a00400c541050060041d54580c071032a440d00c3c2c1c02c1070026081080d002d0b40361010301070030070020000340030030070482d180484201d454100014010b1007070a09a0b0300308000c403e201c4925540d0b003002c29170b403200c1280130504084e64602e0004024405403100760b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 122108696 1250 122107446 122107459
    0x60206010503101b050903071a090f090411061c0f14010b04320402070c1502210d0605030d031b0302071e15090b010f090c05031b07080301030f02 64
    0x700c80c036010794084c402915a12003462881c14514540880f100d8000302c00341c540c58410707600700003080a0740107452810b6980782202c040d524403090080c41140c10703100c440306029010507410003000c5803003135402d80140c00b03040341c5035030741d517101e000c8590041500c0950020a503450103600b088460000d070b010465290703440511801d245e03650001c0c17008c0c501491060502d1032502580a61030804085046444486104200e00744407180d40e012030104d0300070407011208021400028031003070540f6114800d10203241e1008001b84c0c0780d848011030b600081c2c1040911049004946001c032181c13203400c1f0402400e03028048034500a012100180600001c0820b02c01548401c405206524400d001310b59100b90008007914440501902d03a018080307544c03000713403106e020352680b0300c4038503c1c14010001c0300c0d400780e4001505035040c20004003203941720b98001e00c0c20034509060b210503950084146c99000c1a2120044a4000b4104401d034941c401c51200600c140c00000000c010417008002110019000380c0e201c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 122109946 1250 122108696 122108713
    0x62109070b0903030a0507030306030f030c230309060304020307080d2c010c0201050307020a08040b0406110102090904020d0f0221011d12070309030213050402031002030f07050705031201060206010503 88
    0x490709140b080d11242605604100a01c1e51454000c070024515948240390000300aa601e0f1104a80b090300c440040700041c807034601d05c406005081d40300c00e689119428510700003611066020f95248180b04616014103004000030f400d40d49e05201d0200100310a2082c1c801ca41034903440141a406805052601144a10010001c0200b040000321058406031210004891141c00660b420740000b04440118400c21000b40b0001d0701c250050001490030314105a100d07400c10101402d10145144001c585030b10500182c402c513941c1c1c0304041e800540541e5603181d1241c0720304088000d9103003070b2030194100341c490400d0b0f12215141c0e00341c89110f6460b07200030004440d8800c00c081c410414150a003259a100305101e017901e204110003011814402d081c680d00c0c081e0b40e5030124400743c12914000c04080d5946c03007080154101417105d5200e50303500032070843c618646601500701c00c0801802c5d041c00c000000c07410804005c0200110b840c2a01031410030211580d45000c000d5440400f405034074040c0c001c00f00c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 122111196 1250 122109946 122109959
    0x405011e0f030c05090a0b1009060201110f030f090304172d1f0207060e0a0308180a15110310080c0102120d050c190306140a080a0605040206210907 65
    0x507402030340d90003241194018a4901005070f03210001d071500080503601c01500060f80d98086500252030001e4450400151a002e40a42140c640702c6030444510700400480c03070107014000c11254042d8681100c0500da444013400c02d4554081c075048202d01100d02d200c81c8503220307400140003505014003000c0034011400000220030300e130030243d4503110640c0030100006d40441d0f24040600b607102c0d0807000501b000c4050301c525050b91942c507540241d40e0031a08545060550282c2d24590009140081d280c500700e02d219115905d401d14203001d40003480725481d0010610103070b00302e100c2c0813000c49076450b06c1c0e007492207011200c2900d511860038240304c1d18881d0225540041500c50428420501130350074200c2600c420000303458001c06489001c0000c0242e205042c8a944e400300c003180b01581c0002e5001d0524200740380c800c2500c0102441041c038040300b00b19844002407581c0e030080e408500880c560b226403005c10413500625880024007500c806a1301c1c1c5810343c005140740300701110401c699a01d6030302c43c5d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 122112446 1250 122111196 122111219
    0x904050a090b0402011d1302071b050a060509011b1a01060e0117130501060e0a05150901060509010c050f010209011b0201092c0c0d0b1503011202040b0405011e 70
    0x1a0010524001c1400041c051340c0603010740c040000a00c690440030804030400210000d11300307115961002c8e4041078542c240503400d615000c401540780a503400c42810400003030542c424500c0703003608001d0000b4000000b81d114440201840c0000842a16480024a08003141000c0dd144141d10f013050b03078000183c0c1a108030303404104003034180c40380c80d100004150a2001c88800034040d1818914201b1004000f6000740f0402008044030700f013914990422041181c180e4801400d040200d0404c1400d0303001c5650394a150340d044030741c40d080050344c070100c1500680d002c1c80380c1c3c05c024105008400c20704d80b00c0401034000308070800c1e09980e078100c150110f100c1e210070300b800b100740070740010740c02d0005002080108110304e01c2c00048035402c40282224011440441070112060100d00a01098400d02090303140110303c40d4a10845801400b865003a006a01d030b800144507030010090310301000015074840c3c0d071004a040f400500b080c4400c0d070712540e95040d8640c0f00846400f500c0d02c40c0e40002500035008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 122113696 1250 122112446 122112461
    0x30e0c0405010b1b010e100501060801060c0506010b0a0210091401060b040807030b0903220f080336030a0b040c050a0b030c0306010e03011d010e1902040c1707050904050a 75
    0x3c010960070070344614207240c0341e00300c03010251685650b6003802080c0e00304100710006215500240c04101981001c40c024000b0006074407030000d111105050f000041d0700820394505550003161403c0c0c80704c1c60070004a1511703010003401d000c1c0380d10f003414903428481d10b55a0b44a000c07014070000c0c4582c43d84d500000d00c1d60b11841c45a021240c100000034400148016010360300420000c045900f050a007140d803507002c80e0000c42210f030b225002ca00070040720350011940d1000f010716038091030400610f162401d002610300421000d111245400f10ba001440c004401c6140440103811070f0080021032070515a0848117403025a91502c024400092524160b9080c0c426109008442411521507442102480e00042c1405061068005012034191800d1040c096240340078004400100343c00104a070071a100a280740406410112503548100e2020307002c0e491460b41500c00182010200c04104c030f4118044215029540c3d802c428413202551002c003812041030308444c01c1103070307803507110b411403c54480317 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 122114946 1250 122113696 122113709
    0x15130804050d03030618020a030b09040b07111002070c0807120819232113030e0607060c08011401020a0f0201180b160308130f020d05011b030e0c040501 67
    0x80105100d141010400303182c10034442d040c003007103041d203920640042c0914086805034007079001c40d4074441c2d9645400303103042021040d92100c040d030034541c81305030319120010484010702c180d0f80c0d4513a02e0706104001c01c82c1e2054a801c0210345800c503506c0c108108075080d209044040c882c080d000306503200703034040380d1a046510988144c9000400c205d00104003441c94421303c2400207048044215405407400d900d580403141d03101a55601c403800d00c911007007408230b1400030580d0f10780c0204441c0380303900261450600c1d0507003008002031440381c001482c6842800802400d15003400094001c054104060768180c450100e04a1442c05403207004a0380c6208508010300700c071684400e020f000d0b50245881c1403022641c103c440c11a55200d082c15211503100e40b40c0383e140c0b03000740000101416806090b080e040050494400311483c0f02d0b40320909410a04580680b2420301c80a4003c20040250300050a4100c45041d0034020101c1c0b4801030003d0460002d2040b003400f9006100005142500c22581681e00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 122116196 1250 122114946 122114963
    0x70e1306080115080604140723040f0608070611030714010506090703020a140904151e0807080a020f031c020a020a06050c0706030b06120a0501090e06090312041110021513 75
    0x246c41d00c5044580100c0d2402c11000d0249203800310b01c81c811443c0400700ca4840480700e000007403401c014441269035103070229494a203400002d100e00c9001143c8075089a00b649040c41c00301140c600418214031036a5030043c1451007540403140c0c1c0003c1034010602c1480300311000303601030380d40d0702c41070b07003644030f0600dd4000041d6580da406081001c80400707002d80c6500034100040500d10003246100300140741d0400e1a00c0d90700410320b105642c070301800d020007400050002d05186032a10100d141c0e00c001c401402440b841c0f421540031801e4404005580c41c2c0c0020091021052400c108043e4842207150001d0340503685034a000b18040c0d000d8001c490412559200400085240c11030440040104525141c1c0c070242c1000400003100052031018010100030320005859403400c2c42400460351410844401c64100104004800700c1c04415566001e004504411303181e61545442082c10701c0354402980c1c44100a0f141c14901c0f9800a548070408010313014581c0305444010042810300d00e0400d00920001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 122117446 1250 122116196 122116201
    0x903030402010c030909050411030706020327190f08010c05070506070809010e03131403070506160203121606150f091d060108030703020c0409030c0b070e13060801150806 75
    0x501c00c035200d80083d8020700d0101000c0d13860300650400d48206075001d490300c002210400301c0303901d000e10050b0003e2015000030742c40c02c5a42062a96008001d244010b03901d006800313082c506484418001501d01d20f801d4682c1031b00798440840248002d5540505c010962030302c61407010700c60042d8100d40c007054028000780901da6030700e141200c4449008007000d44654969000c80302c014000c1016048002410182c20700590800209000600c08041b0081c425031116104010a456040485e8070307440c8000319a5051a00600210f850017405010420744410002850b0155002034001c0b45036161281c0ca045c064805502c4103520850498000ca03552003419030407c118a6515500c035850215890142814943c03240d90360701d042c418240c3c0950455080000c210003050f03818002c40c1c070b840600312810842d02c0c1003602c00902400003070000030322401c000c00103d07031000d000f041c4d030b41200c3d000281100003a000203461000039198500c680f0600e036007000309480f80c540e15501d01c40161890b004c02401c256 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 122118696 1250 122117446 122117449
    0xf010e0c09011404261b0607080f040605071103010b010e100201060801060303081b040b0307030c050c07091a09010506070f020a030c090c0906020f0a150b13150605030903030402 78
    0x551114048505000290004602c0c031034500c0081d000a100c02d4084a00080741d054580e107041c0700d5120242c1c4146c10000c91101d0080250b20701805802003075484503181c1d9041d180413405da00c0745564100044101003400240c8680c0400100402c51180c4218400440103c1c00d05003a15403c16032180811440c42580c0c8803030914560f00030180b60300d48000308545603100105421224190400d81c0010040740030051103da01c00e43d41c014245d040409146011701d01130070f8054500000e411f4508060310740701c0004043c0d1284c2c003a0307490400c4400540b10740e10768a580910051251329908034851440960a044c24070b80800001e040b01c1d40500302a1814040340d03150b005030300507410100e80c0012440c2010000c111503080c8140640f402c4540045e005449820240c040070a40d406842150b0143e81070114003080440d2900c85103a1211403100e82c3c100a41c103803000f60442e9154160042d403031840061240081e41c1056048440b444960700585441d2141180d90b4882211203988540c420070105005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 122119946 1250 122118696 122118721
    0x3040606090e1b04180204060305030a02061f0e190f050105130213030803040203011b030b1c0f0204110c01020703030204140103050403050412051207060e07060801300204021c050f010e 81
    0x40c50003005d074003203000c2a40c001003c1752200d4006542ca54804250300c00881d4040241c5901720b8050940515000321004075507107410703180d0080202c1030b52100041000d054a4040b0a0900003040e00248840c5000e940c0b00c0000f001e01344a03181c1700d040245a460940d0f03506100311100c101d82d0940c01c81c4c4107815521201d003240d0010700b007203805640c0c2e07508195400303440d00890007400c01c41d41c1c0c001c146c1d03c004a0810080c000d0307003900301c2e2071010300444002c0060042c40701c241c0c9042c0d064401148524005140d40002d01810060540c0c0c1d5000086100400d035051340240b0a4a4031030480c000307803200701d80044080714001c95008011400412003131003134050144640030220322901c11500e2030b07450303540352091030b030441242290070076160f050a02b00d108084c8000d601901107450044880c2d8981801c0c1070307c49140c0490400b2500160200402285100e603142050907000782c010b541c0c44201e038100c105801000141440081c0c500f001180707441301d62047c058101c4940c1001c140340f07626180341d041072 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 122121196 1250 122119946 122119961
    0x602071202062206090509160f02010608070b130803040524070507270c020c1e09161d0a050f01050909040b0a0c020c0d030809030705010203040606090e1b04 69
    0x38070090074003500c0814800001005402000c4400280f640c92610744040c09103201900310900c100182010008900d4500505404400080ca0a80400040594142d00405150308840014001e4202c0402d42c40c016100911501111206201050355200d01082d10790081e4040c00d0b911030b00c01c50042c4000343e80c0c468002da62002c02802180703007143c107961b01c031700c0e20713500ea40080703518a507181440d80c1c2841550b100901c807061502051180d4045c03902c00a465904200c3c42d2846a46120b2004186100d0054840c0c1340d40c4c0c0c085c05010143c100903203040b010500d0800c41c14001000144800218000844c281c590b01501501c0404d42d1070405040000115010004c581001014842c62855590311803041e40900c2c00f030300f0901c0071414152180e20a072851241c85e502950b010b55154505c0c1c0c3ca0700c0c0b401601d050307014549450541c80d03e0042c0c2303043d1b108403080940f19600200602c005e00110394025812101d0303442080000c0203088081e21740741d2800714001d06551107210f00c68071003410160006070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 122122302 1106 122121196 122121199
    0xe010f0b0c0717011e1a10080115120510031e03050405040905070e0f0115080903030f06030f100203010f050a0f060c0f060501120b010f0602071202 65
    0x42c2d80744854030414001041c00705940800340020340c4103103203100180d000195a0003250741c0040c00b5120004419079412102c1c000c481991401d1b101c0303240880c900b51140c4649a2800d07083c0c81405144007026810700c00d50648545982c506442654414071990a00c07140160550800712207032940710280c070b0031414003880c2880220f50004217550446004450100740c0340b1051071f240b42408115441005290a210107126100480d500114140c4000c448076650344055140c08882241d803c0d20703618080e4004101003005010024542d070340c083c002a013214007101d0309683c4507280130707198158444c0c010f0f400310050286500c0e941c40c21005000c11940d035412141081c200c600c40d603189100d1481409002c4054104100c004481140510b40003181040a981d54641154040d00c2c00c0340e0413250b00940d140042102c4400082c04030544045a0003080c84a09060020310308154501d8180e = true := by decide +kernel

theorem cover : BRFrame.Cov 121942446 122122302 := by
  have h0 := BRFrame.cov_init 121942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 121942446 ≤ n) (h2 : n < 122122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
