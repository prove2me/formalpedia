-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2902
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:05:40.640703+00:00
-- url     : https://prove2.me/submissions/323fb209-1a51-455f-b6de-1a6ff4652dca

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 521762589 ≤ n < 521942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 521763839 1250 521762589 521762603
    0x14010c030903020907050f070b01050909030301030c1e090e0f0d030207051903111009030e040c0f210c08100b0c0714011701060206040b01170c0d020604030516180504 73
    0x42c55038082c0110070304020004c0c0301b000402c2042c0c4059a8001010340398541c0101070f000707070740e42c1041c0034013504542c0034105860710345c000c0c001040002c0486210300c0990304100f840d4598035903058904d060b80741c01034010440c102d0400c18424440000012041015120f040444d02c441800e400150201e00c24000007a115070050f1709804500c00b4001c402c00703951446841e2071041c1d0b10220340ea00d403c0001407885c141240d40c584c4d015a00385030780a2114810220b040310100000001c1480152a05994020010921409402918450001ca82180382e4030019500c148000180420024584582100e002100149558000c21007941120684490811207030080540c1420110500d00340c845a60040341040303642d111030800200704101d0300d802804150003c2017142014a0840c000b90740c140c204940940c0309103006d80071b1910000c4c407452144070030760701c0c500b82c00c0150004c00c0c00c40c07260781c001a20074452980c5081071680c149403040c0481e04104010a0401c50851418040e03c400360340181c20b40d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 521765089 1250 521763839 521763857
    0x81b070215040504020c100b030102160f030917030408190218190207150e010510140a03051507021203090d0e040b04110a09050a1203030e100e010614010c03 69
    0x14181480720011021540da615410281d491002034203a901044452009400620301010b14480600070751620305821002582480c031400c0030303e002280d02200141c01c13090800b00741c20130705000c1c65005024000d606103034011060712000083d07a81c0c0c864441c2049601c90042c52040e10070b00d135000c0c021010341c01089680700c08403000d101c035400c0703001418451f00b100d005840c074049414144020314010340304119044041181c0715807041220380c60805000d0590500c1c00708110100a2003058050340c100d45c800300f4055141c1c0e404290140c125030170040143c0305102207000c4001a00403114881c00c010b500301c0b902c030000300c2800382850000783d880e0f80131644003c0401c41c00c94002c092911019030050b0001510000305130000301503440595810104075000600b8400030341c1c0c0106c08502500d025591000d4491600303440080741c07040c00300b01800701540c90804c0a5030207070500c8103003900419082d00307100c0c2c03c40024105009004030b110b590085203009034454565400355003070208081e0951940542 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 521766339 1250 521765089 521765093
    0x6010b0f1308060f010605031306021c02030f1b0a050423030d0f0305010503071d0606120c030a0606211a0a030b04120201020c100c020c1f081b07 64
    0x40e00041444104900309000300e514003820030503401c00614510000b48a6820603104e481e060410607000442000701c00c0041006510303001409181960703000c0b0005075903d01c0c612040040c1c0900e10052009903000001b408452400841c1f030034000d0a131101e0b8800811503d00758582c00e4031401c0a0b480120300c0900040154030003c2d84600d400400304d1607601d4803103429800003410207020302c0200011600003202d0041555040c4a1107014000036802013142c10304000010003c6402b40040548448529002881c65154003081d5102d12400161091060500c25880ea8654004491b550710703140c5403e00010303001c0d100d40308503550a0300bc8108440b40c00548100100901404001e400301d150ba0500b40d240c1a440d9a840000118080e800100307050804c5c0c5000a20300080450040442e8014805894032001c042401d07080d5500d401e60004050002840a90a00b10b510344070030341c0184040100b86000803070081d614540240c9544d0702103036070755580f50086598441c0c4400e040340342d020711135040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 521767589 1250 521766339 521766359
    0x4271a130b01050f071202060105060412020d060b040612050c06070c0611160602070303021204210c0f0608070807020f0c0103020708040e0a060e0903072001210605010f020a050601 79
    0x450400614201c4c3c903199030840104080e07481202d04549240080265204056050103128058103003150090b191a14095020b8001c44001e0f5005e48904e464005180400025500c002c0754000041c200f0f001141d555002c10401e202642c1f805d448501039041e021050307260200403181c450b0307440140405500d003009400c541c540c461881c820524445e0700e1000f01c0500c0140d404c00010540c0b40d00070b000c081c0c1103103002400c10210641610032900140414454009030125480301174036500b0410740b4108250a2210341c420300c943c0844041490400c010820991007450984202e240f500ca00d1400d4070b611100300e0f5964200b00700040e0302d403c140810381043d0b10980060411601070044039050980b26902c00d00d207071a082c0c3c1e80c07500669071b400d410400b4800f82c1d501d041e40100444041e50030a6801c1d15008041d2003402810075089040784140c8034103038003400d41000060f981003080003116200c1050b0300002d0503036010b1240412403903104107440a10014499040b5507019014045c0f80c4d103407003503e003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 521768839 1250 521767589 521767601
    0x120507121e0e04090b010906051005131a0d0507170c03040c0e0709050414040311060c09010f09090c120b06040b0d02090a0b0c060709060f020d080a0204271a13 70
    0xa9402900d500408004c45c2910341042d000c0c0c058180006074040c41c2004100050031800c580b007040c07000074840485085078040b01d98003182c166000b801c0c02491180c80014881c0319815400ca4030303605c0c2c007050142950344031011015840f8001d05072805511100c2d0b20a26030f0008840003894081402010f00401903103130000c582180386400c15408260b248e40024088c0e440350b03a0740d01c4081a0000c100b100349688030a02450411446024002e1400c06c1d1012446c544502c40e1424140801d070f411724003a0038800c10b1024001c00c518202040b03005030303d8500400d0100c4050907011824100700c5620543d00e05441103c0858003d10046803812a4280051006c0c1d04441d090581c0000c002c0d0303000443c45001c0c03006080850b01403018041d08c0c40c0c403003c00340c1102000c2e0480c03010041c006004449464000482c0364140c2c8460410711125602c0540c9207019220f203801038600c0075800c01c1e04000c140c0847c1150312045481c000c0900c04640c4400c1c0d021015001d1902060b8000e00007404101e200034240d001c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 521770089 1250 521768839 521768867
    0x708091003110703031e05060d0311030f0c030c10050108071a0c06090618010c4b0801120206040e070c020301020a0509031504022209120507121e 64
    0x482c0c101c2100c0d42a46481d041240203402207516014040c4100352843d00c3d10300c0c6e481082d8020400340c1480d801140c0f1103001090000c046c000b15010104101400300f042c0d03150904019003060303030765848020307041c3c5a07004518210600d10810200c01c068403814002d450680301c0758801042041e01e401c031419045191f068140d0461601006a404000801d0168520482402c8006d207003905081c482e800d0003000110700000264540350881100c0ea5010703004c26103214468260141c42e660040000c0c06150761120225a4509103010210000f080742c0801500000d00340c680d058103a0b44c600f0303004140c00c10359400030b500030030401c020720400c80c4692246810221519201b00b203684140d0209089920065095000c00d102160301e0615150810000c003008a4504940700300d424150b01203035080404002815619040c0c2c0c003031880214140d8040d401e104e03040b1030360540c01c0c000490060001d40c0503640c01e1340c1c5440a4641e0000d00c82c003c800c8103d121401d84000240010234200880d4800d0700313842c030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 521771339 1250 521770089 521770091
    0x1101200d05090d0c030b070822111801030302060709080610050111030c03030f040b0a09020d1218030b0f09030705030d0b0609041514120312040503090901030819050708091003 77
    0x515404901c4d00d82d910806184207504811035820808801340161071300508038000b1118a01c8490b0349040c1c400f9020011326804200408440180c1001607681c00000034080c20343c071011800001030542c002603070b40c040c4a41d903c072401960f444581e01504c803801101c802c0c46800ea02201000594880d1140b41d0071480400296130070801d51901490039a80191554449071208000740002d01c050034050030341140c0c640104004000c0c055000c20131528580d00090b01000f035020905c1000f601641e0149804400d200079281303907036124a030181d00300304192081d180d4680401c0c0000c0d1140c000004031040b8136003200007141001c80c0d80707a414000d414980001500140c0a1011800d1929103010f80d055510072101522101c074104510201a0420544e00e648100c08100b2203003a0940b010080b01c40400403681040010790700c500f4501e1551080ba44a240c04c901500c0c000020f000e0208003411946010200c01d500c8080b0b912011035a42c05452800b0340300f81801c000282d0b16141c61040c0840100071818 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 521772589 1250 521771339 521771359
    0x304050a17070e0112051005041a041502120406150e0c070302070b0307030c0e04050709122105130f030213020325020a0b060603090618030c03071101200d0509 70
    0x2c19001d810303c207a1060351501c044046150070400e00b0300464010300407040003000b285c075007919118070150095000c440c200700103402140a11031034860416840d40714074010b643d00d4620124503c000e400440d0f043c1c600520b0680c090b54002c082e2456a000c803075400c001d00e41c0c241c607030303001030b40c10b903031111100b107056204000c0001400c040250256115034150380340018071001d0b001e0050000c1e0442c4801910543c038040411187d641c00004d010309540c07034043c0d0300c607040d40345d850b0a44401c503050145c02c0180801e041000c00c1307540e1080080c40035a4090f101c640d4015510070790640d0035481e50100030350000800001c2d102000440d409503601602460010b40070000d25007480c042d0b145940500300068200070700d40402c0c0481810354540182d03082e03e81c545180b60000344603403110001f800680c468402018480d1961004109451180352030100b561340d140d000d890190030038800910024007051105020400052040101d0840c2030f040311f000d03019605124900316103540c480600d03240c5c01403900d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 521773839 1250 521772589 521772599
    0x518040c0b0f0405042d0b01050a030b030f07090912030e0607050703021507050d1805071e090515010f0206040f030e030a140606040b0a060e090c04090509011d0304050a1707 76
    0x3000f0306e0a4031010a202d041e040401c80448400c40140208014407542001414059640d001f01102c1c3c0700112442c1c0007035400503981c0000e04044100303030301c07189620a440c00031410301903903071002009520840703e407010070031200c1d0700340d00703507141d6220042e6150840c10000e80c03194011001004d500d84a8410344030703601c000c00c1c3c5e80c040700801502c0700c3c0c00042c008912007840001c24803d001c4030528181446661040e1947c3e4641e56100780c0c0150b4410751038800e02c0340707103c0111544e400c0c040d00d00c0200a111a15240b10700981c5107400d1114140000c40741184c42410a002044060142c1d4220602d803140150300e4800f40c4050035144a0150103224041000c40403c034691424000300ca5000d000c0e08a6041c03240410098034850041c551123004644000c0200c9600b201e8a0305245506880280f0555581000c14a9601aa03031002c94003a04250402242110650007040c8441c541504900d419001c0c1c01e60a96070300550040a8201d0303140c12090080150020548440040c01012200f04030386070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 521775089 1250 521773839 521773841
    0x1f14070822020616060f1103010b0705070b0d0c020c010c020f100e041e0c05210916152c010507060b03010608150906070f0e01090317040518040c0b0f040504 69
    0x283e003040c000000d210b44c08410061680680420303d10910818480d00140c051190320511042c802d142103032b50b0019079a810480c0230300104008080030104d1a0b01d9170700300f50140001c0c2c242c003d024001801102c041c10802e41c012010307583c40d140c0203080080184201d80602014070040c00c1c1a10a00001d02d07446040d0707079214000c007031080f103d92030750440c4401d4034009a0300ba1905c2010070303021f2240900140700307032402e0583c04491901c00d030380380c42c1026144c8103d00b40c2880001c00b09c0502800105001094552188609203122031150b60340c1350301952445404000135046130403003c503001d9401401801c40d17206a0103041c049020f80c0c000204540d0003000a402c4031380981c405c1400da04010711006001880c6000c441e84004030201402d13051902c107100414091034500c0f90b909100d14004c028625034801c0012401941e400110300c2c20704a000c2d20300c81c6994000d81709140c030811909490005440c000c0501070b001d6548030342d1401082d8205441b004c0507402190384400101000d1000098560326 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 521776339 1250 521775089 521775097
    0xc080a15080706260403020c010c06090b010e0412020615060d0f2d020a120c050c010501080f01060906080307061d1b01030c05031303050901111f140708220206 70
    0x7154a6080c000070306140d0701d040c45015003200020b00d800c81307810400072030b4002c6491003601000740b0b00b01181104500d010070003065085405404052260004900701c00e044840b14040d034010264508000c002000c202e03512542114901c0d94102600d4030401c2906008024014910201001003600400c031016901141c00c041c3c0016074a054400c00380845154000e02140c0f0840b04110075480c1105a80c00942000010203030340c46c03020360300d80c14924003a11610036221480407130002440ba6594a403001550303000b0032a050041da51a101d40082d001246110f040103c1394640d0185051143d140c8030403008010302d081e1141c030352008603150710380c1203c24040032070901d0b50039260b100d01000b103130001001c0b80c903000011400e001c003c1040c0260078804c0b00300c041c5043d1780352400b95503800540e001260710306640064040c0d21700c0352045003510881d072034180840b50500c801d802c0000c00074000100f00224001d03240480803428900100b160305803e110071782005003050100f540406000e40c0030030700703a0740 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 521777589 1250 521776339 521776349
    0xc040509070905060d3c06051605121503011b0f0207050108011d0a021b1c030606080c0306031618050f1509190606021f0c080a150807 59
    0x8040900c2110064800c140e0030120907505101c4482d000da0b00d4503030840c11b25003030b600d81800080c5460401c5c0c2c040c6e0740354400704502c001000403040d000d00d0140f000d01002d943d01c15048003017400b110001480384090700d900c941100300041c8180c40390392104c0d40480b0240303111501552603841e210a410032001c1c480544540a946001110705100402410b001254000ba030401c012100101b01d078100404418805141001d036902480d11078076200300c004d03c1a182c19528007000f40c8841006040e010400804849003c1c04e0a0031003402100c0131822514030b0b01132100400d1541000c14240030201025507032060303002d0116404510240765058059100c0d50000010301604802c030740c0080d01e50301840342c11280c0f0030312040c1d4a040916030840c00ea08154502d600451040340001c01244401815044405140f00200411921240000d40b40c1c17280c51803a00040c00d90b05041302032a00b15118203060b0540766660455541c42c0c5111900180231000b03500d086c404206100402e60071001d0081c0d0000340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 521778839 1250 521777589 521777593
    0xb1c061d0f0106060e2d0910030506010905040812070c06020f0d0e0f100b0418030203190813080318060c092701172b080906041505090c040509 63
    0x608800758450955190790007520410a4104154100343c4880021101402070450081c100401021182c1049040200026805201a818802d42c40300900542003503d0141e820354410760380717842429099800030355006001550800842403d040a41030068020301e80d4580301e0700021150715000c0c1640c20100e00361070b01c1100000c440d007a840c000d100b441a0745003a038000d4000c10011103801d54440120414050002d900e41030419601c0d41e40da4809503cbd0000c12007034000071452400c000707590303410540e442a9480f09070352416401a0141c10a240b280120004c1d41000300301c1035940b039601c3d401c06480e200c50700360ba81c000814140404c0c0480c900c03d6040f0107007a1f0301c1342d80c00401c0009151b030300d02035203010b8028206c81211104401104906480d0707114403100342c403903007211080e14004e41c03004100381c8002c490220760301102041504084500c1d0903078851215403942078031242c6a200a40300201303e01c4900d43d0141d0314044c03542200342d0100d40c4d101910704003072000c0d0200c1c040d940d04440b4520360f6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 521780089 1250 521778839 521778853
    0x20a020d0e030d0207290c1014040503030c07170a1701150225030f0606140901150c080409111c0b09180a02040f0b030c040b1c061d 58
    0x180d034001c100e041418401c40040025003829000a92200da41d402a1080d40784e901c0680d02d0481d164a800b00c8445c059649515030390310101302c040e40c40718100000000c0c002d0134a42603400c034181402e8207600840c0c014024618689600740354455950108800302e070380c0090101034007985e11185e000b1b0703c0004070940720004d00c02505000d586080d28160480c81042d122151511030386a800120100c8000803080001410100c0b402004140c074403e500061200a000b5a0f11041003542d400401c101d501d001480000c5051180c100400403100f405103032942c10450f408810258858510461064040c4a4040c9069128400c0350262504183c00300c010140010304011000f03200c42280c641a000c42034200514880480020034911b805800c241c11907042420030150000288540644c1c96030081003001400710040000c0701030f2041080d1107100340154801c0030007a007014000d01040c01d40050021441148050703103010180801e030310944010380d5a4030002071056000741040e5043c00d10000605007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 521781339 1250 521780089 521780113
    0x1031511251e020117090304060c05071a1902070e0a02070c05060307031e0608070302091e0109091101020601030206040603020d091a091b150f0d1b0908071a0c070801020a02 76
    0xd80d0b2a030b00c50b05c0035016172803c111888a02205503170a681480c601000c4070390b0b080c240135203001c0c02500515400c01040c800c1e148004088001001c24103d503640c0907204d040c2039403050703031540700500c10025202c2040380090b240b81080d9000b085100d21505c0c54014180d107440200f030300e0307800440305040801d0b41d4110310403241000c45030780345440c01c051800740021070400304035a0725940300b41b20003402107209001288602006864440b0100418024240321350394941c0d506018003018901518004840c542c0f216040d48040350880c16250007500d2940b4040c07410000310003d5001d03000b441c03110340d070781d540c0c1c14001540085041006000e060140d000c50921000060405040324a1000582e101c2c10709801240c44401c004080d1041840c205c0c2d40711964049484030705e00c5640e10000d5050307d003e040391009105040388400700402a0b030340b0700000d0340300c06a1580c1d4021500400c480c165101c0c2c17108051001d82c00060001c2130181301500d0051750388d1060700d42aa08041d6101c0096000040e060b40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 521782589 1250 521781339 521781347
    0x304080106120203031204080c0a0c0e0106020312070e190909020111030a0f03020a27060906050405010c080d14010609030611091309050c030a06020301031511251e0201 74
    0x2000d060301008182001e80c543d0b0000b503030f81c41010194141100305000007018800c0200a507420101c1800c00e0f00c03100e0403e4540743c00ca0a0f010f019584420b80c0e400000b05403140300100b59105040d031a84804c843c1c1c2c841e170b68159200310422a44070741c054641140c0c850303170204e00c5040310000e1160000226044d4520310000d01020040705007a002a8402e1040000807a407050001c0ba07101e41b14240140c0c0d45030303000400c4070002c60004821140e00343d1410300403248040030308144211402c070f0750380c69021912000d04503100c0c41148100360000e25206145000314401c4c40080c0920016601e000861004640d01d40e180504268070900c0072500d14101042885164090002c1c0907100020651804102c500018414000040c0c950300c1240d80d150108200f04040012031a00d2000400b1100501c0a074036004010394001d00040720780c09146624044664014010600103c170704d44081410300909168080381c00c022084440503602000c15401e0220320404002e102002040c0c0c2e281d11071011b6400050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 521783839 1250 521782589 521782601
    0x10516050903060705090a0f030305070209090d091404020d140907050105072f03121305040507020a08070804051e04140402010e060a111e07080613030e130e03040801 73
    0x4400e0040402046a0030364000c10000e92064050401075241c901c1140460140d001540280c0f40b8007280c038101009050708240640f480601c00c440c0e501c1c2641e10710886546440c1c0d0b5040d0032001c80c0940b401840b48040d0b40d01c0540844901800060030614610011001d03903192034049800080c10f90184590158140500f0000e802d007801c000c0d2528031150b0700c24115050b4450544921500c4020b08800c50408201d21298020010100d5154445002100c2000e03404501b150303e22000c60040024681040c2c0a50ba1051b4503030380284c214946141c0f9403501d96881490100c0700e122080102103080e5803861011000e40540204240c0c0d901c10388801d2004407084c89040c4103180c00715000300300060703900180c004140701c0301307484c1b05031128800300040d40c0d0011120840b0755035008920036240c00540c802803003c804030100f03003258401551850070760b494000c241d8101c0c425940d45150500403a010f5024002d0040c005030804181112030768008013100c146d000105800d030400941000010804d0007a4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 521785089 1250 521783839 521783881
    0xf010507020a0e060a120305030a0218040603050303070e040603080906090102070807031505090c1e03070906030b040209250305100b0c07060216051305041a01080f0d08070206070c0c15020105 84
    0x60140c6d40781c5a20054098080106030042c803d40000d02c00b0401c07441a0040d034405400a0000c0c0206e40c0c9a1400b2500c940080720200d002a0301500c0c004074520703141c01040704681d0044071481c900b071719030010b1241c10341c468104a41540714080f00010010010062a03006600407800201d110b2001412442a00e0016060a01682c401c20321010281d40700c6000c0c92141c0e50003c80807504554030f001081c03c1c00011380c401c40c2140e1030140c002040c060f40208482c8500c0c0f00300c8880c4040c0d611007030324410300c100900b00c1c44404035403100038039082802507010301d801808150182c80800d65641074072200b6444207c0e06030003a0000306081050b290100210026140d00590100d9454102408660310501401108640d6515a07020505002c3c44001305890860b94111409840da10390081981e11441d07450003020354800c074071096011920500d105405031030705901a0140d0785507240112602036111606a4408200e1100013130000700c80c4294458040031a000424549801d001c0906022910455 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 521786339 1250 521785089 521785109
    0x12020d0503132c0708040201110d1d031203040f06060312030911010207180914030301080a0b070c0305040302090a14150a082b0513090b1e0f0f010507020a0e060a 71
    0x90001c0e4a004050703881d44130307196280c65182070307686000495101e0140450140e907802031201480030568000e1070142001000c0e03540707100c0011181306040d40d440c0281245510b455091004c24000b501004181e58070a02a10300402e9035a129200c4c0e034a8068440358001c0425a01c1c0400410800041480030f20300e10240050a80c01d45030240305061070407206841800c1c036a81e840ca030020000c005c81028001000501201e0b142c2da1203991280e641e80c1450310a41d034815400c03000480c0d0310b1091807141151070f4142e039003038101403866090180540e8040e110050240d240e40183c0c003140e8010b03032003a00c94600300750141314912156082c48070411550f048a00142c1140d41309014450656140500561548004031001c1c1040f00080700c8900450039803641d552800c400001e0740e01c03400d4100081e000811580305210b940c00b00060810011410310aa0304007280705031208040c50000c0302070700c41c42c106050043c5008101d600280380390045401503041149168144102800c0503040b91020b8a10000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 521787589 1250 521786339 521786399
    0xf090405160801051c0507080f120a0905120c09190b04020313082a01020301090b091006050c101104060201050105010f0806090618041104150e0112020d050313 70
    0xc001c084140140303401280d203917200a00e001c6500e1480d180181c0c010341522036950701d400301e00b5158500580354045c1d600c43d98001070303a05903101040b920140340039250044020720341820f000c00c0f00691170144009014000c01c05003503468181c540340c030840355032480a004024041c2d019049488509055024500c180304101b00b41c2ea940361000496500500300a8032540b80e40d00350159182d28111b0525940c0d031602010000c0503054000c0c1d4140c17030380f288090055100c01001d1150707003001141e2a171846e09000000b04002801500200038101001c01960841c0350840071050560300700c2c4101c1c5007146800942004035660a1140b1409414240f90541507103103032800041140c840a000359210b6481100030411035503400c000d0400004807803211030b00314507144c14400194252005818005d038101f8841203a000d13580e456000030b40700100048040ba900700864180d1281c41c102c002c0303030004000401078001c00d00410160000c03042c0258880c8080303003841a500c0090124588401808000f0341c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 521788839 1250 521787589 521787631
    0xa110621180d2f0708010203060901140f0111030c030c0a050105060102070b07060b010504240807020303070c1e08040e0a0c140301030201030e01140a0c0e1008070f030906020f090405 80
    0x42c0d41c02042e031010440803c25640c601054286500709101c940d000d6100d24034000600131419000b851140c0d004031104a441c1e03a1b5001d003216908450a00180d0200720301c22404141d6010720f07001c02c9060408000c50742008054811145558444000403580e60301841442d001c10400340111a4000402c2c40600b40c0f00c1c0c6842c3ca007403414040e01600608441d212030610700140d01c550280c1d0018407408906061030b04d042800810420300d00802e22000030f421070002103a080c00041100c2c0941c80c20369481040800544400c0c0701c91111100f20712034005085d00b208081047c6801500242031807402d0b252003802d00415003012150825010000d001a400a020060208600ba241105d80a0034081047c0000054680c0140f819141e80403001c21403134140080b034441544100040030301500c552401082000401c1070142c101c440800005011030b0004500a100e18407040c0d100703610b8100420021000d595881c1681c00441d140b1640f00e002280c030803400e150034015960412000c0c8117040310701c0100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 521790089 1250 521788839 521788847
    0xb071419031d10031e0c02061302040b0303070302030a080906010803091203070b0a020901090b03160c140604061401050d0b01091509050f060f01080106020a110621180d 74
    0x2184054280a04040d01040082c2d4114402014000081c80318074000800807000d8001c1c4011803250302e8903040b603600c404a040081c4555182d0030015001800c031986c80001208d403806030004201e8010340c80b030404500ca0f450400151400c035101b900550344800c0111001030003842c00030035203c529482603004100c41c90020044983e03540c41039034000745480103141d0313152461180344001402444c24030704210756120705502401180c8402d0f6100710007107a071940004054001518048266649807040e00c1c000c0c2d018082d2000d02d144030310400c3e0340c65030408060714203241d0210307001d4030641e842d00580302154411040650141c80f048405005129840d1680c1144130014001e030f07120b95070740d4424a8803101d45940e1840003451401410b1040b032800303030000d1450b8403095641c20301034508001e92203140d40c09042594180c46840d4028400c410043d241c0c2c00d0001c44540d00c140c3c0010b000c0083d620070891210000da42c500c0e0041d03110f001401d2541054150390212040d50000d60055000c2043c09588 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 521791339 1250 521790089 521790133
    0x1504030c0303021e031302031209061b0a0f1203050c07050a1b0515131a0d09020d081603020f0d0e04020705030f03040c06110a150e0c0a0b0714 63
    0x1450b0043e1161400d082c082401038031001116400071001c070030000400304000c54910304500c00d070241c0e00030f880c5112385035440303000d01400c15621140a11003040524000007103c0004241c0e2000c90303005143e59164102894100c170015643c00321940c40300e50209415006154001e13031180c140c18980707850b031b854540c6c07035040b02000203040342c1d0881c0c08091030b0f4550380300003000b411004089907005200c552285080b90b000c50a20146141c02c101c0c00181d11096504001422040c51403040c0f80818098149008159a0104aa01518495070039010881c40c0f000f51821545c25a503624072170b0f40078100680751540c001c082d00010341c04500301550f07030b40e441400c0c030701801320942e000341c1c440d491031a085046005091100080f0b007004010802800300c140c80c44401c542e40d9884160146406840d0107031203203021b400240151404a0f5880d19203001c5a001046e018140c82c2594940d22042000412200e541d501c00c100050f0041280c505200807405455400071a00c2c0c018a40c031107100090f0707050001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 521792589 1250 521791339 521791343
    0x10e0a0201050d0b22060911030702071a07211e1d1512011e060c0b07120e06070311120c03131e0309060c0506062101090605091504030c 60
    0x511121101e000d80c440f4a601217040403c0107001200307000c0ca50310000144803e01c118000301d401d08001e403541d100440100d9018845a50113040c0c018184540649040d141d14081030303a52404000400c081036aa5012070201341c11032960800c524172659008001a00c0144407014407000360001d0807902d5009224040303c10010803541c00d88011103c0002d07426030400c0181414001c000030030315940c401d50b050050603079040a102c0403000050f041c0c00544104c20b40a2040030a52481d000c00200b010b12a03210b038850304903e441da03541e54032401820b00740c174110727558003201d60f0004050048040c0c02d4011000c005140c0b520513424120b00e2140d5041c40e0710003030a150441400000480c110754191080b2003c801e070400410030000f000b0140d0f4404409004070305a001170071558004c1401e52090021400030741d0010010009501ca00040041c0c8019154903e1600c10540c400054018001e005211003140192400111850900700301c0d402e00c407041e21a04080407410003008000790704007a02c0318141e6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 521793839 1250 521792589 521792591
    0x40b120603012c0f030d0903031805030d0b210105310b0901181406012705090304081207110406060503130218090a06061a04060c060207020a03080705010e0a0201050d 73
    0xb2035003415410100b40300500c0c4d11038080000c030a002c1d000c960704100da40c10310998003000244111401408040c010040082242d0010040d0b448440503d400c01428094000c3c91405448103604500402d0440e03480c00344044c0c3d451f4001c0006055002e402d8481036407040c41d4081c90004950001e10900c45070300001080d21440c280811488a000d41c0300680c4046041296801c0c84811f0800d000b05280d0440c04141500c110f800100da0140f001da880c00d0310007490b4290400560f00c02c1d151381d0160500414034a02c0788821310000568100030046500b000001070300c0c59a0703a00300d41c01c0818125400c03802060156040620070040183d110003140e602408006104070001624400a4401c10508640740b00c5600c0036018803403c0303803021400303169080c030504007000050f0b550400c00041c1c00d52010210761150052104120b618002e2403d003011521800005150801c01da000545480c0749410036180c5010211341401004824071950954070100d100030b11100780107600080c03842c46014500d010321 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 521795089 1250 521793839 521793911
    0x5011401030b04030e30121215030a080406030e0c03011e061d04080d060504020f040905070305060307051002070906080c120705060f0711030109080d0c0e0a050108040302070902040b12060301 84
    0x140d0180207c024a58410300c006641d04202d803240c4000103400c0e00c0b100f8581c2c400c007010880394600040c0102841d03500089083c02d1030b00e4100141d00a2450f002951554018415424120b560a22540000708049480c010703082c1515429081100c10319003003881081c440d0304854160380d04019146620a6116003001d40c1c400380d680f040e01c0986110f900c0a50040d001003007081c03101810401900a03200c0303400c0200200c1ea0707910301c100c050700d40544089030180c2009005104904098101d484101c90724012540780e0341d504d00804013101da05034042c500c2d903081305181c10114038008030215042541e013030043c8486800d11002651612030036100b404125000610b910801240d0004403824410041c020000d02000c0d081000803a0300011120441c0c625007a03200081501981041110345d0028000580450600c0015905880050400d4080d84140400024051035900081c800341c51314140158443c008131080c030a41c04400380c040751090b4104812004a1224900c032500600383c45140364002d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 521796339 1250 521795089 521795179
    0xc1614011803080a050c101a1c0201051e0304060b0a0b0307020c01031a03030d06090f02070305090d03021c0909050106110316021f1d040b010c030c05011401030b04030e 74
    0x1442021602c3c40140603034207003103180744941d0744800c451102649907652324000d1a01048101003a003030078503d24000529030304001d54811809400100e848800301c28070390b000680001801d400480342111003a48070f659008450801100e03010050606102c41801e600302040040d45500c40d4030003441c1011781c2d41084000d54802064001c500e450007800b0ba0740d5960780c0a13200d1001d8800c0f0b01400340c442e810325503032230540e40300d91003205c68030b6415564003400d0111203010080c001180c00c10a03401c40c858805400d4140c1360404050004040607103031000c032a490041407030700369141680880b052142000481c500500d0110888507110002116088001075a00c009003070007284000000d4440c0c240c52100025507003101154000d40940f101c00c456a001e10800c000a81b184044498002015020404c00080c0500000b1680074070400002c20808084141c400540e10242e2095582401c802c0900c01850b0f00300740503140c0c9007025076561544041381e500d2403202100d2480f4a121344907045401c403030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 521797589 1250 521796339 521796347
    0xc0c09060310110d02040803090a080705030d4b092601110a09060207050f0303250605070e18101701060905090703050f1618020c1614011803080a 64
    0x200d0703080142c90071521b5980302e2031000d81d40e070041211107005144046001c81c8d036440010b2200d0444200800500203c03402420031510020240800c1c2259882407440d1006942210020b1410302154000f8907100c201c0400148410b0284441d001c050000c81d00c003c3c840368514001030f12900810f2000c15804081c0c03807d000d4010301401941021503d00400c000207400e07400440c0c0000c86405500301e03440a9103030410030240c2500342801d154140d004006203040c070f804071044140000100300e22012000b07120780302d14040c2d550032986000002e000c500d110080346080c4038001c0070701e407003410004c030140791880700b94040b1a407a000b1106002d01400708036a045809400c171101418940c68207100c075003018001140e81c0c0c891400121160702908003240703000a000110040041c07585003d408041d441c00c06144008100d0210307040c01c0031303000c020b03d5840d100c1c06c01c8201030809103104180d10b054a0300d1580b41c0f0351107003105000c0c10009480805116100311508440030389810040d900d540309400041070f9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 521798839 1250 521797589 521797597
    0x1407060c0c2d030e031009120e03011a010e01050f04090c0801080f060a050a0608010911031c0e040c050d052502011a06031305060103050105071b03051219020c030c0c0906031011 78
    0x181030030f0a1041f100d0400c10b080041000407843c50701d522111041c1c0c0230400d803c0e41c1d448488a410f02c203c0c61a401d480750b20885180d0380c004410b0403d6480c001e40345404000b00e13409078103e21425500d604043c00016803020040c2c0c0144514809400d60241c442d00c0c007911184050260a00c0030744070000b1580d500c2069214000070441d4000821481e0790601d80318221801004205d88207008464507072050004001d5440d09804031130b035482d062003410b04100402407600b10200c404100091042c0129003059200c0c1c0e0b070142d0300c03820220900c4a000305604003078115041c3d0f002c0441e4142001070b0402c0185074420049502e0031910640c130790b81c5808020b10740a02950019149104100001043c0001903120601541003962908900c00f56044030180b250034410000b000035000b00920840040c412052503002903450a80310a041440c1507030f003059800500b601840c039000000c80c05c1c042101081080f1400c08140c1e40d0a60510f0000e001039200da0703001111145164840c000324484081c000100c0d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 521800089 1250 521798839 521798863
    0x316021608061501030e1009050f030327070b270a05060405010c2105030f06010c030e130f020a020f0f06040c0e0c040503031305030d0c0b071407060c0c2d030e03 71
    0x1981e81c84007006010004d441c081234151a107000b2998007000280780402282d105041c10700d0010040001482d0103e88200400c5410034280584103002c1a020382040c01003220307541c070a004071050040d0030401403200580f15100c910421503803071704205035140c12055130b003101d0007403c080c8042241410901c103120400f90103802e04220300401d510a00d0341000285005404220700503d0320380c5c0d400c0c01500d8a05c4c000401034041142c01c400d40f4228903051034034900040382c450340403a1310960b14070b12038141e0300305284401c05070f0480302d03545400460800c502d89008419034000c080500b8180c0341c0b41050160390046e190002c09403800610a0700e240c00c2110020300018085039641c601841005c040003ca5000c2c080c400c0c01880f400c00c007054441c00280400e0b5401001d000310340d0f02c130040d0607600d07950400c10f1200116030900403500071506030300c5140240d1906031140c5640c440f040c80c2400601c100210b0441d20840101c0c07815469075880708919a0343d81d41810088887c030300d07000001c2d1404201404c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 521801339 1250 521800089 521800093
    0x1806030106080403090911030c0d0e2d010b060904150f03060605041107031d0f03100207050c0306070512190e070501020c06071e0311030316021608061501030e 70
    0x715198015200c0d4815802682c90100c91500d90030040c0654007003a010403090071017400411001245080280b0007130303850060000c2c04441034800e450518941089221792026454058803024800e084822002c18210000308056501c020008443d8010802c038107010759551444a100c480d9640b02c1d441c0588038044000d00083da5074509100a80300e80d01505000b581400c4192112101d40010f80300402d0f4992a011691701030310382402402100c0040b4990300c40c400c45403a04841e2412f006540d5800c8280c4009a40e842c102d081591511640c0d890b075500075807054041003903803944034090b180302800c5041081d9194403915058805641c5401040300b00601e4990700203417444001800b082111400c0c0c003601c0341e001220003004aa8000c984001d0029800e02040c601310030ba14290305802e1034440d05146010039810f840c5603241d50021034801615505150340031814580412040300603c80100c03d03403451605000d010350311480041d180c010b414080012040ba942c0c0a034011071100884882 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 521802589 1250 521801339 521801341
    0x4080403170913020c0c0d050c040e060a06060e010503010e07090e0702011a040614040f06090e070e0c0a17060a0302120106062a141501060c1209060e0402180603 71
    0x180c1c10001e40c0c45900924495503c3d07856056007003c2030300070780760400850310103030107190280f100740142009107034800c54860080034200c3c00160b54501c503400c80702c07146030001c0c20340746400c80104003110020b030450020b0103910004040b00c1d80e407100c200c0341507421480c00013201d5141c0040035a196a859003220710b0501846040207182a0f05501500714001e1416401e003111480380c050000300d0f1941d001d1002d4009180202c90100e04268100b00f42c800f02c444000a4a680d07562024011501113004068240e04600d20800008a91445d600c1d082481200601d10308035000902803d00094000d480c0765031816903000400580d41e020f106030055802a042a03112032601d00414028401d600600c4007240c80403198212007414500600d4000f210012003008900b11503c07400d082605640010660380f20b885000104840300e803041c2030082c41d458a0740c20140f0ba051a202c00d5810703080450301c0800a010504011081c4e01469010320150107403401651651000d4510030100c0c0038000c03064101c00004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 521803839 1250 521802589 521802623
    0x50307150309020916170c040b07050f060f01030209090c01020c12011e05070207060306051507260306120a0c06030e0a05030403140c0d0c051504150201050105090901180b04080403 79
    0x840d400340f021059a5418468480e000c90b010351b520025a03102a00303c80070300084c003081d84000001c1140c00c2c01002103078000c26419031280d03e050001c4030b1140c00082c0c080010400c5051202c0c400c1c0e0008001c4000c3c108141e50040000d540d041018a51340c400c000742140c6018241d0290f2219202030340b00c45460140400c2c11464002902c0d043d42d42c10014440c070000000c00b14801e20030035060719030003400c0c0340e1500c0c0110354822058102e808103072030001c50300800030044080890b47c641034400720340304640c0781e150290402c800d4180c4480381203d182c1001841c64005800003400400380c2e04103003000554240d005858500c1c0c0740021000800c0f5200c00a4040103105a84101c00c0d49603200104454102005805124030909019802030070341171903007000d01c5680381500103500d03c4031000c2c010504065440ea5268a004411542440036035901c0f0010b20050030007038071140e404500345000384801d1162010100f043c005072100030b0440304062000c642080303006000c031002103410000070310000602c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 521805089 1250 521803839 521803861
    0x20f0a08090445020117151c1104091a19020a0503060a05030f0a060b0112021206011805030a0609060b060c06090f1c03050604061e09060905010503071503090209 71
    0x303440e03415203a41d00903403483c0c8859002d03101885007641030f5900b8895480001c41084140000790004000c407241c0010001d65441e51b140c000c40041c1c10300c1000c1292992410702e0f90313022400c51184c030301541c00e1640000104d29032101c1c500e02c03542c52001c541c500d69038400112056018806040c41c1e03050000452002d510350100265000d61003c40d0201807550740c0f01e08042e5100504001074840c1d801c02d21503000815260741c40b8050f4180d042c146215101c0c00c0d00000c0317080381e11120146401203952010b1100650b44801c4060000b031076041d6101406013030500007992075466000c01003c02c0d4407074405008000c41c581001903029806030110352030300c0c0038078107043c1c03203800c2260184140e00c2107405c00400384030002141003443c29203207980c440110590300c0c201c001d440020502d44e08a521040002103000ba11160b5060001080041004070784c140381c070300400e40b400d0b5408900001c3c00c120050000c0e660115242d002c5805103d00c08004030001038058024041446c000707948062a04100090a02c02d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 521806339 1250 521805089 521805161
    0x30e01061e0f03031403040516060f020105060409020a090e01020906070f0506090316060e0f07150f020a02090a050601110709140604020307090e0c0c060a0e0d020f0a080904 76
    0x261100c00c4101d688800035000c100c02d0900c00a00050034445171480c000c4001d80003541c0081c000c0043d9011281d0402c0d550041d44030f00d500c4280014503c2003403900140e0f0a2180c6500108220380c184010700d140d80014181001c28017038080c0556a0301400710f00100b00754112040040b01505094032014141000544c0ca0945032003903d65000d0f803400034800301c201104544988601014800c15126607845a00c020450101c10824522440a400d0840042001280b004002d0340030740d8441408501c600800c620091000341043d03503c03003007541005070740d030b0051540d018902c4400010f05070344640c01221200303a40111009107000704000462502e009820800b241140c3d04c081c818942c545c3c030b052004a2004485c20070000e4001032052214414041c030050b00410007030f04403410303c901c810809041283c00d031a406100380d65400000c44c111014004400030381480d0001d00408121004a1525002010740051111500080c05500e554480c0e0110484004440c41c091728004d441c90010400301c6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 521807589 1250 521806339 521806379
    0x2010e0610050108090304030b0a0902010516050f0d050a08041b050d0f060c05091f020f0d080603060a06450f0b0319020f1c080a0809010212060d03030e0106 69
    0x31013800041c4a89800008070b40c1183d90140344003801c0d07a03422105030014071500b0f100324104102000500302055221540b5111070303000d50054645040080c90380c1c0c1c5442c02404450041c45018040600384503000902990310a410a0074142060703c000070012050fa6079070459a403042032a801001071010415014140720310a80c4100885039000400340d40034090840703042ea001d004a41030858400d0003100301807149005004070ba0400401703090007803c142c4c100b0203c5001132150010400c00c0c1c90104125500105140070400101782082c40d002c003107040e198640c0300584003030b8a10000841e80646c002c1607100d042805610882024100744014200e1410b440400500745802c011180c500840c81d161590188440c00300356540030327400d0000c101d02501719180e0200c1104800d5029400381031020030010304c0ba9050a950b5040303481c2c054000c40015104a0181e072040c421105101c1c0d16a0016400010444081600c0855841c0c110040c0c86020a9650f295080803030010b1804056044103083d28 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 521808839 1250 521807589 521807597
    0xa020d0206100b0405060904091401090506060d080702220203040b0601020d0306050108070f0c050a050a03080c0702030a030804080c100b01031409070915210b0f0402011e02010e06100501 82
    0x520341c0300400000b031016000d00200c0c540300b003004000780d06d041c03030082002e04005000440c8558098543c040444550906c2140594580904100b0010700344101d90388020201c07440c0c03039288a40d464844080c00380c00c00c028010300880d142d000080d42e445042180c4c01d9100c2e002590350341b0b401d151054118005844080c0984a51480308602c2ca0090103003c082e80c1040e560203165541b450004c0b18901d440500c540107100490718a003010501c107102d00250580950028110300c1210700d000ad00040c8010031841040e502801004010f95000c0b8000c0000e5825140c58015500c5500300800a4440c4e0001e1300d2181c030500303040d1050003140303400201008009072420080c490020034601e4480b80100c0302060076400065043c02500245d80c04004200c090b0114140403688a2021070480341403c10b400c1c0d091810f1034141e00c1080300014489900030106050103603a0304040d80040c00c4d02192212282442c0315030448146920702c00d500104000c0204002ca40c1981800e00801000444c0c50180c24006 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 521810089 1250 521808839 521808841
    0x11010513060e030a0804080a0302040b070c260307020105030c1209010b0f0a080705090a1104120213020a0e0108070203160b09100605090408070c15121b050d02030603070b0a020d0206 80
    0x1001001c404c2d950500c6440d210000207a50703a942e01001075011420346e5041c140d00780408681000c800002d00901ca1244004440301d50420004244112040191480d00a1300c0135026031954408015221001c3d428200291a5100c40c3c25220850091405a08984081500700091144150171904007000c0075103a01c000c80940d80207121030040d5501981d4941e600081042000d4184504415070062031007000040c04544808402c2c0d066000d035101e000e010403200b54034000c0d841c00c01c400c502c050700707050003c5240031201807025010304210b81f003d6050014880c0001e640758020300031201e011481c1401090341d040740785080d0040c0314042d16002c0d903c2c821030000d09105016840b5174003d03568002c12101050343c07140d58184042d44118411108044035280020b81c0303142c0b030b06800d18076000949a080b000c40b100303003100c811140e5006404440f441114644031004ed0010112103e000b4100c1d00541d4960700d120120f803410b0b01d242d01404418030002084010743d940801c80d106581c02541c25a102 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 521811339 1250 521810089 521810111
    0x40f05100b090a03141504150b0a03020d06020901120606020f0c040b030616140a080402011101050601080a02160c09020c06100302060a0c051e030c0c0a180b011101051306 75
    0x4030b02501d01400e801424400051011034249403002d0304045800c82140e40c4d116070044c01841d01c0c40199400c551401008004440c0b8060601412004503019180340040c0361854002a0301c1c59102030015200950016800d41d05912501442034451020401403200a9503810001e5481894000914060056021041e100e10345801605000325000f00288000c1d01e82107511034054118810540500404500d1564580c1910010f4084540c0d02c0c2c4400a00303103081d0001400e000c4100d085d1a03005d9140508010903681c01c40282078000000c2c440c01038403819141c0450141c8840703100090090410000002260180c54000340349000c030000c1030b035506d502c1c0c1c940000f8100d501400020340c00705082c0700c2c080c010fa2041d0301d13012103d4018001c50728448000085e40040708030b03204010301550030001d940304010f401000038001c490700039200710403130034a0925140c1260303803914560304000b0381b20315100c15036a2058145201c2e094402000b041507040c02d00059032104079100046808038208106094 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 521812589 1250 521811339 521811359
    0x6030803011a130b0319061d0f1006050901020c0a0306020a1b0506150a0938030606040f060305060c131205030306040903200601030c0e0702190302030702040f0510 72
    0x4024500d10f150200c90303003454920010307500010701c14a400308880c40c1201070310205006a07801000042056014441480c00748202960000e20710001c0c010002c09119005c40a80310340012903205140654a5040e0400100c0c00c0c00d114100d140d602683d4698003009028a0364000c0008400c3da48960301d6a030400c046040c115411342902130b04640103040080c46450201400031082200200f050002e65252440c00c41124100c0e01007000c0d40c11044400a485c0008500310040c40c0320240700000880750382c80000382d40b16002400345000d1901d42c41090540c14083c1c106601456104003540c00130b24160a00044980150034001e9641c000440001020383c2d600700c050007840e1b0040055803460b034400b03041c00060a1032440440c1080861a000c20842c0b050303030b08402a14606c6001b0389055403441c02e029881004641101030343c150700c1002e204446400141c80d42c3d4490900030810061400703805d0913070450080c200065002418030038a040c031208658402846400070300345050a158903240a01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 521813839 1250 521812589 521812597
    0x90a06110706020a0308070c1110051804021303030c061d060718030b0402010c0f050601090f0509010b03033c1c090b0c0f0708070507030519032001020d06030803011a 73
    0x1750216001d54040342e41c240c820781200b0301c40741c055150196282e41000c0400c2c402408c0004c5500002c1001c2100240e0040c00a40040042012107040d42031501c1c500d94a04c43c807119101c02424803d000100d8010066503410400300c0ba0f05180c2c001d40d24100d24180aa101c80c02191a040003691010022586010000e1540c00b96500046880450b43d100d80c019103100d5038425094403070f00f40659001e40028001c008440c042c0412220218242c0c0104400b582030b03d0b8064140d0415034140102d82c24581c0b4004181d03880121041d44092000f4a0a10844131018001d4131880e4540501070a40289840010081c1040e80c490444003001500c0c00d40304c2c00498001d65402400326041030046200c0c14020009000780e01501c4103001c0c0340803141e80da040c1c4180e2000c007003110325030000c010070420300c00180702d0040d40884010344103500103040ea4004101c401c0264403507007a504400801c060b185d00035810b4560003641100100b02403a1241043c1c903858109104002608101072010103d1629042c262 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 521815089 1250 521813839 521813843
    0xc030f15060605030a09031107062304180908040e04110907110a02010e01030227030634110f070905011208040b0306180c030601080601050a051b03090a06110706020a 73
    0x210b00b5500d540012101030106504150304221141d8030300c6a0940007406550014030180d1100c15440bc031000c4002e0034000e003c1d24601c1609030034001007046411032b18a500c1824650f800001c3d1290b043e140000c024010b0741c020004c1d80b204982044100320f404c105200c100312003200e4a4010360780b02181280c132078a805120103820b41051200740c0055014072044114000141005400c0014030000d0b02c00c1c2e5455114840c0c5801c00c881590025411f082c4050ba4001c1c400b648050880911882c0c1c4c040d47ea007120400d8070084040e840043e803071900c11aa02e5146610700c20968094800510358036030b5035145401103204146c46c040000580c500c408070320703482e0113501c488a6400c1600d0880200700070b4000915050300a500c2d00740d55042c21503401505807042c850320400301c1c0c6a00b0b20000050030310400422060500800f00100c40c2d80c4c0703030004123032480b07640c40b0b90480d080d03980781030001130540c0641100d194006602080c00719140b5000403090030205070341b4084411465441c64101c0e95041e020b500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 521816339 1250 521815089 521815097
    0xf0705062401020c091801020c06012c010e060301020708040b091305060d02011808010507020d0207060503060a0306050423030a0e150417031e04060305060109050f04020c0a0c030f150606 82
    0x28607130780d0401c5103a640e841040809840081b4000349841800d82e0b2040c42441c8140c0c20000050005011044bd020a00b0b110341010050005a40981006240d01806140301c440001800661150742c2501202e4400303500c10300083c2c0310ba42e248000740158100e140d880348140110350003031442104030702c9003610441c4003c0c45030544200ca074005480309000340004107441d0006a00c003103003910702402120b001d0341d040d038010411343c1401200241010171642050082107020403d010540c0c2d284000c070015a5003120307000559403100e140c120a00c01010490703044400410351700044a00c0e022002e41100700c15910340200c96080b0b9010401080020080201c0565043c082441200460303040e03483c01910760b204403441c0a0042400301f400d1110f1a0000440101c00503052200e00c0d41030207410740080c000c0c04d01007002c50410000618019440382c045000310303408514401ca800041117480045078008a0701d0850320303260308010194040c01e48080c3c401040a074400c2940d040386205a004554807551 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 521817589 1250 521816339 521816353
    0x6131e051f020d0c030e04060b0301240f050a050903060415111606050402281d07121104031502280801120f1203140601020a080702040f020f070506240102 68
    0x8416a4426450134042d81042486605002151030340c0c420302e4050440c844440c0d403a50315018030600030f804038080504414000026000005070841501001c40c412030a02a0720b230a040746084940740158151160302d4410f0700180f000b4014240741510b04482f5240090044800014050415200b04844015180c03891030184000c0340c8540d03c66500584001c02d0314140d0f448003010b060b16146804158555031211700380401040000c80580340c0c2d000e0401042102d02d2810b03440143c81c1d001c00c28416840140c681d00180c45420700401281c024540c482c4114165115401201d00203400201c02032401d49600132458685441e014802c807840c190035a1099566801d00555481e6007a60000440780743c004800e603400041c0001c5c5441c42c0c4031f07120740c1d00020003603404134180791902c401500301070540d004901e80c0008200002c088605d845e40507540400d026541c20030200092040380d071400001200490500208800840d80354000c03014040131001840d40240503011540d0b480c40c0e4140036a210170f0f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 521818839 1250 521817589 521817613
    0x8390307051f0605030a060b010f080c09010f030608010f090b0903030c0315180a05070f140d0b0d140a0c0504060b07121413030302060c070b010506131e051f02 70
    0x20424103602c400001185040c0d581c0046441c0010080d0101c94403601c582c407034500c55074404040880496185440200c0f400e10f10045a11072050300d0b01720341040341d20703100204114000e4224100516480008012004009421000a0007501001c036089854640030440507075000013076a0103040d040701818515103035002a40054003401c04405c2e0000118182401d0740ca169500852040028030804120ba140480c3c00070411805540e00c00207000d65980b188510b6660301007500e01003250b440e40010ba9200d10710004000b602e07000e80041090786540c9003020362903404107e02014900c1501c3d410b00040c1c8030810031003a9583ca0007010300ba04428446000401c0c80030a46182136102420720210a00c000b20b00300360f03140d01c030752100202e039000c00310b00b0010140c1c1000050350200c0c1281c5494107020080d964030000b5001842010320038000400e68003403030380c43c01400c000100119142409441000d0b0f8509103082040c0c8201352113034800264218003807400004d580c8400d0700503409440e096040c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 521820089 1250 521818839 521818873
    0xf070605031603060e10152d030b0d0c180203060d0b071704120f031505090403140a12061d01150306081005010305010b010203041a03040839030705 65
    0x4942e45000301601d078030300083e661440c1880503009500c142c041105d17160910081c0d160035440c1d40004003c01c4480304c04030b28000c62150318540fa000654420100998070080110041e007003030b18149502c03807200202c080c1007005201c9808100d07100304003c5841c2e40321220b03040c0100d00040f18002d81205440c0030281c00900020311169101c7d1641c2060490f2413070a020003a200f420441d4125012060503070052031641e0059803040d084001c6141c05e01203c10303420361200d814081840f541e4010360343e0f880400c0c01c01d8010002e00d03608044022031181ca41000d420010300400b443e514141c240c80c9400c10105410404003422000b4201c125125010b50746840071084068013100182001c065940d0781c00701d2441030902031009480f8080318085815415400e040f800c603081c099071581598020401000341c4842599989101030300144925200d039280d003414990f83c42440f10b00b03000081e00754821008003281c40d00503c034002d4030104510a031001e454416983c0c0c410250050802c1d4040c841c1c1d54485601 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 521821339 1250 521820089 521820121
    0xc0c0302190e0703090c0b09060910031b08010608012412110f0306091f14040902120a0b0a06140909070e04200d02010804080304050120040303020f07060503 69
    0x10038014200c01c9079641040c0741c0c4060140d40410010340c60b8401d9406200e09210201d0142601400c4d881c0344c034140000180070361207a90883c0380036a110315100d8000c9806540720b124011510358408040c0c030b100d06e4008210320b00900540002c50f241c0c10000c00c03156201d41842408007040c14070880d540344032210564074290304a0741082c0a80e2501403d1511071000740103008072a0f08080c141d5280d0a00c20704100034000b00418070794004220794a214205184540004100e480700c10300003200002c220082005040080c0010390440b18a8a09403020303c40001c03401d00c01401095003010588a0f02e0300c0109071200d612441b41d2801d2400b118007140d02d040041590841846000c4904260b540c40c079003000c00000b20750640d0403010f5400c540741202c0c0d08c0001c00080c207008031030040c0459142c1d40060258080035102528401000c0300042c02c1140c2584803084821900388101e0300840c58020214003070348580012001401155928060510001901001c1d5203030350301c032036095689503410b00c4500c40c9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 521822589 1250 521821339 521821369
    0x909030503190603120504030c1406090d05070b070b040b06040c02030a11030d0e0102130909020a06140c151f0f0e04020316060507020a15080403030b04090c14100c0c0302 75
    0x41d80703d00000005e41c645c1990007264542d0384071591201c0c514200610410180d901039400c4000304001d5841070307558501242e02c03524003114600c00c1e1803036078100315150800302d8200103408980022810180140d00e0b00f114852032103440f640806664800c00e020944140c1804540941c1c01400b20301c8001e070184a819014141780c108803030034138820304801b1080d19145c0d06006481d0b54001100c804440030031604401404004405128000d003c1d03001c00d403005030510482017044140411021201f1841d003c44107601303008401c40d8040e041c1d403142c0300f0201f9010784441c0c101d44c80c20311510f4100321080031100220340821004104042c5803411502400000170404c84e854003494107056841300d4186011806001c4503074400d9200d41031403050000e8510031b03412403413079101c43d05050100306511030380c5c0c540c5c0030764107240101e607120044c00400d000d0034510000074010307842d010000c1000036070080d9200f1010021650078041c9400080d00b48c1700300011050240000c501c5041c14401b50510780368812307081c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 521823839 1250 521822589 521822591
    0x9090a0b0d0b0c0c0d0908070308090d200a050a0b1204030c020a06030e161401030b0307080106060509090109060305030f071112030702010201140105130b0f030d050c07090903050319 80
    0x104566265810280100c980c95052000404c400c80c551340108001080365019003040e014150400081d155181718610004010100000d84022035899104c1c40e8400703c1d034031581c0f400c000600200c07841c05284c109458a0b006010b048000aa01e1038100502411a180806914a030002104c8800c1520f50000c009078240b080120808005031541143d00008003210307600058940b03550440541407408100500b05000c4014006204144d01150030528451007420001019407440d004642060210b5200205c694644640044c00c5074110000300b040f400111400500385e0b03220641002114030301d02024050303a00610501004c4a50000142910782c05030702c100c5204907403040003441c3c5200300d220314141500003084410865809000700d9049081da040001c000d0340c10040030416050740300e524a00c1d043c0e202c0090204540b0751400001000b040074040c2c0e0140b0619000243c12603000b4045841144185a40001d00c03072031612482ca400c03549551600e04d035886d4800c3c02c140700c41c3c0d42c1e8200f164003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 521825089 1250 521823839 521823859
    0x10224040203031209060103060c081e040516090c120c140f040503120408010c0c260c030a03052401050d0203060f100f020c01080903030c030702100507020c040c0509090a0b 76
    0x302c0040404d051084100c10006c0400c0d60461901805480482504000f8040c0b01ca0a001d1070245c0d541780300344020103100e45210503a03958140030f4030740844010304449054811001007514450354200ea001024140c44107074400250b090b4990450b159400c0c0c0384001101e01011007000d959450080000400c05503070582016200c000080c108401311540603c5420300141c108050f85081c0101d083c0042e0a00f09102c5087e07041e203441c80c0042c80300700307000200901c122099080084900990340702e164040708881d110000b165001e80241800c1d601441c001504440350b40da11f00c1011440c04c40f0580680d2420b041500000004019400103480b5540c0300c050480003054580f07500d580408081319903a1002030242421001a05100692880c0c40c100a424810000c90394400070840f03070001100c07061150b81e566040022410207400e1700010300d00500b01b405014509600281c9412a034408880801000600c3d407810340c1d41d440762904558124844a00013040034074190300602a628002e4240e03411 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 521826339 1250 521825089 521825107
    0xa0908070b0708130f240309050607050a0203270f030307030f031518060512010b0108040f0203070e01060c030206011706070c140a0308010e0c0f0d23160e01022404020303 75
    0xd0a4040c2d00064404046110f0401c140f03101b900914940c0f443d581400c1003012281e450312512603030700805200c240440040d900074050700c01c00071150f2030b50182030041d0120b2102c1300c4c004201d410300c1c03d075030b44102401c66000c02c2030b250200c1120595a8183c803904070401040d8015006868103094072030003600d80c0d0743d000a00b541d0003100601e100804140008a250412003005540e000714091005260b04d40715030368140d81d03001040140c01a41060202d8407054451000a00d8000b45800044417580e511000091709600701000c90511442502611810781c0c80340d854550001c00c02d0480c281c158042e40201e4001d41c01200610000b40c000c415036071034044291481845d00080110883c000341c64480104040b8038011103250300701450069180c9414582081d15049014603d4502c00701c0351750310341c0b00342030030807001031011440203c1000da025803404046030030b040c5000100400118505c4c2300588015880481c4000d480501d0714100e40f8140d5880300054000c600080003240c0520041181e809 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 521827589 1250 521826339 521826359
    0x13030f02011814090705160b101a1209010209010c1217070518090105030307031110050109051f0302210f010f1b020a020913030c0b0702030a0908070b070813 69
    0x751000d14401c0f0304101440080c0144d0b00d0008180c1c0741000824862001d4042d12440e83d02c2e01c66402180c030001c5900e540c054030580c2001e5034400c55004000e40c44403909880188050305a05201c00b4881b0070b15071303c0c1c002c0e1078280d2082c034003e1400520208017141c001032960004c19060000392421b80c2041c00d180030124504402990700e600441d00108021140000b5180480001c0300c05a5183d42154546400300e6941d0194540080a2080981110000086c10040344410710b8101c4014040c65a4900c0c1e210002e0005a07140d0840610000030010240c85104c08401129805407003441c1e44802c000d04005841c00a10b00003449000380c8081100c11032003409103c5035049142400640c2a4503600000f80700584a1549019900440207100c00359071141d000c1d543c8021805070182021501d0701d012102c000f5030b62401405070b0030100900036401d038004040c3c4890034054455000f03540d11040360954502652040c41e0600c54100b10b00000550801d028000c0314808100d010490341c0c403a82004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 521828839 1250 521827589 521827637
    0x7030516060c02071502030c070b0f0c06040c14030a02031e07090915050f090a020f04020d090b04050601050a03170706150602101b0e0f01020705040e0c090a0213030f0201 75
    0x100c01a0f021103400d00050305e41c0034401c0041600c42c002549132070074201040341c130350080e4401c0c01900200402c008801000c00c1c01181e01d2410494250382c2c02c0d240914155041c1c010900811414458001c51030000b402c0000c2c00b50f40241d0014020036001c803400007090010124a04544864001c60000040c2122580101d4030728511a60090b41c4e61aa00c0c1c07880300845000600032511041c080b0280040505c0126028542d0760b01030b501035000440e40030105000c0e114102c500c1040c0d524044802e000e0124103886e19000300e02c2203080d03540b0790740c1e01c00400001c010b10b400084c0851354100c80d141980e10345003004081c414030529010032042090340c004450b4811651106c005a007204a0000c4c141d190351207032080c2e02454105515140c2c80192004010f01c180f5840f45000d0b406010301f11202d03a00030440c070720050078010022300c1301030783d141d08258494100c19002401520340c140403802001c0d05000b40c54030b02040c44c503c040424617544564984003889802a814407208080113440080c1c070301c01c14 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 521830089 1250 521828839 521828861
    0xf0406090e03250c0b0306011806110f01020f040e10050319030801050102070b09040906270606080c1c03030b030d0906080907030b0703110c0d03090b100b0703051606 73
    0x1454851074045a546205400f910300340300500035910b104000122100e03010015075400c43c1a00c2d03180da48020040c1ca542480721015503612001c40800950307513a020078040900d89800042c3ca4503802041c02e01400d0b8001e080750750781203c1e0180001d2100b41c10304100c00d5031103a00c54084003800390f510f2001c6428000300303540c105002c0304c4250031340040c55040455980180310078401400c1e824500510301240340070b8948124800ca4582583d03109100c5503801081240c034400f0001016810f4040e004030800c48003540484503581854030008401802160211130f042001e00300409503400800d0034070108111704411024995100c92003061a1000c120818266945485844c6e1013810680080c180c608000c08141e2940c2c0320003000e000042c40c0f08500d0b500410207007000b040d09078504101c1e132414080d41402100c0d61007407860074100181d0503040000d800d4000c1c0454072141e1181208400004e915010b0f003842e9220410030400040e02c00e01c002d01d507071081c032142c2e5410044580d4408054a04d00145 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 521831339 1250 521830089 521830093
    0x11100e0a080c09090d08040b070c0506070f02011d07090b030a080d0515030a030e3307031b080a080601090905090c030d030902030c0d030c02120102040f1d060f0406090e 74
    0x100311010708014501c20f0304021104d00800c4540d004110050120400400041024001c2400f16880c03e01a80c500075459902005640d50751500c0000184504200160940198200300203030907010082e02c19032107900c0b800300161603000e080a039a036001d400c100f064150035200f5030300b40b58003042c101c0010b8406c444900c1400308403410540e00c11009441e0154110340320340c100411520000ea0422051040d254040e01c0c00010400940000350121603108140780d0300313000380400d40300d4800d26400103041c80c510a1300e41d203c2d1106041d04484c404494a50000c01d40c000c10003a1808803030041c0110384e0b2219052602500e6151205400010740d10142c0d44020b903030b8441440c452440c60240706404007506c0500d000c00c400d0881c2e8001a43d100300c0346010500802500107501c0c103041c070035115421030580141c29001454683c01d8154001d511610484282d0301d41105c01050b01122103581d074201ca0062079400388240c407510104401c40380d60480055015a890400107406075076802641002040000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 521832589 1250 521831339 521831353
    0x2a08161e020307121e03020c0c09060a050607030c150b010206181e010905060105010e010909150e130c080303100e06030f0d0e0306010f0f060c0f0b040b0403020f0a11100e0a08 77
    0x20401e400d04175102d090b00700b4103005000d10350348440300203030094941d0303003c4581c650036454082c040349210145421003600001e0004100c000c1c507412040100300203105403410410715084408210031a19459602401a0880d0003c00e610904500103540002600400d03184040520880e95400410b2891084480c1e51281c00d44c005220040c04094010f04007801c040440400a60000300050054056442210b07070318000e142482503a01c405070082c0550007181c8900b82000039445c078081070b4142086400918044d1702040008020054030b00861080001507005030400314072f071114002c02415070740c043c4968400760142d400100501c040413940c81e150a0500b942d50f00516080080c160082025280326580400c440182c0c1d8250b182103500c1450401c0d011803641ca80f0750002c4640c000c0103003214580b08144014404e01c91348083c0154440e800700c40304001c1103410a502c03408501000f03401e04000805811660612680f04040098546080504454504002040c04c01c150f0001c13071aa0b030040b8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 521833839 1250 521832589 521832617
    0x130b1e0f060f19170a060803091c0f0807020a0b0a0804020409031107030b0106030c020a080409111b061503010b031c020307020a0807050907020712020d062a08161e02030712 76
    0x304c800383c000320406020b0040a0074006e00703e90740c0c172482a07001d00510a104404170321520f10412460900c1d8441741c0304048a01074200070340301c0d4120b0741c016445102c404d40c0000314405064122014007006031103049050f0b5407602003000401c203210054017404a410342451803940c040c049100a94403e407040b4099506045004040701c8121a55070b0555210001007404544907000752412541500c002180703480c0d07140c045a2080c051101c21341c1125030b801c1c41d0480440f4010514900c514035030b40c8000840500c08081600341c4080078031740c1da00340d00068000c0d85108940001d103003405a0b180112413410301158040b039050202a4844003080d007003c20207025500c0d1441c40250030100c82e10080000c82d0402c440c050100b0010407009114040e145107040400049400100020300c00b104c6246010030b00e81a099146050780001100140c80e010004281c0000d1a4409050310000d90b01c80b0b0881c844100140a1203410780c203c2002c1d407005010100c00103c51850b0314507005080c0d600c9811020b000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 521835089 1250 521833839 521833877
    0x18061b07052403070905120309011821030918020d140c0a0305100909050f072103080a090b090d08060a1409070e130b1e0f060f19 57
    0x1034001d6441460301c460a10481c0304005141c00304036500241c5141e030303521903000a03520001254803550700144a289201d603410000b10203088207440c21b884104e080906c0c0701e80307086840480c2c000c0020540003004111444030340001050007052107414040b50303464840b40403441d115641c55024400a4001442081105c0d050044000114408214480c98145410030284a028550520007055510740c0010551044820500001d0009890400041c0c409042c0140c40d00f0030000721000038800c5500c000303038144840e0240810042031200d5954805080e650440d894032000d09a040c2c41c0c1c1d10381c1d80030030100d00d68900c0b0030700481480c0002c0424520984000c0c4c500316000300341c00c2c4200c02506042010001000414000000403504070b05a50341e101e10940c0d4245270626503d42122024270406000f58040d0320401c2810070481e1040c01ca0600384400d5281180c203036180540202c810180c3c1c41160424a010302940d070381442442d8200b2000303600d040343c8681c40a03100c00004a848038045a00402 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 521836339 1250 521835089 521835103
    0xc0b03010f2d0f1703070b041203060e0a05010e1503030f0a05040509090a020a0801181112060906060a23090414060c04050f010305040f020609060c0f03090f010503010608070518061b 80
    0x3d404d000e94140110307601d44403401c03080244050418400903034120329080c86a07001401400c815546c001e5241080d02140b0008d00c070034010540d60744079840c00300c0c642806407040da060700c0b04010001c52400d0341c0085551010b810501903107043c00010301012410f5a58040342c140b20312011001842e807403940380100881c2d250154054181c42c2d14090125800e00328640740500500c0c1c0010980364165013000c0031500800881c00b482c4140e0140d00240580703010049142c2d801002c3c101d408071041621210051500075420780403c1484d2603513007410303240d07080c9050881c1c1c1c814007541043e40e9042c1a0404942804004c41d008490103c00040503c1a8a44040611a1207108aca810000f924203651507215151000c80b01920400001c0740216660751080111852920020242d4204a00d54040281c1e03035005814000d11a20920307503800c0d050751140056038103d0308a951007000ca51542513007994164001c0004e01d00500164103032001f40e07202c00004217148082140d036203c0c0354894244044c1070140b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 521837589 1250 521836339 521836379
    0x9130501050709030f06110f0d1d070e27030a0302030609010e040503030f0408130f17150c03090106050a27020f0703260103050a0c0b03010f2d0f 64
    0x41d108003800805c0016040c08401075002c5000204200c00c010601ca0385c2c09003044410705032400107002050300d2030725044101102c100414064054517100d0440c4c1e2600c41501034118440c0760040080d0740c0300189800429000c41c0608006030118610302c0d260b0656100c01c0014001c03a800000340040d030300b0101080c90041c140c24405c08070b02e0030f05030354264581c40f000e00789498202c140710201e401c0c0156202103030b030541c8a4182c52000266151805110343c4c000e4030405220f4403a071910601d000b01d010601c5200c0c442c410041d08901d03507403400d407035800f03410240c507210056507100d401080a894914401c0b000c2d001c41c0400c90019000c0080480030b0342418146c52440320b005101030954903ca410696840a9060074402c00c5013001100308480000b40e00001c1041685490000090041c04900d60030030350f0040d0b0252240319125031061165120a200700100181d00030410807020185d229604001c00000e01140c5054641c80c04411608080b50000030140b01044410400700c412012a88040c1c2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 521838839 1250 521837589 521837597
    0x80706021603020d02010f0216090f0e0a080a20032a01110301060c080903010f0b0102061807210c0602010b04150f060e0310020301080307030801090e060402011409091305010507 78
    0x10b4256800b0802c03007040501c0c0203051104000244a907180203012102c09a6010388842c8100c0b6558100b40d4042e02210070351496040c41c2c07032481d603030b009400300d0b103808802e401c0b81400d49800407642c002c0390506400f4100084e9441b802105d4000d0880520042010a56841034141c001c400b0b101c5100c0c0a6001d001d000001d0ba00d000044c1060707104000c01d4a045804500f08011100440e042c15141ca205032840306500d54601003070148001d11690100d00b00d505d00b0b81c202ea01d103986540495403d84154070b4080f101c2d6006020820003001541d0020440c8400d6003800c0b075090499581d03400d18040c0710341000025175141c0402034030900742845514088000f18519501c00c4e480e05040f03e0912a80d8000c0b2010410100d1002c00161002c001001c00c00d40c254034115034035039546d0812074a80d040280118000340003400002400311150160010070030005002d040c0c581c4a0f90700640c1c450780f00f00c04403407443d1803d000003c410f40d05c0026551007850b000e017074190103900c10324060b400c5030402840b1500340 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 521840089 1250 521838839 521838883
    0x20609060406020a050d06152319110d0c0b130809060a0923010305160816300606110d03020702010c080301061d010806010225050a08070602 62
    0x15440018056070030a030450801079840c0491503048815100d80e40c008440542068000078a50041d0001360108100c1c60380c8002042e03607207403070007600381d1820507115401050030301c035145140c0c0c031640316512102c05c80c0c01d14804410030041c44a0800d541c65115030701140100d054032040c483c191203070550000002d0004c40c052001c5030780c0d801440c000c01512600075040401c14500c10342c05010030f04043d12001d140c081c1030700ca18443c0002241103404a040c0044d0810780400d00e01540103080703400704e64a07500c40e00415030707400d40c00c24507644c4888820020401a241281100c3c0d2041c0c0768100700c0340c086440c405188071b044c003849050341d405600040030040784414407405020046600f00c0e000d00c051401581d182c04d50b0004962803030fa103642c043c020f070b00004000200181c00201d412a601201d500c0714503110144001914031007000c036441030161f0030400024801412006800040e4080d03001c01028144e00c41c0c000c9203401c249900202c9140c2d0148030140000d540410010a0320104000e502100c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 521841339 1250 521840089 521840101
    0x15060630061002150c04030b0c0418090209070e0f0402210f0105030a0f050109120e1009081b04090501061e08061501210c1e0302181207120b160206 65
    0x19035030754001204e048414110110f002e100a410440d0015900080015504d0414034034180482e8020310400041003060400c031000cad130b041c81c0141c0742c2d1a0780081c4094941e5840d41e605071240d01c02003000700e502000c00102c9001540d40c5101900801c4c00400440902d840c045244440202c0050001001281c20340c0042056580002ea1a030800343e1040181004c058203203006400350003d85401084480203010130b901841d440000380c030040d5012503103c200031140307a2040c1d0303102685000305851608400180c0c401510030f44c0c0d44003125000600b00084140d4903444a03400c44181d500101e900f6403000b8840e40501480081c0f40e40a0f04001c00580000d04100c404180440c0815400c58180606503201c5912581044508080c004000c801400140a0300b10f00500c0000c92416603595211505550b0003c03510030700c00e4420380e0b54990f0541485040800c00c1280441c400c05a00380180308c1c092022800c400c082d400401c802d0f100c0c86003100241031859180765880340d00000c00003154421820454 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 521842589 1250 521841339 521841343
    0xe0909070317250b0c0a141812100608070b0d09140d02161a04050d080408160810020f0a03050a150605070b07030b0315060630061002 59
    0x304076a400701d07002c2d051544004008115020b04102203000791400c94401099155010f80000300350b10400c50008940c0c1c1d079003411032660089654090001c3c40414219400f0940103009000d484000c80c0310200c44000d03400007504409a034583d407030355178200000704180709065005500103091801d020303000181c200100c1c600c250050706140540ca80d240c0600798140441c07a6424108801001c0940b81c0e2050702e5000a5030340d4054861880300d080ca0f10304001104549038007030072803001000b54228030f041d20b480100301c0c084040c05404d80c2c54650030000040c8004042110b8a00e402ea150640e449a52600f00440e0030080100070405206004001032600540c00c0c8044841c6079245041c005895160703151000002c04d820010720040503d11200401d0054100010300b01e060f105190046c8250342d55a011402d5600e13080300160950b01411611846d04c0080c1d503015480790000d0440c0303041c28200c801d449a030103c140c03e422906005041940034000d140040d095102806071103184025415043c025 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 521843839 1250 521842589 521842603
    0x605061e070c05060340111201020a0801060e09070e310209030601090b0d0b040303020906040303170f06011b110d05072306191e0f0e0909 61
    0xc0c64800028544003004030000080c4080d0001400301a120302d454013041ca0092213030b080400d469142d642140e2107001d003031520440407280703445e07000300e480b0b4840e90340b4050a481e000c091239100d10740180c800c004940910140a0502742c40c1e83e840e003207515104010b010320300740d840f106010703c84140c104028281c1000b05800c199800703540c4209085400d00650308820314a80301c0c124807800c8082c032010f401301b540c3c0251a4215048040e04c4841e40d075041c00000b2103507004006030b041010b50100601040b0a00d80c01a1300600a04001d850200d82c0400103001340d215070001c9002c2002e070002c9080950300b5100721613020a1900c00108542403100010b0a40d00804080010500089120f101003000f40181a0350840014048441a0245141064450455008072440b81302c900c10000c01807240e5995540041c0340191001e460040f6541c8054194048200312030184251402c400c03072008114000d002c41401d00b592030802c4e54807500070041038038504c512260720a0312017105008083d00d02290072 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 521845089 1250 521843839 521843887
    0x316061107061b0c0c06080712060b031504051302060a0203070b0106090e010b0c0a110307080604061b02060c0a18080d0818120d090c05130f060e0f0f0c0f0c0f01060506 74
    0x1111741d960380c0c03074027110400c0007044805000384c200724002488810020186004038881422a065003d00a051208460b000c030f89107900041c00540d450003600b480b0009124080c0c0502c141c074038100d02515032594504007130341305600154040340f040001100c080e055902400b8103c3d81c6900d40760360b220005a40314007074180501315042007041c800e401e030b4041281c078000348402015502c0170310f085c0c1000c4004202e016524010011450398a50070b680c408691544100500307a4258140101000c084440e550780302000d99080012000124020f1010050351131840c0841da00c06400c0c4c80c000284150f48a000700a1000c0c40e440078048a1f440004017080d2a529420240001a00340c00f50400340710340d002c0f607444141c110480301120105140e094104c8114851750080a1000907515045001c0b2100700f02c85000102e2580c6000c6684140350741da1941c0c0216000c182d0320f08105280d195842e00d62302100c031002a40c0d00418460082281c20b010340002031600325140350801c04003026401c241da80c10800 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 521846339 1250 521845089 521845097
    0x512040201081f0e0402030d02010209032104090e030307090501230c1203090a05060903030402010c020d020a150e090f040c1a0c010c030603110a080316061107061b0c0c06 75
    0x2a206803c2010030110950910030101180d55540c00112503000042c2d6040c1d01030301807004007811441c014000c07114040000f40040c86d90b000c240101c840b07074000c6141510110b174010000040d401c0180e01504048010041c05107540b81030510024000441d6640180c3c14000006211004204c201d034420031940102c20743c483d92540301012082c10800c4c0712901c084041004404e00041c0c04001441d1500340c0d10a008441c2e158951008156480c0001c49000303000414100c0300c80300500b8540d40b5182c2c0da61003c0d024109881e229002c6100300c44e40c400c04a4000782403400c01c03084624005280303541044900014085604081d10b555100c000c4a002e4000350241074440690510502001c440324408000000c2100302e82c0312100601030141c1d07110a50b096942c0c10400d000502e004254401150315000007107240c980110102291035045200a5412590300c104c03034004280804010080a8840d135400600030540d48000c031076010f0028901820071039046040c100046000448100351001814 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 521847589 1250 521846339 521846341
    0x3120c05040305060f0f09030f03060d080c01060e0a1404170c12190e010e0a140a09050f0103061112420f010302130e06060910020601030b07051204020108 68
    0x2000c0d61036105070ba200070400d220b000c041240c0307070340c51061903401031810564440e00c0f900c50914550b84ca001d81c002514146004101048051404040c00840a44035031034560400110b1f24169084520b05e0f407040f0701301500340003042405280e41c0b1030249061350b202d6082030242020340b60b110360007a05100034a500e8400080c0c0c410300e90001c10409211032402c0c00f01d1a694442c5a810100c5d08070100a80c2c0007003410f12110140b1503000b181d403d4200e03140640140900c5160108005640255612491300080020030104900100e03008841c403800be210b113011550b514502e0310700c0440c0c000440c0700e0503440040c03050b0300c0c0d6480300032140ba4008801102d1040c07041400008800142c60380c48000d0825a960007403c050a042500c4420f1440c104440304208110424010740907071003885004601019541d40603c1072840409183c3d1b0401e002400f154102800e43c004207100112440d081e1002da4080401002001310302589280d2120803407400c182802d490300034128141c03101500090502c28620 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 521848839 1250 521847589 521847611
    0x30e04020706020909190f0e0606012a06090203060f010501051801020c04090501090204200f18040c0203042d15030e010515011112121b0d23040312 65
    0xc1c050301c043d80700003800250142445001c8680d0b0001214074642c16038106803098400d190740380318000081080c3c402800d09d60b0303280c40c01140c500e02014410164040f0801c100842040382d561014038086c8038810024030502c4c140109403615400070407030b1544526607801440141d911205403100240c946015000394012540141c1c01c00c440c800b010382e041841c00007481c00344041500010041402038400300840080803d000d48808049121502920800c00c02518103011007070041c01660020760202e01e08180d03480000381520400f0501000691000c0b80038007a0741c0e401c0380c0da6405503032003044014454410700495044002c0c94450200d41c0c00301c00314800d074414001c0c0c0054151000503c000c2141d0725059540c0c1440d411969030076400580b018a2145010400051480000e4001c80310b1038200523141c43c203441c9210009040350030358034903032010030b001440b00030181004da04e5405012819100d014482c080d030a00c0a00c0c101074800082060001107a04402d080d03a42452200000c48c06082d80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 521850089 1250 521848839 521848841
    0xb0a1d01090b0d06030b1914040b15030a0203030703030219021b01030e160f211a0c0f0703050909060402091008152d03150105010c0201170a06170a030e04020706 71
    0x75800038045080940030821120060703200c69503d0741030385130200300c0284030030506c041448c0101c500915241c941c802084820a20f54940300707c6040040849508655950109040d0b0304402800c81c0440e80100f412200d4001504500081c2e00c245e01c0103110180c040c1b0005582041c42c6e11070030b410b040c3d6504401180020500404400901c1c0144c11410540da0340c41d0700d0648440751240074543d110740750060600319150201c080e1465003190071042109200403040c00b140c03c000c1c000c106800c104020042e092004080900104d5000752a80c40e216500070091200548008050301e2140e4410807444880b80d0340d0300903060440030b0f5850100b410f6034541d12504c900000340d500c15030748070b4000d40b9105d2401c10881c8841c400c4140c000d154500d24281c04042c1651031200c03c1d485584000350f00010710855102e203003900d0304a1300501d00030300da00c0d0101c100300310215025142104215160141400150321800300e605802c1e4503d0018440c0d40d806480050042c14003040841c030981d00003685000740170103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 521851339 1250 521850089 521850101
    0x8240409140109030f02010b010903030e090c070b0c03010302010e0a050904140327040f090c0b0d020f03070305100b030709060c020607060513031101090c060f0c0b010b0a1d01090b0d 80
    0xd0308002c000380c0203c0d080c06040846121044030040d800d0010280d4554402c0f0640c800b141d0303054458040c00d000780410070040712001004450102d20070f0100c40d000c01c80d130b88400e500905881141a0f0359504500005008402c0c0e41718160040c14421020021626000380e02c650003504500303103a1030040c400700c01c1819481081e5640000a184520118a65a50106015540f24219801c00a407000c00700c805090301c1c4003a4014242d03103070603c010850000e40340000e100da0f0381c3d052001440c0087d0f400c002422a08161010b40003c1c6c0c0e81e504101d6420784800c2c1150140100000f0203046142c4802e004100c00414014001089034590100c81151118400d8508265000c070007440340d45440c03014003081c8120942c0650000c2c4100603058105217043c030856030740c0c0307421140c1c02d0450b07814408107a4070741940d00812001c0107400e41024010400b4032240034007810b151010640d0712944504014240302403100c003900b44000318005140d807681c01c03010060464268480003078690b20300001410060007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 521852589 1250 521851339 521851373
    0xf12060d021306080c0411040e0a02090406090501170c0f01030b01020708030a080906011211011409120102030a0b0103023c0d05010501030c0e0a05090a092108240409 73
    0x5590000c0200400c0c65008201130350340e0001251003001040d4100010740d07080c7d80c82420007883c00c000a1050400702504154003025100700940703410700c5000854100d91359988040340840e941c41c0144140d1420200703400700d28a0401c0240810100103001032110104283e28a041c07503507401c1802504c2c1d000341b0282c002003159100792a140c5540304000340110343e0890340082c0034041c40001045440314404941c50607034020a1141a0041140065400508030004d0040c054024000b030350741640e8020415030701c0c94015001586a0900a072290295280c1502550500d4014040660342088444203da0281402980c407000c2043c3e401c46020003a6a410450850b544002441c044d01041d0b600b011381210001c0c0d0301007040d80c03c125822030b100303c114003600d82d01040c1c00108028514100c00c2140c9c0010103e5000200400542e40300c00d1401007954101c0000486600328400c02a0041d070f020341d1203085003250040c220028100745004405160481d841a44c2e100c000c1014043d0742d0b0100d1412079 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 521853839 1250 521852589 521852599
    0x503150f07110f0d090b03010815130f0515061c02041808120717010810050709232b0303021c050f04060e120a050904020904140a0b01050f12060d02 65
    0x40c650f40825441e10707007403420400826140d9800103000d401c083d040704d04030355401c005031642c1d42002c540b481d503514025104500707629084030300c140420461205003802901c900014445c811280c004034032560300081c0300c03611881484032802006540214101052541154001040c0a03144c540e00007190174900c025000520120380004071886440040b07000b14040e03160019060710504481c0c0e0f82d50700034059031900750070075040880b00c4040c58001d2a00510b11b8100204410f03200c1d0700c4085040c40005079108000b40d036202e25441428a00310805c0c1e00c8002d568044c044502d0400c1d800c2407980300c014018201a070008520000c40c2d504640345a4003a800201444503040901e114402108141d8064400c03919203105000c0366240042d5404283c00c0188200d42000b2141000703445e20b80049082c29000b54003000324028a996600c030b142845200121040b0309400c01c007844100700d640d000c441134140102040105a60308140007511041c00c400301d40401950b46100c081901c07030002c0c0800075004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 521855089 1250 521853839 521853853
    0x62a0602030112061107020105071212050c090a0503120f07030302040b1803060603210a09091103010f080303091b2106090d0c0803010e0709170d090503150f0711 71
    0x1980d100f03464505140c007900c0c05111051112144c40158031400d900280865420848400040c0c100359022000d1080e905150b00030208854045050310012107000c1ca200360001034040d8035142619003030015080940060103881c2032081680007a200b001004079100c103020485500309482a0102c80c0980701400c0001c0c0c80304513900081d0210604030300d03080d01c00d01072500080e8107400c000803400640280440713590030f0303090714804038105607200303030461801c00001c003401141d030720600d010b0403242000c400c0800b5569890b000d04016076043d03903004600c0302e41081051180c2e141c8001001c4140c820640781341d00d9440403400000d5041038598074108000550040d07846070b601000700c0d21611458051043e18040c916884040b030360086200030081800700300740014071240342c000000940c0301c0e6007810030000300380c3c41d14600300305148521003452040e445158020740f0680c0c0400f004c0f008003070544c0149104407c40c3c3c2117500707440d40140b00c0c0c8001035142c0002510306104448100440c0c80304010b80300c3d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 521856339 1250 521855089 521855099
    0x16081f1e0c020607030b060c0c041805010e1b0d03141c09230c03100e07030b040809011d010c020f1c0309080c010c02010c11150a0203030906010f062a06020301 70
    0x5603c4202c0319030340480d1074640400100c0c00c150741101d01502501c0094002030039010104401009a604030a07420180c0310301d6640051001d200d206010340540000300703d194920754130107010500c0707020703020701404418949400190300814041c161102e140c0000c1d48442c4034a008058680324500f95149241c1441c040390b0078014010f914500f14102c45221a02c207004122030b240d991074203214055050b50000d0a5150742d035a2542c02050100180710540b0500f41c0d407034407502e40030720098406540c62240018028055a0440260520784041e58901c002c100300c1080041c003413000a4030060f000350071025810302c80d07640d408030003a041003801308060407003112410010326040c3d4038040c003612803089181034562903000d00d00350040160305964404074440b07180c0d1090081c0c82490207040d00a81002034541001466201404114865500450300d07451300021035454007130181d01c114045081c190040c4406035002d0805134034074001603032881520106440001500005a802501c460300c04000812 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 521857589 1250 521856339 521856343
    0xc0e041a040614010501030b03030403110d0605010602030a1116060f020a0b0a0603140c030601180b1e13060b0904090c09020d14070206071b02040f05040516081f1e0c02 74
    0x940441d004500d6076440c5c1c0c03180b005400701c3d44024030055250744140300c01c20008502c4102d40049c0c2001610704861031b201c40d592034003651030030b800410150b000800c55500607503102030342e505255010401040000c4046401c100704613110b02450042180700d80c190705510f4020040003034202d50010220113145064282d0340020201404100c038064580b035500401c1540c0040e202600c00c0c001000f420031a441e0041845ca1f082066040c80754141d122801e101c01a82c0c0c3e9500d50921040e400c10ba0700c81d104031007003000300094488141146d5549000c1080c46600505015102810f0042e039000a40034180e0400c0004080c0c284d0004100f140000f4801c00c0320001904405c02415003144401d0a80d182e11034140e89130001100d24200003076540001d03c01400c0c142401c140b0711400030b8030000d4407241900a48044d00c00460301510030350b02c8810500f4a140c401d0306d6200c01080d101000d0040c4120020b0600030305c4e05160078010715503032600035244881106112080c042c0c10304030020400a0310064000e5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 521858839 1250 521857589 521857601
    0x30a0e0c090a050912030f01380306011b0506160527040c0f08060409110603240f01020303180c030601090f0b0402031504240b0705060903070c0e041a0406 68
    0x8241d80140030442885c00b04250551b4041d044e40682104140c1c00c00c0b4600718218408021030912540c00007180350107003080c40441c200c41c804051403598a103082400989441016001c416001d8103125600003c02d502245680e00f0a0700d2410070761f0b64070b01041084a0034041d441c2c40c80c10b500c403808400c220403000c80312041c4101201b0f40b0b0138090340c1c140741d1064030808445281c0c40041980a00090f400b40340030360204030312600c00c801402d9200e02d42c40c04078046400450301005900032120940c0c2d0186429413407002244000c0f28035403807130081540003d44031700001d0b01c101024261500c02048a00701801030321240f46002c1c4c12a81690382d541c522201500e00318048460341841d241c0c0c42c0d09607003024000c403071003108054072402001c02e554003400010101081c06510800080080010300700b065003000008141c10040c15446003094202582003000140c0120400d900030080100011096140901100c003580140603042c0e441d800c089819003100d0080c0c907142c1c00200200020407100d81c3c441 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 521860089 1250 521858839 521858851
    0x200406080a051302010914010c080408030c210409020309071502061608010e040201181e0801150f0e0a0905010f060e160909020c01061224060b030a0e0c090a05 70
    0xd12080d01c802441d03c0070041614006070004101c003906008407114180031802407941071610501e0030000e40c0300c0c151a44c0144e08200b009030000a042c88a26404106002d40450816802a24108503888103a40d900c200d200b82c6150710780120001d078118000f4440000109507400d040316542e1480c0c00700a454040448402c0d0501010400c100341c11232240440302e05840405a0300e0003141c40e41e4006542040100301c00070703c81020000040b9102c115440c000317440c090803a0300081007070f0030503130202d00356541215030084604c4070382020402140c080340e11408039070640b4031244c0c0b0380c2c89454880b0042c1007040760240066007032a203244452840ca61142040350320400d00f0902c161a2500d046034080f0304500d81c00c0014800d01014086c4070360a47c01800d958940030000500141d607845031a454401c1e036101a01c8200400402d15451300c9900c8115085caa01d10310301300a16402c0c102c0d10780c0325000252040c1c414990343d00100e0381980301000040103050340142a00b02034900b00710114050007003241d40c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 521861339 1250 521860089 521860091
    0xc0203040e0f0105010c170c0f030d060b25080c0d0518090f04030509010c0c03050601032303181302120109110702030717120307030b03011d0c0103200406080a 70
    0xa525803200740080d4144d83c2c0582d20000f00e2036154803450082c144400c05101915801c2103900b01d0044200194100b541c0031401642c5c03600f00c018081402c0380d070a9031240706a42410418490007511070481c04903030346c4421986421b0300d146c80c108040d4900030420480c650b072003110102707461a40c024020703140d103241c05860700000100001c20310010090689115003c51440c4010800007400781d000791401c4501894004466903040c1c40d4001d414049500644107904940c005009101104094000300043d403058401d451040c0c2408a942c3d2051120108843d405841103003825035404410241d41c0b010142d05540300c0004018141a0440a2103128902480c0121407200a095030040d10600c41d0002c0c06002c205183c070440d512903015115411096002d00040b000d5400c198501442c0511000c1e07500007006001ca0050500310703401c6200c03129605101c03000002c1d03402070014900002c1d800a10380400d00328443c0c00150b05440b281c4410040b50900481c1c0800c01355803024803280704da454140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 521862589 1250 521861339 521861341
    0x2060a06060e065703070201030b1c080903070f030309152c030706031a040b06040302040e0a030e030a021f0e1f0206060a1208030415050411101718030d0c0203040e 72
    0x6004900a14440101303416900184441c1c0050b41c0a0f520104103440064500031025190030310071000c05142c0d03081140c91460102d03030a0914101000003801600002103040c950b103080d40c9019102151521030401094206041c41ca4442d04c40e130703035014200b0225141d042441d410b0a10800100b80300c2c2c41480c0c003030300c10b0040000e6800d10901824801c01c00001c3c40c07029000030b0301c2c24400035201d4000440e0300800100720010040e111403048086c0403c110014208010070b070700c0c00074100c41141c00b21511036800f10050704050307035074090041d0040049840441042d02995020380e88000c0008182d64024200c45400e00e413a2428611201407402c87e40c00ea8000f96110310400c0f826040c14051080003401003295040010209802542c009020350492050300a4054110741510f0049400310380d590282c101030105402c15200110383c0030000c0c01d262a81145199041c50801c03001000000c0c1840011560080098240204c94415601c040181700102c4003180203541c960041c4503424860440e40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 521863839 1250 521862589 521862727
    0xe06011805090c090103091205040f09060b030c07020102011506020f100612020d08163002060714162d080a03021e130602060a06060e06 60
    0xd52001d480c0010b00c00748050701c600c44815810341021900700d05155071007200b080859460340c40f60010344120b81d1110350300c41c10b0102c401080c50740ba80c4500740442c2080303010b2101000380345c180c0340c0c80032003e0300941d224041400106c0c0074007852411020420042c000c003103082640400c0b403070440242d08044800b01c422010141040380c680388100d40b030011007981c110300107180c28003503a440310740160440760a002801201d0301d00c4c645603c104460044a101c0c68580081c500b4007400200e203a00c01c3c40c6040c00703041300400fa485a0000700300c00100403400c0c1d0748040e0720b0342490a82d00100c886140f000d070580384501d08070b649140e0004610480d04018044420580203440141260907840404c0c00d00304420042c0a40282d00a511283c4003c0078003107950903071010000107003c410211001400c0407034501035000c1d0a02101500303034902c0d5030510b0710a110440c2c00020011040d042962036658413a02c00c0d1104c40302541c580000410b2200701040ca0203040b00c028400b10000c0c0008034450660182a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 521865089 1250 521863839 521863877
    0x4030905030c0906040f060f0929060715110a020601030b09060907060f091203170a02040b2a150405060717010e04020102070e0a150e1509041a010e0601 67
    0x64150740824043d0028080381010303041441286001c0324045106610b030b201d01d4801c200140c00c80c07a80283d07500c00035a082c0781c81c224030003025142c00c69200e528442c1040450b44510403030002500110410a40030b144e100315500449085010604064961004a00083d01d0f40c60a110980302d061210011941c00d500120340c00d402220450000e000d4685045015184013900d003100b202403190000c40055070820030000503102500c20750300c140410090700c0c50020441806040060090720500062160070b00c0d000c221071188800b4216420802016100340030318070005502d100729400b0340701e41c00c1c0441011000e424000c034070440c2902c4c0690f50300300701240c4210907400f042c1910154803004200211401010030342041c0188140c03091903440303541c1c00d4042c0c00e00b51060429151f40b46040d040031052440e09401504003c511608103003448006036603503401d03045107144914801d00c046010041c0f46a90078080418540c41d0ba40c0b80d42e9185103100742001d08448803404101c440c100000740d0383c20 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 521866339 1250 521865089 521865103
    0x622090e06012102130e03030109020d1a1c08070f35181207080303070e0f0303070b0c12010803041a0c0d0f020a0506090705040b0d0305030703050c071401050403090503 74
    0xc603a4041201200136000c01002c2402d0700007240460760b0321b555816a805051000307502900207030f0800740c0c3d40c6465114001c00c40e904954090fa840b058508110f030f090390703598070761100031004050111041c1c080c1c4c03c0c044c00520803100300910869a580754002003101040f108140c0301e80c44000091a040180354102c81c1c0b040c9003030031200c0c5000c00c0109042100828000f0150040c028106200c50488600306600c0c001c0150056100c40e480481040251544410413008000c01552280d8140c2c0c0d00501007a031b2400395010041c480d00c0010300141d1107040200584012040c1e034030306004156074503c001e039102c1c0d105020f240011481400b5541490125008554070142414018040408180001c90345c007500000a402103028801090000c86c02c10440d407400b50b154080600074040c905000c11003141d502002d110700a200c02c02c80e550110303030010140c0340d01c11064140440d140e42c034803225040d10310640b00010040380581110b224021015031003d48900d101f07480e001052a15582056922781d9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 521867589 1250 521866339 521866379
    0xe0918330406110a09030c0605040518060105130e091005040f0b0402010e0307030b100f030308010e060307051203070b0a0e03090609040b040606120501060e0f0622090e0601 76
    0x864890080d91008040415445405000001400b084000010b4556884003070040001a9191014002d11901e411030310010100c4e030038130624003172410021400c4a40124010030140c0140000640b0a90151040710403c00d4840d2072500c07415160701b00041110402e440d41003c41c0300344000084401d41d24464a80203507004403038612000d4079540c840508000050041b410402429800791168404000d03100c003070340c46807410003907924205c80d000003000c4c0d65500104080d483c91000b00082178005c00030a054402501c602c0d00c4a9803000042440e000b0158001c54114403540300c44800d604010014203115807017103120113190307240d464100090b12900024801c103a00104100f816a140100061005d45c60181020450800d8540050100d13122a032003407002c503942010140d2000e8161184c00c1c0504136509005034a10b46290100e4119440142c455004440c001f8441100e485458814443c100d0902900f102d840e0301d5411180c090300351003030001081d204a40020a100030b140781d481840314 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 521868839 1250 521867589 521867653
    0x606010201091703040309030c08101407050316021f0204090c020703030207052202030708010501020d2a1a070306092a08180a050a21080a0c0e0918 65
    0x101c8210114040d90005d03000f1000d001e81100000000340040203514001c01c41103014000e448201c03240f07442560a105040c185444000003046038454105081e6904440d03101c125a10740358250505a01d0403511903142515224600e0074900d48210a40013070045da64080d4084c444c03041100000c1c3d0361740480340070003000360300b003400103005034103208aa4030240c07403118100d0030024091034608000c03a4000d891940015480d04d0043c019560100f010201c41d0a00340303422000c620000200000041d120b0305440c9070046169030190030301c90044001e040c03500b501202ea440b1802c0058001d401002144a010100c9003884414020211100c042d030050341040c2c038102180d4022000c00f154008001003800718103071100032500c103c400040200e00c1040d8031030001028060814180350b1103e082c06503aa14009121102c0e0550403548602419040a003854001c100b0f80f40000b015200902c40c550180d8026070040100301314940515081510080c150080d45d050010b2507502c00d1b400e9860700c01403c681 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 521870089 1250 521868839 521868863
    0x60109062115030c030b060a0e0f0f0c0f0c0c031c020601140a1203121b0203090d1e08070605090607020303011a0f03010303051e04051c05070e0f0405060601020109 72
    0x6144550404803410301c61410600b589501e82d038504a000003181c0040c5c1e800d0080c0000c01a00b801c20191a0b805407445403500c043d140380880755400b588078000d014050005002001c41d0900a41205840d80080410609611021030b904410398410802000502c40d00c141c0711008010756222803132a00c0552140c0c0034194581c00d100824050390075107032034281c000386158000107804c105c100c1c06640d5540709a070782d1000e07003052200d5034050f203030b840c02c44c84501110f00300c07010074598000080b1285102c09850b072042650460504501c2044510021601c45006a006000700310840005098040c410a000c01440d02c2d4440003e580709400c48121001da4010401071040d0001c09440315156000d10941914109156003d100302d038000380d00880204a0100c1d00da8406120083c069804140c036512035802c2524200014491070b02c0041360044961100d0014010300c80c050281d03001802c214042c14040f0304003410340b003050301c03000c8a09170b6181c050385022808647c410700074100000c0d00003151380c1e10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 521871339 1250 521870089 521870147
    0x9121309090503040302100906090602030a091e0e0109091a011d0916090209280504020c0f0703110109091407050a05120103060b011409130b062106010906 68
    0x61401c1d02040c1c4180c4400d210000050f41c034800d83c2d59075080143c1e24807501ca498908042c210300f0564020130150742090001c020b003681e2003100c0350b00b2030341c4e2540d99036801280d0880040b000d0906030004191001484008200280030390012121240705a00400f1a500140c0c0f055003030820a018944014485d00fa20200f022246405607405c0103020054a03175204c40d6045000980c04c45611189007241c0208800340c0918046100755180340440344da408441000303003180da204500134040d5074440d550115139074540e1001045101b08001015048400c650785078281550800d8140034402c0c006242800040340c5d0b6100c1e40104c072070392806000c43c42d10716240d0203415907041c0c11202c180400c020341403006113110b00035008180e00031400f9172800076140340c0c0680010001c1c0701403030008070554010403010800d0b403207000d041010048948000119440c041c00000d6540c031610000182c808401010304d400c241c020b2902ca80189c10907241e40340c0701541c541c0151074074240b103000c104081e00c0d500e003070003070b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 521872589 1250 521871339 521871341
    0x62403070f170c0f1908041a1512010905030d06050f1e040b1f230c0601090e010603020904080301051e0603072d05040e10050d170f1209121309 63
    0x70b64009004813403070500310038205c040520301400a165000404440c01c4c8814010380c407016103084241c20341c003003041d40b80201540c0b02c00e04902000300d018040d402d143c0000440203501038032110fa407210541e0794906440403018041c3c845801258803540103072950032424601060a069100340000300a40b0000b1800200070091090711641c03900000d8030070840a800394940505464140d0b42e40740c0c5000e00865091307001d404010b8100500021604202d5141c005070001001811100100c1d00892440d02d012400b60141426a000940240051082c0001c111811020318183c64003a903060401c0c002409400c6500514031500340d400540c1000403c0b2071078401e0004903047d404034011382c80202480000045d0702d415421040002520204080c4080f4004c00d81113600010b00340440c50f00f1600b0140020522450410b009003000460081d115000e4010420307a0403000d807055950b0b48444a8884c86244000c0849821600d4010162145e5a001946099034000c610308041040e00380d090100b941c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 521873839 1250 521872589 521872597
    0xe0a02010c030503130f060504211d040603050102030c04060e0109050a0e0a09020603012c0606040e0405010e0703030917060c0f0c0f010f0c0215040317062403070f170c 74
    0x201c1005c00140c4103074042503100c4507401003c0e03c00d0100142501e094148007050116440e9101d42c102920f01c22001c07415401400d1300010b241c1003c00d0f00c0701043c0d02d8001402440c140e0b1008102e540003100f041081d40b05038001c6c2c022100a915204076111200004490b00e20f00d40c007074640e208810300400d100417003507407016035032202440c1d40009034401c0755000a80f6540090340200c001c4d40c042c03121080310005050341510b00ba0000c105003906030806400259290049008400d068080d200000c2e05005d425005154100260416134040607140d0400411104150190505c0c1080c00003091089210008a4502c504003440d5031700d00740b4940400c2080545d01c10001a00c59105203201c0460b80c960a121300c0708078100c060350014080d14940d5020307040527420384140d88400244410440429000b081140981403101c03007220269584800151520144078805100203480c1b203400d501c3e40070f94000540c01401c003a00c880d07201c01c100c0c2c0400c40b0403a080c0c4a980e00211030400106488840c084050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 521875089 1250 521873839 521873851
    0xf13020301140f100b07020306070305061f0504050108090f0c060d020c070b03010807051c080306040908030403020706320c120d060603050c0c030a0810050d050c040e0a02010c030503 80
    0x4901840740700d00a2407044800d4401c1d065881180052054041e400401c1070005d0000340e400e02d0034440d0540000381c03180030061011040c036840c0d600003089682e800003103400d03480d0b20585882c824071880c88010f00310f412501175075020480e13600205c1c9422200244201c0c234036241c0300007001d400c0c040344244241604102101014140c003449442c04408080c003a01d40545400e41d2022744035850090301c240341503819440607000c8d14a41c00048100340103e40c420300c140703800c1648540d691320342001042c020109080050030307119000c82404101035000c128901101c24940d16003001864015600324148420f03084000c80d00028000902c3d42c2d8006000340054035404070a4504c028101112000142e029a1203400c60b1507a441007030101c0d80c0c242c85207e400106040300c190509803982d02c010798038881d00c0b401c4402e0200d0000010388601c200d1413058050940035010603c3c0d02c0c0203103481c5983d40d03080300c509441181004030301d0011440006a8400780c80d0142e40c4d50301700851a4038203032003540c406085 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 521876339 1250 521875089 521875091
    0x51810050408030c0a2a090e0a020d08190e01121e050103050d090b1204140109021c030e06090625060c0504060e012f011805150f0f13020301 62
    0x4000750888090010340030528121001e0501c0b813415140041c0f00c401c4040b43d07640310350451b500306054441007000c1403007562540c0b5000142c045039000b02c1464440113840c0294007080b11107140040010b80340291800005644260f0030034100d5281c180d4126199071031b1240007505500141400014941111240034007510400300002c4d04c03420702800fa25000d130000d035a070392302c07034000c0107500ca511005820007400c4000c0b41600f000132004c501043c0581c081c0001d000800310307681c402118203003075002220300c41d4020000c42840c0608485001c1c8620500e4041e0045424910a0300c10ba081c150111200c050008020624086941003038a03d512100301480e00d40200215000000884611421040000540790380e500c40c0c2c81c020000f461403000203081030402000c414109518004044401c05a00e0380300f8241d40780020519031a4010601800c4e800800001d4a60413410311401040e5807803034201e210300c40c10300c80d6500d81c402c00c00c0c1e1200f505daa00c80016064001110341d206140c0742d04c411480200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 521877589 1250 521876339 521876347
    0x40803131506151202090303030a0f0f1a0a0501090b0a0513030c271b120f110c07061b260307030b0306011205030715090209010603021905181005 64
    0x190038421a40680c00a00c040348000c0360705503e0390313081400354403000e02c2d4042c190b00d0000f0541c0866128003000d001d44030b1440d1554200b80e40d0500c0740c0c010105041c001c81041000d041b507071200140c1c40700c8c00103150740505280c0c1e80100303141d4032a040000588501540d06450321841140440380c80d4030400d02c100801404101c00320000300802c6903000101000d01185105a042000060104811110020303140d071506105200c9007070f415511500d24181410118100c0d005801030f84003030400001a0605646084885070280075050040d203c043d402d0310489a07030315198981540d840d03081003500e034140501c59540341c0c00100c0d41303070300d00c200308d02991708100d031800b0b640401e20032a4009564013004217840b84072140241c2820020540142061011403c2c001c00e2621a10b80704e01c60801d0241500742c0181c0040207040898001002059018040303483e5507a4034007004000b50005a000c0501c580d015490961180c45501030b0340d0b22840c441d0b81584511000301c2042201e88500c1041014004144 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 521878839 1250 521877589 521877623
    0x40f0c030c080a061524050c10060f0806070c120e040f1415010c0803090c030304170c01090312030b2b05070504060303050a050f0d0204030f02010e030604080313 71
    0xc045001030211400610711400180b6019040d0365900d048111983c2c00c5060401900d415124201b00c0d0288030100b80100c04442c070f0f02100c46200322982c108a910403d000ca00c1d81c4640d40c0e00c610b04a986018020280c1501d503641c03280ca54205031200c800242d03c1c60032a40100340d010001100d010650300b01101c01022002c0400c050b41d05015110510944e200c4020583c5410041310a82c42100a00700d0181281c0203000600f002c031580c00064109040440099942c000800c17500800e800c004046030303250342e903406121010102c01002c9480c14020600b40f0f01030755010720681130030b5030307444030303550025501810741200201070540a0a6028850107000907907203a0003440d0280000d07070088c500710b056010341811442c190075980118011403810b0020000710f40d005e02503803d1344003945412955048100300c1d42860b40181201714918a100050000070880700d1a01442e24920030f0320b60342914190102050307151081100d014101290400c001102c096500380c2d138108291044100c01007880401e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 521880089 1250 521878839 521878853
    0x81608010f06050922021005070501050f0c25081207090602031903091a1006020d08040206030f07121a01030f0b0312090a17240103050a1502040b0a0806011407020306040f0c03 77
    0xa07587d01ca0214200056070000e01100b0f0280641c81010203880f080c09041180041c10980708201e820701c00312a0040016100c40c1c0303404801301302c0d070707070801d00d45a103075a41d0411010346800150746090101c0d0802d080015400e0011042d00c0400a141d20480500b030b0303a10000350003a02c101082112030700003800000328142080d11070b00d40900910020880d996052002c040d28105e0b0300805c050a0007940300070040166035142c201e0f0b40c4080c807015803040790745031890159132800707509500c012024184030822000340380b18084003c8c0094241e800780500c10030a0017540884007800240c40e050f810480700d07211b420200000a0000c0c80014022400142c2d03a9000d400d405a201c000d440660b80010710390160042b219030b5400186101903504503c45d5155555a40d96881d00240082c085181e8800c001500c07141c1e40d0645004002e5800d10955944189030700800380d900480c1c13000d010074018040c0c160344501c0001591100c55001c2e0081c641d580b100e48926014075030240d4220f54811800c0c038080000303091 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 521881339 1250 521880089 521880109
    0x30f220812030103060f020906220603060f03140a0f12021e0d0e280e07030e030a030b030111030703092a050904050a06020408060a05130c0b0c0106081608010f0605092202 75
    0xe00c0c001c4551041c11038540720a100c040e036010000701800e26200b0311a80840013b00301c1142d5001030b5000d00c40420180c480c0c1003a82500c000340241145041c0d12042c00604100041444100d0b405d0b56200c070603035528000c0e284450300b44c14005512505400c031001d4041c8000c824032010040010f04003076510054040a000f0003242a08501515681008808442d0900f00d130041e0b0241802d016030280e110400d5521301590141c0410962500d220600f140c4080d40314106000640b80c2003a034a1038034940203030240110714011250140c03080d00c280d00b130a8686508041c907003010028550041d1505003003100440000d031080e1500d00400300a00001807840c4002d02c000c0c44e401010740403910344003100e9002c03500700505c0b020b202c40482f1202400105000c40710406e84004c0c2d002603485848601000340140f0700c03500701d0070342ca01c01e010a4800e4a00c440100c1e0003150f251307000a21a1121400b05030303068402ea03100300c64000c40850b010841122070504d100301400200307104404c000086800050704009 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 521882589 1250 521881339 521881357
    0x3030507110111031911010902180c070204050406020909090d02100b01020f1c020609010207050c04110d0c051e13120201020f0706030504020f0907090302060c030f220812030103060f020906 83
    0x159246042d405d650441050007981c511100200b08800d00c0c0c7d0040380d0304042107050424400e464500280c1c1c61030124041c8e40b41140c000d0401c03c020300d030529040c0002d5011440701486410504001100c0c4103000a035113143d80201e90140032401019982e00005d0401d8140c854154000c180e90410712060800c40b1030a59440030200840003840c4030360107070800078080c011002c00e074010000c2801044d000144d4150703100c03007990005152904003045c07a040f4000c00001c13242c45070806075618182e5034041c0241000800860468094130091120b00c8024820000300e22007140c046a01040002c0310b030903002d40f640d80180182c40403c4800b0320700740c0c1071070712a41103580030a9440c4184820b40c01c20341c21848600c0c43c2560455043d0401d94000703000d1159030300c0000e00c228400218a8000780091090b12548144600256203980600041000f4010b8244118000c80440d00d0001184da0001030408510450070020518503402e5843e048003070000f4040d5204038640821140701c85403a2a802090b0441d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 521883839 1250 521882589 521882617
    0x1201050411041d06040b060d05011d070501030216060534120504080d0c02010f0c02061801060510080a09020d260415110c0303040605030a0b0a0303050711011103 71
    0x10004204401ca442c40900104054a00c1d400e8802e080c00021343e10780c21a03000002014265a007500141c054a007440d03004060394208003400710034130704106064817100046010b4642842d02c941c0110224060035038503000d000020011074001c140194001c030742000d0b25403003130a001c4060380f880c090458258040e03904a145d011000400c460341c06075000c072090703404003010b110134241504d400140c0d0059081c0540d1955440890035075480c001d43c4a002c0455015405019281402c0d0f40603450b48000c40d00202e412400700c07600c2420328018403c034000e80718028180f000e40243c0241c200c85103e0700031721906004c1e17550713001140541d0701c50030100515885248429080d141b03008850102e600c240c41044041c41040c842800002d03001084019450b07860f1506a8038020f011a0703592418909507a425094040010085540f80d44640114400c2c107a8080c01d000141c2e10800340140c9000a11020340021020b018450000c4c0900b2050704101c44145030400c41c00c504061800e0855001814040300300c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 521885089 1250 521883839 521883863
    0x8040512040f0f091505041503020307140f1503070c0c030b0a050610020622050a120905030d020c0a09020903010e010c020f0f07051c1b0807300206030612010504 71
    0x1c80391101c0c40406040580000d00417140038040300341610703a40303004040c4516100c0a0403520710003c1d4681c00021030300101240c00f0560b40e0950686080688200e50380105d50951150585091403038540d07031010066221a46103944a840840e40007407540d03021201c1078411078000010071640c014080c060221b800001905040080801c92a0b821850700300042d074008504004501c10b0801c1713042488044443c0c082081020b5141060424940720380041001094140288540e68040701c0c0006840e815400ca13000c2030851041a03a44080044015034048400f52044c454213806401402e41c0b48806400030030555818240142910144040503006a002450b240564403042020000a140d13086c081d1002504181c00b01e010451404500d0500000f1001d504040000c505194041c19504280c1c505032192515030003507d41003144a41c2c40501024804181c011001c1c0e101540490341019051001c0345099007441411b0308001d0100350301c00c0441d10200700380c41c0700b03006183c447c51044848181d1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 521886339 1250 521885089 521885099
    0xa02060109050a0b1305060f03100c020706170a0c03090506041515180b030c120a031218030e03120403210806030a030309060b060c1e030c07050108040512040f 70
    0xc64400810b155041d03424013035058140e480f0300b454600c48040d10740021449554000c041851125264280380c1c0600c640c1300489100b211540c0100d60115282c0d00740c91001d5980c90040b91a4000510030341d0407100104003240c50145180d1181c146030003242000b0881032000c1d2141410a103003100c00340c0702c2c003520014180c9580054468188007000104a61984a00f0450309495024078645400d0906030b0f204d04042c41d5035030800c1410050702c8020020303080c56120808c1d0070b840d0103040304100c0128031080c0700a41024424056484450084442280030301d046490441d04842144d035281c2c1c060003503841600003c501c510003040598081c071a91402024070040c603003c0044100c07034100c104001c00d002c0c0b01042d0760114040000c1501442d001c60740549a00f044070003000310b007082d44e92001c00010015550000424009407022064880740c400d0044000602d40724498003241c7c140c150000d40302400558000c00c042034200b8000c80480f00c54118004c03c0350703150342c07042d00403841e100100502041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 521887589 1250 521886339 521886341
    0x3090c18050604240e040602120403020706080a2702122d0607210605030d0c23060a1d030a0507020a0b07150f0f090c1409041203110403080a02060109 66
    0x30302c2212108a81c4940f00113090340350400180207081140204002040900040f41c050ba40200341400814640d82082d1902a50350b88252140d103000c41c3c003410014443c42d103e881000019281c0e9001198401303100c50303a41500c980d0f10641240d10068000a5500f0030104100181e1504c460f86070b55042081804a0303d580c0e00300ba008003207402d92010003004401580100c0600d03105201c006001560004200620041d26141c0c00c5a9058131411000680c2254011210f088980c01050207107030020003001c140c040140703050900d4410760311000101d0601403803a442806140340c60b021010002511800081c15580704c084400c0010f24049020070179031401c1003a0030001c00b0384c1d040180c41c3c407050f80e41e14045032002c140f04100300c0f903880049884800e05604480c0391040101c808020040c2d0900d0407042140c04d03801000d10243c158480000b06007800600d0f180141d13000031031200b00e143c1003d400c501a1504034480014240c051100100050091000d411103000c241c0240c0700c0d560411701c80c50 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 521888839 1250 521887589 521887601
    0x603060602151608060120010506040605060a1403061324060203130618120b04050d050901080c1e3c07060e031c0615180603090c18050604 61
    0x11034a86400e400340f042d49500340c1c2c003200509405060642007a6500710050f1001d00c0002090750140d40042030440500e001940300f1481006c04540c1003240a0302c510a000f00d0b4010220401c0c0030030050303d04010503411801c00b455001c0c9000f01030f2a0010841201d000c00c0d104003c100d4034482150842c1030758141070817a601c0c2c2c09804284000d50502078001c20312210601c00303200c1c00b414080c1e1110046880b5039440f69490261085205428241e403040c0341502c400c48080791700340c41d140500030340c00700c846201b50112480c2d0344d0140c0d5614096242e403071035180590301040cad003180c2d4115402c00030249000124042c200803101e020341800301728805541c200c1e0f9071881d540030022a090343c0800011114070702041d41c554580184000496000490f5000e16600c2981d0b038a2900318200701c408911400c05030442e030141d54814580b0503803403075003a9054600a03241c1e82c04128120b070009050103050f100760301501c003c90040d0b01d1881c0260303880900d42105100d125800c0085030b03d80c420000399003401d015034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 521890089 1250 521888839 521888863
    0x1303150f140c07081908040302010b040219030509030c120a0806010903020603040803090f060a0b0a05041401030f08093a020307170c060f0702011812060c020f070603060602 76
    0x207200d003a404003449180c2100051081c8582c00d8007080a07014031100c14151003800c0003e990010f11050b281102814404084070101c0043d07003000425402814140250b80044548003e1842e40008103901500500001400040c0f00d01c010321400c542d1300130800c00c6441406000000c5030b500d0010306001410070078018040303414090500c8080005844034811030780d0080c0c001c0ca0268594031017000090800001d04510b000c24451107052100040503a804100e004404441c404003a83e80c410500c81075030316803c42c104d440c1e128140108080303081d2807440d245240c070845820b4602a908000a14031140c042d048020401640711400c001c00c0081c1306c0c4040b5024007c1c000c84011080d50300207030781c492481c054181d08841d00468040c07012010400982058002005507845900a11801445030406c40080e40052824041120b102051034541070a0382c80003800042da4544584070440600b030058100801c5105000091990240a004c401c0207000c0b15030b0040344161034000000e1410700000c81d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 521891339 1250 521890089 521890091
    0x120f152c0c0703020102090d0506191401090903110322141018030c090212060d031b2a03200a151e05040501080c0903030307030b061303150f 62
    0x461080580c820520540c080346100c500e90b0341d0070311480c00300c1c0a8010b03800099006880e00c541c0100700007000c59014130a80d21001c004c0781c602851480c1c2d400740c50030f040544ac2d04142c030358018030094400d50030004682e402420315200d0485400c240034a1503100f00e0b080d0702e4503540c00c4c940101c0a4030000f4400c0007041c0b42000c4140a185400c0000d0071600c0345000f0b00305000c09800050ba08080074000c4800441d000f2154070301d00e90703035028520040c3d07200e040c200503020603480005c1d2103450541016840650160b90300002c5000542c803104010f4000b00090303e42d03462200c00c1070b241c8114656012110030300c02900450302482e616040b0400744c402e50710894100030803d450070940d262904150115034038000041500c129901c0142c8401c03928090403c0b80c5207414040015154110b00140100d840a071380384403503542d0344c02e803814140c066a00195455041040410036991082e04140300c0d45100a040514002c6858034501c8900601e500032a01c410000a8804080307403c0c2c0300303c1081000b4994 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 521892589 1250 521891339 521891399
    0x1802180714120a1b0f18050301020a050c16030317090102160609030e09130b0a0207140604120503040b01062118050c06040b12040f02131b03150501120f15 68
    0x10068031703a29200300000104a41144524601c06206001c40c0081102a00840d5500780c2c1110040c050b6000320103410147c800c2c442001040d8a4158600003200d8240d5941451a80028420481d080c030140c0240030310364003884403040700d4130f0003842d000c3d1040c4a0030001540f55410300d0044d103540ea080880c60300c070303d00c41c6042249100030642e10001382a40300807040820b5807000c000c04024018044c02504004071480d1961684100040c481d014a000d80c12070100e401c208241101c55200490703005110f81a1040100291030107040c407655180300c169100092018082031100484d80351502c0440000d03142c104d07010600005114004150030300380c40f660314203802c0000038081c510a044600050001210011381403064032448000116401810b52201107003070f40b83c0802401d40003004891503030380300d0f003a000300300d0280c0303e40c012690061801d2a96140f03018010b42d030801d03092004041d51521484481e21140040c8184000c0d9100c406001c42081d0800f040c91445c580e00100131610031443c1d034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 521893839 1250 521892589 521892641
    0x70216050609010c03021002030103061d010b010509121f1b050301030f170d051f1d0601080c090603010815090313030f06060b030711011802180714120a 67
    0x250031982c0d044800c0c00d021052607a5031400b2031620038000c0a100ca41c5201000210400c03034640c001d0841030040c02030011540704159001c608031381440503c076001c58400c001409683c1000c01039420039110080a035501c900c444a6254802d203d50721442c10042c1d543c0045c0007009444140c0b14101c0313940d07840c1050941d07056544200b410964040064844500e004a120003411103008903013541032400401d100c1810700e0504075251078080e24104103265103e8801150500c1c3ca00035022011804007203207a1252a00c07001580c0615000d441401200c5d41084002003e0321114011030017800000d00030070f5200030f2800901002800a0b040601d2038000700300690003891880d0342d14050300e400c1485e21105056501c3c00790001c3c103459000741441030020041100181c0c00014074000810300f03100920401000d1075068001e4542000003c2d031088981c0c031f02e40341164065000302e50280e09800c200d9205200c43d0190000c2d60030005d44162801880020031014100c1c40c00303170b20138085104540350240d001c45 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 521895089 1250 521893839 521893849
    0x70b07121802060d11070303060e0a050403120b0a08030f03040c0515040b1836091b121903020d020a0305120604090c080c0f100822120807021605 64
    0x10a4040c0c0f02c1c0f00d012503d01140111607100d9544070103084c009554843c01460702502a0846101d0300d046400c02c02d001032106c03011402042d22036a450b640d03440c6411f2420900000074406000e40320b80186503818017217850030f001c10042c0050040003030240c0e180d2605252070003d064481d0041c1e4040e40f1303070660180050300824251410394904105c0c4c1602e0308041000b080e05170302c090800e035074040c09880f0304076100d001c1c40101201c4168100740001380c041e81101c06441c0300509441034a002d07407280d4040e0050800c984038100607584020001040081601ca1851910740c00e6800340c80c100b131b01810030404045d010000b0a0000c10140040c0400d0807030b544002d4194080e0748641d0071002d03802800606d159640f5801104820303032055a405001b5100e0310455039964091039401c0c003c600c4926003e40074a0f0074200084445459550001c0301d64800480829510034451160000707140e134109040014080003041c48064056640c1c0c0c580d5241c4280d000b880c00d001b18010840d100d045060501c6a6210 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 521896339 1250 521895089 521895131
    0x30e07080c0117070309020306010f060f0c05030a0f030b302a1f030c2304060e12010207080702010f0f020a0209100906080f0d0504060503060d08070602070b0712 71
    0x7843c20f05203543c1c0d652007416809080d106400950501a60002180b90801c0c01c0c0040280c1e2151707078a00381c400004034425112035444500c00752640c5d100f4440c22580c02c3c80348204681e039061602c0c01180c0480c113613001c20034042c1d0719088100340c20b450700d103c4a81785054103409a400b9840c0001401180d803902090203c0021601c024440d03a1250030a180054a40100041a501440501d017a010307e000300010000e0603a03500e54070008101210395810b200620083e400c00000d4900010702e0149007040076036a8030301c44a00c0c140c008036000702e0036022440c00c3c4040c06c180d50155400e2551140c080c8001841410100049020300150b40307016014a0341c005410703580540d050f24800070381d48544d00d4143c00310030380e81c1c00a540c0d141042000700e628800850700070180a170700000c6519080c0c448005840502650055000183c41440026101d14080d61000717116801003101528240d00c030b0322040d09a910009013626619a04070030700c848075502c102d0602c0481d0070600c0400c0007001c40c44d00a6417502c0c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 521897589 1250 521896339 521896367
    0x603021c17070819090501020615012a021201020d060b04030b0621030c070e010b03010b0a0e0609040f05100f1401050c07050405100306050f01060933030e07080c01 72
    0xc0040760b4102081084802c480c1980042d01c41c040e104201208010013080031070150b80c0c010302804000c5040683c518100700801901612511150060241042a442c405900d884812002c00040c00c000d03071144d000c00400314440d2070026035240f241c0203014040d03600d50f50007025445c0e410081040880d248154064002c2000c03258844030018101d031600741d0308050090010310303003c0022000c4500d1030001e040b1080302c140c1c0c502400e850b80d85240e1240d0700c0c007007481750800d1503000b08180c1c55418895080c06421450040445003000280000304080b501c40ca20368808032a962802e0000d503c880556040c004d00c100d80510001d182040000844800700040040c1400004500d01405610910042c0003810016200f0402c03803a03e4500081c03000c550b4841507800ca8900000300e0084007507820014166045521050026803408140000181c9403510407103c01c9070b00d0401c0c949200207200040804815a50086a4050442032250400a007a8081040c1d94007145e9002c2030b998200c40c04e018404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 521898839 1250 521897589 521897633
    0x50105070c020d0b0603070b180906040b0102370b0f0a0b0307140d1202030702100807080601050304061409100c0207030b060108090f190b0a14010b25060603021c 71
    0xd01d507400400e02d8840c03e500424081c8d10f0204226441c2c1d4500300c1003024483e021110070800340c603078005100449900911407801038015903c00034240d01e0300704803106554802004990404540440d080c8110034059080724030844000c1480705c4100081c0c17455030407510303002040251284d01030019540d59168801c13030b81e41110140f40d900056644017502010aa0400c2103207582c00c0e003400000351243e2020400b00d101c1c2207130703a60550955115048035031080885868000240e20b96000541d080e410003401265031130b8640c1d00d0000d407003121446490285000d2002464184190521401a42c28a200c2c2e4030865118010400202d00d035102010b8009400f800c0400e07154413000c581c107080042d21084454644038005406c00002008501e034009503010b1410b001017a199485c421040c0c6200800d01070005e41c2580040c408000b08070000c0c0840b801c0f030920078100e202403082404c1d0b0400c45400544020f036980104000354103102d0000c00c0010611113100b510004c095075903141507290403408003090 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 521900089 1250 521898839 521898841
    0x50309070e07051309050403081b090105160614180f03040e071106040f02010305130b042d08090406091e1806060b090f12120c0703020d030c050105070c020d0b 70
    0x914010f00440d0001140d10720780394501615002c5d98000381c10152800c44c00124900300040301c1e11800302c0860900c60408000500c0e00c0c013035500456a981154842d03001900c04510288002039a52141071400404400030007460318011055a5480e40e410941c46025044806000410103001c801c850a6542d181d1080d00785031104201102d09400614001050344110030038070045c040d40c0d03074a003814540300341ea040c030a66445002c0d45c0280480032b103008000c182c1c0368010500082e44145c08012400e00d41e00e284203650b0f50b40000340159800501d003944c04990021302c0000a0a0074001c090260031082d00a1096402421085501c01035020101f14419582c140d440c8144003020401100c0790b4000d2824802c1c03035101c4d944846668800d400b0700384941000381c80708445050007030321559080b80301c90180100d04003246020310680d1020042c031039a40582d80d40400140d0b160134243d420b05002c1d03518008004c005107009421203402409180034401e41c0400a40165212030000305981e600c06024070702 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 521901339 1250 521900089 521900101
    0x1536012003091c0210021e030f04091a091317030906070f020f01020301091b02010c020c0103090203010f0c051c090519030509090a20090607020609030a08130302090601050309070e 79
    0x100301040c5402175000e030160312445051640001c82c181d0382082d521100c80454403c4000f00d07901c1c440c250701411003800034001044040aa98071124141005c0803901015168031000200f65070821201d00382c1548000b00c1c8641403000340e207034a000c8864082145880c40c10150406030380c1d1980101810200148040034141c024824080c98480000e070100954482d61500c4030300c8090b1103030103180000701c104007030184c410b01c2c81402a182c01100a4001c0c01500d41c01c2001103010382070a0000b643c0641d01c42100255022040c0b10700c01c801031840e0355598030303110700c000c40700750488441221200460825940c2408584081080300c1d9000849001c0703028110302e89004c1d1f40d54014081d806034007207090030402c206110782e9040032003008110985c402861400b5900050180244803071a50040d1b020300100f00141890001010200300c02001c88103800f04541c1c1d0380701c86030700c07004003441c90b02c4003d08104118100307181e107140c10075001d0030070314114a4002022030744d6080500c2004004441c1101140e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 521902589 1250 521901339 521901379
    0x40b04111804060624090b13031a040b090a030806090a06170a02030f0d051e07050a0809030d050f09090709081204081b153601200309 59
    0x80c01c0035200620001450141002030051891348501c40301c000600c20400b10038503500103030b064808207544400081c0c0f800c0c10407808141c1c10071002c5000003503904a000c0007088000c0a00039002c94105441081d0346010b207402d401d00c2a000d020013003c0d83c003032509d40002039040342c3c1d450350204082c2e640483d1a41c401074400080c00060f80110382048601d002404e01d41e002141984e03086000341d00311591110f20310004c66882a56584000015805101c170b0102c4600041d09007000307010780d8420340d08020352a140e00d8205100610304071514100002c5001b41c43c241031040c80b0408449060090400e03010210b900349511484503010b100d1144680000c82850141c45030340c01a14108007124840000c061202400d68041e00608a04d8840c004070390f030480501e8490194a100003801c00c0340704080f40e0103400d426800c103844684514400200f510014503003075441e0000b510304804001c0d002ca40700000504821035074403e40c82258021130b600e80c3d0a0000008459588900341c5001c0e4111010340e040030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 521903839 1250 521902589 521902609
    0xc070f2108071a0103081e03100608092407020c06090609010e030109051f06120201020703120225050103050708060a14030a08070b0417030f010b0c1c080703060e040b0411 75
    0x501480100c0f002009100d114070281043d40405a0540c3c541880300c01404042e00040f100c0e410030007003248090003198032400d01c854120341524202d84442c0140298501c0401100ba004051020703c00e0410101c183d0400000400400c145d9405190800090100e10030340300310780629041c0701d43c111100c40a41c0302588044826500001500c905000d2000c10710f5160400d0b01081058500b08000825803140d0b06030b140c208264140c00a0803c5441c40c0e40b03000e44004902002c07015801085420042c00d140d10440c280c100c4a10f500369042e040c00c240014040f68006041d10b02045800e508009a81c0c403100006c105903100d019829146001c840d00003803600c143c0d03880040002002245400400c220310b05090b02542c40b5020404e030032104051209128001107407281c4100c03101d400100320440540e00100311007240311040c0c40290008181541400c410304220100098400c0c00300301219516108540142140c0d00344407910f404c0a490380020180050b00207416081601c0103880c0c41c2d43ca40c5400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 521905089 1250 521903839 521903873
    0x9010f021903260618060a330305072102040306060314010c0203070b04031d030604050604060f0603050309040b040b0a0f091109030a03030b030f030c070f210807 71
    0x5400d81c06500e401001e5400f29290740030340c0103495550010300d07641c050b0114400c2d14040c10004994903001c650300d408040142040343c00078000f02c3d021400090b869110b08003c4000510a440300d00405501461110402e4001f401c05140605000215600c00c1e4481b0307a90f4a0045100407154154142000030b11603980000d12142c6000c60010420208951036042da0103d0002000200341c8204d0998891048441c010122001e41c00080e0000e4020a0403036202000000b92300f0000c050b2102091602d5015107080d2041c0c0e200c1804c101c200849401440c2003000e000b041803207218515691a03a4131301442413021711403500c03010984025219944100702880005042200c101e55410840318141d00b40d01640780d5950510200c011340c1d0b0601c01c00c4960300a0050010954031070305413412001080e0808030182d050180b01d0201c60a007104201801002c0140c002a00000e49404664070036009658008990503a07000032010951411020440c1c3c1203800407481d80d60f0300028540300d41c01d00c10740542 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 521906339 1250 521905089 521905123
    0x4170a030b03010c02030307140f04050904050f0606040b03030a1d04060314010c14070206090d05061609080706140d0b040204140325050f1c050d0801060c050309010f02 74
    0x48522036260304140c1e50385000b0b60080050000011040341c0360300c421614580441d41d400301c00424568000c0081010f00d03143e0300020700341a00c86001410300701040c0c2e0700b5034040e8420210001c5104081c4034ad642c1000c4203c5003000400c0308000402d41320300908800e2024018801e100c0069a8035801c118000c140c4000e00820109032a480c0844020200c1004100701d0761034820b031080f4581c011803042540700780403105282070010744e80c00c12038541c2c002080150000b410708052400501d00304a200d0003051110403c00c0c450044103401070280801c0c1d4002c0c4991341c00f4803400c000194000720f0652000040301c1c0d0541c0d581200750100c80160041c5410140c0040c800203002600c5e42400ea1010b50011049080c0c80f640c2131040e09290915980085101d100c601c007034400c000a141c100301e4948a07034405031000b2445800c0805400c1450600b01040e280758200312259480168840302850240180d4201108400c2440c2c40c3d0a55a00480c1d90240c140b2800141ea01c52160003041008894500000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 521907589 1250 521906339 521906347
    0x9020117090d0206010b040b16080d110918130605040c03080403030314070c050c0105030a090204050414012d05040201050d02031e180a0231050103020f09041a0417 72
    0x1c26a580c812a0b81c0c24400180a810008a18005140c045404403000c0070070b80b5041c903026085000c00c0080c004021120003004010803900098603028102c21100f100902ca074686522209200c201c49919030f44113203000a000030807801603540c55010840540229000445558614050901c007455401c05002e0350008a800401c15516411020612411040f4903185851340032007520707030f42621440101150010541101b80394805c002466000361503580100b139401d01500800d088074020340d03081ea0b0740c4440151900c05600240201d00a0034141ca1034040a654041070b40c07074800078500b419000e26038850002c141561311a00c01d4412069034580c04540d241001110144a100c00c5218240c900100000040b032000d003500c0b41041e40d0208902600c0c50195030350800a0f2440d499a00710110f500d08004100b40c2141c4d00007520340311182200c001038550560042050950505810710f100d0010001000005602c0200750342000303480401e694207944a520709404100074010026071409004030f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 521908839 1250 521907589 521907601
    0x1110f030f2d0601030c0801082a22140c1c0f0e1006060e010f12020f0a0f0201140402181306020309011409060106140a0306030b07030c1d0f0409020117 67
    0x120514010f80003620200858011924280c5c1c4800091041c04602e41040c1110b203094407200f8544441e0b41843c80306c40070030200d40c0000540203030680d00c00110708200601400b580501c10b11400e00500d40c058003c4c0c2c000d26000c031500c1b042d8070800c100045040c6c0403201d401d000c400b00c1d4210b0100d4055844050000c884801c03031047e41c80307903043d2030341c00d2071400e0000015800740141004201340c0300603074445c2d40c00401c03400142d480554840100d902c56500300b02005c0d80d018144003400b13000c2c01d41c0d41c0d10b0803041d0b0101c1000f42541e81000a10007100c0205040c080141d80301c56002c041603450301104c184649e607415144003000080c44c030142c041c0f4000010050705135019817100d1b642c010000a13001c81760b2551515240d807943d00740a2500481e454501c9510f143c01e418000e4409400350386004594a61603640703040c4040e9050f12040301107900d030712106803042c2d0001c0341040701c1c0d5800c465040c40841008000760703418880c5c0c0344050090341e41e480c410041d6486942a0340761a0f1003004e425016003404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 521910089 1250 521908839 521908921
    0x9020a030803190615111f0504030921020f01020309090a0219080f010e0c0409060b1810090312030e030f0702010e03060403020d12140702070801110f030f 68
    0x48a400c1c449200e80040348803800b20500c182000d13181d000300700040c22410080140c40c09035181206006c140f2071740e0340407040141003081c02031011501d0340c0c0200b01c2d0705084c54003401c0c4041c10380000d0a1540f810451881ba4107028102c5030002d90115081750207051644d0050b4298882c08009540103040b0314100304040d02e4540007800300e45518100b0920000004ca8111984001500c40071403151030300c80104000f2490105041d080303c6601110b5142a686181031400c9945581c408100181d0101c1d856000101080703031000d145030700740c0303842c0501e140c1000300810150507404010060a401c04048032014440d0380310440f640d1001044030707601c0402c105411100c2d00f000350b049002418683c01c0c80103908021441c41d000d035038550001c05081100c3c86003a40e08555003009241c1d0555180c5005210b42103002c0c820740a180070350080c2c05043c0c2051480f0b0b007511181131140c0090641003002c0c0900c003840d882100c0d4000d180d100b03030520507181e01d50442202c207641e5210b1050003602032100c10202440c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 521911339 1250 521910089 521910091
    0x3090607060f2904020a120e0c0d060c020607091512020c0102041409010f0f0308030c070c03140f061501030b12011104090522020d030306090c020a0c08030306030c0d0609020a030803 80
    0x4010103c06503460b0304000503403180321110000290344001c890511021a0008035400d088030302600c072028500b0380800c0b40300b4901c85e000c1d5000358850042c1c00a49805020841d0050641d00d0280c5039581403088400700c00901d5480c50b41004020006604400d4540e03058a85810f20b0300004d5507181d1703440c492035008403d07070b05982c1d10400d4603400001d01810048128402c6945000e0210a19442c6895104054100601030b8010f42c5c0b0402c68580008c0c1340b44190340c041c41c1700d08071103c50524040341c1300f49801d11221744481e8540c841e03018844122114011003400940928020500804c81d4010820f100b030300d07411030300080d801d00389100c070703940b0140000d001525403040c4204402d0742ea98458400e0701e402135403440304c244e000704c1150001d0f0030081984144079019040101c1d0060392034030648110350b2203104a1006802c0310035080100040320324000c009141d140300075030031b505041000913200c1c004034104c140b103240c0460140003000100c3d00003181c0160000d000303021803592030401c1c03010380c0d00c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 521912589 1250 521911339 521911391
    0x108150109031b03060615020712080403240c03050c1b0a020d3c0b060f0a0806090d080f0105091803181011060a05060d060f0b190803090607060f 64
    0x6c2030690115440d1000801c0300d04451302c7e40c0c0100740081c035000091000780300c920fa081c1c1b01c0341d100308404400b14010500c01066101c0c04d4004800144222410504072481c1c17506d420b04050410302808191f0303007808152070601144607841894107080b0140340e4500f020100b0020f400c440708410013400d116002003090540c0300082074041d000e0303040c1945018100b5400104030342d208cc8103d800c1c1c020910b0007005545c00341c40a00124a00b81d1071030001039201c060780d400244d140d40110b0030801d040005101c000480281820000d10508100c1e1446d42042e03014010f6074041c074181e00000c1c09000b003d144030160342c8031100c2625034a0041540c01803040342501081070043d802103d080d404036226045080359441054060000b50710385580c03140c007400c1c014182990001e402c030055004103001c0d00c00c5240076910854001401c001c0c00c4103101415010120000c180001c0078000c110031003012003111b1348000b00301c03003003a5101e4081ca0580002c20b405002d0034002841e1282002c1c220b8032220081c4600340c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 521913839 1250 521912589 521912591
    0xf0a0f0215031009181b03030207090204050a0b031b161101080f0601032f0d05060405042a0e04050a0203060a0605030a0227070c0b0a06050108150109031b0306 70
    0x10700c00c0c0000384181e11080d103200007800605102048071084071341c8944241e402807000b00c200c0100d0740c0c49a03004079061000b803104484402004008051b010010400201403e510640c2070615101c000b503025030041c400ca484641c8008002110100d100008404803002c64a00760703107604d0f001c0a003158040e910b41c01103d401c12220b0898144e907005408c824032607240c0950a40ca00d0b80c5460044010742051910b41c42e1a03000d24082400c80e4480d012040c00a6010580054850070709005290550324094840c5010300d01d400e05120206010382c00601c4241e10768082c5080b1204416601241c850b140e03031000703010340004400d00003000000300e28610403c1c0218121101619071820b0002110380c1c2d4441c441e41035008034070b01001410050110301d80000013480302000b82c0b000d00880303d00f00a00700c650200050500c509102004116050180c101c1144403040101504020018000200c05094a01016141004c0c2c1c681d580c481c40010300071715030020b10207506d061482c2d602200c5040c20b000440b91a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 521915089 1250 521913839 521913859
    0xc140a060207210206150111100c050a0305010b0901080f07050702040c030911090f131b06020d090801051306051f0311040e0c060406030e030408160f0501030b0a15020f0a0f02 77
    0x82c620000341d150144158007000f0000420240c015580b04000c0741c0c060005004070549c2078400c56035807081c1c801052160304c4441d41c0303076074200c4020101c40b4140c011a00b518814443c10340540d900501d010b601070700c10418032805032600303003043c0c4e9903000304207000354030900f0003039404103880d4150080c04019101c0d00c1e46100507041182001110241164100030543c4203000007039100b0f1a0050044c01140504850ba072400050711041d80c00b103066810010159100300800055140d120700400000c050100c001c008038140051803940807048580082c0026488101007081c00215154a182d514605202100c2c0d0554901d045180c1c10121100a4803071403400c1c2c008202c0140c04500c6004094000b000d403803a03d41020400c1d0010004980e103070b40188010721006c1f0341d540702003040400b20b0344444c10501c0301a01c1c0c02c001c13800c00c0d035031a040b80381014103060349616940c0b28100b174407056502406a000c00f04105003001c174a00407114458940c1482160840002d1240c000c0400a0f000c3c001d43e50001c2e2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 521916339 1250 521915089 521915153
    0x302090a12020d021003090203161409011a0d0e0303040b1815010e070e18040204201c1b0909060b040614130f08060a06060905010c140a060207 63
    0x804600c010019412080400e8240014030b040030117910003982d00e05000a00d100b01e6000b1910b0031106580405401444801c01c0c400d881e051000c0450305a0115240380456040102100c601018a0078400301ea64010480d6240c119094201d44003213104c0e0400c0b00e4583c546410880009074003030ba07142c09402144960300d140c088022881001c5500d020031600c840364038100703407090102001011a010040c180024442e01d40e81c642d240d4070b0a0303d1102e8910f1250030140108402c0340e2440307001d0701041c000d031b0b200f5400c15800300041e1540c4a82c0401410039035003180501d1406000601442007400641f18850140e07103070046944819241130507402c00c44103448602c030041a00c20b50062a0105141004401d0061080f00040c500f00d030340c10942801866842d2a030403058200340e0040c4034107400090800005104611622008002526050140910307085c0060040b81e41444003508414503001d191104600806c00c1400190748075004543e41c02a03030420400e094400302d40c801c0403100300105011 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 521917589 1250 521916339 521916359
    0x705090708070807142a0f07091103070815030a0803010602100b030304031a040f17071115091207170304031208010b030c1602040e061006050c0a0b070504090c0302090a 74
    0x3c002505180c8915010b4210509051003446d94440258031041d00c128001380d00040c8590700b910f0700d601006040b05420002070000b9a03414100f00079001a041c400c00650b02c8e8809409501712810907000b42600d421040441d0510505440150078008004000100b80b640000c040340b9588000310100410f031840d0003003549a224030720000d450351020051040540007400080b5810600c98800358038101d40540e288680c42884007224080100c001c02d010041c40f101202404001004032041080c001c100700000b1894082d0b0700030300c4e002d143c4944000c0c9001e0010400d4001510410414a0140007080300c020707526440307404101d5002c1c5580d00801c034024000e1326800d05035544418840d055641e51400c12249422500320720201000c01404500035880368032503003030800f00a0000d4074142c6400001320742c4815042d800003040043c100854490040301186100306a984400e04519648039100d04032020301458001e07000d024034100001c140c258243d070041500c3c8605841e030140c02c0e99550b034004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 521918839 1250 521917589 521917607
    0x533042303071b0e01050616060b0109091104090e03032512020d050a11090303090409030905130905070504230703151d0a05070f110705090708070807 66
    0x14824000310540080e0140c00900589040d51030504a908208442e00c801d600c82c010b1624410b82e036208104144400d28031840414050201070b80d03c2403408002c17022080a03103585010141c401903a03070030502c001e60b2190308210700800c0001001e0108034075095064103294854400d42c103040e442c142c155140b414000c0103492140c20301e8030402e5800d10300f010314501c2480d64030038460100f204c4601904013240e103a00c0a004241444d8000282514004400f0400c4600660760070424810610075107045580000884804110643c0e003c50020810300e0140e81d02d0405400c0203600043e1806149802c41c4d46500c03004101d0702074802c541d1000d54400901c42110100c0038980a011843c1c05100c0002510310f0300707180c04c20f8481c6000101081c00c2c000681108400303411801c81c0415071042c01ea441010804155000214944100500e0030321900261a010b00d007803c017414403a1800c400107021905020250080c50064201c0c3c10b1850a00e000500c2018119821130202c2c2d0000040340000d44507043c07034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 521920089 1250 521918839 521918843
    0x10509060d050a170d0c0c0c051905010e04090f151a010906111c020705010815060306090901091a040203150402010207090b06090a0b0a02240a05070309053304 70
    0x3030006072529031203014400a800040240138082044904c108405522580011240699442d0b218188524000c074019045900052280804585910000030740c08140302c100c840900300505031100850102d00a0081030401400ca1040c400102040c050864400041a1071180e070800100d108010b102004001c910096800244209070600681d40284412182c04000d802211140d0030080365110141c8450301d01c00d070050700304480c10007030fa5801442c4550480d61806c80d090121402030007180241c08010080c40c807a40044c00801c1c0e030818294492982d0720b0700080580814100310020071008130044c3c504034040c2c40b42d1413030784020741994024a40902d6050340908103461030508000050031324a40c2c0150300c000708024072211a90341c08204002000c52013a41c40d1510440c08000c0d04007402110070030741000c8440d00c606609082a110b80d5400386424100007030a480d1400110700400b81000f00404920a00c03490703002c00101d10a00544144001c031400d40e40080302c40b110b030005070050b580 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 521921339 1250 521920089 521920093
    0xd15170604020d021903110a08030f092404060503040b0c03040f0b07030e1906050907121b050d05210705030304020f01110a0602041e060f120609060806010509060d05 73
    0x2041c01032400402e03005099000422200c28035180322203030708145690707502c116203a882a1000390f00e28140f00c0304805c02000b540010394100120b50002c2c129611500340258400e86a51410064082002c104101c074401c041e02050b840301d446010141160344140c0c0c0a0300c0380c3c04a940000c0c48004000c003200c1c821544070f0b0b141c24001442c0e80e41d40120210181c0064240344d03c6010418441c5000c00c008200e00000c410400c3c005c503200d0a05008450003d40710000340d4000840074805060089000c02000780d020640c102c0040400b200140500300d0303a0000c40d80070100f0079000d0188003000035500c0f82c110502d44014000d8581a0b2200d0302c501c940680180141c2042c00080d0140c0b910361102700744c123001030421106000c40c000581703051030380720101114001d50200d010712502c841107502040c90b4150a11300c0d001b0606061029111001c0a40100e080060303155014210780481d0304804020281904140b181d00c0e211a02291641000d001e010700410003040012110700e410422220313080c4e08500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 521922589 1250 521921339 521921341
    0x204060e06030d030e03090312071a040206070b0a020f031e010e0601140c010603050f03030103030906020a0b0135030c0c09040816050f0703060c020d030608030d020c01110d151706 79
    0x110540280c0201914071700140000d2000c8001a1010f004881340c20803030f041020340d1040c00e843c0860080303d800003210a04c2e002c41e0200710040e00e481c0c0031544072507040000300200da660700320301c200070380b150601c5004003180c0401030000c030310041c01134030a8000b9081c8045100ba078030341641c0b0381484001c40741c841c000b0761984a200301440c805001401c40b4420b00002042154603612002c0c50300480f400c912880783d00c0040100141984088010090700720b91001d030000400e5900c0d03909140c0018040c080000489102c0c0d03006201601c1001540800280990100e152090503019141d402c00d1407031036440d0080d1199003000e440e05001144c4550b5000e01031508084414140108207c0b190200321030070f00c00c220303801842c2c0e64108904801580b0a80c0301007548114141c009080c5410188101e0906003050b4041c03002ca8008810303550760107101100140c8801180313000300d002d40100340072a0b070004400103107401182c0d101e400c070202c2550101c60300e11b100c90351413081403880c02a140100b10660400c0c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 521923839 1250 521922589 521922613
    0x31b050312030433200a180b0a120e0109050f010626070b0a020a06060b0304060b09040302060a0e07030c030b0703060f030c030b0612100f0b010c020312210109090204060e0603 77
    0xb900912918038120740c0c0c0170340c0340c501c0b800f00d41956205c29090701c04501000800c5490420441c40700c0c02420860440b2400d143c22540c020f002e091000c000e200c8600d8446400c0e60302c00e0025803221043ca0307040000c48017250100c2005500a0080e07000b18080f011282c14080304000b411101d1011120065004025462030100f440c025900720f00b4040c2d04501810ba059004101e4034000c2c40c2c040c00b4203410180c0e0301e081a00d80241146c0100c5890781c0544078100800001c20f070041000b40c0d0007400041e0100b034500b040d1040509002c81d0343c1004041344105000802480f003403200e101d11510b5607850401c4102e40303c004c94100703102c10f40300040c424009080e040c0009011802d1144d0801d2014084d00c1e11807400c03402c01400c0c41398600c0c0c01c01c0c0080c4c1e030310150030021110b800703403680d400401c1c28a414400541e4000c41e450b00303904071041d45c1a98000840d40b18240340c82d1030340144910000780c001815616580b07000080c0020480581c459410700c200496800f04044640d401841c0c018010300035000c290f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 521925089 1250 521923839 521923841
    0x106050105190207050904062315040e0309060a08100f080a060f02160317060108160503060d02030a0b0f06060a0e040e0c12070e1003080301031b050312030433 70
    0x1800100b811030280f5440000c00361100003109003d0351050302d01051031001144003c4102000c0710b980c0721011014400d0282103203e000449400b10020b03207010640711a00054a440c5109403807505030414000107011204d5680608000e020f41503041250300780699a03103003810f526180c4c1c0034420b403d411880068001450030342c080140400d41c254098241154903c04501c000100c00c81030700860407520406900340141b00d030080d8001000d00704652039080034011044000c00b0b4800390420b20a001010231050303981c40154040d116402002c4815100321803038001802441554407074180c009501c0072400c98548107080d14200766082e52011081c0c80800b041101616440b140b18006016503c6403155948a5034445c00101c01001c000741140fa142c0b025070317040c0450040c0161590701e640792080c00014021001c42c1c0c1103035017040300301c5040500170303050b2000c0359446d60190740d0510440041c400c0481300d14000e54400d902a68021040750212940207072407054005001d011035030b0502c1c49030802286 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 521926339 1250 521925089 521925127
    0x60c02030120160c030f0311150c04060507060902040e0a020a0b09100c0206120a0516020a110f01050d2c012c011d0102040302030c150901030b1302030a0b010906020106050105 77
    0xf51205078061340e81ca88500b148056149002e90000e03554480796041d141d0108062170f081603050207074104600e03261401c4200c070300840c0102e5041241c00540300c03091008c82e17004645900e8005000b003202c80c0f010804aa1f440017180000c0b8060990740c1c20008481c074000068070725030440540400c01000c502e4908581542240008982c000300030700000b1320f840e001080952180c0074180300001c080c10800e518203070465251003c1411940500f05020006007a180707800d00030361099400c0ca00110b582d0006039468025040d4070301c00c15107403600850114417440c1d000920446c028040700da60106540c90582681e80b20400c1441091101421042c0452928080481c800145000080c0851402055040c00b0403001404090760340128042c015468140710b00e81f80a034044030a449a40c2d1040410644c41c01142401814545c0e0b500d000c1e04541c49880301e0704104150410211f58a1801c00c15000080c0210102c0c640054000100410f40034014071906c1d040d01c1058613001e090180003c110a000b1403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 521927589 1250 521926339 521926343
    0x507080310030b0403020c0f0a031a090a170301051005070f020f150a03050108190506130201030b151804060b07061e09080a120c0e010e04060b04060c0203012016 71
    0x702030000080499100d18a0ba40200d00c2070780900100c4500600700032001040784101407160a007a5400c00000f450200301940c134451407003441c0b000341d840c83c24150500541038406055100c00b108070700355205020f80150f060318011251021110307041c06c0e0480340703402280360082032941c203549008007500d01a08003041e50740c402031039041545846010203400e6008031000c0340100c2d03200e41c014061108180001304610f8080b8903c0740c44400d540e140c081d0307a200d025040040c0c011070500b0100030342e403098126024401c0040c081041d0660703042c50b905070943c403510303c00c01c0c0030074100d05841003407a05010b160225015402c40c1420640c064441c07100030b101c0315504c0601108000490000c18400303000b0703610294007a010b41c9803603480031040a400e0340c1c810600c001c26949040f401c2c141c210703000050703441e98900070303e001200c6400c0c0c0c2001c540105000e40100c07128880c08540081c0f00355001e80c50300000e62007074009010780d00c0d40d0143c10302c0302102c00f5020219040b007408402c1700340300c80302c00d10580c3d00c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 521928839 1250 521927589 521927611
    0x307080f010f05060d0f0f02090103050a0b1804080919080d031119090503150103020907030605010c15241703120a020c120c030711031606030c140408010207030207080d05070803 78
    0x18a01000100d0f030851f4560b0a00d41d4011614944540c0c251054541c09445580140402813022000424035036031341c0b0442c448801103d01140a225005085d0340342158041c1000c950213029500b021003524a80c811505144546002d1440c100d1207070040c0821150861205401c0032a05440c0e041009002840e8004020003c000001c20740e40401903046814640c00892440c2d50440c0140062000b00a12030300c141420b080003004141d0303108052460842c1c1104080c2818040a102007001d09280027810301c4101e180c003242c02005031821402001c03180340c11400000001054030311904ca000702d0318208030240819001440110440e00104658440d4005640a0304110010f600340c43c0c004c2c10803c107040d0320100b808030402590124030000050100d00502c030390007461400c03142c4184540203410401da20340d0030a01115004410b4090344602c1204682c0d142c0d900e0300c420500035000740d80180e00610500070001009400400c22140e4240c49696051904502d9100c0b900983e0002d843d0345c64070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 521930089 1250 521928839 521928851
    0x7050a11031611120303130602070218070f140f0703020304050a030f030e092406091c0b0c0306011d030c090c0706050601140904050a200307080f010f05060d 69
    0x414014802030011840c01074a10240341400d00301240395401600f10039001e800c1c6044900d401007000825640d108131030f0004028001403602c1d000001c1d001d801c5000f504200c01b03241000200940b2041d00384224860f9a960002e4103036010b080310114000348500c0c6541104101460800341c0f0040200001d50103801100c0c68a075440001c581107243d41d0740140c0b0b2921050006004040c0d00c0030740c00c40301000484038621182041161400c503580c481c0c0c0d94004558510203200c03119105c00b42038a00044008001162681e244920b5200303940b00404210760002600e030000e030340018801c05680c02083c040c1d661107814140d070119502501140c1004030380c103109900d111405981e68030000e0b84542592415152128954074040c004d40d01c1c040c02c0c4505020f0040e074403402100030502610701d410301c11a008195a202c02000c3c4000b0b10042c02880701186841c3c81d040700541850380294020f2207607940710308841d0f0344c840140000160a0003040480300d08100200700a00c2c2450150084a4100c2000103013 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 521931339 1250 521930089 521930117
    0x40c080703200102150c07032c040f02120708190c0309030f090605032a19080907050105030c0d0f06091b0311092707020c040c0c020907050a 62
    0xd026210350044400405101c4031034a01c00c5050300b00321080000f80020100098540030301410680e0041c21940d03061404140031042c9882904210009104809941324a82216070000101202125514002c50401c40340b000041c00e1407003112808090031019034110340b5810400c41d54000090240d6024101200140640006a10503040d0f41600d0381c4000880c201585001341880c05062002c90078820080010000982c0250450742d0041e0b0341404d03846ca60300c050005503800c24880341200c0801c03001040c24800000c04403800c601c001103540300d04c031840c0e482503461603888403540a40c1e800100d05101040e44c0b004000090184001400c3c404100051141049002c4800e594445840c40c1c0c0c0358a100103044149004a00b50304005103802c1c8240707162609d00d9040381c860f080c101c60003110042c0c0828855000300444610075640d142c684c00307190805e02d90003562000c4040c0e403948a2403030401103074034060080440180040c0d01501a4625a44102050301d01d5002603800c8400e0015603401518 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 521932589 1250 521931339 521931343
    0x406050c120721291504031b0b0a02030414010504030210020607030e030a051903060b0313050607080105010c020925020307060e030913020d09080d1e05130209040c08 73
    0xc46040280c1c0c03040790511072102c3d20740d207030710100300300c400060315040d00c1e016042100d48012003c01103010704144104800fa0100d0245c09803100e02d07108800740401e01108100b1121003101401d152500203032101500e40120440b18480d480e141d0015034001c0104004818000002503105401418410701300f07940d0350003042d100c0060019800040c0c04c84130400036500d40501c11407450b103054030000c40c00d1914209001c4d09502c201d8603208d500c410380d10240494140710b03070480405095481c102c10b0b26424081c2d1080c0c00310124107000c84140c0961400035040341c2c42030311480c1c105e560503556074200b420303550227214280c48041c00007042d416408aa0121200c004039042e6141c0c0e0081e07000755951103890601e40d08481c2c3d20003041d0082e4000b000032021320b545010314855041e070003910060760781c41003010001c02004041030080c005000071607036540030405544002c0103030407103910b44090b4104030004902240c01c2101e072412000350402c041e1015043c00007546911a1003007035410900303511a80c84034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 521933839 1250 521932589 521932591
    0x28140f060a080402010e040608010b0405090318010e0406080d1805030309090406090212061302242a1c1806050f2d09100e101116091a15030406050c12 66
    0x11130360344642f01c0c030001d030400d03104071a0b00610f941c010710b041c0030f40c100300050307034070f1500060504000c5200c89510656844d039000f00c0092480b1400c40b00b200d204014050581440c002944565051007640080c0900300403040f00c4000704000e000c43c05542c1c5a40d0341d4001040c0c08001640c10000743c0019108010007085005c1c0210800d035101780f2151140e00c10403038000d10003a412403924804032000607049244605849800d040d0381c07905030600068105041d07500c1c00200c1104642e10a40d4050564100191404508949103a076280c6411144031b040460041a9100d030900040342040011008040a005000b41103d0081e40062400d1214540403a01741582251051414001000d0324945406e00142c00c041c003003420000703480402000040d81c0d1180907401c0d01d007031040034074100310503540600040c46020401c00d10400c1c2c4a80700c1404000030407640111580e020260840f010003450000c5809025812038802149503039555a10a405054080e2920700b000c4014030010f072a28403248151 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 521935089 1250 521933839 521933849
    0x7030c050d051e07020907050a02160e0103062307030c0909060b040801140f070c06060e1608060f130f14040b040209011517040228140f060a080402010e0406 69
    0x10310380f581000d00103412000814400100341c2041000740c0001a04e8060030254086200e080c62502c0308c00142041c3c2c14860480f19013010346040c028041818015515607134166409090704120900a040c40c40c4031403c1ca03294a0f90323010860307800003416107110703400040e40315906150400f0076503035800c40030043e5400350b04150515440401c042c04546400d2080a10400000e81c40e04140c1c00c01210b00706600b074002c0c0400080214003820b400034020960002e000a154034910040c051811207499600c41043c3e8101f200098031800100d02d071131400c1280b50040b02c000404800781030101544a0380242480660b070000035898141c07101d1107800d001e800502c910300425a01003030307103450310401ca201030301604404000c60000c02c00394010b42c0e028015104085442010246c44c1d242d40c000141c8100780c0040e03610030b1064014840d9403010040103200d04403040e0034856000c030500c4504018034201c4001007550404020300c5000000b9100d41c0c0001d81050041c10131171640c260540c042010307600c1c940c201e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 521936339 1250 521935089 521935097
    0x140106171507051c0209060a020d03140c0f0304050106050619110d1b030e030f1e030306101803150207020102060a0b130c02100507020c01080f040506010b07030c050d 73
    0x8421444081c0300c03140d4104a40301c00c0566a103407040c405030050003225113010007a20300d99801c4290805560451383c12a00040005072039812846000355603d449400d040006410084003121032926441c800b030003480e12044681c20151101499100d54000400999480d0340740d940001d000d498001c01018484088041c40100341070800020700259200c50302e8480560040ba0200349541d40201f1180c3c44c0d0188500307204440e80a400c040f0340c0d0803000c041d5140d150190354241560081c0002d051070820040d00a401c0300b01010072000342e00c074041200d4980c0c118007041c00b0140c005110f40f13001001030015a0121b4000d50712a103030300c4528401940c03607090244c0c0c0050500305540e01041900d5200d680024184500602400414000004140d00746820b40d240d4003512560b6000740b020340780301150442d08020710719004034002d5940d2642c0300c0b2035000c0703107812001c200071000e400b0004d44115082801450307c0e910f400078a244507400803105508100034006c1c3d400000b002031000100ca016140d41e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 521937589 1250 521936339 521936369
    0xc0c06050103032c03060105010c080c1b1002010b0303032205030c10060902090a0306111c022d04050d080408030a0e0109080d120c0318060f0b1219140106 68
    0x100c03480c2c1d840c00b260701104c055114034200f61071aa8001078824150350082c60000f0f543d41a528203c40709001e03946140b8020300804000c01000c0200d000361035103526044034002111b101031b140685c200c850f140c859a40503007007007000922401040c1e002c201c034454081b1003000084113035140c0030f040d07400040751142a07411680e0610304075465806140c0140421040c00c5213000051000100c420b009844020000c0303440d41d0803250180001e0050742c51a4022000d0189441c102988040080d4442440e403880750f1381d901880071110581c4090850700310042c2e29101c1ca00760510f02040201a4030800440c1c1400d0b0802010920960601c060814500240c55030b20b4900000c038005001180650840c007980d604c00009840ca460b400307400181d0f81581884000780e4081420801c0303002d0240440080c0050164102c0c3c00100000c2f0307880b4000f040707403006c401c1100c51010410070032400d018002c9005143d10940c1004000c2209540c1802113130300c60b088080e00d00051003001c0d03003996050750100c034448000d8a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 521938839 1250 521937589 521937617
    0x4080604080c07050a0608070807123303030503011e0513020a0305060909032a370c05040b040f0f06051c081c020d0f1d06060a0501030c0c0605010303 66
    0x4000c0c000380c02c003203c4e11700415041240060602e4001400396080050031b10214108071302400010500420460040c0440500204508040d03100c0c1800e400318030f40e207180c4c0e41002c0c0442d2090ba506499050342c0d9546146d2a00d103008807003030819607541000f908408000291662000c8000c0c01420880002685840188402404888000b03040e64019201d040070041d4144010046480c00c400000f00120705040141402c074404d040405501c0c40e600c03a05210701d500041010704500b480703100c00601d0407010040c00518411380052200184a801201000d00c01c900d4160030140004101401c00035030110030403210307415112207d06100700955111000d120b07606180c2403800074415000300b8911004030783d54601000313118920b01c1090604940c00040b19441241c0c0446014a5035100b003070000090710050b5034000d18069888a5000007198100701080700c010030080d03ca050010002c4007810302c4c11005402402c0048001403c22028140b00340c00214540b0400e8042c5000341e0318403282181c80f03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 521940089 1250 521938839 521938843
    0x306050f0106021c090b1303140d050409050a09150515010810050d050f03070305040521070612020f0c0f0105070203030f0c0912030a18060c0f021504080604080c 71
    0x80c001091000103800148541500024112881c881075055a4141080c1040c00c50348255117400c0680c0c2080e000810040c50301485407070000340c9000d1104040c01c1c40b220103800d03555002000032100400c005010030070032808070b036001590205040002040d20350b4140d0700e1010001c00d00035075240080c0d541090089404283e01080c0145100703080c450713a18100740e100da40d2804501d100d0140304040c111041e0303003000020b0052240000c0c0f02000c0f01c1d01c45065282c00780c410f42041c01640c0c040c00c10009003203400c550010f8100050017600340039020139801c5c100b04640c01000c030304815001d15000c02404a45042c43c200510021145c1e0307025250390800081903909603540544040b04540c01403041c0001c2e0520341c002940c01070724103080b10340d8800380c01011a4046420f00c101129a0102050a40c50386821840c0c240c2212042850002e5494640005a42242c4804e4000d8000d900d04108070005090086280009945030018075091650f928203041ca00001242d0403103001c0c401088a910109007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 521941339 1250 521940089 521940091
    0x1c05130c060314060904050109080c0703120903022404080304030b09100b031506030c0a080a020307150e0d15020f130b0708030f0a0b04110c07080706210212040c030605 74
    0x2803406108021030383d41c07040201a40580010722488010000c00d04210003544448d01032680154110707203030302c248400c903501e403400b0f8481925512103907025102140e01ca403d4140560354001c0441c0350b181c0d64680309108004000348082c40001e02000702049024042018000a621071181c5c52001d2510701c41e11418280703a00203800c10035007058a031070402c1e40c001c2801031403480b41c01c04144065442c000041d00c0c0c96610700c00250000d0789070300b0101c4e03603141c041141140c440c002d4080f070344016590306543c00020300c91501040069541d450303004462805080d0541e8803806900760010020b880c624510880c4e1241441c06c490f800c00244000314480381581310001440c00084607030502850ba2234082c458800103003e0700b640ca0a203000203a13449001d0380302d260100d10141c0200139a41040c0c415030103030791080090072114031800000086c0c0d08800607508054138440d54804050b282c43c1880c21407030b0030074105503240641c2c0921426030100400c030ae03614850750098003058034652135402d0420840e0340c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 521942446 1107 521941339 521941349
    0x50907030327140405130c091802130b01140703080106050304080706091101030b0402042303031e0304030e010206060a0b130f1d06030a0312021c05130c 67
    0x200b1000240f0030354002500c0c108155150684401c00786ca040a40007001c001800006018020058002070a40e2103041020070035503019900194003814044404102c0030760b601c441d40c0c215a8010828480c0c0d80c10200460b241841c2900c0040c0001c42c1402404d0074028000045020040b00744200d9943c950000000c1000d210a0318000c1302804811907910300007400e003c2c0540c240d14040c0700311400c0710440b20700004410840024184408010131131150b041c001072101840d84030035808040e00c0070b821074070300d26030b64030741441c016000d208200c0702c8504540c000d0f01002010b8680a00100940d010030b030109441d00c115103401c00690001e6008640c0104050b000082c2003d92488120301059000641e585c9076a80c1405141d036404400c41c2c00b500007548515280c5100d13100d81e0041c985644050f03800c81503c1c1d002146a82035940940300c04402045109081d8213200ba054242c4000d40 = true := by decide +kernel

theorem cover : BRFrame.Cov 521762589 521942446 := by
  have h0 := BRFrame.cov_init 521762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 521762589 ≤ n) (h2 : n < 521942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
