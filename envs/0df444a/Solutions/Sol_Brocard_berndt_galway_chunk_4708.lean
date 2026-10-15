-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4708
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:29:11.220084+00:00
-- url     : https://prove2.me/submissions/331cb405-9e0f-4757-b843-3ce54c2060ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 846582733 ≤ n < 846762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 846583983 1250 846582733 846582739
    0x5040305160b04031e020a1103010b0409030e031c0f11010b060a03020702090c251a0103030503090c01080c27060301140a05030f031b03120c0a3b06040302 68
    0x81c070316a081003222082e0500490080d00c41d602000d0800e00400580003000354914016003003c007100c000a400030042c0c0c821060010008101c442c40c0754081821900380d040103400007240303104103620604040c8041403c0800001014008031291a409042600d611140504200600400400c0ca11080d0300c0b140d8000001008150346819103c0014040c2d00300030010b0344034540c544003280c0030845c0c0030111801c003c400541c5900604060300f444040004110302968050b52014030403c24926105691f03001c0c620a40b195500c0c4c1c1032200b0b59501d44407160f031150741445920340c01c4c0055041e40c03809a66010300980071041d0442050b031803050306021100c6005421070004400031856000503c04190040c1e403d4500040c09075884040540d6018081103c80040c1c0041011142200080044a4016640500f1203280c9003c154500061090481d0440d8045001085803210503a210b04c80c031340c2c229107000c10b111285140005042c8184980d1545107552540c28a243c5040e403103201c1510000c580007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 846585233 1250 846583983 846584017
    0x30e120a150203011d07230f03070c03080a0606050405130b1221090901090b211c0203030603060718050a0e102414161109060406031505040305 63
    0x390210340041d4000380120414034a601d10564002e951010740c17a481002c26984042c4070807049846100110960421200070318000c0003c905421160001036015086958420410141c0c604004155200c00740200341d10130704080c1c040280c00d90000650701074400480b0843c10f2040702c40e2080c0c0061850744207540e0400c1140100100900004c1810041c0d04521010249014001014000070b03126401ca9164000c44a00051241d00c00a40c4458540100503100041a81c0300740301302c034003520b03880030840483d502003201c0ca440b00c070030088105002c3c500c0c0e000442c114140000041d0712000020248820008154840c0c44c2e900c0101180d20001c0c803018164002080c3c880043d11001402200e40c0088064039000014000404801034190205a91300340030400d400407000300c5081040a922100008040c0142946a60411200d0341801c0c819140340001118403820f011192000800c0b16102d50f01d00706003040407401c4145802e5501001e20380006480d655441d0503107513401002208140d285107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 846586483 1250 846585233 846585263
    0x141e1c060515091f03123614091503070b0c030d0e0303010b0a180e150307050906010c020d0212070303090611010908090607140f0d1803030e120a 64
    0x848002d2000d10b02503a5001c650b5a44140030000840380c41080444145030800030000b260410300000b140d400e06140140001594090030009280b1207007400c030190140b4190718010740c85580c480c50040004d41e6010640c0764001c0002440003100510001e6002d180d40e40440d1142d5080c0009005010361040c000d80b5151078001c0d1036035030b400981003110b4080c50010310360324a60000040e01d0407142ca40004518103021041c049621002c01024030200320000007022a03a03d00001d00b05d40300301c3c5201014001034540d0400c05181540603031066020310414000d0080302d90b404603005c20b100360151098500a241d610100f4590f08010300c03c01403078000c120003c010140d100d80304804030b400300e5a51010030002d50034014200c4070201070003405200300b040141c0c2c0d00c0c100440070302b003090302aa0382052120f078000700c81070500741c640c030016409400182001c400c2907003101030780000340a584c8000641e02d0941c1e4014081e0350801140c01d04c81c80c0f10310815000704c8010003e42c20015813111074440c0000c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 846587733 1250 846586483 846586501
    0x40b0613050c07020a14032e09150c0f0905121207030906110303061f050d0606081609030b0402040513060c02060411060712050c101104141e1c0605 65
    0x8040e08a2003036244000c0090602c1b030303610481c80d20200007005003030113400d4030781d0488803d00c5042e400c50064110756040d5a80c0c4c0b1070391040c140c0c180e02603008c4105180c143c00c490011070700562060702c180000301d444141000c2e402481c0000f030340d03000c2c0c50700c005840000140c2407405010b00690745d4202c0c00041d0741010103910a02c07500450f00c40341c4810300d189080c2080d01d61240803c556454208100d02035415201d102040115003040aa0400501d469000c54842081d2860b03600040c0c081104ca405010781d0804640d410404a4241d10b09550075a045a03902241010060000381c440c61b21080402e615200e82c0326000e80150b40900200710003c6c020a02948071002203a00780c1d03904843c002c942c81da508200040780c02039688030401c495000490282030300c86400698014080e40f04030401100c400550340308072030400300900956a2030743d2074445d00c1c620250b0680142e6000ea20703802e803094002041134007078141160003220440e610822003014001d0003074425101821607400e1509003c840341c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 846588983 1250 846587733 846587737
    0xe0a09023c1303020a120b07181d01210804090902060f04120c0905090606011d030a080414030a02031209040f0513020108150114071406100f140108040b0613050c 71
    0x28030039174010100b03075a10310340c10011188400340513129800850000f50308a101d040c04600311420409410099515540b02450780ca501c0003401c20b840e0003400043c01610795803a5850a14140043c0e00895140c0f03e0f80c444419003e00d10810305020f4590348001d0441d80c50805030f501c2c10320017010142c0c403150350382980500900502d009403580042c440c000f140c000198011544134049800c001d10441d12640c004448001e11208002c1540c42e0130b4403040c0003550144041003c89005035015515141071603c41911032640c07400181c8250f0180310b09400503100442d40308034554010740101d8580004c64013123406010083c0c0c05500841ca00010002c04a40c0506d01092140c003e0340c4101003076840303656001080058141060110301d1204040c1d0520700c82c41c0040910912420302500c0c1240284601c528140041d200c0ca002800320260a118580000580d80024403070b0031003c1d01e52010180000c1c00d1240c0c0a800900450881c5000030165160243c2d0622941e1080d4420881450244030410310343e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 846590233 1250 846588983 846588989
    0x15071104150905010f0b04031211030a0203180f090f0a0905030a110d09050306181002120609131a071115071106011d070c060603030e0a09023c13 64
    0x543c90708001040718400d40c6400015103102101e803614250860321400103120a52810f81c04200d4410700354030301000305001420502e01c098004640f1103803020080038040d0030000c4224018104182804407507560b5040b02c85d00280a01160000c0380c49030428071003d04071454000d8007038400090301c80d90702a07000358108911410b52003039800b544162502156081990700c50341da410b0b80708030040365440e685e035107908060844541c216404400ca03181c088099800c95404080d0203401d04003040901d050046055620007480b41c01f50070001d405907a80c8482400691240c458421500300150100703001e0002100000c80303507001c4984030b0b8919007404030f006004075640c000254441c000000c81c0a00016041c0c1a075000044103014865540400400803400074640420400c000c464100403c40520500015500a940d0411001d00c44400c1c481da0b281c50740c0c09241a503104001c90144070549a02401c485400c11850842c52481d12403429040c0e40080c42410000b6000a01c0551001d01c0381085011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 846591483 1250 846590233 846590249
    0x103060b0102030711060a091805090118080415120212090c0d020d0b07050909010305011413030e010c080408071202041103010303020d0302130e040609021801051507110415 76
    0xc5200c00049840f4040d00302e00400340a80120113484924103040581526074403454800c41880c1d43c1c582c0704140c000480c41000d20966114180300d8101c800b80110645404400c4040828070784a07555603800c2d2213540709925002030408061801688180c0c809a451003110909640344c2492000307039150050241c4042e0800c0c410180d241e501e906084640c41044c80d0003c02c01007030200aa140c0d021208802001c00307080010410149600795030302d600060280d8003500000071000d07808410000c42c00c5015110851900c2d440030308200003a44045420180c244c20719101039050b000d483e18803102d00494010180501030b505020a003081c0c4030800e0010725000300ca0074048d00e600c06044140e284001e01000d00160010250302d000f60b8069001081c82610088004600c40c0c0e444500c495800000d90341150840d80725072044080d031803c10040580905080100380c025498840040c42041800010366504c0c031000c1003500a2125004800301241c101900901c600c0707412a80e80004000d041c007a141d2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 846592733 1250 846591483 846591491
    0x120c0d0614062b060806090610180f0b0406080c010842130518011b030911030d1106090f06010b090301021e0418182a0608010306 57
    0x1c1c18801da610080407180090000d82c5050810b540c112040c070300b41158240442e4142c050b407008850720741300380c0004000003805440641070a401050900c04054850104049904800d100390000390141e44061248600300080b006400c1300880003808001c681c05511038035040002510742004681540104401d9850460554811400d96004404080c0400791101c2e849520000c0c1e20f0444071410807184210780714107882c1c2070b15000801040c1240c00300003859807942c0a210500320302803080b0400d2240305000703205a407811081d41c0070741c80071458000101912141d0368818850380c3d010900c0c0784034000c3c1c05c0d1540a214404042e100c44803000e100d410754407030040011102d010120b80281c80080340405011181d180528281d07454004040b0154155400c001f0081c0d018105400d5804030000d0512071601e407850301413950000704950b40381184090500d005404a003811104840d50190700c0f03e00002100404e4191160540e40328400100015203554007051a540040045040324402c3c0b07000c2c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 846593983 1250 846592733 846592739
    0x203070f080c0a110a06050907051c02010e04200423090f01050f040623030d0504031e0c121104150308030708091903031e02070305030408090402120c0d06 68
    0x101d02401c12500e90408075000d005601d0380ca40325071803a2108198840440e28000100d8a03070b50229031043e14480312a90101c04108620b04104080180005584010403d651183e80000e80100e00340180340f445103030340e565082d0042076a01d40c1d0400002201280070307210380c1c452003102c041100c4107011754040101c0310500072442c5854181d1611a000c5030460300f2903a40780400348488a44e08001659100307846510100da1203141040944076910a14040300380c3d10b0301e0304181420315414144c030200f001002c120a00c0410469100d0168412840454141c1e5040341d0400c0380010f901900402541c0340750341e449005014001c40110794421003250100103001400d07540c1080780385640f01c0200714040c20f0001809650050100c6030340064090141c0340701004c0603180400ca00d02d18441100441d1b9601003143e121200100c00744c281002c003290441c80c2c0b800540303003d4054080140002e1040300000b5044503e0b0719580c040e291844000002c0003076600b030041c208100c90300300081045a0ba45400800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 846595233 1250 846593983 846593987
    0x30f020307050609150a0c08030a2c151b03040b01090b04091110090f06020a0c0e060a17031303030314090a110607030201180501020a0807090605121e010305010203070f 74
    0x2103504c81c800603c000200d00d00000282c106802c0b6030607900500c0911746150012a29480c002c0d8800d8038043c03030002d5200948920543c88198207840e820a000c20341035000303480900001c010b111086600c09c15242542c07030100d00481d60013004c10300300c90341001200380410041d201c11403d050301ca42c110240000b40c912400d02c81207522401000d020a955900c04c81041d0900240c0385600c01032501e4a42d00c80b58455510206c1c0f000c0c0c540c001c800603400203201340c0501c0303180c41a040140000c50418141c604161001801e11a4140210180c0c2c20310170402c0e44455408108031000c170400d512403400c0d82035803403c0141c000c0c43c0112001d0521500d40d80080c06421010405c640c049503c001410058540768003482040d800c8008120700755961351401040c60100c045039001080c0c402d10026a581d101d0f200010159407000d408102070000c450010f1002c0e6130400c050740c0301c0c00b400082140c03032540c0b4811000c2070300000003060785083d0303034000000c030900c04190001d600c500420303110010003c10710307581 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 846596483 1250 846595233 846595237
    0x305071b05070b07020402070609051f06050f060307021011030717040f0b060409060515010e0307060903030c0606210605060607080306090411090c040e010509010b0a030f15030f0203070506 83
    0x181075401201090090515400103001d0702c90014100504101086d130b203210455040742d80507180b0b64400e072000b01a44005103400781312400c00440034401d051410f0085074010780c05c1c0c13046600c03a00d004000601c00e28800c00844c580e4011400041c000c2c0f0180c14030f584440c0c7d009031a0400040c0c14003a03014440303505a40b1250060380d110700b011a580100d525442c104040181c409a4496290210000440c000d0301409004031407005140480c410351200252042d020301018a001c1c1e08036039001c0080a4010401c0c83c11a81c05090511041c5101d1600390b00400c1c281d00051802066100b20804c0f241c6044089a021031268504201540711a410031849006d80c4000070700d501802c00000d1000c0c1040c55555070024480c1130380800b0782011a0004042507021a00c1358081c2c50302040400990860794130940c0106416111016154101180c19681f40718000c0410305141d16103484a00d00f041c103611081860005251540101e6280e103050385802048031000d84c464858844d000c100d40c034003201 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 846597733 1250 846596483 846596537
    0x9010b0304050c030d092c0f071209030801170f07090e0a020d1109090304290d020301230a05010c06201309060902160311010612140607030b060412021302040303030507 74
    0x200baa88640c0c50344188d01d090640149a00100f1240c01c103044c1c11071a25005001c110751107a1030b125007544c140b0f40401140c602c141141811540310001e1081032540c08203480069448003000421400301240456180c9600c5110080d00a41d0910024042c0482080c009a04c40d0f01143e0000031600d8010b500b940d41d0085009003018505003400a00c0516a010000701c0f0020294071810300780b0001102c2e00d4100c0e0401d80c001c11031030190004004101c201c85295212506046074500301c42428000020301c01090b0725401040556100369440204403070b2405507050400c5106444e87e40c0712804039409040045100b40000107040c1040030071810142e000765200d0641111148842c4100f42c0c03021204181da540040d4625565140003042c00715004601510340ea000c0e0740240784010442445928140740180054100b40c0340c40d55541e443c0d603c02c821103044912a07407490424003818000034100c0f4200501091080b40300050000c201078050308507500c07a1b00d0644400504103103110003040d8041d1050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 846598983 1250 846597733 846597809
    0x100504140c03062e1e09020a0206220203070306150501021b24040f06141602060f0c011806110a02120f09220b0f09010b0304050c030d09 60
    0x140003d10340d02a0196104c0b04002400600106548011541c0001c4441c81d046001c07211a00040382c0820260b03c0300c80c81c014a070343c2030110f1414004000003929084054028804883e407d0a00c802601d42c840c4011032041d0024281e902c1c080d600e00d0300100400180d030311a0131442c1e0000000400d58008540d44243d01246510604a000003800b0005014100341a240f4842c00d4001e016800f0051080540050708000e0420b034120b506001000d0312482039000e035104d64030820400c2c0340140483c5802141d545506035141a20341e090340c0d0030701d1007500038000c04040c07a602e0001a82c6030588450000558540a10000c04c8420001d03020032040384507114224000d64411403082041c106400010030f040440012640e081825801c000754403401040340701114480650100c0d034070707100c17a8403411107404403c070b81d040591a40000804e0409405100b0390040440c0400043d0a000703007440705031002c0400030706444071500b1030795000d051940240103008000088070300728120501e0060000344111806 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 846600233 1250 846598983 846598993
    0xb040e0c01050316021e03030403180b091306051305100e070228020d030203180405090a0204090602120103120801080127031413061412010e07090305100504140c03 72
    0x6180341c9941d014139010304086126001004450a4000300d942c0301c8800200007940d902c6c20141070041840c3c0b070a010004c1c0c032607401c400400490280c2821588401c0055621008208115640704014120744c1d0100c0c3e046100d00d440240307220940d90001c1c1c440d5802c0c64004007000e482d02140b4804220490b8014090381c4602d0010b105449510300705802074111456101c64540564003281c15400401d00840159201040c40d480c5d20920328400b14807444291420130a87c030b1f00c140915502c81a0b0b40e800307030044c1c5d0342d0f00442c0c0a005141d01200c4144502811000d2607503901d00d0a640c1c021502e812020001d5040000421405010f01170122030a80e420700700c50759002d1200070071310a91405e40045040c4155101c0300c81007156020003a2215980701516003003018a001c00c05002d402c0c0c0400141c140c0340041211900a13100000c107541580d1004109446540d1400300559048181da0000380c128031900103c841441c01d0f50f00000c1c821480340c402a40c4030b0400c428015640d100d0800c4d002d905400c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 846601483 1250 846600233 846600241
    0x50f030c07092706021306050306130c0e0d0305040909260306090a111603050c120f0d0c051e0301050f1e31051e0103080901050d0204080f010b040e0c010503 69
    0x20603031002c1803c1d0045000502d41595159614649606a8040300201c0c10200c10132605180040d52542d0180c00e110f0306004944045800601c80d40c080314403244a08100300d01c01e024144500c041c0e4000d001c40c0390080003060303102c2c100000141e03405a426041d040b6400004030504005805403401100040c05020041e140c03494481e000d01598491002404c2040c003480c948500d0034440e064071540280c40d041d640d917190020b02d50610480e024006035604d8100709018070104804221614000c100384001080d0801110072149840346441010408001c102c03c440740e40c0505d0001c6040710702c01c0707488850014084003480035040300d10f1606d04079880c41245050050810b0581030000d101017001c110b0000880b41441c80800c0714808560000a541c1c0303080003400024516000c5d00011079104041c002e6243d80d5884002e80b2400c0d0510741001004941c21064112540544001e05a003030151030014000d11a07680c02820702c80c060920850406280301140d5101140001741045c069642c5072940d0381d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 846602733 1250 846601483 846601541
    0x3050708030c070302011d03031201030b0105030c0d06020d0b2205220b06060f120414060f2202040204090e1204062c1c0b0c040e010e070c050f030c0709 67
    0x42e40031680c407d03c21082c1700c685c1040d070b814801000c2b0307101d100800840d42d50540c18046000c101c160800d41c00303507009282c0c10407a50b40f80260350390303400d91204000d6a101040030030030005c1c008160146030002d0072105007007a40c142084690704142800001080380d5901c00d01521500102101400041e90f84840803102181c00004080c2c2d012401801542c40c28040300c8101701070741d1021069104d010b00d81030a00082194544444495030311207402031899040c4200340300c1c4414000b4042283c2c1c030840b03814040c0800f041e401000c0c40b0703c0d0000d1046440b15524a0314902034504011140345034042c3c60204548840d52900b41d0b0165080340d51080c5c0b0f144540c0001c0303d403ca000d440701503000c80d071051203503086668810f49a0f1508e00310040e00c0d29894441e2400c000d06103800b805800000d00c0510080c00031021541c0018115803568070701100716250701e841a0303031440300108003401c2c1e0b019803c00780900f20300000c018241507240390100c41c00150b130740c0001c1040300e11350342c05400142000124940541 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 846603983 1250 846602733 846602747
    0x13060903110f0f12180d0606030602070f0201110d08150d0804060c12030911100e0a060806010e010c0b06010509060d0213060905031506100203040e01080703050708030c07030201 78
    0x2611900382441ca01580220292610b103100c94004007540c0054400b501c0d24100b80000186407031010752040c03c0100082505036985203902030340780070340074658400d414003503e90002001990058800c641e0351a003800e000305201d088034130503804100458059401c3c41c4000a40c01101c850030f50380d104540c0c9621410741100290102c01903400352a4100000116022500500040c441c1c3d840d46411602c130791500000a40c00250b8003424186070008180c0810712900c0344c0e80c2c2d9014119140300d01d131011001d0950301d03e5008064260048003520012801e65003050440340912426240c01c0d412078801001185c543c0ea9440d030040c400c4400344082a000d5025102424100d42c00405150a2a0742112504100e070040f480b00c800c403042c580b20402c00a90002c1d00c04000e0001034002c0d0642070a078403101c0c400e450003c1e210501910310000c080741c4080c8203106450183c03840100250070755035540a80c40e510704040c0400d0300c042c010b41700c000584000020881d2151012440501040ca1450b0015a944 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 846605233 1250 846603983 846604001
    0x8060108190b0310020c0606060a090b1c180510090302030910110604050d08160c0b19020a03020405090718060f0909020c0f0f120f0705011b02030319051306 69
    0x1540e203448044003560703001c0c4000c000c1c01842c1000141c5030003c6030302140c87d000025012a0203488100016051142d00c981e0102c191035440c0b1041d540c0d024a4109440c2c10700c540f46001c050249800101d44010700d001c000c10f16554096002c50b05c20501d5410560205c070b2803000b004000d80d0040000e40c0311814000030980c20160603051062807107410050b060b0170000d00702c1d0100c132a40c100103061000c0b19000040150000a066804d1101540341c0101402c030078100d50b809481c0c1d5038124000350035982d00d044001c030403030703030800d000d6480d1900075401030040e4001e0b01030340b0f2180c2d1070940015001403180c1d104002d80802030a00030012460040c0a44102c00c94280c190100f207000784000c20f005503207000515441249000038064120342030b03000c60405001c00c0c901500c54110400341041440e2450690388541e408103012507070340e5130a141c21401071402c544a15102c00008020069864001c4041c41c800d43c500b40101ea41d90765600230950849004803140b40e401040c85100c81d0100d90390750b1012241c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 846606483 1250 846605233 846605281
    0xf03060e0114070804061a18060a0b0a02030a0306120507260706110f15162007050112050702030a0c031b08090307090203090a111c0c1508060108 64
    0x110780c0d001002c0700070040112102c2c004500a80180410000d051084880b00d03039080f02c010300f503603501500080d61102174002c052545a90f0f0004136500e59139150504d00100791081c020f594134056410042d481e030f08040750100c0800d180c10700000710790140203200a10b40303a2120261401504080c501d2941065500c80690088125034880981520410401000d02800e40b02c03407450320300010604e450b221920290601c1030304104800241000400c00c0300340c212000c001ea01551540c0d040040314440b0b61105c003502c100880c0e0805201c4030f60082000810b494081e40c1e812002024000030f03105841c420741c1e250005a1080002810399440f514207490264130a141140c040c00304140c4084c040c520b40001502e07101800038110040c0d16040003544003e18a84500358107500d40382d0406500c1d80903548000c0c090f0424030100e038a2542c2ca28269801032032980400c0504601c1504210701200398601074088844d0035096840c120307a02810550b8403405050703542c0c0310320b0b5640407816440d0850284103919 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 846607733 1250 846606483 846606491
    0x60219080f220f1403071a1c0b0108090307050a0206250308160e0d0809010c0b1003061d03090d0c15020c03010c170c07081e09040507090f03060e01 65
    0x41070303021468402c19080d650000316409241805003114114005622403c50665958074440300b07a1030106500c1c1c00c40302c000c5400d808072442c819100256104e040c000313440d03151800302c01001030703411507101c140156001e90719610240c1e40d080722580d880c0304142d809801c5030f102510b258010714000c00100b208590b401421300c5002d04c05082c1625004000c84100c000c40e1401c0100840406004004407905159281001d1604500c42c0459041da60740e84000d0310009001545034866402190903088a9602107000840d500d003860119100139500d000c11981242410045031354044540c60300c4184a58000c05540341000c0402002040f58a20908541c1c00000c040c00003000e10b00d51001c003802d1806600503151040e829010513084450040c0d06100703100600d000d000084003183c00c100c0e84040351003174a5690310a1410511054010520800003181c41c2c0301e01c01417020f2444019020f000c03811354050090303446100c4203a030030048500a54402c14851241000480e142c2e82043c0440011100005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 846608983 1250 846607733 846607747
    0x702030904090302031e090d082107080f01080a030f050a1e021005010e040807120504080a142e0b0d020a1202120c090606090102150718060219080f 65
    0x75080d2545010b040e40540c01c0031070701e091020b4605a50b14811503a00284a01e03001101c0300142800500d0794001c0d104040100b19510f95010307030396010064800703201c0008c1040c40c001300d000384442c10072034400800c0050000006032001000a1030520961303d500d4040c50900345450071a1950820b0720024108540d80d4a2104c0e4101078143e85610b480482e8082c2070090120300100087d12410785c0480d510000300020040410f07040c00544043e554028500b0141c1030170003100311482d00542d0465070300c074003901440d40b04125603811039410014808059400000181c1004d88075440d181da00c0201d000d8038094031910410940d8401507048000800140d01000c207a000701d00032390301a400c4200d400c5107941000041d880c02d070001d800301d400104001c01d004212140400e000020140095025440c00b16411803640e000b4400140d072181044203040c040c1c030786003000908203a24080c9041d01c0f042d502001142070b40c03020403880c160404407079000024640981d210a665445006000c900003405d000b4a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 846610233 1250 846608983 846608989
    0x50703031e0501030503180102030408030d021e040e011a031e130b090d030b0604030f021306080307031808070602120c0f07080f0601090b0f12030904020d0f0e0601060c080307020309 80
    0x2d40614014802543c8420f843d88040c0320b02c0c03140d002c005040d0740c030601040055610001c1151000d0201100c0980c54144c1c01c8240980300074212081c1025050100300416034154408803a4101c58240c0c5011002c0d10410180e010700e44000d891134901107087c440341c102c220b1075400100340c1081d03c61048985080b5107440d0004441c00c251202c08154103c84801141998036019602903a50211444da25117869551160210301d120b01c0020f009080341404031034004001c1d884203008068510542e80d540c84549001415000c1220b0350451a001061010940c0840000c11005481341e81e00241401c21881c405280c10750040c10390001c40d485444801000a001400660000c02e84078005003031030070054408078140304050b0031000710340b80f03040f044107485d40e0740706900038100509880328964200e841890f2802d5108080030640c00500000d00103a0020141c0d0101d017086250361010400d108048040e580c03202c10a101e900006440c07170380c1c4039010420b4070b00203603009802e50044915200a0b4004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 846611483 1250 846610233 846610241
    0x60b030f15160908030d0510030213050a050a052a0702041e0509010b010c0321180606091404150b0a0b03180706120c09350a0201050703031e 62
    0x560800c19003a6414031403078031022521a030307000e80503041c9400f5140c100313040c05580340600034880c0d0100d6240c0020a4071462241c211034041c44d00940703030380c840e00408013550b0007401017a034032004004e207842c0005c0c4c1400054401c4074001e44081d420701d4004d00d0f14680800c441501210f031420714800810038400183e50354801e440e68104641094401c4281505e085001ca8000400e40290750b4146900c80b0626070340801900e455562605011001c0012100c01101403030f5058641c245152030710184550381e003844250360500c103100d00c000f8410291200501000e80e0702400d80480032400784404a00050304031070a5025680803400c6c0083d0044840c00069190b01507940700100856002090080812306000803c0d04251404020800245030400092200140c2a0b00d07641c02661503a03180e410500c5400e81c80000c0c1005200d070340000c3e01540c4032400000340052903003050403a040e000405c02c0f2004c00e41c1110907805031240341c01c1c03401d140c40603030140c40343c00e5030100d03070038450243e00510241a00c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 846612733 1250 846611483 846611503
    0x602090306010f0837060e07060e041a0a0b1b060411121c030f0f110d0b03070f050906010509040c0c140c0607110f1e030c010309020d060b030f 63
    0x500c41c241c003481d01031440d0802070118000049207032554004810303d0280c0e0f040c0c070030301700885c0c85483d5014101d00b491350050810b544030603014040c481d07000400651003038500d464040c048404201d03400f8511000e41604080480150300020031000030403506404001515040703961070300d074140c080d9801c100641040c84c01c03a42107c150a6142104441b03040440c91143d804011000504d0405a030340e0081c0300340401c01d40380c1d40030103450f000c004e405031085401907901000110004e0002c1503440c8013030320f000e40150700f80ca02502d10b40700c00460705140c002204411150a4128914154107000a100444100424a605000d0108044d1465464174454103c80720481c0c0d86101915040b481c1c022041c08008000c07140f664002c5441000e0b0365244411524001e50140c6507900e074140d241c2c041240041a11036090340507001c240301c01580d184217801007200a00850030341e1782e900060070040d4106d4525100194202202551800000300701e5403141a0010004040345c050407a00d08626240c982ca00d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 846613983 1250 846612733 846612749
    0x70509040c03021518040e0a060e10090b1902030105130c090e1305060901020c0309040902031c050301060806190522020d020d0b0411032703040e07022a0d060209030601 74
    0x8000d103001e0b04021741c1000a181c103e80c14045004c00650301e50b5911081800501902c0d40e40d8288801907208004044101c4400001486200000d013000c10f03461804841560300d4805038455240130503410320803a816120b00405200c2000b0315400260010610000c2107818020070100c046100d43c84211858071403c4421002180d0740e4441c82c1103409d01c0c4000e045111203a0042c80740813500c440100540fa0048010344d80002c000281d030000178a400e0500a0808816041484c600103e503440001941a034680341c50b1486c00b51a02400e1040e4079400085084600c9041c40381848545410b042c140701203202c411210420300c09551000c000c80c0d0180181e4486190300044c0207900850f14019495034407002c560400c032040003484c8900c0d1600c8003c12102e101035401202c40343c3d5040c294108c5100350240000c81e51280c0d220400c0044d0810241d07510b00140c850048559880c01b0b00542c0000106445803481d810000c028090042d1800840000c441094081c000ca1a0540b02005014001d05c211 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 846615233 1250 846613983 846613987
    0x1f0c14030721110730140102030f090703020102030d0507030b0a06120b09010b03010b0f0d020a0801240c0803090c12010912080f060f12010f0603030f050a02070509040c030215 77
    0x10341c102424401e00010600503542028504010507100d892440c083c07a85e0f00d200c2c0381e00c0010b68814103542c14a00300b00040010340003119050b084901580076611070308640300d05001544945228030340d03a00582c44000e00580c010001001c041c54180c00654000c1028140414800a00d40c00180e240c45241c02072400641e880440200d5a80390703004d10740200005640c1002c180d41002e00d0051507120500840a02d4900060b1862110011070101d46a4010902c411503e95000c104024100d1400b8403a145641c040c4580b019228101c000302400248040c5d00d9107002c04125655904494000614500c074a0154501e4405c0c55140e0b2494030440c0e81900b800060400c0030f0b45041ca00f0725142682304010815800308004007410059a501d0308804100c0f4100c0c90311061900144400c0540c8120402e00c0d402d200810280c080f03550020410f5a1117500c07850148000c991040b101c0c1d010310071540340140e02203c1c040101d8245440841d0b041800341c00d0001d0040e403281c0209410b10781c100d0f81c0ba2120140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 846616483 1250 846615233 846615293
    0xf0f01050c0a0c0204020903030408070f05040510081b0103150306050f09160e09010b0409081b03030c1206120102042409030b01060f0c02130204051f0c140307 70
    0x42032144030351011801c104141404038050004100d01c400003c003e00681d0300041600351940c0402c01c2d50001e0404008035a807680c1c4a080c1a005240f05129490045041202150845210000b19801d541e0b110300140741843c54268904249000b001c00785050540e1152180240505200410f002d075016000106440c10b10000c0c502e03001500500e52030440e0040910340c0c422a1034074103840121848001103030440d0f180c4400060041c411101c0c103541c007925201d251400c000b1079001400013102004207444481c05403c1c0641d449200840301e5076410001002031031620405002285d40160025059a09442c4130600c0207007282d1080e003040821000801c3d04155130915520032059015103843d01103402c41c5181c0d1456000c2c17406020794003d2003060500e400a05202c0d25244883d290003c0003410000020a2000029030090007018081d400301002c2680c1604c5401001d00043d181c0e5981c9100115607858030b400c4002c0c00d0050800da40000c00035000428540e540002203000710f07604400340303214 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 846617733 1250 846616483 846616513
    0xb13021e030c071a011a0f0d05010f0e0633040b070b0f01170a150f0c031a0109150f11010c02010b28090c140301030809090c03100b07140f 61
    0xe00d006003c4d0807400040018081c00000c40c442c0071010218212982c0c42d03490550580903680244841d40d01c0e410714000000444070124070400d0111112003050411319281c4609104081140031b0901403804c48000740513094001c00c69145040c064450305160400d44c44500c48403641d8030190080e105005644240040089a0b609450042c40650a0803401c420000c01c071079280d060f001c0303014007408444110801441d00c0c5130494242030b070300103104108282078880040c004151500c0d40e54050101d01c1404c00c0b040d4051600d0205903061140458040308006000715100358076010300d40304021480c0080984c800c424019001e486c401c03038001042c15108030f018002142920880b00c00d40c404945188205440710000e407400b5659811008281648409003d03034841d190454040c00c0100c1c00000007040c0700300c2102905521710129146802520b401749840014041030314807607000310707040d0710400524821078000d01c5054451020000340c0c805402103641400e003e1ba401d00010b801000403694004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 846618983 1250 846617733 846617753
    0x30b011404050708310206070609150207081905040b0705010603051c1d06130602150a02090306280203010e0a0c1e0e180c0c100b13021e030c07 63
    0x700f540340040e401d1600400b00d81c540c000c200807100c03604013a01030000349200001403a060760780c2c01030100e50392004246801002002503520075a907420180014901c02c080071b000f160030b81c1d500121070909206d41c1c05242d5000320045030f51501804130800c40002c280001e42c018000f4030380038000005e0110310710b003031103800c1c03105242880b074000c203005103c20009500050402240d624100d089618400c8000102d40f091140040000742410801800501c4d01d5001900219050f42c0e00300034905a03d40180c410300ba8004c4808255254121000040101c91031500802142440443c000011000c1c1c00c1208220307030086c1c000615250300801000801d105500400e01d01007585d21f1b1680302040181281c20450540440b42030402a20742054895540c401780342d4011142c1140860351903042800c5400030f1030340f011103030401b01c0c0141c400c40202d51000f44505e541044c00034100a001c10414a8058001d40c0900c191902c1110b01003d5203c81c0c41c0c40202070351094030280c01203565090f00781403120100c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 846620233 1250 846618983 846618991
    0x20041b0f0221030403031e09050f0309151309020a0305062404050424090c110313090b030a060c0e0406050906100503130f0b160503090604120207030b01140405 70
    0x5580994807003108060411104110b900c256281992030b502c0760f28044000d40040c43d0020b16041074030300c2c40e104c0b104443d48903100d15841001183d2054400b0036109071240500e030080c2d64042482002c0c00b8004105c50010103200b9070308120318880a40b1108a0801c0ba0094500100000d0741e5008001250a0113881603100071b4200044100100d03006240f02c6a41c03180c2e010303460085840d04200c1c000001101d00300103800c46059402c03481541c64000d0000103107004a0710030002411034554481080010049810b5074400e1003520308224103011001c00501600c0c0d650b69007500c9070f043c08002040d140e01ca04800750071642e907800300b100307014800c0005465103a08801c4c407270421f00003405000d6580c54028401d03000542041d46e01d9654128039100c15040000c80a0720700c032001600d2404002138034130014030030710304100c10900300c80b6601c00407101c0780070403030310328030150700220215011031030444454080f4009481180c1c501b940b2503440c101901000ea00c01c0c4c0500e800d07104602242e1078207025003684 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 846621483 1250 846620233 846620237
    0x10b0d060512100b01051e090a0b030f010e0c0c06040b01080601050a062327012a030e221a01030b060307031a1203030a0e0601050d20041b0f 62
    0xe502000c2080c55241c034803c101c145400343c0c1c2e4145910030307640100d069418100350034203050b000c6610210f105400e60312100c0102e1041042040c080780609a03a010b0340d00900442c1ca0740b01c1283c3c20141c1403136001c0b9000e0a4640140014800c103d1000f00030050207102d00c0c07103851480c4095240c5a01c80785000010b8200760311903d034810051111540c043c80b440180d00411248010b150b0b082e000c4d0095034819822418484000050710710320b50003102250a800385420fa8645410394190416142c03c02c404045a02d100c481c1e0a00e0000480e12600040c0184480103001e80c510806c0c0140c10189070003020101c00e41c840c0c070f80720314002404250388081c040503000e003403e21552001c00d000440d1031000910000600d5500c800c05490001103244504903454042c140034040c44d46c1c200621795a8108499000d102400c0000f41450500085240d42c102c0300094071081819050341d4070f022050344010003240074040301031400d400c5a80c40c0d000d8030120382c00c01d4051020760810040000d108401d40b100c88c0c1e007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 846622733 1250 846621483 846621499
    0x4050103260f0705032d0f16050f03031f150305091501060c42020c0a200a0b030601030b030a0203010507050309070f0f050418020409060e0d09122306010b0d0605 71
    0x192014601c42119904007418176140c2c1e07038051034050f50200c03020003500a041c42c40b80b02940ad0401c4800170056004400200447c242c68520074024a84100b02d03000d84c5048421301360752113140e1402900310903080380c038800949405500b5004040d00302e8a0076406a000030380075450030b506006a1882c1c14141928000e00d0365100204c09400da030f0000d4003001c001c40b1000307540d11904a0321880794103650406002130305480c001d05860428000c00040c901260700c0a10f4660341c41003003451b0407416101200c00b50741000381141e940c8401034006080752071081d40c00d401407000c10380c016502072095510821080d03c505480e0b040c10711981d0325105a0340c20071030b01c01e0380c600405e020340000c80d58810100c0340c08803800700f500011202c841c041404103242c0250081e007014244420807a040d002071030703402500c44c1241d004a1100341c04840905941c4901341d1000c0300a00ca410100d0074901d0400603000514210020809a0311035161500384240c0c072680c2e90280100f01d0111050301c03030080100070f04003110740e42 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 846623983 1250 846622733 846622807
    0xf1d0c0609010c030203040915150e01080714070c2903041a07050d151e05010909020f13170105060d02030613260403050c04050103260f070503 63
    0x8000744206820076051090f0803d00b0410903108004a9000e00f4105109000c0e00c001c50002002e0b0a02c18090700070481040e0300803030b06d4240b203001c8680c00c0e80d40c140d4520b1405d0711019419200a12341c0c14201c84225400c01c8440c011071042d00324940180894030103940460303e0218142c1000303028195030703000b003d4200140310100b24850408a01020404100507135074581a44c140c1d601e1140580f014800350810042c1410203440b00b94a804079880c0180c02400d070700c00d40c9048410180035028007404611054014006070b0410742c003400301ca49512664914060400240d104440d01d00c0d407011442d0300300200058065035003170084c0c42e04017030140c2d0300d0046c0714801d0b800280c0380c0c84010640c00d10b8443c40605242484003442000601080d8000c049014103210300560400398098001601e0754880c80b8078402c0a41014881d042c103c0740c1050701041e040c0d016024561840522070345c0d183c1d031681c3c280b0500c49510740c008002d10f01540310308000c9da2f444c04a1240d8110041c54601480129010301100c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 846625233 1250 846623983 846623989
    0x6080108060a2003061c0605040506010b0f0f1b07080607110102070221070f1e0e07020d050a11070b0904050702070302090a0f0e070e0906182e0f1d0c 66
    0x40341c005031522503c0d940b00d0b926400410b4240c6100035200a46104e82d60302c2c4800d05c0031030b92006c1d00403401071065800c81e030f0301c88500203c14030924060f40040c030030421024101c08612030181c0f403504c15000c01a203003145403104d035500d040e0f104c1e00294003580107282403150483d00847c61003600000754000f50b0820a09400051001c518036421450850700640d0104603028140041e101030a00b0b0401c08800c0703912000344014440704103034052566102e41c0000b0940083ca0401180301d0f2003940e004000c4171600e1381c0e044409411150b19203061000050076449070a00511000b40030300199807100351501c80c10410481611000346c00340065420500c820300168441e0b044071540484014030200b0064401a0404002c0c480c2011008035401100d10204504a00c0c501c142e004a207008212907041c0c0710004820b507280c041041000c46584401c80030080c90a40c030b014234100501c002c00d02c0a21003561008401a9980740310a40302155540e8049803401000a140c00c000803442c8000f00309440b004804 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 846626483 1250 846625233 846625271
    0xc07170106050d0809010519080a0f0623060415050a031d06040201050f040e040609110a06090509250e0102101404060b0a0b0a020c10080402060711030f01020406080108060a 76
    0x14001d0000083c174005542d0040c0d00701d442c2c5004c2c502c211141c4281c0302d100101f0410b02554802401800c0100c400c600043c0d40c040c0c0010f40d520b590420307844491008101c4c0001c9403480030107030061400e020006606100c2c026941d4040401d0300d5540e60368007a000300501721401030480750366140308540d0341c081c2e00d20001a001e07885a420301b0441e9840e2003e0300028050b0189511600e40e9021603030821003041400d8108802c494817403550038aa408048040012864603401007130b000682c100c03010840b6140c066680c580040800201040d0070762804400527034140383e0468040403606808008203c0e50741009010412000907104002c11104040b05660b2140042d102800d025190608070381a640c8100d043d030020003005e8105a03a445a003000a5160340c03560803864440c1e044550400561800ba060440c8a940e0081000307103080056907919141e12500346689401d48a416020241c41009100070400b41180d9151200190b00d0480386616101000b0080007065044c0b0804c0f031241424404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 846627733 1250 846626483 846626509
    0x310030c12030e09091f020711040926090a1e08010522050114041a0f060f01050a031b120518120f130b040806062b11060c0717010605 59
    0xe4220301030711101790ba90301d08104101d6626100740303044001c9811300044d5000302038a03817103158080d08044119041000300d80030410083c0c01c0c2c0424020580c10320021900000b500c04c0f442c2c9009061446110100340358450580011011008545010300c003d0540811072000b040b04600a201a10746a100c1110401c1d40d0340416004140f030b0b411000400c1029000321384003960a080c400914a0306043c040850a54402281c0d0528145800b1946843c00b4a03152489140d000c0c10689640211074011582540078a50280c10160740329050200a60046820340c20a50310396150111840d607071444500304e66000e03045440311401048850750705a001708046494008920341a5104c840f904000581c1f0701c46c600c0000a107030390f850004204480d1000c0604103031201e1340100c9145075a074070301340405816900711101288100581302026003901c880722001c190b2040c10442161042d00001c280d554004a10f00f03403030307a00000024006091642e16065954a048000303200311450704000c1505903107440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 846628983 1250 846627733 846627739
    0x515191e050f01051e030f151e010f03110f03120a091e27050108030703170411040507030f0908180105040e0a0b012c0a050105250f080310030c12030e 66
    0x102c4d6094599000d020f0300b0300c03020082e030a8601010103802e4010f0610700031964035845c124110011588142e2012710241079881d0462000911421038443c110190710b510092540a4001840c0d5400364406000501e1007103035100019841d0301c401031025000c014190449da00c2c04400d201a403d06800f154814021101001c42882096091038006440404100343e401203190070075000242d621400001064000c0c06a0341d111249250400002e5201c0b10075a000345c1040d603890000d100d0742c030345a8003141d00706100c0d007400500060301c2d82c00e802c1a500d00290075680e500d0040369420152042d62854011032209103030040c0780030f0800103041080b0300040d01c5a50000c5c0c0e10380c4034540a900a4102c990703601806c01d00c0700000b031855100b088030064055011030059030b00290000380c0354001e60035201010707448884510340d408014070840075400000819a6501d45105400c0c0209206c0380055004080c01c100282100d0b003541040404c1c0340b1b05a00501c0d8501c10000320340c0100340c2c0f1607001c001040c411 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 846630233 1250 846628983 846629029
    0xd0e0d05070b0307180608070815010806132004050f040e060406150314100c1d0904020303130e0a1b090302040b010210060803120907030515191e050f0105 68
    0x84c03000300c51714078003108007040c030b40f80682001c2042e68008243c580700364070b995140380c0030740c1c0c070f0101d00e5045809078515a804540c4e41d40c04204c5524004610159542c0c5082d800254405118015490109904079105e0860030004e01405682003031421051546015107051184500d0008442d903110002480902200c0d80c0c2d000d019880e81600281e10700454200d00000309000c9280407054031540c1c4260b0303520ba20f924002904940a000b43e250301e0550501d46061001305d468842400f81c035100041003241e00d8001000740000c1142a0105100581034100350389006103040840c40c000c48908995500c50500c0745c065010006a002d00c07540c09072541038030089186100e0b040181e2030b01c8070014007190b5160900a0200d4101c00c0000a44065280d105084003c2e0310341030f0886072202200c2c0005001500b0014070800c608414481e01900710009680082c2d4580750308203110708403030f01c0244880702061181d0340400c3c0d98407a40100c1d6001144404144c1065240c0000501030803c2003001e103202800e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 846631483 1250 846630233 846630241
    0x1050d110405012d0e1602010e0a03020102090325150c02090a1b0e06070308220c0509012c0c070218040b010602031306051312050d0e0d05070b03 64
    0x40c0031034954a4090141050126584803000d0350150030380400245000c2c42d0b0351207641181d40b101c140c0c0030100c900060b044102ca489450f200382c2c2140300400800c05540d00d49004e11038407501000300c071f51928000d0b400141c881003070300700b054200048501c926400c4c80703000140180107038144c44504115158034405139444001143d01f034503003e81c080b2001e90300100311030400aa10116811031140c03401c07490084080000c4440c030588400c0c03040d0003259040b240500c50680028010b04034550840348001c1d030401071500075003460260441c400c80440380400c489004010b1411310105040c09043d43c41c0d0758512401c0028021001e101c00411411b081181d0317030005c0f407661101d5074101d8107666005000c04650000140446d04800810f0f107080f20030000100000400ba4400b009860b102900d0310096000141341034000c80d0141c000c8068800509a034400c0001c200d0740358900103c080344100d020741541c45c11100083c1003506540c4125010b084610913a000144010590100342c0306441000b42d22031b00c07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 846632733 1250 846631483 846631493
    0xa1d0c07060f0c0801030c0504020a08130614011502060f060d0f0309050a120b01090915111303300e04050a060b3f040b090127020f09070801050d 64
    0x420b08418501500d050038980189a101100701e0507a801064003070802c41e030b50000d20089118600f416000141c500000c54080e401c071001d01c0d020a80070b4140481c925121460101400400780c1c40301080b06a00a03800c80e01d550184070541d841400c0c021050b03054544040410342114043d080100001ca417410071030101400351100002402014280d17800440d100c001e176080d0640d40300d1041e10180090380c0002401d50607400fa000109500c680c0125010414001200c090301440c50340f160102d00510407006a1050703010510001e50245411410b04c440d9100301440d00d40243d1101d8038042c0d0043c902884040e081100d403d2a902c1c15600024242d6604a2950050a05400c617800700c00d00050300b20b080c501128120b01495000411290f030a100005525900800210303200e01803160000c0003030003081201c0485907015420380300115468a09084042c0d00c202040d00440110000700503407019030911008000c4418002c1c1c511182505204038040c002c40ca051290520030010b40c0345e0401040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 846633983 1250 846632733 846632741
    0x2030a0c180c090b0f0c0f1f151a0304030e030d0302040626070e0103110a0c0c09180809010519200a0b0a180b0c09130207030903060e0a140c0a1d0c0706 67
    0xd107a4003039a0003048002c2c8c0080030619114540a0711601345641d000400c1e01003410682120100b4140008200b54010000c07401d802c000c0003541408110002d0700002d0700d040c040301446101d03e40c1c006984608101c07010380104402c103450020110b916002007000400211003079007201d02c0e42005054480d0380e4004134040d0441101c00c00349110b000c28503a40e1641c22a490700d1075640309820888100d07403a0314079001120100400c2089065540440d4404100e8060040520410600d4003d282120503040d0100540c0514100b07400160704510b40c404e03a50100c13081c030b0032808606000d8202c441243d10b401541e0b65000d1301c81c003501d031381d110713003161800800c015241c013080c2d40708902c03084900d444594007120b500003050803809094411603441a0643d244200d400544e1700d9100d0141c60f07421600c9000c001c7c268204009910b128008401010902c000041c20050750120010300e10f001000c014008400c89580c858441040a100310b1455001a81c0c1459400101c01071701984840309030418101074 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 846635233 1250 846633983 846634003
    0xd111507091d36071d01080a08040501030f021213030e030a0b311401050117061303090b0c0309040b010201020a0c03050a0327060e0d0e060702030a0c180c090b0f0c 72
    0x241c032400000090710a40c2c105120365140c1402d2617416144c0e645c80d040c0d41c0790034400c1e40061031043d08100900c40396010790300181e00d800307103008010f092040308400700a69150030384083c0342d03003181da07228001010313403152500c0c40c154004e030050603004149599420114002400e080c5c14a40c00c000d42402089a4401d584200312088c00301d009903000c60304040c164401c120450300c001d9400c200020640404259000340580301410041c0348694400c4111441d116180c80d01f10100048048009414050240035105a1500e44065503480035100d00300021104080c002c0c41c15a40140124802c50740c020840411094041c03c0003503580c0d14240c012001001c10070542109115110a401d07000788855402a01c904d102e403070104400e07199100d045035201c40b01e00a81c000119241641c650341d05008000d401150701c0641200d00308030456481109040658024418150000f249103884501901911000c0c50150806d0311302c0f1801c0051b140c80c24480d00050442c07003a00002c1003e0310440c00c00100d144 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 846636483 1250 846635233 846635341
    0x21b01050c03010f080601030804150c0203010f140a09080a14071505090f011a010c0f06050c1210081b18040302030a0f030e0d111507091d 61
    0xc94584100200e80d2a0020f01903800e85020707000d0b011810034030002d02103044e281c01c500480d05051500140d00d90103100d1020460070010501009001070f1801d024000c0079100e11a170201f4070b034220b04200d00d004e01e0b0040040d4007542c10072000c400030a128604030303504c0242500c0c1c0038a000d5000c216008480c071803100c0081082011a810030124070190340032038023405035007095500284607100c55500b0f0b29241c540e0151800880f2041070301e9980100d0741007680d503100e403191003116045610340c02e00f1200110340c031840d089000154191407481c44410503503c8000ca000840c4000e0804184503a1000d00d00303c5603401c5103262111011564400c025a1001079110441d40041d1810f031030002c1d1641c002e0b00d03031200401c00c4101106d10050181c000c5004051410f401040303010071803501103410700341c41c00107560a8002e0305050708240c034000d01528401c04440c0c6546683d42d00c1c00400030b8042c0381c003500d41580019541d0510900c0c1048030510820350501082184070402c1024440840848030150520 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 846637733 1250 846636483 846636491
    0x29030a080708040509070c030e090912030f060a0819080f070f11270f0406020408100902310b0609120a06050901060e130516060c1202011806021b01 65
    0x1c1002c2d000041007502c006807000d402070340f216403080e10384d010b0039100200407851018440b440c40c03d02c8a815079100c008402180c4480c42c004103165181d81c4140c840102e80f40d6903000700802414017445500040200500401c840d502c501c0c480841080b496500412113040050400d509940140684d820746800802c80e003400e07c014504800ca43c403910040b24040e150a0b101e1200074100b001c0544503e4422586600c1943e03a100c100ca170802800a20440e40c003642404041010541040810020100c0c5000012081440d004100c1441006071513540800310a0a041d889860501451202c0419041010803000590710004180303001d8464055002242440400300500f0009042e016144c081e81d0204110b40701e28242500381c800a001d50b81c85800b181000c94101c1c0c01403460b450030343d4012420740e17000360720140d4401810312956001c0f030005815412550144284200c243c0560340050008000d841044031802c40b01d180140e0014009070343c0402c060b00c940c1070074414690140f884000801c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 846638983 1250 846637733 846637747
    0x706030f0f1b0320070206211003140d1d0301060801020c0729070b0a0b180703141501030e0703050102031003050f030319020a03090c180c020129030a08 67
    0x540800c5468801d00001c0e04100e51200085076408013600d9031400000b2280c42c080098090095542c0300f1040e07a21420000b19800491003030b000542802800b003000046230003403450030180f00c00301060719204aa82c10075010304081903000002c1d41c010a04044500c4641c410010020740102810b0b400140594000200c45408410102d20401910390407200880581c961025a070420148001c80c010080020404140411003900301254000052000804c40e01403031404210b807651116541107214a450060006280e05405841550843c1306c044000910300181805c0007001d080c5041790501d40c2d600d5180044d0042881803c0141d90000000e6640f41401414407400080c0c0e480103071800d0090044890621b1000710803640140c4c2d10700c103912480301942490100030350100748008245a0b07207049000005407d0488107000b8220041006160801d80107450b06517064040c4070310442e450302c003049a640000786600c610301100c00300070a0031500c1b004082840c0441c200d0014109500110f280 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 846640233 1250 846638983 846639011
    0xe22060e010503011109150f1b03030411040c08070f0309080412021f09060318060c0e040e0f030418330f0e040609030306051002030d060503030304050706030f0f 71
    0x40d074100e50065000300156007035080c0c40c03081806003082195000320030302c851000380c03c074283c082c08900400016891908101207010b00c8622001900301500382c001004000c28001820703455400c1440540c1d007407058190b0024014540c040042020040c8411440c40356030711032007684421219688284450740ea943c0700c41050401011021040741718010007902102440b007040a541c00f840d181e81c072040c024a0900c8802c1e000ba203060228000c048040e1071408000c0f603545d001c0c1c3c0410562680f150984120f00d081400107403048141d6034412035100030a003031483d1800104850407600c03000481420300350290441d00140a032654181e8404196100d020400300c00c1e80e105401c5065000b9584074000d030b98509000c04414184180000b904102000030b010840c0c50b041701c1c0b0400d11910380000c42c0ea440c1c00000e000140c520315604016400440c80588941540c4a404060700c4120300450561500fa694103a0b102424095a810151601d0901146400b40d8102c010039041030b68051103031000c140d10b1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 846641483 1250 846640233 846640259
    0x30603030d241d06030a08030c0d090f030e150a0215040c0807171c09060c0311030d060306270f03020c0a090e1507092102040f050105010f0f0e2206 65
    0x20b1480683c4501042c050700e00082e00c01280e55000740d956045a48910305d41116800250030400100c0d150190b01c00050340c0b206c2c104414600c2901c03901c880800d0002440b40b00342851001c0d030301a24040080a0f00260009008510150104940e010075a0b4901c2c225010f04070700d50204d1168860b6550104614400700500c04120010808444849141a006081040401c4c0088001c203190842c2804500d01c1090314031007032800b81c103007050340f0001e05402c145540d018802040c02c90b07a60703090a000700082d5002d50b140703510326103803109406089400100c0140d184420014003800c10383d140c0f0340c00c15009102c880d1103c1d400420301e041013585e40b00c640000d4001000909514080c001116402001c4410382c3d41c0281d240e5030740d0300405410280b008080441c0c85035201e40c596583c1440c00300507503460154020785400301c0c60102d0603500d4a00003401d002440b140c00400d02c0102c02608003e40d034000809040e101c001c0f2185802d0465041c501104d121240c0b0081601604020700842c4401030854 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 846642733 1250 846641483 846641519
    0x150f06250c0b03070f0804030f050d0e072706260a05010501080c0103050a0c0c02010f03020c0f0a03080105030d080a0c0504030506042a0b040b1b0d03090314030603030d24 75
    0x31000c0500b07106490840d8146e404440c010007081c4501d1940d1452889070018200d03a8040010000e80c00d0300790401685051416409101146c20000f90344d030f04500c0d0780111080140c4118400c1c01540d041481203c00d8600300c0041d00c03e2850325840c0100381460030440283d4950f0000020406561641c05054440c04031032203460101c1d00307042c0070412200c940c0c803c032a569412a03603100e8491400f075004481c080080c1c2c54490400d80c09200d0300003007440501c0880303918000b0900504c4100900c0c078010300040c405038041031098001c04034005803a6000501c10350b0000d01d07800c00082100710f046095910340100e410280c402e100740400c200c200503a0303203d02145100c1456103e140c00e052070131400b2400c442402102c20450080c1320400585031000c010b804050b81810450b05d106114034a21840d000440200a001948400012050580080d0100003030103103054046d1030b500d480000310ba80c0707128841421030035994480300c0660403440080358410951001c15401d1045030f03104c03801c04507011514 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 846643983 1250 846642733 846642737
    0x1022a160b030a110906031906090c08060901080102090d1407092405030106080a140a12180b090f06030a060302060f0d18020f0d0c1a03150f06250c0b0307 68
    0x40c4c06034000d4a0024141c0e040300700000c04442c40c2d40c2d1042c14414079007040b110901d002c00d0703c5210100d0024154080e144003800142da0310000c91038010100650300906907c15540780c0d20402005010391601100c01200329000340c01c102160b044080b015150a905601c1401c90518002410410411501c0c10040d1907801e46a00da01507911102010b080300c0707107031040581d0b80d03000c03140300c10014084480203611aa00380d41690f00c0003043d610f580a140c0e42084081c000580c0b61a8500c9800c2031000860001e044400e004608014000010441074040080050721a802c080001540001d107604803402450b40604281c2c1c460350303869000d660744d4101c006015410f40c1411446a000d2101504502c17910360010b045042d02e40b001005d100c40084011800e030741354440618040f138001e240000d10303c49062600b00c101c1d601c0c500511000d80030300203841202d126a8052080c404203035500c1c400d843e0500c04082c415020042c0c0640c1c0c0a80f102840200104001007440300016400e1400018501c502041c3d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 846645233 1250 846643983 846643991
    0x1602150403230c0f03061504140103140709090803040807081c0605130902130b03030f070f120f0215060613030b040b0c03191109030f0105060a05010201022a160b030a 73
    0x410000e400304000340484c1c16030300c4040050300a4031f041d40081e80c204c00c09000003540b800554140311940c0300982095501e1051030482024011040005400610782c01008000050701c41c0c0d0740c90018031000e000607013002000700342ca44c10300450608480000e900c401e06041d2001c100151140030384010312400e441040f5410b0402d4a81e0000e0141d82e5910758014008061118558164401040c01c95001e80c0c140c0300500c80396165000201c0141282d900403c0c1c4004034104900c0d00d2000b1000c407a9000f0204407480785c01100440d00002d0913900c00314041d02d00d07801c603954032010498500902c420a80c074002140c1000052102e4040501e0013180144c442c030030141d60fa000401c5c1144401c0d0f541c3e070b950301c19040e00b007a00e07070100781d000306941d07a003a080203458550032000081c500000300b4090590384e559402480241e103041031384000105003e000960424402c030600c49000020904110034210300700d40780380942c4006100401007520259000c440540e10b800c250300140c0c00441e0780342c040c2490 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 846646483 1250 846645233 846645253
    0x120703061d0f01150909150302060412050d09080c1e0607140f19060209151911010b030c240309070801051f14120f030a030b0402160215040323 63
    0x100342d040c02c4d42000d1915582c0101d4503040e203103002000e8041c0307821044008104c000c401030352450000c01c000e08500c1401d500c13401844c1072007801c0101c010140c86c14004141d80c10001ca010100ea400c10300f075021030380c00c100c18045030311803442c4101c4102c20f2607008200003000010001d0340715056501e0700f08501200c200f61242400d080d60b035145864110b1042000313a20110014a95070000c10030404040d14060400424880507401030300f0080110542c60344690480d091136921222a034801300c10440280001c44010000ca52543c81c1e0850311805021102d040c2440c0089070800146006503006140340d0301c0c50480040e84c1c80c0c4003640034a4000d942041c01041200007901010201c0d6905075144d1390600d8078101c19103003e045030007403540d0400403016100c40000303030034820040a6031842015558030301c91218000e080fa2880b100c42c40c8140c0c81800350764104408900b00d20b40d071660548105041e809080c1d00d02806006a620080040b41c10125101d07144280003160240c0e80c0b03222044462501c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 846647733 1250 846646483 846646499
    0x5041b050c0a0618351b0615030105060f010518060708030f011a0a05040e180d021609050408031303050c072c19050601030f020309070614030c120703061d0f01 70
    0x3c036015000004540658417912441858401040c0212543c0b03182c2003017058a9442d141041c4c0115100a403201540491400398102030084c02c1d03001c1c108035050841d060a083c0041d00070702640c00352401c0303001d80f0702c0481190f4442c8c80844203070940214803c0d460345444600c3e1903460009004840f850203045888040c1c0e081c3c00e01c01e0341d0000c4950b88800e800c05003021108142c5801c01001301d54001018020340012113010710411700a501254060400004159032050380c3d111243d200e10100d84c9071004100100b82210140c2e50000403905c020320441409040407910b41c05181010207140c0030f08140041e5403050300710540800304c0c2c200854108000070342c502c0c18055104451001d80c40f44400444c2c5c26600c400c0c0d02040d800201410006101c54584007150101e810465071030b00d403a404104140407507078222010058001c604010285103181c854580b03d00c501175155002c021802c88400b0980c0c1a0084d0030441c0030740301050321088907640c0e0100e10383c0035100654501c0e541207541400807803160 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 846648983 1250 846647733 846647783
    0xb030f030d091118150a0b0a030c030b030304050604090b0301021c05070311030705090904020118060504170c0a06031505040f090303050c04060e0f040e0f0a0c05041b050c0a0618 78
    0x200120a81900c01d664080440e179000c14a0301215034000684c583c081000840800a4403d203801da6800203500c040da480007900715102c94000d10310940c820f100400c150350700da0088401340c680342c990110740e9071444404a8068040d0600c02d0701054924603212021209952151388903241c030796814090041e40001c41e80b040e00c401d4400e50005103081042141906100c014030350421700c18901141d450801e010780c5065060141c1252002a800040c00c000c960340310b40951001000c074401400040c50504001908007102c3e03c611014162203008911380340700708421003401030002900c00d00210686080200040102907c100c012900e0803020540f00b104880aa60595105403100c90b0119283c2d0204849070076100c40882d4420340700c1c8182172505c002031001d200998292002048842c10710b180c120b8105c0070a0700807a00980c07500455420b00380300b040011810021034105a5541e10003405040d017016a1084060401420a2810700c07050380300003614482540980e881d0310035440441c00c99a403417 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 846650233 1250 846648983 846649009
    0xd030c030c09030b04020a030623090d1e0e030a0309091d0d0516021f140307020c040f2a110111030103080c10060b0307111f0b030f030d0911 62
    0x707101d0b040900000707204d65a45a08140001e01c200c110aa50399285000e0310092101505e42d5010136240c03918001d070381511650020b03d02e9020f4000780600030401010035203111803860070003164030300e6100264040c11245034104009000c0e20b884007010704002c4c010f440f00b0310410203800e241409070407812b59291540e00e0240d800c0005810165101315084500350400e440c0c3c150041e501c2c0342420300580e01e40000744014100c1d011070300303000e080514020f0248842c10710b00c450384610400411001560103d030030394021908640000301c0314117002c11040100744c0f104590002d00348070500d9012080c1c80d55049035800c5110360f01c50090202030054a400e0302d94528407180644020300051000030009805400c03060000021900e50482a500c070751705850095210b440941b50000600602c942e11010b00c103003221074203006016181c0001244003121281542d40b5103210740d01c16801c0e11650303042c410362601124200071a40c0710844105020020a510341c0300b02c690a03410040700115040c404480700311 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 846651483 1250 846650233 846650237
    0xb0c0414100c12140d0b01031805030d09082106030f0a0c030f06090b07120c110a0327080606120d090e0c07080711040b011d042c0d030c030c 62
    0x102c0c49141d0703520007061040000d03540c140030400280450081c850b001070000b260b0886008155130080754005800c540c0e81100103086848828070a1002c904000110784503080e010b000040c020712a41030071505030055a4144ea00319103152a100c01c8260030064490090800701d003512141c05030b05008655a0501e420300404070001c007942000400e403070104216245020b101c001c81c40d5445a601c038160041e0445c0c00303c01040c3c0b0030650860303c48017841103002504807401d0180da403950342d900c110b40c2c81454460003820003045034440c00210404010207060812071445211805440d40d4880340c880c442250300c1b0f40030b03003044121710300803c4d0001a07980004489840b2107801c5d41c00c00306c0c544400f04000f000f800304400c00700040000180701d038008050306405106005102035841c0100019200083c00050410800c12400f40000b0a0200c00c070840000803503002a4200c41d500d9130140320515440c01ca007450038000c40801c41450045031140c455182da5034108001071420805408481c001d080c1040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 846652733 1250 846651483 846651497
    0x81207034b060803070804080705010302030f01230405093a11070f0f05120d050406051617131e05060a03380d0b040204180b0c041410 59
    0xa00307010021440d452031001600114290352107000e8640745038041d40f4100d800701c400203003c01a810342481f0403030141c8402d10742545542006040d6843d00d40042c006e0709011414408a6800403003000150300c0049405042804079140180c1095150896540340070345002c00410540c0111501d4030f061040a81d100c4c4031583c00201064040300c501041719280181e0b8411402c0101b0f180c3c52440c02e1400a040b545542601603050100744144a1115034140c11661300614008290a41000944d011741d552890603985a11100085a2560041131030240c101143d000e000c6066140d580010030050124502014241d903a440f00040f00c0b191402d102e040310082d541040c4080c0c80c101004010000c910b2601184d40084401c41031800307072009041e2041c0c1c1c05050341e80b51100045103510291000b00701e070381c2c5100450644a403004000e0050000344565a15580503559182585803000c507290030180c8100f142c134005860280c40c0c4c1c0603019402c001244600110030700d02e0043c45211010070039a80d481 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 846653983 1250 846652733 846652841
    0x71a0702060307140418050115020c0904110a050d05010f180b0606030403141204031101060501052a0d020d0e0a210302030906210a0209010903080708120703 69
    0x132012a610704402a00460401000031225580c016400a28050b03400000d000e500d800710000d101599200000300307540240d01c2d20102a503840030402e1340035070880c40c10201400c5600c0052403c0c0525048a41c0c082c80000c5c0280501c2815400301142840d030340c44c2000100c1c0701b01801007103100c034450000e00030640350000885504152011710b422911178201200380400030f03000e004003500842e2000612030316050170002070561051851441c4840c1c070008100c00760134117000810611032200040011064400380c40d0400003071240d1143c50316443e1040c2c0d003005041190003502c1d441c001c400540090305448028440c0c1c078001d00008101d41503000c43d0007441c14055204070305d0401c0c0000540a6000a01900c082602d580c001041e10302c40e15500c030b40000c019011900c9a00750003502c00c0702c0d0345105200744140380e42c0005010090702e420249458480040e0701d0b061246202c1c620041750302200900c244101160541c001c540e00e0f010401e00f41c181c140d030304c1c05440c1030350710100a10310110b18221861 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 846655233 1250 846653983 846653987
    0x31e11120703170406050f28020c0f120a030f1a0108060d020910030212030c03041802130603090203010c0e130209030a0807140f01090c0314011d071a0702060307 71
    0x408810344207081808141241440d080710801e4100d138185c40e81900c41080150a0010380d010a5000d4a182c0c4510b011520395a9140160005400c8070410325a000071413002092042100500103142901110440e50007518912100e401c0001c05e100800c0c10845100c0d102e41d04c0f400f80d207228003010b074144111440700600444041c003001d0601e6030400c400c02111030250302d600640b14441c04d00a4003c4001c10b14500c144644401e2103865000ca542041c40060206d442c044100ca04131500303000d4003900c0720b204884040091046e03001e084c03214901c100000404a4164000300e0f0180e0088008121258403041c0a607005280e0f0000e4592094002c0700070340744203c1070383c044c150468000c0c049401501042d030712590340d0f0344860400e55031100c0690048069000422030bc0d4610101940244544034203556848600da00ba4000106442c01d6030000e902c2403103096220b0710341c00d14219803015006601d003401d6620344810f805003101020001440400007400030f001c80b9025940544403510b176640b4a0b6003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 846656483 1250 846655233 846655237
    0x1003020706020d060602010c1d030c010e011119060e010902030d030f0617032d03010911090613180207081c060e0705040e061f200a031e1112 62
    0x1007121919402c3c883d44049450302d11408018180c55000000c40280480c805000c203041d00c00014a0a000c40060410340c1e14080342d207101c55002170070180501600038005898480905041110790b22079841c50b007185401c104041110280903400402c0324014241007a802d0383c1450b240a03400d83c0c4140d0408071000d10a500c1050790018940c40007030a5511000e04807450311804c401a0b17150f501c045071100c110310303000000251040041c00144011130403401c1c802441c0c0014450340b80341d9640d590810031010840c404882c080d81d0001c014036070318699040104403c172114040d02800100c12000c0719040c82041c0b0842d480203402030780c0282030220b20b40c101582c0c48500308103540382d1519181d000900a0000e144140618980c0d21150b84a600b454200140c4400007040e440c41403c030301c2c62012060310700480134003582c2d0f1140f51030b02849032002d011045000301c0b614240403070711a26400d0b100f4107910a0960725412003010b544040d00081c0c240c120b400150b0b14450990765005007608140b01e40c40000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 846657733 1250 846656483 846656497
    0x8271f080414011e0605060301030b0703020307030212040b07021b0303180d020301061805150114030414190309171c0207030204150306050a270c09020c01021207030b100302 76
    0x1240a140848402c0b0203403d451400c01c0541900440403081004008079005030350240c0419940c10703085614580302d812a60101a1140c0140b540c00800b1440552180e0101e52130700c0005207503494a4100717460140c485240882c0c508006019201184950b00e0118100201e40c0100800444c1004510381c0b45121222840007940d40c8001d0070b00e4801c005031401c1c0120340040ca090340c000c800c180c440305001c0040c0e92000344083c041c42c4100c684070300143c2e04502c1a400b4a0045400c031522a40c6030f141c602c0c140051136500c0502e910406201e01382c7c1c02904070030052540d10076034600c01480e99076102450210b0628025819a0708451141c003a260312000c680c0c10340400e00d1048031000756880d004501110146013040ea107590040300c0a00138080140210b6800034441c0364200b0012035005800c007032414440603e001021481c007143d009009501c1003400c090590002c0840d03036554203c1455000750b0102d0f03803160350203046c1c0e0700203994280644103544010780c3c040e020042c40d8007880000c0340298800c1e4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 846658983 1250 846657733 846657743
    0x62401031409030406020f0a02030604080c160b0a020c0a03080703050c070b220e13081606050a06080115080a031407080d0c0207140a03060c02010908271f0804 70
    0x22100c04610750100090a0082030000080e40e030721030038201c00070f0910800040c01c81e007980c426110800141c4000a02c0c45c3c0c89030700f1514554445080c0103c20740be01181540300038011002c204041480c0306c0407402490b603042035400312168150040d040c000840c41e40c1c4005025520207103c006c0c0800d0061000701880385103c016603403445d40f90075a000745c5401910210b8881c0203680c403041101680800d070b00c1c0c01f4108400f086030f00c1d440c10152a161543c58408014151080400c0384407103029a003403500401075002900740480d2a125091200402e054860801690300300440c01d4501d0a80c0081541035a00c2900034148001c12614141c48100111140e401c2d0326004101d610f0110300c1c1400a8241c807190700da4081600c03104140003c1c43c0c442c1507004210715402441e08104150717200700010301103e0348030b140420002200401a801404002000ba191130000200300b21032400204820007880c03d840c000d155078442120a100003038848211141d4001e0200d8031000c03015000d0148244c2c064868 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 846660233 1250 846658983 846658991
    0x801091a090d140c1e064302010e0706050c0c04061823040b040b01050603150d0507050a030c0305010515330a09181104050105071a1501020f06240103 66
    0x45003042c032850038000150326a0f00000d0502c0b05000c0781403455905480c0c2c407c2800101c1d01040201c14580302603040c0b50051020800d204410340c0d000f0b401a55003404058151041182d4402c4050001e81c4288070500c024001c00d200c140040ca058070861b010790761032800d0304880030000344005004019114428440088040a090321500c4000069100301c1c07080d104a803241c241450f000004070010f811080c0300c1c840c140100100c003511140b441201c20f004841006040010741081d50921259800039070b0400300700d000c04404d2050500d0f070f05080300c0c407500080120b5916003017040c41e0910500c08007580042124001c0844030030942407081051443c508581c003000c00104d41070080d50054100c9030100e107800381c1c104100c0c000081203904410512500b40500c2c00c01014641c01445580503803130500c00e011401c04180300032011175241e00342401000c1c2110f42001c41d1020f0000e2082401940180700c0c3c002c0c00d5480d5400454000d0150801c0b01d0441240200c078450084400c40f4200090304060792 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 846661483 1250 846660233 846660253
    0x20406080106080a06080304120b06010206220303110a05310506071a041101140708070311070801090b040c050f22020d060906050a0b0703091802040801091a090d140c 73
    0x4140002c0004040d441ea00c11902181d914007101c0300b603c014660b504dd0741000c02000700505000091805000010303030804a4465a840d0a0f401000d4a8480104c40000805c42c046070507080002044500700060a81c1d11020f8211116102c40c0100c6044c4080720f044031200b00704509114010f444840c0c40344100d10500480030100ca00d0720340c0200c900b45c030079030501b04600483d03503044000003903600ba2199200d4031f4090702d516612280c3c441c2d02c2c00102001011070400c0e80350b070001e00040c400b40180c20000e011103041d604180c50400e406640c183d64a003003110700091546400c405d16449110068100f40600c504800103000c500d03c1c00d45e00366051a0200305e0903403800c0003413043c180500f05040300026642c0c103010600288480e203421600030100c08000d03a0002c82d400104a004407a403c0002144403140080660040e01560788220250744c01c1902140401a0903580503510500003504481103a0b55200da17103640e1522010f000011900e01ca0404600100381c034020001c3c9140c1804a50754554 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 846662733 1250 846661483 846661499
    0x1b060a061a0f0a0504233604140d0206090111090d031421090c100912171902010b03160e040c24020c011701140409060c030c030f020406080106080a06 66
    0xd000011200800d20003031b41c41c0300c900d040c0b0098505e20340718001c2e01d00c06520075800c203001040d08000e02951810310800090820030220600e803801c220f02d205850b003001c21082c002c1d64501060f40c403044c80f5400c1c4440c80b201e16040806480024a0003014070340407003c0d903101920f24452000d07803806610402c11502d03004c02200c11540880c403038451900c114074a41240382604007004030410a00ca400da8480440d48203038032040c020103944650f10700032100406440c145481d688265940301c641c06011600071820414080d1750052144590024004c0030725100405841e402c000c0c40400d802c4200003c2800305c1949003840350b900601c0f902c3d40880d503a4540c8120040250459540107000440d090741a90469042c402004040c40a003000e41803000500762083c0441d005000c5e05820352103114040c501d40d0b6840e00904000d9411250030070401d200c120000b0050021040418082410107a80740800300c580d00c00c5404580d01030b66030f11007503420b00710700b02c40d840c40c00740c44c0019542e120240490950 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 846663983 1250 846662733 846662759
    0xf060304030e090705090319020108221502030609070f022a04020d02070c09050c030103141005041b080f100903050403140c010306090e0d0509061b060a061a0f0a0504 73
    0x801c003500e0305d0fa10b5030f0138002010b14200e20284462102c8107042404e00040c1d8010a07000e800c40d02c845942e030202c02c821000b0040e01040084058000420f01c2540790b604106940118003480c0141c07901407141d070703d142c8150345403940888004010f92113981051074049100c11800d03030500102d00380d410306103000000181a03030444213141e030343c0395800034860040100c815240d00c014117084409000d2841c0030821001e490205201c09003014442c48040a0808020701000d1403105040000304040d08207424141c18403290030b14012602803e4020204844500043d00c410b180c0c0c00c03800400765041c144490310054411800100c0034000140004000a5500c0c0d4100c520107446100500405001c0c100060988103140d118542003403600d1203c00301c24402146020f660402c07810550750740d01c8502c011a0b014856145001d01100305100c0c00c0390207506c0030900b00d00441c070745003042c4126a140c03a0040422403c060300701c090707001708122076001007411f00058602061582002418950b0360214481d8903 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 846665233 1250 846663983 846663991
    0x8130f0f060219030e04020d02161a13020d110a080327100507033023060d0b2716090c09031713080307110f0f060304030e09 55
    0x1042810010301001d07504000c018030034580458a1040701c400c40d10064040e98601840c1030140350005203003017100c02c50f0b40480b6031684030481403218641e121b04102c0755a81d8122803541c001c115900218481ca00c00600c0c05107041d03001007415980240c20303a80c01c2c10f00500d0b4401d05402c400010300000c0d41510600250050a5100b80076400c4800300f02894803020503900e020f10711441c4103012000305564810107498400b60326040c0850031500c2494251409945141501b02c0c0a00440400c000382c510342d001807001e00c0c0000007a01c00c0c4a44041c410741101c2c02181c01d242c00a03100b021400103e0040c1c3c0d20103822801104405441d02d10b907031192010040392507860241c03035016980e41414968040c104000901d07040004206400035150002d08040c2079202c0030746a06114a40c500c15a500203040310402010105419243d40e981e4660030745a0704060020b80302c1180f400c0c1540b146050040407200002d0f40180140250040784082043c5e80e040540240c1c10094401c0c0e08259945a0f0342e029400b07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 846666483 1250 846665233 846665249
    0x90a0302090f1602061303030209041506090303020c04020c12250b180a0b070e03031204110111060105060a050309010b15090a06090f172401030b090a020d08130f 71
    0x1a8580309020001d043d007804404811580048204400d010003043c04160003585440c0159580d0110b02c0020007412201d40e40c20200c10103030f54000b86154000c405031088a100b50280c503a91210501000100c1c002c1d07821410341504102c43d19231807000190020890001d1021a42480503070f000b262000800368140308546481840301408241c11080c05c9024281c0b281000030002c0a01503941c05d10a100b018009500780070038418100100d50342403090f2000c030000c07142c0c1ca620915080c03c0c4032281821580c0460f002c0744036501540302c3c070034022a280d4140d80000d07014601d005500c0d4411500385d480201044425581e540184015030b80d42803020030200c00000c1032a840e003048030b041114680c84c0d035000304140540308400300300c1c2c4045503605601b04c915420b200c0c0303800e070021344000b0704110b002030004c800840a04001c8001603090700b0020306807401852400c0c555940d490b4000c0d074410415038041d40c414400051100010600001440850f2140740309544036903a40951510200300368000c600 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 846667733 1250 846666483 846666511
    0x60b0d0b0d15051503060709052b120315061d04020d02120a0f0c1e0309140601090b04060b071103010b1201021206010206040803160512011e0e1b090a030209 69
    0x4507084c400c0c0d6a55048000324003070324007420011300241506c0954425a4000e8080100c0d110204071446003404a12998100d4444078030800e00c5e1400d60a000d000c5560046403030180c0c118482d0104031000d07400c1d640b0707644130f8590300d02242d0b03408201030746141000c55000e60204400e20b1a107607035001410b9600d2042401d20000d042c01c0f174407401a18140f00780c022105151030086140c040d841005008078a401090005121b00381107402c801078040c81001402e22413001c01219520040081d040341260445403003000166484020001992118820380701c4980d41440080080360b500f10261048880c0100009001241900452103400058110351250395011030100c2c148029048410b500207801d1015100600d071640e540221070101030031075200704030750803160244a4001c07002c540e4070320000010f0900303544c3e4628018000c11080daa20b00895000c043c40001c65050b41d58811740550014081601100308840c00c0e070b0900c0d0401e00c4801c2c0d0040c0324050000150321240c1400380031b1141c0101c010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 846668983 1250 846667733 846667741
    0xb06010305070809030a0c05120705070e13080306191e060809010c0207030b0406021303300503011e0b0d020306150703080f072d0909060b0d0b0d1505 66
    0xd012644000c0200c0c0a022162040003d0503401000304c802a6030785003840a2101d51a0910500d0001642850501d8650018090701448000103100046410504045481e5603901144c1180b69110000080554a0078404541246050b20b58002540351310f42e0b2010b125541d9410070f180801c0c0050700b0800e02d4016000c00d000031a404061294040302a900038050303101c58100096071104107200150911000c10040750030400c03036404072800c407418202607029a0361039040000110003900f001005554150b40040700c1061110041085603881c1d4440c00d065030301e0120180100030011880c2d01da410b002c80b00104000c8000b5000c1c140e03845011200503182d1a0101c03d010020354802c0146c0e0181105210b203a000a500c80c107415401340300c800038039095498010058410b9080080c4603441c2984c541540da000040c40601c8030350600f8543c6e05c0f0311426640309080c01c00c5841e03c0c0180c1700004402c100c10b807910703031440d000030020340d074007038440008941175898890700c02242410320703009907840364240 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 846670233 1250 846668983 846668987
    0xc060914010306080d03111b0d0e01021504030806010203071e0201091707030609020f0d050c09060f150f13060f030b0a0e06100e040c2307030801090b0f0406030b0601 73
    0x34008030002070804004540c00c050502c3e9841414181c0c1804040d242d04050401203d14000c0d240c01803036640078216007205c0c010390031380c8513040c1981010000706035980d448032a610000c2c4440e203491955110a1250300d55842c02c442212000f001d5034190b200800ca1440081c0b940d452020700000c80c00004400d10700e80c0c0c400113000b0301c01a80000300486080068080c1c1820200b280c8046030350005000580c5c0035a4400b00300c0c610900c084040e4008409000f08046c0100401d185411240072146035140d59030300402c00c86c4100050b11000d030040c002820303c09402c01118000d1130341c00e03d0b040308142402d00402e04080c0c2080b0541100780080c1607140f2000032079030140076a1659100c104c480307150850070051440c2500d4001000c0c1341c03003420740040d603400301d13170240117a540f0ba154081c0050145a01101000d05942100d8602c40001940c041140a04101d0700d000e0b40c1840c1c1c3d16a95011050340b0b031940540140c44080100f0b43c0c414071420a9851325034580c495070000310b12034000c0440ca40780070000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 846671483 1250 846670233 846670259
    0x206311e0f1208041a0a0f0501080a06110c100509030405030d090303030e0105060603041b0302060d1d07120f0303060e07080a05061009150903060509070312030e0703020907020a0c0609 81
    0x1d0091000083c00d0100040801c055034120342800251620f182d59010381c21806410300000074404070b0720704030020407100000f02c2e40c0e10f9128040e001c140800d80e41615024070070711400c4103080d00e03500107501c9a4500007d64000301c0d000408081200c1c102622800000c1c00c08110f40000004141030420801c1015014000c594080c19414005c0200340f42410108040c1c0c4802040104451901c004c400d41d4140b004196801868025090326218140445400020200c00e103030030042e200351151254180e00001956000e907040c5070035406003c4d407203503201131000301d59010031030a064441c48045640030080800c58443c1c509075456032841e05011501c001101c402818460041050700c0c07075002129046401c407000c071a03010851048200c4000011103a0203416000101690b0a103028400c40100c0042e181096900500000079011140d01c02030381100c00b04c0704180f100b6044a0820409841e0181455901040302c2c010b4401b251040c0c1d0b500080d07800c05070082800b0480c03080c0103020601502c21 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 846672733 1250 846671483 846671513
    0xb1501050c0304120311160b07020102150109021809060d08130e130c061706060a1b06060609050d2f03010504050105151c0b07020f0a0302010209010206311e0f 70
    0x2820701c0c0818034070468244801405800b403113230300000b03000c021a44200443d107620645561852403039611003d024010754800c500e000c00a0300003920b6800c4a2034000c1d2050b00800e0010300300050300030f403a07071006582c2d040040a107541e03900a000c005510408803400340c0c8141c0d45003d074006c850540f8a0030444258064000808000c1150740581d0300b21b180003a440c0d000801120000e444501e10300040b40c07400fa0894010780d406c040200c2140030080190803c100f6140c15845580d034280d1260103000402080b900040c1040c00c201007000b400e0766030304000300c0c00704c1042c410100c951585140030a017524001c6d9811160b50b955041003124000e481c041030f407603401044500b0812412907007407128650010400250a070703c131176004200e00742c8c002c100b041000e90104090f52070300700040c10064002d411940f505400b5005100015140ca21400140c80102038409101d17103078043d02165100403405032040c203c1e00e0000440b104060a440621006056440340110040d1080c3c54500b200000118035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 846673983 1250 846672733 846672767
    0xc10080a150302030a15020d0e101b020d0309050a021e21030a0503060a0e041a1f0b070c05060f09120607080414030d0203150118030b1501050c03041203 67
    0x29002d10042e03601050300c1c40b81ea60010800142c00c144042c20030002d1050b9403c035001d06140c02d0002821031004540c0b2145485070744030400c60280d030301c00c0690340c10041621400050708060043c0c52024001c0c4e0002c0f581340e00071803c032a03a842e0147d0100d000c9003071550b02d42d045890901c540b18118544407000b10b52603a0a550851852003800a4035036032800340c58401d105100740400011415110090070074000c0413120400c20003401c042c01e0444040b0780ca40442c03046000104002205000140d0a032000d60b280d141100145034a080e600241c01d810402c012510344084400010b090750301d210180c42d4128000360241d5640c0c802808000c0310040b05134841c20706400402c108500c1c0d039000303800560b000b501300c1118208480c1c00c92101d42140306010150a4249c030200511600c11180406008404401c0c0c89030118035482d440c2003034031040113100081c65500d03a5800111080003542208030141018100642020248420507046402c240c000d02d1010b03041200072001e041e03020030100a089031113 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 846675233 1250 846673983 846674021
    0xa062a170705070f0819110705030606090415050108010e012f0a140c0601060906020f1b0604120f2a2c07030c020f1216050c10080a 58
    0x1003010484000c8004203a4014044045001030501954001c040b4016522450160340c1d400c4100018526215024260b000104000c1d100c4412500000d410001d0343c0c40100100b9140c0d580504200f00c5910003401219014a101c441074940c0d200c602525010b007042000128071042030761030103800c45a42d46540c611442154441c01000152008091102d0b00b5070900c06a070303040e40e481c8c00e85400f62042c505404420000a00061101000c034602d8140e40075640c4104a003a544c150890752030071072070400015030700106840000c9040410400d91b1400d0041e03c540e041c5642c1c2e40b4408880180d0000c00c1d20380210300304002c000c0141d080f4000b0940d52a010034614020071a40e400c0f0000105402207050f6a600030140040454500410740d1512594010a84040c0361503000200500240102c050240c0300d4070002100c5e1480100ba0101d11020040059081c8038052400380c2c8840e40f80d6409072402e01440303100c50401e807a10f120a04030701050f41c0742d1485504008000208070b80320007071140010601 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 846676483 1250 846675233 846675257
    0xf04020405161d010306030507140301060603020c0c0928021e0406090b0306030705130c030b03010227060c0706021f060302011b020a0509010602070812030906070807020a062a 77
    0x801030039243c43c0d862180c4182c82c80010001a80100035580001e8040c1c03152040c0020746000d41420005001c500343c009000d0156150030035010b9010768007080074283c0000c076000815081c464002070f4020a441c0720102d500c0790341c40d018898052030136040301610350000340c04404a0740101c6082500401e008915240502c1c000c070041c8419400e006e41c0f10040c4001000c62010b980402807000981801002c4505e00041c808a0200410943c0305001c08242481c04150f4207150600c20383d000700440307090b100743c01285909580803203008001205d60150052110004940c81005104040c00441d0000c20800284140d800310140c643c044503059641802c01c2400140d030f0040b03000c071002c220418144445140351000a5a2103200d80061360846420800084c1e041ea00088420480e02c1c510705032420f0588a034001c0c1141c0c0b1044802000542c88040441d40c000d210300050b541c4180244141d4405a2080e9150415584c2c46004c140d1480d14020214902c1d0400440703041c0140b80c641000c04910311 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 846677733 1250 846676483 846676487
    0x30513030b0703090515070c03081801050c0414090411040902041103090a0203060f1306050a0e0a0c0f05120a08070f080a0e09090607021005100806010b030f1f1406120f0402040516 79
    0x40e8500c001000c0210300e00c0401c9104480112f041030305882d00000b801300d03103000c0c1820109c40d0001e1140c40e500400c0451420003034100305d5040d13070140d6002410401d404041205000c05040752a40c2280c10030b950756580c4107580c0c002d60146020300d14003000743c02c91046500415140a08c040c08015011101d4410300401071800c0862072695a40000041025640c40340000010300c21449064101c0c017542042800308800c00584900b5640010440040980c480d001d20100d2602c40c1040103107540701a01078404119024080c00c03030940306680f034248040d000e6940300402d03000308a80c4004584c289210000514140540f2940824034400130320941c50700c07000081d91000e40c001d8600d0019990030100700c8030b48413110404090035406041384c480d96515261b81c000f0ba44205d41d111921003642c00820100380103090700010707484240c11a100264241240454081410003171264003150401070400158086c5810f2417041c06032144071030180c6094014402075900c005d262001e21289604100c441c1ca03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 846678983 1250 846677733 846677747
    0xf0e0c0c06060910050612070f0c0f08091c0b0a0f181b0506070b060a050103110406211b0f03062907050105010803040306110a0804030513030b070309051507 69
    0x108007114511500e8990f044c150a10818540100d6084040052201032000b80c60f00d880c0d00a2800380d40e0100084a00c1c1c6088ac0c000130700910081103c8944500080414401c40c060a09840700030b06d10080c036403a000c1ca040c2e003000005030031202e140c034807010054200038501c03900c0e001c03400c550400d000400395840c05000c0348071800002882d210810031507080580943c610900075001c05070000d50b07070344000c0c00c103003005103012141e5030b10400c219000481c05520a000300c1c1d4103600a11380700d9007070908146d4260b0311146d6070812034090b011009050f0100f5255405940344d1050004400e1450340b01c0d00d01c0007030141c2041583c031800d05040c0442044035100e5911a000f0207168039510368140520185101100e10804601416560070030001084500022004204070f84c0324032010041211400f112aa950150324903090125092400181c0820b020341c00412018283d40380303441d96a40c1700c1d6220900780d50282d9030b60002982d0313141013004215040040307140041d110104c0d09007030729113942c00810b04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 846680233 1250 846678983 846678991
    0x30d12060617060918030310080111040b0f2b0e010c080c030112021201050109060501020618190204021204061a0a0302030a060b06070b0403051c0b01090314070f0f0e0c0c06 76
    0x140c22060001940000140c5c00c0744154107450056a660b42000390760750440c18503900600409510704441c0c500e9840d200350890f41140d6503100c0d502d00346183c40800701c6d4503812144d0130866074560414407281a0860160f190001d4062100004180690b01441400c5401011155003400004c00c144000800c3c0c50302664112001c40c04524603407034961000c0303800c1c0d050711041682150f00304030011034602d4142d08018107441007a82100c00716900e990050a15030020402d6104a80003d002c5208003041d05010394802030000c0d002501e0071900401541304100101e03000e542042c3d4998940d07800e000d00f11084640c4110482c0c00d400d100c0c6c156000641c0381c1d0581c18008007103507a10550702c001c680f120b50075200c90a42200191030246170508003d03105a01c14005150780d10007819030354810710902c3c03042c403005020603598160b40c2811960780c181781d040d5918041903144944000040c05148030360110b030281210402141e4960b20f40046130103581805808224681c00c2408161243c2d10b00040850784 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 846681483 1250 846680233 846680239
    0x110c04020a02030d050f010627031b0b0a0f0219110607030c02061903111207080c0c071205010b03190609020609040903050901121e1505030d1206061706 67
    0x80d801c11200242e02c1e512481403440304203070600040181e10354038008118101c0c1c0c01503d8460031012207030306807004100c0b012290403200000c801c090010a80003100c40d0452400200d000b0341031621a9842225078101000c1030780041d0309601c048000641c1401480f0742072003031088449480015a85844802050002c041d01841c4082144002d25100380030400303049130007030a010390f00c00a5039546020f502d81100c0d80404a4207248140780505049011600c0c2c4a4540d01007101320340300d03c0d50840d9507a40140210381508001d0104034003544003440910010f2146414050b590461450441d081d5186100014440e8100d5048503000d900031410b40c41041d684030f80001100e40c1d05100140490180f01d4070745030800e02d03104100d03081541101c014400c84400741c80703e000344d500000560302a41c81c1203040071540c54000e927180d01c82021a4016150105444030030308410b075214800309260249407034403400081c0300d000210401040c14415003015066521701040c03460305c21701da03e242030175026000e280 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 846682733 1250 846681483 846681487
    0x708060601140f0f07050604120c0804030206030a090503030108010608070e040809060c1006120b15031c17091c02122a070f090e070e071808150a050601110c0402 71
    0xf05a0326600449812104000410f5211082401c041780da03140202c2c3c080328507001c884c26510150303006908106000c1d07807180c54207151a003198240f10b803580000d052008010340301e170000c42c0080c00600145018000120000802c0c515000d01d051820009600c004400c10300700040c040420444011284841410b442c255a64036106411a180c403480103201c1040303525111002c40c901d0042d416880c419802403402e9010703500d583c1301c0c8a001100b0311a00951551207001a41c40c01c441200b8031490700121818003100c4100c01035136440411504540240250b0032a1000f007a04042000503102e0a0b02b00380f00412414030200f002100e64071070350303440d5002903ca4103c1c40000421409031800160340074020340d207a441c0d075a0b40e40603240100340030320003640c1d00300b1a81c02011440081c2080c21208002c10540854a0f0341c2c806640004003d482d404103035651400100d04a03e0400c225450346400e803410007460700d0811441d000312200500b0b214100702815494041549001983c82c18441003103600607 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 846683983 1250 846682733 846682747
    0x4060b1812100f020306090105011b111804050717030316210e1c11030313140601080c011e050703030509010b1e0a0b04270f0e0c0102070806060114 65
    0x26180035203000d80d10070600e007080030011065019130003860007001c00395003d41443e40c80c1c900540d42940c40c0b044510100c0741801c0d12a012440c0f4502d503c1a00d440a0305000f405030340301030003404d21402120240e4490340500e004004030f07500b0703080301184850300d003019505501b0700d06031361241910340e203420f0001c100030391000040000c11401c60758102c0d00035031010400241032070354960300c680744c1164008003000b10318200d0383c1103030042ca50100c00c006103502842c80c550300c034481c0400d00e0b1880107064549540c2c0c440544581d040801c1420301a00310308000309102144600010448860b03608130b9840c2c0e031681d1b498841107a800c034041c1d0700740a606040114041d52001c043c0c81c014108142c82982c0700324400e90a4035641c8401d5800302e001a82078407101003082d1070740104c0b1802d205a11841e88044e03010001c064401d01c0026900308003641035580816143c110b840300d40e09503180700d8102c00c281e8001145103280f075a010803100c00280324400103840c40b468080c0c0040d0002400700c43c00c01600c40001000307 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 846685233 1250 846683983 846684019
    0xc0304020312070501230114011404030b0708010f15120c111b041508060c0706060911041511030a0c030c020d03031e05160e0d0f1104060b18 62
    0x440e10803a402141ca840f088182000c0e03020381010b43c0e402200c000304146040e02c8000d10400c580c141c0c0d040c0000350f08031000c5040110303200c540e50208400c2c120420b020100014242400c1c00780032314840ea48071035565041014034042da5040780d014459441c03101c42e881c21000c3e001039241c840d54628420006000901150a440c46150740089081501841d401c000d2044000641030403241001d460400100d2103030440002981564001c9201d01c2d400400011640c10200009000c0581706e00340c0030070615681c02c0ea032010384641f80382904000358041424071084805c98008517543d14180340010300b600c40e0940c6103440f0f125200d5201c040041014030b2000389070060a0115040e54003820700030303075190142070007402800c0b80106000305045800d40c05160442038054580a150882c0d8a000136490151040c5c44038001c40d035540d50400c801000741408100c0340e0030304405860040354800142e04d00101008110369072600481e1080100b4844407494191000102c0321001d030036505410382280c0d00800c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 846686483 1250 846685233 846685243
    0x703120c050d110c0406050f091305150a0f0b0d06020c0f0f03030a1409031611030a030f12201303080703180e06060a081b040b040f060302120c03040203 67
    0x201070114481d440c5440e414640c07000700f003042c5424200658010400000810080e6011803003483e5000e07952011005c0546002e1012a42011006d90417441d40b000598406040c6155404c521015800d04c0040041c940c4503402482804411703400c041008011050000d400000801d00280c0101d5001c10f0541042504104582603103d942c2e00303c03000c001e00d01e120181e8a60040380c0e544451802c0c4200c0356901109244101e014908440181d41030500261010450824010059070b1120074001c400040c2d0301c090107592401c5001380c2d11200340c035581d0940a40705c141c0041020300403078644079101c41d541161450610443d40400d10382c3d544e03a0700030b000d400070303820283e04040d15010700000c0e1001011781241414400c07180040d040c4450f40d0b03403400d96103400c82c81158020381219081202107840c1f845000c9040d070041c800c0b0010380845050040e034029035000342e004141000d60019050002d0006071002c0c0c0001c0c00e443c81d0542c030b80040541410191600540f002d03a481c1c1c0e002c400700d011543c0c1401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 846687733 1250 846686483 846686507
    0xd08040b0c0a0518150f0310050901030314030604020d051602010606080112020d08072a0e04020d0f05071e03110411071704031e060b01020c0303031302210c0a090c02070312 76
    0x6246803a032006d40d1010350682d100b42c425100d082040180050242007409a6a040b2034260315000380e0001c20700000d8046070b000030402c541c0b0075801c01400050115501c078580c041c0b513070203105982c0301c2c062482c042c2c2100c0c0300b80c0104c03050001e4007004018516800c040340d0451981503d10010410040c50300319941d001d2090024502c2e1384040041d2004040c8107040d0f52000822440114002e540f02c1502171140e00070749010350080100185080880d4024440c55001031144084808050b907605402080729282ca550080e0b15401100402c140a0740d10070071007018204070b404024648440c040c88031244111400103010b945031150078007005014806980c002d40d08070010508202d5644101422000b402c207044418070f1a065022074203510005c1c0030400d00e90b01030020f601d10340f52413903064464401510700702e91003c0c1e000401d200e00000c0c540c8000302038a861008241c42e160b01010081903003c00c0c0c2142c60030300c2c038298008000a90010b40c0c0341c05c60350030080300c41c0304094000c0202c2d070000c1550 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 846688983 1250 846687733 846687769
    0xe011502011401150230090d0c180e15060103090309090f0c170709030b0c0c0f030a03230c030c090d1a07090e0a020d0e0d08040b0c0a0518 61
    0x1a000043c00340c12115035241c0440ca80c0c1c2035540071046061184154450406c070320390001c403030f40b640000d101504c2d40102100a03000380311109503000b60381c5031034407003045811072a071746403071507440c0f4003c2c007003d0042c105a034240c0381c00340903064851088920920350003001541015101c164600c203250140c10b0700c0014103106c8000340402e1141803450360240000c242d42d0790006119000700700b5024000d40e00c190298020b599000102c51541d00c540003d03000142800026100c00c015a81d0042d004205c1a00e501000390090b5489000f03942c4080d0031521180003c200c10840307105015800e030003031100326034025070715170b60b0380d0f12a01c40d45404031003030091030421504081010416014400400c03460147c502e02d0030703c03104899866040c1201e6040c0c00d44a400008015400800d1101d1045d40184c0041c108100c00026042c2c80c0c600380e80c0c0751208402441f004a14180140400c0c80000d0100940c0300b00402c800c4e030300e480c1c0c040c0802407003440307a58404c0030170041640b900c2e58580d45001119403840215 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 846690233 1250 846688983 846689021
    0x40510030c080f060a060b0304020114040f0e041109010b0a030509011b020604050c040c0f1b06090b011d04080307081f08030a081003050604240207030918060e01150201 74
    0x82c207955550b4a803808a84641c1e44100400110481c01d00d0240000f55810f2080881c115180c6500544c0d03801140e2003800f4a01101748008070313280503424400402800e0030003d0300090b00b400d040c0000303400c107502d83d050b000700d18110052241c00360120403918040c8003850b0025080d542c944026004001200b91820003201661803200c8055000a1035805203010380c00751002126a0000c01c42150220010840800c2401020001c2d1078003800072010780d080d0a034044036090350740741d136140211002d410003154101c00b208010310425403200500d101025103820300c04036904042e140c1c00328a00004200b0310400c4142000140a0741c801001d800a042003005038100580d1110501901d03a0004002140099900f600045541c0907140100080301e80040103403001d504c1d1a01c80c4803402074214440400200400445050070800d88000c1600328041e507100030409050104941ea0040000c1009c0041814040280009000031586a04441c2070b695820280c007102d001c16809468061011280e400d15 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 846691483 1250 846690233 846690239
    0xd050d020c0d2105040b0112050111030127050717220302010209010e0105120c0a021c080601030501051e0f04110c0c030c060a0503130807050f0703060524040510030c 73
    0x38144844900041c15200168002c10f004802c403041158081c0481d01070100403c2407100e03100380400b03040d008900205001c0708500c400821170344213910907404507551a074018a03402e04007003080030703000c0d18039418011401c183c2c100074188030008032415400090140481c40c041d400d11100000c3d00c44080340c1001903242414007900039000300f01c0c01d50100f084203c5803655984250304460352182c0c000036920040e00e40200e1402603402c16240401544102020410028040f840b041561505a43c51514501d17050b000101550340c1a4070550142c40c140c15082c0144848141030100c014043e00c0c81c0048102d41c40005014017107040c110b00c020500064003100010020400e60b180820a50447e40c4042048081c0a6103205001c074074030010703905101103811029449807050b042402442d0003410301d021030315003c0c14080300c0d80803400698800c82d02002086035601070350741d0020000c1500d02416215070f01005040f4003000b03510340704c2c1e5502d00004040c0301c1e41003d90740241d07410040c40940c29403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 846692733 1250 846691483 846691487
    0x30203060a151406031303020f16090c0c030e150f1201050405010b030c2d03160801150e01030f0216050d0e0f210109060f0c110f0d050d020c0d 63
    0x1002042c07544003400741c400c0110304600f0340450a000d0003400303003050749150f8682555001c0000d800c6012070450040d03028203003840c501048181c01c800e4801c182024050300c1c0c4140401124481600c030300500850b4444040070940154841d004140d0a5852020070307022030500d02c09502c505140c502c03c201001c9001c4a900c81c40b042e0190680b00280c90801142e40c89484281550008071141d12440c8020009d8486070b090049904408284092418807061000307201c001c80f580045031800b240d10005c1c240804540d0f0300068490040030b0101c910780320303210a6000102243e0507850854181903d27100b5011342149a42c0c112400c602c501072941100852130314149031900e400c881d40c040040c0024480c2c42140c540703103a221144400040119450100d480142401040b0940c00c04d076840d5a1140141d0105440d80205008071a041400080143e621075000c3c0035039040210503812544803030394012406d07000050780d40007082281030a5448440809440d00640705014100d040c0d8020841c401d10341c50303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 846693983 1250 846692733 846692741
    0x609021803070302090c0705010f11030a0b1210020c28021e0d0212031b0f070608011d0613020a0503060a080a0210110c04180b330a030203060a 63
    0x40302080661414011201015034030400b601002c0e51010008010484c41c2d5150002044400c0c031074400850902c0010740c2540440d0403403648041a400c00000304090941c01e4840d4481d002402c07198001411152412940c1c0c4207218060308044990004101443d440100b0844a9880d0030923695a4010354503201c149085581c3c89040340944134079040640e96481c541020400408003621040309229141c0800c42c00407101800c2102e9804108482140d00c0201c0540c0d521126007100100400c1080d030f61618a046465449002081036040040c0301d00f4200e00c1e500d061180741400070a044e915070000040044020440c006045031001a00d00740054004024520484040b00d015070119550040c0903114421000020b5000300d100e044c0ca0310701401a000302c17551002c0e0004949413400090301150480b040e1041c1007203401f031032902c141c0420075a05040eaa00403145030003602460b0300300f06440c0c20000003409044c0b080600032403180407500e0f0f5803141c0300190b400608a8034541030200d9944028 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 846695233 1250 846693983 846693997
    0x5010c030c05161511030f0f060607050a06150b0409060f1208070204111b01020d150f0b03040201020a170d0e03040506070639021c0807051c060902 65
    0x30904060340c0c4070585000b4015149005403a41100020800760340d07540348101c4103804a02201541d84a08185444000015600c03402100314012240e040080b01d10100c4c2a0050016125001c00c2004200003080401d0001c12a41e01c1500030600c8840c0c0d0b016000020016003120211080c00f00300090802490382005088600c00010100740c079403a010f041c107550b030080c240603180400400501c0c005003000c1d440005445440c51030f50341054002d00500010381c150170010702d01690049004641e681d21442008414040001305410052a10f0b04101000c18107100364100d9030400302c001400e5900034070252442e030b0340c1300400c003d214881c0c40720500e840d08580310800318185441c041c001070550000880b42651402400e07070303082c400c2c1a81d0340700280c1703110340c0031998540c2200004101c48141000400714010000d41d410301c100707a03c0400a1030000202d01020304080c905c10042582ca8022800e2030704141700746010341d65000d9a400341c7e01d000079840a120070652130843c0000740ca1815078003505003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 846696483 1250 846695233 846695237
    0x30a05030f06030c092701020a12110c150903090a030b04031e05030a1d060109051e04020a03060209010e09160908070e0601260a0f180f15090f05010c 66
    0x80b40c070b94406141d80d4030040c105294102042c000071500d8101d00b00c0304c00e45022003940d4031001c0301d00c00300c100b542640c00005565000c616203404518004510303000d03416103103444080701820174000a5106d40e4410b03003100092034508550011131405a014821039181d008050316114440d55280b41c00c6c2c9040408031801d90002d0f2104082031a0505040152284400103603590303425525002c1011000b001c2d4960940841c0140c41881f01468805000b00b600810014500160600d08400d460003c3d19030100203800c4008a40c041100685e281030310308064903040b000058958002c240103840600b10740c0c0e2440d0780420340504008940c01d0206100c2c01c1a40a0340d030740c6030400e5840007103555558040c0035a1240340c00e6400001c680d03501c03554592006a101010344424860b102801184c0040c040e103d80036407645070b5541e01d41201d0b042c029000d180c10740c0c40100c80d00b0065921510071085045200500804c407404032440030400540051000c1c507004080d200702d040c0302c0c0c07034080e00810b01e031120000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 846697733 1250 846696483 846696511
    0x2010924080915040b0609130f080904090f0b0a1a0108061003060f171e060a090c0f060c0605010e07091e0b0a0e0405011a040521030a0503 61
    0x941400c000c0c5a0500400300d1091988900641290560348000010168a41440342d00510441c603645101454002c07030083c00011a10304014091200800006005038061821001600d00082e002c0d810300d04420b421010a540b03d408480008001c1e02c60400f02420404400c0a03031814412207035102e60003100106000c100780a80c00148009219218810b9804182c290000508ca0f042030328504160600d240b50014a0300d8840080b50484155500422890010050750340d498110807c032074025070b070b0b0302c0540b000d01c0340d095840780c3ea5907900103000d904110345401f201c1041141d1b08080c003015000c03000300801c00c25146c12009140f690302003c241d6049080000000c0c032000380c03142031805480e484d501c8108a905140b00c00704022000c02c009221545000300000769510844003416401800d5500d514030b030741c0369a08000640d04181c0156110b014420b1850350014481300880382190300070b80f4050301201090800b010303117142c0808040c245020008084404075809030080d4800d40040300b81074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 846698983 1250 846697733 846697739
    0x60b0a18170c120a02030f0a030807090e0c090a0302060d14060d0c17160b030105091501020c040e0f0102120603120405030606010e0324011a07080405010305220f020109 74
    0x80400791146025501070b4211068100031410403002c0390281c81001000c90311401800e40c0031900c3c1c0b11403041f58540340e8109440080030941e100440c1608106946020910542012401290044007500783c004040000401c021652140307000c2100842c0c0041642e0380b070301c065420603805000043c0048545041c03140c000703441481c082c494205920781154000720160b06103501008900328a00d10044a4032800d1780c14203c4c4051020035402900a0100c43d540b030354913000a000c95450f003d41020460341d034042e0004a030766800200e000340804101d402080e03503d8880320300c508200e100740d25080294000500407d8520700010060b008550660864102400040c4d03c00514081c9009090741900040302048240d0b106464900389843c0040030703103244001c0390040366403805c403010000464445140041208920b408019070741483d04550f51460300300140c2c4c507007046110718043e0a041c9990b843c0840c01101c02c080149031550b00c05890054403008504059007022a00c00c030890000701d10100c08 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 846700233 1250 846698983 846698999
    0x90209120a08040506071a0103081b150f0a020d24051005030a23130210030b060d090507230a09060b0316140a2609060103120201060b0a18 61
    0x1580307150001c1d11182018145800c00c891680060740a452508010001d8841c0c050400c5605000703500c102481c9a07280c05403100105984460b808900b2113400841c00000c0580800240300d134000f03a1502d003010143e417405420070090007004c00c02003000c0e241c980400b081174101c105c4124500b450007608130341c00d551034003000035101c03030707544010002402840072a905800c2c0c1d130041c00002c2c40e03000c80f00903003000050203080c181d6011500c1541a91403402c6c104190b0901020440d280c0041e40307800d12040c034141d001300e0a188188142003d200d82c0d00d40044c003c1c0101840040c01400010440303181e6808000c000c000f814000a800c03070310480103100f00180c0315a46108000c2280c40702e6607840e040d80c1d24110410100d0b450781c120002880326810001205204180041c50910300d07588601481003805660b501401c6591f03206041a880040306010444200003280c0e41142c1d400300b103000d41486400c5040b4090030703069100507408540410b1624016411026050380320940c603406805996980e801 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 846701483 1250 846700233 846700243
    0x21150903170a020307090b0708070f0f02190605090603040f0203070b0a030509060f0123040c03020414151902070e01061d090103120c0303110d0618020f030610170109020912 76
    0x5e40703001c503005600400060070784401402030740307008118240c01c0100f56221000d806507181e800301c40c0b10404030600c1c8210f28000748441d100c8420382d0009140182400d00240a6100e0108040e124002c003000250403c11002e6008406507030141c1038541e026a100328424441d08440d00d0340011900304030004110b8403000817414402c0b090410f030303120642d1810b08120020962402030b040346c1250752402284d29140c80c00303008980c0c90713103583c0141c1c0d0310314025050000c2c250a000407803007610300b0980550307141c2202054480791907821201e500c0c11b0640300400d905d400d619911256100007400b00000303a04d40c0062100201c0d610307108a40c0310f034000000810818110900005001140b031200d42500f4500c5900402e4085109040c000f03140200c49a100c50359412030b100c60070740f040e180c000a12400d200c9c01181e4000142224007581405622240411640402028603018220409145207010b01c14110303890002c0c030345038410005584880e6548081c0d401560213034050504444c41c03290200e00050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 846702733 1250 846701483 846701491
    0xf080a022d0d0c150c0807030c0206040b0601081905010612050a330b040f050f010c1a060d0204090b090c01020d09140a0503030c0109021921150903170a0203 69
    0x90310404000c40015100c0c40101d20080d600c2d04c09140341c0340d031200c11a01c40e680d00c500c1d6549071003c02d484c10140040507104044064400c540204092000054110f241c40307400ca4024240000700343d882e185180004a590112400003a0070580000382050f080313005c030ba0584603200401d01490795055402c0080d0381d442d002080309038034000c0031882400a13003040000310084150503486a00e80c0d840520745150060340010285c0000414100320a203092001d11031840003c2c00c041c1c42d40b00e0300340ca401e000c0844042800000c03510a40000300c0c00da8960034802d0440340e00600810220040b801c0100071218101e40f81096072081c112003407125800041c2c0000c11201d00e03903601c0d150500304984030110007941f80d52550080920078011441d43d4003400641018580350000040c0d03c0002d0040215120f2400700c800103035030045d0001d110741d6403480d0005078580400805c10894003042d2505156908040314107074451071424025404043e449070540d80221001910300c42d440d15000f00c036400b280300c261 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 846703983 1250 846702733 846702823
    0xc0a2a080319021009110a0e06010503011514040b07020a090b0d0204180c12110402032203120e0705240723060f07110106080d0c0f080a02 61
    0x1100c11105031540201c100c24030070302c502c10340b00ca03500c142a461042e11007083c4112040d904a5080340c94604054038500010160308004903041e060090000e4407500c018010103408400c1a481090a00e000303007001107903100c5c20650683d460380c0c3c0700140085038102e49000c9214201c4200000f65103d07690240006401009203580001d00c099406c200040004100c204000350103100d82a01080c1030300d403020024103210342e001c10801140d282000c0700285400c810780c0714500c14000d001100360800c1e10040c0d07000c0c41c0d40141b002c6081c6400d00703981818003800301090450804000390712080001c00d030201101c00a44141605035203103140c48452002e0170a040003103000a00811010410162440e2985458100c06c0303040180743c49402c1e4140002150004850019081030114455000d4201c00d204040c0900030040a801c0011440e181c8209140820402c151000030000f4400301c04810021241c0c0b12445550300e11800c0381c040e40b40d244002034003500081b1440390b024901585680e4806403a124 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 846705233 1250 846703983 846703987
    0x3091204181a032d1b012604020d0302031603030c1218060213080d0f140903070614040513051501170a110d140103020a060306060813080c0a2a0803 65
    0x5131511200c2001c28a41800c4c8414003518005281502442180d015001281c2c00b040394020a50000d0010b0740c01019844220410414006510500340c1c803468005904507010b81811080d418100c1c5940a0500300400345c0400d18840020982c2542c4208a2a09140c9070300c800c602d91854404111580506141c4003051a425008009807140c0d00400014040d50301d250065900c90605500c0d00d442d54000c000455030f4000700e00348094000d0b0f11142c02c03580c030303001c03481c541440390021a807140320510506c0d09114600c1465020f44120b242914080c0c00041c1c940c05950043d008500d01030701c0d064800e103210040004200700c1d103500c682e4200c0e018421040800000ea00c8680744800217000c0c0c0402ca0034090010300c86a0403464150080200110701c2d5061800c0d42c1d419401007002c0d10780380354005400d040c070b0400700700100f68001501039030180000e95040c1502d003150400340c495100b407168040c01801010065406c2003000c0b1051110b042400c280e468065000502c485407040c131a0044000c06d600c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 846706483 1250 846705233 846705253
    0x2010606021f02120a05040b0c040302060a1d12060a0e0c0d0f030c0807060c110303060a030308060a0e0708070f020d080609070e03030a030c171b03091204181a03 71
    0x30b4042c412044400e01d0401440e0401009001d402090151608040144c592081c0010b114004d040c0301c0d0003016007890546007500c4c42d400a110b5210300c400c14010700800124501c02d05c6c0c200001c400c0680d001408070002c214a04203107503260f01d01144d2012400c1c2c60300d081501e584078001040c5114620103080650b00d0505a01c41c20a100803041c0c3c2101040a41140c8100162000028100c8607100790408581c42c007100c00050020400024038000940c02441000030513a180c150102c02c40743c141c20085415111800800d520180c00d0f044100c0703104107681488216030f804909944100c0c1030365038450300c1e07400c944012070320381e0880d004107070000d440c3c1c01c0410000d21340141551381250044c20007021621201c000300303003182c00071002040401e5844c0c4511000035008100c0e5441e002c4001500d038a9491715100e1a000c1c0061210408140070000c40080e5048100300560000c8658040c2e105465658580e4941400a0055480720415040030006a501c020f883c009003c9064000c01619080c80c1c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 846707733 1250 846706483 846706513
    0xa020109031b0b0403080c150402011b060b03240c0408030403030e030c03010c03051501090803120705070803010f0f0501031b26150103060e0403080a020702010e190e01060201060602 80
    0x1400b4154018254550880080c8401d01c880061000714454114103868040a44200f818084c005182c841416112801c0000603030380b05580c0d64020f03010724041c081485007800e140004010540c4095018866480d4400f8814007542041c00540d5042c2040445135a50b00380b1090356000742c0c8a01e103a150f105102c148000f0b0b00400e6002c84041c8003408a904a28025001a0070b49a01240e00400b20b5941c40c140080e0041d151641c00041c0009e08029042078a4100310550741c0c8208040301c0400b9240320081503001d07121b01d048660168000780301c2034480d42c448818101d00c6242d8800d580c000c1c401c00900280d994000e010300c14a41c10840b030b40b5500c00003a690f00f0b403149148600300c69690b00142c0542c04e18014845101e80c003c0c4042d2030360310030182b50744002404454107900140100c500c52030411001952060030303d648009900005030b00c2e508144016190f003880d40003980e07405505090906051503490034004101e911a0781c0c40c5015990f45c03c4d0980c00c0346d040d07000d8a001600000359180c1c40350 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 846708983 1250 846707733 846707753
    0x301150903050a08030a0e0613121803120e06031f09090f060b0f0307030309080c1804060209010e040906140c0306031e1e0304061d0105031807170a050f0a02010903 72
    0x1e010006c041040c045521b030795814440304444c40090020500d0824081c06080f00041a060000d800d014000c0f8000c0b03020751115103c54032001704520041540a80154411003030440e0f50380000c1c244580360304200c0c18031f01200c0c035406180d0368200041d84001480450f43d0150300759080e0801c0302e005040040b038640780043d11100c45000d07000310080d022509651410080c1c9030003980250f41d2450514101503006041281c0040320701e02c1800180b040c0314006242201d0b80b03411560000340142d40f1882c080041c1c0301c40451360b0b4407c1d40f1618081c894004e000c041c0d0081200421003010008069a4004042c00320340001c0d2031050b00b59200400014500000c20a280012003041e8203c80c0c480c4400503640d0108403114030b84600c82d80021600300700c0c26030081c04200081880c0100030ad00442d0b140002005404024211884019190000d12140c00d0507c0410040d00e03c1d0120200340400000203944e07510010b10040b5820f03c140d0070302e2000303040c0118606422942c142d4803c181c0c01d2950711585581 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 846710233 1250 846708983 846708991
    0xe15090106121e020306090c0913050717070b040b072f0d03030e060a15060914010804111009050f0927031b0c12010c120f150b0301150903050a0803 65
    0x2d01d1107040c143d00581d4040103000e00c6400350030000d1035003d450f0030a1040d080301c007604411100c82c42c044a0340000c0c5000c1022801e485115030b484180200403560145001661b60110b10040b4001501007031000c280f10003486242c2c0600c9004012001d4003203002d441c1d0034940c10400c2c20002c40a020011490310001441307590780603182c0420a501c0341c0b508281041000e0ba40704583e641e80b1040c8215a49440302c8080003400c0600303040444034500211122081c01442d2207904100c031404c0060100b2104244400c0b001801801c4440c10001a0310702900000316130103414070442d8440d44404151405940040c850030140f1903004c104081d11080420052940c9005155400240000a4044091101c4545420094000703242d4500d1400a205910a81084408c42a41010000505150000742207d80400c043c07a00140c0224441d6049000384a07a03c1807410700d0b1003021380056000c003a0405035050700d1280400348183c02c0c64000a8622400c0e0348002403003900a8030400f008071760700801460340 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 846711483 1250 846710233 846710273
    0xf150307050f0a17161d0a180503071a1b09060a0c05150619050d1112070e1501030501030f080304020609040203160e10051204080d0e1509010612 64
    0x10058913a6003028809141008007803080d400038028500c0042080310800052a04003101c206109072908200c0443c10020322102036207403180341000580014520030b4100c280c2100540e91507040034030b007544010381c002502100440512011071810300300380c0c42c01007540c42c0c9041010302c1c140e680740c140010390700494442c07400c0c00402400403020031010b01184420052442c010982840c0c034200f0407100382500781340c43c030b0980101c102c140025102c040c4880201c541080c07103591207090b0b000000e820350000901b400c056018903000003035488002510a07000701150000c0c0c40c0480e03d81c0004500322107092001404150351401c1190103d245c8000070342e0001e001410300c034501000d10001c0f81c00e070fa00c1940d200203611281403010040310350040300403008100489041e0601945408010b00ca401070b07010707510b40c0c10035000103d0200721504003242c0c9404108001407005c045020016600c8840170b072030001d45401c51900044022708180b2401c000d5440d5002c801c10482e00c5529a03011040c404920464 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 846712733 1250 846711483 846711499
    0x140303071704060206010b0310030f02041b020c0a1d060108150402191107030803011809050f0304052707051605060a0509010f110d020c240f150307050f 67
    0x301207480049148000071014030115640d5160503402454400705a10154194205100780290382c10520f65100859400c42196030303900c446030001800601441c1c0e90b00102e45500703141c40000b00d030003144181c0302c81403c440c0000c0030350b9103883c0103055000044a220071080050700181841d8011503c1a82240380900914990381598011504991005650b03442d0f140d5851110031245038000e4118816009420140c0f40c014a141e80d24241f900042c000c01c1c0300f0303060348616507044440640c4a0005160030004071001d03544840c40b5980c80b940a8021a0b0140d560340058000c0c001e9601b0f06a089406061030310403043c1e0354080d0444040c0c000520095100c1d000380c603188080341c4100b01172400358003650000181c5081c100144e03421180c40703044043d503550030030a12842140f000020ba52a05041c00c9003d603880208200c1c180c2001005210340f1303080b030f000d8084a0402c10307000c01e020b8450740c00046400c00a840c2c3c0c4032003215094000004613419841450148032a007401c4102180c210b0300502704130 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 846713983 1250 846712733 846712747
    0x13060c030210050408030a0501150804080d0f02030a06050f0a23011101140108010c0306030f0f0c0806040b040209071103030a0903021f0f1103010f03060218100305091c020304140303 80
    0x70b040d0303101541c055402c0103006c000d2003039440c2c0c548600c50042c1040041e08008150950b0040d11200c0d0046c0098040b00307000c81c400c03403140c0d03064001f51651032003c042190b6a1400c040da11001700402d0046034000e0200b5030042c20641040c038500403d446910b07178200300c9400c000403c01c442170000c11903203042041d15402040e100781d0074001d0b03900f801d40d92220710241e581030049040c2101e1110070b0702e204141c02c1600c10070100d45101c03440900d841d0000c02181004c0a54241510145056800340b40c4038820041008148400e580541c0d0085101701d58000e01070716241e00484817001c075803104a035140c1003000400c01d01ba080e5440111801d1003801643d01d210307406100d07040b031207901c0c01c05125101e4a0328190780703141c5124411a40300900101b035050541d41000702d00941e00c40140402003d182c2d000480c0c1c5440d6507501c0100c81d01000083c88100c012005450040261100f40c2e40b040700d910032641c805000c45a040303408030103130105500a6090902c1d0081000380000d00e5081c10790107000030408a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 846715233 1250 846713983 846714013
    0x9050102070206040806060108060303041503050a0204031e03080604050c0a0804030e1002151006020606060f040f03061b020106030308070f14030903030f131a1e09060105010f0513060c0302 83
    0x540018910f08020701510300d02907001421181002b4441c07071091700704000522180040811720380b14903809140001da40d540e8200200e00030310550704041c00c2c501801c0340d41d0405207051850881182e12a0b6900c03c2c194840c00203010540f0025581910800018071a45a4540c42206030a80c098040c0c0740403500b80c0c8187c004101c0e048210012200182c020100013121010907038007451308401070b1440d03200385a180003030081d21210040e0415108000001c0c01c8510440a02c0c10f45000e0201c5442240026560b49024070090081c0c1c107404014045012100d15900d0041c41703160200d03601074541c100141d607002d004031003403206a14110180055031201c2c0800302402c0d40550b1044400e0b900844d50b07070038001c07000801000300403c902e59070224503d03d0800281030902190720500760080350b0340181ca5941c501d00c03130141c1041e244540b40c0301100030080c8508002032480c4c125202038131000100408004115002d00c604480307803840e11f051070410890301e4442c10070070442e07501a10585070b80e515180d00c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 846716483 1250 846715233 846715237
    0x23307090815090d0c0f0506070306331202043203071401200f010902092d090307081908010506032707051002071802070b0a09050102070206 62
    0x1000000503605001400119001c00c200e040b6500c02c0c540315681032400c010390a95401e0006408401c100710815075500700520f000d41b80044a911009880503450b0608004000300711511a6100443c601c3c0d802d03625184814000604880f000041d1515101d4551000c1c0d48802000e01d162050310b900b0030001801d125540780c10411b035500c80720070051618841c050301070f210107901c1c1030034800e070450030b0100441e080d05a0251030740e00d030a0070840010300e2410211481c003d0990b554040600815076070600104040d0320641040f8422a1160016100c901c84030000c0007403907030300344615402e00240410083e03c818406511003158001c5a00d018080d0b43c9850458000361040c81c0000304500c03031b10945640020f05203001d40029174016007140f90444a0880c2c44030012011b0000c9450342241c06e031008418030828010f003030b010b0000d072000c05001c000256202028800d40c1740b100c0c48038006030035140c0e250089900b100d80000d0700b201140c40c0c1403840b40c004c0c0b1740385c4021541503600304a400016118040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 846717733 1250 846716483 846716491
    0x90d15060f0f05090f011223060907060806030a02040e16030803044209080f0c01050a0c0225090914060f0f070e0d0b0a0b01090b09010233 61
    0x50a226454a0010070306a840020f400c00e6115111038400c1041d80001c000c0d9140c11144240d1240c43d10369054201003088031580d481c40c01444828003c824034812000070618002d5003e0400ca4007503950362603080f621400e0550390943d040d00031110410252615800019890700c6440c2942c080303c04045a034407000c10681c2c03080f1f070300c1c4038080704010078008055006400b00c1d40c2c01e01541c2980010312505108500360040d00d0212100862401c45404c0007988650929a44034060b260388030996620103016803c0200441c0d0150b00b00710002d80d80520398001c840401c01c40340c0041102060314009440140c20b0701035004080d420058000610101701d018403501c10307001d0a0a0031340c0400d1031074001c0c14400c0080414641079640400d0162915500259940c0303c4a81d207070640040d1410710010f103900ba580c0704090017000007542231040c0064aa400076a0300d000036250400e040703030b541c81e00c10300c2c1e400f88904242c096003052425800e1040209032101280c420300d1010600340c05039100d50030840d42c1c251 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 846718983 1250 846717733 846717749
    0xf260106030507020f0a020a05040e030904060902130603060302060a081906060509460911030a06050909030f03060f0d14120405030303040f0227040317010b090d1506 73
    0x5001e101c3c01d00d8041c42584404107105020700f0f014203040d00861410345092007081e0241d541c03807080000c805414005d5900c0410020b10902c0881d40d05c00000020750001441e90b0214090b00c100040c0080c00780c0b0401080300e81c041e0a4606014005c00300340d9034000c0c003d209100c0c514010700b040100d02c0c103030b04c10070303020f05140d807286502c82c00c42600348801055495040a0b40846602100440d01c1205080c0c100f1015201e034041c46d0710a040c224201070381074503030024021601b456007081c150030720500550b20031135843c03034100300d100d5483c030070030a040c0c1003a40c44900c641c2042000c80c1c800700c01800256801280580780c4400d03900e0f1078000c40c2d0842804c00b0141e8807c1516500001750100c240100302c004406002101c0c00c041c240703030000740c49110181008001c291003580d90000c540b02c4103502d8408950101c075641c00082a480c5054410070300f1a82140080d4144651181a000384481070703040ea8601c3c5900ca04011411044c0660300d0a420001d84603801d0800c40050034000f079005000280500d6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 846720233 1250 846718983 846718991
    0x150c120207080d030b130c0504050d0f061109060f2101120308060a0518063f030a0c1e02040f0c020f0a0305090108040807020a0b071407060f26010603 66
    0x11020036410010f40e96003000401d4146039520100c0e581e000c254504080e800c0c50001520700c040c58042e2454883c0c0c0d80810b0300070303d41391291818044111415800705001f410103104843d04141c0d54040e038401c00215a503c0078041c400800d04020400207440d00207e25559884006995200070b180750500340c0c003502e01015588500d004040d48600d003a03070040000d48514a0392400d00c2c000511200340c2c9218002c4c111000d00000f111941c4c0c05c00b068410914180b44000c68045800c1c4110818044c0001c0100c04445031000304e2951200004603800030316030782e50300f003400419a5544244200300244481070008080e202c0d00260f5240d01c202c0c018003075601400110b80e094aa0082e040081d200c2608620303400074086900441c0e0440d00300c0c0c00103002441c100505569a18008040d401080380180d0808a40c0382d010861014400041403124004c003102e42c05c010641d070040355204e509002c0e0200140b01da1001c002c0d014042d4500c00700c500c546c0c401d0100c843c03810008001c0c150100342c3c03140c00000d440b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 846721483 1250 846720233 846720239
    0x6030a0b0f0409050304090c2021090f040c051b0f0c0109120b07020a0602040e0f0a090f0303020a11160f12030e0d080c060f010906120c150c120207 65
    0x1c14040811030a005950034001d06050752038042e146c0c095489034408171510f4030030030741d40c2c0c80c440c0c2c000450b58220030500c3e5440080e40d08120f50b42c4c50400584d1640c0380c0b807900501c0030122600c4140c400f62940100700101c0c45003004144006040c19014050610400b84690302d800b8903032088110711396080000400e6002c0b8103011091034403040180e1941440304a01c02170005a90141941c00c00b140c000c0707010710301c540324201c0892420a0451018107100d20108000c40e1202051584078003d0f04403c0d4049119102c0c20241c008450380b04c20010410a00405d00c2c1000034000e40181124a00e14204410004000302c01d440c1042036046400b05141f80d0700c4401d0052103040c11000e03014007802d100c1c0d94140d440598000c2c010001080701d1521035528114010100075104046403001490b1a05480e000e00308090f0301d01c110013080c020344c5480340c01c1140104007245026140080541c008020186041c0740540d07443c07c01141400c0041088010104140400c0f094004051070080646c000c0c0340d074030b103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 846722733 1250 846721483 846721489
    0x448151106070f020307121701080303041203020a0c0b06030c0d0503040905090f031b030f0c06090609120a050d090210170c030105010c150e060108010f1506090605070606030206030a0b 81
    0xc4020440c00034480f00d1040002c12a50010644180c00e81c80b8501c0034010159000c19a209684400b017a000804840008039682c0e0f40807003d1409184104155115680c4582003034043e80148075942000408205c9990042210369078540d81003070340501551503001c8084041403015030b48000503101c0340d00000d000c0186040b14030925912060260261400c6034100d0310300c98692003010442c101c040300342180211030200910454040e070a010441c42c0d528a04d2220442d01c4003811035940e141030080500151a520011030042ca0001c0e0790441103145c1000d8080540d0282c012044054191347e0358410304006845040860162402c2500e40701c5440f80592035070720301c03544020010960000144010095039030031440000d581d9900540d142441401c4000c510f00504203511080e00b14400c0c039000180048040d809603003040d414030700c00e1000034680d8280d128a800140700c2c0000091910100b041901d200d5400385c02c0c1c0300d1180c0c4000c640d55075a80c0001d5a01d401c00c0e568140240d541d16201e0a85103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 846723983 1250 846722733 846722743
    0x609070336150902061902030d0903030c030b191701021317060c0910080a090213150e0408160302030f070302151501081801091a04481511 61
    0x44002c400340302d05495035011803071500400000b009407130341020030150954000d205a54121000e4902044001c1c26400c00801406610910b60b000c01c1c80c048100d981030a0406802203c00380343c2c001400668a840e0440591000c10a00e628140d507091042c504e02c500e200e0b900d1001004440b90750075420703003a030700300604042000c3c00d490740b80d14040100c1c0703103142c860314100702942800d800d14150503a5800d00f101e0242030200002980584172032a8800c96840301c0c0d1101c50601c544030001590b15481d000c0c0400190025600a8010f030018400700b5034901d55800114115071203441501e0138007400c544c00c1d039859040080100c015030426580845100094120075920072164402124540c2d05ea90020b4490300c070182081c110114180c030240d003104030941100c14820b9004270340c810041b40240640446007000d56080fa01c0710440c1008024000001a00500340d0b61600940d0045000903091180b0600c0050358070f41c0000054180000e0003002c441d00c0707032410102911015074800351040803d00b81 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 846725233 1250 846723983 846724013
    0x806011818050907080a11040902210706020a150507051201060f030b0619030510050a0602100e0102041a130e0c03040201170c0a0c0f050303180d080609070336 70
    0x6a803280b0402c00c62450000703250301e010360308080a5030260447c0000f00b4054240c8050181d0001c1d900b200703089503210086c603100c1e21710419030140c506058440000300d0312034401e0b2002500210000001500303a8041d5803007550440030b00e08000e03180100c010307002c0034401801d07401000401c01d170000310150507425002e140543c1000301c0d180c51501c0d140520042075454500003542c1050380e40e1000452040d18034030481c1c06404020305200c1415a22030000b5540e051504848503c82d05229020000b82c00500994060710380300c4440901040381c00e8185582504020004085e030308142e040011504c20f9002001d0050f001150940c2d0b491620380005030a01a40b06100d040c0006d0220801488a4075a0140c0e410700c00c55150441000000e41001d0502c0e403e203c401400c180400014400400410500b188220940c1d50a4a00d00c40030014180c940d80c900b182c10702d030000000c0000440320b501c40e611074007030085191590200c00c0c0d8048000030101c2401112018500c113100d043c6c10034414003010b82d40e00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 846726483 1250 846725233 846725251
    0x60c090603050c120103030f022d191208130c0306090209090f06130c0902030903070b090c10110a060c080717060604060302090a0b0f07020406050105070f0201080601181805 76
    0x513100020244a891400511001d010045495400c0054501c2480b1341e01074604800442c4841444203150300a040305d005902d40118400c00c002e0011400c040810505d1954200c40c410400300c814010650b015140100340e0742d8021492400503000a14184010b8003650185400140701603c80c8140510b40f00098880e200a501000d020300e080b403000641264800e503c02c44801c1d21a00510301450020034681102c42228008410441000c1000001d0079105020318840141506c900b40030545609202a81c9600002c4200480e0f80550203080904580d00e040021921a02156241c901c1111601803429000a10402c1449034856100000d81440e5100230558103103070070710500290003031003648203039000c0c15000310701d00c8081d40c0d82c814980028035100700696a901810144400290700003c030407841903160910101d5154442d81c15142c50a5000184042c1c00c04240c0040d0780284008050f281000349115140100c1048455110020a6206641030b440340c003019101c410b8031002014044 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 846727733 1250 846726483 846726487
    0xe160b1206063103080d140105180a110405030109060603060c030e0a0b040f0803010e0106170405060f092404050105280c0315180b01020c210a060c090603050c 70
    0x801d95248072240c3e0250280880007440c1c889141000040b10840c0e9413016082400208a480d004416900210366009401986480070384c0ca0f5010409001c0e00c1350079803510840007900283e07000741141c0c4040e4002d80744025050800d69174500080c00e58a08500481e50b041d02d5100c01c008000c1d890048048001040c01c3c14040c6100301500743e6554030904070050031580300040842d0500032640c0c06d003691141c100100301e0341d968407500741c480c0c00031081c410807002955000900c0c844404907440c03180507e9214010305401d4a82a900380e0100c00701800c154440d019400c01c011440c8100b1100d01c101d8842c50581c0100c80c642414901d00f1580b005250740000d20100b030500395181c1744a404100360420345003000603245412441240204090030948207040400080810800140c00c03140b084108441014800f0482c608012600c90b51b4114285800000480b03291468042c40c1c20550301c05401241120f003034000b9519040d00351015003074468081056550b081c44240c0d03141c0106944410292038140c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 846728983 1250 846727733 846727747
    0x1e0a0c030b060703020f100b10080627090f0303070504140121090204050919080d02040503010c0e030f0f03090d0f082115030309060d0b09040b0a061a0d0e160b120606 73
    0x1808109d104401204010b8450009080c943d245a40c151007854a41032010819a00d0507810640500503600781da050b1050f8904054102e0001040324881d9145580d010704051401c0c802c04820880590b80a0502c205130902440f8000181d0074480f0300202c1d09004075804007a0f006010841d040500507040580080c40b01080f00000108a00c5145a1240c80d03140c2e5010300c0c4008500901131074201c2c1d685035090410072020540e010b420011a100100c0a58085006100c4600e030f4804041c0c03a211304540040c000040f5078a0a14406d040031401101e840003140c0196481050540c0026100d809204204140c40c10b40da4000701c212b0761007841f0380c018107558610880040c0c0d0f28090175001d148948400502003c0007441600614006940a001c441490a06203071182211600710754034800342d45099000034603603411254002c1d13140f103102d5642d8940409021800702a11500e1086441c9100c0d03141c440c00d035888008000310040000020306078a41154404400c1003c0001e41100d01c554014400a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 846730233 1250 846728983 846728989
    0x6120c19180302220911011d0f1003090c1203090f0e040206072d05010b3001110c071505120a0e100905030306091e0a0c030b060703020f100b 62
    0x2081c181ca8040701e0304044180760388111500084814104412141040329102c2084208002818400c409803540303141c4250a0f401c411420280c101503503442452a1220341150505000500f00d0768410729000c50342d040e154a5408018a1541c403682040107586101b205140e44a202c210107000d000102d0311035245001e1012601d08800340020b40f04050010341c442c1003050342c1c222119080d90803d049441008250200383c1e110101c00d81c191340d59400c001c50508a0b203400140300314001e40200c1641081d84241d401030040701c07006103480c006590ba071040340070000f0550018011402c6400000c1600500300920b90b5000b242c1c3d00010810f0100501c00f100e070040e0002c1030954880526100040d41e41d10780704007185001103403280024a01c4c40d12803000c0500c50013000a511500040c0d645800503220700c05280980ea9505a4044100d40c80c02c000c1082e1a04030342100c0c1d201c46240ca000300c0c290880000065040c1c0c00380c04100c0141c1e100290a01507a00c040c003035824110000e0301c08111100b06003000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 846731483 1250 846730233 846730277
    0x3030203031b04090f1a030102031e0a020915070c080c0d1e0b1003050601050f0d0b1816030b060f01021002070204140a060501021015120206120c19 65
    0x100d030490b80b00c2075540040048102c02a40c0080c280b01c40300f4407031003040b82c00c0c1d00b000b4100c00707407565103034101012454110305050088a0045e00c82c4e2000444851801c3c01da800c040e6409003080c41307103a408000d07002042daa40807108054032841a1029a40c0d03030f0740e18154000105951009000740c201d40150010b5035510640e044c0c0443c2c00134991207007031043c155aa200c240301c201c00280041e074400c4c1440745001942003150192441202201d88507600e0b80e040090b204d044400f110b17030042c00f1078601c00001c0c0e044880b1036001450f0301188190210b00611141c05e10003140700e0f4401c441c0c0c40f80001c0043c44003000720b01d03401907800c4d950000c0c80540100002c1d2159480c010403d1050b0b0005480030071515950301a40450201d690820b00600b0300040340c2019021600c2118014418602e40140c000c20314030403881d0320300c501d030f2090070824540856080c1c508003102c0300707990103041441042d4070301c2044039280f442030802819030f41da1303940025543c07106880c080000c2000c00a140702c0560280600c030700 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 846732733 1250 846731483 846731491
    0x70b0f18060c03040323030603071403030a141308010516030903080403081005150c06090303010e130602040e04230d090e0c090d11010306050411030402041e0612110108010303020303 80
    0x2401603500d603605e040981d0380a003003000201c824014000c091124200483c0518015207044040d40c0d44541d82d5030380c2c0198030442c1c58074541c1c15041044075051444c0031740f110042c0401c148214504201161002c0b001c01c1c480343e40601e40f541d44940422090014048074002c140e06c5906003004042c0c0980c40040012100400060078000c011001c1820040c00c1d06240005010050400d02e50703404180c5505450b401c1007108174460301c24000411040b481c0442940c0c16035070303140e4101015030350b01e8003689110b00b001e550581d2013690812000c60600c0700c0500f07091090b0b000310040000c800920506040c644c4151284038100c0d04005420000c0c0c2d940904400700b19500c1c45000c415989403203400100d184a4051081d034030002030f4082504000c05810005d0341500c00762002c00007107680c2e0085c00b00303940c00792620070403c00e4200002001441c0c1540000080800780112003020540d0816450448045821070300c803d8078a4090340007000b044136008074111000380f810f40e4081d41346580295981c0000f0f0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 846733983 1250 846732733 846732751
    0x6061404092a0503012a05030609070e1c030e030f010513020409050c030f0a0308100f0b0705070f180f140105150f07060f0f0905070612060308070b0f1806 68
    0x1032140c142d02d0010075040c000e400000e00810409240058505451103040030442485402c101c1d0b21510900400660f48140300107820401107a440c14811602a92602070450740301c12174448510503203103000080501207101340c580c0d91400e4111700400d4a1300141d1002113641d40e04040402034040e10740e08861a5083c0c1c160b03002701c2c100e0090b203850742c02d0007606110b45070148502506411201800603040d80d203a0b0003520b0b042002d88a1042c000c40840c0c6030702505680200c03d6608105900d1030030300600000307000c0c0094a0702e0716100c0d035072052030342d0a543c840e20390307074000e01404042c521052207100f03132440f54401e041044080001188620401c1445000d2080581d005d0b08030381925040206ca0348540040c002e6940d0321444d1800400518030150b480308603a2a06c80043c1a2100754401e6600c3c0c1500880240107091814008440d141d10f503864a082c5142c03035481c00000030701204090a5102d00c221a45000e03407619134500715060740014a44045000d5000c3c1d28640040701141035a00030b1504 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 846735233 1250 846733983 846734033
    0x141306061b020f060313020a0906260c03060a020d1a0a090b030f0327030606130e01110c0a0506070912030e010e060d09020f012c0f060301030606140409 67
    0x70b00001d0034070341011190343d030050f000004209049001b4880039104038400c9401c10307010350b12441c0c0c5030126001401114203011001c1590b62000c0200703100e001d080da240e0800c5803400c800a82c0445c2c01c20340190b40c40740c005500440d8010340400e0502449040c484404442081094803c2c00240441d19070311512800380e41d28410182591400d001725403000b80148110399903a0110ba260222500b080c0d51200c09000000341c4503d947e190100315103004400c002c0c11007403080035072a420300081c048149000d50302e650300c4007515502c0c503103000075220b0152418042c10b919587e2b82031960501100804440804c54070000c10f002c0c40020241c658031543d0185000120701034410f0043c2c582c1c4070a10380c2c49a2112010a400c01003008580005005a1003a2108522140d0700720040d12605038951a0203680c004948000c5240c5180700007006101c440104a40011081c40c8041141070b80203070010348402c0d03110a014485403141c002e440b10f09038015078007049000540c1d02d612401c030a5030700f0082c19410315 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 846736483 1250 846735233 846735287
    0xc090d080901170103300203070b070e0310021e070f030e03010b06030f0a06061d1210050123031b190f0b04050f03010203070f080405150114130606 65
    0x1080803d00d01010501600350080e585070304000da5030085542c10440c5400d5120782051800359000c40307001403420b080d0015818001e040d51900c2c0d0761720008000001b00040d01b03082d0412507904001002c50840d401500603541c0c8100b015006800c440d440700301c81c0958082140c040000c50500c03221014a404d40740c03421107031072103400190143c1100e81850307520a4020060104281c210400c0501030100308a00300081c0307030f880d501921900410888200301440c541e03542ca880303091044440c80b01a8109065400c200650f11011088a0003a001111040d80c020700c120b05101c842c268510520300118010140d00a04480e00c0c00f1075003500050900031002c2c001e607059200304064416001c0c04a2441c01145980c0320440588650410b11842c0c0c45030351030380e0120405003018030803070b8011015642c1d5202d5181d0325043c240c0d400710001c1c1c0201e8180c0b003101c40030b1451440d02e4070003601a112007044981100c2c3d1280421204a91880c1005801490320104120040c1c00044c20803292107030802007018000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 846737733 1250 846736483 846736487
    0x50702210607030204050102160f090213091401050307270b13110d1103040803180307060c0207060905030d0e01081812030109050c0a0c081c140f0c090d080901 70
    0xc4540c030110051260030180030009800d0b8010308107884080e801c4808508008065a03400790480c07050800251441c1001c1c042c2560341d400500d80b81e40740d0400c00000c01e65650385a01214a60f006002248580c80018401c514041c13106000400386e401c45107841c0201c51010041505160700e05140d21984d07a04040042e88640301d03004008201680e04114042020a091810341d1082000c2c69007c0d01d0f0040c1c00032400c2210080d07a00403a0400c05103402c60391002590710308414250030401c0c10344414060000003800c5800f68103124500c0e030303001d01042440e22034040d04003213086c2c00681c4a90072200000042c4d40d40141c503000c44000910300183d40792034800c1048603181c900d000200076402400c851900007102c0c2d800440c12525201000c200c07030343e200e01404040740140c400040018031007650800204488401516523440440380c0300c850040c001c210034013226400f4011a4124029800700441040c1000c015540040c0c0342c0405842d0601c0e090000d030007440b030003c004080b82000301e90220964 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 846738983 1250 846737733 846737779
    0x11010807090305030703020d030509010612080703050403020a090b01030605090c072a0f0f050114030708190e011d19031809050907080c011704030c0204151206061401050702 76
    0x40e00f060590707664280c41e0900948551900c09010302180c1090045540c4880500c901002c9540e505424020181e03580e540165035808100c0035010802c0c00d00010015980780c070741400081c41c0c1901c0008020f0703012000136050310a140d020324400d0504408008208070f09008450f4107580c03050ba0000103440c2e40e19018960086942c40000071000c0c1440401d03003c050902c1c2900341c1d4060000b1b482c440d0b07960300046030050140030400204003014400300e0403a80c040c291180e0400c00405004500311810348000003120400803c241003691148000d0318201c3d00f50042800ca030201401600c900816038007209000064003c0040810261b00180d01d881960b00450801900d0a0b4505106074217102040a54420070b43c044c00103540030f203500d400e5440d8051810000c0580220044035019a9141c80030b6408904c651006e907049a101c12007071411100819004010302050a124490f041c1a4101315046540c150441141c444e000c86003000c3c907030380080a845600364101d81c000040035441720012081 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 846740233 1250 846738983 846738989
    0x170105090604270b1005010f080901091502030609060a05090601051b0a03030b031002181210060b041a131202030a050601030f120503060d060c4104031101080709 71
    0x200e820310008190501c0d03100c0e64510340c80c080c022011385074640c0300c1c0d50300c820b590601c54680400d419a820041c16400f4064203a03011100400000b00b4501d1900c03000f030300d0b40250744c5032126264004200000c914240078000e811200a40b0050701d0305041001041c80c00c580540400c3c1401001300300988041902c40d010f0315600810700544041009501c1c0140c094001d4081c0715100b801110760000b0001c92034801e4910351035002c1005036201d5044414050f402003003040d00300c058044c0c0100108406954000d6000030541e4ae1500d80e0380740e14240c540f03007268003401c6142194210400c284540a03a45102410079505010305e09819001e480c4000b83c600000030200030100c0c01448000001e2103c1c41154100391030040f10503842101800c0411100c61100302d82030341c0d2040c6646100d101188032a07106180c41c000a042c225004aa2140c100d51940713544614003480705419011601d104040880392640d031144800218102829503a4455507024170780700e49410000320710001184548504258801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 846741483 1250 846740233 846740261
    0xc2112020315060c060402013b18101a0403023015010503060618040f0602270f04051e06150d02031e070c030c0503040905010807060f170105090604 65
    0x6203104ca4040f0540705c0808640503400706070f24080c1c91813036071000303040300488400f01e00034004222100c003038010403000035410280d048001c0d081c6a1202d00d0001001034051781c040c01d408410344e0b18151840aa00114042c0c100015005110420041c1c45891200c80c000360300007468404502071031184a140b505945400d0524840d2140303052030343c0da10306485030682d41e007a03041d500c081d41c0d0340080c410324503c02c22036484409100e01c0064042440800307002501c5106040140c5040c0344041d0817401141c002c903035500010b05001e1000007624140c140d115502006890030310052418140044007612459460014006504001038850343c0d000b031000200d40c85100c2c115214819012004025082101d2100080d0850b0010250480603940158070506081d500e034a074051059508a421200c0c0701d6040701d035840b0900022884000300d01507207010b845c3c032038010305800346080e00c01001340b80740c3d41c0c2c10400d00c0301d010b860000142440084a06407032042c1d954084a4441344003050003041d03143ca4102c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 846742733 1250 846741483 846741487
    0x60e160b2d04150909091502032e081504050c01050310030501020304060b0f030109020f1009090e1f0204050d120c060c080132040504050f07060c211202031506 70
    0x840320001101e02d034000d44030340d0311503060f541c903002c00c0000c03142140e101900203410345075900303001030340794000310790081f052b150040070240c82c8540054500503104054801441c0868144456642000071800301c100c0d2024a4040e41482e07194140c44064603c401810000000001442001c000001400841e48900219680d14160034004000d00c10445c106214203400d540d0030400d45014003e070303c1030f01d40060219480391806000c000d42070407509080c0080c8185c400e4001750100d1140f0031140b0403aa184041d0804100030244007402c403249008882480307106000034070035519041c00120f805580800c8820310241274480a40d68a00105801050340d0b081c90a041406540051494100c0d540d039580c04207544d5800c2c00c1100712102000c1c0c0300c5803030520301d1501c50103880d082e0055608180108140d0f4040160420102c6c101030780303030b042080481d0404006a0802400181035620705807610b41c0001c20b1414a0030081c0000b0100b800101c1c81074021001c07034140d000d024507180700c541c0c0042483d9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 846743983 1250 846742733 846742739
    0xc030b0105010e180c1c050a092d15020409050a060519060c020402030a0b0303160b060405090a24150e0a050c07080d060e04060e160b2d04 61
    0x1001210007401218005289010f5802060074090400800300381095250030140e61079240911040d000844201a4124490340c0705109a441d44100c41c015600d206011498410a08041c1e6480d40a0420000d4040345d616820503100303405030f02460700d658041d06503404540c0070460b070006402281c1018110500c0d02c81440340f0041542c0c000703422604143d61240c09140c44412590b90301c1010b2003000c01040d200000300c2c00610306a4002c40d13200c0141400044e4180c420350201f85942c1082c00c6034102490b103185500300340706030390031601d500c07040c00c480501c45407500f00005901c540c152400104459420360426280e4800d8207004401c0d69180e400402c0f41c1080454551104030f01131003051000d5a01708081106d03c1101d0052901c1102003040d89440c082243d69800308642c00a9031814456540754070204000c0080401c00b130049001d6407001c82d0030306020080034206050302481505680205e00104900300304c1c0400e9901980c09031030b045402d081c070700480c00c0e2400190a43c07440384040000d004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 846745233 1250 846743983 846743993
    0x7060203131208010f2108190806040203070e0409050f06070f0809010606020a030c03090902030103061a0901030b070f0216090501030b160903023003030601030e06040b060d08070c03 80
    0x1c1241c1900031920b038000d8062100d000d540b020400c2c02007070130b5442c64801c00d20864040301c082803c070041242c46415100500d444541d500c1c3c1003103403401c0010504580403403a003644072940365000002201e04518508041001900b6890b5284440b03000719105c0c0140d0302070100900101010360030312000c3e07600c3d51502c10030003040d02c1d1021180c1008038400c0c50104448003014403840d0140c071582d17002061084080d07101941c560300c0d242c1d001c60800002c2c139000301b58a98540055070007035208031400300707140001b030003110700c404e8145e03041c0c84c000e010b80001040801d81d01560703950089801c0c1001c00388810800c4040b41030807a807284940145e00490000a068071701688014100d9014080c1403940e629141d940b00b0303150402d64074641c0044d64580302400980b400f044602e10301c0601c0172301510a042407519602400d0521142c405491700080100000c13075816001c2c0b118030040302c0d00500034a28082d58bc18407003110181865001d402c00e040b54604024160044070116504035242081103940d85c584 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 846746483 1250 846745233 846745261
    0xf010c170717090d3203060a03050d0806121f020f0403020603090d081014041109031903110a0b04060b0a051206040516470706060e13120507060203 65
    0x301c14002401e03101071100c5194601c12540160030301440d8005034603280500345100c6e8001030003859001170040400030016030204281c80340443d03d40ca9061140c5810800c00000007000074582d80741d50003003520350040103280c00c00400641c611203001611a545004500741c5409542c000941000c400000e2040303403c00061121071800f46641d400215540c2c402d250030342d4036050322454016551030051800c0502d40364100301e082d42643c402850400300e4030800240782c500e0003c2c01500303c203d41781e1601e09141c0e001480074205030f01e00c8000c1411140035680c7c054400d02c02400902040da448510504507035a0710800001803000421a03901c111840e003200d9142c15003030740d08485d00d114040551090401e400300036821924078100907003990010b44816141c004228412a20603002c10100c03001c0e80b03c001c0007000000f031445164544415252501400702c4080d90008100300900e1000c210700703540d503404654000303541318903425448046150280da041c01281030040803107001004100b00045205e031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 846747733 1250 846746483 846746503
    0x190b03010c030230070305060607020d21020309010f050c012c0d0c0f020f280e01080105060a0312020304031e0605070305150118030c08030c0f010c17071709 69
    0x541400340010859844039a07403c00c60138541c20600100c00100006d0080e4461540010040c15061074809250f00162902805060442d5441c2201e641c0701040c0b440c260011094400b68002540ba10b05c60000181c001401c5550340030400c10000b5525030030110a4114000882c01007040800c040044030210500440b10303d8031503044c2c0300d40385407401c2c400c1c490340d202449560000094078951440781c080c0a40c4081c0c1d28280780e00041c0780480c00f1407008010388295520810307584801c4c112410000079141100040c3e0007508a03a0601c018803080c3e40e545410071007225801107240c1c0304030842080c241c0c298011540081c10055005c0740d410034203400e805520348507030f00c0341001b00841e036140d240c15003c840003550044c07aa000000400d01e00d81d401403515444618085013801142a66a074844081003c030b6017004150b5080411a128000e001f007042000e4030412100a11101c41a1500202440000c040b040c050311903000124190600036001c1e410059844904000300b0718145020784d9494201403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 846748983 1250 846747733 846747757
    0x30c0309330c03020406110115090b06120c090315010e16110d2006070c02040c02030c1006050a361b020c010f0903050a08090303250308010b0f03190b03010c0302 71
    0x1881f50200e0301e030306104100c003541081c2c1c207a256950a24035110028880d1105003074020800f0004401581c82d03204034071380f0401c00391008660340e401a200307160410f00000e0309001c000302c0b04070041c40400c0040c101c4681c4900315488140448a00d22000c88120100c040e0002c064060841048075469019101040030b480546a030040d03801d8111605903200c0c4100c0b56440012900d2141e000146090b41107000c2c8018a031040b2400e08051a4045080c07025101192180320341c3d8000c20050790400741c40d881c00921031200780070f0409040d9081c0c070420006209080c0c1c010060310302184e04051480e4000b0b080c000940d40c0341300d041d40c814007020795605003058034107001c5208100002c0d102c612400305101030300d90000180c2884002c0366a00c0c0d82c2038000d041810fa0500050154000850b8414140d84101c0c0b9102c00440341d1030502e080c05021040180c2000000305c0302000342c0001402c0303d104036a0804040704001c0307094841d16204100420080b240d183d455420100030340303d0181c0c150060000c9004075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 846750233 1250 846748983 846748997
    0xc091807140105090f0301291f080f060a0f0305030c01110a0e0402030c0904111306081e09070b0c070e0a0204083a0c03030c0309330c03020406 63
    0x381c41c0d040c454141411209000400401010025052080031012000406070012036100d8800785d0490744070918407900c00c0c116480c2040d0310308902e0010000e1070014011307800d4001004500200514001c40104114117081c10303040410003e455414004000b01102d00354800b01d29100e19259899601c4441b001c000c540c02e03e641081201004022035000d8485911110081852a400d0001a420050a80400314014064817170261241d014000c01c024032380407070303d54074800c0d4850390034611000e42000b41088222820042c54211034202120340b14644002e00030711390b480b41d0066180040640024911410200306100c1d4440002084c2042d00c90003108081140e4500b10034000f00d000f148980000b179070080484142c11964000b142491549030980d200d500c42549010241904911131120000b13406c40c61201d050541c544112612104903260900c801d03034040e1551082d9000302941800c861154482c1d4281d83c1202c6140400c907880d440030300380403a204c0c000015001303400c1031007520041110 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 846751483 1250 846750233 846750239
    0x21203160516120f120c091a0c0307050d0f020d120b24030105011b051002030c070c060507060b041802040c0225051f2a0f260a0801031101020c091807 66
    0x35400b56155010247c0c2d182040140791040c06071b4081c42c035540d69900c10324204074032017611900344003c00f1002c1c0117800501c040084280000c003207400c0c4106c45400c40d000b08200d121540d50107401804035203030b103030f101003103504003000011102c040614bc00c0c0880318981154081c0443d501c4069812903800b6207035000c514520910300c0741041c0c88042d00900941284400ca040c4010766405117030400002040e0f01e0400381a42e652140c01c0b080358105901040d40401e042040001c02c1c001c0c5030030500151824410000910303183c030005c03418901e000b0302c12611000500d500d02d20810640030f5900e441c200c45081c1c1004480f0311040c00d800390042c1070180710751624103102c0c0d1546400800d070f6408180d4800003031490f50070252489844800c12107420550301c0310700d00301180030789200351805405903554100a8410001400c40d46c0200c81c00c0511380c1c541445404640398000b01e42604403500f200124100c000d810700100d00b85101005d040d41c2c421014000d0040c010b1800c4a5045999100700407280321a071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 846752733 1250 846751483 846751517
    0xd1d030f120411180118270519060605120f0312060a0f2711041202060f16030206060f0f06091915021203160516120f 52
    0x206080d6010014201000040c50000c0845002580240030380c01c82282011840001035003000e040402410071220000148110ba100300308a80394410000010410401c010140c0d406154401d106241c241c002070100740188034003800f449040c2404420000d80d0103900b03107042402800c8034014140540e01c90b00c0c0143e004140007031807400034042c2c0002142400d2002d0f5003044452401020142c1281f09410f0020740300100341445000381203011080c152101d1080c0500210520380107800000a0804501076407a0f41100100c0e010f955030440640200c41c04c074004244d841c403444c21142216100010500842c1c40300c07240100b03600e4425420344206403a4075041160101c012016154050383c09003808015250820050000b550041c0a084046244c590b0540b9200c0c000d0780815068094802025400c0754148041441c902c01c4240032070540c1448800e41d4402d4084012600511200049142d40c000c00d00b5000049180d11001c20109007503d00f2000300420f02c0428200045161880c040c18400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 846753983 1250 846752733 846752737
    0x3150602010e0c0a030c0e0c0903030d0c0f020706080c0a0c050d050a12060f12030e040e010c02100624020f0601060c0c090507021005060d0614012402070603090c0b0d1d03 75
    0x1030f070801b4a5a024030b05000c05d000d69000080c20003042079204105a0089480c20301c0a846503004035040003900f0350a00320040c0a1100030f440000c110340140d5030078400c0d25000380140740c10a0149502c01d84513012600144c9400503080c2000c0e01e180304901c04101c00f40e83c410010400b030256a510070501c04600c10a101c10b803a124003440090550100c0c0c10300041e6020380c0e01514240c0a85403c5a4180c222000720b000c644003045c5655007a51504807141c1da1540421445041008416080092514064035110999180000f142402e000903564102080c8200a801608000e60040d600f03196500c85029000c0c0c1403110040300c40316503035540000c00380070324403444e4403c141d10740247c02510f580900f028001c003001044507034440060480b40011035410310550001e014401a401d2041d410005d07503c194109080031042076000d012640e07420a5400f003004812a50607043c041040c0082c0e03d020110a00c0700d8103c1c00500c000803d05a00380c120300d4220001e41c50f00080803c481158000b412a1070b8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 846755233 1250 846753983 846753989
    0x906090c05190327051506060721090503030a020303091006030f23010617060a05162d050912240a0f0501230108100303050a03150602010e0c0a 63
    0x5070a030841c018003034042c2d040950b42814803c0503800794182412211550004c81030151400d41c0141c101445209107509810b410103800c88005080103076565030f41610b042195540031036846440ca400040318010b00070103000c0c1200600380c135201d80c90460002e541e5007045030000003912449400540c0b10016200e640305403a0840502d2001d4091506c1c0e500803e0b400b1074046081c0b0030345680701894032070280705240c0500202030106203030700908280645403c8000e03180f0801c8611301014002c8206901c0e44030400b06c801401c000c00c800c1c411000c3c00d14101401d80e102c1d01d00100c0c1e80740038001c0e0f940c0980202a0b800084880c0380600b540c5e03001455803a440b81c1820f0041020616140c00480c071030b010002d500021100011403100200d024040035030794203900084034070000201c0401e40000301041c04003903032401e00e001110f6241c40421140424040d20001d002e00030000b403401c1e08280701e81c012400d8540384191030400140c0c4c40000034001c000c0d00400300b81d58021080100c2181c545a56010f0031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 846756483 1250 846755233 846755257
    0x5011406030114120102040803070b180601030f080f071410050906011403070b0711090c0a0503070e04090506012606100506090105131214191514010906090c05 70
    0x1903a00300b0102d843d0039440c42e504180e100708900b02c041400c110074001000948181405591202040e00d8011224603019122503280d0342c042c24a03280440b40040c110381182d4201868410111150910701900d104000343c500b1000b2002441c6c40503c80c0c215081002d81891204440001801c1c0740714104561040d10311222a07000130700104500e1a0045400c00c040800030161410a640c504020846a10411080381c1803024400301400174a01041e1165201c035204140900d49242840003c14511008001200388140f0504418160715180d000103429503029089550075612580c540302000071003610001844820f05401050300c3d00850440d0080395840040180e035803c00382002244d810107000103041203014842c5604558445601d00003c120495503035005070910b0901d0030b040301c0441140035a40d0b124280454800804d12601560160454207042140004d10500400b904102d9244601e51030010004243c100455210740c0071291280410407000c00c207401c00b500e25004002503000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 846757733 1250 846756483 846756487
    0x1030c0e06030705091017060603070b0a0f08040f1202011b0302091e04090506010e0403090e0c1806090409031805031617010b040c0f0f140f0906070602030c03070305011406 76
    0x11450400380400b94000b081a06c540c4c62540e01c501d0030341c0b92454450000d94050b842402842805d003000d00c10710000d00303040d014881c034207451010050403d415154101d410480c003440068240440c10b00c849a81c03590220311344d84601711120703000f4040e0600f0b1403a443c1c03403011805603d007000e00074030071a03095540103400b01d03148503a9141c00c032524507281050b4a400540303400c10400014801c1c4040b034080c056000410100f4146410018038505050f040b22461405a0317060060038a5103905542512a004000110500119012031494024403500513040381c1040b007003000701504001b03a01c045103040065000440e948030201951042e05080840220218000a01c00c62a03112800c4414400b002d002081d04000390010070125000e8481880000c0c00c58480558502d40c0109117560b070317100d20715000c90583c001d06014403903840340c060b07050040007001685144a0b240c010903290b4850300b051045441e85803200405509500441d044400280340900105114030f01501e084030282016007014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 846758983 1250 846757733 846757739
    0x150b04021306030e030906070c14010801180b010c0506090309040f0504240603020a1202040e0607050f1309110910030903050f03131209060f0c1101050a14030f01030c0e060307 77
    0xe80144134020364401180020005010706840b05d80041050502c503440e48040186010804c95084904410160408c41c141c3c004018800c05038482c141c0000030500c0001d00d124020005803001e10094200a2032030280e54100700d841d980100283c143d01c3c0003036800380105881c901c0580c003114801c96008110200300d4910350350440c62103507000d100a624400008405880742c0020b80308513a030340d100005946503c2500411414603000c0d0b001c6400000009000d14141400042c0403409000301d034440701740021905924001b04500040f00500c4a803104202140e00b607000758145500206481d4001d890940aa0074481d21a110b000c90541d0141e98032800c101c2e0380008010a0344c00a800050041040c124080101d0340b1880c41030701e84005901c0d00030040e45000e501420f080c0e01184800240051680c3e00808a4000c02440e2040402481d20550b12111403e0070780ba050300701022012030080c08820410484080440300e03060f280901415850f00d070369070254081c007400c100d602c581c040e00082c90070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 846760233 1250 846758983 846758987
    0x20603040803131a0a0c05030f0415060b13140102030a050d090804030b190507180512030f0c0106060905041116171c0c020a050615010201020706020403150b04021306 73
    0x2c0c0da040b10071056846110030340754881d000c0100042e10030019040c8600e040c415072038040d00c01c0d00c4810401e800c0c69403c620303001e4450b010000c00200080d141101d10040600704617803a5000070050310044a6550311201e540c81605a02d040c2030103484a030340424002d00c3c1d07441d030002060315403000141d034445e40303805100b42c1e10304080c0500c0d00040329030680500bc0440003486130300c0c155101c1e95400726841640030f906103445d026100060482018015054a90364410100551203c180c460582d400c50645103401c2160f41f03588516440e0141c51000450141e08054041d0031400c121503455a54801c0c80f62a1000c0200f1681283e0706030404000420110110311000c000c0c4c1d90500c0c0c09110000311010140511030002c0e0302105001e41120301c1d40c2004409038410744204042424117100902c042d91300d655803c4d6643c0009421044584a03600320404942e01c01d404540031f00b603000340b083d52219620710f0001c0d003496641812039601070918031a0080d41c1068804d0710a91580404401d0318207192140c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 846761483 1250 846760233 846760237
    0x7080f0f07090f18030201090308060a0501020d08042d06050703020f04090f1121090d1b06060510031a0121090309031a0601021e030a0f02031303050601080c04090206030408 76
    0x1000c64059195141e045a20003404130601c469806900082a06402031070018140722004103140d00c42d48c4842014005c9036800a56012515528104944d02e6151410041c020b110800074001e015600c0305001c02d0003010b00302c0342200d010300c200c1c2c3c24825a15050300a8059002d40755040e82401000d0100308050308454000791840102c1c4000040c81d01d8412405040640c8402c94101c410031900c0803110b24404040e210aa0240c60340019000720041c4030300040014244198144040d4842c01d141c50a02643d64489402868000c0c251500e800d010b10b0060007814176412400c4180702184080cd015500500a90b1459080c00e4241020340100c20502d60040c02c84030001d030200b000d0090b01100040350042c43c4d48180d007075080c0303c9005141c00e0000901e003030f0016610804400d0a40c12041c1000800000c1c2ca0261202d07041c01c800044405804914600500d050450030041c6060004148580400c0b0036050703840802c00d89126036003120911050b07840c074110085d0000b0f0100006004a002140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 846762589 1106 846761483 846761501
    0x1052b05100e06060901181d060f09070801050907110714120318060d32061002151807061e110a0b0a0f0c0207080f0f0709 54
    0x404c0c4103001d00c1400c541403003c82c4c1c451840c00030704444203601030503250f00d4403a00c40c546080d200b5221030041e01d40318000c0040e034206110a00305640a6441850b00e80c8815407664030704024440c0c03e080091600702001000403080c000120140240b10040c1245130403004007888420821540e80074510301e4122982c82000303812003c40e180704050803201d000f280c41d251264040c113414030240490301f2501d1840d08400304420040b034900f01c1607200111a410035441c7c2d9540d0325080c88082d40000ca2400b026a00000e02010f044a0151001d60f1042c8180007010740d130810480d0395890b0000d40d400076004a030740d8900d107003140030000445031401581464001d0800003942c40d640d44410030132070b01802000503100054900440c07034015044c403404030601004154400b190007921413040b8002d0000a00500e20651030000d80082c002c1e094900c01400741c401180741031200b05c01400c4600e = true := by decide +kernel

theorem cover : BRFrame.Cov 846582733 846762589 := by
  have h0 := BRFrame.cov_init 846582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 846582733 ≤ n) (h2 : n < 846762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
