-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4344
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:19:15.850569+00:00
-- url     : https://prove2.me/submissions/28e458df-07a4-430a-bddd-426d15de37d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 781115107 ≤ n < 781294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 781116357 1250 781115107 781115117
    0x70302031b0715030509061e040b0601030b10020601050f0d0c0e0a0603020a06020d090e090d200708100f0b061611060d0b1809061f1d01150c03 63
    0xe9241248010100c50141c1e4503050082082c00180621001441e0940d0300c0c06882c04203081c90010140c41c1070a0b002002000c40b07805600e12800d0b1132501c40d2000d03a2081d448580000d01e900d40d100120300a25201e100c0c2a007081c0c0b0004840b0040d80c002440c03c2c1281c400700c0d1002c00c050095410300103038184503c802040441e00060030b024607180c0030b0342240e0250300010005402076803078001030140c0407603504c00000750b00f0800d1030314000e40e4442c9c4035101030070025080070780340d0810070707001d9503184055007600e0708004034403040300c0e041500d800007001c2415801e02140e600703e0b15500c203d5200d2459003041c0e001d1901d422003251b88404d0074083c51f15144001404c6c207007003800a41021000604124080340d49988001e0302000d280da5a4016044180c1951720000c7e501c080304007485550300c0043d420207405c1000c41c04001d4628000158290700083c0101d0944443c1c1c038100241d00701040c6074210100058080b20907280320301c08182040d040350139103000050071280c0b8480650b6007103820200500068 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 781117607 1250 781116357 781116367
    0x30a14090c1f08040b0405030705100515030a031e030e0d05250b070804021f03020309070f0b0a051b0f0c0109092003070e09010803041a0f091309020d05070302010201060b07030203 79
    0x182040c0c0d8006d90082c0124241d910744603c40d540c590a01e00401c02c00300c60142d440e02801444031610f41d00b118007000581c02048140c0403600c014103005c02d01c0e13040c0c0d610324483c140d10801c1c0601c45e070131051000ca442e1080307503009041140f01a080390410444112980703100100d0403940034440b404800c42e43d030003006112003a01da1450480e501c66004009070703001410321840c11000c1e00c0803c0d40302034580f0155401a281c1c01c1c41c00007542403011641c4103031003181d28400d05001203041e0307004039000c0850500b4515507420f107510b88803051500a9071100c00602500800d035841460208001c2002c4000b60303151201e0540b40d4205000311450500a1010000010f9031104c1d0f040c0b409005581101c0079040c04040f6410b84000100c640e48240c21910807608040307020402c40301d02002c140590012094100c0c2440030b076141031382c03070741c0181046240b151100b0941c850010000d40c0c40700720255000740495420f04114201540d072071030719100490040d8600300002444c280c095058a82d507a92640c0034600d01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 781118857 1250 781117607 781117613
    0x18010f0503010e06303904020c070f0f05150307120c0e031f05100e0411010509040f05060a06050405030d182705061005040308030a14090c1f0804 64
    0x418004c105d40c00d150301c0940010385000d40602c41e800c903c0f61801d0020081c000b020f04d0b400380c0c8800626603080714543c0d41169281001100744100001c0d100c280d07401600d5107045400c07a41340c41c0c00750b8860700018a240c4030101d020200485900c0580380150b82c465003407200840301c2c0c20584800c89010000461002024826203401d8021642c2d68040c1c1c9040340161190302c0002c0d00f40b5081c0c50a03a03000030711102c010b4260300820f00846a20030b1041612003070a030700c1c1a00c0e42d40c0e000002071000308aa0450804281d2683c0210140c40280e4000b0700100840c01c083c0201c0c1c4000c07d426203241c1d1282516400c00a07500d40f040003102c081e90780140103081e41071340008054490340129980c1c05d107184566100841ca2019580410300b9501030342c8428a42e030307604003800e54101c0354043c00e80c5001d0003a507800c2e0007d0700d42090442d42280d90096529036a0b580e45641c4e00e00400b15140c08000112411080c85060718001644a20b0031404443c64001135080c0842c20782152400c0c00c8250105100030001804 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 781120107 1250 781118857 781118869
    0x100c050a08220c0602030403140f0a03120204150504080c03070807060c080c060c03060a0906080703021e09070909060603140408090d050607020319261005040218010f0503010e06 78
    0x440d1918200c001e10340c9103036a03204503d034003813500040e0042e80042010001d00c010200070700507888460300a0b1807805000780c640c58a411403a00050300b848103408441036806201c1d0b040b10000c090108101413240700c1c1440040c402e83c09449111041e104448212a05160120b0031400302c880c0580200b003440c1c90300e1000e442002c401c000c00e0740d245a092041c10440001407201c180701e00c10110a80e681ca2400c0820090808032582050708410b1811909001c4043e001405005407601100c100c01c0f0212144600030031601e080c1412900b0600680911040c03640128803901519000003040c0701054039910110120341d1070f4a02542080b08100228012603d4000140040b120181800264070102c0d03c2d0249032000035a42c290050384001a040c50328030314050810701c000031a103010f11680303888566011600c20820314854203101520702081c450300442c000c0500910014000759180c203424480c4414003001a0289400b1079800c6c00c0c150795040c86182181e059482c01848508640c40703080900c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 781121357 1250 781120107 781120141
    0x71b06110d080c0c03132408010e10080a0c0303090b091311120705090906100c060f1503050102040806010e04170a0c02130b01030f15170c040905100c050a08 69
    0x90f40c141c00c0001c1c0035840e8040c00107210039400c4014454810b4640140f140c034041d03041ca10280c0010b189140d40607003d901c034412070304451446030f0010341610361103548141c04003207900c400700501c2004207400801c0001d0b101113044901a0f00d030388951a5a510b00c0140a1260f4041c2d203502502c5020407002e45031380750344050341100c5e40881c1141020100744405c0d038848401d8800c04085180400d5041d00c61801083d001d52140c400d50b05502104c08440000c1e10466000d040105056181c422600c8a490300f503000044081c3e5240d50501050b54900b86103000798824010740c0041c2c00303100c0010a03404803910440307000c0d41c0d02142c0e0044244250490190540100207a501080b41d5809500c002d692042c0c1c940c11084603490f400207900b096800050101d0340a41d0444045c9818100020b0710036400e50b0428049807000c0d070041594179080d200700703070400c000c0d40c0034198000e01d40106541400707000641507480c0d080c00a420000501e0540f400d503554010209030400249042000810300408405c00754 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 781122607 1250 781121357 781121371
    0xa060501022104081e010b03010606080a05180d110105060901080c0d051f0c120510150c060510031208060a090c020307140d020705040204030b040209090f03071b06110d08 75
    0x90f081c1a1140b001a00701034000072101d64144c10300700540c98024080c4143c4400d00021002040050f2400502501807100180b015001580d1a4001401440f20b00c400044c05c2030103409851114001140c081d107500c07075040711a45030b9882c0c20001002c2d4100780c808141030b10690002000e4003240a001c00241404c90b1070308031110301804c5440c254070309040702600d800c0301528101003a14010400001d069000c13105203141c00c2424242171090b4542d451008000391202581403000101d00a2826100c05c41c1203032000b425503140104000c866000c08000c501564030829006480305000c000032124058240d40c03079644602c19020422854059900003c0d220b007030780c010359080c0382075902c2d26103c0c101404110101c0b234018200d681005a414800800504000c40341181094115140c040400704014002030142c503205c1e0114602d61810088040c0100814044a03682d03070040c5400044c28840e02860007100304c000c100030079014090038420080c0441040180307058000320200302d0320707440090610 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 781123857 1250 781122607 781122673
    0xa0305191e030203071a27160f030b060303181311070309140d080403060c09170f071706040201030b01090b0d0b0307090e0a0807031403040312050a06050102 69
    0x656844109100d0300e070002c1c000c0c2c0145403a03180d1410426988412404480319001151040028811640c10900386614039a100320b200069201402450b0244404021120404074500001c5c0280c1c7c032074008054070320401840c110707174480a060641e24028407040300441c104c0380c0c01c00120740c144400245641d90312510701003841103031092030304007550100406030005000d0714030034440c05c440300c0c00103d1800307070958107140110b005450f41c103007600550000526458036420702c190300b103100c0c40e6240040c0c0040d1000715800c45003980a283c0d0b03491a0818002e090103034120014140c406410300c3d0000350028006410103584a50045004250045516051180c1400041415102c0c0c001800d020003048100048034000c03d03081602e41001a40b10900240c1020b86440400a0104035150001ea0003d040d07900c80c90945000e482c09070840030324200c4004084100014103a05c18102904200850410001e6445042143c0143e8100c1d000d43d50140c0d00145207126446146066030468400100708 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 781125107 1250 781123857 781123883
    0x8010315020c210a1e021e03040509130b070c0803040803060a0801050a092003250b180f01182d090b0a09060f05010525030201050709050a030519 64
    0x6880d4150660007140e4403103c008180e41c12804d401074004688001d41108030700c00c40c1c8440500955070b04401e02c040c4806041404403409140007007007a1000303400000c3c011000d0f840d04000c844110140150103540420394030010600c0d41f03019600c100c0c11580c001940b14a144d40323680700c074101c45d400644030ba50040e4071902c001691400a100b054024030f4440c40100342406a81031034000307503c200000140c2042005130028141c0e60000e543c000b80c00d080c4c00184c0744011541c1c2102e186810540c4020340c0c800c00020454403100003000c005400000440310206421400c0004580442a0205141050301d503421b051150300c040300051b0f80701140320010400d408000308070035000700e102a030141c1c41e00354070b440c071803038492510009020180c20348203400c21800e80b900001c8905404544500c2d414003000152422940c507101190b242000c00d5885500c2803000903181c001e000304000c03aa44000200302d8440414649016072000085942050042c030100040509891184c01c0100d022034183e850196 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 781126357 1250 781125107 781125133
    0x601050331060e0f0705092706010801050106030e0606150d230103060c050c0a020103091415011e080c210f010c0e010503010302011d04020f161208010315020c 70
    0xa03581d900318400d1201142c11068440101e290a5000314400c141e43c01c03001c8140f10a4480481e45980401851001c0c000b003040061407009411340c080f03480405002e070744000300709a03005400042c101e54080d5001c001c2c10343c2e4183c00503240d5000b0b4030b0b00d40e8040302e0024482c0a110449014100802c0c0b203c000140d8611402034006200b50003140c8036030521400801041031004512850762000c0c0c1e41c0c1001d516000d40200a0354840e0b80b22040241459902d0700c0704010700840301440c0480d4000a81182c00103a0310036030480484009100b4200700b041080240b40b510354015082a0444d81d41c54010042105003404000003880c0300d0442d5440c0c1c850680300140c032600d040100640a0304080000219880600c0c801050144203803101d50500504200400042c1d078000741c000c59808418164030720034004000000d0291240d29424003400c0c0f0080364400142000040d800c1c4550b00c01c504454800c3c0c3e69820694600009110182c403086101c4500c0ba1104125001003d41403100c00c160740780800405 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 781127607 1250 781126357 781126441
    0x40b0406020f0c0703021002070b0403171606051f0b1e0706110a081012060b221d1605010f020c040501060306031b03050309040b271b0306010503 64
    0x83c81c01c0b80f071907010141c10015820300f50a036501404140c409099554101041e0316900c1c411488020010310440d81d055440b4051102566545861003000140803030b11414104050316084d40c2407811111801d180d10074100344503a0090441d031a244040d4201002c0382918400329640818401c2c3e0101c2c10001000014082e20903894401100c17400683c4601c1036520007030045a00420104448808510038840e0382c111881807185203600002c00300b800350360100402d001428a60309184040980d10100801c040039030016840c514950f51060098005285901d075550981803c11f0b014a511a40a0005501c542d02d2540500c095004480d68050420f01284c21a07000360f015200081c0c0c2c0780024810001d203040e042078001c450307081c6801c1c4242541c403000c0d03d91042004481c8140e698000c04040c03911003a004400c04500c104000c91180543d40804288030380485043c0032401d0a902d488591140000a5078080c41040c3e480c641180d4901c801141e1302d550802002d88031910841d445861100c601c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 781128857 1250 781127607 781127617
    0x60d03081914100602060708060a05090406091506091a1e0d21030c0201022704090f2a1a070309180603021002030705100b0d0c060203120618040b0406020f 68
    0x1c0c000342100d51810100030704246c805009001005100000c0c00007580c0c443c032050050f94400c807940301140d196440c0100081ca1000c0c4001c21803006600b06003107101c080e5000c10100c0d4160001400124039000100484a01088110390b006031102918410014011044a10000050441801044030f62946c0c0e45004466405507881104034003013650081d0f00d03009030a070f0604580007d5060468981c0c0042004040b042000380d8420710490040c1c031591203030812290750341c2281400c4040021820241030028000707800f502c1010340b904202401d6031040b40072400b16422100542c40c0c40e40e1021143c036056010050580c10040c0c084004543c054054803452840c410070b080002d0a00c2c5948144400390060000c00001d541090204e840411004240d1803990035120000103240c641010000d00840b00502020307004529015000c0ba265800100074000e440c2e0800004003182d464400b04024410052c58020044801070042000a8050501143c00c00e100c0c15016040c83c0902c00c4d000e6880c8c103c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 781130107 1250 781128857 781128871
    0x120708070b0a2d14070f11010f0903080a11070c1a1b1f05011409040f12090906050a060f0318061509061712130f060302070506060d03081914 62
    0x141243e603000034007061060000b960380c20384298285203085070015000c002d0007a0800280502c43c901941150002e42c40b007080150500c000300020585428001c00500c8101c074040050780c90120030440c505090402e40d078900d5401a20103424a08200076041780c2d0b50501a400103c440c00c0c05050500180c1c00c0c40d02d00c29009640040c0801152020b060304405039425440c040c0a01e00301c010300c03e1045045012104d0388003501c000d815629a032030302580c04141d41030060328643c0410a05052164808044401c0b144000701c10b110081c0c96104011140380302e441940040346c03a40f810104010301030b4020718100d5104152050f07155549840d60401d803121242e540e048041c00a40610141c0000d111f031801070560040041d10010072444803d41d1803082c04203040300160041074180c01c0d8800e00d00c92002030036000d0ba511004d141e8600700540a5040808200d40c98000c41c00000c280d41042d2101d07603240d40d015505d83d085500c4801081e401c0350800000039520984844400400c1000b600b199401901 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 781131357 1250 781130107 781130171
    0x213150b03061c080306010c02060409060611060a060b0d0b0d020a0806070f03090f0b040c1703310302011115090f0606010c03090902130801090311120708070b0a 71
    0x10b0804100034004148184811002000c40c8016000c950010140d0f94020820b007002c0c0e80c0103469000043c03003401180d01510f681410000c0c003081860f4000302c00000d1307500c2c860840b241c9841e00800d90f4283c17500c60040b07041c1d0382018820751156107507039000341c0000040a003071182e002c070894001c50881d01550300920b045900020038012407a601043c808980d011505d0f0820130300710303290b5507007683d080021b201400c109030540204003070120403800f0740700601920543c400454040d155040c1c41c0d810107480c00c5455054011001443c9802d584481e401c440105d22000c82d10f030440c1e006455443c80c0d210b80d1000c51140705a4804805044070b1214012032021004000103c0312404241c50a01d00800d0b003810051b03040850313800281c0046840781a2a10303450096110881c681c0d913180110703e15030010381c0940c2880035010034141c0203941184a845a00180c480608240c00400c00361320074154000e0241c0c6c8200007100103d140b02098a410002140000c11240001150301001c60f80314070084039121 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 781132607 1250 781131357 781131361
    0x21303021c0b010603090206030105130b27010b18010305150d03020c150909150103090b01120302250501030e10020403031107060912060f0e100c0e0f0d0213150b03 72
    0x2c10782800c0d080c01003425103004e02100c001c03139020419a000c1032150038041c00820348180382c0c11301e544d04032a040b088003410354415541d145410325618850000d1170b145610203a40049101100c2000715140d9100f11103030340040041500044008100042506801c060703180041a0203942c1c44c0b00e50302c00c0900a60040085015485c10041c082c3c00803828200c80000400c10300c1202d48130440130036480040011511181c0d0800300041c2c0c040c101045c402401c0700c00200011900407412082d07207504601a0342143c20342d19108138044080e07104001d040e0380564210300204901d40c42900842400a6004240c0306040e032040c8801c4242c4c1c00a80045002c034443c840404004103080103004001d142902d8860102c40c43e01c1da9800c00140710440240285072121181110805240c00070f4000350020000c440034423024003030000080c606600c2c3d00000aa1000c070440c81c40c5000200320120001c003e1244146e1801c960070031085058504080000ba81c4900d501da102d4008580f000380100489044503a40e4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 781133857 1250 781132607 781132613
    0xf23010209040b060406020715030609060f0e1e060f010207030c0e220f1104140a051501020f06130c09020a0203041a0711060f0d090507050103060602060910021303021c 74
    0x18500f036031041801004188003c20019500080030000ca0304048648110a43e80040483c013600e183d800c910303401414040300180c08550b009e4008220b8007219514840e42c0c403a10b1400c10040940da4400440c03030150000308041c0d25000c01d11038560041401150100c680d01c0d550031690358480c1d07021540c1d150111040086a105282020290001410000c20650300d15600c203988103400840c05840220401c41c240d4154646501c8640444100000c01d28549485a0040b0103050211064030340c201030310701c00807200d5000050500841000b800513050603034880080b101d05484194040e2900180300400207101c0100d4401485495155409180e07075505007444d8074282c0a0000c420300045c0c80801041c00420580401d00d42944d1048482581c0c80c9005a4600d0040c02480c140c0308080d0305e00410341e410010700050000031584282c80900c0103076036400d010b0361110811600d0034010b400c0f075040c00b182c001c10b541c0208501c007194500000c26503203c0c2c01007078500b8040980c0a03286400440c0d00e4040c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 781135107 1250 781133857 781133861
    0x80106031a01060807080406090f050c011b08040e04030c0212030301090c0503070203071112010c0e0306061215100f030b040512160212010204032109050f010c0f2301020904 76
    0x360200d8075640c2a11035160030002405900c00502040030403a04501080410070150084d4071090381116010300e800c075190030125260035028000c1804204101680b90392446141546e80d101500304000c60309062500c0c460300740e140300c001d2089007007101a003220001a0740d12641050840e02020045071650304200c80c102c1120b000b00703081c0090180c140704010b6003d43c0001103900fa650700c00c08250032000d291004c110303940c802c0b114a1450b9400c0501401010340c0c0002959a254800c80813505d80c0d4895030706200810050000c0c0c0d10141d0021101c003491080490007544d040014100808031141d40d40205d090040c0d10703034104a54080c008410f00040c8003040001d02c01c06190740c081c161410340307000c0340540445602c20009001c1d00031742c41100604042941070310300568104050098101c40b184560500d840700300c0c44100481c00c40e110204645c184981e64a03c0b641d41a19180d5540d10943ca8200761004010700844d400060140402501500f800e0380744c141403502c038005078680a8290030002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 781136357 1250 781135107 781135133
    0xb071103010614010e031509010c0207050a031208130203010221060405150126130302160f0e220507061403093a05030610030e0c0114090a08010603 65
    0x48260b05080040c0306400e8540040c401c1070b0800d08020f07802a42001c00b10741130103c020503000b546403200c01007140454040d000141d040c04140c2c25aa0055140d0003040703100b2070300b404050860030034000400c003030030b01400c03105800141d028880301c49202e09500190990b40224410510070306080b41c14060940c0550300345800c070780700b11010321451810340c2c006922141c04024941c100710400e6502c10300c541c03000c1124218480071120200551510500245007400142001c4005100d14603011411034a00b1000001303540c1c0108074032400702d00d068141b44003c2d0024080940f20034260442080a501001030080b0141c4114003415041d4070301400a0501da808210b03c620020f01002042290f50012840c0c002032004245c4410114100405640d8117030304a4003035464181100c001c00380460b0300000030b144101c0c021181084803100b41d1004130169580203003403404503400b046000b03182c0d60080400000c03003281002c26604200c1c0b84800200c0781101a4442c0704640d40d101010301c113102907142c07000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 781137607 1250 781136357 781136359
    0xc12070b0a051902030c2703070b120a0f0204090903030f05150904120e0a06051201122001140d0b0a15081b0d0203010803030a06060318110409020a0b0711 68
    0x101601c0e00e102400c108804040402c030400c4e90000000b50102e040340255680d400542420b00c4401e145550035200c80e55281d2050b86c0b09100f681000144c100d024022a008582c030340c0c2d0507550946880008a0140c9240207501820302e800707020209800310640704054089000b5600454520b24002e03160046400c081c144000725526030789080303001d444500055801552180500c40843c00150341101d030101d2202d8801d40c07000328900001240341e80b2001820283d680090303050840d9a80741401c40107042c000700e0003011525440c3d484035085641410703500d5100d406042c0b6070b00307041000702e1464483e44100592003905603501c005003554100341c0e800401a22003151901c101c50b00841004d82007903001040d1050540b00d40f59180f14200d40e00f4140c0351020f448170003c1d904c03940c41d1644151660001c88580d03440c03500d40840040e0302803203405503c0345180103818046400c0c4c43c5450704030a40b0460388a0940068403500c0c02401600c80d11000002041c4400d5032585400c2e60746010114514265281 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 781138857 1250 781137607 781137611
    0x20d42060807120f020f030f28020a030305030a0b04022a01050c0306330414151801020304030f03030506010f08011505030a0f0504200a030503040e0c0c12070b0a 71
    0xd00a400c070040100c554250404c40b4100075011030703c0090341ca90180034099405010701030381c1000204001403400c4940440e0f64105502411440301c5840c400f1088101a620121069040000c42e004000568004a80a00200380303080003c0225050364011071009030b410703888009101408407002500c0201030541d1000784000c1c201081f40200600001d0aa10b00c41d00c0c1403903103548142d00c200768600b548031185c590780e959070300e0701c400f01c5880b80c010344121403ca0bc58020091200c0c58018103041081d020600403d09080f85100103150394010001a40e0652004100c08008034042c0701004098502c81e80e4041018030b051000109103501c035054003400d100041f0f005211240c0c02009070800d42c00c0305d2500c55142da0707402906201424003000381d1000c8a2070700040c0030520144041c0d01c1885c4e4a038140b030b0300e5141003400074441446501d2101030600c5c1c0041c0018068242001c00765600112107034110350501048000ca0f40c00c0004201d404895041700154107000c20200b40e00c00f9030302c42100001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 781140107 1250 781138857 781138859
    0x61215010e07020d02010b091b040905040605040c0603090201141605190606060f170705071b0521030d2a120b010504080a030f0504170f01050f04020d42060807 70
    0x8200701c030002900c89e001450704101d0904206610a05540050008010510682c1020708104d4000e00c010358041c1c0b040082c2c0301d03010800d18002e00074110038a90603568140a0054940342c3d05003a040032041c0b00c0740c0d403c14810440486c0307040003440008034614018813408250307444c1c503070215446c607804941442460083c41d001d1641011603c0211803c40000c0301e219901d61000325014801c1003002400b03078400c40c03800750381d14404660035001e03103e09944000d00804d8050300104496100400070030554010019158406102d400c480105025141c17401042280000025254148a90304a000840d02c59407034080d24114003901032004070a0030a00e140500f031180c0c06031101c1d044440a01846884040980c0c1907120350215002400400030180b01c0c0c1a56000e1a521902003903c58030040d828080885c0c2d01c10401c80380280030f0b40c3e0041600c0e0b0304400903616001c00e100e0341d0358034111420f00c00758480d442582000344208000007100d122910b41d02c0d1030a4442c11075510360044081503103d454 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 781141357 1250 781140107 781140109
    0xb040e16030305030a200a090920070f050a05060f0f0106050a030c110d090614160f030c0203060708041a01081f0b120607090815061215010e07020d02010b 68
    0x2840d00a980d01880c105640f640c62001710400382c02c00040c41e040700e04184000303980c0c02412a02402000b895030395440f201942d00e90a40d4242d41058064403160809420802d0000740c1100080501d10302c0703510a028228456124203040c00041641507400d40c0101c4104501c820300480c0d100d60081c400d08130303890781c1d50600e08000e00b2402109024824560344461050242d80281003080041e2488801c681c4007030040140102005c0141c0314540103c0c40c0000d40070b8424a055041c1e07131a00300ca0072050b11001d011a1505010048650740550910000a0760301016031010700446110782140c0c4c88840030b40c105403500702000c1ea804150b0f6000300c3d014a005001c4500e0104070303620b0300e010080c5d848240481c22810300300141181004194022004a14004440c07400300390213100e584c4903100c3c032803190358500007030f51500c002d041900000c0c0c605c0c0c40080e40d0b84c80c040001c0c5480e0ba40200c21101c0103001c60041501d0145c007a0855400010042d0400454582c104600c1c0c0d03100c0c072903100911914507048 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 781142607 1250 781141357 781141393
    0x60405030a030b030f0a140d1e03020715020c070311120606091902030420150f031008010216050111070b0c071a0705040302130b010813050c0409060b040e 68
    0xd4064205a116503903c1c005aa0030032040b6803501c1c0c48001d507184c030001450000e1f001038081211300307400c3c0948003043c90518020b86407182121141482c0100350f10703821034110000d52003800c1c1281c11898400d03207944508154409040c8101203030340100203007421410250810090b01da022441070f510b000c10910040300100708140c20035000d4609031015100c40e2850f40301002c0000c803400e800e070300c00301c1000140916807a034080d4014041e8100886a482d01003400f100000010384000901800c0000d660116800f40c01194031007540190b00300f03c907848070695426030b0b204000d251180744c030913003080303080c06028811171051441c0f15000340e186c1101c990710300c2c04280c0d00400340c62140d14040344c1c0f9020f000103070703c80b46000300d10300f4030700d0740d46203450800500142c100380000e82c0551911074a41c80c241c44107101d4140d8200c01619240340c0d6075607814002c1f40142c0c081c40221070f140114035081285071158064501564403a080c0031030751031010000c2c4011181d04803856855544540d4250100a00c20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 781143857 1250 781142607 781142617
    0x7030e04020a170903091c060c09030f03141303060b010836031207020f0d0302030103150506010905040e010915051b0a020c150702040f060e070f1404090b030d0206040503 75
    0x14559040c9140d882e10560317400c1d409854102a046540c50504945510840c0e44240c0501d105c1c120030007154403c01021121a200c0e40001001050b8800c6101c0100c1d00941140d000d605c0001140d0745400f80d038600d8682c10310004c1d40122000e580384c8098000355a0000c6665071300c0f540c40030301e030a45484124a00c14080340300300d024900a985d41011104245024003c440c0318180d110599038450601e0b210081d9106500c20354007145001c0c9090b0101e0f038500c41d0080720b040325080750b41290a008039001100013080082d00c8203050080c0c0050000311074445005100740c009041000150301d14490402c0f01010940e40c81c2552a00d107081c0410501a1072840078105418542c00750b20313101c50340c0c050180d2401a00350740b034581c859203114052070031114400060640314801e0320203121070741c1c2c0702e100b04054480500568256002d02000039007003503c2602014440110791401c404454450140394640754881e0300114079440d129100108942000c1211410450b203e20007488030349080c0c0c880325101c4c014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 781145107 1250 781143857 781143887
    0x201180507140307050d0b181c110f0a052a060d150306090f170c060105060f0409060b031b0a02070b18040c03140702193507030e04020a 60
    0x140a482d14060f8504002d000040c1c10060210b00404000b814880008181100c3c0702c3c80c0301c40c811480380c51001020403280740d183c0301c0050750803c01c8140402500c003103202101c516520300c03a0b840104040d103020011026694000c0d0b0150800c80110210f002007010840c000400108403882c2c6260320342c640400720303040c100d0303050790000b4600103881000e190344100d640094102820718401c6d40500002281415009105007100078003060500d203101c0b524000c8201e40e10154002800400403414048001c00c1e0201c2c1401d0410b103455103802d1000b044802e00d400c00002c100c8003104000300180ea01d00140822242840120b04104800030029504c10180c0680d81d0404400305d800d0130010719001e400b6444890091040c8a40c890050006008010700c031182410450084046040d00340049a500380c2140414031f645134002d0580c03a07411407040018401003507403c00340c42800f12403181c602c19680e003100b000c1d00c050f81d419135410001d010079280008a44100d00c100f113505603003500a0b44210110503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 781146357 1250 781145107 781145129
    0x1109061b030403051015050f03030a080702011104092c03161e03030203071818091a010b0a021c080a090212101e1422020a060903030201180507 63
    0x2030205502411809140d10040c0148a80142a0b203c1c1d11140c00540300c07100c800108200c0c6559441c104078000e401e0f034046942540080164001079071190702200c0e4004460700011030401c4103003003044030315445a401801c581c0d036105030301450150016200d2051884804001c000305440d1081a80c0b00e20524045c04130f925804403440041124441845944424000340c5224895513410054080d510462305500041d10407103480410300c03094406601071b2880e060301066031604c182072203c0100915541030302c01e8090380200890703526440724030502800480146a841c0d4090000c040c2c9841c09a40000000d0004034200300d002603841502142c0c000c45005011a8002c050700205d044039082c60b072040b00d54040d244070040d001d445da801566200c2c2088078603030204004084514100d8004102d2261070750319006c0403801029400340b0700c1c03a00c1401450401d01c2810341ba40002d12151903a402100480c0300404100309064082c412002500300803030740340003c80040c1e030340c40d034a6600e079001d44a180f0b1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 781147607 1250 781146357 781146397
    0xb090306400b04060218040603050c0103090f050303010b09031504020d0b04140723010306030807060902060f1603030c02061003021002010e010e0f070f030c0b0d11030a0b0103110906 80
    0x25421005034403079039400400701102802c2a0a1840207544103181c55014602e410008041c142403a1040c1403c4940003400b03844030b069403d0045018110b40601920a204170f201c2c1d0750045401400114020400030012543c2d0700704a0041c14208140034a101422030070480400c80962035081c0d96060280e03000d01d00c11165500c070b14040321503591442c50000141300e00300c0701090100c00c14030f04502448000c0850035014890300c0c01181a03842900008215180600101d400101c154104021700b5100412407410880402c8545201e5003007010101514401031811b00c05041d09845070f106020002c2c80a80100d00d0200e0720041d03098814030009000d61410404a10340c0352013035000c43c0184030094001c0c000c516910b44035540e00d18105020110030300804038001501804444094203d0f54824500c03103000d0b20b41040c803440394005140030131116440e141084001100d5030005e5200748407648001816000c1c5a000408980031240340110b0403004001029007690790400703403161b50140440d110700f50 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 781148857 1250 781147607 781147711
    0x20030706090201111507110d170604111201030201031107330e0f0d09060f1103070204290901120209060d020a0b0a0815011b0218010b090306 62
    0x2a0f100846034207a0b00541e8201e003070181c018400c0354000d403d187d0b606108003940088546d26422034401c0c0c41c01080d602c001c41e03960703007029410300740c1e004d00f00a00000b08100c46900f4140c0c00e80c0710032641c0c40120150401031045603003510038505042d06104442d400d000072991509207210700d2040d000b040e100e14100e005411034a245c200c40107054880c0c8207001c01c1c0e00d440d1640e0342d070b61820800d8000d503004601145d6640d81c4900d01c001c08884042c1e90b5000070b24205c1c83e09940890301c80322820700c940000c01c250400f585450007121080d007200c0c04125422000441001c0d1524091151144540c1403070004101c07440b002d400c61500d00750100e400b1a420340300e0700d0009000344945600250040c81c041000500c0c090000050242d80a094480201c1b82e42d800c1d41284141e02000d070322a000c070b01c07200c0c4c82c0380c02c5400c0c401448910600c050f081c1c1d201088607614000c00c10702d0903030120941400014101606080c24000540c0202701d154403130800c0e00203482680c19082c00c0d00c2c904c10071200e45101017011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 781150107 1250 781148857 781148867
    0x6010c0c05060f041d0906010611070b0324040504050d1b050706050702010210050108030706020304051e0d030e1603020d05030f03040606050f0303031006031e0f05060120030706090201 81
    0x140802819079585805420243e07425401034414407541d800044048610710680e6036169104500103400b0b00500e130b00780002034592900b00d462510140c4038500000c07442c1d030a45401107001d80e208002a444413803603a50311903802840007103614059407c0206110000c6c41c006540c01c0c400e251070818400401200b6601e50b10300540d41030103404c5105070000001c009400c4401409800d000303034250744103001c0581680d07058a83c00c2c07040a01e03d500811640740456401d602664100d44582e055035050780404191b0302c43e1216404811030356070800000c600741e20b9014800e829840c800071014140020301c4c042c02303801c00344061001030f004101944041c03003040700603c11500e411513401112a1607040a007000030080410303008243c000d0381428a244110318001065034071502c012020450611b051110403809000e40c00182401c4104800c0a100c1c015072500880c0b940c0000302c0070001e03407440c01800042c06000d421603c00c0c1c0042c0b080000d000c582030013204681d40203410000110f001403942c401207071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 781151357 1250 781150107 781150109
    0x1e060907030e0709023c07020f030d08010611150c0a020124030c05040e06070e030708030c0303040b07050306011e021e061b13140f030d0906020d0c020906010c0c 71
    0x440d0380204900030030611060750150582c020200d00c442440e080c03e040b100b03002282582c5c4c4683c846c440070f1110031004c100500401c3e5251004c3c0012442c48450b2002ca4944401d0710300321804030b8050001400129485000e400500c1000001401c210100b024a000b5201c405044411800d200280301c3d81b41d24000d4008080314076403611096800020f12021111203a09404122403a607030202000481745828064091013201800140009881e4110180d070030341c1100000b19003501461100041d1020144041d00001003d480070319130f04d1515150819a681000b810001408001c0c024455281d03030003040c0c207145074a10148484076011220050380750080d585000388140c4201c103140d00303043c80301060740d9000704140d46a08802c04000c0c03903031140701d0290360f0300f94414100c100410450303011a401c00340c0c841900030740b51080c081c01e10710119003468a00b42800d400305c2e000410401182d58100a280d04a400924144403a510380d540040c00c002d0b0040d18450411107680c41c50810710102c480701c54 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 781152607 1250 781151357 781151381
    0x109061b1407230604031101060e01060503090703051c08090106080d110106090609020a080a2f1c06031e0c091a0a09060f06050c030d1e05010801060e1e06090703 71
    0x22183d007441102c0b1558883c0121800c03000110724a11600102505024541c00c4d1000000d9504442c2e081920440b8290802041c20300b03076100d508030000c08070300244425602540e151b00780d4007181d8620b00015010400c080d02c50025a85480b10400040d90081145c2018222030310307040c2541c8012003205030140000b0703040310701c842e4079041c1b0002e100d0040ba401880c07007014948424880d41ea035100340b81c048031010b00c03c47c80040c1c5411360402041c1c0300301c9a0340c1036100402110f40d040c48980101c0342500642c04c042e0911503684e8400910902080b5418145ca511031030001d49020b00081d5105a000d00d2036100316001142c94010440c921a20034004919090002d012484a15542c29808001d4681e40c444ca6400314942c130303c0802c2d214415802c0f5240607859038010b51414000090b036000800700c02e243c035002418a41d03540038112015002e104d008000210010419034180341c800501c40d5000b07010030085104d102190200202c00070203044d80b1001c1141c2c01c0c3c0a960b2448003c0c1c010b0b10800d2170798 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 781153857 1250 781152607 781152653
    0x10909030c120203040906270e100501031b0f1a0a03110a0207060e2e090e010f0503010606030c1d130e010f060506120a020d0b0907020109061b1407 65
    0x102d00060780000076000322042a13205100303959907000c8000704440601300305100348514140c45105003109401210003808442c00712410b007040c2d040007000312002a0400c0b1410000600c42d50038811503408004090007100c000f045009207010b03059214840700c803821311b070801404108020340364029480103a520608103840766a541d0350400080d107551141c0126800f1502c070340021003990415400c04011410a03501009417520080444000303040c2c182c0c2c0e10340c200b00c40900085201600b2403643c2d40201ba00c0343d01180d070241810105829546140c1103d410180f42420409005920120010b0398108845404410411510105402d21010003511140c0303400c003828141001c0e41588030443d02c0719241d004001700e40d20341041054502c101140880340c58000f0f0085036032031050354010450b10f000104001100d0501d1760203d02c61030707411200540941d41d140030300c500740415400f0301c05251a42100360002ca140255024011040901ea03800447d0382c00310f541340800c0803917032040c2412108183e01c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 781155107 1250 781153857 781153883
    0x60a091a0915031e0312040c0b1611040203070504030f0609020616020a05090103171c0606090333020d020702030304120c0614090d020103020d060603020d140609010909030c 76
    0x241c040848400314078002d114903140c55130b201803d02400a40c0542d880007840c503000c4103035445a82c44401a0080d940a4980000095858498802040300700d0f041c0f01d48004040e8141844001c0340d60a042141c00340307004000b04401c1c2d960000890302925800340006443d00b03010f09003400202116070b8000c3d008880011121413121680da51401114821138a21400c1c40d20703082401984002803000620b41d1801c0350b145040030304060702034803045003520500a840c005114010080d03441c65406031010441548007801401341221260004c101101d01c00c1c0e40070311242030720403d480c06000c41c1e02030311031f8040b03140708001613180c040b180e51680040c03c8031f8940713813100750300003030348030105c40c1285c00700000c0c28005074550240514503207001c90081ca080c2013480107002d0184103003031618120304050b800c000c415075102c403a102d002c001c0c00c01c540d40162100c24080707524084174036501001d102c261b09041080402c5e5a030002c1141901d400f4407011450480c2454140c90140c14044010540b000d0581 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 781156357 1250 781155107 781155121
    0xc200a030b06040e150c0901020f190b01091802040e0a14012f1e090d03030606090504060e151504080303041b050906240a020307021305060a091a09 65
    0x1401c18081c4104407070410440b021440c0c0c0a40da13440350381c07120340c0c00c12440001660a8100340041c10005c401130040c3d9806001d01d20f68917040203003d80100c4800042c40e0003d03814041d0804103240900102e800400c5000d590b1b81c11000305124a801c028402c98a5815808041c0c405100074001a94800c0054a4200350322080b14041e1051210841d0b6510482a40303c041045a00c3c02d15008140c142c01d291070b01003007102c400c80302158864031f07072048442008400700c5912600040e641041c06030f44c0c0001c403503041a2004140314000d500c080e12850038a0410f101410000d0039894101c2541170340c1144030703025000481c0051920710810702a00c4008207001410000200c002c510503803040f04808041e0010712200020021140641d54100307041c0c20021350b0a05001c1c00030555100983c12100709010560314044003a88051240d000581002c6801401c40c01c040807920340040000f2801e0150b817600e0004031b040c2078070300d00c0303030f04426070f200c1c0c0404481c400d01d0510611807070000340401c500c600d8100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 781157607 1250 781156357 781156373
    0x314040b0c12031015030b100e01080606031e1801060303050c01050a1401030b041703070c0c0518390403030e0904021c020f0a03030e09070f0c200a03 66
    0x4076681645002d00c1a00310b4810501c101201e1041c0b0070140c50301461420301c0100d00c0c40c280440c0300c0f08141a621120f03d45c5a5507040100a90081d041da1440c010201c40c000040805001410780d60141c031081c0103010400f01ca001c100c1c4440e0305480303604142540c0c2c1c0c900d482d01075114410f6000f099480c104001c8181035029004150101c0248028800c68440410200c200d0b8518982d00c9008030320240107100180910004503005405462203103180c003c80036410086030300a4071450041150864641c04100703220303040d4030080c80201c60702c0341c034520303404101541c90f03000406030350542c2000c8040c060200d00b1004100e0140740c00600c1c1d014081e42403684c800c03a95200c1d0000b940450380c00e0003800d5040c41c0c0804903034441c1e5405004e0858110114071450135040c001c400032030344000507043c22000c548134411881c000318000c0d520b003200c56440c0b1062103402d41d0080d0000040008502c1700d608042d4125000c1c18505600c0310260111490400310481800c01c109440c4d0b0b0310455a10300003090084403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 781158857 1250 781157607 781157617
    0xb0f060c010501081c210902040f02030a061205071e080709050703050606070203070302060a0306270c020307120503040309150905130c0806041d060408030708060a030213090314040b 80
    0x2141103500c0e1484688140e0a07075000645064000b1b0f4200000c02104005058507104010710041c0100c2c11140a600060641d0b851a502c0031200350f000c0201301c4902d105014101c020b01c0718254a10068a064860503116031a0340902034510f03000340d8007041a00045140d42000388420025140b02c81d407210010000f51034151a03100000707041601040c1180f41c28404c4440c01d95009004249192441e030910406400c2038210000f41a51840e0000f201c04040030803183e017007940a56000c000c1501038101c022107400b81c0303000046500030b00c0031400186110300404e101704000d040181d107035034132454202c85c4003010f9004105244900454240010f4014522000340c410881d035824588000749580e9080321020100d00c400580300300c0200d4000c0c03e083e4002030501020b8100c0280001080c9025407401c04155421507161900108001003a54410302154002c03804030751a200691441c1c0000302d2003541d40c02100c0b1440e564420200030580a000b82440445500d1840c0785c03120b40d5100110300c0754204d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 781160107 1250 781158857 781158869
    0x30709091e1a0708090105072f0c1504030203150f07030e01020706182f0d02130c020303180102070807080d090b07020d08010803090d0311030f0d020c0d08040203060601030b0f060c010501 82
    0xd15001c20b9165000700781c08581c0600b564100c00e504411011808030181d1001c49c0d1950f58051001d55180355124600d40f082084c8034042c0c11039403146903206042c40e000400a0b8154110711007014024020400d4100c240c008000e89800304944c50020400d50081c428418000e1a0501e80504041e45840c0c04420560342c6000b0040e580c804d80005c2600102801d844001c01d9a02100e40380c8140309182055066600c0c2c4e0010f0305450b10700400044030011140e00300b645201503400030080200403401907580c0950025060025801c0200c540e9a00e8064042e1020007400101c01003005400410180d03c0f42003d240c0285a00320306050480000e501e031001c00e42560f0000f00c00c180085100a4000222010722101034442c4c6a500c0081e141114032142d010401009800300300800c0ca502100740025101d0b40c2840342005985488a10400740790003510700149007402038240402000d40d40c040f5030340d44d01220a0801055459000303000a00341050003080c25404000828202041c400550009069a43c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 781161357 1250 781160107 781160111
    0x50d0b16030506010e2403101502031309050411090a0e190209040f03050c01020423030609060a0b0a0e041406010806040b01060f110318030709091e1a07080901 70
    0x281010120141c0e01d080702e049012030170b16003c400302d5003071008580c0c3d038442c1032a1140301415954100d401030741e4010b607450b000300c0c0b0000c5001e1200b210a030224800704000c1380002c0d803401c00c3d00d01000b40700c0111481442c0f4400e40e500002403d020540c400d0f0302c000200182403100d00d10f00b03160759030010f041d564915581445101c0390141c42c2d111084411001c542c000f001c1203900d0760f96640b200761301241d2035000c03000c01005204400d2411000d002600c0649600300c03120070b54814142c1949901d415480e245442503212405008c1d4940022948940000d08039402040519039080458a000c1c41c3d68416031114420004200074061601e10368085d940701502a01c44990342c5603c40d035910038082e200500407601001c0100300460140c0701c0469003030b45500346442900042d00074141503401c1041c0c044910414258402d41c24a802e0002d20050003483c2400c10107100d5035214401c8160284510764281d5500c60644401d0000790303d5040180024030034070381103a01c0d01e810003c000b2041656204500e42c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 781162607 1250 781161357 781161391
    0x506072001090b091b0f10030905030a0206040203100c0e0909120708130e0c040b03040c0306140702010e0303010807051903080f071a01060e1003060b0a0f0801080d1710050d0b 77
    0x90a01c00740c039003403c00511b0324090080e900308210b03020302d80c5142c46d81410365035194500050f0b4140040c041d0096960098206843d041c010316042120000201600c2807500103c00101c503009144890300790f000b41e50761340142d0342d0004050700e05020085400d0341450b01240d0b1a080285480080203c0c00024400360086603a0700340030306100800b03691034111003070117200501c2100360300c1000d10747c454000d0800ca050030343e50f501c80030708883c40381d40002d000c82c0c541002c0108442d02406019945030071940158a0740d8503010700c25845800798056030780b02d020308401035150010201101c0010b0f5070000b0100750f660315110328540e6164001c0708100c0301e010000080d2000c1c905484d644904a0719640c4550420034141420000c21444125800c42491394444010074046034400247c00e80f00203544500c4102e414502001e00b00c50816802030815610002c040c46043e0f6102000d02d0030440f407901ca208807900d0342e42e0360404400c51500182d8024513420b2401c1e081c403803040d844a000d5083c2d1601c4140303030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 781163857 1250 781162607 781162633
    0xb15041508331012060e3c0307050f0102091801050a2d080d0201060e13080304030512150f011b020f130f020c07060c0506072001090b09 60
    0x280d0a609280302aa110b00070411000c0704010300e0381c00f8441c014440215500c0b04480360f841e00030f02d030003502c100b41d0760111280c405204000071511000f601070700c1a908814041400c00000c9504610401c01c0790083d201c4409440400c29502c034250722005076901c01c80034200c02d1b07000b500001030641c0b041109003050b07201d030941107054034180c82c0050032200849051401c0300c445110714204110028400d2801504840801d400b68801340c0f2048000e8045330b040307440000d003560280d4129090100c1d180050203218103084400605a503403000c150394880e0341c2d034141a00c80e03006400a084c0e0481946041142c00b16200318082d100c448229610810729200c00011501f0848441034400312071491000000945045405042c650b0030081c449143c5001c81c021003400c1c0c03590200309049068020070100280d510a104440c0a0004c07460001c0b100b078020b40b110355030f5400185c81c00c1c05002e0083d01541d4203404c01a9101860b040d600c00a002541462818400f03100c0110b4980b41c0900548480102c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 781165107 1250 781163857 781163893
    0xf030221070915020d14070f0f030806030304050306180c09190f0b060d0f0605031006051017071d22050901060b0a030e070509010320030a020d0b15041508 68
    0x100c8069a4014014072034000401d4941c0c0d6000b45602a0381c1b582800788900048921600d8480b040c4a001e41d0030182801c0d29001e008400f0241055119420610042c405520b0006005a101000103514003160100b980800d00f40a4005400c5400465040070000500308070070111000f00c2c0e901c00c0800c190054900341504407804080c0440d8881000c210152100c080c0350031a02c035400c0e50381d1000515a9031840000d02e82a000e8440b842c08580352941000b0f0703884c04400d200700d0070031141407459003015000c240d1010034100500c4001404405040070f40720320a010081e0f02d0499000d450107500704103040120304000e00b0313890a004135504160001e0301049c0d040c0604070440c0c1d42c0c140200c2c20300501e080c0a501603c800c02107801d1300c2c480c3d107100260682d0355005141c001c0d03025041e0300ca81a5500080e88001e030343c14860390303030003a8040004040142c5402854003a0b05411503540342803a00c52a404031188018039803900e40c03150a264044008407413100f4104212018030046038102141d440740301c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 781166357 1250 781165107 781165139
    0x41514030307120f0908191a0705090607060902040504111f022d0a110102071a07240c02030a110609070e2203210905060105010f0302210709 62
    0x301804062100c003c3c3c0350f014481110700c1c2901c90034000307450764a807000c05242404514070948004420340f03500080c020444001c7e261810030f00c140444610f44880090038500c10f6030f6409000c0c10002410340c0500200d40d210480700b650007003040c021400c203070034000782c0441c124110718411a90703500700d03071421001500303070030044880c42e00a8441102842c0400708002d03204000e61510ba108000d0783d090f42c0a0030320102d80214450144901e54140400c00245401e101d900b24200364074200c600d0101c12401c940903a240310354071a90509085d40481000342600b01814480c09299041c800a0904583c0101c041e281e6210f90b40c2c1c131400e20b840702c100e80965071842626418081e402160707083c00098590307500b6a82c0850310b01c81880c0c40d40031069000c075985003107000070340001d610295000d000070301d0205c150303040144003001031049403169225140c031068188034a506100920b1070b508625406901951082000440803c0e2031100d2000d0038144501c0c21070f5800000341e20301c0c001142017042102189 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 781167607 1250 781166357 781166363
    0x1f092012010e180703231612062408010e07030f02061e0f04080c0a060f23040803030402040606020102070309030b070c0c0b12070e0f060d0b041514030307 68
    0x540e00da440c0202400000d240544003410202110312490940c400800076500218400d05500c04280c0f044050361410b81c80008180c1000d801c2101d048926514200c4c041068030341c1150005d05002d064646600180110100c0c0300b100c1c0e45040041d006c0c001c000c0d0040c2c0c00c94101c0c40082c050000da802100b40c0341c1710395001c002c1010700c021901601608250014211514100d000003c0381038a4461882c0180c00034912042042070004041c05258020700040c241e0304c80548054043e0b1b410b10034040d08440d44c04044104001e080c0c88544582c140d40b9251840b0746241a4845a40b42d40782d44206c1d890344e1007120141d014a041020000c0c1083c170504c226119a40c01d81d6440013110b085035910f03a00d08502602e544100f050116070440414003010780700009003034170925241d46039a4075a4294082100810310740030301c8035682d00b11429864100491150303030400c07100582d403800c02c0c900346001070452041e0780f6003061030100c0078010800c0f1100180103844e648000c8010f004030300c0003003690303d01c41c4010007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 781168857 1250 781167607 781167637
    0x3010602101e090f03020d08160f1404120c0e060f0d0602091804120c050607030b0105041203050c101109090621011b03050115081f0920 60
    0x1c1e16211101d500c8840d6a84455844800c1a507030080e0a000703850b00044242d44015092014000305a010010b1641c0402a4200b012143c5000318440b41e2002090030741d4803d0010b18095100f00b140700b25614512481007420268507a500c5030f02d000c03803d910001c0c0444850121410220b0103078040b40ba071511a803001014010340d4050701040c0241022108411214a0f03001c1c440d201451b40c45000c56182d405010081e081180340908022086489400028081c4021040101c1c082000460764951214a43c240851184c0c0094012161752046038040908260080090400c0607400b40040403900240350031902081c03900380a6000f103c160030030070120940c0410407880207041040701264040c03c002c100480c001c4541040f03142a202444d000050342c0d40d280c0700303441c60840741c0d410f2410107580c62404100c1d82d07050540e511001030310000f4400034040e903040000c841c08801c0807041550102d04003588802c80e81c07031020001420014141c0345512052344008006040241c094555a030601c034a1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 781170107 1250 781168857 781168873
    0x509061b0c07051210021204021005120a0b0a080f1b100f14070b0f0103060f0e1005101703030610110d0e040b03120915040f14130e06060a080303010602 67
    0x8204c07540e020b44c07184d40224003c111990402c144144060301001c860031002c1c0f0000c2c82c0500c10402100000880d1605201d81480691311144800100c264899554640000c06010010001e43c2d4200d255004035040e10034040c034000803000202c2c480c503801420410080c0000c11b07007810040102c01503060b40300095541c001c0c2032015440b6080d01c0b12075410380711041c0e18224031901e0308801044100e4a4070403000010380100208800c9101e0080300b00303400b40b01040313519000a4032a40310000c000d643c0310199103440100b170f0308010070b000d0080248042518400c403030f01c5600710142c40350022110240300b000c841d540152480c0c0074840c0196034580c280f000d48400e88044030b040d2811408025002e4000355161094034107510700b04888a0308001f000340360390319280e10804000007611070824105d1204010b000400043d003035131043d44203507040351401e15004d2014101003038052214140200189042c108800380c0b071200426175a000d800181c46144205880d00710340c50352403000388584401a40f040c1c072 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 781171357 1250 781170107 781170109
    0x9040624050a030209060d091202030906090904020f031501030308010503070515030727030506130c0e070c0501060303030603020f0904150c0c050f011d0d050703030b0102100509061b0c0705 83
    0x2860300b00c0c01c070f0030014180301491021035502d070803240c83d52041e590b44550140a011600c6000d4070014114030007186094401c0d00441d06500a03032074903601406d0720401040c210f582d1012070754040718000c3d046030aa0480006007600d00300c1300b88001d401142214002240c0c500b4041030100039100e000d860401041c49000070b03000e0b07691009000303a042207400b81c15520b594840c03091000d4441d0510b8000000c550540c00d0940c06c0c100c01521102501400e06145000121140300d004226504e03804400d6190351005426144080204001071aa5181c040040109500355100f807060b81d00a5480d000c500f4194410301184002c10764002c2c0688070751540c0586480c4c4150440e151001c101c1c0782030328040d0a140d07202c500e00001a07030810816515000b401200d0200381c00c42c5401d0008000040180d51850038014100d48581c0e400601003545444880c26140d00030010003040d0f4080600800c810b1502e40350240d19460250352240e40b111001440c0c00c00c0100400a80b6003540b242d802030038107280740c18 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 781172607 1250 781171357 781171367
    0x8100617060603130b04061d011a01050307121506110a0203150919060b121f150806090106081c02150a140a060614030108100b04110d0209040624 64
    0xc04d0600306903080c510035400140d01d00002070245118410210b4600d0982c2070200100201d007a03070040680c501b0314003035151441d48401c22800582805d0140d5282c480b52001c507901c04800e841e8048140c1032036440d4181120790301000c402c42d02141e880c06d254550414000d501d500c004170001e581503201200c1c0044902460521540120300d10040300d0b0b80415442c0702c0c80311034020007000d440b03c6544104041a0741004140d124030071070100d0107070000303091425080c100c130b88154040d401101da0710040760400b0010a1882c0000d000f00760111005c07071806400c440e0181a0a026100d0b9600a1301d02c1202402c0103004201810072140e0060f00038110851a0318800030001003044d41c2e8951201400f280000784d51080c5070049d9600800401d0050401308090001611034401c5203480604200402c01c4000c00310b19540c0d520100407001c150020820b0010340034240d2110404c07401c036000511885c0000041d4010700005200b502c060191a07941c0092100d003094650344d2683c00000d0f40d07000a1254403236 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 781173857 1250 781172607 781172611
    0x50f04020907210b030c10170912040308131a040513110c0d090f0f150207050a090b1305010f0303141908190506031f14040308100617060603 62
    0x61816290280045100504458050f0700d114009955100ca41401c1c1c10305018006403140181d581d0069060300f801c0081c444105000c1c004ca07409040c10200d4402c0606000315404110038003115a01c940e10388c00c10607201c1e030040421140f030b40083c041c00507140426041400000d504501c07034504181c5080203004144445107044005140e4a282e0207080d20303c1540501007140310740004040c00000314502402c6814030b03400101c0c544c09210420000c1001a801580c140e61200b40c9406201e12990000c0c2c0ca0540c098101551044a0074400b00d880d00d415841114000070844038482c0c86211040c42d04210352003030080400307010f061003082c40441d0003940d1190700710a01050892410040b61903948001aa40700f000001a401b1414040030b405000d01029080b000c40404010600380b5000003980d900181c41c40d03110417001c10580140c0120315030300001002082548240c1207260600e00140406401c684e02102d00c140a100401e0552055108d03908201c1c0360008031160341c4409040111039080 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 781175107 1250 781173857 781173871
    0x1a06090409080409060312020f060a0c0e09070e040b0103021315050c030310030209070503090a021201020c06010f051c0c05060304021507030c050f1626030705070513050f040209 78
    0x456040000182c0c158000b44014002c180300000c140d4250300e00030042c1400c44500404550040300134071030010020420030303009103d02400060b4401c81c0a0151038a9940c2111107512150000800409580203e100c0003000c5013102c04016180c03c440041d03049025104413a880035603442d0050002c04410034860100032500c1c10482e0905010b4031031070385558400c555031511284501010030450500c4040603070056024204541545003540c5c446a8480551901034810740d14541d140b03186900a5044801e000d80d50001c0e10f00a40c1c40c0c0b58251250119441003900400a80c126210364000b212515032400d44e220300b12030f2a20345080c04104c80ca800143c016a13002181c0d9400030000740e5840010082035100b42c1711510710100f641440c0d0305183c1a85aa9420b0b030f040a03c81e00c0d0141420344c003903000d0319461185803070101d0440c40d02103003c1e84c1008031048640310004800080c8823000a14404445c01159003011801c0042641410b94200341d494002d03da4416010600500d41702d1203241d8400c172 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 781176357 1250 781175107 781175111
    0x3070809030a080d020c010b011412040311011d0d1412091002070b1005060a0f03151205031905180d030309020621150612130807080307121a060904 65
    0x103494a80f40d9601141450b00155400a1111044002800b400f40d0590017400c00161624040644044500c954894000e100070202e000401b010302a40c90314151030007080081001c1c00c00c0750403c206008400141000d0340c800c1000c0540c0380c500c50101c25408025800341c0d039044c40e44042070000e000002502100442c0214040d030090082140701400301c15014030100200c0e42021118000901c40b035070822806004100301007150340d40c01802c40329448220745000544484000c00d0341a5202090b002074005101800c011024050000058495000b0350381c00720381c445828800646035445000c501d200d103c05112294045440c205c5c008045290203030030041040110780e07000a8050348801c0c0c5022007d24075082c0d8401716070111450f140e020049002c204440240440003036100d01800d201d152014200400241032414400d25000c0b280707601000c0c2d182c030f81461f80350205168004554840000c0c4154074001e2000160740226945201144d04400ba0784600c0e01c14421036901500c14542c12076 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 781177607 1250 781176357 781176373
    0x7080a140d0903080604150623040503010903020f1501050907050c0a1b0f0821031e0f040b061903150204050913020405160503010905060d120e0301110c0307080903 72
    0x6020350080341c120912a070b50b03130074840c9099030801c82258605003060741c03050442402441300b140c00007004c0516800c010210750704114030140ca804244184c1e00a103825508140c2d00070308240d00050f501416a41860989000910b101c85c203031600e00b024850306030310044880100c1d445a0080008000004180c0240c0350344417560b13250149200f4806a0240c504580000d0410445030a45242c101400131100500300d15507150907010140200044012202e00f0004007143c21000110b141800205160861780402c0c170304440315000b4182c086500b5280310b65004001051450104c41c009416441c04000c0d804007400e41e145c0301e03103013035034102c001001a40c01c10010440e42c3d50100c400348103038140044c07881080c203a84144802d9420141a4004e2040300d00040340b0076541020590741034a90307030140000d55540b40c1000600340c4ca05003101410103040c4200c0030402e581e12400a01000d10264024880c426210951035002c0c860440520801e07001844948001008080103190f1040000c046405007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 781178857 1250 781177607 781177627
    0xe071713150203070c05071a18010c0f0f02041116110102070f180c02010509030f1e041706010e0112021e0909030c0d0801051e15030c0c100207080a14 66
    0x3d80c810340b40c50f00407464480e0782c0410041e040210502400e0180d17130300c7e40542d2503250f0b050740383d005400314503400c58040f00442095900c1402107200340da0b0040c808950384545400c04081d800e08845090340070390306020880490310720100031100d012421800c0382e00902c803140c0f103480c00381c9220100720741180150b940004548100207455005864202e00321468415290245c004490103112840156410b0408001040c603020041d40d13045a954021159602c0800c2d03046000c8085180c0e26a0f80340002040110b601c0d445001c0c000110755110741118100c4e6203450130b03030145103024840c0c00b041085c3c0d04110801420400191625090244200e40e20198030800080c001c840403600d4032020341c00442c01c0c040f981030410100c41c031405142861f1000394184400715003c00e031164256a07000101d440c0e6441251aa1200e51508240000c080d580b46d08090340c000d040e503440f90000840d2032143c1941c0c22200c00d0750b0b00c01c44840c182c0c0f008134145403511052040e1800318042c0600c18869405100308554 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 781180107 1250 781178857 781178861
    0x301050918070b0d1b0c031211030f040210110303060d0206090603090a21052a010e1e0102030606031b12040503030a0e0f1e0a0204150e07171315 64
    0x98120001c8090304d440c20980140e04656070582c0c002d080222000300491a20741204142d1009600762074030081480094020704060503004445405001000041040201c0c1c0303001c0b41801103208440300c0c0c400c00341d016801c03141082d03584040c841075002000411313440e2800301344400c0464400340c54242040a13240000b605030300115810401504148140030410501e0818144046d142c145074482c10448000c2c02042402514032107000d082da24240d548800401000e0600c00d1342410300248652101880016241c00b040c5802480c105445209040404410700a4074461907018280ca0b00b1a907803090b290724400c0a0a803442207100003040f0720440200e603810120f10940c01900213543c1c85c140700444404441003880d114000303400c503022150000e000402d512101540010048022614154402d400e1184802000358028580410000010381140d49001200c07220501d0f600980d03502203080d41d842c103010503254110541800060f5400c01c4001030711196a005144801c4100501e03910401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 781181357 1250 781180107 781180109
    0x203030c0c12030313030806040b040c0e0907020d05030a021809010b03060f09061e040b1305040b0903070302072d080c2d0f03101409061605030105091807 68
    0x18540c100d40035114040c00e10804900e56010b40e100114070f54603004550310700030f0050403001420030000c0408285660740c2da410490000c0401401000b05049421018000000c4075a001e801044e0f00340c000754185002180c8040b9105858443c10325658840d8002030095205552000940300704041c418695207614a006001c0c0c1700124909030b481c241101040703c940d00304100c0c1e41c0300760174020400409813143c0311262a01c2d130311078100414580d644400200500a036109064205c1078009a1001440e819080a80a05d02a003183c04a81d210b5444440e2688650344018000d030740040d008010001c00304060001c030324880d0309803031a031120403848c462602443da40030501301d500c4001d408580e841c0c00d02c07020500442c130301a40c0c1d00110f2102c58880320484071015080c0309401241c102034180e2001d0004034580e00c480b400803c5650440c00303a101c2210800e881c540405d00c1800300185401d4141a41c1404e145400d48940e03045030700e000308200e000e03280104281000c55a80d0800d40400760b04003e41c02c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 781182607 1250 781181357 781181377
    0x705030115140c1504110a030c350d0e0a05090c071707030c140601050108011202010507052d06060a030602160615052d062206020601050a05032a030a020303 69
    0x113641414180507032800003003113641c0c0c0b140c810301900b000007544a0000104407202442106440f180c00b400d900c3d0450440d40c140e03400d00c040c0440c1c44003004004204804500026203900c1003640c80f4100340100c400240c00b48c5600031082c00c0201d2000640e24001c1c048040c0b0907131a0010001e10903250907a60b411109040700490b00740300304034040144c1841c10034400740700c000007000250b00d4200001c4c00c0480600c502d00703202c504080c8010035a4410000ca07442c4c16003002c00ca43c05100b1180c50210070f945065030480c603413950301c1081c000c5c9050125a950056400420102583d415912142c00035405082c00005076052912603000142d83c81c000c3d200015007444289000910f05000e12491216003840b8010b0b5500c90b0400c80e03000d07d01e0f4400ea20700078100b40c0310542c13900e000311080d044400c218407400c0031104641e0070004989a000a0207070503184190b070020700c3c3e0385d900d42c285a0707030314002381c0f0a001c5000c44607210103242c5500300d4403000031a001412903518252a030080303030466004002c80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 781183857 1250 781182607 781182643
    0x50904080706150f14090117030705010207152a0f170403120605010f050f0703090f0305160b07050c100527090106090b030c070804030b09060a050705030115140c 71
    0x41100b4031100040c80c1c01007107a194001c85c802c210303900003000503c0500441600d00c0024105660103001042a2050264014021550fa00040c2441d03480008401c110440180c1030403082259149284005460010101d0b03805c2c0400c03000c00c1050350f144025220040402000381c11207900480003c0d40c441c000c9000c3c0d20384a421072080010901510b0203500141c0c1881844d14550689a038420f0417299002d10b116075040c1c417014940340c100d4403810964000804a0039020001c070600c4404103140c8113100c02c0122b000c1203241e44a206140c140034a00700036055820506a50f00c0a0402040c0e015951180f490540e06d44000000c48521003680540e42022107009001100124103210100b2800746c110f81c01c2c051603035450400380c0180381c400200007444050011423880c0c00c202c40d1400380c82c061980705204070709074503003400c0040d5605000c48004910740d0515010034031b01d5000e501100c1c16144030405000906031a218261203c0010322b5400c030700407000f0004699180400c1c00400d0700c44140442c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 781185107 1250 781183857 781183859
    0x60906040608091605030703141606050a02010e0d210b120c0411070503030142020d0e03060a0e03071b0501020d031a0108070302070b070323010b0405090408070615 72
    0xf101d440c1a0b0f281c5a120b51100d0140e1082c02030f43c1d070006940c0b0480b42e1201000c509080c0300082076090a40c0b0803c100010028a000072614030b8020001e00314070610f5900820203400c1f1318440030342e2045130003011800302d40384441b0a4600f6094030044158404e5098010405640345030125440c02c0e082c0704508d0058000b105081c0061404c1d00940c4c040b1215041b1303260410740310380c0312113031284018170405034501e1242440388000c01d01d0b20400301102c40b014000c0c442c80d003100c041100e0b0010300c2081501c014001c0030858014a070107070154926044026004100365039410420400821030240b03107503603a1005022060005844a01c002140028017a58102070342c0b4100029141941c0c004410702410308101d0307810b42c19121028000548d04091030000c200d600e60a4058000340310307008000d02907410400400020a400d81c000341003807148031060145100d0001c0001d00c00040038019643c1e400d10400082209143c00b0700c00035000350042001903c0c2440c2039036007104072450800c0d40c103800007241c10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 781186357 1250 781185107 781185121
    0xd0b1207030c150503090318011e0201020706050f130b0601020c19080106061b060b0a0503030316090902040612050403090b0403050705011b030c02150c030a11070b27060906040608 79
    0x80d41c2c42c060f0b00e081450031401c00a0040c1e03103d02410ba45451104420b10310400241c0c402d440f4208001c2e1010b0600b0304090b1580f2000b0702071340c00354809448081c1000c010520050315104042d100742041e02c0c02c09680185951402c040c1c0310041d04440c110711a00c0c04d980aa5a0f4001c905405400861001201c0c0342c54015241d007581c66552040083c044247d4485400c2e8031b40b00c18110b01d60781e000c0d400040f002000800190018400d8000603010700c40441000b196941030303200c425801c41903842c0d1030343c041d03130b100255000c0c2d110398059a07001805525a4400d40e05080d0405a00988a8100f03618005e4480d0450f1190703401c203500c1a291030f07019070010441780d6000404861100510075405c13056240c0303a18050507c5a495800074000d100c20326041d041c1c4071001c016144c00614000541b40e84140102000300700e500e40d0f0303661001900a02400041201c805000c8401e042170803494110101c92102000302106d5005a181c0d4203d0030810845031165152402440941015142da10b21400d01171 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 781187607 1250 781186357 781186379
    0xc03080d09022e11031c15350a0b0c03100b0901020a0b1003050a050709060608010f0e041a150a090e0616030225061503110d0804090e0304030203120306060d0b1207030c 74
    0x142c42920410300040c3c1d031003e0123410b0081000c1080346900c102040310b0720700c1c40c214600144034030080c0c0300004010501c0802c21107200290b001d54800000080c10710b44030b2403900e00b288149050140076900400c180f41c000756640032540d0344001c1d0540b480a100d0781d01c1d200d03642409100b000c200c1d803503040b50344144208060f40c4101c0c805800e542c81c01d01043c0d8100b000c0c0c2c54000b012400341802000280d0005400c00048044031055844528003a000078103100828032201501c0d403203036a12401e501d0710085006062807181001c80326002009160548454101c18032481c440c01c030400406400300102d10200400801036001c08103040d1824912110b1418007404460030100944d000160140301027011590442c8030380c0d00850200c90300000b802003441c090600348510381c4144211030802c0c0c0c0d0300902d0b18022002d40100d074000e509072114101d40801c01802c500c011903119a02180c1800b282c1750864030f03580550074098001d00402e00000b040400c203440d0fd07401d6402150418030100382031100c40920 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 781188857 1250 781187607 781187609
    0x305030409051807060509040f18060b1e0a0603090f241109010807050906040518160c0c140120011b0203041206090c03080d09022e11031c15 62
    0xf00000d801c2c80c50030440000c0c42e5106401100e4401d94482100c5d1000402d2a8030540064507011996868141c0c11b15020015011001042d0300c81e1034100001000c1103517408208001078401801d03079913081d09200f0b0950041800b0b003001c7c1d0360646100715485c00910344500079810700a207d05803140e100c0c2041090002c1c0c8070904951030884006001ea59030b60f98012981540210081c1030480d02c4007501804104180030350362105a1041d0342c802c0070030009080b180d000303010345890064000394a40102080c2c44d5010b00040c000d00345808050704102115910700020001e0700145001030700200036030301a805640f619403140742241d540b65003c0f14249400c08080340c516240e4001744d402d06192003105003031140f07407400c060070742507c600500e0700b000314000e5400091903102c0c50158403240c0402080005200385c00c0300324014007102110030540040f2a40c40100079044007920112000c1ea21400c4542ca9199450407080f803109200c9004802c00d030290b495600880c07494001815480c000d0034800741c10301 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 781190107 1250 781188857 781188901
    0x9010e0c19050c0c1c03201504060b0f1005180405090115060f0203091201140903030a0b060708040b0d060302041b1202040e0115090b03101403010e190c030503040905 73
    0x1c01881580c00d4032103200020801501400c1c90b218904910103c2500004881f055150074040d0743d00100704150419200d6016600801d0100440d00311801880010a6401620390780b004d10f0110700b0500c0c03841940200340f07001540c1405c59582a111000c10140c520645000c0c0c0165112540c04204d0324a185650004088a00d4000c032100c00c0140c0103034807886007a100383e00980c1100f0080c0700348482504041c840105400e1009080c2c80e0101246032203800a5030221112800c141c4039045500c2c010040d079000a812405461a1034900440e0203141c2d442050003080c0181c40e0400007025035518860100561410610161a4080b224000340f41c04c0710b121084200e10b106210074440c14021403183c0d41510a083c41254040c1d40044040c0d404000607031010760320a400004010100340c80500000817500c507414038081444043c41010300303840c0201c021040aa01031200d05c074440c01e4141030400c10600920325905116103035100c1a045512580044991030307200c0c0103100c080da030901d49066a13414 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 781191357 1250 781190107 781190119
    0x100504080a032a0f110307050c0109091a010e0d14061e090c010503061908211204030e04060b03011409010501090f18020d0203070c0510020909010e0c19050c0c 70
    0x46240c0700c2c0e4160303d01c0803045403c00c11806210311520380201c004200c01c241000c100d0381c440a06140190361074049501d9540001d040c0000001c8114841c000e480c40034900c52007403030102f200c0c140111010f80602c00343c640c1c04001c82200002203a841c0308035660494440c0e001c1c001c2c03494060b0991010785485411f10806112030740422219280105001540710400d2802c0c50f50394941c00c002400c400000343e00035144040e154030004130080300003100450080142c003080c10000c04c6d821449564015041108611192400002e00180c8607401100421700000c00001b283e50f103d44007100560400d07005000040300446404a40d8540384002500400007440d1040007942402a000a801c44602c20801c2005841c1c100319150a401e40603510103010070b2808544034030307100c60028209050980c05807500e0003014420100202c080c000c440325074038041e00c02c0c006a46009011340e04640000e111070f2102074140014070a45019441748403031a1069a50161190054480070b81085200d000d4503200324 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 781192607 1250 781191357 781191401
    0x303020618071406090946110c070e180a02031504020d06050c070204110a05220807030c15030204141918020a12091e05100504080a03 59
    0x300300003071904291035420680c032001c07030043c0010030210f01070000b1a0307a0010b4068100441004502d40c401c5254000743c01034646040821140b0491040070000407403007401c00503805608100302d0b00514080c6a890300114038003140d146825040c801c482d0404505542c051090005031019152450107004102c00501312420340c69000a9a4a145280c5002d00c00c811034001015075450345036513860769400103c240618a001c00070b800700380d44086000ca1050789841000200000e441c0280e403074028090b1102032603d054803205c00003903124003011040394143c6074000310f0000414441d8800552280b581c2510160419240409151100c1058006c0510511007003100a80f04032210045100a68038000245d145141c40000e0700034030380000c000e0b040382d0407101d003c40480b40e004000820160703458111134109018140d00341c81324841c001d0100711904d581001003100860b1490f0001d0300c91000c4920010055001c0c0341035450484040e46d01120114182e000a43c141c052019503c0310318984070415 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 781193857 1250 781192607 781192651
    0x3161203091a120612120c161d0a0e030f0405010f32040b1911010b030703020607060f06231905041e0903031e02090d0618050105090c03120a0206070e01050f07030903030206 76
    0x210b16100e041c510718028008510302b903540c1c0c2d028810b440000400e0701ea48101d100c112803102e034801d10132107000031654500c3d004142c3c440e1501301c9003071041c41c106100d8040314202c100008150601c40d2020300b2420440003540c600014011300e56a40070311340494800d03030364074409440e05840c03269500d11030f4182610440150390102e0b00c6010b50382c0c1152a141c40320120b0a192000781001001c0c10021454801d000c00d8041070354131780210405019540e41c181e10321410a01c00307403100450715441d10901500c030610403482d2941118002d16400c0c41d1041c0d415803540c05140955004080c1074000c20fa0b07514407440480d0a01072000152240100254600804030380071804040f107800001d0b0407213948086200d000d0003500b821100d80c0381c1100c000e0001d802d10401c01a07d44240d0310015100344500204410880e20008c01c0d1110310351150050003da43d500381080e989400404d980b0740c108401003004105201c502e8026000c1103000359501c2c4050340c1103150180ca02407016019003c0c0c840350a414001e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 781195107 1250 781193857 781193879
    0x1b0c2b0e03070e011a040e07092115050a090c060503090d1d010f0923030c0409051002090f0904030f180b160203161203091a120612120c16 61
    0x4445e080c0c1041034481c502c0c0b400c4102a070285400c04c020609a00e8184905282c6c00640311003a00d43c400c0ca81149048007441e0045100780314500100b0072042d425001d040a1075642c88103500003040716011500301c1c41076035500301c2c7c200c5d02d4103c1e82c04150040148221b501040051414502c124101024003008030452403003030301022103c0074100f00d0b24600d0020401e00c56200c000c01090081145070030030031080500c3e2030b110080d408641c040d10a00741101194a807602519840b141c01202425080041104007006076109100e0690170640f2804958221384605041c2d6100d0383c004c2ea40c030384400085900050014000e803080c400590700210007400f40420366411103084680303101594440318824404607090001c022500407a15501d40300000d034885056148001080c480d0391180f0b131070b81c0ca61482180d1003903074141c03196000606100b40f00030f2110746143e00c0d80000006049000e40081c020810340703014220f40b000c0e01a102c001c1307444a0183c3e000c0080383c03420340c4000744d96840e0a04111070864 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 781196357 1250 781195107 781195109
    0x50d080f010308072f1302070c0506180a09050901051302150c0f03070614010e010f1403100e030901090e13030807050d0906060501090506031b0c2b0e03070e01 70
    0xb8081c0001040c0007000300178450b441c000003101c002403d03800c003c2d44800c031040004000c614091411080c241d0318960061007100c1d89150b10401403217451b4244020301005400201c200c00100d0b400f4941c038022541d40320040001484007000c0450a40f6021041c0c500b9944c000d0150030807100c64009a1006942c6c21142e10821004171401d90b850b8940065498904000e0344020001400005042c00601003e5002103c05070380c500102c0810703903a40c9400724881c480900c82c0014807000450140b00c0c5802400c103045e036580008080b100200e000b11048003c9402c0b4440a494941c0300042002e8a940c000480c20000e265070307207640b01c0c2c9240585070310880c1244008000c0c104064103000841650152042d07454006c0c1081c0200715000ba1440e00c0b1008007102e004050101c0c6017018001420314150040384e200351940070785400c42d44018190820150031401003004d4034040c1c40c21080b009110003001c030310007046031000380c1d060009009002e480c4c0038450205c907029400c018014403010b81c0c0002c2d994 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 781197607 1250 781196357 781196363
    0x150306090a0c090e040b01050103110c1c09230405010602030a170417030406090303060b0705191113050f010801020c0307030c170a05090906121b0409020405090307050d080f0103 78
    0x1103800b940000c03007112a04010340220120040e01e605010610030062503450580f0000c1c0c908100d12007448251800500a0307441210460340144030740102400c850b00d180c1d10000160611140c1d45403905080c00c139021901400c90709400030201350400c40c1c41c150207128010702176400030b549000345003940104807003013003000c0358403105020001c01c1c100040c403070100d04d42000200405450b0700345441c0060141c140040300380c001030705060000c5a090008030442c1c80d650350110007001c550340c04840c2040c5a1040707407004c2e5413000e01000301c281d050700c80c80c20f011a001c0303208a00041e28a0032a1004042c02010781040d0a640e10611014800c03000000c1240c803136580504100940e9640b620b02242070140e102c80d51000510b011a402d55990b8208001d80441c6c0000c456070714241c0c0d145018454051483c955149181d400200014160703810003500341c42f0f841010304041000402900403e050707032020b640c110095440080d440342885014081c009080d8842c1c070b4040000c1c140300640034124407041c0009 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 781198857 1250 781197607 781197611
    0xd060c12060626090304090c02030c150106052b050a02070c0906050a0e0c07081602090610140f040506070b1b040302030a030305060102030d15051206010b0a05030423060402150306090a 81
    0x4c00c106a0041050ba001403900400c03e10020440f0f8138000d459800010080c50184076106a1500513600d5403815410380300c06581e5141058018022800e0001301003410f5044010146c280e056100c1060040038801c0315000380140c0d03210080e1411654608030740d800741c01210300d0030b0030038042c0d590340031001c074121000041e59480c140c640c1900c2c60070030703c03451030300408080d000588006120f408100c41d56005008840f01e41c4039030b6038a0705021103902c0365520000003130300e0340e07589450304a8100054252202c149020030704250b141c801144c541e50041d0b0054690480b0101000441800c10070040c1c0011101060b02d07003401c1c42d540c0400d5a41d40380c0080101495118000140140d200f0070584003019030f03042c2c0038407502e03a030b505881422007040d0040b1802003840d03400380399024100069150403110b200880918000c1c100408030f8180d0009402162040b406640c0e85404160f94002020782000c6c000250959042600c10010340382c21404801c0d000c42424000c20659aa400040c15880841c203000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 781200107 1250 781198857 781198861
    0xf02010b0f0103020a0203250b06031f1802030312090d0c03120f111c0e01090c05150c0d020d031802010e0409081303051b0f0a060e0d060c12060626 65
    0x30b9085005080740414015034948c2d00701085c00710400042d400398040c03070b09011a82c40e130030280358903554000707400008400111045c11107003059500401001d03070000300040400c012540040c1c110b17400401302800c01c071000000c0c0205000280030901c00329065003056010810207603005002c9035031806244030545d983e11b011a00386040354001da00300459808005680b054100d170000c0401c4212030440780018030702a003058503014140302d83e151940e0010030340c12005140c401040206070300d9184102072000305000c0d0103440d44c000c10a038072021170320343c003d0300c0032419210000782100c0090007940e0041d90f01100c2c005c0540d810039002903c0039000c0d0380c0425901c806080040152043d00351085100807410303800024031401051144c4401c456400c00d094400c03842c02000114062448400c0c0d0003400b448040000303d010f0f0210702e903484000b4026000b550116224901160004459036002c00e03250740c0700e441c110009110b040301600740d03801c1c07600e4040c2060003840d84001c801c49080800e0342e02d02c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 781201357 1250 781200107 781200127
    0xc040501170a1506170f0d08060a0e0a0603060513170301030308071b1e11040b090711100203040b010e0601080c0a05090a0e07170a020306030604020f010c0f050304060f02010b0f010302 81
    0x1102401810080042000582d03042e1a9900546d0600341c0701d40c0181108100c119104100050061000411000c18a400e0985101d001e400140800030519038402e8004001903043c01002d2103040340d08060103502d142d41c1402c1c00319101c2090011300b0311208000610000b03801c0741c01150800d4080c0741c03010484028000d003007010040385034041c01500e49008191002400b203001c40c1d104900c101c05003110524074509000c20384040c00342196202c80030710000303500c451050242a0507007a4000c216200b18030801c0c040012640152019101c1500301001440f443c07100c0c0d495507400c4402840c00c501e2070703e4030300c0481d2200d01612050302c00300900069240f00b10307aa041e00c101d014251581ca080c0450070490405410341d485417041d9101011404000b07010340910703200356403003000040c0c00303408180c0c2c0e180c0c01c1101070303101800e001d030501c0888e003500c4c408529803800116440c2d10807401903903183d09041c0c0160140c102400b221045a043c20000c03500c68403100780c0c150414100382005601d03628011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 781202607 1250 781201357 781201361
    0x10806040819020c03160801060603150608090307240c02031201030605130c080607091217091201020703030b01020f012915220609050607140106090606020c040501170a15 75
    0x5840c059140c82003a446480d680311b0285410100c4082800800032141d4825040e41079812200c0202001c0c42915810000c882c0280c1100d13511101020551780340c0703000d6958841ca03152141e240ca000c281e40c001c0642020304054819004c0c071a40c80d000550418450307041890a1000501008040903218004640084885a03214441039070002070030560940322060309a607420212006c1c2c0000307171401000034102c0001c50002c00c24a40091040f440308030700b2055803001d50300c41c0c2100342c0c00000c00290101006002e01c040c200b880e10031b6501045114014000a2428168440025140e45070903d90301d041c01d0744000115213011200c80640104c60000001144c1031407036000b042032070000280458811740800021854101e20010100000e51211030484610741c490151030303007001c010001d40000c45c803da1380c0d107202c140d42d080001c21916121042102503d01691280c00540d020045103546440c0c40d000d00c42c05440030010320300c1040569480150703907070442e020281024803005c600c2c0c400c00090b6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 781203857 1250 781202607 781202623
    0x2010203091c0b1b07060e07050a06020a061409150c090a120c06020102030c030a0f09120f0e0618100504050925020d120e3301080604081902 62
    0x10103040c045524002c0381c44030300b000000c00b124260f074040001442060031a10000c488a2030a00c102c1c100320b50f664410000385800840c220492040c2000020702d9643c9881407006032a140e4098000c085841c9081c100340d541d41010900d48101030410000045800561980b052070f109030300203034a443c0da0203000d102d23200b0503100d140c0009d040300b00440c00b42c045601002c0c004d03204480d140d209980c2c440c4220f080b40002d80b000b40c8040c8080000c030301200380a0704485451b41d000240003a0702d034003e135554004c00207404808808115210590320b249608001c0b0340600039002d50b1a20301d0b000001102e91a034008040d0b045108807500e103407251080d8460400d540192102903d2789295042019a15044007021522841d4005080c80d002d4196840070070141d400781d000783c0b00e0704010010b41e050038025103110110504c0034461403500900c144021a49044c0e011050180002851669203540600700c10580204405a0140d03091000040b140411290100014046031384d0401c1510b80482c200036070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 781205107 1250 781203857 781203859
    0x80d1121041206020406080106020c09180c1206070905041512031b030801090f02070203121c0218150301030305030a15090504061a03010b010801050d14240105180406090201020309 79
    0xb00c507a4203801c12165a0040c019a01503840d000c000e0380e07842c3c8040341d4455813481c40d01c0c0c11660010200e0107002c81c580164452a0080f81621009241b07280841c1082c001c0385803011099000209201059410005500c040c100a41e004d011207110031500820303400b80c601c40c41280c043d1440300305060610400304c44c0d00549010707072000c1402c9404d040c02410faa030300380a582144d5180c8140680e50804610171203520550140140103002051007003940c06801040000000020601c0ca13804c01e803138580700401d650440b201c22003c0301d407100c02c20310000c810310150303003110362201700018804603801800b070b00d5100c00f10200215040119030034044108000c0d6100d8442d075820304090108200464100f48074140c071705c90501c0300c0e280d407040c20142038401544009022503000c200500503407c100494000031402032030b03030305003242403200000c1c50044c1b8801c1c02510902d9034109001d04030021400c050041100300c0303080c0c80c203114041c0039070760602e00584020201583d41410400311b90081c4162503401780 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 781206357 1250 781205107 781205129
    0xc1918360e03040603090506060f0f040f11040e01170a0c09020a050702151c0c090302040905150c0304120f140c0109050304141c03021e010e0a0804080d112104 70
    0x19a1303440c044d002d4540c1040c201d402d4010040054144c1c02d100c003410f80c01400060420b00183e03600350074440185980d05540024907101c0f02c40000000e07418008000800103043d12807190340c5492300200d201a10041e00200a40004400401103020b9051940c1a11803031040140d44025124040d03c0750f2188850003034000004440707858005810901910104858810603c800d2403c900c2440448040c480100c0210b041810140054209640f01d905800c2c807800444a400030f18803500c0600c54000c0b1602d041480d070000403c0200710080041d0300c10324200703041903000c6400c1200c0240420840f0003800b480d4140101c0c0f582c400510940102219075005802d8070342c0c603500c40700807140031310700c10707201300c1c003408901d1800c60700d07068801c00c081d41c0c2d590181c1c013504040007d2580891406040c2141040ca0341d240c2c0301c80303000080c09000040c500c030301c25011030b0b5aa030b180c030320704071b040c04008030340c503000c2c450000c1d4001100c60002c1140d500c41003a500320000c0703500001d00103621901554101500c182 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 781207607 1250 781206357 781206359
    0x9060919030c260a050304140d08030c0a121a13150807170304120b100e130210030b0f150d0501140406050a0f0506030c1918360e0304 59
    0x500d12541142803409012001c1d000410b500f04190f95849200da0014095481000100503120313200c0c4804003040d0004018041c00b040e10340358110550020303111040311610025100d5540c94102c0340800c1041c55608007032005440d05e030700b02c0b480b015000c02414000c0c045e40002c03104ea241c5951290900c0c044144c1c14400b41a2944899951482940540260000312040221603c60004103440440300695143c504001042d61080c050141c060010725100304c1ca52404180601c01c00d03640d61013154400011600241d042c01048800c0c01c0600c0c00e40245864106400301585503600140c0540380d060752a41003200300100b4111003803046c03003d1600700e24507240001c82e805052038981d0140301c0c1c0441d014007005889100f000b051081501c03d0000c0c0c3c890802e8100510308007100a11b0b808402144501e0410102480a5012000f241d8001c4005552800030006212144074000b01400d1340d914003900c1c03090203155035601601c1420340030031808117101c650750310720005400c00712580da01d013000e0326115 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 781208857 1250 781207607 781207619
    0x5010204091a090108030f03130602131e030c05100e03120a030f0b010f0c02011b151b020a24020f07020a081c0302070f14030c01110304110d020a0915031709060919030c 74
    0x8849374043e010a0320100c202e8900c030500b0480e695000d49030001000d040c054509410031a0b4103007030415030010b000c09107000c075180750390a10410b102c3d070018840080e81d40c1050900141200c0501c003403d0320051a01101c034070140d0b4010000284c0c542e0509012035541c41c2800165881a4124440014100d072540740104001ca03009c0c50075560b00030352000380950004512400d0030030071111410001a404903c8640209110080a0711444180000c07849020b079080c40e0b46c1d003a6405042e0200c03c50100040f107104500704a80582c0c014202080034290902040c950409111500e242110800d0307000b02da40c0061001a0303a91404650f485260081050320030401951240c0169070703000b200d54608074048848048440899100e181d00c50305200124441100704404450004000e0380c21480d03114011815041510511200143c0a048481124550302d401a9680100750100103010b1040c451100d542d115081658000001142d900159241c10303100ea440d0f101490f40301034a4001e402c2000a0f078 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 781210107 1250 781208857 781208887
    0x10e0f12030a020c0d0b160c05070f1d060609060903010b030a03170708011203080403051603050414150301290703081006110607031805010204091a090108030f03130602 74
    0xb10800382c00361103003114000e08102a0340c401920280c030b40e414440c002404005c4400145041e40741034107203005a0000790f00e805103480b0f5240c0120b10342c205a4401404041c0e16403045408820340000d110825140600200744c150041c0c0c2a00c500135a40410030340c2c440c3c0d5003034100940340d50380541201d03078410603418014030b034060744104401e003c5000e601140a252060f54010306a414180010840c1d0100d50760448810400810550401c8424010300c1d40c3d0103008040c03030306841d0180d030b034550706c0c0c5091a25000741d40c1500c0c07000602c10700184d4407504042d1701400590f4111400d0364060420340b00c0301d40700006d06000c0602e804581c1c6c100095950100f58009500074002d10010380e072110250384910060315000b01500902d002c1d075104400090100744250800c0150068040f480d0340c08400c1c5a032a103003a600682c120001103500c800c1100007580f1a001ca620011008444d00c610380d514184049440c1e105034103000700342000010000388038550341590250081d43c005011990340016100c40c0b08 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 781211357 1250 781210107 781210117
    0x61201090501150206011203053903120115090b030709090612021f230705010e160e06031204081507033308011b0e010201090c05010e0f1203 62
    0xc01519110000c00d2062480300c0c0701001000381e030001c0c8426402c1c4400c401010488640407010080200854481e50f1110388080040110749558288005c40780c201c1010300c0b02d00002c0358100d42e0f10510145c0031a50400f0076070f504413455091210a5007043c0c100484109265401c0099281c2c000003d2009aa0b40b08400d1801c484042a040000944402404800711141307140a5417040501c9501d05841000c0410640322030b4243c100303c003074189440903a882540d1240e4844140c103a0100700a001c0c00800e000f448601c8840c00050b11880002003036200600e1030b140118000d80c3d91140004429031010071204018014440c1c82e075446541d10018544d0359030745200c8000894001001103840a03021740134000c410b00c20aa04038012030000b420804074024220b12201301244c00700000a100c603000e04c41c20303e4841c0c48100e00d0701600d504000c0030307103e01480c0c0a401d045a14081c4411b0200301c0014002080d83d13002d1810a40140000000a0000b00044070719a800540600075041198000000f04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 781212607 1250 781211357 781211369
    0xe0706110f070b070c050108060105180a080706110601090b09040b04050106051509030d141c1b030504021806010804120e03151b07080322060903180503010207050c0108070e061201 79
    0x10000351b8840004407200b040588025020036407d00042041c4005035540303200a4801404501c20340740c3c0d6040c1c051401c40300b580118003042d4400308060b01240c080c800e25001d032100e81e000340145004640071809010780100090102003031300d0049400c1010079042007001740b100800c00011440910019141d952001c51661f200b0302c0b40090031174046008a00c614108494001440d0a2a101409180032042c41e5103191240741d0303403a03401c41e00c4c28000480e0304100c0401c07680e0016152500d803051280c07003440d00d088401800d404c030040008d16a84a5003003548160f100c100c0036911045800d0aa17140304d001c4003200e90502440d04140c908020410580f0701c68504c0382400b00301004076030409440c078460038002505103130007080046c452220300069281915200c04100000c0b03121a2554011114020030403070008500c510701c0c3c5041090244004c0191400300c00031407600507690703a440e0360b800e003418200b4140011140002c06650040803500004503015009a03035410071041024a415824090a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 781213857 1250 781212607 781212623
    0x303090607021f0e12011a100909020d090203190506040f170c0f010b040935040e070e01080708070c0302100f0b09070302090603010605181e0f03010e0706110f070b07 73
    0x94142441c1405503400b44807076201c480741c07200c031f690301400301c0082c80761802000e00580b4403000401250a03c02803541e680c4c401d0b00000d209550b84105420324000707035040703613010b0340080c00da001007140418400d4010790701414400c1003140034a0200c0614500a844014403d000308030a50250008143d03035000150490081240200040402040300c81601001e4009030703860b002c0b003514280036541501c010303104003100c070900c1c0300f4044c4400081c1d0054000341089440e00040c405c80d16040080303040c07200000d00780501e4900e45807000501404005100d5030030003480c2e004000900d0b00a2040745081c5000d07450503c00315003c022007502600c0001e9102d401894075100280e84d241c0709100351014100d00a0605155901e17010301211540c000100d001019201440d205419584104444e00d4901c14001001c00214070001002000c1420056040c001e9051a01c00008524041045030070b551490400c200b0100f1040700c914038000c951841c4210038407410801080741200c81020f0030900b0701c01c006d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 781215107 1250 781213857 781213879
    0x8101a0d0f0e0a0209150402041e05030a0f02040f0f020c01020c24071107181e05010302100f0e0603090703051c120b0f130f06050f0303090607021f0e 66
    0x1160469075150112805070f00030f40480c4005180204190350414848604500792000070780004040ba0701c0341d8071a03080c02940303031500135058048180c814002c4c5421000f90520001c161208403207103080c0100244220360f101c1100300c0040c031a0b842168184110360301152980001c0800500030b601c8603107491010300c01c0e80150144021202210200e0200b20040320030203403070300b10003502e00c0d8012011040c0e807030046000100d0303030b02c1e599411400915500e00000c00e099a00410001c24065840c0f020049030381044014005038503200140c450000306440d01c40982c00c2c03885802c03940d02c0d80f54102194002e40000034049500c000003000710580b0700a4060741e100175482241040c0a4211540d44804144408840d0002d258290300010780c00101400301c07103e5807182400030f0005c0781841c0d000c040e490355030f504c14002d0030228402c400152170251551281d0014941c0007070380d82d01540c011907100346e200044074400c6480742644041012006981c0301e201040c100d2014000c03803100c3d801d00b4055400800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 781216357 1250 781215107 781215131
    0x309070906050607060c09032f030a02010f0f030f061d0f0f040209060112141611030702090411030d02031210030201320d060f050303030402010f08101a0d 68
    0x401c5000701c0d540103004034604061507079400040c1c20700010310400e0045103840040410480c0010305003003070603014a01d071001c0c11a070408800303e803c41f1510303009034044851840182d800c10781c4400d001103642400110a204000110041c01c1000085089030303003061000540442200303844210188280303810380d101d6440021507520001b045540c0c518800107900458054140b103480da94120750107147c15003445c49008128411b0381c05e0f040c4042404540b2004000c020034540c0e6880d03032511441c1c036084201511404c58660759004804002e0b1044540c1c5001c103080040c1007498111045001c1c0503141a1a40c11001079100e80240c400704500c40720f40000211b00855901503030083c1c0764161181c2018882c00c02070700a990710382c210544540c0004251102146a00d240075000b0000000008a01c4a040641540549510b1b81c03001d2700a9009005000043c0c1e00304c8210b481c00103083c90800842d584030070020880e100e041d0b0007400f0680e11014903400031404100109883e9962702014020004521 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 781217607 1250 781216357 781216361
    0x3030e1207032309090f0406320906270c0409121b0f08031e0114010212031614040504020a0305150a2402030c060106020c1f080604091b0b03090709 65
    0x80d034142d4007100b4140041e240710151121507070083d00449001030340c8481c0a070742c08413a140c0f0340c411402c00000701071b40141c000b11309d90059030b1014480c000703026141411050898003081c1602d0219001250745d46041c3e503407800f08010341201e10020414009000e0509102c4902801010810002201c16181400c4400b20310030002010741c1c48042c4075900451503d07000e00b6a0809800001040c206803085071114234501b40003070291680c48001030303e41426000291604100b101d180301400f0b4140204501c120030002c900c50a0f0580e824888011071034680c1d08071240c8180d030011541300d8400b056525289030b141d84510710030404144018021143c4004104503040c65220f511180902001d81112034030038000003c0310104c060044a04240000110b282840d80913000300300107901000f8200c200d4a0030351054100c0e0b4107852030540da2482d1200c002403031910001d01181c00340342c40700f4204007041030911b04081950b0300a002580a1611518889015031090703c09101e82d00c101040811a00158 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 781218857 1250 781217607 781217617
    0x70c090b030d080408070204090b0106090905310b04240e1209040608030409140705031e06151201090b01020c0901090b03070b04030302010c03060f0503030703030e12070323 76
    0x5005228045120504542010009104403071703c03c018490040140c0f40c50291003151845080a01d0403076040101c0140b911001d1391005000318104800d001c0030303202c1992904100c2c10340340411101a40d803504140001e00702040020b00303098003c01000103000303558504031903403100010080000f5048001000540c0d00d2a0f0462515410080c3d2143d03030320301810000c0042d018007030004034803940d44a404606580090b1b01a02c1040d859440181c0c1d501e000e800c03000c0e804681800c00a0440c28400341c443e07240844080ea65404519900108a00e6038409100c0d424400a41025981e035540c234203103c0b40004428420000400c1c106005000130f58008154040c00c000c010303003100c580fa840e000c480806800ca10803030342d4041c001d03880d021032902011801400a1400b9400108000215080042c115070559110b00300944000c46e05010b240d40100c116050f10b90180b40c0031890208154a4a04241c1818000a1510340c00924281090340145c9280000d40c0c2044085680e035810180b000b4442c814 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 781220107 1250 781218857 781218859
    0x311030f062e0320041e05041205070b0408090303070602270103061d0402040b04182a030f03032d0e0d020d0f020703050a0f05012f07110a0b070c090b 66
    0x20745000142d400004e4855014a00020000300d03002800740c251000503110028102155a02c2d00c0802003880001c40705c0c8118071140d840d11526000b5103889481c03013000e028000610b80c020000b402d48969a04009481c2c0c42038001804560300e04104881c2c00540c1750b00c01140310b42d0801d540e443c1032190302030700c1a142107134100c0c0500003214040c3c400254a507a0014000c030b038801c2c0d030348060340c5840c0c0341c038403562002c001c055076401c1c030110090810301d4031014048400401030300141c0c2e9503400040c41c0c2c10214206c07507000044444c0d00107103203000c0d00a48544a014a003400c0c21110030f101d18101c041c90020101c0410302c080100200c10382d45242c4032081840014090b81c03000c10419255071040840c0c002d5881c0d18415143c4c2c0e01e0300d07541e8a46c00c2c1802130f2016619603040c150302000f4050284124000030f1040da410100401013014102c400c00040c0d1008002c0703813400314803003060003501c1c0c2d11034044840050840c0b286603120007005140e604064003e488618690130301080c500b84a02c500c414400c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 781221357 1250 781220107 781220123
    0x1614060603060a0c2705030f0316110402090907050918011211010215070c11090402030606130e0f0102031515030a11040909050109170a090311030f062e03 68
    0x144001801024003012840c03201040141c1782070320070300702d00e94061464042442c400088540e1500080500c2e007548444032030040e405c200008820342c1e1a000b40d41000c564400b091480c0079001d03c00040c0203014260806401046070340400268542c0f040040c0000c0500302d5007450700c4a0107d80302d80c034a80090290401450250109802040541c901c21400401c140304a0300d5040d03000400c040a10810b0b00d10b100800c04005c1e45100304400400c03041100e0000761a903170701070f00d001d800195550700003604c0ca9026601480072030741c00c440c650b0464118102c441e401c0303a4040320b00703400060003940101c1c2c44203200e5807160b400504501c0c24102c07003801d405a0050281c03c6454644081c801005c4414440b015003604200020f03c9001901945600310b0143c0000944441c9508001115044104405145480401c02044042d821030396407000c0e80d42000c3e00710300e0a22144040b0303160031000c0301d001109208001c20030242400c80590f02d401582c0a000c040714540114504011003421404001e04500d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 781222607 1250 781221357 781221361
    0x9070b040b12040f0c030309051005030411090c13030b150a050108070f09380a210b04060b0714031213240f060e090d0c03090b161406060306 62
    0x75410700d440b550010b02403540f06070320014540d101200e501c880e5008602041c6188010490740c905102001084002030611034594542550f8003001d0403410301d1000d11031007800021404514244d001c1d40c0a580301c200381048142d03100e050040c120401100c010340070010030b008032181c5050900b074140c22120107031204902a22603050039500c40012405100411280d048000f50f07818020070502489000400d0050300a0180c8055129411200104240410081040400460380182c08107000600d02092001643d942442c5c4d002a00100780800e900504008c00850100758080040100520450042c0202940f0350b2400391240a030b20041c0302c2c103840302e83c005800c0000454807441c2640c800c1d40782294400d542402c80c0c901e004411209200300e0340e1400300c66598030903440b442c8081c0240001d02c100615040401c541d507099220403030420040c1a185080801d8010060750000d040c40032403080d05c80002e240003030034541c08a90b042d1440340c1606080c06240c40e02240301c0b0b02a0030082c0c0503298503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 781223857 1250 781222607 781222627
    0xe040501080721140a060504020f03010506030606060c010212070306180b01080105120102070c090b0a0519050607390501030207020a2105030c07080f1c0f0306091409070b040b 77
    0xb841080c2d00c15540220310500c0c441551381c041c44200e8800e8810000007889040c1401400383d90600d000502e03000741c0c501400d05c900d9580000340a548038004940c4140e542460b000c1c01806800b44030030500c690f150300c20901011070f401d50000310a03210400c25140302c66011008003010399940c4000c540c0411100d6006000e036007040c541c15207003401c04200151038240345940c1c014038030034941c0c81480c440c0c0d51038094000a103480140d003c001c080403150180032041c1d01000e41d80079031640c4540c51040d200040c444080103100300103003818100101c0364003545280f2151101304405202030f0b2001c103464808010460390701900c252007110b41c000d00068040750414208001d07000100345011010845108680c0001d0010002040d10700000b001824903945031020151a1905242b50190300380c0225460289500c488850f4580c2d4400919001c0190301f1001c0f001c0d0002c0c0b07816001008010b0401c4148c01c00104002c2c0304070f0041081e00f0071114507030396a81d07501c0c50900a501581c0030410042041d01382e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 781225107 1250 781223857 781223909
    0x1020304140d0609050d09261c020a020d0b0a0f0c05030412021002040f0302040f051306051b070f0b07020303010602190215190e150301050108040f0c060e0405010807 73
    0x5682c8581030004e65454141c42d82840c2c040d032002120002491960140300c1e918034009101c4009170b1002a29104110707003001952503103403c021200101c0840300c041e11f40d0314400c0100d90702d0300d50082c3c16958000802e0820310303108002241c1d003586650804640c01501c11451043c00a003900d103946140c155125a070715108016000000c28045200300d400c1810610418030080c401000b0070400d42070101d10714814081510f03012940502090b20b8103017003140040d940e003103a0740c04d558004400101e80d6900740e0003052041e440b01201100308070210380e000c10440c0e00203065000700d010b5100040039a803100401c90352440f0901030741c0d006030440501c002d100118285910f0150388010181040c4403d00c40501c1c42d282c1044910401099403108480c0080340c0041d50030195080c15145c005010080f601840d4491206200c0c103410010b075000084d0a200f1810408144075600c41c0c1064000f6503076010003460f5400c078100c0d00e4801c40c600400002e6405001801408592035004c0308042170307041c1d5020582c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 781226357 1250 781225107 781225129
    0x308070c080415030b1c02131404060f1b0e10140c0a12030c08060f011b0605060f0a05030a0303020a1103120a0606080f01050405090118050c0f0102030414 68
    0x2051000506284001a01d403601070300141c41001044494035a1600009007a82c4183c85420300900561040040b00d42d40c09014000090301600c01343d80f00558a03011100402c000100708a54440c4401400100b24998101402501c007658042c00034180d054030240341810b11044a030086104045a60300a040408a50300340c071141e810700c529221004448801c0351b070300211000e1042d400042d40c00381085045400500c0c10180c2d445c040120120011010744614400b0b80300c1c522580c0d140c1c210660b181c1c4104800c00c01014040c00400751054a4903024015007070645815200c1c41e0b1040d1400c03c01c1c144000220102c0d1401001047c0050385514258000e41c0030040102c01c12000520b14940c3d980e003000145840120682159038902d8031022100480720070f43c00c0f00040020031004d10420a004841c8203064179802c1b1800105600d403180c2ca103004040c030b02005d03610210040005024003030007180e0420055015110948085488401240c8034859070040d001e1610038001c07902906e00300322080320 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 781227607 1250 781226357 781226371
    0x9011707090e031e0309060a0b13090f0b09010c020606091003080f040315180312021b0106050307090506090f070e0409060b03010b06040f050f0612070221160308 71
    0x1003805840d4450401681c0c440c035100d103034903800004c0921250599500000080040c4c805250450130442c240d0b984581025020387c2c4042e03250748155290343c2e80c01000740000d04c0d20324010085405a450220040b505c0c4000c281d43c100207900010300800d506009007401012143d0262000b0350b140010040e9042c0c0180000f40d0001000e003002c000a601c0750000c1826a1040c100c0b079032101d180d171038000031201c5078104110700da0703091049400070307140d026036014031082c7c0c181040c90fa0303000d0445014000b401410100c104400d416a03046c41e0050041d40450300340c03070081e01541c0c0016100c5411030252842902c15541010001d80010440940c000500d5001800c5103000c2c01d454040c0d0002030280d80c0301e14001e6549541e00c00c42c1224501d000d102c0c4603080303203042e03400604140ca0008943c9620045220381401600100d100c500303c1d640f4001120301030020320500d65206d061a040080d0f43d02c21506103110403007500248569200c10220a0323031254089038068040460031654101c0b0f4545016000d2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 781228857 1250 781227607 781227613
    0x30304090e0f060408070605061816110d0c0639051215010807021c030e030706060b0705191709031006140a0b03040b0601030216080a05030601080105030c090117 71
    0x126002c11061009500917401010f400380c4642041c10071008503030001c0c00c00c1c1d10410045e03070480c0300c245c245502c6992200110986038101202c5a1060b1141490b114407585c0c28040e41411100c2190040d81401c0c0f61030044a0070404c40f0362120b4445403c620450b030051059010f211031100400440c0c8001c0342c086010300c0e0450600410300c1c0d410050301e000b640e5000c454800950404010359002a03410350111107440100102c45641c00e40c4d40d41044000380d20700415844449100b80f040e03080040720b80c60b561101081000503602d10128415420080c8226994007520382104000c5003550700c022501500312450041c03450700e4465032445070f0b00010403070390140154407000901c0140351140d08002d0000c03441c1d003054403038450100180c010480c2c00100c5100018004c1c00702095010f04c0541e0b00610a00b0300595411241881c0d9040c4140404000c06caa040000e1180d811a8050081c5000c0c0f5000e88035442c450b40ca90303041584400d0184491a00f00a080004010480740801c505400010700c000f9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 781230107 1250 781228857 781228873
    0xc0a0908030a0831110409050a05010504030216060e04200c0d120903020303180708070b0c010c21090303020c01060b03010510230703030213090c0f020c030304090e 72
    0x1400c0c250b801c000d0b0b038040401c2d031034000c001c5680e28150751144070b05060010340b81d100090034811100071045940c060606801783c0c00400340da48640d409003500642003c00c0714135014091610502a150880f0300710010f002e54220011042800c01c104416903030320f80c6a0f1408807207140107000c003c0201c0300c0d4034008052070403914002c4854110042100c001d915018100488645001a041610520300200b52a1602d00100b000c6580441500e0b00300e500b490a184070410303040442450841683c21919043c0541800024080c800c90000e20344881c40600a10000c01040b03816103402d5a04c0d0341e00e2021070207004920307111030fa0070340c81100d502c0c0c130034200141000c895680b1a802c48079035030812700116000100602081c50815580070091070586070100b840c0c40b8900e008801d542c0202c003200764503080400c580c000c041c02078041d82c4540350030080211807a582da1901401a0031040c0940c0d0100c2e0640c0b6400016620110f02c51755805406001075150616000005004018513400e04020303014040c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 781231357 1250 781230107 781230119
    0x60c02010b10121a0d020d14030c03070605060303070803012115060303170402030c0904150c030c180806150301060b030708240a060f0219050616170c0a09 68
    0x140030b142a22a560750301c00344601c004440c412607501c5070f09003107604004500c0c51500d03070b5500300d60819154152100225501d46140100403150140c04401c9580804130b22200c40c03800c00000341c058180120018041c1e900ca000900d900c0e4422000058407032082000144001a002e02003180000782001844441d025191121403200c050b480040030150380381c14003003080c168085111805a0000d02c0c104209090660000759209403112400c3c1c007c2000c1d0000909004100c4000001400fa000c0c05000d00d44015000400400d03c6841d140d0118440303020450385210030f81d5a503c241c4400600801194590b0845030703c2c4000c00070700295043d0f485030800b040031941300c0701071400341e00303281c5494002c0e040c504021034280c0c43c0403001d03810b007115115900c102569051081c004480b01410070031020000344800701d0500202c0741c00d1104100341d48031801c040090008000340710b0b11240c03c820580352045c101c200d850341c8026580402c0c101e980004510341d0000c5100602500045040c02c500945d6611 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 781232607 1250 781231357 781231369
    0x9050607270605040f0e091c1202120703050903070b0105190b1305030d18090b040204030b16020c040c0e100201020715050103021801120b190609020702030d1b060c02010b 75
    0x1810100010f0300116080204441c00241072004d00686185509140340c0b5141542e40d0b4410420110180091910030801290189020015440140c0c2c410740d9611104010700c8030303861040d220440001d00d01000640c56413400300030750705400d510540380022a46007104104038201c1154244400301c0c1d45040005d1601d10403030080a030700c0c0310317043c0c01e2828030b183c00101410550442a43d0b41440700310704603040c030b02c28000300d54400e885400400055907a042c1c0b003c5002409280c000811020703819040c810401301514110105035229400c03160b4412019042c4015034200d0843c81d00824071a01304080d461a20284601c501a04d03440010309003000307500c8805051070045c103018400c65072500140300f942400c020002e000111100d20311040c3d40740940d20106a83d1264020340341c103150802207a031024014144c05440142101e00344109a00e548440c0000c0d807007a00e0403442442030014940c1520b00809510001d40551421007458415170b881c0e41000e04502c1c500502103560303501c1c40d404160350300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 781233857 1250 781232607 781232609
    0x60f12010f0f060812030f0414011107080d151211040e0307140c1905060304030909060902040906050321180d11100905150705030405310905060727 65
    0x2242c0402e4482c500b04006050081207403d031403191804004002800178070740c09558225900180499580f50054a02801001410000004c140001400707030144034284d4007400b200307a06503604001c10380e0001e501d6590100c5610501664610100e0303040041080421001a000d602420100e048001e50b0011030969000342e03c221210143c0807403103411041c0c10005001000740c20348403452003120303401c9450948040c6208040c8140400000030b8101845445200014105400c0a000700e0b41c035114144065045070081c140f58030f160038000605c0f854005081c10362651101c00e00c05000e900380b0803802c450344c0440003680020311504494152606d4610088074901d008d003030300fa260300f1100000c00540c1c903002c400c01d004002c0080000d0140ea40c4582e03c050140081514140da5105d0b14500b040c214004c0fa40501e034032080c054180e0700907480d050a03034107200384104030083c11003902512800440d00782020140c2a50301c8803001450b240d028121000209110103c0030400c2d922107201c0b00440105 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 781235107 1250 781233857 781233881
    0x605130608060f0915190507020102040618050f040c1b05100506010f0f0f0c150222031212060302090910230c0a0504080a03020a1a060f12010f 63
    0x5030321410809a1418803180b500046120005002402e181d10300c0f41c1c0e0361800d0310020701160707060b801145240b110003900304101d00c0028000d018500e019079003c0d00070b41103071107070402144000300f600320340780703900329030a402e8035001000921900800c0c1d0900006040000c1c0a00601075150404e41911060311307804040c46d882080201302c914110a0b542080d14005048a41440400190401c03503d4203c400c22000c040613240c010300b070f01d028030022603071640d5095001d401e90b01c802d290780d10b074060560010318800c1210002c0130044140001381290b00d822620014010800701c00c99000d1103842400098654072810801081158480d00000e1000130142d510521583c8100b40c0d50300c20850600503406c000d05405807038400390106480c1d420302c040f0b0090802403c01c10000311204042d01401c00c0d07034040c2840b4022070704401c0312850041d5440982038000e44c1c200a07400444000c140c0d006d00958401d0b1400f600c26240307401c11400b07100c001c00010603480c0c0e6654840444080724034203480b81c0750021003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 781236357 1250 781235107 781235111
    0x2a030a050309010f030e100c02010b13091101020d1b080904050c1803010203060a06110f0a080a020f19300e090a0c080f0403021204030b0f0a050106021f060513 70
    0x41036002404144c0400c5000c424076007002c403560070000000c501c11498007000000031410190f80707117041340144080c615403940b01c441ea0150010703c41c1c5903884800158482d00050240641003001603940d0403200c140007000030303024400ca407008803590554a0b4018800c052203400c10004100040958104448505224102265644254032000301111035500c00750021031039410404041a0742c11041c0c0150b4003403080b404c54456800404000012100303880e0b90590300e00702d031940740c841c0c82c550002c524800144901071410920180110710303110001d1550503840841c0c1d02b40e507a00e29000343c4141003440e004070008605003800c21004140d0000502d070307956055200481a04004c026100030300940740361450f0020303001041c1c0d08240407a03040480e800319001e840d81c80f46000ca25080c540207030514980000303e800010071110400040c061401c043d01c108507692051200c0c400ca070024424480164045038110181c15240c0403440514144c003140172800503202c4001c601e1000700302c039200300616 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 781237607 1250 781236357 781236367
    0x10020703052b0311030c0f04030501020403030c23070e0604090c06051b0303040f020d0c0b0a08070f080708040605100806010f080111040608011505091e04050601112a030a0503 77
    0x1080105000c030b202c07000d041c01c11804c15030305070050300c5010042c40300c0303610b000014180385482008070544004591103030080d9070702c5880f4500100001160441126940103d0340000515096031f0a180c0010040c0c2d0001d101d45440e00b40000c08148014004a81161391030a034030003c1408086100040c00b05030711140d40e92000070100c16015148422820703c00c0d0410300c14400003510700300848984a0f011a0141d007045c1044c10001204001c41c1d0210000c0703280003d203403c032107810000b900d10507c003e4960302800c454851301170722078017802c940c1c40c2f000510100010380000c19075880650820003c140d4440b4294540e0703500ca10340b00f000c0c3c200590304944810100714641c824003482200000d03042d01d9074142880c3c184040c204580c1030123485040c0c6a213400c0707420b82c80d2113042991400d07100240010382040103491003440031440b01c40054040c0d41002e002941d10750003400108a03503480c2c00e000344548111324420000341890040c3d0304101c1d03400c072000f202e410381c1e003080240d55440c01200078546e15 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 781238857 1250 781237607 781237663
    0x10c030c02193b1e010f1d1608070e120309031612030e06071e150c0c140a1b090e0c0a23040f0204170c03030304021002070305 56
    0x26010520303030680544890151200025442e5043e00c0d2204146001d00b4164454041014104400c55030845551002000014203d950400f03a00211801c00d0003c030340c0c0818420440c0410b0004551038162a4002101c2c544a03d114900e000da0050480c1341c0801c403807800000044054400c83c140c1e0f12030390310120f5918002e24060080600c1d00d076013104102c03205403408400c2518a036081c0b802030280101049446c1058442c1c030104e40d1802c5c0d20800860450310141b110264506801c4010703201c5541c6030545001c520039502c200031400446441e8503030808495a2000020a90702c0c002003c00e004411003400011801d2640300d00000803005001c85682c240107421046030411049a20350390300000001c1901c2e2641c4200e18203503885a0030345445003514440402d080f8000c0c60010345c00034500311409801160aa0203031007a1000c8902c8045041c80100c0529a2980c0910b05240d0682040006c600145480311442ca4201814016140c0440c0e8075260141042903030021840d98010b800024240 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 781240107 1250 781238857 781238879
    0xa06050a0605011b0501200304060e010603150b0a0905070c140607050909090309031006090c050f122a070308010b0a020d03050727080601060815010c030c0219 70
    0xc88400c000041281c9441d10b030008003011070640407008600e01082c9002c091190070b402101007078090149840f44002829010640d641c8204c400392820381c41c1c51034410f507001c410300910081300c4d00405954070300313a8452100c030000d00c400700c4129030114903030200003400899400781603c541680c4c0c035003182e01c00300c0e0b007400d40380740300c00c25900c49081d0440e104105078260014203031401d0711016100c5181664807000c4162440c41000d01e038942c54412024495007079001d54110360191100c0190911411848607030640310f03400b0b24000190b10f0b610030f1160480c161a00806158454141c46502508548410700c0f2200448048c1c8541241c5d140000e02c08281a0800324440c01480740d04004c070b01d4003c9030940252102810303c0304108040c0c9440110305101c1c4070310036a6203850348005192505c9165140d045c05e10703c0151042c94102c1c050000005240c1f405100d50f2803080308103600c8000c00d4003000004449040e60300038210b041c041200304210140c2c4a42c3d2850308000c6024001201c400d00780504000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 781241357 1250 781240107 781240111
    0x2821051203220c0e010f0b070809060417070816080703080c03040e010f090b09040807030c020f06040603020408070f120f030212030c0a021216060510030605100f0f03021c030e030f0a0605 82
    0x103580244d5004100200c0d8007802c4603c126000009e0319280c0790b6500001e034992203254801c4025428400b4810400c22000ca00001106c1d450701c2143d42c448440f41e400d100400705445018826084a5401c0012a0420b00140f24081c044030940e8a4182c940c2400842e02d00280c02440c000441c1920500803160107200d0320041001c100d80110261501d9918039401d441400d10040c1000310700c514010854842c0c0d05000d15105005212a44807510b0b418010003c1d08070340b040c090b46108803140000c00d58000031042003901c1c0183c40c184144080ca880d20510311034103080807001c40c03240111201c03052103c1e01c0614094054a507180703a07036009885c0002c2c40c0110500c001c0c10002c50400280a00c100050b903880d01255003e9804111b65075030b41c00c65141044a80d00c09801981064100000e2110615140e4140c400402d4040c182503114165404d00840f02e020003901711228452111004002c014210305e0b1303a01c00c0c80c0c05056a8841c1d800702c0c4c100400e2003101d119580c00f00c520740c010000342e03001d615 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 781242607 1250 781241357 781241369
    0x3070e0f072d0509040e0102042c130314040e07091e0f14060706050708010e01080604170c0307020312030601030605040e03090f2821051203220c0e01 66
    0x9990210b490307180c09812039041c40c81c1c824441e0002e1420150f840c0c64000604039100000210341300d0703545080c0e1190b40030720a944c1d440c0031210b41d00d0300700713410a801403124064500100041c400d21060344c1e0648011040b02c008000c403007010722002800b421950415032295405650b114a4035103001014640d41066428034040c0d80b810850500551f03c031800d00074100c90300c0c2040a02d480c50700780041003451184100107018a070902d0b04016505030408003c44c1201d500840040041c0c0c0d0b1032990a440d8003080e03c00910840425200c40c1c80e01040401402d048020030040d80c0c5809071a038006840c0040011807052803050100407c4150743c0c061140400a040a9509006040f0701c0a441526442400d01d46885181c011a005001c1e8030b42c842584464400f010346a07034114448401c40201c100c5034402d120340c000c03800d80300c41c0c00081400c000140c0164003900500d1803241264104a80c2d07000140702c0104022417035001c0e210042c00b80c1600306014000c5161011150500045143c0d01005070031003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 781243857 1250 781242607 781242647
    0x1b1605100e1c03150503070b03040b071103030c0d1e0f05090a02030309041a0604080a120e011b110d0c140402040e01181b030b010201053303070e0f07 66
    0x14000c00c0092070341194011252500080c0c6013495a504080e22000b0b800564040c8101030b000300d488040c00c00198000e0307000d4004210159205141200c00a200c0d244c203081039001070000c112500d8440e40500240100c800c400301c1c1c9412604046800160240c129020f01e0382c4078980c0c0c090702c0f1454441e5a03004104e82000d4082100c16402017035a07445010f481d180200e40c2c07402040b52120036080550b41d1402e00a01c190343e41d55171120361aa60310482401038902455080301c0d10302c001e0048103860f001100686403011001c00d880c8458150610b01482543c4401a00c2441d060640d41c2086095100344141e40110310507081c507801046070420901201d000c1c41c8100428040600035810310344c1111a0214204420450042010003900d0200f4184070a01a0001400710302c07501a003040300c07200c1003a8001c220a58840b41701e111000c41614007040442c4c0f00d0004c40c004440c090800640081000e0700710799480b03640c0e50155220078011910030301000008024049015404505440f564200e4065 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 781245107 1250 781243857 781243873
    0x19050403050f07051908280918061a0a0905010201020703080f072a050606030613140309060406030e100902090106030b01030216110a0605070803060d03111b01090f0e1b1605100e 78
    0x30140c81c0300e983c0e0141042701e510745c80c81c00111520035000880a461040002e03194426269a0b14003e0307000140600045003c0103400304103944148240c0e01e07169050b42d00c1c03409986070351829011502000c2c145008000c4100716078501014943c030759000400d5447c101c14894a000d0510300d00300b010281540b846500701609000a02442c18241600e054003d00501c0400721811040342c5980301c0c004061707401480205000404941551048200090340015a422414440c80c03003002c46219010017940303c0740503c010300c00103229900032800500181001481d06808200140505204803000c0b102d07844848840515424503540e60401001141425400d00041d0350310b80b100d0740001401d15014001e803c04007410315120b007064030342d1541d82c070090f11012030407825039160350071081c2542030128040590018488091b140700c00100c4003400c2c42d607001e5490341c116100a5002074601240914001e0012100a10011800d181240d01c980002c1681c83da90001c0074054503580044006907800c8511 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 781246357 1250 781245107 781245187
    0x4110406080c060f031e01031a0604020705070303080615070f05010c050a0527040e0c0307060e03060105100c0b18060c16031107080d0819050403050f07051908 70
    0x9031403000c50341300c6040b03440303940e44080310030348285d005c8074002400c003900000801d22902070028450b840e44208004141da55001c1804145d118004004040703902411042000c64852903e1980003003000f00f02a0b504910260280e1550f00040390135548507003180c0200741000300901c59035035094980d05060f401c080608002409502030040740c2880c0320195902c0b060070b00c1c03800c007000581c1400107004000080030011b09a170b03580100b0025074002d05c10040f01189281c0a50301d1106140002070040605a00b01001c0c40703816840b2401020034454030441e01e03030001c7c41c0444094800d001c0c2c0c40158510b40c0c007a4a1030751602002900324800411b0800c14046850b18241040c002103030182401e100d40b041d840031240c03a00055610a80c030702d000d21403448d204a907001c0c1069000e1500ca419070b918080d1100d00101c02c8400c16100100406c5041001a0340d00c01881d01030200c3c00c0c016419905208502e100110f0841c5101200f2180b4003000191480b004488a80340d00035403004500c040080c5441e40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 781247607 1250 781246357 781246369
    0x504021309060b061602010306060509061c020c030a081b040b07081e04120b06060c030306010c030c060c2006010b030a2a09050a06080f2d04110406080c 67
    0x110106011580301c1000c441030082d1030b0001ea0b810000507101d10380d124002d00728400d0800c140d407800c1380000d0034443c0010358280700b2401d0304e5429a00030302e914901a010007208603501c2c0c0249085c49000e0702070200e00c845038005c4c030291052207180e4036504598034101d5501c102c01c1410410581840106100c03d2144800c1a8251180140c4c049901c40e0382d05403582d0b5080302e00d010702191701108100040d01140e022903048500d07031305600c03d40040100341c485600b00300ca98015500310400035841840028800d41c80740c0302c50840c0c1c0f402030038541d06451240e19044155016828110046401034400a400c26280003900300c1021004010b00980e50401440c00c0083c8406001c860742240c480603104048013003080d03908040309118a6541c0111213201020300f4040035032107064070402d0926000500540986200f500c00c65003c05480c0c01e82d07842402c1758540c1403c034079003040c961418004031506060b2404000c0c0c0158000c0e140300c02c0c030700414401c000a562182d04801020b4022189081c1d41e501d0340303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 781248857 1250 781247607 781247629
    0x30506181009020310050420030c130b060d06091d0f0709020a0513030506270a03050f0c010f0501030203010606090501120e030c1002190e0d140c0a0303110f01050402 73
    0x4024045488442c6000103841c2804c544d00405103a440d03c2c040c8001c05c11a21b80c080b0648a510804800c000440c00400d600c6664050f51260041c09101070200040314a60000c600c0500090440741000e0764003a1803802c5520540004480540e960f581604560350780c6080540d0400c0c90f401031a000c80303569000c0b07407140030074441c0d890030540114a6aa82d140600306440c003075607801043d10b42c40c0d03543c0c0c00c01541c0c0741e0050f00c40b00480001d03024032803440801c5443d000d0680c003441005261540c0103607800c0f907459212074540c04207128240000a6400801e0050040c03400343d881c008609941940101403c55607250b1144090018245c010012660072038002c1a00c1400c00400003000c170040307505e09040d88942d2000d56428082d55100c00491100b030b901510aa044490410f08080c2d10310070180c842a241e1648076602c4480c1e941c42e18006108240181c40c18804035064440c10020b813000301d10925802d40045002c03400d0100030461180c2c0402003910102c040c0760083c00a82410f03004240b0134284 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 781250107 1250 781248857 781248883
    0x506060f070f0303204e0f06060f030403140705010b0a091e020c1908070c210602211006180e041707080703050301050405090105010315180c090603050618 68
    0xc0c0e0103003a6000c0002980340303010740c60107640c15440801a440100645250505903080c0000000c6c0400d4821031a03800703481c03161201518451030040c0340f406103a11500002c104808000389410a40c4440312400040d100e0280705d03000219080380880d040109040c41c0f90405900c092801c141c2c0c1c9820307a0b500d244008561950000180c2e520f0700442000d0500034003288082020f07841c3d00300342040101c080010005139020762030b1212101c0c0c482e00840041e9441e030701884080d140b2a4103001c0419003642c000d190200e000158403a03500c1124090b40c081749401c4801d00e0010f006400208103058100b0350601e040982c001d4601c6a180c14456181d5140700c000d080945556510700f00b0142e074011140449402e075810044082d1194518603000744154800d0040f81d0085041401041d440e42c1d05000300d60580ba40b04c0c210000e4450081001030003056180052041c0100794502c2401040c00600500007900d141c40c0041207080c01c6042a500e48100a85244005112400c0322500d000d00440c83c3c14503260 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 781251357 1250 781250107 781250137
    0x204020f040612050606191106150a06020706020a0204020a0c0b010305010e0c01050301030c0b0a090e0114310209030109020409110909070303020a120e04020c0f010b060f04090506060f070f030320 86
    0x440310908032148403e5001d104c1c40ca00c09d09003480f4401101002c048130300c005c101e580c2d500702030b10782c1022602d40c010f502c90100541e124485d2040103203800e4003e000d200e00300e890a911480d94a8403000d068003070aa00a17591a59070304100c5e9902001400b803400700d03203030a0074050300d1540344d0355035100448d40500c0b6408420700b0200e0006203980c410ba006ca00200290500c107056540c403600f107000c0c105000407506110b040c880240881c960108101035415401340a041c0d081c107002c6c011800040d47c80900095815540d500c00100140d403140300300c8610502440211200030400d5090000b011005020350065500c15841040081d50000b40380c04581d500c012a102ca20111260541c1c40103060071003598030030b00200c2d18080c1c0f03500004078505a4218140244400c2c81c004003030282c140b20b0042c2074040f001c82000142321030111904210340041000d4042c9240420300c2d42d05444503005628100c590b903004001920905502d8000d030301d80d0925200750307401c0c0007011960754035403842400d0304403070604 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 781252607 1250 781251357 781251397
    0xb0906061e0f090310050105010f1e0804080405120604060e0c030304170102070c03210e0102072606070c1b0b0901030b15030903250822030204020f040612050606 71
    0x1041440aa6020b040044c00f1078640c402840408400780c082401144c1c002851a040420302034440c1c04e80b141c01c40d9400d4071425070891500c004844402000f001941c400760100700c001030319180d1212140140c2e880740094503541c1020f1074400d050342e00040c14000e80f0340c4058000c20050b80c021084400b01e0303c654196048404619400c0ca0290180510180160b03990802c0001071040840070341011941c116001c0b410703201148801d803803140d0b80390343c6c0e00d005038010401404010911a994002000703400c000c0e006003c90251110b06d0400103c030800c001405041003003003088298005524568424842c07082d0240c10140002911b0087d01c8000c1c0c101278880c3c0c500525038540881140074585008403880d924a0140c20b400e5480c1c0c0f14058404428102c50725514215900040031280e40d58001d082c80e15112203070419040e0584642d0f0100882683c07400d0005c01039403584014135840c0302076440d007900c440c40c2c030038003030b003031030103800c01c10010508081c10888680d503400104caa010100e00c1e1070304200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 781253857 1250 781252607 781252627
    0x1101180b0703110c0306151329031c080f061f44091006090f050609070c060c020f240717012601020a030b0906061e 51
    0x440015032018051140010360380707040c99444070b030310286229035200301c0300141c240301d050681e075000c102c502014800030203244241038948859070b000c1c203800c0d5250200d4810800d694143da401d6148212281c41f0449080d0704d0140e007400c0c002c040031105001d00401c5584001c02c005040c1c20f000904c901d003801034000000300c0356500d56880958001c04035803003d2043c0ca82c004044d007405240060340540d0100900c030805030310403c2901450b0781840d0000072042d0029821080c0d0b40400180101003d0300038040b6a640301c0d40188036990051510781808501d08004046180440750050444e6018440f21000c2001c0d19800015500708158415000a0031284010b4202d0520f00c2c400207024060060002e030701c0d4907403107664240e0610750084440c41c0c01c1d911055000e072100c02c252481002845480001000b0841c5404050707407207034023201d289803502860541054220b91112402c00302103507403282c00d84620704040801a901520980350300d8600600542d00e0341072610203c0143d03450180c000b40000d24 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 781255107 1250 781253857 781253897
    0x50309060a021b250906081902120d21110711011e030207020f04051b0d06030807030804120f05090402030c130e01030b071404121a0117010e0a1101 65
    0x9000d82c050694801d04100c00c502284c601c0311108a0381c120262040225155a952050004a6002d03038010b1030900a800c11040c001240e04100341d0344007080c081c0d51225060140100040e020b001ea40f02c00400000003060602c031521600c2c41010545885e01c0303895400c5a200480d4852504643c0019003082d541c00100c03000b51807003940006e1184600d000b000c21079059006401c88038030888855441241e801d05000450301c048072243c20311400d003107682806a00600050180c2c032004680441c6540c2c0b02d071102210359000070011800100014108001d01152600c680701c0300300c1350301d01007689100015005100e4002d5881d0144600e50020101c1d100d082481c04903030340341e810b01502070411a628210703111101800d100a490028000d40020407092003007240c2c00840c22841146800c150030701d040c1070b8848405007811940c0310f614040c2907445885000082c1c4c020030210f00300021282400f110542914a028a030f00340ca45d10034600d030b500064200904a80c0f0754400e10b000341401d6803031821400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 781256357 1250 781255107 781255147
    0x4020109270e0a020112050411060c0307240b01030e1c050909040f02012a0b06030a23070f0803121308040807230d03030b010c05071e06050309060a02 66
    0x40701d54a041c012698224022400060b064002d0b00c17002c03a800c5242c08454180d03102143c004229240b20040d1001d07a16150700078012074841c2e00f040701d04205090762000d20ac7c1c1a1000402541c00603400e000703c03822201e004c0c8a0300c0e20001c0c41c09208482846280c140d84031840301030005ca031400441000140c511072404e6608101008002d00818285070600007440c00301f800c02a0f00040030804a0100b45824090060341820400e0307102103171117040e45503202810809011107625015030001800484d5100850441200d0141040038200a401c10118501841c90741301a10144a4080c20488040f0100a40b15200092540b003e110355584103600500a100c02c401486124007042c040303200c00001030120300780d9003848807203c0c0c49060040c0e900d8401594007841580003241c0811040028402d420180a0081c1810071318007c404a6650504141c0e640c0c002810813858020070716415641400400001c12803410f040d81340d03052501c1510b44440b03009040d901a50b030002003400c110700f44800501 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 781257607 1250 781256357 781256429
    0x609030c03160603060f0b03190207241503020306160903020a0639110a21050613020a030303110f0a0e01030e030406050a0c080c0a050f120304020109 66
    0x341141e482211000c42c111080c041d07040080c0c5028008142580c1a10358a4180e07403442c542141103580b058103144042d5403c0c02c503044056001e000301d00010720340408032400f6450117626483d900000000c060100c891103031007030f10111403884081025071404103040c0c1d0001040d180ba45401451104160b81604480c0e200940100d411040007800c60340c011200c2c0d41da102182460b1170a0140e08040c1a1003140c4801100b07401d07000005030070700042d001c0658420401000e07161961207651054082d0401020451841a110000030010304208003441050352110a080d1441181c003034030f03004100c1d507031320034000102819515141c03511070700c1c04d02c002e0f101107600d002206642c5001e2070b800101241e0b00c5005060100341030464902480740b0100c191001d0b00c40e00e03511107040841180044071000c80046007610f2100d0100210014000c090110032000303405240200b00710402d04d4034007490f1081302043c400c81d60106005000050fa4024500d908480c00721000043d4165900d034800c5c002004400e4034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 781258857 1250 781257607 781257613
    0x403020604120b010e0403080a0c090b0c01020408060f131b09111b061b0f1903271e0311060f091e030306090403050706020d02090406091a0609030c03 66
    0x1441012561001c0b14282c071824000501c0e90341d03012041d14005e003d80b00100800e66050014402008aa000380240845803505000941d0f9600c0e402001d41c3c00445070901c0d5940008080c8004070b020005641c1191020303241101d24988040d0071501c0d045060002000c0307007e0403540e100c80a4165024201a06240c0e8040045800c40032181016a120100c1784141d890707080da962508010104400f0b1242007151071240351495204034401480d0b000e18080480303d801400a070a01110020131031a0072005a00c000960480e800b00e5603442080e0009ca00034455210180280010700801450694050040030111803030514a03003940d03a61101c40d82d4541e41d1140004010812440d038031400c4c0104041c1c02510300079500035100410603148841540c5007035000300302040c050304202c100307280e03c9406450500d0400c001c0d55a184282d901240014060390b0b00440d103800c0510b000d22415004004d81d0200b00004040f000b02c5503c20410880500d01c40d03075000c252030045403000c0c00300f101c1c0c412004007a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 781260107 1250 781258857 781258859
    0xf040905040204050105120c270406050f0f070f0f0e1801030c0501030908270d080406030c050712121508030d0c0306081e0a0b0903031929060403020604 67
    0x4490052500311002ea2255051000008042c241b0034242c0919a401c200641511040034040c04034a030800100d40c07001c100da010120801038480c44425009500c01c8201080a0400680b005030407034000c2c0180210421140c103000e0300315008000c00d40d00d0704441c2880301045441000940300c42140007820380c0c10a480b01c104d06011802c1c0400641a644580b00080b10702e600e61004400712145904002c0403000200030030f0111402d43e0b203d0005110b03000303c66841c82e0b0032500101d9251065030f0412601c0c003c0106091000c180c25024071405802149006400c041040d111142c1d0707541c0f8000080140400c03249050001002c82d0803045ca18081601140c01da00da0311503c0700d40da9403100c4440c038a294a041c9107400e0300f0f8401e00900b0304036030780c20008010780e1400240008504c081090910fa080c460007840400280784290350034885c54035031000d161607140c203000b00400c0052046c170700c0d0310451400f060700066000a440d450b80075407034005552040e03685400400d9080c40f0b1500003030751110000c20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 781261357 1250 781260107 781260119
    0x21005010b0d060b03010b04090b060f0a080109140618070c0501150602060606210705070203010c0e01021014011406090d0c031403031308090d170a02010c05040503120f0f04 76
    0x10051040c80c0341c015040242e03655400350204c460000317002d00d202007030b03042000b044460f6450704054403081c0b0041c040c40c5400c0c3c610115000c00d5029443d040d02140702d04004200584462140b190514502c44030a950b5240100c00580c060f00c501050820781c0002e200800d01d454450b40b00403c0e0725500074000c001e03c6425240920884031144540300041c81054002411421700c801035a103200c2840f9540c2615240410482404060081030401088800c4c4000c1004d6a003d00407024004040d444070301d00940c00c070000909020b00c43d280194a6400d04105d00102e10728840c010781118001464080039109500000c0d400303204002c45c05a018003588996002c1c0180300c80c4603c2100d1040302d85a00e8160390400e02074507070004407207003800e5000701c410300408078080304010040413400400c80100302c0d1301640d81c100e03240b0404e0000009103401048841500303809100c0c4480c0300c401804c015041a00d8000081d948034510700306083c0139a0b010961050340542d01d030540c0e0b0f1003104882e0960312a03441d64 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 781262607 1250 781261357 781261379
    0x3220803011509140108060105131e0510090302010e130501031101031d0c1318030c0b0705180f0a03050601140a05060c060a05040507120803040b0109270302100501 72
    0xc022040141102c0c0210981c0038020703a070840840d039a46403000800b881aa00540d10800300810701e0b810b000c01080000300c1ca01c9a03811042c054440841514000000c0c07049151036035030f07181c00040c0180b11000d24407040036040080101280d50900e0b20383c2940911901144c100740d404401503020a041c840088104100c0c4100151104400e036010000701c0b000c00ca074030170303002d00c80072203003185402c030125400050400d082186490519480c2c00302d00400c0c8010340350289139803001c013a0001060403184004000c1181e050075089172051501909010075020680ca251a05200444c07081e01c0040003981c513a03c525184800540d003100640f8902d42e5074500040c2003080903503805105070500d1902040500d84801611003910381800149a82e40d15107400100404000c2c00503111803090342c0b0000f501c2c2d1510015010058810448140c50b0304191a04050724281a040300c0501c034281140c000e1041c2003020b00c18111402002c6200f552095818207034104400400070030784050802c0f002041d00c0b0410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 781263857 1250 781262607 781262609
    0x82a010f0209030d020a210e1c0215030114040e2811060f04061d030708030a170c0f070f0209040b060117100603020c0c0402131707030b0c0322080301 66
    0x41d03044d11905640d03000f00b26107401280350300900d902c0320900d03510400751044407082c03400610340c00c0c8462868a1040000c0e1080b0700c208018450011609403103086044c40b04806820103507807481c9a00f0340d4185400a084c00700000344160103142da400200d100b1440c104003288203c200305210011032030305242e900545001502c81550100c101802240c0310307050204c101d5042c000400c0860382443d0404000b15916020020b5804408010140c46292541c0501c0044000d188038401155540121080500420303000b2400c1005d120710032040003880d0f9007040440300744256420f82203940f07940502d4083c4903640d9a0001940200045007000200418600d800b402018240c070344c40c5031a00c484190f0442c240f0101c45614070110300c18010000103020f900a03007280102c01003a50b11101d01000418101d8010b02010f5400000d5418100141680400884041214003028002040c01c0d0749880c240d940c806070160007803410010000c0c10203441003809043c0d62071025a4942822540e0038480791f55002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 781265107 1250 781263857 781263859
    0x1213030204020f04050111060f150609191a0702101413081f090c180204080609031b06090c0f13020c010c021006063501090621082a010f0209 62
    0x1107801b03107c80403400000c22501c282c4241c8042c15543d540d2a00d55036040654685107a08104203015030002c035580e140030b07802203c10300000203521130305d4080c81c4004c0d40408070b064403600a0410020380507880da601c500441400384d040c0000007030a01444a0303d40d200390b4050f81d4580d000d4070404102d004011600c002c6070a2041310b002c0d44507041c403820a0440740c0030b0304000c0c03c070540400104030314080162086c0000741480401400c0c140c7d44c1c000b081c14401c007292081802e400c0020001c403045d03440ba0665840d840d000000702950303d0051405540c0e041a000050703c211400d58000c2c0c0d00c0e5031410142d82c8241c1a07844190744400020151a0181c01030b02c0305d00001d40140752510949404602c516030444185540d9130300c154404810900501d0b8501d030304411560710310841400440d410040c454000d10302c200b000a03803e4a0110200114a10440028006901582e005006c51b1440c019180d41c240d50700410700c0500140c000341508044030b80e40b110451b508001c03100d0f04000207070f4050490020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 781266357 1250 781265107 781265117
    0x40b04060302041a21071b0b0415050708150319030203070c0b0a09030201120b040c0f03060902040b03040201120b040f0e010510030302120a030e03030c030a0c020a051213030204020f040501 83
    0x910403c464280a2407a8441c1d18211043c004014115100030198100c1e50701c0c02c2c400c081082c02c101083e0501520b050584c8c2d9a209941488100030044c0c2641e0321448080c0020001402c0c03201d801000248050300c12080c40c404c00c01224038560b0148140306c1e240d10103854600300c01c24203143c060749070380000300e058548101c0284005001c1000324211a9040c02d00d66804941509603401500d900346501c040914140d55155000c0c0f81703848030711030301440389031513104c03590a862800002010344207682c01650fa0710340140400c202d126818000d89400c2030b82405c200ea40b1120219060008082c1e00310840d03441400c204090b810b070562640540800d521000c001c1c880c41d17940e8190f107018240315100040c010f910000a032502810b2a9028100b0050351340f502103440320030706c54480d2658000340e8040c1c1c00c40c44004140944600640f140c0e40e000f401c00d001501c1c901006031111a00c819000054052200002071028040404450f461002c4c40c1d00410854a1390107017012210560401d000d0180851 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 781267607 1250 781266357 781266389
    0x70e18010b03030a18030503030a0b0907020d091401110111220f0603050c1908070e0d11010302030702070b0c030c0c182d04030309110a080604080906040b0406030204 73
    0x5060007201c4041ea03015008519040d00c0c0c903001c4803c000609500b6042404103040803001030824001035004150712440800e28000290401101010141000c0700390340c0152900c005041d04040000c0485950405000811a121005898140f000403e0791030030751802c008d040c25215500094081e808282d40c0b0040040702d080e001c0ca1401c005805490312000d50007100304411840f9810451b802800003c905041c042c40428082d80c2e0000319040d100842e80880c204800683d1042461540c4403049a89460300c452a490740050040c60440345810542c0000016002c036008102150040c460300300c0182c1d5951402855944a801c402460703405070256001c0d044151a00d10120340d5801e6042c0c011141503100c401040801e6000000d80c0004403071681c903000003029042100d644104c0c0030351004519880d03146071061101141c051b6031440740c02d00250138001c00e140010700030f90155209001e5540c4016850014800c1d00841e40039036800034000401040d05a4075401030f20490700450460750a503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 781268857 1250 781267607 781267651
    0x705030d022503050604030e15090f010c140a050a06050c120c0702040b18040c0b250606081c1101060302150306010e04050c070302070b0a0507170c070e 67
    0xe0350040303101000592180402403003200b0301c81a40c40100c034a0000302c581580c0c3c2e0303507901d0f0300305042200e01340c2c08140c0070020740e152130502074089452081108aa20314046a410000340c01e400c050a9030780c10019000c9084081020a200d00360809049404480c00d40d942894003a6549003126012140300b410071021400c48840300041d1f5403441d500034a4050035542c1c05204540d141c11005040ea8015101c00c40050603844260300121009105040e441141c5414240043d02412650055042c490100084041500517011061100030f8407610040440312500f000d00180506400407202805004d1021003200c0b941000744a110445407255924092140040c0b807c98100380701c042d41104008410b103000d500900000c44d40b00c1c0c41410f0440583d01d03814003003404c07244111801284904006410010306404001242c01043c0600b4442e240c2084480010803038041c031540185409051301354110303090410404d48950040307550860307416560f10b0384c0c0c800484506681d0380c0c4031113203840502404 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 781270107 1250 781268857 781268863
    0x180c11070302010207030305030a0f14011e06090b1b19051c09030212100e0705040b0a14060304050307060908120108150c09040603020a0314160305060a0506150a0809070503 76
    0x840b03030140c01030144185035403400e8803168001850910802d41d10703003e0990b011100e2040788498840280385000c5507040080910b000c2c49003c07101c1000c3e004c1480100100b5900802040543e140049010348881d400c4050800b48904811035810034040e070144002c1004080300148c81903400f42c5d0807a1907064180708118020100c0030502000614546800c1c005810100450040005c095003216000818200c0c50400c40c1d44440940d0788a030003044041049207014060704024050446803d00700350301e000d2818401300061004c1034003c903404800101070050a0041e5405241c0103641441034040f90700d880f4005521040c0548413100c1c02d04004076007108000340f1581c99100074031007e49103484071440351929030011054031380e20035114800840180c90b100c031780c1c030b0046110303541d9440019901c140440c1484040b80c0c8091240d284d50034200041a00040d800760041c2420800080d161500c5010400280000380320000d081d03000100d140b200c0303034403030305442c451640c0e2001d417800141c91b5000c06807 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 781271357 1250 781270107 781270109
    0x30a020301090503090126070f0c201f05070213090f030503011503091a0a0e030d2a1202030406020904020408060f010905101a0c0f07080d09030c0b0310180c1107 71
    0x1c1d00844000240c2050301075220b540d406c9109040100d1032030b070982c1d1030303014070071002c84400b1030001000c08bc0c001c50704042e80848110610541080009041c1401c010828003072003002901c00c1d0708060b40740d50354450f154401d2200c0c54100d000034007400c1050402401c180e200703114000c040716a0040c11008144244255500035a020742032011012089158020340c00d00076200603031b05030b681c0b0101c507600c4004000501000e40784174008140b2120703402505044000100100050480802d108080381d588031a0b1144802e448407401030712503e480c01c049009005007040c00303401610005020894040004485218000342100103100703070b8031603400c90180c0e02c060300c454420280a0700244405541c06c0c0103025a02900c181040c14640780441003441c1200d64001c038552504210340c18031060308107001e1039410303601a080c0500c0c2c0b5461a0390740da00703810140c411201d0311400400407441280201003040700910021301c40810f5100c00c250050002c04001d0240303c041402084404c3c0f0710000811b03000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 781272607 1250 781271357 781271417
    0x270307020901090b040609020a030b18060906060a050c030304240c080a0b06120a0902100e09010b0d0207050d02030c0d1412040f05060907060f02030304051b030a0203010905030901 79
    0x82a42d1810745004003814403c201140d00c1074541b080402c02607513a00c041c00c4101441d0342d0100702da1885400b80416000c80707500051a00c643e28080081d2070b201d034010250041025600203640c2d0510f00303000c031554050b01d201c81210b804000140014040c00c2652841c1d400e1003c00402e488402101c0c1810407500c0068182010506480018041950315403000042070342c00781c41c003854a04820070001031104120f42d403c0e100b641d00c4a2a109500301050307540b070b44c0402420703c880140c10f010005540440c1c14482c0031402070340000d40071800b0415030166915190b00c0411540060003003040a512904480c2041140c1c0c8200c1e8030f156070051042074030610303501c0c2002c1000d10f0081609081071810f4401030080e240a5074039030404000540410800e4032520000001e0000310f82491001000c111040d48000219070051007400045600441c0312014001051000032189042750042801e240c13802c000a9455440e046220041c0710b4080014191043c0980c0d820011040b0401c0c0512000c142e641c004c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 781273857 1250 781272607 781272619
    0x3300115050d060308070515090c040b150d0606030b0a05240f030412021b01170403020f030705060a450f11100f0c230627030702 57
    0x4200251094420480c40d110916045141c40720801e0300c801580d000340c1c001c40d804000025904c040c48400c0c011040c0c80d2006115044841c184001c5060781d035502101c1843c4919a40c803190011655038880381d1000014104c01d25486090390183c1034000e100920a2001017400d02080c9410341c80d1040d074640c155100100010800151010100d07610002031300c000c002100e0030808014886010f4014601c2140305543c2c500313148440348402410840012540742144100544501c217503a001040a54520081c03001c900035aa00c5040c100d2800031054400c14550100040841c03d011001c10803a00c1288000300500081412035001d4805424451114500c0360300f588250070603c54071030900c10203040c031001469140340d05031114000c2d404000000c03544d049806044000380c2c03c207505c3e03a00401c0443e00340b5640c14503206c1e82c05040c900c6d00e21401004001c1400320f44410580003600d12000840c03400840c3d81d98904007159030851109100803501c8800e903015502030150b8000100e0702d426a000e025 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 781275107 1250 781273857 781273859
    0x304020901050f1c050106080304032306101e05130e0120030f07020a0c090501060210052401021e0a020a083009040f050613060b07030f020f010905033001 68
    0x13400042d0100100f00e4495403105400111803400308090800b4500030420251582402c40d0806841d4004000030b54135500004100031032a0440800d01c01180c205103c94500003c0c103002001070510306400040c0e201443c411944091030150348600d8990b148900200200340100708040b140c51050048045d460030b0070000035001c10300100c00160043c1843c0100c405100c00c17643c84960042c01a08810201603070756004100700340e4104840d202c0f080070b43c0020401c904015840480c81d407104200040403250b083c40e0888140d10810545403124110a401c541382d400e80b01c0d00b251200d450030016442100038601c00300301c03600085841e0425205540c240001d8018441c030450f944050149005040c0806004101032610b0310300460600700b1030703e00f001604e45000c10800c108130001c0440d00c094949000414800003844004462203142c2608201c488a14160022450182805030b041465424840300b8401c009000018045c11143c907040400d00038806041191604c1c50922001c05408040300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 781276357 1250 781275107 781275139
    0x3030e0315090d0c1707031707051c1a040e060a061a0909070c051506030d09060c0809060c0304090605150324210a0c05060702030607030b06070b04080304020901050f 73
    0x1603801d1103e100b925450001010801c1c0c921407134000000607404940c0c1d238440419074604403550158800c40500300141000100981031040c540d24030507d0003521707603d503130391010001005246880403200410502414488840d074584820050f204009818201000869138410341080c0184100b0540500c9080c0707141d5000b0000304041c0a04988180641402d201010840901403044d00d044030025030010790500c0740a16180183c0c5640c5042000325038074045c07040c95405221110120781284181da02e03050310304d0001d02648a28000403001c1e110008001034044203c0d0480c0007203030300490341500241345554048100d03200440b0f000e25020701c146002000250160180d05c0713030803000703460007142207084010011580c52000e440403a03580107010400802032864100005881d05a40c001d06101065010956500f0040e1400b0185519203a5a01a0740c80704c1c0700796210145c0185040311981000e003004480c691098405074000e440c50000800c1e9400d00003941078990001070000d031600c0c04210 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 781277607 1250 781276357 781276367
    0x304080f0303071d0d060c1106010b03091005060a080d02101808071e020a090e060a0204030309170111030a0501060815150a02031b0705130b0603060d02030102090a03030e0315090d 79
    0x4165484002c417180c1d440854118401d4003542c4809484a0804c411000c4485281000c1644000d010304810000c0000102d4082002403000e41000e030003040719100c0000041e44410190480c00c0284034411a4031221507000031070800a02598a00304240c2c0071109858040d0701c8248000780c4001c078101300203000150055416160244d046104da5040c1989500240390700d502c6910502c14282ca81100e11201101400155000301189104500d01451581e01400d522150702c07500b4048801c41c600c01180c14000e4000c00d1f94030011143e1981d881ca05110382000421003030003200c00142000b00080c91540c559849080c0a80307008104071100e80c5010100810b540c00307566400118041031081c464500b208040c441c1699403100060301c11542880c0502c0701c074031013003444001254141403c035405601c450b8100c90700488250f4641c01500000c0c004a806403242c91031264001d5102d50001040c56480090214101030840943d500300210341c45035202c50f1800c1d182002c1c01d4000c80050b00340075001e6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 781278857 1250 781277607 781277657
    0xc0204022205040c0305090607081b210703200d02220512030a090515040e100302152a0114070c03090e04051c021e0304080f030307 58
    0x8001600d0414810190a2800604080100320104005080c06140342c2402035040b20a0380d85030400071442c0c0642c030103503079803400740c80340082c8a047c5020960601d04506184c1c0c0d082c0000540594924010030f02900c003108128142601000398000304105602c03900500c00700b000318000c544c140300700c0724400e42910707845a40ca44407450307401c006404442e10640382260803040c02442030711f6024603050612a4181c0d0f40c0110381000c0e0410002c240e005a04003c0f01000e0342d109580e103d043d01c3e08504ca43d107039403180d0b420081c1c2c0000c102c002c100c01c82e1103101d141000e9134400d5401119454442c1c1c2031000c180901c85c0704c50145031003002407981d00490300080c428404540ba00110b0a40c242c0d40c00c9202c401000c2c0c070010002920108501d050680080d2480020605010800440d103010b849440d181c2e160701d5070021000d1800032200f05030b28800c00c032940300a12042030b52a204030304141c0040d41c0c4c0d4401c2c4207030034140c001c2d20200d603003c002c04415244200c4460319038811440c051007042100e1101c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 781280107 1250 781278857 781278859
    0x24051006021b0301230a0f06081c1206080d020d0504060e060702190e010f08120d0504060f180506010e070228061a1804020303090103180210210e0c010c02 68
    0x42c0309100d0a5510100c1945020340341c410f003205c0000d0601000305810781d0b807c45000c0100604200c800c10901d440041d821030205069001c030440c442c486c176011100c05c2040d40c0c240c101c80d410800d000c80c10000201d542c0071112495000c5a50f0706040c0c42040d9000c1c0500e01c52480424042e440318100e41c01d00300010f019480c401480c003100140102e0040b40a240b9581020b201420741d00010b000344042410b0700005040340c1c4000300b02d150100501e1001c1445202d00841c0070755200c0010070100441034110f8034101e40c0c0030340d041c04241e8000c2110840003140d1401921284180d41c0000f0784146c242000c01d000314402d601900e001c417440051070f4a82c03820301c4030035006841c00098000c042103042c49822070700711040c03080c001d0300d10f52401046540c150040c0ca075144c2e004884140700050340c002080300c03c109401e0030041070a00c1e04205080302250380c010065000071890220700b0440ba8016a150210b05c82c03071030801e40a203030365403016048402441c400c040d41d61208441e2134440d8020901030394160300c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 781281357 1250 781280107 781280111
    0x903050f1209070f0e0406020a0e130b130501030b130309030b1302040f0b181005040608101d060408280c050706020a0b01120f24051006021b0301 64
    0x4600351284003240e00c08250005218606400d2082564003407000b840100f42181515190500b0181c08104190003d84010501036000481e51000e5019100d8046115030081904c00c9186c4900d5152028106c003401140c410b42003e044a840e140c114400e60f81070325000b0f082c442c400da80700d0f0f001c1411955018019401d1284c1c040c0d0010000300d404003403a00c1034490340b10f10b1051203554810300c0259100003410302030550800144440c0d54a500555185010618a44030410f44407140201203208150b00000d82082c117040b0042070f11f01c00001c1c00030006041040402c5400500c8202020282c026400300141d60407031000705001c111214007405120800e14401d88050340c503941c2c4511440b140540d14400309924070301c8a818000d0501202c0300400c0c00d0b0001c0c1584442c0c41c5d403141581001402040e8a5154000d07011040c0301e45802088040b940c0145003200d1f05032009821034004000b011004802805c19001030b10703000e000300000d01122881e0f00289000040e43c0d406941030b8091042568040d9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 781282607 1250 781281357 781281367
    0xc01020f041508010501090b1215060d2c0304090c03060e040f050d051903021806040f0305010515060d0525030603050708010c020c100201060509160f0809060109090305 74
    0x1038510018402440c20064807400504100c6001e881e40005a11a9040c08081c44003005108040002c8545200d4a59540e07001d6555160b03103248440b00100300c2642002012414100501c44c943c00043c6030740743c00a0f1071111036500210610840d205460030300458005020810080e540da80040803129514100030a0442d243c2083e900a41c038122401da5192090724108410b011091280e00380c0d202442ca0403e00c0d00c1c0700c07a04811800d628a007000c008042c0d0000d9815201c451104011030b003544001c10b0199510780d0303240c0400c0da0100c00d00003074500b540707403001060000940c0001a5041d4801500340d50810341d40b98081c07002000c00902402e0880b05150408019401c041c041d054900c1040e00d002498504500340b1500d00300301c40e009000325030714154141034050740005601c806074604440003500026645000c9015100039880039420141410a2280b0383d03071100b02600307802c4210f984880780d00c03500c0841291700b002c0c1907811400315080440188442c8025400c803106490003070900314940 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 781283857 1250 781282607 781282627
    0x7050a03053d020315010305040c0b0c03070c0803030105030706030209010e0621010605191713031709011a090f16020a1a07020610181d030c0c0f010c080f0c0102 71
    0x186a81c885800c07160b43c0041000006119036002c070081c3d0500f0300e4104103900d055601c5000c0070704107020703a0f044010045112590404100101c511241d84800e03440b403082d03580e0180c80da0740c1d0001e01641b4030a02407440701142a034440e2090300c00c59041613407070550b20010300c410b018041e40100d00111408411100d13405181441000b000c2c000d080590b00c41342d03134800113102015405001c020380c42c1003010b1010707642d821043d052440d50304030708101804002c54486140607194000800001d1000381c20580c208601d5030410341c08000f4020a50140491703010349501004101c41d81160041901900700340810f64180382a18116120b43d0140100c9001d0500c1d41c4841d00403d02013441103010b11001400c10181a9041c0136107900a2101c0240150031030400c0720144000401d12262130b0342030356842d6541c0680307200e0000036820320a031500340e84d80e540c00b02d00b24503100c1d14036494060060300c55543e4802554414442c28407107030740111225062140c06003054169600085140e050366400740400158 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 781285107 1250 781283857 781283953
    0x4021201021306030b0d0209060f010201020c0706050403170307120b0a050a0f03140a080a0f0e0d060203091507050a0c06020708130e01061b0201080714190207050a0305 74
    0x400780d0b40404054066180c000002c0030703540042c11640c010142001031100503240c00c100d50b42c00c90412191038103011180d40040b4020300448000d400710b0300c101c900000c0d20a030894000c1003540c0c00303801c1c00d070105191240c0b088030300e100943d911400500a044400c035908510742c0442c100b54002441c0180113640c40f000102007116540180102c0c0401450070010400812020800da141c154080d06444540c0c0c1c45800082c059504010148260188940629440342d0346106007044001c000c080d61154900700b1400a400403900642544100d03602d4210300c2c000012440d21078a219918185803500301c142c119120390640104841c807980074014400040c0889024081c0c3c4580703045a511a68601001400305240c180d0040c000d00a41e0080c0400b044008508034a00c0742d0203092000306d84e00c0e07110086901d0000324444c03078500344001c1400c1000004c9081640b1207a00107a007281da80584440400080fa032141c40014180d80c0000d000b6184018400d102c0740300902809c1c4602024016000c000b40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 781286357 1250 781285107 781285117
    0xd0b2802030a0b130501050105041e0302040501060809100608060118140c12150603040807050a050109080a0215131e150c030501140a170f070e0105090c0c070b030402120102 76
    0x100e41c40700c514060f11305004c440a0044550000c0c1800254034240003e80300d4404c07401102d28050f00104922240310940b402c1c40c3c011540030f4820403441d07944100042600109907803081c218000c1c00c00d855103500300d601498007a01c18040203051307680d1802c412003005540038070309881d40a4a0790b1038003d4040041110074880c0020409559032201d80d00421810000024030080300a4038692110889440e100244c80d0f200341c0c010b5600b551048542009481c2130402ca100800943c24404d4041c1003041800c081c0940c0401c50b0200c2c0d04000380d40c80030b410b40d2030302103400091128911180c50041100f01201800c0c0d90180d010300303600c8600c1354403044146030b80b0039400201c0e56140c0042d100040d5051103224010907481e000380154001036000200c000c44588601d4200b81d00350f1584030700034074060004003c3d1a070800e048504507075850300d420302400340c2413054074455104c1c5d1001801e035403d9242181c4a680da400c0207081c5046c2450364190b0b0640001e8810780c0c2000707080820b544400c1d800d02c0240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 781287607 1250 781286357 781286371
    0x30c0803070c06080c0a03090f29011202060d0b0f0307090519020301030f152306040c0e1315090606030b040606030b0f06030c0d021303110d0b280203 66
    0x40d60341485040c040d200b1046a408002002010390170069200f0010060319007004451130701080580341801d02c000c90640c17548000e030210940b0400f015680340c05400300344040b8500a080c03c11a030380c54500400c403640780b11000c1d410036020041d0b003000c606543e115200c80030004004030304019a100c080392a00c621500601c91541d40d860030302c031203645203459107400d00460540035807440d0b0442e41c0e100e40c070b01c8041d50024440c00a00d40a00130302c0032650020490b4100402c501d04403046040300403102000b013920851f005034a0190b0b0018603d22a81c0300703e04509014009104030080040500014003900d940044100982d600203c0d110340907000341c40c0100100c0c0c0d00810300300071050410003192a2540040c0502d8980f583d2034400b5201e0f0f034521200c501d01140c14544956030310f007400401d4410010140c1b0598400915003c89203c0c4402c56000d50b07000f207684d665480c01040500040310700030100640703000b04a00021b04140b80a040701c00c02103000c098155081460304070700702c1c1a83c00503241e10f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 781288857 1250 781287607 781287613
    0x11040f18050a0b0105070f03140c0304060806030304030f0f050f03030c040923010b0d021603020a150e0613050a021201051515041403030712180b18040510030c08 71
    0x5400354514061070350031400300c0c04200002400c50001034424131810a00800d11035440c09010705040c010401a04080641c641b00b0341c3d60798600c040107807203a0041c0034000c040f5100402061260400100313403001c4e41da02c102d0b402801c0100341c0321500764905582c4112840c1c0700700703850a9800c034001e2020b90f00075090500c040b611350f42046542000d0b03408211040070480001c180089116000459590445643c0c00b4101c0c2d48181d901441006445510500c076407626039140d500c4109640041c00541142c002c0000e8034540d00c5012140040d01c103800c2a61842d42c1c000700c086841c2d800d80b0f0049190760391007042154541403c40d800300714070607032503c41a00217966407020445404070360301500542c081c048400606600d10808100d40c0381c001e9010f10009080001079800450f10f08000b1600c0064200039214030f03014420a00030210356245100ea8050f00b0a0800025030186031015136140c00c2c4900000a0000403800500c030007858010514007650048031700002c040341c013003c00040a040b40c203000e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 781290107 1250 781288857 781288889
    0x210501090b1e0403020d0302090d1a1608071d01052b0b01031404060b010c050f010f0b0d080313060204091107050f15010e060d0819020d0503090705010311040f 70
    0x95080c07002d01d0700c80200c0101da0041000006540820400b4401807070307041c01078031440c040c40030403501d442c032207402070100c0300e42003595030804800720446104400d0300c0880c03a0803101020003245d0003c0d058038500c011900040c8658040c458600440080302c0c41850043d003070101290303900840412000e1402040c0c0b01fa8626210072000a026600540703000f800d0078450701c6400c0c9080038002e84001c0014012940c1c43c0c8520780568400e08080c080745401c0310417240c00303481500c0b06900a2801d55801c00030303d498402c00d24003508002c90161500e03604040c0390380c1540e603000b0945801403d201000c903440740c0e01f000003246072603041c03098070f9980b5180301160346c5982041c5807151804d914031145000c5580300d0800c000d25400120b00ca141560103454226003140c444002055080a940c0380003003903007201044030702d03982107034001403101d19416a00300e52000c0d09150098a42307200503601412545c0280c0028401ca5000380c0140c3d600e0b620b0b000b40320b40b03066507908100d008920503820103160b4686101c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 781291357 1250 781290107 781290121
    0xc0603070e0907030b130506030102220e0618071803080a03060e0c03010e0601050d020d0c1106100605250b0114090a140402100512090313061107210501090b 69
    0x1440310383c4007200b800d08101300c5003003c00180c1e07446080d04565045d1030300c1d0b200140c00c0f03840a4040c0c6020407807002401070075945030488800000c1041c0684011105041c001940c64038000361500c00e80c8250302c08003a00340c5c440000884181c0b03022010341c542d03c1d8020000000092401c001005443d09698000a60b1030510752450f407d500040c0402d000d442003800103000c410503102185402c180c1c01d0900c103a440025010140103802403120350341c8040d140a219110349a000715030f03450164900710a4411596402444900368241400b40000041017800005900c0c3c11001e03a1501ca03d07030403a110b04000700d466803506e8881c442600f114000000c00d80440b00c05040080d070f52900709064600074400303990b03160319403440d021004101074841c64660540281c1d445c0608215414222485000d0185151580c1b080c0d42d00c0d401248160364480c001c00000a08a00c941e044201c050358040142c41e04916008600c400007900c3e000144c2250f41c1001c80300000340c401d214601c0070302d1017100d03000010305d050300b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 781292607 1250 781291357 781291369
    0x160602010e010b060c07270513020a06031e20041503050c07030f211a0102060a0903091a250c150c060905031c05150109080607110c0603070e 62
    0x2100715000381e40501495000d40008560103087d50350758a041108280b2814100107800620089020314503d000c00780601c0248440c50000d4030b50081e1010014a0707a81c4ca0100c0c101e6503120080c0310000100b03800180c4501d480e0b008210807001c08450200a000c10382c690b403505902c150f01011080600840b0711412540500403568410a400030b8103041142c01d40300540094183c40c0103030304100c141c12262840d08014000c1c07980c4405440e00c200125200c03030300707046500e50401c2c1030310f03002d0701c544400074a00c0c80e02d40c000c3d0115194180d46a008036494404440d200c162111880d8920203814032095103c075143c400303001395200011040c102800c07a1414002545a03040c0c010b000b5030341000c041081c41720381040c4602c12032680100c0005d00c140c03050810f10b0070750050a140000d03249242c034198503183c005810540c050200041c0241c0c955407030a00541d80c0c00d043d44900c242982008002039003540c060103513201d206400070306440401c03040800191099100b2510440819000c1d003100c01242001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 781293857 1250 781292607 781292621
    0x212010f09110a03051e01091205070303060902090607080313140607081b03160207080d020d030b0307050a05100302090d03080108150603120c03070209010f0e0f0112030e0102160602010e01 83
    0x140c5007880d040c4d040d521042c3d00c0d03005c0c08240c441060700e001500b8145178400d505c10f900194100c080300c0783c22100904000c00c2d95014010a500081c1070841c00b00d10240030344211442c201d40181003900d0b100007699a02e8141d0401044506201030240660b004034014002c030006000e0454003406491a0100b405450030340c2c05050103c05140c03a41c595003200701c8130030840b034111412103003000000303459407400c0303240020540004103a8003a614050021a40000c3c021810340b00b240c80900000300c0d240c052540d5494a07204280c0c3c44030f0004000c0020703003032444c1c840c05440d02924000d0315100840d00416a003c1e0b0315030003140050b03c00d03401080b0a410601c01d14841c0154401080d009042c00c00000b90760701840c201c45144028005880149040c0400440f0081c56001c0c100c1c001d55030b55191241c4040009100303c0130f422508030002141c5515a1000c241038070310170b072a00203c545894070116102e54100c114581036203d04000b811000a0210100000f4803243d0f00100307507a84414a00340c29a000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 781294964 1107 781293857 781293859
    0x120c1e111003051005030a080d05070504091814060708061003150b070c0e0c0a080411180610020706090312031401060f080705040308160212010f0911 66
    0xc0503000f00748103004a103e50100240e40f0030900d0707240c42c00300d14010302180c0c040004d82014440390348207541040e0709142c001e0400e92540003080132191141c0200d103000301c440480748100940220b240015181d050b0160410382409080a441d20001802e04c2e03115140d441ca04070382d014881d5101007060000c551400880701d50307a0001c0c2129a000300340a0741d90702a13854020a9000b10121410300505070907040310b2811803040c00c12150000d015104550811481714001d20642c1d4814001c803914844901016090402e50f041180310085860701c1401c2d5004000104203081c0c22141e041d08407508014003e0300141c27405800c900600d83ca00f003001c58109881c00200e84168070074420000e250154030f400041d610f82c4501600d880c003031880002c051000401c41c83c8246170a0300402c400047c8081d014001800c0e100b0f03060381c02d56640e441c40c0c400740390382d4441200c2800062aa20032840070 = true := by decide +kernel

theorem cover : BRFrame.Cov 781115107 781294964 := by
  have h0 := BRFrame.cov_init 781115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 781115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 781115107 ≤ n) (h2 : n < 781294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
