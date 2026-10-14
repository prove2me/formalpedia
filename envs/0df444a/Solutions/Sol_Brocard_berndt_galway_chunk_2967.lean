-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2967
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:16:17.668468+00:00
-- url     : https://prove2.me/submissions/5364dddd-e11b-4d96-b627-1165bd53a0f7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 533453237 ≤ n < 533633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 533454487 1250 533453237 533453257
    0x905040201030e0303070816050405090c0313151b030c0c02091b0d0b040501050f060d0c0e120f010b0a0612200a0f08060616121202300603030f 63
    0x411000303c503206260440c1e10807100e600106a01e00240301d0f100c05440211a0007003001c0c02c2240c50310f4140000035a980c1d0000f4100710100c0e1002001a4000700c10b90b081040711a48640d07491302c4104d2800c050000707441ca402d0601040040c01d090030080758407034003030300c50543d601d6143e00b69100301076000e00601c02c1c40107224803200d03443d00d0b031100c480070048070044c002d000414800160082009003003009440045e40301e036120700c6c8110045503407995104103d074048600042c0001d0032402040c03007034800401d4a00c040c1d603c4410081c1c0c10014040200740d50b00b4400740b810003007140710949000c01210604074001c2000040054850321001505503102c10b142d60b2500c0c090242c5518400804441d03a4003550818000811a15010700d10b940c104549a42114044800341d0604124840c1000c9425a000002d4818140e208001204602480d052101c0e541c0c00744040d503441c681003070f60151803076a02a032014102100c00e035958032400cbe81c180c0c1ca0b01601c0d004001d146043d000000340403498021364410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 533455737 1250 533454487 533454491
    0x30f010608070c1106030417370818100c1115100b0c0f0106060c020310050108060a020702010c0c0303032403020604090902061308070311030c0d140a061a09060d0c090504020103 78
    0x517000040b0300081e110227000489402d68113040e5910910b103001e0b18200301042800e54030608220303075820080203a400b90f5403120303008144c68030004491400000d42000c881d042c0c03400700c4c4c60420681c41000000c0514100c0704940e41c0c500d001200c2400450201d81d4503206501003001440454a100700901c91103081d90111031428990440c00ca08680040c2e01110118060800750011810306024940306020600010051903141001c11900d480d401010340c0100f950004138001168022502103402c1ea8100c4e0408202a8581c0ba000d002020a00f0114641000101c1055142004000c402d025264050320060a080c603103ca5040a410b01d0741d42207034010b80500842a40c1001041d8100090440e813000f4402c1c0c61641c14100d0040f007131410b2081c041c0d000841e15003115110407101c0c1c101140c1c0920039600da086002842c506005100300008c10080c103042c0c801d03110344901215003283c5c1c5021074079000300d07445513020803001c45d284000051800034041000c00c81e4800980c0a0b030340c018018180 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 533456987 1250 533455737 533455763
    0x803251d1207030c180e1216082104030e03070302010e09090c0928050c090d030201020903160e07090e040605090c100206070225030209091002030f010608070c11060304 74
    0x2da01c011113440c0d0006081820440920001c0c40c41e140220030808809001a1102c600c480d00c80118511400c1490001180980c8102007002003039800c44031840c60081c0e80700c8608040002002c85020183c40c03c0e00040c404040d5500513240c00709076001201e0781610f420040c0c1c00c2e0041131019468005103490706500482c0c0f82c1c850181c8178013840600c00e9040400c003190154041101e00c04030310f0010500300e003442ca0311003048550341d5444101c0e0141d40007214241a00b1940385030490182c0321740c03144a40c050103a48050b030210020108030350141c9601400c04850781c3d540da04112441c2c1f5461041170302d8200d002c0045408200d45511064125248030103a85220f201803020a003202200601003006911407010862403da0500c402000c4030845000b0031440c0128000d0049121080c1c000a44180c0e5640d0209481c800e0800c421104e281c0e038080259140d20b0100c42680080c0e000744030f1500401c00c2c590001301d000340b0800754020305a603c451403000c030030f105409106098100401c01c458241078011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 533458237 1250 533456987 533456993
    0x803090f0409140d09080105010e07180b2d030403020a0f051903050301180903091716030b06010801090905150402130509010606020106060e1008130803251d120703 72
    0x307a1a560f0200440090044d4115038030014012441584400d109074074050040c010300361801038164008081d07103080c0364005400500030007480070790760040703000c8070000a10b03142d61006004141c1c40303803076801d922140c14241840c542d00b041c882100d0084c0140c0000c0c1c0b02e040061940f04255048600135030480b1401252203070401c003000e400300020380105002000421050351400c01c01c00c10502d00131424401001550b80107061410f02e4041c024070b03a0050a10811504170400000482ea003805410503880e40c0d5034109040d802c03805843c024001a0744d0400412004424007030b62041030351180003449032511007921400c640001070000c990180c0101c0c22455501c040307002c0d032401015003000000b101e41c41d004e00031b421500c3d198880018000c0d98214900c50f27981707061010403910303482d0401d266281da501625100003080442c00038200100402030005041d01ca101ca0740d1417000c1d5a413829402820040207940c111404c804d41c6111050105a119042c241002500b4100d2028000c0307600c2251030795 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 533459487 1250 533458237 533458253
    0x604030c1703130204050a0e070b1e0d1b022a120d020607020705100909020901030e03130305010f02031510020f2a011103040e09150f0a05010f0803090f0409 69
    0x38440c0c400311035007003003d04103528043c41a160090f488a10421070020750750344281d26901d040c40f5224880b44081000d0b4148d210701a00c03050071002d4a860141d0f6800c6c00307038400307000f4901d4020317491913903000208400c1800d000203066440107006840009400078180c4024030f6101c140084a030300282000c43c40c803640308040000021000b607640261955240c00303100240307064882c0d44441c0c440c0e01c55800a40115410280c0401a01d10505016954103001001a801f819072180039100d60f2000181440340d82002c81d060f00c0c25648210000e21a0400160640050707010917039008074078022001110b501c619200c412021480707203074015550144501e62005042c001c14010201098900c91040301c1160034080c6170030410f0001f400c05405815100061980d00e010754040c0160003800c403000300320078100c108820103900c08150300120103441c160000d00d05100064903084603150500b400401d800702401282000d5800350001541092003200421410fa09048005a0025604c0c0c0350b21340800d9880e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 533460737 1250 533459487 533459491
    0x1802040510080f090601140f030111070c140301090c1205013305030102070302030703081b07060e160311011202070203010f0b011805011422080d021207050604030c1703 74
    0x1511031003160324010300f02844540000b070009100e0307004000184484c0428400d2a646400305484a5a03011103050200c0c0c0102000c10503140c4103580400c4030002c0102c081401015140740d190341c071007050310340401d16098071083c0100070a141c000705414058802102040f12071980034100101d0311145410981c0640500054038000c0d0841e940c3c0c41603040071030354550500802081c0c00841c035000075038a0003901c034000c1c00030043c104002c600218140c50440540548040d09100420b6030b0350900b4030f80b05005058244c4035001a00568400326041912404040c0449030409070150782180c1c020011140841d10684124100b9801e00c058005600e09201c0c018100c0d045490000d503104603400050008082911844003c004400081c841664801c1e004a03905241c0641c0c292241e4200207034083c44032402000800d58800c0c020700040e907100c002a111007496240e0240d80c4202c00104401d413851007010400741a1f036200101090001e441442d40e1307460750380100d1001041c00005d0b20400c03150707802 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 533461987 1250 533460737 533460769
    0xf060303110705010e0d0803190c0306050a05030f060115022406030124030204050402010c02031b01091a041206140f040605130203100f0b0319050f0303010e0118020405 74
    0x10300401d180501004000c4140a4502400c3c03034020042000c002922400c258000104590004004100c510440600340450420900420700804021400040060640f8428075109107070380200080d09080201d244211b030344240024103038030381c00c01003080b07030104140003000e04620800b4408404c1043c0003c0614407801550510300e0641003802c1018255005807110160072001c061b00c0d940040c1d1340ca007250b0112030303042e20007044654a600040e43d0410030500c0284d09070013061108800d9490140f032001e200c0c98262284c140107070b2a00c0900030280c1d441c1420342801076040006200c500c1c400c004100c0564400c00c80131034024061001d003051000180d0340c580780160520148410044240141603001d0381000c0c201405c441340d40c002a654200101d500809255a0362114848141c2034200c0942a4005012200c80c020081d0b2207481103404000f0541c2c007070180c1000b80e020310b580401103904030f86510325042c075180d082860035840240804840c1441030390800c0001070a84900f4001022030708 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 533463237 1250 533461987 533461997
    0xc030f18031406070203030c071b05130207060e0606030d140f0705030406021b0a090f0e0f070602010f05074d1c080c13030507080309010f08070c03030504060f060303 73
    0x41070928403864070f00c000e440d45055410a10400c1f011007c40c0c810359100d1074100080c0081c1805030500b81d00380100340c0c0c02c202c2e0045c403d0048441894102d070014852a4411541000501f46000203543c41d40c1081e60502e6140d0400070115804030301c2420000e4111840340741c1149880307407841c0e49540583c86140119143d07000460200100c50b014043da08001130810180d104000070741e40010b06969041c01110400b5641c1c400c01e00000440341e220b0030341500c040c41103880c0300d03440b804c03104c0e42c5d8165442801c00540c00c02c90502c40106440c004c00e0300640e10f80e150502404072031a80c5140940c5402401100300007040c2d07010074840800c8002d010030803000021074241d05c045c10266070038075006100416010940c00160610306034805d091507400401d0310643c0c1d4852401d440c001e44540d2080d40003404520550001042800000c001011005002d8035286152000180d05480c4201d04448990101c4d68408510011030302a400c00d580c004c2c49150001884240010140100c4515400c02c4e40019 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 533464487 1250 533463237 533463263
    0x4050603090115080304080d080a150b0d060b0711040509150a05100801052401030605090f0a1506120b04090b16020d030612020f031c0507050c04020a0c030f1803 71
    0x2d5809424405044c4890140d841e0074205505250f54080709840c260810145000140d0b030a90030381e01203c000580f031281803152550b102030310903403500031251001e420391400000044410003582120745650744900b0060034150604100802090b00034121911350190220750004a011b48958501c640c1d21000005660704100501c01d4002e40590405d0030560724060034000e50520040060000c14400b5000110980100f00120098261584080d401c41d070700c2d00c10302c01d00003940e5181900c0340300303200e030100080e6403800d01d842c01f102d106214020100f103000c490810f0041c1941c1003a144080e020b4404203070b510007580c03a00319039881100c8507941c020a6640740801c46074144151200d210407071a09102032420404240c80d00346000000030b1180000828029040c0c030148210306051000300141d031a0103069440240190340b0000003102c080c025009011130a141c07501c280c4e011300325107a0380d69050001d6a5400e55030303451000007401c01e010b051403000000c200c0d520342d400055842114a40114 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 533465737 1250 533464487 533464511
    0xb04030e0a0801021e2a0c0d0303060510050901081501051c0507080a0608191401050f0406060b120106050d0e0601060f030e07210611070303020901080601030501060503060d08040506030901 83
    0xf031040c4200302005140412204094001c201d907a18045103100703442901c46d520048071a443d01041900e40354014030360841c4541403540503400603013103c005480c5400d100080d104100d41903c6a03569071800b250f80127001c55027400200c081c0985282042c10584c0c940315040010014000101300e41008090300d070001c11803030907480f050340c542244440c070042c4000c03400d00070240d4172004103c0c2240c05a91070841004244180103040701c0b850740030a0001c01660414220220080a040340c0035248941002e42c005640048e91084400c400b4160406400c241d0030480d0489466000322201c540c1c09444141c0d6002c82c0d0810f110350342c020071580e1a00f030b600050408015080c1c502504090801d0380011804020315206080e5034460200310b03842c5030b01c2048191030842c2c000c250a99481e0940710700440c1c08420103415500910301c00030241c0f01c481c0320303079181e00c0110280e42c4240101710018200f44042a020300701a84101c0c032261040044a0034917803504081141904202c0304101c4aa45560001c0c1413 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 533466987 1250 533465737 533465767
    0x70e150406201e0a08121b0a02030d05060d1b052407020d0309120c1d250e0d0b060906030712020d170d0c12020a020a0b04030e0a080102 60
    0x2900c90030200440c107080c40142c60076101c0b607483c00d030110b00b202480280103000f0f800380003400855070703c601582d440f01004042010030100886000c100104140401d007030307105100003940c040c801070781d000390711385500000b940c0d018050141c041500403480d1840480020246840005040511f000c031110803490b003000c1040b15007031213509070440c00c02000030741ca440c090380301142d45245e01900c00d4211501546411520f042c1c80c0d0740140c540100d0300100800300154603402c2c0046501c2c200290500c1810070304901c0702d00006450f002d405841c12007200d038007500c2021084144c0141401c2c042d50807100c0704003013005030041e48400c550800421080044a242607289190013036001d0f801040303814240341c3d07090501741c44030001074030070307880c60a07034104100b00c10f11050407002410082d10307161020101d00c0c83c0544034814010020400e064918155160144255160260181d0080010f00c0c0e49403940a0080c00240042d0100800504142001e8840c07092910083c2280000141c1e60b41c050000088 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 533468237 1250 533466987 533467007
    0x60f15060c0302030f130807030506011a03011409071806080a0f0c080a0e03070c0e0f070f050901051810110105060109030804051e04050a0606081e0f070e150406 71
    0x18002000078480109500205984010300c81e01d211568034440d100c226000018135034060405842039000101c2042004901c640c121200c103820120030160070444000d80d07003c2402150340e04200b40d501591140380c4011920b401171a2400c242c28144405003547d029001c15400c11000304401c5000c1c07111081d03403407242030114030b2405001c00288400346401024020b01900e1040342548440e401811000244100c403080c40d403000ca02a600c80c0d403404100c0d0060412aa07040f03403256407030001030a0600801e1806540b40703099581c036160100000c015916500429000000801104c1540b0229144c140e0400c582c89000d0f22543e11070405590314070309503180240310a041068504080000620540544064800444a0f41c0004801030041c165810400001d680d000d41880c00f40802240240e003d01d0035150b140d65182c001e80d039114441095401d82110045059001e48005003104500407201900041e45280840244000500090109022a51440310302400040420596070411170540c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 533469487 1250 533468237 533468249
    0x10c020723150c061009050a0606020613050c0a030b0103020a060f0206061201020705010c0e0f0d0f0f0515091c1d040b040f09050706080112080403120c060f15 70
    0x30a241d103501240089151140180d034080c0940400d4081181591070580d405950307200c1c1250441d1918000c080070104d568402e0000342464600480d01140e103500901040c1d031000d030000c018549030001c03d9102d8214088040d22940114411010160303034094191004602601d00420154158010460760050a90000040c070601e100248110b680124826601c4078040710407030300b841c02c6000c0d0340c2c0c0644544d0380d00411551030f08058009264102403142c00444050700c501d03454150700814808800b611400c0a00b110080440780d030b0024078642c403400001e0b4816001d44019803089410310503e0201614100d02640002040f61050101d160150301401010b182c50820f001c10810802c680509090003203004a0b00c8081d91295030311346400c096204040030700100084c4810f41851900c605590042500041018000194008285052144582e00440d455150900d590b607000510350b04006a0b00a010003a0b603100081401482040c0b0b46a0b80340c0c10100342d40c00300c8086480030303030300c80d41080b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 533470737 1250 533469487 533469509
    0x1207030623040821071e030606081503030705061302030c15030f0901020f0f0909010e190b010e180403020705190911160323040302060f220602010c0207 67
    0xa0603404000c140d035080703908001080d07940c8403200c01d03500101c4d4885104503824110f2a042c8620254400c81456404520692010b040380b500c000447c2502d8030b52055030f00081c0ea04020400c00e899002150b140701e800101281e2504402c2d50381e080c20b047d030445a1b4845441c182e43d8181c25070800380800741013800c0459a00d5440310b1205910300303041c0006012401c1d414010000a43c004d2000d50490b002c1c101e40340f0660f916250400e070103d4aa61161b50300318000c1003c070000051011101031024062700c83d40c007036a810003041002c3c0c54020200c106149040091a4000d0300841d02e40388902a40e04100c0b00707000030640f506060191409210380d010318040c0d07420400c1000c450041e00d00c840143c41c120f640114a520024039142000d0003048000c0c0301440c800c0c003400c0708258000f11034451100e590008800268100c02d01101b490003144001ba42040082002503905d0003600020655100d4440c82d809101080c100424020310041c0c00402c01b503907440b5050b004050b010854880204582c64076 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 533471987 1250 533470737 533470781
    0x2031e040302150904090b0c1c06140607110402030a05061206090606101119120903080d022a061801020315100c050d0302031b0901171512070306 64
    0x720b0440b40c00742032580460f250108580301c0703543d195004040e10341d42296000206d8142058100180e03403203401005c0030361080f49403001c848151402030600710380b10f8112100808aa1070300b03002c003070761100c941140e500c2c00142401c40b655417140302841c02480b0f00035002a0343c0c5410400d10407040035141c001c030850360000c0100903003030000103100d903072000059409007040d40118600f51658100b81c0b0140520703000d03004441e0981805620101c1301c1c180506e0502c40121a907000036202009030b4000545540000c0005a148404980050a5507003004500b000022998403640e003050b281040070421580005051104244070094042c1e071600700d060086240d4100903149800081c00001d42c0d500940c00700b6050800c8600035208085110340181c10744031055a0318100400030340c011140c1d401104849004c202d0f803402101c1c1a2000400180c4440743d5000c41d107102d902040000618a142e0790030005100c3c90182c41b0058050b610440b0103004081503030840c5030500c11f507040500070044001c08404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 533473237 1250 533471987 533471989
    0x21060303030e1f0b0a050a0e0a05130507090203102c07140702040e0111071b06051615020c07031a0105010809190203030d02180a05040e031e120702031e040302 70
    0x1003c480c0c66000203400940b0000b4040880c4446406622141e405111202d001032040c07801c00145202c3c0c01c14141c100090398544003815a42c1d6281000030340190710106081c44040550b90045401105100d0510301c11f65860003c0c40d0450003603159102d40d81c00307000340049200c2c01a000d0b50b4000c1214242021220b58094825005025804010341b02c1c50b1114840d050100b42075001e66007030011210603da07162094280302da200c83c0305001a14604100000c0012401e114800b42c03820608001c070380c00c079200c1140d10b44046821201044c1064070f1750800240c2800c03c4200a042e0085105582141030184a6848030b000418140e2001b414029090304103c12040041009901c1d80d80e280100c1c0daa00140c0c2c00424991f010b007034042104c0302d10003e500300c500220075500008001080307881c0640c01e0b86130f030140b100b0f035118030b401c00071280d1090050f00e10100e0030203a09070500a040c9805410184404161a10b50b4010b0780e500b00507030000240038010054804000c20003000240c00c651510340b6540c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 533474487 1250 533473237 533473273
    0x1a06070201031503080f030115020624030c190608060319031b08030112051014070f020f10020306090109020f0906070312060305010606170f0c0a21060303030e 70
    0x210000c1c109030790340e0380512031040080402c001035a007010043c0c0d00c0303181211000c405503000b03018641c41c0e6001403c4c041005440064194460b00404050703243c018049568283c80e02a5914a50b5050264104190031512511000450198076220b001007440c81c0800141841e14080c000500a401c80400503091200c8900008a03055040c5880468110341080d41113140124030401001d200700040006400b41400742c8038210ba0340a02c0503140b00000409401048031160070303a1003040c81c103076000110301c035000e400c03c01524003031401030700e04501e82040103904007407000100101107580030092001c54180f610395113000d40400c250071442c02c10700c5030b4128054010154143e2140360001214000c051090003800c0d444507804406200d0300e900c0345030842c00f80000b40100c500283d44404100a0314a01841040c0620200b20112101d9211441f814910f64420030205040c0000300d600c000803030440700c24040c0c1c00b40c42c05800081d020b0461a0060030745903440308ac840709500c500c0704480840301d08 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 533475737 1250 533474487 533474497
    0xd0810051f050703050f0a0207062c060c011112040b0601050408030f03150402120105040f140f1302060705070f0e0403120506040f021c0f0c0903030c020a1a0d1a06 72
    0xd410020b480da54186012240b911600c0b03030307a00b026600491011f08040d00003070308102360307401512021a648101d03645100b600c24510410403480002920900660410000801280000100108541100100e000401d0303001c00c080c100072121840400052000a20016070403000900c1d18903c0e141c5005000c5980e40944034152202040001c049540c10400382503200c0352403030244c410754840407080400c44d00968248a034902580c02d100407000b450f8858807a510408030280b4030036065444452040d070340e4040084c80783c00008142c1100e18003581e120000303004a140b00c0d100410110303080034032035441d4418035448010007001010078400065000316610f1005444c1410005682d40c4210010340a400040c202a4070144000759000301c000950054520f40d060002d0180204524883d800d4210348258055000050040f0f00c20310009104101890b801c500090000348980e84540c02e0200500c1a074950310300181d0001016100d4071118040d449190720550703d05c00e21a00090041780d014424 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 533476987 1250 533475737 533475799
    0x60a05010212090418141506060a08100b040e01140405100603090c0f0803090103180b061324180e300307030e100b030c010c0f050d081005 61
    0x1010540c0540c1c0d807100d0384164101d00c030345d40c800000400142404111b10030340d02941000d90040c10144d002142c3d1104595000f1400a010756240c0054102c003120035100140c08241c0a681074480004c400b100350000c1e00c0a031444e80700310002545008031091540000c4600640258181010465811006908a003c40b611400c000ca0b99070502d16100c002c464070380d00400c5140350920404903030014000090308200d202030300c0800481c01c02d0311030f048080042c107000804004a0800040c0241020f45011611900120300400c00303000d01d014010402e11483c1c250764038103005640400010003141d03144603030b038008505c0400034041c003d10a0741e10b458075200070400103022003034440244e8000080c039083c00329100310715a889080c803000040150100c0c0d003c4c45045c1c8074020b41145400014440c000307803031034001d00900c202e005050055512042600c002e44910000c40382001c01b04074180500c0c4000d4206969003c06460f0403048903000280681005002c1c14084d510000100903401001e004140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 533478237 1250 533476987 533477023
    0xc1e140729102106140a0e0606101103271507021503060d082d03161d090a050105121906150f0b04050301110a0509040903180b070506060a050102 64
    0x1000d50349004142621407001304100d1400d84262200e8100d10310040c02900044000e00001000d240659611801581c045602200c0f88408010707290041c40b40180000b0b00b801920700b000c4c035289040c0800240050144002641800d43c600317107184c5120017803101c0809001072420054030303402149202440c80002c10b07051100201240c020350302c1800340084154814000d65654510409010004a400f06a910798440c0030f01c840e828440c010381a1b910070004a03540070851052102c00301c594003000b00d02d04911038040d8000384420345034010380500c40d021078000812a5407410040c0300c031003190a048500c050700a401001d07880d8020414050404e50032600125481c40b01d200b03001c00584d41503021548040e0300340d000141c1c00ca46200078000b1600110001c00c071070f00744a43c1030080c41c4103a00f1400e002074000c01c038048042c680795204076031542c001d01c0c00b4842003d542e800a120135400b500840c10300c3d400414030a0401c0000c00c08240d2000003a6440000d6500e0080041d584003c0d0510b0000058 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 533479487 1250 533478237 533478269
    0x10807030b0d08040e0106140a1b0b15090a0b06070f020a080d1211040f031e05011113050406050303160501111206030d030c1e14072910 60
    0x40c440e41000c00450001400050342111034503114519500600c600200c0031710031000003940f20f01680041c84850802072460707141c540601d902325054800039800104085000110001082070706101d5445413200c8a031062060442c04100030b41c01500a250071f07c040d060200e03c143c01c1c1c880c60706903105540d02961510100106100103104440260040481c902c0b4503410b00716000d611108000c0c6407070750800100800c80d0710f01002d00701c910075030045000034420300d034040001401c0201c03003080107000c0e568010111501555901d0030360b14059a00101c204c400f00d05417102c0100c1549543c02881c041380e080100c0b91601c0b011980741c0c081c909503c244030488000c444140303c2d0a400c18082c1d50b850b41d02103641d071360b0300440c0040f8004003660024040d20480600c076125030300178498907886c210703a07031510701c000400c8820448161941003500420807c0440700c0e80309210340d520103056140d200d450041000600440c240503507021001111200480d000c05201400644014140960300d05a424000c3c3c5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 533480737 1250 533479487 533479501
    0x1a070b1312140c19020114130e04050307060903091701021908070c080a05040609080d090302150903060f010e0f010b0a030f060b0315120a03050d0b040917120a18020108 74
    0x30301610f182c0d2003a6000d40b581c1100295206030464a500c0e100362610341007400d003d8601c2c10a030040049020760409549010b000312242240c0441e400b6114408907450075840365216800d4405000084001c00d080c103209001502e0a542c0340d00280070740000840c2890b02504c61500c030000c04202c1501400340700c1700800d00d15849040d26842143d0000d00d4960f8030407050400911700da01900c134090000e2221440407130a503901081c101400c48007070b9590007440b425a020070801208c0d00000c1038040e0f0f01000350002d1600d0520005110310b0707551001003005c0d89098a1207001800040c521680d010003d0012701201c07076081c050b1010a246072030002142c0107240043e0300100481e82044c02d0207400441003010000b50100030b034280c007100383d032080a0315000600955441c01c00c000c000340401c40902c407510040364241c1c8000d460000060001c030b0039100741c1d2148002000d83c442c0c40e540030400044d8a42c0301c04456201306411003845a401c1100054201c64041100e2000360000c1c100580c41001c0703015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 533481987 1250 533480737 533480777
    0xe01030c0e04180803010f060e0604080303071d0312123714090c01020c0f060702040915050403050a020d020c090103030305091e0c0f0f01140a0302041a070b1312 71
    0xf46591250b541da40c0d9584910703656042180910414000580a900801c0d035820070310199812680b40800441c2540c50700b00082da80e6900d4052002191840502191b059540802c019661100d1000a8a62304c1040001c1010080c90040c003058081100c0101d41200c00b0170051204848000c55075040001c998001c0880c001d40f880350000c0305801b02500911458150218000c28056426004c82f20459541d00501c11143c2c0301c40941c60b4810014007000001d800c0580010480c2e91096081d52803d0f0500c54198084503400e0324103800094010821956250b010040190840312034001400002c414400061005605010040405845001140d404802000f0038180c0310320a200000303420000c41c1b1b426a441c86040341e41840348043c040e0001481c24800c03179240342c502040e91a50303060416801c0001d01d5910140c119802c2560030032000522118613040e41c2004922b9502c3d0a5031a040c40c2404d03403110034041c024240840c40c1c66043d80c005a40c1c8034400400310102e0524541500003410707c01c403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 533483237 1250 533481987 533482031
    0x60311060f0703120207120809101a011805030d05130e010e0402060c03070b010e07090603020910180801020f09040c050a1d0a1205030706362906010e01030c0e04 71
    0x20004d0724540300d4081d900040758034401e127546000c640c805145421107605a600e003c0040910f0048680012584d5114031542000e0101c0310842000780c0740e543c1c0105e403134040704040c52000280f000c01c0705120107095280d460010f007005c24018506504114802e91021405407009200305030003c1c40304400c10045c0260b4600540100400c4800d40e504c0e10010140e8808549000001c4c0003684040368481c028425220b51140181031038003000e401c41e0b01174891000d1940c0307400800494880c001056682400200b2100450080d11500c86128400348001e403085440300000307101d17051010b601c0c81ea0b440b40f607805079000f40b104142174442d51a004140c000281c2e81004a0b0780020b10310030020b0207400402001000c0c82483d040100b54203034001c04001c0811007040140005146807a0003130650008540c000702801050070700c0803401c400d28091141c042c6440c22041c00e100e02403c104a5603041a03000681d0b010a08040c408420566001803545045a81c2a8415980d03503181d1a82e050214003004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 533484487 1250 533483237 533483243
    0x206090331031b0e0702030c0c151207020c01030606080103110114191107082b020c1002010b0906040c050906031909140616051b011e060311060f0703120207 69
    0x110032020340f0b81c9500312584141c010402d9034855000030400544c0f002044501603020301002c1e111720000343c8104456164909042d411140003030000060031007842a4843c001c0506400402280102030009000e4a840f9400102409003078001040440c0450304999030855003480c003505040da101d40f07580700c50b01509404691078043c03000490082a003000030b903030b041e504140481c0c1c5070315520212075596200348501800300420107090700d40c44040f001c1c1c00080b50000390040d120840203080101c2c0044481c904400d0050b074480d2502d40050601140c541e400c940150f4060181007450344d40500300d403042e079101b41c1c003441001001600d43d40c103085100f841544035500070f00501c5001e0070051a189400480441c20b03000e00c10100b613501308003000304d080600103500d4503802c0030351104c3c00c0010090000030f81c204554a50b20a00c4c1c0180391450070403c00002c020001644c40e045040c070501c2109034403801c03406081c040101c401c09074450320946044c5503042c90b0032029403916440010280c0a030003401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 533485737 1250 533484487 533484503
    0x3020a06020f0909090a030f05070323030610020c010f0f0e04060909051207051005040614090709060807030816150f020a0e030105061e01090e04060606020609033103 73
    0x282450b80d50150052810b8002181c03803108507100c10440d240c5955002d0002404a0343d000c28490351240518042c0c0540c0d0f010341410b1004400309102441001c5030304e030b88003903400e03000000c1062030702d0841011a0f680d0304504c000e04400300744c81c00180400401180d00f07800d0280440b01c1e45c03040c0348903441c592940c0e03001801c14008965250038210140c44680e0081703a10707000e9959101282031000c02503541c2c20b900600104031040300c0c0f40c1c4040c0100006001a960309440b4400401c0300440c0800d00c41c0614100c100404440b85000714003001c40d042c6030012a015088480d08201148000b0140d440b801d031800144440d401031403501800c51b030307410182e003003809060020740c03807603d442c940c0585025101c50300c920522440b183c0825080381c6048620942c072000d03040e03000303180c0214404c20800c19501030620b10016a07d1300c000f8a0044c00c11501112466103c038418055030340d050160740d0304010540021030030401c00e030030076202901c144032602c3c6074466140e45000809107401c18039002150083c2030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 533486987 1250 533485737 533485747
    0x90301092301200306010302030c0f1204200a0b1b0a0602090405160c0b0703060b07111e010914010903080403031706061303150e0105010e01140607080a0302030403020a0602 76
    0x80c40c55070280384159550030751804641c401a03601c2020110710407040e04050700d2955840d1001900250006400000809001d00c10742e100d566030344005104800d04010120b51502d00b520b0141c04422101140c1100c0d003120003000c0449448521003038043d02c20008900380ca484015010703100ca03900341c08640344a44900b100c407500f440310b5036000300213100d000d54042c00320303513540808644c000c50700e501c1c0e030030000341207040c600e001c1482000c8013a0070280a10700800c0d013039524441803e15401400c8203a0300c03982001005840751030248003200c0340107501130000700c00d0158100064102c20340361151845900c0002e80109032070f03200f072042d44003655100c05025242c9440f400d005083c884186400e501154441000c40c48915101d0143c80c00c40c7d1101c4a10303403226040d903403201e0040f100344031001aa1511842c0034200e541083c000c980c042c1504000c5841d1a603d4071040e104841002c50790300b4040d00041001802103a400d400301c8103281020304026982e503c1d54034080f894058640c9003e0806480414 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 533488237 1250 533486987 533487023
    0x60c080705191703100302040c0c0c0609050a0e06030a03080403140a0302030f1003050c0112110d02090a1d15010c0c0e01080f070803091513090504031d011409030109 73
    0x90824160f024070740c00204115640c07100907961006991000c0030313248003041040103140c01c2e00711048060145c41c00f00900b179403580d51a50f11292540241d0003042c030103130091005003071803484034004004e20303a9085c170107040c03c40210340c9070159a8800317400c0100700000502030602840c90f0b82814942c4c0002c450b42c4000e0050000c009400c1600c00d00440c030706840116000014548014003920307001405040c000420f00e00540314480d100300c2d801d40e41030725602c050524403041d03005025031041e4480c1c00b41c0e94000d800300304002d00b01c25070030601080304120404d03203448108904081c0c0c00010004c40c8120130f40c000b00140d500600ca08c5008181d943ca490700407800c0c2000c005d6050494205004039840d2540000a4079103900c00c40c01030326040d40c02030101c045d051503c03140d4580d86100c0750440034580500b4001e074101552480e0026419541ca500900c8105940126511035610090f2842d441207050000000c00d2149110312201b0754000104542411766005e6002d0918a0b0f030180001c200c03251001d03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 533489487 1250 533488237 533488273
    0x111234060c1205090601090c14030405030c1207031704030309081819051302090d02100507030e06030402090402010309060209030f0106140d150f0b090a0b04061a04060c080705 77
    0x79103100006800000d040300700392542c0285401114101d0160078580c0c01c010b09040103042d440107620401c198207415140c1880e1800045020301d001c1d401440e6524030f662605d43c80d0480400b01080345200401a0202080c0c0c440b4016030a030301c4020308a00c10303484504088002d48141c40e0042c000100000e1390704070121000311107000e451030548814251030890291041200840d204243d00302d20344401080603501c55070f000742510080142038034400c807200e40203d06ca0300d0710042e0800204200140ca0410b0680001e039060080908452180c51882c0c00c1c0c0c003040180c003000c0c03c0241070540315100715040002c1501501c59481740941100c00e80c0c0c0141000b18003070720040c400c522500c68445070003140360503d500400c0c58140c00580301041d048000784000020000110703002d01c095511001c0318842c2d543c508030507000e0040020301084420700c4d40d04000488699a0180138000488001001c032442c41da800d61702150003604008055006908082e801e0b07108640c4010164003c5502c10b5001ca8020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 533490737 1250 533489487 533489501
    0x702060d0f0f110307020312060301061e08060a02070f03051309020c16081506090c0705030403060f0f0b010e0402070606030614070f0c0519020d0b0f060111123406 72
    0xe80342c18040704110b40700608540c882070720f0150050304100314000e05440720601c0b8540009010b400010139640d5031152030065408413260103040c2d1500c04080105000c01c100880d00503030700c0c9104501c0c100c905c2c6d0311440e40d1200214020240720300403551524038880790640b000142401803040d5a1040364100040d2944016211030f0800404d002c404182400c00144220141c9030340080030255458460401504840c02007040c0c40d946801c204010000d507051010f44000e41c0b00c0c10010650141e202000c600780d50b40900040701c3d592610080070116a4820704443c2002410b5500607030301c10060620350054189500090a080c0c00e2070280e0003105c0c00110b15621070901e41c1e862014407601401c0848030082158130140043e0b0010003c05d01400c0700e4001854064030091010340e0000c40c555039100170030320403510a80341ca10340d04200166960481c0400c0c1040c41c4002c05013690610205c100b035035500521504007200141e4074410f4030388490882035610301148065180c0d502204030b01d811030203040b507 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 533491987 1250 533490737 533490761
    0xe120706092c04050a1410050105010c030c0b0709050a030c08120705120a030e0d1701290a0203071a061801051309051009030804050f070b0d020702060d0f 68
    0x10142000401c0e08408142c2d01d0600d040718149000306094880306442075001402c160303064044c0a1000000910221098560214182c0540400440140c40104a0720305900c12410301c58040400c03030010f50b02070565141c1c01e80c444104440c1d512440022200301016030800c1d03412400944020041c00f200506040890784808100d802024160003100a540103401c00101154407080c040000256004d01510143c0c0b900d180c0052809507020f1901d140c004810040408210106060000c0c110046400d0340500301000d605d01401c0c190310342010064510541142d1407660200c2c5000c2024403e10444400603041035580140e98012040900304c000240c508130f110b42c61120b051441c1c0300440c40018103c031401045081280300c2000c2c0709000d00050081100c43d03002d40900550f01c2c5c5074a11511841c64026911440d01717103854a4a949000002a90074600f070380059004c10419103440c0869030031040704d85026071a01017600c0400c106000311140c186040381090700c4902102100e03400200c039464 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 533493237 1250 533491987 533491997
    0x80705070807030206040306050415020412020a0602010b10031508070e10091a0613080727050f06060c010f05071d1801061b17032d13030e120706 64
    0x180da031581c1e40d50340c10b551100039000503090008101040a275800305500c18000c42e8858140484420000d00301d90107508020320141010103000290b0801c1c014940150a46000800c5000d001c800002c2246404c0703030380c0000700340e19400108180e034450a20300008100000880d0ba00380c0e120002d12041d030300300b190340350500700005038000389440c102c0c010a081c640212040c03100034100c0005201d0a41d011000c0c100802a1480000410140c20441d040c001c0405015140d620702c10b04101d40020103040c80046281c50420080c4150003140c0c152046d0480011034600d5640c00d40b50043d1405400302604158081e4903080402400c1074002ca080c54044c0c100440a40c000c8121504000c210b00340404548054030100340107009145c003e281094842090b0003846907404015a01c1d103c942c0810300e01c4a15462000c020300194080307203800c0050144924041e00902020820b07090b4210700000d201d4030807420300710030380010b1601640030802c0d420b40190199510703000d0440259a24143d6100c0c0e03000042d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 533494487 1250 533493237 533493239
    0x20a09020a02072408070e01051b0c041d0c06071b0e06150c1c03090503031609050a03050a1b1e08120c0307082101061205070f1e11070308070507 64
    0x881e681000d02041c0c40580702d590041d01c1e01b00c4121010300c1500720340c0d410711808019102d459081c140150607403219120081c10350380210703414082038500303ca802d00c541c0c802115142e5844400410f408170040c02c02d0343e05076240d02c0241084a4822643c0b07401090780c10004202080414100764918440c65050710486000a00038103212242d1180c54054207040d0802e03480007070001002582c070403c070921458045440c900d9501d0b203d05591054803c52007031071416910a00f0680c000c00304400500c82183e044400529640302ca6403640506d2000621081800d907004036070300500004240a409500381031412002d807160303055052600e0703000d0007505c0d200c2d418002c0c0154170903204640200070000046c40c02d01e8403681d82c0890700c4d0001c2c01c82c84001c000d08140d0760020780110704c116008001c6a41e0302c80d45000c2e01d49151007100c4014003a107082000100c0c074028142d40083e00e050030ba001142c42044541e0100c00111488410302007010780c03501500b20300009000304a0050001140035800fa07450031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 533495737 1250 533494487 533494529
    0x402030d0c020603060906031002130f0f30080a020a1103060912280c140a08091e060a030906060f0509040314090913150507050313020a09020a0207 65
    0x101e442030768025482102080091510700b0702113580d640202028044809440000c8641c5050b60451086a14000320a030003c000305242c03440e56000408603100356001c201d003440c580b1072000010142414542051500201114840c0c07001c41a026800002e80c2e900c0d4000707420029240c4c0042981074a0340d44501003281ea9502d00070843da0f0042d24140001c2441c4003900e00d420007143c211080740e5040601a88050940285003811181000c00b29640c1c1c00c2c80c21010718280b1911100d15020044660003103085200190000080f1807900c43e086501c480d250b0302e030000e22140860105a01500b00c0c9010650b0281c10750550041d41c4914414442400350680719113618002c14500c2c032030241d100749900c0104010038002c20403c002c0e080d2484a45240000d42404600e040d00c042d143c2c8203841007104425414404d4080d070380f224280724110144141e00301403d0041950002601c4604800518130806045540b00b98135800208450107055440c1c00b4254000307511104a071141e00d9551400013887d42d24 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 533496987 1250 533495737 533495747
    0x5012a0e06041203020a0210030c02061f0b03130c0e060f0d0c05150409060f03171602120a051b0f01021216030c080d050a0e010b0a15170f0402030d 65
    0x301100642041d080c0391403d4150064400e86030000d034150700501d010400541c0710301c0c3c004001c115085d2000305100350901402494944000c1110035a00791030881c0041045081c80c0c83c03001c545000300b45580725100c1400b00010600200001440301101c8103001030b218003600f2080d4490541160240381080c21502403082803002c400d0014240d50200c001400140750181d032180b203095070340038030a04003038995904600300c0d1000d0f006900c40304405041001040159866600a00600c07400307142001580101403d00380002c400080c407038000880940e800310010065020020b41240440d81140f4014080e81001c2d0f0b0204891800f6002011102c4080d50002824402d000410b00f03440b8500440404070302c41100e00003000704c2c00c0091014104002c10480c40c003030302145405030030009590070000001303800c071800607982035030a90401d990000f2a684001d10702003100c03500d100d12520360001d00e2045611500740c0c5902a180d5015800380705844040c900d0b2684070b03920a40c204d824a4419400580b5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 533498237 1250 533496987 533497007
    0x9050913060b012609060c13260d050c06070306080c10050c100f0e120f03090c040504110f0f06040303050d180c0608010915030f0f060f0e060117030714070305012a 72
    0x10120234501017120b640c0c2c10110780e2266000911498902800c04802801c1807484400040010004907000802500a1040b00c1d044407081c01e0070883d003440c020301151101d0f81011068840e4415110410308180600b080318101e5150005890142506070000743c0144411080c40c40c140e8038003880034080d040009000100c1100e0520008c2c10301e10752850607450b6500042502d03409005400380c1524507155402070741c2c0a0b0b4442c0101204c0c001c250b50a000c038010014205c1403184064030058822034803100d04950a4035058a0415502c00c1c11124160181c0980010100001411240e03c0107200c03a00322044107032005695400c1c0c861b46e9841042080d0340049200440f060b80c10142000080c41700a11100f82503c139854400380c4820903110031040b51500010944080c2d2503081206440d43c082c0324003409041c410b81480ba8181c03500500607624040d0043c01010f0002c804001d280c0400d0802c4120000d641c450001d0041c0007102031f07203200120090100c2c0800d1000922030109190041d090340c0c2c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 533499487 1250 533498237 533498257
    0x10f031103030a1707020a0f0317090a0804090f2909100b03070c110a030638041d0718060902090d030302090a0b12060109050913060b012609060c 64
    0x90000310b00300c0024600c0f13009013600d001c1d81728030b118210011700e99070f40000342e1a000e525480000548072003525400080203000401c2504426544400542c11500b52402c0d103011300000510713804e002404000400402c1191062012491400800210341000f44191071005881030741c00c82d1180c641ca01c1c0c00c10003270701981902c0582480014421481140201c00150040a9010610b0032160214900c40580e03003099510b03d44803c134184001c10000001c960101c0c11617a00d6240b604410612030254410700c8e416441540c807000640741e10311040d0180c40e00108a50300340c0306040e5071103481401c0141101c8005503102e041c40800580034a040c82a680c1d4580050728200f1a03c00c150b070118025401148041e51100409a002c59003640d800e0103803180300f80f8601c2d07148a6041c0840050f090700b8044c0e2000b07129100c10000c1000c42005901c4a003803155002d4800700340d0761410300042e2414541402c2c20385030441000140080306890640c114001c4000c1d000f52612601d1300020901e9900c02c1c2041c01c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 533500737 1250 533499487 533499497
    0x80c01110301030b22080c2d0c13290307060e0904020d03050f070c0f0b090a121a1609062c04090204060b04063f14010f031103030a 58
    0x90040301c0105c26030700740c14009000441141e40a594003c3d0580007040112850761142c4015004c0c506403441d842c003c8403907920f480d25860410442c040d6100800a9020f00031074241c641915a00e4581d01300d6100d66402c55040740ca2010050055000281c068a18510038800c0305000207015004d4050f00c66010350240002c4c02e83d035110740a0200b0b10010410450802800300403640ea59040744028001c03003031090301c480000c4c901d04940d5010041064100300f0804c181005400ca45948242c886000c0f1019003442e80c61085090a00c0c445a1041d040e00000005ca8041040850b8582151b8088207042d65190345100302d41b01c40d1f0803101d49843c9242c0c3e024445105400360702e140002188202c24100043c404140301070395501240680341540c0c09001e0b210750200f07092184075004000801a6400c001292072040421550307802c0111000b0701d40401c0503002100600b02d230f0426040155400041240b090465a40d1590038400783c24a10099401024844d140e500030301d80401254030041542d912 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 533501987 1250 533500737 533500741
    0x51605190b0901020f060c0d0501080601120f08041a030a0f06150e0307150804150504390b0901030c140909180a210315091512080c01110301030b 64
    0x70120a9074000303041c071815445643ca003004a04c1e010042c01d4881c81405556907100c08003815035605449040c0c00151158101c6c030018040102c0c1d922440d038106400407403200104007030703040c50f4140340b242c3d40146407003001e89540340c1d00c4201d141e0000d5024041020007000740d922101c0d0b0410842d0160f001d0b4442e100600c40c040b1042031b00c03d003507603d10300600500760340b0f140d80d444040e041000306280002d030124024030204024042c1c001007442c1e00540c548414001d40c0340c640d03104040300511036102c9094500c0180c0e05840c0c00300b4984440800385601381c0005c1301613200d460303060054100d08691400241070450302c0c494248030b17800d8801c7c00a4040701c003d003001e10306400c1100b1203030014251281000d04005085647da003c00140c0005070281d44420700c03905080c0541c80c11201200d004009060500c400010a40c00118400c422100a120f0020f612001440c40c20440c040f030354404504c008403101c0308818040603000514130030780001c00810088101d80008800383c002403002402c82c11000740 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 533503237 1250 533501987 533501999
    0xf011b080c030c0f100c0206040309050409140102030916080a08160501020910050a020c0a080303071107050d030305240603043e010801270e0f070305160519 69
    0x805480007403011401d80b410326046a80181c5403100b50b00b01c0c01103039400008801e91403002c51040c2e0b405440d807840500041c1c90f254401408211540c4901c6008a603a0030001051002071511031001e06659030081d03503a4100303c1403040e40c8030030416101400e05120800015081c0c000295915183d51017407600741084076588081e20148900001130340c887d5000c1104030301c07550b98440c3c1211914003e40740e00e81c81e4000c0300c00c0240703458529a401405030b000180203100108000080c0c99010700686441c6074650140c0b85e80c6d070700700b44580e40803e8000b50b19511580825030160082c41c0f04e0307100c80802d420741d01051640f40e8801405a01c0141e00008c0800c00300e000318400c01c8000501c442028181d62801c054501100c4451041c1107064400605100454800b9039000e05068010103200c0c1154050a0001041902441d0070500803e2866a00c0104028148043c0500d00300040b4031419602c0096680c2001030711145c1c100e0b400b1249903491000410140381c4820140385081a580d0120030940c1070403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 533504487 1250 533503237 533503253
    0x907140105090f0a0605040306050c072003010b0a1d0f010b07151e1b020a0503030a1d010c1107080d02150a09060c0e15030f070c1a0f01050f011b 64
    0x41c0c00d294009030f00e956041c1e110380360002a5001049281d581c10b0703486203035041c000100c400180c2150300742202000f8480200384106401c07000000160007041e14030750188000303030041080c40000350301b00056410018100c0d0f1840341e60241c407840907249009a507105201210340b107009015007440727940140045070100d40c10710720500c03904448100001c0c04030380c0310483c46070046800100f8910680c07655030b6507400b0b1950580c0102c01911900040030301411a983d00b0351030340002400c0001a59a5480c6800948410080e80348070101c0c520003000101d81d0403400914200469259811707138411034200160804000070b601000c4a9140e02502d003100034402d034001c0e101c10141a0352106502d500d941e402080251046040101c5c064541ca1154181d0500303000c14a600361004003035421090082200c08511191120b07440100ca151685606001e443c081d070036072001240803503c5c139407501d04102c12584680300b800c3c1130712011541d13007950b640700600464507040c4501410102c492044404400a07a900d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 533505737 1250 533504487 533504497
    0x40605060a0305041704080c01030e03090a09111b0705091e07230c010609060f0b040506250501090201120c2705040906140108010605060a08130b09150907140105 71
    0x81805c1210200c000300f54403099002904040d240c1d81103800f45802035078140c480d00802100c070502079410420f4640000303850b182c031849450000e944844140c0c1050f21040d00301e41c1902003e541070515812600352a5681e03140501070a030080f00d420010502800d440210491144403000241c1da45503201c80f4200c80510348c3c10203c100c1c200348280060b048490700c001400c80d82d02d140f000000d40d00e2804000c00c061740c0c6c40c0c0d40400840d500440c400e0001c00452000c840581d20152051507440c10203034000c201c1007600000e0080040c454034091420801e0640209030300034002d984612079003601e50020000c447d4191001408124038509091407214841c42a0528580301402842041e0382d41001c201903035110402264019a10702d80140d100d400320358140e01407c0000001c014031400c090100700184501680c400c280700f0500002107000c100e41f90f1400380c0700c1e03200080788450308000da03c2da6070302c400005200400c07501b847c0000344c64a0000941c0401c603681c12030a8641d07003145100540d001c1d400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 533506987 1250 533505737 533505743
    0x2006041a070f1a0406150b2506020c060a060b030c07030f1e050903070f030c050120010c260702070b090102030c0d0206013212010f050414010b040605060a030504 71
    0xc07890b14800702d51040f03c0d00d4141c650480c0c0200c1945400c0c5032400803030b5506496081400e014060030711034030407542d0540300801000280e40e0501c00d01c403803464401c400006030090225000040312841c041000c1290350045084034000d00a80362905002c2c11380f400225509a91072009005032000729108641090103007070142026180c1b100b0720402600d9600701a051000032600c0001c42c20316600f4200000070050505e20030201209003135075500b84404c1010b1189074100000080c08581ca00302030990f4205100da0300000300564154070380c0103003100a1504200782400108124841168041a01c441c45004280c1c041c1c01c1860404c001c909440d0801d00c24641148002d0040803000340c004c00c01c51900a190383c000f46890f41c581030702580c000b840c02030722400340d40d40c2c0884004c001c00b15005003803082c841110701e0200010400090390045c60540518020542001c0070b0009100d10001030303d4100c1c2c0600c0007031100081a105000035541300d4030074160040001c010001c0b50714440d9004030f8002d88 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 533508237 1250 533506987 533507003
    0x3030c11130c030b01110609100e07230a050d0b010e1e0a06081c021504030c0209040f0b0a020c03090d030e031615030606050d0f020f072006041a07 65
    0xc007440c80d150454100402040110b90345010341d4180f582c015610060017103103a07009020304d02e00040d40d1516851000440012951100041111100244080c00107041a881e0f441e0602c071240040c00400102e400c2e129003e4403400c0c501040c0e03400c207071402c815141d80002d402c000a910b0f000789259403c0c8010100b40300c40d0403c0b5000003030040760040300c034000c0a140c0d00200c0d0031410643d08a0800100340c1041403904d01412040c89556004903500082c10010130302e0312940c0d507403400d003580c00c2031508134000e50080710181088100084036440c00c0503035014580c2c0440381d640d41c7d0314a4040340708641d81c54045600600c5a6a114608101140b0180c2d10a01c1c00458640301c50000c0381c0303818100c40c1c41503421100300c0310074480d150480303210b41850700780d07454144000e0b4504a0003800c1449200d00c10004a610750311000c08080443e01162041c503041810baa540310404c1c00c004020080f000607440d0b21044406e041082c501c1d0020654082d512055058150900750089103002540801c0003154142 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 533509487 1250 533508237 533508259
    0x105160201021603060b0f010302030919080912010c14130b0f0d0204080703050f0c0108070e241c05010f0501080910180203060601021506011107090e01020a11010603030c11 76
    0x1480f410250b000852141d140802d43c600f1076410020717060000070035981094414000c1202001c00013854501c580880c40f4040100346aa00341002544210604a900303e14003950f90b002e81c403015400006148026030718085000810813101100d8030610440c6510000c110750306000141e0010300801d2440401000d244c81d003401d03440c0e0328050360440d130f001107100c3c2c0140e0303020010310405020f058880c0ca0003a0141c0002c0c805071001900410011780414204000048140307940e4079884036a101c40071344400070084014403c01007030225401074908140184103030080012040c44e6008160503101071500100c40c1328102401110f02c09801006440781e4813516038090780030070f03040c815001040404405c040444101e03005041c90301d03501a1400b411544507514401d082241400c5940d0030090074640301c410a4100400640341c6807051b00440c0956160100e01000040154020115000a5100c81040004000342c4900f200e070305220160124000c220f80e000020b94009a024500300003d002580341 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 533510737 1250 533509487 533509513
    0x3020d090e0c13150807141903050601020f01050a1505040e0705010e1503010b030703050c03090a060e100e030903060108070e01060c0303021210050a0f05060d0213080607020d080f06010516020102 86
    0x40400064407130045a00102400403090740b040c3c0182c0b0000c8034038a40c5107016444000e02c9980000b42d040da01c20150340d14041400d6a10901860541c8404200240701c00d041c40d010b01c1008001d0341e08091507441c440000002d403814039008648100b84003030098031000d407a120041d04c996a240c048140d104516540c0d0088200c400400355001e00199010f00307031a880d100d0400340032148050039038040d200c018810004610350009a001c1d02c240d014001180c0220f000e5440751400c0481c140342c0701220305152512500c208000080c0400c00000c40484010366611480951100300d07a004000c80e0500a40c01403007450b006404130082d061091400500d001201000301214030400d903443e0a8030b0301c01c14010030903403401105000241c2210035a0050071450900012984c0c410b0301452003105801254241d41d8070420341c0b07400001c05121068800b0340c40d1104000307403100707a1150907101289080003c035840044e803000c031790320402040e1550351520420303111454004180c54000c03411442441c61410328 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 533511987 1250 533510737 533510759
    0x50c16121e02071703130608151c021909110304020f09041e3e011d09090f0105010305061008010b0d140f010204060e0f0f090c1c0c0503010303020d090e0c13 69
    0x10101d0323070364064080c141250800d80d00941d80f584203115a40556004141300910140004140e80c100d40181300300d4101091020340c1c00455100601491401c501c070701103180720340700852049108841c41648010340c2e10421981c0714094038060038540302c4650581107400401c02c1102c0084c06030b0750710001407040b1010720424400256018100d5496503c01c162044074041c049180746174242006000210300602c0401c1c17a0b1818101c0c07a12801841d00420380d02d20b0240311300052140070900a200300d60b1a0704086654060540b1581c10f5001520070000c0e0400041c441e821403180e00401c030b51a1600c1d0341c0c6410031441c205601c096aa03016092038500d030b0150910052004144a84405005090710010403c2d08071081e400d1038020b060080541c4060742e59030f244107910020b00103246440d0f040d20720764080803440d030036a1010901c0c44c10600b44403107034010000e58100e82c801c0e8200d031042c2c020b141e000c4030b140c3e08070b105050080b24000081040744d008030025085c2103011070580c807100359a500758688 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 533513237 1250 533511987 533511989
    0x1207061202091003090b09390306010f03140a0201050901080702010f060806090d0215010306020a0c060c08061e0d0308150303190e060703090603050c16121e0207170313 74
    0x7021a42d0b681840c02003008030444590311590120103000b0600c230054044101c840884c01505000405c81542851444000c89022031143d000e421291550b07181d42410b0040c000500003a11283c030b0b00b14201544100018a030304040c0c0c0d041c0e58203818150944010344080b2005400e50066548030001c807100603203a849008000c080c0398004005600f00f120f0154185500b000030903007150009440300200d15542842d850449901c0100140d40303000081c001c88030a4102e5200a10680c06d1401d11920b180c0d101c5007013401240110b440301b0507840300b4107881c0610044500c0d0250803030584d041c5040801c1c09203040d15800b803646445008041d200000103400c51380204c801400040d0080120700185078021200d80840a0a4a146103400d981d510040e018114030301c10b8004143d118000650448070000648140e582090407000d50603426103402081202a00c10f14000140404c0d046503800500052003a560790071600504407060411822041c043c1c1c0e651100c1001e880104940d0111280c0b0302e4400f0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 533514487 1250 533513237 533513269
    0xa03030c0e040c2304030c081b0f011205100f03061d010c02120d0609050a0915020a0914030f1501090e07030c091d0d0f080105120706120209 62
    0x400e101154800340550300c510304124051442c01507503c00c07481e000f015001003000343c24200d1916108a550041c11032103542c0004207800501800016070071000074035a200348a51350316440080c03900d08140f0240c84070011a4600040d0184100b01000c2040d51103d5001001d40c0c2d0014422900d8141c00004400580d000f21a6075a85942d58800741e1440905140c2c0002c03c1002403040c0804910000c0d501c4504101e04400c40d0400124841c02c0917066110b103005085270b100070302c05407504415a10041030200000e55141c034951101c010008054400c54484a00c1741d11070342c104e6401c1c11000c00100c00c5051031a901840303811102030840b80d00700081c4505400910200300250f040002c444142d84000c401c0e42407992210701e06000103038203d0710403400e5039880400000c0e040584103804160344280301040b0381e40c1c014030040001e00c50f4403200c100d1f0b414030750352604080d6136a104148403000511401d084841e8202100c00d000d15071003a40b1024a1200003030005d410041000d00042c4481d46045d80e603 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 533515737 1250 533514487 533514491
    0x3120c02120d0c0803190501060528140c01020403080708070507090b06070803070201150305100b09040530030f010e07050702030c24031501030605060408070b070f02030a0303 77
    0x40841c03a00600345030031000710101800641d01111809402002c03501401000c102d0701000040e1401182d840181ba1440e0340711050095581d0380401820a60207081a03241c91300046241d0030b40e08800c02c1d984048000300742d40c0c50104800c0c48409800da500b00c1181d001c81c55408001c00404103030204080d10009000e445080d07070301c04413490b00b0b5103000b0a550120004904240c115403240d03417079000b0380b0025900302d29615900e640e510022801000010350140c2000d00d042c2000c4140880060b5080c90340801c0a02001400c1081c0d0400a005604880c000c0c895401aa1401114060401146a00901c1141e0440b0301d2010780d074110001d400841d5041c0c0c000903440e00400101c4034002d0445c0e002146410030301d1510f556600825102d40100b04c0480c06020b11600300da804100c012200d94038a0781c0e12184031388034100822070842c8000c4041c0000e00017401e16001052a103858001c4030122a40e400060040750320304000f9040d04d4002000659039039048500c801c0140c0c405004008000b44aa940 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 533516987 1250 533515737 533515757
    0x112a010216060801060e0a03050604140601050316050607030509031b03060105010305040f0b04020a15030902100e01170c0715020a080a0501050d02090405010b0a17120f120403090312 80
    0x2880c1c59140d034180c03981522421020010260042e040605403410303860000c0807410124045103003005035920081c42e43c45850b0401003442214400c40031284082c2c403d940c42070342d0311404c06a80e031440c1500d0217000d680401c03040019180000003050b4161080c103005061003080000282400c841c07d46121b0054000c009400310b42c5024030505014003402d080420460610340c42d83c64a10103940c00c010100440040481c4c19903840114410042c42d1840340041800040c0f0702c014040d10402504034000d00c40000844c0501e4001d200d103800c4140103035070b0600901c96450001043d0304010303007081030f9803000300300c03035004603401114111031010000805641d402c4e020f5002041d030140201107500b13551500d07006000e50342e1030300002d202d4641c04488c511203039100d5040072401003c2414042d98000000c02000032520806e04102c1040d058407007d50f03403c2c2501c921002c0c1a0300c5203010f0300c0ea03d10002c00103511441c6812004a800c02d0291401c54600b5449680d801d006003061001c000100700407441d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 533518237 1250 533516987 533516989
    0x312030c02060c03010302040b0f1e03010e03030105011b17040e070809121617031f0e04260c0f010509070602010b030a0f02120105070e18040c0303112a 67
    0x29660346851a2004090500e0441219401400180402031003603465084003040c81c0d40b02400090098002000030b1004440e000d09022026100e51050b4061350030071840380e201410101c1907a0480d401a1a4900d490700421000d107441d50200c0006c071032180b018011b00c50aa16070300050000340091500004040c00e1910014100704002802a915a8450801c81d68149448025648094450300c0400c0300d039640c034034146076150120180610304010100412214001e2058807540825800710040203564443c00072084286045401a02c44400905841705e141c0c544891050b602c0300c0314140320705240080181038140b548900c1404070981d110810710281d5503090241d0001094a03000804c001404500801c0d12280201d102410310554900401d0940d228a4030000c2d0000000000b040a46400c4c20050809a030701056907000e00303040c41401c1e17101d203011810b050050344c02620f00d030b0300302d8990303981150829140b0081458900401c050081c240080d101c5c3d103000c824491a2422000605034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 533519487 1250 533518237 533518241
    0x308090405061c030f09080a111203130513020405040516030e03130e0a1104030506010e0106080606070f0303020f0a0206150910090506041808031b04081f0e0106031203 74
    0x30b040c0742e00c5030010480c0c02c110001c5000c0c04480c4103a05003050018811030540c141c456422070351246a203030103106030007001c02a140300442990003044841c400e10ba44d9a41c2c45956034002c0b610f42e4016104401c0c010302ca035107001590f0b02e45d861a1503802500d015280d80c040340540e401030300d402200032100ea02c60101d003034240c01124031a02c44100107500303281d030302c0e950700714424010310506106039500c0000c980d00030150380000e1813003010041699a01e070350380d00e01a5582d5400344281003a2141210000c18a00c0c818004503018030001480382e070914091341c58100762501c0703002c411800d06600700150444444018040c0258612a402801880c5441100c4000700140da08003144100b69aa007044000000000c14030700b40d4415040014195407110082801008800c8103038a03541000000d64040100b030078019031055254030702045210001c61404d14060186001c2c02e102034001ba0301c9494002405d0f52103020b06100b100b0085054220900d00d1403c68070b45400079504e4440480110400075014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 533520737 1250 533519487 533519491
    0x20412080d060e061c0c03020306040f0506070e010c0b061801331707140403060219091a0f040e07020c0108070503010e070c02030102130605031e13020402090d08040308090405 77
    0xc04611080c98000d00140b10456a001100c2d03070105c02e00c0d01d81007400600030140c4042c690150031206c0038245403c2c4141c1801014070115200e118103000603440300e20408400050020603110381e0703080007d656880d80003c800411542e0058440707040102094042c0d10410b00038000098244512449050b003008600031903c400c1030b1000f80fa00c0050303a546d078004106280113044140c150b04588424400321143e0b4003e008040755107402190100602c013595008000d8070360300c0c0256200c0d002070210181c81286042c030881e80418040303801c0811100c104801410b801c20b08410396841d20742c41d0209011402d000351071b4440103901c00d0001d00217550700800820307084107850501d81c0c00e540c9000c0c0c500c03500304c0004205804201d143c403182c4003152025010344548801d0403e44041303858892030b0052068000300d617601c8114130a10451407201c0010101103000c2d03030017260030000000c6503400b444003940c4811421a000281e030310041e00030421500141c0b01452040c0e004640d5024203004000560f000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 533521987 1250 533520737 533520749
    0x2205040e0c0a050609270601170907030809210303150a03051f0b090f19110d0213050603010f0603060e0106020d0c060b150c01050a020f041206020412080d06 69
    0xc000341200540e0b0740d0031007920464004550f403c2d65401ca10000c42c0300c094191800c94180c0305e1240d900c44403078005402c0c50384208800e82c0c03400304911240101c2450450103a880c02d45540080c0b100b800410b0511005120480000e485910402018252580d0120041c1142540d907000402841582841144039101e030140072655000400d00390345586480d14002d03202601402000b80000450b082c03160810022060001c015141c00c0c41d1107000341001c4003048541ca09400c070400b001280250761071003940b0401003090405030404200c00019402036000004034031125078140d000140550381c03040254003800c08d41030341c40304039071410310050181c80700c0741c008140d0b01c00d0110052060b258001000350b889081894844181003090800c03800409025004a03002a0030b00c24002c50401c020b030040071880c1d0480020800f0b644d0340300c48003040307004113030803400c0d107039410441005a41c00c85865015840c0c01580c0051505642c0d901320030f02400c103403604a42050300454154030304600c2c0d2283c8001041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 533523237 1250 533521987 533521993
    0x110f130515040902101110020d0f050f090d030513050f0709050c191d10021f1a060a09081603050d0e060901212417030708030403052205040e 62
    0x241d0340c0e0014800102c280151400c00a460710101e0001b0420000c2c0320314070b501d0a070115541c90414454030060980e01c04002c105d241040c020440038205040d22510520307102018007003600308400101d02070711001c4c140380b0245c00d000d1010404a0424014031465000b10002000c55a14000c056002d99400400d0b02050680c24041d90b903000708030100c0b510b9204c01918011311180f0a607a0040899049052429000600405407104450700000d4140c000048043c000c00d0188c000c900345801e40d00c000035040238041482621601e6800c040018060a40103403c0500e02c10b510b440302e8130f141007144006045c80d6074002104000340082401003140c4100c1c035180c98402c3c403100d4401b142c401d10401c00418100480307149845e1403450381003103046030f000c0005070607c4031708000043d8544660014110701904024900005413805c4201e00400c0740c8030742880a582008040c0c1c50341c62880d04018006e4050103402c000c12680400f001c03140100465816100c120140e0400003484120749041400c035043c0d1b4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 533524487 1250 533523237 533523251
    0x15041508061012090629120a03200d0903170309120a0309050a0f0618150906020403210801060207061b020f090112060507050a0c110f13051504 63
    0xd190007110303034401d810030704282ca000d00021025800030644040d028000c180380036200306c0c030392066a050101d214007201d603601c80ba07400f81d0100415402450803001469010584060020f800f070030300f0f40c2d856854004d140c0e0340c00c0720703158030380d1704000c4681b02c2d0f040011000741e400c1c8100030410b07100c0c544540c00c602036a401c0d89002145035a03144591010007041580c04211503110b5482900f00016141e8040305540c048921440c0c04400b4610051003103503074a007051013104441d080000e2040c001900449502016100a1401030040812000a0729595004c01c17011002ca0840741a28046400b909080069100c00c803000801400040c5c00007811508010001c10919074401303942d10b4001d90504805022040510006142812401589811002c00400020f42d514170f00491681d9a0241100340180d64030210201d40e140f1802c004070021a5001c18540007081803a01d0203485140b01420301e40c6120900d0000642c00800d0300f2060301010b4a4104001440c10f0041640c040c07403038190380c14070480c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 533525737 1250 533524487 533524489
    0x411160b0115051c050c040504360f150b060a020a020f030d09030209060a091803110c13050a0902040501080c0406050f0603181005130b100608010b0a020c1504150806 73
    0x160b2865034000120781c1c0c4405c04a001e800c4190202e900416006004101c0800c0c020203075011902c03420079428001d4511a13418400c915000100c1d00303040e03400344420011030216600d0b49a0148400e104209040e51100131400c4e90300c480000b40071504580d0000c00c42c41580b44100501c01407503010359030007034005011044803540c10240880607282d04403010b039080d5a40300c000c5040b4000c1948806545810b106055804202c00000d11894034040e6541041980e03152031400d03590b81902c7c0d00c0c250030000c0c0130521903450103568089038005c40ca00380701007078000c03035a00014140d89003a0404040d0b5004134480800d9032900d441800000c01090701d030140e000c546080000d8803800020460b075000c40c030070740915240c0700d4144100880200110341c01c012508082413003070440064030310110b030440f20b0440400c5400030044040b10407180b107aa900341c182c2c3e00744100610141c025080c20410b600c00da018034140e1760380d2640b2240d50110960030841e1143d00c1c200d030300308400850ba40309600380141720042c400c0d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 533526987 1250 533525737 533525767
    0x60915050906010e4e06130b07110f07060509130e03031f090908070312050907140a2d061409060a0c0807030f020d030606020a020411160b011505 64
    0x20a140c0120551021403061000101410a00c17074580351401483c4d020322040c12081c1c080c2810040c280100c8101b680d480020440340c0c1c1044001414488205c00092aa5807240314210142d507480c01c141c0d0004141071205c0e910f440d40542290340407507004104080c0703d0400d1800401100d880d46810301c250b0003080c0400e9201d101c003078440407154550120f2640a140210300000003481942001c0021030414200700c211b940214408070000f420203004040c050303e09010b454002c0c844100500a00b92911000751140d100100e0b190b604248a9400060701e074142c0d0b030303084840120700078403083d00c00f10644698003100500e400c80020302501d544101d101d000f0360815140310803800c0d16002c2e5210f26000d0181c51f600010b41c0c0003404280006407240c20141d102e110740004070b0780c5400700e0b140108256030603004c0c2c80060003001c0069001701c0e940d00246c0b03060340281044512004643d03150100c40e00c2c0411609504d04015a007c80350940108000c6c0455450070300c0d13070507940c07030000e0400300c81c003040c420 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 533528237 1250 533526987 533527009
    0x6090c3f0f0203100c0305070305040506070c0309080f0102070213110403150609050c090f030106121506120311070b18061806160b100303021f060915050906010e 71
    0x8000803901180d000c000d0340781222581c807038004003141d03880490407003140007a06850910700000307424800440c807824001d0040a0003a03601001601c2c0a9955005c100c5e880a801941501006034800f00001c0b15207040c800d541c0d0038100ca000150366a01c0c14018001b440ea010b42901007000e00e00440419680c6041c030503501a03030350007041c122020050650b240040d1009421154041385450300b8010f105007040014040c501c0c0640c2c285d1005070000040608076a424410400c0d1480e07000d8001c0000b5040350600140480b54260000d4495100c010307405004244a2080f00462840101030105110030031451004000e1092668600702e4584803017100e049203148014094100840c1d04902da1400c00305666001602900c0a0b4580c0703001e0800d0040b40c114494240c891000c444040380309038500b6104442500c1c0c05070001c0180c00c00040702c404010340d032119007029103030381c5480109409005c0c5c0556100310741d0805803e8502d07030a000400c10b5264000c0d013003505000761050b691030b0702e0725100c1d1046 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 533529487 1250 533528237 533528339
    0x3010f0302010917120705011506030b3111161a09010e0a03050a02150a0203102c07110a060219052d040902212d04080706090c 56
    0x55106d00039864200d000d0212a007c5844485a101001c54034940c03640c440a40010100e0760041e41c52041592604415100b104030040b461203003262481d5414650404c03200d0780e4440c1070691410b4603c0d1100c2c07140b14a07103c1d084890104401d01406100e8644482030740220780c00008010b600b880c051110766030400710308000c1c14004003140781c500c0c080c002d1001c40c041c41c04411308480316241c5100440020350003100c1018101e0304507500440c0841c841050901c2c0c050003d050000c5e0940b1152441e01490001080a810030080da03101d112110018400030100c0c81c0325050151b100e8030b400601e41310a5222803840c008204c4240060240c01841d040825020107a4040d61103542c91015a01d1041d8440c0d0703007040c0401d50001900c240f034041d03503103106c020039001d07844003260710340758000c42008407407000b07200304204d18116601c0701b410041c04205681007031294042d0b0303250110700c7e82c43c08181d407000601912840442c181c00c100e0106001e404000c5011144410700c200c148040d003043d030b1a00407203062 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 533530737 1250 533529487 533529523
    0x2161202180f071404050102072105030703020a0b13080d0e030c0304140a050102121b0703021003050901110903210403020607080a14040e010603020c1203010f0302010917 75
    0x4040d5203981c0501081a81c00e50161066468080654220418151a144005201204c034929082100d0054505a901c143d010788440e03840c0c840011412003080301c4588202e0403100788000041c00410081501c2440380e0013814000d0b0b2075040161030444010151505441032143010000242c2c00381c11140e5a46040600140007001c01811524501030412903241d10300c000030300481e034501881c0049030300d01000c403500700c0a580c6510049861700070000d10700d291064140100900c504c081303100080f01002034030440300b01e0f03562500041c04110440c4001d1002c00d0780e071401c0c082811000c1c000d120b00c010b81d03010707541d01d40610800405c1d07491003c030ba0003050458250001124465107181100d004640082c0025286e1405060210455000d181c0704030101d911158820b0300103816405440440c1c400c01d0100340d2503843c22000b074002c0c0d800f03580c00ca19940100900c1e60321510708500910b0281820030500550b20b825440090031504c2607810015500c00a032700e04061a20000954a40400c07501402d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 533531987 1250 533530737 533530769
    0x6330d030207050a0f03060f0b03070302010516060f0e061302061b010b10020105011503090503040e0a09060524030309060406033c0b06090d03140408031303030806010216 75
    0x724200107aa030081c80d0300441d40c0000103102244409020140c0c0d0050008000c981410040e80c0102c401c00e05030740b40c240c2c01604d000c002542c00745000e048070325480c40920509500c5559900107c4030b503410504166540c94001c0307556036008100d0b45511a114940b1085202802e030000b621303a00030000082140b4200c9034800603490000c0d00080d0701954080c003101480850a00b0203030107482c09018040076800b0003551401d0a5110780a2521104d40020146280c542054034401034410000c3c60707004040d449201c4e20b000100c0b1441014403507488080240916071041c1c041d00d00a80c0f400705543e119134800c0c05401800e0390342c0c800310380c102c400e10704001078191140e04038000c100c480000c948044142c0d07189025054000d80481508440c00700070200070012040c810009075009902e0300c070341c01c50a483d0949000a00604880404031030b1207070b540d420556a0504d003450743e0b1001800095060b00110100101500a01180d420140c240054142800c109400d455080b500c0d1069000141c15688 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 533533237 1250 533531987 533531993
    0x10c02030304273c14010b0903060f100509040303020405091e06060a080a0c0e120114071b030e010221090901060306030209040605061309120f05030c120c0c010501030506330d 77
    0x807201e826411712191000c503641c1d507140c00401c076030400385a0501038060305c4001000070311003003800d9102d017050015000059042106001120400601c00c43c1419401c2001055a0351444807940c442d0162410000110705030941c102800c42d800340c401c030302850060104150f1207030400360440c0d100c405c210000415000440003142d51040500d090b64100ea0400e00c005540c0c40c0642000ca00121284501d02d81910f44010483d40701c81ea41c84a04414803c840700e01c0c00180c852008640609414411618079050310450242404840004009544800a103005007803c21159003401001c49040c2044010314513004504141c10041c801070a007030713035040020099505c1c504903e410808c0f0113401c011001c004d242612a071003120340b85101150003050b040007428402d0301201e1203a801940c038242800da99003c2000c15010280008008881c21300038109018000d2044074001c50141c4014003260403c09901e0740e4103000100d80c83c0d09001200f056550506040040c5900d00074141c5040d4401403480c2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 533534487 1250 533533237 533533241
    0x4020c0a0f0c030b0705041a0d14090703050c120a02090c130e011805061e12030703030b0a060c0c1a0d0509010b03100e0606010c02030304273c 63
    0x3140080010a00101140910074690710001c1500d1241c11809116198800d0a658078000d9100b08600886841c01d590105803414014002c800c5242c0f00103e41c0f0b054051104012203000c640d00181c590080c3c03010824041c0c20880403905141c2503801220003441d00210329110099014080d00601d07128000c07502035084501291f18681c00d0b1a00e040040c2e032a8042d401d0681028440c5034010b500d844012001d0300114030030f0500030300300101003d880c018044080740102803a11001c50340074112164202502a0500091a91501ca03a80006120506800300b00580c003840d00100100410006034000184100e40c00d0015210b040403c0c944010740c60341080b80340d03c5111440055039041405100c0e0440701504035400081c4100c0a98811800141c03201e0101d03103401160408541c0300001240565003e460628003440c006825203140c6500c89003680102c104a5003440e00c03040031421f1141e07080c089403142106007225400324880c1c035400c500d10b8009006407844c505081c2030010000c89001d91882e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 533535737 1250 533534487 533534503
    0x9010b03010923010b04050901060e010806040f1404080403060c020a0b040320011d060a15140301091208090610080d030e071503090b0108060f0c0711180711010b010504030204020c 79
    0x510f0848403568441c006003410760001d10600e400742a2610000c501c89020303140300d8800300703010782d5058001d603280703c1000050541c0c9041e0718101a61600364261001025808901c81c80c011088641d46a1441c94030008441c0182c03196800c5402606d80c1d10001071007001400d80181c0c05180507900048801c00c0c00510f50300c5145080025807800451074040036258058107150a41041a81d13040d07510b4440c4501625001101c59950f000341100a01c05a9010011b02503400b5003d80000740900061392440c406000c42641381011a00d20400c110000707504105455011102103026246589404025039031800c40c45100c4050603240c9041070034040007000110014080400070294100d21080050002d00300c07a1700c01d03a0384440c40e41c00411103040000380c46000300d1040d46003089603512050703010056040b04000b240c41c107004c1c03180c148140e07550042d0003d03a2001d091360440075080081c0090402c404103081e056044c1d050941342162a0781040030355084980607a03015a07910341503040f0310304003121 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 533536987 1250 533535737 533535791
    0x7080412030b0315040501050403121518060317190c0809040b130f0212130203060601050d06180f050702061510140a020102090a08011104260601030302030a0e09010b030109 76
    0x4c83c0b0104410b021054102038000c80c040d0712244000c100b0107900c14290740803c0c07032000d440c0c00000d0042240d0704403445010003044080300000303034040d16991007a10104c40e4021095110380c0120700d900c0c003016042d5105082081d14100311036212000e645111250141d040c086101e9940e611214800e500c8115410060364400f5004012490f600c80e803c4000703411260403481c5040c03602000680c2042c900350860040b640050081c03540d5a58400110303040c1d400301c111001403686400c80045d10a031009143c6d060b02c0f10010001c2121132805812004480009101c00110b50120050080c5402d101d9264001c1b1a820380742d0740541c02c4008030a584220142007900010000081c500c442d499040d030240206200452b10741e61a6036075581d081d03080c2c0c0e4003c03011084660b0100020043c040350401031244a500514400740e07001c2020803420309103042640300341d0158000081e010600341d488443c942448100300e6000d80d0301c1d4100450f20500f4041401401981b994a102040c0b04011060440c00180c1c6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 533538237 1250 533536987 533537023
    0x9050408071b170606030319121505092508070e0303040f080d0c0507060c0311030a090614070b060d050102040f03050c09390d060f03050607080412030b03 68
    0x180ea00d0040582c256244542d03080030400b44183d6612030004902c03980510002070045040000c0030800b13420088101d840e11080c842190613406801405001d02d5055200d54046020304914203000c2c859046c0c8024040b01000f401d101000b075905010301c4200150f80300c1843e106840c0c0d960842d041e11111074082d102541071001080008204c40704e04030b440242d070448410303542d200718071090907111440d00e007200801c2034002ca0400c1c4026482254041e040d14040c1c604050b52403104907503d820f5a0040300130100044002c3d42c03e00c0015000000d804c0c182400ba40c06500c2c154603500d0b02841d000c07001e800d2a02c20100e81050900b40002501030340d000e00300c500c0c51881c12503501c0c50a507684030000001c09018802280015005c203909600400c2e40c00340e01840301002d62401c005070941c44408140d0083ca203101480700501100c140e11414000d8001c1c4207030502e1312421410320314503001e0020014020824401c0800001070382c80b00c1b141d40035008074140030540100c4070300040d0030078030b25014001d0380b58 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 533539487 1250 533538237 533538263
    0x60501080606071209231203070b1602030910112e020f070b010807061416080a020a0b010b07061a0d02091504020a0e040e06060609120c060304030306030c060e0108010905040807 78
    0x8001d41503812140341c0455100c00f2808441c2c1713a00340c42740141040641280e03042d00000700781079401c4444150b400380520540f4600082d40c80060b4034049100d03140400244d000d034404540c040e041124003a0340e055001075080f070b0201c11980f051030400a404400056401041d9030814000c010b0a030ba689680c440c2454003290703100d101c03541c0d95001c54400d95000506106c5061204501c5004840814034204007081c0b962803151a086280e601030020041144541c032070103001325176141600340c0139000c944c000c80e40e5202076040c5041925206140c0c40442034a4180001596440f080a140c0d0150305503181c49856a40c1c81c20340708443d6004050300d40290001a55680144e80100080140601207404125011b004100180c0d1482e0854445c1d4008a0802c1943e040d482c16a0904082c240e0b290704a030381c00d40020f00030903569042070b102100440c0d11403506000300800742c210308029110f2440c0001d0003a400000003404c001040c864104d00d1a0381d1004a010700041c038084030101500060303420400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 533540737 1250 533539487 533539529
    0x1150b182b0b280e10050106020c013e07080d0507210905091801060b0909010b030702030a05180306150a0801020708030606131d0901060501080606071209 68
    0x806003003403045036070703264039800035150400d000102410b40c4000c10b4105909500342201c08002e00d2060710341342071486202019100c60340b1310b0107218042e006c02e030301411105120000141a415103c43c0440390500246460691040c1810312110050a1150360b40d1008040002680c144407142c1c020030300034000c540000030f589070400e005000c16032080c1060801089180076407900340307140400500004146003400c015038582104425000170040d1b900d074400c0240d0390038481c211009a445075961400100c0c0e0011180341603010b650051001a00c2e462851a00001c020749034414120541c043c0403001c1000c5028071404100301381da8000c064100e0300325003005151840d103d62400082441940328100100e000c0320103000341c45525030320100040c19074494608214140c1c0059101009000940382e0006544079014075078008407641594101c6070b410075a5441c1d0940c0c080d83c1025062004200074000035440f080300320380c12150031000c8141d0000505000b00c4440b14503502c04482503840110aa00c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 533541987 1250 533540737 533540809
    0xd030906020c04140f10080712051b0d08070c0f06030509070801181709061b07060219021e03100609200304020d0303020702061b01150b18 61
    0x180e5006400b19110300c03502c50208020385851844640a1104603000f00e00071010070004203400a100c1c040000c0f0090b1a215114070b01040380d0b00072048100c1641810050010a0242c10129501d08041d04200c3c20300c01c02095583c0c90200e0b0041c0050000202c040a20a00c1420303c0702904a076504100701c2036075810000e0203404240d40105090040c2c810010302d200303051059140d17a9152800c01c0c0c0805640340c461941d2040410009062a101000003d0560751514010900003500c0b84266101c2c0d80310100440c07034510b2079040201954840001d00c0400c107000c010091046504981e50707140705a6020400f079540b4402d0102e250148078524580c5036415003a040a000d680c2c80c001c0030840d0021310050038108011140c0880903c1c0d0082021030050704020034200c800034024200545070a507103602040c0e496100d40c01d600450208244a9544040203024051b001000c03003012601d0b887c140070604a040c4510341c0c1c4181e60303030480b2000030015100c00c04a03070714291001c00520311403901c04440c002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 533543237 1250 533541987 533541989
    0x1214070e0315280e01090b011e05150703050c01050f0702010c090506031614032404020a120b030a02120105040303110412020f0a0e090a020a170c09060f0d0309 70
    0x40700e40074100012141580c00408030b84150740001c20700c0c803803c41001d01d484200d461902d01c960b0303003501d580209540102c240141407010b441821070501c60361400158082101078054500d9210303403400400c01540c1c1e5203001c5594400048400c1542d11030b10b51034281c545126a00305000381d9402c1504111074010750002c070030310440c46600203104c2c01460000840d410000307806015809130301480860080c031080300d101c0001c8055800d100b50648503080c00e1480d41d4100f103400550070f8004030419901c81c3c2e46216205400a0700781c81c00d600f03040c107124018142c841c4411440c40300075038842c481c18080e98100b065140064000e000c05c1c112603078403016a4040e000403030701031300868241035505140c81007c200311421500c10644042001e0510b07401c21107041207555255500054a100101300e550440075180c0c01088464010803a400c03951050020204560340702440d5008e5401c00c210118901045900c2c05180445004c0502c0d03644400252003015070405030b54000d6465284807081641043c9444 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 533544487 1250 533543237 533543239
    0xb01050f010201140c03090a1707060b0a050105031902130929030a08211807090b0a0b03060409080a02160f030201050d1806020c0d1412071214070e 65
    0x19015445030801a8281c621640c20488414090f000140030025240c025540159001c01958518515519081c1208503c948884440c002c001240c208003c0c052052200f03906050324141182803600001a000380401040764030003401180418007264541d038100e03010781507407000b8440c50548aa00c28401022509021003004069848000515055101c158520080200140400b0303606544848050704074a50a41700300d12340c4450303045021900345042e0300c40c034101e0010105c2491300510491138031906a0260000f5440e00d56548116103071112800141c0309240e103500da8a407540c41c0450001d007440c0d00045c00400c00421004000d07580415440c0c040300300d090b401c00031a034540312003171549071403403200901040041041b801550f04540010030f42248940d501c14480a00d52100c8003640c2c05194595150f030410a6983c2030389810803000502c4035004401641002445008140740c3c0c100038050f00280603414001c0e80c14050325412400b11003240c11044081b904003000c0103001030400d01051 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 533545737 1250 533544487 533544499
    0x20f04060e040209031207030e041d0618070b13050604030308010513140a0f0e070e180703050a03030e10060306140903091003050c0904091101080615090105090d0f0b0105 75
    0x4001c461802d80240c400c00400200503007104a0091061030b000d90054000314140018071030a1040350303903184500950f0711406d5900b81d40d55014120200c3c10441c00910002c04600c5c0a0071000001d0800074401007644c010b100104e5442d0615022540010a541c0c041580194000f0303011003050f601412583c101c840507140c02480b58030503059031095540020b48510b00441d9000080c181e1002904040303101404110000f60a138056451141031112507007144200d06103d47c103104c3c000d03201300c4a01da074140ca00350240c0032150941d600d0701e4072030516400c00f03000c0507110482c204550780140160000240312100030000c00da500d00e81000645660320082140094100001e240b00b20080704a4039402c5000f04400355a054941040d0000c006c040e1000d583c10100b4070990641e6111440741403c100c1c095a40032810280440004012203001000d85024105174040760441110400546e0300c0307880d09080c06911100b6580115071062070400c40035121003c46281c4100307000c610400e04c0c1c103840007a0b03a0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 533546987 1250 533545737 533545757
    0xa0f050a060801150602030f07060608010c030c08060f09010e041707060b03010c05180d06060504150806010f0e07030c1202040b071106160f08071b08060709060905010804030e0301020f0406 83
    0x4e124400b1000e4810700700960010014411084004402010303141c0c07042d500054050345505105003118054410b00010a540d1240c00b141c054108032410740c000c100316580720040e071142c408503e0f880410310550a4003428034001c24100140c050100c01c60f0050081c10f103803240e2080c10b082002e07203c0648500d0195103040c00c2c100c0660320a50844140a10703000c4040b5040c404d020911640c94020107040e5582039850101185558a50041140303140b15500403c00007410a42110f05180044c4e00c5815480d116400c00c0090901c1091801d40c07100c1142000110904580310685079800c442e070712207540d181b00213030114202c04041c0c040c100b814003801035540100c034540240540c034461058000141c8c0380c013280400c009030b50702e440c5000e141c2c413440406080200503981c02b01d00941000040d06928a554414004078808000256100c440c51074000c041d9883c203a405400f114043c080e09041003000c40000b0185401090307c078240c480301034000c40d5105008005030304107030024046c1100246403111 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 533548237 1250 533546987 533547011
    0xa020d035006060301031101110d05040515071208100f0b07030809070317090f090a02070201020616050304060b010203211801112a010f09020418030c03080a0f050a060801 75
    0x3241d4810800540030342d2940e42103440c0c0d1005407101004460400005100317128412a0511900c46058240e4458a0b03c8608280400003031611101a01281a000748150000310f5100d11900100c02101c7c02c00d03541541343c3c030030350007207604694000d045e90002c0010300041c030104e00c1000740070303560103075941c1005d40d01c07200c040507120140791001030b18041640c801e540d80b4100500040c2a541d0b4000c00080f05091460086480701c40d0846080d0240741d404035a4005550301846016401100c015440d200144070720301c060010300025102030030150b43c1c0c40351600280d000700708841010b4443e0070181182d0410701c103a1100900b046800010700f4440c140b01a03040a0140150714994002c40c565a0802103030401001c0b181010125449134050350a40c1020001000e202d080740c91a07108001143c0c21710765005000580f152041e02c880e10b516000700c1280030960200840c1801a81450600980c0d22840c502c01c01508180d000381c07460308e1500084c81040b11480e4030010866400100910105002c03207 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 533549487 1250 533548237 533548391
    0x170304031b030917010e010e0c030c030613060f0f1517030a02100c09210b060d02090a0905031920070b0a0809190501021b030a020d03 59
    0x201c009000c20b510400510070502d070f000642012089440000501ca1031400400d420b69000d200720b20056048045040d01900742803164044860068008211905021281c604070b920040e501820142d900c60071f500e011401c030780014551544030b40040c060884071604200942005128001c90b03654000c00b0000109004003c4e260314801a4000d0540105400903550140800c110b8000c00c210b801d100c003103209803132407c0301111960740b0301080c040420285010001d4441c0034045520a0040c0d001c6403006a031020141036020051002c082040748451501a241d40211003100400004040c00e0008030b5612001590000c0d1803143e45141e040c12402e1040d0715800140107402c1000400c000100c00c150141e112281c0150303009048a0b4100480310b40045402104041119241d40010700845c150040c03100c44650a00314601552038802c001c080a5550380d10020564140b640300d10001e202c00340c0d003039043c039071200071007071000b0401002d0b0303000e00d817089000003040c0074102e21958102c41c408004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 533550737 1250 533549487 533549537
    0x60525020309010c02150a120c0206010f170a08030a0b090105060901050301053f1015090c030e030c2401031101050904022206030e030327030717030403 67
    0x40e40203586031440840044030300b0983d030401681c00101101d00c1c2e40010840703000800310751205070b481d1080c04940301041c00945074404020300c1154400c40041c011080041c0b440411200e005110a00f9400c0c07000c4050304141c1243c4010781781c0440401040140304a50308004074200003141c01101c66a240e40411521340a80b1100e540000d10a0005001e00e05013103801c09198601c01c402c550080300b00340200f04865421302c500601c40c0c8902c0c1da000d03020407020000c501801d20801c0d0140621804040381c004c15807224403800d09201c0d266510901c1250284d40b01c1c402114030070702525926030400e411250740724400b01039040c40600000203500c02c811504100c50680344c0c80707404004001d4146004440076007040075074545c8146c0c01c12a07941440703401d961488000d01a8102d00b05180d15242000d000c848140a8030034054004004106900315080302490512002200086500341c261220902c1c6002d054002800c51040c480105071800085015621440c801c1d500c494401c550255006c940c2960 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 533551987 1250 533550737 533550811
    0x1305011803121b060903090e130605070e0604150f081e041104050f090c010309050312090109150515060c0a0209192a02150c070302190605 61
    0x560310305000042c91400e0951141155107006611001e4968a00328169410801100c04681c0e80884004254010342010f00400100b41842d4143c40c00b09130b062400141180001c06c660f0b540c3d000503410078095a000f690306400640f10a485e1521080c6c0d100d610103c1c1c031054804551401222030b00711b4807810303001c0c0c46803240c1220b4094070381d51075050016054000e001103804107a81d00b035030241500d60748101446042118460f503241d081180c01641808012207015040604050b002c401040c1c4c0002210004480c0500312940ca40e11812041d004000200004080035488107d10341048000e812183c000c01d0038281c0c110003000d881041251a04c5101441401c81e00448d030b040c80540ba014030303000c0d07001004a030814030f802424207104003101d580354480d19000d034402d80310a039500e01030090801d40d10703024001050a2a035000b1103100200c0000c002c01480c0074000b07800f00070103101b404010540fa600c5243d000c4041201c0c030b808805450101c80d25842c150160560803503510340c240694070442c003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 533553237 1250 533551987 533552027
    0x1060812070b22080702010e06031306050115020a0212070902030f070f0302130b0306120105090f011a0d0b07090e24100f0e04020c030a05090109090e070905091f02130501 75
    0x1409681c1c4c2d4109070000001a41440388501500c445900d5202c015032084117000070341030328031045141c03500403500103801502c01000307d1000c00340082e8000521104c03d82c0c04840c42c21500304080600c61504036560413240000e40080280101c1c4207240d07128078040c0015884040504070404002c404038040c0c5d5005003031000f2071200401040c0b015500558001d58050900009618520304141c00d49005485102159100360101e03040b1400038841c0259004000050218001951000400710210504003030f29034000c02000c100141e000e0291803000b401e1400c514001032500700b410664800710841903c0307001415030001c80b610300d080c01000d11115079645801210410440e4221901101e190310607800650030803610f08642d000f00040c101d5a0000d507255541e600d603000004211740151307484042150705201c803401c1d0102c00810500141c900100d80041d00d80e6031201c04503d040002003506040444408810302090b409400500d07048800d0000001015660001100c80400b148540318000d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 533554487 1250 533553237 533553301
    0x60601021203090118030801051309082a010c020d110312012303010915110c061501170f0106031b020717071e030b0f0108061801060812070b 62
    0x6070080081d607000707140100000341030380034062159880c030510071040d800f04280400400c41071400f405450f0640908000070b02032018a940d40440b40e01940312800c0300c0b12012000c4044000040303080520400440c0000c1c8846c5200c40b10181d12a040c500440000540e69420704024100000480b00245540b4420321910703841e0640400d40d10a9000e028ac8074401156207054a5540c00d00903107010502031040800c65960890520049030298841c1034001c1c0000d002da04909000440e03810391141055140c2d445804515004a69410b00b40341500d800004800c148010100d42c5074495060325442e403002c00c041400c0c07044403070581c255049094010390019806000b00450b10307000c4038006685c030013101e413800c2c7c44541d104040c46980019400c031100d0305c07000304207220a81082c20b03000003c06071409500d50404000b40c0c2c84c0c00c0c000b03040480c40a4441e08540d138000b000d40c00003000340070860a4940b1100c1c2c4041d104920303482080300b9107443d07903007001041c80424441d048144604001443c0c0c0254 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 533555737 1250 533554487 533554513
    0x3021201120224092101060b0d0b011112030a0207021005070510150b1c060e10090615030e0f0613061b022109090109020c010c14030a0f06080109060204061106060102 73
    0x80114503845c94900c040c01e11880425070000d0088001911000c8041130b100c1204440c0c8404481204007000d0420440712920308001f07402013041d030780300446840c88503a42d41d51501c03154007078801c0d0200250004541212010800d42c0702002c0d11406201d4016074480c0e002d05410002075500907808801d0081c4180010845181c40800526031300030f0f2100004441380e040c0d008082100c806600ca403403045101010884031800048081d00070b086004c000f0000b00b42032824100740140d00003413000600d41c1e01ca12401042000b005030070244003100d41110094136000038000781d840d62402040300c680d4203041210455400700c114050b01c8200a500a2180041003100400101c0015195854066040001440b40c0d02c1d5580414042d04d50b146000d41d44c1c008480f200c0d42102c050709910010004c4c07410108101000a400301e9411158141c3c000c1060056040f030314008014907441101c4562030032000740200207090b0090070481d0899107495a6003520036503110386a21041780c290380140c101561010107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 533556987 1250 533555737 533555749
    0x50a1407050d09080706050421080a020a02150a021c02070803060906010507050114190e0a0602310302040b0a150309060b09070305010f080a02011205070302120112022409 75
    0xc0707441c14030b1000c121070040e82c6450b00142d1104906844642c0c4400400c000d12040c00340c14100c0001c511070031458449071041c000d02c2030b04044d02042080d5000035404419a208000c0041082c0c0c0d00f0700401c003a41070410030b001c025488042c810134290402c01d083e2440d82c0413407007554001d641105485145555441c10800c4150004200c10305100090100c80d020600910401d0030900d80401c07040001c0c00d01c017140c200b00307015001000c2d640d6410100d0003010600c0c0418417100c403c0d032204026840d00054101d00e484040a220603441e40380000c064240c4842d65802241c0450b070003518100555070701c590034000000c0043c000c03501c01d1590384101b110854803c2e4000100c8a00413003002807030200c403200041d99944c056404c240060b45a10041c07140c55040d0031040010680701e4014181c0003030310b5001808080541600e000f0855590703000070038480c000d4044600790360040d2800c880c4d0350786403c18070121075200c2a060380a554289102d6016410300c003510103510800023050ba041644d01c1c010007413 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 533558237 1250 533556987 533556997
    0x30f0606040b0703260108150601120c0206060406060c0507060c05070f09050712050105151e03090f0f01060f05040c030605060c010b030f032803150e0406050a140705 73
    0x60004010000082c01009081c05003440c14441d81c0c070f10812060404500d0700c0511102140e0300780300d845000400818000149201540304400301000c1c0d02c1d40da0b400160f40000344690320306c09403820b02056522250b40420501d206032802c945c10442c540d2204411102181d142030010f10300c2d40080424001c690003614401c140500c1071b402c41c0c0070240c44804440c0e800c40d466002c604080c1d12001403104854121440c8080d0300e0120f88100499072411000840c0c13008401c0c50f410000100082030041050151100b070150032881144c04d039039081104495580c1c50f44400c4040706401a0740e0403003407460041c0114002c84414114480045042508000013004945d4540062503910140043c003910340c44058542d0110290000507160181d0061600700025100703107a8045d00104654a094640c0c003da1108200b035030b1114250213a2030322011780081829070748010b004107030010001242540324442c684230764440d5105100c247c45078011103044d81c0c503111000e0001c4c5040000501100d103d000901 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 533559487 1250 533558237 533558239
    0x4080306060309160f03110d030203040605130f0806090d0f0909020a03020c2e0209090406091b03050102071202031306141b2118011b060f14010b0708030f06 69
    0x14904000c9040480c0c004d0343c540d00c2054a240310b0202007041c004500801c003650b01003660824145520f607a8029220310446c040c51007445408a10740c2d10f88400f083c08403014121041a9110280d1110806950b454048461828030710840c520a480603115440750100ca010a4076130742003280c04c0418010107508103217800740c20107500380405410318504000c00e90b0a031019114416402064040d142c4000f54250407403031400d4010050844a43c4804865039400394208800286525080c40c1c840c40c456072086600f121852125000300c1880b01c194020082148101c82040780900318440aa03100e0143e403011040a00714003c00b041801c0c016262038035440f4010741070380c2c1b070a240111000040d010051050b400c1c1c1d8408a1600e00d000c1c40c030010360b8016050100103500b042040c0c200d25a501c1c843e0807406040118050b001c03504190441203010440303610940c00d000c0b2007525400c400c000c01e40c0c2641c1055520310349000044007910041228000d940101c0c0040c9550750381e024030240781501622003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 533560737 1250 533559487 533559493
    0x2104030c27050f07020c010203070f060e030714010b09010603050106020d0311130b041a0f03040f02060708030c0307180b1209030405030d0f180b030a0c0c02060c07030c0e04080306060309 82
    0x3030310301c0d080984992031203022500d08107020790500c4107000b4a0442c40c5c1c12882d065600420407240401c9081905040250b40304801007001c1000c001701c00c0c2107014440c030081420140d40d0951410b0b29040d00400e505110640f410841c680e40c84c03030201c0a5030300038401d600141e00b00c0401002480c0c0b00307400100810a0022095280500c07400f40200c5240c1c0300c2c0d11128030154040350611003805020405032480400282c00307410b00018100701c141c94400680b000300f400c04813039440b000b19180c400503250103c0d0050141030f240d14081800202e0350340700301c50718000243e807103519082030100c090080c400d9a6030341403a1403c049080001d43c0104002138820b92240c807003800001403650f020401440606c0603a9940d903500e440c4220003800300710041d000c1e540b81038450340050010040150981b9403104c10b45102145181c900602569041125407004c0d400c0407000440081002c8001041c9040342e204011140e03031540d48006401d101c2806550003422004100b01040c100d24212000d990400707682030035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 533561987 1250 533560737 533560799
    0x9180519150321031134050114090607170703020c0f0307031110020a140d14040506010f0b12060f01140a022a09220804082104030c 58
    0x2510b40c990141590042c0107070b500c1031801e03003c83c2d050040708802811103016508203240030007400711004040440300c045c038014103a417500302030107a4051510709030020000c0000302e03000315102c2c882207403c546900c500c0c42080082021548a40030b4410706410a00005c026a00c0f1540300720042d51001e10b4248961090000d92000403209000030700d00b0741e109450746a4070200a104003407c000d0303008400d10706030f8418070486060603040a00a0740f01b048200030749507038064040b044c1c2d0040101c40300c9110786c0d000341c4040008020700001d085050360b601090010b90142d80704c4540c0700f50301c507941014448a880d08003107100e0782040c60804180c98014100b45541c1040e80ba040c600e15042a241c2100681c0000e08141a030b143c5200540c0031890b19191508003104102c010403114a0007901c0c10b5580c281c91441101040300509030490031962108000d9941c55840c418941da40c000040380d101480c280840030018068503108560031203501c10001000689845009a000380d00300d2036001e0f4034008140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 533563237 1250 533561987 533561993
    0x140f070b010e04051c05190516030c05060603030f0409050601021c090e01060806010c0b0711150103020307141003020a0c021c03020d080c09040209031c091805191503 73
    0x50001e0180815500c0c421440c503240c01e20300d01d070000369842c00c030b007002e81030f403006102540c000c0440d0301703001c01452041030325101054103c80034490004110241c0078030301c00110816600a6521000f01e0240040f01e00544480003015200d00c100b0b50391200102d4100010000c4554a030000c03a13204034140103540106e8072800529200c40070044002d400113042e490203100e07a00c1440f009a001d071803149061802d91030100d001800c0f0060175000600303002d6600000840c040c0c41a0791b1070000001100c191204010070b41044000081d080c08124464010314002091161902400d1101c1580041c000d8106100441e0140c00951090500c10b0030840c41c90900c2c0c0250300d03400d104007441c03054101c20f4416001c10313003002402c1841d5108a60f08010541007444500690b43d0103580100b6070442d001603039141032400003803070710704118803002c1d807605600d011410458010034260100c0340e0100400090030410b411400032202c0440341545058501c1750801e0520784203038403409641d40151481000d050700c9032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 533564487 1250 533563237 533563253
    0xf0206040e100b0421140313090525080c120412030c0201090c09113a0e1b01051c060602010b01030605030c190b03010b1b030a140f07 59
    0x81c00511030702032801c0c01d000a203820380c1941d00c000d1018252007030510f170a00400d90070003801c0201c8842005c2a00c00d015003406024102890000303030f0075040320354401c084615209080418400d14602c40d1400700000c00c29441c0c0c0b03400402c400c0c041c0c8245074103900d4000b0192050311014003120050300b010701c5100c89015100c8202402203014000890721090303010300040aa62040080000310790400b0b103810009028241c0c4c1c1030643d82c0c100310200d903800342c803984c21040f4000c000400102c5e01103400101e1645c10002d5030f06448411401811041401e03030880417041d2001042800c010740d00030200d103d119100c462580d40c840c40305141c241e00c0c003211028110008070745940ca44032040c0d07641c481040001c0e024810381d03041050030f007003d2221914000000c0c0d11030143c0c030341150041d2019480c0b01c0c3c0600725020709401929082c203030a07450356115000c50890b5041580d02d1b9020b46d264000700c441842c800400ea031002ca40950322000c88401016220745071350040380950001150500a0400040c007078 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 533565737 1250 533564487 533564489
    0x30b041a2b060b042304060203060d02150306040e0a080d2c010e0c0d08070f060b0604090516031a0f030f0a08120a090305030f070903061802120c0a09090f020604 71
    0x58a0208840083d041000202c07202518500840100154a88044480c4032600c2e40c0c015084200140c99070381d0807011516004401e40003c0d81300d06000c111207244c00303d41d0091400f0f8001581c0130004403541d030503500e5075662000c401904003501440400140c55454005d80c4014001902a0300c608141101120b03200c2c8000300c3c0d0103d240d4440c00350700065107041281c003850680031200510241ea490305c03912094821548040d11080c00c81402c1c2c4141310301e641114110b0a00a810075681d995111400401030406451f2070070003100c66503007481c0c514880e0142124002449100d41c4000052000308002001000700d03440e007601504441c8072040c06d052099400180c040c110701940d4100340c0e0b1280b07038111001440241f9141c40d004103840481d41c04401e5960100b8011081c001c0c50300d03040320589640304954402040607052010380c004804841c52042c3c3c205109550903280e12007070740155601c80d141c4030345054000300079000030441c240c131541040400d58001d400c0c0b00b0148074142c0114469501c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 533566987 1250 533565737 533565743
    0x1312020703080a0f020607030209060a0e0a0e1006020c01020307080a0c0f08030703020901020c040606020a1506050301020a0e010e0f0108060d140303090706021c090e1f0305010b01030b041a2b 84
    0x21301c0240866040d010b00207998058400e246c110b16200190001405034012a503102c0100702d101c1388a0500d0340c440d03201c01c002401944001d860039240c50140002440d041c0c0c0980350050040c403401d440341e0750001042d191516070141040e0b05282144c003007107500c02541d050541c2c4031340090303000c10b01251401c0e005602520050f6405a500e480050000e0703d02201a003595000714a02242044441da0105100c00c5095008440b100c03080c02c22201c86020b070920b500311607495480010303441c40c0b4a421220212260800380c8407000000504810810300e944003008150204d081080040c80742c0c41c00c81d02c540c091a218141c103000c61f01540044601c2c50708100c801000540c00410240300e40c80d0100a0321580c0c00300511410f610304a80c4000600e1a00c103417040c1c2c20b11092103c046034046903105501d0a080e400f1601a001d040c0d038034204140606812600c1501003490440c1401c0b450409001c2d4007103889030040d00da4080140c00c0248910a41032820403c0702c811080c00c3c02984821541c101424640 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 533568237 1250 533566987 533566997
    0xd03030209030c01020609210f040e011503090b06120313031b081c0806040608011a0a05040902010e060c0102281403071b14120c060a051312020703080a 67
    0x1002070501d403901c60316030b00e8a0b040d54045420040d9400c00099100d174121382800c000d5075041e80c54001950540100000058015408500462000700c204400c074122100d0021024000074440000c5c0d0489840403c00303050a184c000004491741070540014002d05020f2023100c0c54004000c0380c100751a0f500b60000c80da20026040c800c00c0fa0000c1d905e0784800380001c400904040070304803060420320385502d0703010700500c04540c0c00180a82c0d110750003103008041420082c00940044c0815455030280d0303104c1103102e46089030f004120b500700761044900c2d059041e103803041c0701c0b03039508200043c9400096030101d607590204020a40b01d1400c12034603c1009191203084982c044244003d4070718050304000c0f4052420500c01c1010b039a07070020741c0300c00c80440d078840100c0551040c20585c0c00191000005402c0e0f104110402c0040c010003001850084804816103e40e5180c01917481c7c03c1d600d00361200b00540103109280008a111000f00000c620703d05e0044541c82a42ca6441d04c5842e0803e040b003c0100e1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 533569487 1250 533568237 533568247
    0x804031808010f1d03180a0509010b0a030c020c101b020d030504170d0807180b18011206052209050706030911040c20030c0105090f16120f0f020d030302 67
    0x1040c0641c86142c400720b51603020350918546119564002d24100c2800d604520300700046ca5110805170401070700000d031165401e0b6850303000c00c051342c0c1d0101c01c003040001c0c90642e044801900c080340380b940c00788006105280100007001c00719240c021051040030040014945800103a4641a40406040c401e803a00c94039945041c01c8045161400901c08200e600300d440b011a1695000e0310310b540c040018202400f60116aa040b10301c84102900414241c501c0001c20b03020b00529640040300304002640d03004156042000740710162180361083e40d41001440724a030a5441c84200c1181400001c61000901d020035900d031a0b1900810398401004070ba030b140082c5060103030150310b0070702c20f61043e40e090001d8001014000d041204020041740c43c11100024050410424803ca550341d84144009002e08d0414001c42c40c0c9905480a000c03e0a118010600729122480aa100110340c00000907022140007900c41420a14800d0350071035480303074040484001a0b503144c600b5030346280070780c0e0010f0302d50b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 533570737 1250 533569487 533569511
    0x609011703090d0302071505030c090d03031404031d040e10050403020a200103050f0906010b0f042301020d080112081b0102130e0108150c0702151606180210080403180801 75
    0x203501d147d01008200001001000080390f00502120102201520030141c1a5030f41c2c00c0460040c00c1d034002203c0303150641024481410380c000c94040d60041c2030100000c0510312801003008032581d400c50000c4917008490010802e00c51588107650207802801a66410441940d034200515210101d2400c500543c02c00f1100550349882800da0064450390014014100100e581d036560b1414424254400d0000600e0980c0380980401d6900902c0440000c283c0c61102c050754803005181901c0d01c074014464103c1b05004603128800460480e0031746002e95816a1503601d80740496030010b9190030041c0c0700e402e55800942c40c24801070402480c21080210060300384503500a26400680c46080300368030004009010008403040981c000400040721680c0f11080d2000c11002140c0c0514482003070401300c3e40b240760b90200ea0103076804078071540e010402cbc0b130b800d804590005a50f420019402c14401508131404500409426820034001e0600400000070b030348030b902c10495150448002c9035160102da1081d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 533571987 1250 533570737 533570759
    0x14060915030a110403050307020d111206061306030f15091a0405160b12090705100c0501050703060e0c07031101022b18080d0e1e150609011703090d030207 68
    0xc00c1d80c10400301460030b480c3d5186d01e65a4094410040c0c81000d201540d0800c010460401c0c2c034191501800340710311454200300d11900c50404441310390060003854011150079600c0d20805e0706982d449245003900d0f0b211a06c075000724128600c00b04101e581d40300c07002c0c0c0105400b00048101c00300311402c00500d515291034603a0034411117691582244c0310000c0309100300046442070740c00b00c0000d104040002c0d030300c88907024a444c030307280d01c81e681105607a020100380940c09800c1101d224007a0340248059214408104e04603603941c41611002c89031a004154001d075801c0c001c0c866240286070411400e26031658280c01c9074845148040d88403844440303645101200c5842800750004203c08005c440040621150034030b003203850050060600254041c0325070a10392100d4044000402243c4540790300301302d0303c2e0780d64034001000f01c010702c106010f42d401c046e8010042e40c072814003e004c4098503460081160321480766a10402100c1c001407288003925200c501c413114106009a006000551400980800c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 533573237 1250 533571987 533572001
    0x10b060301122f0d020a0317041e0f030b0705090301050f161409120703060f09020a0503010b130c090e040605040c0e131b0e090705031902010914060915030a 69
    0x1000e518408064011803c0a400c503041a410544001c1540300240c40042e0501c80d003900010810043c2c0c01407403201c1d1400c400503005a80308480344500c402480b002c0300c0c12400032441080c49101c19803001340005000c07014039680000503070902d00d0a1601040c00282564012510036400540c1c4d0340400100c904405140034000600d0305015220030000c22800340350380708003001d07203009600c61841e0302c101d4201007142d50015030300b014003002040c11084c96540982031290007607100e207400c19804129860103208002c0e5000e001050101c1042c000c8080e400503009080041d010721a41160010301030f98044081d9104d54444e4000244502d440c0c42c0c1113041614070707000303d40c00881c400c2c02c100041510410652086800031040903041880300c00e160f60180c0180c12000000e09010280140d0343c1001030b10405440e000c070142c07100790300031000b43e800041c908503019000484142e403c106555007240030351058180a0103003441d0404540c04501544081a8000712142d030000030042d11607414400d0203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 533574487 1250 533573237 533573273
    0x60a0305071e17070c080c030301031a010b0a110102040807080a140105010608040b0903040b0c010b090610200a020405040c0608010e1308090f03010c02010c090b1303030c0302010b06030112 83
    0x42e00341e05842000380100301c00a0b0156142d07040b0000700388182d0042c2c03038041940d6448a080c568541e401021030391250400c1c40111401c0c0380f200d1070411644880b0240c2ca041c0c03900101018206404040c0455031003075034000d014003a560030000031803100000c0c030201d80a081d80b840242500c11036840c0041c400c6260005000721645003c0040c48000d90010100350469000081241d0300c2d161003d071203040d40f0a5501000b080a8005060300c01c03d801900002a2108115159001c958801d0284811541010040d00015003020381d100135000d820481886042c2c10b50301264180b14450f0301050071140161001d03200720028420420025a200802038007604142d114151207040002da542c01d42415802c00512044010070b2040141d144d04220540002c00103000303011403040350b40042e000b41506081305001038260100403501d480140e017158010100006030900062954030112410003031400114115500c0c0d1000749100c0c2c0e205005140600b40821809020102c24a4a00084080341c4002c2c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 533575737 1250 533574487 533574527
    0x15030603021c020906010c03020309030d0809011d0309010c05070902030a09051006030807020d0303150e0a0b010809120307020a1a06091e041101020f06040b07081806060103110405060a030507 84
    0xa04016115207138901d800904c2820120340c0800780345010b80c110700606150700e415104016103c4c0002e0f900202240c081d85101c4002c1208040101801c41038064444c05407946a000700851009035110794003ca402034001d81c20380364025200ea60404c01da900907034900d901c3d551a1550001440300c2030110110180b40340303200b0450f0a01c0e6a0b504191801a484003a214101c010074020170b0500a4000305041c05030800b00e078035036540340c200150240303005a81070b1071442c0c070f0f00765500c066500030643c49025004980042031020440e882a6a040c0e000418010450094910a000003003074407490941340302910342d000050703250103014400d219070018008020601c04481001901354403852290f040794001014201c03107101940145c0c03501f440c4a00403486440f503502017105104000601a0140046075928401c80d00c0d1034802d81d003000183d546058a42e08154085403056001c2e078400040c0b440b6130300050781015540e000190322390b00844140000300707441c3c030200050140c0c02020041d1046c503800702 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 533576987 1250 533575737 533575789
    0x10f17150109091104050f0711010605150a20030c12030717060a1206060e0c04030b0703021305060f070501150b0d0f021b0d08310303061503060302 65
    0x210301010303010b1007441181540c0b43c040c0310a0188401c080201c611000c0d2090100b030400100c1200180012213075000050700144e40b0f458000818011241180c00040c1813050281040310b59000c968084031941c0c00784101012400c8040d59041c12140805d45a10702542d201e6290345030080c2884080c01ccc240c0610501003042007901c941000003201e4202000040300c0441c5d541202041c985202a040624100790702d410023410824941c10540540e0b4404426070b0061315501d09800fa14020f034000104440b288800052006200e540a8104940104a174042c115614030100d10207174010850880c050400045003028040c1c2400b407a4048004024540d00c0149000d4280c40310f401380d207950603819502c0c0d40c890013036407181e0340595505480c9402c0d000e007451010800d0b242d440925400000100e00242c00050b2a0390100034048002e8140c400b40445140341002c00401c5414030910440505580d0140496042d20040d01d0ac810068540c600140310b0f401c60041150031000d0303015500407a050380740 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 533578237 1250 533576987 533577013
    0x3150501050d021b120408011b2c0d030302030115111207050109082d0f0a030b12160f05060f0702010e0604080114161b02091806010f17 60
    0x42115080101c2e54401a121458404682104010b414907401113214004245100c2d40740c5400900850320800000c1100b0b00b10083c141030321100011054021070880c0f40228402c0440d49110540d0400003103400e41008522400500300d001d44000640000354044014041184400707000c031200480e82c00c24491440040c4a151340d601111461620007039030220391442007200c00d4003d00c007c81d5110200d1134030766105607030100ca403441044942184007541c0c9034440c40c602c08082100c4514450000d29031034040c240800750042c3c50000c684075044050710400400a100a2105004c10603120042e2480286001c004140c003039001c0e00035512914040082c911004a8070046179141582800c0c07031120034109000240070b138081c50b40011880d501740030003000c150854060380741c82454400042900f20705000011500c440c40030500c07002421411a03000007501d00307010400d60107000515800c01410750f442c00c1c5424000c00307034020740e4901d840020511024071080c1c403182880704580d00405805030b50030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 533579487 1250 533578237 533578247
    0x602031306230a0302090a030807050c060313020906060702090901063b100f06021c0302040b090d02040e0f011d0a0c15030f06060c020a050f0d0308060307120b010603150501 76
    0xc2c420401d003040005040b0811030207034045d0f943c00f0702d0040c801d450290756410320300340a9002c0c2c0e500300d0303150160006040141c5021b0303058038010005600b00350211a016400d011411001801e40d5921003001d000900050740d07503103c0c4521a82c412400811b10764504601940000c3c055096400410340a004181500080540005c0c10208150b2100c86036120440d92866040030743d04410303c80b0301001e80100380b954001a000d400ca0055510414240c00350302c030218201e024901840c010481d041006521620f4000d078201015030009000048200d42680d8003850031020003075040d02a515908811055060103503524034800524010703050400075a170702d080c0b481103603018400e02101c3c01d008100e1940c0c070a0f804020740e030030020b00c10881c46440382e101412103119140224849d91400c100490302d0b0401024000106d036010309071480e000581d58003541c0700c0d0300c000c0c0f019405100e03c19001070980100e14903e01e42070700600540b076071035052036001802d0304c40348005000d00071100a001c000690b402 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 533580737 1250 533579487 533579537
    0x4050105090d0204150b340b1e15120105040c03031107050a030614060a060807030b130908030f07020d090b032503020d0c031b18030506010602031306 66
    0x44a01d0b020410081c80050005d049007008a2000000e1110101d0850310180c018108000c2e00030030401d200e05044e039941d80712141d00b0783c4540300c4a0500603681c0000c00f0a1055a08104124084002c9a41aa890000120086070080028100c0400c1805107007822070040050343e06610082c012860a5164400305116a01c4001c04000009400840b648000d2101c50050500100580381032603880c10b00c007010701303180c9090904d12100c0d10041911464139114400850798662903018090b56a03140030380040c40880101600540710818043c0070300f10912a400e00a8070546000d40c883c10300c502d801455910017040c11056621100801d4402070f0081100c104540ca02c201da07590342d136950200740458a2160301c16107040440f13041d0300d10206404d40c002d800c1aa01e100001c1180c400c0401046058490004007a04801d100c081814005403050302c1341c10300707410b2800314508016501d0fa41c4034034041003640328200503007001c11603014814134204440b00900c010b01d0040201000704091134055884 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 533581987 1250 533580737 533580739
    0x30209090f04080403060f0c030e0f06180f03160c0e010b181302071a09070b030109020703140414040b040e061302012705041d0303041101050d0207140f01020405010509 74
    0x501d00000d000c20031004119400346500580c00e200c1c02c0c1180807644e024000b8440e0301c2c40400c0c24130f0301c062822400000c0381500d0781828001404c003601d03013406040401c8076805440d01203001d101007181085000300010b101c000007002c1c0354441c500503802c1c1111040403e410402c60a0341c0103004103c440c1154080e50741449240b800351290000400029800b070000d154003e40302800440d01c0814032269200392881d4000e0169230781c0c0990758850004d83c84210034082c045030300801384010b11110701c80e81d0140401900c281001407246440e203220305c031070742c1050707204450756106070040126a0400b0b004494111030160340c14040f01c2c40c0c00003041c0d164800100490032011208105000b560f00c144881411745030082d80e0703405048582c2904a4141060340659030055060544810a19000340c07a00f82a000d441c101443c00c54072640e5a102c3c0c030045500c01c017410020148608100d4240c1c510003003102d684282c070301100f0140c0d0f81400d541025408505100b4a03441070104111598000741100c407038804c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 533583237 1250 533581987 533582011
    0x50703030e063001060206070207091806152103080109090c03020405010f060219021c06060905010e070e03010501050303030a0f110a0e0109120201020c090705121005040c03020909 79
    0x70050104166004403a9802d00502d00c500c0e0800603080b0700003050307414041c011420b4a06a880f0001645e940c2c1c815260f070300041c1c1c0300c21000c000084103507000c000650113940380da0314540500d0b1102d40070f072002d8442c2040f1000031480c08200c0703590070a01d031525200301c20382c010020100b00d0710042c0c40b44c0300c144500c03094140c44540b032204125580c0c0b141d41c05940d006008000319610b513005e0407101c0035603005440143c8101d0036204c044404842055140503070050041c200230741c1602c00701907001d0404000b1600c3da912058080780000442c01080c0c06081d5482c480c040300c1c900850002e01022140700d03030601a0345001d0040c0a15203000c8216540701c81c2d11a030104060701a10807210081145448035200000d01241d072401840d405600c10100d8203090303071200361146c1c88004440c1d2046200000030701681c07010944218034100b4203500d581c403d03035074209030b82003030000c0c2c00c401022102200e5024142541031410301c034a2609100740204072007a4074003103003400651004500201c4d4007a0403800003030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 533584487 1250 533583237 533583257
    0x6100c0c03230109080307090b09131d10151e06110a0618020a0519050d060e0a030807181404110408071d060d050606010309170f040f060c05070303 65
    0x829000b0901903400c844000801c02600f0390705080c0280c2e0021b5030b1002c00280746541c0003982c401a1001d64500d0340d0010420342420340c0d10059a00107081c034400004500c8002c12642d000e0f03840601050000e4078110b980401c144201700300010b010085a001541105034854440380508d4944440d101a0307680c50912003c540680003409103041d1004200034031a40c00d0000125600200c62061894544203480c0d034050151a001008100f403007504603002d03600c062100400207450406c52642096014660005100c40c1108a00c0e0400700d00840c03e50208080000340000d10f5480f07003142c500720804620b80c0000c0c605007054100c40440101c5058401c50326001910040d2407100704960040210384100c80b0142d5135402080b0038820b04883d80c5981c210820001246c46c106201840202030f808005003c440d80c40c000103600802d0f510401741ca4901103140325034007501c0c850380205030079900801d080b83c66601e0400c00a12089407600103404108004030030000042d000076440081d40d5050804801c41 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 533585737 1250 533584487 533584523
    0x11b0e010f020316030512070e01020a1214040e063c06040b03190f1103060118151809381302040e0a060b041401020c09090606100c0c03 60
    0x5400b030115503c02e12440b0030981400c151b0004e00404002582e42c000501d156904070054580c0b80c000100e4601603044081054000740b403800c03040d000451316040c0281e00280070b80301c582043e0003681180505401280c00c1c00224503011100e0250322070045500c40704030308401c544e4030817107101841c3d0b000d49510700700b2125030603070300c50301a500540000e9101d40d4a914101c03102608407032055061a4a1901c1c1044040e00701540d4000d80008081407040725295454440045582c13100d1014002801800614081400d81410828060860203030380c601242040074048480500c00e19840100228a800c1060a00f10003403a000c2e42c000c842004151111241c6520440180c44408586136200c098031440c004100d4060f4041c0c000e60700d0003211449603594400c40c1e181160001d01841070030480a0004220716940002c081e14844018815107042001d4a000b19003100429590300f82c0c0c40c1c114104001150030100f44c0b14440c2e000d90301e8040c0c58800140c4a0720100c030300071f01010744003400c070442954030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 533586987 1250 533585737 533585743
    0x603090b1b04090f110310050907090b1209160e220f060b1201090506040614060906040b0a05090a020d2003060d021f11070b0a09050607020103060f140102011b0e010f02 74
    0x10345008410b10356070300e2170807440c1503064191074000d1609c1844030300c002c686040d11612422044e60090f00c109450442101c5040d406c0304402002102a445024100c003800300040d26a14005d1400b00d40848890401a102d00000075200e030902866440b00c0841d50081034120b4401120540c2120300021100084d0001c10a50010701514154640c20b0030303241c0040101c0018050b01c150b0064504009a905031806010001e5084c2c42e070941c00010000418207d103040e40c002480c45000500c44440542d6a4011485581040702c4003a50582d020410a20b69951070084003041c0300d0b0400c04080d07490003000c6180c254000035084c240100d81c1c0f010728404540398400c4034540f160b0b88041031550840d0140c0014010084105141e545010ba000009114202c4500344e9103101070b261600c20b070300d60405013070201d00d401441d03045e030416031601c80c009085620700d80020301501c444418000503440c1c13580003a003900c1299102864080c0d40200d020003031a030007401195032140c2442c103084542c24009040385 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 533588237 1250 533586987 533587001
    0x60b0a05030f0d0e0d03170a1e0b10090b0a030908040b0708030a060e011401080a020d06060c05010b03070b0f0703020c040c03020405030606030609060f07050d060603090b1b04090f 79
    0x14041c0b10b44060700e0b5180c08002010983c800180e81c0300c0000c640c40d94188594401080c0c13000340030800358129a0f010348055620740707a01031041c0307600242402014160824a4084d80c00401c113260f07403051000041e08080c106019405102d0401c17205071072034180c0b03034081440f4001488080555a0498004010071102100d00500e040003419403a440182061055940b090380d0840701107107400b500083d0710702c520040a0407201200405001e084800f001520030290060540540c207508004440c2c16101d607208001c040e00c5103690364400c010892030541c0c00c482c02281c1c40e5100b81cac801a0200510f8400324100c6520300410761086480300d0301407800b0f902d04180000c40641c01070914402001d8503134580e02074401c44008404031151500c40c501415140c0c0e20580b110707440b41d0011000a5031f0000d29900c481c2d0041030ba0701e0118602010b0112802c115003042d040500000d8540001c0c10a0100d075855894205030307006040d1581c804142d00d0040144241d200b0600c8a58699680c900e18000b0359010344 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 533589487 1250 533588237 533588239
    0x708062403010507030b01030b03010902090105010309030519020a020a06031b1b0b2a030c0d0903090803131403030910031802090a020c12030c160c1205160918060b0a05 74
    0x44000d0921134800b4002e440201c0b11349000a142510040c51441c0c1402250440754000c1e06150442c0d00380030044010b800f40c14030640c18002c040121008012200c100050b006600d5405410815658410000c1240140e40403004250a00040408051044c52021600e4103d030801c6010140c00e03000303c520340b01d040c010203400700e48143c00700421505200842d01c0091001c6603501400704007007440d10030b1401b05840c0144c004205010040380000d060780144405400381c2800504244c1e80c941c000d185600110300c0f0720389968030420801001c0c08039007003038110107000c03001b5500300644540031903008038510b01100200342e22146920b0b4140306c0340904540d06038014207100c031546000d41e2800040e5101300102c0c0c0b440d100d4041020108021a000c0c2d0380140b0290440b585408282a51016620514102a1003040f100840003400c4c05000300c1b840c0699201d18094400304110510115008229a016410300c50501542e40300201e00c840c07040a0940d40300ca0001565201c500200b04002601d411007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 533590737 1250 533589487 533589491
    0x601120f050f1b01051c02070609020a120309090b010203072d0503040509070804020a300317061c060f0f020f040e070c0f14122703070806240301 64
    0xb6440c1040100b4201c42c45a6540c1c20004400c0403000111010710a0303d50394211022100990031040000b070300200240c80c016080807402c824903400140c2000020303030001a103c610100203004050708036409800504000000f040160710800000c0d45a100d80381c8001c01d41101ca49401092650035182d01c2c1c10201c21444441101d00e45103041d40d0740750320a0180d80e2103180710f5400200c40c00d10500c03603603110f59030142602c0780b03440c60009810099100000303500c041401c118041e8106060398202c04042c0d600a41c0c80d59031110311450101141c05000c4e00042c0100b40f00d12402810f80b000311060010180d00050015030950581d0344000104611310380300302030038000220b4410928a100c050f1080e02d4800380b1a203860303120305000f42d50440c4012002481c03418001800030200e04149580020707509400e058070155401100c5240d50b56000d400b1070820340002c0740031040c00349021005921008030a40c004c041503420b0401003590303078200034181d0203003052001c020302d58080c1c07000c1c0084401c00d001e002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 533591987 1250 533590737 533590753
    0x60f030621061e01081c1b05100501050405071d010e0f060f0408070f060c060506040f0608010c1710150507080c0721020f060d180c06030c020d020601120f05 69
    0x8168000701041d0030b0700c4003070084030011540341000726a0402505805a16041136440380009950401411420001c1f211540000b440414014803131142040441980095290f04003c104021240c002d00103c3c10030080e01017580d03442c500c400e12042c0015090070018000702e00c0000003038070b05889c20800d035041800480c10150020303009010300151442402030700d40c601d4071202c2180c3c504c141482010001028800d07a0004154107a000316040700004c0c0012403003150b419a414103079111688041c09580d901c1028600c1c1a85c840c014001c1130000030400e83c440d0400100c810390341d100318080c908800d210388880185443c01002103a011030b92080c0301070380f074001403011143c5541151180f000c000b80c05400d034080a0b4403008105a115500608026a4014550a005064201c1b001c01c03400a5a00c0704403902a40c2400403502c00648600c050594860030124011705540d140c0c0c80100555003d004110f0b155900802c050f8159050605089402e00341c608015485108409000d400707801280d42c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 533593237 1250 533591987 533592001
    0x318050607140717122a0c01030f02090901170102040509100816180b0f030f01020d061d01121a09061005030303070219050106150504060e060f03062106 67
    0x299280c00a2401c406490041d0766507149080c24000800f9518015009403d10215000390300000d01054401c1900006e8000103442e854175940d2034881d1011001d902090021815607418040c0b200000111f803415402d018005010504024040c0a0030941d10415540c00c40044825410742d13004120050450880342800745010b6110700e940d0240d0384890041e114400b1010000c85242d80c00c0380d407000c0c4490311f080c240000c00030040c1038920030b0aa001401e007861780e80030b80c3c0400c5036180b00388a0000059507190301f4443d0380200c1e00b1035802034800840d0708808074886501c07505558115501914a108070b804940391036818409000020f20809080b181032020b0072000140e1940715000c02c10007400115150810580d49000440c1c2000050780003501c42c10310240c59040c02e045c644e00c03074800424440e48412030504105c0c107200c80d440005401050410500740c1c40450b224070008140d8a1514006100c2401a01480018011030045020032404090030441c420800100c2c0c1c07122040c2c031802d085c285 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 533594487 1250 533593237 533593253
    0x204020f0309010e010c08130201090e07020f0c090105060909091501030c0302040c171b0c150603100b010f200a060f0f02041211010203041a040f14010207030318050607 74
    0x307280c0801943ca00450740c0d201040510604d154407401b42c5441d0010307619000301c00400862380d50101d0401c411508000b40107602500708901410440d006001c1c00c1c00d400359036038509401041814480ca40f40720040003a0344410045071170002040e65000040c2d510340d03034030914010f0f2209103c40b1032040702c000001480b0040080c442524422181885940181d04003166400301034580102c40102040c04139800c2610804003907061445c5104441c03d01d81c1e41c0d03641ca8204440e2070100080d80c02d401c410800c403898284241225160200b100700b101c4c09082000078600007001c101d02c400d0000360304030b00809c0010300201041c00000a4104c2d0300360012807501c000605030088a0b203013400c0c1000f84450101103036001355001d0740c05202c0803041d090041c4d1940c8036540c050402e440d040d40010040031034151106d90342c00c5074989240c108141d41340c0c40c0040a441d42c41ca69440681c41d200064420700c40c0b40e0380407403144d040340e800d483e0486da143d440400c00e036038261142c0c2c020b0b90701c8440000c42d43c0402c1480 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 533595737 1250 533594487 533594491
    0x70303020414090f0c1804020d020d05010501081918080a09030b1803090904061b0908060601050a120c050f040306051b04030b0414210c07080304050a060e030a0204020f03 75
    0x354802c04091000386090180d030b000c0c2668080d500f600c042001425580c80300b0094051440d0502c0e0040c0111040d1000c24102d034082e500c0a2149a00055144c56010440c0156130050000307181411007480e1140c070724540b542100880040c4a61103e00714001d03540060200a0a6a0006503455a0715140500600400424401115054015000912070150606c44550540c96400156181c80d000c00100651840700034000c849aa81e1060800b4a54106800c001016180d50302c813a950740e401c25a40514003240200008c0c100841003116202041d4014002d08130401d0402d000314040c403c007d8161100e001781526880d02110200307001060098a80109008050b440401c2460903e0303108100241c0c4a240006000e82c5451804100051010700700219080000300945201d0290780c41c10421403a810028004d140d540461030520001060002c4401800044015483c046c60080490041c0513075100c0c400500c0242011a0a192018840c0f00d0090794001d1045580c2d0340e8020146003146c0003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 533596987 1250 533595737 533595749
    0xe090d0207060e010516150e031206040c05090405191a150702010f050f130b0301080c03070302010e122b0909021305040b0f030607030218030c0a1a0408030703030204 73
    0x41c0040064158007812420843c1c610680d201450180789030011010600040002c85125801036410501510607200d55071080070210040c6030785440940000107454405030403548220b1824080820740c54100c0101c030b4080c0c1d0140c07070101d5541d44a00e031505450840c1111800c1d51410581c07442e401c009200f00e0384414543c1154000301082550b191480c0d41e02800d1b50083c0424824400c00349598024270180c500c0c540301081051030030144010400e00d0901c26849090601008001480404818000f8882e4104e05400801545146800080100e0614000c0c1e6024a00d03120021412841c1400f4110304031184108020184031034658099410240c81c550100003030b01c40711301240e00c1c035241c021121706107003104403c16028102070400005160107003030a940719400e00b0b85031240b6107081c00258840c142c103841c0140c0396101c51130045046500c1c0341e0346604c00d030480c01445c14a075030351040410076100c400524240010303030210114075501c903030342203401325100220faa03100301549074005100b5148 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 533598237 1250 533596987 533596993
    0x1312020609190b0a05180f061501050310050f03030d141806010f05040b1305040b040209060a08031b071e0609140303030a0e070b0a0509100c020907030203100e090d02 73
    0x440c1501e0035032440601c0200340c841c0200110314152103d80011360010908640d80b0705081401e00700d20301d030078147c2100c50325a410501c100b202a000c80e41c02070141175000c1c00d04a28625052100c070903401e006001c1d1a01c2441c900b01c02c44501c0d101001a50240795540c802041070700009008001103a204541d0017081078100f101c68210f210006c66031504036402d070100102c0c001d00742001c0002810390081001c0d085405140b1030002c1e4004c600840340501d000e800119402e0800d4014000c110741e0040a481c000d118401041000e94400000c50788003030002100c004102c0942e60700b190501c0b400754040d03000e840411048007400842a03680c0001c882d03240d01c80d810101d60301d1410000b5881e4060a803a41034200348001080c01d0081c3e00148240402d202c1590307001d0380c9420b010341c11900030050f0500010408074900707240742041d80b103068481c2c610f818000c6000d0282d500280751140e0007402001056000300c0402e4045421043d400041d04001007110100d18010740c0582c0d41c0c0500256001c0188 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 533599487 1250 533598237 533598253
    0x18040b0105032a03030906030a020901030b12070b03181f05060f1806030703080307020c12030313031202070503030403121404020307090c02030405030a120f02160e1312020609 77
    0x202c0c0000c1c00f8864806202c0422030244800044800c000036542d255a030180000c2040c40d00c241c3e2418011440740d01010f50068803002004001001c4800224946001e540a4244001c80582c0080c41a01301c0390041d1020f07036a039a0341d9401d120b81031400150b03075186201d1100051941c122118240c0480d004542041000d66108010094201403000d40719130004d02200e07000f250603170001c030099030110700a812035000740d660f9030b2440300e65401142c6640c016000103945802c1450401c00c03e51506405030300541c15802d1260501c0448016410020180011400c0050219130301e130301039820b01500302059a840f46403905000d01504004020750710503500e0b299900801d00c00107609140503c0c0c001d0020400903051900380d000900500020707800f984800e000016103030350308000b2001d9842c80b03102d1314940d1840c20100542601e52201e10002550401c85808503600c507100a18011030b035102c00110340316251842c005101a000701d0020781030b00c0b01d007000028401c0d00002d01074040e92080044070300f04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 533600737 1250 533599487 533599489
    0x4080307210309080405060903031b1c03050c0a1b0503070501050613050714030a060e0c07020a0b03011413180b06130c0c08031b27010504050f1e18040b0105 69
    0x3a500c05000901c3e8034010705c0284007508003000541303030200014044a07c1c2c800c1c142c5c210710800b14642010422544640355141001501c12003120030f4003107600b4180214200301d1420340460103043c4000040282682e800b80048507800541c2c84076a03041030640f640c2e01d02070b003086806031408032000da0080f4480c60308003a80740010b00c20644038144030303030b40c1c20000c06108201c2c400c01d40c40036004140480e181e041c04121007102018440c01030078403115840c0d4907880d81c414012100d042e644400c05d809000e100400410742440b07000200d0050858109521010381c41141c4020703c40d122800f03600b080c40900d407100704140c400c015805060202c42040c0004048500380003075412007000440021a80c641350400a140c00000e5500041c1c840e10000c42010509851030964100e8100107104601a2140c404020640c807000006900286800f170318007400c282c0466140c211850003d80281030720001000f00701c5282c09003080d0580f0007000c0c0c9002c60101140f20115000c15030b400d50b02c443c00d01e0300004803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 533601987 1250 533600737 533600741
    0xd0b1f020607030605120c220f140f04030c141609020c01060503060106020a0609020f091303080a060e0106110705090903040807050d0c03120302040b0a050304350906040803072103 79
    0x1071190070b10020a0540c0750300701448050004041c0301c0701e505100c4010070001d0003427401102d4020340350f800001209000080e0151084002914440d48072607040e0a05c000703e54003146400a09800811b2a117290358031552036403134140005068040c0300c0c1e11500101d10352065070001d00484c4480070080c08903a4807007040580705d10080c400d8002580c4480791103030024100f41c0140000030700042c0395581800500022802080007118000c001c07801c403102c100101604421801e03080300f4200420010682441c11001e202c50060141c90140242402044000d41040100f44090301015000c0c962508001c0d103000c1da650054041d90751140500c00c004100380c2005080281446d4200e14204031580c61070711010000301c1c3c083d841808040c2c0070480803c1d4207070103a0040c803002425070b48040c1d8a2409082c200701e41c0d019000b1256541113242c0c10781a1003180000e82c2c0b110102901002c40d95446408005411807069500c000c4c1d250002103010340500c400c03d0720084400e49040c045078a20a0b8201c01201 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 533603237 1250 533601987 533602009
    0x15060512060c032706010b030f0c0307050d050a0b04091110180b130e01290a021c18080d09060f090603091e0f12050702060d0b1f020607030605 63
    0xc2c1d401c10510004040040035103c0010b0715440a54201c5401d28040300e403030504000742c1018041c440000180030f00e11589800a55101091080d15811070410f60b100420354440e000b0320070421616000480d00c24100c42d400045c40080c0280100a50411440e09001d6403c0c1010000d1041d4a040c29451762075001d50000d940c0c01d160300543d0b2055a080c0442801b1580007100180c50300340aa40d0041403046040803000e0280c88040712030401e81040000d00310120002c0e88640d0070500c02441020301c51900040c14940501508145005034202c40c44111031510740c85003064000110820001040303600800c041900004542c0e80110864503080c080d2213005000716124005042c251040160710700c60b0b4080360300a4410100801801c07080345019290040606090f5225a5405025003c114030024aa00742d10418100075040100b10380001e042d030701a0711a140d88054076544441803954070b5141c040100c40203172545142e1b100f0540030007942c5080c12150070010926008001c0b03000d29190315804 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 533604487 1250 533603237 533603251
    0x150f0a0f1205010905031324020d0804020f0d060b040e0f1f1104061206150c02090c04120b100f0f09020d0b03190c090e1c05071506051206 61
    0x4004901d404458681c1c029407a1060354203550764601c0340001907090005140ba0785c409103082c4003080c10400f105401c075003146808a500010110402c4030b00790045040c2442000606240b2216551400400d184a040c2c41107160300032118221001004403552100070780c468107680c100324200e52540d41c2a0744404210501540781c0c442641c2001c0c030480c01c120349030301200d521004aa07510040040c1e04239604203401540200d154043c90004c0c680e52881001c0c01031401c0b2102003054100090080d00030000c840020380a800c071200003035200740908088400504041c100b4030b1010040f0b0402c03150404042c0d492038400924000001400d4602240383d41c25240c52400030300d03219140c208150003d602800c0d01c898240e48402c0c02e00710690302800f84556000254440407800201842e2100c0480c0749a048600224a171a01c00d02000200045010f00388101c1c244440c0030f0b1f48001010f58a500480304000c0c000454510303511510146a001401200d1081d00c000c0300e2848144880390729110112012 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 533605737 1250 533604487 533604509
    0x50a0f0515040e16181511190804080f0604020f04020901030e07030501150e09070506030606120406090201110a020d030e18040c140312090603060117150f0a 69
    0xd00c40d528000c5004802108203440151400b60788001850410508498400390079481c4603031007156a4002600d1085504e40200701c800c031a0404000002240803150403030200301480d44100b42020781000348044500044c1e01181601c1c450b8a003107529548207006134185070150b14011460a0000139003140a294001c200e902242076050502000350007400e0828109a01c4110070071692005201c041d002c0d50050b0008102d1101c00b502c04d0305070086c0380e0b00411601548030108080304001054800555a045941c15660b84451000405078041d4094100c1294040e00a110410980c0d900030103000d8801c0c0c8401070302e802d01c0605551600005040a500103070311100710130009104070082e40032180000c044a10080c07080c0c03843c0210340000c41c2d0895103200c5590003170180d075050307101034440340e0001c13401040301040c0410142c406025400e01140a0716010003c500706038002c0782d84480c244030a00340d6075080e190900c44c10408a00f410800c500402000610032030701d092440605060302e03d40050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 533606987 1250 533605737 533605739
    0xf05030c120d030b04020405040e012a020a02060d0b100309030207210f2102060123031b01030b060c0102070201030b04050c0412170304030f0e0607150f0e07090f06050a0f 75
    0x2099010b0700510036203e0b4040d1b402c110204040d582c03441890080944138000141c903000c141c1070080882380d14103450301a0b800200a02c8100350707002804007081681620f6090700c592100012501400e100f41312250300412100c8030440a6a15600c03071051217009500f211a2103685403240c8820145803040b120000750703000707001404201450034403c00c46100301c1d03804c44101001a9120505000303211600b005030410301c01000000b40390303103035014100e0461441600084051000a640320401c0d11058800100465000c5141c2e0080d80044070442c07016011940d6080061000c500030751212100b00d01103490302c140b0340510308040c403520384600340e2402da03680790a00305041c4201001d00420100d46418518440240000c100030146001d240300740c82c2c9400001000300064040310304040c00c41d00411062081001103216010440d584c405000000200d1041c3c01003028003400140a0506492203508000141010746038000c1c1014801c8410400c002501c80d0100011101140700765000c0d800b038828 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 533608237 1250 533606987 533607013
    0xd0e0109061b06050106051201140303030f0a0e0712060507080403052d0408030903070b071e11030708100b0a1a1614030405010f0f27030c0f05030c12 66
    0x552502001a030b850500c1919030342c0c2c2c2d254000c0e030340709803c1800001d1011440445005030190424050080c90003100441010400441c1ea40d00000349507595a010031000b03d010100264000240004c0443c1626603c0d41c030780070000c520400060040b01c51b0b904c1d200c000382c0c42c4da10a2180e2030065038180d40d41840c02c44020310141014800191030b506502502c00003d940c10a044005d0009046000c0a9900c034400c01c0201814560654030000f4010400c1080000107682e40040441c280d407824499074185c400c60800810340c076600c041e0550035110f00e000210b240c01c800141d0b00c0d0002040702e02030012600d0b10341403203141b01c00ca01c119021581d546100314240042c40015012a11044d55800140b0381c4940300d0303503c10b4003105050320f0360b60000282807046580c0100403006100c10f900f41040e841cac0241900408803042c1007403083c0406a031080c0d0b2030203158091250002540c002a800c082c46443d0503200c03060b00c0c1184a114882d02c2803c0040d07609007411000341c032040c0004805000c18803403990f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 533609487 1250 533608237 533608247
    0x403021509030d0f0b041b0c120302040e240d03080103120302070807030504051504151d0439050f0a020312010305010c12050c0906070206041a0a020d0e010906 70
    0x1e070182080340001e0000106000c1948240030800d40310754004100c00c2d100006001c2201c0075188a000d00d000341e91400400140c00203901d142c840c1c1d21008082c000320024030114028015a000040c61040e104280902610100f507010403c0214085402c859040c003401c004031840301c80300050204545400400101301d040380c410f00c0c0d042d0681000b500e45a81d0345e603205000d6210610460100d100031900b070040341441001d00244450105038989007a040c00c80703a941c07000f41b440e100d604000c01d4104494440100c80300b044001100904244403145043c0c1c0100301c040301e10601110f40248a0544011244d5000540c03021184691030305441c1481c2907040f00d1065004040c10029403104200c0300000c2380543c0740450085014000002c0c03007a94031080103111041c00480340342114201418000c000700d10208990000000b115040d50301e0a2034800301e4024080e0b0703030011000b203c0e030000284140703991100030007050b0030941c00d440c0c200c9900310703040d40d20400f5285400d0000b052041c00707004980c050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 533610737 1250 533609487 533609491
    0x141c2102011a0603090f030c06070f08040305070803090a02041b27121a1e060d030207051c1a0702060a020c070302090403110714011812030c14033004030215 69
    0x145042d41c52600304140c4681c47c540c8400e6049055511040400210550041030100501464a0002c00d135080c951801081c1d4001d080010700300440000114070004070801481c90f0a80d40a0300520049451818040203108080d045101056900304481c110200804420030808500c81c5200c1c20340341080020700b1011000d00c01101d480020500b17505010317130000c548520402280f034105800301c0c0d407222140b00c101405032140d8002c09010b401400003d40104440c000c3c0c501c260f81060090315505160400c14181035000342a6940c03d039408081c0303211610459105819540841c0c0464481c1e410748000c9102d200308604490300701c1da000344014a0b16405007078105000f481c040b00c000b100d01241500740041a0b028200741d002c01c14403000c840d40c20007024030040c070249070081c0c1c4d000c0c40e007c400310b803101101e04010100301c11205107204000010220300801e19902c4112500c5002e80c0701c0c140465801d00c0c02403d818038596441550108210040512135075140c3c1c09414601810118916120700c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 533611987 1250 533610737 533610751
    0x5011d060318150f0a11070c0b0309070b040801020703081b04030201140c01020d090b060a0b0f0d090b0408040504201207121107150b0109141c2102011a0603 69
    0x301c3d0306251502c03c116550502810402c0e0b078540c4a4100002c1030400c840540700349505c1c0801c24041e10300461343c2c0f000c2c0700c0c2c02c40d071060040d640e40b940c40704256409c0c44007942029451090200d008107a1910542c0035283d0a4802c2d1503c6030036485482e4940801040301c90000f00d0341004210500c010f504c038a03035415a003644120311900b00b018404200d426601301081c2c520a0990343e0701c01109004002c641c1540080003510401405410715000311601d21402d295108501030010b10311a11a520740d005418040c3c000054150500b0185800d064a034414450780d4441e41c1442c0c504101980c0704609140c140303003a40c01c7d00380380c001d400030350583d03d150003040ca4040c00030358803007901c051241d8020011440c0e09004804c3d502d200340d10744024069203007400140b10078505814000d003a40c104040506450101c07440050800059000882445c928407040410301160800042001040101c500d01c0c02116400e082e803940220070100d088030002071024801ca031200e403108540c0d0078107500961300020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 533613237 1250 533611987 533611993
    0x3010b0715020f0705010507030b090601021b0a030c03030504080f030a1d01200109031b03021f0f1a0f03010c050919090908070c080a05030306011d09010602010605011d060318 77
    0x1c583c1e403524141c0d00480403d0307a05135104c03070802111590511902c8a24003049511030310900340080001d50b50705452101c42a01150700c2008e003000c0c0d41e000b410700c0095611031010401d070b0f0344078030b00245941c20921074860300348518201a21506008010f444000038103507100508003013203800d4816140700c0e0070031050512035180d804558006000c002521940e101c140041100040c61400401000945007010b5a0001c2d01450b90002980451914901d03152500c05001e124001d4a8040082c2078010b09a1019031402c00c001035038a41207401696030200403507559040d1240c4406044c00c1e035808150301d01c0010410041c0100c2d0341340c60852520120010250740000584a94076007049602e6484103648201011444604000010401802030964100980410109035580990324040580024144a804207400c00c1103140010300308507142008001801c03559507101d01034001c02c80d41c002c2900040d0840403580d011804a14101c217480b002828085c070b19034507208a10701d400c0c8260101403c0e80 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 533614487 1250 533613237 533613247
    0x7050715140d02091e030c0a15230316080c07030807050c010204030c08030405090c0f0f0a110d091806210f02030a0606080c1f08070207080a0503040305060a0203010b071502 76
    0xd21009102d0100d20005010791050025a100301403074042c40d46007c44c401c0658000c1400703101e554000302041c0411a04240340480c008040e0200882849100c500f1030b81004003c0106648500c504480d01e054151500101e80d1129452646035200701079001e008a00c6c00c00114100500c10300c0180300e8906094001402c20ba202c1c3c0d9134204202c529803003103c1a80c008201030003a441d2080c8034540001411080340e00d0b00c110325400f0101c90190404c507000a40b40464615481c0b806031400086078180c2d0b03000ea600305c01016101070042d01d20307405060300703040030401540d40112031480340078240c405200c804500c2d003000d092002910b0f0a1030304c2c2160600e030100b5079080140c604008640030f142c4135000125149060500d41450300780d0307843d001c3d03114500c0f01d819080f6880d00700500c031380e460b051031400c49001c1d81d030020140e103001c00036030280249124400c0c2d4901030210102c0a0320941303119a094036507030345400b005882039000c00c3c084c00d0f180c0c0b4801c0001034001104000b10b80058040110054101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 533615737 1250 533614487 533614489
    0xf04140a030504080c01020106030f0816121e030b010e130f0212090d031505010806041d0a15060f0e15090411090f250201060e040807050715140d0209 66
    0xc0905494114041003020a0600c180e1074144190303501028280b0080095900c1d603191a001694081409481c0150029111440e2003403540340c0c20300150080803100101034a060700600e80715662034050740d52a044003403640014480d0241e1501554140d42e1802c040c051030f000c102d0300707000b247c405a01c00ba6541d0003000001c050b07400501a040d054003805181c510b814403240d820129540d10b480101403510b641e0510141804038400f080d280c00b0320380058180d0f1100c01081c000c0a601c820441402c4000203462140c0b07000240da0383c07a40d48034114010a00020956460981d00240034200c1c900340d43c03581c20f000c805030710800b142e80560b00600e4a225401130101060814000761400d56402119404030185030405401160304066680d40e40176080c640112000151140c11800001140e018840c45800c507100f504254090820b00245c500c00d400c4c41c1c80c1203196032388407181c01c848138000e420001a11012054401011110030307150b002c410065411010940e1780510741111a0a40c240304107822 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 533616987 1250 533615737 533615743
    0x10b120309150720090108010c080a020d0e1005010501030608031306080606120103030c03080108160501320405032e0b0d0b0901140109091e0618050a0309050108040302060f0414 78
    0x10768003100310783d6030840d082014004142030581240360149c0c107083d800f105280c1c0c8500342039401004d0302d80050722803111030110b40280c858000500c8542c4a410307040001409035030300c014100c42003600c0c10069199100c22503922030040360b040d00280e41e00008100400c501684a02c0e5200c3c100900442c40c180c0749100400170b654081c0c01c16000079400b100351104050300642c0d224003400f42d1324000c207a502180812000a1003450041e10304014000d40540381d441c2c0d11803a05c0351102e40c00da26089503941e02e62294034841c0c11034455580300384101608210407c103010700c134607013007450028405400032110f007040002d440260b6040d9001000790754014042441c031001140640048000450400c0c0340d0000c40d110014103030020726645240650f11400158002d1841140c0d0311040a83c00c04002d807030034104000d01a1040101c0c7c86029407807074000b044004a10b40c1300f142e100707031120760072240c5480c011128040100d0300140568403a10226102c0c1ea001e0b40003d41c8140724408005042035615540d80c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 533618237 1250 533616987 533617013
    0x90e12071a070e040f02030906040f030908011406040c050a140f0712050903010605040501210809040603080a1403010b180a031401020403060e0616110f030f040305010b1203091507 79
    0x4000b495070340e4003c410307281902030400b44214410f000c1d401c50420070b556540340c01c000741005040b6910b5510740410140507640040c020021040200485103d0300503d81f078541c0107e8140b4403452428400700f10250280050303480002582d52000740c007000c42023001c0c001e039001c90b00e082d01216040c0007200006000000611010146a944540f510510001e1509641c1b15400c0a40305900700401486040c9900850213010303c414805039411481900b840c6c40b003485491106034100d0304080d8084203014415008107030503030003030742c1d05607011441400c885000d00080c0696840c075601004401d00b00107000140d04240500104841e1490780e0b65951884d014044105010460b5000f0508006202030392103100c02403054000980014544441c80901c4140c1302c1041a00f402044522201225410004035920700710400c00c41360f882d408080d905109800c28802100c0642c28541d64104030308102c1c2c2844884400d16000b035040c0740e4540c0030440d400c54080242041d09000703121100106190b40d190350 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 533619487 1250 533618237 533618251
    0x1309020406080a1b0e0d060606020a030224151c2607111002070e040609112224032006071a0402010c0602030a060609090e12071a 57
    0x680d00c516121025180440041c55103c0c0c6500d402a0301001c0c0ca2844018010218140341041e4002040c4000499440ea60200582410701d802c101040e101e400290602101d4003c1d002c458512030f807011110341c86012000240c50f550001000720b80b803100000310229030381d070f0014a00d401d56642e503a03000c13050005000d800d440000141c0004002d60182c111180f580c0341001110600c1c11038107440d100c035902882d183c0940104c0e561032003030003414800d0100c44007510b2141c00e6000039081a0070405d002e0268100107481d44401100da0522030f103080401201c3c0d1a40d03001c2d04440c904840100700c0014003415107105403c491044030b03242e007841d00040b4032010758481d45075144d089501c10503a0443e600e0b59186103000380300410104010441c6030000720307a03000140e12845c07090359441c40105c0e05c4042c8240e000700303000d002006004030000541c0040c1c00742c622580e9442c49059403143c074542614001c40c6070f1800d9130003a80d5400c0300d20292100030802540140a014003120700b01d0140c1b00e118008580034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 533620737 1250 533619487 533619491
    0x6020c03220b250602090a03030302090907030b010c060c140406020a052503060b0a05061812240603010b060f180f1f030e030301090c2c090c1309 64
    0x2082240714000c035184080c0003501102e5090260300c411959114800b001d40d07109841c3d002c60200700f040074a0301200c4042401501300070400f43d5920f0042c0c06904141c400394030503a0108001055079100c1c1c402e4861100050b03450101c10551512040000e00b80080c4450400105101044804182100034002000103134000c10002c0f80fa1b040041c20182111114002d1000f2030f940c000e01c400c111228881502d0300a040000c01607269000544003401d04d82c000c603002a8003045002c0f9015820121180704030080d00d000c880c080b4185c0440d92151141c060780c0304a254a14000c003040044011034541c0100701400010360329505600050043d0441141748080c0100010024075030700740408558044441901d102503e403820380001855810700d40ba48411051880d034100417024407a0f04280c1101a4a5060326640d5840306e804102806842e01801e0205081c890b07201280c00d01400b8030407243e14024107808552035000c013088141c15020b00950b800400a01c40d071401c0c8130b00b000340d02c0c000f0500c1140c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 533621987 1250 533620737 533620777
    0x30c0c06152402030403021903061e050a2a030b03030412050f06041a04031209080c0c060c06130201050408010e070510020a0209070e0d060204120506090a0c060c06020c03 75
    0x414001c8100d503801ca03000b400c28102c100c0712098000050300d040d0303981243d1013160050680c44500c1185180d0344068006e03410240721142114181c1c40d061003084003403501b03000d1940d17613416007400d80303000085802c507251a00b20701028003001140c0c03010310a5010700d004100000140002031031034010741c0100c0c8542c1460038000c1c2c01c0040c100850400c10058401030b06080c071305526002421210f03041044206018000060b040500c0780c49130100340c29000e01c0401c6034604070b00f0580320b1600850400c0190384549141d008441c07400b0026950031440b140010300300b40e41da05d00c41c80310f62a00610201c4c1408014080414084020701920780ca080040004146244c41c00301048810f0040c030b40480255044500b141e07000d40c0351a4425a40a402070401c0071611003c2030101e004400400c0000d81030078804140410f01e22007400c2c0e0410330758000d0b02240e45580b10110079070b8540241560083c801c02c0802e05c104900780c05090745038499401400d00505041c60480c555003107600581076100400c2200710 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 533623237 1250 533621987 533621999
    0x9060e09190f1b27061d0d03020c0301050a11070618050a03030b01030b1804061e0f06080105100e07111516021507050f1e07030c170304020907030c0c0615 68
    0x1803903180e006000c51301c0141e41c45000d04030348130b000c00783c0c0a034904205100c3c1c95103d50042040b100440e00c00d026007004140180750400940b64640110b900d8802d5080c10046440080c0500949218001c5a1a040e2500150b5030f107002c000c0c20b010b01000502c048100d07120700410070078454041018000e0314003042d8030100070001001c6940d0002c01030310501858010b0400e80c0340c000d0321258016030144001944040082c46018840414045810940d003400f84030701c4e0b00c002c280c004008030340c0d514000b400252a1038805c02450401405003d103d040e00500042007148904d036403420b030880843c1581c0c400c03441c01072034910f5044202c90030000b1f45542003003050b00e90780c10801030f900d00d12201c41d400c08904244c07500800c0340c4078000003880602004200f80c4104184581c00c413049010807414266102d28601d0090a544aa0081a40c0444031072044000f4000c00c43c040324440d5a005001c510f1b02d139a0200150018020079125a0422880e18504070000d5428450100d40c18881c507400e00d0302900c0c0035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 533624487 1250 533623237 533623247
    0x120506010203030f040609050f0d030930080417030112021014030a090206091807080901020a020304030611090a06030219020c0a05060c0f15060109060e09190f1b 71
    0x900610304540c010404c00088011501c03110b500300f98081000b04100a142c00d01910746000b80c00c0b401c03030a0107000500034400342c050b8802041e0300d00c280a0103211021085141440041c3d4001c405064911315140c8004244034030710a5034002d04c04d8041c0c14621002403018040703034009800030300b8070030040324540f425031402c20041451010140340040144840325030709103480c000901803101150f1102d00304411582c2e0070041d83d40302580940140a050072010a5100700f800954100f408200c9040100d0480c0e81c0600845000100d00d4005514052a507903802c0000d2101d012000035104040c040902c4580d2901c1490000300030341c1c1e602580341c4410303991110f8004008050f45055622240c1d5148503611114080740480700212003d40e141c0300800301035402d200300301410030514081c3d808008000d80107101c076140a001c4c20727038800e1200ca440b50b00a40c0c11250801500740d000c0c20360b80009407200d5040080159640c9480800308500985807007503420f0f03076201c44506981810000c1c18842e075076405 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 533625737 1250 533624487 533624491
    0xb0901290f0d0f0207170c0102070506100f170a110a12120305180601140609030d081b0c0c330306040f060605070305030a0b1e120c0616020307151205 66
    0x3d008500d4a10241d4071041d0f80310300c141c2e5490000c2c070f0100318100301000a505862440d5084404d442e00c0c3d25080070741000b0100c5900650b82407403e14000403607070b40d05090350303000d255504030028821000e10343c0702e091040da00d5601e141e5122428500c0412154003040c0090b20f058172640b00084150805000036007960070003400c81103d034240c0d03074900d1008a0300160017411560140c0c40e0301d001e0074030000440d480b4070801e82c00903054851420022142c0350700151651182d0042010b2400301c0395199100100c600c035084e21198a980040c14201c190b14000303038110568140c00c160045030400b0f0700c4451075a507207003c09002ca0b02d880403042002c0d504050190a600c96850041041814140003029104e40940b000c040c080010120015048415130782c4a618003000042c1864010300003000310f00c4512058400050040ca481d800d041f505070400105907880003c003d01d61818100c66103042007100442100680e89072041c220002515030005d4400d610000c2c0baa6504101c48903050883c00c156000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 533626987 1250 533625737 533625761
    0xb15031006020c24090409120201050603060402010509040c020c040c020d0908070605071e050109140c0931080c0c1c150b0d0b0f0612010b0901290f0d 66
    0x40070860483c00d40c0c85040604040400c0346101d059200ca402c600c00c1240229400d040c1c01c2854549001c007032060b0401151000561580244265542c3e00305040c0c4507441514000c0c042001400341807440e00d40350304090680c040c0b500c115a180158400000c00b0340300c05440000c050303002420f0002ca0281d1002c0040081c20085c0d0003440903c2c60107a0050841c41008005032240000f184907441c1183e249101c0c86005130070800a100e10515401c020358030031074400c1030070654410300c80803d20398202440384034494a40c000c4200840d004184050f0342071a814980400407001085000001416060180c0b0b8040f044d0002800740e4070500303050000445108400204000e020048a00001c8540e507420845814803140859803203181d0b4040361006200840040c0402c0491081112441f60021b444e4410401162017112610328000058201d498240205821010b07000c01440000629041d0401e960408a155800c40d80011132032581c5030089036003000320b5040001c250b0720244d494007401e104020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 533628237 1250 533626987 533626993
    0x13050f160f0e19111b100b040b0d03030c0201110310030b010b0304050c011d1003090b0a0605031009030507050f0f150f0615040f0e01050a09061d0405010b1503100602 73
    0x300049942c0c10f00c2c1140201058160b03c0303a201c40d00041e01d40042c0c8001d003110941d85031440442101e01a110220404408515490a400000ca510701802049003d14001c0c0c201e80645186407012030140c0f6401800e0415992100c4003410004c401d000154429200c80b481c4500d02c03801d601e020090910306a0104600710024010310003c40d0b00820070382821402400c0c01d020580c3d407102ea000c415006810420303840038101514080c402e4040d003090b10b120b80b00d4a62030005a440421000c01c448076400f61a4242d4800401b4134613102e910b500200100d40242045c90034080145e031101e01c0c1c0200e000304070b5080c0d0468428603d05500400042ca18110751701080c602e00d162004a9662002000f0305540c45a200140e807040c0a80d410001c550140002201b5901c0d0380d5115400196201000c1c85010302030281c14400003a2584203100e4003050f52088206144181400c00e9072014001c0040d0043d50b0315541c0e0120300ba001c2e45c82000d04200301a030f80441c9c45d200d207009180184000900d60145003550 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 533629487 1250 533628237 533628241
    0x20105070207060f180803030f1803041e0b0708043b040309080318130204050d15060506071103010b031605040c05040510020a02030f03090913050f160f0e 68
    0x340d0040380e09400e482241c41d0140c501425034100300c8400704043c0e91100602400c40780070461a0b0003000451103000d008809110644914118040982990755a1030316a0001e00080c005107400c00c5003241300d81e5481504140d040d4941d456040c040c0d100202c2140e441c080040c0802900c1c00d174800320f4861202c904505020301300d0651100e00240b20304031031400503442c1000007400301409030941c07a02401e2850210b0752210a03080c00703001c1c14892190468130440422124030312085490086800307807180501131074501c500c259600612000440590400c85846040109181c0c65160107052004d0256244620f18032408042c10300f150903090b100c90081d003102d1405114610800209021580d0544000402d10801c0c038080303071680501d4001030381c040800180204241d42c00501a0700481c02202a10718091100d090b1603640d210f07442c059a009004400015142c002d11403d102d0700c280030310103407000c1c01c41d2030380304d581016402403c14038500d0714140d040c00b0161600c0311000146c02c500350051114 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 533630737 1250 533629487 533629501
    0x4030c09061a070f030c02180f01080705191214010c0e130c090b031909080306040c1107060315031a0a0f090201051210050d08031902160215040b2701020105 69
    0x1204d00b440b0150034400000510340c1152119a0f0001d03c0e0280103003e000c0b031342000d0364640e100c1c2c8004c0c400c290061207501f00108152034203850010360b030194036524507820b1b807a02038080018946070805603204044080d05801800c0301b8040c0d0725448955a45034000c2c80101c81c2041a003040034141611150301d407002140525401c4850304080d56541c0c0166503c80d0f8070002550080703003440c03404090003414420031004200b0342d10b01071070141d03504990610141c1060325040f208145c4408031100315601c00002005114000d900c00c00070750310404520840e05440e07442d8210369280c04c1580c0d103c0d504459040001c0c29006124002000f04140001d0080300e9241d0002003180c0100750710110000b0040740400c11500074030051400a000c00780200040c4041803c01000d150002c98030211958110040104c503400342c3c1c4212105003170400013008600080b034007030090f654076545400a98110801c404158502010090040740c02181040c045003215040b00000300c3c80804805419a8100420b211075 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 533631987 1250 533630737 533630753
    0x906090f0f070537240f0806041503050102070b060d05060117010207140f0c060903070302150c0f03070308090a122714010306052e090b03040f1a04150f0204030c09061a07 75
    0x24461b401e1404070b070715403a00d600060007061241140503001d901548004100300064010303080e40d41c0221030a00c0162307039020900180c00c004010040503a005040140181d240d0b0004900261644a00040c10621542d40c1c4456060b0041c03400a00c66120b6400041c0c3c0c0300003000040c41c0394909844070303420b0800080100b1b5440f0220b010080c80f50490180c408542c401c808150760489404d1001c9038240f000c182903441e01d0354800041980001c40b480000342d4227a0000802d0005250300a05403c041c080340300c170850320180c03800800d02114015640c0c200c0f820301e6244461b80605081c19184148000120000d012649158002c43c05802e0400c11620038207224907622080183c400759412002c10465070440f550310b1715410950b00000701105000c1484042080340c0c03030309446140c100c9180704082165000604e82120000c010501d0170b280500018a660030502d82d403100c1103030143c1069100d030749100b0000382ca500500f50490ba1560104000040e400407924850341d40c2025614001080c2c8440344 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 533633093 1106 533631987 533632007
    0x30e03160201110c010c080304031106011707090b031c0c0c090b1302070506070e0109050a12120f1b02180906090f0f07053724 56
    0xd00410010f1340c02d90341c444c161110003044060381d88104840d48000c00840400c2030b82103041d0b60310300040113840d019001080c809a600c85006144610f0b1151690050280c0b40c20004ea00505840101d43d19800c0c0303a10a085203198594110b0a039500040b1071002480710b02c0a41c00050500c0580c0e004641c03100c0d04503403640071094101c14600030b038082c44002800c0f58014030f0124800c940265001410b610781070400000b51036940c000501c00d942d069000a504103885800c00c42004071100424070400868105011000d08121000f0104168200001189110130540d4420345d520301d00303080c08405c003880700e402c079615095211580701c601c282e4140300c4504c82e69025440c09000810749281c5c0101c404018124207140004210b01c0c106106001e4984011898004400701d40071242030003140c0c01214004400c510b4000001070784451200340908030040703160b504040300d130301c80f00e0300f4 = true := by decide +kernel

theorem cover : BRFrame.Cov 533453237 533633093 := by
  have h0 := BRFrame.cov_init 533453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 533453237 ≤ n) (h2 : n < 533633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
