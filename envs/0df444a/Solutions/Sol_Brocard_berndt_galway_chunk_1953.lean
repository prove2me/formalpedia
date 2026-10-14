-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1953
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:16:52.317714+00:00
-- url     : https://prove2.me/submissions/39c81e1c-376a-4c3e-b6c6-097683cba84f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 351079136 ≤ n < 351258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 351080386 1250 351079136 351079177
    0x5061605090d172218050910021602060408031e040303050d0507120510090e0d05070f0c0503030d06081b030c040c031d06040b0c0412080c032b0f061a 66
    0x280c0c00c040d00c4056030700c1ca0f1350801394140244104418410304d021040e40080000341360042e1004e0391b0b4a01111503c41281d80000c43c00c110901858079640c0d600e40190071566100c0d56100416502d620500322000422070b802000710030182201c007141c1c212501a47d43c5414040100c00500007010064009014000801013400b904400d500907584227901c00d22584a0851400b01050f050b1407081c1103003282c0d6007003000e20310009038200d4144d9000700d401c54402070b8400070340e1403c903414481a800c081c0d071620000c07502c150320104a800000950341400c080da00d01c030552504031344051489a0403070764150000100c00d45503041952054520300b116190204007842c1566540380c034a00b440000e0724650700024200028405006080c03900700740340d20300e10307864a032400c141000742d20301450000307081d06800610343d10910010016034540e480b030a181d0507181a000c8481540f2008000350300068141400403181810110303100d40b0044030403410081c020551004880300c041d9006400c0419000b141d91007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 351081636 1250 351080386 351080407
    0x90607170c1e18062a0102070602030c0414010c12050a030603140d09140306070815040f060e0f090c011116030c05130c050a111905061605090d17 64
    0x221a860074603207082e85a603407102d01030610b180551881e0550181800700046800310641c10b030101040280740000c02d00022804584a02a11a200d006407500f400030052000d601511402001290200d2070000b002214910065a0104010304040c040c640300b1103000305c00a001c2d4000301021601407400180030760700c940c0c92501101b404180e01200c1e52000381c0900070741d030f00110600d01400c580d10803242c0d041d00b03000c0000d40e1050020101401c0042c2600401e651040146000d0001c000044c01400310383c030718202060003049588115410101030343d02003184450700d0704c0c50500480c400005881003c81140054400c02c12402c0354591700e00c2050170580d800300e08529944055031151030710039a02860441001042038180b002001c1c40c5d460302c18014800794200382114a201014201981540440e03003403981424140f004024400620880b240b04019001c241c9511590328003c41e0301301030342c050b141210540985445940c100c0c04004a01e0041405103031480d010f8445003503880d1400b10b1450 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 351082886 1250 351081636 351081667
    0x108120a022b090e06060a0c0516080a030e040b0d060b0105070c0311010206100f03030e06160b090609030705060c07050f120702041107031d06130617090607170c 71
    0xd000020306648070b003502039020b40c0b0003031050082c948950082c0c610b003041c8001509500c03491050500b80140c072032030501003290600c480001d4003244841454095034401c000c40e215440060100c00107000b804003016a031270a807142c06440c0c1c4002c0c041d4901090310350b803107200402d511010141840014090380d800940103a080d10055445001c0555901604400291410402901000b406284000240301110ba8900b070741d0110382e01407402109051060300851501d11494030100f406002c42c00b220000d00048041482c01008400110f603495076404c80070075100e01170203100820582041c00401c1c0c00c2d0041d84060605030340980d0645031100010b40803185040180f120401c90942c0c0800c102c015464240300784843d800c03500c21900c0c5044500c2e600109291050601c0d82030b00c2c1860349580c50b464440c0300989400304001440d902140c0d4032840c0141440702002040031844512500086550501040c01070003960316840c1c0c00c000b503034841c04d10002d5460040c006c42148400740406081d160102 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 351084136 1250 351082886 351082933
    0xc013e190501021201060504030321091a04020f010801080309210102070c030302060a020a0503220602030c091c0503160609050d210605091906120606080706080108120a02 75
    0xc1c400141d4429810300074003412407050380804148034080c0302c100046600596402140c80707082c400050800074030f18821000702900705001e859038825003004044080340740012030095008981c0c0c01c0c0d51111280046a541109004807102d5400034032070300c00c81d82040b20301094680540486001d22140b800c44039070898002c484192500204030301c0400c01c0c540c06000f0141c00c8160000c0a6203400300001000d40ba522022b01784101d05032140030000d896103000b456090803654003030415552414113032507071011900041803d40c03040d00c1c2e5844030400c103032221b41980f8071503604c6009103042c030a082280c0314420152030801d9552a8940101ea000104140089090240152210320740c0100da45c1100000c0d016907400402480d01e0b051083c88540e84400000750320000c1c6d0b0301d490203118070a20070000a005658000900480322448038420490260009810b450549046595242c3d40300d1007203914042c01c3c801c19400703070062403103c0122000c0c000108001810703401140d604040c001100c221002c0c1d030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 351085386 1250 351084136 351084143
    0x30c020c13050708010803030f0103021e09070504090b040e0c0d081b0604032006040b130b01090b01170f010302151209060f0106180b0c070e090c013e19 67
    0x44000700a00f16400c4101580940788a600650440c0780020704a0302506040c0401f0b4400c1c080e50300a00913194020910041c06400641520314500b801c0502a01c59046801a002000c0c14409401d6407420700780304a000300c9000c0760080c41649188070610910160301141502c03016401c10503d411a10b00c9150802e4400007000200380c20325042c14006c24000450600c800d4003502442c1c5a02d11210001c1c00e15085a00f00e8160032042e00c40214201041034601d400030007a0b603040e000007444040e03da004507000703102038a41c581d07060400b410542003100200c5405800c0010b103001400541000043c1d04c0c002504069031610306204a00d424004100464407150660b00101c1000b440c0c42500169600400c240e0410841401402138000c0c4040321500456580c0f940108119244101c108500384c0101540308200c07100b800d0500c00d03d611000c81e10315580c0483c2c1c0d002707580c01419038564007103c80e2a60a81c884da41c500105080009410301d200c104005034861068501e07804a08e85403aa03000c50b10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 351086636 1250 351085386 351085391
    0x9030d02030904050a02180f130c0c0b18060c0d0b0901080a030e030d0f1b061103070306061d010e0f03030f040e010f030233070818040c0f030c020c13 66
    0x142c00104001c3d20402131040c10114014440c01c803401c15504100a0071139422200705000c5c80301d21004c00d62480c0760181c0900c031070b800c11707111004a40e0030044d4045034500074851402260b4484c1003442a1350422401e070300040d801803000507080c0c41c0e040f01a2002c860390f840c001c200c0c040aa40044d00d0380c2e0742030b004100c0350341000000c0f00030036070400c4440c03913500d406030301421034142c000b8000ba141c40c0d183c0d400c1d8420320007605244c11149000301c052485886d4841d80030420112140e001000d190802c46418010a2070440c011651a00841400900b190101034105500c0411001140c0d00d0308080a100c0d0003d5804e21248800e86c3c040c409010302c00205140280c44920701003403190650b1040e0711410958148032800c0c005a160300d2100903d043c42c4a0310300c800710400d0000030341034001c3e8116400d5003030004540141001101c200404c1400801c1c40b55451154100381048100c481081101011442117291042070354001d0f001400c1206103801039a540c00e07603180115a0704150340c280e41d01141d9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 351087886 1250 351086636 351086647
    0x120c0501020f010c080112110402030403020f060a020301030c14060d1410050a18020c0a12020328080a1a060301090b0103050f07140f0d0f0608010b06070b04060e0309030d0203 77
    0x50703041091001c0800d2440080c0140794074132034080c05500041c020b0340804146000345005110036100905ca04013000740085540c0e2620b402c000707481d6003201003603a400340a4100420700721401c034002d40e0305070798103c03400000481c0303003594084410b0300c0d02c84960b4000714140310140070310305144a14025a030700119038040510b4298a81503205115410080c490099001c00b84400704062411981e49231070240b005a484030b4a500c02c0e4a81700900782c000700f000000840f4401410360100c0a00252164200c0260152001d5070715290301c59500b1401c54001030204002030012005504244c0c110316602040d00842800302c8c0125000c0da009801c035140280e200d510f240c10659061290513030107a114000b80c052410700410041c20b001195000c028026400b1501c00e0031718103d01304990540d122100c0812600d408540382e8400380195100d04141540381c20f248c4002820700804841929500c0100131449a955646110007081c1030145c9105d9880180400203132031302c2c200140f00980c002500216102c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 351089136 1250 351087886 351087889
    0xa0507080601080a08160606030c0807140a0308190504050a0f050907021617011806050a05010605090d0201080a18050615010906090303080603100227120303041704120c05 75
    0x21042c0c1c000c01240d13100e2444400890540e10503030701200744505036418104010f0038100050403050700301401c91009003100007005403000405808444210140e070703480202180410241c2c2c1c0d4648005812004108610043c44904401080d541c400d107091080c201501c3d2004030348a40c2060f00f080a004010000a004900d07040f0324880d4072082a10040840291500c010420041540304141c041c1c13600d12502c40c2c041c002908042e2182510b1307007141c20150101d040c03a501600d402e440c09458245814004250303188268100c560f1082c000e019603201c100f455004603401000280044000ca0b65a01c1c801d011410b055074070840340c2d015000070043e508003501e009611044503a000760600a00b48000c2090700c4d0403018101c00c5940600309a212944d654004c81d007013103001c0c0c10800c0e100d0b10010f11180324800c000c01411080d41540501250318848905024600c1102035144800c0d40c004c0c0005400031745804520030722814043d100303504007903495005080d03422440c40c04840c9440f011070244220b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 351090386 1250 351089136 351089143
    0x706030905100e0d120e1f0c0207030b06010e04020403120c0209070807121a0d03020723090109023703050705390a0b1e010f06080403110a050708 64
    0xc4248008000c01c40c854034100b540c0d40315601d1004c0030301c0070b06107201445160650100130340200350029507041c0c85d09148101d012080c1d11051a05403172820f81070f401100d01c00100c50003600c1d402034002116807100c1e401940c110a0700000c00d41c1c006d40821001c40018912500798414402c10348984041c4075540c410083c010b0002403542d002c0162000c1040030569100309083c1d00081510000543c1000c40503410b1001c59840308031036082405060003104059000a0307490450b02910301d40b101c01640035550604803060311401c00d034000e02c0500140140134030341d03009190204a40341c6040844c0c010900e500074040f4a8000244c883e40b01c4402616a1741d0140110f95015155180c030b18640011406180709800c03820020012440d08100c1e07142e980c1411030910340c8103899020455804441c5458032000d1040129841c0c0202080d09170b040a1040d500c2d4082d5040c2c41c0801601405103080c404c08880c880741c010002e508200a101c0c81c0403500c4014403015803030760b01880207003840354108802c1a25 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 351091636 1250 351090386 351090403
    0x5041202010c021b0f0d0606050f2b060e06041b09110f0c0705030d0e0f04060815071b080d0b0105040315090c0506040312020715051605031326030a09050f120706030905 74
    0x651106d200040710340152041051442e20044403401c055015420704200420400813798074500c0f8030000d03c0140312410400076640101200c0346420203448503032120a039400345140708049401030041003501000c0f04086c040b02d6410408982005a4410019241c034000710400c802280c00d00001c0502401c0c051601800c186040d103080c071180349420482c41e61504020758008440b071500380440c0c8075510428482c501161a07428003605501c060501c0f00f0254000000b40d03507524600403035031185500030320941d002c0344e4006544480c1c0c001c540101c1c0020304881a4102c0701c01d01c2c03910b004100e030380e151005440a0340c020f251401d0780e015401c2d0007900c2c100700740d0040400c174416102030481c01644101101c0800d04513a004146400b10303850050310b1030080c6080035006446000020450341d040e444000441c5040401c44800c3d54081d01c1c0382d0303031a8400c40e8403000008103002410f00c000e040c140c1803141b501c4c0002d0151284800880e4a07a4100344c496044140001e0f140d030132207002d101041140c2034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 351092886 1250 351091636 351091639
    0x1807050f1003090501090204020a05090301060806160c080408010c051801181e0e09010e061503030406030519090b1f0e0601032703020105041202010c021b0f0d0606050f 74
    0x20200c455480016503031500c16600c1000c05846501010402000307401159001b58094001d42d101d558014010f4a26004659158065072810000044040340000c403240501e045030001c001c0c803208040700705c5d100040d80b6070a0300c000c10200b00009510b0000d22810b8001c014aa95440d114140c1640c140014075006001d80e041051120014190064010300007046a01e60143d00c603d12190a200b50303c01815030f40004100414a410001d003100103400240c10200c1c48425103060f0b544504850102024881809030194800d000c1880600c1c000d91207542c01049800c100d690480c264034624040c1c030f140c101e08071074448102c070510440144403a004401d4013809041141000e00b0565644048000189020b04054480245c3c48251506806250360a601034505801c1000b003801c01901814060310304541e450611580c0da4800362042c0701d21281c1d17220541c090004081c440c1c003191030044480003002e50048484400c5422a6039810864001c00d10528000c1342d40c41c80c08041000300c0b400140040d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 351094136 1250 351092886 351092899
    0x2f0f042706090b150903070f180501080601060f0318050604030309050606010219060b0402071403070309090b1c1b14090117030403030804060212010314010c02011b111005180705 78
    0x1483e0341d00c1c0c44540700c60100014400d51151881000070745004240d0380802c10700e14188001042e44910a2416040032442010601c44c503661000080c0d5600300902c2681c2c00220011a2800c205202e9000498068020541444c1031034030f80d03c3d461304140050b40d045000c41d07034a81d035180400809201c40c070b42c0f2000034009055598181c02240c40305140190b002021f03550307a8020410a913407564140ca1225030022618440311100ca407c00340d882c0e000510a6000c2a440e42c00000e01000f07078024180200c83c01750081a040d00c6d446a4002c80c3c000f152000c032001d0708280c1c0c80350080d5400079200d0008001d60750a0398544c003280001c2c06401041a003206003501240e010b54100c10100000700d0702100c0d414540f0348920b0751642090303802030091485038052480100000400e1012005951a40d0304500d0000c1040381d1803031500340c1c2211010700d1401200b0354546400300050b4028080d00e40310760201000d440d1182a491522000c45d1022030312400220140c03000d489048a04020940107004162001d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 351095386 1250 351094136 351094151
    0x2115030105090a020607051905070806100f0e090a2a0b03091c0905030a030804020405131e080d0507210e0303010e1302040e030307032f0f04270609 65
    0x7464443c0200c2c100a8060b050001e070384000c0220801c482a428042c2c41541e99403402c0c079103449916071102d0701c11500c207482240085945076048010b0300044841c0ca090402005261409002100390f00801480311070203282114004202c0c403001c14040c03002003241d054441081042c0603070000d1856000b0710307002801401007103c082c84c0000d000400000800e6000280c0301d0000c07040b205001160085074060040d8507144041507040880e81d4013552080320240001e0f03688662400d07440070540b201610494102c1d00098100403541ca0b0342a42500a0744030ba0314004603090400b080d42c800b80c64480028500c000e02c0000d0145074505c1d070740c1c039841e003e0050010703465400c0d200d0b56a0006005055002c2c0d90380010918140d202d1249241640d4007800600800000c0b91000b034994204495090109003410041c0ca5001c1500d4414003c0d50308040711809220048000e03090700d50058000024180002c01c408690445040e410321400c1c1c44030102c2080c16412071000005580d00c44d4010f0000a092111 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 351096636 1250 351095386 351095401
    0x11040503070e130b0907080d05031501081306021c0515010e0d0c2312010c020f030f0f07020a0e0a0504060f0c17060a09021c0b1008010b030603032115030105 69
    0x4040d50b6540c10003c01d284c20f0310382c010001c2c00c012481c1d20001b91032041a414280d403603008409140b04070801c0c035400311241d14000c01504c83d9241154842c1d00030250780101000a042a4041e0a4250010882d04403a201100240040b90f00176204084820303080d9007062400d41c0d20070b840719290340b801c1e00e0f00011340303901c0e80c0c5060a2030814003840c078000c803200841c81e440d8203103081d01d400c41c28401491800b80c15110613050380200140700e98030b001401406011558200c00101300c5030101004441d070392809400550303203103468118940881e40500303c244006488582c1c00202c5005851072a000603940c10645410707400c680f114491642e0079810017446600310ba801011000d803a01c002105407000390b03144000036125419070381007a01464030202c2c078201c0203102039041298000010004001314034144041001002d0161041e00014400000510191451502943c1c00c09005407c0b00c1c14a00040c110045c8542030300300e280a08519203040165020340c0f0440802030000580080041d810001c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 351097886 1250 351096636 351096661
    0xf100f06050712050703080a1107020d0f0209060108070903080c0c030102130602060f13030e01170901060501080c0304080a0f020c060a050706050f10120f0519051b0906010c03030b0411040503070e 86
    0x825242341036946546404d8401d4140f000c641d0459030083c0000d80c90150361804072454012044283d02400c55a0001544c9500075a416801810329840b440f062529503540c1541a5000441003c1c19000b00e00c0c565440d43c500b40043e07c603040758000784815260030104000c0c58520008c0100c01c0401c41882031202a00d20741503042002505441e00c007001103030100041e00d6608980b0201c61a2f50683c108100f4043d00c1075003d80b01b50345003680c6019280c0c039444d04141150009803001345c8006420010200810b01501c03002802c80c1881c016144032106410006800360080b0b1a641c012400000e091010403e80d8844c3c641c0c00001400d40c0000d40c108203000c84e0340010705000e5076910080c4c046c90501070214411b00031361969805411560b107801003002031101018144000c844a104100008101a4026541144030344028000e4031244d0344010045405556081302a002c0c544d40e946110a161518003400d04d80b8091031b007000c1e946924000030f061600310554880000f4054403170601c5901c101c0031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 351099136 1250 351097886 351097891
    0x636022e020f01020a120c031839150c06050f0118090b01090c14030114011b05060c03070c0501050a090c0807030201021b040b06030f04020f180f100f0605071205070308 74
    0x13903800184008201d03400d9000b00312584040241d1281c4d031880404210058010301c40485580c06c01cad8243d552002409455a00e1494441c2108000c40c6014042102d06541340460140301f450140441241c40d103a0800300c0300c05841e96400c011032400103010300c1000075880814805590303410410a038640d01e59004040040c040e00c45559210492158000d106801545064110310802980da503035070381c24910a1314182078000d001c2404c22403403a220384400703c501140550070002400c1c1311360740c03c0c1000c840ca42c00102884103101c11060041e001c81c4091241c0e51240300101800611301c0071508000c02440020313030110200e503000c0302003800140d1340400e641441c1d0342c80202620b0112144000207018000384010b01d07801201c003108124500040001441c091070083c0c071401d615401c0401070040051660304032040507865071010900d0141c1901c802d950101c84440381c0905187c0700c9064095841090344003100145020a50505119005400310800007850034414078111140d0380241666030300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 351100386 1250 351099136 351099167
    0x30403020d03111908160302040315020d020d06030b1e100902070203011b0206011802030106050a0e03010b120c040f0612030f05040305070b070636022e020f01020a 72
    0x45031110344500f040d00054540741070002402d02084981080000d021400440d01803d880c0d00c09400c107400079001c2d100700e0f03050f20f41107641e884005400074040b101962282801c0415a9401c1210a000201074802e213030195126103100000c4c3d040443d4070708800070049400c3c0b603900f40708009100c1e003210010f0006003100d0030f282e0007503203c200307500001c4c2c014420741c0250700f010f1a51840d6500c0441d404103241d03060b00c2208284410300c8900d280b03e24102c0c0000d001e0311001c83c404100002c03003140102c0c0d00c5042c25000400111300c2001810104000607100d0301002c01580c41003122150924050160040201e0b1042041104e680fa00400d821404103950000d020b110f4032100564041c0e114030100d402543e0068221869281d0740c940002695010090680355103203028a1694034404c162016003c42a00780304618100c2000d44d9a00300046482c002240d10402d04035001006020102004174000c45032660f41080183e02000030742010008258081280d10410005100a40100110714000c80 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 351101636 1250 351100386 351100391
    0xf02010509060117030c01020c030405120106050d2a030c170303090a03051e040b030115110604140c150307020706081e040303020906190207060302040b030411010314042105030403020d03 82
    0x500b1845600310b01c2030003106c000d40d500000e180b440040d0f00000810031140155034041d160b01c1c0480145080f5005406202c1d404030180300180c3c00702d0b800240e031035466100b04241010a02612815042d500300c181d2080381d0007654298100642c1b81c1c509030301f240c02e200480185246241610a00b52200310101008051180125415510480c107820a001c0300d1041c450190390740b41c03100720491441d0802d1094000c1d41840700d4280b01454422014004a5880340700101425111541c1341d01110402c00801c164901c05c003030103000603548090000840c200b51035880e03a80c034203000c1e4009081c03050300c1c0c000720300340320008040c04170318160f007992503d0b00001c80d40c0b00b5000c0d40b21803408501034070449144950150000c5810a0741100014084c801e285144d0215000c0b655151011740c180d0050b40300e052050b100c10300009000c0f503100d84664101840500d40000c92861116105407640d405a406a6200d800b0416907950b072241c016141d01c4200702814040d0841c5800e0758002e641c1e0800100e20b604154 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 351102886 1250 351101636 351101669
    0x50a090908091003051b0403050d1419050417150a02070305271f0903080c01060915090c0306050907051b1906050a051b0f070c0b03070f020105090601 66
    0x201d400e06031110190000c01c0c2d00355203007502c0001400b400081e00c1908000c0110f000d01d107507000e203020441c0d040701d0b4007034050501c2ca04000c00543e03028010402d50421000c0c01c1101000c50303445441d2890b02d024198603020b4440b4240300001c02e000360340b541202041d50148035220009241d0158095110440c841c015070b071900d081c0b03421101802201b90f0394014034000d41f800a2007080140e5100c03070300e1600b982c00d80301c100d40c4454208480c0c1450118480481d255031801e1011580c1c1c40b005001030002d4000200d51203590f031824208465910200511a400e04141071250039028060382c08100000d2a0a100c1c1504080c00641100b0000c3d010200f1b21200041c440340400e200c0c2c0341c422039580c071032080d180108480440302c40341c1c03a19004104c40e600d107090009211101ca40c407445002c0e1038502c0c802d4450700302c080c1d0b01560a40c000d1482d2056540107010110008000840030320162602c1013400d610b03400d1540020b0800c9850205c01800d40e4100410014078142c002080790444001800e16401003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 351104136 1250 351102886 351102893
    0xa0c1d10270e03030103030906030506030c0a18090804060f0f0203030c0901030509010f0f020c160f03170c010c020703060501050301050609040b101205070509010e042a051804020306060109050a0909 87
    0x106003107602c9215501020000005140d000b13070581003211915217041c480d43e52800101901c0359140c00210340c5c0084414414005070074804007050125581d0b100c00190340c16151503105240e002070740000009241d0741a0030200580c080300c0100044603a000450079418541707074101044c01070209890402d580d440008102110035045400702405030a030030070041d00c0d61039041000c0d61001603031200030301c50710f00c1c40d01c10004c00e40c01c140100c0356020701403910030b41540e45004100012640145414106100d00e80c0451000e104051612007550001d11085145142000603904141c1c4402e10907403402040002c02e48590f2450390b03100794000050000c50ba65040c6240310100d0b1508510b240094100c51181000070002d4080141c90040300d41c00d20076a40c908201c200e8084c11100281490319070440303c0d1040301c01743e80d182c00e50b101c10101c0e18005038880340840c04800c1007001007900e40040c8020311055040c14080305402031800c0c40d001245c90304203804039000d68410b06c5120560359840c52020140f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 351105386 1250 351104136 351104141
    0x114041812030603030306050a1406030702071d0105130e0303150a0f0902070605010e010317070201200322121104060e18070b071a090a0c1d1027 64
    0xd5944081251012285500014000c003280c3c081140070070715000c40410146810b4807c00c1c111180660004503022000c000e11020b0740010380000d0551246400219a40030030200380c079814110b80030007112a41c50401000200c0015024003410341d89807102c8014801804800c80754004c80401d151a456684100410a00c000daa0f00c515602c00f40b00c68081032909480d0000d200396400b07600f040c070603a40c07190f041421400080c03000400b41858800d100c0201b02088002d04280e600504001e001c41480008886000400301000031164100040001d01041400c2e04404048034040c020680b190078074030218205103103014081d0021b000c814500c40b00e0b07943e54204401516100c40d40402d1420080d40036918032445644a04280c000c1c144003040312003041050300c02d02a0841e00c6414218004640c0800d0300c04c019213503030701900a041c51000801d140c58250b41c01401d00f03400061218014400720307000e50703001400502440c0541c0c82c0805c50341c04807800d034501309041000190103121400045100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 351106636 1250 351105386 351105431
    0x160c17060c16082832030106080c0403021302030702010c020f100e01020408030c010204030c0602280201020a02150c19200316060203090a3203010b0306150f010503011404 75
    0x102d02c040440402030190340410007002d005c0354401c0e05940c8a4074890507814140000348981034003002031004000461160081c19080200039140703c0c90280c403900454260b00807411516000c40e0000280852141d0912403440d580c0054400741c00c00c0f80583c40d071541c8415880c001440c9641c0c4881c000c250038042941124000d01c44035013142d90319803009107410b010307401c00d10090751101003550f0001040383c000329031180c0c1007807001502d8001c80f00e240000d0742a10301c0761009034114031610102400580780c0204901c2080a03204100d41c884100030455071800385082c03904004815106031400000d1a0000403041c241c804100605c8503001d40004240f90000042200044000341240000e0554020009207004601911240380d000d460f688000018640380120449800180b001d00b80c6003800c18014035401080280086030038070014001910744001a52701090800031000480d032281740c14442a085102c0a00b0004c0c1035600d45480044001c8026464030b01483d10341c0d40c2c00080c20400e00c050700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 351107886 1250 351106636 351106687
    0xa2c1209010225080706020706020a03050d090f0609060c0e0603040210030e0a0308010303020c04060503190501020d14010e0702060f040611090a0902030a0b190b160c17060c1608 78
    0x601d140c0009100100343c03000e601c00d00025004000000c17035041c0c13000c10742c40191760781500245000c007000d070380454459000135400700354203980d01c1c609000220108190703500d15005080c040342c80c18072400c11004840049508005005194407180e03c591141c00540b540315404540d245009000c1840030380240111144014150080203e6107041581001245060700c0c0643d00b2200b90f203c1d80024002104d07518043d190f40b50340a42850422304048810031907030070748100300146c2400000c1462109680540942036010b02d603d0b001031008242d481601c035800100351008061a0500c1ca6000076801400342002e4481500d50015011a240309021074410a002a061b4218240d980da0040300a4105482e2802401e040c5004040d040c0303000f1480c7c440c40011004203554451400c180d650f4654410250303040354600301000c0300013190034500c3d00801800f08a849c038440502042d11a030070b0804c000c140d403003440f00c1404107002090082c0480d00710300d680301d14800e99070205c40281150710300c486100c80 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 351109136 1250 351107886 351107923
    0x60714031f030f0c060c021f03060b0307031a04091a09070b1216020d02030324030f0304030b1807030809060705070f1403030c0607031104030b0a2c12090102 69
    0x400c80000e43c003010711402680c4000819843e0801210110001c2401941c015101444082d04071064254120b07682c010703080c00104156900b403814025042142c4c200b0100307907254041840600345941745000c0300d104580402040c141030b590102400110b1034003071000e0448a0004520b20010041003014000360b1050903201c54070143d08d0302c0c140804460101401003241462012180001481c1c903180c0c501d03401450a644d51a0301c0401e2018074490400349160740300311010340d191814084030141c41e008801959450b803d40c140881000c0c8058521407022190803030114105801007004070030780b540456899030750501c03480050305030301840c2d00260103401002400900140c09600150443e50005c02c00d1415107200b8007090b441e80a1445590810f4005000050026100354080c00000050701003441c1802d450307849100c04150100c07140200c0c603079136500c8410007032881010000090b29002c02140900030114403207890710070fa0100c11400c0800411180f071242c2c0244a41300a0400c44043c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 351110386 1250 351109136 351109139
    0x306020a110703061e020316260901020712020d12050a0f2415120507050705060411091005010c0303150b0c030403170702010903031b0c061808060714031f 68
    0xc0c9006104603107419103440200c00b0055514030080c02a03900c130f0601070310040010030144205496540390070192041040d940c2701c03068980070070141740741c1c050341d020800142c8544085c41d0410030b545c0410101001c0d58003031003007503010340d41c030402d409280b01d058280402d564644800302000781c1386002c600c1c80e1351400c180c1c520484007883e0340e0000000d03071042c10442c00d4030ba6070307039002060a1059010070b00294a5165540141e280c540042c0d400801d145091850280b05840c1c0500300303803060301c00b11510800c41e41ca40b180743c9007507400c5540040c4561b0851041500d880006030181000740300050078180c4400c0b201d4010703003512200c00010514081665518011905241c2e00d0b544030340412924500d5900d2101c048541d80001d5604031607041c1c484100035070841d202518a1159900c00a08603e040d803082c000089656080800403e800c0e00d8180701c901e52045485c0d07200b03446030082c3c4d1896000008014101d03604c15441c5c40c50300440d03050143c0c1c070b858a48d268244c288041c2da4021105a20290 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 351111636 1250 351110386 351110393
    0x50904030f031b02160501031e0506130219020d08060120010608161802030402090402010c06020c01061211040e100b060d090b0601090b090306011401030f151d0f010306020a110703 79
    0x514400303028917000720a40040d1030700d0065080710301701d651181048180701000c0603025020340c000d9801003002065918a0341180008100340da010700c07035408600c1030a8180f0408181c0401800401303d8083c20301103098584080020030003c3c52600d41d1105a0041c0b061080c10842944520098450f19081c0e500d02c5542780d009190482180c071541030503e0743d05144050300c80181c800d981c003c2d98010b00c904140e807519001110070601c2d02a059130415420095940d01031001d1140000901c513004c000802d800407401c0c8000c0e07601e0092a6103000d40d040440c19821640007044401140890050000b044020702d000709a0310700584c107503030f06554030b442c00c00010b01102c250144c0c410301c026a90914182c1c2c0750030807030742c0c0c0b8010b6800181c0c259002400520003856140164000294180b400044031100c01c68a181074445154801c003904004600c140003e519803c9a1807102c54501d0000b4814100703030103405801c0b0014807010705207a50205001004500c2541062202c0f00040106c0c0d10440d03c1c1c2c00d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 351112886 1250 351111636 351111643
    0x90a0e0706110d0234120b07090603090c15121a03010b0a03050705100c051c030b0406060206060d080f030a0c0f1b060b0f040c03050a060f050904030f031b02 69
    0xd59142180c41204604800c00d0f10002d102d03039042812080b4400400703124030043c200183d400f0b16400d0303809917084001c584038011910000b00329008030310305902814003020107070108080350091410103041c501d4403c00300c0d81d00b548201c00c5502c03003c2101c25601034420300310740000102c07641c005e4190074a0005496014403884c5561125030460003000050501d808112107400c041c07100904a03040302408212720320300240107081002c446d0030000104000c5985070303800c2085490b40c0f5560002400210f0200507410b10584541d84000e42d410042a414480080d40e50390340100468818a080d020306c1c03041040700f000307603205202c0c06924280c8a04080030f03c41c0191a9280c44940010385109003405182d2240188882e4800c424031414802d84140e1220b501034032000070303015003201045692280c1500c60f403181c1280303050569070000e0641042510402520340c0ca510400c802c5000b05400c0c48039170345900000360050781c18100310211400010080d4042d08880c1e4004e6285801600c2c4030703002c983c012 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 351114136 1250 351112886 351112907
    0x30a0501051f030209070806061b01050708010911040b07050307061b1202040f0e09010b1012150503060601081f0b031f0f06050a09050d0f05071211090a0e0706 70
    0xb00b21a0000e075210520801115051002a41c40303100c50020580c014000c4034070540182c8007410761848c001080620780c1c82c802000400b264184e40d10b80c1000009a07100804902500e4080400d210004500046012a00450007100c03c580000540c080030440100102c0d45000d50101080c004243c03104030f0100c00d450510f11010114082c900c0302d11103c1000e208840503262000031000625040c05412070241d100100441010341d40c6120075a1103540321520148610040e640b42c600c81500c0c18000002d440f400007009010b42700c000810b120b1503802107802030340900f003864a40d020380e441e000da0081c10304550410608418101d4400318040c0e4485000b1403140301c08140501c0421900c1d80515091200c621545a1a442c1081c09019941c828401023148402138500004210b44a07400140340129059013120303c44100d42940042102c1800351385d0040484c14484a014444c131b407240024054105c06291207040624006100038456a100020f00044a406c5403e0203803290400b0340405242c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 351115386 1250 351114136 351114151
    0x30708070203070308010e07110f0c0a050f090619150302120906131103150a06060908060f071214040f03120e0c1509030f101406010e0f0f030a050105 66
    0x1100041646000008581081341d169807035000580c6840d10324907180402500c150b0030805164044000c0400030040790080714050006012054807800421000f042d40e94071260045001024081c4070f030b650200e4240d803000c02569014030b025501010280401c0b1240c11001003d44034880001109a0690150075a00d001c440701805948521002c5542e480040b41c1d40240350111081c80800104c10000c40c1406d204007604075000040c0b01c0f140d1910b903440464610002a5440404100b840d41c840380311030007001c481c000380c620303414481001c1b240d600b0300500d48014010b80704070040003c41c01e030f817042d81850541400e04000e07052502e00201c40c160340c040c0030390019008112100d01c03101188140c5940303108040c0140f104480c81c1c014400c411320b08032401f0414070301c1413055103480d44040c4000407840c0041406041c03168900341c050800c4848a444180032600b0f0402000541d0340c00450b40d004040d011107141c0d00c0b2100510000320f4018000a142c0c0c0c00d070048031494030401c00150451341c01440c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 351116636 1250 351115386 351115397
    0x70f031e0c0b150102010e0708010e06070507030f2d020a03030506090705120a020904060b130806102106020f09150c0a02010f140304150f0507230417030307 69
    0x40030104681c5080030180c007401e40b0002c90701151401102c04600e01d6602c0042c0000320b110b402c1084840d0030491558841d0302c8a0351605040010a80144509a48840e41d03040032400d05001e0b44001303100481c1c95030b4160038800850424060044e0320282c0c0d0501d18903801d5000348034098000300079203540003240220042801c007408170b403151901042d0300d482840190390f60741c10007100d4011090300c1701e005004500404ea08200744040e5856500486002e01000440c0c0c070ba1320003d00c400c40080740d07621360102c500c6800030410310021700d020001c02e104540305c00c266940946000c00300711620020b0400010100340c4006803140c0c40d100150050a070050b800c41308005203546403510f080c040e1091800041c241c1e0000d158a030010b600444100300e00d0340c034500c0c21448036001c0c190070640380d505c20b0303034141c80c1c2444060040d20aa40540154903000110a100340418108840054400005045a0381c0030301500c421452021950b0000d44000b07040d602090f072410203280c080142c503030f44282c8420340000c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 351117886 1250 351116636 351116687
    0x50a0e030a11040c11030304060c080a090f0308280b040e0f0309011b0b0a0b0f010c0f02270406020a080601021f0b01030e010c020c0102062802090105070f03 69
    0x24000c22108111500034841141014030b5004200051805103100e009001124907969034410040001e103102d44d206580014000d40308110141040e20010842c10300070381408040400a80701400070356071550301d4180f54045441e4426501035085c0300701c0c40c40303940d070048141100b00548e6a40041c070b52440f05480030000b99620034101503c03070a5072500440f0583c410400034016510070b0000214001c8010001071800449a44141c403c0350123945188206803038405a92040c90441c40d20604e58070300b420100d4100d01d80b992041400252400040e104540c3c180240450110264840010480f114605043c610306881c20200940202800100054410000911550002495403609500427401c80705a40c4448030300c00160001c25038540c10503440794011100c003d0700b4058030a075030301c2a401800b41e100d0801c000910f41b14008004a0112800c02c0b030b044c070101e401c00d280d151104000350f40940e40342203190040e120b9105448005280c4d2442d045c0b40d07428035911581464600c4c5540d012004401d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 351119136 1250 351117886 351117889
    0x10e0604060e0c070302030705070603020d0f06030210030507020c1005030406150b190509060307030f0c02030a1403040204060b0703020a05011a0616050a0204110405090c211510050a0e 81
    0x8072441d024081003510303440003103580000a90060f00d01d5610034411a860a43c1942e140d074245400c1d50312801c04650049082d01e030088540c010b000549100007401c00c00b461840d0001a410700240864406060740d40c00880c0d01c961007071007010340c820030240c201e051489200900400c154001ca4094405a20707006210040e0340d40d00c41c1400c100c030b102145050034811100c0050711010ba841d200b0302d090040030826040161203000141d84030b02c4251300d00040b0b05201d504240c0036a56442c100b40c0c210b404c100b200c0306050340c0207044000b210380e0b0320940030b890303a030342c1d10120b402006160007442110902181d031380100b41d0300140714003400744100000d00032100c030592005841d61001c400310784e1050050011a0144142c11001030500d4003841c211080441c1c030b9008102251502002003101d00070028040c04541000301e10160804260035200d464000030788100242514481e40140c001150700020a00784820201e007640c84d0303a4010107102030340d10f100740e01034031a40c000c0040d80c001c640701c17090900c240e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 351120386 1250 351119136 351119141
    0x60509011e0903200f13060312030603050c04090203031b0102070b0f090d0806101d040509010b01091a0403020910090507081b031b03100f0806060a0e3714010e0604 72
    0x181308081c085400d416104010440f0b82c000044011a40300c0d900c1100002186103c001d07054442803031786000801c1c42c15400c1c201e09042404442900842c10300d2100c1e401600c001081380c00700b0101d00d5800400c01c8060780c50502910908001500c4103c0c44001c1c807802c41036446002e030148100340b0032541906801d24084c4d0359180e04541c40790348007041c03c0b045e4444a006400300c3c01000d0300d0108550444030b8520004003190b10540700b000c02c1c1d0399500d080415035600151404041d104450700b070031032943c900c01d1150451046000007405520b4010108164945140f07480303010344075441c014041c074684036100802c4e02500325000312255000309150301c0f001c01420210b80c090016200b81e006000221420024103038400380801d46a001410070026291240c004500068802500603201c039043c03600030000030013256001008000c4004041c07111820810b20b0854003086498240d6038500a00c00705081c980400d660318130441414201d485c03048003103001c101d6042c3c81807050903040300c0c2c440f141030004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 351121636 1250 351120386 351120443
    0x1170106020c0f0a05030d1710080a020f220212010f0308030402041d0f0304090b010311070b041b090504030f0e010e0108060303130303050c070603110301060509011e0903 75
    0x1580000c0c04400240c2449040b00000f0303031001e858154050f80c1d81c00803034036190300c0d1440100016110901d0315403401c8101d110030b402542101d2030a251a080c00d042c0303500c031000100000d106900711a62a01207848415440713800c2d00c488200c4000240000d00010041d500c0020008954a030080c0045542180a400d81040d80d40001410b825a070ba0b550070b02c001040c40316002828162030200c1140c2c0707240c0401482451108150240d0740721840c081180c0305480102d1492418182007140414003200d412082d80c00080c0c00c03010101241e19581444041300c2105403a50158010360000401c805055411242c00350b40309540702c20341801024400c881c91001024882d0014984a441350020b6108075482c0e034012000901382c92500104410f04504034805600c11004210042a458040d6509110302002000207040901c4040702c4003c3e03048282c8014040e20f401e01c2004100325409174494030b01c000c0311070741d01c0d5003610b018241d0f02070190100a42d440100c4610444421035840e80007600c2c813013407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 351122886 1250 351121636 351121649
    0xc010f05030a020304020f0301050c1b070303270803030c041d190908090607050f0f0703080d180611043602070302031201090c140a122d0b011701 64
    0x103095071102c0300000c02940c40944282e90244445c02100c9184d50284250350181a01c41c052a43e03480078a0030300a11a0601e540051140d000b03945c041010940000200001d01400f10000d104109105009032880c4080d030804002444007104020f0b4580300b9000600035100ba84907031b5149000b02d5448860782200848a100040200070384200086c01d15400003001148607a00f80340c2032541d2140840c120388c21030f03101590240d00c040c0c155240301c1010f221141e20350a680c40178003402415903c0340015132003444910090700383d5848400311030681c032202e0f1641035540150240030081c600400103003942c100d0700480c5141203c1c000c921410400c64280c1f1000c6800300e07907640300e41980d80c1601000075040048182c0950008000c10720020300040c1095020b080942c0d000501c041007900010510000300b00a82540c6d8410840c858030706420084c5204007d04c5000080b5200c0c50002992100998419030300d001c0f005101c620020503203850b008100c940d802230342d030039051a80740b8450740c80d860020700c0f904 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 351124136 1250 351122886 351122897
    0x2101061d0f0111010609020f21090c01050702041103040b04061b02120d062403110703020318120706020c040c0311030109020f0708040303120e030a021513050610080c010f 75
    0x354002e5005007058030380d02e111000001035459035600343c84140e0380702c900d50803168103001403440c02d4030802c42c042c4020540b049450342c6aa15201111545e43c60300c40007090306110000c94050215a11900a20300d04c2640074513968480c14a4900020b000d01d060780c2c112522801c1c060030001008400843c92100001030380201082880e00c0400700841d44140c110003002c1c0e0b01c40c2008140100010900160039004000c000141440c0b4103008007150030203a4001c03003110040000e2408a039002058950004003a4180d8a6100b04000019a01c000d081d842c0b0009025640c0001045900032500d00c000383d0040e2000c2c859100705542c03c5044518624404081c241c0c280010700c01d1042a40c0644178901201c80d00760304e0a0b1071512821040d41160f03000310001340c1c40409218000c80640140c0702600c0251000751306160740c07090040d4894140365290000443c2020000c1d0315141c9034000744159580041c01c0d6049414503000410042c96203000b0040d0724803a09010305040c3d441003041b0710098403582d446 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 351125386 1250 351124136 351124159
    0x19140f0c03030412080c0109080a0f08011802030a0b13020706060506040f0e0c1e041805190b01050f0a09080708030403080909060d05010509060613020310060509062101061d 76
    0xc01c90f0150510015281903d0506c0710303100210017442040720a0340110281c1c0e13210070310a180104151031680c6600b0401207006c0041080602c041713807100b20a00081c0d4096101da891010000081030050003203540940c03a60500c00301904943e00030070350140103800078880383d0340303520a0090328422440b4001680023609020020525001912908030030b408600519120b207060302010340360311000c804810070300d001800300109494011040c0700740e007841c0030074411803600007020b00d501010044005501521903c140010360320420032244c12011107544540c41300c3c00400f0041c4080018080c4002a200c0e28a000c00c074120f00109039401c49034810b034039611f041c99440501c401400040c100d81c4e0003140c00300c0030308002a028040c440c4600020b50041030f0520341282042301701c2c6201e0403410101031041061109441c421180c031025111a4103110b49c0e254010000b0078400d01c0340c420034080045003441c8068108051000b018107c900380d603209003090140750000da44450700042c105a100c11204103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 351126636 1250 351125386 351125399
    0x40603080a2a0b0106030b01020a030c0b060409021201060501081b03040f0215030f16050406120b060702090a091a1e064014010308090319140f0c030304 67
    0x203542c1d800c00d60582c940300075115030035150400c0790741c41c1804581c1072060078018001c55500d40300340002d1280902c0200050519503c000e050b4100140c40900f607407641e5000242c058440d90007440b80194054011154154800c0105000300900c0c0900c0d400a00584003040d68a9040e002100b180d440507404d8a14549035641d584600c000741e090200d8000302000e0441041c5002e2101031446074610360b50f036000910308104031082c0e1908041038001400810b00c0240040d0ba44000e05d40051110b020300044d140c2c04440019406001c3e44000a520000050030044000155004501041e120b851000d06080c5c042100340545402159011442208444403000000903c115581c00c000040c1c41070b141e1940e1600c1300c440340e44154010040d13860501030081511003403034544400f45141001c041102c4a10201d4900410b0410701c805801c101c1c01160312040703503500b40014105400b0382da030800841101f030300e80040b030b007551285038406902640c0131503211383e900403c0608003010001c01451800d0304082 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 351127886 1250 351126636 351126647
    0x1b24270305011107031d0a120803060a06050f04061209050109050d1b0b13030314090f12040303090e04080903070306060509160206060607030e09070c140706090b0a051309021305040603080a 83
    0x1c846da42c000400e01700050980384078001c07851364601901c1c0c2e1682d6031402e14140104540550b02407010041c040000c240d070112301c442601d0a6591502d0411460703003d2035145800ba20702d900d40030b0415403070b08007000d00300f00c030005003110040002d40302d6840502e510300d020000411030010180a44400800180a1840311556070b000c0600c00d050008014030100c0002400c0581101c3d5503c2c55030000030340c111103020400c403000031801641501483c0608590780107112441503c2102014440d8a0129017000400800c2c0c0d25450f0010707040b94062136490500402400003403240a00030251007002c140b450455400c4856094000d4004101e80c1c0c65081c24402d1079800240c0950821282e040310030b11030f5440c009030381d00803019903481200d130000714205801c04061042c0900cd8661000c4400c00507103402c15548000c9070f0a24203007070385030b811012084e01c0c94480d200c08140e080742c01c9800400c40d07000c00c1d030103032a10740c4a00446006040d240c070301384030441d24240400740035428103011001642d07210386c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 351129136 1250 351127886 351127937
    0x1e1205031201080601050a0512071403151006030c020a0314311d01030f020f01260411040b01210204030c09091b2427030501110703 58
    0x40003100d241c1101d0300180310a0900070b0304280101c0d00000010402440c2c41010030300134000403205100042c00c0c028072180d6800a80c401d20428203c102022595981c00344a00c0c1485050b05c01036904601e0410352206216506026800100c1e241124001f81c8070f00c0051040c4c041c40c0e15031030302c1312004288203100c1c10640000038181910b95060340140c0f04851540a240c0e40e603030703141d2a091440c034204042c0320b100501c2141241003022441e00100702041007403480000d90354060352683c58407104a40100ea150610f1141c04544146000d2040c02c0e00d00400c918070f2290740210100c080e80d8070340d0001c0006803080320f021035001541b4104c002c0380c4c0b241503007550341c111401c0c4800186072564035600c0110039296a4040d00c20a59940300c07143c10701046070b1650300500214004404070908040e80000d0400d104c10040040c0200d0440601545000300032500152958413182e00c5800d0441c140103030740b6102c40c04125078550030400000c1c1c1c034504620075030340306c0b82c1d040d243e80d101c802c4910034510105105 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 351130386 1250 351129136 351129143
    0xc0303190605030d0504030215030417030c0708041d06040e1011090909030a030b040506060d0b03010902090c04061805030c010c05070b070602430609050609070f1e12 73
    0x4a001c0050075603400c00c00c00701d00300c0e115111785498519500402008803000349070120208010010400003440615503015038030b04101e1095101d4640c1c0381303220307102d00408000911958001402049080140341c0040b400d4101d900c1560b02a5250340a010580329644150666503006070400141c059250700080794091807014840d050940c8107001518920080d148a4903a42000070849030381c3d079050050a070525010345084c03040e41000e1000c6407840c8103445852400c40c0e80c6484d00c1510340d9080d000b543c6090313001840d0481c2800c00d180000e034039902610602d80480e104442d094070044c54850288211384004002e0940000300340d0041d6044410303103508450600460102007200401800940310076030040c4c00041e101d0040e0754144c0d000d0500055440c60700c010745540383c0c0842c03020b0690815070340d0003104008450607152600c1c030050488000011702c01e00036901040381e854000648907049502078503a00403419680c07040d2030443e60600c0000740b035481000e082404200012014803018a20 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 351131636 1250 351130386 351130391
    0x20d0c020d0f080306090a0209090a050408270415030c031707080d021803010e0705011107030b040803090105060907080109020a120f0e070b0405010e0d03140a05030f010b0c030319 79
    0x8050380c0b5500b8100907514100c0f419071011060003c1c50a00050380e640c4034800580c1113103010700e40310000780840001020510b1036034840d000141001500700c20340d22a41c1269a000703e80c1c04c81d5007000d90b0f0391540d4150060199180c190700860303510186030303d84112074012036919071003402e5440b540718240030001d59250f403200c1001884001a4400021714142c80e6a00e0016129010080d020316042050180940700f80c4c18842034403414031021840c00f04482090801714a030b19100c050381414040540d201600e0700c01d90030200000d100003040110720919030f01c0002c01a42da0f400c42001100c0c0420365000000641d61001031040c0b2419a00602c3d03050b829040454261008413040d0043c3c9005005546086448000d01404102c04000042c040d1141c0c954803809d1074202000244404451400244102e03000c000700b0701450701035411001d0303451400359850703615000001c6c040c00716030060b0350b00c4103511090f9000080c3c0e03107400b000f50344051503e00040c619585807241980b5544407040b01c038031031495 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 351132886 1250 351131636 351131659
    0x22109100c0213060509010f1d04031e03140105060712050304021918060e013623070f08070302031e131406061c0305090a090e100c020d0c02 62
    0x2502c0748004120f0700740e01c40c0d010641e00d04140a000041206a03c5010b003d034600300b040c0901452407484072038404c01070080c140036550364101120b801ca04503000e80380d201c510340301c00b03419158103422611030320400c400c01030040e0340e84901b0320440d0311500300c1c040c1543c03128450626030035125800640d0818002801d19017801030740c0f420410280754a60100c00021500c080d9002e0402d5107004420051400d54400c600d60340c902905007128010b0000c03001d048040c0d101a411050111101e120624171020300e0411140000c00b1889003610018030220b03c804070740c140040c0c1d8040c820180340b04c0c07014050380c071742600e5242c15000b0b901942001d41414200240340d010542e440840c000c18038030880c15503e0110343c00d0007600b0540d51001c500c6d089480960070080420025841c0c00044104450303038400f80d0310002c032180c10b04451134001c0d40040d0341d0040c40c03071000040ca420309410a038506107801c815101d07070386800d034195800c6803a824101e0b0090382290a50391500f60241411030010b80c0080c04030840203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 351134136 1250 351132886 351132889
    0xb030105010e0a0507110601050d060e0726060417161205091003061a0c0f0111070303061e051005120901090b07050f07150e030a0906022109100c02 65
    0x1103400b41c100c03207018038100d0304001c1c401c0c8850060642004842c20701210003074100304002e8841c0303014042d5600441d503c407000c6040003000e61100d580305180c5400d40b600380c3e44404818412243d180c004481004203203240756500f034070104006018940c450340388640b10182d0840c0350800c1c1c0042c0c20030410740c100c04480c0c1000c55445000000c45c5405581c031070366143c007428100b21705040d08022180405203005c0c1c040c042c021802c0c1e02a03031f40c0e0162141c00d50306c6000009103030380341c03469030701d42e8504035400c01c454244004000750140200b14403c3d01d050081c1030720f0f030001d00089848481c80e481202c05100b001c020a052101c1004600d001d140b03031240c0303002884803500d07603540800d868000c1181c1d910301603101030040750440309400030654940903103840d0101a00d40098000d007803000d403134100600c0b0485217146059201c44402641601074949400748480c0103809102c840c8038603005401000304038000e4400d4542001458401301d004142040c84c00405d02807080d414450800c10700c000e103030039440503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 351135386 1250 351134136 351134141
    0x903030e0a0c030b100e041407031712150f040906060b04030f0c05030d0507080903070e0403200d02120f090a030506040515160309031808030a1806090303050703030b0301 75
    0x14a0040780c102e00c05600e50f140c11105240b000700b80005a00700c0c0f14040c011034007441c800c107070000d03008482c20298449085000b410503030b4503400140034281000c1d01405512281000e0041c2c0c0303110a45a00b1180d0340c0d2010180c070380001d0940643d01c003840c03015003821460144d01421849001c0c10000866907280c0c800542c80d640f154005460041540300c000c8100511180346001822064001d03000c1020144c102608500813070034020010240480c00022945040121740700920b0070103100011402e107814094061000c0d91148407000425800d0002044030002d078034400a056640245a40d4004441c100c1c0a9000711191214044040260840d0340d528080d80718040c40c043c4003c0c09440c01c15103041490035405001c80070007803040104102c41c44502c94040c5800941d98140480c00c030a503403a084036400f910b20030340d40207141ca03040046040c080c00005030044500a07200c05140023151030400291090510940000960551003880041d120b1401703086494030034100800c82d080e69400113800e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 351136636 1250 351135386 351135403
    0x507050403140102160201050f09030703030c02040c0f09091a130b1c0201050304021c0510050117210f040b0c03181905040e0c0d0b0402150a0905040903030e 69
    0x9001140074014080d0300402d418034024444000c40c81c100c2030b56128092001c84910180c14407002140e40110407c8100489045140040585014988070700d0007500744040c20106034002d601c0c00b85079196a42c010019031100c00c0d42c68403415400361a025070079015050b03624259407c1c3c4030686400a294231018000d0340c0302d0039030b070ba0041200010001800310b440c080350040c5034504940b001c40c60150740c0082c1203d0b0440d4045c0c0b03c80d8140f054403841c44000082c40b0700001c00700d10507120350002e240b903e43d10141c16603010484401c070030032141d407916039501c04120140c841003c0d00c2040d41c50901500c001055460030504005042540c2c40c00031400a804c524010f08280c2c1001a00343c961020303a82081854110440307200400014002808015201034083d06005a5403480c0c040341898041140340078924000300400e0f1740031032901e89278000c168161350490092802c0440d8805080040050f282400c406540342d100851412041002400c0040025400d0680d10544100c078110244500030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 351137886 1250 351136636 351136651
    0x705060412020f030f03010312030b0d1a010506070203030f2803151a0a0c03051e090907110d080c090d060b01090522091103060f0106030f090f0f05010f05 68
    0x3a1002071518064205204540f052003560020051100c003130580e40d05481c15260802c80e0075440400b80b0005400405240c035106a10400d000c01003400c00031039540c6400e200821600460042e640e420a020f0070740502003000750f0541081c0404c038550f1440b5005440340c1c1810561680704150440c031046030900302440710000098440c2d64040666010225810003841c0a5004402c2e1045003c02d0003200d001e80c4188004100c038005d4100189403143c416100143d00300015140324040e01c031707100043c503442455014062941705000820450040ca40040e1031540a4050144442d11030000c5881039030050031780030600c1081c8000e40b403a480706c0031120081807003800005140041100094420f2209500240c8a80b0b9444120001c1d0101c1c51080480507003103541c0814418014a012100254840328082d0548220300c100031042441e48403080c101c6171039440410004810280c8801551201a07018084440c05410140058000d14890000764054000003452000549203501510026103014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 351139136 1250 351137886 351137903
    0x60a0c0f111203180a05100c0318090605040501050a030305030f04080c010912020c090402150906041206050403120b2407140c01020d0c0b0606030613020715060b0c0601051507050604 80
    0x42c0c0c4d45241120014a452008442c8403410516240000c2d42d8086508803040130084018500d604242c01100505441d01c445801c070403100d602c503120440141650304c682c03480b403410680001254149410001c050741e0b01a61134510390b0752030800324108410040c0046038280c2d02004028000b1348c2c28850074801c3d81c0304140c404045a403912009103800c500ca6440791190b10300c070f0140720040e5168612401800340303640301036444d48841c0000481f90300595000d60108a4039110940c108841a8800c3c0c0c410b0344070703854004403c0700d01c0d1064011211410007440e040f1503882c07017610034442125000b80900080c1d07280390340f814405684440040c000b0f00e82e0a022540000404501c640c0c040c814078890480e0f40c6000c89200305280c44084031050b0280000d8010103000000c0381060712010100c0701d91510803801590b44890520700b800001c540f0030f4a4841c1c0a15000300400c0066107070003220307505410640201841c1c1d080c0402c100c02c000031165031003004101001300000003201400030b14400c9019143c0c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 351140386 1250 351139136 351139147
    0x9020403140303070e090603011409010c02060903210c1c0c08070e0a0e040507031a07120b03030703031a030d080105030105130302120a02070905150f060a0c0f111203 73
    0x1a0712000200d08040403160020700c00c004103036a1041241490020440f010a195114013020078011b1802040c02040303181604100403c1e120150400517609600c1d508a414985d1021742594583c040c03ca40340ca251005a4442e0040c201c0e00613011741c104158070f01280c81c2804800c507172117440c020007083d40b1030039480d422500c2c030540e00f08204580c4400c09007454902442d8541c0066074003c02c9005011407000c480010800380700e01042948069540040c240e40c0c5140c41f0491328407100b0341140d1401c0011444120041c4540031030242030940b54000d8011400c200f219a030540140440814001140000d8012029680d03010400d08800a030380303454040e1554101800d260a4590041100d00611010285040002c0e8005582c0b030052021140c4076446a2502c13000702e0412039642e00076981c10742020103021341d41c10707a11810140c01c94100c58400748100107400b440f203039000720010300c3c011442c0e9110750000304280c00540c180b802d10403240c10441649481c0000e10003019070504188a500c042203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 351141636 1250 351140386 351140393
    0x6030f18051f110d0f020c0604080d0501060923130612110607050a08070327080f070308030a0c02011b09050a0905010326070204050c0a09091107030f140409020403 72
    0x5411502801c446014800480d810740400c20390311134101c1903044a599002d4030071420703450382c0c1507810650311030003502c40354105401c0814440e0030140c8082c2c50207280400001c1d4280c040d8115078111480d11488685409601000030035450306007a2081d0018040b2816070307000c041d00c2c803031000076144881c0452445402e5042c031213000b00300304200c14001c0c501044101c0215000181c5503119590104d46680d8803500c62908461007180602e401c01c0800d5070340304c544500c0c00d120f2542d4003610420b50484a04d41044070704241d8990f421312001d00701a0040000c40c03010881604030b1003071201c5900000c5210030f181d403200e003400300b058001000014543c0714184440d26040f500c80004107000303402849594150f80301c52a0010400046122202d5000e400c10880d200d0401902c0100c0d400401c1009035182c00071080382d00380d12808940001441e0000041411400d512900d5040d2282c05a02c504140b102da0b0295828810000c0c86410f0140800354424409070040081015044201015072254554034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 351142886 1250 351141636 351141673
    0x2090118061812051009021302070f1103010b010f0f1803050312060607051005070e030a0c03020102010f0e0615031509010b0f040204050f040b0402211014060406030f1805 75
    0x1002240100f10104024003c41c500160071100100c4082002035009907910000b139000c0b09450342c9000b41030000c0f90b131030280507100504d0021540208032000398100004209422070707403012582c81c0402d40360b0483c850854441e049201d4140704a0038288040d0101041c1241006040e6200321016800092040c003251003c03110f05070851815541e0905000c81070b5a0b054450742c0212072010425075400002e0006441640000103c000141c16141a81c985042c054500e01343e6000c10b03400b56003003070b01e244090380c0300c0d03c1208000c4078090040c100907141d800002c1c03245810100025454031826811461480c2c1640c8041d00941d02c16000141c01814a401d00c050015082c0034981700c0d52060004100e10b03250040790001a040403200043c01140303040010300240100c0741600c400c1d40f0201c1482c3c6407201ca003500c05020b025100044500256240240384800ca00c10340b00b1703900000280300070813003980203401054030446916070103da40a00f500841100b101c01010035585e0703500400944400c07941c0f00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 351144136 1250 351142886 351142889
    0x120a1d0703020f0f01020d050c2407020601050603220203011d0d14040b040605031902030907030b010e0106020703030c05011812201c0c170408100e0c04020901180618 73
    0x680e000304d071120550380041e4a0321501c241c0601404000101802d403004144200450f401c0841441c0c444016000c14580c20729404450010152141500110b114980030041d01c0c40303011100e40207003a08c1c0a01503031b400035560000d0300700e8140d07407200904030003001003445c0144d071501a000141511b42d0311000c001c110090781140e07445180c504000900c58001460200c0c0e064804509110b6a2516003410108a203400103d13460b9100e80301006110741120089601021a40170f03250846086c0d17240e010002106000384240c40240c2d22680c41080000d000c0c00c8500003250180d800000c0b02c18110400d425411580c50f400c6529000e050210070590390007040124101d002048c080400300790710075072142e41e641d0304008070b074104014400c903551840c840c202ca2a81c40f42e00c800fa280042101c82003508198000f8004e04046004820546420240c24498007400c50740110081c0081406801440025801812140d0401403c220140c031240c0038140481c0c010300550781d4170310302c500c10034801400c01c1d24030703 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 351145386 1250 351144136 351144139
    0x60106080702060109110d0f02040f0b0906090d0f050a12031a0a0b0c1608010c0219110405040804030209070806040e01060b0301180b030a0c08150c120a1d0703020f 72
    0x80c081c0040142d000803414103440861000080d043d03140d000317400031409105600c520141c24840f0000d0040190b401a00464914840c10072080d51074803081c800d40d000300652660422402d00c07440702d81e880c0200c0404441c0740240111508995180ca40900b40b4050010940381d034003080c00000c841541c548905400d43c1c0c0c020351101c820000845c005039540b10707d4440d11004103400f01d4802c41010051103241da0340c880080c1c10048003030362114818064060a048280035014098a0905141400101a00c05a4840400c070400c41b04c1c1000c200041c807025100790303001142440007200685550542c03500402e21921104014907100c4100415501130180180490b41020410031031a2902015241580c0c180c50800010740103000000303004041c51441c190740b5204924141041c01b040642110689031600182d840301c08014803082059982520609a6580c0c03c10814462100e0540051340065120300049103403240c10040c481c0540c0010184482500012010000c520700030101200340d410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 351146636 1250 351145386 351145397
    0x15050604080a0f02120703140705270a0f061d09030f07031202090d080403050d180915030203010f021b0d0c0209100308030703020a020f0a05100216080309010e060106 73
    0x1050720700c40c1c07200303000c0000501000380442c5282c2155904c03245000b030081003030120340446989007800c0b203010107081c0b000901406110001f09180c20428101c078400c06101c54104110300100302110f9460780010201002955160307a14580240780f4050200140141914034603403d04d03404032022030764070180504800d45d004100288001d0400403da603000380c0c250501c640055200010308020f44544085c6d02e500203d00d864110401c801c507000b034001d90740681c085644241d04010305817807421070401c5440980502060401182200d60054000401036000c050081503996001c00e095401050640090340d4001c101c40203114500182d8803040140ca00040c43c00000380d02d009451000e5040300a8054010000040e80c41100322000c41d0056600903202552031600100060080d0002d0a120f40103000711490400d201c0400140c4447c1583c00c40c010740000c41540b440c40c8000e5002c00007010003031154103031080c0030030480000b85100e100c0c45e10001ca00d0400302c440301070034407a050304803200340135 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 351147886 1250 351146636 351146639
    0x30f081003031b02010e0301060f1511061303110f03030912040e04060905070b03070f0e0405040c050603090111040803040e011d0c090a031509050c0117040809010e060d15050604 78
    0x9500a4000304203d07030440100c202d08480d4001203460800d1100702c103405600b401400641c056035406144e0850301c1c03080455150664444c8101c82901049010503401e41c04800824440741e180c0c1c4600414500c02d04114503100c901e01c0603981408694100e242c240e070404002c000070580c0601402d035102580c40e81551400d414100d030b984903075030007800180107140d88515200c2001410401100a030901000164883c40c014400401e031a110742ca040c1e001810038117800b8802d0a0600a403801641c0c030801c020350403400c203c14003840303800c004d041c0021903403950313000401118518020005454280c000d9aa100d0420300c00701461081039000c00c00750305681e48004c0003030010300c055a4000c001c0c451580e580b1160035002031060034081d003000e80680c83d0344084200700040d039440180020311079000d541084000710019501889496030201034a107010740040c000074012002410080414107040d07000708400c001291302c5805c4a0500400c0b1070359078110b1a0300980181140004142c1101c4ca80e1619 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 351149136 1250 351147886 351147893
    0x10030606080a0e15010b072609040f2301050a15051801030906020a0503060306090615120109050f030d05060f06070209060a05090a090201110604030e2704030f081003 73
    0x10300188a40b42d003603a154030300b801d01c40e42402441111108a402c0c1c040c0f5584660804485501c1810101c6090091003900500303a11914140070300920740d040101c1c1803151040c1404050030000b41e038012040d40e00d4401404201110311007000143d841d4440c100e04c0d606060900081c6c11185e04890320000d03141c5001001c09a20604980c00e404103a07c0c5065604070410040e00940103014006000302d0000c80d000300c116500002440c4502c2c412403c40c5c0444d01e48410860b15800c2c00d07280710f020035a0081c00b18426041480c190346410f0242d80c0000303034007982a1903560411116070315a400907080000c003420b29882900506800c20303000c0300c50a8035845420001805071207840c400a000300140e41c0001c0f540e98486225078000c01019000302800e260011b40e00008144644049010a1408101c845010800038406104680c0b43c1c84061404c1d01200401080d5140c900c28444d10701020b000f1070b591b07050702c0004140034900c2600c450482031600d440141014800401c0d00801008194040012 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 351150386 1250 351149136 351149147
    0x2130b041413051618030611030601031d030d09050705040f0b0a080d020c13020910020c1e09061909090c060f050c060a0506030f0111070308060111060121060903090510030606 77
    0x4204d5400c00720205068408183ea002e05aa07002600d11890079110140700c00f150401144100303400d980801c400c4690881503e1711040c1c600c80004541d20520404003901c2c1c0c1c5030720072683c0901410441c0c0a0a5841e80000d0030f65204524410155132503103405101c0e414040031001c050a8500e0140c40d1111074040020358490386005103e00c43c00a10341703c020707041070b20780c120b5022103c054064001c3c0114100081c0d0b0300c5014440b100e004042190120600c01400d015140340b2002c010600c01c0140c41c1c0e00100103280c10403198a0780c1c02c3c00741c04000075403202c8911615110714810304104182c945005000341c0012126132a0000f40141004a0000c0c42000300c0c2c201d03440322007000000b540b511403002007441c00100c800030001a600c7c2c400080540360301039020b00620f07072007640d805265643e100300449002400218054031648240010b1154080030b020f018100d18031040d100c14089519190300703058504c1000298081045107406100d1810544421079460b44941010301c601860b16100605 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 351151636 1250 351150386 351150421
    0xa0e0f03070c1d0c0a0c1a010509180a170c0613060c05030402010c2012030c0606041b0807021011070203010e01020906180f09071d0301060b030a02130b04141305 71
    0x1c2c21034001032000b80e150088404868098000c41c0790701450340080c1f985034591001707004881c0f0480c0c682001a0403424140c0803400004e0000014107800c685664980320404402c8146441c080014845600384c40e600700b18651040f90804001ca1718000b99050101c121070f005044801001020410031015136002450070131001c0e400104030b8a05ca40060818141c0d2403a4281e40f1340c00301d80400a03000e2404004050000010108140c9505407120410041100c90b802c007442c0050400c0180880f2544c091000250f1180c0e0710b0064403a040558035281040314400c944000c0d030000081210340550400b4030442d05c030310100d58001c41c45c061031030002900c107011b5071400220711902074100446a072216070b1181420600508008914240801d0182c41d1140060302000b4480f1030400e446054034050041c1c400300c9921072105859525000001e8002c0d50118501c11444c104190002910a140c00000e100900c05440611640050171041101a140c0c13400542e40300c6040c981403202c03688100b021100d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 351152886 1250 351151636 351151651
    0x1101050306100516080a03020a020105102d0f061115010b0f09010e120102030939060910111501030b0606070302100c2f150a0e0f03070c1d 61
    0x90302c40c2c06000e160413008200304030084c8200c6000c00d40d440343c507403d900582001010350300240103560b504105c40800c00c0300e91040c683c6824a064002e03140c5d030b102004074159419003140f120440e0707896100c81d40315441158021400202121044400c9030341c24000751a244425500c58880d5500d400d403034101368025014203510310342c4002455a4280e0103904100e40c0d401014041200e000441c8110340e00075002107a00000c0303401408080e20b00c182203845501c000c40c43c00147c0c18202c00e44090313801c0d02d03003140c040550380000080050464641d508031358000c1e9040291303203c020b20055000c0d000d0521282080600d68000301c0001440081d042e89411070b807080043d44c2150302c81055050481ca8000800900c050107460013007410859503004507a15200f204001030a68041074102c844800344408030700741c04480e0007481c0a41203c104040090343c006800103400b0034040c0440002604000681000c6881940000b441030200a0032486800080c0403401c0096040492850300c1c01500304c0090402 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 351154136 1250 351152886 351152897
    0xf1a0f1b090a030203150a3603210509071a0708070302010204180509070509060d030c05161805010b070f030305041b06021506120c1c050609060103110105030610 71
    0x11250b264920840700550700181100d480e2041c0c0d030f0307070255170040a4070200303501c03401c1202941d10b1150421404042000304814904681041ca40140d039408171040114100700e100c2e40140c036100440c440c03032020110100b10006560801d11039007450100c1c95800454050f40440c100c03001602c0200917581d84540020138540e80f807165250880c0248901c2d0829071424885103400a5030074031700e41c4000d22400204044800349032325442004075602c81207803602c0c2c4c81400c0d010b1110019100300207140804cc440c0c01100d0404001070084502528190821500c0c000329484072040d0303041d94011940140001030f0024500001a102c1d40000c400010014003459202d0700030030b041014010110700050300b807030740c5008003a0b00c0d00c5000b0340700d0006122070301c5c1c0c1e542d090021511510707004c51080e10fa03840c45c0d001003240c1240903050080031160242c1c0030800141f070113000f2005c2901480303040d01c41c26110000d440a50705524042d9041d40c20b20488504000d0180100300d201e4450381005541c2090031b0922 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 351155386 1250 351154136 351154147
    0x303150a0513021c02030403020714090f06100908011a04060b03040f0803070c0602040b03041109010f090c0e030d0201050906180318060c0a060b040e0a02150f04030f1a0f1b 76
    0x4c143c0003030030004404205078800401c00003455030110703641068031408088210600281c0e010840581d07030070b90301d03400d00780306070408211946420100500f1a0f14581040304000d41d440030010308440d480e03c0c144c0155510101d40856901d03080c440c020140860300c40d01415402c00f61a020900f5001400c0100024400404104200e000d81c0c816603509a015005550350741d19606102d12a8200f524121580100c0040303030441460000710f001c4c1030b00c820340c598600766850000480b001e40366559480c01403000c0340c140d110341900d0920900022180d9074001044900b008801185403803002049070680b01e43c890040c4102985c040708451a0052400141568440441c0011018407031215006010721075540700c4000c102c4070740c100c000031103000c50301080b0150708041e40360b403284402e403002944411086081d00032109400c1c007a24410b540c0308581400c10b6180e64540c50400d00c40e075420b1f03078840c44007101001c000c0c802701700c400da02c02c03181140d040c2507040200d401d014805141072070311143c0101081 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 351156636 1250 351155386 351155407
    0x307060225050304090e0613030503060a090504061515020304030b0601110102030403020c01021605030703080313081605121207080403030f0f0506120303130f0618050303150a051302 80
    0x28001d100c00456100d007100d600c6607207005940d9030300c240b082601150070450400c868081c0840c4a0f441178132601940c0301d00620907a001c803401c1d030000b8801513001c0707542d070000320780c0b00c3c5648245885103214840004005804180c4040c55201e540d00c2102d1b411902040e854102d84c3c00f006075030880707901031012503d0b500c1d654010b94000d02d140120858941c8084100000d050307000410038980c0300b00ba000c1e29194003014040b800800e0507409215010b0780318403c10000103685c04000c50303000701007c801d038550340c40e03640c1d420b00203a01c803891418ac01868009a4018450b0a1003000104490090305914011499600b0308120800408000a11070208000b13814075000e5003082c80b0000c1085400c01c0350030901a40301006201c01c1d5030300d40c006d26610f204005004800402c4901440510701c5107164051030703607504501003980e403008640154895192205032090090003a0003a1b201d20003940d05c0c0c0c0b400e0500040c1070944c0740c445134855641107400700b2030760300d9141e0b040003916134512015960308040328 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 351157886 1250 351156636 351156667
    0x604090f09020409060c18050114090a0b07030c053315030d0f0e04110417010b040207081b06070801050112140423010b0f10030b03011a030705030f03070602 69
    0x581c080d4100742014280c031308200d500c0e80080c000301c409403207440c42425103d84030703500d1601c140a40da000c914103180808100644601070400c03001c2c0100f865600c00e41302c0341000352940025500f2404610480944e03002c00c00705110600d1303800d804010081850300c07504151070811800601c030914840c076500110769440449000d540071208040c00f1102c1d60507400c440204002018240c840006922805411451400d4060401a00c070f441282c18205030070f08104580d03110140c981c1441e25075841d86c407107400d034070f40e8000350000c14059289151106403a08500708405032540c0b5551090708484200286a42c11444580c10344100303103001c00790000d24200b900001c2420b203a000003101008801c00040003ca07240418088000d01c504016203e9036512240c00d0382c14910605500408600301c0d040581041190042c4000c0e481c0b03070214070500e078500403a084a81180103a40490301e9281602c604e03003030411000005180c00e4004044241c1d02c08455503c0740505d0314000d02c0380b5000035182e0703c10800c64 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 351159136 1250 351157886 351157901
    0x8071103010906110a0207050609030c1005040305060103200d050d030c09031707020f03031e0d24150c0308010902090f03070b070b010e070e040507050f0d0204080105060f0604090f 79
    0xc034100544c2c040082d08042c15000241d603200148220341000c81c41d414080192007411201500174002c0c060355104103d03014808840c000200302d0180800000704404200440c0254011103141384003001800c0403007503400c00c0101081c09052130042c400001100024008160221450b00045121502208980354400c0ba0720240c00d00b40c032400d2854420003010020055940708030780c41c00016005105054980c000c40c40702d54070102c00c40a89140520300304000780440440c0303000014684040500c6426407021400096220802d0170b04c0600c08140105070740c0003c0e4625003411038000c3c04550307006000510500403c0040c0c1c0d0045101440c03502c4e003108130007200d0070003003da9541548804510f801c1c0e42281c0001da4110b02d5000c000a035a204038034100b03000b02c581c2d58901640000c004c0a00014000c00b6080004211007081690000d81d50f00014041c1c03460100000b6a6951400459500b941d20181c03906110b800710080c00d41e40c40c0d6420044070102d4440c030700c010a044401694500040884 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 351160386 1250 351159136 351159143
    0x411040e030f0d05060a030c0303030e0c0d060e0c061306031515020a290601270b04030c080c10110705030105101d01030201200f03040303051b010504080711030109 72
    0x1041070701c2c20030042e034040d20310280c01282c03c00460307a518003004000b0386140b0010f05040380e10141440030a1080d0001d07080381600304100c4420989201c042600480132000c00d89002c0d545d183e109515a00600185107051000c8130141e081410f0031008038655501881070b541415550f60b03503d40c5001740340c1c00100040c4600320324604148144034021f515104c01d010110380f2030105a1905a900e0300c011000503840307420480907400b83c1d0394940150ba942d46501458146c0d00d00408400d107050139076282041c0a81120b03070140f511585549000c030510821a000752845070400ca03443c17111a240c1d141c6580441070a46400040c1e021048081403c0c01c4580d004030317405509040c20000880a18024002211003000d85030078110b002100443e40e000f0203000003030000c1e2044041014443c90110301344c9420503d102954581840d03c0015807840e0b2059108401150010440482d00d03510002400e10740b081c2240240103629056560381030303600c00c03900010403101310700b6041a1640c60951040344116030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 351161636 1250 351160386 351160393
    0x20304031808070f06030209040209090403050901020c060909040b0c0c071215090507090f02040e0112120809030403080703050903030a02100c02070302150a03110d05090c09010e0411040e 82
    0x102400e004007070038030400301d0928520010800090029001404104448020000c1e158190030880100c01940c411440c0a86c0130341c00b0301030100c0030b0380d883c160180034a1081d01c44c2640c4046000029040000e400c0c1c0c1c841c0f003030605100101c1591203c00c0810340c000d1340074504203081c0e590f000c0f01c000c0d140524140074071a44243c05020500103a05500b6814450194010301c0c507100000758034009a030300e1210000c0841e0041c5200b0000000981c00010b06100c80d03400c05414140c8a0000c00c5600b0f009a02001c0310800c0d040e400400d201032403c1b062803025480c038003000c582c03820720300d1180c0e24411480010180e0070f00117280c0091610850540b40c00030802000d91380e0b40c2502400c001e40c9e07230521a02150072280303001d408003201400010188200d9501601c040404400010300103d207402039000c00c03044c90f40714030743d0048101c0c601c002803182110300000000d007401d0038882c4a25001500d02c07180e0054008400600800384140041035106034841c00e030b0303000c0e0204400810090403400c00c40044920 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 351162886 1250 351161636 351161641
    0x70906060929130603140c04061b14010c020c0a050d031b0c0e090307030201060803180d08090901180c0801030201080f0601021204180f110a0c0309050a0b0c06090109081b100203 78
    0x298960031a00300d0401071b8030828401d84452200e090329110b14447c01c0081501d00c0401d00d010801108000340380c5000b40440480e0340d000d40318080c00c0d07840560501c00181c00c1186c03210500d05d01129200080c003070035a05c102250b011903801501e00c4540000c40800240051a600200b10310f07620002d000d040607101171602e50a05c011070554070307009680d046016500348180801c4e030045c00400e4800c0700e6500f40f29035411800748024408466103032481503501600030007640406480702c0d01d03401d00900d03114a0503072140c15020411800c0380d50b0100c6031402c00c8601c0d0010000350f070380000a103422402c41c610501442c1c0b0707503c005071702e00a1440480781e1804004034000410112509800301c03012034800c0144030100c5126014802c640c190291000001408d001807000540700720901c081d403510904059140030340310780020302000c60a0380404030440c00090340d03139807000040c002e60f90400f0303209c0001d01201407940c5d2307411a903000d1080c0071102030240b1452024101d604002d00d11311442d10079021550f0f170 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 351164136 1250 351162886 351162899
    0x501140f13060305090c0910140a0f0806041a1b0306031c030218011b06052809110f010c170d0e0307030905030d08010b2a07090606092913 61
    0x1d010803280c4182c071b405884400b100c3d40c2170003102d0700e214840d40d9285c5840c041c00c098994800c80c01c1840155080103803101c1c04103480300000c90341009482504001c2c1a14545403914140042e000751000103c001c0c642c0622001e00025480c1904041101002d2601c136178584c008245401c0fa070030452802640303086018814290107074002c02400340040444441413564400556140d86000100d0504940a10802000c01c5440d48040d4200184c8104203828a0043c1c00040d0000700c0038581c410181d80d5020300300c04002860000e0540d5000c00d80e00b59009444860029215402e140c0c00a0b0403841d00f614642c8050110104440f40000e408108110500c00d100c50700d9945d404c602400c402145002802082c4c51a0001d00c0d05420006d42e0342c0e640d06a820a1418125904480400d850312403070341f0f280720860084040200c041d09101f20040010724a404254415500168420800c3c040310007014000d402d40d0010142181010f660a1405040b180000381f40b14030030004070450038070f201400483c22 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 351165386 1250 351164136 351164141
    0x11070b1003032003070b130b090c0103061a090409050313060504030606060509030d0f03062c010911070b060312070b09100510140109090507030e010e03040501140f130603 75
    0x1e6a02998924007410140202002d03003c4580c5801d482c0ca9100b40030100026600710843c0b81e2050903085c2106a1191964030030640c0c0200303407914815034001c0c210340c445a5034184220802007002c0c2c5209591000b03c010340a07a54400c1d050b105020700e840c0c1c0d080c0f40074080100215030159801121000c6801d0380c1f00c200900701e403c1400f084555905200c00080d03010301c944207907030741c1240c01070181125a100180580d401440800c403541496154000020f1007000315421141a8451049100144e0b40d0310b6212502900144c2214812502c0c03c10280408034102066a035410b5100c800d41c074558641d140020b1030124072181c808001840017500c181003054800e903503401108100110b41c00c00300c0221180c01a500100c81c12108800d50074403c1017082c40810601500c1b030b03818180030300004d07298520281034582c222000c5010903100c660ba110a80c10034400d01241c6a6500d0145042c2030600e00002c22900b030910030220344e0003020800201558080044544405088001d4902540d445202402 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 351166636 1250 351165386 351165389
    0x15060a12030c140f100605090105060c0111030403120f051b220b130f05090604110702090906070e0102151b0d0603210c0f030807020102070503041419060e010311070b10 74
    0x4e1500610b41541e82c010064002d540c284d40b001868406c20742c0c05c000030301029030403100d0402d03030301d64a400c080c890340d1076200000c500882c084d541d80c0000c9401d2000300d40c180e810640129a20520300b01c20490516041a44112001550f0182d5555014a4035801c0c10282220b046201007a40c40100056010308220041441d482841c0e611403104d0741d108441e29011103d80310306a040341241d00054464645036121281c94a4803114141c01d00703545402094001c0c001716003100c990341c041c0e018000015004a00c032140b44001344010300c80c11094482142c06194042e1242e0450080650000312888201007501e003c00726043c42001100e9507420160340000a500501d100071200784041c80020384034a081c610b80d02d410481d910220080c550b01122000001002401155400e1011800240080c00280000d0421800c84c10b0a0b00034101009a84500000440316244040138100203032a04070110f096121024200003032a03643d80c040b20700803481140001804240c40f8004c0000100000d4504030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 351167886 1250 351166636 351166663
    0x110f031f0f1506020d020718020912060703051801110919030f0c0e07050c0d0f091d01051302070c1a04120b0901050a0e0a0b10080109030f0215060a12030c14 69
    0x540c0e00038503170010307600d50f00d0314025100500e0020f84082451030241d0010142070300060070442e644611006c81038244041920f400000940b61014880418111110b0078946039140d4020441801440c0e01e200051044010840c01a441c00c05004500081110070f1002941c0082d0060b5140c41c0600d003200d00000e19000b40404038050b60041007a140c421425a1500803092000f4604d024000b002070f15203c9035841d02408010f0b9000c80070600c0340382c01d45501240c109201ca981b045504080400104500e04010190064410f20911000c648180386010885540c1030401d00c8001c29062158458481d0340c00c07801d1101c03000b0f43c1010812a02e010000d104110b0203008001a484404003001601c0345281030b048658040c28160020658034080c0941041c0c0000104504640d0b0709c0c0040c0c2950724245040c0c0c0800e00d035201d401c40681d0140105000001d1307041541e542d510304100000e036440824018001095500100442014020785295000540215402c09107040c0343d0700d10307503030b6641e1001e009 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 351169136 1250 351167886 351167893
    0x2a0b04030908060c03010504020d2403050105010b03060a030b04030302070803240111060c0f04120309030210081b18090103140705040e03120606070b070804110f031f0f150602 77
    0xd0b0424003007202800788100c4814180703076919010811020750801b10800003200d40d1010140c80c60006000101049600c40c0050a5118510308080c0e08403030f0160701150002d02c00b0002c110003070340c40c50881e2058990091034500f240e155820210000d01620380010580c100000034082101d480f0a01401540c00703850540200708001740044501e80c8201c170911800741e00c4100440c1041412038041d0544041511046003420f50350b100202641501c454250045005960240294208450b0400c0500c0b01c606245d6038905080300c0f00c034030560a08600c130064840c0800c0c10004844a509840c070000d100400ea404656142e08100c003100030340d180090340303500c50610001b40034240b50060003200c2c0b440d00091820200c2e04180601c001100400451f8030a42c1013058800040500d46040d00900b5a5542d070440c40c501490030060040910210310301c9000450fa038072180746e500041c41c0b22a074603003294035004032040507448030152100d9078549a645040c26000c03076143c26902c13200030031a0015401c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 351170386 1250 351169136 351169139
    0x2070902040b04260604060218060d23040c030b0a0f0f06090c0c03020c0d03021c02010509010c031116060204171f02120106080415020406020a030905060a0f2a0b040309 74
    0x1d40d80e130440c4030010307074825040880058045290b60b4007419001c002600304103031401e180c0000803c1a0322020a003401e035a41c03041384200d00760325144840700c9540c00008548050410703443c0c0c20304550342480028640c40c442c82c0040c000c591580c12540024080140500c038040340a004180070b0012400f6841d0709134904400301c0300462050030b00c2d001658140d000303440384462041c18881548030101e42503095214000762503035604903211500d00307980f00355400000d460038130403e540d0030345440c00728000c2014142801c214840c2030020441c2c6071040d02c40028040301ca80c1d890200007901881d0b1107001007007610000c450b500b46001c100040741c00c41c80d075900e1035420700b000010802c034010500440c00c000088001884070318058078286801c60300a00429104540c0e21601d42c041e40d202e600400016084048010b04154201c032000020704411140c49040024035400240b0400c14403844808118035080580240d1480141c5018500c2c0509001940c19007075082c64518072009440450000381d01960 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 351171636 1250 351170386 351170429
    0x305090310110f07050f030c0709110310090203061917060c070f080313150605010806010306061d010c050a2307050904030806031006080705010909060f05040c02070902040b04 77
    0x34884a0750122105604101101c4072002e03958010603c11203007480744c8510804070074800c0014100c1a09000d004009040c109030101094408bea10203001d030850038418400c905606014502c10340707441000040e01e035540c1900203400030303804170f140c80c990050030400400d46003d840c00030035000501000722041c54681d2003002c003441c0b040e000090029510780d03074080000380100c0c00568100f100341b003855840010b00d8440712200b400710700d0303222a4a41d440f8803c2006507040b140448d1b0200d42400e041240321720307102028000105520050803108024405004141e00807800718501d15041070490b2502600751400000300e0707252a61642c4880300d6040240c0340310200196400585401601f4aa142d0f01c455a003940c10442c0544690b5050190740c00012045c2c3c50b604c0b4a400400e10b540007841460f150000241c24204180c203c680180d08084040c841030500d00c032480c040b00e609681c00515501240342c02ca05103e02504200c04460000400050b1002c0d80d00241058820755904040311605004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 351172886 1250 351171636 351171641
    0xa0c03230613021504030605100603050108011407030c05041d1503030a170c0408060a051501020f1509070b0a0c0314091003090203010e100e0105090a0b040b0702190305090310 77
    0xc1e05200305040b01200040142003071480c1c0f0070340c074850b01c090604054890f03a4100031380320203d610351128040f08004101e415850300455005007403220003000000d800703444000091000914500501d900d030144003104a1180b002ca8000300070302503101112003100c018030a9070036405e460644144200c251132551a140c0802180c4c0303800210307100c1981c1b450007408907107640c17400105465900c5009010010f00c0d88803d11031030b4850301c040e003400038072840d2514000b40c00314104150a81154040700050a08080014021650b10b006840a6955540d020305092a020640c1c014244801c8045400410a50020034030410584603032100a0080310501200c0118020402c072282d02901280c1e61040050007540114000c2c0d0020300042418500b07101942e15110021500c0c1441039550a101c0c070784040c1c20b01c505500454404083c10740342d901c1c0e448600c00340c1d00217400605010320020200781c8850003005804407880301c4a039a80d0010b031a604018180b50440340c4018080d000e03e41000d06505000d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 351174136 1250 351172886 351172891
    0xa0507050405131e021909060306050609060c0a02030114101d010501030903020c0a08030a110111030105061c06031101030f0c2f07120c080c130e0a0c032306 69
    0x1c0d05501803a0f5200180102030300518481c90305400d000058a1504150350009190000a080001d00c1200c1d08590043c2070701020b80c850b9040515200050206a50310003c0350b07400d08045400340c2d21454100003080c2041100c5c3d900035130641c0ba00350680b0f08401d887c95800e00c41c1656614034460302d99244200b607401300e40d1201814204c2882d1f4014031196001354491a20907000348100c4151840e58008207005851a8112200719800459011805540031100800e5880e880c0e0081c00611043c095100d00e034001801081d11605002c546180080105400703038803405101a0705020b52075503414103140c40200e002401c2d00007401c080045100c0f100c10b01070401c42d4002951109138040b250380d00180440d50317840700c0c2040c850040140c03130344d003000802849014003409618028030f00d00c00e00d420300303030360315a039100d040345420030301d5180515640d0540ca1030142170008004501c14404900441c244a400040288000c1500c4800f0007880011071071342001c0c903440c2ca000001044038140055940004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 351175386 1250 351174136 351174139
    0x3020108070302340c060801050a0650030105040b0303030f0403140c06010e010906081c0305060607140105040606050d1509030e0d110117060d240e03030a0507050405 73
    0x1410f00e06541c000010700744c20700c000c440c4c51610b0260311441e6561182c4003600e5201800080300240180018508082c04c08010072070707400c240ca400c602a8a003040d05118180c1c16286e18006420349854048642c21001b80e0300c07150210340500e618419040303441c83e0b08280a03107406189001050b400718180002220f01465070303403481d419a5a11564210740e43d4482050302c52030440c0a101744200301100300100c1d0702030806d804002040c0c0d07040048440854049900502c1641d10420b40b03580000c0d120442241588031515020803169111004540303c3d101c1c0400042005c508680c4079280c072074041d4011801140f21740300a00819a0b99020807000419030b1001130701e0905910740c4082c0101f06540322106103842070070100345c00241c850000d43c4079000e4100980f414501041d40350061740e403000c440c1d100107800440f030403000d041080100f894400070381070041c071143c400c26007211007154420b001e04813000080000e2107024010032045850342c1050317034040711890404001c15405030142c1c0645082d500c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 351176636 1250 351175386 351175417
    0x1c1a0103050606100201110a020714010306150507020604230f04061a0c01060f0806010914070f1805040f150b03090309010c030c150603030e0415180b061303020108070302 75
    0x20f40700d040104241503158024250743d038520f007486064546001070400070035250090704000345000c13400d200425400850604251401c40140301c09030000b01c0e004800806031400981b90100d03480460b9040c81150031070a08021100d0050b00102d1001d0032441d0004800e4405104841810040c04195030b407034056151544c1100d00c42c601d0b1207054030003810000709000c0011407225130340e881d00c031034600c0702e900000500c3c3c00c04401400441540d0003554940030511740802510300e022400240400030540b1103400300305807103219840074900408100054080104100b02c40300700d005804004042d00f2100f84010116203500081080380c10013640e01c1400c01c4c40166192010580c0111184003040d8404c0302401400079485020a00d006401c840c0c01c6551500010f0460840c00c6c064400c058001d0500d118506104c50954051074209000c811101404041020b42b0140e00c41d10002e04038810741d0301d030485804189a100006107000300f000f103e00070707210540240c413241022403c1c0c0c862041042581a07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 351177886 1250 351176636 351176641
    0x1e1201090c090b0a0e040b091605090705030603030705061021050a0b100e150a050937020c07060305070504060903200303120601081e0a02030c07021c1a01030506 71
    0x246035000b1805583d03000380001000e0742c1341c90000c00c1d4520162015201080a981080340c0b4000c1001500b1015892500071408140b40074001111144010102c0003040720100108003192170800a0329000b586c03080c01d030f519500d401008549078030307042d10500c624500c9500c10a2101550701715001e0302660000d014201e41d50181d1100301c4803c6000d03000e080ca0700ca2810b40050b0080c5c80d0040c00340103100c00c0b10740d0142d009800040280009080d0450f81c40b03a540002070003600307003800d181c1e0b0000b044020034165104400c413038030600401050031a0a10740b0300016503840020000304041080c2e4059840410264441100c1112280290b006103404036580300380c10700115040311594989044892f8000385090107901c00f0908580001014200801c1c9000c2400515a002024154492825074a64040241004080001010180c5080100e640c00008101000901400c1360321031340e0050020349a84250304081d110010f00004142c0d10f0810752560b003402307403510300741d464100c82e080402401c258 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 351179136 1250 351177886 351177899
    0x91d010207141c120506010e03030409051504020901020c041a1c0c0e060a031709100302070b0105030f0a02040f0e07060503220c05060a200a0302010e010c05070f0807021e1201090c 79
    0x504006d01483c1c1070100d002103c410340d07038041004201512403194040742c0d90500e1228947c45414041c010351142c0d0050000c0c9420340d030700045181540c0801c0343c002c20300740824081c0143d0b940580f0343c0c0b00c1c2c001c001840c9403000014450b031962a0107114801310440c007640d40d4104061000150b07600c41c0c2c00a41c0f800c0030070103d21802c23081003564001603003d602d009c5070300b80040c41081218400e103001c25004501c3c882440720341c000040c0107000c1507001d00401a10500c04075158040c0d0800240708541c0c814104c80c2d804500c0d0300c410054629402181e168a884110141a0b90411200740320721560071003030b4141401d0b804401761059580b08004a80d901e00b00750420049801511040341001031203203041d030780c00d2480c00c1003041c0c1c03000000c0035059881190400900351000709010500a80c100540080a80c0d4001e0031600090b07001005c01030120100d00c1c05115500c21090040e50203c8400315403801c101c1c100c141c5482001e0216080d240010082204034240d400d002d502511400c15401c0c01c0000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 351180386 1250 351179136 351179141
    0x10c080f07031b030f150803090105160807051f0603080715390504030c05120709020c0102281715030a06020c0d0503010f091d010207141c12 62
    0x481074505012a031491101c0c51941e810414042e80000252034421450040c2894441c0304507010040b0070440c10b60f410403840ea40d581c0320704c0b01c08604015002481401d030001d005c0040d0549580700050030764820140c103005944400041c0e00b90740d501e100785c002e88100c05e140e01c60101120f6020ac40b1504181c00c1d81c48009209003088400c0810135140c04903134000c1094040501c54103101e000d4032504000586c8840381c07081c61415144018020200400e0020071100300006044440481d0341100800c005400181050016809100311500106143d403030200b040d009050040302004c1c4c20303000e0340340c5480307035000d140742c4210484085200046001400c050341c038040b90f40310b210505919070341c00d001008039181c9a043c0c1801c0d10840ea0202c0e5103501058280130343d102c1001149407050455051041d02a181e01c450301c2603001643d51000d80252030f5410b00385000c2d01c05c0408000b1034030783d04141010203840042540407005401ba4038402c03001404107075580000903916640e4858030381c0950510100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 351181636 1250 351180386 351180391
    0xb07080720150709050306130204090f083403081810021305030105072a0c08010e1e0309010e060c061f0f06080c0a0e120109030e03010c080f 62
    0x1003007070880c0d050120900e000702140c10301050000030400c964241c2c042050045024210100304420038600f080255000242d0581140004082608000540c4005801003803040340007010350012050410502030400082c04036a01c5002e8280740d8401d015561240b41811002c4038120344007107485a1010038070841c206e1350300940192800d0980c0c40c48004027840d0102c0074400c4080c60386c0028238500000c56402008004103000d400034001340c24040c0c0702404007a02407010301d000c80103c1c00380e46070b044011000078a1098019403201d00060310b401c90b0078041d0880b110400d02c00e11a4183c0d103009000d0b501c0e01d00310126030345000340d0700305007801c801100c48807084201a0703030055040c8544e0003011020702c41c1900840854560140c14411543c2d010307420611070f80141d258445040b41001940d41290303032150b00640740041140d42d20200c0d441621020f400c002d1450300501c501c803a0712442e080540c1301414481c06601c0c3c00e080d616140d42054207030f4511050010001d1000f00104071440546580c0700e8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 351182886 1250 351181636 351181651
    0x402070c030f0213051807090e120a020718060806061e040207020310020d0c08010b0901020a1101120f0c17060a050918030304060b27070807030e0f060f10030b0708 72
    0x13000741500744c104c401d6507016280700980190141c0c10348004d50082119031300928900c48c00340881400781c610142c070341c842d5141c4401e2601c0c0000b254a070031031092080c07201500b561100d58428841403a80d0100a0035a8041c1540912034100414041c0c0b800324231411001c40d0101500e60003034400018030029401c003103012601445650655007032441c050024003a0360031200070005040d880d03003170014200001a44808601501001304a410340d90200e02c0c050f205070026900d200c00804040102c0d85c040a50010620451901c204078880c085a6088144e025205540f42c1070f402c1c103e480c46203811002034034030951110030043d040240d030505080059020090051340000c441521a10508580c0203c4041314182c0d9501800c1c2601d144c203443c1c480400e905802d13440c8520a00c4100e14502200207082a010300c120600000d00d040c4c401c0d0000c5a8440d00c030816140207681310404160391301ca0903500e4140030100000002d0320b540ba40c00c450b10403250020340c0c2061640322a40141c40745140500341d030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 351184136 1250 351182886 351182899
    0x31308090f0604030b1e0f0f1003081605010c050c03090d061401080703060c030203060d0201030b0f12010204050406240c0812010e09060c0a09170106320402070c030f02 74
    0x50455039601c0c030140c80207600510000c07043c0d250509155184040392101003004064442c1400003c81c101c0c1f01c0f0f2a03014484140d044000e481d01c5542400605040e800184192000501c0c01c1030700035241a4404064170036402403051030402442a0740074000c84912000d5980b00b4046440d0034034242916400c1310b80500e00010714585038808880512000740c00c41040c80d80f040b501002000640e00c100b012140f000e00c0c0071030a5060a00000340302e911140c2c400ba04251303c442440401e5600c42048442c441c2c4002e103c90540900748412a010350042d1207128402c528003000059240d4252041c115581003001000d00a100300050540d1032082255041d180140c05002504003282c2c20000540a0243c601c03030403045207071070320349246004402407600308a802c040c0003850055400454040558802556039079204650181950040255030320085035a20380b01281140b070818810022040c00f058121010401ca4103000d0200f80e12950000400840400710200041140301181003403c0744000c1c040c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 351185386 1250 351184136 351184159
    0x714060c0f072d05160e01090506011707030b280611250509060d0506071b2a090504122106080106050414010b03011412010509030d050c03130809 64
    0x60143c08050b000040204000342c0c1800380074441d0410400c0d144d01c0003020140c542600700a141752402c001845801489601e81e004212030341c0c001c00d14007204040d0401c0703400c40d5141541c801170141510011450080708080c164154141d02112503011041080d0480840a80340031012104480d0040c00b420403405600d1041c0045901e01000b2041341d0300348182500458145020030603c600c010701510300c90203440980c1000510089403c0e94450b249041015455000207041d0420a0b0742e54801064108030302c13820f03442041d00a007034101a04d121a203201115407220344070400c4500544010702071400c0503850113001d5101d1403801000b0140c030005084003040810f0702900340c03046c58002281d5651288418085418980f10b003507001c1e0000c22002d40103516007040890184810301821210075134aa00b55a2075498a0440d0003211070700700001c10092410404003078a070b8210148400740c1d2070411003c1400800c0070001d40f07008030104143c41c50f03c03000315610b001c0903601c024040741d0080b18450300d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 351186636 1250 351185386 351185423
    0x5150a0809070315060e06041506141b07090c0212030109090807140601051212071502040806040b070206100305150402010306090f0504020f1813020f040c03020714060c0f07 76
    0x4030000b080040b13107000c0354007428030030700401e09140180020b01640c40c0074444940111001c0c5644200c500a08188522003040310f5500700300d22403c940d00700d102200404000030b010001501c3c6045441c003110400950400d00012138a900c1e6900d01d82c00200810710044c0190b140c9903220302017003031148100518010142c1c0e00d000d001500e88040c9140ca4108000400c100d047c01002118000300c0301010380001e20540c0c078505828011074601411603100317401807103940001c40d4101d502401920084035451302c0d003443e180e42600c80443c7e01d60b0050203080c021a01d030903064080c44098a500401516020701c6041201c6a0342400400c02c1c1d04150704d585002804402c684030300c0509211880012030186400d006002c400752580444901541c1c4480003514103d10600a40c2d400094101c1c0b4001c07001600d00000d41803070a00070030f0a40c82480c100d0100b0318950980c0c011f0207214468800b815a41440303040e10758494008452022082c4001c02c00c00b8403000380780f4003c1203031510440004180745131601 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 351187886 1250 351186636 351186653
    0x902090c0307090f230301110c0f101104050409060b040c0e032109060f0c12073302070302070915051207050a1205010b101805150a08090703 62
    0x44904403031080000c02e004209a21410503006004e130301d40c1080505140c00c40c852048003900920041a40c0d14a0300701e40250707000e4110781c001c420040c03082d58456919024440e1240d21007000b038141440f44001040c0307600f001e402403070709008486d04414205403801040c40060020000e08407401c07550b80d481000303566a144254003000f099a902c00f01307207829202c140b502c0d000e4680d4101241c00c150000c0c10181e03202c0081100c900c0281a680b468a40d09a601400130303e009803000f03545503008040b000f800303c812400140100c3d03801020004510303e5101e21041c04014180e2030807000c0100280c1c1c0c2580c0ea984c03a001001514131a104036082c041d0b640c94a18200c40895180c20025140300c8000c100714541000048196107896026007221882c100002d000d1000e18445d00701400185400502881420351184c03201d40300181c4200c01303480240000900d04c0c000060f1034424241d08003404200f034203151210010014100310400d1410215440590f0b80c0500100843c546110700d0b007001c0700003448107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 351189136 1250 351187886 351187891
    0xa0f0510061101091e0c030804080309150c0703030509011106101d070c0b060a03060e07030201031113050f1203070b062d0103050c0f130302100c03050304060f090209 73
    0x800c4140301590404500a11002900c180907003141e050007103001c045030140201484200000c24816001100c1d031800142c0e0001e0b07a48040c150000118001901c120040010720b030080049902400f414000040e00a007809800b900d00c2c02c07940510000e10000380903500414144a0506100e5001d148900381146000c40444e510b85a21000d0101000b007503100d440d900c0e88040d40010b075100c2c1451710540c0101003080b159401762050402d000401ca458944170f03208000366401c502c0c10700c00c0003031004140d07580360940d200490000340f40410f51071b00040343c04140e404007410303c2c1e03845040ca460a4108103147c000600d200b54030158035802451501c0c020002000082e114091800b03031882d094080111070700b0302c1c4c0301d20910b10601807000c0d000325182182c806000d02c82424000340c00d455100440c40c85c3d0003080100071071060002500b803147c032022042c2030210703482110600f9a6022103441101c5000e95908014085442800400e000989981100e03d40070244240001c4458058000401000d403d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 351190386 1250 351189136 351189151
    0x30213080a11011b03030b01141614011b030b0a050d05070e0606130902030406060302100c0c0801020a08270111030f0703060303050a03020c12030403020304060f080601020a0b0a0f05 80
    0x7100a80c03003040700024040e00c442d142400e040302d11501070101040e44002210004042542d00c074030400030380e802140c0c55940c0814441074113845030304d01034008240f00300485094501c10710342d01c410b42c03540405000d110000000d8140e05001d000c17090300182c01a0035006045030303000c00303100d2000c500703515018104c4a140340543e00401505281c11105085000d01034081e40c020103040101c503441142c001594000c07104030580040c0e5990b00c0d410000000c10958000030750241643c1000460541c0c0803400300009800780c101050b005a440340041d00b02e1040701880000300c1d8280f000100080329052410800401c0c0360b5a900c545440321400d0790131103003001c0c00c16940400100c18080188510f86065074080168101006881e04549024020780240381d0710608140d00003801d42c0142c0e10511002e074441c602494481d46a040518020b500c03900309000d5280081e001440c124180c9110310034040c021001078003d04410307074454542e90742180700284480d626948851030a0320301c480c58812140309980 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 351191636 1250 351190386 351190393
    0x151011070306020f040515160b0a0f0504031e030605030a020603070903050607020d030b031603060b04020904020c0309100903031710120f0b01080705280806040605060103060e04120e0103021308 85
    0x1040304025200f106034602d9409151f0501c56084a540408020031340180c009100084540d11112400090401c980c9481c041e1400d08061104058105000b07111030007007002c9220ba110816a0304504582d1144120340e490b80c0881c407401c7c058203141c001150001e02d01c1c034000454a80341d4071902d103070a8040d1071110059111441c0280b00680c1031092441004044000e0f0200d030360754104071000100b00d4000074207400d6035080242d0041c0d86541c100c50400d0b10161056407106440342145890b5004140483d00070a00c0301d800b808118844e813500d02c266581522034801001204481b110103510003010105030015105000c80d400910403881400c0602c1243c5c00c4a0881c454544406080c038181c3c440c015a9000032024005582c541c54400100e0b4071048850741da0702d03e1a007d0041401c156400582940200710a1000b4002207800c8070b4800c0d4401e88003070202c59511701409840c03500846015123650303080b145038600c003031007070380ca500c1412030500d8054200340301606540700d0100c2550101d0b64507803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 351192886 1250 351191636 351191639
    0x20405250f0e060c1e0f010e060105090f0c1903090f0f050106090e0705010c3806150a050c0717010c0815030c33070b151011070306020f04 61
    0x90303000020025105054449074100b00141509a545e190700e094a12074603003a210100d01d440f001000207035007944403a8000d1001d0954a1501a103840003809140e0040402c00c000030507880c1101141c600403005070500516050446030b034040d0203001030ba0713001c00309a11941c0d0360000c101c02142680d0058080c8082080c8050180341a0782180d901da805005518203100307082c0107654000c54400216102803c040388600d81034a481c90890880101c500030a050142d40084008911200c0c1c8074100000400c071038071a03c800c0300b0801c6040125107125012102007000c0c014142c4100301030b1000c0c10706242140d41c0c0546850f4130a2900c65110400c80b043da54503048001c4a5900041c2130ba04068480200c5001d00710f0a40401d458980c0303107905c140180c604032140417420212244040142c0c0b6800c20324060040c210b65412190b034800e10003518815000c402242040841c602400e01c5514010410001d0320500d00040e26058010b600b28501405542800804148540020285400c100400e1580d86 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 351194136 1250 351192886 351192917
    0x90302090f0f160f0c050312090102130f0503060105120a060905030a0201060603200703090e01150f020c090a0506040e03031512030a05030f0a110703170c1602040525 73
    0x207000140000320911003110100d40c0f00b500141d411400c0307052460480d4051015041041c0703580700305044490141c10307800420030700d5031040d40a03004400104085652031580c80c5a04e10301005140034040d070540020b001048549000b4885d207501c00e401100343c0310a19601d80311142100d00e035850541d000d40001034000c411039820b100f00400340038682401c01907850b048840a40c052090070403000b68400024085040c0742c09801d02c0d130014400040c4d070b07144d2581c4500317540310100d00500001010aa252000c4000e0301d001140355400901c010b842e00959580d8245010050305d405042c0b10f030001d80d6035030500c000520500040d4494840d8400d04802102c5120038080100c1001c204406160814021500383c40c2d8403001316034204541cdc41da42c00f916100c0e40c0580005140c2e000c0c007003045d40b8001544100309900f094420b1030100100d50120019622580082c400340718850080c215100180f010100500c1c1990105400082420f42500d40c1050500e039145540f1403001040e010804154142401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 351195386 1250 351194136 351194161
    0xb1315050a17031207020312130c1a0304060f06050406091d0d021e070b040e0f060a0f0918080c06090c0303090a060c031103031602010608031216090302090f 69
    0x303003011120036103242c2d40001a152079000380c1c11468201c00d10fa0300805d020920810030760700340110104d0b00002500f040e050490464800c00310856089000304400129211020b03070211100419900c1c0901d5a41e4642e502e40092407100c51110b1041e58443c000b00d410b48640c4075210140106440c001032540c0240098032008941030108156030780603074074040f8145da008c00c00341300c12000b0301808425000d80b0400c042c14180c0641100c40c0c1401d010030000b5042204010450180189080394007968403030f5001e00c0380004d90350213200060144107508014540c481d03030023042414081c11482075203454030342c3c0701103050b888070000c2003445c1d001d0000d01079103440c00d00c00f00074481c1040f00154946071f421808036559001d1031180c1800d100e460402441031500602e6114200d252b072005a17a07507464540c040d12200c0914224801c015842d10300c0200341005c001003140c5242e64400e07803880d1103a03a1900c0d088010b4030501c184404001c0c810000000680f00c05240c1400342c1c0750808080c065140c1080c15111 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 351196636 1250 351195386 351195389
    0x90f0d050d14071407080904020a0309030305091506010c11060a02160f051305090a02042f070b1609030f03020105040627021e090f0103050705030d0509040b1315050a 73
    0x242c00e24541401086604402c9001079840c8103100d568940b4000d0a04c2d001a010320100306070001c0c00001c6c07840c10301364141e029802c0d16100380c07400c000e030740c890040c426500c248800c44090070511420202e0301175800742d07400003640b44c441c1c0c038040031202540002c640c00d600070030840d0300540d002c1d51039044c0042d1400004400781802e14140d50050703150000040aa54828015210155640010640c840c1c0c05100e0300c0340240c0c000c0c00a0010704480b482d0001c8042d6920400c4948403403864101e070306031920318112030001d078105642c0d103231030389540c1c4440900c04080121038042c0480380c80000300080034030740040441030003a00000740501c0c0900300081038403030301e00740b6910307018000303010821b401d2100c24011041c58043e142e0401529981100701c1c0207169924810341e2002b5214104800c4412910074181601e1080f400d0710062952041407558900780d523202d0001080f8140140d01c490b0821782d010500c90b1000401c40707503503048400c030391320b0488e0b4066460488400e4280d0040c021400d012034101d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 351197886 1250 351196636 351196661
    0x1502131a03060411120a0b0105041d040b0105010f0c02100207030b0106020318060405060d0515191403120d0c020309040c030b0906031c1425120e0d020603090f0d050d 73
    0x501c0c5ca03441484556540303100805c0c200b560303139880c3c074200c0720782c2d1140c410307280a04449600341c120038404014000f00b17036008440840d000d40e80729001181a5108410f010209555600e43d40e0041c01c0c19802c0100002c42600080114400c1040010204010340e440c030f40245115005581c0e210100b2103c00203240c0b83d640424010720301000200b0158030b131442180e0710400c2460001a480c0c56406501040500414206a109031100d04103042c21100940c214220ba40d03144003200d10007a40014507032104038680c1e0401004005011000c0c881d10580c0121102c8003007481900e1803c84800002800c0b1201041801c002a40cae030580206141040480d00d0740101040303004010415001c0e0070408202c0c04880c0040c20040c0c91014446290195402e076a0b04401a1401c0c1c0820301c0902500000c0c0990080282c40c0010b200b0310a018448c007400842c1d40b81d030380107440003103007428507024401c0543c03002c1d00203007041c0b0419142c110511002d2040c00c1007100207a45a9640c1d8900007100c03002d664803103c964 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 351199136 1250 351197886 351197921
    0x180b09100b0f090a0e030d0c02070801141305011b0801031b0e15030703060914100b0a23100f02150f1605070b0f040201090b071502131a030604 63
    0x50716a200c0480000e00402120511001c0d51a05030440281290704580c84541c44041100c1160511540280301208669030071101100da6482c1c00318203913042485c00d0300174a240040400c0c6c207124030301c2035840b0350b1340035500100e90355004144214000d594411fa000015040600501c20840141c014003c1030480d0380703060440030308021402400c8040940341480c0c20840004e0880741d0348003840403800950b00554100081511801c01c401a056107083c8081103000c4c031040000c0d5072501c2e20404942e100050f141c0100b00d400c3c0000100d40d408002030092074481a0b4030b003d84a40c0d0f58a00503c0b50300e42c1d0b60340d40283c0c8501d69001a240040c1d007000111246e0038a010040015035250381c843d032110042020f031900d02e01440f03041ea0148501d5401502040e1060b040110803c8218440e9004034400c1e643c01d0345495850074181600c3c021a0f00041140c3d020036001510040039230003a0a110f918170461003d1169610045481e0800400d12010301d0180841081103510345489807491400602a40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 351200386 1250 351199136 351199151
    0x30207021807030b1005031b0c010908030a0603060e060403090513020d180629040b01180f060207050a180c0302040504060e1506040602070b0a1e030e1204060c08030a180b0910 77
    0x100c6c4010410300230318482d041c0041440d6610042c250403461f2104d0f00690702039604e0402c200074101074281d03400182e076a98200045070780e4003080050868803071501a550140d1030350410040200544030401025006070b002d10401103622024444c4031080d41030b00c0780d003000501092410500b51840030800441125a00c0034200c010000c4e1a130244031584201c03400a4802c407c8001a01c0b540301c0a1008820f08a08440104d01c3c008003510b0303041520466000c4621840c1c0e503908006010446002e50500382030060744440301d5044941010624200600f8054101903e030004101210440c1c1d01c84180c2d40039800038003a085100340c102004200c015112280b601e8244240039644400900c0b0705100e5a100180c840c0d00c162040310000c1c802460321500c00b80003100c4450040142035101d032514079500500003010009950001150102c424540321105030810f1600c90680c02e400c0184428401c81d02c0b0350061107841144501308000da4446d04004855050038105203240480403600c0003007d9242a04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 351201636 1250 351200386 351200401
    0x20705010e060310030803040f1403160b0a27170403021c15060e04290601140c0303040b0106120b090a0903020f071511070b0a030207021807030b100503 67
    0x80028114142c5540783d0b82d40310020b0204502805130f0025080e41d07800b2043c04204808103002890050061142d019941c0c101920300b505c9204414844101c441c0c80d1054800080211407000d5105110701030015070144c80740b120b1101034001000c4070680c060403004240400c90030041010603c0b20504d002c1d400d0a007540c0c086420360758101c14095480f0f06070342500c000c00a01c105402c1c021943d4030001c1c04400d550b00240d1802c410192340880c0c09407400002e01003280803901c8d171444d0240c80e680c1c420310341e07480d550010745001c14920300d00703c1c04000c20130585944c440304000450145201e826550074540c9004002007801310300d6629401042e003001c0c0141080d59800030381540000b40c60400180c05c00c10b0f85400c0c2d107809200700f1b60524074014000c000a644060b0b2038070840032009034884000381c000804510344c42d03840d5409507000030701c0d0901c403000c14603100342c2c0a801d0441c805003044490601c60040020041c80440320000020749480d00e00301941825842d100c9020f1090a0a90550801d4613 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 351202886 1250 351201636 351201647
    0x607120603020a09151a03040b06030c010f030b0a080105040803060109081b040b0103020c010f0b03010c03020c070e0621030903010641040e0f01050106090f0e1009060602010c020d02070501 83
    0x110b6201450f032174240c600c6900760040440c1004126a4415100c07550404400c40080d40048a082c0c8481085400281e10b905002c030300b44000840594440304041100031007540207211031211181c0181d042c19001c681c1c02ea09103e2140558050703440103481c2e1619400040c4445c14030340001c400b039045211500c41c2d8041c03045040d04601411a07000c0381710015440124000e000e40c081c02c040360340c200890140c0c2494281c1c0070780140c4034164000d0103140d15642d0160140c0c03145108605255010100410480d82e60041c5c2503006000140b004001d88107865003202c284010008149040d0800994a503042c9824447d4a000300b0b1103c1d00c4080700d020641c10030010065003059400100d440d10310031102c441c1340c6c43d00c002802c94003d01c200b290222049800c1d50710180700d102c002e495072800c400458454043c102c3e440c11903018040302e094403401c0c0b04403010103200140c00da40e034100300d4510110b25029140110409420a079000113941520968001e00d4a40a6520368007235420030703181440ba0b81d0740130 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 351204136 1250 351202886 351202889
    0x3030412060c05070213050604050601050f0a03051803030f070813080904020a110f07031a0f040206180306040b0619060e06070309080318030f1f09050a02120607120603020a 76
    0x310000850b0941e040c8181d45521841c90000c0d40140042c0071003114440310790003a8082c4005031401c20040e074650740151201d2003903d4a1580030801442810000c511940040d40e001000c5810840d141500c0207100e031440c0c109403103800454003000108201c06a00c03988a650000d080106100700401c5912002840d120700009280201d400103803002c400c60084860201e0035040404640c008040301d580700b5212040c0b408100c3c0c2d42c40052002d031300c0d000924180c950292800100504442c3c90b9a420032400c0e910091420001e505034403046001703a80c040c085903116500a0f0404e00b820700d010300c1001076820070403000c19494001404c0500c8510362041d0400d9a218080d03170f505681d031026003402d44040b031041c1d0101d4681d2100058403d42601c02c031201400501c01641200c1340c0079020340301a0f46440307850409012210600d0002d0403011815000175243c58059003c3da1011700c460340219801e00110003254419034007490030310039501c2d44001c2d00d00d0386950400d8100441c81c00c3d5800603c058406 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 351205386 1250 351204136 351204143
    0x203040209130f120302040503010c180905070c1209060e06120c030901020408030408070303090803040b0319060306140f090a02030a140c13061d22080408030c0a0c0503030412 77
    0x200b0b0320840c204007090100400c56a00021103050010615400401035401805202c1c02542040d4944929a02500b0f00c602e01a6a0340207000d41c40782000700c00401001d004040c0c00c20080c00e580303c0710108580c100c003d107544120355145400303141040707070140036071200190880c041c007000c1003008058120160071542020381c0650341541d035160003480340e01900480e00b003e0b200d40000030f400205010001072480440b4446d13103941590950355442136803203014030312408140410801c0000c845c655542c0719901e8044102a0018500d92240c0f1984101c03003441d01c40041e040e5003103050150030b090001c0d001c2d80c00130b05e41004080b449800e901107a2688810340004003250303500c00b10358884040c24000b03003041000c00b4050303403141c25144030345c031000e0300e10361080d21080c2c1e10121008502c1c11000c41304038031980e143c2c1080702c014a06c05002c8051101000ca050f51031030400e01010580e860107200900340e03030140320300030001e00315103052200300c400090b44414403c0d0300030401001b445440f031002c0c15290f0740 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 351206636 1250 351205386 351205411
    0xa0201050709031a1f0905150303040803041206110a02010b040506030d0c03080a2418050c070f03030b1905030714100f020f060c0c01140106051c060b040305150a0203040209 76
    0x8800da1300b46602e17009152082d100084940000c20b00e10034592080d4400d492480e074400382c40d2640004e1545070320590040d0a400d41040000740403180313a4043e1109601c1c8181e40001e641c0d1002e449020694001e407540d04c0060351100c04100c540d240500a55411400c12400380c610b48400d503502921b8036100481c010300f40300c00b03000041ca41c1420341c0d100003903510312980c000429460300c1034412240e400c1801003806813114450b4042400c40c19214003842004c900c00714030303e0500355864148100c0b030302600880825840341444503554841c81c100443e00441c1086007044603090070205410020b10350454800d081c03440c40013424561311902042d200484905140d10b1031112410102d05040049900310600e00c20b000078410a64410401408140d0007107000f00050102241c031155058020710402000600500000c403a00120007040d200e244100d400000d0b04c140d441107640c0d25900560b006495079040b031016915200c1340741030140e52001102d2001c51131441c0540c001010a88050154006400c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 351207886 1250 351206636 351206641
    0x6031501050403021002010e060705040e0f06040207240c0e030d200a080306130b0f010f090e011202030f06100b0702060d2f0a0c0b060109030807080a0201050709031a 73
    0xd008404407400b568004c1d1800c800b4045d0b00717401a02a040540c951085842550005540c4510800070398041d14400303550b5901644038410041081d010103044960b000e6400c01c4a140080c0c1c4855841740f08259851084440c4004055240b0484010300303101c0c014400001240d031a1590041240d94540030141048200071417001d4040034606e0500311515014400c0a1a142c1846101c1d00031314488c00084901c680c49410001002050b116a50340c3c41e038200342601c450344040d42c0180d0418003841402d00c0c203841100c1c0d4800c0f074080e800400303a22000c4080600c0c0480e40560030103001c500800d1402600034542420500308c0e0101d800c80724032403400541c0b80852040211764402088440210740c81005014000c1400c0001d0342d1003920600e101d22658a1003d0058051024800c2da24202c0701c1d6118003883e594503403a622201d03c8010314a030b0401c01424000300001c1e100c1d01c00b41c005140030340d10050320340056960180c21502e0140c400c0080c003074002401c00019560a91100d41c40f04028003801264 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 351209136 1250 351207886 351207889
    0x7080a08032a0705030720010c17090d031e050306060318030d0507050d0605090c09040902030a0b0c070309061b08071128050f0609010f0203160c0905070e060315 71
    0x1c0d20302c0301c0c81600d00a00001d8807410301c40000090803401d802201f030400450a059040c15400c4040b80700300b80480c3d10f134040071002c1681d00f4030490542d40c80c0200c00340340c6549040004c0031005000f03405ca01284e031000b0040d5140341001c0a484c01c400c40c5041051075400d000000861602004181c41240b80700388450008400060040d2440303800a05010f10a90620102c0542640c00c0b8051440d400b51910200203203d203400c09416000e8a980480e1515001a070000d002c05400d12a0b0182c0e014401c0b000c0e848001500c803050700d0700c03a000b0401c56a1b00c0b0052441d00400d400c48035030014040012032560642588040101145401d07400b244080e82c1c1c80241ca0541d9280540c81021540510204c0100c404041d084034400360b02650030b0420703010103841e60104a03000b262410160f4100380280300c0340142d0b5001c2c0108402d01c2c0c000b40122410006007060b41032451841c0301003182d004664560411506c0c51030300816401c01c065040c840441c030405008203405010041c4098400010b42e0402100f6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 351210386 1250 351209136 351209191
    0x308041713090509100c05160809030d050a020f01050c040b2b0b13020418020a020724110c0907030506062a0606150405010c081b0d0207080a0803 64
    0xa020101d00d40810503580e400000c0c014101111902c0960140c83d44048030a68035200d40350030084240c56050510301901c0190705002c04142d070843c0c141004102c10100b50b03404000d0b0581c0300c202655500d81d1100d64200003030404ea443d00114a25030305100600101441c404181c405865580348004d40b20201c81d80d61500000e030345440c800788950034040e400c6981456400505c9261000c1e503600f0440e58031040410128030562040b0608118603e0302445401119002028160301c288111508181c071600f0090340d00f006144c1d1501d62025102c0c071b0b0b126541d000007004001c1c0011402520006507080086203404800415142c200350703640002407a15a01e01003982d61440452040418800300c181041c010604810f070703480c42da0f114001c00604e0514001505100240d602c0607500d0a180c0b0b800d005441e04103820604441d042c1081c040041c090203004144c0d40b4071400007000303010f074050031600a07041c05030301d402070410780d041040000082041c40046a810040c141d11116503102d4038490340c4807 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 351211636 1250 351210386 351210397
    0x3041503090c0918020a0803040b030a0209040e03031e1b0703030e012c070e0c0d0b040207061b09060806010c02010c02180106050a0f0e092206050702030a030e0a03080417 75
    0x60007813030103400000410305420443c03059031080c0c8407080038584601c441ea6581c021442840340c2d10300c0070000140001c040750094070340f001c805080818166241c46145045400441e400413821a945050b0000c00003001d1174690003405250f10380000320f0484110103050310840301d0190500d0b445119060000e075003544051b100712a00352801c07009030601074601d440715960501900343d520684601044003850b24449501070003d1480c014601510f850342000036000800c11103600a50911041c408120540281d645800e520301107107207031005803040503040a80a41040d02044041c0c0e08102003a6000584100c4460302400c244180c1d04062001480e12007101550f8082407040c0740000544a81040280140111549400740001c00d21802142c1d00d0780c0301c5071120b03030101001004ca946501d20b5007c2c222010900d820001d4011002e8a41c0b0701541c1045d030b400f0b00142c1c8006400403180b0390502c01c015100c0ca11202910710107440388c070000c1040ca070140014112104800740445032a00e420110351 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 351212886 1250 351211636 351211649
    0x7020913050304060e04060801110403030c0606050406060e1c0809060d090210020705120f0d20121e0c0a020603090a0c0f050f040e1e070f151103041503090c 69
    0x95a5a443c4c0340010b04a000102105000d1400c261020400ea0018002c41310b4010310341d104581010724588088402180c140420303155241e443c0c0004c50b040d07c990080a0141401c0d071a842c2d01d540d0700d03105010303060b4a82d60004a41d901c49007203450004800804540c11940708441844e01c4036894801000201050b24009500800c03019076150903e8010403040d0480720101c8407155040f03c8140b401d52034400200f10303c1d00ca0f0304103c1c1c03144080c40c09400b903013045640070182018040800346115240100c40781805100c4000451946600b410307000c000e080f95519030711105e05040e04806c1e4260b40d01ea40101c028400c807008030001d002c81340100034540010f80c00280842c00955580b4034803240300440c0c0289030003540c150644884504040c01488418000c19000b040d040113407a04c0303003500721084100c0c2c03c0240030f1002c000541100341c020f0134000d4540c0400d01201445c2603070f0050900c00c488076400089802c1448204917041039034030685445011411301080c5245546010740b801d822541100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 351214136 1250 351212886 351212893
    0x406021e03010905010e090715030507030b0303070b040c080d0215092404021008150405060f0612100f150e041428060f1205010e06070c0c14060702091305 68
    0x190710b8a190701310398100c80c0080d03c01004e9032141d0b041140c0306c0c0c0d058025240d104548820708010030380b180d03020a512003860f00e000603042c450310000a0541d4080700041c1c984000b94001d010a10049886035402001880000c0c039a1120000020b074690450341016050000c003440041d81c403003c103001c90038282003d50841c1102940164641d041014180c8051340a10121740b1042402400390100301e015040d1b4440b20121841d1610410025007030080c802d58202505465142198507850b002c1c0c1551091420a1803052030310b0324140383c05015603407103202e4000900008000f100c0c10341c0082100980315151507010641160085006442c1c1200010488200f110402960401c50303014089000c042e10800c2e4590030302d09020300141d43c054091905500a844000c000b0040301000b1840310501c120008114a464414028200034007240c0d0b02021502e000000b0781040b0110b100040a01501e9441032492105940459003a02071108024060a861004a042e42e500410040026503000707048 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 351215386 1250 351214136 351214139
    0xf0d0f1a1e09180106060305010605030609040507150203041a13180e0318010201050601110d0c110904030807020607050f040909020f090a1509090525080703030203031605030f0406021e0301 83
    0x8800010100404040c1103510341140450b410344680117080c1203c0c03050342c2f21030a50f111441008105840a00200d17602d10568100007030f1a4016115000148032540103151194500071000c20150285560030000300c0c4204102c0321407940c800f0300301041c7c03907a05d01c0c40e00001d0b2648081200a05450f50084441d02c00407581840401c4140c40328601040c0a82c000e01c819203c96005440e140d510301c80701c07001908034021484185100342205040c180c0151010485500e0490200b07650000039a8145c0025010204004116804001e01c68202c03101d4a0400d00c0d02412608041c014011805814045034560b0760035001d642d00c5600b80e000340100103100740014240540610020071200462011010ba041c0c400540301c0c00510131091043d40150140401003c207043e00c1d60000040d007003211502c01d6481303000c1040300c0d0401291001d50310980045da80e174209201c460101021003075901e42040820010002042c0d1951107080d04940e0160015885106100d000e0300c008958601c0f012044102100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 351216636 1250 351215386 351215401
    0x908100501091a030c011b0605160f05160f141b03010605010e01020a0825260301081c120212040c05030c060703050c01110f0d0f1a1e09 60
    0xc2241200c0900d10200915001c031201108a01001c03402160f00d504461366500300d41d405154660502c0d00c0c8040903203215802903440f1380c129801070318094a040640109140f54541080f01011480e01c18140203051202000c000400000d1040c1d000b0100d2520070703405810440650003210f41c0140c00d2043e81d2646491950f035401410854807254030039070038102d0014040d40100601326001c1810313409007401003440e07240c1141650110408005031000003139140d100074500091800c005104040a50f5600041021501100540d104208016004000401082d00c00154501c04080c140b55140c2d2001000c0c3c0d41507648690491154050600002d106007480a403000564861842003075800c4003142c40d1001d040d07603517290070405900400700b0810413001c640a2005400414aa04008a40e0000c09070318030b8800d4100030000ca800f0702c00032400c101380d16024003c800107244c0c425010844004041e01d10b0112164026241c0d02a01c91744040801500105014aa96103c0036240742c4060414a1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 351217886 1250 351216636 351216641
    0x270d12021618020f2a010b0603100303080403020f0708070501020f060705090d08041a0a120b010203030a0b0609090106020c0111010b06040b0a170c0c190b16090810 72
    0x2158018050315100d00351200c85440c0c200c0a071a00d0303200100040b90000080402544076030004041e2503010b01c003d6541c150303403043d2800d0914000201c4003079140f00100b65400e41c1c4d1a40e80b00d900c510428130400c500220300c0140402101d80502d008003083d103503401c043e0b04011607141000d16074081c40c3c0b00400c0d5400000f8901080715800c1c1d0889444203400c4101944808041c0e1384000020020007480c003203840d11112056445006229052030181e9801c100c0003034190400d072144107941d021492850301c98010f140c0d030752015405403042c0125500180002d459101c01400021059900c0625540da500d0300300659001c0701e4098150000d6503128100a95a48200e0300c3c250b00161804081841a81060145440340e2001400301800e16040480c1456503410080140041100c4810781030410005004a00d01074007101c82519520000d1121b06410f10028011402850220050074070008080c03c0810340e0001e08290100d83d441c03030160701124182e800741c1c4140e42a12444400c02c0c00250709a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 351219136 1250 351217886 351217913
    0xb0d0b27030a0f0309050a0f080408030c0105100602030703080f0a0917070b0723090114030709050423010915260d0f2309040603030903020405070302030c270d 70
    0xa031680c0f9101c00c00c2100c2103040d90a5548000d01d00d1f004004440c0019907500b940059580c0300d4141da904094440c05010320f1a0800c450b80340c0e041e13458031b06000041c0e030f08002c840e016208a10240d0314000316070320041e005000203001c03580420301c040006041205291b03c541002544aa501000740c844078441100300d0304403490948041000e0004250302078000c070380d13240100c44c81240d40c0c2107407500b14480902c40d801507821907060241030142d401c00c520500d80154131030717281510b91019590502060004940040ca0758228019680f010f40c002015011103082c115021a41c000c540c00c0e20301106c5808102840d4014a109141501e10440803170418407540e400340c0c034036021180383d507003a00740490b544da00500c1c03003201217590207584400034132501e041e04800f0014030340b44c2ca1420f0480703408038003161460391040d0005861400140118545805901d030014000d150660a604200740c9146641c46a003070541c1103510704101039402844040940c1084180082a05000c1e103241d04201c0071440c5403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 351220386 1250 351219136 351219157
    0x504030b01050405040c1205011503030215100f0504180c0303020d030f0209090c0a020f0609030c0609032b060306020301061d010f0e01030c020a02031c080a0b0d0b2703 74
    0x3900004955402d10f4070505201d15005585065213900d005001260300713038011402d8849540b540b04480042600d00748480046229500801946946560410482901808010000103040d03010403a00344514000e03410307544102c0740041d15070500341c040040a40a042c00426a030901d26002040c90703000314680308080b1460300c01388541c01c2040b15800803031207030f01e081c10760140a10000c43d400d0041d0501400c103900003030040704c84a105a001e51403616004684400c2c041d48001098070044400748409a080308140c3c3c0103500f030455040e032a490580484440c0281e92000340c6640c01400c0c05908039400842c1c00410031507480d619120000d007130010707194030404d6107942004240010f500c40d48a0756020603840c0e40d561411b6221000440280a00100c907a0852007044020000346c0c5d0188480c16815050859680207540c0c51640a442688020100c1e0141454524603010603240c1d0b40381c01507000d40c0545480303816a103070310044a080165508418001e580c520801038100800801890388005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 351221636 1250 351220386 351220403
    0x10306051b070c06030f1d06150a030b13080f0a0203040302040e0a022407150c0f0212030105040213170a020102010e1b040b04091b05040b010e01021b04060f06050403 73
    0x98200e0707960a4410410000e04800140d032080007420300c298024000034194984c00f00e43c00d010322021001480b07602d01c04505a40014081c031041320b000412101020340107a42c0c014202c0c1c6980c031910550380005125948104003030824000300101c1e44c0447d1007032000741c1c04c02500c40e1081c0200035540c1c0c115000490189140ca84c002c1441c00300040ca03000c450364010108200d52040d420a0302140030203198032000b0302000c0c4011000100e5410250b40340780040700e400103945c415280028401030303185881001350341201c43c10354009180c010440341540c0c01501e025a860358828a851208105680724800e541500724003035040903000f02c1c0d90f80245000b64001d0020042c0b0f0320840d5110003100d079a0740340f140d0105a6000c441e042c01c0d0401042c410000340006441e000945881d0f64900100310602d00e170710400180bc0c4081d1a081c03141c050140d10a10b02042ca4a04280010f50b0761000e01803030b4040f200c0a4520b10b0110781d02d507000003000d4210100f222903529038920740034210b50401c1c003007101c0010303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 351222886 1250 351221636 351221671
    0x403110f010c0b07120e1203040614060901030807021801121506180e030f0a110f030f16020d0203070b12010b0c03040b0706020f070b0604051e01050118090501030605 73
    0x1849020100d00068016603a003d00d9114228151803804104000342c030f8880c2c60783c0381d2482e048810310490310b200c1038401d400741da00d142510f045000c942c0c49402040041c251001801265190303205c86c18103403076016003920f41e9100b0302d000084002c103c0001c100e200b20151000440c001070004c00c001e5190384a0b42e0072480b00044a0070400680b180f5000d001020040499680340d0000c4941110302c00c10350100541c1e00c0c1c141c00718100034996102003241404074071100340b0541c90050400c1180b0000807030102440c1000d102d2030715a4201e205042c2c2111300a80c0a01c000015503a900c50a290100d43c000d0841d1201951403034081705c550407420303146682c0500c03003000013203904a0307a086a030042000c5000d50715041c100800012590080101996160360030700034000301c90030140080c402d0074010103401e01c1030704d414020801a83d900900350b410b4049243d2409061400403000c0b0340c1910710908100202c1e040c4411413408400f038541c404480c640c07c0100004c20700110340c0c0445e0241d0500d40154070b141 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 351224136 1250 351222886 351222889
    0xa0605030d0e03121c140405210703080406021231050d03090c1a04230916020c0d06020c0106050a180506011209240b15030a110403110f 60
    0x1c546280c040703401d43c00104c0080c0c594001200104181000d5040c0e82e50700d103091022401c2114446001e030207008403050148014000100b010088046401030f01c60340c1e0b0084121544894041c103003000702132100d14000710b000c00c0442d130117075001c026401c030f00000075143031a00b405000c540c6881d0084040c1200f40301c00c3ca04062030b401400807030780c6e0400c0041c0040790325071030200c00030301e46002d00303541c400403441c00805c109a200d4200b200707980f400c5800b181c849050000f003121454400c054807003091020442d14045446d0420090351240001c0075021800148038030680c100901c003002903a01c2241c281c5da000c00c0040700d0b8054880d8220711002080400e4403a4188a042078050050552109ea100350348040c181031078000a40c4141b041c0b5126042d0071001e20103c0503aa0300803000c031046072820140241602402010680142903103109121034541070300420500030126a28240d000030010026417210002d4003c3d4250540680d04140e407999281001c840f02d1640c50b402601c80d072488031902103039 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 351225386 1250 351224136 351224147
    0x108090102070b040803100e13060501170c0d05011506180f030b18010b1804060b0a23240c0c030d0807030b01090510050c010b03030f0f030a02120a0605030d 69
    0x11552085040c07010b030301d0300e481712034903074100811403003071002ca0250105120b03000601c40740c0240d20b01d080c6400c003429207240c590705a82050308180c282c81480002402c2200000801203a1184240d98030350818030a402c01c3c1e8003505980204401400145a0005190b588652005004401e00d42d0384cbd1030003910780807040d0725400d20f8400a841e2662100105d1440903107404140100b2078035000000304920404042121954102d5050950314445801c0005101701070144a0240108541580c25035080c0440b000305004250880c0701001c0c1800107000d0191070b40c0b0001010158004036000c000c2240c8490018290700c1020000d01600aa682001e8141070010f00a0340e00080d0340c441c40700e01d80da000b9040700244040c02020b4100518844002910b0300c5101801c00c03c203031035540751a0f8034000c2003001c9094500c1003400c04e0095200b04800c00103400c0300d105440c545000800003580e0b917220100789002900907005c9190b8800010401d205009060358420000c0714401d07000d80c1d10080c1d802c04280c45 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 351226636 1250 351225386 351225397
    0x6050604030323070b0403050c0115050310020a0201020909041b1a04092c030307110c1809121309050c18010f03020d090609020f060421020103020f030405010501050108090102 77
    0x11820808510034140c500e6400000300032502c0071520705000c2151581e41c85e125080e1170940c041200050003401c0340c0020b0140170398050846103004070300d515004c040380d9900d08030802c100d10076501040c5205514400c1d0112410081c0007810f03032509041c103003010200900700311140301c0d448010b230b040091055040e078001041c00b050003010a040a00e00398010001e070064140d40c075045440c211111010f05c26a024880d21a0f02c00b05c000c0d038036403a0061024040b1644c0144201c219407003000c43c0c20a55640c040072200c11503440c00201070688804072a5854484580c04807840a0300c08168040100919000c0400b29545d04406001c1a15413011342d9949101d803c158040304000081100b415500072100d02c0424030741c92800502e08090002481e0864404a004407a1152204e050b4015440c0c407030800c2c0480300007120305a280c0f030316110414410261103115100b01b1520040d034001560702035810b803480801e4003044107070b4038581361800c50700a1000b4007030207000c40c2000021540b42c0310148266031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 351227886 1250 351226636 351226643
    0x7020607080f01140411161103210a0c050a031107061137060b0f010f1704021302030103050c090702030f04140d06020403080a0305060306040b15040e071502010605060403 75
    0x198590a01204d0050084190b80450b0056103401c8500c1840c0e60760707001816820041c9013010080c0d6020b14184501c0410810350300e12030780c0b01c001484880121440d034480480c01e003e41060b50381008605c03da540701281c010240440c0a0020700c1400c0c99001803401203429801c00907a8181c548603041a034441c14118880350960f4820401c2401c08011303401074881040c03080510340c40c02c00000195100340714114004903008c03910f50b110100141014020401c0c4d82200342000c0c1d0019107070301401130411002c1c1c9405801003265070301103001e5480f8400702d4854000c02401c25941d87d078503800c02c0c69540615203203181c01044c281d000503100620200548004080344d03800340703203410307e4400050051160400c43e41c0c2d01c0010800780800040e0144010130041d4429000281c80f0b460102014003290002481107000390008400c000c00606440201c584c0029804880421616034001080c000c1080100c9090325114019000c41e0b040010f0180a00005095009010203525038060010343c9c0510711004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 351229136 1250 351227886 351227911
    0x204051e3006100b1c110307180914040f0305120f010608070206010807180608010e0c01021b030606010309030e0904062f2a03071a0604020c070302060913140702060708 74
    0x3c040d0a00c070f000b005440340a40190205d000301440e0603c0125038015160180416421003201c041c40c1c000038008002000810020400800000190b036580bd500a000403d12043e0301d03120000c15010360207843d1140c0c01c0307405602c090f2a0030380c0186940f003c203001e82c00c0482d2000700003c3b0464030006480d8184d48445002d0701032103150010000280c501d42c100703413032010380340c1401048011091065841c3e1140e040700809081c95010006400d201c0085241c030518080a100701a81e52030010300c01d50800000e01e000102203a060a0442c0c60b5610490290340c400d0510042c0400e2201e940c1007214401e2500c84071111010a00c203038100e070741d03610082603140c00c2c8050003070001104040c115104020030800c0074041007540c1ea04c0890840c2c0c02004e08503034540d1070806104801038941d00c401e03444601a1011403511800c03505c2196120240c0c400244213185c0055482d0b01a10342041c1c03200262440602840305003548030f050307085010119000c4005104100020b64054410a4228011081d02448 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 351230386 1250 351229136 351229147
    0x209031b01030e0307050a0c0e0403020304060804080702041406030f03070209040f08070c030b070e04090b15120d031d0c01080411031e060402010906030204051e3006100b 75
    0x1600e9011540304456818150b45440001d80b0400c14401400c00300e00c60310281c0503020325443c081c420b1100c160800c59551068004020000f90000211415200d46003810b048590300c40c80c00c3c030300510400400a410070300700300c2d05a6502e100801c400d0300803a421401e540c0800062800266240508100a54804042008240410449410590444e000d8003600b407401c40561500c05d0100303070591049500744c8c0040104044554401e513104650102240d050000d03140544444c140c1410180204426070946c0715500302e169222854003030702c003c0e08010340341d10400355803000e4000c20100284468030915240c0020100d00f01194282c00d18505031100c1031141c4942c0c80f141e220703414401101e6054441c10344156902803401031540000c064404c010300051505100051240303076076502080c01d040c0180000c1c08a950f4082828076040c03805908810394465150001e1034001545000600400c0e104000d0203484400a80c1e0103e00d610000c00c0307441d141c6907115814429843d40c405d09403612001d000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 351231636 1250 351230386 351230413
    0x10926040317070b04050d020f06011a0c1f090303050a09080319020c16050f19050d0201232512081807140a060203040807120302100c170604020903 65
    0x10321040881d00d070840341d410710001c0e40d22000404130550302554140d110860103100d61350304000002054a015003d800d00b940361a500c002400384110500c0d0041c0004a6040c200b1002041807204000c0f071030142280c0d405410361450f0040c01d0710442a00080d00303010015581e414103000d120a0a42d00c060340340e10315500c3c1e070044600320042927200c0b080d1a0f020403d50204880810000640d03012500c8001800351400d02008000d40010081c40d00500d003100500307001e014400b0761107040340e50070f5400044140c42440125920303e100d11813080900d0760940404c0c01c00d66050b01074540040d2442c614106083c803000062120082c10100504180000c034021981c04d01c80d050958000b134000500c100c841045210040c1841c0007600850308101c982e5100803818540340b64480c0c01004207001961900381007005042e20382c2203901846e04026809026001003510810018034004041d403010480d94860b040000c103500d9125641c2300f0740d481d40e440030841c18a001d01c22202610401802002103002060 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 351232886 1250 351231636 351231653
    0x3070905010809070303230c07050a06030510030b0717011d060d0b060d060902060304030804030f0306080a3504050301140105010c060f020f07140622060504060612050109260403 78
    0x160301f03c42885150024034400881400a00400040c0c64094170900c3c2c1040280004203040b903000d0000c1500307103401e112110281501000c02c4d603412500e0040c42d540ca0344020f981c80310b6420100301c04020a40c0000440e0404018070f4440d40850303118901c695221141009240210503001802450040010500d07034503140107003803050313840f40e44007050048043e00040c616030030480f400d0700880c07442410030081552181e141202d68515080400045081041c0c0d06d50758854540300520b20204415101c2c0039118010040000c50741020150070314a0b81041e185c051504941f003100c0c0a50f0800740000600402e6030282410303507106030f582c42e51540c100c1c0c4486c8054441185400107580e400c00110320740018030001441724600421414400381110340d410351525000a0149007240d04c2020300c44041c445c9014100c6056404c800c0c0410f0548030b50401c20000c0c852a845400f40c24034540c43c000401206400c400d400c1c5002e4180c2624070740d14402e60783c01e00d9200c00d40300d24120f40c0810042c40082d4090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 351234136 1250 351232886 351232907
    0x6120b190f02070302010902180c090f120610031502040b0904050403230909010909030c02131821030507020d110a021903050d0c120e1f0503070905010809070303 71
    0x100492034142007403240007280e200c950140c0050b51070b0703a82442503007032030503078421407481c505c034005c42e00d24013241c0d403032110700507100764520031a15071641400968035850165500701c0e900303081d01c81d103041c26058400c0140042c44120340e01c1007007424003034801600c2e1090301c00711030342801001d242880c1d4804000042c03100801c00c40900080c4661070f600c1c000c40e00148448200a407541640e16041041000f00c4110142d000b070403028100044000046e5003c88240400780e41a81d0312218a032033f05103074401401820540d5500001c05074004000d01090001c00c001d81460400b540b882d05070b40100c100c090f82c0713084800b00050383c011020314025500c034150550002c0c03202015980c41310701550001e08404440004400d20900c040703c24014400b080c094240001480d040c03030388100200d039a03503403001c482c524500c1c000d02c425110b4140c4180c0b900000c1a2040c0d1702540071a80550080341c0141103a04196519800250541808a07030ba502035000c66008503542d5000389030003840c6640c211a0310409 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 351235386 1250 351234136 351234181
    0x3031418010c29100506043012020c040e010e0604081e0c01020d0c0c0b010315060e0f04140f21040509010623030105010804020d0201141206030106120b 67
    0x220709001c0c16000710b07902c2443e0b640210303003001c0c0c0b00e090680e01118001c2d0b2075000b481c40341d2401c010410401c120f0182005401943d441e003c0e4411f20605140e400c2c03c44940c401808001004204559a45c0e01140103400840c04840c04c00c0010308200380c40d800c0741d88000390030101c0da104001040109101c0400b608800ba000c144a0700650540d540502d000d8004613085051030f034021810108504440c02651350030546413405110107500358031000d200f0101848080e000c5407007480c15211000c10364001c000503005506410485040001e010f000c0c620742121705441000607440148040b0380041126443c02580200500c0702a251200e00100049200302d0500c02c03282c1004001100c1d12110801402081d894845030280c4041c010b1411544c40e9424000044143c20001840b00b681c1250b04213070000d40546100400c02c006100513160680c090034200c100300d00100e84200e00708561740e125445244d00303034001d108050355041290107201d22080c0048c04074414900040c2c20740041101441007111 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 351236636 1250 351235386 351235403
    0x5060106090e0402130b041404050c04140a0507030f0e031b070f0b0306030a020a080f0601081c051308100603150209030322050907030c0e01110714010c02150403031418010c 76
    0x61b1000140c100c510303094640220071005001c00c401d0040504c01040b841406440910076142d001540450444005091082003540c1d80003042d091446944070440780b0805e03800411856803010855507494120f401c02c40700461070880c00c1c94030181d001c215802100c00b41d00b003000070f042c01c0404898154000400168252280c04880070240e0346600030716000340980d1002d0700000c810401e515040a00c141c2000ca041d500c035001c10b5a01548000d068030705e481030761414a071103a081e00e441c218501e00c554806801032182c403107400782e00e060399031011341113a2064000b4503100240c00b1591050380213040c03403160b060300180050b000c9040700d4049103480d003541d03212070054151a0b1000492950b0f0688518000036598110103206a4001c04c40700d00001c0c090074100e000724024012030f0340d00c02c040c2c0030b4801d80140c0d00c03c0243c480d9002e00441503d440d401003403c6942c1d010b074031440712140c1252106900060410391000311b88210309040720004e400110300c1941020020b0010340d581004140104c03411403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 351237886 1250 351236636 351236651
    0xc0b040b09041d280f0c0608090c09010b090d150b030f1203010e04080409020c061006031a011202040506070f020901060801031e030c1505011502070f1e081905060106090e040213 78
    0x2903170110140303841441200c00d926603c1c20003200802001d00286407050580c01860314400070b5036940003450440305200d0845a491a55001180b6403c00c07840380200007401403c1200500411500705400407079040c0c04490703801038010205942d5900d500045898501c0400c0180301030403031000c0380b6a0050060085c0f51405544a012004a0b031040d407040c141900281c061060f4924240c54190042c0301904e001d101c0300301c2c100503046412000c0400301d81801841c0f00c103041424282d406403401008020001d6803110403504005a000c500c84000300d1003290550008140c0c030380641c411a050b20381004170401d5141028000790524022002c040d0244401650100002050701484407a95180340304c000c501c0b54035150700782d22959100040d140a40d00040b100740020340c4007405200848a401094250f00c4e00450300c220025100e90300801c0d032a00944240c2113200d80d03100b9401001912420803110175a0341c0b41c0c82190100054094142184426804a0094035103403003080000000c1c07100005240c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 351239136 1250 351237886 351237893
    0x12010b030403180e01050a0909020105090f120d090801050c0c07060507050316081207030501050d0f0c0b030c040602060604020a0e060a140c0a02030708010b0d0b040c0b040b09041d28 80
    0x3c10580c2c080810f5200c400018400d60408030110b0000b0300c80900c00340030340c10075980003804c980946116135006218404548802d6607a0b0024885c2c01c1c4e0340720081d00c3c0c1188100c0b1005140341564000d141c865800c110100b039012520701c00701c42c181c2c2100e030040d10300e0605000084400794041c201c15160ba10050164810b41090346e07940c0700045102c2c40d0000d0307844800b14100910140010304031010305142c000100040e84403880807000c120350086204014145901c1c2c440e541009517048001e42c2800801000400c2040000410a41e03107180c00b110410b40d2101d00300000da2103000c0c02d201c0092a14095a400d90410602a140b51410741c20881c0102e100d010180b8219000079070501040d6014080c16800c1d0701302800800b01800c401d100902541c0410380100300c4080d41d8020040c810780d08500000c0078060b020350030f000a0070380e44074082d5540e6900c018511441e040391000a1289240180440c01c01d149181000a440c0c0c0780e1014100d0601c014100c090103c0140c6042c587c124064150324001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 351240386 1250 351239136 351239177
    0x225030b070503010626011809050607020105060315010b040b0a3b03030f0415050c061e01060e030a11030c03070e0a060611070306020315030607020d0f0512010b030403 74
    0x4600640d140c40c2c03298503000000f0100600405102c04101000d0740011001c6c04840c01c190644424001c0341069580442c40b1400600344040042d00a00429041c0401185d064000c18060b040440c121045114440300304522031100b8030480107000c41c02c020401403040b13000d0150001203403c2c1451224006450640c04000e01105502032074810703a100500a407440c81c0940c00d040c028242c00441c10500b40c80c0ca03d95003481640194810310503000e801800981c81841241c0400c03260009407034071070808241f425000d2031080711441488445800105460303100f0141c044001d03d0003002050303240040d4490031041ca030340c00b01e00b03034250161039980d131034030380341000100004e1035660107180d0342c0d1900184540c11211150451400c02c50882480340f240c010004100d016a038115400503601d8862408480040c0d04000307001e60175010306d00801c0041a000701d04111507154a46500c40d504002036001c584500c181001540100e100034010f02107115200301450740540f003400c1c82c00f001c41c02d0f8025a43c6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 351241636 1250 351240386 351240391
    0x5100915020604050d0e09010902130b0a030506030d080606030415110c030d0b0303131802070c0305031c05061c0c12050d0306051804030e150c0106090e0d0225030b 72
    0x981c0c402c0c014041080b2041240183c044054603000e02d10044c90000604c40d0103042c0305503880e454010032201c04405420100034001e14255501940c0e43c5c42550015000d0241142d01d14840d00075402e0311881e841c05960420710070310009000c10f265580f5940da0102d14800f40015904c260350340e40042e12190070b1176000b080d02d4040c0200460f00c0d02091000390056030b00302a01300303008cc3c00c00d2180c0c582501c0006448810341ba480f61002c03c00b000c40d603040740020b0040180180c118246802c002050207008030042690b105003a980400c1031002e40d030341c02c003030700c4007600c1c02d17034001490628240c882c0c01d5a22004c84458490002140d0803555298241600c0c034141c4416506c54100011398880d4a806215481c0208000d5800300c1403016950186148403100a000ad420300095100c0c2e1000d513580c081042c2d00003920105425201c0100002c10382c000d00e01c1d8090804400d01c5d100200d410207030001040c15131113400b81d00615000c00040c0c1040011881804402508180300e440840050340b44403a091 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 351242886 1250 351241636 351241679
    0x706020d1b0e030601150e060a05130605091f0912020d0210260405030a030b0f030706020d0311030906040f1e030c020a0b0c15070504030605010b030609010f0f051009 73
    0x10700b41c604041014142038069000126905452001080036078210442454800c01261601d49600007880151081c0c81090214190112101008501141c021002d00795001c020344440b204001c01c5911684030302c030b400d044034001c26403008080185e604145402030040e0320250082c2e0284000c1d40c00f00d0000e4065440183c041800d10144800e00c803501c50601d04840707810803107100300e82443d480b100c2e2a03111b681e1411040680760b1200c0342483d01c94030a201d01504018003220645076540314001d45900c4440c0643d03001a0511201007495242c0c481074a000704a5000a442d40d902c1316502c4825406070417034202c510180390b400c8442c020904109602695000b40c8170396200020900c1000301d2035040d600b08011088081c001f655541c4000610900c0418400741c1312182e9441f040c0d0191518002ca51005018034100720000c282100450040d501031442514002510b03600c1e5025034000b403034a400313450040d1a847c1d00821203450712900000140c08242406440c481c0c8440e01d60740034040501490 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 351244136 1250 351242886 351242897
    0xf02060c0d0b151e0a1d15030702010522080904050702070506070804060801120b04030c03050412030201020d1a0603070e01140d091a150108090f03031f0605040b0706020d1b 76
    0xd0f940c035041400030b421280364410380750454000c8040c0203080e66000004003c0e610f01301b01765154480e00d245036005e40216881c181c6903d0400c5000f8040c14084881078211040025286203021034405c40b08816644120302c07a083c5007080c400d0000614006000c4401c500c200c420004482d01c49200600180e0301402070690364900b07000c03014200c124103a110600400c11920420049071001940540041e0305140940d110b0400e07041c12680c3d40142d810456000300e2000040c1d040540550082c0b1601c1c241d80e40920031448106c490184070f191852945400100c20000200032a201c3c0f10b560050142c1410032491954640d112251140c0054503605001950b40000400f80680314104110640401d0010b501d40d281905040502c140328110355070520403070f0000314034420b03814080003503011406c1c411643c891038168000e1140500d03050700410120744810000c6882071060b8210390a83c0c60507a00d052901007582e440320001e502c004130448030309940b6039a9404510280200084000380c41e940d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 351245386 1250 351244136 351244147
    0x103020c122701090e011202030705030d020106091a0904171e220807050d1703090a26040506070807150f06050904110103020a0c0b0103050307060c0f02060c0d0b15 72
    0x319401c1e00b240407440d5041c000c182c041080140d48001c03200381564040410403c030a01d061021914140c901c0c0c012540c14003e0030894002c1c1a0305604c1001250003100e4180541005850340a0354603000c4080250403811207400100812040f140a03004d405c03411165501e4a2000307080580705002d5841e503d45c17542d10004a01c5103100404024210a103001204140c0d5949419180c3d5590302481c461980150707a80c102c510240183c5002c7c2004950b1450321261703491030140661500c035104140c0440d600010060344904c80c2038a210075006c01035000880501d81030030b242c2041866040740740c04442000b410400600091f071034112402d04001070900218a003400b0761107a0080c0c8075181c00c400c1c0644459020030011500003001403051040a00b00144d641406200c211440b0908010241410031080c00001c1000302c004010460f140c0a0741e41041032880c0302c0403c4400c988100342d5400140e1005000c119107290400017051040802800008c0311880500422128003070940340f1710009001085 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 351246636 1250 351245386 351245437
    0x20114030a06090c2105070e060f0408070b25021309050105061e01050d050604020f280801120320010608010605031b06030c16020a140f01031107020103020c12 70
    0x40d50703140c6005403c11143c040c1065000e02c84800b030b00301d2044191074940b03000c100c900f40240c00700b6401c45006840c00b40d4414490032b0580c1d00c0d60051003001880d02c990100040c1121014054500b40030b203540001a010000c60004901c51a402c00705a03442440742030202080d88240c440c801c006441540040366900d48001000641c4042081e180c1305c0c581c5030324900c40580e07800012264980401c0d64006010b890b4600401c1c000d00500e90f289407000303800a8402e00a00d8240c805c2001d154145a24807072840d4404021a9091005e10a01d41c0c01011100360000190049650000f118850001881d0182c070701001982961816400402c0b01d03550366200388018241481094088004680c0e140484020302c0c02282d0076100080c200c000400005c83c3c107045000b03030501c0c2d00c594583c0040241960a449d404000d108120091400b40f140c402d61105c0f40940d40a4043c1d1030703072210f0200e0464142001500190042d502484071032207180200100755140c0c00842020381f0030007841c08a901590040d164 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 351247886 1250 351246636 351246641
    0x90f2c010b01050a0c080d0e030f03040c0518190905060a060f050603070206060904030309020405070f080604050405030405010309081204030c0c080c06071202030712030e12090319020114030a0609 86
    0x1141c18104401086040c0029810003c6641500d0740140305a682c4c1b41d06000c0d0100800d203600d1800b041380000181244860203500c00340d40a20b004a41403d455a0b4507410801c100070340e401c14108100648000440002d00100c801125080300c00000c120022159610780c14031400701e4030300b0f0609075541c4042c0041001001c000029120554080b803031801c101d44040d640d418002c0049205a4003140090304241c0302e50080c1803111341c050010301050903d1400a4002c0c20b02c044100002440480041c10501e0700380a0320740555003100c05589000d04100045028208880c0d042c2c5444004202c20346003041410040745c0305030b020b640c66100300c89052902c1e60307508800d03030f116040795800543c5c0c0f00c0b203954501c41140c43d620791107d842405002c08000680c2180190f94015000c42c000303444c420649038258000700c00840e01c010030355407005447c5d1080c8109000e6080b1450f016071017059500c00c1c4040200d607071024103005062000101e0480359007150198001c81d40c4844083d1107482c100072442060 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 351249136 1250 351247886 351247901
    0xb0c0d0b0d0f060e0307060c2001180b0705040f12050114010f14040e0d0e0a0f06080402130b10030c0206160503040209070e06040b180405010f090f2c01 67
    0x115a414031100c4582c82d0328481080092000d0940f070340e1500724282c010000c0040f1801c143c2e004400744010100c410000c1c00c030020038140da02e000511060310b00140441803062a43c0c0c1541400103600d06074260f22101a040b1000b0700d014103002080002040d44004280c10700000c001054070400c020303a0a150250075240303c682540d111050a50040c0504003c070515441074903d4114507151950840b80060090540d1050b01c2d0800d002d000201210507078040141d00460005903198151544d460810040a40c0c544c852070f00052034030408103005150514440300110002c4801041e54498900000d0105102030310410100380ea80c9a0a0102e94050022941c00785002d490700c07108586401000d081c500c80100001c2c407640d1501c00007406540110004078000c0c1d800343ca4a62640d8849a01d8080355011200d21029400c1c0342ea030b040664549402480c1c1a5140c0c803a6161019281a0040c0050281c60302044121500c078046040b048142d0000c41d280c103a1940e0b86840300305941c0310800e0865080 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 351250386 1250 351249136 351249139
    0xa0e0a0b0f06030a090501021303061a031f0504080d05010e040309080303061e0111070b090103050a0605010519050c010f050f0604050408030c09030c12010615030501060906030506030a0b0c0d0b 85
    0xc0781d1840300c0380c0c0d901e4107407030303101d0b041031804180c0d1140c0d494464020300c03d03034031040d198100d007102c04005c1c018a980030044100d0640b1007074020740c02c19003c06a56100082ca160341c030503a00e52211806505541001d50807500c1696035608107030601d1a284141e034001d17000b45001900080c10481456800b1031201c0040c1802006145103086c0100401c0044044a00b070451400103150038400503440789140d10402c0c62000c064410140c0c4600c0c09006a5100f9038280340040d0509020460b4591148212400c64405868551910158030000b040d65000740e5542d6041c80024403180580507020301074040e0b5058440000615440c0c69080303820031040c06041140114680301c10040022456030403240c0040042c04466140d800e0880003d20304024244840d4114459030f1030840d00b5601500000701b66010108482404d030b585101c201c0850310248609400200d82c840304001042c043e6101c2034001102506070340d80141607071503503411504191041404d0707907000256000d504585218540c003001d070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 351251636 1250 351250386 351250399
    0x11070605270108010608130609080c0f06060f091b16060f09020109030303240b030403020606030610050d14030c0705010306120f061104150c110f01020d0e0303090a0e0a0b 75
    0x3807880001c0031490140a0f40c0c09214010012440b501c12098510004036481201030043c0341c19460100309a0b080910070000610a05844090f0b120010a001c0d00c2074201420a07021048034208020000d07001601480c2d0550f1010650200310807808014900d49030b5580061581c50b6080c90000b040381c4080310325601861600b0081030050b070703200f070f9000100c82d003500d80490300302d52186862285681541d045030300d5411484000038903450340e101640c4a64040e03001d4608a56403001490b44486003100c0c03d800040c0c002000384031134503050b1160180300c0d01035511003082c01d10f108005407850748070034507100e015848280b041040d580d150041ca00602400000007514603100d5640940d0041300c000000c102c0ca45515510740c111402409540041c01c0c80e40d84141c80c0484a817002c1c0c01b4407461175050b145003403007820a0440342480c0315031400c08841a80201b03607041c12032104481c1d82c42c010304030903814007040085481503540c0744140c00107040410f2189019040161300f20040b03a8038150305074043e60 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 351252886 1250 351251636 351251707
    0x106021f0207051f02040b120a050105060702030a06181a0f070318080c120307080f0c160f0606080f01020409150308040509070c080d0b030c09090304050d0311070605 73
    0x1840400c01c1142d60408000049180b500400200c001c1d0140d50060706951f0800b0840e0080c2c001080202030041c03803d00c01c104002d9880e0710501040d84030f002d40181d055840220f210b0300096050703100b445031120052150080c1203042c1d03224100180f0207460217141403607020900100000168400303400103028281000518048800407180e400c02c1c0f607000c2c029550106031106102e00c03d10007004070840c007000362a907a02d449407028162800540d19200202410800102c0e110ba140d800c41c0c202141d191446d0100d840259941c500030265100200c400382e40703464000901150400c102c01c0540c140000158446d400d112000d0211044510546500c983d10701d020008981264121030681d20242d56100a550319440207880380d00001000a2143c1c20000d9440b0840c074155200c41d80203d02207040d00c2541030107a040000384101541d18a03000e0300704100801a0780741c0344204645540c0720741040e0340079400980c01941410516030001c0049840051289070380184101ca400c1071110059001e240031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 351254136 1250 351252886 351252893
    0xb0306101116082b27081f051005090c0706050a0203070f03060302100503040c0e090c01030b090403141c050a02130503031318021b010905060a0e1c0e090106021f0207 73
    0x103000a0506010310510704005002c82c42260010001c4c2c1c501000f107107070141d544040d1503940e80346030a01358001c1c010b10581c081f604c0036180200382c020b1040c002074a072110b0421041042d800d1002d8440c6103c10320410462000901901801e4410669140700603180d01c1c0c1800050212001a0203540804d03107007610500c01a91900c41d42043c030850352070141e45070741d00d0740ba25180c00c0400d6005004141135039420000044000104524101000c0ea0280013030420704060104842c01074800a001c00c038070050914003c0e84650140c203400380b00080034080c0c0440d2103140710840d10150b9903201260380014030140c4821075445400b00504080c0d0085281c19641c03045c40070410894010080c04031703004a041001c00c01d064042c0c458102429561a07080d52691200714000c0c4540b8000b1662170044600003160030545208010351040460007618001400c01d4960840704401e081c4042802642424410303d5221242c2c06406010f00790001c02001d500241c00402100f025410411003074010000b94001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 351255386 1250 351254136 351254203
    0x7111506042f090a080f060714030105220204121406090a03120207020f06040b0310140a090b031213090f0203060d110a090c09050f0402040b030610111608 68
    0x1901c800b009001d4507100f280b4009040d203411540082c6a500c55030300810106131000c54124040c001ca0b48440001142540d03040d4146d000c240b04056200d018003521110060491080f00c0d01a800c00c4001840c05894030611140d0b031854a00a80760300170110703c44403003c83c082040320f41158080b401415000c4050ba4001c12030010f580003400c15540100701c020440d12610651100344800400c0d0a40780c60b15400100b1494208031030020000d9140d040004000c00444030400306850050b004101c01810312004002414a000f406a01485852096070101682c50080c011603000c00c41c1400940e860f01041d602544c0b58041c1855926204006010080c0da410822015140d88600c201801035100d100161103821281c1c403a01c507050034948501c4015078028aa042607400485155103804c0c4a10107200403802a400303120203800c800c01c007040061a00f03c00c00c403c0041c0d51700d440480788002e4140682041d80300300072030080c030100d100240310b42403050001060f1406c1071000b10f001a071058911420 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 351256636 1250 351255386 351255461
    0x90311091323060703050402090a110f180d0609020a0801110403110103091416140d03080903040308040311090c070f03030c0509040e1e0607020705090711150604 71
    0x4216010601d003982425000c610b849101c95080c203494003850901d101401801088504a10450384c1c1c10010307905440c00d100d11803d80540e080102c1c141800d100841c1c1d455844908140c80b9615280400e031019520b030321002c62594490000441d10201510507ca10000f803908407110590401180d16840480b03d0259021a0341110055003060880001039004066404000d40009000c10104248042c000380341008a21901c54032060306070ba945200b49042e05e8803c3d4654008002282140868440d002d810b80040f1240c064919140c1d49a0315210030b42e01c00c1c7d02c11921a192900350200318a0720380070407548441c60083c02441d10440356500c003c0c00303151200c014203156035071502541c05480340060b0703152854090020055a0001d0000954418031404581c015050b00090900d036440049409130103034441c0d030020b181460400742040f40d120320043c2102c1c02c1010801200c00c501a0410140e035582e8000d041c10081400c00c03c0510041d6207811a00000d0958000f03172144100c1c3c1456803d42 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 351257886 1250 351256636 351256643
    0x601080307020103152d05060405010219060b0904030201090b010e0712090501020906070605010510030b03030d11120a0e010506010207060906080411030a0305042d03030c030c0507060903110913 85
    0x43d030fa01400c89416409106802c0b034040140c10074000712146d0586d1074990801042d08180145c02940ca0342009000c0c8510700031140142c218441e482158021050885040d0707115a04c0492480d66100118040706000c80b01900180e454107061010302411020050141034002100c014600e4184c502405810004440e0010a680c5600401c14401d0039819600c8803a401000c66680b080d183c1000f9014110038014244a00d403030040c4002e00030301900c204182804007401550508608800800c018004083d0450090104200c480c03080380000710300c2481400c3d0700b60300041058071029141d0031210008e090030705550107000203010054100c02c09100b202e05034600340d0040c0d903c81c42d20350704443d40081402e405129030202c1004268115016000382c4443c03d020402e950001030203d200543e001d10560081c0b10f00010910120f44a5212004114028207150f5081100c0d50345280c5402d08070392181002a40d80c90041c0104002c50000022110045980c0c02071800c2c02d125006c102000100001d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 351258992 1106 351257886 351257891
    0xa051804020403020d170702060f04061803210513030c060807030207170306060705070906050a0b120a24270c0f030b3105090601080307020103 63
    0x210103d90b001410007402562503180c4490520250a0110f400801004210090f0700c40304001e000400140600581da60300d4120000e20302182a404c2d1110b00c09000300c100003180c4007140102060003000e0790400c0b500c0e803011080d9200c0c4581c04d55803c406244840020501c0798034070700398007241d00c3c58031041000d650b0030300114100d100d404401040032809154907041002d04001540d171120010f8021172030f051443e101c1e0b0785840c0081d4040c0e198951905402c1c0b0180c01c02c4c540800c000c0584203101420480500403071450601c0c000d000202140d9110300088a04061100b95099800100d0001c1c50702c5460b01010000404d088603c8000070600b0600c0b500d41c19160300c552610510a0b60b543c00c082c004c80381080b805048943c1e05240d00c400e00c00c02d0031030192070003414800ca40319603000c1288580012102d030400d1300c50040210005401c0320004000c1038030003008582d03c403171342442d00 = true := by decide +kernel

theorem cover : BRFrame.Cov 351079136 351258992 := by
  have h0 := BRFrame.cov_init 351079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 351079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 351079136 ≤ n) (h2 : n < 351258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
