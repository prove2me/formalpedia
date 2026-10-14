-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0908
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:51:17.85736+00:00
-- url     : https://prove2.me/submissions/2ccfc791-09b6-4ca7-8d0c-595e313e6bef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 163129496 ≤ n < 163309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 163130746 1250 163129496 163129507
    0x40b041106040501020c0d0c03170301080c0118150c0227090105061c03020a150605040507020106031223030108010c080a05010f060f021509030306010f08150609060c0105070302 78
    0x41852854514030a03014050a110900281c0d0300014035112100703080b074003022508498030f480d007110325031504014a80c00746581001400c14003039001d18140e0b0f00c108141d550031044170004660102d03203810010180c0108510401044d503040c00021b0340382040789803040d442d9000e0f0b004600b54038031080100d558030355a001d49803810046403800da600302004200034841814110005038842124542412118840e20010300805008018901560341d01c101c503070074003840e0850803100802c4240305581c060707410a4001003040d032041c4158410383c4c0d03010803800c520118034441112a0030700c82480c284021512040c48510403406c1010314000c010541c0085005036140c0001440c04101030401c444c168248001400202303c406030340015180c540c0307810a114080310404a2500c5070106203080342d40d800c1e001384651000e0100086102e01e20a1b20b03005108144c244081712039040c11a02e0b294080e404612100032031912070004c00c000b4030001c1003142014840740b4800d086650655011001c01d500180 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 163131996 1250 163130746 163130753
    0xc0714010e01090b0d051e090102070b070f02070605090d14160b0c12030a020f16030f0903030509060906040b04080a0b01050f03030901030e0f0a080d0f020c07171203040b04 76
    0x1c42100c0d20710030f103080d4002071301e041e02403492806901200070100b41c0303500c00a40c0303410114014903400090481d400c00d81b81000c950123070003540030796810b649107001ca80020b21803d019401980e01c142195000380a8140341400c00c5031b16410410081c2c2c1d22190144030000407550780c02c003c001d0002030b03001911210b400d075101d000c0c4050103a4410040c5800034015040100130102d0340d940c084070f0845029541c3e81d500f0101200a1243e02c940702001c00d0003003070f074001c20080414a007003140e100782c4400c441c540328014284c441403c2484018002501041170b02203e040940c003410401c10702030030701410142c0780c20325260300350015089a0741e183d10016901080c0b01d60b2a09860040406403041c58801000300b011076202d01c20b00c899030381450348a001d50036100b8410414418164101340a507080d0303c0c101e1401c0c040980c000c00045034803d040c03503403001d02010325100b242c0380751a80b6002044018a8076002c0503000d01e41ca0710580d964002c20545618a0500d0310046200e40e1240e055400c040c501807a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 163133246 1250 163131996 163132007
    0x4050c0927071403010b0a060c050a0212031c0203061e0d1a09070b0703080606070f0501060f170f0703030c0318090f150f0909051c03050601020f060f01050d03050c071401 75
    0x1440b11320a0703040030803c14854507a042180c054a01c0340c03074028440b16a50409038600301c51103038002c0d0408510080201501c0d80270014100724200a46500828181c0c0740c1c02d041a0702090b40c00c10340c0700010740c2000003603203103030224000f400d400503108010240c415203e200c5002103e50904000207041d4042210b4440e00380010005000d0071400d840c109902c036100140607201c000d01c5280548030008417203042c0841400d004000075400720080c802142c81d0b5940702c070111850703c07510b0103810400b074001d06031f22400704142100301341e140001d1110500c0c5032001c80d40089001015024024481c03030780c0c0025240019590003400390035001182c11407802003201d0440d51420451010304991000c14821400d101c0c2c0030320100c0d004803070041a5840700b1304000342050b00442040f00f46001e209502c401c000e8054101c10322800098082c1e51001e2251840b1035100d0324111500000700d008600148024a00006506e1905029150003401c4c4082541c885151a000b6048051080341e60702c1880741171360703005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 163134496 1250 163133246 163133279
    0x140408041511030f0a03090512090a0b0304110f010c0503030709030213020a0909051801050108060106080907060503040201050d0204080105041b300303020f0a0801090c0804050c092707 81
    0x600d0a002e0803800c14103081e03100d004501c540c500c4050009000d151171403094100d043c185800c2400d640c01840c011002246a50294460501801400e90001400321162007038034400c0744c0100740d41d24400c2d401c004001c40c507103022041c00d052268844881010503402c10140d80304681c41e8882081803421030040107807100c55980d01001c041d0040140031402c0381e1102c842d804446041d08040f03804d441d144040140390061030300022041d0301e450300005001c480082c1c2541200c0103a00d400b0000d0b12160349441d10369580b801103c0c04107000700003142c0154030500050403003021040c00141800c0d207a0110070300351201034505071841c0c07002010740800035952480200003013007540f0812151001c3da1082100e40b40f0400c440011091200c1c15040c1418004e4040300c007580003801c0810f580c0c01c85240081c101940c203001d281c5a161030007804d00106030203844028001c47e049401081103000b620304010850000825400c150b0180d6248020055100316222b03d100e401200075204181c01d1425410b61400c61 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 163135746 1250 163134496 163134539
    0x6030507091b0804051c0201060504050109061d060a1d0612030a0f110a081b0f030703120b0301060306020a02010b030c0301060e19110d09060c0f0e1314040804 70
    0x40211124040310503100b604035200b80760512402c40c0e03685007002d41c14905500003c401034040c0c09000060b095041d407101c020755034126000c2000341d80311040c031070445500780030b0300c108203a010103030000030f5412002240e803040000300781c040419101d81016111212102c46410400c40c032801340032036441d04000da0344840e2001c0340290b04003c079401c8018100c521242690b8107020b000896180b4807101030218101d00740d0025400c039580c2885e4204100000d1b00a0504205030280100c881c644d810003004449110b034055480030500d980e52242280140110718074694590340e99007000000540710b001524132003d031600000b40840103030017071500b0031043e10a641d1003640352010034014a4602c0399015004040c3c11408004034003016a21305c01449040c000f800d01c0540030403030215100e8603802050039940300f540148002d121519003680c00a250340c52a0020900c946049035290911140c5510200c007000c1b0040380c541c03419000008281405c0d60b003036449490024003071028003179265141032803210 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 163136996 1250 163135746 163135751
    0x40510050412230307020c01090e090d08060d020301150609090608030318030c0601181a09040303020a05070206070b06091b0712030e25080a020f09060103020f07060603050709 77
    0x800c0e60ba07420b600e5030085056800d214041c0003c9101203000c0151080010450b80c6495890401501c080c1d61118400b900034000b407240342001c03903a02c80450105008401c04d0000349212500100140c8110200410341a000303180d400b14903001d03a509005001d01d045041010f03a000c00e0074020002d0020095400454145040c00c204011001001080700c0d8040d10240b60080304500c07a041c4242103103d6101c0c4d10003680704000010440401920f900b0f0210411620304120005440b040291800d1404c00402c1c0d11189240020300440d010380c000308000702580c17901c0b500d00241680010320541286500382c500c205114200807942c01c0030301c4100d8000c1e15100d00c8200651031040414600e10660400500210184905200d003602a800c504a110101001c0d41c50140401a00041d9242040484051042c0351a07000038211000700340a56456006440488110080740c144041924040c000504045d03080010f09944103114018018072442224045400c0780b841c1030240c9480c01a030015041140b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 163138246 1250 163136996 163137001
    0xa05010320070804050916030c0f020a030c0c08010606020f010b0a080304031106040e070e040b1905041e05010611061b030a0b01020a081602120a080406050d0b04110304051005 77
    0x1149080351a510460120079160380d5899803a104500340110781c4400d801ca05440c0a001c07220841ca0001826004241e40170012100d141400301c0d402604020010050b030410180c01c0040f03403007030181000c128011400300e0030f205c0e0f07241d801900312102940840d005800c210b410903036199003030060110b24441114800c034210b00b00b256242d100c0c03040780b00003402c0c01c20103c2410341702c0d2104410b4030b005100c0d0070900300091130708030702c05080721807a02600c0d44240d01d05006c002c501d2512040b40840700740007020500e00c181c14641480300030001c11034030708034500e96407042094005440c003815010b0b00306039681c15014840819482d24010000e81518104501048c05050902744c0d8415694050368441000c03c4c0c1c1c0781e01e800141e0403c0382d41c0310f014020540020712403136040d070030982d101d500c0c91080c0c81c0040e845003040740c51511340c6c039440e02c01090190104000c203c071600c00d00107410346820f194030014000e0301f040000303000c40d4080c200443c01c6175400320401080c0702c1c05210001304820901030900a51 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 163139496 1250 163138246 163138271
    0xc09040309050105180a03060902040e06010e01090c0504030501090f0c0f0605071716060506030c06041208091f0309110d0c0b0307090b030f101d0a05040f08180a050103 74
    0x402aa0150904101000c20b6450001080e45c3c201c0d40380650150218031a552a81042030141254040c1030703008a00303200b07540404110009515049910307281030810207134200200b14024081c20022942001802e0102102090080c825103208900c54840202c0c4e10390149008407a011403641718240c4240e00e900100000b507045411035140c180d1082101010141d850aa52000d0042100d0351030a400c030141403008000d800c2d41300c01c1c0181401c50455908103403480c20421240700700c0c014540310141c0b0040c90000502050040c011142c40141980040d81c0323900c0710041000c00c14917182002035140c2c079041062050b4010380c0051500d007a604d80d00d01409585466160461034421101a80700002c0043c0e20b07a441161040003801e091050b6950b42d04211416008840e0281d941100d050314180c3d0026100180441c2d840c008280c403881c2c12102d030343d0b4a0003100109030003001628800c0081c03840b400001c203410004d01d020001d0181d0945200b120005000031400c25400ca41c0c1854035000e00103209 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 163140746 1250 163139496 163139507
    0x9060f060f12060907080c190302040b1c12180e0613020c07030302030714210702010905121b01020f031210120b0412180303050919170c090403 63
    0x3140655a00040c65400c401080e24800c1d000310201180c0500d60034481803840104941d0300b20391582d07084480a0300c080041000b01503414000c80424103488000b0401070034160400c214414000304048004000c404040c4441109000116410003087e8074642c1e04a41104c0050041071a103810000501c0c100300071619400c00260409100d5054002d2079000340380725804950380030541078103544010b0f9827894060b650f40c00201d403c944003d44154001c0c14010006001000d40042c80302807001c0c82016101a081540800d8041c0d04000340c00700041410303128040d0f1101d8028804004000d00400050021403d0080090140c115040700d1540c8041031f10020a5900f02c07654018864560741303d010150300c00c032000754030209030102d03445104030034044000110341c442ca0190840e1480340c154030340d01311481440a00000c840c030218070820b0005c02e11403000f0300344c1c8041c003030f04900501140720100da1002a9a61007030b15200e030000194865130303006101520384031809440904da24289540c5c040c01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 163141996 1250 163140746 163140751
    0x110706080c090f04150509240d030210150509160f050d0b030a0803090d0503040c0b07020f04090606060905010203070b010e25170c070b0403261e09060f 67
    0x14000049541602e80c0d41c0d80041c0401c102008008019000f003069844224500310711400e44240700c48030015056101711255204515000700b20303e5030068803502004102c0000f440203404610621000c8003540045104282c0c01600746040c0541d214031b400e04004c10740130000d00400101300400c2c0c40f510103d030400c180c40444205403c0c001d1300c41010818070310092400003009036161092906000511400700011400703180201c3c1036036051050b80c81c00380c03100d10051b00c0003050564620310401a8290440103045403900c024000b840100040001505441810909681c4143d503000104065504001703d02c00401c3e00380041c60520300705403142c00b080300c4140309450300341c20b0300000210100d5030ba0f03402090398a020f03564030180d0b0b0a1880001d01803604408038400c5076010b803001c940018010410b85c3c2e03510b03500030803030320503540d85907400c0344d419400e02090401c02070150381008080341200c0d44140b04401c8104600e520008446100350b6281010f40040280c3c1c00440c1441441c00d800300d060b55 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 163143246 1250 163141996 163142011
    0x70c02150703020c150f120906010501021504030804060e0105150406050f010e04200f0c060609010803030a0b011e0c15050408120c130303180501030e0c01082e0611070608 75
    0x1800141741145501062240e449111845400010308015044071814924010300110302140c034940e0300c400059a9900c64200c0a50114400384001000280f0903200a6403042c4214170100340280c1c0e2010071400d6031401c0c1c033b02c400000101112010682494401c81b401000c044400e800d20062f070200282440000b41c10090141e905c801c804c0d02c0c5034004541c00148068030052141e610300341c0055803086a042004400494011080441c0d400d190480d10107068600c0c40c0d0240d4611386840d131820005008a20030103050102c008680b01c01403807501d211401c11050f90b180d41f000e915451621120041e0a46801c2042c1450075017031001088420007900c440034000040300300c0d41e444145040800d4020000e500900040d90440402016800088031000b000b44c4007152102c1925a001903040d100200360064080c3c0c0314101c0c01c0019803041d083c1c160040310a20140304180e1124a5186d12541400c5500b03004c0717000003400f0041c036503000c520021a8070401d4042c1103120300340503005202102c06042c10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 163144496 1250 163143246 163143259
    0xe1501030c0e0d140a1722050906010c170a0f020c030106030812070504211e08220b03010f1e080703080714070f080c04020712200105070c02150703020c 67
    0x3400001c2c003080a00007441e0002500c900e103100c414121006c3d0341c003502c0d80848091104a00b442414501d40b500000e40d94020100b040a40c0c850b00110740e14000d00c00f058421a62111404201e40242c00041840034241d07500c9220443c00140060700d00501c0007882d50084e0b1414a0400100d00c8030b500781d481400c0081c501b900d4031f4030b4140e011034640c000e81d00070320841103001d04c12010404203000b040f50500c0c27107500c0396080c2500d800b6002c0504441c00320054404e030350070030000240c01008641c0d850410110034904113815140c8491450640007600010400c05003400140403601007442002c0a00540140b547c10707103420300080701d880308040d100c02040080b020407500d08102c0068141e02c602800703071089900340b40ea507040c0d080119005200d039060b24001c0604141490410303000721941d5940004500101c06011701045440c00201c001c0002c1c46d00710340401e004846400e019460189246a48800600280c0c0c010098211240e103411450280200300c03200c0000e40201d00200b2400084442 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 163145746 1250 163144496 163144523
    0xa06140f061e0a0c0c06030b1509042301050405011a040308030c0405060d05010e150901140102011503060b0a12150f060503010e0303012405030f040c0e1501030c0e0d 73
    0xd44503000100003051082c40700440d01c0c8100d1607108116201803405901e98458040d83c07001e044d0212096040a950000941d4200284a1320700b140148440040500f0008420600044040c9110001c0e0b21030710700040c40400400040c41d2602805001d8020b1b191500b840703d04000c50b00015110f54400280304010110001e2044040e00098400401e07003e041c0695070f0f0710b0310700a1070042c03c09001da0762032070880ca0b0100d040300310301800c5c451071108003801d4191140d00305003101c00c29901c14a50300341150740320075007500003092284c44100158421000071445800000410030071104c0354000ea4442c074400354140000c1f440010003c4040810034100041c503400d40c560341400f60074207400042c0c00d903007445900c0050900010082d4100c881622030491095802c003101c1380d410034000703103000000300148041113180071241d03d00c0b500980314680414000b40d90b41c9400320320311030445080401e6031803410340b0929542c160241540341c002c0c5d440d288011000003000602c50300149600a4840c00b40000b1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 163146996 1250 163145746 163145767
    0x1d06090d0e030a020901060c06060902190302030603010f0e07033c32010501050303070f022b0303020d0e011b050c15010e090d0c03020a14031b060a06140f06 69
    0x400e042c01350040d00d00b105643c1c440c030002e0602040b22104840c250b14040001907020440c1c4241c030360303a0410951540343c0d01c10303285044029400c0a000654195070750110300e020411140308141001211348060080300d851070414110502a00d40d202c680c100c80203106803003041c1c02c0c01b4001c4540c1c174444d8450042e0082800d00302100c0601c482960300c00300d081c100020b4021440400c02c01c40c58903010007484280e0326907040c55101c0c0100c8000038071680c0800301410052405c4203441003060b1700c00501001035250403420541e0702441c1c500c142c021a0b40041d000c003401c1d00d940a0200e00c2884080240000c41c40e9010002c4600d425045100c02c010001c03413200c03a80c0e05d052200d500d04801183c524005561505c4e207802102c030342a681c51030300d8480c101807008820f0140740320985558164000c2d09a00751580c60300c0c3d40b4424842002c19040c0403c0100340040540000801840c2c844400107004038070300700810301e04070f506641065411080b040c5900c4203030b54580705251122041942d445445806414 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 163148246 1250 163146996 163147003
    0x60611070e390903071a0703030c0c05010212160c1709030c210c090f0112060605100903020a09020711062a0a0302060c03070503070f1803061d06090d0e03 68
    0xc0e08040040c1070701c41d148400c240e050000d40301240c01241582c002e80c0c0d0300c812008000072174207400c000121b82801900e000c20300a5010041e1682c9608000c015020306958071800c80c1e201400d26130702011500103002c1c100846104441154446042030914040305464141d45000320841f81c200041e40040c5a10303041e10180032802e018040609140c101700ea4442041c620f02d0f00310780d1100c14610030720b034001500d880c01110240c015040c8480504243e400c040f000d10308083e00c1402956126211080022207444102c140700700481c03c0e076100c05174141513104110160100e580448502401404a031000c80c2c01da00192030701d000c0403900e00e0781e00c6000d0a02e1410080410f01c0420303142088056040382c1c80c0c0003044140005100c0d07407d4502e0b03682c44600d040094003090b9100c1c80081d0701480001c0d542d50003002c0e05a080c9400341450200d0481c484084541380d0700641003290b03034a0310380c1c00b012a00c4402c10243c0c2444003035103000d0041031030100c103003030b6589070b80305450010080d0400c11103c3c552010b2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 163149496 1250 163148246 163148311
    0x70503120c0904060f090e010c0504090e1f0b010225060c0f05010e1c03020301060c0f0309080601080f070e0903030606130308040902120603010b011e050f0c01060611070e 75
    0x60003d003c4c450350359014000b50f403440e1060082c014101075100e12540e0061140d00ba0700c580c1034582900301410540a640203100420120b40c071407190b60130a203c05108d4507003080758603203040c0c3c1c0800c006049100090900c151304844504d41044806504114550398001c1b00c00e44c2c42038901000d100b801030404811006160101601c0d651801140540f200c03c00b080301118101c98030040801f6100c10b400c218200d21091040c03000142102c1030100009101958842660b8007a00d0f0200c07519071601c114600748502a40520180d50120545440144084c00f914009080503c10a1894500400320369140c0c07000810300340c4560800140000e04407030590802c0c0203590032900864456482e51030440080d88060a1000400301c5034000580318941402242c0700948181d6a50f408420094100043c040c07500318480c00f409000d1001c448000380c2c00300a00384058100f000812010316006014004030388001c038000d42030700030103003e00bc80715014400f2600001100701303039900002e01c0b82c1c4c94200c00316803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 163150746 1250 163149496 163149499
    0x30a020a0c020d0c0e07050309030409020901030e0105010f060906081009020913020a081b070c050103020a05070f150615080c090d02060d050a050a14270706020a0314070503120c09 79
    0xa21510f14140300b00100e40700c054402500e02101d164942c00c8058405000850714465903600030402072145c50126005040c0503901810042000303c1011b0b106401e4800980150700ca5004503030040002d16486000c0c81d000700034034204200300703007040b2003212404c1c000d42c06245952070300019031541948401c108071744540074081046480340340f040001001c420307055941600400051203080d03080c24140b002c54080d035601000407c003c030300e41001900a9080902c0301c400f885010f0040c3c00108038894401030000d8883d0301c003100d90710a8408018110741343c0d03408c41d40039540007013001e005160b041b440c2c0a80007103001c88940d88443d4404002003a0000f4448002c6d00020007041001d11800150011400382074480d03c02d1045955103c1403204603074010104a11030a41e0802096640c5408030003800403042c0100620206130380703403c44924000c03440c0d0003000140e0058200e002850790020002d44441039402c10b0b545002c8950b02d619589029141c92601180000c030003040b100d4081000701d902c0c0b10f00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 163151996 1250 163150746 163150759
    0x40807050d020706030c03110a0c0303110a110d052a0106182f0901140c0613050609010c0504050108180f03070c080a020d0b04030e1903050d1103030a020a0c02 70
    0x76054002d443e40c0b4640b20310b001007802d00100c00c0896010b4050700080040403000f890500c100400111881148041c0035000e1559a8944490f201c80a500415108a003a03d4102c0030300001306d9018607103e0800150800c115080c49451600c0c1029400a5480c0200b506440456480701054900510035030780712071040c11a0f20401a050160340c0c000503080200c0f16900340f000c0d201c0d5001e488884e80405504100c0c030808005050b00c41d805031030b03032401c02422454071505081d10304545d14903181080d0390306074420b4011920391007004001c02500c0c1c2d001800c00001e01181c03d00d420050100c0c0140d001d40c3d03040c80000d8000660b24042c3c18108000c01c2d0040d021120306200e10100c0c5900d036071040c0d0013581d014020403000300f003454000643c6030659601a2001c4500380103902c84007050040640202c0070400e800d40c0100b81565080981c42c8800e1086a00090303003441c520340765180000c11140241486032400001c41c054402009899004010640c0035994040b8154100c42ca01a540c1000358044d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 163153246 1250 163151996 163152013
    0x321020312100e060a0b0f13090c0e150a050403060f141518010803040b1b0703060605042319090503130608131e060b0909150106030b06040e04080705 66
    0x42c080da615108a44410325500d5040d100c2c0400d02c02040030303e0240c4051604200301c103084200e000342c018843c0342c0e06165040b6840b07403030300091001e981c030610040300000d01014420721140752120340415a0030072044041e01e81001e0003c040c0c42801588405003601e41c0d038480c20b201e060380c80d4110099144035142c0f050160b14140c100c1f1003143c49011941401610541ea66402c420078507070300e4905036920b0704020750400c1c2c40d1100300d10490307020031141142000450550030486400304a280d0103940300341d401050320360518041c0070440d48000c15924010714080d40000e038003405152301030303040b0103241c3c1e00c1c0c4d4803102207a0103031025000c140310050551000040d0820460620303941301d07042d80c00582d503000e22903c891800621440c210000506803640c0c01150f90f94111000c065141c0c5c4901c03940e004158500ca04000800940e01212001915007141c00e0390242d1010610b015800341207242000c01c028600179022400d80c1c0958010090068400c0003c02c040c003d0903000c1c1d130751040d40076003200c0041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 163154496 1250 163153246 163153261
    0x6020901090b0c0a0b150901030f080c030a0e031002070b040b15030a0f02090f040515151c02040e1908070204020c0307080c06011d0f07090803040803070c0e010321020312 75
    0x1c00c804d000654401510b03401040e10101000842d10001c1c000401002681c0d0954490031005204140100d8011008105d4840a0b407800e00c003030721251089450700d0420310044014541000840041815001e04c1003006d400051200c05400c4d80045d00140311038144d54401d40340d0500c0e0017482020652600c5104a500708204000854210061089d42c48801984030055540d6680e101941c00400725041042c0d004130400d038801e010f80d403201c0c0300110903d0009075480031403400c070500c2c0d410840c02648400080700750700707260181040308206174008014060951012806d9420900c100415020000540d5000d40d5502c2d01aa0100400700081c2c0ba80e685151415201950115490600c20300a5100000381a40c000d60300c1e8105401d030706d101045507078074041e0741110044000c0290b01445a44a000300d503e02c4101f01920241480340d00450341e484a500b4410b000700d400d98059007071400640010300004075030b54a90b0400410107900700c40080c40a1406904601800000306409610541000700c0c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 163155746 1250 163154496 163154503
    0x70c051f150905010e0c0d06050409033c050a0509040507090e3403140412031d0309010509060d0f0501060e03010b01081807051503060406050a030b0406020901090b0c 73
    0xa10100144070021566a401802910000d12a91490aa1074400a26a0322020009040e1203401210014036142c075030700000c0031220282410f50010308164021144802c2c0c0d0344601c3d1130104565040c0745e540f001821000d042e15483d007525002c018000c501d070082140030710305680756480000c1007400985450040241040c50b540705001c5513402060101d281558160003c804040c0550710500c00c0554655203060088861610b000c100b5039540200341d080c1c981c060045005074440d54206c228480981002026204c089a0360440c0c0c01002000f180100000000c0342c107012030a00700551140001000255940110310b4500d41c154103086500c01c1d039403400d0b0721280c1695025241d61602c00d2a500c18582280c50403401c0c50b0100d40c0040100d07801100703802074110748040d56000c4402071500c0d04042404143e1000c078003070071002c02009002c1541703054000c074070250005442890f0860300c0d54650309245903000e0700207842a6030008100c107903a4441c248800c0a41a40c500155803070000358001c5030b5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 163156996 1250 163155746 163155761
    0x20a051c150203100b03040f0201030513020907030506190501020c040906021e4b190309020906030609030403080c0304210b0109050105060f0d0207050f0d090e0c03070c051f 76
    0x104070120100108904031410301b9280542e41000c00c80e603209105a00543c000d041c00341c010800d004040100d20011f07a51050350030b120303804076500440c4504001d4144030422000000d071800614490300e080c01075903400141f031841e0b4401100c011410b0708850900ea8004d00c503c40c01c011030341c034001c001d0801240c1214000d040f44980340c44c1c1c0a00300c107520304000c0c0c0103090050400b15015032100c4200c90b03400303600c0c16000e403003800c47d941c940c80e00c0001c00c2c0380c03600c40310500c9100001c6a11007040d20b042d4a0101049584440107030054141d074a400e0081d5a1644210b010042c203101d004107040f40300020400681c3d0251510001010440c41d80d40e00700404031460b454122003005102c40040781840e00c60041c2c1d8122900540102e040041003030404000d50084087c80c26031681c20b03c00c12000c51030030015031482a140c10f01501000881490040524660741c00001507154540c040c0a0000010b00840f40e02140c940b80a8001034401d180c8541403c40380c00900d05016140e100c0241c01e404030343e10051 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 163158246 1250 163156996 163157011
    0x303120606070221060907180906240f05030303011d040c08071214010b01050a0f030b0a09020c060a0b0a0312120504050705041a03070504020703170a09021c020a051c150203 76
    0x3102070740d40c0311000d0781c7d4051900661586c416418207035050100d4540041c0c0c0c446115110110f05000b0000c0010181018030000107540024214200048060b84140102030b003801d070003551940d81006101103607403600400c02542d180b01c400000301030007001030901028010041c1038440c4156105c03441c0c100d03996104801d642802c4101152210000c0520508454030010303101d40c0e003407801000e0b06841480b283c1d60380100703064454010301070a03651512103034081c0c00320310401600c3d100b0010a0304c0c070b0400d005094a28161803c144902c9903640d4020200c1240d52144108003080b0303070820100c98400c132a6414600355801c1c00300788020018045502c038280c41082d10104020b80c0c12015180702c0032044a081d94058021200078030660038150018482c040c021304002ca510881d15081340c0d9072001c11159484c105564542006c114605000c1821030402810110036002c2c841da000141100d0341c603c507061203264a07501500826000060940c2d406400c85000b02144141402600c06035100711242d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 163159496 1250 163158246 163158253
    0x613090506160206040f03120b03010e010e01141005040906110a090305010c0e060d0c200a020310050f06040b01200105041e12031e062c060303120606070221 69
    0x41d2402d44001040c40c46942c004001c580e01d81c1c8182ca054403e2070002d41020041070301e81c40d15044a4509006801d08803001d0000018a01b924004d128210381c200000c2d0702c0101000404d101901640c408c205054810071100040d0000c00c40c07400704010140c00040f1740c0302c1c0c00d0201d20703c88200e4100b030080c4112405030000f40013044409004031111617580036803030762140701400038242e0f00f0707810742c004010016542442810810a540361000c1c13040030020182c02e961040c0c80060860405012041010828540c14407090805841205040d400206254011945c403101010b02e68880c12125009280e202e03020041020860b4085010b00411902500c904901101000e0035004c14184044000e40111031580d524216002c100c010b032180301e44140d500c000305909180d102c901031050030020000540c8040c45100a4545031204d007200c44c15010801e001001045081e031004022558421000d625401880d681c3c50001200360040741f030003a410644000568111200340103e2102070843e00b0210b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 163160746 1250 163159496 163159531
    0x90906030d051c090507080d14040605040e060d020a08010225030f1107031704050306090a021f091502010606082401053010061d0105030613090506 65
    0x5256481c0103260340c99001500400900701580c0d804680340e00c10090100c070100e4044241d031100c030f24001268202e28030b244c0000c00303180c06a03904110100310072012407100703a0503d4a0100060024003031032040d5003100c00440001415951140004a00310754000c02c086159901c8001c9a8004c0d009034205000408840d13807005800302418041e01004e81e419903900002050102c402c562101941d40c00800511600030003100141910310140321181ca413a8a0750345484c0361804052804c1c802034284480c1d904111b24110140e11744540c0848420100c1e81000a000c2c0621400c460000c0e147d80111003140c500391b06c0b044841e9040d040035045403415a55074900303071100300042c1c084042601d40c0c0004410050185c1700b95500560150400450b10b0022a6100807148503002d40300322401c1a07105641c00c414204081c8221100314400a40551f03d019204214079040c0c0c007840c2041c04000606000020002683d15500c03d44840b107001541c00041c00b002d0031525107581d035804169807070200110301510 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 163161996 1250 163160746 163160749
    0x1150f0f0b040b1b07080102030f0a05010b270102030d110406030b060309060112020d08030703060305060a020a0207230303040308030103060f0b03100b0102190b0a0c0504121709040c05090906 84
    0xd80d015101d0f035410151501d19400c22007580c240c20a0740d11074490007001c074006508142807001d503210350756000054081e4640322640400b1120140c01c90212182c0c1484112031030000c80010b030a09850954104c1e003044e80d600300503440c500502001034005428170300030031300610240d4050421070303038651401c3c000380c0100c1003004070b1404201c54030321465002000403c0814034000b00c0e90f00850010b4500c00d10400c2030740302c0d001c1c240e000300d6240d00440d46070842001000000c000850340b04206510842c180320ba10100252903540310f00c280e800c8104071150880010403600880e4407841b100808407070b6134903907c0c43c058115400c248410380b4003d01d01041455607042da40502d68407408014090031031050f22072940c400900c0741d01c03500307811031051b040b2032102000c0d031200c40b01055008014006052501c3c076004015a495580a001000310a02c001c203c1205000544284940d100760f082000010201100803207000d00200b059015080c0040c0d100d102e5044002451016800e0341c244460307594400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 163163246 1250 163161996 163162019
    0x90e06070c03021203100306060e10081207020f0f0a0e2e09020318030a121b0f140c06010b090f03010605060f0708040506070b100608130201030e01150f0f 68
    0x1078081d000d40c21120101d00f545071400000e41d80910840c94020040e0b480740c54000880b620354000821200d0140140905030f5402d814080c02001c070800281351828800c07000c80894003508000a02a00307000b40390001c15034491402c1d0140c000094040503440c0d94814140c01100c1d000d42d23200d15860145507001c1c0b040801c102151000701303508400c80c0503e91501c2d01030b20080d40010b1128000310390380030007144000014001408004656502c8107441926402c2c80c0007212807000321000b480b21000c0200c40f4041e0000740c540605012400e1030341c80c000100c40c0088061060a00442c242d0051000104001c80450040c00102506540e143d410010610506080b00c0c554020a5404030060140e0300620ac4524001c01200740b00e0b842ca2800c050f56400814066003001108030f40d110134050400c0766406400c00020000c0401c1e10f440c041c1814030300101214446440340c00b9040584505240546800035002001c1801b0301c1c07105110203030354504030300c070095000e405a04442406000d00140050001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 163164496 1250 163163246 163163267
    0x1107030b010e07260a060e060f101b030306031703190b06040815060418081602270f18031c060305070605180a030503070209180304090e0607 62
    0x140c451005900388a28003406000c0209000c0420556590240c900c40c034450980300b2288991240a00342d0900305d90081c00e856540e001101011001d0040050380d640c0c0074846520030b4000d8518100302202004212092215810840c0407007004005c80c0d4101645075000300b0449010b00c0700482400f54040e40c61071030b0301c0103850141204142e0a03214924054a80c4200044d41c0c004004c03e2909076180300c0d02d400c000102030000d410210070b40400006c2c0c00e0500800c0030324424000d400c0c00c609480c0e9211071240c02640824a642c0007150281811901d0b5010300002800f0180009161403088c10b0303801000000440d01d01d4401e070884170200d03203da58007907005c4121040940240d41050203070612030300000f50806800301c4080d2504000400b1480511003040a4551691030b03d50b107503880300441217a00001400355008684120040010800100c10b45600c958100c40060254560702c1c906481408078280c41e036400e000c00203001800000d286e00c00700c3c003841440146c0d00c96603100305040d105400341 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 163165746 1250 163164496 163164503
    0x51b070303120e101a0a0f0806011208030708060f04050a1e05101404140112030e01181202030c09090c01030b031917190507020306060904081606140403050a110703 72
    0xb00c800c96420031081c5c1210003c0c0340e00703201c80003041c04020001240001d4540c40a500c04401010600c22481c0c1400014050008a205244003101e1a5260310766031200911480801c155040400c14a41d5201030703032080700c1c0c00203006011504040851100400d501401200a8040d080061003441d00c18028684550340b1602c1c084030003490315240b41c000b0a01d0881c0d1541c001d1b03458604100c407400e24034205006e0003044e281012203003881c0c41c01622501c00450564148030f40300310085915a00344104005880710b20084200407034251000c0382c80e19140740300c1c442e48890800304021101a0000f0114a416026030701408110100014541c503410b0802000090980543c031400c0803071001441006111100b1054915011000d0100000002ea034445a00087c1c00002d00c0303001c1d0b20301009103507001081102c920006040c03950720002980700ea2050810441d1066141703100b40b0505500980092500b015207103400c0c9014a8000c1041d032040c1c0c1480c2c00314845c04800020310741c0c00500e010035641d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 163166996 1250 163165746 163165753
    0x31b090f050f0301020f0c0106031703010b030601050a020f101e140f07110a1a07020c010e130f02040b04080106170d051308030a18060c051507051b070303120e 70
    0x401c4180700245580407040d40d0559001c011440800e030b00400100140a0384200014646082d03250061242460f24640d10341004c052005000ca002640e0841e600040c09081450784c600003440d040e81080b0440034a000b10740203410052071406401c1c0c10036044075907241047d58031800e000606038103c4420091340c2d0803a8140800082c00b0120040301c0315044541c905061825200300d40f9030501c4c190540204403a1660b9012180034100c44141806030004c1703250000c1c01502450400081c0340b600700303040d80d13849180b2409250780c0e84092584803103429032001c80195622501c0382e41c0340e501c40d80300e0f10a001280d032801d800004c08030140c403007a8480384a1030f405000c0c1702000003421100c0c0d8111f101d00280d24441a2000641020100010104100a03803540c8940c403030800c0d50348260758220741c0550103001084031078100065020510039800e5495041c40748441d00c0d240011a2103000703590300384000c0a40d1a5900d2084400000c4c4003003241d129a0751003254030a403503031601c2600c1481c06094103a52 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 163168246 1250 163166996 163166999
    0x1110d0504060213060903030311070b0f190f0510151d0f0a0e060103061703070818041d01110405310c0f02010b0a0e01061101150303031b090f 63
    0x4100340c01450300700c1c0c0590400744c207100e20380c625031410b001507a00038008214030100410802d50140640944c1c0780000c2c0e4424141281078442640c1c80c4802000d0f08004002840001e41c00d4880d10902c840c5440ca641e01003140d10485032a2000820741580c3c030361007004140300f00041960f400309003261005095651808141c00ea8820b240c85000e80c0c01189500071022402c460403500c40603080e80c020440c95407210b03000d050880c000360807140650028540c8400c230750003020344d0450000840300c4041d07004129550305c2c0082040d02c402c000d90000040d07803280c10600e1043e000e0090f028032020608180b40200901c011083c0c00c0010b600c1140f18954000b10044500c06e070408100c0202c0e803281110350084c0000c02511062300301200d5845442c00c0200390380c0800700641c0b0741d0910031a103508070b095803441640e41c00e014500700f0046051207641e003080384000710f022101d02d0030b4221400480003101412280d07900ca240c042c01a2205080340d003026541000c0e548002403140f110401152101c01c4140400b5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 163169496 1250 163168246 163168267
    0x510201f0c1b140118021212030115020a050111030907081f1a030604140d022a010c050f0307030e0f010f030e03070b090a03020114220312020a030b0f01020111 70
    0x4200c200103441c0f1180600600651400078062003a518a0540580030350842d076104100d05840c42c488102c040e80d21245070b186000075000203e0707065504e10320000307a440c000d400c0b00300c0c41d00507011170007081ca50800c09480c078240303217a001843c014000701d01520405600c84400c5035a603021150141074103088030700703110755201c0e00c3e81c003800c000c20814003041d81e0340052002003031410034180c1d403c6a220070100c00d800310f100018494084180d0303662026111000c4a120703400090494194034488901e40401031011a0b0b000f49600318041b5480b00580300c1c0c0200001e64140ca81d040300d5819000b140300e81b21384c0c071440d1800c410046150201616040700c01c1c00408001c500800480404004620080201c44041040300d06018070a908000c01000910300d070703107402801e450f005449009008146024002044040100122010400145480d0321042402d0440c2e000103145200381050784001070000c0940d5241d0060788691100390388203c03040d02c0d490012801c03100701109101e0911428051a041d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 163170746 1250 163169496 163169537
    0x110303270a03120e2b0b25020309030106050409021f0311070507091109150904060308070f060b03030c150613180512130510201f0c 58
    0xd1050140a8012254072503940410314880300c00030001080d881c41041065162000307981c80300c480d9100700e201034004220004a42c182003034800421a050704000075625241070341440500ca10000e4410240c241940d4029480740d21284c0e05602a509044001c500d07400d10307028520580d41c0c084d00f8404582604441c0400004080c1c0b0803000b015128541d20100c00c3d50540a403c0480c051b030080d01031a89054080b0045507900441c550004106020711a06a1342d90107030420059180c15a55545071884030002e40144500e40004028482c003013102800e2041400c000c044040c4a41c00c200a54500e10f0101503483c014050009003a034000410b00e14600c01840110b03400c20303000340410000040d6640908213030744c03c416145641a501e41081d40030302400308000120000103450751403404102417480e42a10006000c1c4500498214421000c0907115518a4011030030040700f45e070008030000609515002122030704c041c48000c4c400e0081c4002c1c181e1144603041d64068070b50101c190f40d850b400406 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 163171996 1250 163170746 163170817
    0xc030601180302030d050901120507020a021207150815010207031709030f030d05040512030705040603051302120106080f061302010804150c02070911090102060106030218040e0307110303 82
    0x38070160440000005071010001c086000103903894690311a0105400185241c50410180e00c0f594104420b00484603004221030000a4050b10090041d642c510810740c41c200541e4002800d18190f15a0500c4841d800f44c0e1050068502c405c005a0080003170004980d103c3d5140800342002400715002001c0c10a00801805400809007d540307800c242071801e070742540c220600d00c0f0412901e403420402000b00c140300940e803651451035400d05608011000401e58040c6010f000b0600d9519001b00d09001610f07220301c412581d0003070490344040100b8180d139002e800c0510070700a02c2d1144e85004650072001143c40c6109400c081103900e10180f1607001101c0c80032014000361042d5440d400141e01103409030042c0783e8004100e0b0010072103a4904140c03101158210034017140882d00912020860740c0c1d02007a83d030b04480e014507025844900310903224844c440100300c03803981706240420208404801001800f0024004c020303070508003800400b0315440e40300d510000e10f0020804104c00407a082c01c12031014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 163173246 1250 163171996 163172027
    0x10e040606140a0504150b03041a01060c0b07050f0d0504050a0204050a090803060607030c05030c06100501050a050a030b0a0506130305070509010308030f0703020d050103060b0a0b130b0f0f0a1808060c030601 91
    0xc01b0150b564002c034081e6401a50261441d400800401e480d00c1104c010860042c0654600030b0140c10140d112140900c3c1c02030304c05020844d00180c00902c00d5121401e0742c843c800c201400f00300508040c5000341d41c41c02210000c81c090b0342400002090700500d4440e0044041d040540d06243d0f80d500c0e800c0250907070101c4011410b11006824000103e507040000c0c01241d03071740c40020541400c0c0082c1d0003244044507406103040040c200070509074181e000c81903442d24103030390402044107526000015090890741d04100c0e0418004215805038802c0c6600c050204c034081c3c1d040c1d90141d5180d200340030b2207600034040038202810410214100c2e003088219150702c4030b8145001818803414481400a5510a0340151002c3c1e840300b241d9812882d1582154000708009045280741c6002c2421000385910700e88951000c5000110b1100300c403041481c200c44102c0380b4000c40b2507030740000c0c0d10081d0220000c8041d00b00400101d51002c594400c0004103980144002d074989811740d40c2c0c0800460300941d042c011903 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 163174496 1250 163173246 163173281
    0x1200405040e031905070b0108010b010519020a080d020a08100302010903021201140408030103020405060904050d0c020f060406030c080130020f030109150b010302070b040821010e040606140a0504 86
    0x715a1360070a0030a4003150303840e030745051796810b05040070740d24908180c0100310310740d240409200d820f0ba00803044491890050001c1d403480070340a0409d90400b00511000f80149000160107112603885034000c000303902140e1940d41450701c0d1a080c0241000303482c000280820030580c401d10151405410308144004c0a034000300d4550b00380525110180c8050300e003140c0301940400184114603180c081c1c55031040301035130440101d182c662295990380d01c0c03010702c071b40910000d803600700d0075900c0e500e000321703c0c00c08041d0040f0341d955a1044018018560000b210001031404000801c034040203840c90101c101518500c014429805003440d0788802103507008907400545032060580ca91001e0246407200342c0501c7e1080d402010300c068050035900070001d840d04242c410051000002e209502203500540c11401c450b40307071020b050300074222004624441164520a000000c0c0c0410f00381449449188100740600c00f541e42e400c0c00d55107604881e58080d9001c80e081130b05100508040d4000001142c003d47c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 163175746 1250 163174496 163174507
    0x6030a0f051c020c0111030a08040b090a02180402030105070207060546350606090306040620030c221502030301090605090c03010b280203090301200405040e03 70
    0xa021401d902c0302140003507040724890340415030b0440c00341640d2044000c05940340c00c0710410002e00c64000284003c08045107071003c1400700b8410044049100da0141000403d203c42100510070f0b80f0007250101c2c400c2d820400001c1016101041c200102c03805615900c0c2460003107042d005952804c441070301d0300d038aa14080c8518115500300d100001a884030000e51607402500002495800000d040c0110080320801520491400c009a604213070707052404440140c858400190070b074801d503000c0eaa410b12030441880240580d83d8000c042c1f05100462031644600440e100603440d0000702c0350100600c106010300030b8480c0d428030140501c001d030b04034000707076481c1c031100c680b10500b01070194080181d1001c001400b08100c140f0484001d000700307d07140303c200d00d0b29502148291205004681d500e03440440d41c007a290f49107510f6a00400c1952103003198500c01f1000c004d582c1d401c0a12054425801c00c2d04072141c01c400030b455044d00304241c5080030700e050b081c10140f0000e410340c80180c080710b1004102 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 163176996 1250 163175746 163175773
    0xf04020f130f0609061a030a02070212060709050312030f1306060902040e0a0905060105012316060c1d01110a1a07020f06091f150902091806030a0f05 66
    0xd181c0500c1c035507580d000800e003948902031021078610b9000b0444003032401c6014404a034588403035140700c0e417202920700d0352607031203010fa50007a0088407002034000c3c5000c0c407050885071000c42c0c080d204003016034800007010f076039034101340e541c502111104c42005c10401c04200d60051429203180d0000446420117003110141c1d40d034108945441e400f02c1d0000d41d002c60140404440a10305580040220000b8019900c01d600c0c1c03e034454606101d52414451022003103004c001c40182604c400034201107002d61070b0314102041c06500d8a002800700c400d01c1c0b5103004264030501801ca860302c19004100c03507800071101d6034010b40341c2d1184206000040d10860030084c0000300020031820303102d5603403c0703c25040e0400b000040d26261310504104205d40201c003c002d08204001500000b02e2029034801000240c0c01d03d0701e4000304100c04429080415003200883c442d40150000c1055100c20f5600409440c070b80d0b10620b58040044e601e20381d040d04180701c07041c041340010340349503601030040042c3e416078120400d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 163178246 1250 163176996 163177009
    0xf020d090510260a0b0306090d08060a0906060c0c12050706030b01120204080c010809060906150a05040507081009090f0602030703061d0610050301060503072007030807020f010302070b0f04020f 85
    0x1000c40c41182410f4042126281c494041e1079000700080c4e000b0700860500803a21900c0e219035103060402c02501e076001494580e41c21000800900b05408104000c03922080c008106113804c040c160b0380346212500c0015201420745082146903081005810410304040c000c8001c0c01902d44407a0400011160f0303172b84103001505c0140000e041d20002841c106960302c00250a05a0041054003180c1006080103d42280840c007180d103c0701c01101480020401c0000512844482d0040e5400c02d01e000c080200703160b008402503008420030f050070300d941580d4841c40010b0b51810350340103020b80064010100019011b03000385030403003418107003c18051b44940d081d41c04081c00c3e40c8180460010301c8140328040c20540745103011904c15150140c075541c140070f4040e20030300c4041c0003502000051040d0000010408030328001d65807580e000d4a00c8142d0b2810b00c0200b0b80c100290980c4034580414400fa55036000b44215070089a0000c0c6522160790b48002c02101eaa200400a903001042036046508a503980d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 163179496 1250 163178246 163178297
    0x110c0f010201020d1802090105010e01090311031501181a01050f0313060c0503011403030301032117010801020c070b03131401090501090b070210111b1911010f020d090510 75
    0x385c1403030000400b8010040a5281039100c0e071305220051000c0304140c0d92203a40714060780d80020310b4110301c0365004007003444c010404090b0080703c0494000454481c1c42160304841b0203811107010310101c0c1c94440000740014240c0302507400724604024144046030700101650b44519404072038030b0b403201151240003d50304041e403041d00140b4000010300c035600010007440c0344000243c000714110342c15640c1c1d6400008441ea890b84c5062135142002400920600242003194089000d52000e5651040400c3c083c0d085084a480c076800b9020b00404c002528800340c80c45881c0c1c540507402044401d85580e11481490031131751300255280d203a03113008503100f4001c2c005450711840300e0441030304d00020000d06040316001d003d400d040c1004a5504074a1855003a6003050345400d00c3c800014289400746450300e400f244402c0c0d00c0c04102110b110a10581000b190100c440c2a21400380c1415200c2d401c80c3c48119141c0c48501007001d031041071161307052000a010070002c0318107000340c600100010148401c03001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 163180746 1250 163179496 163179521
    0x619030f090f031404120807021c031e0c05070611030c070602060114040507080f0c040f0b03040303060f0819020103020906030f0a0b0409021e0a33110c0f010201020d 73
    0x40b146400100340e4015090282d140d10b084181d410b060900841c160050300742d600203010b0700008181e89040d175031810600c11901c000e00c892504152402d01e0082c1611080d041000740342110b6141c2d00158a018441882c0c1c19580030026011140c00d01000b0f54000d03a5401c0000c486100c00d20100d9007a81d0108640030180205400a0440d0761500350001050102040641e0140341440c0500603055003000c0c01c05c0d000b00918000103810b0740c40c40c0020a82d8050f982c444001003180480010344040000300440c0100e019950074032800340c50b124107403032050300380c41481040d41c002d04800450714106460304d101a40305240c0540b420302c042d400100700c1e803c152210208801070b0824080d42c4040c510031120500e40a4400f80320003a110340024107900c0444150f09400e491a0018611715940d40c60594081c00c071132007120050304840c0d40b10384a0381c0b251a1510007180014040c002000e4028048807104898000040600250060903c010784001c4072802d4103564080c050030380300520303500802060075171 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 163181996 1250 163180746 163180763
    0x3080a0806030c01170403080403050c0703030306140f090712060b19020705030f03120a020f0c0610060206010b07021905040f020c0c0f060405100c0605071e0801050619030f09 77
    0x20304900b098200305641841c14107200a501540451081d0355071450f5025406085c203030120742c2c1d6401d080d01c03544a07160304c280660142010200416425500c0501614040c602650b070510204050201c02d40400e07448643c40819000002e80e6184036080005c01440b24140c0841e42c00c0d586d0040b00e00e80d4024054604402d045e00421445a613810080140181000c030020030442c3c81e1161a00d403207200c2c801580901054074800106110026011644201d980f5052142c0e18080c495003d40c4541c01a105854081100a40081d290f840040c0c114143e0f010003942910317044c190b0342044210003080c0e1320512183c109680000d010380d00c6108045080302018070150f554660035627000d06100354180203034841c03138003114100442c3d00e0301d0054505484d406e42d034414282c05107070420750b039001c2502802001c560501c02041444c40c3d00940100c00c052281c4c41c20800c00203507034416200c2c0e200034007400360040e81c10301c409030407100f82c091000c00c0490340b400d00003482c0c00e82c0300300e04050b01c2c1007440903a500311 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 163183246 1250 163181996 163182001
    0xf09020306070306141306080703032325030e0315090f0f06070507020d06090303061a0306100807031103090a2d06090201031e0c120207020d1b03080a08 67
    0x2414030600703621241a00c1c04101c07403800c180d085c031401a0840c07400e0780503007015440d140e0a00c1141d030018000d06100e104503205255203190080091244d000400081e0b102c041101402c80b18030700903200c1170310442d40e0780200006204031010340c542069a05904100e030300c491840150701c2c284200e110802401c0015200c620307001c00181d183c911690014140340c2e11040c8001c41c0d91102098290b00240e5078940039a0311801800000c00400340040003031312491400c4e8442c0101344c0c06501c6031040741d111403e2187d40400b414090350081c0030448200c0c3e00701c41e61481440489224030700c1250300004500f8006072003091820803d10700d40040390006843d50001034040240b1094855441c00016003080f50030413001580c020955064010b20018101520f0700c844604580c003e800501c541640c2090340a2010910701009000e00803440b01200032901d20b07440d500c00400c50f4000c88244580180500e480044580d40311030614151516440032005c03120710103c00501e40c00001c0604402c165280304150 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 163184496 1250 163183246 163183249
    0x60b19061b05070e0604150602010f0f02040e060420070308090f1c030e0c041e0b010206060f1e0909060f10030c1e0306020d060905060402090303040e070c02040f0902 73
    0x81c41c00a01d08421040300d01e04400000e480062541c055030a0401024919119580441c02400d8440d00402080d410b4440200d0819030540c482d04042107811410f2003e80d9040403810200c1c40b8602907a485000d100001480b281003980026414500320908400d404c1c0940151100542020701c04400040c0309109110201c00104040f07200302034400080d109500d000c03c460100c6401c141d800b8014544c41c1c076088400c4a5040c004a10304c1c0700060402c2c440d4120500c1501018035103030309046a210714000d40442a9440010704034030904010b0400300e1600c0300394040002040a04061552840008240d000039840e0001300324003038106c00005011078141410a980002001040701c0c11420114030100080fa405820220484841201000021303d01c1c11512054001e907410240c0400c3c0002581410b4058943c00b490440f0480c2c0410440354403448204000e921034150402d40c96403003484140002d1031031042035600200142000200c0492075404130f01aa501840070004069a401d10384055 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 163185746 1250 163184496 163184507
    0x1090204030b0114100c03030e0114070f1404050114040807030c080f01020703051b0a0c08030d060603020f0a0e1c0b070f1b060c0c020909071505040b09010309060b1906 74
    0x9041e403000c445803501c80b0300c0f012aa41303050688a41041286d844940000d00d0b000758011245182c0280080c0001c0192605e400100078055481d80000380341550f034000454070403081034404541440285280070704e09001101c81002d26144801d514804120010758518108041d2008602c2600d000111074502200c0900f8075150003071050141e40100b119400095000d021034600340040c3ca584045e604035200c18074504114070301e005088182c003900c00b250040c0000040d000a47c146030042c400a5121102182030b40581084604001c40604c42c1083c035900681c040c2c00340140141000c00c0640d6000034106601800070300a83c0d19039004400d00020544c00703210411304281c28240362002902244d11038460580801024090a17030b900c0c0d4001541788688000c1895680062450721b482c24890107654441c20503228204041c03000c1e82c0c0c4c040406002d842a10121a04213132002c0c102030040c030040d009060051000c40d4003d581303042e04c005643e00c00350300d001e80c0407185001600060400c0e201821 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 163186996 1250 163185746 163185749
    0xf0507020d02060c0901201914070803090d050c060a03150e010b03130501060b0c06060f010f08010b03060a0302041118040b030d0c0203010e01060e1518180f010501090204030b01 78
    0x854000004022114180c001101c481d2042803070120341f04c1124800804240030003243c00000c9001d000805001d5030601c0b00c106c1029402280e044103562691403019645901030322071100145c10920a036141c925040200060050098050300c0031200c19200003003103940404021000300b0340d1108030413a1869a034540b007000d0f04400700310101030750410000c41130b00d000040c258120030546003607883c00c0040030b410600c028010034030030310340b0383c2c500d0805991615002c0b02c3c140c0c0108207450001d001c0c1c2d842440c4985100d901034035101200d9003032904402856100800d0a50400200c09000006840384c0c410545800380305559192540f480101615544c0c0100104500c2641000b0840b030300c5070390204499450840c1400d240c2582505c41c030210f405041c032040342030b8040d481c0c00c0d1f002942c00c3d04c54251030b114110f0700140c00c945420400800880161040b12414050b031020001540c0e81d072107101d10150724002200b110940b40a5134511802c0d243c00341c000107100c98000c00c00700f0402c681d0300c64150 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 163188246 1250 163186996 163187023
    0xa150b0d08130308030106050c12030f06060c01140106050a030e1b0402070c0f0806070207090c0503010608091e07050307050d020f010503100806040c0e0702010203090615040e010f050702 82
    0x2018200800209492200c51014102500c00101d02c0c2c140e0345107400030801140d01080c216101c1da580c0c400a08a82c110102c0e4041601800420200141c032510840e44100003203c54840780d23858050034007066801c880d428800741e65841644061829010039000c1c024841c40c0e8070359580d009402001400c0d40d00e5103c40800f99032010800c00a0007503a8601904a1343d410341d80180c5400c01401c0941e8051125803042001380c00c0c940c40030a01c00d00214001d84108456022540c00301e694500c5da40c111030751014240c0c0019402d00061103514441d1010a0700103880700b0441d9108035812800000183c2e420748071121941c491481000035090500120008160464050f1021061900031842210f035808180b41000000000540c1c001b00310000c1c80041c1243c07804840c0d19241500c1d01d50b81c00306007802001c00103049107002400040c03050003120b1040c02e1940c0641029240c0c4046000242554800264000d0b103948151103845424820311a0f8020030000201d2141001500a0b0801c001d0b008000b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 163189496 1250 163188246 163188251
    0x3120c0a030b010206100312050d020f0a0206010e0c0304021c060f0501060809070e011401090807080a06050a0b181b0a03060e0601020d051e0706020706090213050105010903020d020315090a15 84
    0x126020b06c2140d103422a40c00281034401e180301280c0c211a5881445004c004061010850350f5110181c8006040803010a80840b905662034800c0300c942168112030f45c030a403120800000b001030415503c01c4441e00300710308007503a00c5030540c0e540105580c0103101d0480041e070340c0c00040012692101d22160400b1600d006403160030304010790848821014000c080d07164014201c0d0380400d0348640385480041c420301c81a0350901d40c031001c0c103607142e01c0f001e5001e03290300d414100404c80c0700c109481100f003c107100410396034410010b10340300815240c00402607c0740e444000310f0034070b80481000040400941a54000540609101084c1c102200c040c0205046620804610145542001c101c455503120702030714107149040640007021b5031160640c000e001c507001049800800c51140c1081c03403c40d100f1140c44845014400300d5800300c40092040c140041c40711070041015003041000d14505a001a05641c8034401c0a140690421001d03111800d59601c140c440c4802c3c8403000404c0c40b000d90703841606 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 163190746 1250 163189496 163189501
    0x24030b0607030c0c0503030c0d080106030b0d0303090501110c03040317090d0b100b1801120b0a090b01030b0a03030c12050c0703080a021c08060f0306011503090503120c0a030b010206 80
    0x3003100d900401000a06012a400c210300a1052085090000709002421603a49030781a40709251500800703100e40b8082103821001045d218020b008a0030482800b07004100440f18984040340600b1250009640655a6405a112140c0c010b001403a0b203081c100000e642d82c3c0d140d460080c9064004d080f8407120100c09000d441d4141c2c0d20381e005041d0390340e00312584007041d4a81c00c4a82d400e6401e5036100c42d8040300001950002c40c03408405d901405003090700c0740450031845d1280c2e50140d698901945920282c00c2e041404904210384c080b204001c010300d00000c116241c1d1000c60505c2c1c4440e001500070a0080f00754004000b10060b680d10398904501c1c0143c10a0407101820760b5403140e40c00014103110740800c1c020105442004145105261044000403c10680a01078640001070b1400c60040c106286c0303448540c01c0002d5020b04031007406407041701002c043e28088004150700241107409000801c4500721880b00c2c4080140a0800301511076560440118064101c0708400610341c10754008008 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 163191996 1250 163190746 163190749
    0x1f05100302040b150315090121080f07020618040c05040b070b150402030720010c050f09060f0c101811040c120c110f07210c090624030b 60
    0x161401201da040d1000309400c46a040000d46125804018648039203020040140c0148610b51141408000341d03400000c03643c03540421031002011410010320510396003420000150031000500d0b00d03e00d10040300342050f901da40065a103a1002c411903280d00c9482401003440e1404c1c0c80341e100c8040d014100a86480e140040e00138941c002c0c1100609542803040014205c554a0110b007620701000610071540c81c6000e120191040e07004580e4000d03d2413191100680c0c1001c1441407003c4c41d145034032294205440c501e1400c5140d441181025048030091111031091107400000d01600c8004d0710103481a03015000d0380320200c512110160725980c03004148100490000320081040d46000c0d100401c41e52000710f07041d02c0c0001001e201c20a030518140d12044420351000c110003030000707814140c4041c00d864013041c9030349214500800d50030340f03228001001d40d00443c80a400c0a140319401e610006551220440119656035020110700f801e09544c0d40d010101d400101a20840075084c03c0000340e031b0510 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 163193246 1250 163191996 163192021
    0x90507090b030603030d0906090605070527060702030a05031e040501050f0304030903050706020705030f01140619030b01060c0201030f15090f1107060902090901060302010509150c0d021f05 83
    0x8160014001c00001080c40d548081c0102c1d00b42c88800007051103140b440b031a0140051413410000e8070040d1806020070041803003801200e03079150000151803034040343c0f290321030401c10340400d0a40c0d210400300035160050b101400700403040c07400b03007004d10f80783c20703107600d240901c000c1c202c1562198140401052185a0300041035030b551108410780191243d980c0e150648000040d5040600f25100300c000005249600040407019680103a01f40d90101e1100c0c1c0210b402e0b5814001c0a081d22040280040d03071904002103c0e6010508802c0034034072480d0380e5150109903040a0b000b942c0050341924980c2e0a41d60175000d0a03100c07a080442c100800d08290081e14880704084c0a01001c56480350407601c0c0c42280340d00040920f04200d03182564400003840d2480040080b00d10403401041403070000380079103034113108000440e90180c55030303403500390160208051744034500190500720106000b21110014200000b0310f800c4055001445504120b24158250a242142c048000e90501d000c0201480054 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 163194496 1250 163193246 163193249
    0x816050c060a0b030a1b0609090b030c0f03030d020a0926070504180803150f090903040e060d0609050c01140f070609030207080a03030603060c05030c12060109050a030c09050109050709 81
    0x10b8400003103184032940040c0c2041a020760182c00d804a4211604407580c959102204a82c2d883c0c50b6400c2166546c8051015900c1520301c9580c1a0000c0a00d0369141c144008600080003004098901d064103441034081203130010010303600012000041030180c0c460016203030001c072220300341810301001c2e50241c8c00e0703803085d85008580c050341d211041c1e07c4c401d107005e201c10100b55a0200c0d6a540381e14000134201c8a0441c0903511510a10000310311a11608104c0c80040c0210078107000b96103032509010981e141ca04d07020f0304254000741d80c0811103010522a224060301309115501130040107900c1000188504000c180201c0d00340d20410031000c10803070381001c407000f80e40d020f40c0c042120310003818181e09002c6164060351090091038441704c105503056002034191b0f845030f001082000310303c600841700b0380411034500c61500e00c10000c002e00c0e80c00b501e682070340c03011052400744240d80c0c80340301203041c207811544122940e0f80c52690504c1140ea09000d494054001450b0400c42071500e10001020166207 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 163195746 1250 163194496 163194511
    0x1509010f0504150203190c030f0503040206090409050331031103070e01080d170103021e040609020c0307031112071b0503010501030c05011d0906040c0306030f030816050c06 76
    0x1840c0d4400c911030146055500400600c084102d1603200b00074041c1d105e600c00120907210920040b40b42c0310329401000c0003207101d9050303554200000c1c80d08505a60560010704103a84c40313170042c400101296514002e0480082c8243c000d15142d2085100c81c000511007001040c0404070150310098a514264046c1e40c1165009117100d030188600c000424200007154000720b042c011240008200550f0009203064260800e03074840c0d03421012840043d03c610301c20b01009500c44580c400c1100399041c4031058004256004000161199492110701c0c220b90001030f54451b580c00102e802400d16401242049401c80ba5001034924050712903240401c61041c160000c0c80040c5400041900c44030314a242009010048e00821a95859003441041e20078188101800141e00c40407501c107a10810b041e8015110001d003802c0c5450320360000b0480502180c8000108141d80c0e0701001000c9101410104405030298440c04c1c1c3ca8107204800d07402c4010010040024030104200c906081400080c45a51203a030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 163196996 1250 163195746 163195757
    0xe0703090b13030c05100e06010f14060904020903060921031902030c0d06080a0209160f0f03021608030a060b03040503031f12060c110f0c04050406021c0b040506150901 74
    0x2201d03d4161a4100d0140b005485803060441d078808100b025030001d802442da200458940c0e0780e844289070800c2c80a0b0050221980d22995814400d04000024022940000f1300c09170030401c01c400030038a808000c5039000590f9028400006244003480003d100000e041181180b4514010100c1c0100360561034548106030350000c00070703010010381010381e110381814031400d10066a0303d1042959071103080400360310078201030020691040e0000c81010b02c107640f50321503410000c80c81006650110f14108064241a000c011100300c0d16540907809894034801da004986a041000c4068101c0c0e82540152580c500c0c10028080880c2c0000262503010001d50050000d56000c00038101282c0179590166000c0400311200408101d025000940c0d24141c55640501c0d6442001e4056580c081440f020a201d0700200104440b500b856003000d03501c00e000b0400540f5100740e50740c01c103014010501050000d169034403810985403a1500500d44c01031002c440c9110480c0c0d0342c48071b12242d40700c0e00440030305001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 163198246 1250 163196996 163197031
    0x60503120f070507030305030603060601050313030e0103020409060b1308030c06012310050a032405120322030302010506010c2001030605040c09031406070816050c03130e0703090b 79
    0x10780c85001c0314030403540801502c1399540e8916010b056a04203440d1070740329000303180002c0c013a5440b91007524400c18100e8040101c000c000e4a0555030504460788050401d03030204004202941c0d01d01500780100304552407603a440a1101e0100540d00f20350704030b42c003ea00108441e103a0304d100014014103403907482c803c000400148068106038120600c52058020142000241046401c2000740c140c09145480600020030b019010b0300340c4080500c40c6400a0b58400020721807410030503000210741d42c510045a01d082c030706d0181c242006101d405628151001641c092080660a0141581111023820280a142100e603900152405c0410043c82e400d078903104c400c4000c0c0c1c0720b40c0103040102400392003005170b1304001c0130080a0201602060324070301203840000802c0040010000c0c450003007561540c280d900e80f40035060080303090100810800606110020300170000344003d000e81040b40640355406c7c1d2909581840e001c0e0000c0c9088149864000940041070a000002d0b5110b50044000b40040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 163199496 1250 163198246 163198267
    0x18030c0506180d08030103020405280e030408190210020105060904030302070204150b0301090b0607051b0109081006180e15062103031e22080d050405060601030f06050312 75
    0x10b84444030901d90100a006001007488410360046041e0b0303009440c02d000035907407018200801c1e001c0511000c18000300c40c0304038601e01900d5010115640c0b2403001c2e2460070307a0380c90809290081004110707052007201c00b844021880c10701c002c40203450b16030001384000d00d407040014039800070052028080c50b800013504021580c039584010394a443c0c06c101d84842c4c0703460718801102a0000d015100005240c003071402c000c1e140420a5800d50350b8800018074404410b41e80101c1c4002101e51000d050240500c4080b5200d182400f4122504152500000b0442e150118078000e0301c8020082c44030441c584102000c03214404600b0001151041d18000c2031a29a10b000c504002030319510610341118101c204808040c001c40114098103401e0582044070031019410061900141c07458641c0002c2a40041040d10008422090b1640a03d2185041c1015603107250113a030421a82101c6542103201081580d6805209490b00903883d00004c10400d41054003003036403041e4500150004000225402c4840c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 163200746 1250 163199496 163199527
    0x10140111060a0902150903061f0308071101090f030f0b041b03050109021009050d14031e0c07080c06180a05040c020a050105070309080d0e151618030c0506 68
    0x4103030510088891901e0081034020041c0f041410880c80b0301e00c4450594102c02d0701d81c06a4102500003000381407203880d00f0000350300d010b5140c015600d650503d003070000007140500001e8060396000750710701c0140c2010704000401c00c45a54201180e0b401c1d42240900219000e0180c030200c0b294400c82c509482d84030340c03c01401414001c09141d00315800d0070004000c202d0103400010708036109540c000b1418040b20800c0d50050014059039810a440c110b6035004584110781e60042411001d05407890040d9506420038441044202d03003a08c0c01c400642e08440820401540c002003200c01d010303056603a507010015500b4450050030200c1d5445108106410760368003820703807004041c01003081140c0c1114020107500ca146111080e903555290200103041f160180c020000f80a51140f0351500d03204102d000303880209619141c4060910407801c50f82042c0301180390180c0207000003c100008003080d0301009056514030089011070400005007000010004400c050035603204807801b503110b154140c0701011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 163201996 1250 163200746 163200767
    0x40317180105180f0304320a0b0301030b13051b12070927080d02070f0209090601080d02011104050d0f0b040b0114061e0d06090501080d08060108101401 67
    0x115482d00c410b010380d024000c03910b41290058041034071060400103691540700e00a03841510350f1703004030031000841494609840b41c0181207081e101d900c46240780c0049040f48040d030708994400c3c1d0700000107000744280184400c0d440b054128045a40d211156141603e4141c1151f42e140f510840c0d600d610342a9560480384a02c580c400300440d0411907840282e40003521304a00707848151813400060100c034075441c448095400350401165884c100e1103c1800000754002c41060b2104c02c001201280160b540075510350150b58014001d00e0607505005030181880742289000d015603160040d058446070101c0159030841c1c1741296002e0226525007064100383c090302c00010070450060042000f04404000d20505a4050340007801803050b00e90140119407040349540070040003a103e100c503403000d02e03038002d014084000c6000314405075201091404d4400c02c0e00030f20507542010350144c21440c0d018140d1035206a0902e018500d5062512540e5007040641c0030b1484034401d1040b00344483d9000702c21900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 163203246 1250 163201996 163202041
    0x20906120a1406010206090a20131a0604030f0206030601050f0f0703170c0d0e070506070c0920043012080f07090e130f03020d0305010806040317 64
    0x120601e0411000802051100c0c6145142d080c41c501042c103551000400501c151000801070001c446640c94400c02480b10b4141c0c01c01d01421280034026584a4005681320607806100220b401c980c0ca10091200162014010340240710a202c00c0011030500844044e10a405a8107190b0360345549004030783c03d1040c0c04d50790f00c1e800c0c00020349111703080d00c02005001703081c0280d840140d10640d10030007030060301c0140c0c1e01d01c07070070b03c014000401484e40079402100804c940c10b04913192242d581010034459084070700140c45680000b04200400006130048a94206160000419800300c08084408a0203103026040312101100700c0c00b005d0100f1802c640f01d004102d108005c2c102c0e66a854200f4110803e03d5405001800a101280c480500828014010450380d150603c1590070007030170000094004101022060034050040d01103400e406002408600950142c0080428110003505855040e840b001090b8000070810000c070b03500282e00030403c080c0846000c4c00303889000c0c01a41c10880600400e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 163204496 1250 163203246 163203277
    0xb0a03050109260301180c021615110d1b0f080d0504020102010b090907090b0f180609070c0b07080604020d0608010e3a090315020d0605120a06020906 66
    0x80043c0681d91014030060340c03219603280c03c40350355440c0c01407283c0005e124902e8002d03a0000f03040010307080d582000c02c00a0f10f1384100d40051030340181c01b500303c1485e40d010b008003c2100c0318180626600540030042401c01c5c03401050911144200202460200360000420345641000c400030045240c659800240d0414030494603407008003002c00040009a408078003540ca0a203492041e8100040343d02c1c401c4181a014003000c0e4a840c0c6600702a01e450300300c29078402000034200405907540114030015480e45048180d50f450101c00340030f00070101a003140b040c04448903c940c00110342e000711541c00304c0e952414441544411001c43c01030b001d4100304a00190400b600070800300c405500540c1804400e804030341c580b1080c21918102418140d5007601c885022011900c003015840710902449a9175180c6840140c1c0d50b40c075424074940182c0c2c0110550394000802c3d03400c032403080c0108405402c00b20340981d030718020414600e544940b0158000d0600713801180c2040640e0701c4805032143e1802000c0b40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 163205746 1250 163204496 163204511
    0x30804031407030e0f0f010e041a031006031707080d020f040306090f0c0b040b030604180206040e0601080601050f090d1112032d0703030b03011d0303070f05090a0302040b0a030501 79
    0x140106101380c899502803414002c4840307051400981c0345a410350180c447c1e5801041040c10f000181039854803899480084102640150310204400c0071028100781001801c0390451402802031003080075180c101d140180110400304003a441250b8003540071180c0144d48030882c425080c01c9020315400038042c4d51819040d1405e00075a4020190218800c64103407000310b440c1c0c08007083c24001c034020000445010f0001903c00c1c00d00d075006e00107501c2d003020b4418200c0840d41c0041e080e45d02c03a8000c0c070700403030282044c441556000f010642d0403c5090804505006e140000341185001e03d900300c500c182c00040610052010f51064002c0c4818007401c010740041440c2c41869980d0f0050700e100c2ba450541e940a10280010740c04040c00815002e032a551a2207400d03182203018182c2c090300607074076540e20303800310145144251032010072041a40c091910b9180c464000341c540045000040103206080003030f400f40d43e8648801b541982d60494001691154031800300c2d0103924590001802e030b40c80e0020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 163206996 1250 163205746 163205753
    0x5041e0812090609030f09030c041d0c0102061302010e0f120c09010b0a0915030212010608010302130501140d080c0d020c13090308070804020f032b02010908030103030804031407 78
    0x2000612031004040c080341d1682c900382c07941c81100b281d11000310b4000340b00a95940c50140010400014003d007203c08082c405c50001e0b0840b400c44110040f01100c441742d2004003442803082c04c4441000340064455860316071129035800040c0701c0024100074100e4014590741e50b60301049280032034040c0034440002d403074004081c0d55144814004e0b00c240398038400012001020821600c0c06401d039581c0c0c407103076842c1c00c2544c0c81021501c054403040c19002e110400803021803020650082080746c0e01c48403e545140140820002c10740050050f09040034018000c0351140c01003611a12410b44c2c0107072140181e030074402c050703010301c0b544100c10780610088040420b038002040d007000001252a11522220b030341401e800c0b01c1d09030740014003107198072000409150003019501c3d44030b03002400c0200c401c051000024101031000080d048400c5801054003810801c0c0600203010341800d0008014459003a00c883d03045010501c401010000380f400000c04040c4284050604401e442d40d020ba00c0d02003602c3c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 163208246 1250 163206996 163207013
    0xa0b03010e061518040c09020c0703080d140705160816050601090c02070501022a010e06031006090515071712041a0c030105010c03030f0b0604030c0519051305041e 72
    0x600ca14481c1c03104d07030b900340030460346071043c28010b50f84640c18000d41071400d402440a90808200e580041c06401d5002000c140c50000038000c0949241e0001038502c4026400b5840120290554040007802d200707100c440e00e40800a003004940250484c0d8031030302c1030b400040c100119141c1c02000342c0251400007824040070380000c42240084d80079214242d07155001240d42e500740c5440c5544600301940300c09008440140020321100c010f140c5050040400d0000c2880f683c410388000000500381c030790401c6101d50000c3d038040904800c0b00c000364a2144651800001d00a81102410360003081840c0081d500c2524103e503940300c0c5000d0500018500b42c00c001d81c44003003d451003252144101c000484042070b00c0c08507070584005071540c10060b0000c0d01c08030300426800d0707049034549641c2c03110030569569400c06040194800c1e00400201410302d020300800034008072a003014035001d00c009001c2503507001842580c20708428000100342d52603003440000b81c8601e05040e04845a0740c0c1c0b0400070b000040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 163209496 1250 163208246 163208281
    0x72a0902070c05090a0902030a0f03090504021206090117030913091b080f01060518040528020a080d080c0c070e0f040b06100f300c080a020906030a0b03010e06 70
    0xc64800074540e44811116040d40c082d1b1100962540004c03100400081c0e81c600c0c0d444000d80030345848242d25440b00007090490780a2004446d010100e01e0800513145040175403980581000c60f020b04902c051205519500e0040010451240c000500c1a06012400e03601840700e0b69081044c00c1520205000214007a000c140510f0455000d003d051601d103074414029681142c402400400038040c8404100341803040c05841203405004c0c80d4a170080d9500000e90178050160701d142a032404820078810890200225071000d4802d8020942a401c804d42195105901103610b22500d96501b44070142c4504000660300680e51204011003071281540044801c68441d5114115099864840704200700c0e49014180b51000028103010b02d4504107840b880400d104810b038524030100c078500f48910313042132440350801350f00c8865440d00401942580f09e926203400082040f82145089105400319132140720081c00060740b2600c40c0e080c219251401d510203801e4052008c10b0b1131035030070a8003003072507004c42c0c2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 163210746 1250 163209496 163209499
    0x191e0e040309031e03080c220609181103010608090a06090b0105010207050103050c19020a0614010603050a02031005060c0c041407020d09080d051b0303100f0f080a11030f060a02030108070b072a0902070c05 90
    0x82f40c02c1d10f4a44000352041c0b52a218083e00c00c0c50071603180400c101d841c031070300500041260141201001c00101c560040301401d80c81030055070b07000d44c1002e00091821040350311590400d81400184038864071070390f00716005200d440c00c1d00c0519100206040c0d2402c00581c800911207403511142c0100c050008000034141e48003598284120748600034111700f42c0c042034440c2c107520841c41004000b0340c64108020001d4010b244c0555007c04e0006002070102c800801c01c101416001904009074550f05010401001c55a41482c0f60100d0030722070204d9403a20b48128210502c40c0010301c2e203011407002c0c0881e44011000800702c0ea0391340b07007103107029009031030710b2040242c94007081c2030114040d0700b0900c81e00103580880c0000c01c401d0800d03480f94240f01d1440c0303d18135098003910700d541e00a881c0c24080c07144501943d130000b507620f51611000e5032030f192447d406498440c6060202900050904060314110480f441681d00030a4910951140e00e9880394010304020380b00055510030040700740e11030301c2207600 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 163211996 1250 163210746 163210769
    0x403151b09050306070c0201091802031509090604030e01050409061203020106050105041d040f050f150106020105130201080a0b0319060506191e0e040309031e03080c220609 76
    0x805a4007900c0c1d841803402900e6040d00001d001a085070700c00c024098102c3c0c014940b00c0c0b02d8540e201203160240c1e011060301e151498000042012281e00c1004002c01d0107000d884a4542c2d24288420304d0b01e07401c0140000b01006040c08010440d60311800a9401500a0b07007c102702283e07503034040120b1a0b001c054200c0255080110010f83c542c0544255001c03204c0c8070718420742880c204004070102c10401001180c19132100409600410400c00c8004170901107900186801e0422518000d0144070580c80f032011603050000308030f0f9807044c0210002d401c41d8282060601c64480c180750a01034800300785c4054151044000d10841d000458064128880c003d0300204695210750050203101c0340380350480d089199100604010240011240d080c1c8840726603000c3c40d089071104403e603040e40b01920268005074400600340b050009244400c609000340000c6400794440035600544699002043e01840309004a1072000c0c0c1e1034001c41094403510101140f13103200d52102e0001d0135080203070081869005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 163213246 1250 163211996 163212041
    0x50402090a0e030f0703050f07060b0a081204050d030e030a03051b030f220306090c1d06090f0a090f05070807050102121603030209130603020f01030b091b040315 71
    0x102e202d015a000304900c003643c6040348250321204a41d0200c8012802c101c2c1c1003048554901d03000c406041814803034400421000c0f010800c0240907140b5404c0202075400c4801402207a504140441d0201ea1040e80d428070901108d040968014102e181001d415010305240340f0100341d80903008210440350201803803030340030003851515a240039000f2290307096a01040b41c4803507203850451038041075080f000b1903034540f5181d0380c4240039030301c4403030007110019480e58040c040e5903040115a0308041039150b05030340c103240c0500003e42400018066a101620f00e078040b0b140c00d99141c2081c02107681090181c2d04034142460115907850701403107030038000d01a014022640d0f620100e544010001104859820801c4190300061280d401c640124181942040703040c00907190341022034800c12071030741c0000c0d1544c03950060020070340b0304412a50402d403500c03462444a179111480f1071303003003014114003441159220317001d03071004d1041e50000f44c100c140b600f681d2640c0151039001001c503400201d404007407a8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 163214496 1250 163213246 163213261
    0x1407110a1d011a16020d14031305030c0d0308190e070602060907050117070302030c090405011814010b1602060906130306060f24021c09061d060405010804060f0501060305040209 78
    0x18011108440340e0700c002c6282013005482c00781c0e0310b03e00003130003203107102c040d140e00d030b11941d01c2d5501c2501400c4209030340d03100c20004d03443d040c4150803040c001520105020045550014071400e0014410581b1840410404100401d03a80c0f02e4082d8070b07105c5c400c446005407030b440c2c060b58032001110004c2d05849001000300d139a52003200080714500085200e00d0040d200c101c0150080e400003490000d40c45820f0210403415552406283c0c000c11034070407102035070f10621140c2402e43c0c081e5050225048031100c0100080314950044402d03003003010046591143d8070744009038a40c800c2014169006201241c6200c0051000520504803842450104103050303907080c2000c040c0d84c2d180b0070a000b0a4049031131004014000d51f181001c0301103403060321145204802d440691540160600f00001c24842080c0011a0080384030105c480090841c81c2c02d40f5840c9000030442d11035401054100020400420100400340e044081d900124070303000c0c003681d071315900300800030441140c05a00c120304800c04a540b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 163215746 1250 163214496 163214549
    0x306091f09020102030306102a05162306041505130608190b0118090c1d0604140d0b0108010c0f05070302150615030c03090d1407110a1d01 61
    0x142d040c0c0103181140d4a0004000d1b0350420b07140c1900034040191b90003829500d4040101100e2803a00d030403100f100d859400c0c03031032030120701c00c1e082070f0801000c140601140150b810207408034890200082c03000251075012545034000ca40c044459a80100c00700408030342c200000e000c9510221545807629a40e9030403c031002802502c0303101c3d50240720803915170b1030103003504203441010060401086c20703c040103d1541c1d442d51903102040f990740d41c1d5410303052254480c05122030001c86010689041c885034000a14074842c502c90300107100b4002005803044d4440e03000740c4500742c0d01700032031108640e503c103c01406410341030105000900700b0340302008410302800075662542d070940e00420001c845411080e06403003010304280d60081c080c00403000a50312a0005511460301141c1d010f03100e0507c40c0300e9038a403a0346d0b0a80d140c140481c1c2c5c0356141b55208160140d501c51a04a20300a012100c0b800100c0c142a000760001c0c0b0211440386829103d902c56914003504075001640400c0c103014507000346000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 163216996 1250 163215746 163215761
    0x6040608191e0b011e03122106050a0e090f03030103060b01090e070e0d050708120d203109020901090504050610080a0b0a03030833040e0109020306091f 67
    0x960020040140080c0400c490301c0c8145011707809004603917540300d49960482403050301450002603201150104d101c075800031280116581d6a805003d0ba82c144000201004001c1c0549040030f640c84000074440c982c01c00c2160001654101602c2c0d40756101d003005e801400a5004d014082103148100003102407624000911580283d544c11a00804510811a03141c0c5031610a45180c810700074045a102e100340805588540c90a400603a19650002e640f010380b084d551585042141c11404048850000011100500c621a22000d9960b50030200c14030146502014050b243d4011280440c6070740d0079900801140d402629203041e407664880c1000b05039103044501940001c0c8480030f6011150042c0340349a040401501e000c90500e0140700400c9603001036a00950018000106205174400203e0520008507080403607410421822803d1048403814070b0f049601840d80c8140d000d21a8100390b110f082d4030b50b4010243c0340c00e41029121296500d1558004030700089601150383e00b00304c03192142c3c40c3c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 163218246 1250 163216996 163217003
    0x30906070f030908010221090703031718030301060507030201050609060a060c02030a082b0c022e0504050106060f050c06010302061606090303020d050705090d0b06040608191e 77
    0x20319000450391121019107969004809108103040302240080c003c0c0041c18104e000d681c803005280e01900944604500043c040d15001e800000090010030f620401342c1c0d0900208d180c2900942e00c800d01c0002e10340b140c5141280c100d020110002c140694480024110140294000c0c05561510020400c2e22203082c2e1352143d01401c8041e0410650b0b004084c4500c1007070004043c0e544284070ce854049035a40f0005012840c1c0c2c480c4001c442c4521a11072008108910b190300c10070010f02d080310065594421000f03005480e0303d00d48503590342c000360bc00300c07000e070000382d03403824081c508142c41e099000c0e160320701660300403c1c90766100280c0c0070300c15000d41d20070780c64500050041f0b0340f81d0b40a11126a0007602c411a4810740b0000c0c01c00441d1060240b1041e0911a17500140c5e200c0b0106101c0003107a00250400f01004020000d0b40c10564030315020700040da030441c8034134549440d1600050010301e1554000390341070054060b06038040c003c401004901c903001c1c01ea401941581d403e803c8480481c4200c008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 163219496 1250 163218246 163218259
    0x40e0604030f0504090905030409061e03081303080c10050c0a022116080307031112040314090d0f020a060201020c030a0f030603080309010b01030f05060604090908040e070801080f0309 81
    0x500864454803041003900030500f811031810f074949040310144c40304a00266065071000a003000203251383d128010040050001c000850000e00f850800c04c20301c0c0b880003620700100031905a01d07184441083c207008580c04020642d0303504c880f9a4054451080881c02e4141c41d141c10006491210407604035a08024158094000c10054801003442161541c0b4030106103181800601640814030001c4a0214000d411883e02c03031604c114010f040d5107195030341f14810381d02840303040d4000698450150304664542068500d4070310f00d14062a082c001c131000580d116291019010034024054a4450124003c3d0351a0030078036100c580603401d030f03c180252914550f0007044100881071052b002e407140c3d52024a07000c21910360303c1d100c265158109a98600c140e0b5501c50b052101507030140f26503100c884604506221a151100009210b030259100c2d80340d2098580010104100c03507a001c84014159134050212182020100100810400d01400308144151440a01c0303100001040e10303120711004009 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 163220746 1250 163219496 163219501
    0x705060d02030a06080307030815010201090f0f1b1d18030306010f1103130e090d09051c1202030705060907080c0d020d0b071d0a03080f0f0412030f0905040e06 70
    0x35440254001002c8110040d034501000ca010a018001841628041e031b0394291a4103105419180c03941701403d070326041da0b14003205600040c0002c0900b000041e00228640000c060600b000c0012450b03202d10b0f25010300c0f6445001ca0706e0391003500030b5405501c1380b6591841582d5590b800384075141e6060703080b010581c018000600c0e1076101d01108801c2d0320041ca008103034181d481c000036185030410004007081c410070720018022249040c0009901008000c020441c5240700e85000e8040710542c000c40c0c1c000c00710341e41c07002c0c160180d06001008865200d50061910341548000075100e0b0003c00b03003100d042c001d01001c280c45d40800140742e070584a0550260402c46003500c02c0000042101100702e810006020840e00030651010038240b04000d10346500d482900425124020860a841458401c800b00e4074144003141e546c1c002e5419207100102400e507a1038104900868038002c5901070040e5042c810402070425a02041c20440e960070740d1520305241ea01d400802c03069921000613440c880e40003000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 163221996 1250 163220746 163220767
    0x61b020d021b0a030215070b0709030303050c031e10050a03060905060f040b070e01030e100504020a09020a1d061c0b0108010f03080304060902060c070806041401200c031201120b0702070506 83
    0x4200350210401100c1c6d61515295a88032111010110b500348042241100d08205154141c00b51a50115001c991545185000300090714442070000d01d0104d00b030b400c880001c0007101c030b13808000044e2200804090380d04e45d80345400c9010301042c00d4102c805000342c00c041030101407100c0041d4010741d804192201e00340d403000f40031521807560948460405440382040c046d211420b000031120001459804a01841c26006104200c4020303803000a03207038410030840702e0741c607231041501140d86403480340070b0710403d03441000400340d000b00781c2580079843c0301c20f0280744c15072078952107000c0e050b00a0700c41c00c0e0503a07a500d543c0c80c09042507120107070032240c003000004d00141c256807081c0786917171000b8940e50070445d400300482d141100035044070300194030850500090140c1e000c0a02c26505030300c8d00910580e0b24030148a1070328144034100c3d0040c1c00740030a4601e440c0d1402d00c103448e94a1001c100c0494070b581d6580e00c3e481c000c00421000c0e038041c103520f004a00780302e04c045226402c2d19005800076182c8000900f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 163223246 1250 163221996 163222009
    0x10908030415030f021b060f0603031b0a0c0e0703150b03010302010509041b030218060a0912030c0503030a0515040b0a0b0d090807050a0b07020705010912061b020d021b0a0302 77
    0x6004010965548044c1c0c101e4642c0d0301c064001440c54903000d010303400030111120700e001006005505c1c1c03400c4410400c02240d0f0000201e40d4200080d1140c81d68000c40030400f2490300c00b40d901c0040101007000740200c0c0040d0150303c114420f1945070740601c03100000301481c00c0195824011080c51500420040c0007550103403004140c805405040003c45c85203000d6402101e1801d091020006031700041e01d541c4c01c00405241003650798040380c00d05c0c50202c1c0075034040c1c03510406124008000040c0540354041c0742c050204c00e01c6440e0400240c0340d480c03034507a20000041608a03000380c412209807044a0b56810248100a8a1000501242c8046003806840d043d25005892807000ca02d40351140040000c2040b405080020700c00d000074661401d0328900303811129002404a01103500c02e1404004680e40074030340408445520020000075000d5080460103024440c00000142404182c01714600b58001180450b200301e0348c0c20740300098500801164954014251654060b8860509001614049 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 163224496 1250 163223246 163223279
    0x102060f0915090a0c030510060b1303060507020a08070b070f0309050706050c0304030206040b0409050112080d050402060c060709051e091915030f050d03050106020307111c0506150109080304 84
    0x60103c52136aa4030b95074918508003aa003080b1026000703c100c51081840500400300644a21000c0604020481d240c07444540e62510003d00141c2c0c480020645480c000d20401020359000130002d9034418050801c107100440a917508000100c9c00389625114500c6842040040760f8010b024080e40752415034222980e4020300446001400100000001a51240001c00007842c08001203900d40d840c2229403011a801640460400c484d00181d56000403008000c40e80b2111910400152a45407800850118002c40c0e0481c0340c8c91084070300344400c8640000342c403400c0340e1040795020304080d089004a100301d03982c00540303500040b039100030800d8000401c0090242c0304d610080001c401984080c11a05884660302c161004081c4d40c0c050001c1c0003050010012042482c103050180d540b4000c0029a03a00c0380040180228000900076500da81d2040611504840c00c0511403090415505140381c07503035016200098185030080344920154040c84004003296030a40103103081500d82070100d0690b8029 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 163225746 1250 163224496 163224511
    0x13030c050f0708061005040e0316030306090903030506090a020910080421090807060806090403030902031e030924030612010608072304060b0f0f0d05090c0102060f0915 74
    0x180c071030008048004201c840000c0c182d0b10010f04890400d101002c14030741081e0061802642440c0c100c540b404400001c0300c030002e0b9100380240503141caa041c101d0003082c0c55001810780d07038100032500d020f05038103030040b070300420003100d40405644400e4a00401c03449501c94080e00703d01801080c40c41140540c24083d4014041d26a50048072810041c09002f01015080301001c2658450b050100302410461507003d4030302400d2a9101c0e090840014242000043c8000c0805494654210442d18103000c218600c03044118076401048181454584030741000c882240140001ca8150b01491009103d894079400000e00703061441e142c4c40180646505c400f002c40ca402d40d280c520003c1d036003e081254400801000403600c01c250036012046114140541c0894402c43c18100e0520003a40c0340e9048072511a054260181d8902c8038410007640b5010300c04201290b68a000c003005004034000c01d03840c00d8a20241e00350f45880c1d40700010284465815652030055500503908450040154040b40750010038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 163226996 1250 163225746 163225753
    0x30d0e0321091c14210f07050d09062604121709030307090e07020c1201150e0103050c090408031303110f011e0e10110f070804080709020313030c05 65
    0x10740d10b0200b480c8001c0c9000724031411040040d0081840551100248500103a001402220088065400c0c55002c1c10500d2a40d1010001d24036031201060002c64140750361040548621901d001409000e41600d4070600010510340d0340c084000b1100840c0ca80c40c0306514100e010307a01c2d00c82d510741c4160820420689002e12032110130780c044441a541a1620500400005541c1c0e07180410b0001e000d85180d5210944041900e028080820f40214040034112400d545071190748184250b11800340406034510344804220f0140030801900000c00b1034103a034055007c0310604c2c03055030140480c07080101c030050006c84040c0007140c100696603400019944c007a2500c00854611022301d1410401c008050200f40ea640305181c42c40d40b6420415001d9000711580200300d171040c0301c1541c50701e84900381d10b611806d40d51402641c104000c1101030322412110014107a13210100d900c0d01c9040c6501c02e00ae9521544161080044c0c42603e40c021030b8856140d6244085010600799825103800003542c4c0d00301e07070901 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 163228246 1250 163226996 163227007
    0x1018120302210c0610050112143402030c0c0607020307090e0a06060605090f0301050712051f03031812030e0d210e091005150c010902130b030d0e0321 66
    0xf0f00820109014800d01d0a809402038030f00000902800010b440070243e2a04080c58000200b18200071640e001b8050560340903c00800910340074003076141030780c5c100d20504032007007106110341c00005080000d280c4001c5a032505405010040140a000c0000b2b515510490040c4402146d03504104829125001100c110304116628041590219000356001440105502c00c4034984214a01d118410503402004142000c0400418502c0011070100000d91a4804a003c0d1085852080c2e40007019903013610f407090700d03840d00030641010600c3c90030411a0b8400f02190f0400e0307c92040190744d506480b40310f0490381040501519001d51441a50098070041c0400140c2510b03981041c1c0c0700310260341d08400d0032a094100071881001500d001040c0704409024406902c44440400c842115590000c1d02d851688a80b1809440204002500700c224155403801c5606203410002510070114143c40c10a07a1000d42211086101c0306401d50540c001c44412410704c490640a000b40d0f146852000d2810 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 163229496 1250 163228246 163228267
    0x304180b040504080a080f091c0c0b0106170708150409020d0c0306020d1a0f091008120d0501080303040c0504020d0b0901031a0112080a14040302101812030221 70
    0x121400c4030281c4a80400040c6903d0013503006c1c01c0541c1c003c6903e1024a01d500303103006001d41d0f8200800f403e00d15141010a0000503031300492030014180d600954003201580c441e440209106c00c600f250000d4150058049108a80032369486803040d249450301402e0003079a10104000b6201a80b02030b80c10026900c440f00c040340c100d9810101850280d9000740c0c0d01c0e03040c1c0004400700e5400b400c0c0380d002080c2080c0610345542c4c0d104445d070034201c011100036403991907620004070741c0d001c941c2c0074006511482c4103246102c5041c0f0060300d064000032a08100350fa80c0c446040740c49200440740103000445001044c0200d103450340c00f8100ca42c41e580b000050b01c0c405040416040300e0280c009444c041c0807000c040030745e000d04220031401f5007845801a42032016503510a5554003990712218140109030105100c6001c4c000d0030f880040d500104030784040c071950070014202017690042200031901c0800007007032074203048400f9030100344d25134001c00442088842d0f030082c107000c1c0c0c9041c20040d9010131040441 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 163230746 1250 163229496 163229501
    0x2606070504241716020705010509130f1d0a02031c051218030a0c060506010306050105160203100906050604060e010f06030b0a0302150307020105100e04121403240306090304180b04 79
    0x19104010f1000d51300390880001a00d8901143d2213541003060400c000061512240703035a503a003036032241012075480341c840c0000f405816014004602c00704c400000b040e024000082c40708105000380c00f03580c10036030854104407a004540f400c85001c16000c014581038100c000c0301043d4050044881e8000c1c4118407501c060941d40070f11024400212180d5400090000ba4440e00350009001d00b010030000e440c110018166010f8040c2060003800400101d40540d1018040110f2810841e5000c210198062070114000c28080e03c4c114051880d1100c0400c00172000d511803030680f5070203456043d01c0c0d45403d1089000d0304940711010380090380b62400100603150351400340c10094081c40300b251a460031900007400c40d00c00034811070204080c24005c10115103401600c682103a00050184c100d00c280d400700703a5000d26410341c1204c1d401400010040080140510780e46002c40701714a00c3c002064040806503102c501b80c84410843c0c008205c1002506808640640300101d185004604038a81000017400c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 163231996 1250 163230746 163230751
    0x105010c140f1f0e0c01110708010c210b090a1a0901091e090f080a05070b010f050307060c02030705010806010c0807032d081501050426060705042417 66
    0x40d5103c00420b0050524042848040102500c010401c1090502105540e240f164aa1605000140002070000e490902c09034016259a02c000c0c000c2d4499035100a09c400650f803203001c50000d490780c119810000f540503106202c0300003060b0340134030b44a0700e2400000780b540800c0b9102c2089642909000c5454440c2518002c00e816840021900e640480c034a03204040e4540c1812000d291441e5403000883c0d121004a031030303402c40840341c0ca0b8406008140c1d10351181d00300c040e0940d606040005184a120759000b02590700680580e5485a0354580076a0120006e007002549900105000d105075481041c07010b602800c14500024004516254130449900c0b0640c00c0c1c0004101c03c03800307a82c0d40010490284081903c1001100386841c1000040260201612040780303412020140e0000340c0c455026600981030191080000f05440900c603607030036004144000d014040c600c00100d45a02420540c5d0403540ca041c0d00721084800140e03140140c5c1030f8a0b2a40003409103d146030a58060025140e61 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 163233246 1250 163231996 163232023
    0x5242202090910030b01060c030504180902010e061c02030603070513090303140708180705190e0c07020307030b0406020d0903030b1914010c110303030f01060e06030601080105010c14 80
    0x69440c1ca1020a008254100604512002d9110078003040080e00e009030040c112061071800044408652804490501ca142e2001c81002030200203101e1000503540150f180301e200340c813144611046a0144a940d000e40c032403204a944034107030035488081e9282c004540c08030307008050f2183c2c0d585034000149038180d03801c2c00d8031020741e803420060101601031040c40100f52200e00c540340580b80c048030003411540000d21007036404540b01c00000b01d0800c00c02c052005864000d1841500741040c0e81245490303806c912420103803005110101e002c00070b00a0484001a4000d0042c01015042d80c4840b9120fa00180003164510740c01c1180000c1c44c10903100d41c00c04680303c1c0d600403030a101b0540401400d510002030b408086420035504111910350b10400280c0204c0c00e00b4046540c40650a000200030b01d001070f07003605404000200142d00c002c03404801e0613110b950b00c1e5000800c2010052040e07a000486419022076082e4005001540c01141c01362145841103c1c10440f08811015460410045903000c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 163234496 1250 163233246 163233251
    0x2060f030a05010603021608070c080718050604020c0a17070f0b070e030c010e041109181614033603180d0f03140c030c030a090504052422 61
    0x400c1210042c040c01d0700500c500e240c19402d0010040d00562441c88410000700225000108c010400101402002c010300c148010f41342015501d0005105040035562417111451030580014111700d0a4401d952815440d074000300a11100740d580d408500200801d840c02c04401440603c00213616035181c50001840340c140c284543c00c0003d809030070b03d24607140c61351107030700a0b003d2800070380d900c0411070350a21800c80f80030030700581c07008100c08984550030312940c2041c4054080720381c2000501000e80103000d40c40c040d82c0b10300f0100c041221448401c500c18100c4040400100700410480c00505004000d280300b048480d00701d42e050340c8400311240d840070846400214170341901801c5030003110b51601c826661095902600e940707001c0b0880c00c142c0010284841180000600c0d00050281d81c0703010450800c4968900c14181c05a90380d4010301c0b204d400044c000c0131b021801e42858000c460003207564108051400a55403240855100ca442865402648920540399451004d180d40c040008200000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 163235746 1250 163234496 163234501
    0xf0c070807030b0a0b01080f070e1903020f190b0901120c08010305010b0a0305031215090103030201050f390f0703030204030b010518190b0901030302030d06060f1b05070302060f03 79
    0x26003541c400040c0102d24607890171004210b241d0b0015000c03540075900c54107095055450f02d8060f900303034650b9119140c01540d80c01e1b14010310a900d1400c142030344e000321402c401c81c0d5400d8080101882d01e95014001c050807203401040301101f0710002c1c102e480c105041408102646420000848401291031070001c0c00c000010001c1c80800e115000d070f0441f040c0c444051042c1551a1195203210344880c814102c8141c0b00060450340100c416419080c4004080b40b241d96544c0c03c00030702810050b10342d61480307441c1c0c001180301c0c01d83d620b15940001100e4010a1075042c01e514600e003c0807841400f0616201c810000d001402c025807000b403074020301c40d880058441c1d0030350800c00c03038070300058003c1c40c02011002c1e59406001490903105a0045020000c02500111f0000032005800704121450b0040303810400401010740100182011320311100b8100032056503404211440713910044110040b60114441400c0c210400c40c00b840828083e1084a292070f98960201b0a50b50000020544001c0301005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 163236996 1250 163235746 163235753
    0x3180b03090616110309190306140406060803120402010305040c05040507021501090c051c0b03100b0405070e1e030307151b0806010906110c090103060b030c03070e04080f0c07080703 80
    0x70404030f80c03110710304501e41640d0240e04c29664420385450754400d4030140d081505c000790740d0161502865021f0707020b0200a550b0000d85402410075201214940d0400c0400304500c0000800e407401c0704c809100e084032988454005400030603000d4001c0d40c00b10110040410507485034041d09019090940c020083c656440305500031031001a0810042e5900300b001050009c0d5000e810b642105488043e1040302d00d130707440c810b0002412503602c41c2e80c15000d11050f0000781181da40c000495110180d5040c002551958000ca44000501f03e59650100301c544040280c060f6031203d4103201140a81128502a031644801ea008904070212002c59502c0780110018115007003600603182d4070909268486050000018104003054080c0808100d41c45a040c1ca40d610300308644465908054000c24555840c5e0910002805500c26003031701030310038a28101f025050001d10141140c0014420300ca0b03d860320b075034140e503da101480d130300d8a4180c240038407040039006101c11002400000007c2198519614 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 163238246 1250 163236996 163237021
    0x4020418051204050307140a0905060d0516050108070e0d0305220905041a0c1206010e04050f040606080c03031e09090705090307090e030a20031602040e03030103050a03180b030906 79
    0x7c1054440c0c4075020000c1c40261120b08800701070b64500c00000c28641c1d00d12010807902880c850014202c0d11800c0b0000705003249650000c0181c90080e680c2032615078a40c0c0c0140e504515941045401c06080c4200001103480307000a803500d00359844d80e020f90300c144580540f20568580d042050945e80e0340d8144400c03c01641100107208007103c0740400189044095442c1600510300226007044c0b03c1000580240c0c8a0241003040f8076004108000508028400700c0c420f030700465044030600d14024021604050005a040c404000103006602e400130f03d0441141800ca0900340e4904020144500b14030341c0c0c0c88403040c510850081c2d0340c075503d41015008151a01f0f52540c0403640c00c924008000c2511480030040310b00c1c01c001400c00e0a600c007046015001054035000040e035075400049640701d0304c5550904150841c030f00860b000d002000b01300f8421a220310003031000401641c8481c902c400024055604100002009000b101200380d5a15520040303510132201c099040d0406402c00c1a4000180c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 163239496 1250 163238246 163238249
    0x1201020301050901053c0904140709020f04090f0609020c0a0312020424210606021507090501180f150f0906050307051b030c07030210030504080304020418051204050307 74
    0x842c2c002c8500401515050070b4001c030a1112400d0106c030b18614100ca60a01e0003410201c10058803601c0c1c04d01d001d051a4650390311421828800f07014444000480b6051070090b03500f0f400c0e10034042e038a4103290500881c010480c026075008119151040010b072045548041c140e406040c1300900302d000194940102002d0313140c24018052881440180200c0d40d0314548402585c0c0308010351000250603a0040d40c4c2050a0380030f00403241d95280016421004981002040340e44a401b1103c02400500f900b00d01e010044400c2e4000170041e071010461984564103000c091060851242c00c1035858040342000004590011440e000460110400b855884080500035401503c1d085d230070b440c10f00400030010710025000b0f0007005408135a41402c0e0780981c41ca0b08500300a1400c9941c2e400f608800c2680307031441d070f2109900ca1241a29039200560003402150b1249600452051070340d0364503404c100003450741d680e0712040b80e038000c110440018010018401901c10949805880c1c92512082525103401d5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 163240746 1250 163239496 163239499
    0x702100503100b07080d060627030b0a09021201020f090117040209070f0e0901080d0f0203030f07050a030605190905060f06030a0e0c130204030501060f030206090906040b120102030105090105 84
    0x100200007180e0540c6402c8070944807205806907403006507007052560350141807440840d0724038141001600640002041e0405400d8003c2010302d0390401400c10300c40b000900c0040c001880f2200010130240007640240e081c40c3c0700401500340003080d48046400c9811280a02e590010006039469040da0032540c0c43d804d550104a1424036450140c0c04200b44102c06131590051100b8080d161071440d000799034002c1a0340000e84504c80d1981d45404040d41e0f0403000b01700c076001c100d0742184000c5c440d20220072244070f950700010280036070b01c958400326426400a5002c80c1010b43d01e8002049507a030b0100c1012040c075128010130341250500c0c03100800c60b040542020f01c42c44074400181e038541c8801c0180ca6204a055038001149000403501504040707840007a82e5022106070160a808017855005d441928065402002520b440b014000302d21101da000180d4881c0e02441844541d02d00040a203030700510107040402c1004e0250082140c0060390703903900540b42d4010005105500b0a030300045d005000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 163241996 1250 163240746 163240757
    0x60602100b030c09040201032d0b0117010605090a030803070203030a151202060c0c0402070f060615080103060207060e0d030b130204030327050312181002031b01060302040f02070210 80
    0x1248800269141c0d5003d40483c0944403001c009415a8081e901504e604c03184640303940e07104000e55500b05100800a0601407445160000384c00700d6501c215400700741c1e01c00c04c80c100c44c00d69007480c105880c10303000201800d5000c4410301d0040300044990001e0350041006800031b548034140b040c44402503034220b0316100007070200e14104208951141c407079024880e030180c42541d40d5142e4114494200107070201503942043c0001150410003175003106091145000d0441004034039158503a00741046030b0a6a203800182c00c2d08010b00200d41160300610340c030782c8200c0000621a5502c501142414590321106020a07552004603407035092400c444502d0808038442140b40c42e007155000740103000c60f10117010441241c00c26602e01d032541002c0da00040d18004040b00d443e00660003048985900c10f00c4d000181c10700004400e1071a04204e0b03081d48540c00d00e600a036052400d491030304e901d0035401d003500301110b40d210400003000d61114800c41980c0303402980056610800390041c000f40c4450361091204011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 163243246 1250 163241996 163242011
    0x1a0d05070501050901020f0601080a1407030f02090703090609080d1103010e040807080c0304031b0603140a0e0703020904050a060c050a020307030c0204091b0303020105010602010b09180304080d0306060210 90
    0x10404561401980c109003485900e41080000407071070448247c240090340e200d01000842e424400007680d21110342328103582594800901c2000b900c42203540b000800408000891400601e080403800e07a00454901e000900c0060303585540301070720400002641c0c00300001a40c6480154140119180101c804490510319407400b00e03150301403800104054480280419000c1c20090504200d8035500001021030707464580301d080107011844403040d40a07040e2040400014124040d000d4a0b60b02d810100001520f41e640703804c2400501000407190615005003540400141d5030480d03c2401140a0001055880c0381c900c1d00307100311180514001c003807003030a0266a0702c0c10ba00108031281c0c1581450000c020200a102090203410b04a000400000b0405c00d110020800e03403500c01e0440b030003070b40203015a0342c0c2d03528241d08a559824115800c80d041c200000d540d603820b2914146008201c034101c84c540741e56500010305100d095411040000d44581003040050342c104095810014520300410441 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 163244496 1250 163243246 163243253
    0x50102071a0a0c080c130812090a12020d02041d01061e1e030303090302011e0911041a1507020916020f060f0a0c031b02010c03060b030c040302060c0c0d061a0d 70
    0x1c071300041c03c515040304001803004d12001c0c0800624010b140720402c4820708503002c0c0c080301d8180c202c023a660340030355490300f000124851410307a181c3c80d00360050202c0c01c1e031100c00e03000e002c0178280d070041e5480c034008144039007140000244115802008450048110200c2040f1808000d1802e0307030081e40522a4a4126038540741c281c0d03000c10440313906040014041001d803800380d015201001c2164000c600610007141402055004801030b18440d001044280314900e040000700c5048040340ca0710120110b011440c0303030911841812901d100c924509040c07420650009190303d008858000044580300740c4018000d070100301d44c6011180c002d015080c03900e005005100050b500405461110741c45109050b00a8002e03803081009981030b82080c0c03107c04200c40040d0103854040c9460001030315003140040c004200800b504d00030010000c02500c0d0610f16000c015550304884038041c11402901650802561400d404d9095a403241c0720201d88904203c050500c0c520500c0c3c403550060700c4001910002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 163245746 1250 163244496 163244507
    0x30723040e011e0e1302090906010b03011406091309050d030203070c0201030209040e0a12021b0307060503190204080a0c0902070317070c230c0102030f03190207050102071a0a0c 78
    0x19104212080d10080c004074081e1043e04249520216040980100f0f020503060050354480d0307007600a950060701c0341c48484007030b80c2c2c50b90309114800c019030003480103201210651060f1030b403040c40104424100240e080004684446015810b419135070380e1056134040203810322007901c038a400c2d0709045043d464845005014203030b1101000341010340c00211465195503030707800403003402c42d2001110000c030843c0c50706000d800c14010310200075100e04903000c0e4609010803039848843c80054064013815117440c1d001d442c00d80000c1c00340395801c40442c0346954104280c0c40500010511030b00100407aa12a0038200c07600c400c50b812007280a801003000c0c0c008a0740042005261041d504410034569540322002c49241004030030040450f803050300b8009501c000e03075143d0142c0b03c201e2015101c00a00030401a07030360703101c2c00384505010b15081c0009140221050347d81c0d00300c0180f210340949004403d03566035003240c0c0065411a0841203c0b84940e10441c1e1800b4070031340c00350780807504221486c2000c2d8003a28 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 163246996 1250 163245746 163245749
    0xb0114090402030c040905041a01080d0210090c0803070f060614010e090601110d020606031204060c030e0a03060603030206090601091a041a0a080d020c041b0e03010908030723040e01 80
    0x242c0e000000700310b4010551003282c0040c04a04410031131420320f032411268402150041140812600001140c40b0a0200d80c074842506150010810342101800300c6010300007803101500c800c2540d0304000381d03c6e4401d0000b0402d45100f21181410a0300b030f440d145d022541150020000903a0140e580700c5180d07000108461064012500280180d84000041707980c048802d030106094052603a0340c0f1161900010947c0c002e0408078103841c880d0007481040c0855000303910a034000203250138001408a40a0350a0f030751040b0000d44803041c140e4803610b440090390401c2c1d0085005034800c070104080c3c001c052080d5400f50110500900407c1c60030366269103010000e001c43d03840f40790b80d04481002da450101c002082d00c0e802400c4800c24a58842c80300d6141e0004400010260090810040d41841c0500c031761040040051126503100301d400c001141c001c00c844021581641d40e982c44180896a03c4001d1885800c595941e0030358101d20480000070420320f8000d4000040061100744a1440d0402d0441d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 163248246 1250 163246996 163246999
    0xc1403061c05011806060b0304020d0b040507120b07030b0901081b040213170f01110d050402030a021206070f0c0b01030b0c0f30070c030e030a0507090b03010b011409 73
    0x11141c10180010354800010321402000e561a0240d81030030500c2c1d10502e1080213024010802c8400d40d69070042e103030f92000310346c000d500000b0b5002103000150500c0e1002d03003003402141100c0d00152a40f548c20303020710b04590107a600348550020001010761500560b0004801694003115a51408050035656540c80c42035603014000c800b2203034450b0b1255410341e64842d41d45500c3c0800e1581e6880010810321610300301c2e43c560302401c54610075185c0140520100002ca141c0c0661a2040f49000a8000c200c003502c12a4140182d00046015a482a0103006c004a070303000504a941410030000e001c41c0b03606841101480340c101c010402146d4801c0b8840d04417034200b411000c0d59910480c031240b251140c01824101c515002c98402504070401c00d1201080080410000110014400088824004589184c00116101c000c02c00080c400c0c40a20f102c140084d0440d0700354100c80d510141030180541002007243e590344002c00640c40c2c240a6440b18801c2030038990322400310088140345910501c0402d9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 163249496 1250 163248246 163248259
    0x31104240b0f0f0706020703020f030711040b01050409050a0e061006050f0a0302040302180103060b011119050c030a0311240f04030e060a020a02010801090c05070b061801060c060c140306 82
    0x10504201c8a001c07078040c8445003a0300f6944001030325101700250882c1005074014030a01000e0000c09800104596200c2e80010030f40d00038841410400000d860202c0300981042070a10000960103c2e9008040c01550f1019020410141d10a022490580014900c100280c8590800c0101c40d4109080300d85260031182180da50f2000d409065010784101d600003904084000c01c241c540c481a44017041c1a6441101d090003011896001110910b044840905042e08080101d440805020382002c4445101b42c0a890700c29845030002400e140c070480040d008182c0701000d490601000380076403640e5191020401070306002e58035a0503405403005200c000e00304118404102418050841a150850000d105943e10f01442c00000d407118408078040f130200b0800d90000c600b4215034081d80c11400d0b15a07643c2d03400d2144940318054041000f034201900036114580d0300d00030390240302240d0f0107044151074040c1e00302031318609007084130300740317880001081042d2481a02c04403216081340d1b00120200c404 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 163250746 1250 163249496 163249507
    0x301050d150b030d090f091109010c0203071a070302120a0504050909100213060e12060a0f0209100201020406080906011406030a0f06090c09050a1203050c0313031104240b 75
    0x401c1c01020b422a42c1035040c42070306804144a540409010113035141d01081422450750740521405442c0c20880f4013a54040501203540d180d40308413000001d0a000804031124503541e01042e0340c481c0701d0001400c818110004140082c150100081c401032814000f00e21700e05035140c00c0c000c0141c01203001d45845140d00d00c0c04540300400400403044805000c0c0c0c000c560340d5640346620300559440d8442d030070100c4c82c444103240315860300c1040b2a500f2180030000d01284e03078401a490006100f88200003601c01e40c03d0015030415260582c0301c08015041d0b400059545042503070180050340001d03c0c021040e400040103000380c2002d156000c0040341c094070080e4803a1035260300394000e0700140389040101440d2100024a055031034025584101c2c1130b44a800c07407c0e84500c140f140090050243c407104074a11907104000034842c2b40100720240300201a00c1c207010058455443c1000540d00540710340000c0b1440301010321f00740c1720709003c1c0f002071100c0f406a004c604801e003040005600c01e803c11414042407 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 163251996 1250 163250746 163250783
    0x60608041703071103030c03010303030e0307050d08090a05072c0c190507060203090d08100308040506070302070b031306050a020702010c030e010905030109150f0b030613060f020a030219050301050d 87
    0x903052908084d04180ca84074684008070b00c900360005d1209400007424441110580032000c02240c0460360848041c150122007550305036805a8080c2c042d00c098400d0704540c1010031418003000001c0d050480440c1c030030310220703e81d400754281c0000300130900c42406014454842600c00858800d146040700d0441c0050307a006050354907014542010301014000001c2001c42d10001c5100c000f0501540c4410141c1d450306850260202d00c170340001031101d00700b08014001c900d4420702424800784248101d81c1d405032104404003064200751099222550003401100800485014041c0e10401149007141800082e4000030310100701618058140540c400070308540f1b900c070b5a0000003500014000340480000d900c0c241d260340070291000c80c400362a05062000040960150028218004000301390b50780b80c080c2000c02c070002c6824212480c951343c920001c20743c1700d40d001400d586103554500607262100c02e04c5120841000c1c2d42c840c41080340400044c4415a141c821451860360081d175032a00400b2030340d6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 163253246 1250 163251996 163252007
    0x51603090f0b0a09121416050c060c07080f010b01090603020919060f0806180f10030b0106050c0c01030b061803010905010204030813173d0f06060804170307 69
    0x180502e444142040800d4507550001c0002600c105d440c0000c0c420340780c004441c0c04240120817034960104100040f11450b030443d145d4010741c00340095807100140e100016840703078003502100706103800001c000c0040c100144080c0000f85041c8000b8495602c00c1c000091405942d4008c5505040c3d0204042e4026200d940590301488d80012010112075141c18000c3d080b0f030f50302e030011000a03120900248450800c94030281d402d042c2400b241c10a41c4590008034440140107240d50803910320120000007189a03030070102d008150300d440702541c504400c00d4043c20100b80b40e43c035034185030130202c400000ea11548102c40100c403800135a02c0c61410401d000a01401d50443e02900542c0049408418004000c1c0104125100488a241c46540c2c4e1500d03000344075004841e00480340c000d10803510b598451502540b031a40e501c2d141c0b40b440d044a07644000303101d480e1050300d4400c1a986001d4244600194468035010f4800c07400d203041c840ca0240e903500d0300c00c00420b2058201013804004a850107004e00d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 163254496 1250 163253246 163253273
    0xf07151101091203020903010614130509030705060f04020f01020607090506090109090f020a03050115170703020904050f070f1107031202160608060301050a090206161b030305030114010305160309 86
    0x10240f064964000018043d4101181c0f991281d460500b0014105000c6072990381100000781c102a1203000340300b070201c01008010212a41c0c0d0100b084000001401803050758818101713403450207030608044c0180407101c401281d02505550201050009850f0040340d40012034004440d00e9582d0304000340120b80d00780c020750006c21181d082c080c050a00003007940180001103050707542004a42c0e80c0302c60910f07080c80c40c1e806ca070000c07031190199050403c0007004056840200e03410054a085803a0001c175044641c01c4580f01d000c25501e8041c00310042d84185101054101498015449250304151944610141c423008040003a004204e814560007400355107141030040000c1d521656484030040c2c2001c9085803298440d52074a00041e180200c2c510946903e00c1c0c0203032010f402c0c48205400b60803610f0510005441d030b03c00216803169510204444e03800070314426036407261254074120340710041c1805080c141c3d06060401d000c0000d220503500103038903e40118980400c2120300340c2050220002d80 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 163255746 1250 163254496 163254503
    0x319022406040b180c030403260415020a2a05030301060804060605040203070c03050d0f02191808030f180301050705041e0f140301110a020f0f0715110109 68
    0x51008010000280d106a2003641c1c295800e002010a601c10800090a6251000100260032000c9604034041e0300107550320602ca41040c1040580d20b00840e01c40340600c007102180008104104420084180d6442140d103443e20340c294180401214013512080001e1200d40c440090030b2145118914a40340da0b840c80c50300030b02030b281d80c3e50311010014242c01c0110f4003542c0c00c40c2070040000d020b090900c201c034030481d030703968903d010080c0d03e0b078044815511141c038030310007181c81c0d2145441c21006807004081e03114000c0860100344d5519500500034142900090801c2d0608075001c008038513010084805079400c00c00c0c210754541c0240004040000030b1032441e9015844c1808000115410070010400da03444130b089105031404a1801c1301015041c4e01980040c214204030411000d0f403040b041400c5e03910020004100803815134220b0b4100c2c2c200341003240c0180c0c0300003284540584103008040110f588007014101c0030341800705001607070261b441101c08220081e04101e414100079030080d05481da2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 163256996 1250 163255746 163255783
    0xf0f040207050601050907090803090103090515010602100e03070f0318150807110c0a0306020f0d05150a06080108030a080703090210080103060b060a021c031d010609110903031902 79
    0x700e07041c119542e50090041a00462403072020034402030060340000103c1d610030000390710f840000303001180039200322081200c0611078160646541444510700360b0182009a001b001c0c0c1c00414a2946c054884031311020550740c00410034640480c2d558480402071301d40504107c002101801100d203660304090b8010300c610400380051804281c4d00c2241d00340112101d0b528250011504d10020783c940820b8065154042c00c0c03090200300140f15600036142890380488400d0401a21000103401c0da541140c0c3c0d410090555452103071140760011020f40a80600e203400c440c00d6040c098507981d01d1052030980e4080c4491000081d003013500c02d4200c009002c1c2d02030141c540c032a030700840142c45844203020031910360f4148840500390341801c400ba6040003500c3e038001d0503100310341800341f90000c0217030304007078201504e40c1c80c0000322600040015524124000002074041e1412100c00e040b0380d005000013200400c00c016044480d80c0c0003054031445a0400701c0e215001414042c140e1612100000e07000e18401d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 163258246 1250 163256996 163257007
    0x305030703080a15051c02061b0705040c0807020a030c0c0f06030c171603150f0b04060306080d0504031101020f060705070212030a020a03080c0c192006090f0f0402 72
    0x55000300d100f8002d4500c3d902c240043e04d40441c0900ba14201402203d800582201e10707000030383e8800304e26004050000d00b40a02c0c05010360142c0c0c0780078900003081440365010a0040006042038412040a108030b4503055201c2d040940d0f0013511107010b51406000c000085104e5400d00100e02006001068500710766043c45548200150161441100090201c0c55140d203004920720b4000580e071103803103052159244400300c180b0580042107404d0401026403000e000106075020301c695003002401d250440e258a07503140201c01405d540d46900019442c4d04211034440e02c07907410a0655050769070260b400c84108244100403454400ca04c2e04103021445200144405660480014075519000340c965460750242848910f90761b104d80d40c41e030300060340101c4848020074403490080d07402801e0140181d180201881c070040c507040340800c07480224600040300a003007141103034128031300340c1440800c120440e0213000091010f010342d1010070f01400c000c0b010382c00181d894200f8550200c00c0200b0864580 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 163259496 1250 163258246 163258253
    0xd03021911040f0e030a0513090606020307020a17070b09130606091403060f0a0c110d0207060905031c03020a050d021201062c0118080d0216060f09140a03050307 71
    0x4004118031501540c9082d9030b0f690916018010121441d00d028021032610007000c208480c10307400343c1c0804501100c4042c02042c605014007403e00189990f60007140c0314155401007009010040d40070080d140c1c0c03000d000c502040c1d030100d0813404452408012a45402096010404841108000b080024507100001c01d545400124450a4840e421a540740342d50340803040c07550345e030000d035800f8180350b050b00300086800c400b40e04050702d030050701d1800d94000900d01c00c00c12314140314801004056008080c090011590000c1c1d48001060100c0040c01411050001c22083c410551030395820135030000b40901e28540180b04884d107100d4003240866070f403603030b5099952064900380113500c009940c1c0c69041300703415501d0b92a601510302d40603100c40502c10034001980d03400404204205090702200002030030150a10081d54000901e0300504070a02561100c05c56442050b0860001d000c07032901030008031980b203c6840d050743c160040e4030550034044400075129403982c1c0d000070101e04c80000ea09080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 163260746 1250 163259496 163259513
    0x4060207060507021f0207020f1c020a0602031c09080d0504081306031a0a0e0a0519110901030b06040b0a1107030c03200a030f030516080d060f0e010608060d030219 72
    0x1641c40990078001400003003c4e11051f4820f00601035030080d402004a00309152806003209014403034034041800b00c60310303408560b1117851580454056080403984985c002d48e4400709424021828074200080e44482d558032002e8010203076420350b82c55480c0005010000481e08844a000001c440f500c0d035242d48542c02005010074401740406c12022031100a0070781803403010401514514454107800d9698165544000d20700240a030201da40100703085c994002107031040e041004030907c000d07031342c1d445031100260542d007006140c603000c1d44007041300700100b00880041d242104e0b0945414060720b0a010f252070300c1d10b0b1031908081c2920303691304030010410580c00f005d01c80c02142d9a408044440c1c000003000a24000340c4005414003562560714400207118500420100f4004080c150210f0626114140d80d900250340300100c0542d80c900510500c4484581280140001c140b020115814a10010508000544101c0c01500024140410540284800360300205480d00c62a1544101d00b4903040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 163261996 1250 163260746 163260763
    0x309060e0d0207080304080607181805150f0907051b0d02010c1101020405010906030b03240601021009080a1b0812010e0a02070507032a09020301030302010b0a080c090406020706050702 81
    0x25120f11100015810004016142214103030b00190040ea5a40001940d4107020b00301f00410700c1030341c02000b041883c4009080401750f802c1400003c1c03c1e10f000e0481001e1580706c085c05900c205503c0003029460358034050f2890748801705140c001e498441d07020700c01c1c10148070401e0039040b41c090f10440c0801945c3c15484028860501d40c1d07441038510021801c41e080348103074024280050000582405124002e402001d14800040e00b1202c0901000302455060382c03048100410300c45406040c410503681c1005030800090803010200300300556541c07104140d201707a104407424041148001200901d10482e10b21310150484809a80ca520390040324034850800d000720302a94080001048240c0034510950700c100c1d43c09001844407904503181c101e01d402d54405007513902d03407844400420b105061410440246841d00700941c8035419840c010b400e45000d85601030027042c0180c810032035210001640310b01900d0603214051540c80301e0400c200130b0700c11500060615030a1105000103140c1c0045c1343c3c1c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 163263246 1250 163261996 163262023
    0x4120509151c0c08010b2d18100207051804050a05060f0a0c050f030a051f08010501080705060c0312070309060207030c12050c0c19030f0503031005030703210309060e 73
    0x2d499144902900e801c002801100700181c4203200d5000d98000034002182c15010347c811458036000c002440392425070118000c81000502034209882070f0400c80312040c40308880f0300190100d2400d14001c5654074002101488010b0343c024081402d210091000900003500041543c086107400c50403000200c100761507100310a8645080780e03030310078851002c1e14000000b03c142d44d8903685407040301e84040d0802400000e42c103c038011801d12a106680c4d0b01c0c00083c000c5d0741c004100d030b40c904025982451074a5010ba80580c074100102c1e202030ba00801261810164100002040d40324101d01720000d0804100080040e440000d22a0034103412030600351107107110361501005500c000c40f04860342e0107005c44e4444590b0041d45043c100c0d00d8032800b1286441d105102d10400d459682d240c401c042d03070070200d050383d03150400028021401c2020542501404096000705042c900c2d680c1c0310b480c440602d03c47c6502e8068407040d98011039110342c200390031983c0c00940603c200c4034503407400ca0f00c0322030b85003c0340b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 163264496 1250 163263246 163263251
    0xe0f04050c09061806030c030709060602010e0303071e26040209070201110301090c0203070c0f05090709030b04080d2d1811011413150906030504120509151c 69
    0x9141a1400742c0b5440c3c4151409480d00da0b00d110030030720b0040c2942010300007607414090240700191645080003c0b0b4014110076001188561420201034215002819400c000d41c004000700840b81d600944000d407400d120508003889420707100411103500c0d43c4041c410f138803207c441c4c0c1c400c0c0400c2171010005009074021200c040690310b405006a00b01d03560400c40e22100f00061004200681140d800700b00400e071280140c07840d01c1c0580c0d5441c1920744081d000185c06010440302441203040003007031a075000105091500c1c000f41961900742c0b030380c20000c00080c45100006800d000420154005a41403002588607001c00190019600c1030001c860b480002821710f880e01d90b4002e4032407020180c00c0075400c150304401103084100110b800840c0c4061084140808118140850090b444014010801c1c00c410115018405800078080d46040d03000300201410708051001080e10806444140350183c01d203660383c1d02c202c801041d40b1140b421059103103400d002c500071580c2002060905000d02050908 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 163265746 1250 163264496 163264513
    0x510090506030d091502120c06040b010f06080103061e0905010f0b011404090207080c060405070302031e10090303061e050a050303070506070c060609180c06030c05220e0f0405 77
    0x1815507451112403024000f404e82e4000b048001481005240702c1005441a00c0c040007032101e04010079070000d10b04801701c2d48820f00b000140b140100610f1f0141c07981001402c0d600d460003000900240c1c06000c040c1030955038102c00703a41c00803d030456145036400310006004664660802d24002c0c10b0101024441e14200740302c000b840e62094025100d0002d94040d1542050700b0310301880002d401400081b01c0f0280d00b00000c107400e080812100d4462449100100082801c5105042c05e00000c07424074000e0121240c03503c4071088005c0b40c0400e801000d441c0000780b113003660a04030b0151815902c5045820307000d0324030303003c0f400d510b100c000203540c016034145803c1c568440905a5904c600840601990000d0011070125441444603200c802c0c000d800101d9200d0b212001881240c896524001d02d00042100c0001040992030322800106868101000414030201c8003525512615032140320140034040107031110466a00c0e80b401500164014081c240f034901c0030b00d0304004054909032050700c20040c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 163266996 1250 163265746 163265749
    0x1517250803040306020d0f02041e1202090f0601090b0d020915040608220501050c030603010f060609140406080105010e0108150c0f030a0b03010e030a0e010921050f010510090506 78
    0x112012601100001c5261600e907440b2100290025101259015164840c00c1e02555450016101424004c0d5080075200400d81003004c0c1080c031907001c0e070001c000854031003015946840103540d22445034100e144980d035404004a94440164009402c81c5c0c0c404a41e003c0b203100e459000c2d08001342c094900001000c0425900c45a901451140000043c05000010503400d400d4000110b54041080c0085040e0007a0b558242903c030f0440350701d51200c90100400146203806d01a080c0170b400419000c00c40c241c14640300800c440182d00482c1000c089074528100191500d9106a005150701c8008002e1365031501710f15101820203103d0118248030b142c54071301c041c2d031110405600401c0c8001c035880ca401525001c4900a0300020041e4200d15540c511454640c0c5082c05607010076090b94001e142d94805004016042c1001c84d01018108440d020081c001c01040300901407040b10305400c1c2906111043c9441c920300500d441a0000070750031315051000c0907991a13102c109aa071080400e1041e6540d000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 163268246 1250 163266996 163267063
    0x1a0403030e1203090706030b060d0c0201021e16060c020a050a060506030708072409030210092c0a05100f060801050103110a0503070e0604051011010501080f030d1517 73
    0x10350254080e01722020400c00f090090f030010b448140060071050410551050001c1101c00c00024400544d4000446002d6102c4043d41140e071000c50042c5541421012030720024014a03490008100c26030b9808000359076402000a02034a0382c0c0541201d00031a19482c0c0140545810390700b032400303440b5032140441c1c00d08010902e10f0070b5503404041d88000503d0051800c00c2e1a0003c0340c01c0003801540319011001da120109003004000700b03500c7c0c0c0103034680f82500c00c410000d21485214900c034510500d58601d6000030981a40001081102042903202c642c1c40b01130b440e0369644550000d22211500281043c1c1040f89039048603c241c0b0700700001502440c5e118414031a80d8a050700040c01000020802401008803070040b40c80035042d40e0400f61030b032001c98001c620801681d80458400d40841c50140e10900845001d013044c48041c080c00d40e804000c0640e00d0061002165400340c445080701c8050300003082e0b00700202405440c500e0000710740c214650b00c90204c5c041c600c003142d450002013116890540e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 163269496 1250 163268246 163268251
    0x40504110a3608010c080105030c010c0f11031c08090703230a080d020d0b04020c0601120f051e010f05010608070c030314180601080d09030803041a0403030e1203 71
    0x20303110009140801401c4441180c0c15519024841954030002c1c0c021010505521024114140000030820640200074201c0344059004511039071042c501c41d81c060b40d01000c501c902643c130000c008003004151401c0d485420500c04200d1f01403081c07880c07201c82880d800300c050340040415242d148254903a4000b1503168070300d42c04050311074103500011408500383c88071100124200c0e8820b80b10501841c4d614440141e00c54074800030742a80100f00f44618480c544070742c01b0041e608030303000c6141a840d5042c150302d60f24144641406024480305c11024051102180046690b120060362010310400200c40102c02d041c00b0304000c0b540c44c01081c0c5007800c030188181411b841040d121003409030746408048520040144086040540fa40d00311001c0503540034986028981e44c41c4c1d860308001091000c0352038084140d102082c40e6110451040d0303415041000b00040d00d41200e101507481c0d031282014803651090381b0112000c091070008100030700d54180e001c400c0504241c0b0a1703590050003a0640c1680340020b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 163270746 1250 163269496 163269517
    0x30c0b07050304060f0c12021f05090615030a0501021c14090a080a03060e0c0406180e040f020d0218060a080c180a140a05010303030c09180c09050a080304050411 71
    0x70881840700721700480e0b00700000105840c166101801645c0d03801101c180b03003005440964040c04030044000842d040c450401c501091081001e807410001c0c1c503545000260480c01300818032070182030251000e016100525821000035540d4072150020300c000084400120041d151402e590030b11445070841c480d602649401c4001e09019149485001503980116407000c1403540d99600007410036062046036115040c0f04402c036460310302d41a0050240049e40200c001040501c6106020f00b100000140c0e8009170070212070000c07000180702040f002241d001001e075218a100c008240290140a07009201c0e007400da5290b07280e103a9804540c4c3e5152400d16030b003540000004544c0c3c000790092013850b640000d01c0000030504c44201001201c046c00c0036145103100355144c10050040c580c142c018814140c4079403510380f00d80c0d443c20382a20001e040c12140202c005440d45280841944580100340260100501d01002d042d40c92030f489669500c5442100d003d58280b1000c049205a0501520040b008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 163271996 1250 163270746 163270753
    0x20a0f0b07230a200d030b0f011e050708040e090109110901050f060304020f0604030f030215040b0c0706060504020c01060e010905040f020613080a0b09011b020d05090d0206070804030c0b0705 84
    0x3640002e40d040d1130070807040c16105407aa040b80c49040c0e01004500c04008003502d00044c5200341906201e61000410140c905100820301c03902880c41c0c2c0c10b6842d14842c055841d05d03980300d850703070318119281b48182e031312132100e484282c02400a007036010760100c60034502c201a0309250142503402c0c4001c41c1401d1289a90040055000c042c1c40e0030404010b690052004000414000241c4000b801d5900b254100741e030115205030303c2c28201501002900410451408c1f82c0031203180c02d9070341c20301d00030005001d903008000101d50b1104221203074012001600d0020015511380c041c22240300c1c000c28040c40344807e0146480d0001509009902c541809a9000004d0a0201100d9020f014442d4080c2000342c01c090380030180081c20210038048465000d2194020032103505001c030b0020309603211440341c1120007212130280c00c10300c4e80010742c070075803181503051141d00c4810080c0050350070310902c00e000e9082440000d084080005038001002641c0c0700f882c00003601d5031102c100c455030340100907009001d0762 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 163273246 1250 163271996 163272007
    0x5090a14130e06070c080c03040e040318030f060e0307020901080309040c180b09010903062c011b0e0102070302030613030801060206010b0702061c021c0605040b01051801020a0f0b0723 81
    0x1d208160246001b4080e80c052860003072003801d0149954090742c000c02441d026402813200300b40d4401300015101c2c0e0964007040a441c103607282c042d40c031300740210000d110568a41c4505002601841600c006a400030542c4011390395607031410b9200d50200034407503c25840c0003c00c0d00030301e01030300340c0381c00e1601401c0702044400d04000c69040e04e81d00004140e8140811001c0020000b4840d01070702b58140e000b00c046640840c031002405415041c54407040380580d0610706511110044c80c074204a680c41c103407600d5400401d8460041c2d0526869030000380d0940501c80810a10850550941c0c5000c0d1084e9036050141c0c1c2d071070381c1c02c9031240000e01034642c10030740c2004404054940b2030058801e18000500304580700420544003002c907400310000020480d0682c82e0300c0085030030352103118003c1c00181e070140941004a0300080030782c0300342d050003446601c0000c05503406902c20046140846ea100c115082d5100050404601c600812a031071800540900c10142c09511401e030114040030b0b07148101800d10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 163274496 1250 163273246 163273261
    0x60402060c01091502040303020c01052119092306010e0f070509040204090b03060606090d060504050a060c09090615080705030619090e0606090103080306060a05090a14130e06 77
    0x20790128200d501d096480d080c0031404104e0741148100035251211005075107600d0b6190190410701c40c201c40301d05009003448800d0405200026900340c1d407880030081245039a400500c69920400c0348210516a440c160b8038604015026112800c1341d01c82004501e2086400940c4540e50642400340031101c0d1200fa0100f44003103600c19131141c014555081c1a410b018215002c03400300c1e0480d503c0f000c2d509843e6a0300800e5428144403440d00040203481037072a240722107010403203050015200410b21580d510000d000d0007400d100d40da0398a54400c8050141568500005140410f903003e64421245843c50000b50792062202d41610300842d44c81d0814166142c1c98143c4860f000240601d4000480121380c5071028411165070b4003802c03034143c000901d500c129041506d840030040036039029104880060001c6000102030f2540124111800307562141020b00843c0e00d8010300a0b80c5800010f10140400c11110842c180400d282040e1844260a06a4102c0c2d034203a8a4040c440003550b0042e07008203000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 163275746 1250 163274496 163274509
    0x110c1e01150b072120010c140702010302071a1801271406010902040f06180306020309030d0f05040204110a0e0405070203072901060203040f0b1c050405100c020708060402 75
    0x850003010401c54440112441c00c80391360165003150700040a09000d00b450300d88448803414030b00480f40080001c1910b030240606410503200344020030b070402054010031a0b10079011a0025070f4010301010402c070060408401c540c80a44a0f0903003051010020907081e501449040c0420081681c210781c4052070380e80ca070501c94140c01c4140e500f545100200c0003640e070100203a41c02032840749070040e580c034500510105941d82a4204c4070400007412030901401440606000599410100040e85d84e110362181924500c02c424031960350314145010b030f000c00801350380094441d43c002c1c1c805000c441050b01101c4a00d1250b00101030214040448410b02c5003002c0d4070540c0c0c1f250031b50048030704d0402c036030301c4116045000d5130400881c180c02140d4071510441110b4000e0040016000550615007404140510071010b40250403092201150010540c80040c0100e05901c56240c4100701900341408c080e030f00c40107402c54041510f810328800d5801e0f680f00140580440d201c200c0a09590786456080000c2c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 163276996 1250 163275746 163275757
    0x6051309150b07110406290d06050901080f06010b03060603040b060406171b0102030405060a0e0409080a020a03030605060c100513060c080f0714030a020a03110c1e01150b 75
    0x820700200003251109002d001003a00c0740c010070541e42c164841d03500304015101d06810007424400c00c0c6036601e0580300c10220844e204141b0108294540c012503041800030001a40a10b138401541400043c0d81c1c1e6002c83c0300d0708414000780c1940e001780e03240c0c5d03600007403888107071003864020004000080c04170f0b01c40021190030050040c40444d0050390f03a84d03d5200c0d101c0303044203d20260000c1d005054545501e0745102100e090078006141410300d003200003080f030b00400c41c022060010032101c003021035440c0d03070100b103409a000c2045070312060101d80c001c4d41c2d01050032003200420b1902801188501e030a2080d41e2080300c000c0700501540490041031000341101411310140c61952106683c00214180224022a10666a1042d640c501f0295040100001070601000d0110665420140421020440b540320f404080702503900c8011200480007000c030307000000c190a0700441c1c128810800819007144410b411150b04c0403c00010615600300c030b10120341c41d00340280c414010022007925001510 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 163278246 1250 163276996 163277021
    0x304030e0a0312050903010e060c07200d03030519200d1103040812070e0a0e06030c0405090f070f050f012001050c042102090403200102040902070201030606051309 72
    0x1c4071992507950020500c1080001804903001048100060409201c0d8410044a01c80240200c0c103100c032000708a413183d241c026181040d400b0941da5400e0010142c4000781c0c01c05000c0c125031a50904000b401003400740c23130f89484100e0302c1c1d50300d00301d105040c091824a58101160f10342140315454800e041035000c1031210070040e4495410035820340f2180c0203103100b03500603103140c0da03204a1001000d0384204c0c000c0400c000d01082d19540201070b114030600d4426600407988490b06615600c00092415181064181d44a0300700300070854a500301003000c824031a80c1e81d045900d80c40c0c961418900b005c80d18040c080d00048150b5420741190310442800302c950003580c0f10605001008083d40b0700390f9000305d030b00e40c41d0780000041c10040345c140400144404028050640e503e07180c3c0e940021410040908003078104400b062664260215140c02200c0c0440250001c56442e6628010107000e90401002640428034059000070010301460840e8a000f0501050f0301c00d2500300861500107002c400b6040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 163279496 1250 163278246 163278259
    0x1c1109101a04030201020f06101a0912010906060510021b06130608060f0111030d0b01140a0201050f10081513021503100f05010c02040f0e0a03090306050c0f0304030e 73
    0x2481d01c460304042075056111601d440d40c46003540000f80c070b00f40c0c04200e24200e650144007000f1603103440b4120b940c01d403600d000f400c5102c07070071405e03c2074424010821810b6226034511520f2144041c15403124043e98071a0506010b50b903590410020f501844c2500603004d600250300598228074654415202c21100900c110700304044403903950004041a0408808a01c1c00e0342032100b24a4007544c080c1100a092030181e1048800600640d01e901500c20003203000d90311003104882580c0108601c00c81c14a4540016490300340a090090103408282c4901800b87c010401084411790307200028810f640810b00182410406c0800401140307900900c80c04115a1546443c80169200a200c1108030156000c007500c9041482c486070161025a116803140e4100403401c01c12a41c01c034603003503d0a5011240000c60b4200f00d041c1d00c015061080b2411075500441d0180710415030072601074001d49002c1c003010071041d941c214034000c2610a00d10054036040b414000140000d2185c0c030071a002c5407014059 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 163280746 1250 163279496 163279499
    0x151e070f0c030807200d0206090109031b030309050306160c1401051e060409260906070b0718080a0807031e021b030105010308070f050a05060906061c110910 69
    0x40e01c0404403150001c0740c441200150140c00d01032141003000c6801240040d510303d4140c040300044141d85c000304024026800842d481c1040d80c0960b008000440d00322a180d452030042c0c9840c034002c410a4041100406c5c0c10490200343c9040000d842c5110b29000440046440340b480c805075107411440100b203810025900b03002c19004800c2c00350710700460682c2500107103012004c1240c100560700070070b29030091340307085042400300d400e4041c0030b40c0400c512004d001200d030054103484850301c11032010a0f009040007504104020b1381301100d502c61200c507595038440d00680301c1d02104800140c420304082c6c1e03028100d2030740407880d84001004228420f081400090440c802e0400b09541d4210307030b084c0545c00290030019400c1c81c1c88040c40c02040114001c200d1507045998100060180b5103014140703801111119040000400080c008280c2140803540d952400441442d45d80100701e4510780100e10b405610710b00380501c00f0300d54003099441440c0000011804041c820054030052640c100418110070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 163281996 1250 163280746 163280753
    0x9060705010f050f0903160b061c08091503040c0306050c0702040e0105010305061602122a0106053c130c02070302031c08070309030e06030c0306151e070f 68
    0x980708030060b240303002050f5890066000402c849005000d0030081e0810002410000e0f032029480810390b40c401c1004466441f8940802c41400d21040f034801d07013200344599001800022400381424500c101c440c10b502e8158240c1c40400b500090307800170b0070010b0400040c0001012a08000c0e40440380074412030914403541c000030b00f51140e803096044c036070f550b0b14018001e201c030030301100e0350004039449041c2c015680098001e41c1c41da040403031103c11402c0854040c101c1c051350308805000300301100000248002c4990094000d043c3d41c07103040c1c81601c2072070610300600382e03c90440010181840140403039880d83c281c08001a5600d4491640c0096401e030010840c020030b106014240b541507004243d55810352060501c0d00050055007520030761006000706180d80d10184482d40f10180f49804600c004051a040d81c0c0345222020041d4004008420003002c01c01d1007002d1032040d00200e810010302454103111404611441ca4150b46444c4900c040e0442e400700751008100d214820404000080760588 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 163283246 1250 163281996 163282001
    0x41404090f110f1906081504020307111b0604061d03030a09090b030a02090103031b15020a0216080c0618090c03041b0602060f0405102d0203040b0604020906070501 72
    0x20070454014411090400060820a6861484000a642492101c501900b011550050074814403040040e40e1000548001020f0071381c03c1201c00241c0159101d0a100c040604902d1750414030500503c140040070480800030070a00900600107042c2e54501420f00004480c803820449892220003101e034805800d90300c0070030041c540da041d10340c0c80d2400070341040c003c00305840103e050180309034004003822000da078a611180c0d0460340c0c18100158803c1c4c504007414024207003104041c01c04440100e07502074100d0590002c242182c002e5090310758026080e80b00202d082414010b101c85580030007804900e0f4148000101201c05c200d224035419a0481000a50320a90807920946202804410f001c02c100c1d2915442c1c1d81d41109444030607001d82028030081da6003a00501055286a11201040600c2001d00200d0020780d03034000e082c00114941b400700c1d40c0035000c081c400382001c207100d071440c00d00c1102442030b24002c0d603000204c485180c452804200181d044680c003a640030780c042006100082091 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 163284496 1250 163283246 163283273
    0x4050a0b091212040503070608090c0d1505150f04020711090604090b010b04031b0b03060105030a0902030a050c2b0f02190906050a0e01080d270e04050606010201020f04140409 77
    0x1460f83d540c0c480c100303420302d41018096400031040c0025002441031410001c5800f1045100642e052600028603041c054034000c0001858105685002c003444204058054201014407082d100340d55607510000c10301c001ca20840c04003801c0200c0f01d4600f44264501200d4050300300b8001800403800002c203031145c03030046001380e00c101d542e114006030805c2082909500780383c03021002c4000c000d4080c903111140c07180e4400103200c50304204000000910000c0c0550003900481d4001e01180d00c50001c52030126a81d800c641d1110380f04103140c0b01b000c0050440f151040d0905102e480402055486030b03603070501c07800b0040e10100e80c00004005920000780340c1500da40c000f0047c42d100820154a0403003880300c1001e241d0400611400303110014080b6607400101000c4001e1180742000c1444861519000401c041d5180a00d4030200744000241074003841d200980580d0064040d03a1054840400690807407040c141058811a070a00c1b00b000001075022170416164800351000c20b80a42030b51f52004c140081 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 163285746 1250 163284496 163284523
    0xf03030a110f010c0f0c0213060b0702030f01060f0303111509060a110702100e13060602010209121b09220c0311040911040e0a0f030305160504050a0b0912 68
    0x5484001201010401c06030054402c034000030020740660040c02464292421200414000d4000011046444034004903d1641200030100320f1a80c40d40b0035459242d00800381640300e0301c01c100d000300c6140d0041c032a8008440340e120585c0103442c07a650b0b0540300c08614201031150b40c00303807004100600c3d100760042481165500017400441c6046039400041b56041c10f4045100c0505100300d40040c2c03180386180342c0d039810714100f000e0b00d4018100080ea00b0b150002d074001c88241031840c0059a01d40540180490580c210343c04150441c5144060380c5c0e613480242092050800014000000d0410b41c854580080c49022040581640d4045444c0354150490382100e001d11804001c20500c140f4003050040584100c809100300c40311911440310540d00813069031301c250b0340c603d111880c405080210070307001035200314421243d12580c00d01a00500c01280c00030741d020b81c01141d05108034821000c0340c0076600e000303012314010340c2010b6010f001500701c040364035000b80b034012140c12120010081407034500311 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 163286996 1250 163285746 163285757
    0xd0c021015031a0103030906030b040e0f0d11030309100207020109080d020a12050306090a020d060302090f010e01052202160b240123030601140c010204050f01080405100b0f03030a 79
    0x50342c83d09a80c950b240380d08200c0480a4540140300180c1d0280c0c1e107900300c98651a012903168040400580100b03190011406903110340030b8401300aa4011030b000c0e0042009490320060394680300c0c429900e9101c12a22941c0036004040810714103011780d80608003031070040c5071820800d0340790b04800345045a42161500564070010701c0c042044104400c10854004d98070f801e82c03d5040c001c1c0800c0e61600e0203481a40200e4000c00d8a08905159030300c000c009680040001e010340c02d010f0b00c0441154400e000e50820360b103480c40082841c1c00c040c0903401c036042c0700b01260500d1003403030002480207422400140e400389898110030404514100e051074061402003800380000654240030892031418803084c9814002815a4800d507a0410410501c0c07424078134824507030766550030b00100c85500405403171000f203807004220100006015405041618804d440501000801c0001956260001c83d0700402c203138031030034108040b01055040035502c003e01420200c40304425000090071908405008e000196 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 163288246 1250 163286996 163286999
    0xe100503030d02040509070e01080412020f03130512030301031205031506120a0e0106050a0302040504142a041a0607030c120507020315010b0f0a02030409020f18090c0d0c021015 78
    0x5030501110740c00001230b0420100441a001c00070f40403120060002d061010701a2204400034000d004c0840342d02e00407000d0300d036030703071000903484243c25400c3c0641e90003050001c01c0d54442050010480e4180c03a0080b5200710f8551002000300c40c0c40d440100502c05605045100c0b5006454190113460428407003407000da0300d847e107011b0120490f50070b01030300d0213030b60304110080102e81c4403007071042c0940750155408036850f0358900380340d8031444280c1454850b901c40d41a610b0344e03040c0350704804200b03010101040808440540d00f00000d4072041e80e00310b0288019102a01d8151910000501c80144241408800f4030107a0f1100034480d619078000a001c5100091040e00710b1030180001ea00740068490f40344019410011208564001ca0a101c40c01d01c00014014000600820a0790010152508259514140000c83c8995078009140b101c1800c1c4c1010813080340c601d800352080344a080300d60051414050102c1c207410180032016a0b10095000b00340c900740b002406130080f4410152894400b50b0840e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 163289496 1250 163288246 163288249
    0x1203030236010e060903070305060f0a0b0a090f0b03011a03070603020304171b0f0106030605090109031202030c1303121b0812100b2703010c08010e100503030d020405 73
    0x1419007106501c2a001040c040207090500000d2484042100b8070308a41c2c0902042e002c03645074420901426030500c40c0c5c0400008209000850502c40c201c0086a0303015070b22503070840401e0310703042d8440a031300a0b002002030201e128103501000c40303650510350206032004900301090842c0c2c1c0924000000290000b021110780c1010030600008012502c1c0440c914581500d0f008103030101c2c010f03118002900020a55070b0102005500e101c12000c15041da102d224030300381014024103891004813041800d043c000340ca450b03818824100f8144d015150f80c030265804043c05002503100038040225103c080c032040e0040d0300201c142d0805544584a040d9052902c600e002d049044000300600c014080c9220350000103020009036410390003440b640c03220a0f1103103d001c0d81380e11200e03008000100030201c2d400401c01c100d05151542c048841e12a0440410aa0141741c26249207200350000724079510010441030101c518020f501c1112080751150142d114400281160b00a44072021040e801280c01c0c4201e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 163290746 1250 163289496 163289527
    0x31b160309120b04020f04090c0909050c101205041e060207060b0906060d02030405031216080105151c0608070e012d061b0c17070f1d1012030302 64
    0x24000a600d09001c0380b00e50ba4681500101c0208001c3c011500c22502c000d4580b1a50442860340364001400724416480707000000040c0400d0b01c095030300e4411585c1071001c5043c50340802c069400642e40c0c00000e503880c1031040c80a0800500100c4407904e881003088034a035900c0030103030340040c407880000da0f9507034060402c04280c031917000380305124107031030000e012090341c0710030842da00750140040240c0c480d42c59007001425806520581f020720715083d030400c4280c54100240d068056003e4507007460903600c40d8240203039011280060104182c023000406200054402d0300e00800d002c4000108849880d200d6490a0112a500ca40303100c51044006001c00c2c1c52a040d0302c0700e41c0340350135007190b11442030130040c0e02e4000d41842040b06100000e02265001d9005250001c2c2c1144c0005801062170740e80d6045200860800c1c0c0100361900031546d001c82e510fa40040701c0e208a43c0380500f141034070402c1e58002c0100c81c41c042c00000000c503080c00005240e0340c40004c044010390003501c0058480c64891701d403002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 163291996 1250 163290746 163290749
    0x60c0418050601020a020d030507050601060801030203011d030f09040912080907080c0f010507031211030a0e0604051b011106070201050a06171002130801051501030b030703030c020105031b160309 86
    0x40303580c1003200300b06060b640040c40502280e0126509a07134015181801d031058418010090300c40d015000000c107980e40c002d0755250480b0f100750020408580381800d807040000700c40c0000402e84e00100031451070441040003134400720380014800101d42c02c4030390b106003400000d0121000450302c3c100420002c010288041001000d484000e072540440f240e00081024024032600c030f05100000c2207807024180302d65071070382d80201100410060110105038188281d0404c0718010f000904202e46c10681000100300306001d550300000804c4e500030b101c20030381703800c048201000f810003000c03030384090300e4943c2009141e0140c1c03001e03000092941421248a42540c8036601306000241a098401204801c0005d1000405000042c0180c80c0e0181e800041ca90b000310f6848841d40e98200800d001781042c8a81c91189901000d8800b08201c0502005058403030b082da21000d004641341580410155000300c004580c030000d0010040440e00ca100183c070072070342100c020504440c48072103a0004054000b6642c00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 163293246 1250 163291996 163292039
    0xe010e04020a1e090c090503031b010c09050f0607020d05160e25030b0102010b0307090e011404080406210507020a022110020904060b030103080a091401080402041805060c04 76
    0x44400041030048841c003d8a200e0b080d0050350715902c044044e07200702d154401424006068980e10251160f414a00303c801c4000c1450035480d05c0c800100f500e00400307080d41110030181107107841d2010001042804e8012010590b0003640d062110800242e00303011500c02c2c0b658822120400d54106800044100d400805005000032501ca00c40003518038003084803402c4101d4036010444c0585e1000413400340c0300070843c07150940718500010440c001e681d00030302560311a51000300140c01100e00b10420385802a10082c009000401007030104c6031013034041d0008140299241040304c0c3d0000307055001c07940304440e081d0040e04040102c0341145000052800c401c180dd40710321a280203184800703602d8040c200c8140294643c0040c0b0040c50f912036801001c001c000500b1656200d40e900d0404407e42c1d404001c5e01400101140c07004038010383d0700c209441000c00182e441c1c1565949942c280b0004010702c0c2c1c4070384480340c500704400d000110b08021452007050b0780342c5142e071a10718101d580c1028500101090 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 163294496 1250 163293246 163293269
    0xe1603020a080406090201030e0f1f02090d080a02070e010f060807020c03071211100207170a050c09040201030e0106150f0e18040309150801050a1203021b06040e010e04020a 76
    0xe800a0b520030140d940060308000006060304507403006900a000e4048201003038051400e15407502e410100d6022100c210952107140901401e24500c0d04a00c10300302c0040c0d0101c05220180c0108001e44098500e50909004850900f80ca640340004891400d90086e000149105010b1005a81c008507490300214075000030804581c140c0c00298645001e40550030b00089032881940a00c409054014029130703028000c8105480b590f10025245c04031409000140308101c1500c003003021000890030758a540000140542e08102001c000201102401c203034100350f112510800d12110030b108480081042c40c0500811115500f4045c041d2402c42840030300740204841001c000b501d4901c80103001d10b02081c8964419501d034074040c0d038800010340101c0101d61a501400d203000340c0110303c0505030f0740215560141d442d0f9400107100e00c00040d500060040c1c000400040300545089132203016007100030704285c00d01c0c1d155502250380e040e00764440084814080c06000c254103000303070040090408040c64 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 163295746 1250 163294496 163294507
    0x7060912020a0b030a09080c0304050916020a150617071401090806010b0c01020f070308060a090203150906041b02010518010207020109140a090c0f0306080606010f030f02090a0e160302 81
    0x39050b004207104080800400000182c00c2500a5024440076a446042c0c103440c4e1a480c40055502c0c0c015001da240200c0d91840130414507440e0207203040303196205500805411a096444040d88208442d00c2110151070b0741d4003258001000c010443d10140141c0100002c52401020303612042c48124002c0c1800b100c080180540d0b203001c242d25065400510000f5980c030300d03031005280207100e40810403550b03240100da0300041580c0700034030b42d004034411541c480d00140c0b9103020328102e2105566990405e00d80741e800150900301081c0c0a0740c0032400420002c1d0b07486840d0f0f40b5040b100003105020005035514000c01c070407001d1200c07000d0541400c85008604000980d07002804024260180320102030208856205941c0c9200343c2d41c1c00703080d03440702c140300b01182180080c0c81205114a0000840e0030201c1c04944d07054001041c5105600c16514200b086413501d005500807c589501d414919408000d444050b031507689030200102800004885607141402c906110202d10080c1c0004040c01040b5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 163296996 1250 163295746 163295749
    0xa0f0f030209030a020411090409080c010506010f0905120f060c0c011a10140d060f03111e240414030d0c03090501081305120918010506041a1201080706091202 70
    0x9441004d198190b4000030301820a6144050300d000c0c80b03941b103900504200085080241e4680a0003043c00075500078009519800b0054034407168a8500304005607185408011510701742038120780481003803081c0e892222034550610308120045680240f6030350f0000e24912814800d10451403c4580c1016003015210082c002820020224402d4400c1103070202001140398880c80444050002800c010050302c0c0d905c904000f02d21760700344400da4041009464217031650601c002034510307415410001c1002d40741d14100b081b006100500402a04420080b02c6e080f098078550000c001800140038403099182100b010140382406000c00e2004015000c44082e00082c1c10a0095050783d000742040030003035032485400300c0751418828000e0002d125544201e803040e14440003d005100381070f20114102c078207084524070008000c0c81055001581000204504241e03c1451809079044240380c0780b030481c0c01000c0406890f401e801445a41e000078000f0032000703410080303c030014891401032000a000e00d40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 163298246 1250 163296996 163297003
    0x405011d03120a050d0213031104050402030a06180507091b02030c072102061908010f03020604090c02031902060106030501092c160303230c121e0a0f0f03020903 71
    0x1009610701107800300b401c850f250f0082055855001e01c4810864076001c000103600b0000c5040d2005503079401200384004034038101401500c0c0700c0c94018000b0401904581d0300c40c3c0c020170240302c0982c90360103010074400010340140701038001428010400b16119145600381028800340320390213019540104030b0f1642c400c00124001c001c450140300c0007550304480041d07211015400c408002e41c450300c005140032450090200c0c01000ae42c0a65840c850f580e00d03804801401c103070502000c0e522083c2444200112400b03500124614482072058a0a0041c00b10458603500200498100580c02080041c072485501d842160300401111006200000c00d194203944144a80f0907000b01400c6202400554403808100d80140d4000400c01842c040d640c90a00414254242800708440d00c02e081010305e000c060381c000e60302c0a18042018041140100100c0442580108074601c4034500075691342000b2104c1001a11490b550341c0c91b05140e50035400c0d0300810f400804414042414810b0100850580307000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 163299496 1250 163298246 163298263
    0x9010b030c03060f040f0206030a0203100501020106061403060a0902130815010f0e09160f05041407020607080a0b0405040b0703140721111603020f0606090a02030601030902150405011d03 82
    0x2000104045e1200d061158120145c1c02c4041e410400002c2400803480c516030003140701351180608401e82035103a200490a075a0688540c80c001010040e45071f080c00054002903820410007801c9020641e034901c0d00304266041088001e420110310303503007000b14540030700100c9400b41d0403100419040d0b04060740e1180194090085506d110103d40018095000410614407500c034002c0c11190000e03a501c801c044440b52500440d800307035041450070214665603404050042c405a0003420040d0703507000080b20b040b00000c01d41246941c461064aa0343d840d188501805980a0441e51109251690000d03040d41e9000c8181d001d1010544104612580d00c0004101d040d8001240b00c034146449040384005800c0c001001c10201701e0024111080311010074522031817920035020b40c0c004401d01e07090140c80741400c94405070010750f0040028504880ca03401940d104005060010722605250040769030b40040d603450701d40040c0001007e101179a000304482091180600781043c000f00800d012940f1003221 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 163300746 1250 163299496 163299511
    0xd08010621050702030c070312020c0d0b0106081e010306060509091c110705030f030403061d0d0c170a0c02090912070605151003020307090509010b0702010804050c04060b0309010b030c0306 83
    0x40c0e5003c02c501600c2882282c8400b08080c0860b000356480c1d09203110114028038041002d88251030003d07009051250712092080e40120b4501266803800c08159100607005200d41c44080858964070b21290700c1d490203501031070191074001002810704060212000d40506268031591003032100340d0304200c0103079061101c2c010720701d003c035621001c11160518190305508040e42c1070094141e041c442441c00800360040301e003d04010300c030740c0e4004001300c02d441088510840e1a904044004c85415000c0c90061500605c07500400b075611700003104a0f10076400580002002424040c550020f510344a6005e079089a1035102a10080343c0303034103200309188520b000003071070700351141c00051100341211002007040304050700c1c52000030741310b5400a00a5101b02c030a400811240600070816060460109040e00c0f68000340318030b4103445400560b28044001c0046a480c49180d1180126440b50701903080100f0003048865100c1c240396607270500752810080c80500170381c04025000300780e560000e4204e810226 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 163301996 1250 163300746 163300751
    0xc01030c1704020d020a05030a060b13021e030403050f0a0e01030e010b03030a030b03070302040207080a18060903020d060b060f0a170c04150e0402070b01360c030e0a050d08010621 79
    0x884e4408104150071035404141d050107075040c05000d0007142d800c070240d242c0040b13491200b400d00248050b0224015404180500b00c00b415165a40107000401107402600078144542003004400c070b044004e5020300b2a10300010001d0f01b0070340103540c01d03000e9011304d4010035009001c0e0081002c0469540e0003100d20090405440e00c658482d05c2c0c0701445410041e5401620565550b9900d00340b1030070a40c0130f00d42d003c00080540710f42c900000028640201501d5030383c0e5903404200d185808000a000f400c40341504d1031691607109901542e1181e000b483d0560400c1440758448115a801601c12080e480c0e00c40b6440c1540d4040014201140045506840c05841d0b03403d0f40129100c0100c0b0a80303804207585070000d20000d8070806000000c1c45060480d001c1034040391603c0031140c80b81e40c0010000010700244400141810342008554101b00f18848080c030380042c00030a0401c03c0340c60714a1100054406400181d604405194001205405031102c2d05042d2542046210109040084681440380256 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 163303246 1250 163301996 163302019
    0x50613110d020d02030105012d05030a0201032406231c180b01030f11011706040e01110708030108010b150702060304020f0607060516030b01020715090305030304050c01030c170402 79
    0x140d0f800e031500046500903000700101e68481d9007030744540c2c21f41100a883c26104103c42840e0225580009042d41e4000e000340c14020f0b000da0055025060182502c3c3c0b00b00f020101030005540800c1400004105030f0b90b070b20083c08032a101c2c0c551106540d851281d0342c054204001b0042c1681541a21300d4011021400907401c92600c40007101071403800e074000c2100079480000030a00010394010890140a02503208400c400400151130040c80b0000ca01d117402050030000b2880d04d00755002c0d50440b010f20001041110151820342020740c07000104450b126004401440480400d2085144190041d2680c0206440301c3d00542000e000c0c022009204000000000301151903a00c03040c103a1038400f900b500e450317040625220f03000d800d00f2203014410240401c1890300072403090295168108041e000b42c00d43c182004848034040d0070b007500c52818030511250010000d07400b080114403450054024000601007000010282c0d40c4032010482005120b9440c0c11100e10100c5000703821540c115002c1003100c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 163304496 1250 163303246 163303249
    0x1201061d040c0b0f0a09060801050d0f0c050616050d03051015031401290a0504030b0405030405060a050c010c0504051f0e0a080307060b04050112030804030c020d0f050613110d02 78
    0x21880e4003c03003440c09020401c03603000006440a000c80000644a4403451501c0d411708a8081d4000d101d450780c400030740705002010030b48810b00d00c0380c041d00465800c0091500c0b0130100c1d125078400d8140e4404d01d0b402d044260b06214051140030141c0c20b1500d02800541410260072070b03441c40c0340c00b03001e4100c0e00049008920600a50202d0000f1840080070f480c0c40d80c1d030781c04510005d00c04114a42e43c603a018031301d0308a800018001c44290708002d03110742e07080c1401c50301e8400c400c510047c403c6030180300421002c0f130980c0d20840134040c1d405650340e4540d9190301023640142966081c0101000f40403003070000340070035036a2100264691884100481c000d009051048805040d60140990054410200410f0446c0013200400181e80908010f0251200b01c0c0c0134003080351001d204210b0076401403407007080002e108070f8140f9000f074082e01d0f2490000ba0181c0000d0089903a02104892402c0048081c07400c0000605c0965482403903080e5030380c203d00c2140c54109145110090b0907203e0310035002c0c0710085 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 163305746 1250 163304496 163304513
    0x3010f061107090504032006190207080d05010306050907150503070f020c091006030b090408092809090215090a06180801050c030f13030518041404050a021201061d04 73
    0x2000f400d1030030702c2103040604010740300c4120f560b028004106160180c21b00e0b880001203403406118090002c5c0b0951403000568402074101660454143c5801c121009100c078090145502031030003070b440041c060801d008074510f0181158000c0320f0071144103541e08241c42e0070105a81d44503c0c1070900800081e08003504a09010703101d40c420384d2140d444000d02490341d044c014500140c076400e40701007083c6010b1200b00140803078200e400403c5c6110410003480241420042400e40c00310350360300e0001a180a0926034007403001900040380d0a40c2d203241050a5141244021449681c0c2d445c8891400203d070780480e080140d00c0c000e060900c25544251880b5882d00300010b00185580c000030007131810040004480c41c1c0c42560400f00d0b841480700400d4844204281d4840910f034181c88083c41c0c0728005910526003413044241a50103660b03003181c101302d40010511184038034443c502038010101c480c41000381c5c4022003030b0a07030243d85c580401481089078a030780c00c202c11400f160390007120780d42c1d61416503507 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 163306996 1250 163305746 163305749
    0x403050d02060906060a08060a0c05131d070503010b090d021c0b06120705060304030e03010f090f02180603030f03190204170607030207080301051002011d031b0303010f061107 77
    0x1500c509050110040c0e400b00300c2e00e00480700181a9161515100100200041d4900030a001b6400803030120f2103515295003c07004406284c144203003000c40c280842c92050a040e03004441240c0200302c0c40b884140402c051a50044080c100f40d820355040603803255403402400080c038000c0c45e0601a00041d90b40b40c2c40504820a20021600200c900c18604141088015101079008518081c400c0c5c00d200404a070344025188081c1880341503a4a540f8100e0340c82c010300440036015561002c000a20030494042c2944050148098102d4400d035881441100d41c150440241c040500905011071964003008403505511006100d90312510b980c8008400311803405060a58148001800582603051002c0c60312010104c2003a9106961420b00a400b68490b00000800010302000184618a0141c984c6840780f0070602c0006140c100c801c08110a840c910b403800c01c416030011139611f00c3c0c010005105501d5201d1a0083c1d4107652502d40518425200303130240308188000194102c15200d41041800d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 163308246 1250 163306996 163307003
    0x240118091a1003020a0e01031e0f1707030e03060c0a0309050102040e0114090703090206030711031c0218041b05070314121e101406070629030d0f080c0403 68
    0x10710b814030104021080c042480228003410361440c00150105145020714101da0300101109100c14550700e9880030581d0a0500310340c400d0505041c0008141c0010f103400a084041c000c03a5074403040c40c107000e00081c05800d2524407990281c800c010380c001d131703d4054891a0343d030382c01c0100784c6c0300303240c940f4601a0003203070000c1c9062102b05000041e1913030382ea0b01b21110000240c0b41d40250391108001281500d0714100b002e5082403042004c030309507038840c00303101c0012400502500d00f0903d5480b031400c080c03200c2028514500ea00402c40e440c1c504081c0300c1c54800e4400886003040f903aa03554941c00e4440c18a0742e142c03820b000b40800c41805243c002c1043d00d403049444c182c45662400882c080400e00c2009490a07288441808605614001001c0609001304001e8800c0d688852030880800986a110100190004418000c0200080c1540a1000e12010ba00c00c1404440c840101c0c2c003c01106803070380326201c0d9002c0e5a01d5401c03260030844240200180d807412030583e62701c001c1081101d00c1187e0004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 163309352 1106 163308246 163308293
    0x18020d05130803150109080613050f0a0309150e19080106060c080d0f020d02120118200a0302090d0b0a0e01050735070224011809 57
    0x841c441c90525020000c2d40d10b07100c0071808c2ca64181c0b8614130032611f8021107000c128040c002500b20700ba003078004002c100c03041c4c0c0300103062040e10b10540203025002d500c054589880b4001c1840c4c4110f01405440850032a00d080901b030329040d1140041551900c200814901d00c01c07401d80240c1500040c0040c100454110410002c040c189000070b4240d81c02c10030801c0d00101800a054a0403846807021055803512601120350400401089074070f600d40300f000382200c001c610468a020390b040c40140e464404001c800d900a1051140940d40111190050410003c5100d210b502c140c001c108288580c160740348645081c0d038401d40e012008640c0201c02c25403901d12003d01c1d01200c5001012910740c80b10420310800ca080425103000005170000c1100030030b1380c68915040c071480b61110800e110b2562400c151074410b448050315000c01651110fa400d024400180c50050582c80e0101a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 163129496 163309352 := by
  have h0 := BRFrame.cov_init 163129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 163129496 ≤ n) (h2 : n < 163309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
