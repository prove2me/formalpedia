-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0475
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:59:53.872289+00:00
-- url     : https://prove2.me/submissions/ad44681d-8b8d-41d9-b9c1-ec74720e3db2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 85251799 ≤ n < 85431655 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 85253049 1250 85251799 85251827
    0xc09080c0a08030f0913110301050901120c090207060207050708060106090801060e010608040c031a150612070807020f070e0a0c02150c0708070602030f0f01050d03200f030307050a 79
    0xc01c521032421500300d030b40b0b0042d5900d144841300b010038000803e40381c1e606040030041d031146c02070000d804000c9801c035856000303000716400368400e5000800d4086407007140c4200d0b076501c00d05034803a051405aa04000303402c80c0804a44894080003584040380c82003000c0006401c5480c00703001c240d450210081e0400025a204814a0741410010002c9031642c125190440d04c0a0414000070744c2e940c90441d52400e5950002041036540742d4203928030000844209103da429038402c400b40d22520720400403540207021003403840d54800000106100c0c401c110340c130b4021a4074011039800c0c03854a50346605152a640120406440603000c000307481c1440e000d65244540180064284403008610301d441403a0014050480c4410003d244030811520500700d60700160400411516030400ca000f80c0d404150a40c1c1f1281c0503071483e400800e0f20300d04089942c0000e641512450080144480300f95961040d0703104101c80c41c000c01c240780d40c0401041c0001c4d80700e24200d54138035a4498800303502800c030b0b034520411 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 85254299 1250 85253049 85253059
    0x6030501060e0f191d07030f0e1b01030b060c010f0b040209090106210e0303090d02030310030f020d080406050d050a06271512020102060f06011b080702040c09080c 72
    0x2c601d558642d64404103030400244d074003114140d03610f01e0a803651480c5521003000320201d038000030821720000300b003280501172964007400b8900003900c419090b20340700034041039140c102e9004001e81000b0300e10440b40007441810082000800301d8006907980d0442e920103107440e51a40c20001b042d41c403622450702290304c00c403000c604200c1c220700811550364050140e203080c8601211050300d4021b240148102141403030308284086840114810348a400c103a45034401d038480d10003c1003400d4004816030348202c1321040c101c48214a583c552040d0a40c642100780d800981400030100030072010b00040000e48100d860705980c1d0000c0c20070078011108020301d00303030301249048002c1c050007600e422940f003801c40e0701d02a50140844070800c0d80c001d104180d540440d404480a002800c1488001c0b010140e078000d8003a112030364de0704240f0400c00701e411151240040d144e45d20100814800d2118051540c0c064640175082c41102d9001c50116004036040c4004541c219408110907982000b002c81c0035507050361 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 85255549 1250 85254299 85254317
    0xc02070f050a080309060c0307050a060903120603080f180306010f0e01090c120203040501150303090f0b12040f03090e040803060a0801091a0a140f090111030903040e040f0803040b010603050106 85
    0x1043d16103038020307003181c64840c0c03070001552143c4044c100700303850742c2c5500038054548481407440c020000300154070085000c6400c0c1d10386c101417540607100b0501241e0308151910f10b04141c00d0141d8030381c4c0d4070444144140f030344000e1402a0350b441c00c0001038060958400c800d10081e06051054101740d10590002c1c034514103000944c005194004132102100420480140c0c40380c071b444c81c00f2805000e50f00e21180110030900340001c10315078006508000c079625040c03103c107420340b101ea02100500ca40c007444400000007901240000700d510b2000346e00f40b402450101d85898a80225940380c03001520b043d00c0c50030000c800c0c40300c5458020720709401010000001c01a10304c00b030703403406400d007a44503903010f007080710b003000078030122041d006810b00f00020102c1c48121302c0c1490746c90308140e42c184e03042d01c82903107400c08410549640c0700469000ea03c81200441c246498880d28030900c0d00010022199130b030b02c510007400050742e0031001c0e5010318400c51082d4040c1d03040100003800c6030700c141e0003a000c111160b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 85256799 1250 85255549 85255559
    0x10b010912050a06020f09130f111e0a02030421110f01080609190c11070e100306020a030609020d0212060301051003020f030f060702100e03030601080117100c02070f050a 75
    0x1e8503c05070b6804400542c8441c4e0201905449024920b1100c0c0c2040d104040e12400883d141e0081c044411000ea0400681001c10b00e640094002d0166042d84200308140066540307007100060003250026104480ca010744410f404d015960090103a540d42104419802040101884071035180003000d5a600c00f085090ba03000a00c607043c00b41441d40035a240b24003040300c101d40c00316482041c4409a1040c02000507856004080c3c00013400d40300603501801d1400308803e0440400705010700074803116401080c0c219101c0b0b9000b544405050741c1450390716000044c100082e4009000700989003600181ca0385250000c5001d01c000c020683c5201e649081d0401031075415007421720007501e0301900c82400044000011a140119421030b2440a100b00020080e685a002520b0030011344071142c00d11034030545044c86a900c2c041a9005404154840300506c48006040204410441d5440c1181c0ca002c8014010074126844070000b4401078000a40900c210760540c12020000c00741540e61941a910349 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 85258049 1250 85256799 85256803
    0x9080c0306070f030f0f1a01090504050108060f070201061a030414060c030a02090a0308220f180b010215070302130b030103080403030c020604030b0901021305030d0c060e160305010b01091205 84
    0x1c0200f0605041e079a400380072a07480b1507800340c4400d81c01801e00300400c00441c5203004090b50280a0fa900144010310081250304040c025903040b200511300074056038603443d8650301c4900c4014009003c6650f140000664107241e040685140e00c40c6d06021656801c0038180f2040032384020381d05194036070002c0c06010722403c10f14100c0e0ba0061543d0390051304d8440e28070000e20000c2044e0f001033f010a0b0f0204100280d8483d1203818203403421207013445401e05603503000b1141340559911400b194014081e819000c0e00740250002c030700c19501481550350740100b403100c24460000c10384004000a60101e040c102039202031078880060f00d410100395041d9890360303803440b07024811800020100640f0a10765070454460400b07480c0a194030806003142482c003035941c43e000350003401510482030010000001c180c01e01151180c181c03a001c1d59911103100464407503101900d240c2c40400740c1072090280001440c204640294051880381001081c558000c900051054600e40c0000184600781050343d00082e01c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 85259299 1250 85258049 85258067
    0x501080906060d0201051c020f0d0b0a06020a030e060f0a020a0b010518040807080c06040f02040501051e12030f070311060f01080304060e0d02130e0105070e0307030f0f0503040609080c030607 84
    0x109107021503443e1501c0c2565059882103d080301c207c0c1c0d0000c100807207580c00b05c001401244800759400c0012803610405c00030000ca103407080d80090b0300140000380120b441413000f08142c890140900345402501c281501441d031090703020f200142c104178500820002140002e07401803c0807600f150300b0032500c0c48546001000a0801080e80c2c2001900b60101b00d800c1041c2d5519518400a0312068582070608020707260000804901c920328142c0049a645030844001210f0181040300d0054a034095041c001d00212241140000c0d02c01880005054012000101000d52003582d900c000034554540c40e600e410409070060114008cc1ca0041c46032402c00070655007190700b10b01d0a802d070741c1e910f400403800c03100450303501940211062843c1d101c60812a0481c1400300d085038000c0295030b036805802c5441004200050394150840c1c2400c1011400c2c0d1050341d030510740240301c0030248011660ba110714680c89944070001150000d6410880304009218056038680300360090f0009260084004206c0d041d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 85260549 1250 85259299 85259303
    0xc0905011d041a010e07030608011e020a0201090501061419060e0907030b03030f0304031b0309050d0203100501031101080109020702011e0e040c05041503060b0304060c0512100501080906060d 84
    0x752020019007030200ca0700e00d600701002c0c011201005561114411070f0140303000c0754400040703030510200103142c100500c611070040b01c00707510f580503000c2d22500328806540300b00d6080c411503480d5041c900c00700740c6c203105000c01000d4a0003144a180320080038800d0f2000e002403d45c41000d8004000c10486800c00310840d010002110b480120b5a03401005400909032840c0303280d058400422103041d0422510000c5002c1e81c0242c994400d540142c8001c0c41524a407808018005804070004010307070b00f04402110b44141c0300800340c4e07000755520841c0108540c000d0f4002c1d0340504004081e12700c1c0b56001050b01c5d01603c000b20b405d515101300c40d0000f038100e9041e0380c404134070901c4840d4a850003038818070500c3c180b03240c01407080c095441d014a00401d15089802001d81b564000000850000c1c00380c86000d040b07814201c581415a540c039141c10b0020b111080b5058103004081000c1960704806804042c820743e64003012000c401e0400d4001408140000c00458075640080c00703201c113a0b41d0308100ea5608030703 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 85261799 1250 85260549 85260599
    0x30b0f090103020307260609100b0d0201020c12010e0109080a14031506030a090b0f010509060d050604110a0305030a05030114150702041a1206041406161404050607050a0c090501 78
    0xc0f4030850100e14041b07010076401031038010042070140c2d181e000b15540304801e411030024041c040040040080c211036a21009026074070400e0030303c0441c1802a010580c0603000b0300000b90684e4011400341c00e558200c54112214040019030440950304a401040c0d6084989881f030b003903140040c02d0442e01441c0601003441007078088001a84d28090390080050307240d22804100c2141402128a01039440c20301407544500340c800e002400d42d0525030441d20705150020001c011030b4940e51102c800b08901045041d400c0845000301001087e000c000510300b00890b59502641c035854182102c641c05441c03181c0c24030a054031025910340381070300402d0b1740350281c0407180080c0f0b0304c062112650741189010000d540103400c0703140e09030300e410f80810b41e24801c23405020090510031550300f036240c842c003003142e01205520141814810440c07281c0103010b11014440b003d14a042d4481000409030781244208503041d44c4251150010014040081e078010012200248025414003109640101c40038140581c04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 85263049 1250 85261799 85261829
    0x20307091a09161d1903060b0306090d020c060d0605060a02030315040c1413170a03080f070903030c030207080102070803160903021f050909040503040816080706210c030b0f090103020307 82
    0x16030780c5d0040200040c00070700344603003001da6280b030900040d0903010800c5103e80218400640300c20000305040b10134400300c0d40544000021642000900d0700400c44040c80217035200d02c0890070340c84000c001c01040600e60015a100d181402d510080340c929489075600450418051580740da41105507011258256001903440d004515036840e0962800e5014114078bc00385400030001400204000541c0c80c029592003505642d8040f500180c0f040560360540002c0320a0810030110b03100ba0038110249200b072041c1c9402c19a600859801d9800510098134941000414010940b800c551050b4401e10b0301d0030420301c1c1c40d103580c0015521414018500c0e082045800c441480b47d17201d00d0841e049808001c20410a504090400954a802500410035903200381c1e40200000300c1002d01c084101c43d1184001d1640905041c01110320542c00b0b0241007140d005005a03801061702d40c0034071a2503240b103940c0012106031748800c10000203d089085401110040f00510250724085810070a45c0c008000d14205 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 85264299 1250 85263049 85263107
    0x203071a030610021006090c0f02062502070b13140d020a03080d0b03160f0b040b0703030c0509030d0e01080721020a0c150606030b1503060d020307091a0916 69
    0x78000b501c04070172001460301c0404201031182e5401984890407990f80c900381d402c01a481666920030644107002c022405c5a5202d2501d1303074017039335103400c83c60380d1040d1180107907103081040f1607400401c8180c014200c2120240901801c8001c0c038030100b2011a80100310249a13008240e2b500349900028013507080016415000943c0382d0440e0810a2002c2c04aa1040b000f101c080707a0884414003d2902c0207039901400503003a54018150740907030704550012481c001c2e4039a02580145500004c01c000d00406100400a6940c10b2020340b002e03401c0e88c1c49848000c20050b00040c1042401030180c01881900103040d68400500c0180d80b9505002c40350040c0d803415460020b0303c200d2010354004001185e08098030304d00c1001e6070055011101c4585050001e801d401082014400c0145100f225490707050001502a103010040581d0450001d4240d54200f501c4101d8007058580c04100341d004a00c0d40090303401c19061071840745502c01d0840c500016441d000c004010041d03003d04494030070041c0131a00c0b0f100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 85265549 1250 85264299 85264303
    0x305150a0c0c1109042105130501030608120d0b060d0903030b03030c2a0a0305070e10050108070302090420040e0c0c060c3a0e0703030203030a0e0f0f0a0203071a03061002 75
    0x1007841e600c6d403a0b090340b1002da40080c400d038001c0108407440300d01401c0028155010b07000721025101800040e0002505d001a107144607000a662019901d40394144600180c80740340080c00038504c110303008a141042420042c080d94035481031203019600801c6000c05024000c10030002410708030542d0206802c1e0540e02013900000030103419072000042c400003040010010321203003100e118441c01011580c48802c0e0000b00d08192052601080d1258000361105d40303e81d0007081d41440c020000502c10715510b250751168a2082002c0250100004042c0100549402155030142e5144c0310a403a081a448480391200409403d03e0201100420706420705800072103d00c0c05c01551258012001882142d1246c000d524148148280c41c6001a50f204599001c2200b10689405400851544c0c0700d1100000080c040ca20302c010040c090090381c0034101200f40000d44c00d164140c4001c0130004603070300405050098075070103248045000ba0000000010450a90345c2c0160b003140c00c81001300411500703074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 85266799 1250 85265549 85265573
    0x140709170307140109020a08030c070308090102030d0c02011a1c02060f0d020d0501030c051002120903010204090227030706080a050402010c0f14011b080109090305040305150a0c0c110904 82
    0x1010030340a41d03081003d1800550148181074000c80790705525070f5661080c81d0701c0380b240d19405181c40d0404a0113102051550780105403260040c0304032864001001d5a50003106e810544010040c0d468003504040d10000b16420b50344000221480002062052810300c5040250394009025440114040241c0d500c00c5040d01e1084c403850000b595211402c26028000304024001140c400c140c0b00d00118007070400ca004038207a08515001820341e00c2440840c40125005140402e6056400704408988200540060070940b941d0707800400e0344400b2540400280300d503055107280281c1c4003120402c01e103980440450b402104440c030004007031721180012540d6440760100030b8035041c002c43c40c010401c800c0455100c00201c90344001c02170044203508e501f0380389522140e0b030000640d00300014810f6580c2c647c8080e6619100b82032013480c1540c1e079554541407090000c10500a0070f030034001c1104210142c002c0c000903060750710300004410099030354588924405800c1d07500503940301d0b0000d42040300310111a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 85268049 1250 85266799 85266803
    0x702040e0c060309070303020d0503130303090819170610090e061809060f07020c2206030b0c0a020f120706050405070f0b0a021c0e01050703141b01140709170307 71
    0xb8554034500700800319642d0300c0500c822001032240081014a00e441802528052541650b0000300d080f856282213025101d03540c8280c9400344100a5000a414220300d41d000c1c10446445000d40200203081600d606e040017405140200c01d000c001c6d8800c0d0358000403510070364003200c00c01e01da55110503003c580140504600c288001243c801404801e50000900c6403080080070f401032082d58420000702c1e12070140742d8100e600034160380c48501d0514501080ae03000348038040c00009005940c1d0311250540070b0140c65601070b0000000301743c5062030b414440b0240300103000005000e260100007031034003103116819010b03000c55507440100d800c005050184800620761444011109038491070ac1c0340c0140d0240e1949000744c0b080c95100000c010690300d00000200c11070702c40d00d0700749604c04019250366000d04012010002e02d2400c1d194800c00301c00240c020303080101d4040400703600300450282150303410b5a0143e00c10480804000e001c0b54080d1a00060300d0f140c424100c6000404810310349903020322840 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 85269299 1250 85268049 85268059
    0x1a04060903031d0607240b332208060106090510030e06070306050a05030105060303030c032a031602010203090607030e01320c0a02030a05070311060f0f070302040b0702040e0c 77
    0x1c182c2440050302001c1010008403040d080f1b80310030844841e0481e06180e0210390060301950003581580840409070f24509400000d10023886c140f001000015844602c1d01007240e281907070325002c046c503407007050f40290035040300402c0c07654180640640491054800c061081105002c0200450300c6a00701c0326410902c001200d159003400c00026000e088540a9a8014410744000084503e01409824098000038014516544440c00114010f500040030082c206a070700c000803140796030380540115043c1314011702c927450303007885c440d41c140c1c5c4154211004110780c018010700c41301309404900c1c150800d020342800170381212180301840c05000035243c21300403000c450704140103441d801041604600c10b0100f00300401d9894041d0103881d401010f05600040e841070001144041c01040141f4000e0700906280041d502441307005803030440b0856802c0c22400940781440500d60800e403160360002c10a0400b1340c1040d091411801d6140100f850203440791b519014070000004051003001803c1c540904 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 85270549 1250 85269299 85269307
    0x10b0c06070507031713151d0307170a030b0303070303050103052b0c0302071e0312031401060305090c09040303020705160501020a0b100803030718050405070c02060d0b060d061a04060903031d06 85
    0x30b0000c01018403c5c00202923540408011407080b1004c4102c940c1d0542c001c1100380d14041d0031942920300d802c144216001d056448507591030690b000c20213400d6403842941c0c0410302e98118940103003410112a07a00640c541c540c10840d800342c80b41c0c0b140f8400607645282003c691005030904a01d45103442c0e100b80e03258003102c404102400101004c0b01d040c0ca0140c2ca9000b4081e001c00c108030110f910701c40d17405007001405001804800e10942245400040000c1229000c1a00c200066401901610308502003503000a0b20010400f0074403003800b48030008918207a00916040c000707500d81102d1000200690060340005801040381d0f6141c9011f04100b400301c0e0380302c0c90100c601030032040034801d5001183c0c3c00044001460310b054064544960800d40d10200d254905a0a01a46030000004140c0c2a81c45244041c81c9464840107811515095100401d6442ca428035800d460344142c1c54a10a0840400041c0a11904952494102c035418903150000d00d018494281c44002072550155202c00001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 85271799 1250 85270549 85270583
    0x50c15010609060206130515091c030f052a0d06030f030c0506090105010503030d0b010e03060703050105041a030307030503090a0b010b0301210533010b0c06070507031713 75
    0x190b003500c242d903015000c98402c0d403649a4051000e0381840b500a1095101c00e1a85000309900d4007465002041d9500703c2d524500056100d40c0c0b5824003d504500007a5242440c0c68000d03058018035812801c01c20740580c2d89681c07129040e4800c00c4e00c2c0d000344128000040c1c2011060800d600190056421100da81450801e03443c00500a00d01d01030141d4141c458580803030b18104c0306214480c100c070f000400843c41c1051407113408016100d19070081d070612903244010042030b01d040c05003511441c031680d0005000d60505081000326440102d8628851100c41c620413041d850000864141a4060034200d48a40e0340911251500480030303002040c09141c00d0000404007148000703181601c00c0242c03841c1c01201c200d00c11910102c0d00c40d101420070792080c4051f0514048001e04103c5030f00000070319001344902d0008100c4071001c00c0e07100307920020000501f584e108030203028698000c2d555103805890700c540c07a10000c107500e041000358030500100340c010423070419000450088242c0e10400f03028110000b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 85273049 1250 85271799 85271807
    0x30b07090e040807061d0a0221160f0801020a0207050603100b0705030306100c0206070f08160804080c030703080301301208090706120506030316080406090e060907050c150106 77
    0x9004030365007400c02d13441c00034000340107645401c4029146d00501c0d04840a8080103d4640300690804485441d44611060030b401400350552080f804c2000f54610b0b854815142d007200c00b20b900c0b90141c0d0f44140020303a246e81c0c0c081255802c4900440b031150700c03516000c0321001c43c000c180d40311564402000800b5000c100d00032000d14807401c000c80c0c03400401403c0c4202568101c04180009600c13140c00c2021400140581408001d454059001d0509000525041603c0c00356071160941d04910702150030007043c0c03420400340781071f41d1040d409000359070324540d10070380c1c180018080c08209040c0703001400004030150400501e0126543da40c81d0b204107103402c3c4044540b55640e0130a00244000d000144410703070005040046030b590750780758000f884064401d40d000702006132015906000030484100c10840445c00000001d001d1012665079030b14200d400b50000580d07a126409407000bc00800103a95500c0d118203502500c5418256500d2400d01d290a050000003444002c2000000c00082059580 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 85274299 1250 85273049 85273057
    0xa05041806050606040e04080d1d03040911090d1212020a0c020f0d0519020a15020607021506010c1e061a010912150c02100204030813090c09030b07090e0408 69
    0x1c1030208100c0d02e4601c184605446036005e980c0c404203541c40414000b4926000400c81a000428002000000c1c00d030107071003c5015400a400079413010070148070440b075030300c954400c241c81c81c0230045c03414040d40c0100342501006c0e207024140c0302c0d5220306201c40c03901400255500c0f001407a421562410a86005484011004e00690190b00480c000200904140402d03400a0780c001c0c004240100c1104403030404503103014400c0ba007002e0741140000703500407a510b030440c1c038030401c2d00608102c0c544a403000f440c2c2141112030644145a0ba030901031266004030380ca00c03420341c112041d110421a09284400040030520303008082500d0203ca010f258240d00408000c0070100349d90384850580d85240018800070190030151000c3c2d51184d491103d07580603802001a6019401918030350b25603c05210200c0c1c01c280c0c025104008000740ea00071514400d400c400151010b6002003011440e406001408002c49000c0241031400c0c24010501c4207004180320f10091020700c100b505245400d142403111a04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 85275549 1250 85274299 85274303
    0x20a140102030a0605040203070918060503030d0516080c0a080c0f031302010f0201061a0310120c090501060801060206070e0301020c07030302070305060105010305040515151f0f050c0304140a050418 87
    0x320703209002c80c4a180030700803230b0300a512955a0030041c50604030340d42d440e2415000c20040c0103960741030006030740e1010f10141c941c8a031008000a824034061011168a60158091000b044903503c10000c0812994056072120440303464011040e96800c84a184540304008120031003010200801c00f4a40021180016051003aa039a0300c0b402042c0b2002e900365440382c000d4417003000b000398203000104070303c0025540c0300c0702c40c4140400c41945d1303c240d128170982500701943c458044020070f11880e02e542c05000c3c01040c0d24505110b0700c0d85440e80085d1070b000c0141032101080000307940d11a050383c00350152084c12189000390782ca00e035600d24001c1d43d03403002448110b030240130790000001d00b5030003445050f00c50381e004030150401d4103c4020b84104410000d10450044241a00407043c5c0d4a0300c200003500030351100d03c18016000307400009080b1803140800d076002c00c90301308110302c0c0089001c4144c2d0202c0d40c0c85944150f0708442c14001034041080303038205d283c01502d0480b030004184025004a02158 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 85276799 1250 85275549 85275551
    0x14010b03060310110a0c1505010303050301210b150a03080c100e07300c032f06190903020402070302251a03190501080f0c0108090616020a140102030a 66
    0x1064926581c003604e10342d10700500c080000f4050107185602070603048a0503846000000d81c00040c208105c0201c0318280c1080d40014004401401703041c04840c4ea03d0b02e0342940800f207409000e03881d510030244100041c5040d100480c8145a10416111201204082c55200711250748075451404216a96011170010f400404c4c1480d0044446c0351000c03400d007003038904100411034040086401c80b00840d003890320003e17100e904242814003084001c6040b6000c0d6100e0f1b0f0030f60344c4140c509186181d262041c070804000c2d407020000d20601030b54910084418044aa0346c03a1584203032917200c242c81202440c1d00107900607000003400020941d010510740c042d0a01a10305d55800000040e03100c00000d0940034001180101c081c4109004145074040c561001c40e404c20035010b2103454102030280c4500b80c0c411301e01c42e4000c904e003564043d028481c000f40440300b0318001c4642c0c50040c9034113607140009440c03c000c080c04030307601001c014428020022002e0b0050045189592000e021900070b6004803540b080341 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 85278049 1250 85276799 85276813
    0x20a060f0306091a061c0c120b090f04020906030f060c030601112e02040503160501022503080703020a0506010312020c09010305030a0324090605090901020403080a050d14010b030603 80
    0x3500780e1082001d050050340c04401084d2540c01401070990064007001c01042171412007008412480c011481d544603969120950380005c01c0c41d41050386d84218101d44100c48290400c07445540740104240d101d50100c9501e1055111100441d01385241e0311240845ca020700400c00080f410038900542c0281d0003070341c5140913510200d840c90b0b215141c200c40580c2e544a0b5119801d01ca4040c2d142520303e440780480010700e00341d0f43d1400030b890010200c1303c07944107664000e01006250380512503412b0310303142c826a541034000d40300d0b030340085c0c408580401001c0b200042001c0090510800481d40200e80c044101c90041d44c5900b0b00400b04041104004d00500c504144c00d14282440400c0c2c43c1202d074090015401c00b0251141500601201584a4143c00c0700000040c08204100c2d480c8000341a02c101c002480c43c103100c01d02410311801000e11159a004000410004030307510221000d030032691030b1040c0c54510604016000d460400c0441c1300c8807000c0720020031450600030085000303c00440455981c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 85279299 1250 85278049 85278059
    0x3180e10050a080316032d030b0a050f060c030d150e06030d0903120e06030a0b03061b040302060f0403020303190201050603013308070603090c0b0c0325020a060f0306 73
    0x480b034007500c9040d40050004043c18500d914080440350301c00d003010200c41d10015807000040d800c000345050504919941c120040d038051040100c2c2d14425207064060034100030100390146100000d5902a03040002d81d0015203009000350350164079012400c1c41161602c4030700c81e0300100c1d2806804403030b081403008074696180016810050102d42c0e10f410645138070316101e0100002c200c1d00c111042c0805c0d8102000ca0350390366002144501400540003d195100a060500e4070000070f20401800031401944480c0800f0384d82035030110380d4112076640e41c0e83c074150548150741c000c580c0000e40610004c01d0003080314140b0007042c180e1031041d900030090382d03903000209403e0364004240e180e10380e0094119282c5401c00c001c1500003290380000f103215003e55443c4000d14200440d0b00480029964000400400c001031401c54014604003200d07a0030508e07012485501c0307114800005406407500d040c0f40100809c1e0100200c84650000d112a4003e41d440c00050520b1034046000b07400286483e00100e4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 85280549 1250 85279299 85279309
    0x1f0f09090b16140313060e07170f3a02011a01081005010503130212070509070f0212090d020306070c0201030621020906010c0c03030f120509061303180e1005 69
    0x22060324a03549029114200c11903007003944d4805000e002e0b01c02c940c45140c5c800b00e401802104860308107000140b4944d450702c0300c9070380400110044a565900141c80041c1200800501150800d154650b006054082c800c600804146805054048a64602c0c3c65400b03442d019804160b1102407c0540344030f5000321401100c1e000701c00c4500c0c00184100d054180700035445203002c0c40e4000302c46c40c0b100310524555000194480032880d50510319a002140500090038405500c2d41c0104440c107101d19684a0110302030345902148040131411500400d60300003030366443c5500559a0b03000350a0792110700300100c000301481001e420030f90209040c4640010301e0303c01c109400075183e5000030030b5403515280f030f403c1180c01040601480c1c1044803094904000c16200d400c0d02e4000d40c401e07150009505141800030308040c00c1551a807600c20700d40b404000d605580842c0080d07201903010345018600c070f590728090701c1d0014034807007490802946010200f92151480c10b41806010240403c0c0001d968038000c002d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 85281799 1250 85280549 85280581
    0x4080d0e15010e0f0c12070909090c14120304031b050a03030206090c010f1b02040b030102121e01060c2307290c03041a251401090302061f0f09090b 65
    0x3d51555410003280050319101b19555030030000d81d140070040213a03503200e00c209913241140300741d484c03003100318040107040c0320600003031034254041d24603011080300e1103659916809648405041103140161100e100c070042e034039240c082d2400500401e089604d90034001d42d00d840880e40d8420510540c0e440a41541c05490101803071801c0d0b95641d511078000d4078082441010406080b80c000d51100001401681c00703001a002c2c010410300c03600303207500d40031210354401071001c0e1540030003e004a00520001d580302e030b03151440c01c0e0051034000d1107691640c21301c090249080145003181c080d20030003103585480e845440351070b6002042c0840b1401080d025200d00c6110310300c5044401d5008020400c01802e03c2d64501c8130b510001d40c2a18100f05a0007007081015014407101e0288105010280c010881070f821001c0341c040e10503008000d0000740da5006561001d0251181c003811499031001d0b01040c01201c1c00102410700004502c04880c4e403600c8c108050300050700220b5189054100050100da8503005035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 85283049 1250 85281799 85281811
    0x1a040201030b0306010e1909060903020f0d0801030b0c0307020a060603050601151404090b060d0c02010929010303120b150a090b0c030a0309030c0501150801060501020d0804080d0e15010e0f 83
    0xc911b1035164001c02e00c0d62040e15412869059444142032408210248a03800200740030340c000d0080d4400741c80009040c0b00c90960a502404803220050011803036040480f54000d081c00c045a940e5107941e4402e07868040001002401d107400c0020101c104200401c80a04079080d5843d50014207051480980b9140d81001881e102c046040c0420880a1002c5d0882e840200b400b5111030314000070344c42940c1c02c0d10240801140543c5d1540c00701800c0000144800040f00260780c3d208050241c8000d01e00040001880090f0030407040c06207986507205113074407148442e0304c0101940845080700854a00c10f403c82c80b25000170554804001907001204011145400070140103103140040940c0b09800404840c1006d600304121591b0040005000b446040c40f0107042220440b5510f1601040a0a44032190400d0341150004100340c04402d03008519180c2017680848880d40b1150001c4440004005105e040116403040c808100400c4082c0d80c50141603600740238441c202a901d180442c200c00c442070f908 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 85284299 1250 85283049 85283069
    0x405010e0c040209030c0d020604050a060503060f0f0f220c031d0703020d08070510020301080313091109010c050c06190f0201200a0e030607050903150c0301030b0c04031a040201030b030601 83
    0x20312405150480b01f0f00c80e0f00d03100803c0d55042c2900c0380041900c1249581100c2c0c04100e001080c060503180040030f41703052600488a980c007145081000c40c00341544c40382418021040c501e0700b224080c0c021003032035a0b0402094010480e4803030314078009000c0d003094214881c00c40d40900c03095119117404a032200969801030041007100e101c2c0d9070744400d00c1e404508241d40a0064a41d101c0c1030f400180002c500034454a001592103080000d02c1ca0362540642c2e20420f001441c020410300711001039001e84040840900306502411821b00701030b42016006030410303034843ca0000d486240716090381c0008241c140d19654036800285460707010303422542e040380850865240c4060b04080340c0d0007800103009905191602c000d114103080c011a2401009803a01804240040340844080c10100300c2c0300101071841c100a2901d04250780e003182d00e88818000130349000e080300001403440c41c541c3e04031401154048441c0700d005944015a49241e8030503201240001d007020070f064001c0c0780014085050b10f205480b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 85285549 1250 85284299 85284313
    0x30b0f0a0b03040f0f03030506090603011b1d0310020a11010204060504092415030e0304050f101e090f23011b0c0305030301080601060206190203100306050405010e0c04020903 77
    0x440050b40c0000b0011245240b000700d0800001e2614600c10310903c2c801c0c0c90100b0135040000800c0036240c40208914041e230716010102c01102c4403c000c2c120b540b01c840c104030119807180b41e07a20246030b040b90b80d8542c0521500b0072080041181ba402054012410f903a4420a04100e000c030b182030784100e04c1000c4c0012020b2000b440000031907032240114400c03c4405109140e002c0340c000f000c21100d039202843c83c0000e4201d884900781c141c020303003503aa940749010394503007810300d00056065100b01c00118015030440b440468901d0142c80140352003036240050803014415160018540c1c440307805044600d0b600e541001030118001442202c1e28180c010081400d0005040110381c54000b0402c400e0300c10000444c4c810200700d0701d1107500f0107940184051650f0750705001c0818070b01b0f803041c1c3c444011544170204000380b400341005c000c84c5c8484020380c00340e565152014411070181064001801c12858042844104001548880d0880c040b4505644440340000d040004a02620f1a91070705038010f05 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 85286799 1250 85285549 85285559
    0x50607030503010e0a090b090a110f01090e09011d0601090f0504050c0f15040810051303050d021c0c02010f0e0102040b04050f0d060c08100509010f0620030a050406030b0f0a 76
    0x100000c0d8170a101a600184a01e095220404008425119590705421403d40642400000241061084d00a48584d440004550002000700f0054414034102d0080880400c03443c440a4005203115440032074000c0322038011501442e21180d0a1144a08941c0b0f415805048a1028010544640d070030202510780340c80c01105000c60920308961890384999010000d0b40c0444099000c0e0001e4408030005050402000c4007100c222034002d818400307511591100e84000903030190896002d4030042d0800350b00c4403080e060854106082e805440005030402240030035071903055015220311031101400740000e940d900d104500b00d100d14000c0c20404a42040144510300b000c0f180d030711100d640603003001e204010a0311100200c81819080b000041c601205015000d0620f00700b4001178141222640c41035458000780c194600300c2481801d0a2200f084010418859401000c80c400303e840720a4903a41c00c04560010070170351145c041c200c00b09280202c00e200500f00a0440900c1045c040c00c4204114181 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 85288049 1250 85286799 85286819
    0x210090b150d0209090703110f101404050904082a060a11120a060512010c0f1b0c030501020c01060b070807081c060801060e07020a0218060a03060603080a030605060703050301 77
    0x12918950000902c00c003010040e11560681841213008201601d90036065142c2510340100c40200b0b9440f4903228504191a90384600340d92200c0c400505000c014803450341d45c0c03543c090003a030388035503481001da40802c4144000c50000301240741441d51170702070546590900c0181c0190f00c000c2d81070103600c06000542001082e1f84002c10000c1a1000030703003410400c01d64010542000c6400d0300525031206c1d800c100c02e00f03240e8010807051078408000d102c401ca400314000c0c290a240c410503010801c2d02200b405ca4040390b200400007030368001460487e0540c890034030300e0103036104d80b440410945c42c2900002da0310000100b62401543d0215000b450f011550302d40c101c064002e03104400000003403044d056100f0340288650340040006a001040721843c16014070749000c03004189101b9500121110001079844002440c10007903540119040d0780c450382c1c0802e60100054100405613481c20740080b007440911001740c48140029501800030300d40340c0c400d0003114010004001d003c82d00034001440100c40c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 85289299 1250 85288049 85288081
    0x90604030e04091502040f0f230a03050d08060102060a0c02030d0905031210030b010501080705090d061116050d0e01020a080a03020d02120405101a061c14070210090b 73
    0x100400114400000d915502e0000140c54807410181e58005407c00800300007050402c010680710b821181d9081c41d00001d000041c0703610384007001001c1840c101030031680d1b45a45840c0070b1600182200c1d6084100500901103940c20380f034a5015101d0701e0700180080856008091455242c0e5014600341000d40d8081c5018102900301250207000078001c181140700c20b070000030310419005c1c02d0309028514604104207044010f07041b1314108000b08041105d095004001c5410024040c1c034070352100034a80c201000141580215103c0c0310400141e1145000c145554a44001d03000d40203441d5140c144c00400d56004054403002e60150b004120340e000451000c101400401c80c06050241c601081c4003200d8089038011084240042d80d48028001481800c10003c0b207210308040041008000b65036840c45407007844160b080c41182d00041035040c007056100005030800a61000348061b20400e4610344070075108403008801442200d8000e00644072074002e80c4803c0350480c90750f141c262180c1c2001c0040b002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 85290549 1250 85289299 85289327
    0xf070320030604050604030311040f210503042312060708100803040b0a02010e010605130b010207030614040201080f0c09010e062206030b040b030c090402010c050318130509060403 79
    0x140340a103444952424442140314621a001915881c502840c1c00380445100700d4082100140500c810301040052620402c2a03403c141c403280b02006810f80544000b02850350020220301000c600000c3c00c0700f13a040340400b202880080030101e15800014044c3c1c454100004030800d50200021410503070040308040c1c0c001c8c16410805100640f203044052940d4040e50150002c4540040d5520400d5420b11500d1600a845402800841c1c9000c00250841d10344244421035142d8440c01741034140e0003001014021540b040d0103000c101020030101d2040c150071202a808034540100080d0307050a0081058400c0740a01031a0b81030044010045807900743c00041250081d02c10804018100032000141403040e4200c034402d5516414544010150b444a40d0030602079810410081d80c0d590303001c18413021420381600c1c100519500c40c001260382202c0014050828040051562104542600001d01c034402c02d65081d0001c1100c0d01c0e04c00120b40b800c03611140190007840200300064815490b401c4500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 85291799 1250 85290549 85290593
    0x30b0408040b0403050c0406210b07110a06060e0702030703170c12040b07020f030c0a08090301061503060608010e150d030302090406090915230408070606030305090406080f0703 78
    0x40d2070782c20302c45481d40f041d0010344056000e6982c5414030f15040c01110064107201030701e581c2e030f060821100d005100f9104401000c00943c0400112014403510814802c80c20f0101203400080481c01c0c03400080c4520f0042034079a0b40c4234000a840180004116140c40b503059540c038504000081500300550005020b030407c2220401c46007003900c600c44a81c0d8060f5000311003a281c1420134240180c0b0b007009580548516070002c0c024102d24501c04030f240c04031395410a445980d10f0019100007401800103030061520b412024005d0050301d54160b00c000c4c183d40144e2150400e0ba600e400421a41000452300800401003c03920012075040100084d41018801d04025043c03040b6407001406490040e0820340340f85642d00d80d04800d1103461440343d00030740181101001507004442140c41710721825502401c0c0400f054022a04028480e0700300d0f00d2440d0802401c004582d102d2a004089921041005202c2c07400c02c00c010802c9507010a1089089201d00020082546140d0f81e8401c0303524101c00243c528 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 85293049 1250 85291799 85291807
    0x2010e1e160609061b0f060b030c09060f0402130509100e07080c0d020706110d2a02060609040516090605040b1207050d0318031109130b040f021f020303010501020c030610030b0408 79
    0x200c2e046c426200c414480e00002c50b00005100038185049000240240316180344003c0c4140703a10755039a40c4100e43c10650300940c1e0b5080318041c00d0000103641d80b14070740101a00e02044544440fa0f1503070b0342603d0450303207140f10a1311014800c996440050b141000d250100308010500c1c00c54075030003000d80c1d83c0f003181c0102c3d03640c508400318129904040c0030104181d4a8000f1046030031000590841e0207030b2100395042181a800070000c0d07071003000070400d6019014140100d824803c0c200240400310110145e200049a100d100d8240504160320074123000e6400c21308002c07981d240019801c001c80b80700e8002802051314020406c41101007120b41076040c4443c4c1240700340c10912042c50180a140100c031080c101e418040d041c010214001044138074071803000c01c08880055007403411340e0b40041c0c01299045140348140001480146100b520150800d8050000881140c01101030760403200d0903005d807400940007200741511000202e6564031950880ca809000240070b029480f5041400b0301592424 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 85294299 1250 85293049 85293053
    0x80f07050a021f0c02070f0311060309070909060b040615020604060b0409020303070c0317040b03060103050a1b08060909030a0e040203070e0d08030a150503190302010e1e160609061b 80
    0xc043c8412a449100307448280c40014150100080002401d080070a20502403540e01d50803030b02d8101525a5100300380000101d80a100200005000752030302c3c000400c505155480c10720001d124001c400b90042e030404074000b8098040e904001c0345048240c028103883d80e00c696603a0300401030440483d92165480c0030407000350700c0030805409444c0c49817011407410f6065051040792890043d1007403944244c10041031100ba4100c0050300c4e040442030038086110b89034042c1c50000340c0403090024941481090044504507070080c60721b40510001e0b01d003410561251041103480b0f20032080d8503000304982242c08403540c106940250b0b80718245190011303842100e00300003002121010030681d00c007503000c02800340c05206441b5600c501080c0034802920385242802098850a0001091904c00070150024041c18006c4d0403424403c659081982c2c10110040540c1d03106481c2102c1a44442c80340402d0810203007010050032040c2e469548034072820354507103581181e1070342a010020705c41d0154007210b000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 85295549 1250 85294299 85294333
    0xa030e0102011b0504090b0904020105070807030201021c14062710082b090e070309020f09070207060e0d03020a150e03031302130c0e01050d020403080a0c12080f07050a02 75
    0x101c210303480e034602c2c0d501d40c034051b041c40c255034508600d184510b240d04103100060fa000b40894460070741c800441e603181c2806044c10b900a0240c0300f0010705240f91034400c01050241c90307222060f990050f0308095050340b6550180800e074011000f040f200404900c2102040302d440c40c407a180d20440b184040c0c14070039224004a41000c0c8003030580c031a040704c004002c901c481d8110070038064500561820804062910541e45140e80002d401c10003415500c8141d5415511045c000c4040c003200982404030500f08284000d50ba41094030980c0f0000d841043e845001d881c04074142d602454056004081e0100c0d20b45900d0440080b84524030b0f00c240e510318000b41d403210288095846485682482c20b03030000180188503003510402203404c0180d140c6001c0e404039a4024800200c150300c2881c01030344030744499038004000e128030307000500541c13000302c6c000c05001d51020030a5a1a44105000e0b042c041c6942400d440c2e42d10280c0702e4441001c090800929a0352140000d031010f488103104692010840f0840c00c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 85296799 1250 85295549 85295591
    0x110f0a030e07060206060303030403030513020315061905090103030302221e053007030f060b120a08030402100306090504030f021b060d0f140117060708090a030e010201 74
    0x400c0c0c581ca81c1a030100c4050040c4002000d150002d058103141032800280c41c0c0c0b00007000102407694617004900c0d0001d003841c000c00a250b01400325514202c450040880010084501c1841500480307102c1d8a10411400301d242110406000f03030245074207540c0c050307000c0d4008686039007901050f210300d03464109804c10003400900c3c0c80c103541d021495800702c7c144082e00c007a41009006000c4903d01c0503000040031014610030b03c4076414403001196545246042003400d520240c43c0c0615021070300103000b242c0d4400010740104881c08001e0034440f40486445240b800300c050070400f0b05100242c0035040c80340201040e0001c40c80d0010b4840d88504814040714030503542540050543c103880d000481d0104003040d4452102001c00301c08200340c170000350403442411541c074062610352011401000080e084003e840c0c0d040c00030201a5a11202403d000c1d001e40000e01d180e81c0b0559000c524500d0086110b50701036003050000d8250b20045e502c1c1a2560402001ea2a04540d0307070740341114008200344000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 85298049 1250 85296799 85296817
    0x203042607020307090e060a1508010e030903010f0902010906050a0c0c0b0c010b010306050f13200a02070509011809050c030d0e030114010506161e0f140c0a09110f 72
    0x264481c11280145403520342507401c5201d00c03500c2c003503110000d19800604254003074011503022540110240e145074203018035900005a42d820102141b210210100242c000384c80194001c20401261003c294152070000c00f0190205200607018031000c4d101d00300400c0302d20b140c1c0c10b00c40c0c2030704410703a10024031440c9076204505000f008919040c80719400c8c0200104c5420918083c007105040000240603801a24180c900c00d6501101b10343c0d1030344103034101d13810100c440d400c0c828900450701150641540250083c00050145010108030380c44d01000c80d074160762000e039910220980da4824000140841401541c2c20f11846200c0041036504124541e0b000304169101403c00d80c00000745820750340300452400c020503100d001800903440c2c03007041d9100c50490343d00044200e508ad0901540500900c0441c00820521b503c1100501246141d800071091083e000b01a04205401c1174645401a045031903521000000040081036016040315549400c41810070340b400c85900c0e90100964407d580c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 85299299 1250 85298049 85298123
    0x30509030721110a080a0201051021050f0313030c081506040209010c06060602010b012d051c09030801051815130f020409050105030d020d050304060522050a230709020304 75
    0x508206c0c1d82030050642005d161401700c0052800d1071404482e54154030300c40c0c1d001c081846001401e1200400584640040b07203410b681d40d461032520700642000c810b0000380d502170701400d40040d00a030700042418020a11350f2082c0b200c1d4451600300000f80d0f0140100c00d040115800003640840c040d841200000c0200350000140c1151040c0054441991819004050181790303140c0c40c0403101d40b10822451400e24540f2540c0c030146512303904212204e00c80452a40da2600c0340c0c00080681004403141039600499202004c20034160490f801c0545c201e860340c0c090740e03440b90380445a080c02c418400d16602e0660340820701c0c0c1c01500250007260016845a0700080d210310040200b81024059141144030794030103064544000c020240c005d2001410044c80169a54001001d11000c881502c3c1c0c0c0e00c0600c010310070312200900302a50345112003681079074020240c0000c0c0405d808805240d17400c04101c00064442c0511785008031380207405c0280241c5d104901c483c4e030500e14022300c1c030402080a064070a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 85300549 1250 85299299 85299307
    0x90613050a1e03062c010203010801050c04080d0f09080f24060d1106070b01060e0909010501050109090f060b071a0c0304020f04090302120d090201030509030721110a08 74
    0x41186030441544400e00722511403054034000000300280400352038010758003040d80c40744c0176400d48200140820203900e000006100c20007144041d001107040b01d450000078403490300c900d0801e0420344118401c0d09016804030081d008601e0250320880044a014100300d5889a0b80b814494103000d9001440c0484d60081c0c03c100f5020309100070121a8841000404030444c40e10750013040034a10450780103070082c41610f03500280d5554240464909a5010404030031030f594030301c80a041c40c0902510148a0180e031000541a00c40510401d030495005a440391070303162404100100401054022001e1580c440f600841c00c115004c1c000c040d024030400c03858682c4056100748040300c1502610400360401c00300140300140c0d46010411122105c1142d002880b440245001c0c0d1805084014941c40000d000c503002540c0a0303230783d010701c0949000f070324280b01075511040c040d6103d2240c1c0000429050002c2480304c42d880080b49201109061030405849840c01004e4403854a60030080468108100003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 85301799 1250 85300549 85300559
    0xb060909040201082527060f081b0406050301050916050d0207030201180308010e0903040e06120c030714100206010305030f25050604150b010905010f03060b0705060703060501050307080402010c020105090613 91
    0x89000f01881b500c41942502030602c10300411520400c0710500c00c120f1400040f8800c0d190745600c000755121218800ca91f996a074100c05402d541003480b5081c0b199000000240700805040b03031a0411a04903501c0600c0c082e0342c0790b4804000c0d009448194115135843c6018000349841c0304000b00c000f8000d0703d8a00a541c50b00e039a00080d04c03030051035865070750024402004010048544541c11141c201c40e010080130340500340d185400c406d10491a418847c182c000502004060100741c1040000d4440600c0b41c2c4c0c0d0500140d0341c5030420b00c00203007694000c01101c04c3c5072950130003510380382c1c1115261405803400085a0340c171a0f4910502550503420520502c000c1260a812100c415400c0300002e001100c000d80000c2d01314183c03032141030706000e480c0c80810350301d034443d500500c007a000e0398032015100d2185007406d5540d81e50031154100070a14204001c0303082d40c00b500a80e4410b8120b5a40c2c4285680e5903401194040ca0400e403c80c10700405100200c0c0035a01c480207031041c0131103500e250219620b48 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 85303049 1250 85301799 85301837
    0xe0609060102190b1b03071124151801090f050a090206071203020d020c0c0f01020303010e24100302070b071103040b090a0906060504090b0609090402010825 69
    0x203480141590301c1285940300e0084264400c0a8a68206072000c5007651401c02c920520344001c212107650a500108004056400c00800160740c02c82000301d030302004100b00d030100f40d4629a9005c011081c201000120410703a40030700d4141d2180081c0c0b42820039044080d003114180005c0c1c204414280c1c66034540b01c44031045104c1c1e242d2280d0140c0040c00240c00e560007041c114450404068540345011100c903a00c1030298045840851104600f150b40b02015001c0355200c441140d0294802c500004d00e03008598800802da9068654940345c030409070300c94000d8124005440300d810711080c201046000000d82d2101c3c2c0c0094030380000d031405650340080b0306c2e040c2980710000741031009005100c120840340480c00829030707095415100c0340543ea02c0c03100001070302c803400079417105049604040c00411259070141c09001260b200c2c00f41441142004c80c1041054081d04c039510760040c04140028016600c943e1805401c080c039604644502070301c110300c80300c1780310311000810085134010f40101650050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 85304299 1250 85303049 85303051
    0x30c12090309010e01050306010e120a0c1508070c0c030c0b070b0f190b030106030503070c0f0608090a02040c031d0313140a090509160305010c0e03030702030705060a0314010e0609 79
    0xd10025500d04211480040c0500c1d12a507501410400d001c000166146d015903c01a2380f010010030703c0d109202001c2c1d1095840c18040c0342151100c42150740010f0903d16580e1421115440c1d40341c61007955a5000c0403122140706032029a400d1241c0d0030300201040741014440c01070b00c44008510b03034804941c100440e03502c5001c0c2810040c802c0c2107041244c04076180c07100c80c5000314940d00126442e90f0410007e4094011500043c00c40d00001070702504000c044000401140c3ca592480c01f01c0c59a11a81510705080481d40303418039401190074800145000d03403204800c000542400590410312164084a502d4a12503403102a40002180c500c0350a42284d80344c01850341ca0120b203105504078020944828aa204003003e2a84510101340c92810900c8841804040301c04100849940c1c0d041160180c55120903100124484840740c00650074048110703070781150064000c091180c501f40620070240c0c00703407400c5020540d0341e80080c9a42c07240169414020160ba0005001e20304100d800c000003054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 85305549 1250 85304299 85304311
    0x301060306060c050a1106040801020415020c010c0309050103020a03180c03060b061c020705120c0c010306350f0a080904180c03120302070c08060405161d04060908030c12 75
    0x70301e003c000060000240ba06413158040403030103c1502030310100d440c0d4082c3d900b04490035400031a002c90280000c4003429910200396080790302d5054a8401544c4800d111030014000030703100c0c002804254001c0d001049021964507001a400f0055120000c280925074403c03070703d00d040c0303400810a000441c090b90a041c8c1080325007a143c1034410b40c0e041c140c1c5400d903000040c011740103e807100510100307222490300501c504031032035514240050f030076031034030b05140d99540400c0c49c010707020408140c1848010440c103420840b25a00381c3e0300000130348800c0241300360140035101c1c05100549090b402c0c84134103522071090400b44d494069140401c000d841ca00b52103d2402c4110301c0b00400480d2007040310000b202c1c3c00400c401210014802c2c02c9000e4400c8070806050319000324000617840000040440c42103001c1c4098601c195129006458040c42510400041c04000702e030346c41003441040200f5411600c110030000d02c454450344e609510350000c0314103001d9450040303442d80e4007005030070480d40c0c825 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 85306799 1250 85305549 85305557
    0x20d030c0e0114040806011706010b0a0e09150307150e06190f03021e04090b030a0201200c0a03050c100f0801030b1806040c1806050d02060f040b0f030106030606 71
    0x389408008116811207941141001800c4003a0312200300780c2c004440103000c2d04400d035222582c40c0e034050b0001400d03003800c502ca0f602c505800001d04034507540580e4603524481d41c404001c400040f0422242160151014201040c210800f000c42d42c0d0804c121001000c4810000f0518942031002038010701000c44d2140c00381104011003244013540072100f1400001e24241048a1040100110028041c903d0103803140045014442110f10401001c2c00884041480c240303d602c681505154540084000003400300d1103510f80700c2421112401c444000395421011100703040d41860000303510750403a80c426503964100c040c0c0c00783c5a0030600c21a110307504090400d861000d4210700e00502e0104140302c0a0324038044d800c0402e40d42003040700301c2e0120082d0001100c035241050300f040f0008041c2d03407140604401114410048814150251104403180180f0156101005801344805a80302c0c1c0002c41480c4d004104c0481c456075280007a000d81d0780b43c000d55544940c140200a01200c000e900000d040c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 85308049 1250 85306799 85306811
    0xd11010b090c040603020a02150709171f050a0b0d0c030b01050a0303050403150b060c07090c0e060304140f160e01051509010c020a09060b070209060f09040303021602100e01020d03 79
    0x2e89594111421500c16140040e501d000041c030480c1012080c1c040d90880c3e5400c0d8051000305a0b2046900703007511a816422319607280c4080340c065840c1382494100c086811414403103643c10541c0d9014680c4110303520008128811600001101d00e110744900311400c1e1101d40050003408002c540841c090901507079062051415618050b11901a43c0b1000b000681d0b04a2109444a460380003103140c500068001070f19079520010080d00d070600e5000d42441149031031540e84c8950700c120710009003214050645850f40d295500c80c20001c80b1107240c00f01d4a481400c42580180c00f007003200b10401d042c4e1418408002c2c2c1850300607403184106910151190b03403500d5500c040b145d208411140003100909080017004264408602c0954040d8055129649000c01c00101e140c1e0724070090600c2c80c03088401d00c0c159640d901c104607040300750342a0103802010303c90025000900035402855800c001c104c01c0d66100c6800e50024403820751300d40f40307600016581440703103070072b075804021150044c0c4075420103100e8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 85309299 1250 85308049 85308061
    0x80d0302070f080306030a0206030406090510060515030c0f0309031804090803070c02010e03060109020c060115020606060d02070209070e180402010f0e010c0606240903151d0d11010b09 81
    0x2c00b60505000e4a16200000450700d960303070402507044c030310781d0180119841c1d01d01800c04e42c0c002c0040303d109444a0003444040350018a030380c8075100584030700809070612000440c3e03011481d030304000c01c42040c0c4c0004002100c4846280c1380074520070b8546070000d40c0d5a482600d05d03910070000758922680250300b016075060000e403e07038043d6a0300240301d2404400f0300d42c0d00e000480d06600010020798042c001d02002095022082d00200000c0d0001802c650260b60f9551141075115030110300300006070000300c00704d01c0d545812401003802e003159072009800c14402e6000120398000c141d403d540442c5510890800b103041ca1118400c50610441c40c0085a1401e80c0010382000303c8400c1c19810000c5101d044841d5038014410582100d80011b01013000f1612500034a8000c0108440410040c0d4800c801c3d900d568442e286101c05d499224013401e0001a08002110150441040c7da10718000c050140c104074100400050b41e00d0340d07043e505d8920200000358154210341d400116540140e00260400c00303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 85310549 1250 85309299 85309313
    0x1060e01090618020f0d0203070e0d0c0602010b09100b0c030d110301060311031603021c0504050604050c030d090e04030e0d03020d09050d020d08030402031c0806040c030e1b19090501080d030207 85
    0x195020380c0d040036923203030740d00d07001100c0d0b400c2e28074541540306195032540c10a00900e080c00c0c0055820a030000c2020381340080400c82d10801c211149109541200020700a0003502806055411221400c803410031400c201140180d90320f0703801e440701081001c0010002540d041c0280e9a081401850b22855070405007840c030240c6600321000780905800003001041c03030450031070f006079004505108102d50b0406141c80c5440d000300340d90582d110710401c00c80b9891880c012420030120070081d100c4c00d448500c0c1c085800101e04004006809100c18a1001c0000352031f034092041000384654050301900e40d2500c2c0c080e00d100190703000a409010000300340001a260980907001664000032010344aa41d41d2000074034180720340704240c4915a8a0b050480f0b0580c10014107401050102c0e400d102106c1c143d08210109e0b82c000c1c5081c407441e170002074254540780d00200007c420000160003100f0340d00f4020345904040001c0d038405519283d507000100407440b003d110f013100b007082074a4254a485c00395180e400c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 85311799 1250 85310549 85310557
    0x20301120b04020604050d060b030d020c0a1502100204080c0405150d060f060f120b06031605100c0b0c0403050106080c01020d14040306050c03160c080a0f0201060e01090618020f 78
    0x5003264000700110301590f0301c40c001c1e1401480020800315040c001403819801805144116a001e4422402c5c601340c6940042503c10925501820079004646401140014030071600403a0301940039411690071203000e140010400346c402c0400030300301110b41d0414801103803401030040750800c1e14030203150910354400c1d84018041c0d4012002048040800014000410050340720321a000c00c0b42c480060a500c24903a42200c5600581855202d590340c2424983c03907856200808a009411000c24000340c80c11800541c491252480c1c44c60701c482c0d60317580301c805105c41a0f5801f401c1c1c0c04007140820030130400340a0301000d41f5915000d02001e00840e00040d40e82d00703030380d1000024040d025055441440b44002660003e64001c00140181c2c103140b03100c0b52180e03100b03849820780560a0070313804481d0fa000f520726205030741e4000441e91030007106d440102d9100740003000002c115501c4610004001035a0f00c03420f8003130f01102800160701868003420b03003080240401c03507150f010b00610500341080144000d403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 85313049 1250 85311799 85311803
    0x100617151501120903020607080f010f17031b062205030a08070c1b031a1005040507030e0111041e06080a0902060d050403081006030204050d23100504051002030112 72
    0x207050014901c00042c2c4a07071080348802c03910b203841d000b916000c0c15030000e074081c000d40c00c0740c5402c41c0d140c45003240c0d086070741d0302402121600e00040d002000b6072880c8408100d00e200791081928103110f101c0c8442030340c5c003000244051141d031090043c03208100b203941c00404c02003031250040034031a450791b84298580c06149400d2060010300c500080f2101c1c0203d2b2074864090740440114042d062206007000301c1344050000382c600c0c24003942c0c9071240c200c2d5150500d0003a0125011821501e244c4401c110181c00020001c03c10503803030b0640d01d54407090902501213883d200110a0361200e0406800d180e0400000c01c0c25070f20203403429010408036410000c101e0b00408100008a851040d5001086062151070980000c1c01e02d40010403080c5075101ca2100d00881a040e520403400d56508001c9007030303020b2802803070383c0b01c610244644002113400668a8404a20100081e584a20110b080b42000c04000c80034103641c2d00d4100700401c20100380500040c3e0401008210700319410020180686041c946c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 85314299 1250 85313049 85313071
    0x6010504050c0c030a03020a080709060c0f020f10210c1d010201110d0c030c0f09060c05070f0303020a0b010503060f060603280b1302040501140a05070510061715 71
    0x2140b40c800c01c1000301c40780100100101d81c2e039242c1c0324000400035403025214a00146891011640d1684222918011100700d030341c824944040703680340ea00300c1c04940503049a00100b8140c0844050303c900d01c4076000003505440e0650040c0301c02c019281445481d2040741d8600b17141c500d520300d081e50403258000c9001892021800b2640c01600143c0c0108030054203182c4658012420312820b11b491b4100f07100d001d180ea6014014441c4480d000c0c1d07184046015200040f0764020400d01807580305140c80b00d029070040f000c232079080d55a114200512007041c0c1040c1c00580101c002c140502c035280034401d0050100350300802c0c01d440e00c41c90380340464074007801140c0318010020100784464420180e4110146400f01da9032191510543c2c40001000b06010035070140c00c030300083d0707811540f4500c04d840c102e644c180c40d10100c000c10540802c400341d00480c064130510805020301c2c00461010001003485480265000170700b20700301060f200226075129100b08855014030804203c1405207600e0540103229048 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 85315549 1250 85314299 85314301
    0x60f0305030a08090123160207032105190503011d0603120a0e100503010501020724031112010b030f180a03111f060905070f0c120504051906030c020309030601050405 73
    0x1688602410312000d101446c0000d1b481041441c401d80404a80070b50003030303000364a407010b444e20181c1e241c0030030384009003190011450582c001120700421034841095854082e01c1d00c000f9406403030981d055080c00f0400140003000500c80004403080e400b54403400e40c1d00320009440c140780080d994042156100205440c003144c4600b2043c00b40007107030b81c8060002e100444034508101c0c000c0031034200344a5540180b0607500006070450100149030190303000c0040c00182c075200e0503820f80103801040112003645004004e0350036250b403d03032682c0740641130550415540e82000c116000c18014050807200d18080400400041601c0c0010080019949410034042c1c400d92402003909000f0480601055008541000300076105e8a83c060790545240d07c600f041030340c4801030103c6280c409030740494041110000c1c2d10001c00d0b004000044c8080003460b00c24640354883c80421110000c01d40c0c0801c04070003d09c803d000090709806091842e00707281c8001d40c200f5002c000040d6884070b042c81114061a81d8034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 85316799 1250 85315549 85315561
    0x4020607061112040203011121070512090a0210141209010f0e0102070c0f06300e010902030f0c150c0111030c120708040305040b0c0703060f0e01060f0305030a08 71
    0xe040001c40d10010012551500310f4019458400d28080320103c0c440d500e445960521250903105840700780403031500e070380100034110040102d40a8040d01c1c0201313100041c0080340315000c04021140c4611032803c0503100080c1c451060185905015141006102c817041c21220070108000c10b036106480040c01d1100c16403680c20181e4014058005902d040703d083c00300944980d44150020025a4403410252800c10b96501d0301000c221901d0140314001500c4071b112004415450b45440720545500e6a60304c3d40f00f082c44003100494000285414499444002c60010343c034041c001d8004010400c000b40000000040020701030080c004c500403190140407406107140c05095201d4425a0185d00740c440c0c2d2810704d0101c209444e003105440008042d903210000d9106c038407400e203203801940d15071038403130400707040122007550368001701d0920030540b04003140000800c40900608840c0e114007900060b44488400446003920001d420080b0761030040c18003000060800400c5542040041c80d00c02c015817108 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 85318049 1250 85316799 85316801
    0x50709091109150405090f07030b041a031507080106050d0e0a0c0503060109020a1707110a14010605030106080a03050304020a0e010b030105010905120d030c020f03040b1803150402060706 82
    0x103a00000a9246403090740700510564000a2030040c0048403030404800c0282d0076000700303200394001c1941100c0d0243c04030b0140c426204a55810441a080c0070414140402c0030801700d1300511310740c9120407125405228581003d221200b5071442180004411b4a08043c0184c0854811b101340070400400080326030320889103034402205010340e001519032294a500f000014100c10b80a01882401244000244178801e4801c0b54000400e0303443e500305558001600c0c030104500209101c062000031146480c440700c2c10311030031101034850840c8194095402140c03908440c481d4124a000740c6c500601404501d40c000b400000150340740c03601aa072a0b840d80b01080751600c40f81d0021030610b21850011030350b4903420014506a400030707a640319034a5681c800300524442030701e8078140c83d40c1041c1e81c0622050311036080000300100e1401101c850108480e0070b107281d54042d42c04600c01082c041600100189500603c0a411004500928005d02120450000210040c100074407400700001e01200300942c2e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 85319299 1250 85318049 85318067
    0x906120703050304080304050307080303040c140409060c0314070207060c0b07090b031005030d0c032106050d0308010f080307030f0302030a0609020c010f0b010305010b070f06020d0e0d0f0507150507 87
    0x4050107407902d566503841070507541c7d000f40c02600c0c80f90141c2c0c9808107201e000003017501d1196030410884043c3d107151240c101800400a6801500903403a00b4904012420758040c00558060030b0b41c0000301d007074040c829130300d02c0c0401074005811500500c00412809510490190500b50002c1a01045491700c5000796049034485d4400714580c2008001c000208011040c0700c011244143c081d103603000d420300c7c800c03a002a41000000c0105452101c04560380c95541c1d462142c02100b070300000350854035000011081c0d682c000d0100c0010321000c0040c4240a0344038013141c020880c3d04019420088241e50241009844452800030580c0c00320000b08900201c0c0c004600600032403204554a852000989010f0700072001e4044240b0300300900d92803d035229108550485402c402d00070708001165a03489014000c0d00303420358846400344418115071015110343d000b22109a4000e2080706541240941102c21094504d000c1c414207100c10300c041078210240f0000c081403100001500d80d6040301c2500d030500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 85320549 1250 85319299 85319303
    0x6060909010e010806160801150c0501020f07110307060203030711150112050f0c0109050607050c09010b0301031202010c02030301051519021605030a0f170705030a1205070e0906120703 81
    0x401200020b6030302440380d0198103949030542076501030340d00d00040b101c83c042a0f00d403c07800181c4090042002103009201d200904115182206004101e520784a0aa0308016815001a0340c0025070b03c0421084843d800e912050580241031120709e00103000e522404018401e2042c0890140c40581c0700c9024460307451034003103160f0340721030a503191804541098500e24080301d85100d04c80c00d00c1d0f1480740000d0034840b2203070140e513144406806c19041c03005d00e80002c407080343c00d445560100c080c103680300321089000e002e6490300c1503101e40c035504003040c4121314811550b056924003242d01c040c2d641d010080b03a055590544215644240d041e1139a05540b007140d00d0006030802000110007445d6010034070030450061007034600c1d015915801010788854543c1401800e03500c000c80c0304400035203030380300100401101c01e000900f441c0c41505d826084d13a02504000000440b111010560726150740301d1a0380184151421001004151010440303a080103811144144102c0b52070310042c0c0000c0210f140519 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 85321799 1250 85320549 85320559
    0x3070305010c02010213060e090406112502010206010f12020f0f0415080610050a03140106030f03080609070329030c04090b041e031407030201020f0c030d05010509070f0503060609 79
    0x10b030440300002c0c004e4100d8068400c42e243c00302c8000440c0380c403d240c4011895402008c81e001602c0d01d5071900000c1030644200c0c0c0c1001f01c18409002d404000540600072040140f140d0151a0344510009003003450581000c0200a9199401c1c07041c0d080d4000d4148070242d051b204141904110000115003200b422000c45e03101e428691450b2402044800000031126044200d44c0c0d15101c200d00003101304ad41e8041c0c0c9030071803a8010100049402d0a203d1a1303280c0e02e03e00000b03072294580c0c0300e00301d180030100420f90100d2141024000307181000102c0e00d41c080d050345020400c0300244207603030b405610031000110341d800620304d504465580c18484181058001002000140c0d02d03403030f1550701100110b40a84102140700111038910907200180e081741c552507a10100140425011710056030880c0c0e0703044d8115036080c410104164000002000172440ca031000b5520390003c6994001561416041980900c03a24010f02c01c016400c80180d82000d50a4204035031a40d890b030340840c4141c046d28460503481 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 85323049 1250 85321799 85321811
    0x301120309090501060e030c040e0a020d060912051b0109081801020c040204080a050708060915100801060905090c040b09010b0711030717060f0108060f070507050601080102090a0501030501050d08090307030501 92
    0x1030300300d000650a85815015200e81da07503003000300309c212000714440303480c1a0440885400180342c00d0340003000040c41080e00248059103903c88181410142d070062011540001d00100c01e2040e0076907400c2c07004480c2000b480444c2e201da894010f240541400d0702d4141040f600c80d0034540e8024404a0116400508210b40f190f80e6801c0240d40e462a040065030365020300c100100c0c0c44440425024802c0d8614001080402c011421802703004000034007002c0d0080000402090100d802e01600000b40500140485c0c80d003041c100050a04c450315546602c030ba803406610180a40390740206904403040c1511050b211a03907800c045010040c1540c202d0303414003410901003141c1c459403500036030590a0204807402d035990890254840c490a008100e580c1d408500001c1d0b00c0104460020760021580c508241042e1640e0360321840d040c0c00381c000c0c6010f40d401044821721410800801401040246014403071949458045940c4455492000c3e00c00c1d40001b52003161610108040402950310a00801c04 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 85324299 1250 85323049 85323059
    0x6011401051b12040603060602070f050d02060712030902090c0901080c1303050a050d0f09030510020f0c1c020610030b0105040902030a120305070e0409080d052a03041202070b0301120309090501 85
    0x544e600600a80c1c01080c0307041c5d00410081d20008030320041c0e808800c6480b42c031b203040c0b000b004400c0724940812030384500200848030000703000328a001c02004160b100801d1505507803042148605000b00424400002402024001da0b840303003100e5004000ca40d075240d130320500c419803015403400f00c0d000a0414400e04560400700880000c0e128010440c81c2e80c1c0a10b841282c1038101c840f549140700240035640008148841e000d01a0b00400e5003140480000d850201c1642d00641019100d0008090030b80c501903001010f80d03010f0000300d42c00003408403180703070300d40c03c50b50745200b1080d06000d03803401942d885c010042151803c01c000d11042e50004c811894444603040c004000c2e0400319400303c00684444240000e0741028081c00b602c8a03841146242068644511080101401020b22010031298900c0030b41640842c8014071240c0c2c021404240d17039140a0412102603402c142d0742c042158002c10701004031079600d4055070305484803a956401031300c42c2c600f8100d91448a6070440d404843c504000028 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 85325549 1250 85324299 85324333
    0x9240715050c0c1c022e050a050702190203071a0301090b0301090c09090c0902030709060e060310120804150903031b0309050427060506090906011401051b 68
    0x34288030540030900480e82c9805805455010300c1c40450030304c0d80100324103004080003000c0c0e900c0d11281c610440302d0a010502440185804070782c203802481c0d00d4040298480c88840c010550b100d0303c0050244a0f506089400135620100e030140c0300303180120f40303e000d001c558083c0b02c3c5100500c0c1c8111303002907903400d80482c04c5035544203205a20000d8030b02182210780381410b0081c69445600490183c09039890090140e010f011040300494240480d880c0128090b046480554043c204d690b4801403034505048000d08100900b0038618441c940503c10481242103581c5030800b6244002640902c007400b9140c4800d83d03000e03a030440d0030004203100a1141095000c07003084100c2e4026511603030f812400c0201d80e088245c0342ea20240004d400b9400901c080d0500c0c1c0c001d5415400c144c038140303003c802082034500c200701c5640070441d461511070b024800030345440b0080542140e211800f40200d545414081481107041c1c090740c5040c8140410403285c0340405108070b001046003081555641400008454 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 85326799 1250 85325549 85325573
    0x2030105010207081212130203070906050307050d050703020609010212041427010b0c0f01020c10050603070b04120201170f0106030e0d0e0409051c08060a05040b0105092407 76
    0x180c014810200005444580000d45c0c0134504e0680701c074989842c0c40300400c8411110014044001c0004c16001e0720f006032010481c00d0300400402d070740000c20500340304c20035050040c10340c02207200f24103030100c42010540c04100b40d400c9036411920195a8040340005030f0074603811581070707135802c1c001203000520a290303281c040f60703040b104a8546080710140d00802941112004040c1c072603005440050000c560004000c2240c88020812250882a282d409034207aa1003013100e21425040325020b1030302200140642c54102c10210068a04c03207082a6600d07109009520502d00c0c0e50030098151015640035061184640c1c14108450b90680b8158400e48444042031048400091820301210790a04012809014802c1241d0f02d914030030740e03907a00b000013030100080c041d03950380a54800c1c0c001120300a51084c2c80e60001c1d4071145040e14007241082052034659100314040c07400c0614016040e0707804401c9400307002c41200c1d400b22803145009009202585e070550f80f062400002401e00034041104094 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 85328049 1250 85326799 85326809
    0x117040f020a0e06030624010309030527030f0304050112180807030e0102060c0301120314310603090f0209040c0e01090b03010e010e0c0904082502091605090f0310050901020301 78
    0x1141e107907c46c46c000c0390041100d9590300ca288084990342146540c40b0382c001d40c3d20a0301030b25059082000e0031510048012958060f0072803c3e80c0c00000039003a040504ca0703002e0750f800c07140c051804d1519140000e00038014252650304055940c100b19401040030b0510302503040d4115000300e4076504146006000540ca81c1c0065000d4860f900024008440040c2248d040e01d103811250341d40301070b55650035130390045208440000034000b44034822803110045091070741004502603280d00440c0c401200e990000f002d802c13040405080c600c103800400c0070080b0240c078480c0e050308c101d0a5079489080c080003800d5190090b16041039201d00004100140c2d80085124100840003005165640c0660f142200e803200c000c8803690700412300401440c6002c108243c8c1c032600950045142c40381c8044503050340101e0f441c22030101d4414200b80015030a019a0302e40d8488a004240c005010000c000500240201c64906201c0d2000c000c1c0c01e003050302d0034440040040c0d442e002c140101c1c100740c190305003c1d4000740a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 85329299 1250 85328049 85328053
    0x30714180117091902030322030b010e27030d0f02030a11030118090203030c0f0a06050a15030611090a0f050301201204060b0d050d020c06090117040f020a0e0603 71
    0x580019807404420320783c0581c04400081800304034003603a0620001c84094142d07450701040c041c0d414107507103030f07003001e68030b044604260104207040d840c06244004c0c040c0c100340380e042c201c082040315030b45030006150010304046028806031202074140c82d14502c182d000e0011610b080c01c01c0c42102d00c0003500558000c040703424040c008500c8885c80115140400d20400d10492201c030710700c518145036a0300043d0f41e64000f8054903d80329070204120b240944580b0303484420741c8240101c9040c4519440380c103401000300e1200f40701c1034841c4401c0761094003d80c0070240803540d44840300e20308c002c0700b001140e20200e0040d0002c181e0796550064403100d80e0991086900a5003060a4001c2c081003840b079002503a091030900346d0900d03c541b049528100c400900440314590764200c050010307900c540e90351694074458002000e1203485610700904101c001c40c03c0500805007440040d03900d80e00b0440090101d11460b1010501d075a41e81800c41c80c090070681c006c1d4004408400226a12000151841c801c03201901 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 85330549 1250 85329299 85329317
    0x20062115030307030c0219030f05060105010e18060906030102041701090c050f15070f02060309030309010c020c10050d060905190c080402090c07030c120c020406120305040b0307141801 81
    0x3407548074030661074020000360000603000018a40003104110340b200d0060060200ca840c1d40e1028650700d030a4800340c030140d020800420940d03030b1101e0560a8480301341c1c2d400c200308400c103042144611006e000f45200341c03a1840051001e8074250f054500520340030301c01542095002100c80d000f0200a03d099644c0402600c011560f070400101001c041d03c8050060380500410440d03a91040d041403104542101c00c040700b200c0541d8580003d140903940c540e0185a4030304044243d10300b105d2150b03101209541220034070499654840c0442d07000b0800d80d0400d40e0380c4500400d01200280710703640020a00d2460401405841c4400f43e008204408010790200105000c40d2800d560350042210001d40c4451a84001080800c8000c080c1040a01c00c1c01c2665021415a48640e40d000e485c40d200e00c00194154004429031030079015201c0142403562028802d0035264500806c184510301030422040340010204460600c100c95403014131643d4040d0b030f500c2d0004910113480d84140d2070303034507400140071034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 85331799 1250 85330549 85330591
    0x50607030b090a0c200a080f09040b09060a090f0e0d020a0201110303060904030c050f0706030f0f0203060f06030402030f250608070e1504090608060f07020604200621 73
    0xf116402c03020f0081e85548503030980320b50a000c94100c17604110000c40c010b0380c0c01c1100082c011400382c40a910340481c40b0b41c0380c042d10000e0004071a230140c1d03a0351290075034400f40152501c907200c20f181503c03404040850840744103904c800182c2282c00804525100e602040740f101c5130302040e202d8120303100340d82d0031088109a14500303603240015114a644031f04c80307401081c0002d0040440a180a205900740c03807074500394060340c9040c07a600b80c1c002400300740c44690403201d41c11188510a880f041040003103045043c201c020442c950a00c0b02c00501510f00003000c50150b5504121390613100a02004540454829202c60120100c00100017180981000c0f800305000b40260500d03131050f15280e13a42010919090104501e9002c40e016044010400300300c0807070401000d0141002820002c40140300605056401060300d0307000900d032404642011007844009400740c20400c48405a009001c207021201c000007500a1140b9a02c00b58103410468140c2b0350164a614894403c0d2049407049c81001d03001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 85333049 1250 85331799 85331801
    0xf0201021905073b0402010e040908030406110408030711040b04090302060a0f2004080d03020301211505130210020c061b030c0703050a110a0b04150309050607030b090a 74
    0x1d460081c05a00034010a10440d20391100014410303070348900e83c110000c100001e00ca00c00380c042e203503070b0181030109041006550304114282802030301a28101320180c01034690302128007010708020003168840700401c005815510503500944441070582303648a010b4944211550052850540111300744544030030a071405128085000360140c0252406507034415004008000d180414900c55607952807001401280644003a0300444814043d41d0301c45c2020002490702c0748080c61101003600400042c004041d800e0500d03217a406149050040d0170300540790002400c1143c0d241d07075201070b20304000c00c2181c1c1c0350301c03a100c80304a0080d100c4510389a00240c0407a111421b40b0b45464001204222440380b1228000e03224038101100302c20f580c00d1600d0746000900742042603200303590719802811042c0c00d00c450803260301c219071000c0b5144005213282030541c0303040303000328410400b044400a582030366aa019801100c00564014241d8246240c025000b03001461214046401801c404001403080300c11 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 85334299 1250 85333049 85333093
    0x9031a070c030503100306050c12090c01050a050f040b0d091103010605100f110303070804050709051005010503060d170a020d030509060610020a0501020d05060405061801140109030c030f020102 85
    0x640d40c1c5030341c00e00925031800e03106540050400003150301480c20010211780e95116403805070030411691503450b0790071009080c1c5060081e02900075074000d9009075280d680c011007104c02c00e030312608003a030b12100424102c00050256a008819440c4000703a16041080d1aa009041c0c4921400c040c0c0d016503410424582240d03501c0c00380c103400a9030700000340d40d00c60080c400003036480f020340b03004110301002405aa007181c0096600d4000700e800f040610003040014032100001d040a01030400c0b1a00d0f02040080208149208441c140000000030071201d4403a0300100f5041c1d0381110355080b40040e044050803403540f01c020f0100041c094500f22101851080c0140d5002d81030072401803d42d900c0d04020005a1050f807041e81007548035079480c1c0400180280007030007003040009000a082d107400d43c00d100c1a0b850040025110b611103103400c0d504034000e24032035810b44100d1080c038904030003a42d0068500c0701c0d803900090400052500b00000700280003840f00c401d58400e030f098a0f400d089d840c0604001c00c0f0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 85335549 1250 85334299 85334311
    0xf020306090f15030a0f0311060f01030305030408090306150307061d0f010207080609010603020f0d030c030807020102130306090c1d0112060906060305060f06060a050a03020306060405040c09031a 86
    0x70480c4042840042c0c202000380e0001c0c08460b460319910440c80000385003113407001d001c07038803000d03220310102c240f41d00410000000c1c43d146001e0300c0f2a1401007202d0228140500004043c01004004282409100300550320300040107011912203040c61080b0701910840012218441d200300000400c04074882c01e40041c08500010b20140a847d601c01009135145601410f80e045108a0400149500c0100629400745944500005609003140107010b20b42100005203401102e0b02c00807107000a40c46426220344640500d002503a40d141c514049001e446000c048900d00440710ba004400e0041990207184843d108440c20380000799100c007554280d000c07030840180d000b0f500000401c500144000d000301d810348035040004d00d2100d00c1c1c0d100c0d021202590000d40301ca5000b4802c01103001500c42401d500040211000d40c02d1220f40c2100800b00d110380c22601e010190080041030582d25101e041d5805480d006000740300c044003541c402041d0002c136100c00e540c0b0840e94621081b81303a1904607014001d00c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 85336799 1250 85335549 85335559
    0x6040506010801060b0720040501061206060f0e060307090806070504090e01050c070209090109080403060501060806010c020a1505040503060c1213020108070e1c0303051902130302010c08070c0801060501030f020306 94
    0x340300f5100c00c0307140240b120b0321068014103000a004d47d5a03c501c5500d010b401c1640300d40b8100c0d010909908115040b9070403800c14031043c406c2480304550019440c200306403003140e20760340c0c0f0303910441c04440064441c1d10480755441040203101a254015020f8400d8650b920b1080160800d041111400da6a040d0780c4003050707220421401000d41401902294824101d00020401006541c0c40183c164401d51050b2403060742e0318014811981d11a8019070404e000b481c3c00100031000c2c3d00003030007980307452255a400354812640112032502460a079002031400030f041e02d0305450702100006043d4002e030001d0310a50130800008941c2c4040c3c2d04042c48070354044c0d4a1122650b80c40606480209540000c0366010480d410b450081044100c9011100b500c2507a01042034108800c1181e00d0314003583c0b10860603401801000002d004000d80700003103035024a88903c01003e5810300680038407451501402c1030403250408a00c1e2001500410100c603000c1e80c2c2000045c4402d00800124001035840c19404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 85338049 1250 85336799 85336807
    0x1503070f1b020d1b150e040c12021303061104060806060f1804020708070c140d11040207061104030501060816060206060909070510091d040c120302100c0206040506010801060b 77
    0x150400c0314010481c1e034070582e41c49000c101101c009000a401c90303449641c145248601c003860b170340c0e8060b03100c002c2004280d40900148001d0304001e00f902e040c84560b268071640c0030840380c080290502075072001b1508143c0411400030005020a02e69120f80941320204169030045080c3e03050400c11a00c680203400341d03990a0417020f80000310355580400240343d0007902445140007041e11031008000d0b040c41120698101860220700c4117075800c104a850344075112000b03441c00070500421902c41c3c41e05040310f00503513403403c07442c2040040011310f80c1c14a20002c00315000c4200f000c15170011007903400000c1150b50301465540300d980b60510502030303400140c024201140b05406c2900703486e07401c252a54140c5444a4036140410301c10484001c40c0030010750001c504005003092840c40b15100030200d482e01d030485c5010b844100e8002e0482c07082001240a0042c9039007803510a00481c402001104000d00030a45010f800035034814095400760b405010f007900008525205129401c12105c0d00d0aa150074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 85339299 1250 85338049 85338053
    0x2060f0f0702011b030218030c0d0602220f170a0206120402031015050a0f0b0708030a14070503010806060f01090506090d0501020a020604140102090d060f09021503070f1b 75
    0x300440181c022030656480c2c510251609000440e9940320030342135540143c5484001d007030700901800c91311480d8003075000058801116240c0c410340c141e03040d0700b00d000036035100503080500c00309151800d043c0c0060440700b000440c80c5041c0300403020031913016029004a00400c000c15030742310007030050300940c040410800b41140e0281c100d08641e000d400201510882035584202c001900c124030000b8406040d01c22061005140124588014144403001805072a04150200c2003a204180b0051302400002c00000c6003050541c1042800003d8801044124103140c0d101812941080c020903140307009440004181d8100190b160410b008141d41c0c9540c5d00703242c074060000c543d1060703a4181d080125400d4403c08502c00340002c0c00c10308001d03030040010745014100400246180705080310280d004009019046e51000c0c00da201090b0016400946010140d4804d402822260402900301c0c409081208282c5500f0003c2c1d4440c8901d9121600281303415101200d1600c00c607445100d15130f85484520700 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 85340549 1250 85339299 85339321
    0x1030317070e09360c0a08060903030411120f01020910031e050c090913020109050a1406090a0503150403120b09011205150907060909050906040620070803060a0602060f 74
    0x540d01d206682d4401024084c0304e4200c441c8441900140395800041004810b051072081c0d031000740f142c00d029000034102441c0e4075031a4440a04064500e07282c0101c00f0030725643e440e84404200d60303071038212140c1d03001c05612035010750800d0040c41d220740c24441c4007103c450700034081c1d10358880314000c0d03160502401d60307200c200402001d041d03410045014040c0d02d000781c1f9070b030305130b0b41c081c01c21500c02c46a8460588001041200c594100303500800d44150200701a807003203018544140c3d82121050345800e014000321350440c015a0040e681442450503110008241e045501c0c0228000d0703613541d2111001c0c81c0300b00c05071990b007030507540c00a5807800100900000000705030603280c0720f0019282103c102e84010340080e40d080d01c40302420381100104121164224095500801c200b0505105610340342002ca5110309000f04090510703501e4800700840991821340282140c052003118030b85907182c600f0445070a40045415902518469101140060000610340d00c20140007130010741d240e4078030862807 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 85341799 1250 85340549 85340581
    0x9070509090919060b040c14030106110a240b0f01050d0908070602070b1f06080c09031f1508010612031d04060b07110a03020a05040c09090501030317070e09 69
    0x20280340584064508245020007985460500901010170700300c42100c108011100040700704c9003840038105401103140a0341054a0441e0070134101402c002c402242014102825640001d00c0010b80903ca01c403075000d1803015034041180c1101c20403050f4000001e0190a0040c4c48905010950a100d00c007003e1007150400001148600d000d07a00300240b03551048240d8020312000c842000c040405c22030702c94802c0c050204001414200c5000030781c90580c015002400241440c40c11180004907a50251400c20a030304031f040031840c0c40340c040007000b18414000c044003c5001001c455a034400a9041c40500403081619407070100d0f05452099642c007552034074080085008541c0380d0001880701503590307206060003400000a03071a5a2026880d00e00b40300d4220a8001d4491404880140f0250b200d002031082942d070141c40008011004c8103080c0d0300201140d001460403402c140c000700825510220002182035890103481268507490810764800800c407000d560080511030004825507440c14020b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 85343049 1250 85341799 85341811
    0x2003031e09040c0201050412030b0d030503071701030311070501090b030f1f03030306050f030a0f0b071209120f0801061b080d050f01080706020309010206180f060103060f0b0907050909 81
    0x199107004032240110302615003694200000d45d64910801040c029001c0264203d001e01e494200030303020040300002e603140700e06807014080100110024504600039140358103412803071454a4407035a900d2a0007030960003039010000f29030281584c0010309500520f00f03241504e04150046080d0b694a8906541e030391002015400664042124400103055510902000c0c41c025603002c01d00500705402d102103a8110980307240660304c20107046000c925400d00c1644683d51211030121252141e0000316107000c580b80a04003403c0c5010086004c002000b500c00410303070f640d03460b0380b200c06030b0080054420080134400ea50116074045000010b01007100b00b492500c0f84a2404103003040e450000b66401c45900301d07030034640040c800005000ba26000c101072801080700344020751502114400007034883d1009442d080000e10480000300320713a641884000c00811103003040740d420750f84d81d040460280ca69400c440700f9031072800001c0709190400d01c0c0f100780306041c03a8680a00c0c01c25a5000d110703001c0e034004d0032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 85344299 1250 85343049 85343107
    0x504112502012105060415032f121b03010b0d0b04080409060e040201140301080d0302031b0c030a080106020109032c03030d09020a120b060607030c020303031003200303 74
    0x40c100d5480e20042c4409882201c0e0300700040700e03c2c0c10014401110707048030214002100c401c500b000011041e40079040c02003590500c3d00c80807200740d01c5507922060302c0032152b6404400c4010010b6180070020306c0035540c01410400c070704a00303085001c1c1422241c030a103045410504803031036240460103d585a940040c824a507262629590f45000303000c407000ea1b0004034801042c04e0600c010b41da84103014032207401c0200b02003841d6500d80780c6c04540da5111280340c041032640200011703544d80682c0301894084a98480041e03071360905c4017191034030b9510240d0105d0205960000100e0094414840d804896130b01d52039048101c0902440e404046d02540200544907017803001580c11510144003030000492009404a40c00280740b040040b100d01d0b070781060900240d8038a140011a010284e0030760004004c1e01d115a079403040d800c007103400c5108130720060740520001040c03041150505c40300500322800f5508003e80e4603200d800344500c03c10170011440d8554803d009840e808003064852021000f102c41d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 85345549 1250 85344299 85344317
    0xb0d1401170c010f05160b0402010e03010525020c0a061709010204120816060c050c010e010506030a06020c0a08030705040306051e0c0a030e070905150108090a0305030a0f0504050601050411250201 86
    0xc945034210710403d0121220a1f0702010700046503081900e01e003020030101d00a000924040d0142c0100f45414401000075900a903140c14155000384200b014600b03010b025000303550380342c84000d0b101e1180e031040319a2581c184000201c0741c400c18070980c0d0558440070034603072510420751601c1c5165002000d0601c000081d4005210003d0b42c54455442c1c044041d880c1d00f5255185400002d00310b40d0b02c0da0301d205079039040030100034641e035011803101480c035030190005840b41486c111052038140f0304070004003400c10020a20203415000f1000d00200e82c8103030800e0260fa07640d44034140000d030185220f000c00c00c0c03510011580e1081a0310150191007900e2400043c00b101c244907192074441a07a100d4904940d4032000e2003249102d29880d507580603000c3c03c040ca03250a150350f01981d03a0750186806001c00ca07012004c03d00c007241c6900141450400100140301c00d04160a0540d200c1c00280f00d9644220300e810380050078000103109450b98500c80c0e10641030f046a403102004440c900c40c2d00105c0c10011001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 85346799 1250 85345549 85345567
    0x30718050909060a0e07030b010e0406020705030307050301050312040b180f0d1104140106080406050901020f07050d1106070905090402060c0102070b070e1f050a02070b0d1401170c010f05 82
    0x303040a01c42c1e80c42c900100f145040494400d02240c0d940301100c1c441d5049402c00740b000ca65a84081703811920312045440950360796080c0070000b4090394000030043e003c00002e00c80c1c0c0320303031010203035068400071000d480d500c00c0e800740030301000c1c407962064120014040c444000528040d015100c642c2e00d0140007040500000000074074a0b800224084803848503842403003015060501ca4080c1c91034130304142d480d1950400401501e0000b000704018541a2614001814001d0a406a1b031481450a204903160001464200d0301d460100c01c01800040e82c0100444003420b0000e4814015481034544000c610304150a01c241d40d41c00600c00e9820020401407400e1011091000f8400700e400740c800c407251800c080034002c00c0402c801c0e504034451080c480d0300034201042200350b10700541d45820407903980e043d90071040e41066929401411154400300d400f510b01000380e005484008040d04030303044140e0b21074003031007820f403403c1c1c070341c0f1100b680451440403455004560303000580f5810304019041460030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 85348049 1250 85346799 85346809
    0x1b050a021006080a06180308040818030a03080106120b0901170f060c1b030c03030a0b041b02011d0708070b22140a0602030c1c0507080c0304060806031203071805 71
    0x640c4088803070380c09400c4070805c1c88507503c10950140c40c00724282c03c1004042d01c0040c4124400303270024141a0001a04111411058001c0407150130094195090301ca01414050b003509404d10075400460032804d2032500a034410702c00c040303840c13000510503003460b401d0080044e11010501141540e80c8103038203080d800290104503044c8181855809155910034050043c450b0380c00032516210254000d200c04144004007005407503011201120010750304041d400003a002c0d00d4074810b800c01490100c0451031515a040d006a49007500c0004202903002200800c0340c1c0d60242841100b0070f9421001042c00f10581400c02441000c03c145c1d0000049600f0301c24842407104540c1c00700d4070a81007180400c1150806084078030003031005001960512840a54487e120901703400025a1440d8013003804408a000c0d0050740c8020740c010000c2c40c2c0300c404081032140d0b40da100c0d0040d40003291014001030354a15002030540804041007290909684030820152031150803c9411020181c0c0110081803627114 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 85349299 1250 85348049 85348061
    0x301020f13060f08100302011d091806150a17030c07080d02010b09010b090f1f03060302040b090402181003060f020a230403030509060c0106030b04050607031b050a0210 74
    0x2401d0100d81c081460000054100031140b0f03026070a211086082000d4401000100300c2182e4080c00d10a00700701d107100f1b81e144000610500c607035000d219070040c41203e000f414070072520081c18100f280c0c85c0b40c8640001411003402516226400101e5540a0280307102003505007060500c030350102c0e801d205003500164285411500011500d602250860914550900412100000c151170180042d414544040120700c0f446d2125030085030300d80900e40742c2d5101c4800c04001d03100d04c0320000015403233091000b40501114031060748034900300411419203250000b982401541d0041607100400d82011600000600081c0b6044c07180c91603010000100302c66018080c0f14420311900181d44044116014001810780c8103008003007a560786608100464000440741500d8140c10b1190310f5005550004807988104512514075509041d0000100304130800314a02851068041c0c5906540d110011012035140c46480342d41010203030b002e090107a00030720080c100e140003441039503800c0c0104898a4185d42c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 85350549 1250 85349299 85349317
    0x120f0507090e1c030506010e0103180501021615140f0a090210050301060807080114040e0309060c1606050f030106260708090106120503040504020a1106010b04090b040207020d0b060301020f 83
    0x20800f107800f18034040903800c1e030481c03c050500304018240200001c241d420b064103030906040e03480303400718018900010b0355207070f85900c00c0c02590788410050210ba107849841c0022100b0191500d030b0350100c04524002d0340740c000402ca00040c115517400c1d00c441c0c07060f01d0261a180520340d88403200005a19010707401c1c18141e0f06038940d180d4030f503d85000100800c200030f00300c004100c4c640d40184a0884541c04074450032a08071004244410072014a608510641c404a54407200c00038402c481e0301c1000c620b01402a80488241c07203a2650303424142d804e80b00b00b008003140304104000512001c1c0c022215942c0d103c140e1705858590390040c40c0e0354a646001030314a04003080c1006e04100d880b00d000d00400d80600b44495007504110f00b203907034072641d9004070300030144a15000b0030280801c0c1e00c0b80710165400d09810301181c4d550b59480300142c03003035446401000d940c58100207103c401410300b4000c80d012940d000d89440700407845a128154000340c00343c00554155000c10007803080300125005003c05030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 85351799 1250 85350549 85350553
    0x1030807030e040b0310051905010306060f0b031e0a09050307030215010815010312110304060309030e0402040e06040b060f040e061009030302060a0c05070c0602060609090106120f0507090e 83
    0x3001509001e403032190024600b40c452030a01e01d025003562000b0468007000c0400c0b080124407511040c00700704601034081084602907240c0780000041c080d007508100200ca224142c100c4007143c842e901108507101c202d0b08140a00c801940e441d049419519456a00c40c032064030000e07c0d8a01a0303034441c111b610082081c0d006030b2026180080380d49203841c0490042494400800c11860360340603102d040c500500c0007030a51000c00a22110150140d04c0d90b00e10115842d041d40d903a66101c4101900401a0300e4003580001c648119080c20340c01c0520817103013528034820b4405000d541d10300801001e4200381c40d00075045002400300b02c6481911a0182018081078054401586004000d000b124070b0195484d000700b050300700040000c00c2d000304650380c100d440c404001c01c0c12103000d0425102c1707104981d001054004420b83c0051100c1c0c0c007041c41801203108460120039611049012820307180d4600a02007590b008403070082c001242811692146880341c4c003070701e54040d035030414502258030001c1818616 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 85353049 1250 85351799 85351807
    0x13030c1718090c091008042901080c0604050d200603010b0d0e0c09040b130203031201080105070201060602030f160615051f1b08070b16120b0906012105010308 70
    0x6203007507840c1540c0840c428043c03500303006203100040d4a61a10046103000e2000160100d01400010400900d4607480105104819050007890000580c000d10682d4075600913010705004034904442264100c81c0010184c0752110002d8403203800301c0d81100300500701085c1808105020303817100d5000d1402000b90f41e02594440484540e08400e460922034102d0306c1c0d400400e40143e0070354600d09690380198010000c1022950b540070031801c1107940c9076000e5814400841c2c030900200c0c0e105040f03410380310b0000090004e0f49421000341d0982d1018010034002d40c1051010910520140c805003285c200000040c10002060391542000c54a03244450940c0000d151000e0100d410a491194466054000d04000d450b84a000040000013a5180385c030012210486000a1010311416686c0c0c454010381032842c00d083c14070b40d03040b4481c4440600c1000c1031200206100c90361091040031603800d0301806d4122141d648030011140342a102e0302401043e04070149146904c010351240a01a6200c0c2d81c0456036 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 85354299 1250 85353049 85353097
    0xf130e0115231c0314070f061a010c08090307090f0501032906040b210a0209010611060c0912030720060307120509010e0d170702010513030c17 63
    0x880c1207241e00709410031070103151440c1075840d01c07565880860781040140c0b03043c080e985030498000d0340e0511804001c0e40041006010300c9404801900550b01c500c10400643c6020607a15103601c4440d0002404034000c0d050340340c0452a11001400101d070014140c0344050313120b065143c200c0e19103400c4c5803405680c03003005104108410545040c40d01d94100180c110782001501501c58480051041780219140d8040c8080340d15200302c06950141e2040045100202c44040541e4130300d4440002d07446000e88000000f401402138808454020740c20300544410380d51443c10207c00c0c0c0c40302e1481600103400480b0f40308800024005400414492801c1001180460022404210f100503959111380010002d0058280d0001e400520015100a010940380d480c4100343e0700402c04180044102d008004004c2a5141c1c45102103a9198003003122048130703168803108a0032038108403401c1e5094900440c0100c08a801003c000613024450090340d6680f0f004100c6000c140c1d04111140b2480c21000b46840308 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 85355549 1250 85354299 85354319
    0x30203070b0c04030507170a1403030403090501030c020a020111030403170301080d0302090d06150308031501030f05070c0201050304053c0109031d041404050616030b0f130e0115 78
    0x28000b0a901c21180c00c003400c1da02c46540b5050329200b044c0b030040c0c40c0303054003944503801e0061a00c0c030b036004007803006410b80c0d14094540300d9108850403000a031810f00040350381d600074421404692441d40c01003d6241d2035a00654590348451090805072005210010000b20502c0d190801105070082c135603180d52401a1983c0b502000841c01d00a160060140315410307214130481c6420a40c110304003103039041010034007602c10f070059007020304082c40000402ca41c40d1211488006003034400e03a000c2280c0d00c8a4030b486411148282c03203050014500406d00d0000d507120b02c0103075030414010700544803080105183e01c8140c60641d0000343e0000803142c40d2910000002c4d00c107040c035040e0301000703102c0180c0300d6400a200341c40e0606000c1c1c1691080b2b07069411515654483c011000b41d80721100070030f050a0404664400003154901c9414403040b89000c5018030a004002001401070400d40d031020240041203a034007032030071070300500c0c1e590341441e001a10000d02908054150314103503188081e00300000d00d5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 85356799 1250 85355549 85355551
    0x902030625030b0f100305090c0916050304021302030108151e0703020c011401030c0f0506071101050d1b2003040f0b070c0317180d0b06010c0c0f03030203070b 70
    0x35040d070400810200c510520348001007422580d18000441c43e440d0070000d80c0390700004e442c0b1a003104881d1804807107036815070b000500a14104046072800700c0c45108120131420221040c0407505009800c1944080c0102e001c0c54100784028014a11f4002c1c44081504980099200c5292035000000d040c00d09460140d18907045640c1c440b041498070259024280000c50260081040613400a5401e401d04420b5105a09440e00b01d9401450341d41e6904209403520050701504c011070621000000d0180b0f4000100c0340d01a51128648882c94040303c01034686800040550591580340c0000480500e0740c5010710b8028812a1200d40c007001040b544d0f4119042c99000c40a40d95000308410301189030703c4192417040b03800c8021038070341e03825540c03401c0c581d0066594001040e5860084400d0b0810a175400584600c000c0710b603a0020755444501004a12016694003402001929000c1241941700d580402c0c90302d8000d04280d0041a9108846054020981c3c425001038001044600030440782c85405 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 85358049 1250 85356799 85356811
    0x60507031404080331030e030d0e03061f0e1905070504140d0c0e13030e060f0405130905030a0302091201060e060d0c050a0603020a0f030510090213080f0109020306 72
    0x886042c94a03540d000354511024001c01240700504220320090341110a500e095500110051100740e8802d180103030001c0312203c10140319000301180c558100d032140d0078801103508020010050b3303840b0103580c00d600303100c90321340f080c403503002d40802003004440711203068068500c4038058599000b0751801340701110b1028080008104041008004401d0007010418002c41c1c00c840c90105a415450a464205499881100a04101010855071100e1344140b401150300030b88400c1000350100c0100300a5108026445100601c24801840030741409070101c4d8104042c8280007036402125251185950800807141000940000b42c0c1c189904100144600e8022080b00030321442d0b0600c4044034907040e000b0511030140c0e580032a50004d111019551070014103024060768181a1a200014080c1d40002221000320f5000008002424842d204041c801e001221089124600300540c90020303501c8640c2415000001903008900e82906019404da10000c1e100005120f004901c180740c02c14800800c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 85359299 1250 85358049 85358081
    0x5010c09090b2422060915020f06070305190f1e06031a130f030c0627080d140f060307120302030a300f1a01020a170f030406050703 58
    0x41c034508420740340f110070b1607180b40e210760f58490200c0806003000780d00e80c068000b0144050103001039034a0300300c07400d80107403812150f83d0f0320700c841e8010060741d4401d04040c400000f9401140091030b018400e600c0305030001d01414864580c541c0c1c1e00613200c140d4409603510002680e9a9580c800691001c10f802c00c1d40e0509400d00703107e010b14544601518174141012020b00242804c0021130180c0c40821b440005548407450744440403081c02d0041500302582000c035121071511007050000310000c2c14020740d968012685031700311402d96444403001d802090380d266286840d8001005080c0c83c0d8000188162541c0c0626042c074645002014542103c5070b00400c032030452080582d002c25030100448104003002e04011204540101440591065050b402410b4140071024103040052170f0f00400d08800d4503103001d01a00d0031328880c589074818034100c000d003d03030702c284400f40018140d0314040326011461402d243c100b0a1030402e81d6496807086804642d070964600030460b400783c0512071100e0040441c4c0e6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 85360549 1250 85359299 85359319
    0x5091e0a1d010912110c18060120070312030506030d0c0c08070e150d05100e03161b05010e010c0b04050f030a020d0801120305030406090f170403020a120507170a05010c09090b 77
    0x1000c0340c2d2811f020348042d255040303030070001101e03a40255010307013030028040329042c0303405442c82c10700391592401e0204a880c00b81d40018210040e100303024980c00b860005024010031002d51340300399036100800c2400c4402d204c685100242843d001d00200009240c031850410841c41d14806210840e85980c0100c0e12071030403d85058041980050780242144464000007088804162258618014410784108191891601a04019440707180c000d40041808030480003548400c015240e1400301d00d076080c00a4001d0300e01901103034500d446031fa0040c0c0608103641c00603d01a21650440d03001c24600c1c00035034080503240c4182303980308800900400683d01c4030740e50002030741d0b4014a107210140c0301034034480d1603001c0c6200f4885040118004580d1148030504a1400c00c01003000ea504948020391140c2d400074000107014240100c1c00c1e80a96000c3c001d03003000c90070181d10018411181041e00c6907031080000d82400280e0910680102520f507071140038401e441d1010042c03d44008411081c05111995 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 85361799 1250 85360549 85360573
    0x10e0628060e180709360207060b0d050d0507030306030b01030b0402090a0b0d0602180301240501030509120c0a15060f0501050702010c03080603210405091e0a1d01091211 75
    0x20044180c44204445200811450505001031546d54183c690654500440b2404d041025030080c01c7c407078403c140900c0140d401d00100298540c402501401035040030300108001b43c400d00050101900c2814001079a58494a507040c1050f426002210405d201c04188030070341c80d08014282d407010716034034140503c1800340041051106000c600911068010940c0198400d0001c0e000080341805002080b0300342151010b011151414601c070580007a00354404a281e500c05c0c060984a404164014000310b8030041c07aa41455200401c4402240035801080c40051581f81101100b5440e21401080c141c1c2041072002c843c018030342c030650502c18200711050060360003142c80003000342c0600b0301c28455943c900101303007410790790052a40c0e42001c0780f0404a040c00c3c03071000351080d180305458200c0d0994a4580521614640d450100f0b10201140c00080301094580c0100340030302c46189c0d003206140b10019840b0f0035141030a204a03010308040d20041849588108007681036040c0c800205030300040781c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 85363049 1250 85361799 85361807
    0x2041404050a0b04020604030b0708070e0f0d02060d1509050601020c040e0d270801020403110114040902090f06070b061e010f03020f0408150f0708010e0628060e1807 73
    0x19400003000c040c1c1010020b42555906c0050b100195049008480c2c5440d10b600000d00c0e54000312a5400401d00340c8030b02c503500c0d080c900500c45607104081d01902d90fa41c81a020811207400015290310f8050b190807641c03030642c101038829401045210300200352400c180d400603080c1360450301018040c40c0780c8095003201c0900050824100101030405450440c6441c80c800040580c84869201d000010703840001c00074415030040c400c680c0980c80d10046960240011500a6a6510403005a840070b200503c640030240d0300070010844006d081940015a0b000403803c1c0390046001a90f040f010041044460b0508009980186500035036100702c5145000000e401e4a11b0f20f18410101a408035018002c105090101c40c0580003013000c88901c003a1030049507902c00d204075400c020842c8101e0120313116501070841d8506a4040c680307005016522101400822041403151100c1c202106401f9500181194806030140c070099071160b080c14051010300c4420b0300e40900381c031041c01081040101690380 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 85364299 1250 85363049 85363063
    0x20d050721081206030703051902131506050a0201090b07030b0405090a080a0c0f0206070803011701050106020703030809011e020a0201180f03031d0303090102030a06050f01080601051b10090204140405 88
    0xd00b440383c0e100d6120400400d240085a400040c070300e22070400710744c0201841c43c1ca14a1080d2003110300401e084460024030040d0b4080818140420b4201001070081c2400744000c2c020444c01e920001503131524030b4031190b40703507103040d0340d4840400d5607050501c4c2c140c10103028480c0e020403094001d2103111800d40d6407150910924150604100510342c0b54400c000d00d4803100940c050b001481141c0700c240c0d5040080321944203104514441d65440241c46001c00117004103030407905c0e150060140075180d80c03826505884020311004640d581c1d0b02400d80c003032030000e400e0940c4903560840140c41700300b404c230041d0031211702081e5a1803410810541e0000581c46c9824160701c503074146004a0850000360403800940d2200b160b1458a00022007001003100e03055001e036101d4071072010300340080ba660b6000c0c02001d4284c90481c45c0001c03040000111154020401003503450318030b51140c400880c49200075803c1c081080801450f094a805100f415440e10b406007400c0700d81542070340c103050b091503501c250359144 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 85365549 1250 85364299 85364317
    0x207030905120708060f090c1804080a03022b0b01020a0c0b0d02070215070b010501050705210405061c0b0a050d0609050309060307030e06010b03070905130207020d05072108 76
    0x1c02c5800d516003074000d1115800805100c0c00711005418142c40340360001c0800c9a00261a00c24038452221519006115111103131a80718080d403a40caa035101e5142a40c044070703c4005050b000c000c050101010b030f401c0c94094401030040300b24103078083d54620003900ca02e00c50080c11540000820004540d004c00c0e4102124900c004141c3d440c00b43d00f9100707020b4024400c0c060343c00000d44407459007969009008000507403103006813744d0ba03138a41c0e00540c3c00b03002c0ca03500a400d560104071100e0040302c80d0100301e0180c2c2082144542415070714000905031307078000704d0714515210f805082c01e1415030150050000200080351a00103103418600495000714154002074002ca0320340034000244041802143d115100241c01203940e4600040d001d40a4251280a440c3d680700d243c000080101c140cdd800c1e607016100030390f10b141905240004104544a60405036200d29500304440001a41d43c1c201002d8840d1083c2c0103450901d24204510000419080c1028110a02c100740b00d000104000704451040f2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 85366799 1250 85365549 85365559
    0x10b0901030f0f020a0c140102040e040f030c021512160c021302040b04030b04020906031c030b031914071a04150c060e07090b0a1211131e0c030207030905 68
    0x80d203a40200040c3c240c3c0300035102801e00c00901d40304104d0f841001d002180b4021000c2c084019600d11a841c201d10039031140001181c4a440400e00180c448035020090034040c0c41d045071080b100e5000152440345103001e204440c50001002d0f0034102900500640c0070314404215040030340c02d080c1c05040d42c2c0c04080000e1007440b07110025450324980c2e9041c0c03000380400a41c041d8407030307440b481c0684158500b0b031020b910400507000020080d15000490a66000d0b07030182d00c8010fa0035202056015040950130107906000390582c3e142c030402c24003071440c003450050207403404510911240c2c50500c01c0b140c2225480c0314113a51a00b001d600c1100485048482d10900c4490302c80b01404115002104c81074001d100070b00340381501030f42c440006003000581e50203c0041000300c42000400c07000e0a10340c8500d000c0760f29150000400301d20051042c4540f842c0182c806420100d1031442a0100c42c500c80400300342d00300300001030f43e04030240c1c860080d00020b00d040441c0790030384a442c040e00c440c1d054803400303210f0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 85368049 1250 85366799 85366811
    0x106030903020f0109030c0c050d111c0203120403111815120a050a02010e0105070b06100c08070606030b070305010810050903040b0a03020301231008130c060203070506090105010b090103 82
    0x14801c1208030f91041c1d111000700285003540c0ba008006c02d040d4030b41542d4030218114082414030700042c5220b00c00c0d40c002408280380c86030703a040c0305011038146002144041e00881402c05604c0912a102e802c900f0551207640e11400d5151201d80c101f190071169004498104003440c80c103522010700d907040745a50a0010b00410341000140720001b2541502031980111214801003140004920314224800d80355102003044940046800340141500940f403600307e43c010403542c3c1000150402d5040380340c60148641252616080407607401403408482c0c003a6142802c1042c0f180c551445500808649000e1005525001240d0340c1ca220140e406034259503103901144c030040041080394020804240344030748401102c074010b4000d403c24491a0041c0070556a91145803d00306034290421900800c00494000c9640040f254071000034003030040e00038440e00c0d030b07c0429201a000070080a41d50700440ea281c1302c81c07130b0035070070840050150b507411781c10000140070500d048020346400788001c0c6000030304 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 85369299 1250 85368049 85368053
    0x3060307050d06020d0c020c030c13060b040312080106020c0d06150905100503011a031f0f060f06030c02010c1430040c06020f0303060f0d0b090f0f07030b01060309 72
    0x1010029800306034040c0020ba120010000d541d0060030f46009144400c11113040c441c1c405a07140d140c0740918982c0345c4c000741d002c41d400b49005c0220041411220034001002600c1740303240007565000d81c000380d0342c200c000d0b00c03620b00c4c2c04d0740070558502510007440079011600040c2c000c10700103050b412008140036284c002e00e000c20100d143c5201b0050001c03240502550400f8410b10311000d5807405014000c1d42414008869245860042003075000c002d402402014841c80c009140030601000b0b444085840310581054862107010f098058510440c85c2005240340c040050f0840d2034080800e8296410440040c62649d00041c40d44070b40d0b00d20032140380d901c155529104620311903070010111004404005548232184a13202284114440c0080018072625400141e9642c0240980020103a0003000028820706164030b071140e1915010b440201c2d030103e00d50382c035640c20108451940d42540141010031204404018a2000380f60b0000a8010746040d510ba0341400d4005003d00824192101c2580741 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 85370549 1250 85369299 85369303
    0x1c030806060f0c06150a050306060607060e0709060e15010804050a03050c10050109050f060306010b04090906060b0d051506090904080c0a0b040f050610080a0609030203040f0e041e08030a02030603 86
    0x9090f14143c820b070b840a25004151501422000e0300450003160005408a2981000980070b4010a00104818100f02103035550002400c030305012161180034402002074102d4a9001341d03802f0b041100c803500c519150101c032112a080b00d920240d4100091030f4180404950003184092003a80c161a0095443d854101250300d0714443d440200b0307a041c42e007000040c01071225400980215210108110203407591f00400d40c5d41c0340700380606601081c0c108410070950000c0d90001b65180c0c42500301080c92659000b460140b600503442d9004059214001c015072030a0b6541d12a01f46070040703070100d041c16a41e10104080f0b2400400040032444000752601f1a101e0400c04103c5c95544031440c50030903e00b80c40c001d040342d00c203103404880c14450240814002207800540e00309640500300101001005a02c501025020b40c0e4030990075400204030105600e0400003c8034041c00c00c82c00b425181e41094a00510b01086d64a0315601c855000380194001440b0b010440e03030000e5607100c1c09a2030351a600c0000f4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 85371799 1250 85370549 85370557
    0x1082202011808060f0105120304060c11091602061008030904050a02090301020a050d0e210a0314010602010b12010209030d0815100806130501030206190207050402030c091c030806060f 81
    0x2100a40c2010b20024803100001140341c820564450b00c0c1c1d44030791b610001d00c40315101202d64443c49070020700007440000d100700581d19078035009a662125450941012441d08282903990054454186940c5035002c1d070108041608001e051700403100051030800c44d00d4580c000c3d14803051107641c81c0c0d004240f409100b40c0555560301d030010000c5540d800401005072866100d900248211070910703a00c803d00000104a4080c0c41010390503481c04880118001441a80700c00c4005080c15a280c402c80310725544d000e070460181003d0340000030701e99418800c0103244403034074507910130681c0100084040c648011460480501180c2409051901c4030f0310f04049622010749101d402c02c01c4085118511580107040501410040d154002c528140410400544400b4080690000f0081002ca02c0c26241d40c00040009007485c4107a500304e03a118000141a40d20903502d00303204440103e40c0c50030504d400b02c0307217003110359101c2c185800c905100c6d81c0140c0700c440024820f521546c0045004407001c0301c410119 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 85373049 1250 85371799 85371827
    0x1b031f0207080d0b030601060c020315040203100f0b120601140f1305131509020d0b070e03120c0f0f0c0d0312091506090b06160f0c12110108220201 65
    0x9a038484030600f010000800c45545054400d02c1394600001e8000e004030703142247c854018002e041050f0942d070b01040703104e801610881c0c042c45064a05002e045191048022a100818000c2000070044c0b0800c4042c101e5a900220540c111000402801d05560000c40c1c20325002c0da0380121003047e03800000c1c558800442c1d1950f01504080c1008000c08072103042001c164810503400d620040240038042c2110580b000007074201c542d0307582140c0401d0030441015488a41483c280c0310a0b0340d01c5c40440e05046046040440300b02c40403500344100c0b0018020103403220868030007031403001289003030b42da552200d6100d105c5c0914001094801418420f04442d00c0e5a42c07982c50603c004400d600c0c042c0079420642c01d0303006107645082c0c00820410380c44e00a007411300c6c1004207614100300e55142502081c4020640c00c1703135141c100643c0600080c1c2d07002d0214004010350030b200f00f540219400c00701074900d400362090f030401140d00c0030024003044001c085e1211490702072545096400314401603510380350413801 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 85374299 1250 85373049 85373063
    0x415080703030207150903021003050604020d0c02010917070b0c07080706020f090a0801020406090509100909050a0302010b0a050604180f0e0a0c05060723070b0a030e1b031f0207 78
    0x4802d1540000b0b82400b00e07100d130705400034003400302541103940c2e03c91800300940c40a104c4401d0401d062103a000242c0100340140018602605841c0c1d0008403241c82c0c0400016135154204142444940400c0c05c42d0720508180341e0b4640310f4079035296820843c004002d04504200400d41d4804e00804400f911000341e4840e008640d40c14034000c0d101c102e60401c0610510403801c10741c0115841d20180240d40841d0041e4030303200842400c00f02002801c07540100125042d003580d110000e102d90450003104051401900900070780344440c1802425500548400c6015101c402c004114540701c0008480465400854440d10100c44200600c0548030701410414a0390030691102c01100000c210b45a1a600c00ca5240190554540500c4068003d2010241900e100300c22003241c6c01840c07602d2180d0141c0d80c1000e0b62130301620780040d106640c02c503001071000a030b80c400e1040107121f000c11807000c0440042d9000400d92442c40300080d50740c201e10f4260750b12031000422543c00d2110070b80544080c80e62080c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 85375549 1250 85374299 85374313
    0x11d0306040c1815170a050303070305011a03010b070b0a02070b04030503010501032406140403080a0309122c01090e0108060a050612070e0709230907021209041508 72
    0x500641c80b24140c0a11000308510b01140c1d00c2802c0103124202801001e0350203c015245410301d261130300080030310314201901446440c2d000290040c0002c51207601c03180c0300007845504100d814810081c10624004a80c24200700600108005600340c9d410142c0c810505200d0350f90f418403031400f034040d4500007403002c41e05c002440704041d04000518161242030340d0402002900208090180581e44400040894000d0040c00030070f00c160782c01d51004c02e44003036491410381d0725505c4c1038445c0c1c480d01c207410019640d00081e074100f20480042440036070140c034080e400c81d201c60741e98403110191354450b5a07036107441c0c0100c0d0000d40d0003140000010540042c4050183da5500801c0da01d800044030911401494080024250324180300041a000303aa5401814020f060000110300700002510704014842e049100103410880f120303844413a01c00c500800c1000500c9801401495107024114800b0b54010540040c4880341c200b0944c3d894010440d004201c511158081d581010b030389400400d102d0059038 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 85376799 1250 85375549 85375553
    0x4031b05010e04060e06060d020c030c0c03010c14090904140708010f05011a070308041b08030a020c010918020d0b03010c0c140309090703020c07090c020c0924011d030604 75
    0x4400001229400e0b00c81d0180095248100800c0318510701942c4c00c0900c01c8004a0380c5814104080d00981250190051418542e040b40e01c0c69a00111307006412540300c0c8041c403101e81020700500c0302040c1e4904252002d0030f810020300a05006407a00c4c1405112074500140034046c44840000a8000e040706841d00f983d115009140a0070024545034419800d01c0c0000a14034040001c6010282400c0141802e00019540440d0301e1540070f4829a600144005120310207481003c004c0e00428499008554070442c00b14040d003004002c1a22030306221803c4410441038000e010080846024814010b80c1d0b0300034500413000400031413008940642c80e10702c1c1039a03181e4003c4824000d10703005224201140404040f002e6a9100d010780007a00b1012000216a83c01d0090700601170280d103007001e03192200e4a800c3c1210456014520b5003005038030012507840d0908210700c9003034201541c400c10000d00450036051680c1c034580108810704100f90301510714032100c05200d03191070172a001010b445640c2424 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 85378049 1250 85376799 85376843
    0x803010b040e011205070608040302010e0714040c08250c08210c04050d032d091502010203090c0906030304120c0e09060402010804020103050c130e0901060b0406090312050403 77
    0x500418060b082030074000300320020490307003000c802a404401030000fa8144941201d0000700a4001c8080d0742d03c43c04a4050680c0600041e0f0207403003050b0190030108138180c00c100699444105174070a1181901c180b02c4030b000300054410320f040100943c680400300340002242e094865580103450030602242400411060f42000a5082071035a0f18201d540c442d54a2185184a14855143c2c460340c4990034400182c001c013415140d980d481d446039040300306c01000c1a101c13401000004400240420010302c40850684403490b40c806851000714110318100c3e0102c0c0e5110160b4402d01d1240c92034200003903195400300110f4019000c1042155a11a01450b001100012901611864442d020005080e00000144082c0f00e16016541c1e01c84a45130750300150000c20300904201004102006204510010301d02c50704000d081110381e40101d1b16000d9413040c00c40d1100d8010104e4030310100000c0040356802641001500d41100d00301c1081c0340000420390f168400d030360004100c2d001e0300885010102c02 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 85379299 1250 85378049 85378057
    0x102040b04050406170d080c0903100b010f0c050c0d0501020f0a030c08070c030503040b090102091c020306070809030f090103060909080c0c0108011a0d150e15010201020304030806010302160803010b 87
    0x40d142031140301c0d1107a607140c00c29003d040742d40400e81e000d5400078000600c00c202d0150040c044142306890300800d080461309004448040e03405c0e45440380062042941d000c130200184920303034648580341d000300d41d560a48400110300214402d218248000051040030350441b40d008901005079903880100c0340707014014040400070074022546907070005041034007070300702d032124981d041c1c3e25207156580d00da0b90303181c0020707000e000001c95650a2140e030349152210a0079021004e03031042010482011481090b151000040a036010065032805000c1e40e148000150b0f410a4000703070b20700383c0307c09281004800038919680301034111400c0241c00414400741900402510301c00b2070540d241e200c0a0380054907400301c20311030050f82140c4015002d08a030030070005040e594046642c0801c0c80d40d044519912441c1c1d1340d41101600c941c440703081c000281c40010740040301140a00003581185442d8902808502000346000d0501d500018603101298910311000f0019a10102e0b241d03d82d61501c07910790300c07604 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 85380549 1250 85379299 85379309
    0xc010b091303091a09041e0609022214100e0a0e15150d0902010c020a0308090102060a0b0109050d0f050105090c0a0504020405030c04020f1207121b0917030c0102040b04 74
    0x9400e040410805841381c80103501003c10b10040b49820301d1807050200400481c0d85850034245d010306d407040c515541d80200381c020f2005280160701e4041c28400c0083c04001031100319210741c600311041103010700a081c54107680c00d003210030750058034041d401660070b07820180342c00e54030001d100d034081080108440824001c050b40c08803400f10303030200828000d0009004280e46001c0c80140600c2d12190708580080303d1a51062518811200007503012840322030064000710b4003a040880c01348441d50f81003060395880403625070140b101501550018000304614003541c0d0007043c68036680401d0010220b00781641950080080103c3e00e841140603450340107008010744502d003040e80010301071906000f541d0640e140100500400740e81041000000d5210071070403090b08a090040e030002c01021440c0034842e40039030301c6801c41101440348890071103046880311030480d55038900030407645603c05840010383d00354441c134500d40000c1000703641c5940506101c142e415030000501145000e5210050000c0303403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 85381799 1250 85380549 85380557
    0x80c030301060c0606140f09070905040911040c05040f03060207021804030804030905030a02011d21030405030c180a0e2d0c0102030307120203070c060f05070e040c050a050c010b091303 81
    0xf58441c6d503c540c10401d000344c62030344035094000710001450800000382d00400700382050805240d650340818140e91440d130703064610304009000d000c50740c2042d0260410445e594070b8820316150401100c0e003038140d991b02000e072a0301d031302280c4241151240c0b101c0300d05d503000364410300203240740c03500c0c009101e60002c036000c8000482403000003806080000d00c00344555416100c0b103042c3d10b0700e03240d08040c942c040f030740666000182d401c0b41000c0c03111070006240c404550784080c2da40d8904040a06240c1aa07184c20300d406511040b82c0300354558002c00d9969001080302c500070401c124151f01c02890540c18803010085062040d03641c903800d44d03900d82101d400c0c038070481c103aa80e400050310043e84c9a00080b2281404a0b52154074680340c00c4e034641c015580b11549003050015101240c0f284400c580d14400d030420090342d19000e1121080c0c201d0384038150818121028040041e610078000c00320700580109009104010800201c2034074290045180c1350b0015000d51100d2074131100d00c0581181c40d407416070100b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 85383049 1250 85381799 85381811
    0x1808040b030a0609202109030309060108070b0702060304030e06030c090414040c060f0539010e0c010e0a03060203330f01050a05070c2408010e0406020304080c030301060c06 76
    0x102e401802140c0c3c0480e01c4000c1c100c44410f2005d48200254046207075545941a641612183c681540355094090750b0004000c0d07840780341001d1414641507040c2c004102030360200340c1c02c00c05006860200d0380c0943d41515a1512622a49010f94034800c4800d407882d4002d8010082140100d8607001410007804101d070207211a03460101c50036100c06003174a016020560440c014000940117100c140c800d40500d01e8003520340b2048021004d80300f42c0f00d403010320b8008202c01d0003448000300c90b084013040c035515400820038001c40440c8241d0701e402c41c0309030718144500d50b0030001e080d81e070f098141401190800f100b9076407171a1040741d07006054a458100171803aa047c0130608650000e00780944242d280c080c1290826500d104010746154010308061003c00204011003c0000d0440c0040030040c19a103010b62101c80c2540c2144400048202e24107080142400040140c2451550010341144c0c0000e00140c0d241c8032801e000300c2e10b114607010f00d00d0302d201c0080001803040d40030005000181c0a46030030044 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 85384299 1250 85383049 85383059
    0x703021e030a030e010f053c03040803010f24080c04030f060504020a0608010b0702040506040e030a030506090a02070804090f020f031504150e041103100903020606150405010804061808040b030a06 86
    0x10701071013020b40544090200107051f504000c8552090f810744000d48c084542601b020440f0b040d40c811281183c142c031000c80100410907601c21420080c1c40301c0e141d124403d10b00c0c07205c0340d90702c072580840030303010090b0302000b04441144110403180030310f411001e6110704030410308240b001f400066030124011708842e50005011445081f45c04d0588000d130098a03c2c04a00c0e40810000c0c100207401180d004c0c4c1d8070300725000d542038200000c02d010b4a4035103000c00c0510b044410444503c46c024600380006004116000010340803404a5080d590804d02c000351864840d8400c1000380600c0401701c01443e000400d000c00c9004489003507050b070f00102d50a02600c44804840014031b025803140c0002c49400303001190004549030040002000081d00701c4800d5000a9064400d9610051042d0050303009181032002d01c1c10032000e5000c0720019010a2480c0502d4000020a180380003480907151175a51100e20080d82c3c1c031065081002038214103890348036515803240c072140354810744900c62010329001d40056 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 85385549 1250 85384299 85384307
    0x304081b03071716140907030216061107060204060519050a0c02040f0b0a06050a0806060a0f080702150c0d1803050d02090a0f030302060717090703021e030a030e010f 73
    0xd9040041d010307144403482e0505110090364900000d1030540581d420700c81d00c91007900e100c100200300500c009040003404800380500b6070806000c403010103004014064001030b020205105d4242d00450021303002c81d40110780d030180c4c01600c1004000500001e4002819030f4818060702081c010b040d40036211303131410501030703800c0c1c40f0309c2a015002c603400081400152a00f03910101c401e25000070003058044c0244002400c03410190004408507070041010543c1562101595074445001d544091070291030580240c1241031641d0b80d807007000b01050010b03101d6072081c000740000c040415180089030610742e41d0040140c0010301c804022902d0102460340300300c41144403171006600354644516003d0100e402801a6004040140e04144900e00001e1f02801c29003501e40110b0207507002d0003140c1462840101341304203914901002d00c0040052046159020595030111703076040300d201500c10400f080002090410a0348030b035041c0641d2044505254218074205400f240903a100c0d141c1001c150400e035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 85386799 1250 85385549 85385593
    0xc06070816020a0b071e0305070e090405030f07050a0c060c1a04200109030b0a05060103050c1206010c02040b1f030c110c132d0b01080903030403080406110c030408 72
    0x760050748861a0b0340c020951002141c2e80124143c40c18001d1807025110920100c03520780040400030303550b88104420254400110b20707101800703c40001e0b082c1004d485255a034002c1034159070380c0c004001008010040200b1042d890700390b004400f0030032140c3d19076028200b00f150080030741d4441d03c1c1c02d1180b0004610481d40720300c02c9511000c080f00241602060109012078060784905200c04c014010010482c0d042d05035200d091940030214980c50044001016214064000030901805001e2019017001c807041c0036034003100078070f0401e03420799007400001c0180070180c01c810f40104520304001c200c014005850880702c5901d8405000d0392050900480f02c070355541c80c401003140c0003c4070b01c0c0d00380e00e0a0040c10f100d6104410300481d0b001e1000929240501200b01c1c0d110000ea4844a640c0300051030340105a030004003428180290b1421004c042e0312448000c00040800c0b5000700044c04110745548440c0380010421a12030320f458081225540e82d92043c0030f40c0e0702506c10700c034442d402e0880d006111 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 85388049 1250 85386799 85386841
    0x10b180f0105010c03080f04021201090605060f06120a05040602070218060f010207080703080f04030605010b0a090608060105030103140a05030c010f05011707031403190504051206041e0303060504020c060708 91
    0x44003555407c40408224030000e00103d0748520814042c03080c10009024200c11b250150b140025242480000c00008044040b4075601400050007600020010034038aa94071030020300003c18141d507140340410080c803d00d80002c1d07200c4080d40d10a031032100b003482ca45125400588041813000c000c80c005984d00c0e907140c070880d10a42d01500050001405c4940907100c80004101c0780e909064903941c0d1441612426004280c0c00100400ca0404069011504800400d8a42007945190426038002060341c1f0050001a1154041729644440039404205042050750000207482e01d83c074910404501825412000603103681c141070002c00d001d1240c881c44220040c5640003008000d255940b640b622030070309401c0d01c94a00091060760406a00f2040382c84103800d20b9558295118148010040007040a21035104c5550102c42004000358a10350241641030394401d11100303480c040e107422809003902c0e801c8540c100d030021601e4551400000755540c014403003500e4400b070a582d60190018100885600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 85389299 1250 85388049 85388057
    0xa0305060109090201031514090a02030f01150203070f030306141206010603110408151015020c0f0613091d1902010503070c020616030908120d0c02010b180f0105010c03 74
    0x100010300d01a840f100c0400e1041c1008030310050301070509070b80d01e07032294881c01007040c4000c0441e089150026159910581b5500110700710709100102c002c9816050040d004501c16241986500070f000b0019508075940c8403284580c28101031070300034043d001c00e11540907409031000c0d89281c0c901e411480c10b025a84010002c041c2c03070380307408400c6001d004c4101d0001c3d00b0301800c02003c2010441845018468549488602c44038181401c04004840040e80f18040c02c0310602981d220165012800800c030450456840406005200014500344103c42800e40704040341440040c02d6020b40e08510001c01d04020384000511540b240703940c0390402c40809050746000400f816005602802c0a541c1000f01460441034800395036000c501c0640c80304407146401e280601c0c00e10304155000140c0405440d01d18007a19070001540701404407805042d0036084055154400d600c0c0304c0b8400d602c040100000140581003004c402c62207030b22080c606035007156040c0c902e02e0010480754080da4003000e5580d41076031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 85390549 1250 85389299 85389301
    0x423130809060904060506070302030304150501050d1101140a090510020a05060109050c0910080406050105010f050703030e010e161401020105070804020f12030a030c02061f1703040915080c0a030506 87
    0x4028465220001c81a03210350741345c074080341d16110400070340495032298005650b02d0416040807c102d07105038100c44200c1303052200500850301e64050302c00c1d032280d106c20340301c1c10640380c040162607900e080c3e001d0200c0240049100020980d004098030219042941c111514000c00817003281c580e00030f404003411551000004011890266104503886600d110905003440074480c009500b2841c1388072201e00103800b20040c0810b01450b8800c80e401403600742031a01200755600c00107001401658009810b0555030010342044510a4115140c090340940035034411141c10038800300c0c2c640d01800380310a428203401c4116515401481030364000c444a4481c051143ea49900b00000f401907105e0890b001400d1402800702d0584c10400b5003c015001d440c0420f09a01c5208020b00d046802041d00007849440c60403108c2030040c415503c0160340c07600740c1c00403082500301201442c610540e41302d210107510345050f40002c0720b203490050054560540903200990080010056449a80d00018145801c044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 85391799 1250 85390549 85390567
    0x806060a1704050309040204060f1205040b060f0307030c12050607030203310b0103031e091203081e0f040c0602061501111501080109020418120e060904231308 70
    0x20049a840b40c4210b048902e484100c40124003a41c1047d8402c8010074440c0e0401d00c03071303580c0015400100303805c1590b0812281c64a034459a0680300040c06083c0250500c45040ca4a5141070200002440d00305400003407a81d514500d080c11410102030070381c0d19003d802c0201d0b10841c07090003200e014000c81e8070221001d07001d00040c4408000001030000d41d6a445208240016400045140c000c5000f5218001075078420904217510310907440103030701004641903043c000c005c40412240381d92909850288003540d01c14414000c8400b6035004040c03050110810482034041d9100d000748030f60300c01c058450070140e40d50400c3e607481e90195420110b01c0c402880c084080d500c5980d0f00300003030340f0740000c80703c404c9900d09405030503000a801840e603503511000803001707509003805100030f4040080ca24001c0700c0d00d00c1e00c402500d0044140c0c0142000a003042c1d060140d07840c00c058449810700103104100164840310008814040a10001c0030006818005600e4020545108000d00c1d000f01e1428900403488c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 85393049 1250 85391799 85391837
    0x3040c030209060a0320011b080d0209030f03040801021c0c022a060a030911030a020a090209060913090201030e0d0903060b030124090b0a1406070201021e0d0806060a 73
    0x14a041d810a03961134001000c00c444410035002040e8015400366402141000101414454010005c102629040e00310000e54140c04603400544e070401c0041c1c0390150b02e40040c1c04c1a441254229440c4000304000c1a400410760080a1031004207010b48210380c20309041c1c3c0f00750703040d0b90051800350f0881c621450320004442b000340c5d15003140c1d943c0341400305590f0f80080d00c40d8210a24000009030760b101e529080100905c00a410701100b1001800000840c3c0d002034080b5205000b1403820f150046686003040c0c5403281914440d210040c00090f98954100780ca100414458900b60b00190a080320b071030308070801140201503d40c072580c41544084c190b40b43c0f03001502918200642640d80c400001c0000304120510350180d256107018a0140d500c0c0440480984142e140914451260307800100000120443c80c8000c0c80820b6038070310703110056400181d0800406144545404900c0c40c0b40c40940a00401c40f0305e00a15a511404410b0b154130090101d180194000b04002c03c40480800403101d0b01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 85394299 1250 85393049 85393051
    0xa0b252103060e070f02060c0903061914040f050105130308060613120c030c06030501080c040905250f0b0304050307060b0d05011410050103020c06151207170c0603040c030209 77
    0x41801c0201d005982c500c41d60004160403101400002c0d02c40c4c1146102c541d050041a406c070a10744001d070b0030a0b12400001e62210800f910302e0651003040c0106103d4107405800039a900307200400d0315065883c09003002d0484921786081101c455180400003504502d0502d0610002030f010340c5c45050650b548001c1c0032596105451126066074610000541d12806007007100f0124495540307902400c0c0707186040d0344404030a81186c000e01d8140001441066070001d652410244101c40116019009040160801d410441203086812045020a004c400c04090281c102d034456050400d6290b03540418035507500098030000c0c403e4008000100104416410046862500034000d44452046554550840704003580c4580110710308020400ea0341d40c0400040300804c0d084c02c040d4a03016803806955180c44000b0300b0142c1e0703440604150005512414400d00e11400c00404039040750303864403540c242030039101da0b500c880c03446243e252204505051007900c2c062a0702a4a014107142158208040c9040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 85395549 1250 85394299 85394363
    0x30319050613050103050d09081513030527090a110d02030c090306040302010507030b0f03150a061e03051e030307030c170103030807020c0a0f0605090a050a0b25 71
    0x103442c40c401200210314850680218417440042c0b403ca4010040508a075107240c0c0444000c1d0040d64100241030403001c1130b180c0c01549480c00244a08503482d080d151400303440100903c0045070003030003007804401082c0d041d0100d003c0f104001f0b0f03640c600011500395841041142c03038802080c000550f846102e50041e50300100c280192605100512005c02d19109007224142c0050b074480c0c040c813030096010701c6000580f250035101c200303400c009a000b2070390b07540300d6030700c078421030410031001550b180d019510042c06000350032441a11015507a401000c0d9000c54002590b0303d0242e2013055113469401c1c1d4403003d500341014091802c50380c5010055009040f94403240050000b42c0501c51890204051258080c6109403141102c1b400c155600a00d018800f001285c0a043d1030402407042500b981081c40c2102c0032486e10710f58400d00200450700c1b00d0016405a0341044c528500450005240d4014000819801c7d886859083c81c2e40880590001c2c01c40001e0440c1000690f2002d44002500754442065 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 85396799 1250 85395549 85395559
    0x14010912020f19030611040e0403121b09080106050607050d0f0e063603250b03010f080f0a0804060305070c020901170111041505091203042301020303190506 69
    0x202d920100340329504501c0d1202084045150a004014491103034200005035006031509190a1203c402c0d1241c41c09000076080c01036000b080c1881800e00d0b003103d00350b00c40b00c902c030043c20202c800018041c02c6043c00740100c15400c090000c200350905000307454507a40c0010080000f01100031090b60b00d0010504401c080099580304080d10b5181c45004120b41050501c01c4005007429a49a640c410b03a1400c085418610b1f540c010004e41e600040d111511640481350340301c203002c1408898081582640c00400454008800081e00c90b050000f42030071260f0800542d46403002e2100001e8684410900081c1300c07040c14842400f80030b1295000c01e034021000d050240c0d601c013658000540440c2c0076800180403411100825604000a005296485c464180c00c241803901300400b008110005030302c0c210400101040c0100155100e80b0341c6002451210207485c1d4a40c3c035030100d1074841241e8030000800078080c011083e601d5100200300c80c800c8a22290f0350040c405892803040241170f000e81304640c09 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 85398049 1250 85396799 85396819
    0xc0f0804171e0301031a010506070213050901060e1008010c1103030403080a060803160302070603090203030304120c0c060f170403022e0c0e0a0801020901080a0b0105120f040605011401091202 84
    0xd5002d81c40110f010f980644252022268100503101c041041604034a0140d881403080f400107032150f018130740600c6401040401c140d0b8940c507469005110b80d5202820704886e1704280010320085402030400d950b40d01c0c0c001e100a52190b1001d4035055104102c854440d88100000740200b4410b2a0642e04410060404140c0d03560743e19200c0d00e5900200105286e0605180d10070742059010045800180b020742400e200b00c500a1300042d850307020060016040e1120300b0301700307d1000d02c03400307580c40169406582086c150791104801041c140318418254042110350350100341c000c0415080030710640c1c0c1a130082410030070004034240c0b80c0d140701d8656441d50340b0002d80354440e42040e00400c00c0120380d40d40d4014404800c94100f02c02880c1541c809901d503441041805010390303011807070716400300d20920b0100714507009500482d60742c42220150003500040106015201218404485c051401441d052049980313903403503c40a8000d4842c01c0e40850000c0800b00305008420b203029603064001400c114203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 85399299 1250 85398049 85398097
    0x616030e1005030f09070503070302131409030403030206060d0206180102071502010c03060f0303050306060708160309050f09010e19020f1303021e01020703140f0106090c0f080417 79
    0x1141246110790400b050b8040f0420a40002240803654007004000061211a1601001c203807242c0035800041d0050007201d440c043c00200350b40045512040305a44080245027890995807240c104d4042200140520070114a01c2d107003081034040400d40040104c0c0c80d060502c03c04c2d00c2040d12742d0844605501586c0000602400503680d518029501c940003c41e509100a200504640c1d00b90045000c800b114032080c004603900c5019640d00800695559a13254030900b4501c1260048616660400005c004024101a8094419001c07184251103c041c440400b00401c50f81100074007580b0000507000d00040c07031848101450516802c55030100610b842c4401c001e104055210301c583e040030050b00d010820441c00d2065403c045030680f9135510806903880c0b40000e40300c04051001401000300700c2e00e6010240018030035055080041f0307000f0086541d490700d841f0003500d515651200450032115004094a0042015610603540002064040c103550108000b2640060b80551000d03940b0701c580001c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 85400549 1250 85399299 85399309
    0x51801210203060a050d0c03080a09150201060e0f04050604060c05070605090d090501020f15040602040e09010b15040b12130f0b0f0c2703011806020c0d030b0616030e 73
    0x8094a00c0300000d40e99280c40028400d000e00c080e400302c2d005442499140d00440e40924102082c0ca0740184000d030345a00c0a54100d0300214507402120046804c1540f0850081c0c05600c158211000000480000d546644c01c8450803038045070042c207650008000036001030004d510004000c1400d09182d400c140c040d4458404403201210350b40080c3e0301445e5440c1d01140c0050100b8003d1030240300501c010892102502d4031a21401000d010701e2401c2000320341000466010f48015001c40140422180f91016603180a40545600540908240d1600001da0b01d00001198240d5082c20000e6117000d04d00c241840b881d4000030112203080400c03921500000d612000c9103080d8134010a0080301904003401649504040070303242c0c2003803c1c81000f81c40540300c41612101403503808440d0031240188401e000c130780500107003248150030340306100030881007080d11382c050550100318004903503200f421228150215513150002a07400841445228100c2842c2c5244000c1944a8a0194244810280864 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 85401799 1250 85400549 85400597
    0x306060e01050d0b0112020706151a04060e13050a02030a05010605040b070803040609120503010812090901030f020d150218090403091a0c0102070f1203140a0e0c0901080a050f0d051801 81
    0x22103c503283c441c0800300200601008001d841040680700700f407101001c0bc400303076106600c103800130300a2600e00c0640f542c0c1c074040a0482c211408034244407070b1402c03140300002580100c5514008514100011035403600c0f450684060322400901c803894000640c4490b000c41d000140110b605a4842c170300000014071f00060300d1082c0325203031074160f1254101540c0500300392040c1865032603600f050003100d180e41e840010741c5044941080100c0c49902850011580381c000c09000070f4510704150700f16101d00007040d8000d21092004290004036100b0113404c00035490340036280503001a088410922006480c50300ca050320b1080d10000600d04825080e101d420390308501d05c190f03002210744125905000c0c51444034100c41d80c81d0718081040d000e00c0500314032007480103840070889035501d61500044880801c250300f620388c00100480d009680d03d0381c0b01d950741e005508045500307008000000f1a01540040d0b030005409403500c0c0d407030424035441c8035224500e0424407031340d0400526030110841184202500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 85403049 1250 85401799 85401803
    0x7050304031406010605070507060f02031b060106020d020f0d0503130f03020c0108010902031b0a0c020d050303010503010c050c0a021905090709032906040b0a15020601060306060e01050d0b01120207 87
    0x81d40c0711055102c082410f01405905c01d20900a081240303100141c40401c80000351005820407009040782800200e2560240b19940a80c214400ca040080b0010008500d030487d141942151411000142d0403a2104160020159964005400000802e0089019660160305440480072041464961900c0d4400e81c100c240c002da04080d48602c030070751744200b060f0701510a2510030740c51810000c20303030926449040301500d4860030214030603501602c20000e04010540047c202c5d0a110031a0401c141c4903407080c425988298a0a5002401c450081c0140c0303101105070745c0a0001d1000c50340034810700d01d6140020302d00b01c651010001c03a9079592000080c0c01510075030b071441005411440e25203602c280c4000790041c20160704203603808402414810650050b0141e8011952107821004180d603210a0740110750840008041d4556156000504504850080d581484419604e1409079242c160074134009000440810070394000c0840c0e9003181d00c103042c041c94859a10301054070501c003260014041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 85404299 1250 85403049 85403063
    0x301151a160c080106060509030d0c02010311040b030f07170114190605070c0503030f0d0e190503070b0f01030b040303150b0c0304030203151e07020102070b0a050105010f0806010f140705030403 85
    0x414810301d1402d02c01e40006e02014240241780c2203110f0002991400460109010400c000301c40b01c0031640309809c03c20b07004880890322525591102950980c54000725001000c12030900000380b002c62040301c0c03840b000b44143c22001e20a03401c0c071080307800d2089505001d54001e000b00050480d2808101704400040c10f00340d03940b03501c0c1d0540e4600403010f1851035100768400d60092040034030f40d110324800c0398106d032065200001c200c0392201400c0d040400c5c1c101401d400c0048003040b2801e101000c801410443e22400c0310081613910414840c201c0042804064400e428642c00900064081d50100d05941c030141e00ca0307010300b40d40d007880b0119584805240e8486070004142081141000c01a50b0b110b0281420441103034a40560443d16001c036141c0502044c00c0140e000c610b07801e000b075040b0f9110b15000110346c0c016213800070540d00903200a02c01c19002a030000c40800d00c09205241182c050b0105030f60f038440c1c00500c2c01c030444261103034800300c5807070000402001e000140301b080104003c0d885260 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 85405549 1250 85404299 85404323
    0x10e06240a03050114010f051c18050718060303090308070615140301140f0408071407030b0f0702030918060319050109030306050d0c051504051315050301151a16 71
    0x852441501d4007085820306024147c040d0342138803038006060310212050030801c69015000301c0700c40b0340503100070130740b000c1060180142c140a1140c0421a101a513503842102c0541e2902411014101d030712500c0b000c2c0000300c05190520011b0f21a5000301400c81c0110000308a065030710341d10381c041e08285e07403007804408a2941c1c00d00141c10203002e041388003240310503104141d1a20040c04405080c004000420401001070741800700021044540200340c00b00049924198580c980702d528081d09072403604100440b800083d481c0d81c400811a84801800350400c1c1a508520501c0c2070102070103448164103000714000090b4403000407204c0d030081c0e4001d40002c2402041800c001e0100c0d42d40c0d8000034058440b07401f4550218480c07807601000c0300c105480240c0c0e10029524501b545d4081d81c0c206580c8407c415907251080b80090f040410049283d030100f01d58181d035401054203c0d840c00800e0221606150070411070300240411080482c210341c080d2a2400040512800300d4440d048811a07800c20914 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 85406799 1250 85405549 85405559
    0x619030b0405071b0b09120307050403020103140103050d0804141506040b10230d0507020d030b03011806020304060906020a05040e0610050301090203071101110403050c0603010e06240a030501 84
    0x1008503a003000c814201181d1813a2403c0904505000300b007000340800149802051600d001008103441c103503481c1d1551038507070500d0040105554801d10083e40001d0078070701d40001c119041031059040b240c4c803000420580c40c40080c1520841001803007078a50a0340c03a6204042004244000044031003070604811152403d5010001140c00c2211190f0240c3c017800300d614500c0d600700080f4844442c0e00a0107945064681015180d1441205282109181041c00b481511030300082c80304e59080e0f140d1000d200990904051501301c1350041c0001384a80d8498408e000402c3c4280d00540c0c0142c055803001c594803a407910b480e0280e80c0424036400c005080010b080000005400b0004e410510448000e01c10305202c0800030300307901042c012030340480e03800004280000d029010420510030688024442460401c91ba46160340013032005803040c0c00703a0020940c1c0d03450080b0880f4141e0700c0010f120000c580b10300c0e0500203007084003803002100c0025401059030368141b04000c1c05905005540100d0158144 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 85408049 1250 85406799 85406801
    0x5090109060f09020f060c0102090409030c02120c1005090f04060b030105120f0606130b030708100e010603150905100e010507090501020105040203060f1e0a06080708150f060619030b04 81
    0x70240b4100b0b5280c850040016980e0801c018071104003206e165032142e0200c59080d00920078103118a40c0f1600d01613116040640001030281100d00031113214116804921f041c039101c4218150184d071140c01180c000e001c84c1c0c05080648a09200504901a000480301c003060895940d904460030f2132802000400080c54100810003150400340c2c00350401c9041c41951135916080900319034031519900c010b501503106260301000940b2070040c12504010f81d5891000d031140800405203000b10f0500880c04800b40050069404032607202c0b0707140015152015050300105450101103403d40070f100004410070f4154080c001d0008442f000006207400d040b03034040e10708450342e403100f415641480200405664003151051344150114070800f11940c6003d240e2620407143c00c1c4120490301c00d0003d00c00e800d6007d502601c1520303140d000300d0b103600f5241c150075a500c41800c0c001002c07440200c00042c0150101c0c040982d005803018180d0b44c01d0071a841400e00030a43c0e580e4840700025519003c8a0315450a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 85409299 1250 85408049 85408061
    0x100c06061410050a05030406050a09200301051501080105060d060816060807030b01081807081029031b03120c01020306040c0e03030a0c110307080a21090905060a090509010906 77
    0x10b904003d49001d24004001d049400020310140090b66918001202c600c6260000035041d41e00452607400e91201c03031841c4c2015002500514025840e040002c0c0500c0010754182c4103d1f40b058507106c03c00e81c6828204003090303100e03001c00b24506443d0000047d50090811881c0c5c052410b0441441752581441d01c01000300d60001d00d44020182400100b80c11a40c001d0b60494000f40701d42407400a0510000b07445143c00c840340e002e4180c2d0b100342d200b80000010749a101c00780d41200c244a12604c84041a1a00b88400c140c0d40c00d16452b030000c3c01e40c000c1a82c101c04298180c40c0018080c0c4205c4c6001460f00b003802c1e003005400d000f00d6500001007205a140500c100100e00e2200c0c10200703115801180071940c2ca002d84604403052160a1016405000e11050034400452004080720512034560b00e00fa40c6135184a542200c03070010103d1440307113211b40d54942035582940c42d9100000c0d585441d43e03031400b03000068055500300940d001e0124a5040c9401000d21070107001001180120492a0000403500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 85410549 1250 85409299 85409329
    0x40b09040312050a110406110c0333041211010e0706090306050708010303020d0518120f070b090d120507020a030305040501090506250212030c0d030f02070b06100c060614 75
    0x1c071702600d0f03040b0f146044040e24241c1c0e03011302d8690850400054101d10380340182c80155071512a90302c12421240d1610b402d034441d8281d6528890064950452000c1e61a80036100100340d10b40341c64408500740d01c9060319070202e0307848100105091004291980c20003883d0b4020400040282a003030003070242902403290130600342e1034040115032640d10002d40350211031001404200300020702e5141204911019501441c1c010039465040c4018518995218000c4046000301e005599000803505413000c01e54119480183c101810031009999800484800e01c42c0e0405007e020702880001d601c1d07480d0721502547c82511001c2d07846003010b0014090010980c0020702c00c202c20070944424006250503c1144510394801c5000314416100141d20a14481c100e20352030310002c54207241d6014001031134002c61050361410010112000141400c0c0c0c0305109000c2e06a400c07000104196042140050407901c01c5031811a1000495a50320000da07900742c0d2210603500d02003860305a55242410000181704 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 85411799 1250 85410549 85410551
    0x2030601091e05130608031b15011a031003050115030302010e07050d0b060102010b12030702040f0509062715010e06030102190e040f021c0605040e030f030402040b09040312050a 78
    0x844030b000140401ca1407030140303500405000d41e00c2201c101041d0443d001074140802900e4071054982a042401e1050030400a868400d2040c004552584a0320081c1a107800c2000e40b24880304410611030340c1c2e48090100d0034180c403404000804140e081c82407103000c45072003800d46411441e42c00c0c004d094405001d01000700d50000c1d081001640d90342c00242c011907034000407100080d035034040107030b004140102007282c20103004503000f800c1c1000071001f84001e038400c0b20b0400408090100101c11610f045440120715444000840c044110301c96284080d1086003100c0075004242e4104203052101c468001050945490014000807161652032503110100350021410920700700300540c20a0010101c45080c0b0a00c46811040b40e180e90300940b00200c0c81907001c1d550360000c0714401030f40e0b0050109050b00e8604d060408100392900d0b01407081240c410000450400007090080e640031b51001c0c20417a0f1103a40e5054101c06601c8000c09030740701c1d9000e51540b80301c81181d1080301c01629801000d8891031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 85413049 1250 85411799 85411829
    0x3092206060f0c0b100e07080414010606050403030c050a080c0a0203010b030c061e0f0a050c0f0a02010206010902130e0c07021c0f110d0b090105070207060212090f0307090f0203060109 81
    0x3560303010310110f00160b0880c10403031481c2c48180c20302c8038503040c41d00302e0030791844031208001245400901503402a0700c02c041e003083d42c020004281e801c8420354018000013174030800040000c244500c404690840c004d030151b13010844a66107440c9540c2c0301e01c00c1140300390007030120f402c154542031144503881e18040c1d014081d0750a12500054083c810f55400d02000b81c560251120764018a43c1a116020800c03a0000d990306954880a01590480f41204040344901b04080242c8040421030008a80d07041e0024000ea034201101400a03400802c2e000541c040c20100002e1a070840c8001d0314010500d00444039039031070480c018010031031104035243e001c14284015180c00a11104800340c07885403c8200310703c507080407100080d040354680c08042d05400c035900c1449010f00781944000d01410071038080301c076880c2d69440c1c207984800320f20048102e046c0d0140480034803418546120120020010140d0744a241c81d5000031046809251101c4401507010041042d81d5801080c180b020300109a120452 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 85414299 1250 85413049 85413077
    0x703140c01050415180c03080c070e1302040c0509010c060e010b0a1712070809010806040f0c03050601180803040b07060b09040503030703150e040f0302031911010f05010501050d020c0309220606 85
    0x9185c5880011312340400050652030401007400203001510349800e1005443c182032500c010585240c0600303038415450400b5030300103280a07608840843c401038648148410750360f200d01004001940410340255203410750303191a41d4824040e40041d000c410009151040580440b0f80340c075422140c2c0c000300d0070b010440c8402007400344040c0d8007903560074038003400c8030750743c60021a0140c0082041200c1250070003070000401c40e0503030443c1340320b001c080e07a0f0020041410718500580094521400c2e1540e00708200c14001d4030381070002040e0ba28007410010039042030390300104003007400844013030b1255080030083c0010340c1d41c1070088201400c160710f201400b090a003104208606c10240008000381c20244000c0c2c1058020302c16036162102032030780c02d588030072480405841c010000c0140290303946440907800341405944100d5040e1a01a5903917424000800405c1e40254041c6d207004166100c1801004255554190320a03d010301000c1d0007104c146000320500e00340c071442d81001090045039900c07041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 85415549 1250 85414299 85414313
    0x5071805160905010219050a0c090218040b0a091d070b0a180315020a110f0a15090b06060c0102040801020414100206040206030a02070f02130903020f0708030703140c0105041518 78
    0x207850002c80340c00840e1891f10f0702d1843c1a941a0008091216003100000e954040d40d0160000c01e980a6216960786036080401040340e013400304542c0d200c8221001030140050a9000ca180501c1c00f10000c000003403104040c6203040003540c0710783c41082000408000c0a0350003900000c402c011883d00003451401c50390341420040d4230310313001c0d00d44030350100d048841c2c0740c414206079248480503401d490640c519244441d80310340c0e2200094840081c06503608100980d00d00c030716814990007546162094444008220513035000c00720a50700b0350740074403000c203410f60b00303100074070040482400d000c5150341054144189000c141c280001035410403403c00003d0b0b10f8071702c201c1e0380c4801d03900d800507a0740c915858010300c050782c5d2108c040d4000c1c6000f40e014a05105681c4400301d4980030350212101044014580c65441695000b031b10034a80081c8603441c0020f012b03d0032100c000401001c024100400141c3c0a42110021181500c1e0710104400581d120700040c80381510350345289850147d980c3c202e4031461 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 85416799 1250 85415549 85415563
    0x7051008060d020d0c0501020c0603090709110c0106080d1202032815080c0103110406020d0806010504030623100605090f0d0c090207061104030308070804050718051609050102 77
    0x60144041240080c0307a41e42d03920703000410340342e0082c0001154011803c0469024141e40a45400351044803821180c600d4140d094a00c2201c0210040c82e03441e040240302c4015080e1200920303501041030040001104083c0030304030107459948010a1603e800582c0100300c04000c04003000c081d80304000f4000c001c0882d01a114018403001c055520001401c05080300400c3d03d00102c0070542580320f40032030204000f1405400600c800d0380d044c0501c02c61000000042d100340e01c40c100150344240c034441c2d1800d000d680040c0d400030050400340d0406540e07480ba00140d48181b40307090000003254481201000754144006e4105852001340c6184906204000e46180324400207240b00d0803441d10351603090740d41c03c100001480c1d409400e1030382441d915411070010350400d8400b241c4481c1800b0303803031311003040030410745049170382540e00c54100e40c40b0010251542d000c098400d44980c0550800450081d035054114182d019070840e001130285001240503841d150500341040401000c10b070204a00c0e0313800a548 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 85418049 1250 85416799 85416829
    0xc050306191203031409030412060b01090b03040f02011121070c080f1b0f010507112b1a09030f0f090a140f10082703030f0601110705 59
    0x142400c98060520074400080742d00c60034890700c11205140c20103915801c402c03c8001c110612646507240c2c90925600c84c025070040340c9902081c540850041085900168909001810a050059251b1418076100d84c011501a1280c0143c100184110750707000749178140000070000907068500a545850911512142c80c040c1102c501140d9041030007a0360814800610b090811281d400110254854542200ca200348a00766100d50101d90a801d000a0061020300d05944562070500b03035990f080d198001c150038440d089900b0075040810703600e0390795510388459441640f40d0980309440c6041083c1e0311010100184040401043c400701c01800000d85040740e0580922a0715652610604246c03402108503165021070415000501c1201d07001c080301034050241c42d610f5800c2641010300c403100446414980c0080d8826002a00b41002174200031065148003034021a00340180d242185142c1007070314100c800400d0602844000d6070403800a0f501d41820b0f0002d00340140c64080003912600010100f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 85419299 1250 85418049 85418059
    0x60108060a1403010b04020a21020c0c06030a15030b060a0902040e010506071a0f01030320060c0a03110315181e0a06080609010914070308040504020f040f0e07080a0c050306 76
    0xd0180c82d55429080082c200f18082d0085466140c4084001c2541d1500c030040082100089150b20241086000f00d03140c0c1d03100c0782e00a00320180c41c0341c2400708270352000b09031905a9684801450303005456000c0640103500904038000c103402c0c004100308880d55140d02c19504580304100c208001013144001504456040700c100c1c0c0c950980341442c1404200d51014002c500000b1b034104134603820010081810307640070b60b6854592445003142010070314011110003000e58020310020317000c08480c7c0010481d5000c903103400308001548142e1700d10241c05c1941d5424041c03104014140382d0b402e045000d64004041d40503000d00600300103900c140c11400d03000c10360f41c1101c5c1d41000240954a01c2d04403500400b400d5017161030078a490016035000b00011141242c00e560070a05110000703100083c05070a690700f20744d02d28a0580380808120007580001c6071902a00c006020004424549440701002414110f0b4240748515188100811804000f819007410301e00e0070b01e401c4440380d880310659910680c1a29 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 85420549 1250 85419299 85419329
    0x31209091303030e0a030203070501050a0c0816110706120c020106060c1103161419050a0b030907050a030503070b090703030c021306030501020a11070510020303071404050a03110306060108060a 85
    0x24210044e0820803c0086503100700803551042541c000010003940780290020011600c441e6040c0d0b003900d51810f10701c40010310b41c0c1c001c83c485c0600c40441090144050070221007040c0c0c0080142d0510b14594050408a40b451010384242c002900038070504100d28402008094140030005d07051442c287c1c000ba200d15000140d504241d102001240216402003d0130819203035140400d01070454a00702c40c0307002d00e80c1d0700c0182002c901d42c5c2002200ba114002c00c14428281417484a0240c0d400003440f03804144030300c600002d80d6448030b401d40303005507000d0009107541d4010b0b4244000c0409010308125441e611002c010004242c2c003014407810a617044a608030200d603003000c1c40c40500b0068102034403c0d407002550b80c015681101d400e62030b01449400b520000c5645004118119880d101c1c6000545c0040000812007803080c000c40000044c00036525060039201c2e00840c0d4102c020750011251740e10080301009a07461b040000c0c40e44180c0901c0c00b1740103440d0410100b403d41880c0d01c15041d410702581 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 85421799 1250 85420549 85420553
    0xb1e0c0313090501031505090c010c0c0911041a040f03080901050c060c041e0503100b0a1502060f130c0603050a020702150d06060503040309060e0111010504060b0312090913 76
    0x4400c0722009a280001180c0e101e07216800000140020710089811098414261004000501a880c0300d610083d01a0885100d8040150351141070241c084501c85207802c4c1c08107144c80c16108403a4070016205144d501e4034105691018441800c000780561288288000c0101c02c5040c1c040e00c0550380e001508588800e62180140e83e54060051240b1080c000c0004210351814030308007400442c2c07410500c0d10740c02d8489003041004c2680302e014146d01078100c0c483d070010158080d08400b02c0e1983c0a00894841540c8a8041201003041005200107030465000d0040bc3c1c00a42c10f07075138221a850f00d84600b100041c0e90740c096100b1143c49060245500c5a0000d0079403051581034444035500605440b071144000407850300d40360301c1500071020f00e901c1c1c0b405c0070034880d00c0307102901c0c411585519810b40403070030200181c85003031036030040034100045409a03114850080c01402d002d00c0c4075607c003141c00501101010700f4800c03044418610a01c05001c1d043c86552581d8040e50042000703004c0441c402094 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 85423049 1250 85421799 85421803
    0x2007031509080a0e0a14030606060702060f0a020d0306090b0d0f0512070510060602060708040803060d0212030c012a050d02070206130801050601090308070201111005090706090b1e0c 80
    0x903040070b820b050000c903041c030441c1c0e00115580896042110000600d9403103038141d0103840b0340c42d02d54580542c8003e001a100b03080810090070480e000038000c0c5d0410000d40d0b0f1115483c0d202d803010380300607004882c190100540500614014003101503040c04a40b0740335000c10b0003a0500c10001d4040b28403011000c0034090709000383d07180f4102085149541e14420304000b503513090b40e942c1d964102813a01c0c4001031200d00c007240c001d000c0c41e40e40d50740704610f86071900c8948064002a00c11a402488040202c0050b602c00c100c00300c500d01c164000e16210f6036001000360031a465190103200309106c1000c02807580c8408051031a1480c014100700340ca80c03d0410040009028181d0000d402040c00a00f0000360744804038600103c03840040203000c5540c0b00030044a00140c1440010a603000c1805481c00640c01070b070508580242c050200c804800c000c0d0b802105803081038821560a800c038640c184002c80d0311801c40f401804510301c20504e4443c05800030715200510070300c24810900003080c160112001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 85424299 1250 85423049 85423061
    0x30b01030f15030308010816121502031005030c030d120207050106080703060203040b090313030f0201050904060311030d0c020d02040b030709020711040501091a01030518030d020a20070315 83
    0x505400c020a1102c286680c03581c01c000c0c041138010035144000021100c2000078002d280070645200469038514065005c4005408540202c0d50070314100070040704110544003840c414417051120560a074a80300034181007400b81e00c486130180d00710510400d20513801c541c210960240070040160f5603481405c00d913004050f0782d000080305028840380041400442e4000d14016802405408a1603c0c1d5440c2c0f950780e0700c0356140400c82051413981c108003064640d020344104c00d0041c1040d51a2446003000242114450381048403000079464000c01c00b42010404807060a0a908140b11005119000100748101b001070091003240c07030700350074031030f94409101290051000325020b54071800545040b03410010041442d50082785800d0000615241500840414465001c41d010321404030343c00440107001c00401e1880c008021403002004008200028100384400c60001600ca84c84804000c2070000c01942c04202c9240820032441030780d030003050718400c0304d610205010713440358034103100405024 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 85425549 1250 85424299 85424321
    0x3200d051c090602300412090e0709060e03030405010504050d030c02120d0206060603160f020102130f03020a060311161a04030c020108010905070219110904030513051c03030b0103 79
    0x82031445030001c21403150003034801d01e03030365170580b014180b0028100d00d10040480c1c2c109a5107240b100c0440e000ca405012031400000301464490f40c1251148200390b20007505032509000101449400c214240e03000c8419080c10707608401842c43c203403405000901c1802a805224420103804942030f0806000c1c0c0c007440c5800380d01403d89074800c0d0814440d107071100a01088400580500400100545080b80c101e83c440c0100c480032070104000018205c44205000f1140c1c8207540d801c025aa184010140e001001040d1502c1c00031451400c41c0305002d8500c4c80790f408423003810f0401d0340245114240b401540c2c80c840030030201c400d0840701420100050011510781c007200c00304500038441032581c003124110606000b80c0750c41011340d0341c400900f01100d00494032800180c01401462090401c3d00c0984403903c1c0c000c10841c0711701d0402c00300082625005a508602003003000512240010b45c1e80b5200e030080c101103e01503c8494002d226001c408960040101019558141c440c0e650f8001e80c13109100c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 85426799 1250 85425549 85425551
    0x605010e0103050d020c10030504050a0209101409011401080705070206030109052e050f01140a020c130c0c0609080c060405011d1b060a050403050102030903040303200d051c 76
    0x56520035a80001010030701081da00c42c0102d9000c00c4c08940001144860324030054041d01421801210481c02042d014000b1500b40c0911803042001da50b51520150182240c2000d010520346054604c12b540c0021015242c040c5241000401c4803c04001e88c487d807603003007802c0c05013a940c0d54050840322846401c0009500c840080004503d900382980428480e000103615108000c0036134040170000001c4400f002c3c8444d010800610403420070240c0720141d0300b01810a0300d40005103d411144581001101c4030045c5d020481030b1056242003c0c00b02c164681c030800070042d044031f010008000c2606000040c041c1c0351210160801c0155050480300c40740701500544106081071700e0207501903c1a1000100340c2c400881036039908450206100c12606403511924019500020510440d9005480c2a02c10b20006100020100741c0a0004520550421000e103540c1c13400c5140140500340b503200f100f61101d1900901c408030f00400107194081c0c11060901946903140c80815403451000441000425 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 85428049 1250 85426799 85426801
    0x2062e08070b0901080c1e0a022103040c050118140f180708010506040506030f0901090807060603030807110c040b030313060c02091e0103060e031b0a0302010501081b010e030a0605 79
    0x210702c4540034011005003603851071000e490352200403445010300e01140c28406402072000d10004502e400400440c600ba0060702c1c560301c0390a580b4443c02407403400c101079444002042208000103800d60b50090082403e20030500e5248052600204001d40101c17111031001004c595080d54684410182da480c00901100c1111540c11114401500070b50364440400c6031400080740500c0c00205a82c10b40c0e001402607810340e0b4440700c1490200d0406044250107560751706501d804111440000d011150098401007440c52035864006d200c510000c16113020008104c0c95280e01d00400b080c51581c03c0340440e404101288500006402c40c460702c2d13042074920804000005009401107c0c082c85030740200da843c2d54583c1c5a081d02050030030076010304c00c0c142440c00c1c010f200080c81a404001c0e16184141120306040e0007101000c0d1101c25203e0603681540715030307540f4003050b038240102d038090001e0074068494044803290009145480f103540c51705101c041e14101c80940c80c20841c034005180c02000910103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 85429299 1250 85428049 85428059
    0xc10110d05101a07060b04020c0307060f0216050607080106030207020109150207050301150611010b01050412030507061103060906031506060d0e06131a09070320090403081602062e0807 81
    0x1413a4400b00080b149182041442c6050745010300c01da03580c200c448405035180900d5903480340010242510303810509a800e01c641241100c045400102e071a00c10001080107081c411005442d00e001607000c0801c05004124100c0141d030b0048031030044410341001c00c0340d440381082080c0c0c10284242c21054140d840e00580b43d44660140308140122000364985800321151484c0c45801d0b40c010744c51050200b081080200020344459080c9104036001c0d141c50340c109070059403414152803294840490350761303000c01481540d290283c003143e0008070807002070003110a040180000f602c401045944a03d10215450041401d80c0c3c0000301241e425070265859440e105100006c40e01025506803200c10803010401ca210350280f023014000c2505900901d08985160394207000c0344142c1341c0d0105403c8401070401303255115100c4403400b8601c00d0f10f03450308515211010040007400c02d040d07401103502190900c050141ea403400303142c5940e50340c14002607003107000700c5800a01c21a036114502c107120340c2d030000030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 85430549 1250 85429299 85429349
    0x4021c111c0b0f09070306060609030c09090203070603020f0c191208010320060c0102131703090f06030402210a150524130c050c10110d0510 62
    0x14480d6000c4404505801c8401c0d10034000d0720440800410841c44900800c481940c40b180d00703980003203440100d40090751259520b80c151040da0388042d012030050641882000510782281003d8054818100030f0449a0740000fa943c450741c1c850f84082c581d000680c0d1205084000031503092820640440704401164041c04040320940e16056641020601d00300000c6407240209034100c0c0e4102c5c3c1001031680102402148030010301008070b500600800a0008000b4280058440c002c1c1c0b03507900c80b07030080ca0000040c000c41032a80c06d07448540c001304201c4840755195041c40d20111015582552030b42e95504c08a48100300c4c3c0e602d0002c16825411410811020000e250640d4500c03803800041501c102e60300d0741058500590f034414001e1114504481b000003909a4060304031401000060410f031000e00c0c0e90100d071100603803c00050310010f100c4108030f104100d0f00c0a0008008002c0010340c0c2c0b0300074003000c123019842440f041e0b2520f83c00802d5242c0346409640d4050135685161803224014410340301 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 85431655 1106 85430549 85430573
    0x50705041a090d03051305030c13020315120d020d02070e01060806041d070f05060a08040b09010207020a0b1209060c03060105071a0702010606120b061204021c 70
    0x504580d880c8801c081c8014001c0d05c49555440740e2028206030f03840035410071806503100344c0310741d0b0642d20f481d2480c1540702d00380300c0c1c01612034a400c0464008028141d8803540d00200c0014220308980d4041030012408003287c00712000c4014003603007680c54000b07d2242a005ca8402c4004110307ca0003001101d91080e002400012140808682d05a0382c00420000c4031041d8001c10051010540c411001c8015100868855080020034800201034040040c03005000ce0402c4022901a10094060707503040c03a4020300902080e0f0301e0302c1d0190840c0d004041e110180030700c0140458003407040860b41500599940441602c1d682d592401036400383e00c1100221202c007056004d010440130040b0041e0b003c0c100a81c00460040d00d0214021701800120603580c03c2c191600b110442c0565403a02101c0070346849201c400a160342e0750000842e02c0c2405c404080150300071901070001c05c80158102 = true := by decide +kernel

theorem cover : BRFrame.Cov 85251799 85431655 := by
  have h0 := BRFrame.cov_init 85251799
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85251799 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 85251799 ≤ n) (h2 : n < 85431655) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
