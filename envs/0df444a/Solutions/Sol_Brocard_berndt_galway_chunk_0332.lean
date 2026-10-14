-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0332
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:15:51.520319+00:00
-- url     : https://prove2.me/submissions/1363f617-816b-44af-bdd8-0521da3c6767

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 59532377 ≤ n < 59712233 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 59533627 1250 59532377 59532383
    0x20d081909030504031112030d0c03020906040617070503070203030a05070302070605010605030109270b0712050c030612010b0a090209010507060f0b04060614031f05091023010516 79
    0x1004034101800000e511072480c6051080e1100d41e2a54590f051480c1d00b01c2d65240b455019041c04200f07000c8034803001c401c0f14030a04041100144100c00e107002140240210710015822007800940407800d160030a0b40811f010080c3e0515510360f85e0380242c216818003060300c040d80076a1050000c501d40382d10a130002a4000c3c0705150040c00c0c01d074542c83e01000c3d0780c82a07010101050303002005101d1035036980941907211108015500c5c0c0303000302c90510300e40a018010094200700551000c5403540c5c1c85040040c402c50042401400705041c0142d18642c1c0d42e105480d018498514204914a003c006001d4042d0400d8001c29003040b0920f0310400304007075400035070000d041040030010000050b40303500c52a00740620b52000020020000c8003808112000e9030840700c103010748144d004201d001c0d020101c940c0141d00e0100030200313410540380c0011101e02c40d0040c9a000c2c80c02c404110701001d00c070544000301d46200f140c036034414502542e420200306030445424001a4100558540e006121a410180070f00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 59534877 1250 59533627 59533651
    0x60a090510120504031107060e0303040306110f030a0515100c0b19020c030403060b09061e030111070503030601091707050415050d0c0603050603010c0903020f03010603060218010201050c0406020d08 87
    0x50b56142241c1220012034040f00450455117404880b05800c000301c0c0003a200600f896940c031100341002a070b5901a511000300105c0d143c4110342452240c000646082200f41480d42c2e45078103040c8501e4003d07003000c42d001402ca01106000100d14030345007c0c8a11035a141d0307104c0004601e0585c42d2110300010044c810140342a080b43d142c90081c0040c4001c094442d488030107551503d0851502005440b007031400c1911032842c00c1c0c01c3c84166034910004181800c8001359075055414000b0120b070140141c40a02c1e01d00301e9010400d07400703001b4040020361141e00242d07038103076206840359481c04041d000d0002503c1240d00c0759a0a0120b800c282e8410424030303070980b110502d11030751200011454400715200300c2e00003c0c101401c010041d0940a4240c0001044000b400100c07040704000305012424400648620030301c1d840c0341400d0304c00798000d00186800030300540d900c905004541810482c541d002d24019880d00c80083c0135180213200b9201921101ea0152481842e0a00c00701c4800c0d07006061400050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 59536127 1250 59534877 59534897
    0x5010b041518080a0309080601060806060a031509020a11010603110103020a0203070c080703030206010905190c0c060c0518040207080304120921110108090703150603020d140c060a090510 82
    0x606414501e4020941c0c24000d000704c2106183c006c005030119070051030a50300000060001541003402107600800c107403541626103100348c2c000c03070142034500e801c0d001c61419204003280c041d40d03540003081c000306c081e00c403480351820041c81d2508039000c501c03001e01f100c85401500e0490350306c260020210070305103104503030a110854039401c4610000b5888040c5a0788031034402c004040d018041140102a441c0082180386400c920226900c2012800300200310f82d50100307016803038010801d118825400581c100b1034012214000f4015030300203104451504050211035a2a01e40340c0200c46421f544050b141e0b00395161660f451075604002c2d00684184003080340c0100d8000c20744031060000c0c00b40402005044007060034150f540500d401e800e64108815041080010040007030000d04499000780c01106e40080140d03c54000c03c41074200960080000c1184c2c000c0c020f61480740282d10790420141c5082881ca41c0030411588102c00102d0089401840304201c145008004a81c90f5030942c1003110303000f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 59537377 1250 59536127 59536157
    0x1031109040e03030a1118060f0d020307080601110d0909020d0b12030d180302060610050c0d05130603020a0c110a090c020a050609070b04031e0c08030406021005010b0415 75
    0x750328408209030b01d070341c008005c1160402c40ea000e545000d641040c81759240440c0015040706503840c1c03500c0386005400c0040d800e098890030700219004184110f500710340764248440c000b054800b00ba2100c03400a58114a050f440741c10100e8820000c040c240c55038071140d4901070658000c0c4d00400385c0c1c0044103548002d4181a130301d45d8070441c80c0c1102c1c10070141d5500c403400d0080d8070440b02c60024940000303c2c068140030009800280168000c0c1044808807103d901858040720503101e1480036065078090082d5402680b5003103c05030035588002c10403003140985810084041b801440703101c40c00220700c404403401140d0b01c0e0040500485021740340c01c06168950703400e9010b50310460400070059001d0051501840f109020aa800c9a41700d400741150904d0850200b65501403404040c07c0d2840e142c62019240c044084c004011607400100e003000c1c107980308000c0381c130303034105108941c00342c0903800a440c0c41203c2441401c1c1604c1c400390b00341d410942410311980c1c080204003036000502003a8440c0c41d2407 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 59538627 1250 59537377 59537381
    0xc0f080118051b040f18110d050a06080d1101110903341205010c0815040216021503011d07090b0901021014060a0501020f0d030506031e01020d05060d110103110904 72
    0x34000e015810315840346081c200511000c16107131039041b807a1502c448000710200d10800c995080324896401300d510303143c00400360000c00741e642c4600703c50305c140e50001030600c1d0441800d2480200e072130f000300700902c81d84c000741207980709500c810f0741d141d008401141d070004d026510041811103803110001c49034200b54091040b03244242c0110306161082078006c402c0ac0424000c041c04000031780781c5903410b13042801c0020f10301d007001c11a040c820354001c1003048000c01210558502c0c42d4000307169065401e403031403920b81164401c1c00780944820103880000c100914100e0014014403255660300b0b251803905072410b005401140005045003e500c10203032a059150003140c80c00c80e100000d01009080003001c00007c3c3d220795000e10706541001c0074040040c007002c42c80005401c5142404199542c8441c0000c1c20002c12040c0c0d001241b21035103201c4502441503026001007035120782e04201c40e4072340a08001c80c5814200004002444d14000018694403941220303c059851070441c41c204494000010b003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 59539877 1250 59538627 59538629
    0xd03050c16090c031b1b02040203010b12011502030a1d0904120801120f120504150203040305070f03051b0109080307030215070905060304030503060607020a03060c0f080118051b04 79
    0x1400440598051248a0aa20034010180b03264182002441c40e007910300c3d81c041032a6101790051085c40c1c1c03000c50b090711040390101c0e0480d500410456980da1105907540d50b54100014007003190400f0000440d026490036040858001181c0055040080780c02007100c96582d0300c8910341c004404aa40d518458441b02d65047c0903620446803100c00c1d190500004000820503840341a12a101045400214503a24541200140c2100340c0146100507a6015215803203154008510090034403080d242d100e034080064003c0d40c1c410401e441d01030f99034030b07040c4251880340d010180c51900f118507901c0745959000c8000741c1c24101030401e4551150f60b607500b170b030554000030340030f60140e004452440d0340c5012960119501190504100410a04080109801e808018070040a00c07800001282c110390314001941c5800703600a040d64415510317450210f020b8910300200e9804945900d401040711801451058140c980c2c240c070503c02c1c90b1100350144050b100150011103840103200415104104400042c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 59541127 1250 59539877 59539903
    0x30f1f0803031602010614010513120c030c060306030803150a03172503090314010213031406060405092104050a030303061809080403240509060618040209060d03050c 73
    0x1520703441c1c900d2901c10843c900c03403482011a49001001c0c4680c0c40500c0213505021402c0c82c05039140c00c010701766429510403503000442849501100d030b004004050100c03c1c1900d20407092140d4003580c8020540544100d80002448040e091000862849581d0b90f00075045800401c0f140e140341d643c3e1240f034401c5007030042200008100280a0500000c00c10014001c6001d00038440b040d0303109510010483c107d00e0000400503080e2181052a0403c2501914000e0340c807206100211365a0b40342c13910295000400000c064024000000d020346400d1040b144600d40300405402d1404450103601d0000c228000f1900d403c40c420b21010503251140d051300c2010314400e843c0000d1a03800e10890142150064003030303000740c0b8202804500059007410588040343e5120b43c5a00c5d4910201c1514601054444420141507251000700030401c80d00142042c000c660641d40c14507440311080362400c0459085074080c0d00f0221007070220742c041c1031006144080a0082c07602506000280d4040c50628006603622 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 59542377 1250 59541127 59541133
    0x319060b01090e01150f14210603031305130e0111031803070f030f03020f070b010e010506040f03140a0b0709050901050402030f06101e020601030b0606030903030f1f08 74
    0x10340c0065070008500030103450300790f100300410361410155818034207050f004201040104a100c003070f000d00a0000c0c000300304d5503003003407515540312003030405a40ea40c0c140305503182c00400b0041841400c012080300d007610801076456503054248002c0c881b5440c620102c600c002b5540301c03420000d00c1400e20039102c101c0c860707403100780d524100400b03224040e841c0c0c811051142d0700b04001950000712091502008994981010b819404d40740700150000d000380110808050380000d002c40030003d50507002ca05982d40171105a0b81c1c4d03602c880611565005a0155401d82c801d40e800900c089505850482c03401c40400e0211008503610344c1c2c5185800d64195181408101040d03402d01c01032510000b030502500c0e040c1c03811403c0d843c2c1540100b11509010f441c480c09080c1d02c2030f03400303a802c0c482c40e021800c46184408400d44407580b240c009555903001d10040d500d8019890100c1d000f4613085044130b0080515070003c43c115100c0310540d002411020340444a8080b004404400103695101e0410041c0f0f040320203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 59543627 1250 59542377 59542391
    0x3160b0c06010501020f0303040609020f090109020309151b03100314100f05060d0311070905090d0e0a0b03010b0a030b1003060312020a0201080106201b12120304020d02031906 77
    0xa03091030603506030441d070305541000c1d4030391105440c000140d80d07115400c888080340c1c4503036900120b401c000e1554a10be4211003c1d000202e0b401c0c140741c0013540506110012111540500442154030880a840003010403060002070010004094041d680008c40e0450828040d5a01c0d41c485107001008524001c594024008041c080c0403d03208244220790103000601051400c01e0000341d5008000000030305101c0305460b03d00d01e03100200404405460f25090801107030800d40b030103558803034443c90300700001800d07100101f0941c18000b002000311030005181e036045900301803174156079802664000c4100740d6110707130740c030742960341d4011146c1e4a01c0030b42c4002462900311306001d0f1100030050850342c1950701030420000141da21002d8141140c5082c5007110342003040c1c940003681010000c803445014403400c2c0480b40440341c0c50550004000c811220102003140b50404280c4403659908035420710038050002401604250b00c00540d1144010181c4041d40540d000004034558158001d885403659059 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 59544877 1250 59543627 59543647
    0xc0303040f05030709200f09031506030120120c071205030615090d03050306030f06010f0608060102070311210105131106040f1505070c0e090d05030603061503160b 72
    0x4040003414104005016214480302c03401b403039800120403100882d400241c65510048580203a074070300c0100400b070700c4800c41440c00b000301c8a601642d0061295217002281c5e000399600103032050420513010400d9003401c001515503a041d0782d00400600000004100740ea00003441204284049030190b12a40e40b01d041c101c00384000c01240d075414060000003008503078050303622691980303031540d07051800b00c1d603964511021a040000c00d03441c800c818071528001144280400003801e0986002da41e0b0454180e40d00c8004a27601c02440c40302402d00300030341248004c54206040c0e411448016041010030310000344940c54219a4210b8150400c0411840d500c2e041000b00040c4284030034045038a14102410038030345012145051007200c0c08010140030010f01d140c01032041d10040c0360414000101c8592714044050070000840303005002e80200c2e101e840420380651f0580b4001c80000c0c3c0101696514404400c1d840d8030300d891442d5041c400e00051300542d6031400c204801500504403030644466241c6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 59546127 1250 59544877 59544883
    0x70807020c0402031e06030c1203040503060c03160809030405090a0e01062705062701030312020315010c02040e07090b010201060e04020922080d020703080a0606050901110c0303040f0503 82
    0x5101c0c107104034010001d12456105902d104402c10320307041e5444c0265180c9000003850300740700351482900486c02e018603206110300031000d8000c030748003581036905031740d03904024241c1884211007440c010300c1d01c2c56035100600d109803040d9034481e026030300702c9180c00e4135000050803c480840711103c4030342e01c2d084503080c50301e420b0103130b41c0c02010189903031181c0b80c04070081d06994206000092282960f16000203041c1d036944e00c44c0c0241880b0ba04100785948072001019904030800b4001980403601c0030b000c403202e2003002c0c800c407841031005580a0a40b020402c00441d1041403e4034142d0748261515010021400103014040c01011151000200781c0707080000a400d40b07100764402201600c59600f000301507200c1420903035200100300990811f800301c0035006104004c0c146005051082c0200e0440a14040c650041808900a4686a206a580e4511641614001d008030800280c06200c80400d41d402101031425202d242d40c103a5901d000c0b00d401292442c0c2050f0b20800d010801124200528207080c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 59547377 1250 59546127 59546143
    0xb040c051009060503071b080406020f150105030309090a090506010602010e0d08040b0705030c0c0a15050105030307050a061805011e0c050f030c0a12020a080108071203020a0212070305030307080702 87
    0x5042c00c00480345000c0001d801404014854010303c00002d1540d1182d41554800c0c007080c81e4040b015640b102d8032180c0c000e65842d015058501c60b4810f0151488000300300621450481c0c034007e00551404102c03000788000880085d00b00c01010382c07180710003000100c5c24030049001e03000650000420302c2c0d15100707407403a00f40040720b02424000c01c3c03414800401c0d001d020b880c4e808012410695965183c1c0c0c400100103100c0c3c1c2c0038000d011b028500303d5034108000c208200b4240180030209100342d988134410140c8070311610100a24540c8846401c1002480a03001500c00c501444005c45022641d07485141c29100188a4071803070000c16044e1081c42c10031442000d2141860b40b0380b141c1001000c1d00240000d11010749840300303032000450812546413280f030400e0f00c02e226144080d9201d11130514054201407007805400454029010b001c5045078800302c03100316a030740580c02001641c4641e001c0c043c2c1a03181c14001c8240b8028600c000c8041f450410065004564690300ca000b90701c0c007144000c1c1800c0c07038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 59548627 1250 59547377 59547409
    0x212040b0403020c190519050a0303050405150408060601032c0114090c03061503010f02040b13060201020901020703062a0807020705150403120e0a1202090109050c0f03130b040c05 79
    0x1502000d00c4405808518644c1640c3d416110038070342e4030440503444881fa140e0b501541d444a00c0200200415901001500c00c840050f108502c401c2145615002c0c81c0c010382c0203820480d4488000141c0640c0309070410000c84071403c3d18005580c142050b00c0b0650403100b400840b640c2e446d69151040007c207207020683c0008054060031031400400b00103912100040e00c0740c41c02906103e6514041c2d0b07429845014a80a0740f9000c643e07850ba241100c5240b0381100c1d502c0c070810608120006031150040c001c65103410b03016800b52000c1c60451f0f80390f00090546040311000500003e01041004050070112654420aa105d403411450720340320007454400c05400990250030200d0780185100300c4613082e103003603a030321484102c00c00311508000c80701c0da00c010034940d501c071074180c1c80050080018200340e81e200e030007604c08840311f0b80c940a1000030b90324141e41c2010011400c110071001000440c0255400a030240a01e141d00c034490740752000c445200b9101501c2e40782c1820810001d0745440d40341c1ca000218 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 59549877 1250 59548627 59548639
    0x9060f020c150603060610020f010c0c031107030b01060315030209010b04030b09010c02190303020c070e0109110f04090213031203021201210803060109050607083a020703030212040b0403020c 84
    0x40c1c56008291174a8001d41341601407500d102191072054004c1c004010402c0d0070a0081100c0c03440140004d04010300c1e854250040307440341a003000205404101a815a41c0008a814690346842e1046001b00503c1a95074907543c44803001000590311b100e0079500a100810348992128110b0502152600e4003400c5022160b14013080051201d8010404821907042440c0c003242100e500c0c201500688030342243c0944070f028403400030a01c000301070b44150584400813000c0000301d06071154100703948640c58209880f00001d104c20460f080a980041c40211120300041251079580d0f51005060660300c050034021030780100f0024600f00c030a4800d40e004100d06a07643c0d120a4000c9507000e41800303800130141070701900000051090340510240c00050001400701561040c44e07092030303500c981100600c02440e05400003807141081d80070756007200907045546144040003080001c40700a61001c0310072414590203101000c041a00139004038801e42c020b130100411491309240003400e046120b04858440c20b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 59551127 1250 59549877 59549881
    0x307050a080c0d090f0303030f06050303071a0702010204120213140c030714070b0a09080903030706020924030106030e0709051e01061407080903010e01020f13060203070b0c0a0309060f020c15 84
    0x40146a02421a1f0301418009001e180811240e0041d1106400044d0184000240141040105425940314103801c0e00c4648070f070348814204a00342d2045115120003014600c40201c0540750411040f5048220300400241c400142a4406c0101e0400c44c0d916006500120403c07820507080f26403030358805500a2020728203a450354840040000250a50203410740d076400050401c038084040b194880001000c40c1d450b00d001c0e14001c07000c1c2d401b04941c1402110b0400703e07a889495003001001d4562140c405540c256030924508400038490000d1007806841020000581d01100d40715650158008180301c0f000d00b2130300320352a665441c06a100408000003480101440d82d112420b440c5800e0348211540c0c0d803600321000003400b50038851803181140d48005070018029580000421524411084650100d41c0d00d0406a8903401840400b826a906100c009040250031500415200c0c1d80d82c00c0008061407642c03107031422901303040d09013403440750700203503404808500b0400e00d21600c82c40d44928260b4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 59552377 1250 59551127 59551139
    0x22050615030d0801060e19080106050a090207020108041202031306090504051f0918120305011a160201050d1b0207090e0705240d020c0615010305070c02120307050a080c0d09 76
    0xf9101482501d081010000f500c00b419664010420480c1a070320f505807240545a840d40e500a01040c820f0b10311501c1c000500040280080c000e0741d4826805840781200396469484000403410812031140443c08100480300152500c1c7c070401c4042e00b03032030361110062803c10f4184412124060400180041c07103a09592405031100b42c03000a45030792030700c00305200c00688011120116020ba00074102c01d1040001c0c40c1e002d034941e205034100c48020085080300005000003138480d1140405180c581984130402502550003000144100e1700f00d5440003480d141c10f4941c10501d005107026850068205950401144026000b070040404400c005480120701d000005104c00c201c40400c12010124031241d5a0400f12410a840041340907143c1076541f0000182282d07290748017200c403607904051003280c0d94040d51281c451075114069613101e0b40c0015103e0380070007820342e02c19030000b000752000700405c00001b00c042c005241d2443c440c644550f02d61071b201c0c60b042c2c18500e06a00200400c180754404100c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 59553627 1250 59552377 59552387
    0x605012303061513051602012d090c0e07080402010806040b0604030213020f040303030f151d04020f180109110903070614040504110703080606040b040504020322050615030d 76
    0xc002104108036126080360013207090380c1c034480b072401c000501d400308129807031982c91300f03104e00c3e407140d03500800c10340540d1402d16080380781450301059221280c500d000200c60307103580550100c038011401e0450042e501c0d130303038404100704c1103480c0000a94980709000071960000b20058100e442120148107800e80c90f80030895500440c41b0180c0700390030804203007090222540c100d40c0080c1038440060355494480c10050041d01d1000c0307038420710501d4180d00395180d402288011065a000e050301c01420410702c1d00304407682c84040e000340c0c1c0c401804c00c2800e04664800c0020810400900c03c021703455854a4501403c0b43c140c00f03103900c1c003801c081102141560b8041401c6050f00d00300e0074a0345c05902e105085049a000b10341015401c42e28110203a042e14003800d000d000924841d0347e40724066942d1005129007030040703100f0f03500d019000380001d01052a164002e546e01c0882c020400300050107e521512000107100c4058030590840c01c10321100251100051011361010340091209142803600109 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 59554877 1250 59553627 59553631
    0x171e2404180213060504050f010305070e010e01060e010306090c0908070b030f06060d0b031f050601090305030d0b0411180a0801020705071a1e03010f050d021008060d060603060501230306 82
    0xb203c3c01c1d0451000b050f0015a0b40004064140508204400d15000380540a0b01100b07000540340352041083c00a04102c90a0b10070741a18049007030407805920b407280945041440031440360506844440116102c3c00610030030004040079a00d12019a15103507015041003020b07001006c400004004104405c0742054070507400502c140d803001e41d00c1c0c610303608940041c5940e020441c1d05020303100203042244101010031100c0420302c001004a515060300554a03c81907200061154000341301600150391103034040ca50603000908081003c4100c1c10302c0043ca60b00502900c00f613041c02115204c0c00381070241403500588107040085240c01450340f5071565031285407045400854403882c810398031880100507505407510340e10034081c4843d40800c01d090aa0024002c0e640140c009843c001054500482c4d1019515000350403245080489113044a401c1c80003448250451800f400c040001019841454011405118005060750501d40c221107003038085004800f100c0c18281078002280e90100d00c1507 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 59556127 1250 59554877 59554879
    0x1080a0b090f1902010f081303030507030b06040f1422110c1006060e0d0308040803061f08010302150c190618060501080715171e24041802 61
    0x14116900c0d04091880c180b014805142c043c040d40d60909000c82c0d50005011100b8405d07291010b8915804000307e0f900c1000722035035000c2c12201c0020a001c01e00a178070454001c40c0e14940031420f4030f80711010038001d520503407180d000a90200340800c100c202e034082e003040300e0000321807180c1400c116103a8482100c60404290249a13a00c005032114045a41c007180d5a0440e0700d410303a540c0c1f242e50f40c441e400401d56407240c10041281071041e20302a00d40400301c80d40055140d114401c5540741c580f140f05464000400454200c030003c5c50050740c458000a10303154914040d039441f1303070940c15441400b2503811560102803008070248007255010f00c1c00b08803003c11090002034055001414117205000e826401e104e04480c01c0490000401c0c0405600500d040c0c41006040320312032075884148100860100b0b203600e0000c0c03407400ca0440400a402081e94111109925401c0940204820b9074104130060300c0300110040110070040a10454501c40c400150044030104256031450000c00355801044c9030003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 59557377 1250 59556127 59556143
    0x301050919060b010504181a010e01050a03021806030f090708280309090f0207050601080307050304061407050709020a0f0f1209021f020a03110604050703020d0213050703200301080a 80
    0x70b86500d0b441a000d64006050212561413880042400c42000f46023012403403886620480207440305502401b042d103000c0740180c1d01d49141c9445c2d20000c034000d4010a50703080c890f8460000400301c0c3d64404019501030030020b00906024100401c40c50b00c0c011f11a0f03c6070742e440d0030807030800c2c0b4603025510461807c402c0c1c2040c0150001d25074a0220341c69121904048200791911103c40101101603000c7d00c0001c0c030030b1040f91280d0b40c880c85d000c1d0392401180e1004040c0d82c0200400c1c07294030300c162540703028000075000c0e0340c0c2040107960350f650401c884e542100706540d5000c1402ea5050740e0024800322000c91a081c16140700c0910000141480d0721100100b611584a2003803800315242c0b07079443c410700e5094001e1240c03190401000207446a00322002900081c42041c041c200ca00c80102e2503d004540c403030b000344091403841d07003801004e01d00101c00745d070b010350101c544607030010080c024548191080d98001401919002c0c0c01014410300305c8591000300d1050005102030040014401c00450b0000c643c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 59558627 1250 59557377 59557391
    0x1302010e10031808090a06031404060903020708060a050402040605010e01020d08060307032405070504270b0409030201050f010b041419050a03120311030606031b040f080c030105091906 81
    0x42d0064245108104050f0303400030040018040d1040c040c040d00c19040718014001c3e55910b0044040d24940d000810388410031901180000d102c0e43e00103003d15200c0d00544802a0f40e4405407400c1c800700300c66804032951034008001c01c40c0f400d0711840000d0002402c0641007440800c00003540d0f00c48208402c030a20480c6030100301555000c011001c015a0f00000502d440519280d400c03280d0380300780200350305a60803c1d001c5007206024605a40c1902c800c40740044030b212103072081e0f155042c4055005d55000d655041c0e02d0120391514080d025a00c4d00940022510b402c020f003504800c1407050344112801d01d41800240f180a204448100214504175004054407001c80520000c040f05a4000d5600401c50040001005200d0425480300c0c416500d04026600d2904460304540c403040301c46503442001040001c0030301d880c4204129900e504a0f960380d0600340ca5203504110340540c0d8000b80c0c60359020042811b2246400d010b015488060700c00034000d90750510048030410f04041070002c18071512100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 59559877 1250 59558627 59558659
    0xa050405070b0d0e160317030408040e01091d06090a020f060d0905060a0506061801080a110f04030506090d0c020139120c0203030301050402090a15050a02061302010e 73
    0x716540c0901500d100e0340740d07110b101d410500024085080820030034040e04040168007003428032200300f101c1c0c021031444104a01280983c4080d80010320403103a1407400e110114680040b403010a018140c401e0f4000741012040500c004c200c0c998a0310750b440c0742c2c40781082000d0a0404194179403903a17415282214038900d1040011840e005410308180590315107140368051003c00100c16019040242c8204400c0d11340e803080c001184209803140d10340d0b45900781c15001c1544a00d003001d5001c2072039503000070300c443c544a50b2103841d40701d04040c150f010404a030030303c04d203c02030000d0fa402c08680b80040100080c1401d01420350010554040d041c0320a042c1e00b1548080b42c10000b507600d114503010420b08070203a07200112844e4a005003600c041000c0702d40c1e00b094034050845c0c0250580c005000307600350307071070001080003a5210760340d00c94200011030000124004400c201468045264483e03644814003005c0003850f00c7e400411900c10304081e881c1c80030242c1d80100000f0f0030074078240c400c054110038400c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 59561127 1250 59559877 59559883
    0x10e060a030e03030c1e0304050a030e01050904150f0b12011413050717090102120a050901021b010903081b03071b02030d0c05010c02030a200a0b13060605010c08030a050405 76
    0x20301d00d2003070f001c004100000031108000402240000c41528084540c1c0030740e8030440790104460050881d03111b00ca2620100303000b402030300307260f140502d002e600d400140004142690410700c4814041a202c10040c4220294440304802800d01c4085060400c424181500c071002d506108003050703000044021842d580724100340c075408504814050100c1d0404031001803414032600d91040e40e608a0501041001d08180200ca40418204910103100e0700c2e0204030000414003e000380296640c00c008524019003000704400e4480c3c0b4070000002e000c48a07040103404c000e001802e034452840310240300c44042c801181500d80019042c0742c06000722000042c15054182e88001c00380d0b1502c9542e0f202e07041d29620403202c070340c032600c9030b0f000b845441c6030b808050380e0328001c035011480414502c425101801c0900da4020f0680f45110044038031200301521050040d20040d01c4005180429034404800d000481c016003006020030700c3c00c08154031241e01c60508501028190003040e64480003c64107000c410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 59562377 1250 59561127 59561141
    0x403020c0303090d1b1a030405010f11030601030c09170f2509020306010e040207060e0c0f0f060903150f0108070e0606040605070f020306011206050a05040506040f1703040804080c0f010e060a03 85
    0x46c0840c8590304100e200b0110303900116004c0f516176007051020640403034540980d4480034070b890031203400c40e00d841c4015009811890008030400c8241d81c4006007259a011041001b04070b500080d1411020910065040030440c070504400880c140c0b58a0034800f000580040407161030460041c0c4035110f0400480c1c03c8581d0709003196106001080c04001e20103140c0c014000c1c0f004507022205250004801d000a00d200b5240403948014070014000c81820032030700074450500000d00303031740b140040c9004c490300840060320504040c010034001440003074803c00003a40503110b40031010415151090000340188980c0c0164010443e0200700501001160348105403065401015030b219503031a01d1400158000005050740d000f424400410580f804c0c922074540600e4201020f4030803565035880d0b0300e002c48090f1100b01d031041840400d00340e513003d18101550081e40b1403ca281d5450b458462420f1401e080310000522540c44c0d0080315405a03042a50380414142c00d0341d0403034484e50341c5c0303809500030030700c1c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 59563627 1250 59562377 59562389
    0x2307080c070f0906050f09090d0c030c0b010f06020609010207110d0302160306020d111804020306060d050106020a0b09150718030519050d020609030a03090c0302180403020c0303090d1b 81
    0xc000b011900318080d400c40016030b0402d4918100b202c0c89070041200c0710074255640c40e4590808080c8c42500f40c4141a10710145010f400c203219015899502c000448070f099000c10302030b2000c0d1006000e1341e90f042c0076443c1c0000300280294281616902c5020006001c4081c5074421100c4072510303c00c140c000d0202000c44400140c4035003042d580c90405c0c0300070754000d80c0e5500000c0e141070300841101d10104155072a290801d0204003a2002850600c8000c0d4009000240d000c0400d00c040c443c030740300301d0040901922095014009518140c6080e120006002d0441240d40c4c0044400103c500040c003800d642c007030080d00c2d00e1001d061521480014040c034903040503020f406810804828002e41c04a1613040a1280044034041032407094100c0c4c81d1407090b14540180c0c0c100300201403805100380c100c180703814014600403e14683d83c0d40010310241400405c04c1c540d03601c03130301084103043d0180118640b6000560141d03141050010005410009281004004803942d0718001c0d90344000180d46006020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 59564877 1250 59563627 59563649
    0x114120a051e010e030d020a2f06160806011202040f0b1b0a0f0303020c0c060309100614011b080f030c0706060605070b2403060a0b012307080c07 64
    0x82030400d9a254a0008002c45079075089034000c42d05020140304548184009a02641c2810f00054141020394002810070080216040c0000d000c0f0b00030048200d61059107240246865000ba028a8141000240000c20140404020040c0150440004e0340c0c00701007441c064240c1120f540d0684028044c942189000c914500c0b0045078008040004000d40090821452620304c02440c4841e0340f843c0d1000010030380388a9400c0c07100003d0198000e040c14162280956110703001500c04158260002c07605017400d903005604405000c1114440c030340240c4450110801e403400c8400020b80031411a0004201d2500c12514800c01e01c10740703c05a0386a5610310051310b03901c0c14034060551558202c514241e0f1000e20b82480015044c0c0280c080360340203035018000780000c0c0d07180001c00c542029090703182c0940c119140240c81c3c2596050040f20310a030303624803000904100c40400180000030450b01902c00540b0403c1c200c060071030310790a981081e54854001d99036a84c406c00640c2c1040c0e403d601000c8680c1d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 59566127 1250 59564877 59564893
    0x90405160609031704032f04090308010501080907350601030b01060f030501051e03031606021804020325110d032a09030803060117040515090f0303011412 68
    0x2580070300b02404582c09924800030940d07511018540a200d1840018458550f550046030a01070340e2200c80350402203482d0100072624000c0100b0141c6540b90411000100301000511a0b50b82090100341c1080028000300240741c24000c0d840c0da034510f120704003224070341803401e841d98000c50000c6079620181d0000c02e40d070707031560750b481e018440410a0080001043e081c40b4266240792003031007401d040b910000c0801000e014214900441d181c00036480715010f002c2006aa074a841c2d85a19480c0c01d940f00302d10040c1d94811354500380c00d121164045042c480c1d40100140700d030001d560002c0c0f40072014641032821940b0642c001c10b8402c1007099460070036502a03100040d4603260503a000c031044250100107803e100182c400c54100812418440b00041624548103001203034505020310b601000c18180040f42c24000ca503084518070b021503040720345074815012400060080680c2e59004030040340109441101c2000a0341c981c081401039000301100d0040c52500c565840b140316008003901000e0b0350142e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 59567377 1250 59566127 59566139
    0x231b09041d0c0603100b0a03022109070501030207110906030304150305040219080a03080a021e070507050108010f0b0309010906110703090510050703030e010605030f0307030201050c070c0509040516 87
    0x5040614291049008285030701c0c10b1418044200ca2162007208030303a00d812820b050401c07107990890206070381016800d104103440b04071600110341c4a224010050312051510818482c581105030300503a04040c018018000028407a0070800b01081d0120f401d0000ea03a0781e9030101e450740c000d961013608142c840c00700b40c10801c1e4060703000f203001e45d000341d450541c000e031003414180302c00b070b01842000456888442c0c034501107440f03103102c503400c015007500261400925034015418500350300c1c07012a401360005440d104105e400c00500000303102c00c0c00c1c003280545c50141c48081c241d409100e42e1300d04041c00000200003035401c0d4002c11180b0361268003040b0804c441ca408240b00c5d00a54411404100404008103036850007146850030010680d444a02d04103c541c0d04801502d61500d41400350740d21040041900c0c0c2d001e001d81c4000303008040046031211402d08000f42940c00142c11010200000c000c0c20002c1303640e080b0804151407040d14084d450362a01d00c8e01d10328200007400030258a0303000c0d40c404a00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 59568627 1250 59567377 59567411
    0x3090a0512070308130b040204020a0306080d090f09060b0306060c01020d0510080c0906060901120b060705150a020403020a05010c1b0801050702100b090f040f170409231b0904 77
    0xd01c038003994428804d56201c2d0040300c00051020700c0900030800f100001001860b040c2c00a184000f000c0c940428100e40d207402c607a151280c40d00700c01010400e0050b05106505410541d0001000080781c148042860300d000c01c4800c0c03001902882c0586000140581400d0b4250122600e404129800704000c0c0b034415103660b0060380900607900e846c000c0c1014031080b0b161071650540a02c0c40201600d242c28400390044d10030100000105581c2501e030703040790070103170b4580c005024206d02460161220588212008a14000040070301c020f55206000c1070016071608500d034000d0711820700b0143c12800300740c00d1141d00340901900c001e0480203002d10100700c0790010340296016403e950200c804407101d00303010205a9844003a40307038000f04018000362660214003003081c0c0103401807412407a000d80d6600c404840d20b1106483d1001c500c1c4c0001d040202c20081c0c1709080302c1a800083d60540b01410260400c04010040c184c7c05d511035080880d420841c1b84042124100e0400520070006640b1901c40c14413 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 59569877 1250 59568627 59568637
    0x40803130504050405060c03150306010b07020414010303020604060921020a020a051e0f0103020c0a0503070317190b041d0f06071e1101090c030b0907091a0603090a0512 74
    0x40c54451500340090281050f0084a00855100020740070f02d80e41c1c103a5034045a00014040d08120041c214a5180e42c0c8082c40418040c0900c08005603440d04036006000a403180741c02c0300c40b40c44055800401c00300c0d601260194025920400110b6208000d04000c03641c070104201074a10003580b406210809900041c0c1380f16560310a890210205a0316010811200300b00b2a4000b16500062056550f6140000c0d01d001c0c10320050400500b410001c0b61498a011880002211150701c00901081419004002c44400c520408207008403403410380b404000c051004804e050b9010340b142c54400256841d50000c510035510b0305001400405400d8050382c0c1c401d12004490a01e01030340740403a001d49c0c0b2451010710a040414900c82642d8188401100c1c1184495002d005e995601da0400b0001b0340d0203a1410b0045019018800312400c0900480d130600643c2c0c1c0c44160780c0d900e000a11000200c40103102c020b40d0381c00310b40140c1c583d48d8403880c00f03081a600845c024014025000d01c1d10030385080c440608 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 59571127 1250 59569877 59569897
    0x3070e1f020604060f020415050c150414010b03010615110c13060f0510090b0703090e04111e010219020114192007090504080d0e030a0e0603240105040308040803 71
    0x102010b061200302000324840c3d8056118802151230994032203500400040c016100010304035644600707003107544600a0026a0b049805401c0a20000340002e03090140c8465140110000c100e0740749881c40c016000031a00d240e21040c004014085610b4200900803030111840240000342280c0c50901c6076001010a40100d50413012036030008121030400c0c14640c00c0408694aa82401c0c0d8240f4001e6501500030300c3c0114100444c0c840c021400031180324005003c2e6200710303c06682500c4c00d400b0400a0030520340e01d00d081c0300c8449000718003680c0c0000e080079060701d521060824207072a400120380c480c204002c46101c5402c00191560364610300000300c0c60071401c5030303200c006441003290583d0100d1202e40f86c40c000c990041e4001c2c0071400b4907501c01508544111110b525014101c042201925a6485034911503000410300380002900400344c0d0308050713000ca0300c451452810300015000000c80e081c28030b040d421000c3e40300c000d590180c0102e50155070403156260700c0d981d440011a03603c1e40094005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 59572377 1250 59571127 59571131
    0xb0f100807090602160512160303050d0609050403121a1f030b06030702120d0e24011403030304080711090a0501051f02030d0b030c060a030501030b01170303070e1f02060406 76
    0x2075444d10108400030280b0000565800b003514141c01c00c142e02d001da80c1004818050700c042141840100800c0e03100640c400e88550392a44c00c02010310b01140c1d010b90088048604100401000a43c00950706146803016980022003402c1031a0442c0e1a40714240ea094020746c0c5515401c0004040da03a8044c80c0740c0040d503050044033a031105111890009841c4130000d41d100c05058039070f690100303026024000d00c0b204005020015511b285182054009956a40307011000c007480241580484c5240505041c04451500c1c040304008255203100003040508072003004550b200030818a8a060740c0701d5000100301e20aa42840144000140000c0c130400f8070665220f040000c03607202c0c0000d91038940c00150040c60901d103040da000005082045106d41e80f500684420252175a14035001d000d1805580c4d03000188c540c11032a00d0b82510310b06030081c1440c0a94072405111210f80002140d6206c4298a03040c042001110b01060300c0c1c0000c21540550702071160b043c050004c0c2d00013030f114480d901403001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 59573627 1250 59572377 59572379
    0x308030109150605070303020717040306020c0c060c032b09050f1507090306051005041a12030c0309060a0c080708070302100e0d110f0601060e0a0605040e010501030b0f10080709 78
    0x8002d00c01d0740030701c40c1d4000301e8003d00540c40031a019501030281540103074039250188804288000fa04c9d4840c0e0421100190b000ca0540c5c11490100605481b00b082603070f92920742489103020030ba4a02504032954509050140d1f00c4000750605a00c0409441450b00e0500140000d4584503440e050007221a05580c070520f092100d17010080c1c0903807806000e0780e4407210307040d5055440d07600240070002d10082203070040c640002042c0d21240710310300c40060300c0744c0b9041000c1140341c00c0026120b4080c40c0c00360668014400c102c000307078010049520207541241c0d030f140d80d103290080035a0030030030b440c101804151740860f9100501240000a281c0380c0e00c40d07403d80e02420500000c1404035261b01d04411500d50041d003d6080090089402580f078070903640803a4104090301d640b42e843d12109030004400a0340c841f82c450301a0504000342d002400d09070070301c681480c0c281a1a00440038052082d0fa04050f00d038940e02545440750000050401c3d0301403d034141949141c40082c1c00d40c002503441c0c40020707070700d040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 59574877 1250 59573627 59573651
    0xe07180603031205190c02011d03030a061e0b09030a0c03030e13050f0103080a0e090a090201090608040b0a0209040f1802091303050403062a170c0c0a06240308030109 73
    0x41068450b117000d04210380421314940c1450000c10b075008041c025036581e403500c1c2c0d40405943c140f40b0041c2101400a684d02c0c502269a40d00382d5036642d1040304843d03d11225001002c103c018180309882da900c2070300e5200e510b0000080c0c50b140e0703541400b400c10401c608000c418154041d60010325030405950a051a10780d10380d803182111021540400d940c10420700500000c0e64080c010a0714408501c0d1041141004a002600300e9206468849110b5501c3d1300c1c981c02c42d42c101c41240c0c0100403a00304121146829110901c0c0c0c000e008040c08501580090100c4041c0d882c0e600c481c1410308920401c11010358901034505007038101c4901644691100c80000b0112400c1d04005041e1030750503580c0394145451540c80101503c4500142030070711414050248041e4a801d5141e14005410394a1040c03007242aa0100404c0300046d160241e40c0d6400c1102c0ca49400f0005910140b041d400100040d1100003c121a00400850f607c1901c0b0100403250010070300c440e40e8080e5041c0c030b607803541c01c0102c501120 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 59576127 1250 59574877 59574881
    0x90e010b07120e0102031c02030f010605070201050a0804031b050d02060901060b04030f0c03061404030f0c170c01090602030c07060f020703140c0309030a060504060b030d0509040e071806030312 85
    0x154008201e10390b00348284a201d84103004029000806004490806100c074900c02407480102c5550203085034048208110700d80c05992550040445050003031400f0107503000205607119410003c024014801c01203010103116184034030b002c0c4003003610044040b8444c80c3c49c68603003501002d41d00040c454000440d00038070040c451042100e407909492841c1524650300c1007440c65114105844010b102107001000ca5814001c1911007521805008034071320701450040c11801c1c0d0b00e04280100b0a02d8030503680080da5801a01100901c142c10241c0c80f021038240103400b4202031400280002d001005000621764204040c00101c0d00c0b440c014801000942103081c224090028043c000139800c40d102035900b011030009044510145080d2850700e141d580209192241201080313a565945100700810f200492080354900301049010300a03619009800400c14012001c00a10660703a4005020360b501040188100501400500014400300560850028110340c4801c0c0d0109a0341820108010001c4c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 59577377 1250 59576127 59576137
    0x3020d05060a05220e070305010b090f060a090504060e0d080601020706020a05060109020a09030501060b030714070c2d0b0c0609030a08010b0a0c060216050d0311070206030604110a090e010b 83
    0x280081880c00c00a1050b2102d844e2286080b01a40d940c9501d144082d003410300c00100654001c90001c200c400602c0180401104014409058111a00103200b0181d0b00d42030240125860000081481c8e140d03070401000520065110202c2c0d4801d440000182580140e2100d03c5500241c00303840c1425540d5106917250349070300c14020120f8001100510420344683c6c0034054101c1580742c070200440e241d95485003103500f650003900e13000f03001000300f0122940c01920014070a10302c1800505214444e03480d00b5196003140644c0b41710300e200d11184102855001c2e48241e5041c6528416050143c1c0e40c951540c0c281d002205616040c000d620024928030360000480b11600d0042d41e6072070082e03280c03201e400883d42200c0c881200700221482c016005c20003500150116003202941c10312510b072946801807804825550a0052505100d1000044040e2005495240d0f40607100d00d6540e68a85c0700240007486042004510fa150204103258207692200d035181c19124071a2003c0c59a0362548404d0080c1d02030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 59578627 1250 59577377 59577379
    0x312020a11120f06010b0309010c050901051206040b150d0c0804020a1203020a0605150a050a08100902030a0c060809060105012d180611192303040504050703020d05060a05 75
    0x40e60076062400e224003220300c0029150300f9a031103141c142415904241080e80b060142240210600c4045003080c407d045064682d418420b10701740b90000007070254042c0d001c510515a04c10800183d4a440769041075410280c000c018209124010b00032000e02e0b0468403442c0207491070700d081c0314465030040c20315a00440d0001c21807070074503287c500a007007034004602d4105c00f14011640340d107002501b50b0141074000c0c1b84004003038a103441c5034018080765941790f60001d4410720030000e040200800100c1c1c0b2505d282e00c405008550250b031800803e14140e540d5000501d039500714500000c0340c5a000c84c0003030050b10180309840d0640d82c0c400045408100c40280000c2c15840b80318481e1051541c0000703804070580c076082a0503807480309020f00c00c944446171700c2040030480b1041854100c0000340503516242d00c1c00c6941102c0c0303903566103800314011940c43e8100c0400c80c00760000400035200700b00765001414000d005000030310b854a001001f942150b0450854242042e02241032498001d0048041d01d02c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 59579877 1250 59578627 59578643
    0x60308070206030c09030a030801080c0405010b03180703020907021513020f010f030b120309031e0606150408011a1305040201020c060a14042606130209070e0603040501060312020a 79
    0x3019000c2000340e510140c2456414034080110b0881d64805101026009000c0c2d1101c103065071405807118104042c41d080303203200d0340c0340c50014414018520706494000f001c010001e200841c00304003d61804e4007540020f54411003d03020043c8050340000d01482c902c107440110f1086841e09220040c00400e1854000d40c000c94042014403d544104030280003a01c06181c0418401c400074081080f42505040320380c03142d000000e003900181410841010160040c88240145940e030701400b5448510240800e807150401c403e81400c0d60000f0000e88014154580007003044101524a04041d500700308101401120300c0481c001d070448181c421107101d2901a0043e2074080300c00d1040100b03603808802140305022403051001c90000309d44000c0c1c0301508113504240f20041d150f03072142c0c205118007164008168411000c10481944601146076066030644c3c00d0622a11680401d03946036000c00d000070303048800442040180601500f00d101100d001d80510100d040083c1812600c1d82e40038800030300150 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 59581127 1250 59579877 59579887
    0xe12030d090312020d050405011104060c020d03020a081207020c180601030b030f0d030e0105090106061215170c0108150d0b04020301110316080702070e07110a051903080109060308 79
    0x1a9250300455929842450190b074003a050050142c04c036000032020340300056884081104104091043c10080c0900d01d0100d810145003080003882035143d0940240070b20842c1c0758001c1003500030020b80d40e059500c0010281c441180d80c4d50b403203007000102c1c0d4000041c403030307480e089a0b24205104c1d00d14810380000020034166403428015000f40002c4540c15406201c4c00031101c49040d014803441d0000308190380d020032800302014200c1e0039558094210b64032039141c100100401c503007000c02c171079154244100110b1031202d036001022010381799601c20b4a61250303500c00704450030b00120b10300612400c00d803907001d1680c0715035000c0c0d0440d1800420640d00000540500000300d041c802c2d010b13234010700c02000032a0442221951b03449a420955050303221507001441a00402c0e003215036558000d10768402485024544440050300e10f00140141c000e01c200006010803d0405208a91525400404071040d09001000040000d0741d000c5080e8000303444800082840d81d00b500800044036004143c0ca4100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 59582377 1250 59581127 59581147
    0x2301051216090314030a0e15070210030e12040305010c0215150a0503121e070b07030e1c09060f020c1302160f060c030f0209011d01020c06040e01060e1203 68
    0x2030003034965507200303100220748000300080c0102e4801c0e01c16908000955140d010076040a4000300845126030310030a81643c41c2c9219590307840585805a4040b106909180540101034005010380511103a4074000d0303d030b004045d05070440080c02140e100b48020000c0c452001c6049881d1042c030448610005d0307840000c1241002410000c26101800030030b040c40684d174440009280444d02a6010b85480010400c0850003000008112810450360245442d004440c1d480c0f038243c1000519010a050342c500321004142c1d0308100c07000c503203512846c0c21030000101e441c01601c2003116206400002d0011482c1010f06827000c104800d0258014049080c092458201c91b0040e400c42c100c01003042d5210003071304007c20442e10640440c2d81c062500001c0706014900001d0a41d01c60114108002d0b004208070170440e41d004004008450040900c2400c1c0168100101e042140c0ca0f0005075003d0000f14000c00e0002d00400124100c8002c0d440c1c241d4801da80505100903050070407440c04407600107002c01c0281d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 59583627 1250 59582377 59582401
    0xb071e02030c3d0e010906020a080d06030209070206060a0f08030913110315040609020703050909180307060f140910020a0311040312020c011e03020f1323010512 71
    0x2c80d68840c807503d20402c100102d0521070300894100b211200c55841c00b100c0c80540000300c28900d50420320706010310500701000a503a03001101c1c1c000304407400000f1190500b601307583c894400742d68010300d00b030418100392400942e2510b05841d21413284a14003800242c841d04c20304400d00700c400301070243d0b003050546c2042180b010382c84204803030036075107610b019101201e203000154490090000404c1a110584091004960080e005140716034070401c611804280c1007419200c0c2000c0c211004150750f92855900b240c0b100a21230030389101d21002c20107030200205a0006559a160000100400c9510140190491505840c640f500380c120020341c1001c2003581c0c000380502081070401203a90b024042000c00d44c0e91150788155500a2480180c82405030304cc045050f40440910300041c1c10940c1c1014020b030070000e50b040d0006d15500003a807030b0003001c0da0b40c10f4895008030f54240800d0a0341c0c0b030004248200d48260740800c400d124000d440b9943d801802070780c0e400204034000112a80d50008078081d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 59584877 1250 59583627 59583649
    0x1150303030e0a0501110c0607020309150903070f0b1b030405210c0a030309080609010b1c0c030c09271104050403050705060106051c020906070204091a010b071e02030c 74
    0x45402141810008141c00b40511a06ca4401e41c5145540e600300712000303070401e40047c01c5402103400410541086a56180306150780c9140d060a041c2c3c0c4050500c00a440c200080e4480c10300c1e41e201040004522107000c014101c100080b440602907816000c001580b603108a024056001e0010b0110402d8603512090740e92038003481ea002c68154074480000030b02100c0442d07204800040c4021414011100c040c0401d80c0c201c00d0100003480b480840c1400070300010214220900c501c1c002c40c20010501008601c15001190022419050b990325444000058803042d04082401d85603030350741a610b0001c01f003042da002c0f80c102040c45d80c66490203040101904003c0c009400300034085c042c82012450030f12107030703000b00843d8480e1b9071790f068242402c491200d88500c4001c50203105201e01002a21441c0071036001650450300018035541510382032001e00c0129110f1174180030700d07000100301011b03000000c122083c0124903c0908541d6545031224060348024000d4058100c030311002005d08006010714 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 59586127 1250 59584877 59584901
    0x40b0909070b0c0a0b09100b011b060c0e04060801060f081501141201021201081b0105040e0601090308070b0601020705090103080a030b01030e010f0b0a0902030705040b030402010519030510080115030303 89
    0x44c030903c0d080e0315001c10300c604c16503c01c0400d400c40900c007400c540082c0301c1c1941e865000c4c01d04181b504800c1040d91214180d03d0f60140030140c80c1c0f00355000300341c0324003034044c0003520050081100c0c0fa2281d4080b030083c03109010307520a800100d42c011981102c00665010701c2c800c6800030880c00c2e030030030301050f101451102c811500548104060078107540c00780040d001c031102c2d4140b0340359650700d8002101e2400c403840c00880d1040c445040c18196030399004003254290303500070180200399102c0d00c0040700c04d609681c0c030141c009903021942d00d041004c1c5074101e602600099003203904964584080042c1c1501c00e1100420b4642c1c00c201486580b4001c0d000592405814180000e4a4524115007802c3d9140c9450a003001c4d95100309202c2c89243c140e540a0141000c458114114a0071003000341240c030407401280040440400002c0071680b00340c0441e04102c01164441c2c1050910380d41c09800313003506540240348036500d800c003c81c012005104080441407040b40c510f0096281d03032019001411031100b4a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 59587377 1250 59586127 59586133
    0x60c071410060b1c020c030901080919031d090105060a030b0102010f0e010e01050c0304050a02091801020706020c01051317090d060c11100e0705090612011109040b0909070b0c 77
    0x28944801886440c00500710035210701e0361070840200c0350142d1310300e00c048078907a6403042c04003c164100001c10f4038a00708082c2403506e01c0c0e8454002071844d003000c803a80e00c0780105070f1001540030190f2100b211900c000038008030204190043c01000300030301d024040e89030008401d00900201c64400e030050101680180000101c0e0041900500b046e514502740d8080f2a80d141e20603444141000d105565019510750205810740c180b55446c192241840d170341c042e210308200307004601d80c18129a0b01c4500b034040c1c2402155a400c4e41e02c1d080000e90130140018200354039141c001103080c175103461859291a440290700d080361070b10007885e005a42007184101d422000e141e01980c005802c84c4216500b15250380c8540043c0768000f01907600d0040d42041950303040b81008540100c1860008015044d034000315150304440c2c0d03c26012411100c040b03060404290300300382b90f50034108050402040c4440302541c09120464180c4280240340c04155022216907020b83e00422030200740b0700240c04000307640c0c403c2d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 59588627 1250 59587377 59587393
    0x30b01080a05071e020c013005040c080d0914030303040c06050c0304080106030c0510111c0e03030a0306050f04060b160501110c0c0a1a070209090f010608030c0f060c0714 75
    0x144d6042c2e003468480000b6a0007280c08820660300b003600700c0d07228070440802c07940030601040c80300c0b0f2601501d628502074544640116040040401031034000e424a030045a61801408400900d01070252141d007800c0d0748583c1d0392020300e0401008407803180303030080521540d2074034003134080b01c0c1a07014500c010440d00050002041d02c100031300900d80114054402d100c000c504250170803110080c013031040002e010020903c0b40b0700850104288080110303200c00b480c0c0c00825000c00399581c401e42d00c80c05034140000203445407616010342c800c1e002c1d03400c00d9900c21040c14400040c44100c42c501d0180d04c0390040e00b8044803881012010546446620520020400044180a0707013529005540c40080e00c0e0420301d01c080c05030a0182c00780000304107211900c101c0059008a0a48900c603801d006030040f1100710020795103000400070100c900803510004c1008a603208121501d07500400400c42e001d020300c801042c141e5000040d140d018844c01501d20346080142d40d580703600c841c0030702800b03603036030180b100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 59589877 1250 59588627 59588657
    0xf0d060e030a02060114030f0d030c0e04090f0302010b09060102100504050307080408030a030f0207080a230301060302180315160c051006060f020604080301091104030b010305030910030b01080a0507 87
    0x1d8a035092031a002130909505010003030403681078007040e00d402030348040810944845c00140c013a040134224100080c1504002100f01c4880c0c52803417031250024104086201041040c2e4040364078180241c0c020820110390b41d08012445d802070300e00d540180d10004285181da002ca600281c5c109100f00112031030506903030f07100c1d4115000b07a884400c0a400100e6108603413605801403100c8032103030180031880c080e510359440b0140e018105d100e4080017151035265101d01450b440100b0004048c1006640325a9102d00044c081d5102481034503012b60420b81044050400141030700c504100000d00c0010780c1e580c052401e0520088190a4080189540d10a00810000c2c07009913141318591402083d030341d082c01c10242044201144036021075020b0740030400810a5002600d05442e01518040380004003091060078070700842d000a80645065000002005030000c000c04403141d040e22000c0c1e01c201c03001002c0d011109083d100718049510100000c8108038281d100710713805030031810301e2110800021 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 59591127 1250 59589877 59589883
    0x6071d06070f031e05030402030312090a0c08010b2d010825020a030806010f0807030f06170105010f150206010303050a091e0603050c040f05060a02010912051201060801050f0d060e 79
    0x14000d501090300a07070200c100f0119131545850b01d0301d0a050061071428a0381c0883d503244a41d501018140c0315160120b005440e06208c1050b160380c025a02d80709454507088024001e04c0840c4e40d0381e00c513904031110b0300c2e42c40c1c01c10003e00d180c2410342404008034031482401505d0318a40144042c1a00018080340e00241c10507000230803400072550f005041c403045618000e0b007800c502418050620090603410b002040d03004141e994094114a000300c0c40c40c00200d44100a40184c1c2c0004042c19810000041503980561105040381d0000070780c281c007a41d40e021164245003d607150b034001a00400c00500100f4040c400a0015140fa0714110007043c1ea80c0c44081d40403201c1000d03c5424030110002013000b103505001c0d0342c0c3c11808500c140c5140c03610784000030f141c00040e4890b85000e0300b03002c103ca42d4024001e612402a042d005603085880000c07004000f00780360300850004d10003802640c008100395102d01c00b0070741070300c02c0501101c1320009500c2c100244d401080d80b003203c6c503d03117801c1440e17003e0f0424 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 59592377 1250 59591127 59591153
    0x1e050402210d0f0e060d09051f1b03142a0301060e01030b030102310b030708100803040f030b04060e010c02030702030f01050708070f0203131502010c0206071d0607 72
    0x1010b81030400b4060401405001c0c001c0142c010401d803c0075800c00c1e562000e045544401c80c0a03000203c170201d92070058280b92100c202380080c2070840984090000c525042418503003501501003028a542440545c2280c180d614014000381d800c0001418a062640040d2032a0b0000d41c0041e800b0b44858006100c941d100740c00000000b61016016151560903001d03624800c40d04a000f5402d00c418203401030000784100b800004582005001c11310b880b407c3c0c0c000000a40030071040b85603289081c4e14050800340050b500010350310000100000c8280000c0f040c1d5040d1100d4002076103030a461034680901c0d40340041d0050f18240c2d43e42e01e68448000d000d03c6481c60710905600603540301c10280c010581813409040c103c4c6041d90426040090a962007901541c0c860880d040001c80014140c030100d01c2c6002d0000c0004031404120000714000e84026940101d0b031000f54000d00c00006051812a05d03030f0b8068a07a100410303041400030040c2207092542c0000e035200503200f10305007041603c80308155084 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 59593627 1250 59592377 59592439
    0xb03010609090b0f0f0a02090112050702060108160308040b0a0302090d0b0a0605030f03030f04140105040506010515091f02030706050117010e07080c0d020f030d02010f0b03011e050402 81
    0x1882e07011604110111011a41c8201400003a0489103040360b40001c034a000180320041c2c1c107600180c10412070b03010307103540c0109100310f04041186240001c000795030780340e007070090035007a01c904201c101c4424501141d507004c0d44d500604441c18035292594900341b9400441031181415001d1200101503168400c040300d040e8002c403100352283c01e100381d4450403240140c0049020381c214181c00c03004034100000f04c80d0082030061041c046036845040000001509100070781c0554244800d100a2000c00945c2c1810b81d20100e5070520402c40048003140e0724414065196000b140c8440310003000340c0d00d005120790007626401a0380c80c05070142e0b18402101c409802c0100300d0800000c00c40b0000c802413017524001c8070050000d00000381001552603482c2d0700c03a80101e2054150611460031901c2d030802d40421100c010f0121070641c905490007901800c071043e00021214a418984446407805014a500e18450040744005200895a5400203000002c0042c0d80013401f2a0b500080e2002810f0041000d681d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 59594877 1250 59593627 59593631
    0x32e0308070b010e09010c2a0209040c0608070f320f040f08030a17060409080f030708060418030c06060b0f041d04020105180103110a030b2704150b03010609 69
    0x205291140003940805440d14409a1514110848541c2c0001e64000e908c240c400c2010030640e00a54412152800f4940094202c030005082c0410001c510f06d00d03900741e400f04c2d10380701600d55820b0f20845e005404a954607001400c581c4000911980050320345500740c908402d00c0c0341d00e68400507035036996030007104a00400400020100850b035400c540702805081140081c40c50060200f00082c4002c0c02581789840151030707000490b455030380e187c0c4003010313480e4003011150700c809003000f2586a03600304a401102240d0381c0350005e0050320341072103114500c8500d20162400e00b845030728111010f80200b00c04840c0982d49000100e030030440c00001e090000003100c100360b40d690401170500c0c1981464826440c0c04030000c0d080c000143c1e0094251480041d07802d038125004603541004a004e400507a26a899003000020204280307981600300440c203034000c3d503c2c0001b042c09400c1481031108110244241c0c01c61100101e00000c0c030403171052040c0c0c01c84001c0403039408011f80c0000d08540c015400130310107503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 59596127 1250 59594877 59594879
    0xa020a020102160f060807020a050d090905060306010b04090e0106050a150f11060601030207030201090b0726010305100203100b030702030d0606020a210203070b0f090f03032e0308070b01 82
    0x980d0401c265203c02d484414004a072038500306500e202c3d1421405800700b071203210800103481c1c038420400340c038500b034000085484920000c5400b0704014200d00840f0800d034180000a0050b040001d1858100d50183c107020340341515000140c0000c020440e051100d95481e0400010182d503803071110005000042d42c0b101c03003082c0a03040039000c009a5050041401842d01c0c40c03200748400441c403c0d40c448000c1c03c01503030707543c103500c1d08900511141c2002070060754108103101001ea0b00144410b08100101d1011030008010006440c2e031001c2488000c090b607100840070621b0b85066005190070a0003c00e80344940d0351260842a07480c1c00c1140c810005034008902200b01c44a5801144000c2507240094480c00855440d0455440d040f801001c4500000588428201380700700210340320160003840c0e00500d4180201d0038410305100342e812240318403c00c1d8115900d4400441102d02480c000400e41c03071601034030600c0d0009020540c4c2d0f14450007601d0700000020610400c000c0c039400c3d1107060100269 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 59597377 1250 59596127 59596129
    0x50105030f071401050a09150e030d02010209150d09020303070302100c091d04050c04090809130b130506040b090406090615050a03030e0f0402040605030403020c04020708030117010e01020a020a02 86
    0x1100040810601c01e5001041c20082c1040d88409942695000e103811959090885402c4d21403881503031082081010324003031401001d03448032410105410403802d80c1e0b8421084540ac82c01d03400b800440962004c0150403540e21803142c5401001d040020703c6011513510070b42c2e00001d04582041d8070950158000900400c1e0748580e91107424110f0300c2600f0201d103a0b03401c0001182c01105c2c4c040240540200e00004a028400100051504200b0040c0b00340027829040c5000d14454005c5419640559401001001c6090031400303089407c00028010200a54214441c1805800003a01b80e5030001d9a841c5c1c06c14440c0c0390000c1c0188528096030001c0345013040c0d4030300f1034112a00700040c0d40340902800070034000f03070342c4102c070301760880381c05240c0f10b5641c43c0c9a4001230707804406804450780c0507100140000e503113500030018500c038070701903002e4900c1120b2907400d00043e8843c2440040242000704014080c40da81545d80c080c1002c1544000644500c41c80607050072a8810100280076074001e441c800c00b1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 59598627 1250 59597377 59597383
    0x90e041b060804060b0a0f030602090d020307080c04060906060c02100c0b040b0108060a1a0402091c03090e01170a0b130c031b0914061c06020703050d0609151e03020604080105010503 80
    0x341d0314180c0e030b5050001d10340034213441c7d8498a03000080c00d0540000d90059159156490303051003079001420385501540e528801c03551944401086802141001d00000c1c942101d8498801218a0350700d490300c101d01ca941c00c0011080c1166440c0051024145070003011a00e02c0e108680700758030800f00400194141640f0614000b0b000344103440a81c105205204c2800c030703451501d10482800da601617141c00708400020800040702c0c242e45124122003030600c09140d840400c00c002c480c800c03003513017142c1d903250f0042d880c82a040700750001e43c941c4144040400a4980204a42d01080d02070402d0014142642c1e40b0414003401d41c02550320320f4904006140301100407000f240108070b000020000118151400300c4a83c600401c03091103420586122400003c9040c05001c5980d803010046545540615000d000d641100e03d000420614021012030400e445115020920345002d0003030001d1481e1042043d07026848180c001c02c0c0e07031400000040103849090250018040004c0040352070341c101400c1c146 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 59599877 1250 59598627 59598641
    0x30d11040311030d210e03030c2a0303070c080c25060905090c070206040308070c0602060f0403050315030106090603060b04050601081308090105120108010b090610090e041b06080406 80
    0x803081c0c01003d581c0f10380c2a08039240303508800200171030307074035440d03400748081c0041c07100050848850000004008040f090b00b001030006440c0c507910301441010a6242549060000e4400e5074660310401c0403030035081c00750700c94a60b96481903006910b0043c0c42030380c2070b0038244841101c465201c204514100803a40047c2103001604503498600e450624001c0059080000904450000301c40099200203546031042100c02954004501a540301420300d4424a0300c500f0744190303001406004041074075119080da40703070301454043d034a0500b952280076a4418071604c8801903989990707150400600314100d8029000298000e180010f00250000705020078ad603c000c012604201c414020800f80d980302162280d10960411101601d45481c200181c4903071190426071445c04e2441d000006912105411007251044142d42c40c003402d03100d120904c2109000a09440003046143c04140a01040c200e102070f03010f40201000d54055088410160900d00e050708001c00040c03118013040107000c81c60203588 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 59601127 1250 59599877 59599879
    0x51203090a060e10031107050304170d050304021005030a090b0c070507090c02120a09090501121505060609040e03070c060e0102071401020a0303051503010501141503040506010314030d11040311 85
    0x881c000600703000280136400b01c04601d00501d641c0c0d2502c0c80950f01d2107400d6039102a03000d803c4070b90700c2e0b8641007044860b40300560000c0941c42080718802009108a043d60300641e805004c0002c1c42d00c4c042d80c2981d1a070070041003051f0040c1e0b1400030f50003091054082c0390007503d864041c20307607860950806d6414a409074114880e601c0c140b0304280401640028040d130319843c8203d1841d00d504034001c0031685c65000354000e4004070300341000820300c08040c807039102c8041d2041580d00c400c9401c000e104402e9600c120340c2c180e4080020b10606105091a812a9220702d40600c240d0303280183c20390700c50117552000d4104200040803080b5005103540c0410a036000307400f9903000e0074a411130b1f080c0001e540d04442c62000b002c01d82c94101042100603800d003844024072004000b030056603103440c3c2e154603404084000fa4811800394050030020b0303a510301100e00030b80c0c0044c040e21580e03080d522401944842c01000921901c030400a0078000e4895125640c40c1d501881607955031645941003154680b0040c1c0c2c40a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 59602377 1250 59601127 59601137
    0xa0908150105060c10091a15090a050903071a0406050c03010305070306020a0c06290a03150b030c130c0e01050f0a180b04060201090212070501090b070c051203090a06 73
    0xc036840c0c80003519040c11604200d0f0100d81d502d106034480382c1014280001d640900c0d090100d42c1e03040180c03030a2a0809015248100300080e6a041d100000100d0700f045040d0300302000502003860551140c0045500c2600f8804480c60803480c0c0d035400700d40080e9080b03c0c425100f8810700340820840d81c1d0159540052841742010304550460300c038592140040d1000900b0940d00003121000b5502510500600702e4020b1801c00c03602040f44809070055440031480100d0240181c80c448107850410448010340e0b070040741820114040016020040c042c407540349506100b55a14401b40741e43d11548002c4041c181c2401203000b801159014044119080300c0034140403040c4091102005c05405403032122506192402e86090000441c4480c0c886640080c02307800170000340400c0250301500246c0c049071085ea81c9095611200c40741c05d0301c61032180607003400100300803c20800020f1580207003070824002e030403200c40c8070b039200000380040c00b00011210b9140c01c08648840c40d4900160307020300900f443d00302 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 59603627 1250 59602377 59602393
    0x70c05040b01110d030b0307030209011509060305070215090102070204020f04030c06050f09010c031404090b13020a14030a06080d0e01031b0e0607050a0605071e092909040507050a0908 81
    0xc03e074480d240c200c03802d402c140d5280c1d100070040c0d4041160b6802140c000e048003401c1d50712501c5080311445c7c026541008556020000034070a446803207403e10841056002e071603002032034800030b611032401030480e040a41d004c1c001030015036150b100070400307c1080100c03240c3c0c80e8618903091940284030303070002d02402418019030a244450740101c0d48114001d113007140ca041d086203019199104c5551103484501000308000c00c1c01507255002044070750040721498600080d014440003603100b250f480e20001011482140c0007984c9003400b454005000d0035000c650340d038940e907060b440c183d002c01c82c10b00015011140c1030010b503014840c480409804107025581e00012001c05001c4080802060740221000141401841410b20004003071590288040c84203060551740107041d03121106030045442d0a1403c0e0a40c00790040080b0800c4803080c2e0b52007451110b82194411112184000001c0910000c200040c61580c884c4600f81c80341e621619030039215101c0400040c00c14079140c06c0340410358003040c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 59604877 1250 59603627 59603657
    0x100608040f03020a0605090c0301240603020c0a06090303150605090f0127080109031b0302100b04021b0d140405090f04030314040b06010f050f0702010c0512070c05040b01 75
    0x80103a03015401c0303144a10341101924007245000e6a0350b41c003502e2240340c001807040c039000c0440c1c0b41000420450080c0450070200d010130029114100d900e41c8041d4000b41d0410143c2c0c0241c024210003000002a02d60b4180240c030359205aa0078480c0c21400a50740c0c05510001d075510303030700102c06810540f40590403c001d04010a01c01c2000d400ca0364140880c1e9002c051489201500300c81045100661038044583c3c1c5030145d5000e086001022004608d906020701010b0f1842441e031500c4076015402415411210003a484c02049126041500301c3c2c4c00704100c0c0c02008694281803a00707686c09006007103003071800318010200c8261501b84250410204410040c0d5900c01001d260842c03a079442001c17850310303030346003d80c010005540800c103200e26400411061028038800c16106544c2070300d41e601620203140007202c180c821107401e03c1d06c400007800190b015505c42d0b01071b50300c018890400c0728a100500041c43d4842c1c0c014007001c03550003150070303020700990500c5e00078094000030070f090546501c02081 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 59606127 1250 59604877 59604887
    0xb07090608070c06050c0409060f0503060c03070c110114040e10090c14030a0204050a0b0703020f160308070224090f030105060105162f030f0d020304050103021b0f151006 75
    0x142002e01005e80303a50200340d810000400b00c1e4014040007000700152507a0f000410b64451062040300e00c2401002c0003d295403a01c5403c90348520400d03500c900b040b00715a03a80c00480304464242c81c1c1001300003c0c0901c00840504002c00203803544629000b4140707018040c229000c0c80b00d8010680c410f0400302e400018981013441e41146d54181c281d596165641c0708000c100a000e558820fa51004d121040083c1c502c640360020720b4028000c0d8262001845d418400b035070341e41710b000701681c0e013440304031420070110b584170000c0c0402d40d1000b40002d0441d103824101000300c03020018259260b0000085081192400080600700c2500581c000c4c46140740060002c0c0241c0901000003801741401d180716010441c030502501c140201341c140f001c00c1c042c040c0600b21038021081d00300900911400901c00d020103000100301c44103141a90042d0320701418103004601940005100801c000c0001d910004042000e2113030006060740b001c010046101d070f0400d80307589410054000105001e8240e814001c5503444 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 59607377 1250 59606127 59606147
    0x803030a020903030d0906140a051b0d0e0d0810080106030c050111030d02070c1809050a0201050a020109050109050a06230103060b01091203080108010605040e101a030a0b0709060807 80
    0x40c04010780310b00003038010904610468107168038003803422107030740200080ca5100d14042d4010b400e082509640382000102100c0c0141c4a942210b4070905820f005406101c009140b001c955010101d03804034510f4080d45403c094509000214000c2c004001e402d2044505880050184a00a002c0303607145840300c1080000c0e6004050401c0744441c0380c40100d2130100211200318040e42000c650b288814180940e4071400c0740520340105d100720445084a4400c2c0c0500a165500b00015000c24034041e0b0040d41d00d5481210214159504d426005001c18000e204138802d20780a00040e04004130a8130b801011552010000302420354004010140b084a0708956815282d02c00400034120103008016103085100350b0110442c02d104130010010164044040c5040350600780003800500d41710010002580c100703850303d91046d84460094400ca0444ad0000241004104aa13030520340c01940840d05040c4103a07415120514507800b4018055400f20510005101626140c0d642e810070345802000c400c55 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 59608627 1250 59607377 59607391
    0x607121d010915020304030b0103060b0a050d020906040c140a0201020309100c090e09030409051501120606170a0e0307050d09120206071b0e070309060b030c06030f0c040306050c040519080303 84
    0x40e0100d400c404d00030404c50340559000180a201585c2d24a0810054199110f103540203080e16500052681000826000801d038001e02710312190f9a010188001054000b01c1c03d0204401d82d500d044450318500c000303105026a0794000769580c904100058a065114115016007502d0074803c440480e0f40030000d01c0a41e202240d542d0b410f40c5500400510314040ca0300450444c5141909000400241da1181d0603101e0003070b2100030710480c0d5005180101c500610840002c143c02e0580e895003c86110170150f0f0225090400140c0c160980c104686590401d003400c50b00c41d84004503c05009d82c00c000040010031000941c0c826402c00399001c00c110b4024820f005200e218035010042c0040e103e08445405001e2660754007240e03180c03424000b4058003100c001600c0c090b15000103282c4500340410420442d0802401052035900c4405080d000c2c0d80f4000d221000c0300c1c80921011001550074000c407409005101446038490741008200800054450b0551810288081023000682d00100589a100d22 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 59609877 1250 59608627 59608649
    0x140d020603070e040f05090d08010303021f0e030a03050103140a020d03050705210901120213060c080d0f0203010504050c070b0f07110601080f061b040302040b0f0607121d0109 77
    0x124802c0c20303a05840007150542e07102d41403003640e0000c00c12690010348202e658200301c1e03000468400701551480c0c0c082c04081d006030404040c2e800750703013413041c1c0e0745031164850b010007c1c600e001001001d080d82c00007004000020780b100010820700c84915100f45c8164605405403030a506035030f00050784032040f081c1c001c090207004150b0805000d800d11902981e4040783d440101c0c1d076158503082c1340d25944600103840c0411499418036540211510984400c0025a101c6081c2d0074181102510000c154030382c02c07030307040104004020720100c4a003e0080316103a05400503880c0c0d41040c081105843c001852245c00c58414819580451580703601c0d00c0e040f03209640740d1400707a11195800c559000800f60b0b618868404c2c24000030300b0240000341c41c12109964801d64026403078407402c00505400030074103103040e00024001031000d0b18190340500e1600340010142d42d00100c1160100700903030410072007624981c0240458800c1d072a04054001210840e0160740002d10f042040040c00f0b50416000c0c2d001002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 59611127 1250 59609877 59609881
    0x10c0906020327030a0308010e0a0603050c090a0e070806010302180403020c040f0e030408100e0609070306050a0b130c020d080c040902160f050304030512030714090102070b0a020c0406140d020603 86
    0x3d40c02141c8045540003a00f03440e00d0703500b10b0502414071203013072040010500b4028000342240030984551015aa0700001814070b007561030040000c00400548000002c55840d20fa80080c0c05082244000401c0c9101c09000c5942c03540c01048024840b0501d136841d0f021009003003200081d404034034085040d000b10b40021f0503200c46c04106008020bd040882000d100000b0302007a10b110005440c20700d0701c034244080c462110440486600e5500aa5480c1581c0c0e00102d01400016a5600001d500201c070100005d04c0e00107060001e4021020100c41002103503449401e11254cd03414421161003044a0400e20b800d03003041c0d440c840b002d100e61721800d80c681e640440d90001c0c5010381b1030800055074104198040c040381d103041030f685950083c07004658501c200090025811100400c2d28414000c40d212103035050035003808682190300c4a621241180a003900102d10384000a000e0f00f9040040e900610f4200b150b0b01c1170204950281d0406108424076101c0510260b44c0c2e01403900359258143d50302510f039 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 59612377 1250 59611127 59611177
    0x6030b130f080c030711030114012c0709030201080901110405010c0302010b060403081201150c060e010e06040503250503040b071502120a0605090702100b0a0302040f0501050102010c09060203 84
    0x51264403100424580000070f5594151a000000c2c2007518050056138281001e048201030072150400e00d407125400b541d9004001c80b00c41c1d12034280c080040d418200c014003000608140c00c0c00700484502c000704000c0d220920655a005020b1036014103500000c02403040c448804103000d02a900c1454104414506e507002090b100307420819441c1030107450740e40c4803603c900d4088450f80007115801407d00a280c0002404200c204108030f16071110346070080c40d07540c1070321454098100010825055900c4516104001c103080100a00c140d00030030185841d5561195840e1032410605c0306040d0039030078000c1040c081040442200d04070398002a602d5620000d030300d03004208403c408140b80c01e0300c1c40400d0401003c010300045034442e041b10307201040003e84070b03810494041c20a82c0c403200180d000c059410a8400c0a6010662000000380303103050786507987d40050191400c91181a05c0786456200401c12940c09014a0b13942c41000d05140280c1414800300940d82d00841307045c3d22982070100454018 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 59613627 1250 59612377 59612393
    0x601090e1806010f03031707080c070218040f020a05041a04020a2304030302011b210b03011503020a0b040501050706020f16060203090601090e0c040b0f030a030807020d0306030b13 79
    0x300c0c8142400382c4400d0744c2c0d2158079078400091480300b940411703c50a140d0005448407418103115000a48429005494044a940340c64000120407a08a049504140c1e040300074245918420b611480311880711801504c18029030070481d9208900807820100c0300c981140301040d0380f1070000d2050f10300503100d90000304201c80040c0800b205141000c803444a021850104800410542c0d000350002d0207036002c0010070460360009640000d0020348884001a410283c0e07405541c03003034030710724400f050303428841d800203003101da40300a06141c4610050301082141003110009004101640502d810180342c03e001034454420280000c000f01d50000f440c0b048115407a0a48002d0b00e1030030102030b0301001c0c40c58005d0084d0b0041e00c402d03140e07101d800700016140905014400503002c440002d003488400349824480070303100d0394964a501103011001d950711610304202c0d042416010740e80d040c0c4142080e8501a04102c280071990007014204101400800c5003e4443c0360030100d94070a00542407114206150 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 59614877 1250 59613627 59613661
    0x2030c04120b0403030e03040f1e0302030105071d03030306010503131a04060501031505010b390303010303120908040509250801140a0e0417040f030305040e0903030601090e 76
    0x201ea955003800c40d041c022101d04662046109480400072150001280e55503400380d442040c0f24941d080b007007440b01301d6500c6809240052041400f580081c6c89a002900395141252070760b001a40d8003a03060b0f600d0840706008000711030294003461a50400000090451000400314881001c2c02041366041203d074611007600d02600c0043d0b20f0070b40c1024a84040609002c1c071050b5902480754400c070700c114600d489418122020307600114a0045c04081c21419a1100803a5070440726800d038030380d4040302010610280009045025550f01d605618010300740480a01300415510300c0e01c170880d000206036504490503100c040f038000c0f43c6a80c8818580c80741c8043c2d900141c41c62a18504400c2e00550480c400c40d050b07440d0110208040c0150780305005072413085208001907860250f01003030100c1d940c03049010350b04030040d129903d056105c4840e4040324241740e02c00c50024600280c104034001100e1000d075040100c43d4080c62841c1040d40c002084841640111500050100089001ca002d00c2c84840 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 59616127 1250 59614877 59614889
    0x5070b160b010306140f100501030e0102120405010204170a08030c0d1d0c0109050d0506010b030604020910120b09060f120124080706020a08031513060801050a060f050a0902030c04 79
    0x7403001c1da101e01c0d0410160034511100c0c0c014a00036000b00701e6400c0604c00043c80f60100c0071281410a00c1d0071300440282c040a280030319155801c2242c010303605001e0003942d00c1603024800150b583c51a125582a4004055150603016088600c1440c0080c0d0317500c0440f9000b100b2204a151242001c036a0b00e001007561201084203140f4405040e0f915030300226451142c0f605c26211030f031030580d866043c0200e2440d03c1c100103040350054130040c005411b03220007850304481c01420041c145505000881c0703c1010071407040020030ba681c07080080c1400903000b50302120005480c00b00141c10450b01061220444140300f07485085a08400c9812100952000a298010303251110101c0c030310008009119000303009c2c06046010b19600480c00600000d0200700c01540008403078555618040c800300c000c0c8207058020f0b40503c60b90406040d01a0b14003800c0040c0c09401c0000825042400381603088440d650711104161486180804c0140d42d041680b4044412484001d641c0c2d5485041703010507031003150008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 59617377 1250 59616127 59616143
    0x305130902040909020a0807060c201206191a0d060b0415030209010806040201020304060804050c0604030c150e010219020f0301050723070f030f030207060e0606030c0a0305070b16 79
    0x100c14030543c01030b0000740c3c000d4401481c1241c03684103203508c404860180c2c0020905031242c090002e11203a040049c000c400200c1c050712242d038500003401607200c4a48000b0309034096400d00580c41000c8141500c0901c2c030383e40400c041c164103040749100d1921542c60b28401c001390300030304007444440d0304540341c170020041007004074036030011112151220300e0205034001c6000c01e00106441c000050f066024a805800071418240750100c11100c240005000712000e00840032610790139128400680701961080d101144180e09112418a0038096a088141003000004c000280c0f071746c02103890085040c6040c03caa10004641c000f00769402d12000c0015050b611b06001c0209040c0d104403080321904c5030b42c040d03243d04146c0c45998106806402c50181c0704180043d01440043d0260126081030740e00c609006d4146280707031721020100c81c012411580741d40c02410400c0b1042c1340601205600f800222041d004250840e110b01d0356072105400b41d4180d4000c009050591580c2440042040c26400b601d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 59618627 1250 59617377 59617379
    0x1e141b0706050c010614060306090403050403080705030301170c0a0e070903050307080304050c0108040b071b0501050405060103120203120117070f0906060806040209010c060b06220e1012030513090204 88
    0x1482d41d8424500715400354a003940201ea9440c103203038614100c4100900c3c4a086440742006c01a4444004c5d0040342030060030000040015200000381c03038a04e008802030354880d850300d41000700038038546001103a070342c0101014058a0344c03004c030503409071681c50b2a0300710682c0d2022000d54407003101c2d0300050031503c004600718007041421002184154800c000313503070844100200640d031a14003030b54010f02c0ea070f00c80300c00510854480c0d103110071406020101c000c003124154981c142101d40559090701c443c2c120700014824050385248800c1c4102e000c3c2300031440d24074510071050794648103024406001c18402007202c641d050410121002d400b1644400e4200e544d9424000010003451084801082d19800051983e150a1081d5150801d042c0c4450201e214507030b807450001d002003400c0c0d6910020070301200303101220b001000a1075040d011000109136003044040305d1004001001d60b6104107241d031041c41b0180c0140c50800d105645070034450386441034424000b80300c0301c00d5000b4030880c07880450 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 59619877 1250 59618627 59618639
    0x9060b0a091e0501080a0605130f0506040512030603030a0c020d02061210060e011e030f05010f0303200d051e0f04140d0203120f0705010903030c1e141b07 68
    0x440031980c11200c0c0c0310325a02d254005105415190244161442504040003800100b026a0032207903106155003a405940011035540f40d00303841c00c00d03106135a180e00ca44100700420100300702c11302020407550800c41c118982040001ea60b44a0f044015041004481e8410219252401039000f40d40d0700a14440d207450381d0014840358000c0480d01118107c201c08030004c1c1c3e480c090408481c0411040e5500280d6419001200300f0400c4070030300450401d42d503034210389481d0725a485001d000c3c100a150440b2001c4c55030030010496140030210441e002c485000079402d5510004240d1481c03d540c1c10310a40707600020581000c1480680d02c3d810340c41e00d0006000e010034480000920680b50401c24403c0c40c4208402401281c802c0f80d000250503500495810513012400c9c03018107090f9805600343e074640380a41d170b02c080c25035008002c11004a038441e20300c0394605400110791402c07294800d4268003804418040204201c20348032407131b0604800015110200414401c641789404140801c1351510303a0380d81 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 59621127 1250 59619877 59619881
    0x314090a030906050906030403050f0c010905010b0310050f0412050c0a0c0302090106020d140309010204090906051b1c0506010306090903090e090304050d02040b0f030d0309110d03080a09060b0a09 86
    0xc120005540c205010840e5400340b425960101005404581180e89070f584c01c1e107055100c80c1c8200900c075001e0025150b207031801d0041d5001c80b03100d00004180410420203052030204103400e0f50b404c2c54109002c110010b05240c42c0c07941d00c03c0d080b8a0b40e1104072010700c0e01f985c0701d01c102c80404609000340b98180381823120444100742124400d4480011a030380c0c424040303866500f00184c40001964079480a1510880b260166800074200000140307003940d201103010884a200c0802c40d412603c490810440011880e83c0b1030b850151030000503d491110361202c407506400050030059181c1e00c401151850f446544540080d105000b0200301113031b05c906025002411394468008003050440021364182404000c2c0e40464002409002c2000255800c00020b00700d0180580e41268007521003284603501044a05208912510006245005400d200c0e4250312034201442c0a02d082102d600000b0f07074004149688035081d528001288a11860030b5070191820700203050344150040400b107480c20b599 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 59622377 1250 59621127 59621143
    0x60204050a09020a0503270109030819060b03010e13080c0f0c010302040f051c08040e070f0813020607050a0c090f2712050c010204090f0b0405040209011203031409 72
    0x101e540920550b501c1684000364411410030070f00142c410700214500c80991300101100d021000410400d644882541a08441d94038a0036800240c40100b404000c1080307250350403100440100c1480a00c0c00c240c01d80040d448103120b0100c02501000c001521101d180e254000080d41c0042c0044c1e036594020200f0b41d031500740c0b48000d000c6014041c0900c1996010f44221012203d0400c111404185000e00b0421070003940c800302c05072403410704070f24400038074400004c00c05000000c00c41802400c1c41a801051180039601040c2800304901c18400015050144a00b046a04507a0b207a950421854020304205103800014040c1c208000c01103101580381d00f101c15102d44000c41002000007000c00d0390701c10006100700021007400c20061350042580e85d01454401545401c265146c0000d041c06203089030320542c03056429035600e940030074070a1000d0245d2180740c0421035080c02a82407940015680903c1840380340c404030305584d1600201400303508103030507410920350610028a42103106613141d20741 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 59623627 1250 59622377 59622379
    0x50601081e01090b010e04060e070801060815040504020310110306040b040207111216080705040c02010b030c010f030f02040306141006050a080604090b07090806070c0323040b0706020405 82
    0xd11800a01521446210108100d00c012040307500341e4a040b015100420400b56040e041041400104500b92103034050b1000420406410680300d240c030650003022808107070406003c01c054803041c0080d81d1820080960010400c0f540002c883c0c880d07200203484c088013048d1440700681000460450030b800040618401c00084e2000c0c851a40c440040204912646600801900450f9505241814004c003040c044881c3c1e901121804000401d81a0880074035500201e010ba106600500c141d040c0b85c02410440c400340d00091015a024000094903042e11030b03686810040340800c00d0102c03070312a41000502945d0f8010440d9980d07140c2c00c1c0340e000b0b498a0200c13156001d44600108481c007000060480880700d844c1d0340c890405511404c110340d9048043d00ca1a401912800c2940225082c042028007409080d100c1410350741c030b050307489818540300909200a102200710b01c0008250000f40803440c00c4407400e60700750100080000100f407030203250402c42d0410b101060b40700810070294014400e41300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 59624877 1250 59623627 59623637
    0x150606030509030708040306050606040e0a0905012a0e0402190e03010c02060f190204170c0307080105280e030708070501050a02040303090e061807020a020406120b18010905070306050601 82
    0x91000300c2e0075a60711503140300800d01c0c00200001c1020804030b40c4403c1d003000005299500d05aa500b107040700d03000b0b00b03030740f244800d50b5524914010000244500d06400c900e040c40310b21b440d00c0b81d400f5103124a02241106050250600781014190350726030440d1081000c46600030380040030365000800d486400c1080754020341c0303400d5240c40c800340001541c0340304808480c0c0d182c81503901c00350f60020041d41c524400c0f000580900000c40c1d6042e13110031a40d4102c42080080001708002000c0601c5c05080e1340c401042a49048240300840328001901d0680d0411445807000544e140c0c07540000400381c0d030b41e44090602010034682c0404c04070b03000800300140214002d000a4803010420400c038803551000074041041180c08005021038201c115500c01c4004005c000b07191603d041c201031000781107444130016042940108114074151040c1e002600419070b01011482441c1c3e81c0070800d810180520b28504501c044034054144e003508888695a80070f410385609030f5413840d00402525080c0c85d9a40821 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 59626127 1250 59624877 59624881
    0x20c0c09010f03080306010f09080a08091f020705220e0c120f071406071a01050310091707050f03040305030304030306330311030408040303030c080c03221506060305 73
    0x202c2c1c04859003030300e0700810341c9851510703164010b50b403008180200d001440007141001910040030300c13503150024007828266503540c500d00300700001c020b860218030206c048001842110540e0020b0400c003950320549140b4800c40358403d00c030195034814101c103803245045c0501520410804604d2020008090b21245076005a107445c03151164003011542201da405800308002200380c414240c8107040d40603002500d4080c81e61100c1c800500d00d8032f850350040c40d040c40104160b00301000b000740c00e500e0101c8200001111035840700b180742e0300c420039211750720350100e180d1090040a0014900c0d0302c1c00001240d942e25583d281940c3c80e03400454003603021920b4160006a2242001600305155454614000c984c4c6405550720322100055103118041554030080075103144100c20055001d180640c1c00d00d80c4540c0b0b50b01e0001c0559054010a000700301068062000440040e426070f600246034075584510085941ea8502c9000d40c2c521001d408054158200c08441c43d096000c007051314003607034042c0015 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 59627377 1250 59626127 59626139
    0x7051c11031b011404120c020d060212070e0a0b0f03040507080304080109061b0f200d0c0203010e1504170d09030314090d02030d0f020714030a0e0a12080304020102010e01020c0c0901 80
    0x35000072500070301b6040c410a10444254825140710b00c2040c0b0041c02050a040c040c0c603054104d0b0003243c01e0300c0742404804140000150065079030f40000100300c3d02c51900c2d0b0700b09510294140030301c101c00c170000340012010a041020502c4101c024003114411a9281c0790b9800c0824040d00000901340e900b245003216080241080f602c00c0c44c0010300d59141d14141c2041c6034022140402c0094408040e051201d01c1c01103030348130601540c5880c030910f035100b800008460040500310f608154651460f80c5c000e02e81c403883d0351071068110341c1c440d401070f0441240141e176440f41811803141c900c480011501d8484060308054069100703a5004c900201d10340c0d40b566500d0041396a0300215a131003005640140035001241c42caa030001548001094070150601c2920f5032100800d00060b004400c49410104030085210351160b250031071030500b150100304a070b151025002020071642c4010b0b048aa0000015095900035040071004000a10013155070300c0705417851503203038150340700310900c01d16141c0c00000d02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 59628627 1250 59627377 59627411
    0x215040603200405060a09030209090d110105160c0809040c0302030906090a022805090901020c0f0106060c06050a02070b01032103050603030909041a01060504050f030307051c11031b01 81
    0xb0a80ca10129149030500304030401c4450703040b4000c3d6108101c140c0401100684a0084040c02442008024075070014618405081c00211081c40c00d210f030b1400b420001006016091444000748038241914010110708080305548074040196400508207404044000d03130542c000c6200300e40d40c10a44000da00c032844001e031181c4c50300340040d41c090184180498100783c842e11007580c402c8022010b040b5140c2e66000314840d008112552012658040748101e20000b0500856880b180060020040c0c0e60400700081c25200501078050002c6030b841000900c0034100d94111703480d154215085510740d694900d09081c0000443c07ca607002c5502c2e404421118902034042c00340a10f00040245081c04c415a0510031000d40c014000d5441a00c580854248030303401c4461740d8080d0200395a01da98031030400d4113202c1c44041144030b942c02031780304000c9a40443c60103d091034503015003000f00007442c3d401300003c82d89e40550f180300d81094000003410b2030191401d403445050711208c0d00001d01c80080c800c881805 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 59629877 1250 59628627 59628671
    0x21060712090f0204021c0609020d0c0903050d0309060b0402070c060f0521040c030b040501020304050105130b041b170604020a090209130207030c0804120b0a1b030207020406030215040603 82
    0xa0b01c0b54115000c00603e0250094180c2d005102c1403203074580c1c0100c2c3c5007400e0b00d51560010f54902d07070009104828089070f0144d42440d061900b054211145540d40d695a510103400142c41015607411129042103104d400400100800500554640c085410498a0b10080748034483c0441c0c0310108030000c0600480948074055455080004e0f5810609010342540784001e2040b03030400220030300440015641132000f8003a03401880016103074a0145000303802c460020704500c940c004208000030024a01d60805584207038008031803d6000344040309130480001c0d40d008070b10100c01e60030421600d05000510b26100c4c900880d0a2039a950b51030074103400f00e100d1101c116803ca0b031010008a03c414141d002815428440d180980da040e4250300c8607401d075040342c0c001607401c442c000180e905220300d0034409a08019480d0003001054403600700b4142500000e4101c0c4207154000c22144251364443c1c1c401e200460b005000c540300040c3d104030401c0681c3c45800f4000202e46404403010441d041001c010b5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 59631127 1250 59629877 59629883
    0x1d060f0c041206060803040e0f061e010f021501120605150d020607030c0206040f080d0f0203091210060902041703040b041202210105061507050d0e2106071209 70
    0x7403406007005003078808001d071010103031400d0751280300005508004200500c01400358a04200e80350170030142c41c46090707101038100d40c0b154690b628465508603162200805030002420718a2001d607401c41d090341000320946011100210040000442d019407802100002d0b00c07400040010ba56400004032510307400c66185a000402c0d40d6174080141000340003014014002e04100142d4460760b40081d4495200d5000030301c01c0303440c820b0204101501003150701540926418590345a10415070004c0d0b4a00a2000e0b01c2d100f1050b0740700800000b8028052000e401c001e505041c41400c0d103900c5024060350240c450031815400000b402c0e590501c000c820b031000d4072051411203142914108481e1102d07041d014060380c0c0720315944481c0307040854020485c94064092400400c0c0c41c0b810408001c9100c2e07100c490340141c0b0f5020072800c00003c00104800c0c11005440c2810340300000743d140825440302c8001d0039183c114071178854280b07590342c000428602c141c1c000e030385010700074521601100580300351103402 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 59632377 1250 59631127 59631151
    0x140c0909041a01080703020a06080f0a0f060305030d0207031b0c0612020f13032306060913080a11060c0c0d030902030c031609060e06010c030804020301020d1d060f 72
    0xa0a8642012299001405810324180c00111400c441c0c1c040d0000382d00c40341265210305020421824207003560402803ea034108503409141c0000442e848940040400108640d128a100040042c903407001020395082001c894a803041c95411000950082400b0340105210038520035a03069280464202c0700c2d031001e410381e201407401d8000d6507115a0380e40c1c2145425000e010004503081e040014004000312200803030141855410022040c6246005080d014440349114284141001910540002c4240ca143d04241e42d1406103000e04d01201c00010007604000490a081c9039010b92120780190000d030a071340ca203440c0c0030304805080c8621400c200280e0030144a54204902075030103080d0460018056846112130500024100040020007030001ea201031408c0c00070b10f40620401016100b00800e0404500740030340040c0c561200d0a00082c100140b1000285c115282034054803c03071500710b032051010005a080e11561414500c04020b800c0c810706c00010078068440c212640120b8501e0b0340c0f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 59633627 1250 59632377 59632387
    0x703050a0602030702190b040c0e06031203090c0901081b06090a030f02120d0f090803070201050405100c0204051501110a1e03090e010e0105010906090f061b05060c030a140c 76
    0x54000607410082c01c804c2076005480c0d0001140260010340c3d60440e00c181316080041c074003841c140f080c1c01d41c3c641010500420010401c24191000034000e400c0c0d200106109480781c0e03035154858039180c4044400b6410080010001403209000a00030f50413810025420500503c0d900501c560b03801061103096000d9030034041000403e60511039a100030380007034141c440c1c514010746020f103440c940341411400500c04400303080b049030380000000050030759240130311b140ca29180c000a0407400386001e040d208a083d85c01c1c24a455000700c21406006602030014401403608940707501095010402c07150100b40300c00059044801c01056071201c9582c448544041c0c001c0281c0c801c0c0c80a0402c481c11018840c80460100f8000a5803c03402d00810074010448810360401c000140400316591182d0b003480303583c030f1080c03122101d4411090256030380b41c602201c943c403a40451302d2000300540400740850050400740402696507400640c4201c8003154240842c00700c3d0031b100302d003001d0121258408801c040c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 59634877 1250 59633627 59633633
    0x6071d09060102030c0604030e0f0f060d020307090f0e01060311030f0708090a050304080c0a0e010617040c0b12060f06120a02030c040806010e040303050a020301051e0a0f060512090703050a 83
    0x824075040541841128100992181c081e868408161030030380c0460307511543d00b5960314101d40310082401040d21032090300d80100008c41d8003402851f8420880701d0f004000101458401c01c520303c000e113080e0b81030017109544c4856140c0c0c1c840b02801840c000905044403080e45600355400c9900a81100c42402c809035184601200c4241d0080c3c8a400c090050140000c0407407c1023000c0c0c405885c01c00041e040011802003003044180741c1e44e0050420782c2c95400100b0006030420b01e5034070300c0c2030488001003c6580b186042600c000e61a0000f11040740e010449190707580402c01d1a42c4030310025101140000c0d103010404c82d090255060f088007640700c2100049003c285600516041804045000d09158585220a0410710242c001d0004d441e02c180401c018941d05010b01a08454601e80031441d55040c0004030713100200100318501915507186e012081510790150b90001841c04099100c00141c862030b00804c81c2c5c0c0000120216980601c000c55200e40c00407e2002c1100c1c0d101004140303044143d6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 59636127 1250 59634877 59634889
    0x20301031a0618090313031506050301050c070b19061d090712020402130305030c0f06100302090f100320031e03030f0c0409020f070311070605030712110a03060806071d 74
    0xd00804c0240000d214141580610b06007000265104200d184181d007958001d800441d046540185d00c42d07810b21040c083c1c2c2e030b0842011542d5294000c01c0d584140e948864800c0424000715200c094202c0c0740240c0001d0f00c840c41c0c0c450010881d01c001e0300319080d8481c00300740b554901c114000c401c154030081c09420f0052805500038120402d25900700140d071b83c2d03a6120b050864108103d001112b070800f01c4406520f41052082d41d90240300c80888a03505030858000c00e03000c031070051440c40d4101000380442c0100e07010b618540300455001c420403000d0031000c080c820400e00550222800b91184103081420310b03400250324030301d4080800c011415030f62120302502260001070304c900c55401f800c000c08a0380c07407100c5c001881e4050b07000210b580d4805c450f1a008001094064048929400c1400140861075102d82240e801c00420300e0500c0480445044080040c00c24030b920000c2c000002610f8110309400d0f81000c400c450480044e61a244e81da08002d03220141c6000c400e0440341003a204600051900b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 59637377 1250 59636127 59636131
    0x1302040507171513090f020319050d03591510080709140109020304020d02090705041d0f07050406050306010c1e060902030705011403040807030e060706020301031a0618 74
    0x8021415a480c0c48503130340201d421111042d61103a1807148010250708003040703507043c405142626800b900e03100b0380b0b601c0c0d1101d1500f84c0c83c004050b01c51056410001480c154001d51102e0b140400c2220320b02a00c275407505805840c14668406000e0501c0350620355181c01e4034001810301000703000840c00c0003a60180401000340b90b007018000404001c15100d10410000c401f4010314000002c0503072030790424552002c0141e100c51703070683c0100304004c01a21070001640310651305540c0c0e03490b40e4940707103030503112402160044500c1c0c0c00b0980280301d610801d124460b001d282c0d400d050103c43d85a820040344c2c20301c19800399001044040020408a5105100f0b035040c2c40d01400c82c1e1a5940da0424850940c0301d00040f007a240300e07807103140d56415883d00340030b884005e00007400c020102d500c004561141c10f0000800c05008400041149802e16025a0510a15100082ca1955640d03a10314110000790001c0c08180d81030700c4c101209255003440002c1c0d02c1d004220040008900ba207444591000c50480 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 59638627 1250 59637377 59637379
    0x3060b060415022a0f010c03050c010f091101030b0307060c1a0c09100e10080a02070b0108030c0106050a060e1009090e0304050405062b030507050613020405071715 72
    0x800c40040d03901501c2c60300c2100350080358080c1c403c0f104d003c2006292003c1101510001c550205050103541d9598003040207440000c1c00c01e00105181030409a505004682c05400e9030350801c26404010b4815520071104a48a0204841944070399801101111b0500380701d030780c044c1e11080341841000d00034640c0d40385ca00d1155800070040012441da481300140b09036007004941c200070650003400c7c44c0080c2c8005c0320060a01d00308410342104000290026814003034101842104004587c220203c0c1c0c04540704650000000201d40d6900c000c0265694009001483c10b54139002c07020640f494440305145c203c80466030341600142d0f60400308490045984198014410300100000b004801d40c02044242c905e18805903880310f10b03140c18003040d00c3c0b004044510503450040d82c840f550031100f1031041b201c812200252a01905c5113030640b107610030703180054068030690080100740e4001054000701c4500c2a502400240c541c7c40090b500300211414110050580c580003894080100e408031745d05c1d80d8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 59639877 1250 59638627 59638639
    0x41403281709040f0b010e01110705040c090503060403020a020a09050f040305030901200a1d060d471804030f090b070602190206011404020a05044a0103060b 69
    0x900c00003d011910640b00c003400040d01e540c007100280d80c1040500481d10020300740b09070410a20001c440d128141d070f020301881941e5810320380c541b4611030400361003c0c10000d401c07138020b070509003000ba40d29205e1003c00c074490f003090200400c042d038480c0a41400750a000700080c00b130f606c5a54060300c03503800045c070f4503403651358800c050b40c644845c00149a025010101203a60b640300c4240b4010141480d80c1400068115001540709080d00c540080b41d2903000b0701d41001032400c400d400300f6288482d40052840f1004011401e000e0b01c030b1b401c0014268072008030300d07515031104807080500c82c5030381644000c07201d0300306040d0001c0c0100340100c0041c8a44043c4d807910510b1142c560b05c0c21411074001c0f880c1034445940c0411140c201000303082d4940885074150000302411b40c9001c19100944960095040c095a00411034620720b6010700141c0e07000e0500200402c411a00e801d030741e91200303503a08502c0000710001d03050020341503614800d4001d1150021702100c01c00e80c203588510010300f50b161510f5070002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 59641127 1250 59639877 59639887
    0xb130306020a12051014030307020108040809041b030e0706090810051810050603060105040b09071101020d050702010209190b04051c08030f091c080106230414032817 73
    0xf09244200392052146104440186081254442200b80e4291101d4000d41c001c200100142c3e0308480c02a600c6a8884005030380c4041700b60100d0040d055546009280201e5048040c8e426a010740003000d10310000000c8500c503130780e590400c5440704850710419026410443d0a050043c010340c00050b40401c40c41e44aa41e00802100c02a15160000314005c600ca07681e0710074094940340920941d80149000c80f81070141420540005034160310140041060240c40540d4035501d80c2c082d01914003003043c40d50100814903109038003901030741c01007803894401d25600c44005602d03850300882000395452072082605060401052002d880f45001403240c1d00412260320000050300340d00158441c80ca4540c82a4030b50400508280c03400782d03102c0c0e150040c1c40026582c4c401d1a603102d42e10504480151800000d43d803074040f0811180c00407021180e02029002034041454080d0707034148008070034141e08445203103003016807002c41c01e01c0c1498200908040c81e089000410540b04072001281445c4c1c5200c0c0c60030b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 59642377 1250 59641127 59641157
    0x5040c08030f04051302030106050a08150d030c03030c030515011b050109030507120e01020a0f0320011b08040c1a0d0501030b041109040b0a05090a080f040f0b130306020a 75
    0x64114407a11030302e200c0009010b124a040c000281e40c10a07500b802e0550655040c09009443c40c0280c01d05201002606000608101c640304901d00f0a408050f2401c2901805410024000c040081c0c080d401b090900030580711242c800e00c5468402d1500c20440c010f44c010420044440345411aa00d040c01c42d1400c1c0d148012807400e1148091283c4070b030701c80c3c5680f0002403401420b04a1144524010b009000000d0440d80e600403584881841d44a4030107185807480d49000e9803e00d000c0b079140408014022148909804158045003207101989d0303903003040300b015000440e82c000301150001c01c46500f1403c02c00c001e901003010406804160307040d180c140049130700441b04603207090f40243c3d608280e038003e01c8117014514000c0c07a0080001da0301c0044500c1e05032030303114440c54081c0045840c0b03030f42d40c000621403050a01000c034032507a10104255640c241180300240c1501300f8012456900f02e00080000d601c100e41e800c0311503e8405401401c02300346140c0307914000350400781007082030083c40c03c00d4a010b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 59643627 1250 59642377 59642383
    0x50a030f02121801020f0a0b0114040609020a2d020c120111070f1104060308090f030c0316030605060609150a0201021902010c02060a050108070909080c03031e0606030c0a0305040c08 80
    0x1003800c1c0f0ba4101c0070080c0c08080024900915a2440d19054201c40c01c0c0c000812101e0300038034103607105809085030741050340d070104004102a0748680c01c07071071001c1010340226501c0010840c030a900412008581010282509580005a1002005a40714280d17441e140d0410009007408408400000070f41007001140d0040d10b80c0c08210b044902800e440d075801d0030050000c540c8150301000b80c42c100141030440d80c541d500e605c104141144642070b1040000d41943c1d04211800d2410b80c050280c8041100405c03445060100c2c1c3d0104440301030a0000250840c281a800e50f50301d040020412100501405c070501b1440e803112421400b195020464520100210040c14001590303aa000095132a85008d00a04008002c3c02c5c004071181444010020030400107231250a0350346010000440d2760403450140303900e11134544075442500000c0100709100201040441d00c0b800111009186651444200708661000b220000c000020038000620428480e921203a4000d1003040441070098032845101e00d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 59644877 1250 59643627 59643637
    0x9050906190b03040605090718091b0b0903010b0303070203030f03040c0f180e01110a0f03091b030b010905070f030b06070212160501140306040c0507120201020307030c0c050a030f0212 81
    0x81d0402d40082840300f000414031407136a0003000302d00070f04055402c0c03804845402030920004504540c81d02d0f4008184440c10014508100d0703940120342c80141e942d2000140e903008030300820f100c2e529011302a0451b0401008030f0313640a50003006589001008060b40c5801c1d04050410b40740880e481501080500340e01c040280070341800d22030900b403c4100c02440003524940e0401884590400c00e8144c102103a4009540b410f51050030526241c10082c04220014414101e001e0151428561024514001003e80c00282c03802413030503070b1460f030300c91061300c0076110301313842000024603000880074400d842544800011540280a84c3c50041d040e00001c04200344140144165000006400c60b66460b49102c00d0040c0400c0c207100b195411910314080346400f008040c07030f0180d0780340c00c3e985400070f10031340482d11955400141d140c8071080d4001c000307000f50011150740020901c0d200c2d00c840785501a060396901c131603000e80100025000c40d90215815419048240150b00c030b0035200500e0f035090000544 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 59646127 1250 59644877 59644889
    0x9090303050f060f0a0302090a020d11120f010e0a0207031412060406080a0201020a120e03120d0614030307120e0406121e0b010605070215070b0a0b09070905090619 72
    0xc2a5420100303009810158040c0045200e521081c0105496851703001080c021290102d4071700f0181c0d80d6406100000e8414040e000ba56146007054030b0407804001000351000482003503581210f50340d200410701d0340c02428010f210808042d000040c28813140e0380c004040d5240f0074074100d800b58441211001894000c0c405c000300e6004000100200d50070300d481340030700a20030f81c80100805200307500041c1d00d52100b0364018100381c0c1405401110315025000a0314000d0f006002c4030405900b85661400e82c0c8c1168080c080e45c103040400000d01404221003100341400014061440c00c43c8550b10500b51640c1e1141403814414030b15440f00c0c59076200c3c40360310000d14001c40b0128413806149400401c074104990403c41c414281d07800701c1c0100e04641500b034152262814001d030759108a00010710345106000d81d8040a00c0c0c0001d1140030000340c0314106010324003101c0e042c0442a007190800c41c41d20400c448050002d28600010050362600064103504407c0c083c101c030200c501c2103154052a034006070445 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 59647377 1250 59646127 59646131
    0x302060d0509010f0b0f09091c0f080a02042304090213090606050d0c061805041d0105100b1c0204050303040905160206040308161205071112030f01030b090709090303 73
    0x1421482801500c0d8202500c1c030702002504002c5e000603404082c0a071229001c1d00144000401c640700c108050300c01d03086013000e840000604080d004005100905804001400c43c9003c900401000e0081d14143c8a21410b12002d005900f01031002800000480c01ea1240c1c9910302580540c4901e180d9802c10029440301055a1020b41000f0701611b0342d0f0340c0203600811034802200042441032420805844040c85d09031200b0503110040425942507400c0136500c980b404149020912000e403041c0300c1c0e02c81040090109640328088e52003c84038030b02c100c00040c8000c000c0070b181d6486e100040c07030400744440d43c010b0826441d440468595046900305c10303171a84d0740b0320500840182c0384030014022216880103008a18083c0e400500c030038000350000d542c1c81c00c0410360400fa280036584080c41c5100201c0100444d2402d468010950000100e141c24503003d00c50080c41d00c00c1d850012684903244031440d00d01c03a40d1842d03440b01034840c8000c02010550194500100b00c4e4005c0c2c0c051540d03058003075900 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 59648627 1250 59647377 59647381
    0x121401090b01090f050a0b030702071701020306010311070b010311060409060905040302060c040f060318060c0c110105070503030613140408070c050f030c01080408040f0305060901050c040803030a020d060302060d05 94
    0x3400303900b00c680004c450032104a104000c0d568414003002c003680d10354200d680c0c0701d455049082e40350a0540d0446008051000040c459003101507002c3d52042500340c0c1c080c400c07003c200b581c0b551184295200a001e90084100501c003040025a030700201440280406207082e43e110080c0d4116000c40d040100c0703441d01e450902c010326030304000080e0407443c0000070310720742454461000d121003224070031007007419103d207411184640020000d0744410f401010038441c1e1140380c1c000600621b06040c085072040c07490b00b0309108a5200f0030903500c030740f6848002146561170340070030010348000e5400000185522654040c0f0b624130110030080c000c522403c84035407108503d241c0f2625111103504201e01807002c17413000014540d80001c103248000c1080c00d203035050f5280c6042c13094482c40385030800140ea40092400000304040020b0b218400da0415000f001183c1b43c4801d00f040e540301703a120312000c0d64428004106801000d03801040200802c1c1c400243c1e0076038982c00300c1e01d40d8201c12400c1184035543e01c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 59649877 1250 59648627 59648629
    0x70f0602031b0f100902030102040306090501150902090307050405090c03070f09050c0a1202070f08160b0f130212070906090c11120d02070c0b0d050709150807121401090b 75
    0x40b80c0302c42141440c1c0a0003800900c4000781d55521801100070420684400d01d81d41503490a5046801446e044402032000f11034904049000e058104070030079041d0119034000410031468400d4a03164900103004d03008803450482040054100030b070200060303010350781c0c26081544e01001814003c1480c1c240d00e58900c1d00e080c0c0d01c64201c80c002450203d010750f0400c080202103501c040070100c0d400f400000141c13140451b09001d02644c50481d8000c0c91440e001a0f032410195030aa560b0600d584140042ca600e1394860003050700e003000030b45600c061040e00d16010f0340145030001c10310181c1d144210803101d60654584504045c1c070100e51241c406241c1c0c03402d1303144100303600810389808034040c48000c01c007004943c100d0858910840c062b2046c0c070365010030510200300800d41c90300000c0450b652036a80310602d09098100410040d5540004a50501d0001402c54a20610741e542c40080b03440d544000c0e0740d182000c0c2d5003a045880300f09a900d0b135a01c1d03410007403140301e40c0705401380204060009031000204 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 59651127 1250 59649877 59649907
    0x506130302100f0c0803070c0c030503030115030b031c020f0109060b12010903020c09270304060e03070f050405040f020910050a0807080a11030a1e15060e18070f060203 74
    0x5002c100400500c00700c00412941c002c101100150362243c2d80c44c0d580e6441820031074070360390400c400030071030104041d002080c0100080610b05840c1e2140314908a020072400176000c943d49034210503019044a40e00c43c10554101c58000741c100030724010303100303040c07108107041e400c551100504940b41651101121514140038420460001c4ea0748020020100141c81c0030b0342d2400c40f940501d204200ca14005080302101d059510300540c2e603100e1200901002e03041e05030300c82d0024014000001c1140028044a24000070303007004035190200c02c070f8032441c10442480003604004106541080e01011300c80c0044c0c44074101184141071314441a00101d09080c200b050f81c1800394004840c40e403128070180085203002c62080c800990104020303d8540003a00400d007000c0111101800e112204080705505100740b00e0b032184050b1060240000c0380d244030a405084412030300600c0400395079500080c504139214560300c40002000412111060340c1c4000d8031040e4001500100e0040c0c01c081106421a40f180c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 59652377 1250 59651127 59651149
    0x309050105120402090622050603120909011a0403080d0c110601152f06070e01020a0c0504050901060308040b0c0618030a05030a110a03020a0f0306061202130506130302 74
    0x900e4410b1400990000c0703042c0250300500040e10401000001c100359955900c01e12500c10f480c0540c41ca001940c0000c040700070501160414000e0282003c6801d012541008590108000521582080e400d105030200450402c0c1c08000010704104008008501400050f04080104117004540c0080520000b0a501a103181412055000c05c0c014040b08150350814003104005140180e100c0300c02014900300c50000a540c0c408800d2910b030310701643d41c2d010407201c2c401d50441c4ca070280c0003034141004aa9600740c400020701410014201070146291a03080030b85c0001c2450000f00700503803a51160f410079800b0340c1c00507140081c00198904080c2052081070781c040320740d803003400440342c0300c0b01001e4891195034101c01c100034002000920900a42d8405042d200174451b0f4143c0302c1d4800710024009502000e10940411031851450500d07a200c1e00400d02034801a40e00c0101a500c1c098000001e074100c040704603401010307001c0104668030ba000c0038183c1c0c0000245242840b5103540103008541e03c907 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 59653627 1250 59652377 59652379
    0x15011d0103050d030f0209060a08010e010807031e1104050a06060e1e0609010215100938060918010509011502062205101406060403031b030201021b0109030905 70
    0x20080108045600820714075104105400c4c081124407000b10040024460810000d620200218aa42d41294442c1103d8182d9484807281c0b81c081e600c80580a40d54249440000e0507524041da040344c2030300f0b0552010710444c0c440c0b4402000c84100e14009400c0c2d8008445040000f0b80e0703403030108601c5030b02101ca010149020750312203000c03440300c0300c2e034115208003030740082c0c001d84000625071381e164408c005c1c1008605680303a4100150400c0600814401100c0c801c0901403800c1c00d86541c3c840386c2c50b0303102001c001c180d54250000c0c030a03000740a50f14004440855580312105000d401c0135601c0781384001c2590901d0300042c01c2d0660514040155a28040c4c014009481801c0901e502958001416541151a90b00304420900c500d513400e0300c100341070038402006070245900c0050b07400c2076508004082a044d40d03240070f160b612441480350b203014031300c030250000b8550064403081080031403c40002d980a880003600d0300401405e4944103030508800000306079910440503040c10390040000d00039040c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 59654877 1250 59653627 59653679
    0xa0e030705010c210e030609150601052109030d0f06080d020604240f02040e090c010e0609060d0b04111c05011d0a06090c0c050705060405010804080a0c051501 70
    0x3c0b543e03c400050f070020301003400f440b807000115202c1e02405066000002d8400504071255443c0c00103642d81c989e02070a418403195a46500421107a41c003d9054501d05040c078002411000140f40c01c14a403400301034148a5940400c0042d1316812186006051610010081c00f00e1020310382001c3c00d00d0075103c40b00741e1086400076018080001c4e5140080180100d603601b452a15181188020005044ca41034503411244002400617075203007080506480b80d030043d4169075801a445006490341d40350740352240d910581c10002182c036494407401619a0000300b000c0040d020140e000401e049070604014075070710704c00200310743c080300b111307609094020141007006000369490b0401d820501282d07003580784507600c0910300180c0b40304520340c000300051104042c01d102c2c4a075400f002510705141c0d02e40580d1a40202d60010800c1d05040049604032101031350f80c400307580e80715102d0b030b441900150804c5080007510481d00000c170303904100001e4003034001040c0310032075450584c1290070410b030200b041480301 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 59656127 1250 59654877 59654897
    0x90903090803070314030a020c0a0c0e0f06010806010c0303021905030414010c0c03030f020c0a0308060a0e0906070c1a0c120f0603210714010609050105030a200105040b0a0e03070501 80
    0x607a10000c0f4030170049a2071101c0d0317101c1d1590b00245c0003a0081c500910124031030703107003420140011403400d401101c0020f0340380d280e284c540800360b00d0b4191080728050b011400c900d010400551183d200c940f1014003070b02d001810171000b60b001d2020350442e04405000184080248400c2c0000008410703099042c03040204852101d07010b0250404200c0e00c009414075544500000c1045119012550400400740507100d5120329490060440c0304241e8a135800303411480000700d2400003010b0707024011041344001708061307500c1e070a0490b20748645040445d00d4203a4100300004898074880003d01800461106503110340a4a240309580c1100400da406010b2003c01445020b032404248101c41e0a1107030035000300110544002d03032a5100b0b40c100100051a0b102d100c16150b03d06610078001d84030f214601303004690742e5408040e0341e0100900080c0c00e1544002c4c040c0c00028030000528038a60301070500c1e0b03062036a100703009841504104101c501241e05400c00003210b1400b4000d00000d08be00f403c11100351 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 59657377 1250 59656127 59656133
    0x30301030b0f0c071505100b090105040902090a0b04170105061509040c111204030203120918060102120706140105150409020d020c07061206090b0d0f02120709090309080307 76
    0x10110152107408801c4030340000c6411000f480c021501aa43c2000e4101101c960401201008090403a2100d03e18850040007065000d05841254402c06050351814101414402204029807100e2241070744014003d00010303002c0924809040101017440582c01c1c0100d110483d1400e4a03402403009114a00e1224035258020700ca2003903440304401035800048182c8944001d9a02a0f075004582100780b00724142800d00351440703401030094920035030907110127440840c003484003409101c5140e80e00182c1800c07841003d0522040140d0700600501c110340c4c4100e4a001420055440301e982900d0254446174000d0034611140070f00c42c0100410f45d5452070510498010310100c8c090307402010081d940005400320b1140d681d806682000b0b00329001c2da01d541e03a491030003400c0200007141c41810241040000500d811041c0304008484c2406446201a086a55907900220301c2c0244202da01a07100405c282d4412020010803000e4981088002201c44080c1400742105145911000d000d9000300001800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 59658627 1250 59657377 59657393
    0xe07090608060d0f080c010914030c070e070f050d0b0904060902030d08070e06070204060509070206160305100b0d1805030307030e010b030304050d02060403050d050910020a02010807080c04080604080406020f03030103 95
    0x80a40c00c201441c2c0c41301b0100d124503000d0a1a0b120260004a041c040aa0600d5021000f00074041d4484c040705d00700c90707031788080880c111001c0b102c51021520500b1198191401400100701704a100c41000481d1441c8000040c205401a00d064440c0e50380c0342d46800031801d0802c0070850049617401d00840354908910300608607122000480d0160720b012400d00c1c21500c40350019000751100510440c403a1800602c000e40d103110848840c4221000840314944c080d00911689000f95030a040e141c01c00d074201142e82d9140c1d070100c40202c103d95500c581d0f1114848401c3c0c0040b0555105101965a906280c50001c1c1541c0d90f010824105924100480985503030010407101120020707104801c2c5c0340000d000145c22801141d0014080c0c1c018450600d180541c48401014001070440b2480030031011144100c0e69510411402130100f04584082290540100b0459610505c205030a0b403400b6211008141082c00c195401c0310f0b84940402e0521956805016400840551744025411907145488180c4c1d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 59659877 1250 59658627 59658653
    0x10b1b030301060c140c131805011a0906090405030f07170d0b03010b1c0f030e190302010201060f0b030f09100609140a1103010e0403051314130606120b04060e07090608060d 76
    0x594140c1d5846004d59000c88c0324000000950000000c02c40780c0d0303210001e2103c000f4000943c520581c95400012410301d060320210b8001ca400ca401142400611001c003d44c1c0c0c4d201032020781e541d03410341c9214800c0d00d01c4100240041501c49401040926665043c1401e4139601012140b15028410004841d052011602e1100d241c0241e10390103011b180f8181030301d100240440c00b540000380340781c88404100060b0801c2d0101d92003a8020880d15580300006604012580180461060200b000c540d4402c212040315800210480c00d82c2e0715140003003e900e0494031694811303040141c03103000344030750b03070304280c11065226681e400c0c00d1104400311140001940b005000d0700324401c0400010800b8036108034241c0d4000101488403500701511000c030f90603010b1040c0d000314401c9140880340010311850340159401c071055601c2e01a0280d00c50b5202d40e0140c4400d51060313401c035550b9900018084960f034800d9015030f03842d4580302203260402c034005000c0c0c04028103042c020300f03405544400103907074400502 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 59661127 1250 59659877 59659909
    0x12090807050f061305030102070308091506060703080402040b0603010f060908070501090b071a0f0103121d10020c030604030302090307060504030c030201030515120f0c03060906010b1b030301060c140c 88
    0x196908068000e44e10b00440603000603400d0340c408507480c01015000b9000740d020301034020840d0385400c0d004000c040035541c210350035a0020b0041c45a4030000c0d0103180c410341c000c0c3c1300a1002c200c0001b14804a05503030400d83c01840454115501040365a400800d25800303030507504040c10b449030030140040c1030500b80e0310549240803c00914007040c0307c2010b5000c02400c9050710501b52508111407034240d4018280015500a04c00942c0080d003640500c1c1c4000425004000005240d80d00703000300014034a6052a60055000341001c42d13005a800b40805c911a030310944006844030b0801c01418602900d40e00b000060010400040c80071405015859040761b6091030701048079500d1404042c40c003036401010a400c02c030140a414990b083c082070001407802d0388002ca80007101001b04240d903c90055420950681144005119521291000309501003510b2501d2102220070602da0346594000da00450000b003010034034a0800c03616009620300c101c1024000c0003000b000f136000921001420001d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 59662377 1250 59661127 59661139
    0x3030503091603050309010e0f010e06030a1404060c081602070902160f0f021302120f07020a02030304061809141603060801020a05120108030403050709020a0c0c0312090807050f 78
    0x904900700802840c2e000c141100e080408140c0e0300c0c038085940fa080305810b6804a200641aa0501c1c144618107480e070480581d5a041184440000d200082e440500040d66041e2100415202c45010540082c022031040300006810f224040005244502c042c000340e503011025100010f2942d40000e46c00d09450040c40016521f8901000340c0b0388620b03802d000104034903003045449003841506420078aa0038025a1031442c150310070207019089210f80283e5055403c4c0c00c9010603030000352000610751102c81801250300b001031a40000341380d900107504c031500280c50b5240080b07040d80f18030407540042c000002c05204800780d0584540c49210001c12070695040c0003110740c61614400c0c0c200600400d00e9030006c5554482c94a0002c0607944590400540386000340f00010b001038000003168212a0043c02800c00b15081250701c801075800301c0b4420040240702102c520208060071280302c000d41c851519241d004948000140c443c3d62203074411034560f0800c28042100b178403810b8883d003032060221a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 59663627 1250 59662377 59662381
    0xc010c12090e0115090b090604060c051002030f100905060f2e02010c0306080d090e0703020c010c051c06062102040f12022409010e0f0d03081f030c03030503 69
    0x4640901560b071090b10004040c00000034130051a00b03e01c502503c040d85c1d024000360b2121070300302d03182c4036807000940c0121003080304004880c0710720901c152061152060302e5a501150071200c09a820a84082d8142d40211091205200c0b110b201074004240303040e014800f6141141c001030401c007807800c04601602c10700c1e114100070354903000300f1540d44221035114903030703c1c01100c0c0c024002d0694211800120380b4046d0080380e020b030001848250380b0101c1d80c4144846050400e150000d500c0502000181902440100921002802204451a00395031000d0b104e94034240d012401ca600035003031035822842d040c0309100c80f42d0300c0f101c0800c000180c1480c64407440c0d803000d01d6000900c1340d60b10004407071200b810f01240050884880f020514000c0b41c1e40703030841700c1003010414880303000b0505108010b0300308220b0030654021240c208441100418500d504030b07000c00407505a40c9004011800620080104000038201c0c1444501d501003000203c003945003569525923a501d59800041c060000105c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 59664877 1250 59663627 59663663
    0x5040f0605070e040c08090d0801030b0a18061a0103110c1203150a09050417040609051e1201150801180212030405030d020f0105181b13060605090406080c010c 70
    0x65842070300f5801038070401045604c5800141034020580c2c201c1aa4000c02032250140c1380b0860107241a00d410042501d0503440fa00d441600a105a18100000004c506601000b15031745218905440c407020702034100f24000c542c00182100c01003031301100100018071145811010000d501c40300107074141c2c05642d4a484022031a1303010200c2c10f5102c0d80c0f0448070400401c01c108550885801584541e46985401007222078110940c0124001d5030001a006170b8100014500490400c401c82007081b03450444540c880082101501c01044045090717440c0c203548204150b903a056240103188020082004d45401c50361042001919a000382c424101603002a40007a42402154000c2a00504694154ae039182000e9200c034600c48581025507e4140000e0300e10900b0041c112005941c1070141a024904428428114550076849a0004a9040c5005003e42a0303c203100c0030784000d03141e5549500038041000240c030116040048190044118001d980e40c01c508982c0e0003e503c90b80c1d40c0b420f546848 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 59666127 1250 59664877 59664887
    0x60815040c27051c021804020d110a0312020606030606100c0b0c0d061508130c050121051302150901080c071103060403030209010215010506040b0d060504020c031c05040f060507 78
    0xc0c1046500c102030b01000100003103028024140304c4c1c400d64001c24612000f100760400810100c6002c0c0d0400711540041700040c0b032451001540100080039880c1c1d1705d80b40c0d03e400e81481400f100310740140e400b000501090f8a02000f2855104200301c4038008510b5034440700400e02c500c61440104003842c0c48011078001040c0b2002d0380c0002d04001c2d01000b540b07540702881801008606c40100100e15800007107402443c071001e030b954445402c91000c18280d8a000c00448200007108080854a00c00340e2440f00181014000c1ca401741c0b00389a80003e034520075004100c1035001480c000340c010801045030000698100d02c00b160302c402100d01c1c240c5c442c0528203264a02c10f4107007100c1e81d458014102081300b05a0141c1c06860510300070307070850b18000441002540c0006080c00790340d0b40078100388010001506448020b10400405080100c0d055a890010405980103074020007440e03000440c40e140c0c0c440700701d005443d685043d2903017840541055150326070000e0003c240030300056198400565034038026 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 59667377 1250 59666127 59666129
    0x100b0a020102071704060f08010b070807060b0a0303020105090c01110606121002030109150806060109050f03010b03011503170a08010909080f072003070302010e120f07060815040c27 80
    0x1000b01c9400040750f8130360071280d90140c011200480c8a02c140d501d18a40b0a00d4020b042c0c40b48620300c103182058a0f140c400441e00040f03400c1311521748942c000e40d100c1d210740c403004004512a80000c03440c5d0510100040c00d059003100b00c00e04204152492400260000079182d411000c15592040d4001e0100c1d80141815002481050a58000400024204c155500801c1081c00300d03054a0200d0b42c4030816180c5500055900341c2c0025402c0f0014007492418407000390580c50020f0001618045400c0801d09666101c000980403e003282020001c2c416046501051407141100c107601d88011070001600c00d2006008903d2207940d5126584100700b1024215200b80801012454941201c1d10b04081c1085050002420581c52407040b82c0d110b0500040c4c00d800d40e581610f400303030709c1051002071188600000038200f000740b00c0c440302c203007918800384045400380201b9950000a8500b00d410005100c070107185407030045103015040200b0355400118032101110090b00b0722021610030407510001846 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 59668627 1250 59667377 59667383
    0x1a04050c060c030a0801051522090603050309040b01030204060807050a03110f03040201020d050306010e0d0501020d0e16050a050f0111160b070303060f06090512010e060a020301031a100b0a02010207 87
    0x2000400310402c0100001400500e503140e95500c03801d80c0c0302c0c001d2003051200c428500d00d03001001c0c4652480d0042c69580c0240c09a540700e03020050f59991003d49007650482d910a655030340001449213020b04003406140b07042700c001e0034194a024038044c8001c003c0b80009004800300540428180781041c0700750820f05d60310f0107a030066529105113440c82c4e107481d442030300c00b2405441036152030180c0e10300800503244504c40507120b41016030950818803008902d00002250b15541c00c10000c00901d0040c0f1030381c082e4400c6032004000f081c1048000010700c0c2c1c19500a0307845040d40f02001c202e42d50350319046641c2e008083c41d00c07051600054504501d0030035441280d4200107000c80d0041402c51100c4050592180039540034040140c0d03400b0002c10a0340280501400288001824049801c040c0c0303c1e8094640e0300800058520548060a0308044058030340b24038040e000030040061004d490001c1c9440030883c15042142d091652441103031500e1480342340081c00000c241d020b01c4038001e505a03005c20f0b030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 59669877 1250 59668627 59668639
    0x50304030308090c0316170a050a0302070501080f090606042f19090509010317040914010509010e07120b01030608030d1b0c0f2d060c03181a04050c 65
    0x51640303005041d550741150031103e03034492a034040b500762400003403030a890442c000c03450b02d01c1410800b040340c0e00c07503e0150706d5019109004640c0001b0308104000101365009078090403c075820a40010800c0c00c0c0070300044030403c002001c3c4540c0d01d201158080e04040f08480020306401c4005845e10b8000c10b410041040902c100310405420178008018848080d0b25124204040520002a519900d0134016180c00c0795100303006000040d6070400c0301415148100c0c40a081c5560352810105031000b640310701c0c1000010400400581c103203640c0c454054106505465007904d8808401404002d503030034404801c50b00c41d4003000d12039000781d01810140c06000152a543c0c503200701300101805108030303d181082040d000d01e11a241c42045031903992940800200c000601c0c81d1241d2000128031004521580340c0e038180f5134400307018042a4a02c0130b102c4e81022402e81c00f881c0c0e000d42100c444030920989840c10701e10306400101050b00c1001d504100d50007608058940d418454604100d80301c107190815 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 59671127 1250 59669877 59669879
    0x50d0b0a05060f0d110103050a0e0601140604080601090f0b06040501120b120d0e120f030a03020309030d09140706020d170901230907081906020a0e04020a05130e0408030402010c0f050304 82
    0x10802c2050346185d01c280c905010688070314000c0c100f1104001c1400b40c0f82d400000050111710704108a1a01e2000004c010504043c3c0b58800340e41000402c2e07100724100c0341d40780a403070241482e500a13001114400c40e44c00341040e1410b00083d054201000d010088140d42d59081d0800d5903401d0601208c0c03510310320842d0042c541e6004060aa5503c000c0d604e8414018030003813804000b800200b80d07003010003180145041c8994044154040e4001402c0c00c04940001d01c000845070f0460300c01e0184590007049080007210309040d0840c103000c1188c0006045411090341c41d8640d076001041000b22644410140c5501d031789400c03a1500500c28070880385071101107010980c11a038200c00c0300350700500a10701074039146580e035141c0c160b588020400d0b40c032041d14113400c0000404d00e181d0203400e1914484c10f007150240031718000103040f64031403503006011a03030100d1140348518001501001411010881130f0160504c0d0f110b50b011800002d000074100035140752118100308015003280940d42d0f200084a0f211 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 59672377 1250 59671127 59671133
    0x5030603012904050a05010501050a08040312140717010b030c0f0d05040606031b0321021e03041401080417071a0a0c0311090f10050c06010b0408010501050d0b0a05060f0d 75
    0x1e001c294042d0f10490400307001c90210000c038440d5a0484405858a030f180c216a0541980e641200a1007602400005403100040003514040c2d00100c0060040c8121146008070b400760555031048203080c0182d2203100140311550301c580c1140e80002c0d0341c01007682c41d40c04040d40b0054500c140401e20011904040600c820000150002d8064900c12a00b42034441c800000c3d4206201aa00c000b4200244601e06a510342035a805003054940103231064031858070130148052001d0398090782032800c40d44000745c100050321350030004501c00340e801d103451101414661075903204134004006444141c0000903a080810501c0b440039038024280150481c80341c0340071034982c070080c11803018200210b8102540d216034a14110200d03010b152008000e1038000800000388507503101c500d10104c09004003000320000011003000094000c0280d000c0c55651542414102400d446060780880d009041c500e100348001840c907011540e02180c003203000605507580304c0004211060581c3d1680c0c00184608180b014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 59673627 1250 59672377 59672441
    0x31401021c1a0618060906090301090b04060507020109080304080318120405010305061c0f150212040c060e0901030b06010c0804090b09010611030d020c0111030906160c080306010503060301 83
    0x1081c0c04070321803a07600d880000c0600040f1300c070b00200c1503010810b181d0340c02498a80318018107802d1102078030840c200802c0c03002280c00c50340f0110301030b20398564510800c01000054001c0592010083c070083c041003105650b00d044500003c3e00003454894080001480da00705900c3c01b0702b400c00204122249415601d0860083c0d90041c01920b001a043c003000406d6410541c1c01e054968a1650311429000c0d80f94031041c45200500808580b403a40351054a0309248142c00500101091200d0024460078645404128800117610880503c22000102d09450341d070400b172141101d41101d80e1100035030340c142c0102c2e080001400000c001080c04240481c2040e11070b4024030a880c070a4a0385613503170762900c4059501c4020440b203c007503036000308061051800280c01501440c0254000490010f01d10620241245c008039504200c652251003000303c400ca030300c6050a4143c0a506103001e5200d05901c84150703038031005100c81c0c148040040411002d850950103181038080c14800700d8032406841c191070308 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 59674877 1250 59673627 59673641
    0x1320070f020415030c0f180e12030709231c050703020307030303020c2b050a020106030c08010903020d05030f01060f020a05010f0f1104050d02010315080706050901030c0c0c031401021c 81
    0x1400c402da07110003086c40d0741d0707240d0040261100150401200c0480d0f00454014002054048030103000e8600704d1805080d100f40554010100ca48034030400c18100b1110114070a045000c1c40a00404d20001980c0f0b92123001c2c12035183d25541c121421074894a00303100b0700d090351a41c0b00941510071444000145030345030740a841c03405280382c25500b05180c0881400d14501141c4d800b0095000c440040c000964050700041c48540703ca07000124400390703240c841221031002e40e8000c0c6a2039448040781d104141c0d050202c40701205003070400d1030a60400c25099950403905014000c2072100302c10f048000b00e03000300a014003140d400030003801058180341c0400c0181003041200e41000b418010140c410401020130b44081d01c801620800300500c65400440242101c4015026164100d010201c7c100d003050002c1d401a140d103840303503980c80d6034041c001401c035002c01554504002041c42040000360319900390400b01c94110b51603d86000442c3c204c5030080c8980070100c1074104000e0040d12800119420120b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 59676127 1250 59674877 59674883
    0x7080c280c05010f02150a0f06080c03060c040e0411040b040903020a030f0203070f1b1d09100902090f0403030e0d0e030d090806070507050106030c0803091320070f02041503 76
    0x1d010300c2c0d41c1d500191510508042e0420150f0480c240465410740d0358049079078401030500001c9426850f00c20040111004c2d40c0120020307402000980c60182070070410103411061050f111071030b10785003000305042080080c200030b01c4c81515650020080e5150f4022110b401d200070002c0003480c103d4074000e943c6e0750b13140c5000c402088601041c0d00246001106698841e50000100c40d64424103a9502c0c00299080c0c1d00c0d0070725400c0120011540c0c81240b411004600030134200f91543e8140740c007550f403030600d0f410640d241d114148070b4450f0058407400480c07900100c3c200c80211b180e445d24a816006010f0008021303034244580e4407921081d81c4e02c004047d4107814203506071001c08040c54021101103243c0e000e0682c040e40440f000c50100c0344501c004055071030049000199103510303583c80c1c03600c0000c298000c02d881e50020482041d1450000b82501e520352580344100180d000e040030704000240d1795140041140d1340407440300c040c04480f01d040c21000342d0042081150711075072414511403404a000513 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 59677377 1250 59676127 59676143
    0x2011415030d020601081002031b041211090601050406030207060609020d021308010203150904080c010504030302040801150510050906040905090a1b0302090f0603030712030b011803020607080c28 86
    0x40c0e4202c074004902203051300d0161018210f03510030000444003035403000d846801c2841c004400400200900c1c40507002801c000e0660961741c24190a10a060f1500508064481d88c915020b014042e03800030100c80c2210100d06000d62960b04038280a070080c200c0364070900314107000150668141100d54014940c8080361f001200240e91100e600a00b01d020444810f141d424028003100f00394500f44810681c002c0c030031440c417894000c00520b51400d69500340c3e004c1340440e0f0045414000480c0070b01503009a640c1c1440c440f0003191030310002802e070840b55030182c41032080004820901e9101c0d2801c950142c240f505040c801424040061903035000c0040040d2810180c080c484440c03018104000d80849400a208203101d403540b01c034070908810091314030340e4035201c10080b480002d41039001503451080551000280c0058200014103403105c4001810141c0f41e0f6042c0c103000595488003580c0d07503680c00805054540501c112102e103089004502511008a100e20900401c0e4220310046d040c5885035140c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 59678627 1250 59677377 59677393
    0xd061d070b03040204090c1706010e010803030402030a0b0a0f09080403020a06050f19030b090a090c0603020408030d0b030106081506010905060c100e030d1d1c091202010201141503 79
    0x194a03114540112079818404201040c0545000e4000e0b010301805070010010480e03072000b541000340050701254426400440c0100165030081e40110300418040f000f5500d180381035030000f81c42d00d042c504000c1808840c240072590302c4041798022010f014040001300324a4401e404c00603065045480100d108804800010500b1480f070001c0e5000510300d400041d040c43d001c0d145000107029100003400030559140c009985555800721500d019058261000a1540380303418040084121500304405142c0100000c01072000b0000c2103407078148241d00000f80e46580080001e01618081e030003e00244520309840d040f52a031000c01c0c500448007602c9a4800e00e60b14001e200d041e00400b69190b803940c1144020380104909070b00300083c40d05c3c03003606507444c01409200180846240e00c0c07024148854918074100040c0c81004042d250300d4074643c414a12070362180009041a9142c06400d60b2150051050703021a4000d400c0007111505195012200b454071005010b0390b180d903603079498480e103c0c0603c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 59679877 1250 59678627 59678681
    0xe1c050c1b06070308060103020d020d02030a050a051905090703120f02070602070509040b0414030406050705010506030c03060402220c03020a020d03142d1305060108010b0d0b070e0d06 81
    0xc0d1980040300d002c1c100a00300880707600c041e140b4610041c02c1d1414190204203844030126148020412030306807032001a12810283c0d250b10031214014000c0c00c0061070202031060b03141c0b035a980121848403182c0042100d40c0c0d500c503030074100030150b48000d00c440750f0545542e0392a60444101000c2c800c05500b00c031566a1f980304100c0c1d0b107441038811190840e1054002c280800d420901055016016040c850400d90300030826900e0b65020380c4c0100c0009074080350981c20401c01780545c50300b19a0440c01081142c50000001c2e07101d8102400003403080c451070b65000710a032a030300754070000390101000412641e0300140014019510a40513680180503050300039110501070300c2040804942100c0c040d5207903440602104501d120303160035004c01c1d60000f40310c809a40c02201c2c0c040c41607041100303a071062450b510300b4601d0248182c12075000d0364184001480b0a0b00c8541c01d0351400d98004102d40810785500704103503071060704490f20705d40080780c1304580000d102d030541010511280c401c104a9007020080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 59681127 1250 59679877 59679913
    0x30b09030423010201021303110f0111062a1219050f0612030409091a010f080d140c0105180d020d08060f0612040b060f010c0f03030e1c050c 62
    0x30003460304402c550042e403600c072000441c0e6607010035018000103151480001140c541410580d00403250072545d0540b400c06070a001c4a000d10200d400c3c240b4010140860710710548503080201540440c1210300ea5002900200100f0b0112540a1903626542c5006c0d41c103003900410720441d03003e103c0070341d103401c1002003031810b101c0c1a1084003c0c20b2641d149440700c40030440440f0400100d9000b51200b44008100130689100c4c04482c14421a0308805841c4215201640c03500c050380308550030f0804e1002044011408242d03c801c0b00b0750f85c0342420b004007070304c60002c5040c02400c1180c072543d840c1a0400442c1c2e44e40200e5203002d10f200104403864a2903c680c126507501e03075036903000700007603110001c2082403e00e16418084280000c1645042c03000503d032a03001440200c80949040e1000030030b0100ca41030001481c5199031083c81c0c00c41c00d50000340c540000504104e0401070815a88002c2180c1083d002c0c055401500624400700d2110211075400401c2600002d00d52040f46c001c43c0d20b0107814070000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 59682377 1250 59681127 59681129
    0x406030c21050705040801020f0414040b060409020a0c120309031e0c02010804020a0b0a0503041106030103020d020603090a020301020d0f0506030d0c0f06020f030a0e0606041118030703020607030801030b090304 92
    0x12a01400201d00c1035018000a06005004002440320510011800072028005011105c101e03400d40e43c2c54074509502216806862018180140d180c144452031940700c80088070141d070791022000d692030351285012685008440005420380704503001800401e5031641010004038020f6a0303000c0c402c1d498054a401508031404424041646030b5102e4006502501c0c407694481c0c0001c08048016584940b01101c50303002074480000900000204010000c001c17101403640b10003500c0a50030b542c155070116484129041c0e01074815200400021020482008004842d40d800340c02507454024001003000900200c81e1007003001410000002c0a40c10009005001f80006580e48186984141c5072002242c1031240b0556a4030307002c0160004400051005500556004500244c52107140c00002d003001e401030b200e40d100b54101000f24a030350145070141c60203c0c0010000381c040c1d01c410340009290041c1a400203405c5080811100281900402c015048a0240b550520940d83d103040c4c2640764462 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 59683627 1250 59682377 59682407
    0x40303030c030b18010512010e0d080103030f03060b18120f01020409060e091002030402180903091f080403110c0310022a0a12030b03060f0405121e0d060506040305030406030c 77
    0x650040200d8a040016a01e11161510000270317001800446141414510200500483e0094004004142c4d2210b0b2000b50100d851608100407800e000e1011964407a030030854030300400103040010980c1e81c403450103440340842411120041c029511843c041c4d0818800c4103c928640080010305c54580d03401d01d0707c6890a02c1c060a1070b070a10b00f01c1d48000b504050f0040e84c100c0003040382411503040c0c4001c0716000e0a050030055403101d448004100e010100343c02a000c084030f5045004140e903801607a0390b43c120358141042d061544a080030507203400715000c0e0b12503051191600c02a00c3c40c00f603a00800c00340381c603049004003074080e004040401200d91074008850754420004000401d254200684100d5613901c2e02181060025001901d04007043d50507404261074001070104000c1e0130448071f0300a4410b45502410900b80b40c0120400c5142c0b8002500c074143c0020f500608860b4a501c024040c010061100751a10b440e420f00c9980ca400c02d024400101c0c2c40c1c46c6202c001140607015510300110 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 59684877 1250 59683627 59683669
    0x90c01090504051506040902030115030c021e0f011805010b030d140715060602010c02060105090705040504090c080703030507050d0516110a030204052a0403030f1d06040303030c030b 80
    0x1150100b400020507005000001d00204102c0546595864100500040001031000f50310b039410705040e0b07070001d60766030031400a00d441c2030444034045401040141401c3c0c011140030b0110300b8001d100f503090100441e901d11841d442c002c141110380c1018141c54890074010402040312495110a041d07413034600188250204d40000d955401c17192030340c402030682d1031041d40c100740003032020040701c020391b80305400410150751990014030803158100066401000f08503041d07901814054005081c0d40b285020b0b0741d0081d03441e0328030802841245442a000ac00708107084440d441d6607814000d1080e00094400c03541070040c480d442c44060310038000da89131085100c0640403884a40d03910080805200444150401800c11001000da641d0b0b214680c41401c5c14000d807070018480d0020f61170b0080004986408060081c002071020070340c008010402840796052441c01405424000c000c5d1011114107582e000304001804070401d03515810080248a09407014072502603008200a180c0448520f00b0310380700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 59686127 1250 59684877 59684879
    0xc070b07062a1b0209071b0b091c03050601080a0b03010e0d030203010f05030a11010305100e07030f1d1c0e0d050705090108120403171606060e090c0109 67
    0x5610081101520500300052581c0c859642d00100c5103035540040e0a2540c44840c00044603046280804034100c480d88110b241c00081d4005040d5000240c81c0320100641d240101c20451200b9843c0c030038a030b03001061066280740905d40559034480020200407407101d041aa522580d0082c002c9a0241905868444e0300b41d07907902100004050a24001741e00d90b4981c580552820f0044c400f0761071400c85a500541d4941c1819800550021a41c1c000c1e4000c1d40321140c030602061401c2e00c509441c80017441c0102d510348982d5840c11500b00e660300301020301e201030b9041c45501b40d055402403000070301801d4144130b10901d40c2200301400c40c0021101c4625084400400309500c00e101d0070b103180c091641050410000c6c82c80114000f0512450103c2c0c6d564400c02090207103151000318140145182c10040044441c11030140d840c601540c0f10061440a10030114428150300708103403a900042440c2403020500f1904042002d451544900c10a9095180229035281c202190380b0045e144181c503181502 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 59687377 1250 59686127 59686139
    0x3030c0a030c0206040b0a0206010302043c15081b09011d09070b180901150c060f0f1407030507020601050105120604060308070302060901050112020a050d0311030406031a04020c07 79
    0x40302c103080368000e40030800401c8204544001c0e00c8060700070340c0200041d40c10740c0305101c11607101c0b028054460381058040d101d81c03003000d0115050900203102107a00780a441c001c80c0041e0070300c50413001d440b05601c00049180300d0700040200c11031036440034501c1e60f45017130002d0042c0d41c4401c0c0600d003401045110f126825204015031160052000c2c403c440c10aa617400a5a0ba943c100881204040499441da174200c0e24140350214058014131039511078005c0318000140000c0b100c07040060205498440b41042c562880c2d1146210101281c82031282000c0903041049076082150f2041c042440d040100e0b008501c0054400d05941041e140c584c90883c04440202c00400001c3c44503610a8690740c0c044005106030000d0660940710790014800c034205410402e0941d10140c2101210418526480001d40c5d02c1c0801803007190410354400c0c480c405242000c4500700902c80e10296a8440000d000404543c15403001c44509110600a098141d000782040240d01c1400880401a40080014848 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 59688627 1250 59687377 59687387
    0xe010b16050a0c0f0303140f031906030507060c020405090a1203020903070f03030206071d0a050405090102090d110a0b09130c05070f03080a0506010c0308160507240b03030c0a03 78
    0x4414001c2040ba00c40080700c0d0b81d00944038000e074211100d081d0205a0070020142c010502c103082c0740007115124140405045101c01d03600004008840d00601069404095003d0354010809503401405440b407141d20307600c7c05405090b80403812406a4030f0680001c036807140110301451030f1540058070003024a0004000c0f0043d400102070b1a900d40544803001403c02c2291803114000c0d0720a401411042c54440d0003d0240000741c90b4402c0c0680b803404602d800c943e145060303001590011180011991a0f80800500a000b07001d0003980100400c03202c04140802d459181980003000c0b543d2802c03041c0c903015918060300030398021540012a01d203483c1440d81c5284c20851044829140c102d08002c0c545c0c956003280c01107100250007003458032050003611a56401550340c002c500b8280340640c089195001400c1140080c038098507401c621603c0d50449221304100c43c2c000760018045102c0300d07010041d4608036061820725201d502d14040c0950401e003004425035250034494400b40c00c015071144c80c01c3d51 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 59689877 1250 59688627 59688667
    0x9060e0f040b060d0e0c03191a0a0b0d0c08070f030f02090a02120a0204090605090402102001020d150f05031b13050411010909110d0f020c061608010e010b 68
    0x580306006020b102c084113040d114444407031201741e0040502841c140103242c00c1c400c0701c0704010684482d081089003c41c0417810003501848403040d80e8030743d942c0c80090313001c02018056116036020544107504014006560f50745000d40c0c504100351061280e490030b010046109501c0000e082d84400b00d0b50202500e000c01d0001e501428404016250150481701c84064860840c4d80c0c00e000c036400b0500380611456481160060b1a050f00e8425440c1410740000307503070002c00030504040020481100c11100c0d50350752421540e81a10000790344030300074034140b4005044c422400c10036090301d9503000a4440001e0076030400f2550f010780580031810f2141c40304210700b00c00c072540b01c0d0040c210584003040c1804e103205103489030380199405d00c81e08001c080014210002c0e0b6004440d00c0d4240300105540001c0d100071180c030141903c0002802001800c50728001e0702400e66407600130b0094200b00705000c40b1a60880c5013115103030760f07081c0aa80c0c230b0f002c0030500c410083c00350300780704c00e4180701c0c90b0710004080c50502 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 59691127 1250 59689877 59689879
    0x13020105090a031b03050607020106030b0c0d11030705070b06060f09061e0d1b0309020907110c03070f0e010605040e070c02040f0c0509040c08090c010507020109090509010c09060e0f040b 82
    0x50b0400c0e8503601c400c214400b8803560683c82c000c0da08420814001c082c400395801141510081c01038500d16200c1100c5440c01401c070711404100010708480d20042a40700310142d82c50a60074036164074051030b01600c203402101055610000f90f000180d25454100210b80140482144c03507802c00440b0740a00886800c005158200d443c0e101050780e2100000c10b0207000c242100301c80c0884d0342841500740c50141c0e907d5006071f00a02d801e0080d030b280140d40d00d9103007076400700301e42c94143c543c480c81d0703800c452510714800106500341c000c001c400704891050420301c00640329140c042a200d66600c03982202d0340d100390311805d2214080907002c106d48900c11070110310303403900007840450111241c160000c211007100b07820001040740014800028100303406441181005400d100d5100c2c034207030000c0c03030311400c05910b921f04004000500d04116801703a500301000c3c002c90b5404106c58504201c640e402040211641d9001c50780c8003100017541840b0703411000c0d880340c3c080e00c0441c8202664041c4000740c04030318081 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 59692377 1250 59691127 59691139
    0x60219032f1c0c0f02010b0a030b0a02040e090a111c0b1003020619120b030307060f02130305011a06030115030e0c0d0302070e0c070b01060f0e0a0e0402011101051302010509 76
    0x140019040d18401802c869030207800040050000383c000c0d100b59920031001040da41481c040d034a040d40d07a04941c0702207a0304204c44c0c1089640301070109009200b250031070700c02d80550000340304001c400040c5004000c0d00c070f0160681049001e000f0010ba007110b1405440c00030040c025000c000401442515820800310400da0300065240e900041440c1c00c0001056044504041c2d6180341641c804680240f1503010305041001e078015002007a160700c20204081c0a840e100d05030340b0403070942e90b81114078010721041e0499000d5201c0c074210307000e840e040a0f105103140e0303002c1d190f440a02e02401128100e4070340c9401d0508221240d4010340180501c00743c1c560031405005031808868a560400c0703406280300303a014184003070a1058040d007110001c0c0c5800329503c41030100c0c20000d009890b107941950b586051500c59600740403811903240721b089508030b4118502c2d04d0009032860444d07204a0003035100b40c860214554030301c51030382c1c203c0d441190b046850010100780940554042d10007041c01070741c050300c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 59693627 1250 59692377 59692387
    0xb030c0a02070f0b0a080c040f0302060f090904140c091e070207050a06200a050a0f080408070b0901031d0601050f0402040305010510060f02010e1018020409060219032f 74
    0x4107800e101656104042090002600e01d602e1a48186c82c03d60103285104d5090816040c40c404043c1403000d800001d0141c00001140c0901d002d0940a541042400921007070503407500c1e1074003035103030400850260028800c542400c501071801041a030321450b00c0c4118001e04054915001152100c007400350000d40c001d0f4440822140c54480800000d007801d03850b000c540714481c1100840e01d203100c1d0000704054000001030000034402040303001c3c10f25040030300840380304154280110107101d00d5218640502c20818006416842c01c0b001e8296510262070401801022003a184078203152025846c0721074102000510062910709442c104860b00a00018146070701c0380c1d85c043c00c440b070503101e90400f0741e1741e00707020000b1580c0030003030340b50b0844140b00070700480044882055884880e058034048142e01e5403080c1c003405180d2107030072403983d4004000303000903921420808002d6100c1c00b105492402d000c00301030316690003805880c6a444410340c001290b10f012210f10745a034140494008000081081 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 59694877 1250 59693627 59693639
    0xc01090806041703060103180c05033913150e0a050412050d0b09040507030b06030a0c0e07031b0e120d08040206070201111b0a06090602100c02030c070f0914010b030c0a0207 76
    0x15056588901c200c127500c022504220425150220744220011481d02c40d10b000c605007103051290810b189220b20b241c421003040700d00041c030750380e80220000c3e09240c0782000344503800d07045085c82c800b00c0d43d140035200200d07200c0c05801c400b40c0d02d04413405012007030707012a40c6004905c140010411508084800500400c04ec000181041406d45059866501480003030051001100000c0c2c0c00a208034010001c80155641c0e60811841134410b03aa001410880042c50a074041c1c3c102c840403455000da1520100d9000c0d8000d0a54501c1c080c2c0e05004168991610011440c0014420b45024030344c1c03154141980c4a40c00c01403103501804007203040100b0a01440c0c1e0b10b85082202c51040c52614141d000364000e0101841032562041d48240b0130060101410440c05402041101c02c40380e131250042000c0c0b0401c4c00a910394811007101541c0ca00c10440000b906022a40c403d03030642d24014004d01489010a800d240100c100780945814404200081251044048010040080d150040d1101103984d40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 59696127 1250 59694877 59694911
    0x5070210091a090901060203070b0109050c07021002010e0705010e010c1e020901081005130f030f1103031006170606042c0f0609060306070e010309030e040207050c01090806041703060103 82
    0x6105851640004038241d420fa240444a407805400c59200a500709152030f00c85180040061280140b0103a5950200314000c4050044944054024000101d4120302e03940c024008c1240c43d9680005029440700460706601c2420400b580400596a0700e070b090500d80c50320442d12641100c00e80341941c0c01100c0e54016268550a580240110006402e040d00c2c4200d115080d07400c004c1004c20701c1c41280c81190000f6440b10019108260145410a44c3d10000300054070304038000d41102c1000d110100400c1a14507001000e0025122207a44041000d02102c0c6694015031041c1e503110362040c02844144030010860b02c0a82100700c2e10a0542c5041c8040d00320601220801d81d01c0c02c0608070b00703a040100307a0502000240d0004008d80080c4541c2c0b600146c000c000c80100d01c49c40d0304041c0c58060781740c01c0c0f510609034550304080007007003150b5501c014500b40e80d842e070f034601400d404220801d00015440e200891510301c2140c2000301c50301c4400194881058950004042606140e9561100e194400e159 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 59697377 1250 59696127 59696159
    0x10f05010503060c0301030f030507110307031121071a0f07060507170f0c030a15120212030c030304120c06050f0105040e03070201021902210313150507021009 70
    0x4000009029410030041c98240308000f456000812401c200400001c2c4c03d030a100c0f944190103181864498000f4503020780d45840210103268036200301c400c04814400350a684074401d1001f11401400c50011007507200d2070b100780891581c02904490010000b00440c4a0012205ca4020704000d00c3c101418617590416080310101f0f451041d076600c01c0050140e041505503410241240002d0398915000c0fa807001c0c01c0200921001107000080042600c0064540101c49100f0119044040795503d5500641c00c81c003a0340c0e4207a228104040081d0940b00000c42107640700108080514030355511520b9840c008000300c1481e00030800100704000205110344078581c05007001c00d04110300395241c80c2c1040700303071000da400131442e5070001c2009400503071700055040c0002540c0c120300044080b4074000110055400c03049100c440300f2204240d58000c01c04002032091415401641e88501e88614045d2004a402c0c05480042101005150090320b8400c0310407607001c0451034400a02d58848101ea0001030034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 59698627 1250 59697377 59697401
    0x50913020904060b03100b090402130b0604080102030f0c16032708030307021e07061d1f020d0905090109020c070b0a091403010c05090d060209040c050301050f09010509160201060801 80
    0x82c9020303000b0759180c24044451b215403441000e01190880000056006d00d0240c4000c1c0309000840892401e070540790400200140300904442c1ca90380e803690600d010750700440b42843c07440e00c94800220101004402d4a1400d40c075040c401c0f100e9540c5030342c01d840c0c60380005503070191f50f1001000c0c000d42e08278012040025001040107141c80342072100002e842e1000c80c0c8032200400841800c82c0a111500050710021160315140c8520b814110142004031403845040b1240c01c0080030800c80305154401c841011820b083d41e08031400f000c0d910030103d520340c00c2800b82ca64400600001000044101d4028109910100050710407044d5035002c0035250b6030009116001180705010108905242d404100c624070105a00078800000701d454010003034410b0a0744c291003906903450b00002d000113507056459903400584104000904804003520035042407203014400c42005940d55003906103600c801d41240c0028002c03070030688400303150140002d00b801180c411503680d4400062052001d000f5440201c603 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 59699877 1250 59698627 59698631
    0x307060c0b1e0a0b0402070f0b0711010b0306042d111008012607030c09050f0a0c02150702011e021206100905010e061b010f05090c030705091302090406 67
    0x45207151039402540c0007001c1c60307403080200702c0344aa442502641690310031003118000a07042e00440009000b8010144040e040c1941e00480e0300810041255450088201e40c6822110300c6800414600703a94010802c0358041d04000701050010741648803400654007841c001503400180c05c400750804002c44030707060711038008039042c8541e070742403099100340007211600c0c0200c00da41c1482041c150740c0001d8500c07a0b05000e10300f07210701e01e540c1050007090045d41d484050424156a0307074080700043c00e400d80308190f86204981c003159500d000b0344907101590816401525840c2450f400b07e407070f9500000c02142c00d55403112060b20105521084c0f4121300b0141280050f11005038107005140319000030042d5016601e41c500882e4401d803c00601800c94209207081c5012035900c00214445019400d86000c00d100344940c405401901900044032074a0519410082952034544482e42c43c94030508181d01900682da060082d401c010054503840200d01d5034136150707540e0700d50200304d0154048400b5280c041e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 59701127 1250 59699877 59699897
    0x605060f0d02010206060d06110d060503010c17040209150a080a050105010603050603070b0703090512100c030204060509120102040806070513080a021005030702010f0608070e0a0504050303071409030706 89
    0x100d000ea0005900c0003041e00c580c4014441d55001035030707510300901a14420911801140300308030141d08110b0040102d081d0194039900a0041d01019010b50300425100703500f80034480320705602c64510890900f814880c0c0c400300d40c8503030f000e00069650181140c004d05c5144007880ea03150325110380360b0700204280c1000b08003104541c14400d003100c40c1078100d0b904246c20328080c40200c1d90002030660544003001c0845a44000520301502c002107641d02c49608480d200582803401e28011595000300744007550305100b8070420401c100c0480c45a4040c000c04984280540d26071420305503146044020840001403400ea11204900d00e000012102c04000a02c0000c01d8012010512241002401d60100030041400e1365130004003219070542c034000c02c001001c00000e000e01d2017500031565440e90020100b040c15211594180c80340701034003411703e1480b0349602040d81102c840c800e40c0d1249403c000134500716101d9000c1224601c00f5502c14803a11081800800c40c40c1c0c0d0300784002070041c00c1d1038076004003507 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 59702377 1250 59701127 59701129
    0x60909050f011203050c01020d110a030e01051b0a0c060f0213060c110607020319080301140105030907090b0604090213050f061215060d060905061c030c0303090c030f060506 76
    0x66103004051221800810004012440a141c11502d00c5a070505009480c0c0d0340e021421802030207900c200000c09424600040d030700e2220000200069a482e40c1c00380031510304001e070207003a00d00684240b0000c02c503021400024070214009003001425625102035445007544480041d00c0001080368041c82e0700162000c00f401502d40440020541e07400c05140218041e182d18601400c44000c0e540114800180e400465900344000b102c1d64041028150182503241800200c0d034000b400f50b01c0190360103110151072580581d0a41e840f03260040010300c0c43c070b428981d4100207064a000a20341046080c440450007407000e00140906c001c0b4100380c52041c91400d810400300710a001c0b13610740521382c1048100641c10309030120036408210f00f007a032182c0004200c045451b074480c1102d0300ca115407400c000421403042581001d07001300e208a4445000720140c43d906104960301d5040100850141509000000d02a4103d600707901d02544100c03140994a03241d071a0300144030001102d69aa550040200c6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 59703627 1250 59702377 59702381
    0x10510060905010f080417040b0a0305090d030b0906040c020c03060a091e0807022407030302040807050a0b07031103070f0311070e090d0302180406030f050d02031801030902040e07060909 82
    0x24602441c01e100c03e0700d20040050240e003005840904401f6248404c01511003908044500602c01d400740f0746c4d91245014070040c01408152405280e50091030640071101e4401d0140c00c1c1155402400303c00350b5100d60081000501c880310200c01940074001031040c040d41e05001040c85000118000b0501c0c11300c600d440300782e404180040c00c80300500c00034642c02041d00c00c011785100320ba060f0741c0301248502c010b80c4003003000340340100001301060002d074076000c040d8940c015200b1070748803004a45140340c581041040c045c0039402010700800c81484010003003842805070341010300030401074a26282d05d5480300884403101c40c800741e000c107100c010500c241444c200100700c0240440e81c3d54141a0a20810940c2c513941107903803000c100f540109911a141c1d0302c041f00c58203055030050040000503607030302e01405c290b0441c840603100d074011310782e8458089001004880b890000e81c18180c020001120054005100c8540c0c00c1c4d0f013150341d031320618251600800200c8060101501c4020203213103000320041c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 59704877 1250 59703627 59703629
    0x20303011d0f0705090f03010c09050a0b0c03030403270b0c0d0216050f01021501140108070507031b1e06021801020102040509010e0c0d020a0905090a0c200307050105100609 76
    0x90354014404000b103a0241801072904084103150a581d11200d00e00010120700f109611503074154030707010001d034009820610703880440764140c40601500b540d50590725054041c40523003500139002040000c0000c3d00c00c50b0b41d190602400c1d8045c5440308031103084c0c000b005516801003d11010700107a1800080001c0103180300c40c0700c3c00c0c4018503455198400390100c070320240c441d05019025035501403000e6170080c00011450101c020b00b117802c541e56610604084000801c026011554030004207503034600c04c2d4100c852480d05903e03044001040025020f120141c101d00a540404a43c82040c6041c0e050300202c1000300c4c05500c001d44c580c070070681c2009400c1010340c40d60741960301c100410090354607000314039411145034403500c501ca035844444410f054070404002c02161440011601d403216004070221003520020340300c10107160380f03c15803030f401c481c3e0041c011404900703c40210041400e103440c0c00002200f6090a407428101a0340d5580c3c290f40081d030300d0809a9035942f406008d0b080d40200420 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 59706127 1250 59704877 59704919
    0x1207060b040b0307030b2206020a03051f05060a0309050609060901060b1303080a0504030c0324180605060105160b0609060102060403050d05040206070c06030c030f0606052a07030302030301 83
    0x45a180304400081e50341303002c1d10000786000416000222040c103041800e00c003090344594074210060803403a00b40001d5004088010100c0e1410300856004512000c81da07400c1d00c2102c541586c61400d0008000458110703c12110426864508040001d4001c0c007081d030062000c040106842c2c2030407000c83c0d0030740d031041c1c0140d0640d18043c8030150726a44c04d13404e041c04880d00700b5080b0365107403001c4404617011701c02c540010741907845096001081080c01000e420804030454010126060880c55200580b450000c840c0b0201541a604402080d034030791082d80c00000505100d80307030134089040345812503101c1d10251600da4002042000354188045403039400b41c024800707013200d49420b80d0080c1c880e006060301c4140c07060740d9000140840d03e03150102c80003150084c1484400a44d1008001c0150002101c03a50020782001440000d40c20940a0342c000c1d6021078072800d0a1540f030b40303801c8806200b91050450341c0700040b04440301d8101c003808000c0103503009a026682d0f030741c10300b0210002010241200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 59707377 1250 59706127 59706131
    0x50a170c0708031e070c170604030e0102010524030c1f020708150708040312050c04050f010c05070b0a05090d05010c020d0203040f151716030b010507080f0f0403051207060b04 77
    0x4c1d005840c000c000a84040a80c05200b58459089080c07404030207425030810752035940d10400c005200e00001442c01d11445c8641c1c0d9030703140c400c180e0004a0982d00c0c250303003a072425140d580c00003106070042c41d031711301d00030320090119000e4007040c000165846004000c01044041402c0c030f407040c01035050002c10042c19004001b4041040d1003000450f03001001009030b0304101c208800b14003058400c0010715a0725001d06424056428205d065100316801031040c14403d40280d60718040c5035001c1c04412b290150001d0184c01d81c586011201e90040e4805480d4900304003040010b50140d584101c50500f80501481c00041e01c903039480c4001c0c0c036114087c1b040c881950f00601003001600c0040d610802130740c103040c4a01031005013690f410f4900780c450b99001c4940c1d10f80e960030000420b010040d540a1b200c0d2640c3c0601c41c44020030015603261040701d80c00707040701d10200b1403840401c010360020845078140c49001c1e803800741d0b0303522907130304040c074132034044580760350018014050225a014030420001d0481301 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 59708627 1250 59707377 59707387
    0x4080d11120105120718020928150207090e060a06050105040b09040902060c010207121b0302030414030a050703030f031103010509040b06060904090312060905061507050a170c070803 80
    0x200c58030007401481054468103a6107141e900555007407194400400520304940c0b0301051440820010f50045203010703004040301a0b03140b004604540810980307441c07114640da8650304025800c0d42c034900c002002c070706621400a0000301c400305442121000d642c0000a49200e040c091083d0040d1450f65110350f040010510040c044184800101c07943c00400f10f070006814806440840d1043c051500345108a510108200040c40b100b0742e810301802030650f44075004c0c082d030380350300e000030141020024005034410300c0140000c4441352189883c03440018100c90840301103a584da45000004d800440c000b9201035a900328090b0140035a505010600b070380c031829503046c000400c42402000700b0180c0032080e010b0100c0d00c1d135244c210854030f20302c03c00742003448012040d00b40038050482400c01e0600b95403030084006108942072154901a03d00117202014000d001d190034040c940001400741d4050007595568400211500c803110100c0500c414040d89818282080c00d007400c1e4a41e20100654004101c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 59709877 1250 59708627 59708647
    0x121917030405030a030c1713050105010b13050909030906040303020f06090316021c050111040512240c0c0d090611010501080d180504060914090d0e01121404080d11 72
    0x252013020322949800102ca5031070300d02c215164082020f03100349038413844042c006903a058000c800481c60050f0000d101c940d07070301c540d03103900c1e4841e82c000b4554494504100b44102e1604440c15608800350f84120b0f0300744900301c00040c10590080e8030480c050386c400307404800e007a0310921003694041140805542010400c003007000c0d8803602c13910002d10641190102c40210602180859402034101d0003c014548250014425a91050080c1c0d4491030401c0e514841408000403804100b18040071203500706036030500c147c600440003034046640d1000600076541d240d5020020b1051806596881801040c81e201018080315243d070a10060359040000500c0720480c00100ca10581d101c0740ba00f14680c0001c1c80f4181d010400e80e0b007060b03a00030304222001440c5103440d000501d00800d1501001c00a85918540a80d030304540c0c01e0900c040348400000642c10740c010b0180d1410040042008243c0f90b4201000306940542154201e8403503401040c083c040340c440e40710788203641c0043c2400604d0246815 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 59711127 1250 59709877 59709883
    0x9070f090e0106140c100c0206072d0e010210020705070e0702030711060a0302090405100603050610080f06040f0905060103050d05130513020f030a0f0c030b011d121917030405 77
    0x81c2c13003c401c500000031541007224003084400e0510003622803c100240500c00029110541681d0000002c0c50280300d1230304046110240e040350a0441c0c60b4425141c01e807502c00c0d100b81c00c011183c00d065004002c3c2c0c8280c04030031400103010080c40352001d0030340c581c02c06200655124014082e40210351040c456000049c0c21018100045041110482d49a0100c04011000380c800e144d07440e600142400203200b0a804c01e02c10703041c2a0783c600d0f107091095503200340500101c40030780700740e0300f00041c40c4d000403692450f000c02c403e0350000301c050300208401c0c0b02180c011017500d48007401200e181c0d01c590010010300c0030601c4011181c54091800718588201b01601002505c0700e401020b2190342c6604490310311445642c1114016200003248648902c0c044103080e00a102480e407840344541400398100017248284210709802c0816141c500313440003403070560004d038000c50714079541048100c806d01c00074540c20403410141e060742110801407010030385410f480303691a00d1400400d03001c0c24014400051004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 59712233 1106 59711127 59711147
    0xc030708010908030106050f0d02030411010f0e010c1106070c0b040906090b06120405011e0b120606010c15060b0301060e01030b0109140402160209070f090e0106 71
    0x80c0e4520303098410b4928001c040000410052090600800242c005604941812820030a1200c60744e01240c0c0182c2c0c0984005883c0e4002e03155940c1d100640314801041450320408a21444001070030f00c00a40b440241040e81c0c40100d0112a119401502d01c665041840e060141e542ca0760358040981c8580140b103402d07802c0c03000c0840d0000150150030b0b070524002e40041d1404000120b5181494006402243c0654035100e00d00140c4a0408a0368070140100c07000168a404540410611540d40b40c85130303000360003490800883c7e0ba00a400c14205642001001110100ca0b00000e001800c40e5080561201c038080008200160b0102455192100c281c800b00030540c0b5400040d11070018134440e006000d900314003d4038050400c0e80150480b40402d414445d101a100e80c00110195012aa00703000191a10545041d03a507000e0b0f5820000c006013040f6040d55410000c005142e105a = true := by decide +kernel

theorem cover : BRFrame.Cov 59532377 59712233 := by
  have h0 := BRFrame.cov_init 59532377
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 59532377 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 59532377 ≤ n) (h2 : n < 59712233) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
