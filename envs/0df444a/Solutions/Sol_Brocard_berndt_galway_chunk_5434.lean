-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5434
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:51:26.970199+00:00
-- url     : https://prove2.me/submissions/1077b9d2-c1b0-422f-8a14-65620372784d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 977158273 ≤ n < 977338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 977159523 1250 977158273 977158279
    0x60f0c0c0809040b06030a0510080318090a1107120e0102160e070e0d26030408071704050a290c070b03130803070201021801031505061608031303030c02010501060806 73
    0x1541d0010000a02418594030340a801505c0441440700041d8541c2005005030101165140c0c90341c1c80c2c03811075517240202d0784000c0c8e00e00d07a4200d150110b814006c0003160801160b000205c2c12610643e103022181e8012130048403070800012103030031103d600c918078800003642440030340310100702c400400c541580140280c04002c5d50600100344264000d412035602444058203071504000d00d0f05204000f1b50080003000c3c000c4c0d0b01000e40008400703031300c0110380c855944000340ea130801c002c5d6218686070202030040c103c0c49800400000c61039947c0d030b4098200500da116116000c4855a8500686803e01c1070b80c100c0e11141c0134020f2500d204400b0504105546810340802d840f40c0c0d1341280394021190994018007846000000c1c005141d9040d00102000c110509001c0c0489070800c0044084809400000c081c2000707850f010b004600e0400b0050030300900c903c130158809461034032040740700d0740240d4038403280c40b58030003511081680600031403004020314002002a5032410034050a401401016584 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 977160773 1250 977159523 977159527
    0x1c060b040e0a14130c050306280b04051302010e0d080403030f032009090f060a05060a1e030e060f0c0a080a020d1103060a05030712060b030703060e060103060f0c0c08 73
    0x5a6141d25510460800105480c00441c1381004000c105070701c64664402e8078102101440450740341400503145010702c0c00c00c4a26003030b00b03041085c02101c002864000829807500c4112a4119980b103004181c0220003110b94103201801910001d000310500f0110306005200308a01c01e40401e85044c150350480750142440f0482c03220302d181c228003c6c003000d00d6020002064021000302c2c03040d00b1001e05000c22058803a01520b45074241c0c47c60301c00c20100c0c0d04640c000c9082c502441981442c50141001d006942043c62540540d6201d40046200900310440040d41d2034060400d001c00402c44682c1180040d040d20781c29090043c00d0001d184211107000c8140301241020605805040c0d044510119502d18100480f050318040c2411a900a850346032040407000000710340c916000c40c0600440710071060345d10080000c0c0e80c03004080e1031350040950303150181c0d03100000401c0c10707801000c0010360b9090107041e4642c194504001150300003c20415540d203005e0149020700d03004481303100c02c01d4000010726 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 977162023 1250 977160773 977160781
    0x414060415031a060a080a080301143c0409112407021e090f010f15120b041b0503070807091d0603100f06080f15070e0609090c1c060b040e 61
    0x17003141520f607105040900c1000e09003001d01c0b15001c06507044e03500351824808040e01c043c0400500c6d41041d141d0502400741d88a80c60526414440901101c1c0700e9030804c10414a2078000141c02c075400d1590070ba071400c00f08000300990b4980031601600e50328030503000d508003407105800c8190360302400100038010800f800740280e9100160961400400004100e000641303080c441c100b00c018828815a0681c403e4584049050024407400307250102c5140c0e903944001c100804442c1c083c1800802035900242e9900496448100c408003200380028251900c9a0764104404010803d4070002c00e9642008014041442200c241c80b20b0341060030b14020750702111f6100d10000900300b00c490386864007031034603042d00420b90414503041b140407100d16509448c1442420000700b511340c20004054500b81c401000000d101c40d0041c04c0b8400f081402802c5a070a141002c008148122419a4100d4500d4004038a01054007550000c1d08805454143c080c480c141c5000c0108889000d14000c50035076451040006d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 977163273 1250 977162023 977162029
    0xb04090507170703203c0408060f060a0f0311041410030317010806060915061314040908030606090d06060303090503100b030c1e0414060415031a06 65
    0x801c20b403800b0380c0c0c0b9508121002038010402480c42030755030130046403030302c0c1030101000c151990000e0400040000342d01c621404401c103030100d04003000740c00e013408804103840d20f64000b0340042c01f0113030000c01180c1020181c03003101c103400034919403051442007024030001c0d4401c03a17003204132030b401118800c61028210020740605000315148080302c41500c10004c1c48658100e401080764040d4171012500741c1c0e81d070356800180c00240980c0405a01c400c01041c40c030304090114951104030750390b0402007114600000750040d070060a1480c5004c401440601140c0d0044480c014004401c6404010100143d6038125150000030b200c0340c0700788030201c0d007281582c44144000781180e074014002c0100541b2842e01030050422401035901920600704042030401c4184a114906c05000b0f0040440340d00b84000c0000050134462190480041d40806005a8a4038001d042c14410010040c0c6500d04d003da00307200888000c061740c6001c100c0c8072102000403800182491540544107410010103540d5503000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 977164523 1250 977163273 977163287
    0x40f0303031e0f02040515030c07230d09051011060402190b030103061a011b1b090e0f0c010905010c0f020d080403080d180b1f050301020a0507060b0405010b04090507 73
    0x4000030b07060510840e01e40a80044e4010700a4078000c03031344a2164181d007103085180340021521415100410000a400b00e107951500880b064000880f18000080e0b07028a5030500d038641100740b001c180005c0d0188031510300309aa00d54104103e2074220304074410b407d20070b0390f140b0028102034080c4500c040c0100042c0b04036402c04000d0103500201580d0b959680c07411500509038202d0211805085d407540b105a90701c9203c500c01c40c3c1800030038130401c0340c3c0d60b902d07609000b0b50701940009100000c464005001c00d100c1c02101020358400700038100c0500604081c608100071000114100304140c6004c0c40075a800202da428031680140742e100c0040c01c2031000c27030741c0c034201001c014201400c0800d0000c200070391100205450070039a8801d10a80c1e00400e0745026036501032800401e070090711400a0710f04c0103c02c800100940350555203403080b540e214046800c82e400111a0700000754009000c0c010321555000b850046007046d41c081180f98582030303005106001e9400303154400c54445010442c958403600c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 977165773 1250 977164523 977164571
    0xf07021903020606040605060c030715180605060f040c052b02131d01140415051c020924060d06030210050316030603024005010806090102040f030303 66
    0x2561400546410043e40e105402c0359298841c9040c00e0003c212418100240c3c2e0f08044400011402c00d102907949001548000320001c210070760b1076106525400c3c501b03242c001801d00510000a440c180502485603600c0703110300450066003403401400c1d4040d0710000b100c2000c2581c00341b04108000d1981c00c414a008416040720740c1c640046070401c11024081c0401c421030303490306102400000303c5034881c00e201100b445422509134003401c01c0700140c00d00e5000444a85840e40161040e1622480051044802c1115281001e01e10001c0b000450809004403501b080c050f0b124451552010752078443e101752030606142c0140c5022070040c48078101038000c0c10140d41d0081120040304449000184140c1040f1000c8210855005450031268028800e54050702d4000d07081c5a150310443d4403091071041e05103107a4a1514441d5003820788181c00c003500c00c0a41c03605401c04900d9500d4900c9843c50003501074159051640304020410413a031802811a04407030345810085494105181e4091140641385 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 977167023 1250 977165773 977165803
    0x60301120c0906090e0f1f0207030512180c0301021611150c100f0209010c03030e1608030910080c043003020f071508011a0c0a060e0106060503040201080f0702 70
    0x1110204011314141c000004210800003102d85ca80c2c0700c144850784d50511102255070303000d00001c0700302d016900d0340c00810360a4003a042161401c0c1e0f061100600c0c0800072100c624840b0000e070002c50aa000a01980710403800403402035041481c85107a00c030340b992440c007004068584080824207140c0720b40c170407501c03554111080940c58403c100040e6440300c0c1c00c00140130486141c0b40c00c11031004c01c1c600c2940c0c090b40d01a92414000c14165505400030000c140901055116102c5668030f040e035030500d403070b010705600c402a5481e860380c9000d1001c0e900026000c41c080c04078020410481041030b2080c5e404071800d031911860300c1c211440113291841c0720031030402400225564170f4414560005006060b100208040b114642d81d18511107000400c001043c0000462a1004010308541d81c5c462017025000c8111003483c180501d01540e01d030104103642120380d07540729021414405400e100e40e1006001e217081c124654901036000a082010007002c0c00c9100000c0b0021501d0729200300700c8064050441 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 977168273 1250 977167023 977167031
    0x91308030f06090a061401030504060e0d02010b0915090a02030408130e090f010b030c010e03010204090204030c0f0626040606080708010914070503070308030910020d1415060301120c09 81
    0x10305002411001e0880d140c500545590000c0b030300030649407040104641d04000f002d84000b01100045010703140140c020386055465402c03031160440d0510228040d5802d50700009002c00b6020140315076018020b00c443d000d124046240c81c002d4030303109a000d50203502080c005035640c2d5203203402ca03854000d01691240381c000e09400401d9003404280003a00600e0508100c40030f0b0501083c2e0310342a100c0c800d04442c0c054000d0b48204c000c65004510f2031468500003400035080680350081503003241c11940c801e0341c00780d26004042240d00d0031004003801a029a1801440c03140e07403a06600005003003ca0204c0003070416a00007014405158481c1002d440a4010344094079075440a1501a003001d000a84584025407000c407580c02000030038408603240900070700406860754030350310310741c0d00018140001401560220f0362006040e2006100f100c0d07480000066004082c2012088000c004040703102d011001d03844550a42d94080642c1c1c115109401c181c5403403140f03882e009001d800940d000c10415030030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 977169523 1250 977168273 977168281
    0x30706140d11030106110606011e0c08030a020a1e08040213020c0f16050f0a0504051806091c05071a1305030c0319020601060804300f030c03091109130803 68
    0xd81c1009504980c5d150782c850154029099410307440d0700082d07680c18003103002ca40c0b680b5122854031501c04800016401c2c52004000c3c2c540710440298811070b81e00c2202503000800ca4040d80e00640c0d58401d0b40d01414205c021910700c9070003c2d016100150000e07100310300c0440c2c80c41c40300d10660101c2d10f030b464440c07040c0da5071014441066a52102004c903520b40c0842115004101810021003c404100c0000c00b4000b6041c9440305210040001402c0500700d0b040300010460900c40400000740180300e0200148005250020400702242007025424100310301040040c4c0440c400400b80d4540b5480c0151540803600c4008245182d0b030b01140c00105030340004901780c1c00f00c0b140030010f0b00d075180428407040d40d010469131040340c9400007400340c1d40110f05008042400711b5440242e504030544550007140071184040d14007550301c642d120b00304002414101c0201d10380c5606008a03001107889003805c3c008840c03140e642d14510311207040700e01d000302d2401000800e118811542140103030380040c840e03692800c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 977170773 1250 977169523 977169551
    0x2202070308101505030a090507080a030f02010f181112070609050f0102070b0d0b150f0c121c05130602040b121b070b1008030406020c04050a0b030706140d 68
    0x202120342c0025102200000141c16000501c6041031514955450349181d64840798440180170a130b5065855215440010964100030042c200300b46000391102d100d42c44030b00c20001d0030b40f03561000c0c030f0154605000f030900d048920741c45409440c1d5170100039000e40300403500108440038144c5284000b1031080c0da40001d00d281e004420365040e941c041d1104043e01d10160016030742d814681c858003418804c100301c00c03a141800d5500801103480c00502c81c10b8204070642e03800883c0d4110348207040b600c0b0000100b60b045031784100400c00c40500d08036041c50500d45025020a0000d80080c40100c1a80d26600001d150525035005040d4403a8403400440d155911b071540e01110f9000460b03502ca2510794600840d075819480481441c240000701d40e59131406034a540e906ca14510003500c0c2c0180c41c8101d503c046101c4e41c0510103880540300d1a03000700782411020003000151a00500440c81940c5009401006034401043c010306844180c02c12001c1c400c070110345440517214071444948058604052803074040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 977172023 1250 977170773 977170787
    0x603020c0709090507120c0b3009120a0e060408011d1203012114011a090910020a050d0212010303080a021624061502120a020c22020703 60
    0x103a10340c0100d444aa407609495001c6606562000d40582d2110604000d40d003512000390402a200e00801c001031a600d511504d1250441c500008039084550207141c101c01d03ca40c0c0c000c4038001b410b80c513020030381050100c09450794115000344061240016002d0a51402207034100750340c9401038000e0b503546a480841e14001c140c005420700389064104040300305400e0000701600b441c0c0c9016034a61443e4a045034450740c2cbc0103107404c8001c1d44079503d1041c5011400002d400001024a2000403c04e50381500300200c504042480f1070740f08003006000e0040704c00300020452a00d0310320510042c1e0707488001006031424011030403e82e0500e40001400200c00c0411107070181264420703100e100840d05c4210070341013070b401020356210315800842054400b00322500c0710030b00035030f4000241480003a0700b01c01c004181ca00729000101681c1c504401d0682e1682d04004203c80901201d40050802c2c280d000007e4071055402c4c24144603040e41003840003414840211040042c6210b4421550784406e490040c100c9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 977173273 1250 977172023 977172037
    0xf0307080609061608060f0a0504020310080f07081504032a060b010e010e090c1e07051c021009050304150f03060602010612060915052404180807050f0304060302 71
    0x50103404041004e9114000040309030166589898800307580d94800d0002107241d00c03c40c541e001c581c1500014140d103035072000754010802403400070503190400002a01d4111013040c1c2c05660780c800001048880c0c0041210300d9201e9000c602000c0f2600c8a007001c45111205040e600d50303801044c0c65085054005290620f4400e10074107082c00700071007400041d65a41520005140404d041002403c0c0b5454900c580340c0c0c0c0240365441c0c25050080e03502e68244d03030304049070001021100001d8020107011007000b1418400d0710254005042c00783c010070003501c4084c40307194500042e40303406002003008070034010b0b01c0c0038240014502000e15200b000040c200c20020183c100840d18050f0081a001d1040c000e100a07209850111031440c502944c0c0c21004080da10300a64032a44241800d00031428540038080c02090841113483c40c1c1220824003101507a150003c140c401d615040341c2d5030140c3c0c00d00e06641c6040d41c020140c00e0729044a802c1150600100c2c01040d24180000680400c109405602620030307 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 977174523 1250 977173273 977173291
    0x30305090f1c090f050d12120204062d050403151808090f0d12050a0207080703080712090305210d050406150f0305060604020a0513030b010e150904110f03070806 71
    0x4119661481c0813480060750283e540c014003807900700404542e910100600c01a180d1401c808003100c0410034104a030496003141c40020041c407426519195401c0310307003107544d0401c16003003100c1d248040060311703d12452000a00391056105040c040e801e070b590000c02c59507214078082c2921060307860101501c0c1c2c020ba007244e105d290881c601c00f090742000c410010000d544040c2a6420098421042e170702904001402c030110b00c01d6060214101400b40800700c02148202020707500c9946510b89048080246000c00d4100100c410301000404c03170000b840070492803c00d01046011000182500082c400d0301c0450308030750709000500042003107035072110200c61082003040401c90f488082c40340d280382081c403000e40541e201030301043c50740c6441d50041c442090a810841d181c00c025800800c2246001d920590f9903c50f030030010000590400d92840d4450301c805800400314030840b00041031100c0142014051100b4021014095110065840c1c8060002400c49041560344c1c2819942d519003281c40c0c840c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 977175773 1250 977174523 977174537
    0xe011e090b0d11310c02030307170a0906091b0501050906071121010e120405090708040311070807091b02060403080408070c0b0c010e0316030305090f1c 67
    0x4104800c1e12641081807070051201d49070200ca82c507007400010681002e1a0302034041d04002107048001001501580844010b84000559050b040021203a05500d00815034100308100000980c2c08448240b0780440c06007503105a84a900c1c40034000c00f41e400d801442c603813412081c4818050030300443c111040a40d42200320803503c0f9001160180150910036400c0402480300704c001a80300c00e00d01801d1080030b0500311242035078038102643c05140441158469641e800c4001075203106021240f100760003010380a00d02450f02c2c001c107505500080a880c20481810301007010103106d413085a000024480840d841c241d02c4140258a50000d03104800e01d042c0f070010720019888510200c10a1034003540c0290060f41c1c5e40e5103094400305001801150500f4040108400145000461201600c128010280c0f9005c080240d9030841d80418114081c0c0e500611122050600041544581d9a4507140214140d03d814104520300000100d4401040c007500140c50902c140c1600c00c4112030640f030351400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 977177023 1250 977175773 977175779
    0xf06010510050904020304080d050408120f0103020105181f0e1306030206042d03111311090f0f03060a09031b02030c1203090901060203030910051303180e011e 70
    0x45020720040540801003981403041052070728080d409981d01501408065103054204502c0d01c04443c0210b50071948404049041100c01001091040d4050030000200c00341d54150740010b00103002e403120600d80310681c9100d0082c941c075072a40421400d8125400741580024280c80a0400d8144642c1d60307007d408c00d080024201c403418019103040780d8010305007078900f50820700002e606d601c0070145200f20f103400b9420010440f401645d8000118068022100003407440010041c407624071485108549082646036120648003500f1507202c80030856810084a98801c081203c0c2404c0003400365240c0595030400c5841090764001c00c00f00740c82541c41c00044a1543c483c00302d880d04680002c0d4056204106030781c1d4604010302ca1035140c09207901282d00b82041840000d903075140c244c21040040c0c002000f80700709400200130881c0d10649440c020b110354581350031021005da002210290401164030307007040000000c155064042d048182031305401d9a111a0340d4120fa00d07034018200e00d114034000c400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 977178273 1250 977177023 977177029
    0x60d24170105040804090b0118031a0c0c0c01030b120a080a1b03091a0d0f060801050901090f0f1a07031a01031109091f12020a06020a1a1e0103050f060105 68
    0xb55218580c0080c0701800c050a10443d00d00a0050134030160600c51100d00d8521020b602d420401d005500c181c0090f06000d0a84580e5080c00300050005641ca1600b8000c1c414001e4011030f07a460040001c0c0307000260003a9800005030007000d660386454050168052400500c0300600c001c050381c4140c4d44070054000c200700000041e81c0750342407000d40000c0ea004000e0041900707242030394040c4000c100401d41400400c180100403284c02e09460a482c95a92108021707004080c0101580301d540310b80204031f4220340340c0b6285098990240010b0410049030300407030070081d082c940031241440642e10a1094604910041c00410040e01c507403140a01080c10b0f60040e6200f4002c0070114040001440d09048144040c0105414046c0244c4000c0f1100d401000c2000c440080c00b400a15150542c080303042c1082c01803001c007074410b0b080b01e81150055001c0d00086040c04132610b004418400020200b43d0728010000c50481d00c100b84d061001c6100342c000820b00c900081c401c10100a140309642030f6982c4c890030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 977179523 1250 977178273 977178281
    0x120105060307021b0301061d062e050f19020a1407031a0703060306150f0e0603030703050c0102090904240608060114010c12090315051302060d241701 66
    0x24140040e40544c080c0002044040340d600c0c0000000790011641315201d440d5517094040507850707040e05000501c2000180e152440c80c440c990352180012080360403920006400d200603108400c4140303c400a02100c4210307484040760301d0800070740140d00c200360310001d000b51103e46c0010182d5025610200b18204041c010480c42c0840341e01c40c26004a94518080480d0b03601e100030024401c3c1565000d0000114500e409142c840026246070302e860743e4207000600c10005060380004c140300c04540f007000170f1510004200e56074180c15080c00e640300d616011015019124030b18030250021901018801000036201c909a4001d050301e11040c40084148445001c645151140e12550351104004103d10780292003a50400c0c1c0c8189032051011002e510343c00c045000c4603401c1000148442010428000c02c0f510640002603150020b10590415481b114800203a2001c0a0311980000418090903201036121000703030300105054003031300080385060650700c072103510403074550001056802c001e0b00010b00ca = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 977180773 1250 977179523 977179531
    0x2031008150a05180607080603070f1a07140a050102120a0207020a031106120c040f0806010b0304021903140604060c11030d2c0d1b02061605011b051201050603 70
    0x34140702c0e95101401c001500d40070700a002c1251800b00d100d84400c03018440b00784036440c0c80d1540d00e1642014002c2c1031804005504c441c0f000510117000b449102e000d540840c02d51910b180381c1684a101c0c45c100001c1505116844440314420303207003008204203040d0050310b01000200401c00d029503900c004181039100e80304000b0350150050401b840014022030b10241c01d41d402602060400d026003501c1a80034000382c0f0542c6a01c840030a040010026280b00707240500700c00c00161280e549444420703503035404040e1000f445219034888404400ba0500c00800056820113400c028104010201507203804041d50103a4610781032524009946018110040c40c056245000750f1400c081014048001d1000201c04031810784030300c0d0b19036441c400c2a00c1c180980c07111a40944100c201528001e4804500c02c6203401c03141c000c2c4070440c1c026a6484040e5400b80c0e1070100100c0e0703034000c50300d017007030051044040c8201a4608071180440040e404400fa15201c0d240d61003458842c0d8803a020401140000c035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 977182023 1250 977180773 977180803
    0x9051e09190615090501140105190503061f050304020f060921030903150106081b030408070f02040f0e060907030b06190503060c0c01152904031502031008 68
    0xd503288200d5103105a00c1160710b002e6203001403103950740395031a99480c10a50040040640320401440360403c040214251041c0900b0802d150a0198441f02a09641c21048030140100403000950b5a107401c03041c804500d1810343d40c04406020010068030a0300300780c500f81d005010030805151139007441d0781100e00203c0018050444409101d00107442c24070030459480e220b020900c1400f8041c0c804020028024404003c49120b940c10408010030641c00144404070108048212500c0c0f8050681202c2e0400d400001181d40c903819070421418ac100340c414003e40040c45c0030000c103c03950880e071045000e00c007610306851094841510b220350345c110b1800007506401441d030101d05207140101071050034801c550b0046503455951400030f0b003080b504548404203540c0000d114421190280715070b40c04001d51003942040e19092010f0820547c0d410048166200d40c4003c0946140360b100d01600d0040d41e128054000c032411210311140650000c1c2c0314501905c14121005c0342e0000049448442c2d41005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 977183273 1250 977182023 977182033
    0x8190603050705130609060e0906090309010816031d0601060914060307110a0b010603022a0c09181902010305220b1e1509090f0a06020a0207080709051e09 68
    0x1002c104144888086074141300ca0740d481d034001a06d9081400b0b100c00800240c0c03040e25952410040c0b0742c2c20301500508a4a440c1c00403c40f44190b87e8101001c00d42018084510003039003d000513050300140b01c01c0040f0603589030f80525203a0620070008000d4140c4840d47d1f05c0040480d075550314001c0d02840c903440164060382c02d00001d80c0540c4078440c9802200bc1d10001c035440c900e4ae50312000c3c01400281c028400090700014003030000040c021040c00c8544100d120115940b050081c000d847d168450181445070300d102c00842c0c0c800c842030b80e00e03441e00200340382035640c2c054440c8505801c19070201744c1240880d062500050301c8180301000004040c0c4101140e00d1a52215030ba00103641c0d100801c5810342081d07040d08030388640d4160101c58801c15040002005a0480070200803070002c0041c404215076100c001114042c0c40c0102d0031111300c80d4449805621203d8080c0160304140c019003101c2c4051107050800107401401da04001d02620248941c02c070088620000c080c60340300107d0b0b0400701903000e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 977184523 1250 977183273 977183279
    0x1060602030d11121905010b040302030a230d0207050a0815071b0b07120b060405030a08031015120c030b0105090123030109020913090506161806081906030507 70
    0xc10f400c0201c03105540c02d59a450110412180f4004000950b4101880840801e204003882e82c03d104103400350041c050b4403810580303194002907882d8440d02d40206240c03080078010084104040c0c0314a6107c2010050300c00070345041c2d80095840c0310904c20144100300c0d0400020b8540000320f00712a48280041841c031080da06c01c107040c0c4e02460390790306007000e0917158100701d0041124004401c0c003030500c598075500140050700404c02540c410700b1001d441220100002c100c5a030f0000b030000089580308215035142c0d40c49010844d0301d640c030b40c0d2142130010700c40780301c0044856010300035000e41910701c401007254552090048084410100625011032410014607000e90300403102001101400c031303e0240e4500045514001d0381d002a485140c51a0300401c4a062500e441d19680c810078112090802501201d615182d54544029140510303042c4011030f88c42c40188590702074503020504500f601c001039520680100284000c0b5004048002d202e800000e54254900441c000c480c2c001000380040c2d41 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 977185773 1250 977184523 977184547
    0xe060f0d2a0809120a0e01031b02030301092301030303050402030f0c01021009150e0715230c101107171201090b0f040f0b011403041203090201260402030f0106060203 73
    0x24003d04840394503ca560205039250401c0001000d682d183c55079400c03100c0e143c1c14000750030380340c0c3c180608406803111203d401445034000280e0781111030030000410018000041d242e14480b058840ca01c014034140004802d240c1c16402c01c41c012403003901190340143d645585140c694180704582d50050f04250b00c025030340d02c81030b040044241c1c0210007100e150603041c60345800702d4041c44400c5035582c111a004120584890829400000441c10080310034100f03015442e45c0d15521142d11702c500e071400b00c1c80b40c0e4011010001c18016168501c4200840e61038801001d400e9080404200c0c0e2448841896030b510003001c2081d01c41d07480540000c1c10b03040c0d00303007041c08014000617480b91b80c122008004541d540e903500d028590016234035801c0003401d074001500042c6100448603960825180400c28040020082403603000d40481c0da14001480e1001c920049422041054201c80d40200400c251099040c2c04100c41e40610f10032802c60710b43c0d040c00741a180c00c0c0c0d02c05104030400760f00140100075650b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 977187023 1250 977185773 977185787
    0x60f0901180c1e0206090d090503030910030b06070305280f030504260d0b0108010302031011070b090d0207230409020a05121c020a0b0a0b010e060f0d2a 67
    0x10b009003000aa40000c0100003a81c00c0c0041054200691052040c80b000030024025200500c500d031411510103820600401c1d031703920a003004180928145c1c40c91050b85440b9606c81025204000c05260b0398035000c0c100201141c101d05440d02d0b4414004404004020007a1401c07040d02d1102c2c0c5902c404200001000d800602c0000c000360344501408072500c0708101c800d013074020211842c00403140c503104d5054050302243c1c2c0c0c400703103030b414003182c0030041c005640d0019894100340c450400c089000001c0b003103080010b000d0200005d050410000601c54035210120300444200c00507404c80710301d01e40d928440400c14028140400e1181907207114030b0081e062030707042200304900140c8032036a0195960007041d9031400101e040741403070b001001c104401521800d500c2880907000c0c8020161880181c441e8240c011029012040c0140d4484055102c0d90117031248090101c2c005060a13151140ca504465403540521aa215180c2c0382c01030600403070905000300d0710f100032140300e510307036010200b0002e407010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 977188273 1250 977187023 977187041
    0x20301120b150a06020a031106060913051218100e090604110c060a051e010620251a0313030509011b03090f151d010c0b0f060f090118 59
    0x1007a01c00190b07041d60f152000c240005040d20341c001c1c4a403403042d003001850340300c0c0700488094a412080502c0300b10fa44611026801400c81d1b613000515a00524000d4903044882c0030801e142e40c004500303400780c003071420703c591080d4005440058542c00404401c503040504200b400b41d0020912020075241e040540c03001a00b11107800c42940b40405100741145411411030f10301c401c580c1c4138020808256901001080d9044c03142e180360f50b09505006028040b40d00004105d12a10102c0442c482c61320740c20080310156080001506004c0704442030b62090aa8003802005442c142089400030100c4e900c1c0c04071b91040307070540300320b0b1082e00451f40c00321407580c000f1000b40d0400146c41e4810301e4007455100701c0b11401d8404e8070345034419440c010411074001903d601c01c10a2107411a80d002050390000040c44c5081d0602103411803034031181c00181c5540e171607070382c018010150340400c0081c440d43c4110400d00424085840b9400034121504011480c0c0d000d008a0108514801c000c40e03481005030042c0401c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 977189523 1250 977188273 977188291
    0x4020d1b1208130803430804030c0611060f070e130c0305130305090402030a020f030c0a080703090201171906060e0306132006362b080409150602010b04020301120b 72
    0x4142c69048002120707110301c0d11b0075101500c001504208004200381c13400010710780c5041104074a0303004d5906a80b44c01000b0704050540d1a20400684c26620078490740380030040041c02c624400e840c0e20750140040c01000c0182c1c01007450301c0042140200203c0380c2c848804c0d81683e8051500001c001400040c0d0409490000c10980910610800f9114030024621070503401000c00d440d0100c80c203005200b2407000c3d010ae002d0600e04860000583d074003d00303101040111800e81c651075100c401c900c0c00c4600c010f6000824007441d005000c10101e6100140c0c16510200b241110466218110200301030715051000510100c807113620500d804d080e06652003042e0400409171030800c504551621100030002c0740c84c101007130142c5004200c84902c0d002c03141c1b4510b0180c0c1c0c16038051f4a203090345c504820344101000f403080011481e4400304200710040b01d01403c014030041c4010855002d1b0071040c04490f000b010099420320b030a00c0c40c0c6081030320a0b281244d007002403098441144d0385800e003c0400103400c03841 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 977190773 1250 977189523 977189617
    0xc0d0e06010503030703052217070911090d020a0b1c06051504061101180305040602060f06091512010e010b13140c07060902101206080604020d1b1208130803 69
    0x1440e010701d048e00000504826980041088004901c90b0805a5079000090900e262200d0380e038a51880c00d080e16008201654603820309030140c000508500482da0282c1003100000405140354600100d40c540c0010320b50380103101040e101c00401a0885003200d140903501c009100c104040c0d8801c404080b00f60106000014150300c00c4003100c440c0026981e0180c0109000160070424140d0400c0039640c1b05807071811150241c1400f400040300e244020b000d281d05103240107030070901a69440224002850484003c01407940d101c41903501030004c0d80c85c0c4a101c0c030380d104400d182c080c030180110200d200720b60f85485030b250394800940c2c6094016002c244c4010381d8880b801c00c0107031500d246c01c8007903020710b23214501d070329415441d2141624a00e4000201c190400814000180c5075100000040c1e03500028484e06480101180240448280d00400d0079422894000061003209070007041b100c02d009400b0700c0420b407100303401d641e20710505005d00a160018481d01c00002c02015134464a6284015411 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 977192023 1250 977190773 977190817
    0x18010b16390801020c0d080c0d06080f011d0d031e020a0207081228031104091a100e0f1512010810050c0708070203010f02030c0d0e0601050303070305 66
    0x401c402024a494038501c900c0d40074040c0c0d041600212250042010704001e6290044025099484d24001da96100c180070700075010912900704c803002e451580113895420070030555074442981d907800b04013400c66a0307540307080a00084041002015040072a10380c00038804c00150a208400400c40960381c04d02c0325100215071280050580010044680b00e94000c14240e42800c01280c2410a98000170f401207400b040303001401d06401d020f00040b03141e030004601c000c880c5010260094050032500a410840004011461446541c80039203031900b809000c0e440d41601c1b034248540503100350601300100d501d6030f200340d0301031074502103441e045a8003a00895000c10402d108861039001688421a4004150014440e0314000c0100d05641c18040c0414040750038030b0900359032070b489180809847d08074002840010754400f500050b005020190003190340e450550015005501321903a03840515080000c005502ca90000c4c180e0705a80c4000c025610740740c582d54081d0b5480c2c0c0408481d006004d81c081d5a4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 977193273 1250 977192023 977192063
    0xd0c0503251704080a1403060a09020f040306110d050604060e1603090c060309030e0603040b060613030507060914030106050130050c120f01060915050c01050a0b18010b16 75
    0x80340554450904d40381c40b900c50b542e014040c05a061030301903060300140100b007460740d01c1095000884c0c02030040180e55101c4407115610b1840355410281c4103605002c502110041400010880200e03013400400040c0c071401c04000541d0100e200b5800b44048032804200350340c1a00f41304000401035400d0010783c01505942e12181d544907644034102195807040d0319024581c01803602c2c092083c0465940d0710b0342c40c0c00c0e135507400204409440300e8080c80000c558000009092000c640107960070078101ca00040d61b921000b0000801406400e0641030a28002a85810140100e500f6148161550003c42c0880055001c0129400b08140c0200c3c0c500f0404049003601403107054005c0b8044103840390f50710800e07404505a410064403440500c1001401040340d641d025031484240c0c1c000b441c500c1d0748690710b801c040b100c80c013030b4044401e0306510f0501441214007940e4420744003a1815a00d0000c03100354600c000711454805d20404400d0002001844515226034025000c1503109000684407040d40d6106 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 977194523 1250 977193273 977193317
    0x60203070605060d061b14070c0e09070801020f13060c03120209011b0605061828020d020315030d02030a080a090c0e0c0d1a21011e020d0c050325 64
    0x1200f1246d031310210380c0ba000154860545070201c803c0e4040300303141a1995690794501c201e2803095010100c4c001000c01c10b400001d00c00b000c01003038450300079920741403c8103002d0000e0340400c5c4130600445001d00d000610394001c0102c4181c803905915a1100060395042c188040e6003e403044504101d521506180d500141c0c2090701e01c960f016800000311742c07801005208281a215000106000c0207104004140030170788141c0c0c040524238040780d1020022544608081d000d0050b1860a4600220400807210004451600080c0c0704404861001c0b0040500b83c0e1240b00c0d8508500024140c00d0014005001c60b1300032444c000c0c4500d4251101560310040c12180d4807041d106a02075140c00500c000c18104680250201c4140c084489044604424001080781692403500d9408202d418080f01d42d00350203500842c045030000800c95000c41c0e102030300e68021352140c000f0700c4035030746001c105007240b9100c0c1003981c1c0309021120454450403a0b078107080c008803403260358480400c8082c4910100ba5100320071 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 977195773 1250 977194523 977194541
    0x30d0c020102040905060d080f0706020f0d05040c0f141203040e07081b04060504050f0d02100f1d06030106050f0408010c03050405061302030318010c140604051204060203070605060d06 81
    0x30006803102d04040901050314000f50650307108550510086000ca1f200300c084441c0d80036614161542c0d000c851802c0e03000b9008079040082c2855000c10444154415034210f1440f89120300155501a502d81d82c4a074255000c82c0524a00714603000320949141c140a8408207800c070402041764145aa07800c4580e070420000c54901d00025040d400b4014210300565060b6210400401c03428102810140300911500030b9101c3c15200701a40c4840c004543c8449450003c01307500074240041c18481080054065071982c071150000500d15840c00d00d014201ca5515003241c20010000c52441e4640941104c16420010500b1624041000005542d02c4c00348156101c07801d01e03480c04a09490f041c00d007207044c804001c3c880c01024000d107286400580d0040200c070110028480381100980c04d04004841c8011a11002003000a110210710303400140001c40c40d208520030b8003150900401c500b040c0c207180c05284a01740169006110b01c9001480a81040c0d03070211018000e5148801551a12810750740c81d04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 977197023 1250 977195773 977195777
    0x5010501090c0f05040b16080d0e0303090c0a050a0303141b011a1207031b0b03090c121b01121407090510050406170406060506120601021501081509030d0c 68
    0x22119400e0369810441c0c07160f4129450404034182490050100b815202d400040700300c9401400c2e820301084580c40503108850070b02001080309000007000190780703034400d82d1158100d2003010756503d0645407008089041d00d5001e09204c250711714542e400d03103441c001d42030010b101c41c1c03007030207403400c229402080c0604040500e000400e1650300c00180c03058140d1003c400f0b80c0106030900009804c8100040d030642180da102c41c0488500304070900c913600020007030f08000e0640b20004240000e8100000d0b01d0180030b04c04903400c0c02002d01021010360741e014003012000d9079a0a9110b50a40c940c0204ca424140070402640494160007044d40c4513020072007102e0500110741000d0090125040800181001c9000ea0400c0d6144c5402c080000d0700c10307a040300303510104115080c001420041180c000303000500d030142a00c2d0b1204401c5006101050013112410f005104101c00143c05918841c055412151410041c20306440d1003407005001050007000c4c00380b240720400800c11081c80a12480451130825 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 977198273 1250 977197023 977197031
    0x9080304053316180f0e090a03020a0b130215071b0513090f050304060804060b0303120601050d110c0f0f0303090c0d17190f021b0d08070501050109 65
    0x2080c100003800300c1d080c0c41c42c0224401d04080200c01e159000d80e4a4101a1607407180180382441c2034120380a0001c4000c8512044220f80001052682c01000381d0030340350110070390285075076200d010036030f9074035000805401680401503c0700414802d0903681d40250000c01d811012000c50307004111030b0404451a08561003001a002e001d202c5130800340340c10005420b07280d802c4640b8142c00109043c801d49091900142e40c1c02c403440400c40e924141211156120b02a0f0380c035940d46901c054101101210305450311820708400c0c1c00640740201c11501001d81009010b800307611000011034254000a802000c195560380d4034000c041401c0e0301402081d80404002c0c041080802e1809007481c803045900c0ba2a94418028420000d0f408512700b04600b1041c0c60903d901031a034185140c0030410300608038005000003c4801680c00b204d0b150150011154440401c88034460000300d0340c8464190f000b001c1240b58580c3c0304000d2a059040e203e540740145030040c1400c0c044c1c0c48441c00c42c0c3c8203a1000a4450759 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 977199523 1250 977198273 977198293
    0x2030a260c07030806121b030307050f1609020f0403150902040e010518070f06030e19060207060e060708040b0c040306020c030d150815061f0201090c0909021c0302010908030405 78
    0x8422600d82d4086003e4540704020001480240d940f55000c1c5a0040078a50000007c2901c0e1010820f441d03e01d0382110440300101900c2e0030380c1e03031150011041c0321b211440c866008545c031700c564000c480c05001680c5035a440c081c919115401c007034a03008003a044d4551524542c0015958071300a103000d90300103e00010341d604140c0c2406901030841180c0b0003058100c42010403a0300c0f40c211420003142d4440c180890705070b00c030541050628005005101c0703001340c200c1d0301006000031035026102e95481040108400000f004150b60358001c1268840c000424400001c1d001a01c1290030783e3300f0001d2100c0c05401c068403540d48506903040746040020307540c00420104500708031400380c0e0050f100d041084402c41030070304030100d84136001503001c0350141c60020085003c0340c881c0004031400750380394440a1100704100708002d01800d800c46050b102c0d208401340c0400c25000900c01c012402e54010103200c503440259644100d00d00c5035100940a40d562a660701c00824405002103204034480c00182002a40d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 977200773 1250 977199523 977199527
    0x30c0d1e050a0c0504050f0409050d02030430060b060c0a030c11011e0318020a0b12010b0a021e0c0603010f03050f1212090a0507150305090d02030a260c0703 69
    0x11000705042d410a00303029a20075543e070480c080724261001034400b901101304040204000d050194801012842201140011554040003400036a40c0319080050744c0c0c02401d4200003110083c0e808003d908103c4105200001c40070740c410300c609607000e8040c03420003031310170601401d11200d22416000315a542031320758100610304500c1308180c6424203000c10780c2d00c00e843c031070030400c000c200000c42811703070f10200510725030301c0082d21041e550b40c01896480490340341c0443c11038540000f184c01d1140070480c0004200d180d82c5000303032403054500d54000c0410840300354a031104044035000300c18241c0140088031400f501c5203001076010f0b1040107029804036207145070040c60100c460146400e01e070410324031281501c018a088030740013031541007151025110340b10040d0504101107402425842803400c0052152449036a2610003c075a032010002d546e50692440d03140c4480301030341c4d4010303001040a181114005c225424040388118034004a91055203064114040182c03100d00351540f001c1003481c201a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 977202023 1250 977200773 977200781
    0x1206091508060403080f090102090a0303030b090f221a0705090901120f02060918072f100c090906030c0302150c2a0904111c0b0c030c0d1e 61
    0x80703081030080c80c0e01e00e4aa10020448407001c0c01e07403034032901c080000c035610b410250140c451445e0b0041c0f044841d00e81d00d00d0b0140c010b28070521098010110080090390929507009000d04c00d144050070800c3c401004a4580305402001000320b411882e00111048402404c0113030790706c95a91a03c1c1c4a540342425010003041c164141d00c26107205504000c070748002608400001142503041d035401d900c4403009800a01c0451858a60a2561411004220302203901082c1c04000c4031249080301c07100001c008404a28162000311003400e43c4c4501901c02c585111584000d0304d40340a450815051074035a480c000540d007081d030082d03419489251040c401d41c0361031444002508004e0507090324241000780015241c3c80158000000300f050100008110000e618441c0c000d1480108086103d141c00c1c0340110440c2102072615001e06280e004000b0009035290000b514590003184507100c1c0d0303a640040c80d0050f440146104205d039000d00c45400c4d100110b019000303514106200f040d071440d8140761080222 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 977203273 1250 977202023 977202029
    0x605010f0509010b030705040b180607060605090c1e07060912080901050c09130924060807090c0903111c0b0901051b09010c061d03070318030201140a12060915 70
    0xd9030b010024409087d030400201d50454101e2200ba945a003101d849035141c000181c000181c2011001913080100000d41d403007441a10b100311751094150311000e0904606004000c0c07050081940704480c00340a481c1a00a002000e01c02c29010801d00d100f607503160200001c405c40503002c581a4803c0c0500c1032020f018180c1d02412042c0002d0a0084d00400100382e003142041c10051165030740d03050010b0100c030310300307040790b94241041c2503410302c21105c8104010b040e04e10070545a4050700308003041d40107207802254810003466454402079030075a10b48540f8400039101c004da005000b11015420480c00d4160006001d0141030384404920703142c2d14141c2903a200600c2408a00d00103174440b0001c010f4101501e00b14142880c107022582141c1c5480002068150007450b00c6481c8907110700e00c42030001008180540c841d41c0c542c04100c8030445070220000c01e0f4013000780072504950103412603a811070040e1000070200e01d014440c8030046044401144c01d80e411030f800c030540311401140c5070803501d0510001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 977204523 1250 977203273 977203289
    0xc0c05041a090a1d1f0207111002010e0613030807022e022206021207050309010c03020c1011160806070507051e0109150903090302060c0102070605010f050901 70
    0x455454280690458510781c140d4601c203206030008203240385000e0303200d503010449140c0c00c03100b03040600d20190303618070256001001455948140603840512802643d92841c2e05c02865800c0c808a08200070740c1c400042440e008640d41c0700f038241070191081100600608901440c0390b8903c1030703820000c002110003406031081d5400a0301d51403c4007038820b9a440b40c0c6008800603a4005600c4050001078405c1928a080c0100303021280c1080206140492048a07566000c0328100c4d04d004000c06454055108060421b401c144181d803440c2d406441c01001540c803e10503121000a040d00140303290000d0a090000110038164410418504000303c00030003c414129030343c524903015580c2d5603100c0c020911030410001007550300411608100c0032149199000301c510311007001700321440c02082d0101d42901c520b20711014054508040d0f01c502400280c040d03440d4103207141107030207020840d400100c444103c7d40d420000305001ca50f061007403d004c1c0030040032085c2c1e507034617050401c0010081030304083c1d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 977205773 1250 977204523 977204531
    0x130606090b030d050901020a140304330f09090e0718020f1e040e07120501090b0f10120e06180706081b13180c0e01050d0905010e0304060c0c0504 64
    0x50315560014940003c500c15180c60ba6a480700c410040741031148a1800500c0c90b10640b04000894401202400c19a1030b802d056000c030001040c48900c0d252020111081d8150041000c030703c0d42441100007400c00801c50410120482d81c2c1c124a8040b6003006002d0490345d00042c0050240c91405402c49407105600a010350601c41c01032100f003424414070301e00c0712040501ca400c45d2507540800c403d54000b04400f051100a038030b4070180290086140c0a038920440d85400008288043c180c800e0400c407032009007034001c0800410f020300031684064003600c400c1c00780846590101350303224060b5406842418001c0c00380c0b41000b500400040c5000014402141c00030301090001da980640d8096002011802c610954442c2d404402c03400d1045400c0e03048503007448080400d40004240341c280c0008e001d0103080080980c501c0045519103424200107002840c1000040f604429a0300303d0100c03d8041c00001540035107d0400b2071860344660701002c04a10007820304414042000e01c11030092106444c244 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 977207023 1250 977205773 977205791
    0xe01021804091a0403120c050a0519020c0418110f0f060703030905340317070201050435190b151504230f01030b03120313060609 57
    0x34200140d25101540695541c1e0708030801e0003030114000c404040d1101034010f2a041c079040c000c01c0140c2c080509280142000b84280c10b580c0b080c0b0403902c0c5450599182420140003480d10002e88022009800c1144206491a019917a40d880365525104003060350715030301e444514050407040090b504641c4100002030104402d034650b01038195510b1401c849076a60380c002854150020400f4807400380c0244680034429501e9150000703101045a1041e8040c403202c0300303100d00f8004074403103400300504820002070f8007a01740040001410321184141842800c00f51605421621210a05143c11a0161104003103c01000108400840c080303100007a11254146c000101c404500101e40140096009070000780d038401e500300d0681e07a415008261441903000c489061606070414028010300000040c1200c040001401c4c0011124402404801c508a90381d801907008007000c22000750540a01d03c3c107421041c1e0000011807050101c411420101c024178148501211401e030440d0308a60f00e000584 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 977208273 1250 977207023 977207047
    0x80f03040807090915050f0609010839120d030507020f12070f060c030e0606270604060312081605040e040b04080d06080c100207061205100b031503010e0102 69
    0x29002d650403681c001c1100c100914254900007403a0310060750305ca140030280b00c02e082000c40400c3c0965803c0300c00440c40c0e40c0b01c007000340c0c0f954903001042c2c2c091143d4240383d00301030303000302440d0b010700c0311100014850160040106201c0e26408007603244a03005140d003401007540501c101c5801080910042040204d10342166513544688180200d54030b00110b07414042040a07541d00222942c0407509014030007800707a002d005030068441c3c0000303c0c01014002191420981040043c200780345800e544044005030107081c11a070060510794100b6200d410101c00f003440080c01c080b07148910358407a101c501d8000c04080c1000001c180c5401080000c100401c80c440240c16540c0e000341c5c00400c40c104980307440c90415201e21072503540c0005181460f00c001806072010070301c1c0031030000c00e90307404500e0824440100d0700e0701294005d510104090807890441c0210580c4015402100c640c110310140c0d032030701485812500210f0b1b00d9046000d90304560903050800780034210300c1011031030003075040c4510790a035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 977209523 1250 977208273 977208283
    0xb0303090301231e0a0b0f100302090102070512030409021e0c0a120c030807050d090204052404063c1502011a01140c1204090209101106060402161202010204080f030408 74
    0x301030300480d22070346a850aa0303651103101071100740040c40c108d0b411140c0c24020300030750070034000c4501600440900158600703200d100940784200c01400341d45030900740911000290858084400241c0c011480458804c410400500501c2c00c804002d050340c0c032942c40e2110840b41c07100050340803c1b03400c40190000a400000c00c503081800c0b41007640d22241d104018030000d04d00084060360050610007808a00b01c042485010030703140e800b8042c4650780b504c00900041d10036034031980140d401c04c100e82c41074403690701c1000228100144003c0c1121031460041d541e0400280e08921380e981211640c44c1840754092044100e80041c4003020102c000c1c041c00041d20b4074402c1464058250000500f010440e441400300c802c02d03200b103414590711151182503500007500044c0c031050088034000c1010612600485c080700110032448020315055943c5c005001c083d41041c903034254081e510454403000514111001c0d10a189203a000503100c1345040c2e18185052003c81c05070b00d06400c200000d00802d00007040c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 977210773 1250 977209523 977209531
    0xe0d052a06070b070c020d060c0e0102030f03010312110307060507080a1503170d02030f04021503090705040b120307060e1b090c220b04030204110a0507060b0303090301231e 76
    0x244580b9030b41e5214000c5d2521058814001e51000010740c1c09001c201d8560303c41e580104869440d400701040c03080c01a40c0e00c0c810f0380e662584241c0180010130002c3c203841188003164a09203418880c0d40350001c0110b02e10f802c410000c444640d218420801e50550009071960b20002000c0c0902c200c1c106c041007010a080d484c00060104511042c0383c9101d542100d04a80b01d00480b1001150740b80307414080580c1d13090b0140d0f001c81c814000e01c0d404000d8542000103036402148108080d0030202d1800f0308020041610b40055504503e000c2d02d1842101001d00c00742402c0ca00490300480c000c115952081d09001c0603c4010000d081c03003101c0055903880b0f6030041a03020f036200c0ba989580d6400b00c0c03844124003030aa00b4841e00380d284c0c1d03840801ea00380322001410440e4400c8d181404400801c070060401c030b01400c0d4a40000813003e03c0b4400205185402016a0203000360079240f50828160219081d642c0c4d505103034010710160307039080380d00025035a1074a82c4584242d0f4a20070014628245401c0740d04064 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 977212023 1250 977210773 977210783
    0x5090f01260c1902061506070b1810020f0703030e21030c0909132d02011206090c031e0c0f1d130608061014060a0e0d052a0607 56
    0x2002402d014111800c07191a40d075030032580e4403000c090680003561984125882c1e01000c4090741e0010a500780030054520465000070f03032540c10f5071015000b92100860a4865005100e04c81e8560340d10701c814401001040c003060358590707071915941809820b50700300740c40c0b2500b517610480a00320011a030250744080301a413002d500f6aa5252000e81ca1722500aa40709160f1203407a480034441a03000d43c2c60706400e524829401004070242d081d418101035800c50743e03950794070364011078060010361040c081001418200103000491548800400e0100c0300a09044004696613010b4224104148010041c00200f07240061019080301c0c44000c1205005034110414811850008052456581c0b009491510064900c1005824188080000d03040f031348a045210302604011454202400c1d070030710281c514501e00805c07007101500034044540d100c10051005c02c0840c1f0b480c86110396801c1ca2100009000d0f40040031284811440040b2640c65044c1d4090050200d00011645850341004d40d42c80b9a041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 977213273 1250 977212023 977212097
    0x2010813080d09060e010c0c0c05011b020a060c03140a080f0901140c040f050307050303180303041d060f031c0809010f05010306020705160315050402042a09060c02010203030f13020a0605090f01 85
    0x722568a1a1113343c60087d4422000070000c161550300c0690354003281d010766105030920701104111000c51083d40355200001d9140d00c0002d940034400b941040c3c000c00c6940c0005a01c3c25428890840705c0390a0b60001c2c03909100080c2002000036a500d00406010102d000d0241d0a04d88030010756a80300d41d1003100f040ba200044401030564042c01554001c1a2250f8000c0e04844c1d90344000c210090120303405489200b0312000c0041c42c0c240000d685030200000040c05110701c40c084010f98001000070a003440399034945080b08203c11711070141d180214880c40d00583c4440c00f502d00300c0d0400c001c025003041d240c2895001000411005c881480700b800c6400c000140b50f8075940003207400b90034001d0303034162030360804600c10000c0c1182c44905d110301017459443d5624a9201c1104807085c01100b103001e40103034424404200b02c04030241000e5005045000c00326000085e5901003080e00465a0000011440104450540341810410100c01940c00d2074192610400c28880d103211014011009441c2c40c55 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 977214523 1250 977213273 977213297
    0x40b0d0902030708060403181a12060a0807030308160314190209040c080a0f051302041a270c040f090513020913050c0d02010813080d09060e010c0c0c0501 68
    0x410f0040314064400070065441d14506801c01400b22542c81d0306080840003128400101d14420000140362104190f0308070f40b4046417410b80150604018001c91b600c590307000000262840200100c6005511030303202d5421b01d15000d1011600d424082703072010b080c5030910814103c0f08030300c07411241c0c0c000b0f00f0802041e41c06040000a00080c064640c0c0142c1141c81c0503884c0c1c1046400c10710341c80c4102820401400141c24010344001034030801e5903400034a2010030961001403400740c000781d8080c0400b440311100d00c0080c20000c0c40301921108000c003501c65444028041240440c0010341c000d03c060042481e10b0314001000441d075403980700d14031030b09503514042800c400320310502449040d00100030403403500b4040380e8641c0804038105c040325644102c11149500d800c1211541c0345141c0c058585030000d035a0040108444c50b10aa4216801402003251189d502c9040c426190840d000c3e060000742c031354100c4841400c407403603100210240910342c06c608001400c1d100100e81650428030f40a45c0d5804 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 977215773 1250 977214523 977214529
    0xe040303091208180d020c0f13050c0913111215040606050c0d03060308250510060e060603060306070318021203030703050f0103320307061b05040b0d0902 68
    0x49544402040c6010104400b125580e004084034015084000d40400c415044150960384011048982c00540c0042581c4101c5292404480215074406001c080c000b6405044090840744200e6070000007001c041000d85040c142038800014800340101d0411006020311501071243c0585001200c40303030081000a02680740300d0380149101c4101820600c4203031f88407480980a03802040c1c100382280300360140e204100c1d22034007030301d0110398014000d989403120700d00f1140300400300e80c0500202814158407910001d4070401c4038017181140b6801c000b8115080a0300c01288840141105110301c0d81401402000c1d900030484a0b00420281000290343d06101d2241355078094144020f0361042028000340e950480c00310080d8400d280301d0f9801c2026a0b202200da02e0700000030301001d030050300c004032900d504103001c0c0d03241e91400e41c0020000c0003102503c90010b1450740001411202582c80d12521031460805000d500102052400c003181850305084848030140288009941c86c0e03034441c03200000b952 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 977217023 1250 977215773 977215781
    0x30506011e21060b3001020f0d150f06030e19030509042409020c120a02120309031201140f01031e18080a020304140f0a0608041704080c010212090a0e040303 69
    0x403001808145d2040390746440d038032009000c4a40c1d40040c0030401d1080e078074100103208441d2040c0c04411078a041c1503080b5410b100a003103117440c448800c028000d000c100100d481010000038003540d60041a064609005036043c81440001ca860001d4884070724000a1f410a05403901c85d06c09850004140304000c07a0b1801e402491245e481d2014503590000c600c07442c3c01d40007400c854001f401101d40001c1c102c80054414132411503030600680080340040f802807003900c011904200b05804a0b070910501100000c40c014082e848000d40b8a05140030501504007100c0400f040b001c2400c0400c02d00340c01f19982c00000c620510045016591480783c0d10105141c5034403a00156000399006407035911194000e56240e2082c003c02400c004001038400702481d22010f100e004c000090400070700d040ca400e806844e01c55018200300c070155040e011007481c890208018000030100302c40104a101031000000e4209090a0907801d050b8004118041e1951100c007642c00403624034003e030a042e6620350030110024 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 977218273 1250 977217023 977217041
    0xa060e0708040303180b0916050306010515030406110a0e10020d14070602070f0b0405060115090b0313060908031e01051e03030d1418030a140306130204030506011e2106 74
    0x218441401c0c03101101f40002c90204c18000300003403074811901d9908165980302c2c03d08c6881d0340300d0050500442c07051110720245411901c186004201030300301c0c100e0190145c10805e071540010703520a21001c2140b40200405440d4005400600941a0041d02c01005003940c81151183d05200181110400415a0440700101e4100c4074051b00a0351901e8101d1103076a040e24155001d00c1460008240c9840305510f8000303031503041d102d520b0f44500e00710460840e500002d1080d400e8545151001011402c18040c0c0b50340d561244107078650360b2030041403070f0300000b2400c078525540401c0340f40180314949541050007808804070002e82007581e103041c00240380d0301c145000c8100036401d054005e000185a00b80b00e90040c5400340e2440041085e006a041c1d40b40071b2a040503002400ac03c11425141c480301004541192025000041f4000a102d100c42641d0160313004551315405500108510803903130f18685008400c0c200140b00c858641000600e48207140400f80301105906040c900c10818964041206 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 977219523 1250 977218273 977218283
    0x6061d010f121508010c050c1b0111060406090507061404090b281401050c03030a1e0204081e0a080f13092c0118080c0a05060f0a060e070804030318 65
    0x40800c0300300190107220050710680b041c41d800d20304458805070047c800c0d03d04401c40140140114159025098101e40e800810203060004421404128540900100340300d10b00030310000c01c0d2140b041c90007a00c7c10340c540c0d21520801503c0c440b01084480c10f202120b04079242020f000c03801c07446400000380540340000c90b128000b19401074a079960346654614004449604040d100c003500140010b40d40352145030340388036140c0c00030400214100640c1e803100074421004d091000903801c125071010200c2e40103420914050b0711940341000d501c026003d884409071000c60140900710307003c0d40c41c10024060040c0950507410041042c290482051b0420802006440001c2c07021505400d05d0325080304800e002c104020202060215602300c0c14000c988404034404e0a00440000e01c0d100c060781c135000084e1301c1d502c5000701400203010030410400517005180301c4c920729035a81044002941110225030105200720020020002c03665040443c039a846901810301182e103180c10114042d4610556800420b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 977220773 1250 977219523 977219531
    0x90d230c0315091c2a0c170109060c02071e030309030311031606060501030b0a03050c1527091f0b0c1f0204140d0512090a0905010e04020406061d010f12 67
    0x2d420368017a4050780482a40d105940e40f203840c07060b802d907900800f41000ba041000c40388040042d07c1008200f4100e00d10940000100c041036940d82000b0348941410b4200103074004c1c88240141010741c56286807280358130200881685c40c690340542040703c944409028400c69007519094400c00744100c49405210110708640307084645401e0b00101158041c0500280c60f0550000660402500f18002c0e00d40100c01040114162010030048104804c20300704072600600016560445216400c5440c81d5182c03004054a100c007030500007244001001c87c0883c90154000c20881c901c000c0c4500d042d60b9544036041d654982c2117003000e1a21031170050303c4e0080162803421004986641d401341c010350304201180743c044038491007048001d000c9481c0142007504120303002c1040349800c400800900700041d00240956a03205a1401214001d17071103d514001a101000110315091040c24003074100d90074801080c80300300103010554040c1314211414850420900400e690280d8044005503101441c01c1c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 977222023 1250 977220773 977220823
    0xf020d170d050702030711040c09180501090b032a0d05061006021605130b040e16080d0c110f0103020c0706030912020304031a0a02090d230c031509 65
    0x18419034480038114407050b107008003154003a0701c040129242240c00c1603200d61288041380800c03005100b40c01e045d505000c038901e800640422400156904000300c0381000803258503090100c004d6981480d40e5921030713000101c40984040140c43e84288408003120012000c26500700440c400c07004451020b415413195004001843c0d240b00420750990b541542541e0000c0448005010b100849002e05d640c00f244402c8480c04404540c1d00c040100000100b02113843e180503010079041c0741e46a4290124902c1300c0c07074203103d0782d4820403001c0c00c0800b00e450302d15048011030300c55604c41072600000c00d01c14401c0d01a01049603109070180c400c260603c0c0143e4040a036030361800740061043d00c100300c0c0d41d1501000f600707003100d00210075a001c0380d41040752102d40261420006071104001071824101d0369003402416010b40f141800421214461034011034898620000d8006181c6000340c0003025a11403102d0082688001c2a20010b1000810008516803190b40c41a4104031050080310000d040b055111 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 977223273 1250 977222023 977222063
    0x2210306060f0d02030a060509090a0303020c0724180e0f04150509010903020609030429040f03080703110c030c0d150903050304021806061803010207051213060e030a0f020d 76
    0xa6006d112103880c2048800d1f643d90500601007812201e030a03054206540c2c1c42e020a000780c00030921498007001ba102c900b40c032002961512450040c0030385a07411005100d0842541188442019524803038000182c0340c83c020703401804250007022012001603110114040140781d0103070145140400006008a00c1c00c003110741d0003800100e2007030380103208010104501c1c61f0003004440135103110803d008120056145c00300101c05800040105110381000300041528415054101540c421080f42d03a031400c1c2804d0042c2100e840c06198241c0750000340b41c81c8499070700001c01d0380714000b040e10107200010060a080741601d00c58a2103409003402d0004440030141d000c1d0003144110710072283d00d41070006148900c504503100316041508440100176500028681c03242889000100030b00151034941244e40702410000e100c00107400151011445203800000c600c010030261205c1c2c601464104410300000e9611450400013400405400a0420554840010640986400c0b40c4112014014500c034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 977224523 1250 977223273 977223277
    0x50312010e151c0f1707110406270b040b0310051e070903023601150203120609040c2310030b0f1002012c0d02210306060f0d02 56
    0x941a52140a044182614a403550f03e8010150703005030780c184081c040350303070705241c00a4004040d030750b40f074044014082c4494504000c1541d80d00c541000c1c0d601308846800d02083da442900b02c0954544a20f40044882c110241100102c4182020102e00300e51108080307401842814500c907058024425400c3c03e40c0482d0300518010140751001040300e0030001503500041c142626071720006202c02d6400c1015242c07080b810300840c071300c1080044805041010719103030703109011610482000b00400422080b441e4041304401d4200304d0018601d8850a5580c000034074000501c1d0500c03072a080b01c08101405050780c0280301500042410808020341c0071000c0351440c0301102064400c484080c2c40182c442d12902840300c03c0200500044c0c0386510780c6041080408440c0d034800219940c9521b04200055801610764072030710358a000c00f0034100401031540c00c08014185041c207552040540f24200400000e1001203050b50500032138403034a4881c0020301a21035600148825103001c6a400c0c2c1d040d25941c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 977225773 1250 977224523 977224531
    0x10030c0306180209090c090a140613091a040c0e1e040207032a020604151106130303050c03010510052101170606010f1b1a010b070b090703020d030c050312010e 70
    0x80c0d20005c2d540d8400450009104002403260043c0500204020b454074200d0a080b44100040c080c0c0d051096682e0b00403814080c44d44624145511000005450f1441d201081000be0060703400f40700065042d1000703480e14141204080c0102078400240c424804072030350b044040440103105558038140380c03c2c01005c20314824a21034045024071603000704046030b400e0740002194054500380c28a45000100c00004040c1d504110034840764190101c45610103001c40e0f44526080400429600c00034200101140d50007403003101d001908000620450341c49443c034841b02840741c50210717600d404082c8610180209107040030340300c880800010030344480034140d601c405101d80c000c0328050384e00c06004403801d9084501d1000031070701a5150068008542d44003000050080c01c0702d100754852900c0906889400340e002001c00007002c60b1100800c040000300c15000b1841400900e42c0c40d055400051036203201c0d10000381440519128242041001c0c0240c405101580d4001542503a60310070b440c4131111700710f07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 977227023 1250 977225773 977225779
    0x2070602060a18060c030e01090c150504050307140a1d1608060a030803090c0616060501050a030b010e040c091d0d0207030b06040e03072a06080610030c0306180209 72
    0x1c0d00041200840d4803d800324006188414001001c1c5038880000900007001d00004050700d401384484500c109000380f040b11032040c021150280d140c00740e103010030798411b1442801c00034100400c2101d960005940070941c1c5800214819051400c00003488106056009280882d54000004d0303a0741c0320b8600152103030404050814170340790040c408551481b070454540b40c0c02654410140080740c00300014591090b0743d002281e0608091400003401c030341060a44d04207882c0b072045002c04100c41d0f07010302401450180c414819250641e40c84a00300d0f10140104003020001e04002400c2c07055400101c030040c11070210400030900004855411446560325896040c86212004a2070a2001400c641180e420800000d12601e5130000c1001070002c0d0095152030b40700c14414a0045007100400c10100d6141050140c0c490440900d1701e001c0f00c441d940a201401041d204200041d124105d15800300e0b0f51034030b00050a403c1100c0c09030020030240c1c000c3d105000c1c0b0841c0d4010041c0c0f4590050030030100803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 977228273 1250 977227023 977227033
    0x30706030e0d08091c021204030b100b0405012a0c030b0604051012060f0e1510060c080a0c030c120c06050906040c05011404120f0b0603010c1e05070b0702070602 71
    0x380d01c00d8803503240c107031081d4285601c15004540000500e00c170384c041e4000036106488211002c20800e07a21a0003540042d1102170300c0c070050250090f802c650600041070441407a0b4100740c509070000c0c00030394410503000f02c1c040c0e8109881c05414074100301c4c410810391040c0c09040417034803400c1490360041c040b601503025a141c000404d4046d030440c9101021200103407400030500c1c01c0307541c0d10009040c46201d044c000c1d6440b0ba0007000d0704c232414800c00d201483c070081d01c800e291408102134515130ac007560001050102440044011a240305d0840300f0306101c50a103c0302c1410700780703400c80d40c2c62034512015100c600e000002c40185030b0310044010b00340740101e00c24016030301c1c1c40101d50b0311180240d600030105003400000300070031b50064030340807845068152643c1c1410b5a5104001c40380e420300300c0490740351122100c070364200400d104401c1c3e0070a2041d0002c006c000c00c00c84014061040f4a01003401e603e11100f0340940036480703101240c0e1200c1c0d0000c50040a070400c00c0d0040c1d070341c61207402004013602138 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 977229523 1250 977228273 977228293
    0x6050a0603050c060d0e010608060601140a0c03030b0d06060b1917040201080c12040602270f04020313171b1204060807140c0c10050708090405090c030706030e 70
    0x1940200c80a40340c110024204061070030040080651020b50000c000d00e484100403009044284259002018220003a00c500c0c40c00340e000403c240d0402c40c00704c642c044144414603c0d0703580715204100d0f0030703031500b0b000511098070000034040c0c0f0001c6000802c16818400007189006480d030107402180d50b10300400c004050011420381d00c10791821504a2410f42000024001d507108144107a00010aa50b002d45000d050314117075a801881110300b81d4409400040015a0760000d810740d41c2505441120050708006410008989102c42901a4030071500071001c02c42c94107240c10101c05943e071200503032106036096029820345411000c0e4140580c085420214600c01c00030800b40b0710682c116030392034a040c0c03e0040550300703140003420300410448000710000d00840d03c1801450001c08900042c50034554000400c1013600389411a0000c1080c14408140003410781019503802c1202120082541e0340e9186009186c0900e2001e0103074540f041d5000000c1e11038241d80001c002054075029180b01c420 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 977230773 1250 977229523 977229541
    0x507030f0e0f0a020f0126190606020c0d110402070c050906040c050a0f090e0108060a0e0c010e060706090602120907050103140a0c1e0e010909110a1b050601120605 72
    0x5000c0b2580003503070018151800189842c0a41070f40c07092050524180c845007030189031020380d07020070b400300c0c1882160b002d220075401480f071403000d00500c4032020b0000900f8401c2c000c1d1100000d0300018051210440268108586e088d08101a003038058011500c500c0b00d4100f01c01e881c441e03485260700038241d03040442c030b170760620f8020420b89400c81d44915280c9003c41c04201c031051000f0392444200034a11802190108d04004080c0c020244d802c000d09441c01c004040804440844021452561103ca8080340c1769030402180c0f508004116403243e1a801642003032409080649002004944001840303542c800207050034500801003041150601741d202c40055049a100d00c1040d01c0018070b50780003456003500d17908101400901841c0440784c1181b01e4013103d0b112403810f40705402280800700041241d581c00401440144403102c8140184841070201201318801c0c0c40100c010000c52000008400329270a0741350320700caa0305c0380840e80190707901c058110411881c82012202d282c245030200350014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 977232023 1250 977230773 977230783
    0xd320c130b1503090703020307030308071101090c150201020903010c030207030f091802030903070f14251401051603030603020f12070b18030f01091a07021002070807060507030f0e 79
    0x20241200c8840141040707940c0c00b035003000f0450b820602c1040710110068070f081c08007000940c0b203610303041001c0c14112005020502c03003003000d101030b070b1400940c0b001082aa126403411503036050f42c80d1041e8000004128060b12074000155007543c28031911076003040e4107600030320f407a074000d60301c070100b40c01804011075901e4502e1092440c0140030400c1c2071103a4409900030b6800c2415032080300d10707010381980c1f2404428090501509e4682c0164070100c03955000740a64140d58040460440307040e00c00d41d0242c5045282d502a411f10001e81c00c00030840c2e45d0140048840000e114648100340024900c4e00078050002170204a0045005143e9080b06041414504a103141403001070401c01d41452414008d81d00000d05d140348542400420060584017400100d009a082c00008034080200b07040284030040e001c08450b080303007409404c000000307a011514040b145100701e000750341c4148508012419000b00e03040602142d2400c41481040c40c1c059000750b2001d040903409200508007002401d40314 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 977233273 1250 977232023 977232041
    0x27050315092d0d0e090c0a0210090501090b0a0510270b01120e0a110d0c060c050a02062802010b0f011b0602030c0c15060d320c13 57
    0x2648007942c0c5080d0002d81040c045a02103502254410024480e030240340341103001404030f03000c81c11850804100e800c00381c0300c0a070700040c0f20800c549400c0030b02900030741d504944184421040d80c0c541020301007000030740202000a40044510402c1e003084901c1c00010b14040c2c4016440d80f4410f000010408040080040414185000d0407214a00c2c1131384a0050508035500904120600d48098191661441083c06607a00c80000b06a01110f42c50700038228185604803074400e01c142c900e050002000780001800303440c06403620400900003860254900110407400070361003100828011204500804a000b0804041856812401c4914001d03400ca400c0340b021150808114100d81180b035000e0103040300328007121510700300304141ca51200380490704280ca005c080c0040001c1c3c0b11800202c20080c07c2e07a10f00c0c84018a41039401d10000081c03000000510081075404040343c0100624908400e0810a034100c44040311440d1900b0304840d15124a90401031140307900342544c1b004801709110310810 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 977234523 1250 977233273 977233291
    0x1140a0f0c0507080d0617070f120b190603080f070b06151b1207030915110c09060f0a0e06150705150402030a08040803090108060301020a1e27050315 66
    0x14040264890703404c503910821040e17070310548580d0001840c52091800700e45283c0004040c0c400e45050048100702500590720410b130b028001200b21000c14a001c040540020141084400c4000612002400740c0120707031001d80490b402083c1c00b04050805c80052100d075219401c20300103aa10402000341e24401c45101c068104804c1c4118401c0041035840300130300e240e16100320303803c03c80c001c140c00703155521500c4100e0025000b00c0c405c003d8115004602c444440150030504003040d43c2d41e060940d6820b9455003180700e180c500c0d000c50003c0c5ca909040402034017015102680180e11303555807000008003903661382e010394a45c902809511074400295031580b035010340500780b408901280080883c10290007640d150294000050000d4401d10040008028900140d503c1d40c400f400050030403400104045d0203640104004211550300c0500f601d0010a61404840d02c00e903d041701300d50000f1941c11100b08582d280e1244160110038040003801c0740c204030100c501240180b080c24041d03100696038400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 977235773 1250 977234523 977234527
    0xf0c03060b06030906040b15220507021209090606041815120302151f06030608010501050f1012020c0a05070302090a0621030302072a0e0c04090b0303090301140a0f0c05 74
    0x8001101f50100581102c12071070302d4220340361b40c1c2000443c03a2204000312008440801c0300e0f05024140380c050164088030600151030f2081e1024906007061040c003080303500c581a150001070f440e550b242c0c00e031005052000401c1c0500d030b603024480d10043c15180b00318901c045080300c000820f402e100c03100701502589036018000c06c51268044c820302c01005000081000701c144603503902c0d01c0c00b004603100202403e0b9400b158507072030512501d0071120b060b00034074040c424100301c841c250780341c40c56070040c0c0a58503d01581d079406c00c02d201c10001c0c098a00c642205019072201e48090240000da00c80960307000301d40e000601c0c0c495517400002c9440034460180f0340b1400c5007410781040b2000c0046481940281005403800003140e0f500504400d40d0049600300c2580350032100340140d8420108405420328850070b03402410540c2404240d40200e00c01c0c44d001686840c0c904105481c01d00c151214400d01600038002900c80c88294481c0400840740d600105140140b0044c00c92601e02680c0381441c40764941034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 977237023 1250 977235773 977235781
    0x7030c0b0f0c0d0504080412120914010512092802010e062a01090807060903231b0304090f09031710060c0221060a0c0305060a0519030f0c03060b06030906 68
    0x10b084e0081043d40c10361407e00001640b10342041c503402c1e5080c4116000248a41c03403040c05803003c181c6400c0f10440c0c80d0112985a41030760000c0444042c07040c140c2c0050030541d950846184ad1117004029440c160014038545c0220900c007140300b08401d4400d80707464502e084d113172050140c2c80c011030070302950540c0d005180e07500a5280c200740180402c0190000b0503d1001a00d6109440c1d00c00d0100321405030b40d038051441810f0344040c050b1842d00ba285240502034180c0f00681740e01b8012004074150100f12030041100102003041110000e0841c4082440711083c000000d10040c0b0140b10290b0114403400403071021b44420803043e07072043c1040c4e46108812410314800326554210202c00301d13044405000402d290800d24055240310ba00c2c520000c0c020b5103003c451941c15541c030480e4010516051000b0711110343d4034041c00505940c8140e070550f144032011082a102d105140e03002030558001c81080c0700074400022039103810f40c3e000304420f10066007020140a0b680c8000c44402100d600408081 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 977238273 1250 977237023 977237047
    0x903070303090812190518060a1a130e1212151201090b01080c0a080613051204090603061808070f0c090c0305060901060212030103080d1107030c0b0f0c 67
    0x3620f005030141424920603010b03980c410f101c1619514031900000170000540c10890040645c00000f22081e08000448510342c0341c3e5a89024144105d03240d160a000e0940c494007124105070341800400461144000c00d44040040251180b0140d89000c0e03004118101c0311410120340720040f112a540c52a65a612954481d0190709034072158025860219041101000d0281400d16405100c014880b54034100d4580c0c5040c84400140e80107459100c010851600b01040007030348001001d1748541c041000b49001410700a1400d078940b42009c01042c0031600c100d8551000d803d40f8441c0004104150f035154413110b04401185000781214020030400c6c00281c40002001e400b144a481150402600c0b1454841a40c0880420b880042c1d40c031410003003280b410981e600c0c01040c40d40041d1012440d440e11034642840140400b9007591000542d8a10540c1190b020b40040300c8a12403107601c40413149070003001960000000e40c0c81c522270001090000400c00d070154010343c10781c5100e619201c032003180 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 977239523 1250 977238273 977238281
    0x40303050601210209030d090807030803131a0f0619060509130204092009030312040305040e16021e0d0e060c1605030708030315091302130c020706080903070303 71
    0x701d141049040350300c410000c00c40c5083c502c1d03034445000380542c551100c0340038113203450003c0c000d4508025082c1d1042228620114070082030742e401c0101580da99035110764001030860b000c44003d041c8080e0313003600c40056841304a1a4001e0550491144950711110204200d2030320690010a030360f030130508100f120502900017411624006000140106c2483c11454100c5e007241d4040394507503403909040004002c03a01d01e001d0001002086940c20200c00e100070955070700a102d68800e10010500200701414010000d64000f440d1a2010420b40c4c03424a0340c2040c2c110002d0000e4001d4030460f02046404044c5422b100302c00c01c0c0304070044c9480501500d04850095072102c855400003410012a921034000b400075400e01d455031403105140c1d40c0b92030145071400046511080d40380d041403080c0240c0d040242e860b601056070840b4108500d8440b5441040304140e2101d0095015402c2c101221000d419a00120703001d421035026903003c50740d154400e5440d21407c40d00c0c8600ad400801141000a02a0344 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 977240773 1250 977239523 977239531
    0xa110909090c040e0d121a091305030403050c12030909071b140307030e0d1509060b03010509010510050a0b19050c0303090a06061a180f1c0c06110604030305 69
    0x46800c21042e14002c181111070000c0040440e800c0200f034511801d411440d558400b40006000308090300c0400340c10115250a40c40d000c0c4241805404075200740d000d0150103c1c2c4139040400d50f9a201d9681c2351465586850054042c02110340d80400d50001c035002c01910001e5a01410119141c1d4407240304460700030a04803000204014004640e005c64150080c10310f00440003001590b035003d150501402e034260014101e031007083d030701d000c400c002050b0400500744504008001f1521404618000300a41040460300d50190701c0d003c20080c01400540005006e404079105807000c0503203910501000050f0703805038941c10041004591400400c5a1807041001c81910300a810421549016811944140c83c4071030b4580c03103e1310410612100348903841c001c00d000c444120451403246410700711800781c0003604a102110210a445d5505c07070403851501500c0c01004800c00209403c2207a800100c4480c003950b80d81026074000c541c20b401101042ca026408034010f04083d030b21950202c1c00717820024 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 977242023 1250 977240773 977240791
    0x121a0405010e03180f0405090d0e0102071203120e03030907030b15100203030907080102090108150102071e03210507020d0314040303080103051603020f0103020901020a02090117060a110909 83
    0xc40a203a1061003071015140390450b40c02034203a44d000d0f0714100040002002c10140c4a94607000501810450028004188d01c2080c10542e0b210701c1d0f1880180e0920341c060b400101214031100c8540d040507401005d55103c400d00b06001c03c5032000a8041607aa4001111240a603502074141130000c100403a1006900420100e107204910a42c8404181503e059440c410096400030007880038102041c800352000e04450700c004c508000c1c01c500000c040386005080113088200440324415664030a01443d0050190a6407030501c0c01c18611000110806a110a96a101c090304400210918491210040d043e8070f50f9010b00b4440d95400304046018803d10881c00c0c0056592022021000d000241000b107019844250085d8998200705050420001a0f807481000c541402d10041c1d44080080e02424001e290060320b0301c3c51080143e140201429000e94061580400021000f001c080d00060380b01c1210705548050702c0b980f40900c140d41c81103040c24186a0103210710324260520810039540100d0807 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 977243273 1250 977242023 977242031
    0x14040b03030a030203061005070f0816050d0207170705093402060a1803020a061113090603170f09060a2007081c080a1808040b070507121a040501 64
    0x4001070300d103034002c03a01c80010a402004010841c90480c0c55032292502c20300308903140145c260740301110010f940000800e120340118a01c80303000035130401c2aa00d194010103d50f00b1501c840c030041d5959071640301d80d0740c2100c54009645000c910100d0309208886024100044030b0321031421450031018141e8250306008580b0203501c125081210f00c1d00006101c903006055242804c100c17000c00c1d40c42903c510811200c94404400000b036000510311522604090001901e00d034880300d2200600c45c844503503904110612001c114290207a10a800701d80c442c460341d5001d0144620000c429000304050745050b5001801850320905040c801001c10312000c4c903003c0c1c190040010060b00d0350004880c401c01ca03500c02c2d24180440201004101c0fa04260811746d80d0040c95082c40c001e100d031000802c003012003619010228005801440314400d200e0f07000211546540d00c0e40750907059904120070170b441510425800140e50144030000040c2241c101840c0358220b480e80e888468901c0020704100c40665036 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 977244523 1250 977243273 977243291
    0x30b0603010b0901090f050918070510020f0f01060821090d030e04060609270e0d0f02060106091505070203070b1303210c0210050f04060519020f071404 67
    0x91400154040e2050078020354031800402c0005120b01400e401c0500c01d9501407505100b6592008502584034161021106407200c0441e0b1003820624607038000ca80141a00c1c854000003030b00844c8824100d170010703007161580350351b060381142070701d45511a246070398010754000c0e0082059190808440035a10320381d12304d0402008045008580c08803000c0d000191700200040440c6858000c03040140664076103070401a04050790070b01801c0583c043c410b01280d64401c400540801078000561a000345070654001c0380103200054640c0d50740d83c1c51440103001e104004611140a4144501510300d40c560340c1ca104000341c2c1050341e2550140c402030364140703e00100054402640b0000309000d200511039035501d14990b2400505491400107030700569514104581040ba602100c030340c1a00380c0445043c141c510323140c64103581134032850424044000c0e000902103089a04000148000240c040c981c2c0c0c0c4550003180226121003014850b608940c101d5101084040c86400c804101c070074001b80001a8241 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 977245773 1250 977244523 977244529
    0xb0a0809070e0712090b1501020f1518072d0807030b04240507091a1c050606120a0209090106020a02030706030b01021e01050402010e0a0b0301060f2a1511040e07030b 73
    0x700c07c88001203090310710b0600000c01d59042c800352101c00071348402851150344402a44515020040c03606598002c60580d00d040100e0400c480307002011a11020b0400650003c1b41601d8031403125268403d200d0b20613000240520005400d1048a402615031a89500e130b0f80c1d0b502030001e62a2405080c2c0510310981d41c1b0a15941c0d20455000d0b891689461541c14600306044524aa54000c5a40750080600101e52401c600c02d04454000d1184200020203544130b40000c0e215001da8481c0008814482c03041021902da940d009000e081c1b0116002071040c1e0b0f8500c1d00700da44080455000303400d07422141c002c014240c00780d08208801d00050043d12044882d01c0d00c440140c00351500d40031400d0713440701c040c0015540c0007041000b0303c0030141c0302d03030a403c0d080c4500b1084510040c8201010490b003603a1400e5141e20410080c01c103099000b101d02d41c080092520741030300e03005020b000e6410704030501d95041c0000751803040d880d28144881c452030400f40f41a2050340407810041219043c95107809221203269 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 977247023 1250 977245773 977245793
    0xf1009261504150209060405041d120d0b0d02061c1b0518010318080304031b06050402040501150f0e06040b0a180501020304032103150b0a0809070e071209 68
    0x7000c500e10445507440c06003081c1c0d1061650300382241c0c040e80304100030f400070303250b410480e0b0aa807010b8034040340c01c001d0800321030300c2190411040b02160062852840030041214010700031489082000d1001c0d64480d020800421a078140007035000100300000e404160321210004040503c0365030014410b43c010803203201248884003441c0000307000150f240d103914164a6480b051010a1a0800c8031400302c040c04129040f10b8000a03260803030110008007094800c0c46420841c0c007198050352200403c40c036001024140941d01284101c3c00c08001190f058403d420b5580c62412540e10541c0f03022000405441c0e00d1a40c803034041e08100204008103c40c2280002010920b046584d240c0403100010003c0306040081c0d00130a0464004110410100d81828181e54844800729401103401d4100c1e6020f500505220380f08445000b0300b50400200500c00310050f1805807129207075100c1d0ba0b13440b510443d403209168010001007040c0b0001080d00d03103105125030700c1c451124070340000e100b40b8182c840395010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 977248273 1250 977247023 977247043
    0xb0d08040803120f0708070c11100e0112141f0503150907140604090c0c050f060910200c03211602062509030b0a020403020f100926 58
    0x154000a4084040f01c9440c1400390700c400e501105a540d4104114003d00307140002d01890704002005180d10305100700342036186591100100040c4080c041604060806040d920920340881d44c170010001560181e07000d01ca420910400b00102c09544007184088044156000c140036849041000b180c0760310104441c7c0303e004205584d06d001841c02c00d07400740c5030800c10340000d4040b00d038010b507500341500e40b40f050fa0251400d0180200300840580b00803503c03e00c4201020700701d84500a03443c0000d100100b90280103048800070381d5070100d1000c00d80c000366041c01080c1d4074650710b10412100c040040d90040e01c00408404140c900c3e00d0b103282d20700d81103007521480e0766000386812014885d2030040110040001205400a080da0303142030040d40e01c1541e00c0082418030820718822500c1040e00c10400040036603030000c3c1c0c0520f03a080c6200503030025005404128000c2092490741c007e94504004c1c0103100c1c480540c0c034901c643d0700308018200c008200400c0d80760411030651481c2c040c04824001c000c55 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 977249523 1250 977248273 977248289
    0xa090b0304060e06061c080d0e0d0804110324060a0302060d020a080717070f020c03101a04020405060d2c0a02040b04020a0e06090a0b0318240103060b0d0804 69
    0x60f50540824582c1481c1e00942118891581c0f0281d804102001c0103030340c001c0942105406444907140002c400240086e49441c104a001c3ca8000313640d419002840140034502901c41c002c1004000c000f4160340d03040b110350b020002d10301c0600d807420a404a20040394002000b42c1402d0845549a000c900c041d000002e40c4807406401140d403456075684005003070b502c60a1450241910150302c040d40e59180d0300500304204000d1044981c203c2c15008120042c007010005c1c086401090201d4240300007024400d102040018072080881130500d0b1a0007075800340e440c010f025503d0217541c801410000d01c20207000c06500e0800c0c400742401d42e4080900b01e0304a004010142c1000e4516204200888010741c420f540316510501c8504112540210f8440000d03805580c013664603020702000a060900650004c4821000041000a0a003d404034522928241402c03540c8042c1180c0701c0c15a0361185031411501e810300400100013241c41a00b01c044524005422800d4010f92512030740301ea5880740d00721b070f88 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 977250773 1250 977249523 977249531
    0xd050705060c070e16140a090b0307050429120a0603080a0306030605100f14040e010911010210060605190e28090b0a060c1e030c0c0902090310020a090b030406 70
    0x40440a030620855008030f045c04d0f00700c100400d00c1400303041301a100c0c00c40180100c02007005d001140c040c001c0d00029140b200400d036142c5c940003100604d20b9106001d4030460740c11459004150550f49000c6c0c040d100c5455910504001015120049090000301072040e0251542000030114401078002c10146103a51b030040750140c254208035066a1010f007005004c5010380f5010840994460f4184040d109010b28030008004c03141700050141c100004000da503540f03002045400c00800c100c015041c40c2c02030f0203883c00015050114802c0395101e10a8034046070b020070029181c011400005681c1300114142504079105d0304001c505500c2481001190385002140d0200d945403280c80304400a0121800602c4207040200200c2d200c45074600c41c2c01c0601c440841d4581c01c01003d4200c00c00410070540101d81101000d04008121110b0b2481c1500c00049010340840c00c00c100c0d00840e00407020260080c1010085008004000d5221985410401c03440c9040840d150414400a40c00765001e484081 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 977252023 1250 977250773 977250779
    0x307030207031b12030f0222030204050f160c0c0305010f0506010318020f0910030f031d04020a0813061104090213090912030e1516020f1b0d050705060c07 68
    0x103801c01c048a118401d510503107600800c00541008800b1303403d0304051070302280e03540d45e14150700064010142c0c2418400a1640c004001003805143c001c2100d000302c1c1d042c0a23585400400b824000c10550380c140d441514541102045ca014981580000e84203804c01180ba55407038075941c1c00c50750051500420039807903505104403507034940292842c088101e0410003800c841903000829001018084901034502100083c3c03030000d040116000443d0031040d005007000d040c1c03070000c0c110001100c0f008100c81000c08103480e01e007054825568084999151f11002e9240c00140e034100c58240901241c0507030b203031805103c003400410007401c001d1072401d001503201e025203840007e030401d01d504481d0815280040c01400310707007060150007000056003400074030980300e0301440d41801000c10519a02a14000c00d00585010300b00c000800128207134255191b56007505802901c860340310001940d035805101e1f9101083c60600790002090344130b181200c40d20795552010410903000b108107592241c0086600b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 977253273 1250 977252023 977252027
    0x40c030b030c030c1806040e070305061e22110307080d08090d050901050307030207050a120305060d200109080601060827030f070203010b0405040804150201140f07020a08030703020703 81
    0x41c00c03004070100d003d004050307000c90100e00c450701030b031201e041d1010b4490701184080c1c6030342d405480008c1088055800203616801d00c83d90b50341f415111030141c0c40500c2c40341e8994840d000b02c61402901d80d4100ba54030341c64210f00d25248820040b0040d21003040d80e408403e02d0b95000c00411005254010180c84840c2c44001c02501004004021004580007100d90344040c3e6401805c541003404c09003003050700c0341c8441c18110024011800010018841da90700310050110a5000722142201d50b901800540c0c2d50905100c0360300f6000c000142030188425060030081015401c010062206140c1110b42d00e41c0d034001c04d450100213920040c0440c44030418000070000d00381c09460070f060f940c81e000403002c1001800c1c65a903c520070091f4544180403440e9811950290060341201d48002c10600180c01c203401c16003801e42c800d21444c092030901900e401486401030248040101c0d0312500d10301150303150921100b0f81c405c02009042140500c402003c00586c0820180d4050f985a507401a1518814500 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 977254523 1250 977253273 977253283
    0x90117010e06060607060e10020f040e0112260c0118120903050a0b1801020a0801090c020c0f09150a14010f0e100c03140c150109020a080103060e0705040c030b03 71
    0x740340340742d0000c00802c446074807070000f141c130410f51140e0006844080444d207513080981031041b00d644540009154440080300002910903a0781d0f15a1080d42d91343d0f50b1207044c1c0c0482c20711710010030740c1e4012030419400020049094050440300710000d803600101045031750840d080300b03112021f80d40d400c090400600400f08940d201000d8036050a507049030840e200d05996501070a401402c81481340c0018100311414004100001d00c182c5c000c2d500c40c90110b101900026003400340603181032603e200c0c10341036407001801c504e030303504054000d01c00c0b00e03107802c140400800e0080803000e0703820441030310101030745424400b8001440449a115140d4070a00300040c0300d0048449a542040a50124510103a1f2229110511101c03603007000600005503207400e85402c9250150441c1c3c0d40f00100305000c480c080450041c1c40d02c840e48501201e10381c0c80700900d0049000e2000560300186030301c0018800210550301c1394100c0040c01d000c550113260b481000038140c1d4401c05044000230b0311100c03000814102000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 977255773 1250 977254523 977254541
    0x1505120604060b030f25031a010305150f03011808030f0a05150d06060f180f0c0e060a0c0804090f051005060f07140303090102040305070b0315010f030b09011701 71
    0x3001e00c98140341c0342c0650f03441c0c0030191070200e01c1041000459410700b0401211034040221200084d4801c4082c40e025005001c4841d22094800035100c0c0d081c074543c824803a00d031049400c0240c0300701c41040c03141841440c001d0740f84826015943c032000c503140c4a007070814910415100b05c420950380c0c50080c026240c42c00c0050038a031380941c02c0a050010385100c282400140c064203450607200840c032800d046018041940c44010401072203040850f80c400e21144c6005201c103400414000d680003a6140700c1200c014444290010308508600c0c5441c0c0f41050040500800310324010301031410300e40340d11034240e00a030f000344052aa102c02d010512000f0b4040e907640451103084c8940311a00c3c11000c40c0c140d00c2000b01c0b4241c03c440000b070080411031600e02400000c00b015049039224030b01100018003d52090106a41c03900c58010002501e10400044a108200700050b8012992000e001503800e0302d445c8281a06060720707100111442d03210200440c1c0201240802e180c1850b004c074285c0c60851722206 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 977257023 1250 977255773 977255779
    0x90603160f020c01020303060f0d201005210603100c020a0614041502031b0f03070207080d05090402070618110f0604060503060d020d050a03020c010e010807080f0c0415051206 77
    0x1c03c0e06080e581c0c002c8156640140180d03002e0b1090310855001131803008a0f408000d018200c1644852aa407542d074004018060040c1d8a03d03a400749042c000740c13000d02801c0c9440c412070b42c969071404c0c000400b10500a8102001804032442c41a04c4107200040d5815031842da40182d02019010003404194020820101641042035445040607107640c00602d450010303080201d6000400b040441d041031006180d50014001072540341c05840b80031405079031041e2a01c00040c415014045028000814042c0c006402c0751502031a0140f94824440690403500086da00341e5541c81420f11002c080500118a03641319428124840c3c40030001c00040d0030072520028000c0e0300c28401809002c1c3c003c4110b0b6007100088401c000c90004501c00281400c3c83d4401c0140f072030041080090405800103152208580300b6252045c44226060044454113011221030000038440070102e441124162007161b040110354000038030303242e25010100c403c1000500b9103400220009100051494080d0b1607640041d022 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 977258273 1250 977257023 977257033
    0x40b1e0c0d050403260a0515091909021f1103090a03020103020c1617060601030b06030412090506130303080603071505130909210e01020712020105090603160f02 71
    0x381110354940c0c003a09560300c003840c0d03648010070b0a25000306800502d15501c505000122500b02d80888000e01d0300340c0b20340061a0030540450341c54404c58500780001080586035010b91b030b0301d810f60b24020a241002c102c01c0305592703e00410258450030102c0032180100704200c401e191080c44000c10b109501c030517000d6290010320026009548060b1031400f12902440c2c0581c4402282002a04080404060703500700c0c1408000055500300f00010341c0255011541a1481c0f0780c1c0b08801034064900c03002225500080c02c0000600041c0f0200303031418030011914201c40d03060703124002304000786d02100707003032070070a02c038220410030903503c024000d41c01241640038011103403170a036911030b000d52204801d1040c09008a20700c440720903c50441802091045420f00c003034202c60800040149180340d0081d0380511303d05103855094003c1804120844040e8000d18840c0e150409699654600da081241003044c10070044442e507441074061400b5010000348210202040c3d8005001400c143d2942000d40d041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 977259523 1250 977258273 977258281
    0x506070f02190203061305030d0609200f040303050f1c0e0d0c11090c0f0a0903021e0109050418020315010801180c0e1005041409011a03060a020702010e0306040b1e 72
    0x1010624a0704007507415002000b00402d4541f0f64154095031707103840d8401e807503c400042c00c0019070300042c10610a110741d910300030000700c42c3c1503001d1058100544403004d0410003003000a20800090030b0000d00c664003642003032070301400b074032441003c003040d001619143c114611051905004251012141d400e10f5080384165035124203802c1d006030540d61041c244030b0b0025941610304e20407228801440c0c050540ea0b00450320010b0102003040c00f09a00074100c440036401c1d0032004070b6040c041c0034816160840c1c0e491500c0c04200c0a05003e180110491100f1b4842d040161410041c80c100480f00010351200c40d81409802401c41e440202e09024061001d6488008141041807040540b0300040c01c0c81c42c940c0d078038590410703000407070b0744181e030002d283c80c54400600c05c120000900440c4802e00a205218030305c030407014583d0101884540c160040408210003c04950080101e02e02c181400030760040640006818003000721420381b00c0000b81000c20000320320b2003c0040401480140c0a00c1c1810 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 977260773 1250 977259523 977259529
    0x807050c0918071202061201060c050d0e0105071518030507211407022b0b0f19090f020d0f060509150f131202100f0204080c06070309030506070f021902 67
    0x150f42c8130b01d2001401d0300a440e01903459040071680f0203130031400c4418495070347c0e0380024001c8402250a4541c0e0003101e0b210f452080c860100d199110805945160034030741c460b15080d8003860040d0070b0050856480c2e50140c003001c211412001094060303280d0300d44401040c20800f03e0031000c410088085a04801444030391904120700c81124880c00a203a078680820744081192100d019201045e40000300e803611203103009000380c0100c1d861003400780a019031624188880010b00c113540c00164060000d14650550304241d104904403409046801032044481e0045513603c0709295003500c1d00e180d003d00e0f83c0c0600c1000e014080c0c00020000c000c04101d1040d40b481104484042e0002000c8100f040c0403c14000c0d100804010881d04074030040c1e400700800c1d0340070f07594200c01c102d043c031824101400b0b46244190b0317200f5541224083e6000d026102c00b05010010113a111000440a20001e49030101c0411010020b040c070070489515003c510f40c100703d901910740144c01403210181c2f01820350300301c0103031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 977262023 1250 977260773 977260783
    0xc1103070314161401230904020d020d0c02010605030709092a060908121602010e030f0304090e0303011a2b020711190e060d050a0b0f01060507050303070c020d0807050c0918 76
    0x1401c0d40c0051a06d1810b10090304015116002030603601500100319101008080d60060802d0070041004003c180583d01040e03003610081d02c19070341e0681214100304001d10103070b041405c1c02449410b030442c40a04140c2e40308100d6041c10300c80d0030f0843c2941800c1c0b10241d04100f080025201c854002c25407401c117001c80c5c006500c155620004214400c5e0507a00071a4069000c0c007004440c004c0565039103a0103201c07a60355942062080703851450510030008000c03030b8040212816680044d0b000e00784240c2103c80c01109504c246400d0090302d001e090301c0304100381d00c01010621240780e8440517944038003900b2312a40222800e08285d02c54800a041c000540c010024070204031280c103800c607000303550b0312800140354408002001d401401040c42e80b0041224050005208091480e041313403190340c0b0b0b008216601d001741704005003107070b0003007020a00b03942c003810394141c83e9840104000c01c0710066030785075940d6402842c0c0460300d5912060b0030ba41c1c180b40c00103080c4c0c0d12441c010305140c00110000147c41d0b4030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 977263273 1250 977262023 977262047
    0x501180e0112210c1509051005060a0b040609060f030b060702010f0201180c080f0c0d1410020c0c03072103081b0705030a0206070504060c1103070314161401 69
    0x50340b2919102800c000ca482000d2880200189925681c0c140000d405001c540d14080b0444c0c0c102d180e00c048a016030b010f80305010020360000700410b130760790260900000901e0080d02940d44035000030300024811040c100104040c20440d40c0301e87c48207140c01009010801140000000e041c01e080130184540c4a00041e100040d40918010040c0c410f41c1030240d00410b10040a030100d2081c1038142001d00095108032800c46518900b1280f1090500313491540352450120483c1d03010428040c0d04010402000a00d02540640c03010381c0d110750306400b03044003240e00500c0007150340d8100b03070420407251505024490051112619500e4031280c2c003c800da41d02d01755417600809112078100410718000c1900070301d0341619910400250780e00d20030b0500070fa0300c2d00600304000c01881144000780c0d10a21500035074084584507114030005902603074074424102c801150781c0b5050b01c41c0b07030b000101040c00518001810105c040181041e580c0c0014444161803168000d4512102c40320b02000499a0110828080f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 977264523 1250 977263273 977263289
    0x30b06040504060e0d0507110a21060b060a030b1f050406210c030b15090a03030c29091e06131401060b0d060e070807030e03220501180e01 61
    0x1070340c2d19460014010310320f500354999184180020710784843c0c2c1001c01851054011a0b200342c948414900b008000d820601a020940f01c540c0541d1240d0764180c112142c05512404010901058084c0030a400740c2107039034040c00082d12103051800505200304d450900f43c00401410100050364200a0501c0c411403180004004035520014000d01c2c2e488000c032560200e5800074811514504c0008014000b4050700310701c150040f8064840c030461480031590181d42c050141d42074180b9549050f110603000c203109a82c0380b4480c80c1415062001002e10310021240140004070504121000d40d1400302c2411403c548102c120411464100001810641c4105920300f220b00c125510701e0801a0111380c803602c0c90b078560030b004020410800c088068022003500c20b104004096a80d4130000d2428402c0d2401004110800302051245200e60050216603814108492030441c8114107010003c0346a040c000c2000d04990080c48039680c400007121042c00012202001c0da410044600080d00040c403550701 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 977265773 1250 977264523 977264531
    0x1080a21020109050a1208070c03020703060b060702130c0909090b01050d08041d0105090703110a08071407080d0c0203032712040e071e02190609120507050d09030b0604 74
    0x80303814800d41001c100310b580703c01074514034070061070f0174441c2410805080c40850f000d9000103445074868a020b064060305035009040c0700c1e2842c0c40301001845100701c4d95401090412108001d615500010404605d41c80c4002074030004500004040c403030141c0210107241c0c1002444000305184c03d900b13906480049072103c0f04100e084c1b600b00024891035110b504201c4210b455440034010f4004501e040303c4050354904c0807030781d0f150030484c22217118641c961f642210900422500c1d5129500460703004080c0e085c0303600301b6805514089290313041444125141440020120f40d0096503029500c01c0c40d406000a50842c2003184194000203680405c0c2c2203000c2054124580c004010040c904000c41d107030040c1c1d1b547c1e80d1580180f45910808035141f4000c2003ea0007408604407000d50980c2c55088160301900d0000c024160503181c042444405070380140e2100c0c0d01718007281c482001c140b010b294640b1407903a940314500c3c2c02810110014611403d102c00d078602000465549000c13540e03c03602c2158002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 977267023 1250 977265773 977265833
    0x12060902091e0307030203010e1c052106030f07320607080708090414061009080c010e030a1a040b10080706030f14010303110106170c061b150f01080a 66
    0x60310700b04c0302e035102950560034202003040000d008903020b2880e5800e0784003c0004100c5a806071074a115000c1e41c10080808240b10742140700e944010240c02c01401000d076904002e501e100a85001c1c200d41044500e04028a00e1b46920441c0000d2030701141c1108100a2281d04035500040c1c20740940c2d030300a41082c00014440d0100900c0c00c0494803807050050040107c98070f0807030980300c000421152a401a001c4040805502d8051a107020403100494004d10080714640011621000d02c0000c0542600c01c0d40100700004103052031100c44824217044183c42c500e0b181c1007800c0018405854240959005c0000340840b101c0807400750180c98840c1804034841034900b50610052a11200c145859900c003000801007550120b042c0c450b50f00c0110003840700701d840f424900c11071403116210701140d030300840c1d4840e40c0b418004080c5c01510700c1a08401007440e10500d500e820041c01b42481103007100c640003041000388009a004c1e002d410000006c000c0c000923680c0ea02070b045e443e00c00b030090b2079a03005604 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 977268273 1250 977267023 977267029
    0x140417070b030c04171b0f030309090103110a1e030f080403080c07090b0301230703090506010605031e060d06090204200d0501080d1b0501020f070312060902091e 71
    0x350300401c1189600c40c0e072407501c140300c0d000c65000790048100441030540c6404050500040c056450200041160303081c0c620407082000030700358220382d540c06000a03c1147d205690300c4550500840c010402d00000e100c10004009061103960464000b00565003040e00030130384102c4030242500d43c070001050307400810303090110382c2c4d000356800148402030000e5001032400020651b402140c6160000b4400101d00c10700301800d82d607817902e1800d810005100401001b60504203016044800c5040001d16081d481e00c54505045c826088480030400006c14440c02d40c6c1c680a85440c80003c80740b00d00726a040810000303600f02d20305100031303001c0c035201c6044105542d1282d10a01520b0001d801c1460190305d070702d003100e0b5541c000d040e01804062030705000080c43c1c1c001103002000b104050750b510114036031504510010620441d0152a590360034820806105011001011018040e880d0b90100c84941144103058075815005452a0350040c8090050350f01c500902000f9071803148020b0030016500004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 977269523 1250 977268273 977268283
    0x312140910050a090b16260712090b07030806041d010f0c14130509040302190f0b1810020c011806090b07030612080c010e070b03090c01140417 63
    0x201035002070040004070946400c40e0041070038500907110002d407903a44180418083c00380131320011440320101c4583d0b000490141a60b04442205d1204010403881d00960454a030040c1500325020300e0308651404456030000e01000003041c000080d60f2030b00403980d90080541d4006401c00d402182c44881904038a034200b004403091012490013000391808580303014000e070030740c50f0f074030804103a4500c003c0e03400000c880308507428120101003c00069260506104040c0c00051040c0c003140100803540c0b0050480012907c5094040d0604030207404090034991b281c00d10140442000300031144c140f00c41281c1c007007444010115400c0c801600d41c24900d075818050240d01880c040400e0741c4013002c000b00f000b07560041222074020b01e003e24460340c0d4400f0075802c680c91400344000414660004000140030007000702002401c0600106007070691020302842c104468101d05d280040110801c55000c50800c000d840000c424a4000141700742104007518502c560301075030207440585101540d8551040003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 977270773 1250 977269523 977269537
    0x4415040b030c150a1b020d08130305010903031a041a0603070c060e0708010c080f0402090a021611030c0a0b07230a050d0e0109061707091d04020405010e01031214 71
    0x7240d4011a03052503010196800b90584d80080340f2801c82074280355100e8540513030060703400f4120181e043d0241d1214410794000c61207461455031050700c0400000c03003c0c0a401010b61003501d0201d1001e40607129407544102da148564001d515128140300000d4440356050055070003529056a02e03229201c00300c0d6241d0f006540605640c2c100140c0703c4020900140c2c440c200c4100100800c0700b8107442400f00e802000503200c60500c026a034020034050b01e02201c800e074100350300715401458945c040109020070141e090040c3e500104031101a803403418288443e0f0a1040100c44c682025400c105203650b8a024156010b01140c207085450030041200c00c00201c440c840500444a2550052424581ea01407800742d4000142d448412001194042c50b512400e448c00c98580b00f02210610398041e0302000024108020048142000117050b01c030180520843d07040c0000202c4c2519150045c8010380e20103030320001c9070300d64040042001c11a003d00000c4600032510340003c1890302813803c03180743c0c00750f0301d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 977272023 1250 977270773 977270779
    0x212120406080f01080a03080a0c030204031a040b010509010815040204090c0f060f020613030e04060e0114041b0c021e0907050304060f0506010e060a4415040b030c 72
    0x40e010411940110016109107412100c241503685c96103c01915401d099400a02050018021134801c0c0000c0d0030151500c003d80c900141401d9903074480443c80d8104030380c0e43c01c900340c403403040c00184030003200c02901410381a1554440ba52400301255036402c2141400d200801503d4003107800c541d40c03904022055500a5541641c85440d8641c00398614030511464012800718640a08214004600e03284200040c0c040e140c0c803002c8a4505640140250299a40c0150f445001003407081c0141d02d0240641072130300740c41c44140c1d06a400d2008aa0803002101907080030000c1000c0700c0d5a00c18120600c082d41660801c0d03580c40302c0a100e10340b18845103000c903072208201040204241d07005014501c0f480c001c0c6014440321384112002422504190382090000707401c00021110b6003008402400800c180f49050040d5140d00c02010316540d4415010600c01e4403c600807411610444001e000b5203059450700311810b0811420038002d1103034850105001c0d50702c82070500e40696090040b80d60744580a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 977273273 1250 977272023 977272027
    0x31080405090903030f0f090604030c080d0e0c03160b041205070f09050708060d050c1e03010f0c020706020d090905131a04050d090602061f030c08010609110c0a021212 73
    0x2c18841510398004913003224050b80500000790340d6500040440b8010100c540c0074080035156500c0445030b041100c0030540700c0b048200140d45112110b40b14451045030100701520f040e1901c0703420503007010562606100b001d84901c2c0305010304880241102c086541002c0d032014410b01920740181080c1080d4030204914105c05000100c900c003c0c4c01162096030389580710715540d0b88010070494040c000c0304c0003a00381d074417407030781100f5500b4000802d16168107072107001d8020300e03085070009080d2141d0000564605d902c2d004440c0c2c01c0d940400c58880a0030142c00901800446a0342c010940380980c411b20340700c6511100424451510701c081200d00c5604040303080d0356086200010541e2820966086440380305250003074503014441c86021040d00d90560203001d4603203507010b8440d82112030384206039520040d07800001c0000c903080b6001008003402e00000c07035070514106010b000c41d0f12004200103807041c06c01881082035004100725801c503504682c488482495203485914001080102603440b07800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 977274523 1250 977273273 977273281
    0x2031603030f2a020d1509050709060b030118020a0513030b0f0903180405061c03021b040506010e120a0803100e1803070b0910110307083108040509 65
    0x8040450310030b014058803030899580c00d100c001c52101d5594100384100c1c1082e44a00c2006207040e03003072402e480b809003499250f680e403a5821041210304241c021151a4019541085070580c140150b60003031042c900300c113003558513140e0b40360807114040034081d15050380090444040c0d4081c0040d1510052800c0b86205015168504086212030903500e40e8610348010b40083c1d540040001200e0384e020700d03100340d02042c0c00b0080920000c0c050241090764051002ca41034400300c4410322841007420b009038000c04121407600c214002d40000103110900582c01c007010083c0c0c0344d810180145c541c5a0641b5201000f0704540405400e00300810001400118000f06105c8082c2e2a50b5142050741d565041c5264039485984c00400b082c1c4140c020f08040707400c01e0042d8004140130490b10344e44141860192000d004020ba032080844000304003180091a000c400d008009501940c09940040203031044d0004a42c013401c0d84141c4a4028191842d84142040700ca0070041c54406a5005110180a00c130305820 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 977275773 1250 977274523 977274527
    0xe161403010e0a0e010504080d18051c08010603110306090c22060f03021e16080a0210050606090127030213270807080f07022106072a0203160303 64
    0x1905441c40b81440c0d0130a0f004071074554040c42814011544502440d2400c5145030721203000e094081e8221860681805034000421400e1080500010101c1c468072451a0a02c401a001c030006801600805280c00f9015240742e03031070001c0340c3d00440c08650000d610354031440040c1c40b0b44038927005080f1190306403440480035620134403201d00303407202da85070a40d0f42c0303ca80307104600728060711194400300100c01120850740c204000050490104402c03c070090000551a02141580408486001a4464038a892100030342e4415160001011038205141050500008018402040741a1202d40300290018034074884003142200440d805000303803103076004122290b00140100c03c00c000d06e280c3c0d1200e100704001522603c1144650340084030509060064072503001c5600b12460301d021405d010421407000d0380e680c0204807141d10100e5044802e10102914903030800304082d00450622110402070000745409010300c1c00065088540791210f80400c1c0002490a1102121802c1b01102c181c0c02000340750f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 977277023 1250 977275773 977275799
    0x3110c0f0c030d0e060d1a09010e061c02030c0108150307030318060801030f110a0918020f01020606032a220b0f0a09181202030403020f0303040e16140301 68
    0x90340890a03582c042c03c00540c151003441c049070009500c12030410150140d01c00c0c9500ca141c0000108001400450144001c904070200a800001a80402c0070070400d2900c0c01040200c2c400c0f115500300c003104115a80404d07524180090464140080303030700042e44602d5844407185940c80e0083c103d50000e540d034140a880d407240d10181091008081e075011905a01800301c8a04130f0741e0140910301500c090381c0b103604a5840c0d521480e58008400341e4001480c0d450380c040c0b4040c0c0880b64009006864031441000b9101a492581c5410741d000001089025a40400c102ca000342c400054a1446610083c0c28444010201e92550307202c0b010300200b4002c0c208200604503032203c0d200e0200201d0b54101c04002c00300c180912000e501c685034541c103021010721030304600b49110a45180e880c800c18a940c4480301007000a11100050388042000c200307600e44190030740d000c948240c02462070541003c4100300d81640080c04020000b4030b000590111078800d40180398102904030079252030303584030031071030b20f00e8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 977278273 1250 977277023 977277043
    0x20f07050606040b03030f0c070f0f060e03060123040905030f030601020708070302310f0b0102150c0304030f0c06050432102c0303181c03110c0f 64
    0x2920807140010414240341c4a04503907444024019800d02c184c6580c44c441960141c03494030114000c0080009450b02c001031404080d02d41e580d100c2c1c0301103050003401840401d0059000d80710303071300c640010007642c03034508030300603000c0340196040044112010204000d000c01d804010700c40d11000a01000781600a409180a88002d90a4680d0b2a41e0380b0a041c1d5507a844d400040c2d07110000d074a0500910707269040590440005240f0a074490b00c0220424040780c0078503111031051621001507051560b41840502e072047d060b03d119090034207054100c0c0071b650000400080c144005c0107481800140074407082d0b8002da500c40701c20b000914261400000c01d00a0f01d86d4968000500ba100c070442160018444888203507040c01007000031560900ea5002d080855400800d81d20605080d450b000c000c098010308004080c00103580d0b0b4104058036101655820502d0301841e044003010301440340d00e444a0f00c0c0400b843d4540810294120764503c03502d031003502d021104c035108050005002075004900e04841d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 977279523 1250 977278273 977278283
    0xe0604051602030909042a06080a06081b0d14100c050309030909070e1e1005270414090a05010e071a030901140106021b010323061201020f07 62
    0x50322890070100001002404100160300140910101c0342000c90020798494003500c1c0005580c0c840c6e13020b000041800b000d030821400042e20080c4081a0450002508500e0317100d070401803a441c3c070401c15150200d072032103000c22046d01d000c0e00b682035649412494032180c102d07070360f804c81a10500380280d40302039440415000c40e0410310304c001c2060090341507078401e05014000d145402c01460400071b411400134901c3e02484a0868554a07a40b100200d081d084040b0150300c0015009200c100f202c0580c0f140442000c000d0204520341101e048800c200703000c0c6003504c440c203041340c14103800207016184030780302a05614280c20400c09a203900007100a800c3d400340008101a151804159484101c1401800065805c10000040152000c030040d603002d1945000043c1d40800307500181100502a400800143c0c04081a41034160990b483e41001c002c09080c1082004c0c446014032001d40450b401001090740034000003249501e030010b41e0030403c0300780b8000710f665000314003d503d1305400a150903070f8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 977280773 1250 977279523 977279531
    0xa020d150317042403060905070e0108100303050712020304051305040b0601081b0f0708071208090607020c0918070602061e010b07081b0a150f150501110a0c0e0604 72
    0x342003481c0812a000d80300000500b0030f1907a071042c2183c602e01d02000d04d07031040603550100095071104900c112401410503542e1220240440d1000428660001d041d4001e11103440c1c40800000390040c044a200702d6101e042c0102215113444240d08500855008940000020000c45038110b0594080751250740b1901007034800e504c0b6500110f501d00b40071145044c4c0802505c800c1650080c8810241141c0b4214040d07023454035008da52945800d4104600485401c50000d5020070100c0c5c005041c594001010002001c481c40c2c400f000a6032490070300000350007944011b000c980071101c503511080e0404034010860b5019941c6410096503a1030445000f04035000c50f0280c0d40316802d40c141081d0496203010f076000e0030007442d52610781c0540d1200008040d9940c001c906403c0050b0103009150026008103200306000a00314000c0060380e420b9258200754520301000b404c940c04441241e0806c0d908280384c048605000400054540100818040c04e800c540e034200166850070061254440d81d02a50140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 977282023 1250 977280773 977280803
    0x303030509010c12020904021606060e090f1506062110050a030f0803130210030e011401030308130203030c100b13020a2c120309042708030a020d1503 66
    0x2d00b201c0d00c41103810005502c100b0b81c0c1007028519000b41880050050006252010002c1006411409a6400c5506540b54402000301e003081041003580320340800c01602c0c41410841503d80c446000c4181c01542c2c9401c1030200742a520303280183e62900c501e4141201403028407490380c1003030060403541c904041005040100e042d0801e408140e00f1640d002040f0520a14641c0e246401c4ea0002404100a101c0c04103101c00942d480b1841443d85c40601d0720000b8120329a0180982558040f00c1c4e00a60745480300010000258440c2c007880d0f0010340401c8036242c2c803600d032000a081d485420781001c2a4856004084590b25032580003960160381160442d00c20b120070511201030740900c0307003808003156004d501c0120185d1f0303810000036859149008005001b100c000080c01c0e0851074052901c0076400410031503032030b042c24030420000850680f112052040c15032500641c00b4541d04000b44203500100c045400c90100b034064907583c43c1603580c00c1c40195003204c001c1c0580601444146d1b03418181c00d44070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 977283273 1250 977282023 977282041
    0x12060602211b030403030c0c09020708090f030114010906260613110303030f012c070c061d0604030906090b07061d0109081e0c0d0e0307030b09060103030305 69
    0x4241d0040074026011185032140900d140d142d04a00101e040307018620044080481c0e081c00204050b620035102c00040d1030076400c01150102d1203402040c401c03031040210b41d0101c3c20070701c25503059502c2102da0b0006000b404011030b000d4005130300b01c003c07682120790000c945801d06400000680303110401b010f204403164103080c10f07a0302c0f012089a8403a004a07010074403850006160064050150030507010327a1501d5408203103141c1c008c0706c4406103060784400500810b0407040d09600b822840258200400c445a2003002c11100003030295000c1c000d100443e00100090768004e80d5500d804110702900807440341503203c2d00d5400889045001440111010400602076222101076610041405090403100d6030344a00525260004940c410305d41a000c0e40c1100090061420507442006400d846500d5210729201c05400c500c4054840d000174000c0d19034108001072003104c800b60030b14000c0d028170030041c04a824240d5540020b01000c27001002c1000c86140060403038101c0e03210741c0c0c0401c41075890280c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 977284523 1250 977283273 977283283
    0x90d12020c0118030605090a0b0408030f06060c10051906170c030d1e121a1c240207080a050903060f2712210a0b1c0c09020a12060602 59
    0x1403c00c0c140504402c4c404280c159000e15441000a011240315103d0340d19905080c0400311340844031954004104032070781091034915504000207440481c202407855507599103074040d4a00c0030629039511000600880d03c0d01c0d00400c8003101c5200c1c10406151546a1181400d0144000c1c6515114240041031541000158507800e00100d40c0d98500d41c1807002c501880c00545040b62904000982c1d45c100486074641c466150700300710144190103980c03170341070a01c402131140841e0360041c0c18011188401207410704c2104425000440e10342c001808025210000034020342201034040480842d601daa0303103420400030101c49008404684050303588603208025801d085a0b5242100f00071405489079032064400c103640441e2070410b55400d0480702c0c1d0aa650f40c5c0180c0550b94500e00446200305801c2072025103075810424800b01448000b412202080507000440680d00002440c021204144000a440030010b04004c000c155540c4141c00300040080c2d1091a01c21011840d1020010b03150303000041c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 977285773 1250 977284523 977284547
    0x4090b030c09060a0e04021906170a05070210090f0b0f040303150b0a0c0501271a060a1215050f0103050f0a031d0102010603021c12020d0905060f090d12020c01 70
    0x14904181c05c046410500b0640a0000c03038200c049194000c0c0321645414454001e40801e40e00c041103d001d91140000c99000580790004c698546401d00444076404642c82c0b0141c031660402141040310340c500706405004030500509101d1419062007110345101d0300e00f0340141e02a0b07509200411031004550445030043c45041400700c020407143c207032140101581001ca5000340000980034040400e0b000320340e0301800820300c41070308902c080001c0004044a0b024998680001c00307580385002d801180005880c0c1c0250b0329810034000341181042001e1543d2100500040c00034842d80c1003109240003449805e000845a500540010155080c00040c41518298055403000c490807103c00c44440d032034410045007411552070300700200158071524201c00f11140070740030401400708a41001e9012030343c040010750440d0005c08809001c1907200c0038103025520121005a600d640100c400c84203803040b0180b4036040000e0814982c14020448030482e00000550241c40c2c01c0c0d2880c00045500c191015 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 977287023 1250 977285773 977285779
    0x10815010b04292b0f0203062b05030c0a030905060c1011120103050c011707050d0213080d030606031a010c1104060b130504142401050f04090b030c0906 67
    0x91035440345240d07454126040705400011141340840511040f0450194003158a4040c0110005580612200c0c81004640d4410400450460400c0d070001100c100740320700c100344240c47c03141e00c898a11403106010020140c0c400c00302c9985074811070f0803945422440c035080e00460342540000405050000403071b20b0326190207024020401e01180524000e01004400049010080c401501007228200701c090285005500900403000500001000c0c0f020300e4041c0350301c1c20b00090500441581000c1514400c0c00c00d1000035840b118501940001181a03612040042c410110384800c2103070194070400560304182d9080c007900d041a210340041d4003500c207413240000d002021080c0401d150094204003800e008101080e01c681e294865459a04a00c031031189503003044a0410503440c1a1103404200b40a0415000c0c035440d04011a6003140c07040124040303581496071141000744c0c4200d040366400c4084460300c507192501d40c92000014030341c00444501034801c1001c00c40c240d01e00f010200e44245001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 977288273 1250 977287023 977287049
    0x3010b031308090d0804051302040807180f090b0601140405060a050c01060b040f0f0503010b0f010c0204061502011a0a0b2b0603240507020c19050603010815010b04 72
    0x708a000700c02070a000c00c02c0d54202c100780154240c0359a122140c41505000d5868941c4990807c000c00503010041d201000c20240304010421021b240030681c0c80454100150b2a40d60700c644410140180840076010418036181841031001c1104400809002d03007000c0e0f9605520940003841c01c00c01c5d21417405407980c8036005201d6011000d110303d0040030300c08855030010030601e550304101411034100740c0040c0f009411005e01800403600c1440c6205c0240401c030001d104010195000c0b40004000d404d600d0b0400582813022015034a171500315500600701844542d0100c0344a030390090007030289028241440704103422400c224a4041101401d88048410051400c04050750740740c0121441502495408811041c80011141500c20354000358000c41300c0c070000107224012041e400507441b0322040003a01e0101808102c603030005032481021400c2d282c0810301d6003141c40517007040c4865807150754000000400030410781d01c0412415123a082403240c18000780d0325400702490745e000d2030003000d1a460103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 977289523 1250 977288273 977288281
    0x60c02010921021006062003190c0219090c030b0306060a0605032206060f0b07030c14071e0f0b07030807030c03020c15100f0b2a0304030309081203010b03 68
    0x207002ea0344140b0703070380342d00403613100c2e24560748004152005944003a010a5040321000100da04403c60341442c0403412019500d40241d65422103024546000c403082049030010045046441b12481030705284030550030075a0081e40d441e22240600700726202400003904200044019040c0014480d0082078024107400e0040d04100d0200d9030303904010300c000c0f240c1e000310074400c680030240303550010b001b40500804100c850420391800d4258107950300101410f0801c00c01500425072024107407400c40d602031292203d1040801e40e00c0e1501c1e6540c4c00181220040d1711441d00500e10300707101d01048a4072003c0901d500f5a440c0038281890041150150101d0070036000901e000c1d11a9000c07461a00c4a0304005042c11122020a494180c82c0003514561855030340912103085003910100c4001c181a05110841506180448545000e565240b085d4034001032084589040740d1030b420a038507060309007100d40b140d1307503420020581440d500c03030807070785000c1c040c1c120102440c1c440c103d0741a510545d40039031850716 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 977290773 1250 977289523 977289563
    0x18070303170411090c032a031609090204060309060b180f1b03180616020a06020c0102040b1201140105091c020d020604060906020f240c0c1009060c020109 68
    0x10000c10844480c5541c00700300f00290f541040d018000c000340c0c0000c68582ca00588a081403600c440c810b408070505007128030510080c201d04503548a00c0d0303074940e00402840440291242e40c80c030b8000340115400400c0120780c2607455030040068034081c18050182e030318400b05121000048407000c0641040690000e240340050342c0c0d80755082110102075508001041410004580050320f032403852981c00c0305400381c2d0500c2004155040111400107c1e8070109400740a9501c2c03034200030003000c403038001c5400c0755081e10a5050340c00a00d40358012590382c02c280054924180001d019402d00302482c0300d80e580c580e51140c811b861a900f00602016120074122004c42e0368940481d41c01c036402000e00d00c1c1c6400603140c6401800c010034a540f989240541410400380c24210422810315441e801005141c0480c501c3e844452420003a10a108145480f145080a158418200c2603005442549203c0d8180c8005d82e0000c0103d030f01590041215001048080742610842480035245107542c10442c0c200315 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 977292023 1250 977290773 977290817
    0x150e1c08180a05070902070308060405160c1407080304082505090624031006021f02090d0c030f020f010c17030903071b0311091b0a090e040b18070303 66
    0x8048032040b1041400943d8905107424503e410030b141c0d141d008101c8004241d001081c268100d00c0c00c45081c0a2490417444040881d01000d000c0003c0020b4600030a0a00c40751041d000d0b0400301c05000e403101c01e43c035880d0742a41c1742c0c0540b103114124400d6020ae01d6845099514072100098030040b400f9546280000300b160400020b0074040d4045d400c408640c4a01003002d0310042c3c1c000682007003d481c0d1510386c003190b2407000c440d0b0100302950040400322405d010b81e20f0b11106c2c4034044080c0141c50324840008103070400c2040800425106c400312012062021a01020500501c00c0b0b03126000e0000544c0115000401102c1c0104031060802c00c420301e04514074003955005104008484c10002c8a4661032a03007446a6400d1050b8281c190080c01881440da403005282d810030b492803d050f081800301e040b44c2039030071038840f4070410300070400340300350ba12804084000f005c0c40c00880030740b82001e0500032903502c820354100101c4400c000c801e40ba1000c01040c50000c50350180c80d001e01c68009402d601d0720f00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 977293273 1250 977292023 977292061
    0x12030c09010c1104140a05060102010905060f10050d030c060501090608030711011809200c0d0305060307030b040b0910060b07030c021201060b03041403070c120609150e1c08 76
    0x7030300180645001c181c8951207455035050300e805c0304030180e05054202804440015102c9411039040690b014045800000c1e296000b001505a40b40d09075566910500840ca25070401644003100207440c1091641c4a912500e030380f0300554040080da60385458401c100d07105c0384107010090b0000e0045030003082e15084484c1c0808010b041801c6e035030303000320a45003039040b482d001040c50b0381e9681d808182c01001c0a482144401c81200340074079150405103819030f80c0c1d03c6040c40d0780c2015102c20004006480503c1044015944280740001d203040904e40b100356000c0032500c5403054841c204011806071a00d0003414122002082d5642c600700560320111400300800c0c8041c0e8005104052520301480b0921580d0000c2120000107a00d0b41004d00d414400c4264088414071554018840200803070b0034000c1034011504401310750300081c0c89902d04180a020403040183c040c941c0300104144001c03050304886203450403441564001450012480c001200100480d000903070720b440000d0160078520726043d40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 977294523 1250 977293273 977293283
    0x21c0c1e050307180f06110c01050f0705010605271b030109270309050109090b130e010e071e0b071205130801021602040b0609101407060501120512030c09010c 70
    0x20080070b05071a80802c0c041e07a10010300181030017000c0229a030312001042c0f03042c24110240c441003405d000024168010313030a940f140c08000003001c00c1004400d501c600700030300018094210036109440780740e8110050801001e0600c041300001070381d090843e500780e459000b031076280310704590a00408a009081423840c070442c80ca00b259a5820361000c5078512402e02d44240c0d5405081800d0a000406c43d074041d45c000c08403141841d01c90400c903524400700310303110401848000740c2c04003507201c520b000d0040d8641d204094041c001c0045000f1145904000810062402e8813031940e540c0c0c0d401c0c030450f10680001604e0184004070741c0c180c0d98444c00041c0720014a038802c1c1e80c00070740c94204440c00c9900c56124111080341004010b02103092030300409140d079108540160601c840d0101140c040c1400840d104200001e80110110001100042d0313590a60404c000300002c0d03858956a80340075030503000983d020711540c8003c59040b400d02013141c1c0300e02000d00340c1da030030f121036440107403000c8a201d502114 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 977295773 1250 977294523 977294537
    0x170c0c0114090708160308040e040305040b13050f100c022e0809010c030e06071206090c11061f060e060d05091c030c021207020301060306021c0c1e050307 68
    0x601c00e1004403001d40540501005048164034150521345050020300c0a40711004581d04100f01181400c0140e8080380c890501403081035481e0310b0b007101d0500c03454000c540c10500114800e90018000c2469909403841030318541010f0307902c981001000d81411003401c0003c0d4415951a005088c4210741408600b148000c00705003c070309841c544801d810800420002900d01c0040045000c000d014000041405040400025541c450b4040c3c070340b000145003a051122041d0300f10300403503060303100000a0014510402c01c42943c5c60004042c40c0c1b046034000d1903131040343c011440300d00740029071760000001a03001700001840c040d410307502080207400e050b500c01010f201c2d4640c004900d01520f440f421409002d4403c100400fa12046001d03403c0170f0000c1010b10f40f0a0b071100603500010034852003500c43d040d8036150155440003d024100702d4100600c4540085001100d01300307060350001e003000c10300d20140019038980c10101d40a50001280c1c90410b09403006450390140514029a0415400c2c54280 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 977297023 1250 977295773 977295791
    0xe0a1205390d02030c0106060e0904140f1c080604020f04060c1b120312050f0c0f0403020618011704080304020108130c0b040f0b040b0915120a0203010510170c0c01 72
    0x40c2810b034091003039400358100042c075805e00300080c49110302030815810040500c2070604080f403007103000104001d110413012220148840810003d80d048040d9017011140b216015800f0002c49007190340d40080420790308008a0418907050080e1580700d1000c140c000e0802d440c101c1c2c111010384a6041c141c40361444004c00e0b08801c0701e1042010090005907900c1054980300b8a0010300e8140e684000d81441850103041c40f01840e0001081500444030366682611010803440390703111882035a00084d8415000101011002c0190804d09400c0310240c031130900c0d907000d0400005800404a50080c0400d00c10000100198001d2000e2038000340c2062035185007005a40d41c2e000c1c442c81c030381c03c112007600010408010110340805054040d0481c102507a051924042000000c0e0188601080c480c0100e04241030580a040302510541c001910041910f800d00d18511030003903100b0f005003400380701800103805480b4000c1818852200310342d11445866a540b07000d45880b41c02407642c0051340d540302c00c140d03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 977298273 1250 977297023 977297137
    0xd020c13020928030c0510080103121101020c0f01050c0a1b11130b030d090e06060f1c0906060f0305061b090612061903031e030209040e0a1205 63
    0x2103c0310015000b07450300103410b40c144003886a18a5015620510440040f83c3c1c02c1d540c8482041d0440360700014070100d0b416001010340340502d510004c02c08035803003c21b42401d040e00001c2c580050591910080019440340c0c20441400d10075a1840310104030a6a25900d491060503403c01000740910440c1c0314000803c000200d08000185842e440c02d52140c580046614041c0b00d8041d4010b401d0400340e106614000f6010403404004104912450020504050b0380c1a22421244003490448145502c1c030001011030307004003a0818165a514a41800803428019040420007602d0b0014010840340c1c0c2c3d24402c0100802e80010000781c01c04062101801c00c0d02d0328006485426603500c800186442c00000348528507a03010f030180e000307411501007040480e40107100e2038103890310940b41c1050400d00345d100798040d22911490310380003031502c0c02d007600c060404510720f554580b2030706002420004100048580d80a003e942c81406e000441c000505006080c0006a4501d02285480c14600d000010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 977299523 1250 977298273 977298319
    0x20c120114010609050d0809060702100810050a0b030c28091701090305070219030f1101030e0f0705040b0d0b0c03011a0c030706230a0e0d020c130209 66
    0x56404640e45500084032001400603586001d0405071410910107464400040c480d000600c002038000314001409805a840f007100b21442c1ca9005000155201c000140041840300115411441151b0211004c1914501030720300b84212545200503d0440d218680c00d0360080e48200c00d080d00001002d100f9109003140c0b41240280c1100944403d001c181c901100d0351181851010080c500343d2510111800003500501039a0a054059400302c820710344500e9403600b0500d00d0f420182038001c0c0c00c2000c8040105c403403618005564281ea00784660f0214800d61580c4541445007a22030341c0290743c0038089070803e0351203007101200040c0035030300003621b0b91100b18039030000342c078081d0740d240c1c001005108102c81c9910040342001c3e80154103103490807481a4030340b207000c2c865004100c0c3d0340356000c19851041c0282c00004100b100f02c60302645041210038100141003001c4801c0960141d82045c101040c0045107010844070054118023690b442080000025440301705140c0e8807001601d142c003c540c00e0f11807 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 977300773 1250 977299523 977299549
    0xf08041413091a0c0705010501140f0d0b0112021306090c0f05120402010e01050d05090a0c080703110f060d020a0f090f050105040306090302011508010b0a05061810030e0a0c030c05010801031a0601020c 88
    0x1404280c081800c006000b0821022f1003418051002c0f4085000000c542043c903c0c11106500c0f5005440700c00d510000761840c0342c0b03810100304039080000108a01070790384e011040315107083e225046c0540d84402d0030b454a0250380000c594410110000501550240201c44405141494054a040142001b480071541c05a0300c0304100d5200013240c004010005180f50050403810000f0311030780c1d00e1651540203130201410102d000360288030030844181c403213070140c0b2008800000195114610b142e0300600d103800c118807020005d03810810028500b440100d03081c098440c1030b5181c0345401e0854072030304090429480d04808541d40c1e491940c0103c10380f4240d040c00b0384912000881c210341c024003005208455074101520174201048400d400502a440208003000300f910305860303210b0a001c042c0c008002004500b40c403030055441c0c4008115100010009903485540c60400982c4c407040111641c0009000042c03030301200002c600c481407004044160701490500c111403220822002040941200b02 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 977302023 1250 977300773 977300789
    0x6161202210106030510140d060221010f14150408150718051c033e0a0308270307030503160804020303160f08041413091a0c0705010501 60
    0x2450007841c0c054460700082c0140241e2a0921440c200400130303800c0c0c000700d4400c0c4c2420812100182070a40c9aa0000039005c5030000f100b151544005608a44c5020800c0100c01e00b0520070400802c400c00d0310304600041d50b00c805841e0603026822010711048000c401000c4108010030b01001404600412188901800100d0202c07001d0403d410058540b2341440000380302070411201c180502e49074511140c1620001d040c4204a007107403400c054600e800304007540303032203010780c0d540c4800d4403d09442421003440840e60400351004481a465440f180b00c9030700280000c00c60300100351803c403c0d40c0314940207000d8940c4200282d040261185c9580c1c82803104070301040011040049840b0310010300408075140303062181c101e1401f40d000036201d00c940c0c041403602d120140c10740070506c9a004200358089510046140d80d807901c80c0500c0f0507441907402054411000051003802d445082e000f1030b20301c00d50040c00c400400041e14038492001500906071400c21005000d203501040090081900030f0000d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 977303273 1250 977302023 977302057
    0x100504030302100c021207020123090f010905130203061f0c060f1806020c0705061b120a0c060506010c0605040c05041b050d05250e130e06161202 64
    0x501e0060308215080e400b40e0105460840429800d580129000018558072107400d070382d4818901c0184d441c505400c58200912115200c002d610281010092a00312401c81c2c1d10349084003040e00451b8090709038011a43c1149502e18040c184500c203030040c54100a00030464a8000040210b055014007040c25090014800040c54014460b07140300c0c01109001c044001e11000813650a2100100561030004180582c0000d1010f00c00304188034082c0135190082c5280d5503062034401d075080c0d800400d1030101540c0a4049400020b0000d4021030b2040b5409445030300001c80d06490703140c0201070040416052121448207030000814034442d0798400c610404070540494107040c00d01c07048035440754107245e04100b00e10244042a4000d4141c8801007402103001c5a41e80d14000310585c10b0305005451041403511030074007a801c07a0850696940d500e0f050302d5082d00a448162440141c400c001d00340c682a4100d0004503484841c180391183c40740d107607400d1040f191454400b07500b00b2a406001d1030800a118 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 977304523 1250 977303273 977303279
    0xb0a05060a0e1c0b16030f0c05091203040924090c02070611030f041206050601021209040f0e15011403061003151d1f15061b0c060e0405090f060a020703030902100504 73
    0x94400c0904800d0b000c41d081004a40b108c07409850b610131543c50500c505800e9844940b034450070400c807006054040024020841c3d04408200f1186000f0f2411060401182003c241c00000d881074100840c1703603500811281f0f103000c0c420344242038000e8114819000812100103854134240c0200000c0420641900ca00c0c501b03030a1032011241c024001c903045401900e6103040d040105070a85180c003004690020781c140e43c00c079025004118494105507a0b0140180303021007030308048100e80c125280c0c1190062001901002c1681700c2400312440c0216002c1100c0502c04103281c01d40503041e104040d00001502e204d503071150b030486030503540e03807107074a5000010180d010080072400000d14801220240440c84003008101d100c08042e015050801c585090141c0c01e055101410180183c1c001c0c001442003074a6400c0186414400094103000c0c605040110302c102c01c2c00280721180c20362603c060000c1d51202c03040400079500c0200c3c04c0e0101500c502580c005a03544222015028546484050381c40389 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 977305773 1250 977304523 977304527
    0x603120e01030b0a0614090a091d0d03150b0f1b1f050c03010519090c0e18060a03082d091504030b01030f0303140405010b0a05060a0e1c0b16 62
    0x2034003e4038084c511010b0100065600042c001052906034120203880383c0e101808942044450780c070a00a440c20800780c44100104040d8810000c81c1002c01c4d5404004001811740503154500c1001000440484003000000e1054014104400b84560410314040115516414501030b48400d0501c6400c900c035030007240d41d0040c21080600c1c1041d0410f200343d00c2e1003140365005010511440f0b029200d00e010300d0041c880c1c6403031108046c00e0949020000c04246900007003400340d07420410b030702500003c10102c003543c0c007024110b8441c1000800320703100d49003169103c0700283c1040f02881424000310f212035503101003800b40300ca4084105143c4d5503d801c500c0042082602c618045695206010401400416141c02c140e505483d003080d208400410145011401001110001d200c03401d040d0082c0402c00006401c00820310404a84004003130f03440750300b0810f4901c56081c400c6c010a20240d401c0c14503041840743c1c0076030000070303182a4012006607101d060340c0c000c01321142d80c80e02400310506400a5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 977307023 1250 977305773 977305781
    0x10e0c07050f07150f02120a03020c190b06011e0f110304030516050906180601050706050108010c030605091005010c23030a030609140106030506190b04051e150d0603120e0103 77
    0x907445c90407101820000d400a5140d03859814494905280000c40c00012402901101d090740b4101c4100c9003800c800202401c01002001e800301c030034400020104500d0361184642c040384401c0100440e00700381c4000011751320240b0b062070710b100340301089201100015007440134000950046028240c1304842941c041d24180300c41d00b100c0d201d80062014040c0315211482c0c008100c20900100c1c58143c0c03105e000603680d5028203880144114103110001c1013058041d0000d240204040c0c800307104140e158420014061170807141c442101c2003c480402c1150b01c10070300800d0640c05042410111030740310b610004240c0401107400c03801d500019005503403607814407441006014410041102808101d10251460720610403103003019103540200360305d5a24004200a040b525100940700c03142c0d00c400c0a1800c2c1c00a11405205982c000c0480c01c51090152035142c0c0300b0b400405e00101000c1008004015410109001010035941c440c0440015407103880c85070744018640740c05001d642008001401c0e1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 977308273 1250 977307023 977307059
    0x1824060c030919080304262a090103020f0d020f04180c08030705030307111e0610060903020607030f11030a03140a2322080703091508010e0c07050f07 66
    0x146401030360820041c50040296400d5070903000810486044000c80c00c450501481105e0f06a40958507041c0c4584c8184d908002c00c0321231704500001e11400c9142006544202440040e402c0319600c14106c01e98034029a02c9484a4801040d481444c3c400501180403900c00e00e4400c004285c6c011005014000d01010880050800d036009524124a13030f940c064407800040c0665007130019210030300492180a0000032400984a08a507910350700d00342903550350300720540c1c00c0b04518582880210b64148101c14440540f90081d000c50f04c2c00c00d480e0380441e0114504070050702000601ca40c042d444410910040180344126a400300704440b010b20031102c0d984000d41400c01c41b524064412151080d046441d00c4201e8030f4a403525680e941c0c0c6803020000e9030411203021001d1100c416000b04000f05500904a035601035501e0b862401e0722140742d042d200310800c0051000c48e2110004210620742c0c44501544411420301407414000a0b0f981c5a00e0000c07032505645c00d075040b001052211101d582021845 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 977309523 1250 977308273 977308309
    0xa090203011503200a0e041b090902060711060412050601050f0414070320070506010f0b210c04030b090f100b18100f0b03070e1824060c0309 62
    0x800d8550383e2035001c0702059107413101900c50b940401d1580340e91481c42481c004c0410391200242441c0618003980e140421101c0388448907203001e004a400c4896101c0c00b28003a41c080c041d10b2421394192540d0380400410402c0c294010010000800c5000d141810310b5612413080c0300410b03540d4104010414900800048180a10302d003402c0c40c2e5642220000c90f54001d02c9500b400213070450036030000007003180f65900d00c040c07860300000c0c010104540000d01c141291704540869800c240c841070042e4141c03203003c1c0042e9030102803016007000c0c00c880380029908815080c21940c40c2c1035403984d42c0060030b0402c440031442e0344c10400a04a02140620801d14000b030401c40400110440c0c40018540080e1840c1d50341108100000140e8900e04030035a08020b026140e014025a55a9010300e8400e98030440d804c10005100042c64800d0f800d04890300400d050703d00c0344440d45556900c01c43d14403803190a600300c2c140008401050744607124800140410003103000a5540c42a0407403d000c54541700c0e410741c1070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 977310773 1250 977309523 977309561
    0x9041d011815050c0d0e070b03190506150301030b0709030f0303051519090b0f030a21110c0f06070c0e07030e0703020d080c03040f0b0301050a091404080906120a09020301 75
    0x13508802c2d008503085103c449000051110b085200c292801003280c1045160349400002d0001c0c1c40f4851022442003212168103000035581c0f002400f40311603004000054290082c40188006000d101703e40343d11110501c0c1124445a0b25140c141070b50300c162a054011079030310820300c500100040986410340c0815902c014049010812199031810288a50261684c1d101d4a41c041e0f075036594204890f507200202100e507040c0260601c0e107002e10140d2002c264000c10305820352211800780013044c031400c910303070090618007805500b403080c1d1207204100994410010007040e00010384440402c8041d013000100c14190f440c000390081c1c21242c3c81c03910342c50381d58030400d41000140e4405d02c1c0c030403010f85c2c400c0c001501c6812400032a851409550042d20040f10012408188140d590003c1d40c100e07a01100c3c0d095400d503075400d0a80071510303080580c0c00184072000000e0003003070803580280b61a0700040c04251400310600c90014040c1d40c01d60340449680d89520032041549800d000d5081c1140041407400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 977312023 1250 977310773 977310781
    0xc280510140a0e1f0b0d060b01030b0d08040e070e0303180a050604031106160206030c0720030606010c0302160906080d0203030106020607230d0b04150b09041d01181505 74
    0x1d42e07030301c1303512241245012503951100c0b010400368000c0902d416010b4100229115540b4007800a4058407400c14006490616a6074552030880560381c006500319402c02d107010705244020003012030041052080c00409060500151010001040f100841c5002041032501c4401000210031b01707540001e204481c00d0100380041030040d4900550324504a42a5075650002410940404000b24019510a030040108080114ad003402403000394414a52452140701259041e000040b0700192036030180d000d070300007a40650050030750a03411402030044400002d803035003481e184003659411030a20580c40b6101001804810807842886411a002860556050140095590f40300610000c00c100c201029108000c0d05a8600180101001400c903500c0ca002c03102200544040d40740c2c030307029920f0b00f4844101002c02c00f2607002a00c0e101e504203858a58407a04000203440c425041111909101a40d04c1060409120301c001d00111020702060000307580c1031a5804071040002c2081c0e07503090800300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 977313273 1250 977312023 977312051
    0xf070b0601090b0a033e13050d0308011805161d040612050712330204152d03020f04170c0306070f120f020903010906051009020c280510140a 62
    0x1c0c00340d4200801410380c44c7c031080c0341206001000c9521181d00404030120380e80c14154040301e103a06071040c0881c0880104064000c5100f03d940c00c0711203141041052194549151240c0c03d600c2d03e160106052159112020b0b0001d0110340856000fa44001518600c1c14200300c4180184d000400c0040c00c5204200c501e0785511800a00400814640144543c00d0304124005260308044000c0810700454880b07881e003000071100d4000565200100d003c3d088845088110a0900c501040c6118031201020300c450200350302a40091a4030144070b082488081004105440728101500038140100851031a5409050070f02c5809030000741040841c0c119281030b2600048030a40700d00f202100064100c0c8483c0500009020308074019070b040d400c3c4400b94088c81003d070000e80c054040844906040d80e914000c03002207108441e0311842c260407818004045400400c00d1122605100c124200482102da890f0340c10170180701e020b04407141e03842c110114081c1c000c0200692080003c1c000b080894104080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 977314523 1250 977313273 977313371
    0x5010c02060702090c0c061501090b2b0b060c0105070f08041a0c0705150405010e010902010207120606080a120206130f12050c010609060e0604020f070b0601090b0a03 73
    0x83c0c004c14510700454a040c03010011030f1034000200b803e0314481d0134080541c40f45042c441e80c050740060300014001c903070070711060119492901a03400325841c4c1403500d140c0c101c450700d044042821a90760342504010b292203d04c0240601c0526030300002d102c2c074100c4405090320303908000c91820003084404000c0014003101584003020007896808040707542d14203425090303100d905801405c0d8040e0500d0359110002c2c0429a40c0074510800013408181e410315855422a030319550b020340164030407041007000003c40349180200500900000c50040c1e101e206103840c10300f085100300eaa02e100d503a2010080355043c040c640d005a007000340704568004076116000200b40c002c3c8050900c0090001c9413403498001c404807401d10700b103440244909903682c500c44008020a11030081143e0940c03000403460314180c82203a0380d1002580400341410260b031243c80d0000e00060000b41030090150380403074200204c101920000b601650f01140c903100340441d880f50081100300060030400e04441d08081e80e561044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 977315773 1250 977314523 977314537
    0xf220803070b040f020a06020a02010e03030324040e2e0c080a020a0c06060b04030212010204121e0204090803061815040f14070c0308090303014506080705010c0206 72
    0x71500340a071a60306142c400d41490582c025440506c52000280c101d17000304011312214000d0700d9120360640c00e0340500d5103d2208440794641c1c0c5107890744041ca842001c0040584810b0b0203400000e0800345881140c3c94042c00104045150700d080f000e00000340e4200003141000050494280071142500c00b02511524020700039000041d0040f44029a4501c20382608116580140083c405036039180354903595644640010707070141e0807000e00315010007814002c540c12036150a200604041e003585a81c03001003440302a441e0401c13132001c3c001d009a079450094654030707809144100c2d92428680200300c56404401c0714440d410101d4000c0101341c02c00842d00b41b15041080e0b1b00418948544401c11000788281c000030305e040c200250030310000303d80c00401c0c01c2c4254481d440307032400c0c1d4591000c40d555a00091007040104d140f000c00d0880064100e11030401280c000c284030403140d00b80200702c0c10401800c540f001c00203940e92442000314000c1080300800408003800c02e40e0354803201c0c0d000705010b8170540c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 977317023 1250 977315773 977315783
    0x12040504110c0109060e010e06040b1605130b03160309030207050405060402040f0e06010e22020a030623030d03062108040305060a0f0b010906050304030305070509060f22080307 78
    0x840400040710301d00c01c644541044000801101c805840d04900600c2c0d0708904a041d90303e00840b00120301c074005402400385d60030002c0b50401d90366032003000100c000701c1c0c0c600c40108407040c0414444c016110108002516140d40101e449142400100c004059168000003c250030021140d002c640c02140850640d401542c0124807561464003240280c801e0f58440c414000c00e000700090882141000b140c015942641c5162005400f08108000311104007245844d4000c0340d03110340600c44044c1c1c001c241e08200c0341804182642c1d6034007811100c2c680c840c02c20714811a011072003029490284000241e42c1414241003040c00d0803c00310b0424240b1454502004000000750a800e0002603000c0c1e4005540c40300c11503060346040050310025000700460664424101840300b88158014200da1003554202c0d524141190b44644081700034140180101c014044208000e040503203a00e00141000102e121202e81c1c5c6182080280304000601252008503001c0e070b000512402a012003151000d90300f00b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 977318273 1250 977317023 977317031
    0xd1211160224031b09090a0906140405030d0c080705160602040f06120e06060d0209060f13061707120f1502031501080f06030c150d050108150912040504 67
    0x40c030114104a10b02d006184031262841e10210110a0312002148215040302c448041c0d010340b000c64140a025a9813500e6000048500054070014158801d803029402500003048c0c08152407902c6070f02e51001d85003503c0641002541c8a2902080d00410300c80030043d1400c6425031500d03100081c203500440401200401400720080300380080c41c0c05035005000400391800a103a0b84800240c45044549082c0340d00c141007101e40800c001020030360380d11400000c1c00002e8011425030800c07070040c900409155220038200d10080850f122410742007c2850801c0002940718141404030300c04036070019451543c1d03408480d092090340b844244a891950780542c44544011071490b0140700c00101841d401625480442000b080018201d0002c0006100381c0b18a40152145c8008003c0b000e01203c080c0c1e09a8494140001d8505001d00c9114a0481402e12141024180440d24013961030aa000e042543d00203501010010248005140c00040041c0108500d042455000c03010340114407605124a6036 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 977319523 1250 977318273 977318317
    0xa0b04080c011e0c0c08030d0501150207050105300906270309090c0d1104031a15060319180611030432190c1e181b020d1211 55
    0x255210070113403211b101601e4407404444004030003048244503d049007c200000204a01d0012030001c050b91030680d110f40c94402d002e80800025500c40781d10400004c421540b40250315000300c2da69004000c0a001750003542001e500c1c0048264090408003007014101d410649055800021180300f003605a42d50400c90f42c904012441c1ea0003104001c2c50f600c1e0a082102e9942b03c5440010010740b4071903100041c0a1441b01c0021441003070858221051030f01040d034811651030500040c40d4001d0401700306440002c221512002a01d941c039402000403520300c000301c01003003094011541c00803031a10005080d80b0b4140c8a41900a8080c00044030000d481c2211101d41c00d1011440f504125102e0700b01c0e070314070003160b018105140c01c01500f51210f09420801040425510a86035201d01c240d9002210003421300c6e031500140b10000302490500c650320303c40203090103c3c40900010019141d005400c064540b02d0001c0c0048901c2c4000030a0030786419940a0520000016160900002e1000d1000220 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 977320773 1250 977319523 977319533
    0x1807030209090a14030406080a0b010f120e0a060203090c18130f23120913050c1b100f09080409230a02043308040807020a0b04080c011e0c 61
    0x15007010090704c0c00140c00c0c102c965807580040108226030807030350b40742e00641ea0348500c101145c41030800240054003125002160030b1291100030807100a90800189819460345120b20302000c03984119038054000c0104410800c00307108ec07001d07100e41600c1c1d0030745101300780a4040c078092000300044001000710f80c00f0000d0086065503641d0880d4410124030035600f01202d007941c00d8184682001042c4030b0301031120340c6040d184084e11807001018204070b83d030818030050407000e0320b401040d4600615007400740940005041001148002101010741207548240864000356188100d440401c2070130104040009041c8004a8041700d440510000d1041440001c803800e50020b04044060032101005114000342180d004104461080354034235400c0c0003550051141c4102d58040c0c20501d984c500072611200d018a02d160380c03051080c280c0d103190070020741c0004c0c22a10250400da203e000003050501c0800001c00080e8002c44003400c3c0700c0b12400c0e0008408600d031600210401c10001c00304009000c1113 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 977322023 1250 977320773 977320783
    0x50c0307270b0d1b02102a03020c0714090c0c010216031d0111030a0f0c1b030317040b01052103160320030d05060a0503030a09030b180703020909 64
    0x1035041164510403039a40440ca03059400c9400190745036403400000340c0e00e0004134410070700c0e01007094016040071381c041e8039850010b11040d1502c403406104528032800c0303135401440c0010300c00c1c000e0b1401a16440d001191524183d101c0c0c01c9400111840905c942e03042d40c85445640e0f004803111a16992002c440b4410350181c01051804035800d254040da01e420540c110f40b01200c4261401c0100006003000c0004581c4040600d0020285401c02c11940a9840c0b16071007802c3c4c1c1000c942000c01c0c40c81d0066a900039100c130911810012010120800d00405500000580c15490b4044d84806141020b849901250b00e040c895680714198405882030781c640b204008207400c010070b400ba070362144d07180c102d8942c240a0343c0000302e0000e04000e0811810030b0701c515031540c032105a04001e60803d2440d01c12070380100800307072074a68000c904d58800501c5923420070003020700d42030b00c0d0380e215000c0b880c5140944c0d280c42e0141800c408484400c030803250441000174104101e940464085490b900c804001070309107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 977323273 1250 977322023 977322077
    0x10b0d09020d02040c030b130606050909060d050307051c030b0f36090d080903040e040219170106060203092b0b070903110102011b0c02130213060909050c0307 70
    0x242c05c00486100b541d4265020b014080401d440344080308808030007081c01c485242c00b818010400c18484160b4605040740b25030381c00302000e091480e15510075150715240d83c0104030101c0d0140e210427818018110b00521075a1030692a003414000c00390309000007184124550f442c00d021743c1c807215a1201c90920400740911868040c448041042000e14604c8014441110b4a511338400c40c0d01c842c0d5030511500061303214200e8000030318105401c4c1081003c206c5400350050307920100340c41859842444c0e072013a000003401d0382200e8108041e404508103007952407941c03014007590800e10180042d500e400303000c401d640150710310110ba18481c0c007154500c0041130041c05000d1802030000c00a08a070030100000980703010741c0103504003d0003980128243d0302100340d40350b100000c100c081c81c2c0444c05070b105003425501c0207040c81d6061120350b030448101e0300301001e00c140000c40e021080200e540c00c025848090714210300705101c146880400da40042c800a0071141c00c1060380103169046103d110b80750540 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 977324523 1250 977323273 977323279
    0x20d140c09040b060304031b030309051002040501020c030a022809020f1c18060902030f060708160302120c0309070f030c030c053109171908010b0d09020d02 69
    0x1181044030004106400004a2038020341c035003050340c4201e20b00036090368422503041d56a54030001e030401403101c440005640842c14951036036140c50010b1418880742e0040b203626140103881c3c0e440c0030002450042403241450090704030001e10f40150710b0707003403e50010203910f19144509c500381000741510343d0502d40c001e110b01e03403001c20383d0503003203030400010311000041d4004841c40761002c0da140c2046400210091090081051800c00052001d410070754a182c002000d48514480840c222414014100c3c0d1950002c6c1c804c60030840041100110082900c440d46011030508211110541d022180038200385201c0c1c40c0840003851020017000107a0207000c601d08013922450f80c130703c1c2071512040c40b4042180c0010402c403000c28a4100a81104e00300041444000482e205c841d0400241c0242881034003845512001440302003a503220003024424174128109507100604407001d0309150180740c0c10020828001c00402c00450b0401c190740c0c2811034620300244603030316480080c00d900031620000390 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 977325773 1250 977324523 977324561
    0x5091e06031f020301140108090a060c0309080d0608010c0f02100b1513050406091b0f0e040c120e0c03060c28020c010f03052715010e0703060f0f09020d 67
    0x212040c5070f00514101c4000c911005000b400c80d5005440c9103504a4101d0160b40c441d003417500108009030041e00c2242e1081c140018000c60580b00c5070f05a0784001350075003030766483e14800c01260b00244500e0404103502d203480c0840c48110074001752100309582040c0000354942c4114126980c4141d542c46601c502c0100c05652641c108000e00710003609031044a2199262410008070f11007180112549103007980a01501d09140045c1996080212802c0c002000781e1314480041c207480740c0c8140200707102140c83e40c420840c0f5504001c4103a0b21070204084c7c094021804100544d1000030704641c00820446007540c4074211031720340c074058841d0092500025494100c4800c0807e0300420a419010400c1c3d03228004003115078025030681c2d80a031007410145420301502c034410503801081c40f9944840c0307000e40f14a503c150098070000785082c2c01c092103a00b054014031681070317054800c8100610108080400007480c048810220501310710950441d1038000500c1d10550107980c1c4028404100590018 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 977327023 1250 977325773 977325823
    0x905220e06040b1501050a050c0a1211010b0f030a1403160c0e0906040c120f120206061e060304020f010c021e040c0305090c0d140a030c060605091e0603 67
    0xa41d41d03a4280ca0546402002c1801300f080007103822241010124182c541d54944512010220360036400120b001e2003071f020b020301000014400c18044000700003265100c510440d01e4a8900e401c5a00d180682c81c41880b440c3c86040c150b40b0003084410109402000f411007000b1181c0055055215151400900c2c82000140800704882505013000392680d041d42001c1c903503a400341c1140c0d02e62060760080c24000000300204428002a1014a1607911408603121105915a104503415402001c1080940c04c01e2003008510b0500310b20000780c0180b0036005242501500d00801c04510001c3d0019004000740410485c940c2d000d82807008200c3e80c050721140c44403c0e07a04140011200c0f05050310701c254102000c40d96010702c00e025003402914041d020788a443c0070007040080254440108176442503100d50000780b84101030081103c5a4000e448141d144102468020120380361600700e148150110000d02607554545011900c0703091011071026010340710304d4000381c603100d0101d20321030220309804011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 977328273 1250 977327023 977327051
    0x51003060b0a350105100e0c280e1905091312090504110a08010b130b0f03010810050c1e09150c060a051308280528090522 54
    0x10aa46030900c09030143e80041c000580c0c1d003a90000d59644569481c1540d042c02041045003600390400e041260091070815950f41801400c54190104040c04204a8080040b07680140d44520101c00c07c07103620028036074190b0440c050362407a0041034090483c1c0d40019480d40084500c0d100e07901d4010111005080740444000c1c00d0802e617002d41d81c0228140000722010300209001c1e101000200c1d1500841a0708001c0c2c00d1105401a0400101d10102450006000320001004242d407910071403895275030758185400d2a19200803010302003030701440e01d410094480701c00c0c001c0c0e52244000d103c0313002e1054400c1d2960110703030041180e41030f400808100c969405295450007041c2521303100007520415559a000841150401c0f140c084e00705284a030711380c0002d030740c0304c0040c891020141a00d1400c40200313102c1c0120b0003038103920304001c910002001d44005510301800e40d14140c0185420b94200c1810500800954092003800d0117503041e0010394090781c007a900e001e031107208082802c02c200386a0150b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 977329523 1250 977328273 977328329
    0x603061107061d0d140904050f04030e030d1b02150a030903140304020609150d110703020f072102060c01090609300c02010e03072601051003060b0a 65
    0x400c80d2010b18002c8071070800e50603143d92030040c1c3c00400c00f4200c1014941d0041d103069802c0702d10b00407420010466090543d0303075403040d503005103180c040e00c400354a064500a0982080540d900f4402d60090700074024169001a00304240003154402c0e1a0111070f61010441c030fa03020420140040324042406075a60b64541c1c000300300d03a4065556030f05d5902420040c004140301c151000f80d000301c001c00c0980030908041610340c01090608404074a0074510150110880c2c00360544003100c102d00190b02c4091643c10000c10380d480980300701070800b032440c0042e40b00c1e840101c440c42081c40b60307922a418066560704001d8906420840e0001c0c07080d0b080603e8080000c00e031000084903422208489a80e000002800c0940d0002e40f140100c6000685d040c0241c1e4801c001050480c104400c12602404070749080c0f024000521100c010f5079200d810641c4e0f44050300c103100a004442d41e160004026503240482004021a90803110005d425803685000c514240195042442c0001c2e5900480c00d41000041c0303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 977330773 1250 977329523 977329537
    0x60e031303060e010f060503060703050c040915170f06070f020f01050a061a03010b090f0a08011b1d0603010b0307090f060c0c050d021e040b04140a1503050706050d06030611 76
    0x1c000c2203020703001c403175030340896a49000e140c0c0c05900810020320280c0c000ea1045800c0a1001001402c1c950b0b52400e0700d00360b9000e50f05401d201d11401204001d10029090b6280c03040f40385101500000e0114406940d50312002031501080281141c00080e142d4001e02c0700d14200c1d01c000c4001e0000e031400c1c00c64503024122521847d1442c90030401100448031461b02540d0690310954425498170020004101403018074018441d80514118000134040c0f901b442150300306950007048048040f01204064815450900c8182c017003400005d5080c030039030302d02c0c08403815200d41c04006504c0342c0303500314210303290103050304428130000540314040b03017094118810701d20061290320312003110750b2607409001c54076110f40c2000303410201c2e202c0c4511403041e556007004400c0001400010700d0350076110000c1e0503100001c500255840c04082400712190a50141003804600506510309092455032420340d16090f5200300c00806c100403072010011b010641114001b1900034400b400896050b440301111a40100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 977332023 1250 977330773 977330801
    0xa03200a03140703020c10050916060e131505040e011b08010f0b12070309030201200705100606082e090f050f0c040b0c0c09010803071a090a060e03130306 68
    0x11002490343e40c8280201c0d01400d68080250904d4808150504094140582110024050902004400094800c0718401007115903641d01d40b0300c4c01a4144603158502c0d4002410702800c104002442e81d840c45441c00c1100c400317403030000ba0218008410303801005000c540d03609603141104058462607000b1100f84c10b81d0a02e4890510799070340c6450841d2641325004403541c10060b80e80006120714002e0b88040c40c5c4601900020038034621040b00590b031060590060150460042000000d01900304103007022500030480c01c2191508015010300b0303d00d00245800c4100e80080c00515440c00640e28006072003160b101ca031000c941d250603100740540030046600702d42524010004a18103e80c1c11800d00408444c45d07420b1030113090040b4282d1540c040e6070240a20f208062800626484441c401070003840920041c507182e954074501810185080c00803203034140c84810a01107821008104030024030760064000500c8a2480310890030340c0a081e4004040503070303000d000010300c4040e4009001c0c00101e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 977333273 1250 977332023 977332061
    0x1e110a0311100203070207050d1b06050409200d02032a031608040f06110f27030a0b0123030f011401120f14120f1207090b0a03200a03 59
    0x40c09070b4100e020894a420041c0d002d10710070406800d0410708040f80078090a000103003020104105550b50071140d00c110001400040c0412141010b803090f0107240c50401c9030303411b40d2468950380c00d50340d00271100c0c2d18020590000204080382005192210f042401e8804010101d0151000c80340d5a0802c0b078441415600d0080302c4207c2d144074108451150307502c07007090319582645481d00f0008110402940c10410b004205a01c94480395501801c0c0d0712040400c0114003a003c001407901d1009602e4449009074801404103000030f01e03001103c0d041d42c04100b5010580755111070441d9000d240b00004a415014042444080b080c06401076842d5802515804405036603680010881c40070b1910060802d14000f281c80001503009a040c400d407440c0002200e0080c080030132000c0c03030f42d0302090400e101c02400140584944061a8015a10403005d00b0b00d0950b00c2e190007101d480511800d64181c0805039101d0340c0481c07500c01040d46089140c1100e0b1040e80b034101c1040c000d8010266441541450055 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 977334523 1250 977333273 977333293
    0x190513080106140d050a140106051203030a1b02332d0106050714121c0605010f1b0204060306020d0b0411070c03021012050403120b030d1e110a0311 65
    0x44c4d11440c10b0694040c00500703070b54007151a00c038000801240007091139520790000140607603500c004400c840032078002460383e9042100e0100100e40f032100700341c000b1140c480d09100343c80d90042901d00e4032900220030080d10603100d0b40c100f2100c2c14907042d151401140041400400c09500540d18030f1103508005032240c41c03100e03080c8a1422102407040c0400110108007100000d0f00c40c11058503448040c40840306004440c0b0720050305070f0805100e90282251440c2540d5030b2581500034480102001e081c0702800d810f240b4002020547e40d52141004202c1d07450b504021501ca6900c808011a01301500b1502d40d000d01c0301c24806001048402480746062510780c24080039a9030494800c0c0f54031840000d07409141d0360030300124284c0c0541c11002e1243c040b02d0041c504c1c1803402445d2280d40b003075031501000740e040104401203c03001c080c40c0e4025840010403180040d00024001201050b2002503002404654400c440301403c4420018040c01032005020416411000040c058004901031790000c0742 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 977335773 1250 977334523 977334529
    0x120303140610031107050303070e100c080d0207080904061401030f0b21100c050405120d0c11120703060b18251b050a0b0903040b19051308010614 64
    0x540d1a141d00c210b0303924490522501a0f4090280340c1c00038259142082c2864071150305582007112a030300401d0080395240b0440c601089507200500d83c0c0d0802c80c1d050107082d254002135010301c032050096241c0c00541581888240c2c42a0386048000034002d000c41d07912003140e25551000700c0e00040c0401c1c02d00e10b41000c40062030040366540c540c0030340301c2c408100c01e218890100001400b21809140941c80c0b14402415040c0240740950354107441e050748c1d8525083c284104440715207003896050b00800309026072660302039001c002c0c0603040780043d1b50380a0341c0b80029010f140c514441003910301c100300001041183c1a004851104000c54042c517070700400164400d0b090a04a95086182c203048504520100350b42ca01414400c4042c644100c00c089184841400c50541417401d603083e6011222020420000f4020270394044000c60180d400c10f441d20390a080342c1d000e184c0918017224031016150050030700c03840c1680d54414803104001c10040d40c0b1107003107000700b0a9010340f05603001e01c80110b103281d003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 977337023 1250 977335773 977335811
    0x14010306240c020135090d3f39120e030c070305010509120a11010204051512010b1303021e040c080702070902090109030f020a0504020a0e09060a08300301120303 71
    0x7030341a200d10070341c01440070007900340d586800c10a04030a552000702d6081040c0c501c0c5c2e40203030300ca0b0b031b8000000c02000701b00a03a415602801c00c404049d500c1420342c149100e5409050001c8145a803e00c3e0030498841c0500101816004455151500c00031079010b5101d0300019444007102d008000800c90354850041031600c0d071098141d0607004407400c01140700e146114122a01580712080c00040c142610b91000880c0380f4854201740ea01010080303042a419180303503c1c42401800b990507014501403078075009540d01c010078030010f841070200074000301080040c415440f40610740240308010170011f040c00905214400c1e2005001481007100203e030402d8507200311895000140c44441c050303859903030b480c03d4207030b00e000089820800c03807100003c241d15640040c0004000a4070750314540e1015000b880b1940200428179031041d00d02240c1040b001e00082089840000548038062010360150b8044c04502817607200301518140c00800041e045c00c1d8805400c268500c6a45c09001d840328074800d4110031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 977338129 1106 977337023 977337043
    0x314070504051302030d18270c090e090f0a060b1f020d17040b01060c0807151a040203040512160c14010306240c02013509 54
    0x6240502129286d00c08514090034039013480340040014072101d2213000030601d0080c94903006c103890310500040f01d03012040148141c08040354000c01c1e0401e540300303908170500a0b00100c0c0c50300d080460010303003407200302004141040030f0f61501c1000b02042c1c182c01e075105007081d24012034a40b940c00f1000d00030009402601c4107440c2040061f01c942082d10303c581444c4038840030800010380c010400740c103580c800d161003800d0f000c0c00d14000703000d48942940070b400d4100700c41e003820000320716400814130305d40003807108110303012254180b1040c0e01054500030f1090f00a4085c40d0321845459018010105c0689032146030800d01d0344404c0740c44200754001c188a00100c07050008903581502441d00101114030100218040041c00a07440e0960070304104108428581000256071040340503030200c51401c8110b40001800b0b1404500400440803802c25010310a000582e241001290035150 = true := by decide +kernel

theorem cover : BRFrame.Cov 977158273 977338129 := by
  have h0 := BRFrame.cov_init 977158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 977158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 977158273 ≤ n) (h2 : n < 977338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
