-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3210
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:59:11.874204+00:00
-- url     : https://prove2.me/submissions/e865ddea-61af-4999-99ba-c20d8a4a0f78

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 577158273 ≤ n < 577338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 577159523 1250 577158273 577158289
    0xf01060e1021140103050c090f06060a0309020a050d0606080c0103092604030606090902101d13150e07030c020d05040302090a060803030a020a09050a0b09010804050c062107030b 78
    0x98039940b400e01100942d1000d40c65449460b11102004500c003640d42e40e8284107480d80134201c2c20a008500030400240050581096030f405908090046468607404034412030042c810300104a0f370003c440400003489548000f8808031682c0280b200152584c50200410b25003a40c40da071490615003441c54000c042540d03207000040d9582c456280803800b4400d001030981e14802c03500020902c5191074404900384225600410000344240c0e51a400322040e04c0f01945c504011140c058100144401071010b2800d1241106d2004110a43c010070548a50350080940c1c00700c6070400e4100d013010f4820856815458010813904500d54009000148207030b000040c15031203140006409000b0010118400a81650000c00101800020341c1c1d22400e144048038081c0d40a101d000b0001000180003041d20300d08085580700319010620407501c5d1040e9400151703078800340248191114020030b61400d80d1030f21502c008000a041c1403000071000d1050726a41d071143c900150086e02014644050354145459001d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 577160773 1250 577159523 577159547
    0x15010e1206160507080a050a020c01030605030c0d0203010b041d070e01030c06110a05120a09050f03031e0408060f0a0c05090306071d040906020c0601150f030b010908060f01060e10 79
    0x4201d1060b4082005071203c1c030411400602e00c19000600c44d624650004c0580005440795081e41e17051190a0011030031369607d4026158180c211544074000b47c034080c0030801c001480640085410842c040c006011950400c00701461000707612030f004c004120502084000d0302c02d080603031f061941103407a59056140307540624018000d07411a5559414030400461980e00d40c0b1070100da51080c1d000307505000c0c1e038001d004900d010400801d8081510300c1c284040c6070700201e001c0c0040d400c00c001213400308401040d4100c09074290a04100204108005002880c403866102c52210b1707050070038080c0401180d83d000c28000c100482404124000d13500803e159400031f5261070076161800412201e1990098168039890380240b80000000030081141c0217000741001c0304e02035030032030307a0381d03e9508022003000c07094003000504528032441c20902a0740181c0340c02a062402040182e19100d966203011401d82c1c0e200c45c1648641300411105612400038841a8010790708040b54841f100c002412030214a6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 577162023 1250 577160773 577160791
    0x34081614010909020a1e050418050a0e070305010e0607050c0a02010f11030d0e0f160306050a020714010218010906120e0f0613060507030204120209040f0b15010e1206 73
    0x45040c015a00c01c0c6544030140041c0c0b50110b50f5030207162801351030050284013440310840c03019480301540d40900299411680c8a2600d807220392900c1103941c00604004080011503aa03038181403000c400300b04000da003e0f52160700000b0f035400c28820f4640c03400c071000f00001c0c01c0080400100d00c400402207904e10040b036080c02c1100c0c8600b20550241d039910420060b400c1c943c070010070841d03001070254001380c04c12151381041d02c542042200c000c1d40ca0300c01440340c200034a100300e0800c00c0004c0c5564000e5a00480040340103040100941d251429549030140c0414a41c0d000704004120b0f40744400100c0001d0000d0030300c1010740d80341510260450a442d0042d414065940c00c00c010303080400e10102c5002010706050b1020b614003824400001500440141d400c070b464000055640d9000c0d20071203007919006250048c00c2e01d881d07820000d1000d0024400c0758003a11134000d901c00078104010040c041d40d59048587c02c01d00d00314000400c600003641d1031510500080e01c0c401c40b5184d012840c2c0ba0044090 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 577163273 1250 577162023 577162049
    0xa150815042c0f1b0916020706120e12090f04060311010309021306290a050f0f070b040303020415050301050906040b180a05010320031b03340816 64
    0x91800c2d00d04091508001000f54010b01d6116022010305144901400390201c40c0e00e40b103a2120400030300042c5640740240c001d80e01a50381484141e010300030368100700409031404140d02c403060403118101010405004040200403850f00c0345490407450700300300b111080d41d08010785407445d242d80100d0a14803001e9814180d80b0b10610b03055448400360559440703440c01e000d00c54150384581c00c00540c183d0610f0003214038041c0c803004400368495022141348648580d1090304024945043c242c841e401003611005000e01000850000750996842c14490340c0651030050702e9503d8095910101c1c0b406082407420045c1c20001806075581d1060300b280c01030001c1d600010420b4030032006c24034000310409500e403080300480402030282d040380c01c024162403190f880342801c11030740c4805980b081030140b00c10381d0540002112180c002c0c4000105000036100034103c0f440000b040f00800e040c041408281c0380720304030207950b00c40449091a01c80000306164402840f800546a20050b1464964042c0c0d264000c42 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 577164523 1250 577163273 577163351
    0x90702010b1e0a0e0408040510020601030c060f0504090f05011a0406120906022512030504020607030c110a12060501080c1e010306180e0d020f0d0e0a15081504 70
    0x2035009001c090040c04c5440403503801c041c1400c0c0391603006442034134840d010220000751030501c041843c0d8100d9601c40b202010050910b44190360b03451105403c03e0030080c09010000d40401c050060b074041207500500000c1a50401e54400a6400071190780c10340400200800c014030b070f0748001e040c44584c42040c000515a02c45141c1070b00a80700d03511000c0c0d2600f4140048451044d140c07c1f54101032480b50040c8003d00c90003507025025a039044402030750001c1c0501105001c81d01a8088026881c8101c8090000c00d05001c0040c4103580550840d0280c01040d03801c0204019540c401c09000d0b0055000904101d900c0c400043c030786601c0c9298000110040369500300d00751740070b900424003500c1c4030b4114941408040e11100e00602400c41c0030f020520451850300c140e00c2c00400c10b0480ca56a0700050700b83e0303040074002980c1c00c2a019170100e801107450b103000070342000c8031811394900c034800b65100019402d10326207070303d810850354010b144240e1030900ca1b5a6100f4804400d6514089120800710342446 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 577165773 1250 577164523 577164529
    0x40501050c1c08180d0903020d0614010b071b0e06010f14030a0f0c1716090302060a02010c02060f060618011701080f1002030603030301120c03050f0606090702010b1e 73
    0x481c0854800500e05422005038609030420a4030344540104c0300e000030f004070310000c02582c4000714210035000c100485002c2c00035007080b01440030058000c0a002c035110002c3e540c6054050026404025492008562102040707070104410a141600300c0304c0c0050942005004490b43c000a0070903414052030741e4500d01c44031300460013540f001605250a5440e80b43c4010554064140ca14407000b4272450095090b100130f00552540b69204100d1809100c25641e003045164100c209a00c2c46040c00b103c40c0000006039100c1c0300425204289900206400d0003121000e031034081c0142044882144810030042d80307403111420351b0030500700c003844043d0160030400141c56a4008005d840452000d0f00700100e05640002004c0c5d2400d81c40e8400c640001c0202031001c4202d006c1642e0084d0705800c100010803001205260144045004c1c51a00c4811540c0355119440c2031000300d641c4805e904208200a101d00d00940c0e1180e020043d80001d00c10349140c2c400107580c1040d0546209215101b02c0c2d60040151 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 577167023 1250 577165773 577165783
    0xb090c0c0f0304061206060305240312040914090714041a0d0615050a0308040b030406020f0a021501050d08120c040f0b040806060114030c030c0d060611070515040501050c 75
    0x55801d406480d40c8a464003801400041e140e04002132240c01c01a0025020f4802d20070035100e0006060b80031101e802c40107018004ca280204910b0341445503614407100030b8030003c001c00084c0240c050010b65407040c00e4002910180007800351403950040c0d0420003502c08192030034802c6120031640001c00450200010401c116242c0b0702a81054103a10818200007043c1c3c46155200800004030500664507410059200070341d010041ca400d82c04c0c48100300408409001d550018411040503081124003030014001c1c0c0c0291640b68010380c404010089822030555034540504130903981034074914142d490340340700792245c84000d501840d03001000411410311107098034058260710007205103459845041ca68070390068000c566580c029140030034a47d40c000c51150030003460501007030781159a0101c0c090f119400c018800b0109610410400c00411500d1095038007600464881c04202603c5160040c90101c158000f14054020b0500c0300c249a8403c00917242183d10900e401542c1e0351032070500b0b5040c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 577168273 1250 577167023 577167043
    0x3030603070e0c161112030f0703050705030f0304080d0501050603151c0c0b04030302060c090a03140109150905061315480201140408070f050610060f030b090c0c 71
    0x181c0e6051444c82c20041086030f80c0348a5a022a940c8035084006a030580d164030a211008100034020400400041e01980203001d40c1e5002d80c05590804c00040070040099100321030490b1a6600060b00c0051010107116045c090a03003550042c2c103600e4140c40380042e0305604001e40b48201d06000e112200200304400036250564044101c1d92400c0e0b0f500b0010800b03070000e01040b00075008140000710b10442280507143c0c028401009920101d20f1600c0315408442c003c5e44143c015500d6164080c0031849240f50b40710700220244000408030298223007035040141c05411a801c0901c4c94002401103940e0680400c030010302c1000000c0c0035a2200f604036059414101002002940c0745465a542c806040750964030b010302541030020340f0780710f500c01c0f8201c910495540c400302144001140c0450007030409001c0f541d108800c80b201c0481039449103458400100c0b85059070740c40240051102c5544950301d11005442e80c01c00380103682103c7c00095161000904081d44460b010074945510441044401343d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 577169523 1250 577168273 577168297
    0x1002071202040930111609050711010e0d0e01022a0102010b03190209061801030b0c0706020c1006090608030301170a0f03081f03350d1d03030603070e0c 67
    0x41c95120200c0441c040841c4000c2c0004501115280703015281c0c0401c54410080300035010001c56820140c0c0c4000903c8041c1100e2708005a07040c0481c0f081c40709100b12100003140c803009000d8040324000080a40c00354a08250441d040480c01d20804c03100e00820011515210165071035461740680100e0040040320280390b0301d0300c00d4546280c6c401000700c00483e42c0c0c60007502e8940c0d0300d0b0780748410b000b5088005030f200207543c521b0600400c042a00d540300c40d0381028000300c09603d40003260320b81c20300f40e81000070880025049a000c000f01008640705150082004000c1801807501e0210b138140c890005106d9030100759120b40c08428010800d0280c03620640d840a1114a8031805040c01400000c04450541c2e8500001d05082c881100c50f10003401140d9001006500038040c089021800301030742190080d070005242c01344c581256020b800b0b4120448280e00004400e82c2441d0140800201084514120b400401c240401e80d1000305030001500d940c0110001280c9172400d0f1844141f145041e070380c40d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 577170773 1250 577169523 577169573
    0x1209020102121201050f040504170705070b071202160b1c150b03040c120209062e021f1a09181b091f060f0203070510060510020712020409 61
    0x20211401c0b0105040c0c545c142e0710611012040010300048841c142c501400049203c1e051007a140b4010000304a802d20032001ea0300400d03656007038255560001c0070100c500390303410b0390502c6409504000c2824100751003540c0400c1300d86424010182d80c0300722408070070ac0108144c000343c8050380d02c1d004500c1240030a0001050207030740d02e0400030b20b0b400550b030481d10f600c4030103800580c5000d0303070202000982e0014032188072616420b04101341c00c000402c040c0c10009201e480da9030404c031040c1100042082030b8000d420a060003810b51100f8080d064021200c561078601e104840078040d4040e0381e40c40d0406d49032002c458455070702c0c0700ca46000d02c0c00317000150f115050300320352264008076011900c43c205441c00346840e03d9103140118000042030385500e09806151042050318400c001e01e0000320001e00540b0714003803ca80310142043d41004500c1c02c5251114820441401c1c1101501b03100c1d0f10ba8405005100d0420f42000016111000003900c034588840c6094180650081d014030400b5020b40d0000b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 577172023 1250 577170773 577170787
    0x4080601080a03111506040f0b091815090d14040b0c0c010801091a060a03141305060906040b06042307020c012307140309100c02040c030c120902010212 67
    0x107569010a000803000220700e4840c2910301080003540f84200603174603103840204e90b1044244401850424070606940d0703114081040c45403034155116000b0762103580c21030b80c00e8524410312890149000f001c0d4488001d0802044035095003c54802d02c802c0082c81d02e076000039030300300000c00c0c03c1c05245c2244000d50700004842410320400a50100540300a80790000f02c0e0780c0c4ca855030b0003100c822894030f88200d03110082e822480d10700704005003003108241c100010381c9032050155030ba00440441e01d2400b01d10f850078070b640502c007080200c6941701381c880c0d000704082d18003981e850f921000050102e83c01603482d6409028107505034000100c540200780da02ca2150710349150b00940d104481100180030880492446100300c084042b564800281e00f0051031070601c1e10780d1100d40e81c00400c81611500c1c041844116a00c0da1080c00c0911003032003590707860004102c140100001c541e074007000744007450f190001078000c290b0070140032048a084a60001008105400186e007042c1c680708240c3c101140c0084d0786 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 577173273 1250 577172023 577172039
    0x2a0109051309050d080739060509120c100e0709380a03020d060207050f031c060302010c08070c0b0a03020406030f11040b030411093c13030504080601 66
    0x1005003039005800f00c8130003c0c50300c80c003500c40140c00d690340d82c001a01c5040900c86201c3c8103e401200366030842c801803c030b18074442c440c29503d1030b00001702d918540700c105200a08008203c1c60300e5114200203a5860180c0d41c4070b03903594890100800d000d1168880181d0464044107000072801000361780020f10509101402401e103550681e042001c41200c41303074980200050642ea20300341c010300505103502c402d00303640030040849002c080032640c2d19020811200051001e0080b60051101d002c0190348951450904800004008039502000341c50a041000580c0e4802c00540750142c00ca030466903501c02c41d00b001c0d40c518142c2e402841d142e90740050480e5800e603044d070050040f1140d640c5c081000256030740e11003084e15100910700c00d40b03100c148028024091040011070b00304d0300c142780407030580030404003240f078000f011640002441e4058450a0302007030aa4a144100c500d8030010641c6841840c02140585402406140341030bc03680890b0030070907000b8021a80501034000444109681d00e1180c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 577174523 1250 577173273 577173281
    0xb0715020f391e07030804090504030207170606010c0203010207021008060312070c060807021608060124020706030f0e0604050c04200405010e010507020616050c032a01090513 77
    0x2c08200701e6810242a0004150404216074034901e0b48058000040c18503194418040b0111988115001d900390000016180100820040040032400704042ca824280681400c000354071046c84c01d0b01c101507001d0b0085003c40c00380d038010800d007061314640c449070010a00a0060710303002500034040d8494044801e82110107603226201c110225002105846900002400f0308076000305007210b211000d00025005070052640219944119480d540c0040c801790801e11040e4840d50311508140b00502a00e0201e20440100c013815201410340c0051849000f5594819441034000305580d51206d2921101a600218a111464412140a41010b080503a103a01001c090107100714138001c181e5000030321108840c1c01d181801080142082e1900f4019070b11201c0d0491568104501000080010780e10785014100f90303c01c86010854080c410301e481440c00c030360444010312903840080f0302401400d800c10310402404100044104054902006035441503c2c1c1d000349a02c00b2a10710302e20020703452640 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 577175773 1250 577174523 577174567
    0x90605060301200d1107021f020c01050f0a083309090705091501091805060a0e0903090d02040f05010824010f271b180b0715020f 57
    0x80000c008040a0581510380d0350f10a075804050601100da500e030140c0c3e12441d8004520f0042a15040345c5600042c149a0340016065251100006850710107604000c419503090080c00c1482c40c0c403003040219003d5002d07003003000e001c016400000440071200f032000c00d80300c18000030144d815201d2000116080340201c00005010380440350014203524400180c410031520047c10058440c0c0f2403200b008008031501c00c403503040c000b52650000f0b0100422402d0741c00312020f5200015203080210801c50529040d5111240b0840245c00b1310041070004011920710700e40440345403079010658408100501020854681014a004000190058007080c40c0d141198480900042101005404103110100303015480d18802c10b03280a02c500e4030715000131031000308624031a4200b200302070314010980300c45102e4107c409810141c4100c0c019002207141c000d0b0721414400524503803c0480c86181e40c000d50f1400f404040b042d0560380701d0307412194100d41404001e010069038901141d0039032004002114 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 577177023 1250 577175773 577175779
    0xa200a02060a02073f0905010f031103060f0a1a040f0b07050717010f0510170601120f170d090b060f0d060b0a050306010f09240303180909060506 64
    0x40c0000d0002c00041c402c680340c60741d21440c0da2010010001500d45000f40c01460100402c0b1150707075052100b213000e2241400c0c4401035444464950610000520403103192044c0800c0c0360410703150036420740483d41038a607c000262120401310a6920004460010036400184e0079201b190b403100b0f2413003035a0024030940d009103000d07108003680d03038103070140611980d00003a15a401c94401400001c40c40210100a04a00000490300203d141a6401120015940d03079000d031032044010071402030071151a180c5d41a02d00060103641d8034004c010280ca036440f44c0004c0084110602d030b241005280341d6100840c4003a52103180c0c80e20004500d5100801e0249000e91b03940e41240002061481c11840e118844000a0300c0e040410b2115a81c810191040300046a44148400f1001c0b806231020044c0900900240204a155600d040070780b80c11074042082d0b0141c8032544900f04960581031913011401c407640352619650300035290054010104031500b003284c10505004c8070b403003408103e420450242c0303011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 577178273 1250 577177023 577177033
    0xd110d06140114030708060f13060203070e04232a0301080c1309031706030f01140a0c09080d11100c0f0801060207050f0906032e200706050a200a02 65
    0x610400d983e17105d40d48a01c0e142a0f21580000c3e41302c0728804ca4450300020345040790700f4520000e942d61802d903002114a0302c001a104582d40b06146803a002d40f00244054880d41c00710ba400800941e04441c40081030f01c0551042c090300411045a04659450143c090024440c0c403540c41da60415142c2c1030001045200e240d40940c03034004601c03184103805a00354580c88819010480400e100d0403600010000c0d81c0c54042d412082910031403e00a003000c000c3c1c55001400780d480c00c50803807012908481644d9042000b915414494004c000645d101c0407121401c2c41c03060504100301c02c1e440c0c019041a4824010700f02200040d03085d8011001c2001c06c80380da00d031551260380300c88040381d840302c2e98810b9540c08058043c1c1500c1c0c0e0700308510043d400c00e01c041d05803003224183c40007007030044201d42c5140f020504c0b80e04040414410902c01e42203000d0f01d00b5000c0582000d07071220400c55008a0b034001e06050358407400724070b542c865548141108041c800c0c801007c204c0322504924a41c0141002c00094081c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 577179523 1250 577178273 577178309
    0x4051611011406010c020a030236010605091c060c0915020616050f040f032108010605090103052707090c0201110a030e070b0d020d0605010804020d110d061401 70
    0x81030089151030b1401e0200b202d4030380d03a80e0004651003125440107a80107540b01101001580f9001482424124407034101000810070700407200c04080d4054818031030103410360041c80344a40c080c04555141c1411682d101c40700e4001c2ea48040440c00144000b4440d61a188044101c1d0360041c54070000c82e10500010309092090940076610346508481c0769024a0307506400c194468000c0c0c0c003603d0386038a442c003500e0070030351101c48071529940b0942083e1114001480d0489445016024800d0b40d142c5500c0c24190039450044013420500400a200f070506441c1c20004a2058541d0858515810f1000000f60060060140140c840810380203046800342805840c8060300d0050040c01400840201c1030f51920041d04001c8006141c02d0385030007864000d01000080c03800d00b22002c1c0154898000005969003000801142101c0b100d41c03045040c82111010003015998520f181c41034581c20100e203401c064822800513000b0070780d035003004012601d08003654a24141e02503c00307040e20401070090250000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 577180773 1250 577179523 577179557
    0x10f05090c16080a020f1218120c0103110c0a1406060d02030a330b0103050112240f020a050415020f0703030f091508060a140f010302090f040516 64
    0x108800d1202000da582012240014080d10000e081d9824584180c4200806006159041494a191030302c0804804941c1c5034841914580138000742c603084644242702101c1600054482c41e1107500f55060603039a00d02003945100071b100312101c050040040c4d40b982003052620030116980c1d042410150322542000800f0f60528069034035806030003d0082c4400811641c40f40b1340030001c1500c0d000181c9541149100761070900c2140c0228a5860b038001ca6007640d031800041c11213505900030001502001c42410208140ca02c5c2e11503d441700008d03410766020b01d00e114801800450080c0c6820a1002424020441d88a80030700251242801d400e00d20b0954150101c0e82c6a070102074240042d0081c100406c0000d0254001c00303100364450800e4001c45613280c10f51a54070110300b48032004140d14804110840c0744c00015030014000c40030581492005200c08680144000b40485042c150b0004d16080c0c075603aa05241007101c00c00600502c130a1800c000031800c050f025500c141c01040d40040c0b00300042c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 577182023 1250 577180773 577180777
    0x24120b090f10050a0b09120c04050708010e221119140f03010615050d0b0307090603050105070f050a0c031803080405130c0f0c020111060702070614120c0a17010f05090c 74
    0x500701d00c0311741b400e111404040240e00c41c48a008042ca07032084c4070110f03c0e162113500420b44581116110098990302d00b030051028101300601806d101c0751411078900c204402140942202600000d0303c0c2c080459960102d900340854600c00d28000c400c1c5e8a00080703250319096886103207201540d80c10301450a40e4145420780f9900e0150141410401f884c3c400c0e20fa2146d40a0300c2a0243c5c0000810000341d00c101190030460b6940100d42d01d51f8942000740f003440801d0117219000521072506120161030781c4001049806107640340700c1000440000d40341410b00c03460326040880725000a0b8410190703207241074400b0368002c1c8102400b810300d0191009a225841c4108410544161100c50780d601440c1c00440d10260841402c034144031030312000e010040300c1006454414007030741e001041207a05001003d03014861103004d0341c1039138104000022001541900c15604541070039440e0352180d000450940c0c1c00000d202a02c10200246000000c0c1044040a0001210030540c0c0460740303a1500e031100c420034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 577183273 1250 577182023 577182029
    0x609050a0c05040e0a0905120a020c010f0206040506010e100b0d14130c050f06160606170703081911030a09060306050108012610020c07030c24120b090f10050a 70
    0x104c4046800640e0b038041036006115140c0c414000d80b5014903880c4048030594004600c01c03070050b4011021207580307507003000041c020944140000c1900e8a020399640740d540c40c050080d90140212040800c0407590524061009040002d0305c42c0e884105041c070080c010000f106041c03c0008a81d40450f0f03442c9114855052800d8221508050141c03d250521074403d0000400f2908003a041281d000510107185031103a01a1040c0004280c5920f41102c9180742d64946885c500317190080d280402c0000c500c1070031281000516140843d8840250740292000c8920626002da980000105c2d0000c0e1075110480c07800741da2003520200062034449004441c00c103c240540e640000400300305d80d0b000031500140e4090321940c6c1c0100c940e0190722030048001e0b038016070b4403880c0b90b50080c2e505004024030b603641203018008400310003540890310850b40c03402e2078074000608240652000c0511205519030019a17261102520403800d0781050292003400c4807007103030b4001011400d07800101d01841c0000b040360403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 577184523 1250 577183273 577183289
    0x3080a060b04060207030f0213020d0b12010506011b02030f071e080a0c0302192114010c170c0d050415051006020304210f0605160906020616120609050a0c0504 70
    0x201c46c15581d0301040b40b80c86401c2647d0240d500340f003440b0648400d000a00c1c8190004202207645400138003441803c164060380c45003640d0400081007400c4c0d0740a511500228102030144600054500200c1d04222005807103020701e008036080814250100c0803c01000c0c207007440e200081d2550341c001c0035203030300348038400426406051008002500e023180c4448029107281c3c050018003a582e10901607005c1c0100c0d010b83d016404140880d0900482c03200028808d60b002c00227000d00400280000e122032011510310150b902060089008a42800281c80524402c004200882c0c18036041900517000d0f0248112012820400060404080b440240044a94580003582030509010360310340c40500d4a41103050714041e5440b8800072900c0c034007105640714051100046d890070010030704925000f0010010044c04840c0c6410400c1aa0020302d45922400848002e10020500303a42122170f1642188488007250400402050415895020714040c2e00380080800c1358020600c020f83c0c0070b004620030002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 577185773 1250 577184523 577184533
    0x190b06040b0f0c0d02100c030b0d060519020a030501031713140310020d0b1009150806010e0303070b2a190c0c0609180612060b030c0d03080a060b040602 67
    0x54041c40d10040d0034080c841550300b5003008072a02c2031a02d00b071107031191040140c1c0500b0f00348250001500c50310500d007066240c2404058084004244545640700000700003030341c2c6000141d0120142c030a50b0b0341c40405070000303558560545800802a000a010a84900461412112000f01240100e6a414181d0020304906500d0800e000c00c0003200903503150307010301a100300040e0504540c4000c01c0b00241c0c110001401001010030310003190582c1d50b0000510400719414044032604080a0b0b0300700c41245041c4e0360075a80d00d0012100b030310300013494581610011501000700240c080c681c0c0c0c89405040c100105240843d24201005c0452082c104103e0008101c08082010842100d888803600d44c20140303100c413419910301d128005550700004c00199410014048003c07204030b070fa51820400001404400d050201c0e0802404601c84c0040c245981c2d0781d90601240c07420320084203154001400150740c42070b40d06001d400090210350800c140b51401a01180c14102c030b4042c2c4041c0c40d01c69000705 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 577187023 1250 577185773 577185779
    0x6040f030602181804030c0620180609010c060b041118100509011b0f05030307021b040209090c03040638030f0c060a0207030b01121a09031e0f070803190b0604 70
    0x144050700a020b0640d502520340c29484042270110750341c0824140d4034007101d0380d10205081500440159011140c1c80b4013020411009240c3c1e100c18400c02050b0070520005648558500180080600303080420250308045402288007002152420282070183d40f4a00c00403412003040742c2e14810350098501090a041042408e45020055010514804d80700d28403802c1280d1285c52450b003080f08c2600042c1d1107541c00c210a80e582201d0158440c3e0300340c030f041d4100081c0000040b07241000900100c101c9402000060078405140c02001c030301d150303100114900c03284402018985641d4001c0361040914115030380c41e20340c1000241c003103c0f0740b09040030f4001c2e202d4540810002d50300c030400f424114882d80381d01002150007444000d0081103804100d034040c3d000c52404800301c80890402d07042d07840e40e03032080007204107012040364082041d0b180040c080b807004902000c030038001c02c804d41000c80c1021079141c080100d80310040d0301036002c51149808416010070914140e07100d4200464002c48180820 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 577188273 1250 577187023 577187027
    0xc060310081f0c0905210f010216031407020307031401150e01050420030105061614060601120c091a0c070305030417030a02030405010c08120412030515060304020f06040f03060218180403 82
    0x180200012142540d60391100d07c5492426a0041e1001c10060344a0048500801d90061844116441c0da17807032035400c0621903000a5120065072201030720107402c0c024030020b0f01d0001e604c9036560354020200005016240c0b140c060300304509001d00390040d85414004408482000c907040c2090058055162842e824032060060356000a180399007050039940800d0000b0f850003400c0311840408400400062030900001001000d41c416408180c1d0300c0e01d064103103469400415a8203452004a031100d520400742c005070310901c0340c20001e02d030030300402c8408010080007000410484000d000e400040c207501d008025107a00c00d001405000d079100b00300403c22940290b00c010101c6010320034060a027954040030048168003107030300311800307590f003900d58803829014450180c100f00c0b00c5812850030303418500460441d101c06800680300f01c80081007107000c2d40c0c4030011100545401000300c20281c1c0d403403600b440070350041c0c0001c90100c10100004c040c07a0424a00e112a0011200f0406540e42c03030744d482c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 577189523 1250 577188273 577188319
    0x603070f3b01091205060a0c0c050a0609050f160f09020a0801150c060c0e010f05131e090608030c010c030b0d06020705012c010605120c060310081f0c0905 68
    0x480740c10300c6025000020943d004401c1c424026005a0203404545040110481214404180c14090226000c601c60210304005180509180d0280c030008813040319061183c50703c01010301030b032071030b1140d2a8084448102000ca0004440100c00f0091020791519500c0040e0301a0316100300c0000c03807000042040b5500c444814803148268104004800c0705920380009072000c2d00400c0300410720400c149440303541d101d030421001032000d151440c1040042e8159800d00c2c1c41900c42c0640181000b61038000c2580d4180819004200341d007400c1161a03540c85185d0780f2034029945a0700d4070751070044100300b0b65000e40035030581403100521401c21001541e0b2084002c0d0003100c8280c0d110f40d80c1d0003c0b041f510341c4055141c400c5070814008030042214414506003035036490b07000340d0b000e50341c80050000c4612002802c0101100c0480b140c0d41c6079a01c0001c2c8900084441d8040b2007a4880e00c0a44004506480d40382c82c80c0486949050050410110007990b0300545071140700e07003124280c0000030400c04800c0c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 577190773 1250 577189523 577189637
    0xe0d020907083c07031406060c0f03030a091b030503030a0207060f06060201020d06080f06221a040b01090c0e060d060f0f080c09072a020603070f 64
    0x6a06004055681d20f80203c0d0305651100c41200c00302c25100300b0300000481a56078400780a140520250258943c507412810b000790440e400356201040c51600c8003014080c40c4001c1000e041140e4491400d0214180035046e80503007524040d0481d815060705a5541d510882602d0300003000b03500e10b455a50080c5e000394090f83c4140ca030180e45d59840e400350201402000010b00f100e41c00980c4640201e10f20104803002c4e6801650154880d0032000c2c0c505a0104155522000710308120201103504803d03020022500032000b40501070003000c10000e00711180001d8050780c0507460386040c503a01c0b585540701715848503001c0c0c0c0200c0c0c030326034240c1c50038070303016004000000d0300d80408640c680e079070300303010283c1c040603040342201c00c0c0c0303a1005102284e4104039900210a040791800d420341000c0c0300107001030700d42c2140b00d10400b04104017446a5041c1580490b445a4003422140c0e0341d2500da030004040000c00700d1000c00182d5802146014400300c0110000c8500d50013000e11302032645401c00ea0b42c184440741d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 577192023 1250 577190773 577190791
    0x40b09160f0e0306040b0a060b16020603070e0607030305070807110604112404050f06040522060312050310150e04090c05151b0a0c030f05010603080a030204060e0d02090708 76
    0x902d02d0161034500344980e0340110310610000e8082c1c01d1801c000c3c001d1341c560b500042507210052003e0843c0b10340c122115444150196480ca50f40e40303900e903040b110384101202441e00140700048040070554558005441540307165103a0f822034581c680c048954011242036800070b41c1c4040049804691314200902d40010002c2983c0c4400c00e21b20904c1d0183c42c803080480a5110740800c0801c528181110201d80080044450915241c180400562134042d410b540c102c409039040b03000c40d12a40c05d5489030300515081030311144406914440102140d2003120303104085050443d0018000c0b95071444080e030803405481d5603070700740e00c010140001803403900340a0300d1078a080100060691215051203081d1503010b0602c555405c20301e0f210302a5a9110406602141d02a50900b804640c0e007400307010030342e50701c0009079880c64103905049000d170006170406421148006040d01000390980d000300111001a10360803441c0340014200065010441c50181d040140f0b9000119042d00c1005910f034404000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 577193273 1250 577192023 577192037
    0x120b010504051806091b06040605121302030a060c1205190b130c0504150203090a05120319080105030c03032a120d09140f1005090718050402040b09160f 67
    0x320070708511340b003000d032030f0300503150801c0802c44541d5140e031480d1041c1080a456142c0f4092800c0c3d0003c005100d125110b103590841900410b0381d01907041e00c40d07000143c009040b9250344845003031060051100800c0b002c041002140510509000d600410344604005030006070b18903141c86030200a0482c0c0c940581d40b101d0600441c0c0220f4a03140f0442030b01c00a20b640380f83d1103034100308001c0560110142404190352050114015540e160410001590030507208580091010301d001441c501403881a00582c0e6059260810041da0041c20a07040703030b10450880780c41c0002c5906140c0c492144d44e4603010040402850f9099604011001440120044084400303000034503a00309510f0700f00c1440145481c0d00c40d461502800060000c82c2258803000b409400c100c02240403907070f551070301d00010f026500d4550b000070711004020311800c03008040740e40340c0c0c2d09075010822406004080c01c1310224405d42c5041c0301ea00c0303d0f05108480318030607009521303000100d4989600c00e6274410b4440030303607000304a24 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 577194523 1250 577193273 577193311
    0x8071d130902011404141c05011b180602100509150108030310091a10110708070510030b0a0e0a1b0c0204052a03060406030606080610120b01050405 65
    0xc5010501003003100610001d800d94451000400d9449180314a420032803041c8424800d0341d01c00300c10f45004075412118203804561626002d0705c4035101487c050101d5107032415036140503d0329030a01010100d00d40d40d442d03020340c00140b00f00600746203019100c010b9011590160700c1400359480542c004102c5170458224684010000b06521f901f40c100e24010b410100c14441c030000044a1000541040482400090441c0d81c1886d042c40001040704c0c460700ca15101020b21364003490041004469000070703510119142c5101540e21030746480344a0041608442002d207884c860f21803079001c2d02005184c0291285031060a0716a41c201510310a07030700f43e450007991400310503800b0312421400f042e20794000300b210071300400c002c4038002000305420500340600f0400500d0881d00809801142d5030a06071291a8540464028526030b0001408680307040b1010911050014001c0c2c411003158000d410159100d4194a40000070518020702d1742081d00c006200a2074203403c11540000203440e000c41c003202c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 577195773 1250 577194523 577194529
    0x30d050c0408030a2c01080c0306010909050117160501020c0d0c05040f0902030c030c0f010c1a0702010212160e1507020a150306080105040c150225060e010c0308071d 73
    0x1101c40451404900000e00400000105c8003462419201e00800d1110101d881e000281003c5001426000c65020000004400c2e0b03018010311400b511075540c00304a44d41c0c40b0a11016580510038103103180d4421256000040d80d14140c04509950040c1d001d070a1500e0103009001c90300303100c2801128049080301e80480e40703032518405e201041c0307000000461100d4542c01498107000f0030800480c0290040000030f806038030b07040303420001e9820a21b0702c8042c9440b04d007032030f60000c40c0c1515203592004030074060080381c3e54150042d04950a07252185909900c0701c022815460f41140800c901041c102448100e003441c2004a843c10021042500b91031303d44194000340e031521191300141031004100080c0889a54107128020207070202d98000c124508040c0c683c0b440c0424917109200e40b0405504011314000d109100c008590000030720030142d040c03842c510030040108580504400a400b983e5505980d6105440c2900c605070551100c010390340302c502c411038100c5868080d8074160400c125038281e641c0c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 577197023 1250 577195773 577195777
    0x11523150307020109060b0d11060d0e0307050c0f0306070c150605041b080a0c0905131b030203220305031b09270a020c0706230403050a021809030d050c040803 70
    0x101079030f400000c40e04042d00c6e04004407440055240d00400c000328440000680d2102c3c14aa9248201c8400b43c0f9440c201301464041c02500010080034003003c121a4200600098811100d0800b1141118103c00541c01e0559880701250b20f040014105602900400d12850a06020302412100841c80c41c4c2ca90000c0340607101456900c5400c0038119216802c1c15a02044550b0491940326050162009010340100202c4290007000e03c108504090450081840d5000c85000381c00f0101905484d800c0300ba010f4029001100c41d801ca2042c1482082c0d0600f8004050031415036054662038203548640341082c1040e284804000d810040402c0b0491166031010311891203500c0d0b181044003003030002c02004c0480100a084212441d0051280034066840800d9170010303030300c00f80b4095925052201440300c4190744010555014100014040180000412130540b05030080d95600d0040c40300b41c0c10508811822140300741d09800a100042c040101c0340c000300c0d003144140c9030490030907482d054094296 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 577198273 1250 577197023 577197031
    0x27050c090c0c010e0c060706183003020a0818070305070b0c2a01050a02070e1003061410140604031203020406020610080601060804060e0a050606030115231503 70
    0x1000700452200c180d65024064140c000450002030220360b581c4001040d06806840300050801c0c4e21600a606411004220700d6038142c3c100d20101140c01c0626803485030140d49803035010104030914540c05810b400390086902038110785d940c1c2c11180d51103400340c004030311f0300304650149030060742e20000210b1000c110103809025911682c0f0f40c1d4000300b010261500c440003550050300c080c031a081001030700301c40418030180c2d0740c2806d02d25a1560411403c07070902c28560003606800d0120310522404804840d58001501e1184504128220b0240010792003150100c403c01e0000c0f50050092250014200b00c00b00718a401808050030300c4e0b266501c2c5041514203030f081c1d00001c0e5022404010807a4104000c0f500100300d00340034000c00341001172140e00c0303480502404043c0b00d04200403d08001040d480020400c00100503214a0b0b456481d2079616801c061700c2c01880b0f50300f8502c8181803a15105040000c542c07034000c030850b0070b0050034181d03010f46d01380004080c0d0000c0090210344000700550011446 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 577199523 1250 577198273 577198291
    0x120c0c0604060f0c02011103010927030e0414060a1a07200306010509090a080f0d0c0e01021209030712080c030c0706090b0406080f0a060f0906050901080127050c09 72
    0x4200c01480d400001c64289241c13101c21a810644c0a50b0420054402c4070f043d600a16030120b04ca9441220080b0401c211071100604248074401c88000c0c5a4800c80c0b654500c80c04581c14440b41942d6481c2401d500c00a135282580b2076950101084000701752140007070088419110f103420005291285a0000816140d009034000c444030700d800d0303628041c0300c0706000d404c0c22a22420241000d03a1580d5603100403440047c12010005154814145080c0540f442c03203132500410302500c3c54030000203109008000840d40507218400c3c3c0f41070f1a20030402950070010000c0e00500030b480c90b1003030040c030715060310350300356100e41081220140c003000c103200a00009910000070616640341036001400d04106603c00705ea00c0005100c180440b942c030044107030300030305a0740b11072100d074486a5440000305902e9100070302e40e2024410024100f0040e030007400c12140c0455452205a9880c1c1a1900341e46150202030501c0040c2e0b41c0a5140012800600a0003409242100c01d0700c005240803406001d02581d00441c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 577200773 1250 577199523 577199531
    0x70e12010614030609063321010606053c071b051005191808011508010606020a03140c12040e090c011b031e090303020d050301050303120c0c060406 65
    0x1581d0404028694210820031700508461801854400081070f40b0341ca0b003000b05030742e060020101104815131a25403030000302411040150034114001c500d00405800703100d5400c044000455a0064040d288800c0d600d41c0d040666900140c0c0c04031156640c003161190034095401103c1c101070b15103001d40380c10344c0724030200042641c081030301202543d0681d015a100b40c0c00443c1c0c0ca01d109922078146d52b02c540c40031038404504003001d05c1c25114040d240103a8503c46a084100003444001504115400501550b02c0c601050300c403031049090f61034a00501000d0b85c4480c0c0c2c5c1c040028420100300c00f21a03c1c501ea40d40c14042109a240c3c14221100c2c0086c01c005000304003030040410314a0303c9034021968800812400d20b5140010b01428a4806c1c1c000d02d606450b406801030500500385182d100c2d002407400c3ea400b00b40644050f1890b01d4900043d0010b00c07c80b0307101e14a09024000b264103a8400030000c0d41894182110f1081c034410003080c042064005206540c1c070b41e4410890680110300c81d0304080b03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 577202023 1250 577200773 577200809
    0x7061d07081203070e0906030a0b0a05161b0b090a080c0604020418200102010905010204170d020601030c050f04021b060103110f010e0603070306050306101503060509070e120106 78
    0x1071801c0d444590350900c40e41d00f001801403054015000c90300e02c102c191600c4c0c400e41e55560000b41014070140d0040d0010b40d0800800940b80e225510584c0b00350983c600400d4142d41050b011510103a886141086403d1401c1601010403c03030780c031456010000e50308595104215a8828500e0f400c00e407810001c592041060001311f107014040c01c4010314107002d240300100d801d621680f030400648005d219055100140490650340700b074100600325500b101c020342d502c80e55405444030404940ca2251480d00402000380d103058030108410341243c0e04a0786814a09040c1010800c20500100342954000c1d400c1101500c1d106242c40b82028500c1900050100fa43c0345040410002206025151080600d0201d03807483c0d03031b044400d84500304003c1c3c81c155125540e03558144c0c02070007243c02c9954148140ca080001c0074032000c2c0190309544d521107040038040c82004058050310b00e50700400360701c01c40c0c82e0000b88401d441051181e4070103000504c035401d4a6402801c141c03c403051078005c000031100e000410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 577203273 1250 577202023 577202039
    0x60409110d03030e060604020f180604120c0513050702060f1003150b01030b010519030506060f070f060e010c090510140324060702090414150a090506100e060607061d07 74
    0x40d5002c58280c90a51500d03140301c402003058402d9044002b64044020082803041d156842581e019240c1c05800711010702647c140544000d8051040310710030858070301c0d9030303c1c600140c1c0103030b9020304440c1e0014204ca4030340b10502404004014290307241e81c408520000701044c2003007011000c6c42003002d00080d100324000001802c2d103000d4601c40303045c040c0400c0f5551810742d4007082c008418400d4500040c3c2da0301c45a00280b114450351418603582c1c480070a19000f07102440035000f0a0b14840da00801426074103103181420303955100b440c40c000c184481c0c82080b072400c214a5034003c2800034900040c41448034a0514100d03003003076503821107003183c3c035a200304660605c4c910b507550b07076030111059400c00000c0d80c00100c881100400080040a00c0018083d8514017040302801560300c4c43e03e502c03030381e2501d015407400501034104282e4440c46024085a11507103018608401e441070960702500d682d603080d040c456698060882160115900c0001505080b6954800040c0d2800c5070050314250f4508082 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 577204523 1250 577203273 577203283
    0x3050106020d020715050c1c0f020d030b1302031509010303030c1202130911040b03040f20130c0e0d0b0601110d0503061c050102031003170a0206060409110d03030e 72
    0x511015544500301c2409460001c0060b00345040192826580d01e480c1088860304100f144000003082ea2230f0300604560203034114019a120812580c01c4030148851001c08509942c001d003030807508003071450301408000c2250307001168011001e919600480a400e0b02103400d651b4242c0c020b03400680d031941003070000380d440740d500045011003a50a40c28034103800000384182c00c06119001201c1d9642a00c0c01c102024002078400811360b42c045240c4034640340c20064018042c00c40b04a4000d1144440808020203080202030072120142114003201403413502c4900410764000c0d100d00b44804000940c0c0b4035078800c0c40c030340c401c4c038031a0741d00948909140001524074010040c404070250404842c1500981d80a0144d0340c0c400c0049903494540340a843c036100d06422400b8000c1c00c1075000204000d61000602c8103881268422060b184c8201e0218030701121a00808030581c0060304040c010580524103a0010802c881c0540d2030f5900350008a000111460901d403807c40c08251203440d20302400340701f480 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 577205773 1250 577204523 577204543
    0x90e030a120e0c120f0c01140901181a07060b03030a1409130204140307050103020a0512220b0919020904020108041a1e010906030f02060304050316030305010602 71
    0x2103040215100c0081c048080c501c150310021981c400765076150090400c5610030341d42e0054400d036403410031003652645400c81210409510310403112001c2d1b0300e510442e4040748510050484038140b0107044011500c004030100d4901c68001010400709071071820586102400ca400190030b5540d024a1900d41309660074105014841e4005108600d45286c10065014014038040002551518588005140310000280b000100c40c4082000b2400c42c0e040a0340c1d00e00300340224200e030900ca945900440992040480e440c00152003440501c540d10310080d001074010380004006408410840394500ca280c00d0084191848441d0b0420300100d5070092201003481588448113684c544030030b401040c61141c01900007810000c8500000e414040f00303500b6101040301040d00900c95040003040c00c2c0d03140445d1740320540112852000000e00c00c403a840381d038045130760010743c1d4440320046408003e01504014002d481c517000030004030f00c400c0d03400c4c68541c003400d00c251000689941440d60003450088201 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 577207023 1250 577205773 577205801
    0x705130f0e0f0f10110328050a060e091f0f020c0d05070212030328090c080d030e03092404080304090f050106020a032001060e0c1e031003031209021909 67
    0x14403041204056581240d51104810b40c4040c0c81003074036403034011f22510000c0d01204d01890041801310f101c0e02c0f500500116800d900ea03203d001e0300e50380c02c69900c5401202c85803d155002080e0240254130740d4211405001c04100014105100f10100071300f000000e9800b00c001490006120b011407404222803841181124002d60442c608011801184003900d60310054030030b15841501d1110f4826001308140740e500000c1051403540e62408290359081c9020030001003800d02e1218140d1100000032b54002e40c50090215801e4030310b03440590300b6005a1203070108484030070080401c50303080810050000f40303014400000c480701c50340c3c0b0910495030103070022011500103c48040c0400d070b011042481d2514800c42048a0340704d1079581900501d655800f0301103484181d01000041003c1d54042c0140d15402500d2a50051b541c1f840c00407540b00032584480c065107100c0301800424428805a0f000f402d62850000b01007520f6000650001e81c05c0f2800029030344c80e10800c1c81444800d00403c980c0003040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 577208273 1250 577207023 577207031
    0x603070b07030c170d0c02070503011107020306010b1e0f0a0201060b0a0c0615090f051602060402030d0309050c0604080c0a05012a080403020d2001020705130f0e0f0f10 74
    0x1598020f00b00c80c100c01001e040da41c070200c1c901442903d24800c031503070580d01501c100440f000e1100042d448010603c5051311075480c0c0f0164041d40d80c4c5080841d0741140d80103014280507806d108201e5541d41001100e40e020104160078108051501b030011302c080840381040c42d07101d241c81c010007402c0d90126003108012500501007009804c1c9c0090f8201d0445503c660301041c60014032205111800c0d0340e610075511603003031a02080318041d081d40701e50300541ca01d0340c1858440422800030390f038424098070700a4055001d14084594180300b0780c0502c402c130788079005464111200301c00068540e0400d4200890741c0d00034059402c4240703087d03e6041c3c000d04003801c06484403003070130f4180d0110910304080c039418041c8041c82c060803c0b01c00310498000c2e59000b0034520840e591428a110f60007050810443d03448802c170303a0315081c0d40c0005a800120343c0e00422065001580e0820400a80058841072000c2511480702e03105404007030281d47c0c02000408010800caa201840041c5449680030f0401881460 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 577209523 1250 577208273 577208287
    0x2120f0c0a0f1b05010501180b030705010903080304030e0316180c05030105040b1f0305011d040b040201030f150e1009020f0f0a050f040311121f1a03070e0603070b 72
    0x10502810401d40c81c140310340b105034400c0e112071803c800080c000300359510340710002c030ba070190008841200905040041010300c3c030150505030395185038065940468283ea00c100005100107004507841807192a05542c12014000031174034000c485000510190800c030820301405100e520510813800308490180030360f4000071006019480103018250283e51100340711001515013090b04482003240c4480c02c0007094000b08020003c00083c00f50391820140c0315284c0104400035000d060045402000520544c0c03129801940200002404888120741321846035041130b05a643e08401410840030040b402d2400070350210598600340c2203005418810b101c040d0f06401c025099822096180ca0722580d607840022003603c0c2401449500d0780d44600024010080010010b154034007107000703448160440d079041105070380b642031040c17814a00c81e510b00c1c4205510201a040118001101820a080d0038100b20101c0d090403090303000288004842424030202d81801c1100e04001c00e00d80603075506144c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 577210773 1250 577209523 577209527
    0x9070e0901150201020708040807031b030c0e040f08070501090b0105040905030301090203040c081b040c1403041205041509051f0504030308070207050402070b1009050108070e091002120f0c0a 84
    0x300600030320b02c0b907000405005500c103000f541154081500b004800c0d40741c03595442e92a9541d0300e00e0200b100d200c21954400c80040201c00762078010780707910180068800781840460241c180000344240c68842c0311000c103002044883c0d006045481c000c00000ca0314002905092150b0704040c0d014038022494040644003091001c41644c0c155a040b08015940e52224100102c1c07091140d0041d036503500585c0c1c0c030400b080510042c4c00c8010320303040d601403010b03940181058581c900c1c481c03914405100d04000040014410b004810b50061040c14154140307926408040f1082001c0c1c0342120100301d0300c00d01480360f072405211a0300200040056100c0c3e90710f00c00e200404c00e004038071004050040074408034010070300900108010f0400079108640740da03800d007401640c451007500c4018224442920108980740c440c080d03941039415010041070308a240c6401200040c0d40140b0001d8103001d0340041c0c02c02c0320b00a000804050620311045c10590401c0814040003040c090404c42c08041d080284660392070f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 577212023 1250 577210773 577210789
    0x305040c0f150c020f09010b0d0501060e011d18101a0a0c080d060b120403030e01060303091208040306050103050105181609091e03050301150203040503062a041409070e 74
    0xb030032843d008445441a00c08a0050200740f030525510040c0d4a0010403d1282e44000d00030380200064140b01c56661104142c3d41d400b010b2031741038002101402c0004042c140c0c1c1400c0140894058942c140c589070384805c10309040007d42d00240c000250000401c48444504c44c25141001054807007464006c2030a40a000008801c0b00140700322030201780d42c08580402e0f84024014181031030300b41d03503550540b415261200412101100420321b00b1704e2180d8040c405200346019258191141004281460f10720241c007044810115890349080001000044690041707500841c03140001054900300030302002c840003480c021581c1140e21440c44800b540c0c00e2002c2c03440407120f0740200002e040c8080d05103118400c0300c1c103103504110400b01c0c0400d4101580080298100e885400c0400d030000401d442c201d0f203e111704e04c0703841c0e415444540421b1240146104011a1303e031070b41c0d06140c1214000600308860340250b031201c0c0041c000c00d034001003541448a1802d900102c0c80c540718402070041000036101d2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 577213273 1250 577212023 577212059
    0xa022b080c0412110a14030a0201050c0c04110d05060d1104020d0204030602070311010b06131403190302030a14210903090a14030f03040f090509030d0c0305040c0f 72
    0x40803040200e0745a00641c811200030780340205622040d2010750034141c04003051310700900c1c024402d81400240c045050460b070340701040020083e14802e015900110b6083d0000c40d1600d0700d5018132682580543d0311071185014080b82013201700d85400c04910b180c811154001c00b081e0151900c89106030004804000303020380400c04850050700d5501c004a03020090003a0740008207000d100040000915801000011100d40d004000b40800c95000c000d002150007041d0000011030711518040c03000300e004c0d00304071128050107802c40c1c00d20114200f407050340e1405d692050f00503800000348100107682c00484140c5202401c0c203064603180ba0b81c941c1c140f55600300510110344040072000b083c2807080c240200e036a080001054004c0446c0c960440e80b60503443c1c880b0b16440b0f48a00843c82c01c000e0300110549045920000d80e2140742854001e036072000e02070044c901c0b500e501040204011082c900e00c03c0401500f0241e40000d1949001e141800004005070040b005281d5070150800c030300d0121003494101c4c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 577214523 1250 577213273 577213277
    0xf06060b090d0312020717090a0605160807020d05030f0307090e041a09011e0f1808071407030503040f15090b0d0f0618050702060703090b04021203070b0a020a022b 72
    0xf03110a00c0444c0c40090003444801003c40b01070005444c191040503014129000e0102c8010411030343d00c1d10141c0d10b900c56110780c2c0c51000c1046642802144200c4040c0c844240042e2111071080065920a030850703005a24220540c0d00c08001d00c500c03550721000d141c026280c00d1401c40054241754072009204084010a81d05c85410703000050b00424080d0440b02c5e030600101c1c01084d90a11032880d500140610035030314101c582c82c00c18040b0380c03544886c404000041d003000c00070746400403d4642400e0100030001e9a2030a2041c004c0000c0004c10400c0200010600000c00c482c21a00b451003442a4180c14545881080710460040c40300061403812202800909800020f2001044030f1510292660381d00080520001d05800703120521590400340c801c00040c1d003624895581c04400f1b13000c4940c5604064400f1019200040050522003000001841c1142c2101d080410f039540c1e880c038407038080f2000c3d40144d80110f03182818640411504d00110003080880740d412072100d0b16400143c0c501811101 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 577215773 1250 577214523 577214537
    0x4120e030307150f0f0b011713060504020a0305030d02121501090e130c140306012903060f100e010f02010908031b040312051c050405030913020c0a0f06060b090d03 72
    0x2802092030f5010713101c645000c000030b000100c45010308000404403458002e000c100c600c0c000c00c40900004003e03520905040000205a1000351107900040c08000c00480e040f50303503480040007240041001c0c2281800b40c01c005030350384801002169400001a0690451810480405c1c030113a812404c24410b5541088d0700344556690001c1c50518081d0492000d80001094200440c240040c0c10b480864807400358115402c1d030343d035142003035141a00d225041b40803140824503c0600300ca20801590070040c02002c070200428010001005c0401018502c40480c40c0040442c0140d40c0203d45003d002d54180000c00500c90b1076280d5070228400200040455907034001465141150700042c1c40285030020f5098045a00c0100c018202c2c0d0311642070403000d1100c0008210035842079010303440c0320382e500c03602850402190b02c061203d04412515034046e515000c1c00ba890400404100301328045000e400300300c4402c501404d102d400c545481c3c0120240340020030590760700d610350601c000041c980c03510300a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 577217023 1250 577215773 577215803
    0x30f06030c06070b0f16050f0a230a08070e03101e1d010b0a030f031805040c2114010b0f0d0f020703021006050307051210060306020304120e030307 65
    0x1a040007100c02105511080214a103420700c0a02e01e01940b0500e0030408030010790315205820503448490ba05000c00140c01044065418078124000e0110016542440728180040d0340e25009001410812140c9550010661f10901c540c0b0070501c50b00b1001d0380c00e00703a03504409200803e46803130030050048101a1141c55a03080910305003102012001d09010410141c040f0366040d002d10507248110160941c2000c0f043c41203458041c104000300c0b0340c010a407045603030303480e41d050b41c841d1010b00e6030811034550041d00182c1620340f8001d0316001c48d0030f942c4a1034030010b0706051000240302020707000310251800c00c46e1411200d4824166054980c480007030307034864a041848800f1446426900c1e00e007030f4100140310a070a011600940101c5100e40c00380c0d100704081404400849000d8824143e1560040c40c080202e8182001c0c01000c000540095502555030030846505441d41e41c0d00459503a980001008240719520589241c11441032400c03c103983c201000195072070241c86805003000400072142c0e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 577218273 1250 577217023 577217029
    0x308030c07030c05010e07030c0f1203030506030a060e07050a0b0f0a0516060f090b01090e0705090a090503030405060403030e03040806150f0909070608011a1c020c15040501060902030c030f06 84
    0xf109103d548480240015003101031200d0321480d640c030048401e50341104003c03881040901c81c40701900c40c84140a60740c0650b0380c608401900c1c000c0c103d5030701409580651400b16007103006081c3d40040c042c0040410510388070501000100035440301e41c1e4000140b22240e101150101110050b940902e400713038079070440682d200040016407070010091481c10064040180d0369801040c202802003440d240c00340e984101103c00d56600307240d01860b0782c01c007000c00e02103403900d000c900d80c02c400c408c03200081c2c004503643e076507107180d00541d003e07111640300d0002c0104040e0b06009100b82480910003a50034989007400309070b65500c01400d2101900e00c0b028050685486049145841c0305c001069251319040109280391540194001c0c100000c0c808800854100c0540107640c9440d404061854908a05000b072030200610000e21a2481502040700c000c000703000f004024016100200800407a06141c40c0c800d003102c1160384442074072030062080026036a502d40582e5880810443d05c1e0310f04c1e980324000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 577219523 1250 577218273 577218287
    0x4030510090c0b03040b040506010b072109080f15090115060507060b0402030f0f10050d030804260408070f0e0f18010c03152102060708090a1418010308030c0703 71
    0x203c5100410080708200c00d0190b601c500501941c02070f026215280d80350075403202c85105180002e0708903041003002c403203500104203004070100a185401c051894480f8440c9042c00c401c21b00d9074a0542c00440000a1008007101444d005100311000300900030144d2440d0003101d21622464040c0314001c901c8005000c0640c100e28410701008004669034a020803030148641030540d12800c41c5081c0c0c80c0003c03000ca071b59007605010340da0000c0460300107080c0e50b034044840000050040302c180f1065002d600f041d07540020304906002560310302e01e0f04c41c1c1c1406100751a0041903441428030403828402000410600e0a0540d00200a84040c081076951080f450303440c40c1944802043c990b207406a695009641580886401910b0620218400d580c41b01c2d2040b0010b803e4202840c5003d06a40c1500145414001412010322802d0214100855180050404031941c2e100060f4003903401d41096907880c261041c41200c11424149008550464480c43c602e400010a10300c50041c00150150a050198503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 577220773 1250 577219523 577219529
    0x60a151b0b0103030807031e020a0c061419061406032a030105271303020a05010903051c0c120c021f021206030f0606040c0e030a05060f09010204030510090c 69
    0x80c054103840c0311441c11241000c824071080d400511850040f42607a8420300510200d001055081500302e284108000c0c001d600103101d40017032058038220b82c80001c000c8d00400070141e001c00d0b0405210304e048051200c00200c01e420081d0b0044c03802c1c0061001c01600007030644c01e008182c40d581c0d01c036a118210100d0104042e00040c0c07446100c10103080008003107800850503124184e40069070f200d4001072905228102a00204800507000001240f0b103a8840c180040203000e403049403441c1380c858031031500b120480c2100394005003000400b400100300c41781806490149041081154500c1400010001d0310b07005031124100d5229090304140500c00c000c2031400c81003101d00361a03c400c403107903518000d50005540d080c0f00550540000c2c400e10b00800c85130342c4600e400015003e95503903882080001c15410f40a41c043c41683d81c1411400c0d1810400740d21801c4c450002452075081c801c80380c400b01003005059404c036a00401c401e10002e00c021400019904c100340c00850440d01c545441010344420760 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 577222023 1250 577220773 577220807
    0xc0702060310090b01050a02030313030516080702040c11250918020f010305060d060e01060906060804060b0307080a03140903060c1914040b130302120f1203060a15 72
    0x40240080340701ca1110301400c403000d030f060410000a0050043d16039001d000007070400f68105000055030741486081c2483e19501ca0301e00640340414680c0442095003806c081500c0311070b004585042142020311540e44000c0c03542c2403d005114401c01c280e43d0b01c072a00411161410740080004070b400c0260f200d02d13800f500340c040c1c0501c0032188000c8a07030881520b10030181e10581d16002d03829803550180c880d06001d00c0014200020f056031030b44036000074120109186410350b50b41c5400080c0c1508520031000580301540d5100d120303040c04d08240b4265014642070a00c01d0b040f210382042201400509a180c03240d06081503240500040529034150056009140d0107006050070408800318160040075009210f031100c1000c1492640b04440e1154000111003041c101000180f10103080074015048401040b440c90140d82e4407513000c00d403141c3e61000e20721a584c0c882141005550000e00080701c510007550350b12811071a00800040044005106544d54510700c0d2600e40e2450b0310400c50b6a044801c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 577223273 1250 577222023 577222027
    0xe0a02040311300a021f082a13032105180612090a0506010603060f0501030905010f0603150b010815090907081c090605130e060307090f0b0f10050d050c070206 70
    0x40701d510380d21210904c000700e21914000090704d180483d0941000c0c4c10090f2a07407010115a1002c03166400c007041d02e0540700c01c81c880f400904c00480c0711040180800c5840c40580140e0034990300e0008032401a0704540c031074580340384403110782c6581e106042d40d940c81d1003060a0f0103003111010115040c1c1c8211704540c0c940c901e000b401c02040c0c5074006009403145200340700310f40060b1b0341c60f2411400c0360f020740a5420004044001002070358880c1c4c1050805502800000540810003a030602c101c0f241940220b902e102c1c5407181c01954000c030b2141c48425402804c0494191510800c9841003111098000d0321510755000852100c1c10200058009015040212051280e00c80c8035808061034200041c5d0000e08400400300d0300d00e106400351058451503640d01d11065080480080c43c5104c0145050b0301071141110018951010380034200380c0b480700c500005091146003040c0304198080c020124000d5011400c4100040e034090300b02c4140844030500016542c95010440e0310700d22402101942c02800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 577224523 1250 577223273 577223359
    0xd110a05210c01081006140f03130203071707030f080903070b07020427060f0b0a03030512071b0f03030f0c050a021516081009150e0a02040311 63
    0x320031420109104207204a0b14403051400c011603401d0301c21901502d186201480400030750b400b800e82c13040d25000c00641c031070078059009261081a007040354452101d1081b4113414003582000d11042c0003801c10842800e44043c0c0011489a03140a5440700030042c940012079101403140e001c080d03455070300c4000d0030344980d01c0d5036030703119001c0f900001400c0e03102d80d02d454609410380300c00f10110a00e20340c451040421440c8030b074440100824034050103040541d202e80a0200aa4440c0c90100c06984a0303221035840303410140003001c40200080469040c809001c6215100ea522820740b0100c065205030202c8113142c02d441e08501400303c0661824071782e428411440300164002d0042c040b42c0307066030300300e5040c500b19150404c0f44000030341d60700310780d81050303001000500e20070b000d050f501c0fa9940b440300300d50940c4c564040d0104c40d10b200010001140d400070902c1101055900103804c006850000d504060558507122621620300d10214400e00044061310005200c642d0f00710071074003c561078202400c0c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 577225773 1250 577224523 577224559
    0x30a09050a08070c08010c1706040e070609170606060405061e070b0a1401180902030106180501150908030a03020922051b030c0414030f1209100c020d110a05 69
    0xa083d0844195551203008546200140301d081141185651003001188801c080c0809044c4040c0c0b01580180e02c412170842c1410003041410000d040ba07943e5048084d10b8051201501206046510203070b400480504c4030698035882902c00b51001100c105556a40181040c849461019161881c202020034800e0910408014251265203402c0f020301240201c18071107042800709001d20100c00c20407940704a10142d440e40a82e04152002e000010ad564542d004030300d07203001c0c02d64a010b58a40710341c01030280e15045224804c41070018245564551700300800203840303020340c000503820180e0216001403241c2d41d80400030756045445c84054400318404520401424044600c20008402604480403800030359003140e20820b100c4038110b040508001000d25500c8111f14030680c50303c5802c00354a006141032000c84d031030fa190080516034920001c1c2c103203c80c00c100b81a140c418070013503150a90250b15100c9a080250b030b0b00005c0e140d91100010b0005c0e45c08555a004240c10100710007420815132 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 577227023 1250 577225773 577225777
    0x705070f030c05040905120327030a1e0806012a051b030d0c02060c0124030209060d0b0a200a020303040b13051b010201020f0a021609061505030a09050a08 68
    0x40c1c06505000010380d142c07004d20055800030702c0020901d900c4000901e81d062094006103800012050410f5074200c4107400c1c240260090401c40281d941001910007403880d0001013100c012200c8402c58207185140751800b500c4400010b08650512000449446446044d01034070030f140c4100041e4a0601003403400c0060f0790394041da0b206007000c542003084100321316000030140071020b01559140d20180041d400d2003000c2c9c02c1440d500b071b429902c0d0152008120100d10490f1340303d80290060f1400c0e1461801000580000a48814000e04010400c00041050403c2c80ca60000c1c981601003a00011100d41d5074140c110b0074520128040041141100142e000c802540120700131040c1008944078103400000c1500d250f8401071080c0d00c0307008003454900c001400c940b21104140001030500c0014100c614865101844460041e00714089421029601d00980c40143c100c0340c1082041c9420101c20704c0c00f02201c400f0708801c0c0078021000070f441065681002d202c1e541e1007015151111018509510a6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 577228273 1250 577227023 577227029
    0x9130c031205070b0c040b07030e0d0b071101060504060605070f0212060a06080616020a0210170c071a0402010207060e03030c0312010501020601060c0b010506030c09030f0615040516140705070f 85
    0x540c0000c0111701c03030340040c000703580030f4030746100c40c0b0342c80e05a45507029100010341e012020342010070146980c01164101c0400c5200f0365050b202e40400c0018441d607030b800c40e05d1540004e0b101c0c40c501030007407040f03070362100c01e0341c506991181d15104204028000100100402d24050766a8420b1801304030828100340c000004513901d0008451150b1a00b03c14800b01340240c214840050b4030103194a0058a0704030031074130103c0e40710f0902a20407401600c40e04d88040c0200c90030b416800001079200f041007040300c04c4a04030a0511301c2d0a81500345540000c0d1036541500c03030710b400c000c00a258032070345030750505c2180c80544115086130b54585440c052100307145000d11956015020b03079000002c0e99409440d00f141c1c280e61000134104180e081800300f10868202900400f90003a05000904454601300b02a040300134400c0c0041100303240a401c2c580906910b04110b80c001c6003400107124001160401008000b20340d418600301044d2001009005030013400c4026005125200002031000103900c0c40c9015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 577229523 1250 577228273 577228283
    0x2090a0b03150c1219090516050102030313021e030118060b0907141309020a020604050607030b0f0423041b3305040b0f030a0f0b09130c03120507 64
    0x449900e03840e0b00c08007600b1255125074810030089200b900d20200411a4041030040c038041c905520f010f14502140d1075000c084070141c0c44103200a94a02d812508080100401d100230340c510300d0300c0c0900f4608841130010080c0a0280c40d0801c0103c04982c032801c51040e10082c1c001c12105140805080c111402c680080e03071031601d0400c2c02d042c2410105441440349000707880f1401040c1d841c101c44030455100100318042c0035010540850071003c00d00040c5800620b641c010140703401c1c18146241401000b80904041c10300d030140c442e0694032921070605458600701c800040c015039243c07a420145030002c18000402c0100c20401040008070f502d034040c0c8089510110007440d0301d400da580c40003c0780b00803c1c6071141400c0d01031502e1204000c80394628a05038503000342000c1e900e0700c181a00703030031105111a0b001d1000c03003000303018a6240710b40d03004010529801c2c41b11045e0407012880d0b0881c09000718040e614031503810828000760110b484c0080d0b80c00900950b00c0080110020b01c48d4205c01001c440b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 577230773 1250 577229523 577229533
    0x10020a0e0a080607053a0516030527160b120705030c03010909050a06060602010606030b0f0906060a03060e04030512072c120709020405031606090605090d02090a0b03 73
    0x81400c00001d04134801c0b0003030b4807184c0c501405601c08481002c4040e0590000d4203e501481121951404142c665203100c3c10303000c01c103400e0a501c4200914103400900e41058549020002ca0701502044070780d680800ca103004803203841c1c02601c0b03418a08640b0500b4009103900c0030014412100c1002809104805d444110792510380301350841d030030b20081e5203051541c8810b00050103c01c006500821803070b803160b021030780d03104401c1d605c3c0c03015a0b01c01d92043e00580d6450b4420400d05070140150000c0041c22944403a9041c3d4440003d4059400504182e0250402051800f6140c1c00780d40044060410480c010071030307140500d00103015134020402d8028503000c18000c103120900502e100c0554042c2c5160f44441c0d0b0f61024034800145108801c003541c80f4414822844051405010070009444070038009a580c50518007032602d8820a00c44070010000c010004002d09680001000f003582c015140c640e588801e000c00040001102280181d804a100d005000142c041644400884501602a10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 577232023 1250 577230773 577230779
    0xe0a060f080a0504020f1e1e030f031611010c050f072d060e010527150708031302010908100f05010902070c03060e1c0203130b03240310020a0e0a 64
    0x200548900351002500000b228030007190700d2502055003143c2400c0700050aa481a1a00c006045802306a43c1d1201000c15141040240d04040c4140c0c404541820001d600c1c2180082000c80b0b01c031001c1001910382d0942042c86481c60b8822240c800510b03030000304443c1403200e9071400a4650010348100f981e003800c800a40b0720308050f90820301100803c104528002e081c5012030960300240d12220141c100300081000f04401c5103112030745c501000c0722110715040c1344102814028005642000c1c800c81e02c00a010460019001d40c0849510101d80c6401004070206440140c86443c4990003c5040d0300400345031120420465011700408021240705012a0343e841d030000d41203106140002e00039044601c001c1c070201d0016000908040d03540003c80343e60300c9100d00c0603030010002009640050f000001c0e55030f101c02c030940c403000180418040d03980c514200701a503207011030034950580720044000c2c560500070341e601f40b2022121100c0034009641d038454002d8020895006060003c0c401c0c0120130b008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 577233273 1250 577232023 577232041
    0x50d151505030a110411040308090301060603020309061f030f061b2102070f1e030e09010e0121080a0e01031104081203150a0308072001050a0f0e0a060f08 68
    0x3160440301c01401402e482e440c29121024104106944290000d40b18805042294800c1c00144000c5008442c0c1545400e0404105402c1d41c80550003c410140140b0a01c00407070004180540c0000c3c1e10b40000c0550790035810001c1d1190102d0340050b00540100381100305000c22034003c40501038900030036101c8911b1428040c0c501001f0080201070915070f940301c602014001e5070050001e90300a044c0d05040011036034442259011204154560b4980c02d00071904064200c45640d002100c1152940741c65810400034411924052081c030328801a88040040200784881d400000d9503000a0100da030390101a501511030164020340c98002440c100038181089a0003040e10159055440a032951415890500c0c02c0d40c0c10103450030312502004010b4a5942c2da80c0d08680005500c01d2006580711091400c01030036660031808002e8200d4081c072a95125603038040c080740c620605074100010301000740201203510f038000100315a0041e0303158002240458001011182d000f003240c0d107000b0315540c2c0e1804 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 577234523 1250 577233273 577233311
    0x40221060a0807230607290402060d020a0e10031a010c2112060807031a0906010e0a02041d01051504081c0309050a0b0f0a090201020309060d06050d15 66
    0x100702182d00f006409011440c000a1003241d200d0203c000e0141d07900d60000060019130200004441c00c199915080154510000d01907109840d00e40100b960351600d50081161886402503900f801030f40041e40d0b045850207408001a91f05003d0801c80d40300d122401d01400500307025440449141035843c50103204c0d8800c2c0300c009003480d444803400880c0b203400e850440c0c0fa08003000c041c2092142d0300c0900000540300d07101b080002c01058000f410418078506104034012400103000300c0c4450540f08000c6001000180c6a04407030785000c02d0b0045070f4400305440e00a010f142c0141659001c10040e00e0030004008034058103843d01150480c04c505100400300e0703c58403903441140200e03040212728120034082088080070010182c01e003c00d007428141d031400d0800310140030071121005084140b10140109a401681c442104002040301c0d00003500081e640740105200c1e03501c1480e0009014810b564150041001040040d1080804c50054a00a142050040a400a440d150200b61502c224420300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 577235773 1250 577234523 577234529
    0x604020f180607020303030705030718031a04030e0409151107020312160b070309030905040203130b0a021908090609010912030e0f07090605090903040302010e100e040221060a 77
    0x442180340442a07080010411aa04103880c1d21010600801001d0f0300c0c01c4c0010361007242c40d40e0f20302c0d41c0c81c40c10f40e2011b081034131100703d0020342003500f5205000048454170b0101070a012040e490034280c0d6146000c54051011000c0940c1003400e0161071020801d0010840f041001108424404d54800c40380d108001e003c0c0e003601961650154520404116004000b0540f0300d485860310100d034a15901d85420020080e20710000180d51101d00605040d44400380002030201198254550f042c40d412210454036000009042640c1030710100d8034451550741107030003d14008450024094914070098460401100d46a036140501000582e40681c184900c0c241e4550050107449041e000400890080001d01d05041040c801c820b62091055002c005110007440d454801150060815081c0803107800d0207041d420055006220910060782c01c02003e21410074207484080308810002d00071103d2183e840c2000350018030001c1d00c40d00d012258402c100b800607400c01e83c0721131a120341c01803000d0094148 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 577237023 1250 577235773 577235797
    0x7080c0a1a030c0715090b1e161b05011a0a08032a010f06080616110601031e0f0c0302040612050d030c0207080f070305071a09040f240509060402 64
    0x40010383c54421003014009890169042e40e081407421404101181c14448040d280c4588580070021400400d1001008007080e00762205038071b090089962030409558814481840b1104050440400e02003082c3c06620760800000d110410003140d426490880d2005442e0144590490100b9421000030881d180e035407000c090f04140c2c481300240014443d10201e4038030720301d54031040c44455000e854001c030806040c2c400081e105074140031007003448502c925100b80c400e1040f800c11b40000d0702c9000c5003c90441c4c1c0c2000c400801541d001107628180a200b08008240050001c408000e10003e60000d0055a100fa030301082600c1d02c810303e42c500c0342c4000e40c00400541c81181e030501a01d00c80e400c8410240383c103004070ba60003500c40392654205070040000080c180d21104082042c40000c01c40080140803000c0191603000c1c440724442d4480c421034070301501654581141c0a541d071016484022803008100b0400403009543c03514010300003031480b900d4416100080455294a07082c421600981041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 577238273 1250 577237023 577237027
    0xa06020309010e0718050a061e2102011d0414090f070504090b0711070810020c070609030309030305030718090b010f05030705040504273c031101060807080c0a1a 71
    0x45c0c50868050000100405075140d118140000d112201c02c5041d047c124400c0402049603082c40a40c0c51945500358500d0346d098100d51289000d41d803c14401102107400303100540d180c0c20070a0100b0051b001301580c0881041c01c15040020f0203001203001504100e921050b50703070040c1e0715000c1000741c440d00800600480c0120010480b001d005100034034490000c54242c801c0c0c0d13a5a47d41080c1460600c88000d1140b60300010000d44250080c0959005800a030034046040c0b4150384000382020300e5408004c0034400004041207840c2d00a10801c10403d542c41154580c0a4a4504280c0070f0140a800c16010880381140c0002041c060000e580c458000c45e55014149481c1800700400341809003503844804170321644103041109010500c3e4001c40c09041c1c1c1d075000b101e0480b042100c2e1840c410406940700074800c08020034845800000300a15058504580307900190303124107004003902d0f44500300910940c040040c1c6076502140340041d800040f03403030b550800e540d000440e5050010a0a00b1900302d42 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 577239523 1250 577238273 577238309
    0x616020d0f031d0304080a032007050d050307021507050d09150e01030e03070f0b071e0c020f100908070b04050a09110f03010e15181b09030a06020309010e07 69
    0x12030381c48190804550f2403116070150348012500d05550040c3c000d0300382c0350401d41d040c0c418550031445029403044140c51010140c0c1c001d003d0130ba2585401d0242500c600310480701482402030400507a0000d0b40c0003006c40410f0a03c501c91100c4039440648112414003030014080c50031406500107608a99060240389045c01c0c050504850400341d80100906140c0c0d94200801540070801c044c08415109000003c501c0009060241c0d448100911410130021801e1032004001404c0c0584610030f552800c0c1840503c0e50b500c00543c107400304240090f0030240d0003070303800760865001e001c0c082114600c1e030030741c0c41d904e4a40307007107840c0b40c4118040c00c0e4000706c0c1d0380b404000000c0c00da030110f10f900c0c1c1000e4809080030607602d60580140e0003a0b2080c031284500718103118084848c2c2c41440c146600484804528040201240100b442d00030415010940400c1d103151003680c0c2d0b0812107600c0c04004007501c00003030062402c0303002034000f0745000b2220740c81d218202545040c00140b501c25104240002c2d100415 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 577240773 1250 577239523 577239527
    0xf0b0f010e010203070816020f0a0602100f02090d061b0306062012030c0405090c0a08041b0810090605090708060406020a1b200415120f0c03050616020d0f 68
    0x30070760048038118407042040074042418403020300001486a0481c0819a10500410034500d4096090038800c0b94034500801c2070359000039140f0403006000c10041030060040121200174020014200d41001c03171000c100c0204099540314207104145140390040c4010034110440c100c0c1da240c0240030215030b24001d4a00601d44e000840040e0306080c3c81190314000c0d1070118000c0325041074500d00007da101290a119601e050400580d0021000441030704018003403100512940004d40050301e4038010300c00c41d010070030000301684050070060381201c0a0102e60004540101201441640d5951901e800308102c42030224040c411542184000d000d00d884940310035000358410074506051044002250080800d4808a944080c4c0a804031205503245094014141d25040500c0d900c9689440340403220880c01688041c15154240401146a900b03441d110145e184a000044c00a0b21007040004c104540022078502c01d40c40d5512035011342481e0310050b42d070703080038081000100b0035003441050701c54 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 577242023 1250 577240773 577240787
    0x2d02030a0503250906020708010c091403010b0411040e150d03050c1f0606170103020114090604030c090525020a0314070606030b0a0b0102030c030a180905090a02040f0b0f01 76
    0x818030a0f5502c81c1d003010f5070800188000b0005903440854030f54801013101c180c050019400918401c0b000b400900710fa150002c1181c0614020299900c2054035940900c2c0c03025841030000c40c502500410001001411300b00403500103200c0c2d0204d103081030300018014001404003203541c1d200a0007081d0b8215450b5000d4030079410043e86412140700e01c1c0c412012540030800402d46481216800003400c6042c0701c40100096040c0c2e03c181e1014011000410040c0d0780700e005114a2100703525415195422400092207030300c03a40e03201034441c1c4407908010812040d5984090300500510204ca48451914003000003d001c1d1111200090f811504015000c6400741442050103000702103c5441c2a405035244012200680c0094403145d4401040044892051007188030001d002d0000714241383c800c1072156580d04c0b46461150070402c51404641000901508040240c1800c0000f84454600b10556a0391110404410788c0b180303003412060400c401c04d900c00c0c11a08a400303800c9010103004040151a00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 577243273 1250 577242023 577242031
    0x1150905090f01140601091202010806040e120301090218031b0402070f051905010b0a0e01170a02130906050c07020609010f05090a06020717011517011b2d02030a0503 73
    0x98007502400350700b0940203101d0441e11903000507003010706041c04000105144041c3d003141c01000b419031022000350f84c205410540c000310445001c201c811a48001303d05001c40718402018580f004800440d8650090f00035004540a040140c2400c000c40c6c810556240342260364805150000544e00c0f00c60b061940080c80080d00544a04261000c0c41d5a294a401c0e8502802c0c1045450280000e003081828010700c203103c0e00131241c8000603070400000541d2141c06124201032944400c0d420100080300f406400500703070300103021021001075200050040c00c030366141124101d2519002504421054055940c001e4001e4a00c42c02c041000340150f400d0315400000360280b1000b8042c40c6642d40d124007a0314082c004540c040c11005180c4001c0c00c20080b1109001a00d60b410034058003c2500a004c10008507004040301250038414010402e005200d1560102540740d003014081e01c54179005640c1203445200c0207007082400e0000010742c0070741c0301040702180050b0000c1184081052180d000781d504 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 577244523 1250 577243273 577243291
    0x506011514030103060e030f0714010b0103020406141e0f0406020606030a170705070b130e0112030503060121110306030f0a080a051c0501150f0c05060f18010608010e0d0201150905 79
    0x1401501d200c08880349d803c1600c0450b034030300078000301141150b000e000d50350030341001382015400d060138150043e020840d1421081c080260100740300030503060841e0b40c800680301460a0a036201001c280f0b482082d0f000d4000c02001d4412040490030368200010000c9145070002002600f90011750f1500c81581d0020394203a44a200d040e20100d001410000149440c54089140d107030440c7c85d0124200500da03050b40540300c0503052424a40210390024202da500c01d00910382800a0020b0061260240501e0030348844210701d0a5048602548101d006500640f001c908417000f414140c070b5101e90300c102a03040205946801e01144c802c44d40280c1c00707400e500401c20341210b0500440900b100c00ca038000d9010b1f81e501000541ea0703501d180d0300b04128041c040c09929003003c0c0f95950380c4600382e941c50041e040c9440303000b8086c00a0000400040b03d0b04868100a00078030520780e40d0031281d80038220691400704c503400ba22149005860051040110070192010f5604005180001aa005110080c42001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 577245773 1250 577244523 577244527
    0x5012307231201090605030705010201150504110408060a0606031136040f0911060309070e0601030b0402070f030905030114150d0f03171e060d05030d090506011514030103060e03 78
    0x69502c0b40c45440d50103001c0107030700017414030300d840101441d0071007650169055914001aa103803030b1104e078800c8030585c0c0003520082049d581d880885d401e2886140d11003041400717203100780002d1500c00e41103441107403500c2d50b040c8140014488541080d00c1751407441044000d01c0982c0b15500441c01c00843c01e09500007442c03501c403030000000704042d100501d444450150b9604110f508000d4150041003005074196604c2d810f525140d80710964424480c06a046401050f00006141d6886604001c04815029005548620082c0741034609584030740811008251025004030b06070405106225244008082c2c0148541704c4241d501c0d10052195141030700300700d51160380c4000c0340c5205860b00e41d02e03100b9610350703110540b4416820212640500310100c80000c0080d00c0c0300821a0000d40da810840884000100900f41c1c68a00d06c1c41c418051024142414014480e090040100d03809048498040541e5089030040104840c4c0350309000200c1c00000c0280018404600d44d603105004522844044038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 577247023 1250 577245773 577245787
    0x910031e02041502031c09110a0803070309050102031c0905030903060f010611030406080408280507060b04050f0f0c04030b250e030d05070501090c030501230723 71
    0x5492a80c0503500000d0880d0001800c12003000a1903035100005040e10196090003008401101114012503019012a496404443c14030504612a00d8040d00090100c003003e07580703020082c3c803608540d2055000c07403552140010154004000c403408148a103440d520014040d590301c200400c002c140580300b51109000302d903140c3d01c040028a0044030340c522450f034558507085009200400d90400310b4059041070000b002000c0c0c0241d55640c11551100e00c0c2c43d02c54804040b03403a08000d420003030403442d894003196000c0c6030f5080001003d9150007240b052052143e400103204c1176410644d48141c034000850002012a54051030568020101d02000c9150903942d0300d5541f1600f1095524044200c042c100b110140801c003030340c418030b503580c42c18000004919000080e803100805080d90b400d0010010b071650404c04298060b03140305a12821b80c4481c613032a07040c014001c2040d0700007410000544d10741c0e409422558204107100d61030a40e01c2520044c02c8450600000c1600e080f12042460300380700003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 577248273 1250 577247023 577247051
    0x7080a090f02031914030703090b0319090606050118150e130501060e0a06030e0714010504030803040b0a11030c03011202010e0409120201051f171c031a060f091003 72
    0x1810302c0341410000110742c0d1000b400c040700f44034a004603201286e401006800c0001360480c40c107400f243e900300c8030305450750b440d40048900300d02c044004010003480d00c2c180a04200183d404241913600a03070b00c20164149000c0072040c610000d000d9107507412044150482d045104120325108100060103034102ea8085115000c10f0b5203003038100038082600544882d400d82010f0300880010800d900d014001e1500241c102600c0e80068001d819142c81c10b0300321560b42c0d9008604a400030f5078084401c139920303d0b086c100701ca003c0e041621064039060a040c00d01c030740f8805071815a801482180e96076071440c0d10301010303124240030544040307050004000d01f10300300da601c42c8510743c1d42500030003503014161090440242102c0004245004c0c0c22048bc02310f07600e01400704050016149110159840710941d040e40500e441c0c54041c103480c0ba160043d17121032006600d03403c8a89031150340034002c0501d100380010800d450060408100038440f040c045548039150442504405203458200010041c1c03c41401c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 577249523 1250 577248273 577248283
    0x3021204060911010e010f0807180f0e0c070203030301090f090b181c090e04050708061f0b1e0d2a0e0d021c0302010216060b01110607080a090f0203 65
    0x100740da0807580c52100409001d442a81194021024680400b07480001d00000e40900003d0b4545420841da06000501d920b028a040d542c07500304410844556a40d00d40b0404d514140c0b90042c0b604401c000c3e408603101a02d400152540168014003440c11a801c1516400085c5000b81180d13400c252121000310100f1625181e00b40038924940481a100c0e050f142800d00d04034252040071402d1030664014940554072590035010707560014003030b00c01c0e9104d5041030783c60300724150808041c42c002d1205009284549810040e01078500b0410600320319a80c4950010074058900f0000d294162a1040760900700c40c0710003003c0c403032403003040014112003420000d0071440c3e0408404c05a084d011510028450b0407c1403050758100c116071143c0740e4001765002c1180c245c0b9036100030f446c00f9010040381c2c04260003234040c0d0750784402c0d000028081d5111400c001001d40411311b507007804102022028016008041071552113103490392a401465100d0041c40c400810188100751800300c42d00306000300503982800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 577250773 1250 577249523 577249531
    0x609040816120c12080603031608090402030a200301030803160215010f050f04050402060706020f070614010303120c0c030e0a0f0b130b03010e130303141e01090e030712030212 77
    0x24541c6040302c207074a404803001c607003131502070b06128140042200603a0000101c1d00044030000715820840e070545080398039402090001c5030b1090001c01000f030584c00d02e501521042c0107013010400c7d090a00d0340c0030109444280030180448070100009a44060f01501c501000e0059204507020a81e0740000083c004a00383c00c100700810703501108100b03d240030294175032800c02c00c940070041400e16500180d00c40c0700e103000c014500c6801040c000c240000007400c0d5550950020740501198403000302003131050409000c120003045079030500100000e454800c0384501e03c459142c2405070101501c0c162509003440c2106540501c404170007103100d40e440c00c2030000514981411030785808411009603040c03001d5420416400800340010031400d00814441500039550014000e404101410124040c0c03285405041e80c15020380d0901400c007094440c200c505090502030101e01d0390300c40024009880b030510304980c0c00d51050080001154614805090301c0c00182001850142e0010703641c174000344104d0f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 577252023 1250 577250773 577250777
    0x110c030a09050310110702101707051c0b03060714040f0b1308030705060c2508070b0907060906050309210d0606030b131e050a0c02070b03060904081612 67
    0x144081115043c1040340d5501a90940b1040c010680c450f250701c20360b4000c0010207449141004034095400380680c083c24958111200d0074001c0d841c00401c054080e51010040e000080c40d054044c0c00541c040c0d02c9415803041008001d4400c039100c0010854080d0071491583d0044c5004100002d8041b00400040c40100300e0002d046807600d80168001002c030240e680260401d801c20800400000c0005c519180c1c48050a40501d032500546a03e42c030981490350442d0050510896511040c03100c1000a020322074802c100c0940c0d20f44c4d80c0801c05854000e030344140b202087cad924105102140c01807029542c8a106441283d140207801100b03540340c803503140700da031b6200500003c540035240071a01404010343f8170350070103002c5001401c0204e001200e100000444040c0d80d040405c546020b01c007425150603640c0b000510040c18100c07040002010030b4000341c0050b110781400011804420420703680308078001080f84180d0303952501c0e51a629407021006001c18805003011100084810419211200841e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 577253273 1250 577252023 577252037
    0x30415140901270804120602040e04030e1e0604060f0309050a11011e051801050c250806010503030702120708160905010602061b0f1c02030601140319110c030a 70
    0xc2c0341011840c80361182040764007803d0814140410541411102140c114140d0548220325a05000c07000340115040000003031512402e00041c16804400c003482c40c5012504844040c208454840e45d9500f04c107200c5820070001d00c001c02019000d20400150032000f030030041906481c56407442c1c1040284d083c205c5907503116030002d603d42e5a00034103441c4101140030340304200107803c62016241d401292a03001e18802d1100d4240142d910076400d03030f80c1482994080344c9c81041c0c0c0100d0296001c00c0d41440c5100d82c85040e8001070380140000e0094100c810117070103149071150a4081c040030f40700120b042c021512400000052540c4e0400c0a0442c0844401810186904200c8000103403030044c3e015604642c025028003d40a00d4482c40741e11a000c540200341d500e040541c0c00c00700501900054005000305101a020034030300980045110303036030036a03d85010075508540b18803e80015111584000c45000c0510303e0310702150b01502d00c24400603119800d002400307808a26640c003a028640001e448 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 577254523 1250 577253273 577253291
    0xc15130203102310030f140607030f0e010b09130c0509070206060102010b0f1f09090e161517060303070209090c0a08030301080307110402040803040602150c0906030415140901 77
    0x24450b805091a480749000603c14149101e0114280c00d507800007038403003801ca00340001080f200901c4913907640b0f0f8810940d0403502c2c00d1800600200140307000002c0307a0f8200304441403441c1040c8925000c10070000d195620a49413540c07041d22001c1c0c10102203480c17003c4900003191542e140f07800c4a00c88c5901d60b00034440c51812000081c2544c042e020744a0246181c0c800503070b459a07820108441504254a40c43c600d508024001c0701e0244090340030750850751a1164959102c08007040710301c00240302c80440030380b19545409002c1401054200c080000b07181c2c0040e10b01319400416041c0d003100c402021282094241c0c2c0008015820580d048091680022010b280ea406d01203113127030041940102444c2035605d040101c40c0c41703210f80c1000800aa031511294512a541c9a0549014003016403c994559032580800796558040c0c52404666480000000703401e6500042180d0b01000044d101c0c605544540d618407210407890141020660b8a07060301e40d40d07000c164000f507841040044004250420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 577255773 1250 577254523 577254551
    0x15060807090e0a02010815240403031727030904060e150103060305030d02070c0e01300f03111906150603111b0a080a020705040c050c1513020310 64
    0x2c22100c440b4915040200c01002503a006103030140e00040100c41d5007039030940200051954010408500e5090482c02c40003003540f0070010140c42601d101e6220040e0b0b5504003036030f0705030007401152282030240340b0300511000200b070401c40c401001c070001e003160f00b00800100010280c8503503801c03001b6550f070034108014007440c2110740348202d404282010486903003035440f02c680340e224074494031801caa000100030003002940308540e00109942104110305585075485c000100521584a41300540a0b4241c003038001341d03400352054120340c020401800e010960b40c2c15101c40094203008540340c09a860980e11221079a0415503069106d40d50000d0050f008241048080304280c100d4030806141901e42c05410503810115a010000c41044200e041d588100840c070340410104002d044000120399000e403184c001030031301c2c103a60301181c080c001d408030303803808881e54010324139000d22940c080186040540350402d031407500401000c000030717003084c1907401292038020070189104007550f40c0c0100c2a4200 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 577257023 1250 577255773 577255781
    0x5070902030a0b060a0c0201030b03120304080307030507091d0705040902160302010c0201060501050f03091f05010614031612060503030708041a040510030e0313030b0601090b1e071506080709 84
    0x42411070300c0710b04010217900000c182c1c5000780c80003410b040d550f0081d00107603170b020411074822040f450403181e0b503840e183c5841605500155016004030b8200401728a100b030094294005440311040c89261024042c4000e8443c0840600000c003030000400c00450030348105d00050641d22400045d03d02d104401c0e01d0002d003140c642d8001901164546403043c80340341c0c1d1080c00c46990001850340342d80c5a85400403c02d041c5041ea40080b00b006075003030541e00340e8111540026048521603240c0d856212102c0440041600c000c2714042080d560a0004080280c010103014040c181d00d0031002071070985031b07400729155a100540c2591240d601040c1040061034103c802202c8a51041c034a900340740c544070105030018081c149041c18152140603088081c80200107507141000412036145140d41d49042502041406881a5001590400e80071502141102c202c82d0750004000c0c2000b00e00800004400e0641c2103141c084a00c4248021030085c00e40203401032001a0500202400351a80392a10400842d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 577258273 1250 577257023 577257041
    0xb060f0a051614101a010c0804050405100801180206070b0a0902060a0c0c0807030f0f1a0c03061206040c061d03070e060909210702010c0b0f15090f070e010c05070902030a 75
    0x2c0381440c105c402c00c803008180c1011031607020f090200301041c2518064640d4041d0781c1005820500d01b401704100080791b240c000f400ca0310a1802040341c2661b5070b021250181d087e00d4042d4000804100080010320101c400300d40c0701014510002c3c0c000820340c00191603522803d14000040c0106182c48107101b000ea016000a000f2400106840d40c40c55507090b140c1401c0b904040d05148a01c0140810701c5104103200c2060a12840540c2440c0b611502c0d10280ba04103030749890040d03d00741c5883c18602c10006069003d10b801001140209141103400c0b00c4185015039001c2420600a56100103620100f00d41c50180c5116040703c1d00360300c0d20038140510301c01d00800d081202c0d80841e8510a0381401010030750719003411428219620207460006aa8002007090010801602d0340100304102009080c81c9010b035004040d40802c5034510f80c10003040c040e06580f0340850508003004a41480d015a070141000070f418108142d100c125922500d082505c1035100482c03060b0004100302010440d88200440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 577259523 1250 577258273 577258303
    0x290a060801050f060708280815090105040f0b041b03390c051902011d0306130203120304050c030709140720101a040b060f0a051614 58
    0x120740c980380020324905801403101e8000c001c00140c01003403000c002c1c02c959054080490381005a9001062010490413130701c018000a007100d0003141c10888408101c1d50403541c000c140806903401c1804000042c603000031150101c9588400340215911240160f89607108442c0c0e6021103000600030103400d03203034411040140f511000c0c905011240011000ca0901c84809903201c104100000d01a00c00d80070202c0d01034980d206900c400c2a1450180141d5a82a4801c0e0386c1c91080c0c1c4081602c450501600e0000c1c0b030fa0503041900054401d24103130344003070701440c00241140c1c04826415203142180d40152020b8a46800640c412030080c2410030007030004114207441003002c4002d00100d48140341d0050700300800c00011104141c4150442c45c25103c0704040c1c83d0903030f144480021400ca00030040340741c211800c4078000c6018415840c041c801c00c44596400b030101c510b08140c0410f0000e90707900c036810641c00e201043c4580902071700c04250700d030b5203144074104000d0500b0340c0302819403030b00411030880341c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 577260773 1250 577259523 577259537
    0x1d040c0b0f0a0f0315150905040506011b020a091112070242010f0807080d02070303050a050705030a1218051c1110060303090e0405150604290a06 64
    0x400001d040c04482402440b86000039602c9038400e011005002000b0151001c48116030000c1440c07070640240e44800f011545401c06c44a40e203800780415503000b1a64580404c0345203e081c00110001070131400722600c02070001811a41f0ba100601c1261040400126070403404280d12014503140320034241c120304140003c0c040c642c180d80a5040504c1606080c1200d14000c205828126030304102c030142001806c2d9540903a0b42c0c40c0e2804014801c2e1754071031100f1602c035403100020000008210501040e065502609901d0305649060315554061040f80e42007101c10080c1e400820310502c05803c8401444c5da40b2a9030708030f121124000d407100194012103807001c10f0103c034005480000c1c01404005c401c215103901c903501800580d05110300c6401c0c000302d40110202610581115440030040d0f921980311861f0082e2294040485c504003100c00900030b034404800305403070003016001503501007401007000c1507421100e070701740d05603130950488401c80f107514014826a600e08140350501910152800701 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 577262023 1250 577260773 577260787
    0x108010f0e0c0c030904141f030b040803100f031a0a0e0d0e010e030102040e0402091006021f0e0d0f091208030627040f051c05031504061d040c0b 64
    0x103000e100000d881200b8001000915414841c030a00c01d98540c56001001000301209405a5500301c81080311140000314400800201d818030310b00d402402d480d0490880c00c99540e650b51002c2c901e40c0b015090a281c0301070a040001e005045e25204805940300b044022120052001c034412003d5010303085540103410715a00e228601e60000347c80c40c0d4844903103460780f024804900141d500301e000100c01900740d400001c010500700340d603500c29030007a4800d41c2c2d044069a00d500c2401e9200070113001e0100160066154a1207070985414400301800340340c2000a58000b0040500d807070108a94441c1011030900042c4d40d1450342c010a00000030181c1c41141a80950340c1d42d50381c0d40d1484001c010b1445105040c611040c1018510100d112024800340894010f003850b0514120940070044125500c0c03091040507aa468401240c0304040945e5444090841d1180d0303c00c6c10803c4e4541920641040d83c8200c001070f00c462225100340c00c6994110f010412713084c5424030302c08080c03064100292010040102d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 577263273 1250 577262023 577262039
    0x30c0b250c0521040f03060911010e100305070219050607080a0b0a0b0f07140a0605090106030c063204170f03250f060506030618030301050420180108010f 68
    0x10f142d00c0c103c80f819a10304080004841c4140c0c2c0201d070018103501c0e4216801100700110b0b90311402042d4090400800e0100319103004650000d820101141c10885030904070710380c00d001c1d03000ad030342100850069402c41941c20700c950680f026116002e031181e920040900c090745400c40f51154005130101e03001d00042c0c40c45800f1800e804003520460b410404005800e03011039403208250b42c02c0c10b134081884586407020f142000d81c1c0e8501181d05940303071481c0c4400b291014105104200841e54080b50398000545000300c02da6009504007841c3d024000700001c0b0a41c03013100c01580004800746040e00a03165810150040c040007410380130403071640e03c82c00356080040300004c1550300310010384100b82c070800c050742c5420321400c03680c04004201c0056802348008010a03500040c2c483d100a504544542e0398103105038004103482c802d111f0940e00f003040148840d040c1030300616090125900451640011070200e6502c65021540d01520314400f1010301400b5030340540850f006095001c1e040c89564100841c2e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 577264523 1250 577263273 577263283
    0x2d04090b0a03080315060d0f06061805030a020f0102010e0105180d02032a070e07080618060f04020a0905090c07020103060b0a0219020a080303040c080706030915020304030c0b250c05 80
    0x105c039803031200007081004603950b8501190859516900c0520480c0121590302d00604201c0c0650740104001c1241040352000c101c00d614102d680080040006021540902c0310034141c0e00c030443d04554a8800c545c107806002d005040c050741e0908540800880f1000300581480e400000308030031508200311310341c02101000c0c2000160486a0a200302c1544545082440c1031030550040303080c15440d8041014046d00038900920504040d940e001030380d00d4110800086803801c8610a5000f03c003500c1c0e030686800c00e036025191602080c242008119103d0f030000304030309422112444148070014800085503414020000100304603803003d81011404c1c0f20217901c07500c400c5080009500701c44d0500041d96100c43d299001000a1400e4039500c1c102400c102030107000c240034445580c40752002c00220f01e40b00f8410702e5201500020581030484c0802a0400690b001030400c0c6c0410203c2e8116001142455014600945a107401078456822219080d01c1300201045240180041d5015800106030040740d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 577265773 1250 577264523 577264531
    0xf0903080f090a0c08061501030b030d080709170601091121102409081b0105090315070c150b0a0b0714120403051b0105040b2d04090b0a030803 63
    0x1060741565542005860b0140c00400940394800c3e040000512a0000c01d181c5d0141303000c00c0600218a01d80707801501540c28046d0304503010350107552100c1d400c510941207540c02602525003c80c100369501103006007040300406c0021141c20450040150940c0c2c4e200c2d1a070742c0043c40e003040b810075400b06100c6190070100801c0030302259000002030300350046800c0140203080340c41c1d006001450704245005800001d450541c0c0032401111000c80c0303038100001d850841c0b10529440c1c3d02619420300c011190b40d0041140250103100790780400c585400301829591007204540e0703411755000d14a0400c04c44015120b4a0029180d160603000502034a03403000b00030581e41d81c60340c02d90760b0300036520300b080d01c04034607900203581c5006510381803044d117a500000300102da006004550710803030380307080123485080136861060201d5400c03c01000081568801f40020880000301c3c04180b48001828070b000e00e9401c40f100e24400e0002800740002090340c0309004500cfc400741c1d4100340090841d0b076203250900c0058 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 577267023 1250 577265773 577265791
    0x80901080c0d0212010303020c01030501180207060e010e010b190f0e150405040312110f070f140307060621050604030e0a080f06090c0108070509010302090f061303060f090308 77
    0x800000e00d8040394404960300910b26a404565409503200d00c1504040280000ca0048c01080e8190f030941d071180c01418140c070a40030600e6040d510725078501000790300070b11302198101d031501e00321040454203100303002040c082070002003250400e07001004041c400714180c1861404101078140624000643d00d1410346050052010700c42c1c6400c044841d01c0d200c81c100f281d40c0300d41014200300416030f1080040484600c01282444400601c140b14040740c061a10300c000c40c05c100340300010205020a000034003407400b55645603403e9039a00080c50440d07001c91030030340f40313161140d00822180c0c01ea090110141d04402907001c1d40c03031500b5034400d42c45400291001d0104110356005c4240341e59002c5002004011100483e1400340b9003140c0b4035190310089074489410f005d030f2507c64209501410209100d0b00c45980d52915000f000300040d4000e4000354404e0b9040010307815100110389859006007210055200f03803080702c3d4038624004055501e9403030307810105820000340b4070009402c8421150084484 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 577268273 1250 577267023 577267037
    0xa0906020a0c18020d050711061e0412271a0901020a11040f060801091e050316060b041d070b18090406090605100311010509011403060a030210020f0118080901 70
    0x202e2614004e40101d8450f010240e15007010f110215411211048400c188042607442a0750f96244000060185542c0c030f510006400340040c00041c48500303a140400d246081c004520780114026154034464403105100d410040c0f8818003059000c0030000d07907403140030f034241c5140c411043d00003901d50000001c0140200408034800000355540d0700119502c041c0c0c04010042e040ea03403c0c04501030240c21000f83c90804c200e004501400d00d607448007403512500300c0000e515008452031030710340704c00260100b5504180e46880c2c070101d9030b59500030146507040d41650b101e01c191481c07811605207405d46e03002d459044030030461841c448034102161a4420000c03101020643d8036030174182c01921420000402a615042c00c200203003000662200950380200140c20514400b5801569140f15442e600c03400b144141c2444038034109044c0046a1219001d07003003c1c3d0b0b181d6250301140c0d5041c041103100025801181e00581c2c09907017442040c00306050340a01e6400700030a40c81d01c11030351040d018003034100040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 577269523 1250 577268273 577268309
    0x81002270d12030c03051509160302070516080610060905010c06060906170709060806041203090215031906121b0e0f0f010e06011e090909080a0906020a0c 68
    0x400d910484440d800281503000507100140c014000c001002c0f144020900d00404180c4c7d1545002d18107165006c09030012801e600c800c0c0b946220a8440d011400405808101d240300185051042c850900c43c20380041c04e0203402c0103605400c00c6401086c1c03c03201a10a141003060580c40701078982181c00a080c80c818410f01400e082018000c1070300b081c07140e54180720000800141d44400c017030800050ba015100e606841d040d0803010754589202d4584281d02210200d00405e651640c10341103041c16003000600c0b0561540030030044090315440b5203049401008002290481d05c0210a2291503420100607542c2098082c4544a038900c801501461070b0300d070740c1030001001101201c042c00884110340c4561078a20428140304a0480b06100c80c18140740000401c0c86000d200305001c1d4005864078400d400420708580854030f0815130480800071f500c2c80c0041c98003010320859081c6401020003030b50316580c1c00e1000d404c045031035112400319444201c2d0388000c00c81c1e4410030019a00c406200a1010803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 577270773 1250 577269523 577269529
    0x215070c0f060e1008040326010f0510021204090b0619080703050a0c0203040909031106010b0903010b091e040203030919030c05090103030f081f0603090636020d05010903020708100227 81
    0x1023510381e40007550a0303100001c0340c84076920707041c001142d004a45c080c40348451008101c0e1a1803803d0781143c1d08840901040c040211550880d41442c4000380199040c000000c8a016141038840c4c48100460320601c01d110017244d1601403641d125a102101b4006081e844030001d5a0784200c2c030560a01643d20800001014490a4401200c0d5002c004454030343d615500c002a85d40c1c000ca080c18460340c80c00f8154030b01828103214140c13107101301401c0c00c0c42c0c0c5400200c1d1500300d007100900480c0e2501040103074034032a40c0c0d890b04106207620241c4105a58508504d04a034440003181c1007640b203850040010000203911406000c444811072501e00200d40b00c8001c03604030541000c5184150880852010454541c03550020301418090841842030074034101070b0302402e0301501e070502002121003114411007401c0100340780365148080c140103440001c07602d626003101c0c0040742c02c0b0f00680140204000b0790404200c160021620324004620b07001c1804405003450345500130082d0b00440403c01030030703daa = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 577272023 1250 577270773 577270817
    0xe10030b040c090905030408070f14060a022a0a1706070c1a0a1e0908090d0510020d05070206070302090f1002100e010c0201270215070c0f060e10080403 67
    0x3c10901c03824401d4031428900742e5100e4206009908a904c00c0c040c0c0010003500f10003101c3d0485011009078034010070744038240000c2d13a000525100c1503100c3c41b050b0402d140a44807404102151424040c8100c9009400304061001190b1169803502c0c0c884960708a4603030085007840e0000035034140854030700050300d0b10740c09200131031510b52a240d039a40200042e40683c1c2c0c00c80d1a241d000c070f041891660600070346c844c2c02c42d440c0190240001005124401450603c549003984150003007040713a9003104800c1d1110180d07403040f541a00352544078402c0c010010b404009650304403515003025801d2000d0000440d00102c0f00c00c4049102e0003103082940c00303e600078000d502c220480c0c0700040c003034602c12226090180000101d1900150300c4c004100c030030303c54085014220500320700c81401481206408100c00e032025900f8020b03d0a008000c4040000d20700c01d07403c0c008040503405100c0c1e45180c248064a440c0c1051030460140a2200d214214158050702040e0f00070780c903043c21016840c40048d48000d034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 577273273 1250 577272023 577272029
    0x7030c020304080c062206081509040b07050d1d03040501110d171306050403090e060a180c1b0c0905061507061a030109050609120c07060804110d060507090e10030b040c 74
    0x80e03031507041c007c1607440e44060030074030484c800e524403005441e0540c14440c6002e030403100a046403c0c1e00c008165000d00c07810041458403c2a500070a10903800d404800312044040721041d110b40c0000340410155030442002d098215107030000d02a940710450000d0701e02800e1582c0700c8840b1422100141340c5580150010b481140c02200c204040c2c80c081c83c02401c114003901880301c080c401480000d003075242514550003900e2110b2540c03010221500f9001e40a80307540c81d50802072014582c2002480100004014000381c0542095820705103019a00011102c0c050045402613810701c8084d205404540b00f00e444441c0d001c10001002141007081d400d140c5121505a5815401c001d111400c0c46000580c140c054455401950516071103c00c0b0307105103210300040d5000d0745d00551400c1140742d0082d040c0c9a4050702854800340c54844100004000c140381100841e4401d913038609000c80030380d1116018024108a240c1c28a242c104080001074018140c0310081042690304009020440e001d1500001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 577274523 1250 577273273 577273327
    0x30319090c06050d0b2b05151f0506090604050f03070f180f091a370506030703052a0604030b0f0901020403020a0312020115090507030c020304080c06 66
    0x110758a0b540018410340c0954403020b4220300700141ca6050b86003d940e00018450f011a1307220100144040c007403554100d8880543d0309000d8503441e42c10719004200c80c58440ca49510314400d600c0702ca02c5801c2d900c0040f9030030082c010441442002c405072900000c42d0252041212589040d041c980c1c0000e151000c2c0e90045d115007035100c800054042c14400031500041b032103002c180100814283c0b42c10803101b650303502400010b80a00e13000340702180c402a0a8100e003136905d001200d03080b0351401c002040380715403898100d03500d02c0c034418190510521030140c00c060200e0103000203510310389440b9651380d20b154078a2480640346250420815003c102c5080f0000082c0401d515203680f07013031082002204649401c02c0c0c045074000640712700f4040c800c440640360b000301041003040c19921009030700032600210700e05540d07031090f200c3c00f0116180300010060100c03c60120780d610305084010183c0300d4080b110015544140018803104001203a1000c0c0c01d2819175541d5294141c074400100f020b5812458088 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 577275773 1250 577274523 577274543
    0x21010f0603030f090b031009020306060f0c070f0803090102060711160305070311010c2d050a050a0c0f0308030105040b03010b0910210327090c0507050106090203010803031909 77
    0x8050b04858144445001c030f4540800c42035481c41710700e41c0c5101c100d03841c2a00740c0045c4014001521035a01540d04000e01408140c2404007a0b01c10315031f2503000c103640da209503100312000c03c044072429040c00c024264210107035040c5100000080c3d91214068600414002c2d41c01c0560700c0700c0820002c9040e11400450030b200442d5403130601545843c22404103641c03000c0c05200410b9554051402c010700c596010305001000c80f80c0c6480c4107103419928072400382110000b03071010045141000448901070060300035000e00d1055241c44100c504495000c3c000143c1d900d5402c001103404d06040c2c904403402135801049250b0a2400240145000c1e240139600c031184c02d00780068910740501d104161070084200340f01803000741490f80c0790b030301c00e0b00402000202d904207084c1c45081d07041402e920a614541400f00017580720221802500c214140c80030010700c0c040341880a014090140308024078441404500e55410114034644a200080020f55044422a440c08030310b96258001050280c000031250 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 577277023 1250 577275773 577275779
    0x30e0703150609051605090d060f052703180d0f050d02010e070506071209080f030919080d110a150207110405092a100201150f0521010f06 61
    0x20121009910340000c07401e261000104010105215650281c4d0160500c0707071181c4492081207820b548000d407030b00d82194a0484020000d5068002e400310b8182e030000100710340c031b00046e4000040703003400c1c001d0010b1244c081784c0d103580300c1000c011140d655250f0500c2c03006010980020460364181c043d030003000341142601180a100340411200529400c42d8001e11806642d01c889903520380070b80c000d141d84200b0400c800ca0006103004044c181810301814040761841d610b010741410071420080b140580d1300009581710710380c9014041c40e03840c0316a0700040301207603040180c80b954500201804038140301d4412080d44103400c5c104454031300b0660204081d950506840d45000182d0454003040f107014010218044035407400e4014148681c18400c018541100d400406490400c07404220f10300c03200c034003d01100a52950f400715000e11203660000300e84243d500320080ea08091507402142c00b060541020b10180c1c1d2070b00300b40140000c500b4031119000c00c110300c0d024010a000155103c0d19481c1c12400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 577278273 1250 577277023 577277033
    0xc15020f03030a020a14030402030721060f060501030f06150c03051b070e0603010e15060103090b0a151215021305041505030607090806041e0203060109020c0c1503040f03030e0703 79
    0x5c1500310f12903a07400910180e0309200c0c144a0100346ea00a5040d0081c020501c0404468003028125207001c10300c4a2040c0c440d52141030440d030003001c441e001d05498817424000c650305030042c1540403481040405c00c080c0f5203d060014001c1e1901701204216002d586e64040c548101c06845520980000c0c021000080c15aa0781c1e590081d8814020080b4045001030030310310b410712407503910150f9a80179200c801050101803c00800041006042c15030300d41490011403003030200e5034410a4a080b002800101070a032244507010b02d0b5100100f540030b00c83c1d440700000c00080e01141080c0302c0d01d00240e02d4541601b80000103089a0704182d0300113141049107001c010101c4110b0b4201c0b00c0641c2500c0864a40f00400c544035210390042d2106540540b002c900044c1801103020702e010801091072400030035aa00103400e00e10280d1000505540200c4c402c40028401e205459000d41d0441d001d11500301080b2a8001e540030080c8042d0403503a8048450040c90300030b03040b07001014144800d07100d05584034509 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 577279523 1250 577278273 577278277
    0xb060d030215130b0c2d12060307080106140a050607030210020904021b010903030c020d1b06020c030f0a020c0108060f040e070315140105030a050604170c1f0f05040c15020f03030a02 80
    0xb0380354102d50782a02884c102411282081b900302050144c1c07601d0407400d6600003681c1e120140403640c1510901c3c00c0026454400c1c0314190103810060401001d030140402000450038280c0c000318811441000a83c000079000201d0140d182c28400000da15000d070040083c009000344e0b209908001e20001c2603024001c01940040810752080d00c08109481d100c08080b6650180d900503000498054051400484d41000c800c3e801035106e40400342c030307003004100d82d030b42180c01c1712201345140c2c003003c104d03845569010301a410078040c0a20b40100b07585001000a141101014a240d001d0307940c6109810112000340007010180da00a141e00b40c070003150f058580014044801c3d104040031079200007081e146400324103510f80381d4014000344020f440310381391201e52044148465080070350070820603030086402e20031780610b0898000100c0f240c2800700340c0304054802c0700b5100150300d490002004005450721440d43c0a44124054a060344065440140e1a080d1186003901080c800441049048009500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 577280773 1250 577279523 577279537
    0x7031e15020c2a0424270e030301120302100c020c1302070b07030513061103070909140103110a0f0905150a1401050904270b060d030215130b0c 63
    0x3240d801e01411020361441458080090190f800d0b080301e400ba2615041d000307a11000400030840d240ba40c0e11040e005480d80141e4088040b01c0c1c05003190808500542c0c0d001000240f00c1e01c03040c0065008041007580700c3c441406100500141d050030310b0149442004400905c00c02e0b41020403005440c1c52001c0e6441180d413100354840c141c1100c800c1d09081311030080d01c1301c09511000d51802516000303000c0d07000c0c141c014003140088001c1b00d20740c00441c02500031020309540c42c0c800540e076070070010750041c08a450b1f0b130420000300d800e01d1079040c8401d0b800c1c11a541103a400403010100c040e0705070006050816a680200300c83c0310084004140b2581d2a44414090600c0c140d40e00e1100c5240014860008654480c800750044034420410300e65018000400200c2e200520020345090407400c40d401000c6100342d41c09000c62034001101c108003003007000c030b6000101120404034854155030025503854184840340300101040001c6141c460800c0b0040701e2041c1d024800c1340c92480c21400a07007650300410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 577282023 1250 577280773 577280797
    0x30f010e091212060d080d0605130203150f0102011d01022a0703171605010e06071107121407060f080f06010e06090307081c0e06040807031e1502 64
    0x2001081c4241c03000910150859808546607040001c0070302d546000020092400d43c20202d105850800505040c008100340002d540c4c00142990405051202907010f105000403190b10400134050095180c5030490020203088421000c0fa0f100d29004034058220302202102d5018030045070500008190082d0496003566007280c400c0188040c201c41c0c0100c000d41814030103402109091003c14404503070342040c40c08103103040f440c15664070048075021000c10816240c3d650b5516235000808800c3c88102c0c0c00164034980f0545501c0414920798450702c1521600c4040b141c0800d581c0e040043d07030b09940e952100507205a9140780da44080c06410282c52803d540e00040c10b0704001841d0448905001d409114181e4644401213000814410030368094000c250381440b039450001076001e0108666444a007045071500c243c0903201c0000b0b0050714044103071900c43c031420301003032180100000c1c0e808112508100c9145032154025000c524810690b0380280007118182020713030541c00941c0082c05002c50340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 577283273 1250 577282023 577282049
    0x504060e01181b06050a12020903060a0b12070f060e131404120305070e0402071407030809030106060311090103180804060c17180909011103040605010e0619120c0506030f01 76
    0x78070043c125101d071500820000c03d070709002c00c1540703c1c8207500c8401081d10502c00189071505040c0084d207401002ca440000b01a11107125160504040703108400c03d00300c40c03005080c0942003800740c4000ca00b60b0300506080140030306442c103075641d07040080b0101c900e20b0fa00c2044140d20340315804c09910b00031070b001d88007844500d182c6090184284030f921701c62951b03555107100b80d80340181084040d42c03001100340c07110020100403030b00014003031002000071807051484964503000c450505003503031610360000003814a4400701405110b852002c441c0b0142c000d280c006584210022080c100c819961405003902d58040b802142282d0850349509103940100750703a1501034501e662644d4680b180442103043c4da0424009502603040c150f80c01e64201c03d41c074002003268840111001c034290802c07a41a80d116858030300401104d840441e1241d0008001c1d5000c08040d04140d82c11005841d05100d4004402c5000b040340382480340c4002e400f000303030030700500d00c42c0d403410328544481c0400001c0c02000098404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 577284523 1250 577283273 577283303
    0x30807030f09111203040e011401110d03050106030b04020a080a0207020a080d0f033902071206090b060306060108041709090c070605011e09020325020f1b060d0504060e0118 76
    0x4c6e60110340c06064059440c1e82001c0c03d802200043d105110705008612009041e01801404125a12701c0595030002d440d42c50020001e040e280c60340b2400e40a24410042c581d496036101e9401c0d40e0160a108002d0380c1d034451803021400a85240c1e1107407841d401001030385240198054800403a20509560502c000c2521100348940441d0f000151a071058111854111080c1401c40c900c0d40d0280e10300540318611742c0e4881d06001c5401c03401c07048442c030765121510b20410045909803034004605a0080c1030510300344001824110020b00050f1642d04040040340704596090121800490301409205041c00c010b1120090745e0058107080343c1107410400081054a0583d00001002440760311000e00d03549004034400080d48050000c0e054100d400b007170203540f040d071041c40303101d9001c40d9801040403072440d02205080c80c030290b030304d941c403603400703000b4034040d656407100b5580696608000001d441d11070740303000c400400b6402d24184055003403004a5020380b8092031500700d10b5001e00124452118 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 577285773 1250 577284523 577284559
    0x303060e0c07120c0210021501080c01020c13020708130510140307051303021011060c04050612151e0a080c03060703180b100515070f030807030f0911 66
    0x2021960014075110a019440c08100400e01c1c4103004a480c1c18150340300355031600801c401815015011000da80b1102840d845c40c81e400440f0350060070100040c0000200340e400003900d81d24400b450707521070350b4205102050346000340c0c100c44115034442507250f620089407582c440014510b01c82c19101d4074482c6e008002081c010000c81c404040c0d941c98242c42e50391040000d81380c40d0131100820550480314840440180c40c0c0e00c03205500c0100e6170300c441c0801d100c0710820929040c0010b04007070b01308400b40020081a00d03007100f030383c080100501450301950740c3e2111001c0e40121a020b81a441107403220401340040c8222a00098103405030380c4141c0300361b101e0b01001c1e175418070500065055407142001076a12486036220200c4034252048092403601c1c1d544a150042c0c00c04d03506454400440001081540713000c00b414112200785101c01e03803c0080940f1444c203d051003160190034001c0000000c0c230f08070700c02d6200100c00c03c0d035040c6c1080b44000a042c28a4030510b4160359901a4100314600d0444038 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 577287023 1250 577285773 577285799
    0x90b09030a14283c0f140c0106080a050f06070c05030702010804140a030e270105100e130c08060a03020112240902071b03081c0b040203010806100f0b220f0f03030306 73
    0x5020303a140e60041800d81301d18950550b10050184040c0d5527180d10200303031010305003c02030000c0d0044000b442100c0c030b4a00d1407070902901034012000e2040007500c040c005200030050300d14250702400d003400d065886061620780841d070310440f06090300400d07484504048d048030410300004001d071042c00701c10350500148004003289262000e000d018000042185180c43e04030b50b02845180e2a280c40b4107641c150100300d41c0e02c2d1803011000a0b544034041001c0040e408880e09030f10100c200c4807888980d1840e000608154078003076403080f1040c0ca0340013948240c0081c80720301120801e0b200790300c03401982c0c0c0e480c504001d41100c40107c4540004c5007180c040014041017010542e904142a40d00d44001e042c44c032900000103042e80d10703034a0349880603182103a0359407010398001d00d08200071b000f0515040030710501003000d98012160406004500780801d081582c04e544031040d10b040d800e8a201c81686200c1d11544a44d84403042c86003c10300c0204070742c50801142c00841e03110f51400c0c0b001c5034070360030641d032a8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 577288273 1250 577287023 577287047
    0x2010509010627020405190e090c09180c130c09050d080a180902070b07170c0406180306050103030306151b0602030a090b09030a14283c 60
    0x52076048a01c00103843c076a40c03005141c1060840061409940d031000c1501e580740e140c0d4404602c1e1400b601008001300c41d0009603030060300c82c00a02003400408001407694100600411711985d490014862502410400f00f014200b00404401d1032011681469014107508403c4600207840007000007010304190050010039a0b0101c0494144204810122000490341c0c400c20b18030342038550b000520718518401064420f02030880d0b1001c510f4441805488448001c2c944071108401c0d008004c190a555020340e825074000c0e24000e03002c0d01c8505011452100190405000036203000300010815801d58010b0b4113b4421341d1031181508551502a0303031401c1500e1414910380c42c0700328a200028042c6d401168845500540060000c80603102c00c003034076408481a10507a80005001500145c102d0f0245520314100d01c0741078a041d00006619030210202c0c000d184c0c2c21000089508c0200d4020806400c208001c998041d00d000710000c0b40c414030310044811070150030f001460348140b480c402e103145881c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 577289523 1250 577288273 577288289
    0x1e0f0105060f1005120a09030305160801090b01050f0d05100f03152d0e0c0a08190311060406060501091d1317040303090e0606030405070e10050a15020105090106 71
    0x2115415609000c00b8020704000101000000c00405d4140d001307101c000c6010f0812200009100d1425103406000c80c0c002400c0035010010074801100c6040e4000381b40ca06480200d2408142c2c0304215005850500560b000012801404103d1501c407003440c1d48428410600d5401c081e0364599182c0e0140096038a5010190031a0f03269608c0f40341c0d10709550016820441010443c0360710301c0120f0f100c26500c1540c84001040aa2200c41c0107000340e070100000710035240211071000c0000c1c0342441c0242c0d42c4502c6103500110501c008603020901d80100c00c6002607550035002d840c102e1800d450007500410301c50203810f0104508a10226841580300c14044104111840c460780d01d488160008080c0d8949a20407182280d9510f1043c0c040324492019000551081d281d51600f0340c200f24941035906402012240142005d108100206400142000840ba01b0700809045604d03030706803d884114681d01704e030381c2040710304030002002020f241c41e6403c15038035603000300300ca42c0710360912909035103480c814082 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 577290773 1250 577289523 577289539
    0x190809071202330301080a15051e04110d08040906140108180a2013020c1504030c02030105070e01030c0306060e060a090f0608060a080a0503041205030c1e0f010506 72
    0x5484015900c000f068500f421402510001103071800340441d03109030003c0c1183d4010081e04401c0081c10821084540a0504244624985902e045229140c80c007501c580244440d0b02003000c1c01081e04ac00c40d902c0e031018003400000c0540307040c0440c2550003803049652491804500140030042d50041c04010141603461125540302c607460000d1110101301c141610b40100d005400c0015041d0000d90b00d4074080309016240c80340010301304400c900e8441c1c1034007140c0d8010840e140b910040440c10b0001524180906540c584403420300b110242140c520007500b6602e03000501403c03c3d08400c22230b405140990f814401c00202800490991390320703116010109032070300b10015003031078480301500942c005480e0034a0299910b0321444c101c0d050982c4404045049032050200c18101007c58601030300c8244000e182a600c540d440c55500d204912600041c00c01070145d04007001018012150800300c1d400859120250103e010000c040360310f03c000d031003449813101034024004c0c1800350328414000104660 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 577292023 1250 577290773 577290799
    0x1905100f080c030903160b060111030f071202071215050c0c0a061a040213031406040c0b090d1416090c09050409051615122c03190809071202 62
    0xa041e0f40c20140c40d0f12868001480140c082901841030000e10034054510341c070300c0c2d0500e08001352459444601c06074168008114005203901100115069107034400ca02e004960300030300c4100e04001d002c3d0003110441c90b05400e4282409426800700e860300c00084401c000310b4840e0121281c41b403152180745030581d0014072140000c00c9103a40704c11041400c04003000c02e950135040010f0126404541c45d62102c84102c1c1c0c0c10320074800000c00b005651103a003c004d040c541081d4451075081c100b02c0c821600d44020025850900c0e880c4d148a5180c2c03e6441a290302070a1040f152a40d2a003d241da06003481760a403080029280070f241c080c40407080c40c03945440000b5418041804040c000740319085d5918480c981c034111005589001780c400500010b60fa0340e24254016a004000d45102c1504105060620b007840d5030301e0880800c0d4207912103141d0340c034442d980128440030781076001c0c4882c484140000350f0150101c4a821444803841703800c0e070340c051320040c9442e00c941000c1060075402c0030350024070b2080c40d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 577293273 1250 577292023 577292041
    0x326040303121e0e0307050f03070803150a050901080d030e01060515071110050a0e0105090f010e0301060e090f070e100e0a02070c09020a110606220204051905100f08 73
    0x1507070242d402c0b00010030b0321580f0382c20030030303115075105003480b603440029280c040c0700090080f074044101c0b4401851a22107192289003941c080580321003907005000d0014040d07560740d14280c00080c14003030070b501d040d5039540c0f20a98843c01500c8101002c6402c0c2803003514000b106201e034000703851004040140d00c64102000b0001030300040000c40705810303c40224042d5a864458141d60b22030696901551041c4200b4024155620340c500b50b4103001c42404940040c0d628060040c1c1041350a00e0601e642c82144400039002d4045030b4000a100c0360f845060181068002c648148050300410880b41d8007a40e50000c109000803c60361f081c01d00b0f40990301802400c0c04009141d402c504002400750030f041d41074480900c1d00c8400e0740032401180e400111440b20303d0300300c992000f0a9000a014001d5440c007400400e60082c4052040e290180d140018203000c8180e80d1f0580d0068400640314542c5c0f0003060909405510981c0a0a80700780c1d00910031003040d0388104242101c1d01010303034455445032290091 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 577294523 1250 577293273 577293281
    0x30504140609040204030b07180e04020621010e150a030b06090408041d221101111516110d050406120608060708060f011115130b01032604030312 64
    0x64a078046010070200301d4507550750000d04061400703040b40385c0060404030300140040c100500303000114541503504003e00c0b00d241460035440368050392180c1c0e4a0188001039000406207080c1c0a00000c0ca0b036001060040c082d000031031241c81c0a14038007103d6a0a5403c01c00484404d110083c040c042040016025082c040f00603600f1a11400186041030744a0708e1400c80345000c3d0070811030704072401c020428541d103915941d50190781402417004600c03a0603101c0812500300350701840e05000c0175503403420401008118100c990502140041000d090281400200c040b2800b011000985049003500c65020b01203807445081c821901c40d50301d080d01c0d01c8030a0302e00000401095014941e1035100050800084c80843d20031040c031b81d66902c2a02d4006c041019540b142c4502604000102640d800325072000903010b16a6004040070081700e5a5050070313880f0350b0218000042c03c10030410000801c00c41d5002446001e040943c54100840d2a0300c0707103c1540b40518403014002800307080d4403800448203940 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 577295773 1250 577294523 577294559
    0x201092126030426270f0f0f01090b0a2705030a0b04080f162a06030509160b0304031205040312050405010f0e1f02040b09061c1112070804030504 64
    0x32245107000800c041e040f049070801404c1a03070000c00409800304080d1100140085c02004550075004510300d14041a99021500901d074000d1604840700742c1260b001c1d20100c4000c01ca011543d5581d07000300e000040900f43e0409445a0401e9045a4448041707425a0f400c4c0a0360710107001401a91000e44842c01c900d1300c061302c1038a4101c000c10014070000e411100802c40f0525002440e05070401034a0400b429286034800341820604a43c0300100e80e100143c0d54004445140c41d0200385522400216030500d08140c0205403010000c20000494480200245108a00079202c40d84c60020301c203104026140304030750007000901c0d11061140c3c0c1d4030303040d4803458025002e40000201d0f4619804004215860390791751750601e512040b0164581c0c010384d80000010380100100b5414980390034094a010f000e040360451082c030012039060305030b840301050003600f98405803090245c0400303040a541031ba80a03046010a58005d01e0015016034081c00c2a1401682d06136109407a042c5000c038500b10300d112000c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 577297023 1250 577295773 577295813
    0x5150316030f06030b0114010914060703030b03060f06090109020702010c03051b250b040503060604020906072f010305070804031d2d0a0b1602010921260304 69
    0x8000c1c0341501c41c01d807243c400a148601030510080d41441d4080507141449000107042220810f400d0000100c0142c401c0c04112007540d08031380390000c03483d0640240c00c00d03074411038061040008104995401440d0300d802400140c654a0302ca03601d810f219800d900c1000406404903410714060400244100c1c002e20f052000190341d190504032800d091410040c2c4c15681c1001c8410f043c075003414007020b000c00580145078028200780f800c0d00e4100070035168a030040190384220360106400308140c8403682214103041c5d1000200e02c0b485000c4454482c0c40703444402e40d09030841c038025170840c154002c0c4280c030b002d40354581302c0e0541692996000c4030301e00300a0516240ba000c081c480400700e521200403a844800c007907508095604000718681c942d80401d100d01c01d11030100c030b50f0100045440c0c2c10455182d2000786020800c1c442c940d00060310804000e510240c5917886203942071100400544c0c400111a115200c40d0811003500c294907044600040840d02d00c03a1802c00109001420f00c1c41840d5560b480e003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 577298273 1250 577297023 577297031
    0x70e1b0708031521010b0402041a2d0d2009090603120703020114100e040f08040e0c070203060a060f1e0302062d0f0307050903100c0210060515031603 66
    0x1500110b8140241c0340b10005104d015520101100c04007030007021560b20b01901c04609103403400400100d654400e1b480607200030000540320712081c06907030311011000b0800c003104400c422824083e1049510907044007201e05d05d080d83c2048001070031180c440c1c0144036242c6250a0004003030411907032102c06824180d01d8443e81c032810720141705850180a07900d0107500002250601c20740703010151310004145110100003143c2c1404201c03602505282c100390041008203a044003450003041074030607038201d51600c0c060388041065180a4900402c419031007502501c1050300c68162075826150140961000c4422580091040e012385180e40c014540c19001007400b1140e4035004110a41d03c4814001850b50001038444031314282c40008402c0303603120326046032902d001c41e1072175601e601019083d8010080c0008400303d443c0d0301002100c1401c08420402c1041a140303040c0690b4419171380841c01c04041c200003000519182c021280d000416131424018516511a00c9041d0028102046001415a1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 577299523 1250 577298273 577298311
    0x1104050a090b280b0d0b130c0314010c02010e0c130615050c06160507020d0302160b030117030403051504051603050c0108091903140d0e070e1b070803 66
    0x10b8540c0250043c00780c202c012081070900100c90314450040704819211a0515181e40902e45802e640f20b5042908022408a40c1d07d450743c40001c19010100080d048031030400000c0700744030340000301c0d0702d80908520080004000d003030001d9007610500501040160091419484641092050a0325148500ac00001e045481d10414006440c080b00c214001030f8010450700784042c0e04001003500600350702801c4241302c9a0210003032091044010003400341600c0c0c0c4084003054000c02c20751424010002c100001c80b611403246800e550001d10071030030482031306170040f104054048203c9099a4000c0040c02c41840c0da0412084c020f04050301c115664071800d0141517402c11401c8808002c3d6104070003501c00300981b840014004100640f840815400c03082c550000d180d648980354010070b515007404a82c841c0300c01d0342c040d014020081240788040c241044214005404910a403c2d100180f81c403040e1a00c8225600004040c0c2ea515500365290403c81c010118841c44003940e880000f11109140c5961 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 577300773 1250 577299523 577299533
    0x30f061602010b0105030c090d0c03080c0606031608100c14040602070e070807120905010e12030402040507020f0601140d1e0507090b0307260f24041104050a09 70
    0x1400300e5408010441510810400c20380c28050807a081d44246003031421350500d031400d000d603840b450382002e01c030300381600c8a1802c100840c240700000b56081035800b91110000d208840d02c48800700c49462007409080c41311030b80840888200401c3c0c0e51860300528000c006940c030300d4000c0c42d9455860b010321034030f0400c41d01d500c40c0620041c405813240394098042246000020031010801501c0401400340d0f02081282403a88072052540740445450042441e00031402e20b40d00428083c0038103031440c01424100c4d1054141c0c5401103005920a5400304103a5446680482c0c40c0c03440c0c070311520b007076410800041100d10302010304491141d0008100c0d040e215a15600d103d40d0f01e4030449950707468000d0800745014000144082c3d0000d1107020740c24851791601c1e600003600d440c91070080c551003110b0800d800c1e40d10700d0ad0b050030841d02a10042101c3c00c6603505030000e07036103219402925031402c100100280720090040c0c0c0290065030b001c121540c002c40301600700000341000408030400306503540344c0000864 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 577302023 1250 577300773 577300783
    0x60f1b080c07021507060c020105010e04020103020703090e010603140c041203050705240f090a021012150f0312020a0201300c03020301080d050408151b030a0606030c030509060c0306030f 82
    0x100e4403540343e17078000b10725043c0140c40d04c4180400a5903d0b0800400071500300c10440c9501503824a0010795505052805403070011041d0041c8822014900010452540541c00b8107003800510580c2e444556a24409136680c1c4214011038000c06036403000355000902513005000000e21071000d89001000b10843c19120320b416000100d040140c82040c000c0c5407001001c4503801140400c094401d100481d0003007040901920a00c00410902103844218017500b0f41c0a207921881d89010300740490f40d1042c0c0b9860004c180c2c0400d4075038000d41c2500210399800040c21100c0f10341c0c1178441c003410b94400e10641c40c84500308840070500c1e202480e107403200c848061241c00c070000c2150f10016140c4d410220381a2030f1184120110040c40410402404041d02c00101907404080d80040c2942c40d035165000c1d00b4103082440440c0a00900c08014030850b000c09402490540d040b6690800540c50341890450039504e060f0380c41c81d22600300700049180c50a801d40195484007000d01240c400d5007030112064600 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 577303273 1250 577302023 577302049
    0x6111603020604031103150915091b120705030a0609030311031003081803030a021516021b04060b0f040602010b0108010b1206010203210103020a0806070f0305040302120403050109060f1b080c0702 86
    0x5030304808010844a49010110b640080c0380c68024a220000a2103640c00802c00c0bd415910a5500102c058005031041021401030000501503ca036090246840c0000e0002024101c01090030031010030360801d01c52081e85d00c030301850039208203002c2c03558680064607402414050003441c3c0b00218000503031010001086007900e5940240740c070411a68400f07400000141082c91800c40c1040000b40e070b00d5000a20b00440034003c1e4004e40450f0003c0b000034010041c903440200c04a902141c406510250500030704101d42c2c19800901c06400010b0044035120024011210891070501c200c0c901e031780e002c910090380040306004403443c00e03806050301903404c0c460406c0d4600308202a0010300031800c0168550f4005c2035044020f250b035090005e40502003a1032100580c081503543c0740041c003898401c1200b8069410f202042c1c6035030325260704010340130f00340944040c1c0e0160700b00303513410500103414070032803281c41c1d1618000c40548040e00c47c111894000904400740d942424040000540d640c0700c015094 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 577304523 1250 577303273 577303291
    0x90109021e070f170c0601080706020a0b06040b03070e0703060806130615030c1707050d0206042d0308030a1d06070507030509042c010e06150105130611160302060403110315 76
    0xd81c5d407641816031800c40140c000b081c003030304139100400c4140d4000a04004141c0e005011041544e1050701060042c41c0c03e1008690501c40c1440014100c0f0000c10014002d0303000e564288842030701e98500e96901c40068600b501240e40024010300490780b1903000d164409080030426035000c5e50b9460303000a0401ca60048804034002180d00c07032003108104081d0000b02400d9802c0403001215800040d014040d40c0708049078003110354190f01e000140c04810409200c51108144491600c038184030216400850708001064039100c03946206244540c40c40c1c0c2829074020092030b5030356440c0d1007112141c0040600320280b0a0a100d903400f296210701408014001ca05030348003020561200451050f40d21040415841c3d1504440401c03000e004108190701c0281941520740c540031040c0100d441d486a01d4926a03001148000131a8003540707c1a0708000c0001e113000c8502280b800d030030208281065100c025400401044100700040005541400c504001401d07541da41303600c059503049011080310f80b061 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 577305773 1250 577304523 577304527
    0x50409060e1b13080a080301030b0106082406091f0e0108040c0e1506030a1a1e040e030c160513060509060d02040e0f0606090109021e070f17 62
    0x1504450303120340d4005010310a20a10503081c0120303000405201e480914212000000d604071070000c411020100038050f140440d900706500c0d00f0440450f07042070004640d5001c000000103a0148540801401a0b000007a0700c142805010300e004a0310150102d2103410440c14401e4524036a42c04201c0c5480604030818943c0f03150803000010000004d10725000d0502c03103140140400f04016441c8641580c000700a0f54004d03031070740540c0c840200c0a6810940c6c2c025000002c11141a90a800c540c0204072400d0340c82d652540c2140811051404401c080c00e24010115040301107860a9000f2801140c01002603c1c07820000b0418035080940302d40360a101711843d22003c100c01d080c1040c00320003083c2a99410048281000001010000e014111a10a40d45003210106540d600e0344902c040001e05400c80304010102110703e6201c0904a40035442900b007a400010100c41d14001c54020403000c0400002501f110440d046054000001c141d541c54428440c040c00124205100c4c030f098050748040c0d41e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 577307023 1250 577305773 577305779
    0x2071a0d06090501180f02040302041b0e090c0d05190603050f070501140301060f2c090a0212010527010b0306040b0a050f22050106080f01170a0204091b03030504 71
    0x40290740c2a940300e0404180b41000400204a090400e002c20a01182001c240c03c0c0754481c81ea0040d00564002940c010b15088010325007211400c0100e12400130341e110004644204001c0110440c000c6400c0070060714200065125516103a010f250b10580b81c0b2210030740c1800280644080b00c0c0c4a4004846652241a4200800c070742040140300408003403a0403802000c01803103551981c00107114074428000e003010303011646e80c001d00341180101c01c5405442e07000390b080b11000203c0e0003106039082c0103c1020ac08200300001a0088511107410300303410345050392905e4103010300f074a800c1c0c800a42520400c0f100742140003011080780c1c0200b181c44844c5484c0c0c1400700c100000c403500204079034410759103402c041003940c8442660052988044802e10603c604500301c181600400340d88074000b141c0341100200d01c882d0462142802041c401c580305c607650b0380720309950601610101c030402d9698050b65420b4018501900002c8526215500480c04421032140c4458406129082200030031030224043c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 577308273 1250 577307023 577307047
    0x2010c270801022115010c0308190c030b0a061704140a0f0303090201080903030403080105040f0b0310051036020d090c03030f1403220b100302040501090b030303150102071a 76
    0x10075006064542d892445d400d000002826004010074000c041c81540400201701941c10702441c109240005000d2260303845042d801001090204401403150001e60400b00d0001d20501042510401100d5019816212502c07407212108a081150809228004000d40090400c00031099000d210b42c50110380c4407071502c009007800d500103080c000240e00500406c4046584000d21358110b0310240c500040e240d840c81143d80c042c0000007080d0f44c26104a50252252840321307404140b15404030b42d555a50036403110004d2002d4111080800001010095494201e180c0c0c0c0768040084048080010f142819540340c410550762056010380700d08103406410005e060700b103040000c07110150320700320049040c4207c100c01c25000c003070721340c15144841003500b2151074000c103100300e403190f00310b03882c0707101880c02d0060368014802a0004a001d031742003c00005002e070302d0b4051a420510028003543c11990350070503614414200420490451085860000d000386003d40328158400600070601d5030740361072280c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 577309523 1250 577308273 577308337
    0x1e09050d0903170f1b0a1208070f0311130f0503060603030403020a06120225170a090b0f0c070b030a0b030c2209140c0a17030306010f12050c07020f0102010c27080102 73
    0x103482c0510652308200168194041804142d6122604000460020581364a0103a000380305040b081c0100c05240407920f0200301c14900300300d501c22011103445984000070300d40c4038041c501c00250042c81c414420300000d40518048040950b01000050400b503405030030a25034515814001040c8036542c01650070311801c2c8070707102c4004405079001454120810401801e201440c0b160306003d840103d24240510030304000c544002c01104101d41d019626011204856841510703102034091810034000800d090100c0e10134020040206881c88007410766503410410002101c03000d400035541c0715040009400258143e030581c480c0c00080190301c4491090281f160300d141c10280440d07542c00c0d80e801c81c02c40c0010440364481000e00c0d004200c0311a039401901d0500640c0381d5540440d00704400c202400748020064450b0500848400542a00000041e4222038000340008000383e81c3e03c54000100082105c0f100350040240c0d41c0c90341241d03a4005060890f040b5407000d00e4411000050780c0302000e43e10031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 577310773 1250 577309523 577309553
    0x90105031b0c10020703180e0a0f02070b27070e150301020d09030f090506090a15230703030f0e060408181908010c08070f0f031e09050d0903170f1b0a 66
    0x18076a203180d0910503070510020006100d40389c05a141c2c007140f08155950f40503101c2042d40007014403110300b01440a0490401c0e090080000c03041088800d0101d00c44c000392a41c100ca400301c840ca051030326590301303801400010040c080e03011364007004440c603035545a03c01c141c0124025a0340c0d1040c02c0240c0c5000b80440000e600c214881c0506010003000713596910180821112186035400300c041d400740b0141d5940d030b42601218044a0809118030780656a6001052200c0c460b503010011442c0f03c0d400801110150720f011074a540c00b032000900001c601c0c1c00100130703035010b6100c0c4a80300740c041000110244514440818070500161040041c11024080c4040c0f2001d6030400380054940410300a151341c503000201400c001d903054800c8912802588031a038503100c880e40c00184071000c80f494030090540140202d90030b1250b41c004040c0300e88911900c40540c0d0340007000700f102940c2038032054801e40004c040818080310811411091109101b031355022900144050412002035082800302502e8007a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 577312023 1250 577310773 577310807
    0x3121d1c02071403030f0a1e0203031909120f200705031c050a050310050402310f051e0a0f09061a0f0c011d1b06090105031b0c10020703 60
    0x721000841d6000b10684446c0080c0d03c0d5229224001c110007141d008030105003003661100d5405961000c16400704c000c43c0b06940050940d010a0a03030b04c0740170110380031400c025260014016008103007034440d07001c103c0010300300d00c0c4c2204450f0840c282c84642100e0341c0300d1603040d52301c0b480040000341014000113440f1303034440c3c48040e1001c2408201428034851030605004003c0000001051403040106520107407402070070071500c0300407000103040100c4403140c412401c0c41d0854030058030341e55581c886c50b0170354503600c85030f944881c50241400420032030594101c0d004400603940c1c1700d050b107401021800808904007042051480c2c41035002c1210160b8200c2ca42030100010448100004c110858040c00030011200d0f9807032401050a9005122826a46a03440074024452003084d0700091203070100f031509002c00c4d20340032802c0104142c0740710741030905000c60014000a500c052511046071a0708034441095403624410715081d0342046004013820011036800700d1600241640103042148102c840 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 577313273 1250 577312023 577312049
    0x10022a030f062205070b0307080a0e07050f06070f0f050303010315050112150e1e010f06120f030c0b0f01030605060607050a150b040f02032203121d1c0207 68
    0x5000420725150915540c1800f00c0385510345042000700812114000b0309a00c0c5c00c1d9a11303401d203441c0040c40c0420a582100e00c490500426545880380401c15600304c480042401820b92004007e025294102036000e6071030381c1c200e406d507001107103a0f640f01d00c001e148500040c0d940c030740c1545007041159440d8040000d0344d40c9803400500245030f40801440a964100c1d84035010743d05030310b41400241200003000f1003107004450140040300140f000300c0a0903107407030000388400303003020008404880051145898600100800902090303455001ca883c480c02445c0804100f081034644000c40c0705c0075035080124101000042003441010f11505400020407145541f40c644292034482e41d4194004020380740403050010005103186950001d00b180740054022702c640d41c2c0410440000350403c44910142c540c6d08994084c104a075808035020345603254841039007030303035400e50804002c2100581e001c01c801d140100c440e6600004100e0204284500c00e0301391240e1541ca00d0007824440c2030340c0032400014007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 577314523 1250 577313273 577313281
    0x10031704060f1211120105040b062b02040509070f081b03040209070201020c010e0705090105221e0f0c0929030901020403020d0b0f011a040510022a030f06 68
    0x100032200c2d0500101c40c41c04011000c030b40540403008201e9055603000c041c10000e1341c4a0000e1640c0003103812500708913030405c8000800d07014408a44030341b952110341d90614040800d03070040e4403100c00c50400c0c041d440c0141040d4807440400c1c10300c0819144e003c040340b100b804c6d03030b0001c1394008565648003e0001c00e80c025692210f0542800e408080d00007407184480c1c60008a0840c0b0075819152010704000080c00002d01034030815031190b980340180b034003801a030400840c0c40d0411a210b401040c1a01c154020004e140030070342d81c020701e00b501448907440310f0054002504c01640c0203021003400c540500003140700b107048018140361032039403218030300108034000c5064605210391400c117085401c818080c3c0d0b070b0340e600070394a00a1146800c0254402100d010303140038050410003841c4903215841c20030000c0d9880706442c0700402d0400c002e000104108202c1403101c0d04243c4604031001842e401140c200d00d00940f034030484a400f03a140d48060b00f0140b40c1081451400300310212191401801a142c00c2c28 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 577315773 1250 577314523 577314527
    0x70c09110403080c0f0105010b07031e050304290c0c010f1b0507030c14030a0207290a0c150209010909020f03040609030507060603060218040219030f06030b1003170406 74
    0x20390310000c1e00400020420301c44100085c02070258821904000704000e68595800724441c1d04188000e400082c222441c1c0c82400c0801c0c0070b02c1c4200d460903103d0904680c1e80c1e6070303600e12015240b010001411404503015900f1000080200c2c045d0102c1040b080e141c0341e100542c0360840300c56181e00b4489508143c000c0c5240010010314110038a400d181081c0d07988a00e080641c1d4506419500400340c10b0442c0c03404031b0400c03000c4003615000d02a0f50945440950311103000407003c2d16480048221040c2d49064644220307204010b2040e400315017003a5501100d59280c0741042c00004104d044181d8001902413119070744020454013404070907508500f0a040c01d604400d072400700600003000f0035500c0c0100028580203105803240f15030700074010300c002c3c1d0322450b04e1030180d0800c0c0c0050740000380d900c0030085246040d00039601628124498a43c0d24003541008074040c2c210000d090040969513600400420701340090103104070200e03110410024914a044ca44031080300160101000c014001403000907 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 577317023 1250 577315773 577315777
    0x1f0207140d020f0108090a02031b0117010f0902070c0b030907030506130c03020d1406070c02010314040201081b090a0e060a09090c06050a0e0409060b0102060f071209050a0803010803070c0911 84
    0x1002860068203698980385034500d04840c60101079450700c00c0001d29000100c0300344104a155030b0030b0741c0e00d011290311210332222a075428041c0b8079020300300400900446e0718990142454500440170030304003e40da58400a915070050740c05424a400200742031080c084100f00702900301c80145501c41c0303140d6107901d071202c0386101808020312410340c00040c0424441c0c1d070314501010300120b0082d500d89040c94031019149407ca0601240881c0c100300740c01141e02c90207030000d4031554068403070600360b60740c080d544403078081e401e20700e44440e80090017110307060789030a50214050904480c04c05100e041140811081180725403003e49994100500d500000300b078000e05900302c8a0030308145482d220300c400c00317035584402000c0080e0450304e48191103003032003d03d42101d03420300e80c00e80035140c098684080102a215040303030041c001c0744000342401d04c441c2c902d0707001095290054081c3d9941c440250340e1040690303c280e00003000742d0b1010524a0074080c94460b2007000348070032002046410509210142d680c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 577318273 1250 577317023 577317049
    0x103021305060a350c09031e07170106060f18031b150807020601060f1202070b0f010b0c0a0201030203150d0507060e03010203241f0207140d02 63
    0x1500480c01100c500c810400300405048010029500c454001400a0031032282c9000805200c0c850603100c0f40e24005a101613a2200040401c503281e5910920114420b45c0b128a40c90382520541e84010b1040741281d0140c4d5002e585440034160b414501000b680764003110100b001d80c1da0349882d504003d03c6811045203500310a181c20b146d400c0c80c18580510300e000645034400350800c1c00d141c842c202a4440c4070514010b40d481c0c00008000c18001e03030700c1290002c01c00c440907409644203600600c44079010710039010f5512480d00d044008000b9029a4400742c1e00041d8040350380240c4441802100040c03054107074054013001c05081d0904807101d540d19a80e031134004010b410301d58000085050300c002c0b030b4145114950f0141604251910714a01030355201101c1c030518000411009415040c0d10301802200d0040840b900104c540d070021030310903507407081c0d04800706a11420341d0303241051300c04442e88103503541710050b00a0034071180b40c0381000a042c404100d0740d0307108111910040c401640c40707040460329 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 577319523 1250 577318273 577318277
    0x100506010215460f0c302301050102250603110d0e06190b0a090e01090c140a090e2a060408370b0c070606030b070f0503060f01 56
    0x8420704400114034a0503c00c14030208004040b400155031a9440d04042c0f002400401e0400040703120340d204407411120b113400440e21785140141d1600015500c61a0004034100420000d00c2d01004120003c1102c030400300d4150341c80d20301c0300400142d078040c426024551180c46202034010111031440710040228041c2806040e40e0b680b00481401c002c0c0107070f41c10704c1c180303075401c06c03e02102410300da541d0813041300c042440901d0a40c0b500300707020403401841070405016202c680b80741c0c10010040094000f0203d0f1f00f01641d030303c12180c400320f902e4080b0107008140c440c01c0014000185402d01010703410540210b117031903080843c441085080050f95030f402c100309103401d141608081d9441210942d041e03c0113a070090b40450040340104e030205140c211956550a00c0f491911200c1340303d0508404146181014134031040e000c1c01180f040380307000307620241001a081c0b6115140e5210003c445994005403080600807007000181134005903025100c0070b8a0401d0f40c03c62034040c2c00035034010101d02c0701c541 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 577320773 1250 577319523 577319581
    0xa0f0c03020a0209190b01030b010203090103020705100510031202162d152d05180303030f01030b0a050f01150903080406030e0709020a020303060409080903100506010215 75
    0x428580300b84160786601c0d900030b25120040c180171041c81000d20914100c03600103840e05d40030b02c5180d07009218020b4020010b07001b1703504002d41c0c00e0055000390420b40302907801c1c7c0200411100751013114070030644142174981703001070302c40d04509108031402c00506851f419940303c00809004044510400d0007181ca8801d01c0030070400c00f41d1182441082c081a940115007000326001c5500d0a409451080c04907183d0742e0204081c0003114015121084011022070703181c0c0300803800013042c0c07181005003203007a0311a0381c22401084070000700b4a0342e4030441c0c02c2200810b07070300014000c0001d05e80340d01c0c4e013000c9000c509100342c1c00d20500100780d400040c0b0401e0a90010664010b502c0f40c041c820800003140c02601d56922565605030203006402120301c0e2074414041c2d0040490344280030300c20b8441c950415402036003966510414407004140150003940d0307548050040078200d5030100502c0f290300340c106401042c5d40c00e2481c00685003001894108081c0164802000b0201c1e070351400c414006048030440742 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 577322023 1250 577320773 577320797
    0x3020f070e061c060e031809010308121027060905152101061d1605040b0d1b0201061403010207030206060f0f1017010e13060902040e0a030905030d0201020a0f 70
    0xf000111484100600d4141001d111a52002d8040094664081d0b980d442c100c00007482d41c10405005c509010003002c9910a2148002071007030380149903400b041034480c81400c991107489001d05c8c1d6400d84c11240c0e03d045054620080e458603401560b004102904003403209007800103000e6500c40c40c050a00740a949105a00d8441c10f116500400d401481c1c80c0c020080d45403036071000d444282940104a44448480001c60745500c5040207460b1084100e503035082c146420400c6d170307126a034060091140460b450b0000e030640c141d40c00340084041da4982c2c000007800b0b0301d452650268011000b642e14881e900c140300c010042034000c260103078018011110141040304103400140541d400040c0b480d00301c01c0c03c980c40e40280d0b0300101d0445420702446105e10060380e8400f03610b007805d02c0440b008005280542003500010765581c02460000b48000c001040300c0038581001031408a008009070300003001039000708640d044c11300540ea0707000c00e980300951030624543c1025100e15200c58040c002c104407401c0c00d07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 577323273 1250 577322023 577322059
    0x11071a0705130306020409050612030a21110c0c060f0a030f020d0501121a07140304061d1605060c06070c081306030f0e0a02010206160e090c0703020f070e06 69
    0x440c51518019405102c9603200c3c2041402074015002c5c00b0007070b40c9840701041c0e4619200301804000c50360a00150318210001900701c61805030315160790003e100c1440b8540bd0000a4015807520958413540d168440700c880814074a04480005030034055030080003810610390301d40003140c1d0000f8a501380401c07421007201514000303100d10351045040d14904030001c02d6141c040b280b1034003594055004d4203031055a420359288500d40a898240118402e40041c1541e929018080c41e40540500400200b01018a4280c90b403c82c54040225643d0054122414501000289240640b10a0b6499402d00300b90300d4803159511f002070813a00c24007031804c8440d0100f0807803204484031100e1080400340020303a03e030350190207088040001e821a5080c000c0a00140400240c00440541c0580c02441c0d030791641c400b2109120103210000d0100465a401c0503c962281c1d00603900440361080425030712045820020b040c10510018061140c00c15542044000f2211034a580c0002c07040300d43e603031062134010721 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 577324523 1250 577323273 577323277
    0x1f0c0803040b0f1503300a1707030e0318041e05010609081b04020705070306060b130905130602090a170a0501060b0a020705010e01270905060607021302030a110403050105040611071a0705 82
    0x6d208403031030303002400c90344160b8801d6003000d0071804514084c1c000e403580031047c1d0a0b1180c0d005050720319032041c44080d20703901d6882d036247c12252000d000002c00742c02c80314400d9150f04410500241c955292401004410b0f0300c220b5903401041d5280161440481030004600d03808401030882d0322454000c10684203100c01404680001c0d541f06201b0803901c0d590780c41003001504400e0400640c0e681c241400103241c500c174090184111170900417080c5981d1140d484d07400a400c85412590862400800442c0704103c42c00e070319002c210881d0040140522500e4418251012500644501d00040c030030b0090813030300019107005460090074004144021040102c0d060401d403c01407091710010884003841041e22030417401698141c040902c001d68507801844614130440c10006d4101038004150769032481e19a010316084150b040000c990541605c80306441500240c20698507655140d05100c20050035205a030301400c503140085051400030b880d501d8600d040d007900b40e483c4000c0c00b00000c100a1242d01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 577325773 1250 577324523 577324603
    0x100c0804121b03020609121213030e030703060218010c0c0b1e12151c060e070b07080d050f06221410091a1f0c0803040b0f1503 56
    0x2a0b104807040007070800960341c2c00c2c10707104c00005003d201580400c400c40310086a10b8501c2c420440090741d15802d0062805005a00c000e07010401d5141074503038541d409001c1600294000c0320056169080144010000300000b000750b03042c008442d44105c000303460700074000e04982c0c041e9880347d119042411040e80501c0c0d5060b10016a1034009842d150004e40300c04018001e490780c0a03000003844c00368080c40007014144400191403590b852441c000a2520b4002c070b03a00c81d5500c0283e43c3c510b80c0d2028145482c0d00700d03640448030745201081540f0031074101e1041541c80349481e0752881c00350400b0004510100090743d4841003c2c140815002c070b5054554014200c401100b0310242d06500c0c100b80b014a401e141c601682031050304040010b80942601c101c0f20307440c21001002203001101c501d44088160851141510030700001301c4040300481c803036038003446c032450250a11141a1602494000150000400400104001c1045c21501c0c1d00c000544100b009181203402c1c45c9001c1a000000d000c2c1711601c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 577327023 1250 577325773 577325807
    0xe0106031406060405070e040e0304050907020102041e0b03010311041b1101061703030732090a05030a0b0601050c010b060d0f060e09030a0e06120f0603100c080412 72
    0x54000100108003240c951000308081c00c1d51620740b1000108016150242e680c8000a40c1c600e032280380d10b1505500640365918103c00300da20385591500851400c0404450303090160b5808101008140c581d0b032100310011440e858900e031b1040c03d0001649040c0410300011b400403090102291243d241d9600c8004c42040d14140111100c421860007440090100d0b14001c49500b00500058000a044c0f1803456441c0741001650840d0b1321800219011581c01311000c80e49203160f141100020344580c410f0b1402e8210340e22145d9100f074024280850244181d02030b40c0254407070021040400e10740117806411190034030f085070f500c881c8000e906000d040000d01803980800c0c0042e0415548001c1c0d403258070703031400c814800e0001c19501c140303001008100700c5030703900c107030304100925401a40308140d2504947c3c0003d081c42d050441d01400510b4501049485108050b0000c0611800d4582001354000ca0000c15406214005814100400c4900c001d8001014419040008103070a405030080d814406418 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 577328273 1250 577327023 577327031
    0x30c05010e0717032503050f03150a05100503070c08040b040909020a120308010902073e1507080306040b100206040c0e13030e0d0215091504150807030e01 68
    0x40ca84a40e00c8850038803408101120f40024040c0e15500802a00d511034500160100d00340d40200501e0f100144480040302005030401c011860114103030090b6002d62207954074801c4141c000014041e1000c1c10b40c121521500c10182c4503240f2980c01801c50354408821710f08002e0b03000c0280781140c06e0b4044c076001940b00900208000c260381e81d9075480012551700031241d0b04141550f528103012002c640c0600075000501c4003005204404154000300742d05807142c03003416246010060501c4003041000e482030450704025681113288110303003811087c060301c1100e80c200c110714a00080c0340e035441200d000a040c1d080200004403981c0e155030122407140c40107800407100d101141002034407031380200c80803102c100c03ca0102040e2044000425441612243d0380c028107101691400d0311074030014181641e208101001d10401610342a8031a0410040e10101c191a615050304004940e180e0300c0001080c0c04080c0010420145580c3d00060243c00d541000304441c3c40d4007070101c0280c00d03101e6040241e03600b8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 577329523 1250 577328273 577328291
    0x11040501050946120201080907240201150609180906051312020a12030504050a0c0b19020606030a08070c09050c0a0f0e01090302040b030a0c0b041e0b0301090504030c0501 75
    0x74030760209074188900c11040f149080d040c1d501d90301942c614080c0c09454913905507160015400340b4001c0350000390701c1c42184c402c150349003614040c01c0382d240030142040c0045485250340300d40900448505003003e2511000190070a00000c080310858441c1c24001140801d403ea0608282c0d8000310901e40c00410911081c1362258108202400b4850200d4001c040920005e0381e503031021960b10402c0c1e51051883d1203103c0f004030f0842c0038020140040c1d60a001d0588842c1c005000c04503544d004100400d41c668407401c11414508000e44d071140b101e015904003108101203940c0106912002c1984884400d4850040c3d062001031245603410000f0020300d401c051102207007103e0003820702c00100da960381032811080b00707080300d04007062640c1c1070220b0071510050005140641081c02e03982c0700a400c0320817800031912840800e00e41584901445440040c0070721000304032044241030a1911222041903d20707010f10343c401c0344014801c08043c1941c500c00700301010b120b25260b500b0150802c0084c0300c0244 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 577330773 1250 577329523 577329589
    0x16140106060908070b0301061409062b0e03161b0311040b04180212031e07060b0109050d06050901091208090705092701020d0203040f110103110405010509 68
    0x20034003980002c00d80071003002440c2003001580308195034411510344e0a40e4680072003540d100714012614107420005001440391621424041c040c50151050200140f070b900c0b9154880340f1141e500600c461505048082c1c01c410400001c031050f032600c41d00c11940c680d40c01e04140c002d0344159642e1105840c00b400b400400e22281425003200c5450490303040025221030760420084a20319040c2101d8155102241c80261410240a03284822810300752498282c0d0344401d101601c442003c0da4255210104948090041d01c0c403030081c2000c0c0070700341000043d0814002480c5000300380801090541c5032000904810300070b41004100702d80c0b00398240c2043e52622009080310f041121903401504ca000e00c005114a490b07401c260140111144603844402c2110072100d85802920903800d10b51340800090030400c030584002d600c541d020740402c144070001850030241c0c00580d40030160401d828000341403211074180702110201c5409083c080e656110050100d130248026580804282c0002c10040103001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 577332023 1250 577330773 577330781
    0xc050f120a020f0304150c05151e0c03040215221d1b0f210a050f1f421b050c0402030606190201020a0f020a021005161401 54
    0x9940e809075400f680c1c1107418541d5034050391060402066140014030710540c0203102c1c81640b24000c50607202e84450741405c0e2903480c03605840840c20b03500c45c03070ba1440007100310b181c150344c01580301c82d00c9615504042c0c0029240600d5041012812032000800ca1084117960040d103060843e050201c0c50095507801120ba486100304450b402c0041c04200065195030f0304905c081c0c2007039203014075181408800300000407103800c075030f01d80302004001c040440e050450007040f1a00c11032107804041a01c2ca04000582c1c40c07841c015082c03500041e401c014050003203d040c004c1c42c081c0c07410002143d0601c00c052041c20002c0380c00d202c012600002480f411025000d0940d13540d0800016511000c003055007005c05a1500300c49802c000d406600700f100c030b1584c5850941c0043d60800402007919091180160709503c01841207030340103000d40c1d4005542c2600c2078001c040304881d4112030020f071a04a1540c0c01191040416035140c40c100040015600b07500c001d001c1d800c4103129001504e512030a84903009240c024 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 577333273 1250 577332023 577332037
    0x1905250c0213090507150302040e010306020c0f1501050f0f0d030e010906170a05060d121e0507050d0c21090e01080601181a0612060a050616030c050f12 67
    0x140d0b01c24075a00240001e500400341c0d400d501070f00900c0326070301c0e05400080d04c103400e408203800c150b020007000a181e80d0450416020794007811006035140c0380e50f40c07440d02e00004054503041c2900701141c181070100029101a0440e00140e071008042c624082c0000c20070010502c900c0d622141e4800307200241503210315921405d8100780c075100081d503195001941d0005000c0d882d00d06004040d0005004048681c00440d007220010300500c403800040d0f51755085902024076100005000001e090f008d001000d0240d51034043c5500b02070380b8100c2c40b40c07215902c3c0c0204c940c16406000d80707180003030200b0030b080020390309070814140d14440022a61400824801c05403043d6065040c03000000300d420307400030404504075038041050085e51494596000090b1603006060351042d410000c0f91091500c2d8880282542070860000260700e25000017004003811554114500416081c0480c1184840e40e41e40e001000340c042c200f0b035015100c14540745107042d96103124074080c1d0107201d54000b80441070704054080c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 577334523 1250 577333273 577333279
    0x2150403080c060c0c0a2901060f080c0f0d0207030c020a0f082b1116060302030703291c0807060b030f0102160b060112050903040512061905250c02 65
    0xb0f640c0758400203403064040d003000e0b920325801054401c03000031198480c50701c5200418004001012002a40301f07000402644602c01291140500090b041d5010000d264800400c0411074141401904110703414003500804441040c0d00060390002d240c01501a000c1c1c095004019411140c1c4541400100002501c6050118400c1003086c9201c20a121303c2c2d18083d143c401e509007a0102e0389a401c5804220a4401074018010080340c0f0039060941c00040c0050f10f0b41d07031009a500d041c0f00c00000e00321500e00c0d1170003510900680c5032031522402e4840f001401c00f401c4903c03000034880290f00000e140c4010000500600000610b1020030500d81c1101c582c0250403401e0b2182101c00c0d00da51801c0c2d00c00c4801103c0001441000400080c0b42c4212594101c41d062600d440404507a600c10001c80b201982d210003c0d900100c3c04001a203411081420440c0288002d05050b00703001c516200f8500f44403a100c160b40c1c1c0c0b20310000d0130708025030080d890a004040010340100ca482d01000d084412621000d81c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 577335773 1250 577334523 577334533
    0xf091201020a0e0a03020916050c060705120603032b0b1306050102010617151801090606080705030d050f070503072108130f12020102040504060b09121f0902150403080c 74
    0xb498075019480000305c0390003800c5001580d17100d0850540c0030040110b69002c0c8082404680c0074000304000e000c2c0710750b2442e1189940c4d56100c40f44050703d09402860382d480382e0f10821a0300300c980090b000d074001d910001d4091004503680c07021000c0c0541103010300e0540200d100441010410b03802e40100b408c80c1c030282c008222168413071221101c40d0780c0840e035103002544401b29030841150713210803103680440c80f1480e8110f201e0302410b415081d00d000b12401d0701e0140d1202d5040c06a900d042c80381c0c1008040c102c00070106c7c1c1c214120090654092100006d4420b840404c80e401884000c1c8101c424466211080c002c000c010046a140c245a09092440014600c103000038003210748402d40340c00040d08807804a03400c650380c1d510040c00440c081e42002c115502484001815185c0307024070406032107002c95007a10f0b03178401014002441c50404c0704144ca94044103e5076540780d4a14550740d551564890040761358100d40c0041744d0301101915144502800c0000c000013400f0188001e00240344a0b039050b10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 577337023 1250 577335773 577335797
    0x403110102120f0d02090d060b1005210613020a0206160302040e0c070c08010e0a03020c03060411060a090f151b05100f180305070201081003080f0f091201020a 70
    0x240e6602a00990204a00c010000003c00d42c3e1840054102421107003400751a14502c1004210540003d00d411a41c0d00c3d100c4026114a1600645192040d0001d00e00182043c058901020200040d048425440c10140c4003158580d16071200180b00c0c4c0c01c1c101c1056640b1410284003e40d601c074101c2c1c14490f4020980c41815000780b00f8000c440844505900781a0161a006d8125403241d20001c2c0840c0c020302d070003000044900d0280601207840c820709015002c070707000605000c0d06040441d601a4400c0d002075041000003541501007000175402a52401e41310703034040d00d051714007021982101442d40b003c0c01c80040d01000725402640611b940e60307074182d141840c024501010040c460001483ca4000c420b00120404107a8020700c400000808045004881c420101c0d0b0f01071454103041d4005003000501c08295600f215156801055220a004516146855001980c01444060072450780001211005a51404c0070780700040e0001313204ca103501541c41400d500170340c4200096004220211618 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 577338129 1106 577337023 577337027
    0x60f0f110f070b090118050306040f0f140610050d0308070f021609050109140c2209140f09030406140c07030c1d060406030201050901030c09120804031101 68
    0x105680c4c0503928001800d01900030340c1000da41441c04020001c0d030b100020920740c0245c01a0a180391801c06140001c0c0b40910048082c12201c0f814400f101140c0001c940326004400529414500d0780e654402d000d000c0746400c40c0540800d0603100050711440c01500c0c00f0151452520548489000307140b4019440811900150710b03040c1d850005000e00c030250320403910250384400c4094554907004804028034810824036041c3c040005040003031010300c40105034003078244c3c4e140c04d00c02c2034a80840c05c040490115107000c4980d21100c04210700b144080101c1d41560615510a10000140ca800044603480080a402244030360304001010520354142030000c1d201800801d4003010009880302c10343c000107440c0c0e1f44502e182602c100010303a0410200e4a203c00c1c02c4c00c0202c0c2c40e40d804038056806c0c052680c0705a107144000c00d07043c020080c92070010403d40780f1600e94604800141001 = true := by decide +kernel

theorem cover : BRFrame.Cov 577158273 577338129 := by
  have h0 := BRFrame.cov_init 577158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 577158273 ≤ n) (h2 : n < 577338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
