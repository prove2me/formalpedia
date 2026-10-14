-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1628
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:56:40.11765+00:00
-- url     : https://prove2.me/submissions/6f57f0dd-7f0b-414c-8548-eda42ccf5f8d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 292625899 ≤ n < 292805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 292627149 1250 292625899 292625903
    0x1305010f0f020d0f05130b040204200306030606010e131a0603010824040305070615180218030a030503040314070611032a0d09050c0904030c0b01061107170307060501030c180608060103 81
    0x3550b00005045440d581d0bc481050012125100c180c042461025081940304851090290050902003503142d401451041030900c1c000704440e50f9082c03034006150007400300052002c0489160300c8941802d464110045028140e18030241044018103a00440000b1411101500c4000c0e194200b1002c00e500905580b800c544c812408522060a040d02e41905080ca801c09502080380300151000160b10b030b4000c12904550050311600340c4010010541c40d040600c4010300814020400900003e04c12140441f504051281c101d080040356242c3c00103e030307085c0100707003402080003043c00640060403e26502128520003000e000a0030250f010f8103e0107010302948210f902c501e0300000300b08040c40408400c1d00013074182c81c01441c1505008111820702241a214900b000d400442e202d03100340425162000710300000c103e498501407418014240d2003240300180e00017440a88002800c5004181c001c42c001c80c5898100c0341000100e0b1a0302d0f020b00100703031b410b9240c940b00300b112800101e56070303044903 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 292628399 1250 292627149 292627163
    0x308070b071d0d0201020a320106030f030e0a0b04081605030a1208090118080301060807050c030327031306080c1204081812010f140405061305010f0f020d0f0513 71
    0x10f10343d10060307141c00d0400d40c001308210000700c0d40c030500440030000307070f100c0e0701c0400e95000713410380d01500340b600320b60441c0000f4081c0100c1151250100c2e01880e07411100c200064080e0072006e584000781002508036820401c11504200d00b0010760482400780100600011400341c03051038400c0d65100c82081c0f40c101500b09008140e000600203a00070b500608840f000c120600c1b2284c90186409501e942c0b090081e040032400800c00f242803a403042d000c2e41c20348102000110701e191143e01a612081086c0260b1401c1c3e040f04510240807900c080c0094180c00f400218403464503410f0981c060201d441c010155441c3d00002e104401d205121100419000354001803c190340b440d24907507a889500a02d0003194200814162900d5105d90550043c0c507207441041c0308001d07040142d003030042d0800c401d86001e44640e0000000c140700d8074400d603020b0155031060000094684950b040c010580700101042c01c1400c0d4041558901e54086009680e26142003250410032450f09504107604ca201d800b601138501 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 292629649 1250 292628399 292628419
    0x91306080a2a24020607080c030423150c09060f0d1b021005070e0f090a0b0a06030c12020f0f07030507020a0308040915050a170106050a0308070b071d 66
    0x24403000c80d441206a5800c0400110640b9920f441d0742455500ba640880040050705000ca907038404902c04c0c2c051001665100115200d040405e041030b000075000340c50b21811014a50b0304580302c90b070840030a0710004068100c030401c1808107851038100034030400105208020380302c01070351103034100e550103003c8040054917803440c07070b186034000d004d5095881c40100301c0030b82cad07180095000101003035100b60f088030a00c05640e80c400708403945010320280b140c2152044408403003d240c440d0103640e10417400e0b00002607803030407200005e04202c03690b0311110100c0c1e41d40c1410200591b01c460791040071120341c0410761400e0142d42500006114400203146518070100315601058854011200141e8008100e03041c0700d41c590a0859090b4070034420514410b02c1c00e580000c200102e80c2c0c1103000c9410040c0102c00042c0b801c04400c140304841011003806540c3c0340303004036060703880349904005180941203440d1500d000d40f0b0003c40000000c0e08040900c030000104038003071140100b413060382440c2a1400000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 292630899 1250 292629649 292629683
    0x1e030a181206060312020c010905010c061806051005010c02101b1202030409061d0f07120f09030e011107050607151b021b0a031407050604060302091306080a 69
    0x121554001404040700400c041c0180100c070340203401074a0040801019031010050300303994420b40c90001d6400309401e01d00402c4158020140300c8200fa000b40340200344600d0b42242c124a000c10520308441141e0f458050000c91074031140d18801520080c01c01d2541c1d10020b030001405a0301031001c04082141d500749804181182d05131500965074400c4040c05da4040408002c0d440760042c0c0184441c0c2481e00500181d45542051064020101703001041000d480780d414003110104000c100030240b008892140c0c801d14968407410410035040003000940c2d03165454003e182d0f521900c2490b0410403004101103021401058810407140700320782030b66480500d490080540c1c254410251521780c58144010f00500c8003220040140c0b02c01d80c02d580d680e94860016038450403200300e000341c0124010f5000c0c40001d41c03000500c03c140c400c034400c0b00c3d125503440c400200329074055005000000c3c0c000c5003403141030500c000c49000c00e20303129606000c214148444140c0d0380e011070070302800c03200120703101c0c0b49 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 292632149 1250 292630899 292630937
    0x22050f010504180b092d060d03030b1c080909010e0906010b070302120a110708030f0d050a060302030d090f0e06090c0313021f110d020316171b1e030a 66
    0x10440d207018004070174a1821801300c0c410491a80300b4014810300700800a5804456108403d00c945802007003040410f2032624210003c0001810040e00400c03d100b40d1800f210b0360504101c4c0c000d100303440041d551803100003070041c079020603404415681f1000341032028055000c65000d040d41e81303046840792141c03c1070808a16261613504025548040007031108071290348207900201c001020000c40341e080340d548400b9a9070b4407501d500c103010a030040c8a2001d51000c0c0781c02440d004080c081000c070b0400d840342c0010f8204090700c1c0202010800d080c0c3c041006004114001d0024520750810f050716241c02c0700413030200039005007402c481d03071000030004d51401e40700f1003050b021980250a040410481c020232520141907440c0200114580512070f9189040018100140844a5002d5418942c0d400e40003642e040071400308580c411405030706a000b10500b500600440c44510356042006100241c0c03007400c1ca0603040000001801c5e01c5035800c82c07440008115000101d440c60700c08150103010140c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 292633399 1250 292632149 292632161
    0x1817190507300b06040b0f09070e0a0902361804020112110405031e0c060304170d02040504060929040f050a0b030115031707080d0222050f01050418 65
    0x5a01c0e680d24180410b01019001040c404c10b4152000c000d110020020070050800c24202640c1c002c0504001880d114410044d0030104c02000d400c0140907900da0b44840143c0c5c00501040d10b81d2846102d03a000c200300290a128142c58000c64901c560342143ca0204070520359422000b80080180000700c1e003164032840b001c0300c00e11a510030812544101070305440701a84148900c0f4440d101c1c0c3c0f106a0310000ca40852691007900100c01450448290b100b0701c5402c0c0c20060044d641441c0341c0740002c44254403000140701d111100c69005030f0322800e0104100c22650300d0b4002140c1c0d00d1400100400345281c80c044000c401c504000381d0401c5001d141d0009000e4841401030a4405042506211485125401c203808140046001b070090302002c651200036010244070180c010203800341000c241c441007000802d00f9900449405103000000110038050b0fa0003440c0800303a110440600c080c00c01d03150901c480c003804081300d56040a00d41800000c01c6806a8020b6802524240c40c214200803100ea00035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 292634649 1250 292633399 292633469
    0x718030503070b1501051201050d030203090907030606020d03060b09220c080114060306010807030e15040302030306090109061202040b03102405040501060c060504031817190507 78
    0x240c0e0364400600c3c00846882d420b50303030403090210b12004091298025001d0350024031130b9071a00c28035030f80707014200164445a007905900354001081584100d44400007424071031147d40d01d002c5440f0b498140020b1904403944d0102c410941b40c000c0500990060800315026007204880410341c0950003101228121039050f86201e485182034505000650810b079814102c0f09000c01d40e441c44001c0034280006440101c400030b001038014400690268000e40c806d0342c044443c24200c03651510003980011816070246da007900903a002008001d040d01e0b0015a40f40504411a42441200e140400c220000055810001d10035030310303200d050308140c50400c1540f5618041c2001446105c000010b12040501c071440c901c220050b094501084505043c0a0079040311a42c1d510380102c41f03038548400c4001c21000d04200c1c10000f858040d00440c062034038044000d001c03005010199454a10b2429292451503c0312000350309034501040301203600800c41d03000321015569407a81d5071000a880004100d4030b510f0b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 292635899 1250 292634649 292634653
    0x50d111002010b130605030d12091703090d02070302090c0a02121206011106060102121813021c050115080c0c0a210503060f040c0905210105061807180305 68
    0x154000c0c2503054100004010f000c1d110750381c06421482c0d1050950b02540960b90b010303440291105030441c403502404200c80d00b903540c0003a0700b0149640e19000107d020030201d0b0030075004003e1061404051000051800c2580002d000051950340847c035060002880d9698180b0080390503540c2c54003d00c00d0000414500d03094980d10802c0c1d11100030a140700b80c0300d8a0000b04904681907804c00c2c0020340318010903058000300781e1094050024425503000701433004034040460070880a6846001d039010314144813060141c1c0780c802031032900c07041a48240c0a440f6580c00c0c00e00412000b418410402c02c00509498000c44c07658404c4058650782c407801d13148c100c05202c0c00f040003051141490005101d08240d080e01c803400401b41404507094003044d59099402080c2c4035440f100740ca400d6009003142401414449400d65072800019820402c84d0340d583d03070301e030401140e51854410a101d4168800000c9070080da45403255543d0307a0708034400030030030428058450202d440950501c45008021644142 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 292637149 1250 292635899 292635919
    0x31005040f050c06070b0c03040c05060c060105190605091201090b0424061401030e010b100509040f110a0810180c08010b030714070c2c06030c0901050d11 68
    0xd0407074094a030301c1c603081e1a0b0780111890034a2610f0202e088420060708508901482e0300c903003005600d240d001400c1120340b00c207084000101c03901e030709002e0000c100d440f03405000550303d01028000c0d0103c0120b030705905a000724805205494101054035440700d0151441c004502c1c1b42c1401d50b0060070800006070501d0001c400300010408801407080079406104250b00c07100b4140c02111003520303124003840a011039641c40036155540710351310555112006800100c0c0d00404100071451041909400e4000503e001a501006003403c0c0501f84511340324980c1040601c0070800043c4290085400340000c011001000c2001c1c40c0d2800403600107403c10b03049401088900a2982e4010a091070f04c0d807000c02e0403100000707040120882a01d01c07030021520380320300d03040c02d00191010f568400030044510903043c0b80041010310075440940c1203910222402556203107141c86410002d080100329610aa21201c1d12802c07580700d250003541103407415250f6049004052512501884502c5995508005128 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 292638399 1250 292637149 292637153
    0x4020c01050c0406030f0c0c08030702151009200702060f040305011a03150103020102210412030905031203040201091206090f150e06060918030409231f050f03100504 73
    0x250041044801070b8904005032840e0303101c0c1c203003031f00c004095010101d000032401d00c0c0802c0c0c0d26002141d01c0f10462065540c140e409042c1640d0714075056804066005c01590248901c2056120301524404038102c070390406a40000f03204017a20400100a003c2d0b000030580300c0c11092000103480c040c680c000001c1c00285514182210700107000e50700284607214040401c841c00d150304004506807a0113902603c41c14840301c0c1070303440104ca00014003040a030b04000000e1920701d00b02000c01e80c1c41c07080d48d45980c114981030425107000c039844001200341c0001c00500005030703082900c2e0012200441d074203018103012403c0c15001040d543c030002e03041c240f1041c450b03410000c2400f081c101503070304410200014482c001065a070f501080310b456820042c1070b400f00d019400c100d03c1212006403607178202d074a485c0e181d607001d0303042d1402d0301d03042c8003074003606060400d030a81076520356030388451012000404036400c4403152002c0d20a5200355406281000000c078170310344007800007171070000740303803030140101d0a10f8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 292639649 1250 292638399 292638421
    0x503010f05060a0908063d09110c0f060907150e04150306020a0801030c1517042303070b22120302090a170c030a050601060305060a051305101403030403080904020c0105 74
    0x100c1070b004040850204012680c10890741101c40c940a03442c407c06056050114200051071617614120b80204103101058030004104145c100c081860700180c101410904059850140503400100e822030f0401c034000c03009a8002c1d40904691030403100443c0324a05142c041c401d0b038459800280c148d900000c1d00e500c00c140c001d203006040300d00c20810300c0f030b51035501c00201c42520169030b03a500008081001088900c0a05e208958105000e103080d40c1c40c0600110740600d1045c1445d42d81080c2d50000304100c41030000241c140da0344840c4044d90780c0e41d00c110268844d03420a0352104002c00e200d4501050054803846581a1051000c014251075030407600c80c0380d0000e08140011902002d40314000b005015170030041030007400542d00200802c80c59003001015009840c0051032140c011400c6080040c2a40c0c515002c40f240d0303042c8480c00103840c00c000c2e003e83c100594940050000c450b4070510700a00791400400c0314104c070340082c1103640f903000100005010384504596001d55600f400c1c240031b028012 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 292640899 1250 292639649 292639681
    0x5060127171608010e0c060c0705033f030c0309070e0a02070b06100c0b0c0705030d020712080106050f16080a1e0801030b040303051e040507150503010f05060a090806 73
    0xe01c0d44007180e03503543ea50032800e07200358172140d105c26008016050150b0402102503c061010a016250003d4076040030a14100388602c00c0d0440c0ca241480358443c80d0642c0008003965170780e06045404041200f0070702d480746c1c40060b15000440d0400030010743c90b90024490400500308a84034808282801240000a908920015600301c20b002c40030a625280c904c100f02c202c078080e0303101c0c0368050131151112100194001c2114070401010008a400070b64280005e00c0ca01c200002e006031168800d040030004460328030404030030308c40c1e420300600075250020140c5150010940c1000e0356506000c0385284030070fd150380028403007200415004603080e0004100040d1400704c4480b081e0169403507100f116603107001e1002818004c60311002c100440d1203a040154002c103292110b41c44d0f6048803010b420380350000c032030a035101d4204042c00e21480f802c00700f000b14110110315040d825941404801151105e451103154030841d400122424850b029414000040280c0c4c0f0070b0b1800c03854800302e09011128 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 292642149 1250 292640899 292640923
    0x91703010503010c0527060705070f180509100e07051306061e090612020f03130204050108030a02190c0b03040b0a0605060a0e0d060b1201021b010506012717 69
    0x4240108136040c04d1203841520007085506201141d114400364020103886004984250000800c0180d0030114104203c264018940c09001902d40c0c1d113060700a0070005a03103418035480c2800c1905108682000043d40d01a10b03424520000d11211009031203460712189034070141e0441400743c0313118803905440d80030310101d914036155041041000f41d00703060000007080e84500410300c150000e00901c0d00c20001a0381049090b040149000c0b184090b400b660b8008403002c00803440e200407040f0450a150080600510890000703506025200754040c0d03d9074052203881d448902c0c200030080502100c1415040140b60f6841c007031740e4074145410007002840084038071103140d5042c001d00003240e08100d01281c21400311941c440b011140f105041002c1466640c41c107503412902e841c0425220ba59994000702d640042000050b0f0b190340d80309440450650001c0a5100d03649042d0400080d660041043e030160b90101c08010305090220741000240c4285070820032481c840a030300c10110407400501512100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 292643399 1250 292642149 292642151
    0x80a06080f060f0a0e03071407050d0f03030c0216050d08070f0b150303070c0b160203010606020f060c0903030304080c10091208100303050901030902030304080d0c03170f130609170301050301 84
    0x3640f010903800036a40f003d46401c017294070411842001c0340c917802d025200d00362000d054131100740d5504006600780803014030542c2e02426060350001010340611514621f4001070014010f5100c0c0446402241d50541c4522740c0902e4500e51000b040006c2d000c2142d08541e4041414400b1466030700700a0804482119a14030042d41070560280615000040d260045e078407159a030b4041d428285001c2c401d803c45042c084030340c2411112070005030b0f000c3c0101409400c00e68014410070001076403d51230031102034030458001c1420842c0070a00c1e1808022254001d0300251000d0340c808140d002140740000314804400e1b12454108103a042060300107840ba244801c42e540e680082d20b9a9002c0039203038115200c01004a5000c10803202d155010b600a0704409000400f80d90615030340d0500181001d4101c0c00d548001980d400d1604101904902c4040d0004507180400030a803403c5810305445810281c221052201031445907420010150400a04136a00a18103441680340c0e45411441c0e40080c00740b203100f5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 292644649 1250 292643399 292643401
    0x70f1e120510320609190303030218040513031103120c03041101020c0d0b1519091b0203041404020714010605090a0911060d1113080d03060803030403080a06080f060f 73
    0x40c1c18182044540f1034002004401500080c0d410044260b2104588641040c072410300c0d400140391300d0b404440190f00940340583e9440e04540c0c5040c550010004940c4940d10301024080c4040d106e481e00103405506040002034092151416881e502a1100c00080043c40c217003000100350315200694000d03441501c102d101c2d00b030241d0041e41c032210a04000d0303410891406800000c40c401c081802e40140c0040b25020f44005418003182034201d040140400e40d0310201005c000d401041d11a844699400d152014004d24840304001d40300d100314420003510815984001c0d07001e070340e25070440e100f00e5481205c2907903264501c03100034080c2049114103807040f400100040c0320542c50307028000c40c003a03008552a0701e0617081d50030040950401c504030303420540c0e0b86140010032a9180c0051560011103a00440150f1400f19041d140064000342d0808060400708108521103000080d25003140d81030038440741523940d5520040040c43c40e40c0c058180c038403903522400100300000c1f900601901c140040d02c41d603 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 292645899 1250 292644649 292644689
    0xf1b12050705040b01320c01060f0608090607050a0203090a09090209010e0c161b030309080631060b090c040e06030c030a02060f0903010c09080105070f1e120510 71
    0x22640000345140c00b2890081b5664000c4204801130110070501c0c0410380fa13030741c900e108002d0203074001b400c03122040c0e9903440092051028080052000748003a1034414041d1828004040d00c40b2805003900c0184800404c021840728003d000740c845c044800703410514607a235280010405002035060680c002d03000c0100102c0d9690a40348082e1068500c07174100c900d4407140443c200451404000180d8100d040c2000c4159803070104058440158080d0741d4140c4034504050440f401d0030800b41c500c0709454109480c03180510405100402404048800c16100805506000001c3c01c110707006190300c0309844041100850b5060050402c3d035000c1507040c0314a550f0341c41450350b10200f1040701d541c1940200040307401850614024604a00c0c5040d41c1c50070060070341c003c01e00b59880f128400b000304000c070b03c1c107126141e024031510354010458944101e10034000c450145c070380c0407a0b141e10b09501c3d2070b84041800050103400e0a000c440200801000f0515000ac850449980340340078020903800d0040038401c07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 292647149 1250 292645899 292645901
    0x509070c0b0f0405071802090901080105100e070f0e0d060e100c0309020306040602070c0308270117010e070306030b0112050d020321130f05062706040f1b1205070504 73
    0xf01c2158400001c018950900355204085608a40c103c852103070204980c0c1c00d20340b00e805640f8003c0082d8800030401b42001c0202000000468020f41207540c604010400419400555000d03602c2c15802c040b0002d1601d03170040340d045260020040e24a6007426a030b12041d08000a80c0003052000c1e02c1c2c03c101c203181d0f03180110280d50701c00c1c10182d416400040491f01050700d5600404202d03110707c4481000365520f41d42d9102c16000340d1a901602d0b805ca00f044c42d0311403050102c5000d10301c024a80709161940b513040130420340c20103024100c1d0405000c0002480e4a000340d00c1440074541080003c4100e40c0d450065000344030502c402200e00340290001d41203c0350000040d2044440e5855007641ca821071074611110310a0b00030101c6100c4e01d40c0e0306007000841c1d010786034007161501071006450300c0c1c60550441010f140e0104803c194105100c82c0030500d503280415940d030490707441040c0100a422508085a00c00c001c0440190b40c01c070b9540700000c04040e001e241540503440798040e0b4004035a1501080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 292648399 1250 292647149 292647151
    0x2180409141b0d150228021006050d060f1503050a14070303120b01050d060306050f060307051011010212070c0c0b040b0a180b0409090c0801090203031c060509070c0b0f 74
    0x103800200909040f0001a8030340d81c1020544d101301401420035841c2c0d806500d90b034a44405e40c2c54980b0700000350040d450f5043c44600d031100748400c0240201890a030111308442e07100c0401038001940c074140e18420f981c0a400503039100755030303180b6400c03102d03284e0514503120400c00c2c602312802c540392000b1900700580400c17150205d0350142c541c070226044a040c1c2002900000d101c07281003180402101d0ba8200280c0f25183c00380d401a20005a0761034450414030348030310054040751180c0d0120342d007044030b6654008440114217a9261100841e010002d405000e030080c984903c0410040f80708102c001039020f2401d517241d9020300f100840207580e445440311280319601030b0400801d030412030003410501603042d03e0030011030190003231010395030354580c0e20680c0c100c1d4000d10840b82d19025600240700072524a640030381030400081100f800c0720b42c00282d4905c200204014003055245d011862650380d035118000400015010400e03078540140014900c2808090032121103e07010045510318503220020b03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 292649649 1250 292648399 292648453
    0xe0c0f040506032e14011401020a2a030210080402090f010e06150c0105010801020a0f031104030b0c0c07030f020901290f040b0f18010f0905040218040914 68
    0x180001384840c040700b07000030400c002079202c8003030402c0769090208494440c0c02d4020240500d4540c035941031108104e41e849122041d10f04641c400c54110002c17070380c07500c07249030744a008016407548202418410604140168000707517001d11005500c030011a000310000e8482e92084540d80382540d1020180c0016031028000c1036541c154000c00a1a0b82c2070084a0a103c1641031407903034100014010b0250330344d10300742c01c0301e4803e9401180b84030400760080403000014007181403d1040881407000c04509010320301c405400303550541c01140d06c0c0fa00c800c049440d040e0408096404440e140c0c01c2c010240d0b4008e03007003207005048c010000510b042d00010301020459000100c0b540c0440d01c042001040c0c3c0100b0300740d0a03c03500c100300004141040710300802000740c2c80b400c1030340c0740e61074a600501044100f205e03860510800c0411050307110340c0090498140da03401c0300d00503150451048004c008050b003880c0d44e5006450101c081c030038448518003c0c0600060881214011440700382c50250481c1c88e280c1c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 292650899 1250 292649649 292649653
    0x109030c05060a030209130e0d0302070b0c07061509150e060f010f0e120f07090203060303070f0c03060504030e0f0f01211503150c0806010c0209060f040e0c0f04050603 74
    0x10902161070b1031002480ea2861038980176040882c1d41c800980c40038049007403502c01942c0c030f0040810780d9405105941910085040441c1010307015201d1143d414402040c1c005800d5002504108008580d8050110352440c200e07246c0c3c0b450b4450407003000605080f181aa0001d0205100081d500060740383c142c40384801030004244284521300540d40e400c0134821400c140650744050703000382c1d11019180e071000b002800003002d43d03071058403101d4203100c0306401803c0c4050040081003084e840010444041c0c5034411140b9a51072003d040460100d000ea400c01440340e0309040034081455840950043c01500880c0c141942a078440100441b4849031012103000c03e11341c9864818007107000090500e0300c0d40340c090128019035a50500300c9195196042100e01d031100084031040c041c1c10344511040c112850402e080c860810350000b8001c2d05402c0c0c0700901c00c4180500061064445800d4450b000b01c0140050082d540710021031902c0d084030220043c000c0700404074120891405001c3c10740a4400900 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 292652149 1250 292650899 292650923
    0x605030106021606120b0a05040203070f0816170901020d050c071505040309050409060e07090207151a0d03020f010c020d030e070506090d24090b010b0c0d120f0207110906010903 78
    0x600d40d000b81c180d0403046c0781e2210741d84c840011303181c0325400258070a040b01d6840c4410700142e004040c0c50400c018002d21900c0c101d200f0090a074507003049006011540c05040c0c0b03a0241e0b5040d86c0a800392044071500c0740c4850800e0f00f40b2544010740c40280c6a040e2003094001041480c001010045800880e40500020444101000103040c10b13440702d06560301507034000c654502a0114140341100302d50005a140360700107a00c100b0302c100c00084400b51412072009000001c40e041e01045009010401a885070200c1c101003402c040c020000c207250780c3d034040700078842003442e00006925280d100c4200301c0030074101031040e09015000f0824405540c0d00404007410410764400b840248100e200f07040322689100e0140450040c12081c10b0503601c040c01e24082545203603842e00c00e90000c4103900400ea01075003406980281000071407901501030705d80c506640103851381d41440002c0c1500c80350703401c0000d00c00512a000d00c51a034054209650342511280107584509004403240743d220700c400741100040c10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 292653399 1250 292652149 292652177
    0x901080607080a0506030f070e04060b0d120e0a05031f0501080f0627060c030405070b040e15010905060d090c0f080319030633030c0e09040c0b040605030106021606 72
    0x1500550300080040d04071003100d0047c4092920b8285281c0180b009854500d0404c4108191400340b4070040d1000d03a84560000700d1595162100000010540140000b034055480c4035140d2024200040a004040b20034003801c03a011510291556690060f01c5801d141c008210040000781c1c015107621701c40010101c03955400205081202091142800800300c2d1102e42101d090030002203008002c5000466500e061500c1c0c440c0c035003100c0c3e40c0030b501240c2060004005000082400c0c03540400303404009a1000354100040b503a027907550f000643d10403000b00d0707094031040c21580000d21091190084085c11611180c1c840349804191240c005194020840f40407000107001c1803171800300f0075040105005856010b0b021070502d840d1221040e20050001c0000c0b070b800341d28081c01000005003001c2003401900e4800810310499032201364003070821540401e003041203c440b030f0b400802c404015551119110440140b00c0c0d0701c280301c1c2800521510002c00942c4a51081d42001c0301c1c196181e06015003058 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 292654649 1250 292653399 292653401
    0xc02060f04030c0f0617040213020319020406020a151a1e030318040510050a140a09050c0a09060206100e0c090312190903020f010327110901080607080a 67
    0x900d0086601100780000000030b0850b4210f840504591810f40b07000a04021000b480a0500342c4c80b460021074900511015803200700ba0503010030b03841280542d51b07540d488481d504c0d00b4041c1c91651601d6200007400078607207501150710402c0903c240c110108403940f0030410819070720810100c1407000d56860903584545080000c0240f0f43c401d020780c0e000d07070800c03a4001074290b4001c000041140480882c00810030302c0c041c171841d94021181c11a0280c10f5043c08042000d000365802282041590b0810310240c42c4c0d14460204010115140280814a0611b03100c2c80e494100d4080c070404940d54070f1020131a9030001c82e0652050904480640c03546203410650706000901600300150148100881d1460b81c50501c0340102d10200c2d500440c0d91440110080041c003c00710410301704100c4540ca0a100507661041070303114904092a01241e1401e14100054840d0003014030601420040d44039201000b0014040300d5030300380122000c201c0c9030b03642d140240e2170380c00403501100010082c0002500300400c17 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 292655899 1250 292654649 292654657
    0x901030b010c0501090309031406070915020705030304090615020303040b070507061d0607020f0c1c0305040f030b01060210050c071b0801060801020c010b0a08030a030f02090603010905190b010c0206 87
    0x3051515400d200c8040c2c0b40e00c1c0c03c441c8203030700603400200860710620520418501219a040d558801064289810320b001000c01c0030500030002e0703580c40d8100a00d0014800c0000d100a001c0080a0301d03625030362000701d00d000b414684500034400700c08001010741c2c0d60011003507a1240380c0080b548802983c2e1420200c801d50700038003040301d19079900e00440781e01c542c00e841369400d0036a4480040009081c481006840c0201150360420964028460212503440d410004194030200580454030001075103400d9445010307a40080b920744901850002c24010b00c103000c2412201c0313603000d69046880325618001515011259030000da541000100000b0300c45d00c58942040e0b0000301c0c040900d43c0c55170005402e5407103690210300c07144e4000c00c0c65070186800384501c1c41003200071a00c55920310315266065881e80903540e00c2d10107140c0e54420f1500c40441c03940450740e00403802080c0c20b54a41e160003046000b41070940d42403c121a0740c0d00e10f8030304c0d068248518070310000c05854040100c0c066074200006940 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 292657149 1250 292655899 292655921
    0x5060a090501110315040e0105090307080d0f021c0509012702040f0e012705060f0a0204091e180209010911070212011e020415050711090108070504061a090103 70
    0x242c1e400783ca04000701d000e4051401040400015445002c0d0a400c0000b0750381c0700400e1030f0107a403610062110120000040b1465998400c01da240c40d0240a564140207202c0d800d410015640005001e08004142d048804507450b8408010003040e11141240f03400c0701e16180d170302c40c492050b103403c075101c001781854150a094402000400c0b01c00303540d415241a110305401d0181d05a455604240075646459000c500b404044c18989003000800e848059071602c01900010f030141121020400040b03d9404036009441426000d10401a100b041e454030721010b40c83d11003a261500d90103800000f482d620225404d80c0081c2180c00301d074200100c801c000d0042d4003402040b071008001c1c040041e1a019000184100300400008503212490403075000b0305003010180c1c031124030401052060303150014220380c22030740500d41251182054608a288050380f05203407030744803160030b00000d0b80d41e40003d51202a07070001d94040c014140e40d15403003041d0b0000684044510344040c0004001d0354803c2e400061150 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 292658399 1250 292657149 292657151
    0x3011203050f07060908040f09181b03050d0f0806010804030e0105090301090614041e0506010e040c26010e0a030e06070623061e01170402011101020412020a0506040305060a090501 79
    0x34803507695002140c600c45c0c0d04071240038012400f00001e402c0e1407000030042c001d0120034000c60441d580c022550308001c0400504c4508510b404071149481204032030055980710040701c860803601c08001c0c00c0c0c5848081e00074005040ca02c0010b07910752060305007900884e490b45a40242603910301c010359030b541040c1c1c11030350599690300344032012540078069a03000e101c04c0f4203000102e00301802e241e140c800b804440c100a0800e81d0440c2c0d400a0400a04075044402d03089448103541c80740d1a203040100d050f84e00c175000c002403122000b520281500c03488580c0030076000c02004102d00481802d520b518420801402040c1c0c03a5030850b510b804d020008000d130601c50240000c420703080200c2c141d034400c022602808102c4043c1308011460400e2034410416000804015801120010000388521000341e10800007041c083c0204007164041e40d21503c40a905038003e54960b031f1201d60712560034201d40b5040e40700d51100c2a001607141270032005c65042d25045409015256140e90b000000340c017000400321025 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 292659649 1250 292658399 292658407
    0x9061505060a12110a0e090130031403160f080610030e0c0a030f030f080417070201020f06130203210f030705090d230f03030601030e0c03070803040303110303011203050f 75
    0x4c803075010002c0c2005132076038480302c0c0414281030070701599480c160402007200c00d00c140b034091040b0111107008003072040540550912101c40c0390441d8005040f00300081441808400e00011082e601c00c0c40103082030581d6041c088441844088919041c180c40441d0003400701b441d885035061107901b04100101d9110115841407111030003003090360a1951040c0c0f1001a0102c9480405a11840a0340340b6011450000f03200c0c20191510300c401c0d51820481802c200001507650700b164000d00101d6000503409003503075000c2c503100c4042c00000d100d803801244240916201a0004202520f07125002e4149110b458140407107181c1c0307032034a5440500034506001d000d102540b41c6980b4805e4840308688640e113030010b41007044890707010347c500214010205800010031101c1161002042c0c981c01402480e005c18070b044c11610403400c01c242c15540075018010b3341c10110344140e00000400469101e6910b503000740b292020b815481c0e000038054641c5004000c22031341c01007071080303000e03041203640c803041a071038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 292660899 1250 292659649 292659671
    0x40b01021b0f01090308040801020712030b0a0909030c0c180b03030f1605030c0609030a030524040b01180f140904050a0f02130e1f060e06131401080109061505060a12 73
    0x20387d82007070b4800902a900005c09078100440e01d454840307404120700341800301c8031029000800c44401d50180a0900d07a5a089203424103214003880030040c0c0d006034070001825152a00b5022851869903080034443c01c11340b00c00c506040020443d0361407040c0c80d4001d0305200310000c580c4003840f0600000e458520080c41000c005160a01003107006601c600000e55a920407204040d007030307c800901c080012541c0c0840714413445030b01818120640c400701e80008080310201d005803520907420b80d40c03d04c2e0711b10302500480c800352204030303a2050b214040101d00140621000304408200201d0f4028640d4100c14003401c0081e60b200344a030280d6200070400a0340c0b410891880d400c8a42036804441c0d0750384131404100700b045680e40b1071070842d008101d05110040c01e20300a004500e2019216901a05000e04400403212956001000d40c4290b4004403002d035944102540c041c0541031015980d20f4603001c440e400382d500c61030f084800c0321006032202d41440c65060342030b54282c00c01c0e9460b80720b507071b150848061 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 292662149 1250 292660899 292660913
    0x515090c030601030c0e090f1b0a02060907090608100216080a0f0f08010602070b0c030409050c031504021201060302070f02150d06080303060616050c030615040b01021b0f010903 78
    0x8811003050001035140d251280c001000c0d1800e04940c401401500c140e14404ca40399490b801d94071050f102c0d1008001d46401009402c41c1c4040e601e280f42d203403c04944254019408550140100440c0c01198501a1600b1410f0100c0f0b546201b0781d590741d486507400042c07030842a005005200081c150322424040ea40e02e418085900a0010341c000400d160041d1a40f00d82040a4400c1c03c50b403458202d14a40c141031003c0c1da24a41d5000380051244040b500c4424072400304100d5000d0403d800c4140140c4c1440314bc4005150400d4800895600008005c1c004a00f000e03c282e4044842c00d02001802c0c0c0d29020b010b0f0001d502454064804030b00954200307016855090414440880d10b0b1003c0d0350312400300c480082121003681003030700507400810a105440d0b9030141601d08404524148042400d031a02d0081d107001da0510036660140214402c00c09151014019940d2000c01903c0c14000c030200c5030700498489203000040011240c262121a8040c100000ea80020031300c1030520813201900c0c1c1d26490 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 292663399 1250 292662149 292662151
    0xc1903020a15031b080703093206130507031205091509040b010318030f05130909020f030a0c0303031a0306010e0919080306010f0306050618121f051509 67
    0x40d0600750515001e10145501d4032454144c040c0c0c500a8540c8480710a10040508902401600402d51a03441c0c0b582407020703a80c01d107240e401c04450782c0c00448809940b94401c0e83d02d0514000303100c1c00341c0700020300c4588030511090400ca40c488040c2c03c100d803c5554a502e0403000701e000000300682031100e1030454480c0110351280c0301c403486101e6103451070b54040209031500c1c071104c0d40c1003600b0401c001e001a0001c0c007031240c0b070356071504054005102c10a01241e0714014039034030004c0c2d000100ba0000380c40c07200e0f9005640e001e0090720700818a43c07200c0141a40d8206070040100400c0540d8000c0010922076803225610034501c1c8445140340c3d8640000030f00d45403083e042030740c4140b0b00100b031140c14038040003015042c1c0d440c40b405025901c00d43e20741d00b409000085c45035040c4079400c60241c000c02d1099002070041c1030020b103620788a07189244c0c000c0f505440441e0240c041d2810b0b0710380041320040000c284264610ba5045059038581402c03422019050140022490380c1c48180c0d814071f00c0e52092882 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 292664649 1250 292663399 292663409
    0x3040b0a09080d090c0501050c1c0c0209150f0915241210082404020a210b070302130311040e03040b070b01050109030b0708091c050406020c120c1903020a 68
    0x4200101c0c135080c45002d01c0080d03800141881420046000f40d0a80481e2502100d61a040c900c3d0f55070542c07035000d60342d075110704400070342c00141c040c2004401c61010f800c0c0c10041c04140e1f04509500110003d02c814824140c4007010149050010000340340307480300c1c042c080ca06112040c01940c14441a1003d0560444101322100f481050100881c881e280c9030a04020107011000305809800b040c2d0702c0806a800c034030202400d0554100003815034849404550080015041c505403c500d103060762580046900d60488006445c4404035403410312a00907144900d901500420b40185180d90f1100201040c1402c55002074482d10035101c0101c040c0060f00040c41c2c6080c0d029982c00711494810708058058022074140f043d10b080c14004180c40c014055480721140c104141c1d6900c508041d6441d011000311b50440e000e203002048212103600401a204651054084603418503004007045040b510750741c803991540d400715145076030130300c0c1044016100c420940c01a5460075200c0e00030070a07041880c4c200d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 292665899 1250 292664649 292664651
    0xc0c0503131a0f03060607140a030e0306060f03070b0702040f0204060806030f0a0302100b030a0f05012313020d03090f0303020c090f070c0605070e0909060907081203040b0a09080d 79
    0x412038250901c0c4251031061082c5001841c0002d950003410507404040e0601303005042c003244060800980c1c800d0221010710040c1120401461458000c0100340910345440c0203001c1d840c08102036082c60803c1080140c001070181c0784060401100010396000480e003681c0c4a512894002145034070741c40100003800159603906e0395803910b041030503d8000c81d101c4a8416a010302d400e50b001c00d0380441c203e49035410111020403402c0700640001d00c2c00000780300c00f411850601350385004101c4154009509684201c3c140e0700b10303812219044c17034820310440d5100b417103544841510006240010744045200e100c2d0401319006501d480d6010955011078104501580c00b02c8580701c5240703130050220398450b484201c071340800d1404a100511500c084500105040d4444011070341c924012018905080f001410483c1c00e440c0c4020800d13030350310301070b075180ca00342c090360b600400c1c40400881c24100b1089059140c1d45151916510f000035004002c0c4078003480307582c41d01c0320000a00c44030024442900c80c200 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 292667149 1250 292665899 292665937
    0x2306060d0f1401050109080c10050427061a18060c15011d0601120903050c01090605010e01080d05071101091a180f0f220e0706080604090305030a0c0c0503 68
    0x2072900e45200c042e0130071414003444220400c500c03000042c0b002c615401c241c0d500030151005942c10340e80d0740100d030030250702003e0003410f652a10070021100c00100c880c948003442283da48036001e0401800c001e02d001401d01081060303500010a5500c002082d940c00b40455107440242801c2d0b0782000303000040e1884102180d001040080440009400792a80450784080c6500f000030018240c0e844661110000d00c0c0c41e2801c030410b00d80124256170407820b200009101c0110719240c6640101004d01910184084000000c40c01a0700001d1000c3c900702141c03a014540070745a01d0f036481100804581c1810003d102c500030504203c4001002d1121074210f4260f500c0c0e0880703091107000c03203680d001c0003070181c075044804904695075440c0c1000002004d807030744408a134040803000586014505441d00c91750a080c482c0109880001d124401c82d80c0c542d5a41d512510ba0700308010031b4940b5140c014002510a1000c55080c183e03e91060300101e0860410500c8042140d0b030701402c2d50404e0350002c0318039060b02 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 292668399 1250 292667149 292667171
    0x30209181002030f0103030e01021606111212010e040f0818031507050405010c05010b090112020a091107080f071b060e0a0f0611030705010609020301060e042306060d0f 74
    0x740040034000c400294214a07110203500f4200e441440b000d0104011142d404406034000d101808000074580204805e00f52110000340044020002c81403080c8201024154400c505800703075004d40b4910503022900ba4a45078100c0364010015109403007030329841040c0f400080215004019180d200c00d005000900214101070030980e088446500340228001002241507110007101c09039542400d00c8411011030341041c1d0300400100c07812a4204407007400200c0d0340038141c102c850705607208540410401c0d854004083c240c0300d180e0345013010400d0921200c1c00040f1400007a20911160180f518180407282c0c840c0e00c0c06601d541280540185840424882c4a9012240408611098600b40b001c546007080000d2002d035a0b100d0070f8104903298101c0c815040040c802c942c00141c2000003400011349038004d29001398400c0c4078a601254001c08810741038201801074004200d140c80803c405990a11015144004014201d80e8403c0081240a465121610031084144098500001c40098417 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 292669649 1250 292668399 292668403
    0xd0e01060e09030a0c0b181209041b020303011214010911040f0c020307060b220c0f1103090f06161103100b030601031106090a0810060504110f09060403020918 70
    0xe40062090f03041000300400b2a60042a81c0c1c135003030f610114020513030b40c805040403000e20001000712100d000c2d41c46a20001c40400700035020065046a0800903114941e551501d80440c0e0b200b00e5015030000e2004101c80000b2401e80d15665000b509041c07038000c0c940103c0c600710b901d1920304560003020304141e86203e0130144180d02d14409100c00401004081110295882c0101c0100410003504e0380b107034240f20340b108606400d05504c1c2802d00c0c00d0420300105264040d00883c000903000940403000d02415510078143c003442d03208010081d5181804c41030138040303003100c1841480d070824010400e000100e1754841302c19a109006495900034240343c0000c05040c14021304004207814100f2086821550f00419142c0c11690b110502088a403800c80109100b07028011390540c2c080d03102e4100045458003c508003c0c0c44022181c1046065280e0080008544400c1b580b4560740c03a003400a2110f00107210020b0544d49402403034503080c03d0ba2035000440040c01140c02c0c6180640a24816400c0101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 292670899 1250 292669649 292669651
    0x20c070603050105010e09060f1c0605070c08070305130812121006090e07020715030b1215010b0c0f16051309080d24060206070f0203031902030702030d0e01060e 71
    0x9250078419945000300003000300340c203151b10f41d100b200204c0100e40142e4a0594081e000c1c00050242d041409044800e5428580301c0b00c0c3c141c505508050006800320300c1045c490810315030001c491410301c00f042d101103d45401c0441e070310690004c00f08001c29110b07010490a4060355102c20510340e1030200d50329840d40000042c020070351014500c20144502d0b030308024290306842c18900c800394659500e0300f00324502001c0350702c03e840540e201940c0b0703ca80d030f82c15080030350444001d41b030071507000307003040c916035034401501519880804803d001486210110001410440408000c0301d082c61f403211501800c002038141d1504c412129103030200b0460600c141d44900754a00100c08000465003078803000d40c0e502c02d40e40210600e03603076100c2d00d503203010400c00c1c0280c08624210b0a81d903c2502c40b030700070b503070740313800f40c51280204079080f810005444c40007040321b00c2a1100003201a101040c445500040c0d0005070803441980001c0c404808001c0440c843d490071012444004542c5e68a0a006a060000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 292672149 1250 292670899 292670909
    0x207020d20130b061e13060323070206040b13050709020a0f020f031e0f0c0d031d071707030b1006081005030a02011d1203040302040b0d03080c210901020c07 69
    0x82040340389560f40e500c660035940a9003a80b941001c0d14040e15403402641d102d070020a0100840607840071075036030307455888151003a031400314404201490407061800440c0c2100c101c80160300403030003d000614600070300303500081070410036980086039a40b06070400350550400041141d002c10030712040780d400081c01500b49480c0c00a82044466022106d450f03205600c005000500e1003082650351100d05011500785140d003004054a4005011030140c444000f80d41c01c00c0000d08110a102d17032540c103600b01d140004861030060030031070302d0225034400b00981c0004a56072070040c00000004a40e910140a12603071940e0b00d911111401c080f005070039420060a03102c1000c884150500443c5ca000443d640c8064090800c0300301c110581414202d9440b4004003c0d0704803103041c0c0d0340c954607800040a0419a4800c07107060004039051414404003031029100a00069101404a04407903450001403035100c04000b92895102d0f924140300501c814244c90039080303a0750005209001400a01c8804081e007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 292673399 1250 292672149 292672151
    0xf12090d0806030a030f0e0904031d1504050d02040e0d08182a0a0807180f0b0303030f04080d051302121204090b030a051002031f180207020d2013 64
    0x10500ea40407035031300c10404900030140100c0020301a259805007402c19080c13400104504140c1c902032070018458000300c0984c440b4406001d062070781901e80710746019140030300501028140391a080c100320025119200980e08540d407840c0360b4042003400d02030300400f00c10b140c07105105414500301d50040e14984410514150700274081c6590107010706445032641022520041c4c46080d030b890000740c00986103078008102440303009000070345070001000d0518020a810810803214601c0356034074041c1c0c3d48030028154190000c00015145a0011507000c1d0024000c824040c2013452003034190040b82d0040c4c0e0304070034007075001c05102c04615101d941040e404114401404c000b066a11000c0e041c0e01840c01003041c800d48410782c485050701c0402281c0e4026821004071100301106503654002548181c41e50761001e03075024a00541c801020800c00100c800b40c01455002091000020b03009401c8058200c0e8080d00b900118004103620f00842642c014400e02c02c8041d4808800410082d4580c918003e000c00e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 292674649 1250 292673399 292673401
    0x1203020306030a060b011e11190c031202100203090c04240311030c03030315030c100c080703030908031014030f3004090f0b06070222020f12090d08 65
    0x1a45010503c00c80d02948000086107612441e001603984510622184051044580c0752003131566010040c100801b02030070907070342c03004148031105054038030084001e0403000000304100300107040030954128403412403058444034940740c00200c3c207981c0141c4100ca41c644c8101003201d041e00e003522402440c0c4000724442d190600d80e040c9540003442480c44040c058101c00000c0714265141444030022416004050300d0350307450034403c06007044608100c002d000f03204540107407850b8100101003030402d41040c1c50ba20301c102c1c6182d03143d00041e88001c10031010591501803e01c00a41c8070390107140070b000d84156012140c1c4c10715013a000054524143c0c1d40c807946c03080a1b0034400c0300e004114060b090215041c0c0740d0350013600202c1208188a4200c440d45006000603000820a030355a02542180d8100d142c06c1c030144111104000d0030b805a0000a0740c825480654130300543c00000d460070149805d800050f0920140100340304440e04100e101c0561b0784120010000100c07001d000c0c10f45244840c0c00c0c11262 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 292675899 1250 292674649 292674661
    0x20415090303260f0601020c04020703030f050c0a14160f080c010c0e100503090a08040608090601080111090402130513020a0e060f0306010503070c0519060c020d120c050c07090912030203 82
    0x20f550b00c00b90145001d8079580e00420101d920920042c07050f1840a8404c0d50f0314005480c009000740384001c10380c0641498140403801242e5900212004840d10781d41c3c8000418240d0000d0340d0315400003101078205200410715100054002e58403243c0540601c54a0352141d03a82c149260030340e504410414100912283c42c50915600d145540c00e000401e403400c42d4980e550103424900d0320941140140a515004c540003403000e80c00f1030217a01c40c1c808581600e134542d907101259400d80380300d40c441704d00e400824809404282410b50180102541ca0745aa40c9940e03943e20105861050703c0401c180080d80008480c3c1ea001c1c1c00140503c005403060b1000c2d03280584900d40d41045010150505042010010205465511030902c6202558118040d948451904442c132903c40d0350744541114258100030403031440c0781c00881c580b24004999210310101c4030100d801c7d50004c08400802100340b101c14016a00d01401c104a480f02402e00750f1800105c01800381440f601104403a041c0030100342c010020400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 292677149 1250 292675899 292675967
    0xb0a0606050f0d02090d05010501030302070b0c060403080705070b040510270f0c09180204050a0c0f0e061201290301030807020603060d0b041b06031107080d020415090303 75
    0x1200c08031150b2142c4440581400744060321070b01080782e038803044800d038903814440107503c1035040300c0c4240c08070b40700603544000007411030084c08621103107a007020000a020074003c0402c0380c0d012086180c4a4a861250780e00c2c00809c0038156810b4415a09c2038016094100d003600c2202d0f04c82044260360600050000360186400180c184002d20003003000d01c04d42d00704030007100d042c030150a415000340b1511000c00065800680003c509074840d500f0030012070580d00107441901041c040550314029003061107101a03911014100c0d0203070300403108000803880c4005070264203000c2d15042c5014814402441c0040c0400300c0c0e58222418040e0003000108009124031084030000c5d6410b81e4055240d036200030004030f0460400c40b0103482503180000304800c21991054801c2d41c0c901c00039003964620b841d8042141154070021a08001c1c00c801c1064101059074480035000b50315013210094a06a1106800000e011014003d4004201040010b00415801c800d00c100309114401c05401034000c850012a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 292678399 1250 292677149 292677157
    0x10c020a020607080d15030f0210090e040609020f1201140c0406080f04021516020a0e060303040b07020415150207060e01090306090f021c05070504020901141b190b0a060605 76
    0x80404d00d0016051202d1000f942220804110305002010700b01d66a0400c0d403844a1000703c100d114201070302080c200d880c000d07203c0e0307029503241800703014071340da19641d81400410150000360390240b42c3c44021103460340c07540041034440404da0004544034141a01c010030051024004a102407000e01050040303507401140c155015100380304035800742d04c49001080b132124074651000c2d018200010600c3c6131094495042285030310036100300030015034900c00403030381400a50343c0c1e9a16030402c100410081101c60007900d009030005200207403e405031019039000801075848010a21194200c0d005001d8040c40020010800b504046440f5040800024466840340c00020200d079030343c03020b89013840300340a000d030b41c00c03075004d00200740d8100c0225010342c9600c0704000031285403184080c042002c0c00c00d4020b81d00d4000c01a100e45100003452412460160030152511b129448000400b24400e20704001048050051403d0080041d0541c2004448002c00602d82c6902c10f0420208001e615800f100722 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 292679649 1250 292678399 292678403
    0x30306100504080a1406070c080a03150f090e190b060105030a2310080a08040b1c020406030b0405070c020f150c01020316020c090106050d0c03060b13030302010c020a020607 76
    0x10300d04000c2a806484034040d540104056208400c2002c0c208a50306050071030011460f411207180d6038416000f15a0b440d81c1c408010080b91051040290440c000c0d005414a0074845030044d0805480e1085040b80500329405000c1c010b46038118883d0104d03040c003401c2c2c0d40003d000148400d0041075101d1008010010f4001810444c0000c0001c440b203c1c00d40c4082e4407040403460301241800118190310284c001503402e07807200101c401d80018002800113104030203507030010074281441e15004d110101600103844114108034101d0704044144503d02c028000f6008544000400c040100700b130000310b8078010300c07010900051120303071009a42c8001c0d0040b1851400c4030555020705880586196500548250300340c60b40c008814801040090540848203039519030894041d090a102007000104080c41000003141d4100a00d40e2880541c0c0c002d200102c80e81c1c00c0200724250303a07126900041d400100240101d204101c020701c101542070058a0803004144002c009044482c0c0005101c1d1040604c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 292680899 1250 292679649 292679659
    0x913060510110d050313150b0933040209060c01140606040e0a050403261906050d110406150e1201020315040209030a0209040309060807090311011d152a030306 70
    0x740c0d04a4286c8005440c1070303401059035000c61205040ca00207406103450040c440c2106400003200302d00200425500303000c80020798040131001c044070400060701c40490603006a000c0000e4610390b265040100f406010302400042c0c000b003c06010380c0044c402802e401e00c200c0041200304060140d5032905a040089500e0006907a141d5180c20790380c010324041000c03000305003084e0310b000c00085207001c144035100094014600c0030400c40c00301c1c00c45005009843e407101e4000b82500c041100c040091081440280c00003901c0c42d00c541c1050011050b50040c4400900c81080003501401c1c00d0320300e071451100c0c0030300030f40c25820000700c02550f03007a58817207990145030b0115024901e55010060f092111350040c0c12160345003000d050003444a480e902400740814040d01c04601a5886a0f0160040ba60402e84180d000141c440c01100c214102100b0303e086602c050718110a240d17a1015019004038045410726603a00151508c11400c00e006824011400d40d0701050354110500401280d900c480c041721 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 292682149 1250 292680899 292680901
    0x50f0d03111804021c0509101103010503120a03150b0403060f14061207030204061509080c100807030f05191404080304080304080d0e030414220e030913060510110d0503 74
    0x5a609075844401013074117141410b01c802d12010b90f50210700e02034009140b900c1484900d10030400c0c205244000c0c8951034055215030070600c1c0b40c42466014002880180c5000f00302ca0880d4907503400c2003600354000e40001c000c00202001040202d118034044070448000c1481480100c02c0c0d40300c181803000f0304003401040303010f10852075000c0500400b40515401001001920b884820103903c02ea0040130401c007040110700049031030000000c6410301848000c100c492003242c1000100e130b81d0f1354060700d484285601c4440c049441d11080c01514419111844090034241d012040d440c20798001c401410b101a0601040c403000c05c950b0021a60320580200445030f0706d40380c51070089100c1c8200c0000b800c0c482c2c0b41500d032009003800480100200d400403080044034814107400c2110840460164404014900c040d400009000d03802001c0000d0145059a0030301d8681d6000c1101c0c403d0403003445440b07a81d100018082ca02e0314008000c2d44040b40e140c2140c1104102a0340c5580d4244c03110303110b042c400084 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 292683399 1250 292682149 292682167
    0x608130c140a030b010b04062d1202120414061b0702150f0703030b090f07020d0807090b0d06230d0b0406200c070506090604031707050f0d0311180402 66
    0x582c6000941d030240c00c4c080d0640e07407806400d1294000d80103400001e80e80080801510b46007022559100c2d41d40101e500704240c0310f08090700c3c050040c0c0030480c0e95607020f00c8100c0856070325405c2d551045006101c15818201550a424100b98008280c030000c0c6480c0c0700d00aa90007200c5c819a441964150b03001f000c200c000c042040e00034000c3d0390700e03d1400c0f58000b414104155054202000400b400e407444c0711070351540e8044181d420300449803070005038025140002d0b83c038443e544c2a90060124200030000948901d488580e582c00310700c090130f415072141d004200d0000b0009400100c2c54580001d440108041000610b4041d8143c002420150381e480c0401c080c02440c2c0d01803070b05071003100c40031116041c0100c03a10200b9009841a40401d000341c0c1c07000110340c2000700458034000401420b07146810f007150745040f0340314800441040408800e100460001b641000040074840320300c401006540e0384003c0081c20b0300c1e030400299052200600803040a60040d0a014069030802c64025844410b44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 292684649 1250 292683399 292683409
    0x200406170a1103240619030b040b0a1e08011104182406110a1e0609080304140f03070206270a030309050418152301030506010608130c14 60
    0xb64120049254001040c060840c0e009441407241881c1c0601880f108003031a0100f0000e4000e000d40030807081c03410015110260310a510541c5010001070001400700081d9000c00c03801c1a45800c8002c0c2003c1081c06510300034170f68408040186443d4000b80b00d001200a0100614000e038896801c4241c0762540d25041ca1015821840c6038603a0903216203081e04c010314985001070036038480c03400402d141411403002c01e00d01240e4881035503080420101000c0c00c110184808542d011800e84846564100c07090020f41d00c0c200039405a4084c01c80540b072400b100800b24103040e4180350401c026802080b0000060300c5000c151041c00c0788100302001c00403161048a071220b4105400268031101c07a803404810107401c180382c001910307800e68080144200ca5410403508943c0c0b50400b41030f280409460030700a501941200713502104002c003041e48105124201c2000001c02e800448003030708604010301000e9401854035034040e20980080107078444603241c1e00840c0c1c1722030082c030107040e42c031004d40390700c54441d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 292685899 1250 292684649 292684661
    0x100306050c1e030906010513060b040b0306030114040b0a021602061603030b010c1707020d02060417010b04180f052505030106050d0812040204060905010603200406170a 74
    0x100105210514248107004003030350041c4a401110b80c610031440381c0111598007501c0c441c02c04480284444d07401c1c00100904252002c441082407522040c1c04a1803c402c84040d10082c0340c14443e00d6140c1c1080780c00c05003500c03504030715822080620310400022a6000c954075400206103200103036600221001002e801501d094040d411540c0022400d444104c4450068005802617608010701900807004440500064901421506d403201102c40700341c00000c020030300716100805000e10740100f83d0200e00150040d03440304c0301c0e590301142101d1501d9000e0150014840c8112020003400300341454400c01d0000024000d0400d40c213080c4194100401080842016110501c141841e01c0000e0000040c40e07829000e4240a5403d0260000780c508202080f103d015510203055420002c001c004181c15840c02481641d001d62120f6000a0350011441458042c3c913903940c000c50b004080c6051498a1218140c0906418008000801c02241d11400c0001040d0101d4401c0200f4cc44406100380900f02c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 292687149 1250 292685899 292685903
    0x18120d020a140a021509010f03061a0d06050901060c0506010902160605060a03080c07030201170c040e090a060f0509011d030a0e010e10090f0f0e0c0c010f05070f0306050402040b121003 81
    0x4441403400c465405e80002412600d01c3c240d0756090040d014100840948640c0d1141d0102c0c1081048222925126000500326207092807000290b04d6030758000203075000d1350a9100e1008070b854024aa01840800e0000f0350240140e20415032404928408803040300184a402030040350703071000801d40c541c5c0c5142008005640010819403540b44c40c424031500c50030103200072404a03030000062081102c000d400203124400b2800524146807a084840c007194030000c0c110b040c14083c2d0703084a030024410707100e21025000f408a0028030392800308002400c4074034070252000560201003000a0750480001100e00030842458140d44140074000140c42020f06800003a60003031040d1603240d00c00b6440780c1d02000b195184401c02038416036513592940004002d0142d0350744141800300003401408028011710030b149001000103159000441400121071003601c00754001004020300040503540340c00750700c01402003280c00710300d490324002c0030358850300c146510884049c002c6000a200300884030100c2000756 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 292688399 1250 292687149 292687159
    0xf0c05070314010c02060c030a0b01021603050a1403090a03060b04111b010b090903120402010e0d03090501080c0903151b0a02030405031002160f0c090218120d020a140a02 75
    0x2901c03440c00301080300881651065035813a01403034071407007071000920601030903800c0c240c2c42c03940e1035460500000c4c1c85416501030640c03181401c0b0240004000714030000450007031003d09024401454502030801ca252210b020a074400d0100ca540e0369101c01c002803c40768000c4c000a2001e6080010a0140c1550300540380b198002140c4e081100300c806280881501d5031000801c10507500784200030b00e1060030b6891405c680d00c280807244106109118490b00107005050010002e074034900051090021440c044000031200d40f0201b10558102003011f81182000484c0390800e220100840d0751508d44900c1c0140ca50036400102d03d810351340d025005054100820507681e54200c140020395aa4407611809000e0310410901c000ca845d0f0500c01d6851811881c502202540300980f40d00d0b4001a034481c3c2610034943e9a14001100410791004024260f2100749140c5c2c1c0c0e4941608100c078243c075220315409250008907002c0d100580c0414110300295100c61310070340ca544800440c500c0c2100c0d1117030094000e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 292689649 1250 292688399 292688413
    0x5060609120f01091412030f040b04031704030c021e100810170303100e010e040201030c27180c3203130b0a06080309040f200901021204050a060f0c05 66
    0x200c13071030020840450045c1030444000014034806280c0901c82101c0110161f180c2002040004203d281e259402c03a000745000c0742c80014101002d440c2440540d4104e000c40d00d21422801141001180515110710f01d21009554076051000304610400580d070f45420810b203180000d401c5038411079008082e24540e504a644d1130382d4501980d513241c0c02a500301c2504400c502e00043d40021281030141a1440c8a407601ca81c0e469130341c019030181201032003030410b1107801030b400c032014245100642d1401e002411000d12891504090b1850550f100b001c128129080111010b40c0c20740200c141166401d4030b1511200d00041c11358854002e0701c00450200000c0d50020074000f8180280e03003525520380c05040c0700b042c5a200d01c4580401c0307442274481c3e074134aa00240400004ac0c80d0560041005440d6000c0200705050100ca0403404010a2541d1024520011410040799607041081418045002082905e06070828000803000112031245000308004c26801214041c80340d054040c03915446402c803804 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 292690899 1250 292689649 292689653
    0x506150906092808122a0c0409112e0c0c03060c0302040608010512060403050a0306170109110108010806040219081605150702010917010204030b0f06011205060609120f0109 76
    0x40100380c2c821304942c1c0c49114918010582e1000448118600203601da01080b01d1000c9040e84038660055102d4403070180310404030071901e030b40c01105507191298111080d41c3d040c9074100320380004001c0e0f0196290005111440d200e1410100d030b110001c0450502e21240d82d00d900d4207801c0808583c1009125500340400b0106058150b0043c10a40e085030302d8060305a0b1300c0d4803e0080d0100c80010744c40e0b855000001140111740510f0050540075200c1c58045145d940b1400c1c264108500003450b000706070b540e20444024040300501070a202032091808044c694940800a03036a0740018001a1144040d408848243c0c18224002c10040001b1020347d10405280401e03030300c10000d10f02c52180604801f9a101c13140c86800011210b83c80d505866492500e414088825242c1883c1180160b02d903508020100111b864110458820301810040ea206031601100041c07a01c0401085201e8079030500c0b00f40006682c40310140c8022440c1a505000990200645c00b8034250f4600c07400c5031203500e8a910402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 292692149 1250 292690899 292690969
    0x402190e0f0d02091504110a0e040b06030c030a0c1b030f0e040c1403090a0b0c030a0b030703080a0503100e011511070e042414040204050615090609 65
    0x10128411202004410400c800b48034401c440038000a50003000b4500213070403049074207060b5000440240002a88100741d000c401d0440d40308070350303050201d10814492500d500e007500858a041f00c2c00c5e60318905605155100c40800d00019000032403140d00c5481042000f0b01c10600c81442c80501e610700078001c0c5803420050807408a461600b400651600c903a2840c0b0305050046054004032942c440b40c28241041d1809003c3d00090901c510500401445002055610304681d009100ca41072503541d80c10410300714401c4a20702e40b45603000f900440e0003007010a00d0007066844228903402d000341e50743e030303960340103010040340340c204403030030352030000042200c101d844180d08104460341c8a5103c00d0040c12440c695500380c511070103c815144000041c00038ac0341d5040e21028140c005c0002515181005d58801074800c20048880d1070760324001003106518050103881e4106801b035a80c00c80121040c84608604d1103000401c42c0030f02c8000904026544074403261504065030460421410044001190 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 292693399 1250 292692149 292692167
    0x11030706060f170f032a0a0602121005030c04020d0212010603020d1a03061b0409020307080703270b0c090307030605060108090f0c04110c0f0109050708030a05040e0402040219 77
    0x1400142d11004010180100040c1c80c1c400340071040010740c04c6c000c510300202074003680c0b0702d040340d0303101c44464032039240e005e00701300e42607510f40b29180268481820030b0f0301c191214401071200c800380c05440380811440c1c0f40400c0d440101001a1800741e521100000c000000c0e1142d0583e401402e00d1a000020700968158003400e4500c01d01001030240c40110a21406412507400003254103400a00c04502d60a0300c406008885602d0350403494102940c46166070100e80045481c0381c00300303155000308800544c0c03505c602c94901441034804052406d20543d450700300b08840c1c1c0d0044c041001003000c100bd01030b048095520440000b42160b00302c0c3e85070300e8184081c001c262401070214191001149400c000840d03005200e24160380100500b10402080002810204500707100b211010050060f044500307015038042100344100106a80100345030041ca040d0345070340500e0725504240540c2d50826030000c1158125816001201025290780c00010000c0c400e002603c582c0003440780c0e0010403642c01c48000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 292694649 1250 292693399 292693409
    0x1050106080a0b0604090c021204030c080d170601030b060c010c032009060d0b04060306090318060516080c0f0a0f05060906060f0d03030603020a0602070806010b04030c0611030706060f 81
    0x10300159156125000c0a5038030f12800301d60300503011721041c0544041136005046980003403044502042d1408160912980a50400e80b0652071140c0d0034425903000700001400520303a8600300307208550303a000c0b4a080c1c0c3d01c0500540d04060301c4210400b1155505d0099945004ca00790003040080c2c00b24102400400501c00c3c043d0030ba0040c2d842c4260030030460010341c1c40381c01000d0452440d000c0b90603020f400030b1445500c580d5004c0e5680785d012000c03d4487c40303088000f51003a1a1020a2503004001c0a003080c00c0750710650400c0400c005001900f03198001c142040d943c40a1855190120102e50a007030901c10042554140b107a840c06c01c0c10b000110010003074140c05602a0341346038030f030f00c010340382c440701c0449045800010303910840b4254285614603c0c1c41600030310340001d0550301c0340c0c0081c030818000d0380b151005a2281c5803d11404000f400141d0040090f100b82038030301491640d500c8080001403080d1006e010b038000c01c00f003501d1020300c100c03444164050010455942c0703840c140750f900d04441c050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 292695899 1250 292694649 292694657
    0x5070f030605100e010c0f120e04050f0424060b0c03090a0f0509180c09071d0927150106091a0313082104060608010c18090b06071401050106 62
    0x80040d95092014104030000801c0d1350301e03207001143d10300540d1442c860b80da045070f80510b4803100c0e00c007160015041d9000c5d003015550b050100c220620801c019900302510003407104911100344000109550382480ca641c42c441039080300b08440c444118014038541e0b200e80c88080000505120305207001c002030002105c102e5040d240036855001e042141016401141e4010a80c0004a601056130240400820420000b01d854030200d80012903c192400d580c80c40220300604142081240c0c0081c00841810f400d0303501007a9490070320044051003481a0f9030380400029440d0030304c5010302c00c1c0440b05031401d00341105011542d40e40c9000340080c940d0b20801c0e0300b041c901b10f41d9690011103403007220702401c00c0b40341c1c0e02015982d41e1502d0366107a00c10485910304040300071700c65201c11001e100c04d0340704d58022000003590340d14094401d401c0d681420300300e4080202d901448001908400d42a80503110b07085800a44095100046400c0d4421079001818401a54030008110007054104c181a0361655a03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 292697149 1250 292695899 292695911
    0x27030605100b040303080a0f06080115060816050f0721020a150501080a060f0f090809030d030b06120907030c03121805010f1d0607051509030702010909090f050105070f03 75
    0x1082141d010f540001000140c081010400c20601c941010a485000c80c00005a10340c0d1404070310308640c800790717a00d42c480c00100300c2003203615000380390140d110f880110042032184400400404603c114201c1040070400401c0030810701400e450071000502540040c1c3c8200e8440310300c06940c41c400316100300e4821003110149000075699000380750403074801400600c030382c880340c2c0e4030078003c0d2513890140b05d080b5981e08c1d00070844072210b00400000314040c4c09070a680d42c1d42c25080c9403c005110074040c041c103080c44041b0300302e62030340400c070398101001003c001c4054503100701460900c0e105a2002c7c2501c52490382c0801880709540042540000c183c44082d00d140000c003203038041580b01d1050601081e02c808a60010f18014000d0701c1900742e1141c01d00c031100b1401c0c0002071058004840035500b6901503411301d1010034031200c41c583c0056420307004600704000c560009102d111580a4203040d607469032440c3e02007006018031200721940c080300902641c0340611004083c0ba03035402c04500000c1c2840 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 292698399 1250 292697149 292697159
    0x8060c04080f070e0609041b060e0a05180f1506070305030a150e060409080c0604030203041a0f0306040207051c0503150f03100b011202071a0a0b0901062703060510 72
    0x400408840780000442260384c2c0c5d4000300443c003a001071040e640600c14511081010082c140c3d141d01411007521038482d88180788050110002058102c00d00606044c4075400703611000d5104181d000c0400350801095681e86e90305400407d00e840d12643d080f46010076081c0c00c06401a02951099420103400c200f60210903100002e0308403144500002c08105002068007810a50488584180200b20030b529011400d0b40440c600101154103030010382012030148410a0741d9a22561031210352403890b800c044401000d54060302c00504000e1055600089000400409000d9010041641030619142e580f074078002804a41c41129068415401c0032400141807a090795003040401c0701400601e03001c22498400320080040341c02c2d440c140140303890840504105e81c001460030358880c0803c07115914415401030100807001d0300405520741012003501740b94550018072411201185802401444d0415041c50345103c10300c2011144c20800c04040f0a00285410150044149007152882640c3d11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 292699649 1250 292698399 292698403
    0xa02090c130501120e0f0303010608010b04080c041d06070e04051305060a0b0a050a080109060c030c020a11210a02090f07020703030f020309060301060e0102010e07270608060c04080f 80
    0x208504229110107580c1842154800c4001541c1d00591140c000750403400307000c40700c3c6013059004c01a80300794400001402500c3c0d00c0140240140741410206040609028030703682c40707800b0104450301175035489c160703011908954200340111030720390f00c20348005080000008201524505015000d1428100842d00c101c101c00c20b6031026581000140109440b00010748000d08040010250b2024407400040742c07690f540d0110ba8001c1580c803000042c529950315050040d1140b0038111000e1616107070086009507000700350750001030340c401c5000e4140381c40b100014200814000c1c07540740441e542c0f410f209528a0010b08440894002c42d1070790119035501d021907140d0841102e0f00c0c00181c00201d001c0001a002d903882d030402c1032076401507030b007421842d0b00880e0158101768402800201d8584d036000c2c0c036503028070651801d15107a001070304c0da8905050a032100f0300b0600313650b000fa56402100030b091080d0785a004101910b07489058941c2401c3c882d00008150300680520b074090700580d48090000900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 292700899 1250 292699649 292699657
    0x7080c0604050d0204090c0e160c0c0306020a120f060e1605040b0304030e180f06010906081512070f0303021605090601050c0f010507110f0a08030a0c1704050a02090c 73
    0x80145a035107000d041005220041e80b0150040383c0041e00c581c0302d503000814001c4924043c2c102c000140b0300a250011003160f03507000203441c80c01480701840d0100e000c02c0d000c01002c01513030317001000941e6070546460203c42800030000007400083c601010b004000a01d6002802220b141507003500c4c0584842d10284810080d680008010580030070003001980011005558428024107280754040c4401000c501c2040d21118600501c0301107004000034070249040c40c54000c00c082c640040f03000d0801c078002d854200003403c41c1100104c41c0381c0e1107401d540c4035000d410849c0301c2402070340c1010ba40c0e581a10900c07a094002180540601c003016552010002e15580440344020400030f201c3d2034140040d81c0e031707900103030020115000317800c04020318150034001d041c000d403110b40e1607040b030a070240712039800d0041c0550320b10703915000182c5041c0441c1044050340d4100003a0080090140c490280a031603035103801391032a2500039903a040100b8045d0200b5410351140c025a05610700755202c2e000b0b81b1103489 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 292702149 1250 292700899 292700923
    0xb0903120322262511010e190e0103050105010b03040c0e0c07020d12121e050601020c10050a03180201020a0611090a030b010911091f03021213050708 66
    0x86a00180d0704030710110605042c0e002d00815400158020500d9038403000030b43c90001c0891140009245014240c4c24846100d0021850042850032109691800c00b42e01c4e503071608504106500c801d940050303880d1490810541c40b02c003948a812540e402d4032034040402440b06507040d51800e000083c451060b078044034443e941c001d40f4030b0003007414040c0d1400c13030800292600e504458144441d100588501c98040407035401031000b0080c403042d0100c001c007506000e80091014030b041c080040092065502a004e0b000451440800d940d0384800040303240607003c00036558461120061034a51940080080c40424002d940501c40800030040380c02046040e080300a00580c003a08071440451990781c01342c10825441d40c401403404003110b00241c00305d1601d030001e550307141480004204400b018410540302180c00c12100c1c0c01e15100800041c541c12641c0415030f4a45000c1d52090491031103541100d141c40100c0031904402c0c1030a6900283d000304c209000ca8551060300c80100d0407000004005078255 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 292703399 1250 292702149 292702171
    0x70b0609010e0103051011130b13050319141c05130605161e140304091409030901120e010203070c11011106070509030f0703030c03091203051602030a0605010b09031203 74
    0x4904071140381c002c0459070100c3c015400709125401c238089605000500070326803030150f1030b21034500208038004200310307912151095000000705084907854452407803a0340c0d005240c0746c1c40740141110040c28509654400e0410280407100c1e240c0c403e40090103055030001081c031071001ca07901c0322001d45240c42108848080c5c01041d009030340025403146001407414080808907114414980d95072220100c4440d00e84500f6000881c0501020398548507031070401c101d400b0148070605101d030505803a8491824002c0c100020420b56038414403803900b1142620840f00d008654034600710300010b040950725107044843d403a840648403d82e40c8a1444104500d0030840601040c0c0c80701081a1826445034000b81c1c2c16008801d80700310214010f00a40d80214000c1d200c0c0102c41810345402400301701c142d00007821141e203070710111001c65480800d4540200700c2c145d0394a0000070302e0000a01d8095440c2d40141400c1c140400490043c1504003e4144450140c084800603100c04c1c82100b01804200c820a0504c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 292704649 1250 292703399 292703413
    0x9022202030f09011a040f09050f07140114090105031e09011407051801321e0f041811161b0509130f0b0a1a0f0112110c03070b0609010e010305 63
    0x17500c0d2603404028614000e00d0000b42c0e1694681d00c7d00e08025035040001c4071a00144010405072144145040d18100d0901e42200c608251890004003800703038103942e504008020002401d9034118560032142c20001c103021642d10303d030504105002e80541038001c01c803444e08401140245004209882d115803100d8010883c0c1c112000044070b010207039616040b10031124810b0400b12901c20201d8500e0801d00b800c129a8a202e0b003950b80c20010500f0805004011081014040c0d08909900f0b81d0280d0780000d503081d0b10701441306e1030040a009440c0e100c8124000c0001c005006050b400300b518151445140340e000ea11046001d8000c00084600c19143c020081d00001000d0111444140c585076125022034801c49a05403a0a40702d03901c120f45151003180d8440740c81041d6180d01158140644d003c0b078a00400849983c0000c0100492140d40c0b540e2940ba6a6040d01e030070036010564410003140c50403642c9a455500340f861801100342c952a000c0c03600e82001143d00885114243d041c3e03a000740043c501 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 292705899 1250 292704649 292704701
    0xd050d0e010c0b04060e3405010c030c0b10051005090103050f010f030201051c0516020606030319030b0a0302030f01020406090801090b0103031d0a0b0a0201050a1b0309022202030f0901 81
    0x140081c2074414000380904051850001c81c000b64004a140341000040c01000301c4d01202ca035007447c240c200c0f60500c403070315402500207588422a924940d500c0301d14140c040d00d4041c0d82d0004409160441c80e4080c91881c0d0016055500002414420000341e909100b140c1315100195910b00d42030003407031103409490b1070902c05940514001c00203281d0104500c404101c4600942045500550310300054441441c260408142e040201d150008030481c051803508000031a90344c580c0c20200802002e050702e40c10000755030f030b480d085040006c54000e42555036025041859600030341c054002c010106010840202e018041441080780503544107005484590039510700f070380c90204850210000d81840d103440d10058880007803500c0208401f840050311141b1801c0b0290948500400803000e4038985100701075062102c402260782001e403800c0000d42c078038550021821f00c10a44100c2d1b524002c220b411880c00078290b50007180310704c2651281110503240e004034107003a07602e451401007059110040e0b0140f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 292707149 1250 292705899 292705901
    0x902010e040e030405090f07080109141b07020d0b1006020703020a210503120a1802030c010e011101020f030106090b07051f1e0b01030608070612020a0e0d050d0e010c0b0406 76
    0x5810701c1010840c3e050545d01c02c00501e1101080f5040c000865652080c80025038000c4585400341a005505000708110212000301e1240000c001290000400079810000c08604040f80c0c8120707000703001708a40c81c645d0b0403c03107000001540c038805498074070440014810300c04982c0e582503941c020000c01c2c00500e0310500c50300e0360080c0e4050350310200040b07100e0000520100000c00c5d40c14031100350410307a8500f0380e5410007264442c080d182c1d50503019904410042e070300881c84000302e14003400e0210810401c1c000490743c0c095488004040c0d507100046a030030030440300016504a90896540c1d04205449801c80c410b240240f403401402d50f40100d030880c050581c000308004a05014801c001030306808070020f0416a0b403a05c0844481655030550030480d0350780f50050b82e007d0402400101100c3d860a00010900f0362403a1642900c0c5901190582a80d44a03001105503440003e01d10b48400d00d25041c9036032243c007a24040001709031402c41d00c807925406540400c044a0300b010018406540d0307611958 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 292708399 1250 292707149 292707161
    0x30309090a0b0a0f0603050a060504060321020f150105030c01020d090b0d1415090c0a1b05030706050408130e0c030c0a0903080a0c0c050301050c03062809020703020c040902010e04 79
    0x207640310a0343c5101141d45103102003180c00a04055401040c14100780541c40226403203600100c1c0601e01344002403021444494290714103c1007500031500c07003510074004a00b04013803007601086500a085840700340003109801c00703040c2d80048094502c0120782c01c006994512108000c000804c0790644100501001c2c0b101500383d641254001042e008204000b0f1600040100c0300d8020355080d1550501a03418041500795201c0748010165240040d40a4090074540c00e115040c600c05a0240c44503042003018029104903079072040b401c1c8500d092500c0c0c103801640284590404c54156a180040c0400c81d2044c0503001e40d030709104c154030b1a121291080c1c1d00d80e01504401d800c0c0400e07480000000340c11040140b21929040e41e400750a90624034224403554881c1d8440c80c4268108010b20541c51000f00482e07400003c00c80c1c0c4403800e101044c0c005030049107a28802d100258010000007606146500240720b0300348030b03609840300714917050200412100ba603040a40029074024030740b4030f1750510364804 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 292709649 1250 292708399 292708421
    0x150c0d09080f07030b0903040b0433080112020a050414090d020a030c0f02120609030a02071d0105060715020304032628110c010f0e0a08090409020609120615030309090a 74
    0x5a892325840e0700fa44804c03507000c1e40c010300d03505000c422946c5a184100c1c00140c201c119800f002072161100100c024030350081802601c0420810186460441d91000450002003002038400d104280d400c0b031140d42034400c1187c3d15551409181c540d10025880403c5003810140c1c10b0b215503243c2041030721074500190030107008071b0f006060030003807001d118410418144155583d0380215a03490300310000a0a042880e44180c007001d071103011820710918940c030b080d070540700e0680c2e10300c0c4c440980341400d4208080803604004c26134800000c5c4024540e120641d810000c480110443386104005843c0d2403400003160030035202d80d0152030003136500321104180c00b4402c0e10310002141500c1c0d229a00344956114001d61900b9a40d208505032003c4103601840007080c814601510581056450710002d07031041042c41c42c401c5076031380d5480c811552420117a401082c0013402450326040c0b00c0c140c003a0307034101c140c82c240a61349150314125820f140000442e24a2000945400b50030303100c81c3c202ca03024100754084 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 292710899 1250 292709649 292709653
    0x1a0703050705010e0601080d03060807090e012405150a050306011404210c140d0305090415180f0e0d0c0c050613030b0601031a010c02150c0d09080f07030b09 69
    0xa200c0c00b044090042d800921042c8000d4900c5500d00f1404d0fa00c6c102d603000da02c609040c24000100702c0c412001c03030240d00300c42c0100008030b03030030300200019801482d040407500d40e40c0b10100e080c6110302200306003040aa9100303459a211403000081400d03031602560100f08001001000010010752040744c40011100c0d0700d00800e803c1c075441321310309140e400e41489990504c818003442d803001d00008a110000400803111010110207002c0c0201d40c000305421400703802c5c084001790800c015100ca034440c0f0031000036007a92584036505e6906084c41520701d103000e85416400d0410b20403280040d4802c8040b2554510020407a043c0c214074281d80051a005042d90701900040000038580c0754003000704140107030b026044001324107504d00040d80d004081e000074101840c101c89105105c1030b100280d07030b64900909088840704201d03c0001d03403807116031591030b080e540301141c440000c45000984140000701500e032541459183c81c907095079080c0b400001c00955000403401c10115248240083c0c0103015101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 292712149 1250 292710899 292710907
    0xc050307020f1c030b0d14010e0c120a020607080f04170c0a1503110d06150f09080a030804060b03070f0801060b0306061206010c050f100c08040203060c22080303041b1a070305 77
    0x1100c07d00e5240070740311034605075110030200f80a5403080c0040300d41030000729283c0320205001c640341d0740e94500c4410002d003c2c4000058450070b100c0240305403420480c00740d550365030b2140c8620000035281803405600145115207100d1440b10f280201c0c0840c280c82c02c0c7d00005c0ca8072040e1140490182003c0411a1400001001b4615480915000d82d80103480100c42c607642e007040d0007070700a03c90100c0440860806c24075041c103000070080480c52800268041c40c000440317031141e00300034004002500c0c040354140302e2940002410485503400c00115203284008004c526a62100084288800c84a031039000d41d0800c40c8000d105240040795800c01c00604d0440f036214003035a5900d190408000403544c146e84510455011840d0030300640c1004a400c0c43c000c0701c1814541e0100766684409810b151502101040c5404250070a08401c01c1001410a14907001c56450810b95107a60041c0c2d0150749155041103c0d20301c82c4d04440780b003001c4400b0702d12650041d140240e504031854110840840030488100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 292713399 1250 292712149 292712153
    0x2070b0c03070c050a0c0314070b0f07080405031b0909030c061f0e040803011a0f090d03030b0a0306140f100e0402010314010314011a0a0608090708010c050307020f1c030b0d 76
    0x503413040c0341308000100c0c6d000c0c254186142040846243c032801c59000c034909002ca10014016220100c0c44503003800e0721200c952625a20502440e0407041d010300c100a4040f504505490081100050550303000b407030754550040c0d10792640304005c02448079070701c00b901151600c04d001300d40142000b03034818480405516141d081005d11320a0f2019140d420000c00140403a2050488968880d6400440c0c0c519010b0000c0342c1803024000c4112052042d62440d100c0300c207050094012032400800180440340c0b958a81c60300c03000610980100004a00c9440002502112540102c60080b183c040d4440c00721850880c0c8820b100400070812410180c071940315401161140031040d01071845a51030b051080886640d03a421519041d100d452203501400100c500350311400301c600c080d0303132403403078400c2e802d6035440801440d214682e40302c51000d61030001c0500180741d00001460180d66254243c50f2644020b5498a076101080d400c1a02d1702c1e140d01c0300700405240a944041241d26000e8000c1100040c55 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 292714649 1250 292713399 292713403
    0xf06110109050f0a150606080c031b04080a1a060307051003020904021824030a0f111207140705120c010e0d020303010602010c050c0a060902130e07061202070b0c03070c05 75
    0x241c0a01c0540c0e03210301c3c100e41c00c001000c0600030f1a1060341408001e51881c1800081c22340c6400b60125401c07120000c0401c00059110001807001c001a8011560b515920280c081d52034482001c10760303008030040001c407a041c528008850040e00c0007030051102a007060704200e0301603030650f440c609056081100300c0740b541307039800940240c40d03009018441c0b000708201800410100b4090800403c18020002500d884444059079000008644005203060f0261121002092020a000d00c0010b002c90359016802e10044040e21454055070b4007040c2d411b0803180707160725000c2d881e002051500714055002140e14140c025080c0342c10030500104a80700382c20109818080b09011803001a040040184240c94090007480c04030040cad4030300b0910f0989410462520361868010040c111629840c00d8000c0d560703280130701002103074000010040c1c810b2804680b80c0c1c6206910400010400d401d4040c1c072030500c1e5200703492a458010081c08500d40c3d410505000c40d0340010175202c20300c005462842d01096003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 292715899 1250 292714649 292714663
    0x40e0c030c131509061b1403130306020405040b0102030304050d03020325030e0c0616111503091605120a0f0309090905030c0c2e031b02011b090f0611010905 69
    0x107440d1035070803041070860006144c130340d50b03800050611401e405120f072050300c0c00a088210541000e0021858040e201c0034900350310406c52210182500882c020044c0102c2da401401201c03070480d01000300c4085180166100c1c0000c980280c4260004000d6280b414002d400550303005081d42c60f06401c2c51517a100341218102c54500341e40010f0b81e9501004600101000b02c1e9481e00803c8800034145020007299203105c83c600000203280c00b0181d030711040c5503194031110b1500c0c02031000403540c607071625503012607072038000c0400f1010202c041040000c2c103060407142004100384a00103420840d8064854035140280d40034110100207100200141190305071040041242c410b801071983c1e01d19940c61149051040c0c00080d11501400c640158846204210f0b4005120341c15000078510305d200c102500105120034101c0c03505034032901c14406a80d810760241004010407891042d0b50000341c0d008603005800c03030240100c4010b00c2c1e201884014007135014507000d0303c070301000030070607005656800b828420 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 292717149 1250 292715899 292715909
    0x150a0302070b0a0b0a1e0e09033a1d06090705120d050403170403050a11031b0a060507061b020a022d0105030a020c0106030506010f0b040e0c030c13 65
    0x640441c00c04100040881180d81145900c442440400c8102c4001030340b150703413841107580e090b810054200304001a00070410060060113407080702403030118100b503226403210010f1603a260411050448011a0740c00c0c80d02807050b03040020300030011412109004000c41d03081081001c141001d0000448020000284940012800341c80804e14080a10101521201d024646a04054100107644e41c1c450155800c03a50000c541e007020709100d80c01c56802c0d11403030300080c0450081c000c554003482140c0c0c1c92003034a040f0941c02c60721400500f51020804c410f15a800680c007a0541404001251262000d40001c50041100040203070881b03074038080e00c03600d100d040000f40c1c100d0f0360664198503100244d0b440c0c0b8190a800d0041800c4070501074000b0403a9400a00c0c1404008004a00c001056605460201e61408020403580e622410040c0c3d60b07010910456203111005080030480d2104001a5000c4070030020341d4a04540710034000414541000307100444040c0203009003030307001c1e6a58201e030000345 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 292718399 1250 292717149 292717151
    0xf0d14071104021608130b0f090108040311030d05070e09090a200607060f06151707090b0a020f0c03070501050d0b04020702060d0b1504051f03020c0d110106091415150a03 75
    0xb1031240c84070702c00301b45980d01440102206000d020701074844c100850f03500700000d107024080341d9260301d8203448a0595403100350040c4000300b40ca0311740c80c8003603004078003920840d150b00155840600c01c02042420440795441203800c0701001c030340060712400408070005c02c20400a00281c070054049001c0d60066501605d01a4842403a062429a54400d110251100d06141c64480c00e01c205c0c003602014040410282074502e980009810a2140292070040c280000d009585c4040e02100290b46012441c0300444a0041c914683c10724600092000101d91040e1941c41c1000c2d107008000008005411449410076000c102110050343e03080014551035400310380004040001d042802510070f0b1440420f8403038401007200348440c0d5603414101d81d410700e030814454001c3c001c08000700c0181c01940c034400c0c6207105a805941240b80c108072200e449136140b400030015140d807800c0c08816201c0d105205090100c1100105580d0540810a180040f03000f4004001806800d40c030301c130a81d4080c0200c40006 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 292719649 1250 292718399 292718407
    0xd0f05120a02011e090308041203061503090b060319110a0518070e0103060b091311030907031401091a07030e0a08070b150f0103020c0705040507020f0d14071104021608 74
    0x19500303000640c5060313040d500302000030b085c031650b0180107004040e0001d4481c0b640510314600d010b00c2a0401d1014000040d2080003d00442d48058007508505038126040e0007a400020224100010201c0c1202c440c8961205103d5044d141c4041c940d64582406801201041011505459001031000c00e0f02c0c000111480c84e2030404001882800f58090140c10942000d0080000c1c01a40060702c0c42c80380d0444418000c8129804904018280104003200085012042103113409021400000700d0740201d81c241821003131b01e03003110700f2035036803040003042e04490f419040c6404c07051180c8558001107504001401084507103c0d1894481400011107007928002000c40400422010103504240c0d000c3c10000c2d400021800121024669440f560405501048040308488204488001800042c208008909040c0002525490303038000b00314151080c0700b1002c500078441c02107078041040c4841d050b81841010307941d9130f8404040ba5980d650064080c03049001c810381a181090f04140301d104e8003035035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 292720899 1250 292719649 292719671
    0x31b070b0a0f120b010509100c0b0f07110316062301080d090b0901090603050718031a060603071d01050c06070e010e040915020c1e0a020108060a050d0f05120a0201 72
    0x3c403110200d07a01141d5800e1510321030850340c000c0195090000f00710342100034070350301a004031018456000d016000088500034040340002843c512405507034107590746c1c03147c16280c0440c2c40c0c3d684928600700c1c041041e1412030501180d100d50141c0032500100306030590074641c00207000c0c43c140e02a00008800c1c2c00500444000c1c0d9042096400109810346442d41402003601c0044d04116240c4101024507803100005034a0380d00c02c140001d0803c1c03d94a02d207a605440381401f04188a548078041207090325480816058942002580e20441955035020328403441c180d8459110030039542114144101403062461410061010724800c02c0c0c0e60383c80b6050130b03c0030700004003440701240c400c600862808241001040c488090042144071b150000b698681c80014068900401100d481300c00e180c9000c00c0c0c03410181d0100382d1000d90cd000740e0703c01610b52511000c104030b40036280724040e4420300c1240d100c800580d04154000700c1c107004009803102524100c4101c240c6621100300300380142d6440d585661 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 292722149 1250 292720899 292720907
    0x3090801061d0a050601090503010c05030912070c03080706090803090610060918111e03010f0f1410020708120c01060e160c2f040e0c03031b070b0a0f 66
    0x1c02000c1d07004824041006564000c560140c000c0c2c1880200b0342c0320000a02164040c40c101c0e002448054000c2001900c541c0700200242c000365280c0070540590710303000c48850a404162074015801400d001c0400d855070343d80c11490350103024215040d5031a4000d440c089807160024501c180310840242050307162040042600e00e8094011704280034524509201c090b08070511468440110380c00001d40c0508200003c10314000c03200c80c0143c1c414450030707100300e070307010440134504a0314118031000503152640c00503007503030041e8050035000d075602d136005070150f1034076900c081d0142c032590050703500981c2c44007469400c00da050011088002000100035030301c642c0034130400c0010030b040040c0d100f844c200f400081026043c0b9030112400c1007a03034014002403089101c9000c801c0303202c0b4de840b0b64900040c280002803400c044000140b09615003c90071003202804108408200001406945051209030310546101d07580d254140041c456900041003482c0403400922440d0619140c481091906401c014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 292723399 1250 292722149 292722161
    0xc1d0f07080412030c0c0204020307030e100902060304060209061b03091503012105100c0801090b010302030907050111010902040e010e0c120c1338032d070803030403090801 76
    0x10018590104004203001043c814240071481c9030200c2c04550034001158503c03c070320006503116100109000300c15400d9449403503902000030a440d1071040c91b4100404031100c440c4080e401c5402000010f002851540c001c000050008000c94104100e07400080d1404400e544690015440001e10305441d103002000401000c81c94801c507491503040040e5141e56039541000e0f51000100b442100c0c0c2004400d200f000408805060208410b804119004021000a00c542000320b8680251705496520a0007241d11030348072040104803030781c5480011140c05034550155640c6558032a0007000681c2c5500030640c0342000c102c00400c800c0d21340d100351400d00f007102c81c03103501c00d01e00341d51440400100459404e0504108889041c0c001c04400b81084c098401c50302c51041569100e00120b00304612008205406204100d0181b40c0d02601003d06540d80d0f14400384203c020541c03003038a0940700b071060401c1030303051240c0141d4030b140760b86484251031a0001d03075048011030207040c414840c0010900c902 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 292724649 1250 292723399 292723411
    0x1011040b121b0405060d0b01050903030c071a0a08060f0a080109060b09060f1f0504050405090a050d021207060b0409052d030f120711120a080f01060e0d0c1d0f 70
    0x2e2854070b40f40400040780b0f4071a0040e03110401e500c0c0c0072403442c9680154280c80500001400341c1c0d030750f5200e103502c0340d8851449005172005036015100310510180c0e07441c2134824020040d115404140c4844040080c0d441e074003152654881c002e0400402c0c42442030291000080c4210008219903840108202c80001c0051801e4003446101408c1c400355502c00030350340c5284000c0070b40c002010740301080849052040d9007007160080d00b08400d21101e10f8001440b056240d004a041c0e80a107040064201c0e01c46141a802c0c2440340c0003404801c001c00c503150f20090104600610010f6580c4859640a00342100200002d10403010504611102010101150400c46030100a0740c5000841c040c082800c0c02110302c000d10b10a01200068040c0d8010f4113608014030001045a00185484134a281994007150700c0340001381400000c519060a0b034280c00d07043c1c0344162141041222501e041c0011403064020664120503a1100001d050074100c480c103800703825003803c41c825854a4210303c00e2014001d440c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 292725899 1250 292724649 292724701
    0x10f2f03091309030206010303080a0207050102030106050705100b010206010b0f0403060617070602060f0c18130f0605030601210318291309020a02070b0c0f01060b0304051011040b12 80
    0x2c443d0001ea03020602e41d05613945410b040d8440c0d191001604000e015000300144598400400800d200b03030810050960b0501c00e0040343c0032a40c0300e0490701c040e220714480302c9000da44008014000c001d03459000d080c072506003540c42410182e4a440305029500968003003400103410f24160a8041424030121024002c0380c0010143e07810007680c0803280075001400b401000b08082003800c603801807406100d0791170700300a102c0d503a50207902d03101741d00070300343c000d82d00e2601484c003c3e0020303d40c280412014102c82c11003440c00f80f4005000302d803a40f12203c10808400f007021402c2c1a040f01e00e080d4403220082d080355a2107444010301004480000040f03c00310191000043c4009002c201c65902e0100903203c039105c01680702c40448000340d240070b00d250000e903040c04002c81c426429900000da181070420200c402409042d6880e450b28091b03200c00d54024200303070055400b1081541d2985c1041650500f0301c3d0210b0b103805e650740c0b03500c103641e0441070702118841c0b8084e0074002c02010085440000780c0071500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 292727149 1250 292725899 292725911
    0x60a05120a0603030e330904020c07060305100602070311040b0a0807091118040f230a0c03050108030f070f0f150e0d09050d05150c03010305010c0e010f2f030913 71
    0x88045030448120032600d00890148071b10781c200700c0c03818180e41046201074419515041100780b036070f480b83c0381d030f0041e1800a0b18120006060040542d4001304032802c40d0044e0410743e0135038881440403540092016003164440041f151651540c00542d00209100006040c40c54142075504056030010103204003481d034244034500c01141c11740c0c0d000242d01d200f00e400260301031101020314068000c6001c81c4a010b00810719051360065240744d0584113a28510041002d60000d40d000d4007124002c0c041da020342d42c4203111117201c04078010010030f0124001d8580b482c07200b45e107a542140d0400c0c0040210380d003c0860111042040481c0a00244d1400359030240c03800403421b2800800801552003140d01c504108084802481002e001e08181d082040b4600070b010702e41048a41d106038400c0c4811909036281000c440354183c810484600544416550070a0700032404074100c80c80d841030045607815840c44160901c2c2d0440403518a644004c8000c043c54517500c820040060102490304c490111900b006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 292728399 1250 292727149 292727179
    0x230105070201060510111f0f06150906050d060807170c0409050303190b090c090306010905100509070203120403030f14060a0e2806030204060b120402060a05120a0603030e 75
    0xb45d04030f0072901280f078501c010b80c2030101760318a480d5038130004200414510489170412a400d0b0804080800700e100d0502800f541c401e0881090008140c14070001024100d0500c181c5200d507000b0030760042c02600c0440c0036078460f0741c1d950034000c183c1c0c8a04620b00c40b141810030741460074400030700140021117040100b28400d0310340c25261322001304404994146504646010401031380b04040c100c0000d03003402940d10706103800304126405803595510a12031a4000200f00e011401098031803d03008401c1d00c810341c039141c148414414007500440940c081071004011039800b484100f44158000da4021500703407540c4803280d04a550308401350341842d519008124103900c40b07005180450700311708040056075036410184440f94885415100210400c4005100d1107100c5401c0072080d80c2c000c07507003008895502c1141012521480344044001c910400c0000e015160100140041c03a0003401c00601c2e014000000c2844440122040f450b82a621181401410b5110b2002d00d0340315010703641c00602013085 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 292729649 1250 292728399 292728409
    0x20307020108060303070f11030118080307080f19020a1101020d06030b0604092f060d02030a051303020a110f0d1412030903070609020604050d1103011a010f05162301050702010605 79
    0x486c0140a10700e5231107840b40c16480c00d60114000c1034111406216004031807502c070b4201e50054034880000740c1301502254404027015543d070f00a50303000203200b182c2c2d0740d985070030350117134100b41004814070811000d038000000003800141700c1041000c0d070000d1014158509034503a0100a008240210700c1e1544000c005203200c91183c2c601d800c442c0600c01d039540030300e10500d000c559900742680c11001c08603410b9280031954020f10f0062104074428092560340916511130010715420140c01a13001401e13200103d080c2d8000049981030261040500e1301e60000404c0c00c10701340c03280403030b81014900b101da510b0038001c0c4042480d20700d26050542c83c43c14480129540d0b40900d04003d090f1a036034525900440d0b8400702120020f1202818003027008441b07091000303841c6509039a550095080c80000855081d05014580d403490058548006550700010111119044540859a20340280c080031010401301240c14500e560b00c3c030141e003c05000044194291072002d0141c5055a060900902c80c50b03940d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 292730899 1250 292729649 292729673
    0x180a02130e064e0102070f0b010806040c05121606020d0311070f080d0912080702010509060708070f050702031b03070b03150108091c0207060212070b3402030702010806030307 77
    0x80c0c580c001184400c1c61000003c00c4440070036421035031000a29004014403a00b0002c0428011240b0000c1a81c1c0c2c2c003a855250b240885000b014088400c0040c0070515011034504582c02c07412080f283c1400380342c04042d00355034050b0021005a4482c0074960045035040c040e0b840503040041c40c0e00d00700089541c4110500c01251001403054130042181c20030320040c1e0303010103042500a00a02034400b103456001e008824207a65410040d400e04000078200000015a1030140f0030303542e2848a290382e503103000c0701c28101d1107a0040c01c10904100e0040035035410004581d50f00d414076000040281003004261a1244562004102050902c204610344010141d4070000460a0a1000085d502c0340d2030182080390700e40d503a07003588413075194900b0000d82c0098044141c03815034084a841d0412502c00760701c02d002d503800042000050300c0011f10030720740d02400390500b50017010b0507404a0382c1d41003c51040798038200b80040141d02c04500d040c00e41d80d0101003036400c550260301541c605881500c0c1c1100800b2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 292732149 1250 292730899 292730989
    0x6140409140d180501050702090c090f03070b0d060501110c01033204150e0618150403050c07050103181b150504080c090105180a02130e06 61
    0x562a00305106009045804000025007903040e10341000744030502401c008803031403001c4030350169040045050350280c0110b1b02a141c0052550070240d49440c3c1c501080e5015071078060300103071640b035081d00b15202000a10080e14041d03840d192103041c1c2d040c68404403040e80e40141e0402010501200b00c5200115600d540b00d282840c0110b003072180a5058107000d104034180f98030f80203072840c403103002c040d0b0040c516008a00c0f80e2900700d02e030814201c0076800d5403600d00c6903440c10380119004c10300d10b60040d008103102072203901c1507804800180010640740d15080703030280c010460000d1814a045d109005500261400f403e003009a9042c0706030f07283c082d000ca40001000f4038554070342c030010102d408030004000c21080140c04e6010480d641c009000740c00502c2414450721800c4408205490102c00c400e0584001900c0300400b42050030b120f0303812003000780c0a180030b03980c00c100e50900f450044800d407002e030001c18550380a0f400c0c0f01c802e000072444444103041f02200982001000310000c048035000d804 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 292733399 1250 292732149 292732151
    0x405010f030b09030f0d0911030c011202031803190905030a1203020c12040b0d060e1e0c090307031a070306150f02070e011511030a0203091320090310061404 69
    0x651012400303807441c0b00d0804d44104045c004a000c150400141e000400b800c0d12441c81c800691080c5d000b030640d1801c040d0540c60100b6480d08000c1c800c2e420716806142d0089c1c41c50324508510950302041d6003140d01246248034026001154100c000b80c000104000500702034000b000820815207881400b0382c4100152020103400040e2941c28200c20001485c82c031806210b900d03a1a41d496080c2c80c4181e00032901c01116505104000074030114114185204030704400004a0f41000c0384420781242000819400300f40c0c0d4144248515030320300f0809600514840c2c484840707118131541c024102e09000501820030141860307400d0082030340c000e500071841c551605082040c03528143e000d03070900455070060340f81c1d2100b003000002d8a200325502d41400001545540e9030600c1c040e80141d84034411001c0000251303208000720402e0f41030041c400b44070200a00c500150306980061040c04a00703100b000c00003413031008030311484c0d00e02d402d100503403111040c0f440400003c0d2820707001c9441c00002245d140d11a0f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 292734649 1250 292733399 292733401
    0xe040c0806090304051e041b0807030f0b0f2403010902031005031f0506010e121e03040602060411040e060a05010608130b0126030a05040f050901060e040b0a12150b0405010f030b 78
    0x58951f6004200500c020300320130b01c00b4030008e00d4000d00d104412101100080d080c1618230210241a100b8400c10702005006424005001130901c503800022000707004c10120f44040d1658480e6459000e14064118001c0140c0e490401d50701c0c00707980d07040c150001072180e00202054607506501440e040c0d103d44184002242c10303a40d07000143e0391207003004503071a0412413002001011720400300f844c01c0c0d02541d1100100403251150612039990041f802017038003690220021801207109090f030441214002030000c1880c841000c100e90502030141ca000f00390742d482c1c10041c0216500600c2c1c0c07541c480203101240e00c080e0f010340ca83c0111001d06115504981e000a40c003034146000703142d00080200300181c101c0750358030440c5d41b00034403030f81c0300c2d1040403030001c5541c8000c1010702d0309291081c100d0740e4a42c0d4983e1020718050402004284091085510468108002402040c85615007070424000c281c14907088e880c00822600b5644150b401501c52858040180143c641c140d0901c000e0303035017201e1317a1481 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 292735899 1250 292734649 292734709
    0x90f06040f02070804050301061a04091109040903171b09091b070507061101060b030106030c11120406081e040b040501020d0513030f090b0301050d05070e040c080609030405 76
    0x345044078102448600025a05050141250080003160703070030b07002041703050f980d4840d44802c0385400d04041a01c1004010400c11181607400000701a18442d031050310300b92403940003e00311561407c080300071600711046070408101d10310100d41e1000b007038400400c05820413800349000b440b4a1011900c982d4041c8080b030911803903006c5011084c0400c82d0801d50703c1c0c08500f400b030b07039411a501c0341c00c0002c1d95413015034071806410f0140400b100c00e04d01d101c0781113900744901036001e4100c40040c9010402d0300608100d9600081180c14906103512406075034490501c0780c02054180000e1110100542e00c00324103009000940807540e000b5007003040d00c40b140c0c40d1450302c81d01900c259000f40c1105e0b4106814400c0301d03056402c0f60210984a510351080d520b00364002500c12213080d02c12082905005c0c0010040d50806180011105110310241ea00e505c0c1c83d144912524481a2015180d6000030341081c00342c49810400b07290040c000800031420700d40380c68001000050911020208004d640c000c4005d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 292737149 1250 292735899 292735901
    0x11010c080f160605040f150c120e100603030503010807080309130b0105040815010501110c0a05010f09030615031106070b01061206080a0b0901050a110316020c090a1b0509090f0604 79
    0x350190302080902c00340c00d060401244031000c2180070380c1d40e487c82e2070003c0c1120f000c17031040b041d2100741d64850303800f82085000d01c40c0041044140550789800340c010b011088545a10076a400740d4803070344819031654100800545002503580101c85294030400031030741269500890f0155905c041480803424001c03c100495240c0610b60024149104155550002c81d52030383c0703558141c51080e03071103184c039184c0007008c0d90741c2c2d4a02015188d00030003000380c180702c40d5114240b041c9506915013000d45802d6601e07510042110302d1a1922500f2500c04d1f40e0500812400315a20080740800700d598034140700c8141c45500501c0d00610031001030004101035407003180255040140100351035402d588100003503051102c15040200c90300c2905510307180c002000c015461241c00d061840c6260b62074150364078000b00f0700e00814843c041004ad4800e11111510359a1100c80c0540b242604c4c80b80410440902108140c0320410303c50200c06000040c04206243d07112100c060358441d02144401102c0d403980d00c0820 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 292738399 1250 292737149 292737187
    0x40302030a0c0905070503060d03031a10020c13020309070e06040605100c1a100308280203070308010608010e04110f0301110c06090c011b0c080a03030911010c080f 72
    0xd400d80a51a104020310101e00b02880454205010501c015915003204585610003110b181e6404100d01034400d002c03e206e50301102403940c0890040102283d050002172039001400520300059205100840240c10700c07500f45110300008120950035400d1406525844500f0380c05001401c44003000000c0c070655071a0801e40090801400140070f00109100040005404d95000d95251f170803520703a101081100c61042d4803581452445100c1c490a650b14940f2940c0000c01142c07241c10b480440a0084488694400b0a0903503600203682d54011442e001c0e2008905038450f4040c0110000104002ca06a0303080581c46540090304140340e00c42c3d08000350b00c0408000500d50950318251718030610400300002072550510740d108507084c0342d5400440556800c11817401c07900060460806103540030b43c40003803540e950702c62140801c5664844c0304031031401070004001d0300026120142c4134148404202300304c0106400b860000354002264460401c944101c0d4925915900b0000d6010103520403d0b2803d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 292739649 1250 292738399 292738403
    0xd08130f0804060825050f07060e070b030403020d0203030402220912022503110904020d1401020d05090d0807050c03040e0a02120106181406070807030903050d0e0a1a0403 75
    0x903544a076110300c40102120821035410b40b06000d441c0090003494510101d007005c0d2442c654401e450280ba0803514911504404000c850707454132441c440f0740e242401d200890180a90418482e02c904c2d103420024509aa007280c803c1c2550401c0040c800540c480981c078030b042001e405034500611040140c0140105804072000e0207c00d14580c0100c98285d0109840c40d540b000182e204580820010fa02c3c1c5002400307200080004d4440c40c5985c4107403c06003040d0307a0242c001082d0104000302510340d440114004409408036075400034102404282070710807035803c0b000d0000104646a106031000d440d0700d07005031482040c81408076100b44104000c00c01c07100034180c5596440303514140f0289040c00b94001c0c2c499042d00e00032078400860036510a000b01c0303402d0303c0c4a9003003002c40ca25020300c50b04003444440529800c55810420600840c81c0e450091256078880e40d03400520314a107040c00c43c1080d110281160400103500350409103a0303503c0d08a80c041d1108042402c1e2010040d0300742e280d6601c1143d01c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 292740899 1250 292739649 292739663
    0x309080d020a08190e210909040501140a020304120810170a0b0a020a0819270b0a1a0603090f06040b041203090c03030503040f0204020409020903010e0d08130f 70
    0x100450345903103d840a40200c49181000d02440c0ca0510403006481c000011955254040303104010710041d01200000c004008041c0d1a160541081c0482c501010440f81070b1281d03034440d000760911130540f0082c10b0307001c241840d0850441c1019030740d280f00d13207102003041410803c8480c04100007124903c1c4200081c00760344400042d200c080303007a40d5240d450030030040c0c4c0c1201c030400010f01d504942e4000c55003100203555440f2455925a05015904060305400c0e000c03c580d1800d0381c00400601d082540c080c1a05414038500310740442ca817011801000801c407241080c01c0030b40301d070801940044030000800007100c0711070700c95843c2d0f0249450200c0140c0f081405200c0c010601091045000c420340c0654000c540d848240088800280c00b80c0343c10810007040300d43c01030700400c00f0922520107550050321070b03100b00c001260250005420b03604960410f1000d103500203030454080c542407150300d403200104e00c0501012642400702410900000f0304c0c56400c00078006484040200c4031201c407040c0d590040c3c0e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 292742149 1250 292740899 292740907
    0x313060234170c010e0402040e06100c080a0e030c0103140a0902031c1e03150302040c05160c050112060513150902030c120c0c0601091a0402070506040203010b0603010b04060309080d02 81
    0x440b40ea0724044040c006000c1403d800054030a401d140c001c81d8240d401070300c400c9445032641070500544544203408942000ba10460050024a80c20024007040362a959100c110782c01003410142421012032446052604c1c004e1040185100d50240c00e51100e1103110008a813031550001c00d0074648015802d44100c1500c980641400d900104441003480c0071102500004401c10020341c21104100540e0f00c0100d458401000186466042100824154038015081148056880f8070454000340129802c040303505042c0b189503403002805285690310361003440614540030100f620f1020220b07004281c280c4488203015481c01e4070404c10b00500741018215501e00e0090341c144c08540120302104c074107540d00c030040b03440f040d100000d942c1182c0281c3c01414240e40b901013802e009100002c0b004941c0f983c3c11050340c0041d665840640565405540070304040d03d0144101801c640d11044a0392080b4014801402441200d00507202a10960b05000611541d18100b1044034001d0306183e03410940002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 292743399 1250 292742149 292742189
    0x7020a0b030f1012020607030e120604140c2404150903020a05060a0512180a08130902030103050307032307060b090603060c0a0c14010e0313060234 65
    0x1800452041025804096080d03d480c806071600d010b82c1e1055800080c0241810340142c40c206c401010790354442e0030416102001c44002c9002e11502141d03000c01d6400110400c0140607100c103402e0b1a000c0400060401000710700d00003440c8500004c02103130404001c10700c0032100c110310004c480140030100c05004985140710401082170955010413806001c0b440c0300000c03141001800d640701c06959840b050308103480c1401200b2642001440c0700300320700080d0b40030110318000303200c56010b00b40100380542c0e4549140c1220452000f9a174030480c448c0344100010008140c010003521001585468a0b04082e8900c60200141710060385000722802c6000541104204480c0d200520303014082d50200d2103503486100b0181c403040d04469406020008000310034860344184408207074940f142e001200c1645000712480d0855414180856180e800050101c2c1207900c60003540009100920041881c5003030440b84155000c48c5251030b1018120501c6031141c29403c5841b450302900180552109080400e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 292744649 1250 292743399 292743419
    0x1e2106010603060b190e0a170a03020601050316050603090f1e1005042a03080c0102040e130201050703111c09151b021c0609061b0c050c04050c07020a 66
    0x81c4210340c0420f01e0110300042140b150015601d0910103410001011880c80030251800044402125800030f4415008128110f41c3c61140d20345508034401060301884a1074007034641041a00641c0c4242d02c5078001c14214541520b500c4207444060b00e06039203d48078000118a0f10f4100d40b5500b0701c5000360320001481e114850b4099038512203c6040380c040c20100700c01c14046075000d40d000ba148000f240a80190b15036200582c8844141708002052a1560381d103404c00b01c0c3e00100e8080c1c80e26500000c040045020018403583c03c01c0618030740c28032101a82d80043c005200b42c85c0c004090101c1d4014510070fa5a003406020a06543c41074a00000398280b88001c201a05502030f002c11019218900011580304414041c400c0700042c0d0b043c11542a03580802c000d05056009902c880d42008041400055142c09040103d074410000401c005034420041210024801485010828105502e601041c80000d641c00004400d50380014580c8851050040ba481100c0e400303500180802c6c00020301003c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 292745899 1250 292744649 292744651
    0xc10050c190e0f040b0d0f080306180f0f13050a0302250602121e04030606080601050d05060a09050319080a0518071a1603050d1a1e2106 60
    0x4a610040c0c10740e000e5020a446441c40c003041260004884041d011042c20a94412005498014080e24400c040c07556000d5103004038400c04c0701c928401105010507400c3c002c4604445e0320080e0b400d122203180000c45c1030080c0c1e0008001e1461006480082010075511400750600030313400c6001d07501e0310400382c207000c4e665044d03040b0150345c954102401d900c903010741c03200c101e016142140d0103000608485500c1d501315400c80c03100c0b00340d8641824218524140840300030300c000c0d403040d0303000319801e480d01c0213880c10282c059000c0d600032081500c0e0b4a0000b540894050390140b20590300040c2c2d55610f040003461030262190091444000807081044c55412000c02c40c80b0f2035122000344000c0c0d03074410010400c0803625020501c290700007032082c0f2000070618444410058000081428600c04c0004440380044441040d0041000042c680032144124000d00e620021180c5808008148180c081186011108010271072001419012106591004440044030048040c03022080d18050441600c0b868 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 292747149 1250 292745899 292745917
    0x20d091208151201060909030f140a05120702010f020a0201090221070b030a020903030706060501021e1207031803050d081e070503060f03010f1e05010b090103020c10050c 75
    0x1603222400044148078003a10791140c0020020a4850141c100c1402a2000140d6100b0082d54076010007280d4907000d4801c40c6e070824001c1d81c0b0501c500f90252806064400440352500320000100304484500f50050102c2c0c40319039050140314801d40c1ca8100c00c0380104085622108010300014007034000560540200ca051030003101d60000c28074505000121806000b0304c62a400c1c3c00c12074082203d14082c0c0082c40c0c0c04002101d0151034143d207600002d040da0700c083c0040f105c0541d100700074486542c1c10072004160181070141c4945034407841c0303005a079892150058201e110000109401050700c1044030a8080d404d1126841c4040d440c0d180c85912400504103940c002071040002400c0c2200303c003541e010141c44001054401d80319000d04071140e500080c4040c1e04601080000a12900c092003001010804c0010000b10044003240701d0103100307000310241400c542408014804909034500703c0d459401c007407d005a0790390760318482c03030b082c00a00c1d43c604440c1403506082100c041c01c0403005101d106 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 292748399 1250 292747149 292747163
    0x70c140f070306020c1e060a2301060f030e0a020a0522020c1e1b040506061909080c010302090604090b0d0209130b0604060303080f09010e0f0304150e0d03120906020d09 74
    0x146d409541500c000320411006001540b0034804202e455149621140030b0184030780082e03107009d0090041d081d410100fa444a00003800d0354100a0030a42e1500c240d0441c0720f11080540070481c45074000030920400c50082c030703114001d812248089245a00b146401c1500402c0e4117645a800100d552034aa00e0345070018801030160141c40d00c814000803420340c2031411320603201400c2000c42010702c070061000600c0190011001c1004e480805070244024500c13480710345e21114080d0a012205040650343c121040c1071500600071131806e40d440200b660142c450384800010f041a40e44009072070031500b490b019401c811940103102c0582910740e01d00d80841e0060302944103036198001804100c07030321803202800003002800890030401703031b0481d5940c001d000385002080640c0799046070360404038120003100700c5c1c0d400020308010700c601c0242c0c0480302c80c2d024100301c10301c0082d50010542c0b030014010014100005c3d03041181032030285070300101140780c004100315142c020036481040101b0360844241d45075 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 292749649 1250 292748399 292748413
    0xe19080d0e0a0b15010c140303090d02071503050919080c012315031f0b1201050903031803040807180b0d0305090d1515031208070c140f070306020c 65
    0x11503000500000d40d40d403016030f84507180d0711400c0f070141c2101c03030b181850f0410020840c08030129180c02118400303c1c5030000034540d81e040c110019490500204010825501b00700300030401000d202c00300c181001c3c154100403131982d4511030018201044c0229005a242e8001d80c40c10600c049040605540310610008100d003082005e01c48019521000c44040c0070803419001400c40e800b81c504400d0744400c06805c840b4003511032410b628086000301c901c1071a041c0c0d1414955603a2134183c101c0403180b140d08008000b41e003840300e40c0ca610783c0300c01444440c5a541401e10052088000c008940c0141444010b9401143c2c403074030300c6448039941030900d1100310304091484640703280c1114050f07602c6a1540b02c00b89810a40350500071300b650a03403029200c01000741c03003025180b00203004002405410904c2c000d03516081d032904981c040d0714400c40c40308110043c0104180307280c0042124981503004040a010846218441c51400400c14510705850059140003c02c0114039005083c040b48580300352150 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 292750899 1250 292749649 292749671
    0x30207030f020f0705011202070c1403011107020307090c0203040e040b0601030509011401140111010e0d02010c08070e091b0c011a01050901020606060c07030206070503030609071b060e19080d 84
    0x2840d20b00ca100d5a03d10740026804010310341c080c0006243c403c0001c2805814100136444441b14510142c3c02008140c0f51500c52004924080c07040d08003001050300e44505240c596000320f552614140910001e082e91400c002100c9402041510f0060510b00d015403903600e03045c1741c403895006040d12075902003401d043c0400e0040f40103006800301e500c84240d2035501c41c1e20300076280c4001d00740e040059040c00519510301c3d403a41406c5c01621a0024641300a0410b006124002421a142c0c90503a4040210b00c4c1e052000c40350340f213503210040350360465070201e16440d04c580c0d8186100a51030103650815000941c00d00c0c000e01034100c04601c40b600540070161004a5005440a01c0303152409401030b000400040c1e250b261000c0a440100017600882d09981d4803940130860a910002e0251620b40c00030040150916040007080d80c0b04015140031810310310740310385d0b00e030b803c40440000070301050300c4e010040000c0400f0090240c1500308031020030003c2200b82071130a100d500c1811910b22483c145a02c0c150 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 292752149 1250 292750899 292750903
    0x303090201023901050c0d080108071e0b1c0504050c0901090203011d04060902030f03071b030809120f0d050d14010503060c0c0a1a01170d020309010516080307030207030f02 76
    0xc1c0c01900500030303001900c1c05210204a00d0350140c03145051102c06c1c800740d07401c41d90030098403106162a444184083d410107040b28640f510f07aa00c52070208801422103446c892080103150115a140c0520300d882d00c9440085140c110200410821404e18040820041c820009543c0131189415202080943d803103092000a903c400d00030f0f40e203544a446841c1d842c241c030804240354090f020f034100041105659000a0400010600d18100c030341c8081180b6041c880c800c1c0040d498043c04089c0400e203d480e566481e003a50060016007031213031546030014640f411081c046c81c84811940025581e01a42007100034206400044402000b5880c01c1e4503c80109035202c4c1e003c1c180c4800500400301980c0308903082c0010b40c2309513051030541c0150342d40c000016005040014030090a000b001e29990704280707808002c41521560000386912540010380740c941c001c41243d40000d0207203842a83c4503502924a813031100c80100041c61003800000308620140e05a0192100354469030315420541c0b40c41d40226 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 292753399 1250 292752149 292752193
    0x160f0b18010e2a04090b0105130603020a0303050a2106141912150f05070e0103021603030f09020306010b0d050f010e0a020d11031509010816051318030309020102 71
    0x3980614000282c4030418840302da48480f45030b105110701c21402c808502503c08102e000c9541c1c1800c040140920720f0805501c01c19204103510400c003051840e00090650001ca210203402d0103000502c03408818840e413440201d203440030f40c581295182201422000300715a105a650305001a81440300a18011103481c49a000200d1600007507401c268400c502805682c03000c444e400c40071014190840c2e200d006244522404000c000f8062030151405803003a0304d90380c0160304051041020403001c0d0321175000c0042d030b550945400101d2040c1304002d040104030104c3c010754140314803c000102282ca11000b00703c00b029854042c001500c42042460a04a0a0040f502d80030303004400034800c4036a5502030a9020386918002c222507110315002c185030350003958402e224007064090030150381001c0c8001401130100b24003d04111142111011619109000745c0e84500000c000140c40f00000d5045070740851075503d104580c010691502034018030404104074003500422011100041c484080c417 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 292754649 1250 292753399 292753421
    0x705010c020609060a02010912020f060610021b0102070803270d02010909090206090d080d2702011d10083702090103150b04030c0801021e160f0b1801 66
    0xd2410111100f0811102d50070180d840b0381103668480c1d61380c01003441003420008010054011b80a291041d403030181c100940144054081c0c894205038010842d4005288030455201c801030501000000c80100d00300030051307100c101944008504c6240c60789540c05840a40c00045407030701ca00805107c18088803a5a240b400307804640a04000c0003c0c5000d500034000e050f200074041d5240c1000c5000066034602044000e03a10a9404584668a90441d100d103124040c00721036003d40c40c4030465403d05400d0f808a10081c1080b081503d0041240030403058450440c800415203180b003844028000c1260008607007040d00565203150802590032802284428601c5002c000b40009642000c4a00a036205a90740d41c1050350b02e1070644248146405210060849000000c0d9200d1a5040210403601160440f0a05910421051120310720280304000401486d8038142d072100785a0350560140c1545c520054052510b007602c03102001807116a00b80300d24510018986420101c150b014200d407803464031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 292755899 1250 292754649 292754659
    0x50702010804060f05131202010b0a05150d1107021c020109301b1e050405040804090c05190309030804020f030a060e0d080601050a0503040b060f120f0705010c02 71
    0x5944114076080d482805210045442490794400e00200c40c0101c4000400c030840c143e400c0100141d80000b5500c60602d44020700880307040c08001245002c0910515110340040c4444803c1c0605034001e9071480906400d0400c0341200e40c0d00f01c7c05560384070000880c45411008151078904940610482c00c5a40681d5034034491410611100c040c0c1c40d0107006840114522062075608041c40061201400d10500803008840c3c600c0f1020a2411065002008000d24084064107a90b070008071350360031600c080302c0104645c4c880e8200840d0600c5181c0203640f01c01e0074003014001039600880100301420000201c40804464420210704030703860040000c0008001101040c0580b410207540c0995031001415580c540c1c10b55500c46048901080c01e41d40260850601161400e8202110070381c014006e0a00c00c2c0380080009000705540f10041c00141808031000c040b0340c160301d0300e0f160b50855140240c8688250900701128650f9a0302c4051021a40c0c451600301141c01d5101f2080203100c1c43d40030300307 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 292757149 1250 292755899 292755907
    0x16020303010f0e10030209040c03030306150509190e010f0302010906030e03030703091410060807090b1c05120f03090d031b030203090a02041b0e0f011d0d020618120a0305 75
    0x80140344220180c4041d134824801e00d400310140e9100780065001300c0c4120400909103155150140980b4510741c0010030b1150084600600e00b038006044a104d0f800407912000052402c00c40c1c0084001903800540720780d1202800402e000f12049603a0054a000b62101c5000c139650b00000c80a5444001c95808660428000304507218080e402896220348910742d03000c01200460002c500d084400b40c40107034034a8a6001c1003014090a00805001d804800c8050212900782c1001c6051031003104588441715000448242c00c0c03060600104441c4480324003102da5072541520882601d40050b60050070034000c2c11a4800154080d1140180302e100c120301c0241200c00302c940a4000f500014005403042c0180c03007070781006070743d10700c2104101c070410390000713284001c505802060b0030550045c02e8014000c0051942441c0c0e000317403101d440354045c4091280495403600100d16010700e01e00000b50040008030f0007040d240310044160303030460300c10388007010f040c41c400d950300c0d9071a5414035000c1c012402c200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 292758399 1250 292757149 292757159
    0x14010221090709050709061e02031e040801020a0338190e130b10050105190309060c050901110c1806010207150f0e01030e07140d0c0e16020303010f 65
    0x214a078405560000d690010356210080801e4a0301102c0c00300004000020511020f0381141182c000001307003800c51515005030003070183d541d104280b1000140c240848403400c140045500b203070b018140d204025501c1c0e500040c00a405000942903007014071081d0043d0484282d0000c03100000b000d41641950352003001803050203026800052200e101581c4d40b0800b1950100d40c11619025605555800321407070114208038042400182910351a0318400d041004580ea1100507581c0d1480c00c0352021040306e003400310980c020b10321036400038452400c1101212907e03400c00c01801340c20800382c80300390b03a4000160446443c0c04203101030640c03110420350344007030701c2201d06140c0340d2104040c01194146038548100000d00089402d41c8000200c1c110001444c1d96481014554280c500b802c090020390004d00026440309005d0007a081403104c501400300b56941c0301090011001d4021400e440c0e16030b1581b5902e20200c9040711400c21400704e08501e0703502644008200c034101c0ea200c11107800c0003030401c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 292759649 1250 292758399 292758457
    0x30c030a060e0a0b010e010512060705030402011206050d0c050f0301020702061801030b0909240115080406020d0204030609020a0506130312021e06060909010204180213090603050a140102 82
    0x24000b450081d215100d03c210025190804441c0a850307040032500c8258502000c1140c0306051b00000440c641028051080554101041d2900150709082c42e00e00080701c074103094000d10700b40d4001540300c0791500000b028080d8149011080d2071003900c10500d6802d140040c03509034420140000d400140400405e06006014010b98600c4001490040f9440500ea000608031480503034015040e03801c964101c0160400500b04801c002c8115079845050750702d488800d010035040322500700103121440b800941040201c1d0304030781000c035026400310b44407034590030a5401401402e500b280aa03488000c003003210304e0309500b0b0702c030707099400c61300c40080504680e10308440d80540401482588940c40500c584180b25488804d26a00311500070000e074901041000710f00342d00900310344100d0344104000d10204055034030f0a040700602c0407000d0780c2e41f07680042d100f818050642c00341c1c110034035021002c020080d01082c004e4442d406002400d040850302c916007800c074416510030032a4800c100000503620000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 292760899 1250 292759649 292759661
    0x312040609091d070305101a060307080a15140405010909230c090f0a050610021b01050d06090c0f170601030b01020321190501080304051507170702090105030c030a06 73
    0x708104000401c0c5443c95504c0d02d44141c20442d0281c204074900c2c02104d40e0b91081000304005546055600100c4101140e05444003400c00700401004800080e10b4000039049440d840c01e140711071a015941c1c2d010000c0500b42004800d80c4168144070002604a115001d079601c80ca82040340c040e0902002c0492041c00c20300240060514010305440030003550358103004900c207000785071070030b107892800082d04030442d000100101d1041424403a1902d2280e0300281002507070320107000319030307464451a0040e901400b49074000e820032400c0c010003040b410400e40000c00c080907079803107001c0316852844041d1400d4078840c40000c550b0400d200003d02c070b5031107a0040300c02d820060050380c1c80c11003a03044c19900307030242e003a051138044000310620086410443d1204480341c4190410440f40d410145010340300d11507407040d00d100d01c0c0c844042031060981507044842c0940d106554405680d0880c100e8807842c0c05c949000d1340324004400000905007404161841c42000c000c001e0008240e1070703980da20081c41 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 292762149 1250 292760899 292760921
    0xd0c1511031e091201050c091002010509060601050c01060b0d0c080601090b070201030542040b18180a06050f0109020408150c16060f23010611120406030209031204060909 75
    0x1c45022618484130a01c5510f020300090501d03a035440c07500c0d0041c020681e12884a127001c5a16000400c40560800b24000b03401103400d2a03c2e6a49103407079061140980344903001403494400001c1c130b80c031200b1025448200d0b03c078000c2c1c407102c1d02c43d55820010f555400480c45608202481000750200561003a8886a07001410b66200c08259550406240051000d82e16004006002d800392440800300e091502d103000c0e0003100c0c1444000d55410100b50114400e40085480415030404100100c2440d05801641c64090f801c80e044540141041c03000313044140d074607440802c451000418624500d008440945503804000c002d400d402e0203407844001d00084c09041704030410f201d14007c12100c01300d4010014007500012070204080c040700f0003120b90540c601c0c080b140ca081d20010b1a1a101055541140e0b428104100b801c96240411070920300c0c664030814004000040c040f50454255000d40140002902100d003205102c01501110303100d44d000707040110706040d0b4200034851013a002020007030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 292763399 1250 292762149 292762159
    0x506040b09271c0215010504051003080d06170d1706150a0e04020409020c100e0c120f010204030c08061303021b032803080a05010b03070309020d0c1511031e09 70
    0x41c0c1c20420b14070302d1450800810040e0040058031038080004401e09002d0030080310204104d003010000c030120702b017503440000d0804901045202c420401544a240142854a03030b24500e10a400b2070603490f0b6000110f140081604880800c061b0702c00380481920402c405403442072045c44501d00307180141c00c010310703500400004007081413603601d03940080c1c4014040d00c1005a147c00007007042d2410581d1080104001614001400c500c07010002408035000300203039814a03a0341d280c01c0f20f039414101f42000b440d20540c00010004108800c408400e0101d07042141928415180c64184800550005001400584c800010403020b040d5141040107001002070860303001c82d800b00407114020725620341519550094202c00b900b80758010542a83c40b88031850f0800456042c104a80a54003015204008060766260040d045454000313004243d903400c4524144000d070b0312101c907800340703200040c0070000846c0b002000c40302c65400001c1c3e999150310104500441c043c109441c074060703040032030015031003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 292764649 1250 292763399 292763413
    0x603060409121806020f0a06050615130906140108070f12050c1b03071e020109080a0b041101020d091202030106031b0303030b0609180405010b03010f0506040b0927 72
    0x2d20a03400e003482c180c980e500c4000c0300c010300214030044043c1c180d000a00b0340d040501040c2d2608004103100c081107030302071000195a218000130500404e0b08080b8070090440006490300a00c940e030907100c080394000401407050940f120341c8541818080a0b04e5404035030110b001c5010a8025820015403024519213131010004206003002643c0040d944135090031000120b5a0348a6040914400340c000070900561400e11660707940860340444101d0501500e00101c0c060381160b00c40c07100b810041030704604031a8160700f2410041c807101001d4a041742c03101e81e20000c651195001180c4484025400e440729203a191405001040360011313014101d0307041d581e030700001c03002804040e0043da50310820700c2d00103261030442c0b9014044440b8000028403e0100b80443d041568548813503400c1c040903c40f09440b152124a402400f60401c0c28034030f5499400c0038004400016070350b03c0640b00300012101400410320b04402d200c00804155405180d41300d044054600340c880024480680c210040304485079 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 292765899 1250 292764649 292764653
    0xf0305071a0909041110120b10020a030809070321020606040509031204080f0c07060e03010212060f0d0506161d150a0504051c061a03060105010c05070806010608010509011a090603060409 82
    0x300b46d0401000b01d010801c03c0d00041418002441983e240d40c00036030b034000b02d0101c0790350040c1d074600c015000102005011800120744030400d100305001994011681e000c1c8002003804502e02e001350600310790043c4504c4001820510702030280c1d80c01210414051480c0060001c680c0c46590700c01030081d0f0350060204105201c0403021401000f039000614003a10440b41411402060790700d0b514001442a801444400d240c55180410180c10800c03c503520840703042c03030071f0118180c80a01400501940104000c008250200f580710800010f80c5071b4400081802104000b0b50030382e140720140d60840000c11181c081007a40400806405142d410018200342d0398800040c0b51142c0c3d0a410b00e1800c1003082e4000400c00035000700541006c480044850b440d0124000c80e59840e4144107060410160b4460b58042c8202809024007801c81001a42c1e003541e140c40000e4950a400c1c45000d006500e01d20001600414840c0c0b0501c2e0208511141454581040200a07240d000070b41a140c0c03203640d03026a800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 292767149 1250 292765899 292765909
    0x5010c03052206020d0206090d0c0213050108010c02070506250812040638130228020f0f070e06040e010e16050f010909020a020f06010f0305071a09090411 68
    0x10180710310801c10000c3c20319000a0410001c11155000e540c0901c043c000004000301c0e511114030300300d18007031749040d500c1c1c00000c050450003200c0700d00107072800700046650072040d04040204900768085480d0995240f09110452207102c8070800c41c3d0394450000310008280c1c8071401d00d41405003400701d042030503a00030760014902c01e9030308641165441d2802201e044541179480c02141e145120302c0e820010b9043d0071a1181e20900300c0c18031564520380e40039814465130381035440d80d14403602c40303460b0a2141426141c40d0012406500058441e010105010641c00511604099110000b0b4201b61b0701e0424440800350f4054041c9a115444032801302400303809108140451400500901c8641c1d0454581ca0b100c4445400c0207004884500356070031580d0b042221070085520425005980380d00d201d00c02c0741030901582c4595614010040001500b030303122006901039a01a20542d1081c0e69241480200003c000ea0104031030700301800b0380c02c42c0d4581410056440383c000d003504440e8030011300c0051 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 292768399 1250 292767149 292767187
    0xc0c01021308070f1d1816030506060f040203011a03060f0409110a08010506030304050d0f020306090706080c1801030902030f0105101805060102030f0c0f060109020423060405010c0305 81
    0x381c80c40d8030400f02041201d00c0b503221100188036000e43d41c0301600c1071441314034040c140140403108041c11581a1071034500c0c200440c805407000c030100c00c4c0302580c0300c5c0f03000c54880a041d5015840752565039294038240c80d092003224103c40000c0390000c44800ca8104c855101c0d000140390590250051200e0310490721a800b50a891600c120f6200c95440840810810650900d8000003842ea25110410056440000454059400072191a100d100041c50f01d11410408804001e4140c040c0c5400c2c00f591110000c0c1c080d00f60340703040d00d41000c10307901c100e24410076004103180c080b0350114248a240495000307a025010751030010302a01e4442c03080f1070701c5500b03641c0c0649890403c004140300803c00030120890101400d400c00200703211a0500c400000e6582c01030303200c4400740440004804000103002c014504200d40c04c40140e502e50741c0c1d1000e2039030094100d032051000c0c03951526081141c0b206105100e200e200e0780109603904140c01c0c00c004444044000d4421018454104800410580036142c8a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 292769649 1250 292768399 292768409
    0x81306020406120e010603081606090503070321051e06030a061406010e03010e1e031309021b0c03070303120608120a09060f08040204090812040b040203070f05090c0c010213 76
    0x40d402c108480c500f07542201c800ca40040340036450200f040c030024a4000844220310a002d083d4241c0865034100a4000d00c65207c000f48244800a500d004041d000780c458161007030410403a580381c01e050300880050b50000c8669009050007142c6122901c0d409280080e0010000307821644450100d68940d421510f02203862403003200e101080042c03030b45e40611540720300c400503002070101041c00c00504c0d130b658541a09100b500781c0c203800403072115034082085e1011181d120902140c0240c1c1c440101d0001c0d4018211400d0602038860350704021103002400c14030161024000700708261840d18110758030481d4118001c3c0d22501c4da0b00000d03401c4010050000d074200340d003000f6540c40703511f004040c0001d070407603001c08180082c861030094501e420021031a4070a8042e5004503044c0750f586001d0449224070480b40d42101c000340180014042c1840c1c0b9648928800e03401c45410a0b00d800010005210500c112035100d05400001050041000060054950410005420040350280404d003010b125001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 292770899 1250 292769649 292769657
    0xa150b100809070b070503090d0201020a050a0b0a0b04060b07030818010618050f010501080a02070203030913050f0609060d08071406011e05010f09030b090c04112a0a03081306020406 80
    0x1401044401840311074011300c034612000b4944410f507911581c1300d005040035107119038030007101201964000d1001c41c1a25500809651507441c0700d14281c8030b81e101c03e4032031000c0d0500d403005050141c14544900301c250740213860710340d04007446540d08444582004014202c5400c010036800441e007400d000c1c4401608101800c150100c81080012003207c4004104a01e00d4184c80010040da0341c200941035000000c881307000d6170300d946a0011070b1551007603420071604100540c404184810095000da0301500d000403882c40d80d9103035402004054441a070300103500c10001884100003444003c010100544240b00d0840e84c18010040d0300c0c00c1400c240d000003611090382182c400c07107800d0030041c0700240109080c0b1842e0003d020000500211341800010020355004011039054003080204d00360740c13500100213000300d0004482680b940d412440c0c101c0799082001180f044400e0080342200040012800101110b00300d94508540c602c4000d002c6840e5001b1140d81c0f14041207160001b4800f07030103c0c1d15 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 292772149 1250 292770899 292770901
    0x60703110d052212031b0803280638030411011b03120504111f0e0307051f11061e010803121801022809050a080a150b1008 54
    0x307803c41e0404960030509030307203034210001404101c0b841042e03003654641610b000401e0000d000391706140340c2130303001c406401001c01000300701001c46c1d030035600da4014542000c504a40d020341845041524a18064142085103116192a1091030b12240d03952104c11a115030104020204402c6034540c0151410b0f24456040910107000e560044d011110380100e07141203109050355510020900306200d14410280b540700d03000314042c085545002062020020002d1402401040000e400c0d403801442090100d10040510505882d001c9220011100c01400c1d9202c01d030400c428105005d9200c01d0b10b8000c1c850b2015a0103130101c41044607500c40d50000700007c81708041039403600540001640719001d0740d8001c00000d14150231175038900350088610540e0b05481c0e03c0c03d40351140a405190000a00d88000c043d0382000c000000d80d40c0c20b040103003912110b00300c540321024480103203582d010f1012181d201d030a950001400c449070b40d407001c403640f100009010706800f001556205c1c0581031800000c0c01a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 292773399 1250 292772149 292772167
    0x504022a030307120537050109020913020a0c0c060c171602042a0203030417070f030804110402041502012d051b0403051b01020c01080105060703110d05 67
    0x40e10001065012100071415490b0600c00200404041c200e000d61151301c0c0c40201d501c0e02c80d071520856900349041440082081c00e00c03159401c0115076410f0400310b0b410b2200002d45540d0a10841d032051802030190b120b00300d0700d21101e0020f544240101030412043c1c004100105446085100c0903040035900c41c0c8a0400b0350401229001d0380300042c8200c0708041100200c2d01207000c40d100601941504c0204038480300070002ca020225800580c40441c4108402c2c4aa1690100c011403085106041003090a95503501c0b65116016189004081070300f46042c60011034011004954054460b001c58018004804042000d0780c20542c09048a034101c0078412001c0c0d0740a0188103540417100043c0c5110152042d15401a400c9003d40c83d400e0b1a0398002042c015148406968182d203000c05203d0342c0d0780e03a03a15043d41c1d1562211205140d50328054240e4095600c04154030748404d005070340c0c62055900304410010145d011100880070710103202d80d6404011024010604514001d4603440d468400031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 292774649 1250 292773399 292773457
    0x3040b0301150801060c110a0b03090a050f0610030b0a0b0627010806131a03030c0a0212030901020d030b03190b1603020304120f050d140403110303090c0f040204050402 74
    0x884020b8140329100c401071103020760105540f0603040e0014204603290030b000c000310314108181c3e0810035040000100708042043c3c0010520702151003101211462130317891000c1510ba01041da50b403003114103030010070008034862040741c503000f01c00c8000c0003581c002460001203207940500c10f28a500428100e1000c0001ca0740b840c0880140f40a00b002d003030615000000494940300c600899a1741070f03448820900c1c4022010414440d1080174080300d41e9140d444040c607544000f0304800302d01c543c0202104081001c40401030340c040d024180c00800901041c4002600609000f1200075054810002c80c1c0f02603180241e60107085500a80e0b48100038200840f600103030703500380540c1304103040c010024070001904d20010040c0d00b00c100d144c0080c0c600242c80f801c441903ca00480f403804507003402c0004418101e200c00e514092031282e120a04601e1049103040d4a0707000481360504a80c00030503104000341864620205481e100400c01850140c0300c40000341207801080300864407121001d10307601c0305509 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 292775899 1250 292774649 292774679
    0x3020a02072102010f031506110f10092d030c21030507080106020a02010e0603040606030b0a020306090f041e020a05031e01180b07031a040204180b0418020f0d0503040b0301 76
    0x2501e002e0141e030700c0f587e1004d80b08004600c01c2c4010405002c41c6103404000038072050124601c14070030f44480d001040240006403030708a80a07501241001c0032000c00b440d41c10909400604106040d24140c605514240c0b104d280b43c13041030f50302e2800c80e4a0a541e080d00f04600500069154070001003608019100a03d8210160009403c0d90b019015240150307800000c41c00c041c40701190b030304d581e80c0c0e0380e4078100300500b40a0348010f1510940780103010b0300c00d00c07070b4000e07502c2a04107a071649055514624880c0e01c00034107582c0507014016540440d0540da6038070003110802c50010788420700c050741c0d840129180c01c150352144e50380b1800c3e400b40380c1103208081c0103006002e8050381e8440c10491150f1210b022084000e4005414140c0d1603e45007001c5071114101410104000c01c115100c507540d0041c2284012440317800d81c0c80304d00d41600a511803903c0d01c2801522231540c0f0010301e9001c0c4540c01e0102c0c2510740300c03e2603800b0b01045a6000012020070081018295011040b074895140400803070710718007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 292777149 1250 292775899 292775927
    0x30906070e060f0c07050a120501050c090916140a030c14090105041e1a0a080708010b040506090f03061e070908100915050103080307091d060103020a0207210201 71
    0x203a00e003858411540ca0000f0b440024080c0f5003440d5880c05854111482d11204c0d62280d03420482165001a0702c20380480842c282d240540b00a201550b10800700902d14420b886031540c0c440300110100700c140e03003201380d070702c502086a05001d549000b62034032002c0309403c0340405200282e02d580781034000f19480a8180c4600612680a81c03e041074280040c01074062030081d0312964002040c2000031203071001c2d101000303181741b00452007010503203200000103071f0003103030180045260700c0081100144103082c00c0741241c00d1295080d003030505240c01c0100741d034840c0c00450340c031004130302c200c40d0710340c5d000c0c011240120f1200c120348591050885c04110040d40c010428400c0c000100700412400e1404269030700b5031580601300180081c4a1301d421480718039515042a844c0345440008010800c0345401035004030a1a11540c91440d5a9041a10704c40000c080305810703110407a01042c440e5000e80c01402d80f21030180152156a621082c000d180165844d10800813032000c52020019960403001c0114001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 292778399 1250 292777149 292777157
    0x24090b040504080304060b03150907031406042112140a1b02030a0f140315030c120c13090b07050406030b0603220203030f04060e120a0b0103080705030403020d030503090607 76
    0x46416210303e0140e01005101512003607c40030107900c942e03418041c0010a002010b080c000b6410a0340203e5a5040c103400200d45e10903881d4001500c600000070000d10a5901c58848d102d1010a000082540c203110f0362810705101d60307600708284840c3e45000c1c0079a0843c42031110100e5140c00440c42043e1100901c3c89140d6000d07520490b440958003204903945035107a410080d10301803041104880034101045109074070310012042c0031840d10149081410702d8401c800312015003100b04200300700040c2688801c8401e901001e4a55024240341c1501da94403c125240040c01310201e0f1602141740c40200e45900000b40000ba050041d5901481003114212050302c505041d454489013945084590800c2d0720b0316405112861801c650701001150118100c8400d4181c171696550740c040c0c041040071500c8ca00c0ba00034426000b0484400060680120390480c014039070350b03407a507181c1c20708640c030a04041d240380c0005c020105c01f503110b410007000040c0c420307540c0c2980c034580400c80078101302c4041e00320700c02c00c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 292779649 1250 292778399 292778401
    0x71a0703020f07110112020c0102071202070602070e090a0203030408030d0c0512011211060a03060f17030a080a0b061804050a091709040207200a080607200124090b0405 74
    0x1d082242c065480855215000c03c02d90031030a130050341d012610543c0d032000c0ca800080c0d05511420b041d009000b10b148620801c1080600440050740c40c0ca600d4000d0500592000c2d42c10400103c1081e003c5401906000a44141c0105600407030b003140c1c802c1d00700d5099980300140c105101c0c1c00340e05c070303206502d00217142950505100c1403652080d020180b18541103481c80d005d03500140021105040303016000100902d40d14080c455019010703282510443c0604032158400103100b100a0900111032041103001d14130780b00c0001001e640e0760001400101c0e100356610501d08881c0c8a0400500180d0045012108aa80640108400e844000b084000000d05245244002821143d81101f002032001503150f152400c00c0041802402072a00241020860003680300500c0310070410150310b080c1c2036500c5441d144e2140c2d00d140e41c40030f090714040006803200745c000070410182622101c924002e14004203442d484103920012441c0014824600400142802c10070404688916018144151400d200c3d0f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 292780899 1250 292779649 292779667
    0xa0c12020f0411090a030c05100c0f0b040c080a0602250f02010305060d0602070c080115030b1605040324230402041d06090109151b031a06071a070302 66
    0x70325000c0c07141c8600031500e030444148141c07000400d950564002522481040e0380d681426581d403401d901c03070140202944050350800b04e01c178100d1031442c0e43d000349900c0c03810181d5691710f00c4c4c00748000700156001231004d140814092402e01c60400300d02c2c0200000342e21040ca004100c07407900d040640c003040b1340320000740450004484401d80c072440f07902400c00081ca5030710400400c41001445100500c1244001003140400814100308800d43d906c04000300f040718003010744241c280080d408050240728407500083da80004000c8035074185070f00c61030540d09040d5a80d844103107410209401c1b412800c1a01070340b01082040b403080c6010504151051f03030315050f6040c5111440d0070301400280c011a1901041c1d00c00300e8011b00b100003d2080c2000b1503103035240a4860078001c0102a00484001910701c4c3c480611501e64001d020111100c0e411010216401b12415030091041c0400d01c019443d484207000300c0e5a503207101408400307000300b10301c40301b103821300c0c2c2032048082e001000340050510500240d61 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 292782149 1250 292780899 292780909
    0xc03131a0c250504060303091406030603030711010309292401050702120303070c0b090303240307080f0c01110627010204030501090f12030506150a17090a0c1202 71
    0x110751148040b10a191942032041e4000e2440c0e182c10441e082800e01c4400000c00d94404107910454152182c00810210034508225031440103944465040e0f00501002010031740c0391415a840c44014100000d4401c203550f180c1d98818044403003034103580c201300d070a104860740f81c0310b107994402c074030f058001c0c800c003a0801d24040c101d540c01103550421402058210440d00c60005004d1034010303900840c2d03101e1800380002040341c0d0006204944060792400414a0101d0000640b402000300034105400c0e803014514150031034074580400340d0700d40314940002030300c0ba6044c013009d0144000000903010329445103001504c08a1001c08607486a445001080807424404084400e0002c40c058154950007041d110140a8080c9400c080c20952802207180204044411460390052080e50100d074842c0300003105070100c3d10304684482d000149000b00c2c284440c03a034001405080050308008940d409444890701c00c01200301d901c01c540741c0c400c2e0140c006001002c8034a000a20810700c5080b050710099000c54 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 292783399 1250 292782149 292782163
    0x1a010e041b14070b09010b1c0c0e07120e071509120f020310140a0f0e060c0c0307060e0c040e06070519091211010f030204050a0b0904020c03131a0c 65
    0x110070045038251085100034800c08a8060355003048052520741172038100a03000341041d4100500c10001c0b01000e24160003505100b400c1190000c0f40030b00001d00c0d06141400c0090010300035003c01814100c0c5040e01689071041c0d0a04203401c000816100b81402031980e40d02c001501804180f2024060800c8001510b1900b1601981d000c0c0781e980a50300e41e440480c0c54003100d28400751402c0e09000900c500110a890031900c505810003091011101c0c0c0d10014007110031251210060b81c010300700052039007480b60000d042c4c10058404491500c2c1321902c0e8402103038190000902d2940011a04404601d0980242c4840c8a4604090462403d2039000580244200021480c022a680290b014142c0c007c40c450801480142041c0d5400c009034072305154040c05050740c280c08158111700d08140c10f48203209035019144090000d0001604102c5031480613004500304560068080221311100d82c1c045c8003400041d8412000c01c4515810691b18490010742c065503071074401c4043c415007418041c001041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 292784649 1250 292783399 292783451
    0xa0c05071d010909170301080a0215120f0709080a080301050901051f0c0c0e07020d02010627090609050d200a0b07050d1d0a0510023a1a010e04 63
    0x103454061460100340f400b421400d0150303c5e071004000091503900114078088203510849005031800d00c110f074080401c1c0140954841e105e2003030800250144071090659402200c0b500f040844990798006041c43c107149460200d5101001000412441c10301d00300c40c0e8050401125141718600350f80d94450218840038100700204103008000509201c060603400c4040c04623607000c40c40030310f01214080d40c0c4920090751040113600e010030000d41181121034810400b600d6540224010110344603250250480d841c0681d4196903c844007000101c0c00c0241d034440c0046a21801060303071410b44c1c2411480411005c004054101c0001d0303000245000c3e031503d9000710103082450b220100b03000c18800401d100c200e40c103110030b00d0780140541c1c0d03900007504160840c4a0401c03152004215560402680a840f01d201c0801c0d40c226000c164104080c840c94400c126010200607113592413031042c01c1035548480500701c0601034540403c2d02c2d5644894002c003a000240d0b020f00410303080d4240802c581418201c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 292785899 1250 292784649 292784651
    0xb04061713150506100801030b0601050a090806010e06010f0804020d0b04060207150f1d0d21020f0406140310090c050d02070516050a0e04060b01030b03030a0c05071d0109 75
    0x510109495100414115003000c4041c40b0038804040b0180100003c0e500c00e03200d20501040244007611070400a8140d80c1c2c80100070a1585039200199002c5d048104c411050050041021a141404001c018001c0500b06070401160810a0014216065032848181040001000c00c0b01507228001c840c04190341c40460315503203640b51700b0200000d00502200502d80850303146a0300030030005401428400001c01020010031142c5c0901c84038181c4182c1c0030003019000302c90300500c01030103540074049000300840c00101d20400c48690804a80c0720b600d1190b450326010500f480080d5000340101c0f02180c24608a500d94103020b10031440b14801881890174154440303480480c02e030b110350f059400c0d8082071103040d5140c43c01454115203622a07140a802000902d0900154070318101e41218101c4e600d44003640c4442e01c96498450203041c01240d8941415214074402c00c50392820001816890150307603518030000120700d8050b08000340e5a00c840aa40031701e140340d006050000960030304448007804 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 292787149 1250 292785899 292785901
    0x605010929070f1a0609090106030f06050903071b03060c03020c030910090801020f182e090b0a121b0e0d0510020c16060c1a10030503220b040617 64
    0x2d0300090700b0304450f200074815242d61214084104010108601494081780c4a0300142e551103001401c0360b00718030000d84071aa8031503003800422115070199420602c907809691610820391076562a00810412015480c4890f400801c02e03c1490320030018003c10790715055241601c8040425601c0c010115072901c42e407500da00030450740d0b0195030580001c0ca000c0c3e00940d240e500e07081c0124500e8210200c4402076801c51010f4000e98074019018112203008605490034880e1103540795092294548440c100340511141c000c03510350841d40152020015560328040e03458218503001c801d944001084ea802c45c0e00d0409180122a0000d032031820408003030318002c2d03904120b42052b40c03616080c1010b001c061480060480c0e02140c0124902030394044000c1043c5203550b8400049a0940c4403840c00b0382804120002100b80300601300500b904010f0301448980490307126140c042c00c503440281750700d64407400080110700740c010a00c40c81006001c10081c4908103440c006010b045007181401200380b40860304 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 292788399 1250 292787149 292787153
    0x6100311010c0b090703020310020405300a12030b010c030509061c0f060509010e010f0e270705040c090509042d0501020901080127020f090d06060501092907 69
    0x201d4910701854004003070078911304154009a4941100340426402401034042d040c00d00105402150102c59002d80894080c240c1410300501b5980303030214008000c0210030620094440403c461500307140540a09615409144009821181e0405c40349040c4607005a100000c20b80000c1510403211080d100a584d0f46201545004c40903a2801d6000d2401c1c07410380c6240076120290b11440a0750802c2d0fa00095590304c4070303486900722000348114000b1306492141400290400c00b00d298000780070400c4510f601c140c1c035403a03000900c00815049200c2d80115401c2101349032070b016588071404e41d402c28010507800c1001081003100020000780c100c000c0300d80908030602d100d05a10684c003600700c007041414855840d144e4082d5000c00181c0d80013495200012070040303803205113200a8280860300000b0703a41d07583e40030750280d08440c4603403001c1001807081c150030f41c417040e890209441c0f00c4c0390009100ea04040026000c00080d400100c21101c2010f50301501c11131160f1200011540040b1080c0c0f151818 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 292789649 1250 292788399 292788407
    0x8060d06090b2a0304020d240e0c0a03021503150603010e01030512030105010c0308040305090d050307021f02060414031c0203072a020103110d0203070903050f0610031101 75
    0x948009090a241c11040c40a000c20101e801e40640ca040c41114031070800296024601d07009080403081c0c92008101080c011720304451307600516403003694140031110500044454502c1c954a12041c15a10740c01000300400c010700034907214100840e00740c0342003401c54010a80c6030042400d0000705960000c0400c915001680c00b034a41c00308003c140660b2507071980354900c24958284000c41e10b5205892528a4030392a001c2036034103840040c1c0d201d02c2c64800d40d88003110003400c00780040d418003004104514207070701c030070300c010600c680110000d50f5100c01074414002620311811400b01c1d1001c000c10000c10b101e070b01040c1c654000343c0081c0d00c1ca2541041c1c0c00e82c28118440c2424946821900711724044c14200150081c44c030480700c940300c006040f100c000c1588940344a9640c03011055424006220041d0b010303500002d440c54240120038100307402485040b01300c1c0e0040d070b41175020139844582042049400c001c60f4402d94002009043c4a060000300940c040e881404000c200441d01440c1c0d1245901c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 292790899 1250 292789649 292789669
    0x70203030712050c010c03050f280f020c0f120912011b030b10020d05030106200106060512100506030406020307020a02090403030b0315010b030601210c0e040f0c020a030806 76
    0x41c041c0c040481d4030340020b440c580c1311044000d815420510203c079018024400c5601c1381004260b076991a03a902295006010744242d1001d4030541d07404005001681d541c8115110400082c000680da41c81561142c0d20f0311103149880942d5074800742409420402000980700703d44820340310030401321000c941043c0035043d00401c0c0704006400c41a10030410784d0580005681400070340e080101e03c20018400c1740c842501c5842c0c4004a0010801040094450170300c82400450901c060340c0f0002d8222681782c291003c680c814800a807010440c1e800380c0b82604042c507040442146200383c4186071801040d058040200040c04ac2540400018625802130203011030b440e40c000c004902e00d00d0207143c06002840f0301c0103990300900c0b41442d5952006048651903050f01c0d90302c20f00500b03554499004490846d600304800701104082904c2030480c2c000c600038880900b02c070303844008010b0404404d020843d5141842c0701c4000b03041000307000583d600854400c1c0100e03010701c3e04003c10b60719540840e0504807 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 292792149 1250 292790899 292790903
    0x40b0a0e06070b070e09010501080f040b090a08160b070207080a261b010b1c021c0f120f030207020d0201081b0c0109020405131a0703110f13051f050702030307 70
    0xe540d0041200c8242e00815005d404041114000003690f01c075001182c00503001c55040c41001c04410118012078030107919160310500c158121060381c10f66a07120109604400303030003210310000301c65460400c44d0514089501c0280361004080e03542c5814145c0b6a5030301854405001f0148040203c0c012008061111040d400c08684050350341102e94074102407480354090080c2c5c00d52800705820444e01c0c154041c000c00e20865202400e4424064080000c48200c24840201f654805251000065070340d000070080c0c42d010781c041c2e0034001c0c1ba055010706403812007003500e01010303c100101c0006a8030140722000154084ca0300c0d5605c0d640d00f441c40100807019607000c0305441c6020810000105054006640d103e03c01d0b90705100546580c00b6503054081c1e000b2000306803d00c922050000c41007000c80b4158030140030314002c80d0042c864140e8040c0e40d4482c110860f4000000204c3c02066004a010203008180584483c8030340070001c90b0040168000101042c10003a0001d150015598100256042c0c55 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 292793399 1250 292792149 292792163
    0xa020a030f0606180e0601210603050a08070b0106020606130b010c051905070906030503040b0a0201020906270111100b0111030d02040e1608060f0d050105090601061202040b0a0e0607 80
    0x680c40319005400131008901800c0300300c081c4800801c81e0040b041d1614090b2006031540c01d03580348224850140d9100050591505681c0c6813400404174104100c0c070007900d40a941c0d520359501c85c5080a014800e816000501035520280c1030001d5a2110303c1950b80300d10b40000b0000340d009000740121495081c03003d0107040ca20072a0300900c3d103000c1040054003113a124200721400c095039036a80b941a031300d0750b10018285030030502c0100034141c2441c1c0180060314880c80010319012455000a410fa00b1014005071829002040c2864080301c8020b5010170580c00d080c03440c55006c2c8411107940e9a013800303c44070714260312081d11040316406000381c4d050390000310303042c0d030389498010900701c00a400c144030b80400601c2c1003000c05c848490041c10010041499920fa025179919001400000c0c40c5403d005a0060781000b0b0010120f8020b2050718010415403000c1c055a524100c401001c070240c002c00580a284100420001d089941003201c2800c000e9003032001010031400b0029985d40988040a0214 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 292794649 1250 292793399 292793411
    0x6090703031d0f03100608161208090102241602031c1104050d05030c010b0d030c081606050901050103060c0e0108041101031b090510030b060913060906080604021003050705030a020a030f 82
    0x105d440d086003065418802c11a0251807165500d061180400e108188a21340c050f0501c01c0803803034000040100744d0040c01201c040070000b06d15a002d15400500400e0140302090034018012000e0b20450981a410f20045040c4070380752000103030001d00041c004040c03540e684c0e44040d000c1d00e0081554010a030041000000000a0824581740e510021001d00740303518025600c0c1d520715040940d0301c0c00c280c150392805000001980e0384000341c2c1c400b0b0b041000910a42340604006822401810712074040c0303400100d003e524501d0300b01c0988074907aa00a09010000c10800c4999030b202c0c0c10903900c960481c1c03902c4d0002001d0401600104440362180000703181c010402c04c0c1c80d0790000f41800803540d040e036090a02e822414402c070101c4507104940c81c0d001c04104050b982ca8501907203028140680c00c40006240399482600b0401c841e5264042030070350b0020701c104025450703d02400440c03c03281e400c0a10151400c484010220300c0028540352440d40d0100d2441d04082c400d41c031100504d01954010010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 292795899 1250 292794649 292794673
    0x604090c090c050415020a05070e10090914010f05010503032502090718050916030905120a020a0201030b04050903070305030915070e120705061602150304030e0306090703031d0f03 79
    0xc190f000d401045c441e0540d0040b1005085d1000840c0188546c001c8054400079041010080d004c90001e0000c284030307009003d020940064500c5442055840380c01132168010316400041c0c2036400074010300d008140380500400a903100070044807045400b00b8030101141103440b1842107030030340306a00a900852802c082150241d0001504101010005001a40b0783e54810030019081c2046800790150101d0361498000c481c00b07074118142301842030058400e003d0300303040a40420780001300341d0f90041c1d02054698080d940c242c410302c81c0c01d0805071400c1c0b050340340480030107030b49100c2e100700202000000400903101a0301845161100904003000803645d0400c1e41004100801702020548030b1170300e058418500e0070000400388120350015044034103000398030403803113040f00501400381e0300102070b50b000080710f01048000f944160300c203031130b41e50b0b40001040c14541752101c01050310b07500d80d0021500f40003281c0c020b0000d10194050003401a499960000031608030b100ca9030556815105250041c0b42e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 292797149 1250 292795899 292795907
    0xa031a010e0a050405070312021c0905012631030c02011205070905060a09030b01090504060c05040b03060d06020906161b03080f071a04060b10170604090c090c 70
    0x8100e0700038500a0400b610303800b00510490304103580050160703120103410400103100170340039201c840190054403120452a000f454030b1985140c11080020807090050040c2d68004504881050481c0308252076001a80c0d000c0180034006407134442031f00c0c2010b2280485450000721150000180ea902040300b0103145005024141c48000803404141c07085105080c0d41c250344605031180c052542c651300040d242c0010301c00c03158071108650040041d0508040003060b01014118000c0c12203c03400030700c0d890182000401c942030f50071780f801041020041040001480b00c103032a0070100c2225010b0402081c0d2030903c000388074000199410036804140e441001c0740b00c40d80b040c0d50b140a1240c03458100940c0c0301c0f86030b40d103402c1e0100500d942400d100a03088202008060310f5064415443c014000c04c0d004c1d000180c0e000701b00c03401c49946448000700d81841c202009058122145070500c00b0a07541c5844800e050040000c241c03e001c0d5944d62240d806100903141c40c10000d02e5454400c001c0b405c0680782c024 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 292798399 1250 292797149 292797151
    0x8010b0306060f03150a0e030a020601170706080f0907050a030506061305100b0903240403181a090301240801050c07030509130905240f010317090a031a 67
    0x610901524000030490300304003d580054420040c043d00034074000140f2101e0600024042d180007070b1b1744580300880c0d00820801007101c210590010041d40d8500505c1c43c3d0000f0b44030a84600c030f60800c44080118a801481e81a08541c040c5044483d6648441005146c22810780c059644411024000410b011002c2140c034050441550422007506446e4590000d0360000c0c1c4001400c1080c2241c2000340f42d10782d0380a0488420000c0035990000e12232004011a062241d5101180101c058188010103130880c11141c3ca07a407006403050560703031500204c0c4669103c0c0b400400d460f441c0c0081d0314444c0717503001c1d40a003807090341c603c54114034a00d01e42041c568501c1d05000c0c90500350329001c04968620b00b9070058801180d03040e42c99516125103070007400144031085480d45895030b100c25103080000c0c0107001c807940780304401001c5910244800c010760f01c1003130064100107440c900c000050010400100701601c0196000070f100e03696042c02c902051040380c1d075900c080c00103850914284c2c40d03140000042c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 292799649 1250 292798399 292798421
    0x103080901030e0f071202040b04060803040e0a091e2f0a051c02011103040b041202090109051915051207030606080d210e1005010503061b0d150503070801 68
    0x4000010800c4401c580d2103030000307040c2075950b000b81d20030006c8401c000b00c44080307148007800101c2c0c0c046101300403809a4095401c1680982c0001c0780500504200d9810980d12114180c001e01c6202d8072901d41003800c2481c0c041c0c0c800001c03a80d9915000b40200b003005000c10301080d441e15020000303070741c1090241150001e0780310710a403038810000a017468000360305899181501d070081a181030550040d690612102803404185c0028070000440130107130390141c002001e01d401201c0e000b0440e4810004103284c140c000d0081103151205000d2103582546041d0000c9110f01c20000b0034508201c1910031030081e95000075031146a001c2c0054981e503000c905001100c0c450301741404105d480e03484860315246007242e1100095000c60400d4150b1301141824281d90000300341c002400d0f2002c01425050040004559002984400c010040f03800c040042d5a480b2045444070810807101d030042100d10320a00100d608402d803503000560403655404143c0004220040c212150b643d0307a41041c5018041030840 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 292800899 1250 292799649 292799651
    0xc081b12181c1b0305030c09120a06091a0c222c0c03090a0f0303060902031311032107110a080f010c081e040609080c03041a0708030609130605010308090103 69
    0x3046100e03a64242c50081a0f42c1e00d500e840d0700b9a9103092000e0010740000a07060303803240404202880c1c01c0b005220041e005c60150b14003203480112802c01c10081c84000100d1004145841c0401814101c208140d81c81d0155990394644141c542e8080401d0885050308001081c103004800c210400c41e0404141c454042040e20046890b0764010b1031540d580411100030045400540c920710000f03c0004010280c14801c0c05d00140e1240c03074424000807600100e4820481c40d8030302e2010820711400420802d600c1c0011002440d01e082c40f5658480505d10306e05d041c0c4403964011030038004201c00303000414002c08014020110150380c9081c1031790340d11501d81003417010754070b045403100c844c034420038034544925a04241003141000c0b940d05004210f000810036503000f81d540383d07000d000441d000020b00b2a04009801582c403181800e071030680c5208001c8a14a00803010020350000030020810b80b580200c0c201e40200d03440c2d0b641d1050829004044600501c031034038000010003000742c0d50001e00301002003a07034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 292802149 1250 292800899 292800917
    0x120a1b02031e0f07031e0804080105070c11030c0109051e0303030a1e110a12150305030405030c0103050f0c0c0f120301060f0e0a03170d09060c081b12181c 68
    0x51625214440d40c00080c03c0c056040007201c41106c0c1800890404900c07404519282036a281e00705030840d001581c0400004202c0c4131440d00f4050052480c644002c1c04a015020844141001030080801e92141c03a0041030800640c040c912151848101138a002030141caa980c58204000b000501d8118000050400c060b400709110301c410b4802c2524108058540525200381c0d48000e80300440704010340310003e51a150001c00d6108817000c01c500a40c8100020741e1030f10709044c01c040c00c00110000a038100740c1345c03004000050042004803600010320240742982c03120108003040c00e120440e58022014400c000070840c4101d150707002141258025074035060b40408000c422035101454100595100240842c1400070403011581202d6105018912500d05600d03041c21800b0380314081c1c0c040d110300b503440720741790034041d04015840c1e4884515400b02000d4460a4142400350141421000014018500007000107201d540000c0b900303002501291048048207001d0494640b0181e051070000381c10304 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 292803399 1250 292802149 292802173
    0x30f0708010e01060f05030c04081b121902040c03020f03010611010609050712050a0b12010e070501020a0507060507110a0b0c0c010e010c0318030c0e010602010b03120a1b02031e 78
    0xd008606840c13060303648500202141808031215000070788518101001001700103861002000700d46100d200c0b01d10200c49808840c03080103815503004100840c075800c00300d03c0700c82400f55090070355402c1c4d40c1200c0c00201100b020100301c000b4010070a06841310700c000000801c50300e810100b02480200c0150081c410552140740c4441038601c01d550040108401d0400580c101c2842d801840c1e0210175603c00190769444140040d9018814540d0404c07140d548880590041d00140803200c0a42000e00081c248042c4660355595075030303140e2150b04100700d80030542c0d008002070b01c000c00441800040c082107016454600f0304290303600103e0320505500ca001c0f812083c550041d040e10f02e42c014145c42e12441c031071041c0c4064900b89054244000803c0d407154001c80002c141d0280c40c0040e04050080070700c99810044068210343c54408503500ca41c0c4854a81c010f801c01c06170865803030400c90301e05560f28480d00c04441c490608240e07402541400745103040355031121101e043d10100c00c00c40048684942e040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 292804649 1250 292803399 292803419
    0x40b0a0908010e15040204021b10020a1e020c0904140610050924150403050105090105060307080304050901170f0a0b070f0504080c04090212032701170106031d03030f070801 76
    0xc4c0c20101c521114410014000d480c1660180c00c502d5074001c040b80d0220344404005080404d240d42d004c0d030365030f4041000845103a000160082400c80700e520303d40c00d165042c001070360b1022524a910700c10704020b000038042003900025082e00312a4a4100c6415080208184240305610701030140034020b00e0b00020032120b40c21101400207030048044040c9034046405000213581004050302c03811008100010010301e092040c58800d881c50400040e00d420302c9070030035041015030751103228143d0051000340f2140d83c440c400c190454030360154540743c1e21803e050113428520007049180301405054580420b0183c0403002520500d050364604200d0f0390300c80d80c01d84050207540690005170380403124807460f60a2582c0410082d40c0001c0015801a000c03002d410300d0f50b80044044e00308040b0b0020b00d8042c040c0140505603a10900b401c000b117602841c155650360039007051142c00c00300754891106070840c0e9401109004441c40000030789944e45400841c90f510380203340c41c14000540c004000040f92901 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 292805755 1106 292804649 292804663
    0xf030c03031b07060f020309040c030e252907030302090a090614040b0d02090c0d140108100c090608060a050406030302060a0e0105010524040b0a0908010e 68
    0x802c0b8101c078107001a503131200e0144840d041c10304034031a4010050b10151031b0240da000500c149058000c4015000d070f14890074581c0913941c0500311542d19012607034084001c5104814aa40d610701c2e0441c81c2c0024419042401200707c28860716404c0140300400c9014020720700036060600728400546582e40e5540040580d60381d521080180d0082e803091045940000c580c10010140c810011403804010003200902c0342d140e50b80010a02003491007540d00d021b8a90500704000a0301da181d005900400f03010b030013001e110340c2c0002000c0d04810b0103190f415003600d0b5242c0181c2d902d402029500714030082e10075036101030740701004640d0f501c3c0c17071144800941c0260300071f00140c10310600302d8085403480800d080613641008010300070707a141d80c10705c1c512141d0011185640100780d20901d6000b400395402030340000000184c0f81c0d00780c95202d0907140a94040c0c600810507a6400000c0c0350342d54a03 = true := by decide +kernel

theorem cover : BRFrame.Cov 292625899 292805755 := by
  have h0 := BRFrame.cov_init 292625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 292625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 292625899 ≤ n) (h2 : n < 292805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
