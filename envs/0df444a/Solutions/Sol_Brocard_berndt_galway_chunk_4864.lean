-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4864
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:59:06.30619+00:00
-- url     : https://prove2.me/submissions/26bbd753-7bf4-4712-bdcb-9fd985aeeeb7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 874640287 ≤ n < 874820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 874641537 1250 874640287 874640323
    0xc06030f06011419030c1407053a0309030e1210051005030a050a0519020a03080a0309080a27260c06120709061b080c0a0b09010605030c03 61
    0x901d10b610894541d0040c40d190000607081400b011030480001c0403148103140401e503904d84100e8410b030031909101804000240092170304219603070f056100d0454025004403e0110100a0009034081c0a5904030a10508200b1902d605140c1c0040c040e288102092b000700d00781030303120403560810300440d035030311903900c40181610b1140400342001410b00900744400c0007811040401c080e5002e010181070075000d00010141032a040c00c0190910780c01454030f84000000d5000300c40140c0f40c00d00c81d003003100d4102d490703140c440007440425030140412510090407004001005244144c100c20401020b8031021030381001c030f123007044108100d000706004010844d15000c011591410f2464400ea109a131440150344007101c3c8040441c40340d4000c0d1220307000900702d16080203000740d84403000301f00130072940c40c001c0c001010640c0d450318607008600c0041c20100c00015640012442000500308055100caa09102880c00c00440c9002306a1406010310134002d250b840d580c90314000507988140a0001c0071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 874642787 1250 874641537 874641541
    0x18061f0506030f0114012c0315150d14030d020c0105090c0f0402160203120c15040c210209090c010e01020318010f0908070e0f1608010311010507080f0703020c06030f 73
    0x384242c0007411104c40c1000003030040d41f4a4001e48405085200c029142c070014444104130030941480800c0e108041d00098202c20005c141c20705101c06000241d090f54440c1140c040381c1840b9016600108800ca454030001411101c11403555008143c04600314008000d592290040e8a84030080003901c4c60f88503100940b10740c0f0703a240036030041500c0582c0c4580c040142c1030a07030119003030000b00490603d546401040780255404240401c02c00c0418a00c4d844c1c41c107207040d03520110401c02c0b6001302c8401c0740501142000c4801684802c07010b00e50002c00c032481615006088990305c01c0d481c443c5600065030036254800c40e500000980e15003840f11986010103002d800011103045104403401000c11624020002e410300c014400740002e040e0407052480c039031525008488a41801810000864401014840159500210f0700341525404551150801d0324800102c0d0b080c0210034015000090005544102c1c0d0002001491140c0c443d800741d4040340c0c443c808104083c0001c4a540d2025200000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 874644037 1250 874642787 874642799
    0x4030914040b0405130515070906030903050c0313030c0b04060516021804061b0c02030a030315150801090c0c0203122503081e01081518061f0506030f01 67
    0x840044030003024000040840c03036a000107080c0d0310142c0c1c90000e03c5142105440c00e005091015005501e036984a108490400203c0244041d09922640d402c00d5070792140d0500709131040045034001e11802c1e044980b00c0510008500c02d9417034611080b100c1c003060b2a0300050960043c0c084d02c0449101d41c03209801d02c1c01c81ca00301e03824041c0d0107900b00d80c0b0180840c80ca075074500750300740114021360181c0070000f40d42c600d640102c810310802c0e54a0ba0148a0352400010040c0d80c00699500c3ca03d60514022584007410f07043c1c6103401e07007103820001d1035142d14403002c559140e10400d030307034101c90f04c0b0b25090065000e17030101503591988010300070350117810810240100c803807034200030982c0803446104500c2200e0507000310040403041c020220001030b8518148680301c0030b440822a050500c04801c03644952414010b01e940e00c0d803410946114025010010b410b4004e0800c145080e001300d8015038050740381050030110090414001b00d4082c5110380c80208803820b084055074800c5c0910503c103c0a6406c0030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 874645287 1250 874644037 874644059
    0x709060e0d0212121206010518040911060319110301080c09100306021b150919020114180109080f06040221010c080a0f0905070501080c0d050f0105041103040309 71
    0x2041a41c008200c25020183c09000708100c4842c40816501c50b0b032034912411001140d840041c0c4403604008050240104640c04180c480c031a80354101c40025103440f0074035042503034400300a40c2d03541c800710100400444084011030048246c0003000e0400c2201d510340c242503110301082c011249180c0c00160342c83c085050854071190040b0f85600380040044c0d51f95103c00503a84800300c4186180c0207400f586000003000c1080c1c031104190404100c0e1645440d964a44d521130083c1982d2901c0d9141c0352280e429640a00002014440d0318030344a5130380c10710300302c005080e4142158568000342c404800000c0b40c00d0042110b00b260000c00028007146d449a0302082401100641c01d0404005100680a60100d091042d500003014030b88400032640b40ca0b1211780100c1f5070400442900f28108410305d0002200844d02c9404d0b500242414841030306ca0101c030165a008802513034111610700414010ad0080d4848074a04950080300c080c4501b600300392015405000035100100496075101051012000c02 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 874646537 1250 874645287 874645309
    0x16030f050322051005070201140d0b040e06010e100b03071206080a0506040605100b0d050c120403030b03100626120a0e120d020613020a030f0809090709060e 69
    0x6100300c07418659850400b069440e04003007442d01da8000048104840c1c206080100720090181c140b050602c9219000a005180d2540a6403096900046d404580140e1a4000f94040c100540304104000074003d01c9a6100002e0240721246c400807800581821703845076001090307030800030985055440b059001e13900041c0425035144515210500890208401c100040b0020300900c02403040d410941442c500701c0d60050208107000c09410401d00811001e0300440700c03e00c140c80e20000f80c0e40d8907110b075140030340150035240190030700c2c040a100c04e00d41e041d0082c085924040b020b880c546e81c121040d0794101c3d069031280000008201c2150f042d08104030401d0580b51100e0380a807028076160b80010481a889290780c2000305220b00401c840e1420b0036021030615907907100080408088201001e5a40c0a00410009060355501c2d0641d04644038942c483c8003c40d801030b01a141501ca0b48ac1041c03a581107c0c4480740a485080e000682092147c10180201d404c25114109003030070701801c2c0040300c518 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 874647787 1250 874646537 874646543
    0x10807150804033e0601080a0803150d0503070507090507081501020f0d2001020c03040308131e06030e1c18030b070801050a0f060807200a0305090a0816030f 69
    0x9242904c80b10101c06200101100480000130196074000d0304004840040080c04600c0d602c060014080f160000030f60700349654001d03c08075200e0303450b2100c990f484501680c01c2c58010200181010070844000f0140820038469001e81e02d6540c2c54207559070850754100c13142d10015424102041c00c01042800c0d2020b0001e061042d40c0d0340210b250340030342c5044804550400021030040410500c2500c4440f4100b0486410000754074010007047c0c00c580c0c0c1d0144d400054800f0400107500c102d018901e10180c002404207a46a01410140308005034844182d0b115450100c0d04219994901480210b202a51005503e80088086a04090442e1b10104c0304090b1140358060140110124a03c0c20203144550455610401590b0500e000c0c80040201c0c2c2d032110700419a25941803005a17005503080b0740c040703460700c0d045d403000ca1100510000c480032500f2030f0b205c0c1d01441c88060285036101004041e000010b88109650f00e40e0745401c035a40e0610191b00032155040400144005107440c017203c001c51380 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 874649037 1250 874647787 874647797
    0x24130f0602070f050c0109141f0c150c03050a0e15070e06070f02100c1a040804210c080304050105120a090b0106020a12111009020402161a01080715080403 68
    0x5070303d03070354121901c0724103000f0f0326294001c074107011407580d12140300005400310305a001c580c10750350400700302c40018041072034185201c41905a02202d10031540051019040f6005020040e9141480c400800f590780203640060f00300301c0021010129400b410316064241f80050801c100c0110743d141d0709040c090240c0c004c0040003e10f800ca2683d420004e007801034091404a543c48480d4810030292100c0c400e0888207005da101b81d864040352407a001d200c00b5610b039104c2c009051380c0e2441c0080052003250800ea03814000c101108000300e241c8000754031080d1049404a203096200c9500650701d01642c810b1500240d000c20100780e201509026080c0c00051540e80400c1038003041d0b980450b1074500740c021100680c13058413070805000031000c45100c08101c074101b118074205111262511903881100c0000c900ba11759454604544880d8121202400c005004901641e151316009020b004120380034148280c50781c0010860840200303185003195006000011001d206035425545107070014000d0b42445 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 874650287 1250 874649037 874649047
    0x19031b060c02060a30060806010602010b130b0102031e090a0501030608120d060f0b0c010c09030b04080304150216110405060306062806030902240a110c040c0224130f0602 75
    0x200c0003a40c00400b0301d02c21100806c0090421664034540081644400111781c14101034107420f40300c1d0441400446100340001c0344208031000103074a14031507005409401e0000c080003e0303443c94038001605950300100c4404840382d03a22001181918014040c0407001d400c210106e04600180e2401000120151710000c11119603c070100e001039201681304120840740020503207a40c06080c4528080e8a03400d060090415003036413102d003a00e001c000d200802e2904004046024028050142100d40789000e07800c2d542c400300310807a002d02c80c00c019070848240200301071003840c51400c2d016080c86004080e008082c15a91a8200b0000c41094503107151000e4003803020500383c451144085000c0c0ca01914089803200161060084049000f111488004048030103607014501103011a1071081881c50980b0408501402e041e040503210400076510a1420340e00703e02082c0c011600c0b40840c00c000c8c040d400e074400c0e40040c80004100840c0c1d2500039002e0100780c1c40019119020600d80c00c0d002d46801410300b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 874651537 1250 874650287 874650347
    0x1603020c0f1002070312021e030604021204050c0a0503071805040305190518060304030e09090c04061d16090303031d060727060507080919031b060c02060a 68
    0xc81c10b00b841e041000e80009202090581102d8000f4103424406000c518110141c454600710201080d00e010030300c0b4000000c541c4e59134650301a142a0501d004002c1120308003440c26955460902451a0044050440015075482c0110782002126000f510345000c25214000900040000400c100d06100003801144a003813151145c0340d40f020302e281c5a040d5603007500c0c0e013101c0d50240218a417501c1a034040040100003940000c0c00b8010642c166a00041610b417603c00c1820001e1642c001ca4001c2d05e4450006070fa24904180360b148194407016104050719003450b0403204000c4013a1a00114417454400c01c0040c1c8030307501c4a09083c240c0701503c83d22511400d08a07083c82c1003940c1840001e083c12000d141e0500d150a01001400391088000c28411b103840400381c140d001d100304c040c1c02c0202c04034410740691244a800c0596289040c0ca8102c1e81c1e481340340840b42007a01c000c10720311242404c071001c14034500075410403000c141c008001c0360404a90220489880a69400c04180301e400080703000b03030f1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 874652787 1250 874651537 874651543
    0x8133b0c070b0c03070e0a12112b020415060206010b0a05040308040801051512100e100c0804140105010b070210020f030a02151006080c0d1e0e151603020c0f 69
    0x30f0000340e00307519541e08214000a0641003059002403080d580362008202c400007156141c030100341e020500317072080c00040d07002a21a44a00c0f04d2042c1c5407240c0c580c9403500702145011070b100345100702c40802055041c030401d0001c0540030300800e0b025a00c440d00603c01081c206001c1c00404403545400342c54113031242e4641480e504250310000071a1b460b4424015008403002071001508400d5038080035030a0f628006503502c201e01d020002c14a1b6a80e03241420008003070015000c42140342005019040c2e502000503c078001c22101600d12019159103112030319012b0058504031004d113080c15041207850b4003000716030352080c08444254403178520308a00100d4203202134070130400c1c2a009072290549071010812407141c024010441c03e07000d820148411b98010b03818640080e0f110075601d8480015140c0c0c90002c2c02c5500801003000114042000200c81036082803042e030b19644113446d00303103002c8906411010026103641841d00d20726082d20380414401d6010b01f04480942003100c5c1d0026542000c2d0742 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 874654037 1250 874652787 874652791
    0xa020d0b01080607031e0209040207050d05030f13030f0f200c0a090b03061f0e100504111204110135010812220308133b0c070b 56
    0xc0c04400c104010048031009024407588514182020300c4207642094403039105600d8080c5003010540d0120780c500040c0c40d190706860b041580001264130b25588510040c0440d00704440c480855581000020212a01b5951407034407a640f5445e1a2862503400ae400c0c0c0d03010094640c0042001704003680001403800403a11101181c1c0110041d0048500e07a509100c201402904203030240c40c200440805d8035100000d030035510103031120540055000c444542205081150721440103080b11605000b4042c0a40f50780c18102c4800701c0301003045880351001001c1500603002c41c03a800505410024001c1501000d5110b500d000c14907050000340c0a8903000b0740c5d40282c040212540c40c11016602c604812070211890241c01e400008080080000d0000c1c00c251003240701441c00714514047c4480310842c1001c141e400785038040142500c803000f40c420041e5a0b0041d10489503010750148002c00d40903280030602c079001009503814035103046080003280c014400940307040d0740160b00f04440004200f035200094 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 874655287 1250 874654037 874654043
    0xf05030f040311160e0604021305090403030905030d0506030c040c1209050c060d0504061a09160e060705030a0206010b0f0d09020f030a0302030c06090312040308060a2619020609120a020d 82
    0x103502c1310700b841101884044c0003040140110b00c10020000f0451501219100310742c01185c1d120103d990b00e103000c4018000324507008085100100b513003403454445801c03551144c0b600ba0212003107980d00d8000c010640e01c0d4194400041441d00d00c54031a2950b0680241c0f0700d07940110103ca020710024800702d045540054604140d4955a005100401045008813840b4160310082082c004200e074000611802c005024024035202c6260b120000a008001130314000c88010091500c59840b810440e031250b0284e02040014000d800001c030b5003111110a844200385941b040d0790400c0300030880304c002010850000e03130380613a01503408800c0d41c0d82001000c04461296010f1901c2d20050041e452900d8000390440e01030341c00a1007180c10307203114880040c0d807240e014076165081e91505c00103c0e0062000303800228519002d903c0c800880c01c10341200744003c00c050310840f200b00341003003400350a0104400000f0b60208040101040302c0c60020f50410140c0e903440156030090486038001180752218010803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 874656537 1250 874655287 874655323
    0x402180a02041d040308010b181008011d09120c0309041a0909011b121407020d0905010518010c17131d1e09070e040804150f05030f040311 61
    0x7481030203418a000000a50040300403d0941000c0c1d4000d0000c003014001c1a081c21000728000d000d0756201e1000d801d05690180c09400040c607042c100524510003401507800d0043c071902d0b4211072019103d603e900c65061200a048070f01c00c180e0031b016155204100b06107562209104110385a030383c40c820180400b0752010614a040d03225800e1240d40b032001003403d0500e91401c0c3e0048000846968440300400880c41e1134081c2c50703200800d00c0300505001c66200200d02602081080d110303000910400d01501503103a60500365a24001100c5e184624001c05040e0608200e0f15005940079103540e40c05280715030000707611124503500c0c101060300300c01c1e060324070141010800c0080c06c580030040b004061880d56100054917160789030344a00d4904c41e51401c42a10a840029580d000500040003c1c100816601105003081d0510340d1250b00240030700b01101c0241551408594000ea806001008a40d2a05801e40d65405c100841c58000104154148421402405041c00c400d10500e84102010550 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 874657787 1250 874656537 874656539
    0x30c0b0306030f0d09050409021804201005090405180d0c0b0609060916020f0a0609021507020a0b0a030b1503090105010e06030a15141303110619050402180a0204 71
    0x406241c103515100180f281d4000051040a0301d50000800083c0c81c4142d402007614141c9202154a41007000b07a0101505008003d02c0104007000400300340701c500c01d80449a10b2105401049038a4044080c2040410f504024086160400d604059407020300038031020391601c80a80c1d070504060101c8a0940094680700034002080f9610800c0303604140d0589841c16103107042c00c0071a000d00005440225a40224044c500600d40300300315400d80f00f2000f8042e541d80d140c0030319115024000301c0c20224411103910391400c3d0380e86152001d40d041c42c3d4000b010901c8440c034081e00380d0707110307070290b03003a80d04050311507420380506d072100c9401c103100c007507200c1089980345801032071982154010380180350110049003e001850b500081c100b104240c006500601e03041a0b501c0c46002040d1600542220003510700401800c0030350b50411150040c00380e11503c0515480700e0810781c0310300007240c242d0054501c180a0058081c000c1c0d210b0390f80944082c04456601e115480070103048001110348481850b00010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 874659037 1250 874657787 874657789
    0x302070602164e021c0f030f0c02180106020c090601050415052106031902102a110a1211010503100b12071e0905060a09030c0b0306 58
    0x100c101e410000840080e1503881c01d0116240384030900c0080301c0180f02c0340e8800d03046202486040d411042c07444014090451043e004410702d41440c0d948240d20603010208424071130070b800380000c5001c541c04544140c48054550f81990411003150741c050400400946100050300e07005030a4186d94540c400c03c100d198949080285850801c500c4680504448014010282d8111050702c00361a4580610f8401190a010840d5640212805500c0c03510340280000e15001800380d216002e000164295031602511080c0340a8800e21108025045048520344540b6144100582544100c111702000403900d03020300303445560000c0d4817098540f225803244c00d4000d031038045049001031a04c1d40094000c14426112030489441c0c0544950600c44000001480f00540c50360f014040e0002031031080d01c60400c1d500502841800700c030141c010855020100301c03100c201c2da821000c1c80c08107540340800f0a051405000c0e049d000b1428001c14413007201408000140250014806850702040c2c40d03841e0b1400388 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 874660287 1250 874659037 874659043
    0x3300c120a0203030a181505070e03100605040e0a030503190905061906080d08040809120a060c030f06050d020409060e010e0f150412080618090d0305091f0e0a050a0302070602 77
    0x61b0b00344e80244040365440300004c1d55084240e00c40c0220405c00580c4e6070342d281e000d0f00c41c458001e550030361500810488464002141e03100d4410b851042c0e504008450300c0f1106c3c01c0d0b03224030010024000c40d6080c4009100025a900c12003c901c1960901140f000d04075618a890004203403548c580401d0021165412041c1ea403040c60001c001480003490801c186030405000400041c201500d40a030004004686071650301407607010440890886208010f81e0600300002c0c5204100540000e05200b000086c20045000d00025644010518000191a503007084010075511004540281c0c075035418a011090078411010380c660700c00f0280c1b005507601224241413500c0a4014901d0000103824000800d00004211442d2001420210300b203894110010310290f08a10f1440400c00c2074404010f02c0c21804282c48072100000c0e01c3c18025501c41900c1d036038a403c403406542d0f004c0704090304407101a0b13040307402002000000500761540c0c9a00e548446003003860400b0203030094bd10154040000356410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 874661537 1250 874660287 874660301
    0x50a0314150717060f030a050a060506040903120506040906022106100801061803081306022e09020f03070603060302090f0f07050a0201022703300c120a0203030a 71
    0x550401c0400703103008040500109082e10000884107242000908180c031000301c2e070380940100900312000100c0a1400503a52180c0b18002c03501181000c010405604003070103a180580c1d415200c5460003520700c21180028030000f0401907102da144c00c421804940644001c286007201c4c01210500419107080249080c2d5024000b14050702455120b0505aa401520681502c0240c5000410120046283c1000ca40d0079000541040f10025004c60030103000300e41102152860340030b0300c8032800c90454401200b45490403c86805240310f07290031810140b50700c0106643d1008042c0d10100e0200c401003443c080d244e411010201e583d0f48024810341c0f6003984940d6000d8205d41d03a003481e074500400300500168018000c0d20500a002c43e1041043c0c2c000c0d011f42d01078980c0324111514030f00100c820b1294402e040d05895001e0b02856210400f00d0310075000034031503948000c5801c02009107001e08055a940800c5158110f40180703200d610a154180000b04407595032580110b071039003800c4036202d00711421313 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 874662787 1250 874661537 874661563
    0x510090302092811041703090a1502030408071203080c07050d0309060b042d0e1504030509030f0d080c040302011205090313030b040b09011401150504050a0314 70
    0x9004100680d140d04080c0d80c85040c40a800403a24861180030910041e2280303192951404c100740950903120210103401190482d44800d6004140a4000c0c0e45038070806100d9900700040c10418801a03040c0501640d50034445e00c1244d2820780d54023040c42c01d200c840d40200d15800d501c00142d5003410740c00300546405c200c0d1542440d1a021041e5605070381e460f0500d44a2081c981c07207050700010700c40543c0c0004003c04000d4402d02840c80015641d1410007000520300303000c29151980302952107414403c04200e074071030000030301340b041c5400c010b41d0188200810460400204200c040c0135600c0500c2500001c03c245e00003070034034181c801b5020b05443c20080c0047c2070300c80248820000350307a0003020600011080f120009141c0c440c400d1550035841045491b003001040d40e60008204610190454419801442c100e000343d00ea680105007a1200820303030110842082c00148100b24102e1000302400310541070061400d039844001c10000351080d070003552a17100040c07051030041e070140412820268 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 874664037 1250 874662787 874662797
    0x1b042403020c03180409080d0f0c05090d060504140a08041418061c0b090a0b06100807181a09040b0f03030f160203030c030c150103030804200d08040510 67
    0x12801450b554a0041c107016944a00a40e4070f44403540c5c0b1075502c0343e08035a82000549903562020241d07400540121310301001450300d401030016080344110b060303508096009000c660b040b9465200c1c00007030306015000b035640100c2c42520070407201c000c00902d141c41e071280700855103a81c9420701006075090180441da015400c100a042420084a071420350b0000307049070112045070512848149035551402c000f009a4991028030011107000989601c14501c00d45080c00d031942c03480c0a204003450f01d50f506901142905021440980c0075104059090300a41140400700d40c0c5d07501c981100c3d2121914094560000260b56407050a041c0140d01d451036055844495098292001c00d84d24880c0c81300c1c1b4030140d071022a1050542440320304000c0c02c6d80d0000c0c1101e880710048a86a0340300d9110444d10466881044242c40da00c0b624103180c28100c3e501511a51300301e41e540d850314900e450b9404851351440c1c1c51017440d51a00e66030b8140a000907402406c24a0b200da0821080c07001308070f034040d08001800 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 874665287 1250 874664037 874664047
    0x2091905090f0403090603050a150303050904060b07050601030f08070f03090510050c0c0111100509061f0303020d1b21020d1107170a020a060c050601050103060302030a0b1b04240302 80
    0x6500010f42ca0300306d8501c1d00e0b0002d00380e61040c00907401400d00402500380d80c007201e00e000003071641c0074000d4004098201e404211030f80e17444901701e142e40b2030341000a00341c0d00490010008980b2292580c01c3c86c6000303070000c91401e8015551000e1030399580b18100e022440074807081c00b03d810000c070b11a031900761504000349406400309202e980c0340300c00e2072041d0400400c055950120041802031001080c4001024070403420448401030b01c403d0704440ca2404810313461407910501302c903490107104998168028009404007494200c03008200004c52071400600304c80040e00080c1c09400c001c04007041008440380040307a628000303040841012084d410401488094110580049055000c0390145080e50525035034642840e41059800c5401a5008105040005001d03412440c0207241500c90f606031100ba0b88c0f150011b50440c0d20602010303405034012201240080e01000315140c00c00c015405080d250301070070050104a50160f0081c0008a01d800800004010f901c400d03178a0000c3c032403e040d803c2c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 874666537 1250 874665287 874665293
    0x70b03040201120c140a0809190c0b071b091d0d0f0c020414010f090b01051206010e040f110919142106042f01091802091905090f04 58
    0x500c40206401030000d68500d4803190140c040e45d00070504504e905200b45c0c4818401d40c000e0242d11088500c100e56000c0d40200861955a113540001c0c190f901c01816485c1e1820010002d8035a0003440d03003124130703411120907445203a24081b4900002c2003c01e6000c1062040c48038000e03103044590355065410342c0204d03080d140d015000206070200d01180c1c40c0c02a20071515000123806007450304c05140b4008440000030402d19444505a015030700003503010b12295241d20011540707441a808a280150042d00200d0f166601c00c1c000c0d06098400103002185410f02130b64107600321604e801d0990012000050850094107082c50001400c0b034070b102000520a24021034503080c400c0e1403a000384075001002170100d10360808907921081c059170004840ca01d01d007900c3c0c030780c9007441c2904c01440846a4104c94030b28a000070b0010407040001a5075606206142655444c5241d03003c2903c65052a024410840144c44060003001000c0c050441d82d00d4592034070041c8101082c0141c0b2511465502d00100301c04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 874667787 1250 874666537 874666547
    0x1b070804031b03020321071a16020601061b03170c0319050f150d050607090321090504021308011a09070f14030a1e050a0b010309021c05031308010905070b03040201 72
    0x24070321030b44000d1b10350142109001d116610031414020a04007100382d01584000501d40014401d4451030403e00f16600c60407400d9170703110300921610340003543d21803d02907085007004203c0c5950b032217424284d44c1800d0b2860440080380007251903000d1450003100304a80f00543c00328004d500844948100302d10b04020106011000000b8503000307010088146420540c5c503500e115601c4507801c10281c0d074440c00c0c1280010403010751071009550361200383d61074032400e00c0c84443c0c81410103640c3c0c1b03610020350324000510020750002c800300c0102201c20800000c1c0d012081c010ba4401d003580500b004009000d00f0f042051240d0064200010070407415074156400350009131420030700200740340881e00c0f0380d00d4141c0f840107880d00d040a051103070700c9485510460650740d0803a6005820a0400b80500d40700ba000460807030702a420040d510103061601c180c1b14110210300440542e00a030103891030308041d11054102884503920540c92607541d100c24a040c40424030140b80a0206100041c1c0755080c031b6000201303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 874669037 1250 874667787 874667803
    0x91501090b030c132702040e0609061906020303060414010e070806030c040c020105060f010f21020d0905100b06090f130e0d020c011b12081b070804031b030203 70
    0x1140140000403420070000c030300945866421100401854035291422051740080403407140d00e4600c80301a18010301903150003540c080c1da13141d03901200555190030401c000414054031440d0400080854018880500c400342c1c0d0161080d60000c65072410a031060000b280c960444c0f05402c5e00e0000018001c89002d030070160b0f008074032460183c45a0b110040017038145080007442550085c134040c040040343d070301034028600c104003c0f10380c048c481c101c1070015950a00c10700107000003d4481002c02c200220000d4001c01407034245000182040800050101111403040c03068030030f54010442c03011054007074010b2004c1e40d54259101410b042c6c491021a2081c000401c4480c4907440030443d41030024110b038009660305c080501140c00b00280b13180080c1d182d040e0304070b20030b0005411071007080592060941e01805140c4c0324412480100e9145800c80b00c0c0311010340700300c80c00d425810102210000d450702401a4500401e0341743c1c1c0e22807840c50a01d4003c81e0241c1c1d090800f42e4035103820000760303802142c0c0341 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 874670287 1250 874669037 874669049
    0x10e0d080307050708040b0a17150f0d030e03120903070605040b0405010f020c0a091b02190f02010212071a070810050114070204020403060608010e060c0d0b01050d051509150109 78
    0x94840000e840c081005000c6e03a00902d1030000c022401c0352890781d114420b00c4000c08200c540020b5911035150200d081e00f461421240c01221008000105d800e01010f8031603a030303000f441e0120130003040750000303410301583ca0090b2002140100d0b9407a02c500d01801480300038000380c01c01c94581460b0401d210f400e8041c5115030760501401035805030301e40e40280544042c17030200809900f05c040c0c46a180100500b0011811490b0064200d40c0078003003170000406484454031540103503108c1e02c10b40c3d5101c80814003818100c1c11030141c0202407500da08090302600e07a40b1700c504c1c090018191059440b003a21440204000100b21030101403182d299181804042594801c4ca0b1070b92426000d40140d2445102c0d000000b0740082c0700207070020900040c0d9000e1025110510024421000500c02180d52144141c0300c48069840030400072403490f1143c0d2162100740010705001e41000e0f4143d0703107a4210f807812603582c4800342c900d691810303103480d055203100d601002ca000560301c000324060000300421994020b00d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 874671537 1250 874670287 874670297
    0x7050613080f0604170f030a020702150f030a0c030c0c02120705030307260a080f07090e04140f3405040903020f06010504201803010e010b010e0d080307 67
    0x1410242805120000a8150a412122a14008442c0c20741e41d400c00c4400740c40004440301603070b050900480440d641802c29030f1480d401c40d101c0810320802035200090480e4801000360511040c080e0490203050b40708800300d842601c82c900f015441059842080b10300303040520f0012030541300c1c0d40011401700c181c1d8065035000081e0307444080491520381250055541488080b881d10100044500e6a1080744d04490400103504034242410703205014000b444e1000c40c01c0c0c0400150a08206221150310040324035081c20303040ea440110580519040e50143c40101d45c2100d268002042080b0080c00800100d004110300303001c0c040c80780c180390085015141300a807040500c00742c080c00e2003c1e980c0500401401046040980d18019640d107804406403055070081800019a500d0640720b0341c5102c0c0700c040300c0e008802c0044502c1d62201e90100c84011030401031444100c1c6142c0f0248201000d901c5504000582d0145070303000075040b9001849994132880080e10301c03100080d02c11040c0d9403c02500d00304 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 874672787 1250 874671537 874671547
    0x7081009051306090507090e0a14210a021504030903060e06011406090103110a030203010f0816062610140d0203031602031207030201020a0905120c010503100306060e16020708070506 80
    0x1001b4100341080e40117101290601c2d01d4543c645402040710707080288280e4814001c500e000300041d49840388001410502081c0000c21800846440c1c0240b200441c10f1041d0346a140004c03c08001d20783d01a00d040d00010071502e805d01c00c20078544121039201881030300070141c640c508940c030f0802408042074103000d1000841d168240345d0094001428009440310a19210100707500010000d400034410301921402c550000505900d001c183e0101028600340e1120301c0c141413607800c0d40c62081d040d402c074410101d00b9281000d10010742c25414010041418212541d51900d0005203c41410300c15003441101141c1503000140c0d4000212050385081014141c0c0c5100a030002904064400d8400c1e0481c582c000b4a9104056040d4001c20310040750b92101181e840d00c0d0424480000004003810400e0750249140c0d00440d801280a168450086106080d0845d00c99a0b510161501c0da88848002955282489042820b00020032841c40d040d10052034035525001401c0d031b94281034440e00713000b00f9000070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 874674037 1250 874672787 874672793
    0x51b0604090f0507081e0703021b0d0c0506060a061209020a080609070e010b070803041103010f060603090c050402131811031501080c0f0f030901060e0708100905130609 74
    0x205a0300200090042041075203a0318a4000191104031490300c00140c0d64400569400701c1d524949101a4002207041c60640c0d0b810340980081d403002c0459101d600c40505060b0103101c08003c212036084095480181c41e128600d000c0b403a1582c05815184034140028082c44415449210b90613070300d0491740080365041007400451503400003a005148036004103020411071701400110313001140c4058400300416a42c41000e480d41d8000c00c1001081c0f42c50410209005c1341c0b9070001c81180b07500080c00051b442c2483d441d50000c44103a644048046522075220406010080410f100102810b0f01c0951801d065080c16007002d41140c0212100301007521042c26204182d0f038441490000c4c4a0394156580c10824138001501170000c1400c2e00050440000400c038080203420b550503007800f102c1e480c0c01d010702085010b41541009080020541d80c82100140301c01ca03580b0b06500a1905848035401400d00380701704c1421490f41c2c0c01c110032040c2050180704032009a00c180600003034004c2c400141800f5585 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 874675287 1250 874674037 874674049
    0x1b06070507030807140c0d0204020a201506040507020a1506030606091d010c02030a0c140703062c0a0f110a0b03150d0c150909060b040609090504051b 66
    0x48005441840303400004401c02000800a0020f01d00484080c410b025204107501d54900c07410720920740042034070300c200740113081c035801400c0c0b40109420452141000722543c43c11514824401c004940d000b180c200d108600c00800c070300e4205070203075801e001d04e00e0302400c080c0d03464459020041540426114900c2e268916511420145600c01800e003c291b9032560010701400d03980340d48100e01c00c502420203000d01c00510412440000c5500034600302501d80034250f62044040302e080e222907035042c05148a0304414081c00003d188500d80c00142015441c0b1610703512103198205024450b80094040000e0400045110007198040000380106d25039161503003000b07a00021451304072142100c040b030035150f820003441c13160704542c40c0d08005580c54401c01c280601c0c0d4187c0608401e132850030502080752641598107e0110905143c0c0b8110390301c911900880b102c5600c46d002484020a01b40411680820700000034400c41c801801241450b8843c039403290030f507000c03541c11040800c80291145c0c0302c0b8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 874676537 1250 874675287 874675297
    0x90147180c190e040b1c0b090114040506041b180209060712030c141201140102030c1c0206180c0d021f080a0b10090b160b04030c051c021b06 62
    0x62481240c803082c5490300980840a088000d510480c1010121091402d00c60b010101c42200500038403680d01d29516600b04000c03014080030700075500c1e0404444c07032024002415004511520046c0b2007883d041c14040030f40c0c404e40c21101e44282010704100550500030b1144084001c00120059607110744c400003e030a071203080401450703610100810408070b07425a0140d040c01000f9203d80301d1010448801035400c2c4260a6a810300d581c40d100140080a9402c26040c501c40703040c0122407420b08901e20304c03890700410b0700194a081741c1c2c00206030040c03a410701c800c9400001c9030100100c0d412100841c1034650160301d0003a80110441087d11040d50742d450141080c85071104148000b000c01c124000700401401c13610745030a51304090102d4140d0a04120550404919039100b81f039060815071443e900d5807210b0400e41400344c0c4002071802081403405d15a001c2ca20948030200d60403d039141c41400c1118000702007103046c0d1007511f1041c00340e80105508000019242d06c0c0d000200101001407028019 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 874677787 1250 874676537 874676557
    0x603170a1808100507031112040218010e011a09010801140a031202030d0e071d070c05100920031e010204030507080c01090803130e090147180c 63
    0x9184000242c00c07030b010030b40006040b00304506100079a6403010650a961701c2c1e0b41c011070020401c1000c1d03032032120500340e03540c0c02c61720083c1042c122009542c078080da1000280c012940202d5a9001000900180c09003e0514212140030740d05080084d00060017040b414483e10980740500013440b64299aa60704c40405140e01c24050f648a0303d041c00000c1d941d41180400c110f900d89001d500c2007103c50009601070482d00150391100c0740e41c0c0d04c44400ca269084c080c09100c02e000c0302074140c1000880900c1412446840c003000085e10448605240106142400d21500c41741c2408445e104c0984010034007002e2925003003501162940340401c02d07402441140c0c009410b82c0500c41e0013180441c00407603807240303481c000d0f40c07201c08180d120903942e9202c1c030815161880d038600f80071007009140990740505501c1029040009010328a05004843c0090064003a170910110401c040d0032100702d910340c0401d01d544890400480c15083c80202e00881a181d103410b9209144800003042001c154080b40c4030184 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 874679037 1250 874677787 874677827
    0x40b13061d030901030b010203070f06320f06090f0403030522051b1207060e0a1d1801090b010b2214090f0f28090c05040c030603170a 59
    0xe070103515440ba00030480d102d00180c204498001c15600c000305903480c40f90003017054100300745103a581600038030040c1c85401d03000c56001072070142c071400d1214441340c412000304120442d20304480d5801e03080c000184034601c1034001106002440c00300000445d802a4075040000d0140c17200e03403442000040520001c0d24940d080404042009030100c0d0302d1301000c00c40d0f1504190030b05948200001da00c040050800b60780e000c010f00704185482420924044400030b88522825600d5412182824085c0d81d404100f8050000070300c640d20181110354001e49403200c0080054071100c0d83c90306940d48040c420301c00034440c00308034060214613040e000364410040d140d4007013070603503541502c00c010103620540313f00c2500000300144100000200e8603103d002d003101e8a0088d0341d01c800c05c2104620540065074208100c903170203249450b003e480781e00f2000d4003940024144c03038a460200800d90304040e06450405003003640400c0000e01e82c01e206034520b29240b045a4036044072840071518904400070b1120002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 874680287 1250 874679037 874679081
    0x61502070f060302250215220b0f07110a030b010e180304060906030f06090507080702011103040b0c0a0c060c09080c0402040b0a081302030a0605060102060a2c150103050c0102060f040b1306 83
    0x5540d140350704000c8200448100d050796581d0003a9664001c081e2442d42d118000c200360310004ccc0e003c0340040c40343c400040c41003034076079144e490b07130781440009070803c40354100c114080c4502c014240038115010b050b40c03030043d0714041c1004801001d055081c8540d0051540b10f0108190f000010340090300508000d00c1d0400541c40c204200600c80b160640e031702070165190004002500300c2c40001c5030302c210342012b403400160b25003550300f600035880301d200c250411203000c100d48001201e40c09140200318455844007540350428052906100300100320a00c1148100004c008810f801d81c203584480c0752600344001d242d1303a101090f0071070480c1707135000941c580101ca03c514100409540aa0b00442080c1c0c2181c01d203076603100d0039100301d40c008911942c9443c0308080784070b5044800e03091155050102820343c0c0001000000030900d000007070304101c5058012442c0c0c6070b03040d42e0402c511640040c0c0c1110082103400d10380c0314036035400e6003c1d181d0b45a02c4100c00f440814403006411203030311281c00c2500d03240740c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 874681537 1250 874680287 874680307
    0x1020d0b1009080c01080915100f0602010e0c09090f0f0d08010803070507180e16090e03181903120e0a05040b03060c09010201061502070f060302250215 67
    0x300040304409101e01480003028010301e200c0c00854050700c03810802002600c1c004c60045d21050001070074200944145003070007582d1109191140c3c09003400480c100e01ea82e05015140d02c1414072500000c1c00c5a1400903980b4003250f0004081c40119800c0c0d8558100b0703101c0030141c1c1e084c28860010110103100b550910f0211140001d180015942a65a440c00d03990b228414141c49200e8940040c006500440742401862640401c0d0800009402c2002403c0b05040300024181004511450791104d86a0010444d5008a000e01d40d1100785440186d45484105003541d084011b451084c1400752204042401c0d10107031140812000e181c0007206041d4001f900c0c4001059400e092201d140114600c5a00003042d040078091103d500c40d006003d04100d0740c0390442ca003403903009590030034115900c41d00c0018804002402000f980c0f43c050f4080d0005505010440c403107080c1661005080510410a0310301101c040800324903411040407407024144030314000946004176070101d44807118070001d000401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 874682787 1250 874681537 874681541
    0x90c0d0b0702010c0c0f03080c1c06030510090203120a02030417060403111603020f06040504020307122304060203041407140108010b1e0a1b030302180a0506270301020d 74
    0x45441150b00030b0140503041e000488014a890000500c20084c201c0d114000030f00440e41d15034800e220300c00043c14810303032108181c1416450f0040d4190b0f295104004c1c420701005011042981001410078030003015291b01181d5500010000d14402180210704081494800d104480081034050010703035a0040d404c000c1519410145c40450104001000b4041490070100b81007141d01d9103624004451880d5400344058030240d80c890302c0d4007410400010465a0b5907202850144890f80d48142c000947c0030844800c50340781f045005854007074408000810b20096070241d40c0030303920210158032520703280b41860144c0c090f004c5d09411402245000f04030700d00742541d501c9880030266038a40c01d0b43d0f41c843d00d1208500c1910766174211003981001e41c454000815000b002d42c1a07041c035100d403800741280741c0106051a03040c01140041e8000500c0303009e2001028500075000c000700c8160316450315001c00140c051040040520048000030418811042c146503071058821000c2c000755520340b244100440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 874684037 1250 874682787 874682791
    0x901020d0504110f04050121020d0b0405010510081b13140106050c01060e0c0f07260d06051f030b010201181b0b0403080f090a0519140d0b0f090c0d0b 66
    0x1c09a0740c0f021191342585840e000766412126140803070703424030b290a4501c0c80d00c1c21000100703076040405c6000e01d400085c0704940d180d101d580100000929400c6c030400c0c8000c104416417104805510285142c5806591034040781c24616048588609000f40c0101020107045040042c0e0500c42ca014000184244c2003801010455240002040034907200c2e00f10304903c010030381c0c0491004906125403072010b10f2141c02010310501900b0311a070340010050340f02d555005c040031500c02500012030001040042c5029280281404030780c1a0620070940f50000c3d1540e5800d00440205034030b03502e29090a900030f6000140540810308201c85000d09810824504501003613910002103c1080010300307e4007a2058800341d80d4064240c1c2e260400901045c1859040020107944c0085000320018803540c8040080c0300e08212081211a040e241c001c00d000c5a85041090f030f400b4024501d40f820008059480f15a48540d8202c1134160303e84515a0152030103140c400665046a2000750b07550600c0100e419140c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 874685287 1250 874684037 874684039
    0x40b0f18030307060e1204060903320307170a050d11040b07050c030f01050103050d03050a151e0e010506090607061d0f06072c03010e010f0204140d0c030b0901020d050411 75
    0x2400c0401c0042d0b03c0d06c4c0510440c400c140005850441c1400060f5112050310300100c4881c018444103000d1048003c00601d0f05910200c2d00d500c0050460104410a6403c040e0000d4103142c890500814003000b03811841004041840c11743e40344040507030105842d0a6802030900c0e92007158540e80c0910f007580d40c5143e04052a0b100c0c1c4184100001e900c801409014140c0340d10030003a1a03409030707101094002e0480502501d202c1a01c800300d03050760310900c0c2024001003060000f242a080d07010180c032020b08503076030400001400c00308010b2000d5100c1008554094600380c0c1d000765a2641400d0080082500c501011002182070450510b006e40000b00141d5450181060b82d1f02915103a0381a00c101c0414140188494510a0100300d400b4200c0c101c1d140c242c10160001c0b030744840380c0514500b110070010640d00501d5010605021040d2110310364002000c0640b192101d254003611640071407141c0340b00043c0981f590100080044c903080d01030350360b07080d032014084c802404c041c0303018440907072550719917 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 874686537 1250 874685287 874685293
    0x70312020919081b19150207150f1d030d050d020d05070504170c0904060c020f0723012d020a0b090109020f01210b031e0606100203040b0f18030307060e 67
    0x10044d18903202e0460101404901e20901c0080c0c6031204020142d900726141380154040e803a00000d4401d075990604c02d0841c81030b52050040c49051001034075000d84602c106d40b0a142e84600c41406890006111785150711f141000381c1c86001c944410070180c0704262a05162505110a100d20300e41c01c035002d401542d0300b4160300c03044000c40d10b0328640c4e00d9540d4261a503010450038042004910190722000030030980d84141c4080d458444111890590f0075403249101c0c11140130400b0380b01e05405ea0080d403884c024a005404281403441e4268140d4020394000c103480544a1010586402080b03007a00036a806003080c1214900500d80e07170300030002c52a06a000d100c01c1b413804c003900e44c4520b40462a010400c590341408403d401d402000070100d0084881d01031240f80036141420013458030140c0d03400d5901e0002c1c00280b528006000310010903a9046066500910050100c4d03250101521550100e810380c41e92110503000045800700700c40c250182e010300001176030006001035500180b20035240c500032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 874687787 1250 874686537 874686583
    0x190b160c0501110601050f18181b0102120c150702070303030b01030c1e0201020f070b04110105040518090c0402070302100c0504080c0607050f01020313051207031202091908 76
    0x19a0003c3c0802c80146180e00090018013144c90a921040b4401401801c000f0a001001107071440c003103025917003e0701c40b0144261520502c0381c2009003400c01140e0860000b07001d031540c00040e5440c442401c8a0107141004501d054890008101d200c0701c20744a103402040b54141160044c2d140d850340d010540011b0700380030151911b54007a0084185002d09655180f51518035450700c2c07090700d11840c03c0002155004c0cc608500e502d00320000d0151039000303031089841c0707080074a000265180d00c08c01c00ca0501c1000d0000b00501e42e200011030040d680d002541c0000c03a682e00420906041103040b01503409440802d114040c9030740025a82c07807214045108100354060a1010746a5014501c1004126401109040543d040007800340c541244101e00301c0e0321340c01d00200e01c1c0d42a60000c60f07024000100c520b00e070000340700c1c040054409003005051190700c0c1038a1901e0040801102c0101155019000204903400f0784914030b18540503071002c820340c8a043c1e1100c030141c4d00c3d0718410b0f1001d582c803410040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 874689037 1250 874687787 874687789
    0xf09090a1b1e0801060503012d09020c0105090c030307081b0d0c031b050309040c0302090405040b070207090c0c02120307300516060b060c01050f0a0e0c090105190b160c05 75
    0x2450f581650a56203405045a280100f4880d5000d5070444605050758080108134280c5505044007020b0b2001c07032070150700d0b840e030300c5250f41c21034500400101c0d190340250000f01c0241c902008560845820200160361100703001341c0d9592070150a001c0a255206104034020201d90014408030003920aa0b540f800b411107240030491004052036014015410030000302c0c0182c5040c2c0c0c040252401e0609000d400d144115000070105c1c2c034110380540b000e503050b50400c0f49061303050003c140a0411075000300660b00000708000d16604003042c00900550f000d034031400c200380c01042643c86a03075004440d9985480c02d90320b01c500000b0116003001442280c1c422580505000d4019503008114181c103c2894180e1034650070041d00b1032112403074101c1c00030010840030807001e01407140305031003d8100111034100fa034880c0d0304030b0f406c01303440504a4211015280c12a81c03000743c0c1a04540c4110790003005131200e0281c1f0b02a07000643d1122820304400507410119084030b4850080c124045c281048910755694 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 874690287 1250 874689037 874689047
    0x70203070606140109091a03011104091b050304110a0314070602010e0a03050d05060418260f030a050601120606080f060d030503130f0212010b040f020f09090a1b1e 72
    0xf10207400f04203502018000e459040e0700100c15550440c1d2410b0085030030f040403c0c21030305840040340f486100002d05000c00d615a000d070125031501800080c04401c2240360040081c000988000c04018040166081580e80c0304140809540c00614846d1007007024201d840e41c800040c400d840140d400e0a1481c98801000302d003000301540c0588400d03181604c07c10100000380402091642d0142d560044c4490856443c1680412075200b000c42d84c1d984003c4081065041c4080d0341c0010104000300320040011083c503080e01c0d01f00e1070352107001c00d40342c541600590303a4040003081c05803190314003000010f99a0b40201c6881c0501c1c40d41041010b00e44910040c015041c907815000341c040b500800100c1c172005800d4004140d000c1c0118040c220801403607000840c100002007003481d1503911030104a13008e2920740300300262401025800c520304100701c884c2900c40d010314400d55120300c0340c2000051885509030854000d4000b03e00d16a42c0769802650040c0410b0140303a1681c40f040850103140710164065 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 874691537 1250 874690287 874690319
    0x2040b07150513260c060415110a0806151801080906091e07120c050924010f120507030507320f0d06090218090411150f03070203070606 60
    0x4608800f0401c02ca52a1a80b08103c19014044c00c101040a00e03031130300c612a4080d25030701001001601d000c4c10241440e421400d900c0044d086c00c50f140486502c0c8510b103a0040740c260940c0303410300c401d42d80d8880001035007554055007003503128000041d8003101d01c24444c1800010b81c000362aa500700d07482c0c0302c0300c0396551202210055402c1c0c0c402403190403e0b0088091045110101c94203e8000d81e4131032004441e402c14401d82150a031885040502c0a1703d810902144e2208902e1042c000708101a0300402d1410100340300541072215086500b441c0502c5812214110b54500206010a042880c0010010b050031110040081d01441c2e500c01c581c507419074240700303201440355400100d012100894100e070340854204140c86208000303450a85c1c07400e015400c0281400352005841d00038400200f803c2400fa003c00354801c501110401000610b08001100f800805903101c262604d00d440e60a00d2070300c50300200d03500a00010040094980d4004000e0040c2d03880381d80305100007a61071000d44a0f60243e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 874692787 1250 874691537 874691551
    0xd03140103020607170c241b1e28050708091e10030504110a06050d020a03140f0a0b060a050a030c0504050414010f1502190203070902040b071505 64
    0x2400410140c40c201e0080e064072070040c010300720340d0a40c240c09440c0940c0840d012041c00e4001e00303000d0f032540400c00010507501218480380001481c01c070700000c080b01c24045800200e4000402e88200080b0403140308000a0b210324400c607503500c2c0f120064040d4a2401c64040111038445d0458007800b0300c40c4054520032507000b14501d041c419103608000200300429040039000068038919080342d40d80b10511080031030710340c0740003940e42400d05001c041c60a52601c468051504040d0800c88141c0c0801244e000070411800140c40d102c2101e8103e019001c400402c0700001f40c00c505104643c003059010728004c044076501040b40d492a64140301d15405030307802d280c02051061003c0540c0f540290041e540007000d51602505d041e80300c0c000141154405804600c8065000c0e00600c0700c411015036804c003500c000d8101001142e04050029500c00700001700d00860b406040000086440c1000003c0241c045400259200c50700c692007500b80d608510030941c1c0003448840711401c91050341c881c503401415 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 874694037 1250 874692787 874692821
    0x192603010e1f09050601020a1509030306090b2d030106032301110d090c210515010e0402131104150e010f0509010e030a0507120b070201050c040e04081201080f0d03 72
    0x303d48500c0000074400246500d0660082c21001d40000c1c4681e503111140e0384404200103448805818002d00b02d468a1300300c0041d40d8540606185540c4d1341d02c1c041501072803403885011038895036400d813030758040c548c1401d20b40540c00c0c10004800c0144100300c840784030240c3c004100c00c800309101031390301340c5050141ca012148010030000240c00ca160b0450b0403803501450311003c14a5803800e040e642541e4a154200f14603910f6000f03001000803d110f46040c0e800d08203181c0321ba5506041a0080c10384024000034814a003092000c0c01c616159082030608080303081c0e4072a249da958050100b0340d21007a4030010700080c4250703800b046035030048014240000060b60340030b0400140c0300040d07032241400e02c00b8560500c10030039002c0001c1c60800c404c0c1c1c0a40040e0803200402c034045c0c0343c045600e0601800304020b5904100c1045820000d00c403d4404940e0342c840c080b01591224103140c100b902c69024960a0030380c1c103100100d039401d40010081181440013040390803490300036808904540d902284446040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 874695287 1250 874694037 874694039
    0x10303170609150d0c0f090c0525020d0f0b010e090a1106031003080706020d11031909020a030f0308061201020c060402210312090106120302192603010e1f 68
    0x18030503209603151500003030308500081076140c135030340c0c000c9802d903001c02c06c031050780301041c401e11480380038440341d01c007280c1021802c00070907090203000d220000b0031544a401c0780000210666451515501880750016115048c0f1819410154280c034400d005544440007050081156500c00140d000c501d9908841c1e0400b0424200e010851a035102421200039418020740110114200900601004d40710b5400142d42d942044c16803015031342c03207000c1d00d11307001d0301842001010b0800d10300c0e0740c00c0c94103031f500300094008040c80012078501d0550405800506640039a004040d01706070a01e000d400c0848052200d000d00c129228241c0c41403141d0040070341c00003404140141801e0010340000d0740c44110124260484c02c1d14640b66812800020003490100003d1140fa44028800c1c2005003141065100b913106d11500e0196036080041e2510b14805541901d0200340205c03204200c6640c04c0060490303040c98120301401c49030760400e00408400c4404040454048401c00f0303c456032203c3c0d45404580e090b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 874696537 1250 874695287 874695301
    0x3011e02370305070e04060b030615070c030803040f08030415050c0a0c0326090a120219110f0303030117070e040c060807030e01060b0a0f08060114090a090504060203010303170609 79
    0x15000140100c400d0020903400e0205c103030b44d140158005040c041070801d441c0c1c644801001084031015035880845c00c020090480800c4405e100c810036203400c0a841036030f90301c030b901c3c0c41d240c43c00c451500070b0720716031003c41032008201c46d1102014110b0a000010f00c00754440030700c0c4c00701c54482c0326100d2010400015407000003900840032107200040240c5031078044c1420302c4c41c0012080c0222058075103904450382c0001040144e00e48844519803920003005420000242d080c40b900300050043c01e44c000e10b00307031107841d0f03503d507000540c1c041005026a0b44075650354520036000e18001c081141030b40500c410106511030140c0100381700d02d801400203941c0d24a040c0c810b4500c0712001d0143c404058403100000d26628090042d50010038120f80496a01c2c104900700074a109070300c50a44082002150901c6250384e481208200b119020141c0503a9405441001510110140d030003001030f5810030b0200001c0c00520350186049034025204c9071400100c4202d80382e941c1e4000c48032a039001c890b90340420700c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 874697787 1250 874696537 874696541
    0x120f03070f0e0604350d0f0c1e111f090b03100e04021c0f1205031006110a0f0f0209061804290420011407020f03011e023703 55
    0x242c00380b1710000e280380f816400031038203030118004000203940d003c900800e40e003c1e4017121014204510785042a5914102c0d42d0f03144401c06580f11400941c804a283d400600841d000200d405c6c13071000346001c40006d0381e9a01e413036030b0b42075607020743d00031405540c4001140c0040c4001c480c403407009580d0746440641840420303e49184080c0050fa040a12012408940720f00c480c3c8801810b8055600d240c503c50f4540b1b403940ca0b090f80c1250b45400c2000620500543c40e0035100c80c5004d88501c0e040c02529017036004c0504d89000c3c070600c800b42c036801640c400c0f201032110110003c040c0900941d4030b201d03280c0c0c9490a22504001d0b10018800d607a03681d0300024089503480c0c14001c4d1302d011a103808400001d2480444410000c10f4805503180e40101031030109200d02c41c3d03040c3c91003800a0801541806068000441500a0b0a4080e005010400403401d0941d800e41c0b00503004600c0f020503c00c05401e11070100002e4005547e003541542c43c844500003820704d00c110090342c1d1100c01400041c816001003040300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 874699037 1250 874697787 874697819
    0x8011803140a091e0e061e10180e040c05010305091509030403020d1b050a14010507150501080706032726190305010b0702090414120f03070f0e0604 65
    0x204485110702040307020003503005501381503c004141903041c4c18001c0e001004030024203018443d0100107082c000004000d0124101824121090403030881e4140081d500314130b001039a141021200b050105003818122a400c0c020390180025140c0c4c942c5450064044640540c2da22a003a0b01c050a1071800c004100c218a034031100035010380e03003095a00d40c003148421403804001c480b24010f6444c0c2001c08210129400c00070841154459103040c039003400c2c81c6540c1d00300d8200342d041120020311034060007048039440801c0102060f04102079a555020340d5103800060140c0400281072440070701006800c02d407a500211400f51030240b120740c0c103558040070b9122428540a0211070f100658107401110000f8107407031172b01280110400130300194010103c0350140c002010480d410700506c030168035034441c03041d48954001c46018101c101c042c00286000780c1d040790180504400110780702086d200402450042480e901c94134800c244114042e03d880245102640d004370050008000108003000b90300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 874700287 1250 874699037 874699057
    0xe03030703082809030918090206040b0d020c061003050d0305250e0406090e3a0c05121b0c0d0206090d02060c0a120809061f0905100801180314 63
    0x5200d01c50545403d8240c81e0418001d03400300d01078050401a040644000321803100701640100003401d29940000c1c514040c0d801071313031844400411040b03403d51050b811103d0003280902290040c0c034140c91109460700150000f200d180c01084140c1502501900034240180440740c184c00854005c0e45400c5580101d00d0b92143c20041780741201c0c81c1c942c40307134803904020b0b0151040c082400d10303064503014948403848445650b200c1c401e441c007075210300d01c403d90356442c0384518101c3e23a90491001003ca4142c20301c0340303007e051401100e485401812070318000300f0107aa001d08000365400441c81d64140c030340009908840d0816002c8883ea0010700e4604c0007041c042030010180c501c8225103401042098000742202d0026a002c5080300050041c1501800b5845000d440e10035403600e401464240c8950f005002d40038001280380004a40c40006002a40a801340070b40030001c5142404142641612510682c0c0695180400c1a80580f5000039002c80d541e42544070590407042c03420701c100103580001012 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 874701537 1250 874700287 874700341
    0x6010e030a0c05190b121006021605060c07051e0301230f1b0d0f151a0703140d0209120f0307080309160b0a1b150513020a06020a030e0303070308 64
    0x1c00c0b540d16010180ca544c803800844903a242c47c2004c00c0b1f07501060141c10a0055510100034856101c4001d240740095400540355107844004607407140e860b0086681129a115801512490101643c000c0500341074004500a0003990100c0b00310541585e08140c584541c910142c0c0094080c80380d400d2031a8001d400b05560248494140302d0000d61600000ca0300d800c910384541c81c10000294600480480d5038200040c0b4403041c0c90040060066022440c1442c1c641d1004a0079500341405a030503001d403024107120503075840c2101c40600c002544043c0c038051280320400300003c3d80010028a41442d1340052000b14606070a986404e49150801042800103120340780d2200c0450f00b42a0b0107000910f20b410b81a91118510710018211442d0f40e0400d0359150140600c0c24046540c401004e030600d5030340031000446131204e050300c0d03000d1100001c0c00303500030a85903400100180c1c000b84194200b0700070398460322111001d1040586074820200302400240024020440da15144529624419103840e68 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 874702787 1250 874701537 874701539
    0x70f180306051e0912070f110910030b10080c010c1b0909050607020309031f2301060f0201090209150d051b0901090c02060c0d14090606010e030a0c0519 67
    0x2480059070b408542d0746911090000301d0b1410288000c1019070070080d840050031a1580d00403890100c2d0003212409807482409803120428403d40c2d40c10007103e210003824440c500c0c034210442101c030b100c0601c82114684e00e207400180c0d010700c8001095094034200c401500080a4040044800042e01a02525003000b60300c0e6802034420442070701c030000c020a0301c02040d0101a0b050141c18007000074461010740d00100940000355501040e0001d81400c0301980401c0e00a00e0000c042c0204004c4031800c1908910003062020140000744650480301c89075120302008004003002c07401d036200b002009400505150105141754641c850540303031803002030a0002d11449503240c10303207401405000200d00c03909100d40e00344c00b4201340201a02401d004034050280d00c0350400025607801c002490320751400e07408540308031740a1190300480c82c1a9074401c110005403c00c40080c5443e200141c0740130b0701080c420140c0f0103141c180440d9117074020b60400398000c07030303249850300b40424038020155040c01000e21803c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 874704037 1250 874702787 874702793
    0x20312090a181418031e0c06040c030507060c110405040501020903030706050a0c080f1f09090303051e06102102041203121a1c06020f21070f1803 64
    0x40d0004407000c000203c0c0c01044840c00004040700584000441c41c996882e40401e2100001180d08030007030468006610809185000094010b1a5001c86503019020030b00003806805d00384a42568010015140e5881c3d036400190b03081c01c011300c0300501c0600401c695280034a001e600150780300f4040c000240c602100c040000382903a00c50401250501da0b12404d000c02001a442040075020050602d0440c0e400c140b9060f0002d807000510102c1402c2500c500c03c44020380708500b00d00107158201040c0580740c0b0920f000740152034100c58402e203840c80f429000c062100300a000602590007e41089084131944208a03070040c0c1c0d0340f40c40300310000048071520718011203100500c001c0c502902c15145101c61490001c0010003020504108542844064180c2c40041041424103c2c03080b00d94815508101c210751944c5034030441c010706910b1020070080e100807003407402003007038206942c50b41c950341200ea8602c81409005480120001d40209410242305000c0c2070803014400360800c2400189540b07503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 874705287 1250 874704037 874704059
    0x6060903030c110a0303091403060601080a0513080d09030e030102070305190e090f04050c3f010c1116060e04090f0c090e0d0503010e06010f120608010207021c020312090a 75
    0x185c030850008500c60400c10080748448060014004c040340a0720040c108200000c10444001d807803400c609940301c02040d6292124843c0805a50b4403080594035800b100c15004c1c000d20071044294041103036039048113281d00e818030032140c50541c51345134a400d10241c83da00400d0100584c04440502550b100d82020715030761100701038851100108241c241c1e14080c03400b9820006482082c901030401c4001d280c40d0810041c001c0710111001410341e050414150704030078046150a040300d001e42d403038000078400345036019044104011000c02200c030200d078179295140c5185000d10419000400b2078502e09140d141035005481034a011300100f00e0040d00d0364981180344903150348002141603a842c1070040083c014000340114210b94102a0304541c5032040805483c8402018a410852105586a9514010710000d44100c2064100300b04440d00d40c0031042c001c1d0702881050f4130800414104039403c0c08201e0702640e240358047c0141c4440c0c2e50354603502d1603a402907441e085d4002903515010400505c40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 874706537 1250 874705287 874705289
    0x30f060106030b045009100b0603060906190b070809030601121a1306140118060b0403060b042703021e0d03050403050d1a040f14070c08070209161206060903030c110a 73
    0x300064030402c40c400036504101c0e014230a106000b03240c18400c20080e030303440c4040c40b64424401d8907841944600d01c01c00701c5464055804c51000300c0341c081400c205001e40c44000c1e0941400070b404807422a40c0f40d259102c084c408e011170081000300001d150030040408590301c69008400e103074070f045800155540304419107440c04100c108480c1220010400889506c0c0c148062826426040217094104608440c1c9441580005003070b280e101c28140c1c00d40d4a59038030026800e03030b91600380000e01e1040a00c1070343c0e500700300a043c0c3c01446401d50301885100c007020403c80c5030045200510000c480c030001907000d090300901c250b003400001d015882c0b40070254000c4034803800841703541e603c501100d10200000c880140d00001061032900e44100700700c404906400790061078a0400e2000b0504514115109100e01c4200070740269100d8240100003041e07030500020341505407540400345c1103810094040320304510811000030701c41e81040011034002c1030040d956500078020210b0508080d40490082c50035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 874707787 1250 874706537 874706551
    0x61804060213170d080705030907030803060d0f050d0e04020a08010306180510290f090a2018010305220501090602040e0106020f010605010806010509030f060106030b0450 75
    0x40303461134007a4080d000c558001d54a040450031802e2150b4010798541c11400024003949000011030001d9940c940341000e0340f54003040c0c00d41450501d01e042e50b00e0f03400003d58040840c20840049940c1d00d02030080d030f801480c0555843e1001d03032031a10f915000c2c2141401c800d900311110485940410018042c00000c80e0058070007099580412034102400701d9000400100c182414040021903520f5800600401d4411036210200c0e488458907100203102200303139076545d00300c1c206040030030f6020100500300b850102014403010030751010054040d030310200c80a0108107480e2540408009100d03504800301402140006030f84e6001e0355605040f60f2103074004100302e81c0501c00420441340d04201010020040000910049282c000040c1c824400034016a0620501240071000c41d20b01704004c030103d03001841140e0807960350300300150042611140d0280680c2c02c0c1400c1120f42000c1060005080541d002240b1001d04402600c1c01c6816103201c400e0300c2c0050101d080501107400d24612401854 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 874709037 1250 874707787 874707793
    0x3040506070b070e191502030f040e0702070b04060e0a1212031a03030409050405060117120a05090910170721061503292503150e04060506180406021317 67
    0xc2004c643c41b107106c00b05d900c0c0c80f0855004001f491003200c460790070748048400100040305035450b01070b016400c0516503006640d540001141c00108180d2021421090043c02d03070302c100c5807540704d05c0c0044901e82039081c06442800145229011248241e00c0103461841e03040e14420200d054000080c199446035002c800c800d5281d0042c4003e021081c403516004002082403a4400c040e07000005850b52940d4000220050004c10803445e524021822550307008002400000289890341d660003400300e580c050300304140300158043c04401d40000b07400058901c5804201528840003d00c9061032034814000c4980301e880c2d0410784450142004420f0155110b4403285411001c1c5c0320a107171000e250243c0112099000c070041c8403010203d160f0130f0340711045900da50307000d40d030040905038054030009000d404885d03404480094007035104c07061503020b54032980d024810750700c03810b08200c020040e2498140101012401080010380154020541c0030705415070000341c05d0f0f0325600b4203a1903000c9940000c075a0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 874710287 1250 874709037 874709039
    0x42003060301110a2a020907030e0115051c080f030f010e071d060702030f1b01030e060c1c140f0403020c0a0b031f090908190203040506070b070e19 65
    0x49803e0003801200000d401082d030034807004090080040c0c0c2d0000b001e21054461070440c080100c00c880c3e81c030400700d0f000340c480401410b200e00c00400500c2001c3c1644002d520300401a0b11022109080740212003006280c20281001d00c13802c022003212401046a40344170402198035074a0308000034621500e121303000724038150314160081541c00030091069003000390604080800381407c08903400889420f403103580d1145864400f080ca4102c00206042203031180503000445200c01c1c000364800c0207020707070b418007120740580c0364655034007070a542100f2420024050035600c0e8441d40078200d071001401c140410f03c00904d44039800545e100ba912200c1c142030910421051540400c6180c5602205440000442e4a480c2c03945102d80005440002c50441c0700001812001c454440c40020703103180181081806080d00e4038104035071080301c030b000c8449440c8443d912500d00200c203480484d48040c0045180c00b445690712000c1d410010100404e00170840071401150301c40740700c2807000a000000b41040c41d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 874711537 1250 874710287 874710289
    0xf030b0d03020a0219150c1e0b1b0c0c0103150f030b0f010b07261b0c120601080c010509040f091a1602100b030c030a0803010e01171b04200306 63
    0x46000503070b801c4000200c52401c05c586041b2040c80d409907241c6143c8448000b00c42e1a24001043c00303440740780052003404488000b0701c264040110b008900000b8108003140d100000503100380100a0007134840e41007000c401e0482d50107a008102007800662080750401e8481c9910701040d00d0f50380055507504046401c00c81440715580c0818098920540f0142c10020560754123a03017000c0c04080281c0544204141c60b03481c0f10180c080d82c10342e8000c40d036041d0401d807580303003180d03650303007480300c089120304240b0450703000c180030110700780d03042c0e5440b000038107a03d14110005580300d0b8800b18050790800e0b6908001c41104031a0b00c80e1007074040c0b04a1a00c203006d01841c0d1041100d030006400b0403420905604444161600004c0c080400e020348100403940c2541400040e0a0003141d02044e501800b071201880100010744000f035041c1d401503d010462640c0701c208201242c1e1034000040340c2070303106812841654060311681c80182e0300080022401c082c821180721121407040025150704030022040c0245 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 874712787 1250 874711537 874711549
    0x702060304060510050a030209060118081902040507170408090d0b070807021e031605070e180114070f050d0e07150e06160b25051803060402010504060f030b0d03020a02 74
    0x85c0780c11540b52a9050860300026001007014160302e041c0400034035880010142e18407014020700000040c0c61740c034801c15103206840d1503028012885a80b03400b00241c1001d002d00011000c0c070300c0210001071319948503520003049600158031158054074200070384000616200c801441010a81c1d22602181456800645003042d0a8880d0590308580060710b00101c800200b940c20308251440000104034090401c513040c01c146402c10023900030500108010501300c06010b0058030301c0708008001030212541e00030114401680c240c00000c41503503102103028824400750040494030303c000147c1c046404d1075645803440580c820000b003605490301c12a50758124201886001044d82c84514080c01030041c10301059400000503e07201c03a0401080100803601e80d0016601c0740803007c1c03210008580006022074000050b80245091410b220301a1414003107105405164107846060501d030420001703450107000850b0801c20550359111303840c0300d9030302c0030302c0e41d070482e8001c2d0003500d40b036961030041c0a5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 874714037 1250 874712787 874712789
    0xa1e090f020d180c15051c1d07032d0503040e190b0105041a2704060e01211a041a1303020c240d02131a191202030f0106080711100c050702060304060510 67
    0x42d00149d41c200042450b03102e451a81005003426200360030f04480e0190865080801e0140c0144000308000c03aa007556540064007800211601440301340c1748002d441c040e10030080c0d04500081051100300228900c0d52310100104861030031081c20010030146a0054071005c80031031002107800050740b0a1400c1500c2400c0140c40040c1d5224659810030341c04a5003081080d15440260700101c80c00400e0090500c010040d1941480c4015441e0a25081100b140c200040c9a90500140c0c040440d05a100c0801109500c540c1600548018070308901002144550389040300c40c00c1e04e812100140790080b00000302141700c506800140c1322252b507000300d00302c1c0f00180c1018026410b1044a1900d42c2c0020b000d64030800c1e01c1040700d440c48104060304803981c9c002e000c1c0440c4070358004414042d03880d1040007110f040c0c3c0c01d41d43e104c000c0ca5907a804c08413034030032042451034400d402480c6240c0f20032406410500c114400380c1400c601e044510f47c01b040c0e582c0c1c0110b8040c1d92140d82e90060003004400c440c8440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 874715287 1250 874714037 874714091
    0x1302100804020103050c130b0307031b02030403030e010507051506030c100519410a0e15090a033c1e020a1e090f020d180c15051c 57
    0x10b400c00301010000b10f00080c41d80505080c06230084009003085100b80c12400d43ca02034000440608103590002950700d4004e40400c4005c07542d07080c98540b15500c184141d031300d01c6410030b00404404099005400b060440035010b650140181c000c10107441e103892075002102c13a020391741d45540e0016005040030303041324250000b041101c031171050043c006601210444001214194103410210030a504001c20200071039440c040d200816441d03442a0080c04401c0c0f80c00e42911420194007066030b048909104002d00941d0000d43d9107070134000704030f4440c1c0c3c00018001440c1006003101307a50110040440044107282d500c00c07102d289410820189010403058956940712218100009a00042c200c4180d401070311007502c1100340040302e440700341e00f541c4002c0803402130401007250100341e660042d43c0300c2c0241840903400c184011190b182c44038114032070036800002211519050680035441b45159204080c2003000c24800c0c48002d1312001a0f01005906d032820000f09001c400708981d0092020180b45 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 874716537 1250 874715287 874715311
    0x9010f1d040203061602030706091211011103070e0303070c121403161103160f061713030e010c0c0b190804030c02220203010f06030b060c0a030305130210080402010305 74
    0x100c0700507100024419080310308211040c21942a1030b8041f85140030b03024028150504200100d4244040030302c0d0142c8001481d42c8032501c102048804900b40d502c03600e60107038079840030400207840511500880c0414580142540d142c082c1c035403a030005034412030f0032500b1110039101c0d2110400181000102c070b4104074030060740c14607541440c2c800342d0704518140035180d20020360f6030f803400e40c0d800e211a60450b8085518040c0181e110043c40c0c0342010703e4021107000ca500c0e005a900685807072800d051044084d00c500841d1108907a40440394501041111418805400d5401002032111400b03a80075002422209440e94409c010085544140c0c02d01c0b07800f0310490005110111b0350210b141c4949907010f848200c00d00410343c01220200c42e01030b524442e80e40c40800041040c6041e10b83c2c01cac0403948156418050820742c41c04104840c80366001100143e40304041340b10002340250051940181307480140c440801c00ba4000c1b981d0b00c81c5c0c00d1042d1002411103000c0108540e094402e05821a00035405 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 874717787 1250 874716537 874716541
    0x3070501170601031a030a11040522140705060a0509010f05040b0306220e0106081c02030406030f0f0216031403090a03050c191a060625020f09010f1d 66
    0x108440d00d14082d010904042d01c036aa01100050388610404a41c8009000c40d80d07100e4460030801141524100401d20940c1043c02250034152540c03460390036120451004401e81c80c407580c0381d04ca240c0700c403120825180642580000c050740d41402410724580d4a80b109540ca145d9a000180f080140070901420300c442884203010208056054980c4648180c070030034003007002120742d8070f180004440781903081401c200302c0380402801904454111259141224400344282900b0308011030212001c0c00164018401001803034401e42140094800c0024000381019941103810300380d85c0280140d104000d40c1e0303110541003640c002106540c48945001c4c0320b055040101e1800e88034030013000094200000401c03940764034581032001c5070541108092250ba50b0b01c807468071340380500e010780c00007070383c8540c1d44005280c0d0705205046a18856000b81441300800d4040c01401c500c1103080000d80e00304030b001c030030940c40f500d4825506001e0300242d05024400da2504207098203100e228000e6107110380b84101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 874719037 1250 874717787 874717817
    0x7030317010f0e0402060703020115090213050d12051303080f04030b06100f111f060e0f060d0611120c030907050f032805030a09062c090a090b010902040503070501 72
    0xf03030883d00680e044400c40e40da40810b0400307e002d4483c0311b44207004503081403c00983c1d0301255000304218090140c8643c1c13887c0d525070412181c154074200180841031003c8403034034418030400007045201519420804d0342d98690300c504886801ca400f031101c0111000030180103010481c02d016902c1401121069412026a40004c01704a0340402940038008901d0301e00081760300900500d5034007a1a030280c55420512402190007070811407044140340511080403a80040d07810340442e216031000780c00340e040c00803541c1c0c03218001c164107120b416501c0400d100004441c0d0f49103600c0c500400c42403649030744170b041c807240c52401c101240e403000d4442c8142d2017091481e510301156060209255121040c0c2e22240005030500d1b48100c068002c0443c00300048000085410801314030a490741555411a03949401c550145040d0208042c0c120281c141d03043d9441c03510300040301075400380074907200bc1480000c56840c28a808820381001d0314003600070509011a0400304040001000c092814403120311400e4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 874720287 1250 874719037 874719059
    0x10b090f040c020c13060e0a0212011e030b190c09060e1909050604021909030501110c03030a0e030903030a09141512040203011b03020a03050f01050a0504051807030317010f 76
    0x4038044d0b0068038840d8403003203009007580c080c9004180c102120403031071030540c2c044030003588009060349565092a00100e1040078102207491f030000c0082035a81d00078255110940600c1009024581585020119480c140c03014014070728203a00d90703142d0403810350402c040504050031a131800c034040c102c010718001400b01d08005000889060040001d480c2c1c60f047c0109010f440340007014100c094a5002c10b080442c1d10541143c01c90780100020040c1021108261005100e1504103a610b5170050000c184459a1548054170074403820b0222442d00d860080842d055401c800b0741c450200d50400e078100807240d6014031140804808a818480444031019824401d001d4071800b1001890130030005011904c3c258005003039859508410a071802c5080d40c01806548081840f500003400c00c404200d400051f040c409040e0b80000385115441800d040901c0001c19004043c404201c8402c000003903201018407070f45020314065504c80c48548a4802070000e10001a071242d0700724a03154008026501c140c07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 874721537 1250 874720287 874720303
    0x130c03020c060a18030809010905030a17070905010917070f0803040504110c03040312022a04200f070804031202070302010f09050a05090408070605090f190503120c12010b090f040c02 80
    0x103042111103a03e401c8a108e0050041c4617000f0050b00c000a00c0c200c074541c10580d0b03c09114296058804565240c2100720b50300f25241c803c0601103030401070280300400b14900040400380f003200407220306540c1c40707104c6c0c1810041d0b940030803640d410005091000c0c1c1818080c801840725005a00c51a004411804607524801e9100280c0005590a50800014401c0c401520320098084d0403490a030041071680c5c2c03100c0384911179148034070329110190300035400788113451041c5150200d90300c1c01c196405544040940c004803040300d811300f0410020001862202c0c600c11b004140350300400d410b50862002600000035403444400f0310480910421240d60b50503900d1054443c1941c919140e61103e00e007510b0035028940d0010049810b0100b0401501d600103880c1c8000da03070719001c84d01040800c042c902c04400c0640ca015045410400c120410168000c01c4e03250441100318071940780410001850001c2842a04946031020b00010311f0360003860030360300c1c0705039100040364200650313070700580069603039406 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 874722787 1250 874721537 874721543
    0x12304242112110a08190f080a0b01270608010e0c090d06020f0c060906070f020303160e0a0b0a080f010e060f0a0f081c050423130c03020c060a18 64
    0x2c0c4041c4401c5a12960721035128280385000c43c0c4601d8141e1a042080d9041700c4080d06290034201c03001e1040300c0c4621710913540320b4229144e0a80584070390743c0103409062960310781d906110487c040084501d8182e0b03140311080e6900194551040d08054000780f00075410b80c05056405045130502614034110700840e10b0303140d0105c41100c20b070103003440e03c403000e4050244101c0351642c003c14140b4501c0d002094041c46000f100e000c2c1c80a40e6140d45095803040400145440103038028130000f10300c0344000004030616410360902911583e02900080d500301b41b1501300b0110030501050044000d9004083d0a82158072404c50700305943c1089000b01c1942030040156200d060b58500c916010b03111103440300050628100b0b4803203a1074448803103036a610014030220a1480c404003603103000600c28000d450507135900c01c5c3e1403400c5c1a91468080748021159801c154480c0e1580210b071503010350b92040856242240d10056140c0070301a1205040010061103106503505204d02380c541d12046507021441d90394 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 874724037 1250 874722787 874722803
    0xa020f0d0f06050a1410020d053c0406110304050105090d060f020c010902010e04020c0c010c0c0b0d0c030b04150902070f0506040b061c02090123042421 67
    0x1d21015035000b90035140c0c03185400426281d004181c8200074588040300c0c110a541010001e13020180403660b900445107003e000030030034000c900b00484004071851240005110074040c5084090b80c81c02c0e108009500710b00d816000090030020250040354540800c69520055410640740c403001174094810b0b60030f03a0b440f940ba2080c14208100050740009481098a0021900d038800211007600a009180080e400315404402100942c80d042c02118075410151010780742d00c1090900643d560003041f581251144445e42c0080740f10003501c0041c16000d506001c0101d009460146d000d422500001c4000b8040c80c180201c0c059071000c07501d0150115892900d0060f0b650a241c00c1881e50300c083c0071402026070140380c05010a0101e080300c09402824100d41204003091152401c130f1701160100d00081d000b02070781004000c0b20068880e10b01c0c030504040304003122071807030300e0020701201e245d0300c003103031010030031121802c0a200c060410700701620b03030800d045040803003240200c41450400440200310f44 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 874725287 1250 874724037 874724051
    0x210030513050f0c0a0e010302060d0c110d0314070f0f0f0e060f090126040308310c06031a0f150a05030a20030711010e0a0c030b0a020f0d 61
    0xc04070710410054a508001961410450800942d884044c800d00003840340c02145d201154540c24000010304880d801801140b6021041e01c0c01e0010340348142a1b01c081c8081007264042c0d0960520001c02005680d40c0e0000e02d82074044640100001e020f80800100301049110510f015046030006c9150400c500303108801c00d45072a0100e400311800c038507040e00880c020030f032a440d0542d424003804c0b08a0003602c0702d2816101901e6440c16000040403860080d034921800708000c01e001c0d4103d66000081100d005114140d100d1030b51000807103460007032110084003079090041c404920380b40c4001d4901d40c0b030300703110014158641c0b001784103407d003c0d41d10a84402c00c3c901a20380e10030708404540d0400512160f110340c152440680950000c5401a011900704140c401502c0c40008140d010800542501c500796100c0600445540d2114000c132403080d90303038400750785e5820710400924044501c105034035040e6504528200c001c0d1000980071401642c010b100001c80c010080041d2001c1044018000550b9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 874726537 1250 874725287 874725301
    0xb0303041815090e030415030f0507020609120306011403190e030c0708030702061804200a0306150e09091005240a050a1208090909010e160302100305 66
    0x54415a40811074140841d003035030810a585410442520444003074034848140ea548549040d101ca03070f03040c95043c1c1c1042000b4003408130201e11060f68101a40350025200200c0d041c84011904150f4800015138805030400c40a15020050700e0721040b00c0320405421428041c5c0060641c2d00c624001c500740b070300d01000007441c4c9c40014840301c44201d03210800b40319400005442a4aa6010410640c510b01a040000c1180c0500004544600d5030150040d0f1500c4407041d80d1401e660b03440300036103034025100c245066010764000c1480d5005000800c1c0b056498460110280444501d44c1c0807809052008507101030583d0400e44044501030113480300066580c41d02191401c021000f441c28960502e40741c02d0001010106080800b001c0c07001200ca654500440200100e150003441084c0c1c0c0000c184c01c0910441840e0700c544c00c0c510703129500b854101800c03080040d8090004464501c0f00d40e42d07495041d4401203080040d424000800d001c6680d0325821500447c03068207070055040c05040d00c42000c81c8103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 874727787 1250 874726537 874726543
    0x601170f06040b010f0e090d0e03011d0709060f0515070c031a0a1a030606040b01090306051906050105030903070605071110060609050109080a120302070c03210e130b03 74
    0x5001210141e0704070745810f140c0300501000030300600351004031280000c18645c001d441d030140110302141c010803801619070001c49441004a03501031701952182ca04ca0084605181e2003030f1809003400c013420410f07041000d008100d94466010f84c0442c81003401c00c20035078491070b1210864150300354032565219034505003200c140c1a00c0d400100948848102c00880700b9071020210b010305c1010300305100285101561081e0410f080e01103d0b8581c005c2d8020811707034a8517500514410720103041031240c96582c3d8985c9012150215024040280a82c81d0b010b4a08454442c6102400c1d00742482400c500300303900705a0303480c000d090000b01820303a86d4004c500001d000c1d1410401120281c41150203045155010703802424061242c8000304900250108496015252000545612a00a044410305501c40b0721080028100b00010700d41d080013410003113003516411001450103201c200f408003441c03004400c200f05400d4040c40411803410400c6e103650303480c40341c25490503882040105a40007401e0029007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 874729037 1250 874727787 874727803
    0x2120a1b060b060a0e130e06070f02120c0a110409120e130507021f0501050102030a12060e01080d02060108010501143a17030417030c070c240c05060117 67
    0x83d200c10040780424006070710801c8400d08580c2a00c081004a40103200942662005406141d4541101c0f000503000761080d00d0b81d400d120032910417205800707040344803036070140d00c10381c0f0140d80346d00040081c109114007c00708214002041d20704010804440e255a0803100d820f81882e42040314a82c400f1003682e0300c42da0250710054a040007005141404140690703940e02600d5250b40c00d80080451580c0c01c100b0b48980c1e812168181c000d10b1074135154641c204d900388111307080c0400c041eaa030200410400100e8051134044c0410800410030444412006860040140d0100750700b40e05220043c0311042c5045a84407582c001070b14000041c50000f151500a071204110f600d10489a040110141c1503040350f402181c1400307000700018110314440c1c04811f80c03108842c0a80184010182c4040740008070380116400813180d8291360410032039a581d400e0039991071b4000303461004a02e03480c0050300f64950b102440340307034141040c96800c060f50780c030306407035060510406641c0c0009a140f140302103402c3c0f040306 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 874730287 1250 874729037 874729039
    0x6130c0c111008011e0b34030207060302090d060513050709051603020c010b0d11150403381e0c1e030a090606120b0601050c190f060906060602120a1b060b 68
    0x6c3e80b04c1103c01b401034900d110b4070fa5610b41200080c000e000d644002e029072596107c3e050b6024142c2103082c00c4040c0d020358003080301290860729001010011450301c0c4a4980903031030007000c1340881c42c868103042c0d19101075034205101c8a4500310030b2280361000c4081146034003420341005620340c402244054010304650400070b42100d46031040c04204804100c41500700401240c41d490405040181040180540d0200404000f221020602c503d05500c1d401420307004410b07500f001488803403c03241d02000c000c2d20300b001c0140d03c0d0042c2440a010f0582020750180c2c0041040341048811a518607030001486000b00c0800d030300101084840040703400025004e500240103001036943d444c030800645104050a4400701c19800c0413800711340c425812203a101040307030014400c01215a0352004c0e5030043c0f100458000200c8402907000134414044c48540a003d9100086c9281c03030500045d0829540d1039040380c4900e010000d0000e9541c001680030b40400142c2c90304540403a42d0320b0100010030185c0070715 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 874731537 1250 874730287 874730309
    0x30a17040804031b03060f3305030a080307030506011407020103090309210c0602150406020f040513051005030c010c140c0402130306200d020306130c0c111008011e 72
    0x203074100f0084ca44003d000c07248190403c00a140c002c022010440e20520009091a0703d41146030180348250018095003016150405030096a02d2001a241c00746007142101c4645010040064041e0103101d110360128082c05d0403004841c580310451520721603841d00a050580d1800d42406040c45024a017003d4001220881c50340b0703039011581c91405e002002c00b1201580c07403280c0803949030701c0803038200c2c0c5000300f03c15503020540390340c1e50701000b940100c1c03443c0e14101024800091035556070038900000c02e4182100240605101d80c0f0409036503201d0b04003900030740c4000402039442e41d000c00c2c0071155541040700094503003140d100c5a400c140008049562090000c18010241c0c103d110940003142e129203000c100741c2003080c940c0c180740c008100300c0144ac80350174080d03140300d00710b0f6030000e541c0b0020084c11003510b2290003102c80d044035984501e401c00a6181d020b400104042220741900a04040b00ca8100d60449907200500d02c902c140500c115890084c1003c50110418400c1140504580500c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 874732787 1250 874731537 874731563
    0x403020f1605041118060d0923010b030c1f0c08030c0309060f0c0a0c02030c130e0705010309020604030201031e0c020120070b06270108010e010e030a1704080403 71
    0x100d01603481d1280510361180b4500035082800c0f5294504507001c000c40000c0000017402030008201003908a12410b20000d901c404004001a00440007516003407003054041d0f018040700e180d0242122a04455507000e03900840c1058080c0d52038600c1220140800992800f44100a05040350000c0b000b4030010920040401071007000e004036006984119040000ca0705280d0300c1e003400004102c016140051044010021285490300c10300101c03007000d0020f400c1b5464025024003182c0c207500c107580140031007556620584a20745003404101c004000910307003407042050070b0300000c01d184124031009050598030f68000441c0600400007003c4001c030320004010303035040110040d0107080d41042d000074081e00540c426441500381d205031540e032900b0508030150b95942c0d009100598500c5034940107000e5000c034080c401943e0034401e840c0070301444000890040e114103025404c0d00c103080302948040c4c00600c018200160700c0010029032100300b2000340c0d03c40c0c5517410103940300c0c400c90f000504134481c000c007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 874734037 1250 874732787 874732813
    0x5030c15093120070305030c04240f02010b0f040504050f0a1b0e011805100b070602091503090a06050417030405160f15080603120415090f030b010b030403020f 70
    0x200c09074802260002c02d001407071405000d1940c1260101404603452000d00401000c640700380c010350380c01440e03114060314054075002e042d911580701c00801c03180b00c01006010300b00164020260070088203140020322061000b400080e0b00c100c85490414080c50380c44000406001c410045052144882001c3e0f4480c40494101051000c24140a1442c1c4040301240000c0c0304c4d614130311260407144003a10074040040784609940c0901006012081b031b2005401010a810181c0001480600d00c40d4600503900c051003801c0c01042e0303e400342240130101c024400c10070b034424003280c00406298800030008003580c0724500760803c0c010300844a03441d100003000f0801085400108540b425400307451000c100d587c0e13881c04200d010218056000303401c0c0188803036001180254143d9401100080548090100400c42c0400c0c0360440e03030107034803884441c0081849003508642070001030451280e10b90115800d40d210101041d606100b0054503040c0007000806241c4240002112405130009444868501d14 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 874735287 1250 874734037 874734109
    0xc1404031401180317060f1509040912050c12090a0e09010609290301091115211f05150f0c012c0a0b060f060c010c0903030905030c1509 60
    0x1011000c02d0200031404510f01c0d1400003000703417035514024230a070500b113103400c0300511540003070450541051715140c1201c0014140c00c1902c4080c4415034605850ba08110805403601203040000c46140400b00258003050300c8082c00030098800082d100c0c0031640340c181185006040c2039101c211054942000c170308408501000000c4007031451855101c002105108141c00ca03120240c0c01400302d48020084540e41c1021040d0454890300b20005030304006c0301c84141000d09240e09a0803201c403107c0c000300034002907403103005e0584841c042428035416041401180e1821100034134040c103c1c2d000300d2a80c600f4450103007221050080b480c001d0101001601c601c0d9060070319100307801d02d145406000c00640030000a003060721250017603d24602900c522081c0551904000080b80c0c1100d0100203564a000742401206601c41d1070b0383d2480003540c910306008007448203a400103803180d00302030094400c0d96289041440e041880842c0d0380d54030a0800d0000e02080c1c100a50314540c403440d00303402c0c6003400d00c1d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 874736537 1250 874735287 874735307
    0xc010f0b040507120c05041214120304050a1502091c1115070b070c0803102918030319050403170304021008040303090b0108030903010c14040314011803 67
    0x141000e00204008008100c00e070382040b1480000503d401201070060400360300054011541130400b640f40c0741c0c40b00411180030032507000130f41d0001180403200800e000b08002841c4075190380b00d146829400e080c0d03134242d1507003101e10010340030030300c1034010500c11080d45d1f0445074003c0340100070300101400f03241c000c20003000d164070640e41d607000f01e113080d8414101a4030710f007004050780529500d0060140d89003510311700c2c080e05010810001000303582c00121000004d5024691180f54440c1e068030b4040358014510200d116540700c0c038004002101280b081d00280ca00303000040814140038590440440d00d140140702c9098181d292484076200b40300e4000c40100241da004209901e40c1c4140e80c211072981b1310081da0020b41107a808044090403610078509a600103210b440c012030003504a4030360681c10b510a8005160540001820b00341030320302407240000141c4281801d102d0758289914160150190340f00c050301d00c07090b84448112480d401e5006a4408080c40419214540d00341801044da07040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 874737787 1250 874736537 874736561
    0xc0304110109171606090f17010603020405270c0d030c0f1b080606150403020d0816080a081005010f0c0206190513080a021c0f05150613110301090c020708030c01 71
    0x9010300205406102d000d1000c00e503100e1030f04a1507514900f40c0140003141c8444008c8086550307604000c40142d445000c8d0500482100a002c04280d4500703120944040401c1c08080381d540c030ac18070b440d0781d44c1c4584401c01c5169406080c1244040043d00b860050006402c00051a0000c60b4800341c90312a910240242602c46c01001c848565480f0401c0c000c20354607003d1400c0002038140810001464801c2406503120b209200300c41c108080003040c1c00c801003281204803450100415411086d690201000b1343c40414040700d2103038286040006002c86d003401c1c00c030004109402103050159254182181c680d6022410f01c6891a8018000103009420019000e0380d4940f0302703003002803410340000380781d0100360300100300d00b0074201c60002112280280b402c2c226011404844010b001c64424003a807031a40150251580b0145455001c2010302c8140700d150a580034030304610030044c00d40d100103480c103441400c0c0002031204072000d03080c1d1a00c00301d40c1c8042c910341b10001d400e00900b170041d0003036000109 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 874739037 1250 874737787 874737823
    0x1030b06100c210f021212071e0e01081f180207051504141f150302090403080a0e0111030a0902040204080f0304090c031415010e03150115080c030411010917 69
    0x2000005c070f072502240213038042c085c0e0090256000856007040203907001640e130b044c8102640c03c010314030518a100130341d92402140400c1d8440e001944c01000700c83d4086081c01d942b41c070701001520101e4030002540220142031000c0036a08858610703540c11103500c590410200e504503084036051035560b02c0200c40454a0340d480e44000420080001000c1070240b040c941440d8803001c0151410b00101000f030076880b0301035154400040940c860940342030040340a42d0b01d40c0102c0c6000b40c152801d07a0349004140c80c10f6031600c1504404500360741c0030380f03400207110300003c949480075000088c082e001b07642040c030003400780600e40300358484000300a1046600c0d150041c40000c2503090b05900302c1e0703200c14003013010307441100c0010030450740740c4c15034044001c050400c0c5440c0401c0c2004a07150501e00340d4200f0702c2c20032580061003818500c440320050300045203020040c0d40b80610040030740340409040140170940c803040c0304083340c1c001c0340100080d2400c0180343c039081e0400c5810741e5480007a40c000c10001e207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 874740287 1250 874739037 874739057
    0x160503041701090803040f05120c030c06010b13051908151b030403090e04061b0201091403040503070302090a091e020f030d02070b0a091206020c070b0301030b06100c21 74
    0x241c103018002c00c807a048505241141e886894584400b1704041301150180541e030710a10341c1d81c1c0d011018013019900340c0d0003035468100c1c02c256540384c4081a00b014481180500800b0072484484510034182d44058658000790f0181c1d94001c1d800b1681500104414080c1030402c02c011441c0b51040b40c841c0d0382548082880141d001c690000b00e00c0306403001340024420392810300400140584050b0841d10404001407490034085502042c180c14420000c0140d440c0c4031610144a56041002d005484200141d4039051a00c0c0020343d440c0441d10000b4010220400099140044c90384118042500b10600601f0b90108842c00c1c4416507a900c4200e01c207854820024200703007800600e99070f0580040d00100021814082c50490980080103c0300c10012006000b244403022400700140d118410130015031101369444440c0c0c100280e03600050744088080c03004001260001c7c203003a8000400341c2c0c5c008240c4200d060111000703401554040d00e0049405413541c018840707060000840c0d01c06030b884003000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 874741537 1250 874740287 874740329
    0xa030203010e031e070c05120a0203060f01080706030501140409080d050405030d051503060f090f07030b0406110c120f041508100506090d02060d06080f0105010306060e04031b030516050304 83
    0x16001e002805021001c0c0280c6c01e10076130406500c83e10341100940f0440d09250b00d660700113850402d04031180310420344c00f4070040014800c10031940300500700c40d003000e21042d070400d00b403c8041003050b05a00d01c603035240e4030401d007440f00c07540455000720128081804039241ca414080c1d641e60042642c1d03440b00c1d25060010301c403082e0124802c588004010040d0200e03072a580b00c9124a64009050100355006003000c401c11002c080020f640114030030030300c0e404189004e04200c0100c40e030501d94901c0b4400c04000c003e402c5030b80031a9116424002010503900c6036804800c01840340182c2e00411000e040d544003034201d0a8100d42c07118462b011400346003e509460b8801d0128502481180d80e070850180c032445401881d04901a01c0c1218550300300140003903845045900d4442c106203a40c2c6d1a035525401841400980c0c0224009009504404d408909282c0d03001004130145410002140d603082c0190810940f0402c100d58103841c12803124041007c2e18148140c49511078400e541e030445542e4180d00b10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 874742787 1250 874741537 874741597
    0x60b1309030c060906110403030306090f02090904030c0f080307021f0c1407111c030f020d08010e07140a0f080a06060806150409180204150803180a030203010e03 71
    0x400e07410303a01c803030542c18036940b868090f04042e41c0c12101103031100703042041000d000001d080114009d541c0411642e01e09041c2e6011920324000c007154150040003201c030b15840740180e540e00310341d151030034030700b85000d504004084038900e500040001c280041485001603000400e901c0d40d8018401c440c00031208034110303100721000c07141a10041485980004071641c0802c0140c0202405401028040d8074843d0004142d03041d030b1126207000320296044c00044c0f552180403c40c0c0307021580020502d145440b407020300b03604070510981c41018402c40006412034031030303c01c90104058501c900c5440742c04029000d4581c0081400000c00140f1105c002440e8281c07034040c801c02c50320a910b5101c100d03180d00023804548056640361030180c40e81004006030b14001e40c400c80300094003000e005c3c40c0070f038000d1041205803450800d20034928201079109000f13141000c002c488086410704001001541040c000c81c0c580800d45e8006941b651900c03191242c04603011005100024001d800d8031400e103c1c2095000c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 874744037 1250 874742787 874742801
    0x8040203151504020a05131d0a02040e01180b04060308042c0a1136010f021f14040803070207050a1505090d140c0f120309040b0616060b13 61
    0x280745403101001034050038240d00905c1452450318140b4500080c2c0d1482000900c025841000d190340640080c01900301c0c130f50319654000d60010401d40c0380a180c1031a540c01210180a440300344200c40110703040341111a4800205048003a000340070186d40d0381424420713508180304112020280030300409503101030ba100044520050010328020361110103140008045440b440a00f25200f0000c51903101c1c1402d1240b9003920b15500e014208400e141c40307080340c00840d030994505014042c12000901c0e50081241801805a0000500700b105014031240244c13188004140355100c1c64800c0c0028400807200962040c0d00e07035021079107520360b40c40030302605581d64030079120402900061840c1951256000701284d000007041e0007072011494580360020b01481000404a41c48507900c0c1491782003811a020310000101d520718180c00f5481800d580300d00c586031300f03d80301d81c0e070301c10800380b075941d40d101641d2952541c00c00507100c503c41843c0031300007003c1d23540c1601e1040300b460508003500b0425003d21a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 874745287 1250 874744037 874744051
    0x703030206010b0f28090b09063403260108070306020a210f060e2202042c1902010c0308090709021c050604180b0411100804020315 58
    0x1440d0f071030704010300755642008104d604002000c214030710703405c0c03042c2404036090301014100301c07811807401801a041c01110362013103806982c203110004080e0344550a40c0c81c0300214114801e180d420a0341010400c1c040e0b003c400019019001403403013810b900902050070104144486c0580400e49007031882140000d100702aa25801240300740000341a54000d0900c03c041da08000415071412015001c0000f56031703030742d4605103584600d400c480c000b650003024028807402c01c44d4178903800c0c201803604411740d00301c0641c2c0900c040d060440045403502c0e803150711007046007814203411821107081800d168200d840b054170184a0100c41d06111481c10f414824002e5051f117620207200010303501510040d40050120606000e440c100046440d01c6000034171204680000442c1c0e0401c030b50000328219200600307002d025503e020002c3d400c0e01c191507050780300e5a411030596440d56889160040e44e80d400501c5140e0030200411141503d10303005450360b401513201f2070a403400f5080c2400c10011084080f50f101c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 874746537 1250 874745287 874745293
    0x50f03070b0714030d090f051501060e01051809010e010e01080606031923010c0216081915020c06012102030706110a060e0609010b03070e06100e090a0603110307030302 74
    0x12200007032800f010780d00c90200310801c2c1c0e82410042045241200d14181e8141c5510513030b0418081003010078003941c40050b03484000400c855040103001882c1d0001c104515040c41000600c1485c5c0750814000402c000c58020035030012580c480c00e03c00900c0c1c000b0b12810b800c02d20780d82c1c0040b03220507001c0740c02c504c10b40f0040c005200030b0000208104000b01e220100750350404d00705508040d0403420302c820070ba04507104000440d841111300703002807a06015401001701d5031075000303080c001904040f4040603012016600e421803640d240c18540e0000d00d20910801c03a0520010310180d15aa01007a00f0b030494504503080e01400000c500d02c44010b0315051402035054109103800e100d064015410341e032a00d00c0b4601202e0800805175100b408640c001d46500c07030140e01c24010005075441c02d0040980d003050a50144c0364440c40d0014607006902d0141001e8410240c1881c014803181c4650721038441071000400e800003500f0182e90680c02440b0b2030205403880314514504d40b10f10f0400107904e10469504bc0c0c01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 874747787 1250 874746537 874746547
    0x303050a0c021507051b030c090103120509130b150306010c061a0d030e09060a061403090a211701080a0204020d0b0406060207080606030715030213030b10050f03070b 73
    0x2048800e900700580c01ca0b881082e001c00140300300098005805018032440040545001450800035090f100345101c920950041d10701c0c0303a05e034071030854550460f580203c0c50450141c0122083da1140100009650400181020302d100340409806c185c072000c3d4140c400b0b41c000c441c0b41c00e14500c1c51100721602401700d800032030b120b400503140350700c07125207000b65010b081c0400a001c1c00141300040d41c0c03281a40000c1c4a41040031251800202c1c4c00e403c504101c5003250780c00e02d002405030280310204484200810b000c400221108402c0c040c4010040d4021440400b044848031b210014804601600c070000d01409a08241a856501154142c440d0200180b2001d1300075030800c030103948070060801501e900c0b58200c0c3c2042d1254041c10000c0c040c41d401800100b8140b10000746001c1c401851144a0703444401c00b08044030303a0040080540f440d0b461b01590320071100303010142203030059100519805004040021a00c0711b100604246d0f44200c8000d200843c00008041d03450302ca42c0546042c51104202d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 874749037 1250 874747787 874747807
    0x12050a0c140c06030c0409051003170d150b0c010c08060a05040903030b0913020117040807020d051905030408010608070e0c091216150206070917070308032e030305 72
    0x20200c14000200d10460300101c0392500401c60704d0b0401d036200503038400085801c0c440a5042c0c0101607200b0b50000101082c2c0c0d180d0b8448180c40300c050f40d422074801c9400102445c040401c0e8000452001231076400c2c2c41003035640d00714007210350300c2905210102c4d403078a04441820380c414505240540001021642c031541454100001070000b01011424075075194101241c0380c41d829400d502c2200b22003a05144984540000b4003142032106400001480600030080016000004e0380c80581d0150351019001110f46411490600441c00980442030003025100c20420000700a20945d82407100138094295a0100305555000303a00486e09410f40c0500001d10240b4440050302c11400018440450325801c41042400d10707150b14403460316000d00403c00e1006840c03040c0340044081081c8000d000c40c1c0b610000c000c203101070174011a4400442c00c140a4440e176000c0043e0390165810518040d41c90508205150314405603642402020010004c1900e0001900d40d000040340d8140d2501440c0285581d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 874750287 1250 874749037 874749053
    0x1b0f090a020d060e0c0c19030c08160206160c0b0a020303150a0314030a020607110309010c110310090c0e010e0a050a0615020610050a080304090e0106051c12050a0c 72
    0xb00c810000682c0d02c69001a0303400c0600001401035480c01d0513907560310724052a05050032401c4002e14002d180d01c00f2042d001030390144005c51341a4102d50805e07103c401c3c0402004d0b850521400181d404800424024000300310001a2110607210700802c1c1900ba41c0d41120407040d01503100b4400c0560400c3c00040d044500310740c5807c50f105c10090043c8100ca44a959400c0c11482e44101c85032140d0001c9180c801c020b804100d69904040d1604041e000c03c0c0303200c510340d6075903c0303080c40560422030100480d800f0010030002c54400d24000809903403148526483c0c00000340780d028016100c3d152a0000065200424840c0301d05035541c40075020050780d03a40d030340c040107810b0140031131124a1340c44a001a01440a281d012250106c81d4090201414880d0000641e256650009489402015030801c4010300c00801c440c12600c2249002c640c40d0b401c04102ca0040c80b1661107250031403c40c00c200105c40703415801c00b0300c8891007400184000c2d2180b1508403a40d0003500101c402080117010500b0200e1101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 874751537 1250 874750287 874750297
    0xc02040203040c15261012050709050c0909060d02090f040f062315060316120c050307080f13080f0705070b1e0f0a11100603051b0f090a02 61
    0x910500031155070b0703a401c19804022088490343c00200d80000b20040d40c1001c002480308010104945c5da42800e01025a159042c164850885208140b441d80e1041007800d01c00c520083c101c6810800ca41c0c585918200129400b200003680300b0302c500b00001d1150314115551680c66500542a00f07803655a550040d43d00003030242c42603907a02d42007024080090f81e60f00480384200a4880c03400040c018400c601c0b0a0341d0f0018000850b51034980510700c1594840405507980401022a01d0302d508038241d5040c5c903a060164010400e107030401807600352071604000214000c80303003650350200a5590072425031003d0015688060003a000320102004140307c80c003e4200300a40c01d40142c40c010407543c90500e012140d0b841086d140da00840c480d101d280042e00c400041e141e0100000749040140c00201007240320300007041c0c0c140684040d4221242004002c030300c40385030020328204001520380c01c015542c0c244001544600f2681e141c0701c18030030300f0900e481b001c00307401c064101c0d409501d40850400c0a034000e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 874752787 1250 874751537 874751543
    0x150c030403170412090501110a06050a0b0406080d090f0e04032105090609070b040308040e04030306170105190209030a06050a02090d1401200304110a12140c0f010c0204020304 77
    0x60b40c0c0040d250070032140c4095000d50302c940100d5142c81c000c514050582c0d0303101da0250b07045c044001d0103066040300200310310810982c03000001400d60f660012800040483c40100d9070024641000807507039840015902031218034030740f00c08480c03d0b81e030088032000d080103000e18480e011400006c40c0c00640182c0c2e00e04c0c4118603100e4400d290a0940f01ca06040f10320860f0324000c40e0344048148a607a001c00d001c014054080088000e10f0725045071100c48031031040f44128280c042400001606051096211030003408841e601d030410300c050400070038080c0200741e598044003400ba250180d6030201c1391003101c1d9001e40c0903019000b51728083d00c41800420000340030f18207581e000c05c4150b5459885551384800c15114841c0d1054400c2c2c2c0355051070840c0d0004003d00c840d0046610003026a40181c002d6913801503102c1e185814850303941012440d1350480d40e00001100d8681080c031010451240841302602601008881039645a00c041140c050035200e02e0502084c1010010390242c20710b50021540240 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 874754037 1250 874752787 874752797
    0x70e100b030901020712050a050909130501060308040f080a020f04090c0e0106030917180d061b0f12050601081504090203030d0c020d03090b0a1a04050411040e150c030403 75
    0x164039004800203074021a4032907241c1c0d500050341c0b030412800901c90590003c051400d02d0414070b0929014080d441901081072040c203028001a400d40720081200380d100d6444002880720590342c4c509030b00345070414015680c401c4464080414410300020340c005800d900200f450b032100e094481032200400c800007081d01c0c90004040c02046004066240034001d0429030382c0000c4130003040c14103000e507400041640361026805c0112040c468001ca140e26100c07103044900311188490f074900303c00108118143c204042c150030070b0f03003185180c012031003440c1c0041c1900c5507500090085911300440304200c1d0490b0210340100f000c42c0380222501c5211002c0000070f4000103100546400091031500130301405c20040362640c54980c1c04a505001d4140340c000b10303040501515045565114060360003e0480c0389943e500d6640a86100450020085000303002c1c00400190509052181d4104d0048000c00d0040b81402488040010009001d8000c3c0380700d002030558a0319459012042648081c0041d42048 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 874755287 1250 874754037 874754039
    0x2010b0a141e011e020d021e06060105031e040c06170403021507050c030c010f06050a08060c0a03021210031b0b0412080c030d060905060a080a030c030216090204090b030f070e10 78
    0x380e048495074002000e0340007441c9500841b2002460187d55040b00c0f4003030a171601034010f41f0200094425004035003420035079220b81e02d0501041d01080c0c1e113141800468400004e2006000b02640140f09950a540d900114800341005600b011a010360740240141c0c0424620010740040201d070a801250034505980f52003280030226142d90030400c100d0708182d5441c0782c840504035940c42600001c0005032180380640745825002d81c1c4480f401000442c5a840002c0d954504074801e41c103c4440f0603010845043c61700340007074072480d946194081214105d002d191048041282030384450216442010103501cac3c141403042c458403c840c150011907207500d080c8042c0418a0b414005002c82100f40000010b4107460502c0090540301c002e090b003805180319001c1170021040c04180414600c0c0c150400c840080c40d21b181c105d290103001c242c480e402d01d212501c08211b844c455001007041b07c10030403003403084110803800c064075181c0b1481000380c10761050104010300350414490311b0b401a90380f0801501c903 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 874756537 1250 874755287 874755317
    0x6030a1e0209030c0f130c050f0d0e0f010c080f040309030f0b070f1b020f120114041a1308130f08010903030b0406080717030d02030a0212070914120109060c02010b0a141e01 76
    0x507040300c2c1004400d0783cbc44010751100500c08205072040362214000a0180006502020704801c070b0142002104090711400035081c180918081c4001f568004d07002102600c1604003038000e00ca081d10b0500005154105040d1014411101802803190710004030440100c141d08020300005441c402c01e4010000c0307510144801c2003031064000d40b1401003480859894580340002800d10b1845207050040014410703c0814568140840407540c1d1020420f95505117141aa00380c4000551100006041c15503006c11045e80640004200d24481e8800780710ba07420b0301003004280d43d928003030300a85034007251003003041400009290306d05c0c4074803c00f0307a854910301003592002da0348101d48038a001034001a44034283c550481c2c1242d8804550b282c105611424030b41c00304240e455072049503100712500303022027a6014082d480f1700c1c0b51a50101c1c08010440480401034013915a840c0e060344a950305003000074114143c807003103c06a580080026107000c007110055070f1141018808a810094029070300390007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 874757787 1250 874756537 874756567
    0x9180b09061602070b030f0a0213031506080304030b0619080106081c17010302060f0c010203040c030203010b01110312130f060f0c02160506030a1e0209030c0f130c05 73
    0x240c00410007821503407a000b144680c0281410358002c08550010408000000f20401542c6e0401e003030f001180d6aa84400302250068040c400103490313405001c0200004200c20341c01c01e0b4148481d003450a0101640d00d800180e12400341d807002408401e11040003072418505480700d01403280000140409203520b6451050031544250000c500c140d110705102d008540300c020301d91000391858680404035515617940c84032106418440203014010110b8000704d0440d1603410346a600f015a00219202d20b4a410445000106440140d000354a0300c07064003071301d5110751400c0390314100000086280209814007a280348000500214003440d084d00d0432000200701040d1759004500a11000c541284040202d00071035075804907020035940052549001251342080e1442241c0781181c60640b2503480d0007101c009008159180000380091030906455800c1903030280c681c602c03080c1c080340c510507004824403801708600701105074030200e04e0302d200d5024610794201603003807180c618003a801c0808500740707201 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 874759037 1250 874757787 874757791
    0x301030305090103050c16110109080f0714030a03021906060902030403030213050108060a0b070c052119030c140c04050903040603141006050f04030f240501030c09180b 74
    0x5040019030044944c2d05000b1107070002184068646055000e0101c0240500718000051403d1603a1903083e846a004180120007440c0180565090041c503c0020741c5884407809000c40c40d620041c2d00044a0a00040385158164150000c060702c181d4a5003451603052002d0301202c02036105c0748081342c0003080d4009035010314400c0c0c40250302ca55a0802c030440001c1941c01007410045000100007456540414620880b10b003c88515520019800c1458043c0100e40045401250001d1000907190b11088403000014040b000d58030804d0840c00030742e906a2116602600180e4050351039804160031034014103801181c0000c607411581d040001c60103454003111404080d4001250030040e07182c05005d4041402c3c26a41401c2023442d202a2210010065000e15001c02c2004501400c5101800702201c0145070421540041c10400e85407120a0a5030341030004072400c503807594a000349159010303160580f98030007005c031412801e24030a10000c100e401e01c82c440e08410281860041009440014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 874760287 1250 874759037 874759043
    0xc030807150b04150b070f02030f0c1008090304090f020702031e010b030319030207140604050607030b0904020312180a0b0703091d06040506010e060309010608010b0d051b01090b030103 81
    0x2800c045154030741800c039040004007601075410b05885041884141101a00703135000170440545845150078140114190000f0080d01445281c2c604103500c0800104903a2403101141c01c03c0d90009020320403503000d00c0640d000251503006010a124144181d002031481610421006050489030340000c0d00d000b01c40030400b1800f8090308140c0d000c500d028000c900d461001607004500d0100581c0365284e80c0540c0014041c10141c1c040b070301404200c404000001d8105e4010221041428141040c5480340e4041d0380d6200440d00d04250000300b401d1801c025441035400401914082410900d0315429a202c142c0f1407a9802aa61640001e9540d0284030b40c0608075801c20151641c100b85401780c0345184a801441541c0b0714040d00074801e06c00043c0e410343c004429600440c81c0d488240043c6e6403440141d900542c842004410020650700c150300100403102504000c0c00340b524102309104001d006098040e0a03070300140f0601142d0010b29454200b006010300d45203038103036130368014000300b504203030021 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 874761537 1250 874760287 874760303
    0xa120c080c0d030f20070f05031303082805030a09080d09080c0d020a150e0118031806091d090309030f07030b06010915030f1d0d1701030503160c030807 67
    0x1503a0704a04510a0710b041c2c18440c800b122a4403880000c0020314045e607400202201d007e8007042042140500079280070951044a940c0310356102d103424441d41d003064407200701c00070610044921612640e445080650580d40352513103162a1500c9004c06000041c100b9141d400b0100700c0350705520030300e200d1101c180340a82c1040d0b445d4404000741c2c50400c10310651100455200507243c80c0421228002e40d400d080340e0120002d41d1500100105025041000740c000a036012542070400307141c0c20081907440e400c01008400c40766500d60000ba43c12a4940c011020102c081118103401640700880b556000b20140c41201c0c2010440c03400246000840020038130560010f5004108000d8002800d58102c102400d10304403280c1082800e162148150541d202019202e4108842c0729109901410f030402018421143c42940c000c0899070f182e24110310240011000003070140c1151a20000d0360507654800c02841c64132000c01901c80d03000288900a40d80080d074040c00200142520009001aa200e00b0390 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 874762787 1250 874761537 874761551
    0x40606150e13060521010902030307030302090310110316021c031d0d021b0f1e1003110406140d02030a15170a02091b04080109020f030a120c080c0d03 66
    0xb0300082d1000a1550803499003000c10038425076582d2100d080640c3d6150f8170444503d034000c8001d074050411200003071b400d800006411000d066243d002070a60350310580403501d8104603003a0382c1e822110184041c0280e14428230114500f20001e1402c460706207032900c11222600300310080e50108800c4030324803a011a40d1317900c2c84420a54091549000c000804020380f10048100d42d0194a403030040e035040e0014203511900c140c40e03580754002211441d00240262040ca034061035031302c42c1e000c4a1100703148100780c40c45048092030712034054071b112000b25820040c2820b10b84642036840c070000031901c450309802881000005040c52002d94854040c07007901254410700c02e54213003a41c05250700200803e40f2000d52069406000082c0c424145505035200c405070380d10030803104c104183d024003065101000003000901c4000540194001c54002c1f1034001092a03d40b04050380c807514660010261340c101d1075801411801785180e021110701070500249442d98002745a03080002982100c070100b9941c01d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 874764037 1250 874762787 874762789
    0x20d050c0f0f011d490e04200403080703030207051f0606090303080714040f081006060509030a03030c120f0c2003180a0312091706011d040606150e 65
    0x70f401d01d0400e006020340084c007080b00651800c0907288822001c5003000c1003250711030708513100c044e0071782070103110030280300c081207900c020140c0d004045040d1250f4101005c44000c142030807907a4807160285402c142c0750a02d5540c85a00c03a4009036015003e1590038040500816024802240030a841030810740031505510346520880d842030b0441020080b1600c42880003a4100d291103400ca201410801114452225400351b50b10480c2c202c00354040c41e900c000143c4c2d0400148000402108030401d1003456250314007216980518010b607030381540200b1404011a000c0d50251410701c14a00d0301d045810408004001510109220108207590f070b00180286a40d000800c0006044034440c111259013a80103540d50300d0040c00c580018801030086000c0c060707036071240071000450b07011005011201201032b02528403169882040b070391804420701c0130030b683c0700856a903041e42e40d0301c40340b0300c110110064a0446280010002c8400680d10307039000c1440e40600442c505c4540030390355502648407041e4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 874765287 1250 874764037 874764071
    0x80a0c0c080303061e150a03091a04050a0f15060f06030b030a02130e07030c140312070812061801270902030a03081f0801090c060f020d050c0f0f01 65
    0x7030700903603003074105005100c080e69990f0701d50303d8092182c0300321401083c1d640001038001d449400c0c2e200183c410000703180005030b426400c41c0c098203000d055005000b04440701c4c1c0204a41341150010825045440c3e0200007a00404050940c1c9000e40c8461241d10b44580700c0710125845078200c8002d01c801d5000402041c3d0789805007008031071042c5d02509441030240c3c0402d104a0b440c100388404242c807090790380308038541000340c200115085203550111035a0f425481c044c0d904100300b124081c1c058510701d20705660b6034208546915502140882c94180804484220b44201030400d56211900c05041c0c6544216040b0f264042c08070a40d0855126071580054405194040a01c6106030b0030701e910180542e0340450f5803268a601810003103065620341c052002c440baa4101001c0309080a60804a0450b005512103c1010700c624645180c070f945911098606c00505540307900140d100d0b0088500c018441d0000e80290701c0c00c0800c9030792040e00043c40600f880c92550030310351169900e500a0030305003049 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 874766537 1250 874765287 874765289
    0x10022818080a0312110702060706050a05180304060e041118030d11150c092725030b0a0b04091428090c090c050304030f2f0307080a0c0c 60
    0x140200125089583c02800c41402e001040c410b0b1941d94000800d00c034005012250000e6005000c0e41c2d139810700c1d141c06001070800b40c81700c4008031715000c006003110455140c40130302c0c080102c000354201450105d088440c4035084001907003003030f1181120109a0014805462001e100c0c1d03500701c5260324000b05040c6007a03170603450401041408008a040441c010410b07001c2c244c680c2010382042c1d5a0341083e500b8602ca00c9111075000039040c4104080001d580404400605201c1d20007180d50315621a00c80348008030254900c00e201c100b9015004060296204071141d00e8050b1009007400d03503a40300c040b01500b042c2d01580c503403500e904214100418045645030b001012169191440030410030a03401240c0320324880000d0780c0c0e0782641034240402c03041a440205441141403106007001140207002c0d4205480880100c1d034010b8110a03007034001c12180b004441072501c0241e40c2040300000540800b031107442041c0c240002c000d58400700e850300c3e006207521212900d800f80c002000d4a0850015449 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 874767787 1250 874766537 874766549
    0xe010506010810060e0f0a0b0a080705090604050d11061b10020a09050603041a04030e0f010804020f060a092d080c01080f0402120a1212050910022818 66
    0x302c0b0208100c0000201d0b5200c1501d070b592501c0e008100000000c60f5621184184c1a0360004145000196a1807032100900381d02c40d1a07524506561513016054400f0b00444c117181d5449842400107100e64200360040c04601c5000f550b0401c61300b4141c0001c50019440081c08682d002c00e520a200c46c01413041006900c2c03440c080784110301e403c10002c0c00070302507281400303100d104800000204060001c01030400180901034962180f2604003450301a03c1b00c10700001e0300740112080c0700004000c1d80184030315486141c000d05045080c0100300200500d80d40a17903c000d0070705c080324202280351000c480c400040c0c0800c00d40d003900c00e000f4880211415600310f92081000341d101030041441a64404080754101e80c201010b4003040e00c4620005507071040b102ca01034843d1260304074a05c00c0c01040e02e601e0413240996103420000c5110b140e010342c00d03103800310b803d20340e1607108210034480c0808650003001c1115181000902c86521141410350780003102d801800021a00c1c588440c403d0310721241c5100a01c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 874769037 1250 874767787 874767797
    0x5190b221d06010305060a0c200303070305010e0f01031e08070b1519060f05040305010e060114030a02090c16020a0f06090b1611060d090b090c010801031703091509010e01050601 78
    0x807441c0c1e45c0e1940c0d41c10052860122644520f07a2680143c0202a407181481c003039052015520064001d85070349800c100e4014000a081400024048258582480c05007206020605260703003141c941d5021800030050294a44180300503040c0410503001c050403905200300c078005070b503007060300c3c2a075800412620103a1141d80220b0701e1441058851b40ca030802c460043c20005e03182011013400f600c550041e076001074015420a05120801c1c00040f48190603198100c60180c00d280c620800d06076648604080290404031001c04140400d040384044e058030602800c69500c0c810b80390317012510700a819801049944490030060145540142d85030000c0c06e6018040e5003802c144c0c83c842d0306462440a0003400d6902c151f86858035070b45660040300c01c0504d5201003404402c0c422b141c00f8110300c0703080300c000748140500f03401d0b01220743c440e444da54103da40100300c0d232000e890b000305200305a40c0041e1a14099200c0d0300d080011080da20143c00f41705a00c07e900000b0110914045c06094440080071301e41001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 874770287 1250 874769037 874769039
    0x80318040b0901060c0302030f0d0e07090c121512050706030e03120c0307020a0803010803040503010b040212011a091003140f0c030a0207060b04090c050a060305190b221d0601 77
    0x2c1c507a8015541110501d250082c0b40880600b010703800d501c2031301c55140100000041d42c1c515060f070f54100c0c0514000350003c96100c6550b031140c440850702c100300c120f4006644400f503130f0349038140c5402008040c104042e480208a64a10040030b03640c02c5490112002d401c4004100641600b51181900286444002d185051091521030707844400052a149039000080f001c155042d00c200310310304965070701c11040356032540c460319a03603501e0300b080c82507610941c00c0920820326402d2500a4458414202c48402416420b142d003441090841d814250817180b014068000569200400d00c0555000d98500041c00120554199100f140040000661300d9075903090041d00d41c004800c899100e0003a01c801a15032083e0b18250000d0410006203c0d4060f06102101c4140540c030341c0c2050031501c00700d4141d10742c0c40e9500002c0d0f00703480048810300510b40080482020a00258100181210b070040ca040b0340099200d106ca0034402014044540c55a40c85600d0302c501c2010400703880720740400c00001c2c0815 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 874771537 1250 874770287 874770289
    0x11070e04020d03050a0c020a0905010812040f15020a0f111309031e110a0809211011070516050a0503031e0705150408071a0402060a0f1206080318040b 66
    0x180c01e00e0300000f0100000015010082d41c45041c2e51582c1c00ea00600050300c642e60703800282c000c0c1400780a148541c1c06110302d450720780450b40d0200c408480e030250310b210240745071140c45034a074011046040203500500c1d8200c3d000512844842e120700b4403034950004504640b00a21064000741010007060030314112a26021a410424003e0540c1003400000001e03504904111006641e1002d1462544520060380302000502030181052010a440380a1414824449009060701692164480760410410760790400d149400c107466000c00b02001d14544002ca682d120302e40720811480e220001d0f07250301c0c1408545049500100103100840055041c1154800c4418040c0d643d003014904100e40054002c041010034424814040c581c245000d4151400d810403591542c860300e400c554000540c81d85c0c00045010012240c0aa07070060180360800c14054402e507182071410289806024490201c0080c1074040d01074980a08810809162075401255003001c0703150741c0d103541500c560305152180c421 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 874772787 1250 874771537 874771549
    0xf071212090f060f0605130204080c01020c0d03050c01110409020a0e040c0f080402030c210606090f01050d03020c030f010204090e030f091e09040b01210b0117010e0a0311070e0402 79
    0x781c2c43d000304000900705640014038005013010703800075400900030780a40038028110350160089419030340655142c200050012a00d48400740c841582c40b49200710702501003480f90020b001c4c8954041c0c000904513041480803281c40d001680f28641c550b8000031507082c0f10742d1080107994070034000e84042c840b04402100c00b42110980c11000020010440002003c1d9941001205401d1802514100208040610310020400640044003040c840c150100f469820b001d4416072050582d41c1c0303104007507420a001c00c925a0030001d41541140724507506249159400d218000c180b00f0040001a965444c0c507054100f61850980002c42c650024440c2d00c40d418055011681d0440701180c003d881e05024a042d406080740628000e40c01441d1003040204108c5c10284942c16280103a094035554006106070101e09030001e4001404803c45800400104061501094803840804004540341500c681181e00d0801c03420420342c00030b14000c44c7c06940040a100e11809040d245880001d03526064000c03c803 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 874774037 1250 874772787 874772813
    0x2120306010f03020d0212040b0c09010c020d02060c070b1c020909011a3013020d021017130c151d0402070b04060c0f030c1e050f07121209 61
    0x410310182040650b50103110758121444c4402151085448400035419911031031001c0b80e0132640b401e50740700801d1210b524581601c0040e601603464112018043d82800b91314a200c0a0883c0c22940c20311000c406000300f4800c1c040940a4040300c0ca4403440300388208055202d41d01d81c50283c0ea031041280140a8480c0c16880341565039111300c28000178504800b0b2907032441035101c4e1541d4032150b990380c000d600004241c240c0c070001c40c2c0c04d4174411039210360b04021024070310500700950102c2480740702c0700141003002004000b20310f00d042c1801c4c4400c017581d000f502c4d4402206e46d03118a18400070284200b0032001e40240203411004005c142c80b12040c1000b8041840e1400e4421a055520031200c046036101c6e0119645c03254000380342c400506191802d9009001c10b800358801044290204102071886403181c0c0124550a036607515209021950000222807003403202e40c1001010000c03000c50910800040c18400d2003594181061403003450020440200d4864050a150500d8299004141c1c0038034552 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 874775287 1250 874774037 874774039
    0x6110307020c04110408122a0d0207060f020c01140c010c180e01030c0b07170a02010b030708062205070306090f050c0f0a0e07210b040f06030507060f030212040b0402030d02120306 79
    0x10354403001d0803040c04d01230390300e51b0040100300301c0c3c9100350107102c4c80400ca058148455408580e031507904c5071001e8516003441001880181d00158030202c1a40c03003001c4055141c1e06e43c1032468a0800d09c03c1d18142034442000140f00421500c40c00190b151000d0350040c002800381255120b21035055540d4510300004520400e804802c010034280e05002d008501c11301c02c2220600c40d5a0741c5d51601d28003a01900480c070403e440703406110320000d000d09c00425810b21030782014a02c0c00b4144480245541210218482510140f24159000c8000b0701c40f80320300c6410500414190510154030710b4010700e400029409507000f404240d4134011f09494900c540307404c1e5243d516501540c1d9844e040300300c81c2102580d95000001b24184603114501c0d4007070348101c5800c07505840500140100c543c0740d20a03a02d15203c020059846084e00b080101d21440d95031050000505d405840c0c60400401d0b040c004609440a4611090766414402189801c014030400d2001600107062944130704524060240401031820b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 874776537 1250 874775287 874775323
    0x1703030c03090106080105010f061805060d020c03040b040308040305070f0e070e0301090b010b03100b070f061e020c0616113c0d0818060105010c06110307020c04110408 74
    0x1c10340c42c0034290000302c0903102c8034000300a150707910313202144012454801c020104000d0407455800c5d20084a01a050f80c0000d803540349090030b0071201200950045605200c180800d20000c9044c050726002000190f0003901e142d80c60780d080d4203059040007119402098010740200c4100101c00c00e40042c1a80f00340c940c00c010001c505c00c00c010a01600650b080200b40081400002c03405074580d20145005218801200007182d80f80c8002d20038030b03c0351050241508009406c001e0015580380c104d04d605025582c0280010b0404d280103c069070800d00005200f50080000c00400e00100d141800540c0b82c3c910300792841d041d2090105481380c10251108400c1c0c5505d110b401d0700d00d048491500389200030702c880c0c4988001d002d1a030546404120032090300090302c51020031031030112642c000301ea5039962030140030326034a0b2400540c2e062841d102d0480340b594480000c4a2042d2080c2c0140d803091074190081c20184003e2000c05c02100c4480d000003801d008c0c14041444214000590084010102550 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 874777787 1250 874776537 874776541
    0x120f10050f0a0905181e07050603340201060f08030f0309151e0610050304110f03030c060103290a052a090f010810140f040e07031406010b030a091103070f030c1703030c03 75
    0x20008204080c513070bd0700c0c07555071450a0440c501005062000c03401d0b426500811505403114680a14941948500c9031030394014480c4900145405c80150b070015461000c940f0800d440d000c8042d2881011511703114907500303030310a140302c140f200c0c3c03407207a44900101e44165240345140c034003600d2800007030000740002e00e80d10001c44150301c0f18035490311800402030403603441d01440101c890344c80c1c0c000d0100300d954000043c0c1c0c46500c0d084075020700c0d030400da40d44081c40300c0c1d47d1034a0040c0c0003043d0003070a118a80800c110084103180000c0c4410009074010701410340d852468906110300642034a100f07070b041200d12400c001008002004078000d44901040424031380402400186c01640124a92540306292451303187c0740c40f10000d5010110b0b0b103d0004907404255841031a0380300e40782442117007000c050070000252203100a51010740b034607219180004409041002107454640f1640151a81000501c001c2c414005058600b1004100c482b42e2060412481d1a1080d10b80c04060720302c180c00382c00800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 874779037 1250 874777787 874777801
    0x1203010b0d0f0906060b0912030721260f1807050f0a030c1d0c0a0504091116060c030e03071205070309120602120f10050f0a0905181e07050603 63
    0x3000c0710268004c2c005100903510b030041c6030410750041c0b0985100da100305929984c1c00801006451526420805028001091900c0d4050107001071400031700b046040403400140c3c4071b80700c0c1b8044844203160b45d0388181d4a0880e41400d66041d0240601c00407030542403407e00580c8000480030141c8506035000e400710303071051000c24400281500010300c503180549010520340440c20303400d000e4410794007a10381540c64842542c0c01603c140d401d02d8001030002c10061250503a16048504807038240680c09103446840300006220040000d8103c8140d510360008170f16030b6903d8080c420301481494040c5180051664942e2500f01c0300b50200f03c180400491500d003414001c0c81c0c1030000b0600c0e00141420880a850450b00070351210041c00a407100c29004505443d1480803070b01c4c41040f410b030403410042e083c0401c01c258848100002c640c48100180c001c074800300c5038050030340201400c3c2039503000c40e100c402000e0304011442010b010900440c0e100001c0706440006c90344220340e800d03540160389840f403072 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 874780287 1250 874779037 874779041
    0x807110d11161d0c0f091e04021303060e0f0a110a180f050c0405030d030e0f030d140c031618091107020111060c04380c1203010b0d0f 59
    0x20301000054180740000040942c0120040f20008101c0401030400341d4506414a0302c80c051540d4030008544c091050458600b40001600e0040c8005100307404540e880a0019040e81d11111283e003500094107010410005a802624400340c000301c05403449102c40403d01d0f81d00c1014040103414101c0c0c0c54103003d0207494040c919406807102c80610781400382d81ca640e4502915580c00b140c4c65140c5488009070001c0254070a0710b00707a91008000c1d1034640d03220b003012400b070940d110405e00c00b030140203403110740e010041008180d0f8411100000c6901410485008000603008104c4171b1840c50030820000e00d2070002d0240f8529244034180316002445610031400030080076008820b00d2850700004c240300c2c455141c0644601403003640c494a40074509200c0e5a00c5c2c540640700254100020710050150082194a00030010602100c40e4071081c0c2a0340d0381044054008840c1850f45800141c0c00d400e4101400000b080000701022203256525048080146100e180a4140c41d00e40d10741d51004440d82c59 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 874781537 1250 874780287 874780303
    0x605250609020a0b13050409120c03032c0f03070b060114040305101a0a05010206130f17120f0f010302130e0f030301090f060302060304020405041a07020c010807110d11 74
    0x250681014548804d6450310540c00080070ba143c034154030382e0018403440c16000e00b282c0309611482104c801030711043c09403001d0340000c10442c24941c5421910b0cc00c9001a1001d010590018000d1003405994031101801e00390299030101860304200012408642c9000d58281c202c0301c20718000041c25140708074a0b0050150740c100414070b0007110080032010240740c1180086266014140410104170b404203c03080c8007511a450150b0000000141c01e000f20780001511103008004070601608595211382103500c8100340351003444808103c120b40c500c961030490713500c021002580720302800d06000300b000010051100900c14103204d4864440d60159800c82522020b4110481d04106085054961039800c00d0040d03402c42885c00111055204490064200b229005481d035882c41d181ea8083c000600401481514201800c2502d1007540c00c0c00010248901c1007580540070300400500010014031001d0012800c110200e000d50344941d10105003041d8040701400d20008000802041074181005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 874782787 1250 874781537 874781539
    0x91005070f080a1d0d150609020f03100f03151d160302011206350a0303090b060f100309020f030a0809101103030c07020a03060f09020901060525060902 67
    0x9401c40302400c101a00c00030701003070040303920f494284603012540142401952030300729500c041c440c04c075480414035034141c00094040b0f1000c00f19080c0d403101040b906981c0304150552403903400104110a501005d420b58015080143c2c92914061030740e201c0d0f51260390320303059103110b003692011000000b101380c2000b82040841041a51801c16030700d40070580e032009602c02a4081042d002119000101a106407400e848100780c1018a00080441c442c554088102c121440500700c0480c0440e40b010030814091a42c0c0300e942c0120354108903141114a100d1301401641c0076150500303040c1d90f259582d0384401c0f0500201e150024010f001400090203500600f00a00e0b01409060248010300049000405000300c081c1c3c2ca410703c0c0c900a080131900d04110050300a0305420510120740400f076808024100759000404e50518580c4989400003107600010303109203a26071312100300045085c101100c500510280c2015401c010008004100559042119011400003001958104260356100c412043c0d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 874784037 1250 874782787 874782803
    0xa020a021309050d0806100e060f1c0c1b0318090203160e0303030717100b0f030106030e07211a0703050702070f031a041e120e1509100507 61
    0x1000380800001e1440c21410b80f060f0042c41903526074180281000346c01013001030040b00c030007501803078102d440700243c9100603484401041074080003640c4102500002d642c4841c4030056684095581045540c8d400e2900f0502c04a0700d11920704a080607004d20150340c00d420005d02c07c2d6507000321380341c2484190300018a540c1c030110070720001c4e0a2400c21000013803110344450030b0b220f40b4030040603900c0c0411540d2a0014003200c3d240e154040c80c0102c001d8005841d002844016521285181041c5d08410440303c0c809502000401402c0e40c18050040d20b0740c260b0000d4420a1304080c1c0c0034621080c41c0640c041c01d828071240d60420420b10034200e032041d0415044070160f90070460801409000244c80050041c031414402103103500c003180c0c520044a03441302940088032090f608500311302400074410395005400303840480c01c001c82c81c20b04944051007159140c030401c0c1071007805854542202e203c0c0e4002c2c41d1002a446075042e00c0000c035440e60340105c5621300962002c031800c8816226548000b40850 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 874785287 1250 874784037 874784059
    0x40911030706091212020f0a11010905060306090402041e0e0c011e0215070e030f070501030e0706021005040c08063d180e030d02070606060c150c03061502100e03031b0a020a02 77
    0x214012444d50311509c8245d91701e00c00303155039400f00041030006031a40c0e941302084c240401d00514196102240c039050a00320201e1440804000b070045960042005116030003150100c10716607442003411404100c85100e0300d40013a40d02034000d44e00c401c09416844034040d0000800c0c02503002b0102a1401c1c10001e08a0f88070101c0301c1182621000e25100720380c04030741400d003241c0702c4803400f0584a040d20011b90080066010b00c581b004083c1501038070036225903c0d5840046600301041c4085481600241f20309a108254918111000c40032020311a000030400060507140080c03490620085491381c11182e0114070400711078000921909030501c07114800081e001900802035000b0308541742c0240c001308601661120240c850341511072000300320b0410368507034030b4041e0300365441410982d503245000505692035840f4914051912305485015900c242d41511908569004012000d05079202460460501c1c803480020300a410b07411840441000c02c00b40c1165108001c2c441e15103800404580d988 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 874786537 1250 874785287 874785293
    0xf07230406090e070201060b030408030601120603060218040b15071a090f0c03030a0e04240b07021207030c0b07080915190c0804050d11040911030706091212020f0a 72
    0x403440380c4514843c28048000154541d401031150350229500000a0751465441e075588022a80c402080503040c85070400e405242c0480c81d02c80d81001c0c43c0300da04010b030785142d55048148400700d5019400d01c12400c0001d07089050300c80c4c170603d250840114442e00d444a81500c0c2c4000f420702c2c0115240351103400001082281000000e44440d03011828041d03c50340200c040500d6164490b0b140b41d1f1011513200c61001c04182441e500101800c414841a662940e0f48040c41c1d4101003025404401c104101107405425403400031504125400d110009000ea00d1655072541640c49451003190011200030070303402c0910002034122104104002c090107081c1204544581c21030300194001ca192101071964402082c1c020064030b0390194000c241c05060504d010300704002c181403418100c807035245912401c40c0989541c000c00c040c8910450000340903c904409061901c41c19500100802c81e800c042007141c00b145a140803423103604405c100003c3d18088000340e00d4081c500c02803903941d20800b091072042c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 874787787 1250 874786537 874786547
    0xe030c0310060302280e0612010509030a110c13020a0512040b0103060c020102030f01030206160203030324100c03030c110a1a090f19030e0d06020a170f07230406 71
    0xf42c0b842295003203902440e980d2440211441081c0218800d5040502408800c406441150b480703000100314240c213039100c1210500795401034400581551020600b03030ba1050300160501941d0020400510741c2d11511400154481c045118400c2c0340340d40010174440f40341c0729078110b41ca14021244940014100751809004a100034401540c0c014a00020a4640303881070003124054200c408480125034216001c003c070075444101d5000f24000c1c030101a800503202440914031864114000c0035002d10041041c615908000c400d02c1d114011600c581c64850390055030006403507404bc0781c0060703180104142554410f03070301041907030540b24558030b444c1040113032040060a41000c804441c0a510f072040c00551382e420450507040316410540012000005404d904503a09001c4e2a00080c400c142c0c001040104038250003d8800580003e00500f40680003d18840c4274100c1d00521103c40c58280d06000c4c1200c400340c101c0b0104800305600d0070045d48021000840c40c404444501d581d196901c1c80580 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 874789037 1250 874787787 874787789
    0xa0b0a020f2b0b09040212100e011d01060303050d021e07060504060b09010f06080423030706050f0717040614090a02093603040b0d060e06041a010e030c031006 70
    0x110058055031142c03050103650051507200c40014051001a407246d0b82084000e10400ea24101588a98054a414038800d4001d0b285002c103001c00006826032880c0117040b81c2e0549800f0304505a040440401c002036020084800d16500300400585940031103400d1384901150911030982090040350450910000754031280c0261310414040140349910303814030003403d209200310120640d01450400590340a07000c0b00d0360142c400c0181c01c1c1c1240100142001040e400c0c0f180ca182680045024401c0100501c81c01d50080d0720314403003420500c0c02c800001c1008910602e217486040315400030500b0004c0e10780007181545034540000a00f440c0c184c108d1030759400031080a9100792009004035200c0c120300d480001d04d600c0020805201d107408440c00c501c2c1c0d0008401484003900c0204000900e4602510140280d1154072034041030542c07070803810700e00c0d0f1900502458402e507e054a040b68901e0640f1070f500300c2550030b0800362664080000024101400401c05a0f094091803140e07400c4c00e03000f07a1040d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 874790287 1250 874789037 874789087
    0x5060705060f090f0706031e2703020708010c020c01020607031406011b0203070303081906030b07051e07050102030109110a020d08070c0609062a0e0904020d05160e0a0b030a0b0a020f 80
    0x200e042550005000698a49d90390b801c51071075400c264404030107070030300c40d140003940240110b920456645420340c1c00c480c0340d1007000300182c00c100c00640c00c0350b03814070100e42c01029528090290b0807142511521220010b01401d06002030080140040d004d1164400b6949030018107944009941c0d08020301020700807240ca202d000001c42e102c100d420b0a610401c005c1d40d07040101d0382e505580780007041d2855408851103804441503448000c0600d6203042c010130410344684000350f10b9514003030000f4181d6032031300c03007440c2d10308010b00c882d05225a000483e0701c41020b9a240200c600e442c1e129042c2d07503d03c0381450280503181084951010300115801c62000c030310085d03c400011659528001c2c418170780c8a816200020800890b51065140a80c00f50740c025000812410900382e440d070b540391030700404240313400005464a408010941541480960103004c5150902503020b811001a480e11407828004103121411000702c0c580c41440e5042c1e44004104800036035a6030f0048800c0d050507114500d40d2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 874791537 1250 874790287 874790321
    0x3031b150c030f0b06040b09040b03070b0705010903020c04140f1909060615080c040905070203040b031f050108060a0918050706120c030204120201050714070909030905060705060f090f070603 84
    0x4000103017003000c121012551020010390a1250000c1004050803002c8085541480b070311034046540701d400c00007000403521810002491b849a4500039050091800050780702e0b0303240203010310602c001906090703031009507031a84c07585960310094440c003403028034000450250320b001c1c20941007007015400942520014901d416666102e035000312001c2d00202c0d02c249008030180420005c040d400d0f0021904007030207005886c2400d0312010103c4e855002114640380000c40c565101030310907096074010020b00403c0ca03125090380f0349503000c00d0b42424a441054907845d65805a140e005401d1062080d81c80d0307120094420f00341d0b40c0d1100800120041007040600d0b03107405c0003140f050303020f031007114116147c980c0c0a02e60940a40c0066666030000c400070b446580300c4020031182c010060003000040c09103e0400600340070181801041c01040f900414020b8104002000c040b42d400141141c0c0704201000040c0c00395140d0405030300b480201c0350140795510802c4400306019400d03411441014100f9444 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 874792787 1250 874791537 874791551
    0x402041407210506030a12270914150f030c060a0201020c0622020603191506020d0809030417070f0311090a020915090a030209010305010c0809060103031b150c030f 72
    0x102c01c04540056450940c141c0c4860940800076105818040c010480ca00306001c075242c2c185600445422580022000702d11f0550040c015007031706200d0303415401640f280c0c45465103030814a1113011000040014455039030095883d92036503003004503084202c8050b007032a8440a10100280c080d40240c0700d120824000c000001e503881c6001a65000e12280c41c68140209400503024845694006000c01d80030aa44c0c90b0030f0320601290740038030440c0245c0365013a408424503100009040450b10300c442c0e01009914414050600b60000540d07050b611452440142e41a25102403440e0840d03d1348400000314a0314400418080148482043c4032821313508034540d0703a29600603404034421141e0f22580103104070304481c1d0490b070303030740144c542c90401401d01c42e13049881c2d40006072100000d80c0110741d143c0d100c649000c29103502a4803103030030505040c0140469415a603016004562100c1d401d200c05090108090074404000142c1d00c854808001c1041048a07110005020701800ca6000360f00c0c505201d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 874794037 1250 874792787 874792847
    0xb132408150a0c03020d0c0e040e0307020a09050601110f0a0605062d03030d06090b0310090c0b09040b10020604050606030f1b03030d020a0504062309090402041407 72
    0x1000300c0d0001c80d44250110955803248400d00425000d86080d041503800d018941c0e511000e407082c010100c501c0d480c0e402a041c0c8c000704000580c0d01c4001030b21040e070418005100140c4403812488265500021701207801d0b0b40c1c07500126000480d1454420350380c800c0d03c6816121280200300700300094003a01c4140600d6959006011243e8815030341d80844141d80c0291900f2001c0c050500d98842d1402810340740f8000440c0c000c0d40030356000e41c0252146a690b50f0346462a4541000b605215815070042130082010944900d07401c1e03130a07803041056510f03001038550026521a440456034100081842441c8000c43e03000950b5500112021a1144594030100303446140c005943e072a45420308004104040725602c0d110800e140000031690548401d05c500058100e15002070b0420040760794030b060701c030b601d40840103004101400804003845810084010003056010071103010b000c040d50001000e480c4e500c00318005002503800d5a0422208800303001d082584903140005030110304428003101c0e075000c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 874795287 1250 874794037 874794043
    0x203030112030c0c03140d0e0a120b0a021e040501030e0f100b0f040914100e0601150e0d0b1503011401060818070603061a0307020c01030b132408 64
    0x1c02080640c40d040456007001a02c1040d50300a1580300b00c42d140045a5280c0e1240c3d00362117081105a02500715003a1141c481d5803080000c1952141140e403c03a58528040c80b01456901c0080003501c80201100021401a040d404699409092807529040d60801c21408120743d0072030700580d40040d00780000d00c010640006001c5010008410240c0801420985800300410041c0120780c1c0210103840b6551143d590740c441c46000d24001c0303290001880c0d0a0a1050401c078100c0c0194240c04c1c9880d0660012010001300f01d4151082e8200c2a00000c4070313030200340c03400303d207000b07640f603200c510601e002c0200184250100d018a0041504603401001101003500381e030070108a01d015080c52600402909210b882c002d908801404504040346800f03000c054100643e5400040100380c483c03204124201200c000700d110820106201421810000c60080d01c0b4499065481d04044d2501c469000031740e181420203107030f1183c100041204012000240c40d4510950210b00e84100c100180011104404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 874796537 1250 874795287 874795289
    0x10504020901050f0d08131410210f02130f090e0a080a1103070b06090a0e03180a0801060602060114030604030f08090304030210111612060b1302220602030301 70
    0x401d000314581c2001c0600555001c40d98156511150701c80512001c910004018000c01c0b036501181c07101142445007040500300b1501a00e030283d0854640c0b01c0074250310101150190901c00c440710b006816203000100a40810120b00074400c1c400120311010030041d96101084581680d4903544c11540c40d41c188044610380c00d030140d582d401031038098001904000040450030f145007001d100e030240680419241d9040480c04480750380a01e0107108403481c0980c1100d41c00803001200f0b00654503120050b585901070046521060b40747c2800044050380c0300003a0b038000e0100301000b00904c66071003000964445d028030400c1a01c0c00000c0039401642408501d01e481207030141c84201200c1d5400d10704070351034180123180b01040e02083c007001c801039071800d00444580b0020750710a238103407a02040d414100600a00d90b520552643e450130050703241c440e42d4140005400100c0010518885004140e12420040407000101e1001500c1c501140c00007010481858030f04010306425a120705051f41e07a4442 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 874797787 1250 874796537 874796539
    0x3030509060105061b03220905060f0a05040b180c18100f05032802030106020f0a0309060c0503040e0c07050d0c0c0e061906120c0e0604030825120806010201050402 72
    0x1c0050885c07690603103500003140e0002d41c01301c80c600620100403101003030358080c4400a45982c0482080541410300609030014000c584d101c07a11080d80d8002a0b00701c0561090386d00031030b00c03602e1050050356103d441c0d1400c03540d00d100d141160302e09601818030a500c41c009890b400c04001040e21000d06105100521109168a9070400c480e08400141c2d10b030703000213210301102181410001c1515039020420004a03501d01d00141e10f80d4108240a420701c3d02c10300310700d125680144e1190000c03951000c551030841d00c0314204ec0000c101542072007400e41c8555000042850104401d1240554121000308029030082d0306461000001c040104e444601c8020050f20600c821801446602003056000f50404c400400561031400041c0c0d05484c090b42c3d917840440454010ba4941407641818001d11100d101d051030300800d03130441c4e100051594022800702900201002c901d00781007544600404055040c2c04103041c000314241c2c40c2000c0041c0c0200d0000e03001903e01c1c00070441c1940140107050040c2c0e8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 874799037 1250 874797787 874797799
    0xe060906090d09081225150f050402090a0f0209190608070203070309150306030f20030a05060a02030709080f0d0207170d0f0203090a031a010501020a0215220e0403030509060105 78
    0x10200030360160b181c101e40e01c59090041e0440340e554946401c0451b10380d41d98424108068818030005588084070550103d0ba01258184010031005075038401046078411000840042c61201621050009005200205030003c04002018a06008030100c103021540c1c85c0d921158541d0740e0510490712800380d6000100031800369801070103100e0701e4181c00c0020051074a00018036a568ad22070022031036116100343c0b101d107a0044c010212024000d9020101403040e0020082411141e88080c0d0702d540081c4800049079000c808079000300e20070602e42c401000c0c2c0d08101e5140000a0000a480e2541d00c2c5140c400752040c140000740a002c03101140340d0345204800500100707800d0303480030b03600c01c02e18121030000c600007000111515a180240c1001035800340c020b0100148080291281441d0180c200174103540c012003100740140c0c0d41a0000103c100d070101d610792030b50181c1c9806c1003500000040d0308e03a52680d40c180442c0700307200d00b860980304a00170340d414040b035200c9240c400c0d04c809003030003040c0e0020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 874800287 1250 874799037 874799053
    0x10b0d0f170f040308030619060207030b0c07020909030d0b040b010c0308090a06021306020111030103080405120a0b040b0f0f071e120504030306170c060412060e060906090d0908 78
    0x78aa20201c511000c0c012148a16144040c000580c090f40160001c0b5905840402408094207241c41444103150041780b010018608110780655101d2075440004c1041c80c0002c001030b0908281c005032a9041e902a006d0a42c41c140f02e013509859400003800c1c0c1503d0391400300d5090840c600303401054652101070b102c044030b030011602c044414060087c00318616110349113542c0300080307440c4010068070381400450403000e420302c9002400d59119100c5410119001d000600c04100396404680440b003003280c0f800d41d09500c0350b48150a0415149010300354402c8102000305000d0719002c031620030340c40740d030038180313a50385d041070b8000554403d80302100091654044141c4031001000b801c18491043d040405000307442d00d900340700380c8108580c00c800003504e4500410034802c1446514601418980207401e0013404c000100ba0140240e01c41e950690641089140a000450740301070004454402521000e01d450009540e03200c00c19034000b00c2c0d91083e20311172800c452156041c081658113080280c002d075 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 874801537 1250 874800287 874800293
    0x2120705090f0a03030338190f030302010501061715010e041811180c031b09031009020901081504080307180e07080c0c0d08102105010b0d0f 62
    0x10703800401095400c0088055034035000da40303040080c40150f100e540c0c0400d001e0b50f081010090301401507035881d2040d0000d4400e60610720a03024461001e201a03171112401101540300c1d8554481a901070351010f80000070200c1403541c19040a8181c1e082515140442c14203043c81c0035901d041152000207002e8805421042c80d0700c55010004083c40080004c07030000c180310342207020b41c041c81500b01e880541d407546005803418104040e00c6a203002e080b01c15900d1404601400e0b02d48001401c0000c2821240d0f02e021702102d007030094800203007000d01229400e0340c42652440c02010601c8081c0d100e069480300002d24144005148100741c00c80700310b003011a4031540d581502680014001c001400171600d44400c0c45503588407204002c1040003068812800d0a41c00500b00002c042c22030220764000300300020604000185100c0e299106180c0316107584c2c0c0382020844000100e8105680e040380d401c1c078a00d4000c4007408520500790290f002004030808440030004a141d542e81d0040100300004044004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 874802787 1250 874801537 874801547
    0x23062205061306060914150405040b150103060914100801020a0f0513080f15010504063605071124010b13030503070c0314060108101505060c0606090703021207 70
    0x1d40b40c42007901040050b01d6001c010140c41c401c403c2d00f1200304680d020403075508060b80d002031100c3d105850070003950a00381c07185504984000c0c00d80c1c10000c7c6d5280030006603407284d03201400414030703848200b103441500d6521104002041e107891421144160020400d52018400c0340da00c268645c071444089404c03c40142c0e6250480e03040c0190b003440c40b03000000c83c41c02c2807050000c01042d12010700600c8010b070740c03030309501641a0007030344c091498a01c042c801d54890032078204020514410081880229581200c0086c02700b1000212145c1031005001c010394000541d03090807610310040c1d810000041e01034035034004220142507030402c1e109004210a40c9660700501b2100f8a901003032500e95140d032070300c5203194820700c02128100611b9a0400500019000d00c00060241001910041d494007081d04d540b6000800a6514070791341350000404500c805941500405014018584410401c508030f902c0b1001210014005c009009c0018041c42c4a8402c03190507000c0e0000510fa0350b00c0e0a082210 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 874804037 1250 874802787 874802821
    0x90115050d21080f0c09060403082808192c0709050718060f020615040905070801051b0309070e1506070f021c020108132306220506 58
    0x2d40000901c1c03404014620311800c021084415403980c01090500f02c0303801808010040400c030b5084810b000062895840347c089130200c90b0042e01481e102c480c011841048818100594000c450400c04102a101c3d08402540e1203203440c60451001b00343c1808590003034036a00241101b40e40d049145000c46961010795000611540a0480b040551100d148800b120b1040d100c0700e0224500c9031940f1080120043d1700d401820740713898801c124020310600699280d50103000705031031002e001c038140d08603210f45c0d2004103655003040c11500b03a16901c2050700d000b040c00303030744e5108415110540c11140b1403240c011a800b40700c0c42c078000e010341440c2000740030341050301418203154403403211100c04040c0d44d400c016000007070080030419501d040074410006134980c110f90915403005040300e00b4001d83c2c4c00c07007809503000ca8030407504921038489181807203000314400030710290200d800850401c02c2400080d0316100d0020400b10000c5152041d40034282010100c400070301a44c041c4001840705810700c51004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 874805287 1250 874804037 874804043
    0x90c0304140601060305090c0d1a04060e01020f0711010e0a03030804170a0f0f180b0705030f1303111917070b0a11070f1a030c2a06090115050d 63
    0x40c1d055012055500b442c0c82a4003020001e520784040c84460300d41440140c1d507090007200c107140380904d10f64170149842103900d00e02040301c07070000c001800c0c4a0a500100613541112000315038403040d246280c8029040054151080d0721418100111540651308082041100030038042c8120b10f0b55030121200c0340002c0c41201c09068800e11085841e0703110024044940440d142d420b8000e101c1c40d070003410307400040e101ea030030045048642e42d6982d2001c049002903c00300d42515554404608040386148a511118044104006001c0e000f00c150800c6403000c4c3c9100304c0044401052080421000d40c4020504000031506400c003000194a484100c0701202d0005013501d003011350b22900300b42240c1148400300c002c68030058414081c510140801005000d00d0844083c005080c0525030250011901091264100000c0070600d10307503000050b84d90941e101e540140782805185190b00d0759546c45440250786205400108000c2481805982000000d051380c0072515480c04081244500321a5801d0b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 874806537 1250 874805287 874805303
    0xc05030f311e09060e01060f140d020c0f06040b0612011a040c112508010905031602010c0b0109023403030506060705010911030c010203071208060105250605060609090c0304 76
    0x70f661681c1c1d0051600410500c846403005614040000d4035000b907000d039140800c803180c0c00300d40b002c1b03000070281c803c1c804031020010388850703000124515110040240042900c1804100402c1000038078801c1e201d5441034a6000c0f5010b060711459080e01c6c00703500144100e404240030f00d1240c0c2025070181101da80a490b1050704ca03003074074500301e06003140c00714202c1207101080603005481103c4031000b0000c3c1520301c020026248641c0340c0a890b400345506d0304400d51840100b03003056a115060911003550021034481d1a942d54242104c002d611400d01d802916464082c03c02d004010f8400341d280010702e201139000180510358040b4003c28004000650002c410700104d00491424030600c1c035002d118240e40700a07264010b041626091007400030030b045500400c001400910309a1010050700c1060a20040c20340340d910060f074035401160f00145580c00c0101490b014805500c9080f062130f40941401c104544a0308140070092050b01940d07500602005c01043c1c2030f0301050000c541c018066518 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 874807787 1250 874806537 874806539
    0x10050c2104030e0a0501050702060f09060f0a0e0a0e16050c010e0102040528180908070510060605130512030d1d06011508010e04030c05030f311e 64
    0x112144003031025021a4918803254104001c040e0030490b0301440440c110307a880300e03440c07808000a0642c803803203070020b00910010446003c854103003030941c0c0040400400c0280c8030424140c4104150f040200b403000001c25001c0d8603100780c1070012500055030425000642ca40d9281e00c0da00d2500c1c021420b1070001c110381080085021203084c8680802c800840002580c3c1d10b1a0004100310242e42109565800c0c4030710001031607a0038013821010403580c0740b4942e80d084454590f10700c1c1c01070100b80000340180d400090200200703c00801d5551984c0e002480401c00070b501c4005c102e815004c1e00c0c0001c1d45070504140b00b441f961902d020002501410b16007102c0c0340417403d01d4020300350750301c0d41c40502c11107010a921004c89d03c4140b0280340541030f600c0100c0c070301038808840205182010700c02c2e000c5070b8504502103800d044c07140300891049a044801c40c2e50b00d82440c042c1903915400350040403c06403214548004800200070042800d08080000c614a0790801c24000742c001c14800744100c481e080d50308 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 874809037 1250 874807787 874807807
    0xc43030c120605010b090603040308090c0307090609290409080f0f1b1204091e05070e040b0f0d02060a1205040b0411060304030c14030c030c011b1110050c 68
    0x4003140900007030410800310000c68035110050380d8041e0040707600c401091019400f291a90401d9035807098040c40c0c000c140b900c5440500d4144060b5030365180d0940502400800e40900641203c0211442030604100005040b0b161001c2d8503ca060282e20140c8696424003441c074240e0484500640190380443c5040e16180851107590f01c0741c454000c00180204140900c03100340402d050815401c48040c112410160f880c8a845211750700400d00e4807949c50b281d81107042c400444000103000c500408000324141544042c08401095000300d02ca207041a5583d00ca5060a00b03100404003405000c0700061203280d401c10026401c9800c1d010304128046804080a240902800c0d010381e00039288003420341024180141c05900002a00380216010010b0200003507001c94240505a000340e00140d90f00c5030036480c0c5043d4440e10803501c26034803020903807064800065008084d13140c000702d00c003006511580700540703d041c3e440c03d18007126002901050b1440580703410203175000031075483c01480d21030540c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 874810287 1250 874809037 874809053
    0x1501151101180302160e060402070c08030304030e030d0f14220605040e0f040206120402011206080601170d090b070807140d120b0d02040e0c0d03050c4303 68
    0x45480b1480c411803010031018550140202a0f1100300305e10351424042c14034015020760f500250205005a6000401005002d00e820300034000c1d01e0b905080c2d075982e06103030600030300d842d41c0604440e120b0b00441c5032688121b401043c4100303030a80e65444411111b0a003020b450306640154000d14400c5001040c280030b681c05140b4040042d102039101c40782c0344e42c100014110103220040003041068029010703c009a6905401c1e03c400c070288030404041942c4501c0103d40b000070f9140001082c17030070224085080300d00032440c0c0d41602c1e0064800243e10700c90495055688c80d6601c13084020848480741880b210f040d020040034403900540704c640c9814080c1da20600c61080382641445241c00c03203200b0424032a40500323030700c01d001e0403006d06003c00c10b8450002401000d45000083c801d96443c80554a080c10902012a4035600100318502850007402c0c05405a4030401001c07225000790720344c030041c1100300d54007100b000406902c1d0740310100c105a9001070400c0303080580b0a010301e0074030740000000c0001c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 874811537 1250 874810287 874810301
    0xf0c0f020604080d02060108391201020d0f0203130311150408090f0406080705010302130807030c0305061806130503070c0807080106050f0d06051b2107021501151101 73
    0xd80c0080c518101c40100c000d0030060180c0141181d50010f0ba00145060321012700500a000e013450001c802907540d208039083c00c18090001c94001c503243c1c40e0030f035544a041d0f01400703091500103c01d1100305880c41006040b880120f031074040d0000c101e002c0202191203846000c044a076040c0496450f020080300a041400e801c440844940317000040480c0e0b1030424092032041c0c40011361b014013002e410032010a0b161603083c0145810940d010a01d13340581c60300d0848002070071a041955041034880c20902c90300200b80c0001d485500c114004620103c00b0003c01a403107030f81e9140505a0b54941d00b03407900c0c2400c003044042d03609200501450003c500d61000050040451400800c4100d25182c0e19609484072984803d100e40e440344071440e1140c9940290205450303000000281554403101855034107003c181e402c142c945001715412801d07103411000c0c3d044076800104a40c1ca169110082241d07210385009440701e41c0f602c00360040040c4483c40d00702642030300160074500801030440041310308641c42 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 874812787 1250 874811537 874811549
    0x12020706020a03230711160308040305070b120a090305070828020d02061906180605040f0221070e042316090b0a1b06050f06040209010f0c0f020604 65
    0x40042d0a211060700751140104c1c815240aa040c226030224a00c420b411900625810511600303800c104e00c407800c14419030780c0100c04d401100002c103031a4101030400760040e0104483c94465440007007000d10b00f60040d43d0416280340d541c0142a50740c4810480581380c201d004400b030140034000000011400c0c4003410508108000c0e075410b42045482c02d000881e034800e1030340f007503400c200311410348aa4042182e6034400310300a100e81004d03072150004001040389901510051001d07401c01c2400884030b810100450340101c0301800307130a050100340310403445106d008a00181d43e0141045012480032006a40b080d0a410170a03ca400300f84040307400d50b41d845580e080909000070140683e440e414074580d42045a40e4507890000424820150000300180240030312100e02040001d140740c8164a1100031943c1c0d05510003030b665071458940040c001c2078850720240202c181c0080e000307090503c281c814040c070595400c1c803100160b01e81070380c01c000813510554480c01c03c50004005611014020402007030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 874814037 1250 874812787 874812791
    0x10b030702070b0a0203041e0305060c0a030606020d0c060b0f041d1605010e190305010c1121031f08010e1c0305040c0303111606050a14030618040312020706 69
    0x1500c81002070911005070004000c0c02c10500c5000040d50307001041d01c0944500407002c44480703150756008070812616520090192140e00104207142c00080007a20300c1040366103013404200e032109420f07038a0780c0740181d00710300103007405840c140414075980090303100070741c054180c0781711202c4032001c50185d8a41a03880c98a51108950100035100d04001240080c0c4044962020250070100000c000c0200700080601c42d140074010b0f590120840030030400110751103c0204040e042000026000e8209070b02c0310405400b17442001c0655400d80c500d071003076070595000708524554401001a0300300103480b02c4600c1c54803c403503011801901c00d201e00355142203020700a00d460344140b071603a940001a000e4650405062909010005080811017001d8a034103007006116481c2480c0e515141802420241c40d040c01c800303000003103a070f80110041900903141e139941003000c01c041c41d002071140300a644c007030303000840000c5000c2e140d0010158542c12600c2481e120300d00022100c01754040c0c0c2c02607801502c40907 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 874815287 1250 874814037 874814041
    0xb28020a0e150a0f02121602180415180605040b0a05060d05190f02041b0807020102160623070503090c09090604060504050f1608190203030a0e0315010b03 68
    0x1e03040034446000000c212a0300d4105000381d01c0481d118022440054280f0821520740c0c1c607443d00904c840000d159005d02e04c581c40d1100f99024812542c0d800314181d0150090303c84000013030780c61411046c4156000021080c2c10034400c00d1a00081c010503462001c5481031b10300c1100000e4460040138050740c041c00300c0c030715039003403034010f601c00c0b00c1003d00030310301c0740302500701d10342c001507010804083c50b05945000350202c010078105852685800d1100942c40740c5405810312415680401e0340c5030385441030b900d00d105540c2d03070b40003030f0308074031454600014548907000450b0008000d07030000d411201c0c0742d13080d05c82200d420020081d01c1c4441a21804c004c030b1408400c00118680411801e14448402c4880e61003600b84200c0c015210b581c0a040a80b4058132440000c09000d0100040010f81b0101c10448290852511244030344d8401c900520f03103d40503041c41c040004104800204030b15400601035460428902010784020003031110b029010302442c0d200544041d10b05100e64024510340e140c640d528 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 874816537 1250 874815287 874815307
    0x1103070602010e24150406150807080a0b15090301060b0307020a060c020303270a021e04060905060130020412050f010501140d0204020c030c0312070f020a0b2802 71
    0x10341441c0c001012558500d140000e55850383e0711303d40201603e01705407010b40d070010128001c0c02294101d551403060f00000c02003c2580401c0c0030340302e045030f030b079440d005901c403e1404400d07500441ea1041d0b0108000c40c030380c10540051002002800303001400002c003603039a20709101a94004888080240c0c004008900c1031052a000b1410001150b1010b94514500340c00d14260051011000507001d0205122036802e0101c1080005509500103014680446c4e00d41200c48040a184a4080c05241007040000c0d589a1740d025160040405844007000881c040d01100c44030401c000c480103054804100803018540f451000708041d10141c060f00108071801d04004c1d01e001007000005591fa85402c004000c08507113200c82e000084411a0070120681341e6000090180c05011401c0e1014080080c8580e044440000145004610300c400c007455603413a10425103a1071034841a000142c1c01418600c00050041070040307a0101140800c00480910313aa1491f0701e000d00d400300030100950000d0030b4000c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 874817787 1250 874816537 874816543
    0x1080f0d0305040c0e040f060504060209011101060b03010e06010c0606030809010f020309130c2f0c03030408030a0315030f0c030302060c280c0f0c06030f05040506131103070602010e 80
    0x1400d180c10240000e04040d0742d12806248035101e50941d1018450100b0104017000190702039880c0c00107802c0c445400c09040c010004d42c4031035213141c08900040444400140d040c054081140c07030100c10281181c0c0384c5600300e400d010b401059181000700040c42c0d0000104984500c10244d07004070b4869848140c407100141c8604c01142c0344000703652003403020685554030b400c1c0040d500005404003243c0d81c0d10544e400e9a840c6601c0b11200c0004c0d40c18000c0700254907071008880b05901142c0121106151408141500e920a5020380c0140303410401104c880d1358000d4100d2210041a900410700d49552903d900e00d400038110000c0303d1281105c1010000e06a0401031b0a4100044a0080303252403603494401d01c04400099101002404041048205902400615103515004040c0800c02c00d02031030700c4800c43d0340901410300440d1408424006502051207503510030ba502c800207003141d03120010408605c42010104031280c0054030708800d485d8a0a22000d0020440340d000070500070200d8500501f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 874819037 1250 874817787 874817803
    0x62107020c15120411040e1b0418500f1902010c050f07060c0b090d080f06030705060c03040f050f0105072a0f1401080603070b0d1401080f 61
    0x4008000f401001046100f0400003600940d0144605402510000219000c0e100c907498010303c0f809684005520548407200071492a041103804100c52005050661090110140c0180031500030740f03031a902000301480c040314115018401060010300c081109005014809030340151340c411407555118410b410400d42c1d1008080d0400350000741e002850000d19100e01403406410094041000300500500340201074100446d581950041c646525000c0c0c8040b60401e0300b210004400d800241d008a004254444800001d030b0b40d2200c02d07200c0707169001e580e0b04091700243d03040c00380400c0000e11b030740c60034010400240c1d104091501e45190054010718170740c403544a0784c0a00d041250012060b80e0100032102543d0f0311600d4402000540002414103c1600031400f400c0c001d84a00444c14146280207078040701c2d20981c266600c60900c030011100c40a040e11401d825500443c418004480c5250140c22102c4c103203000010140300b002d4541100036800c0e0701482c0d094222170041c844100c0b06205910b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 874820143 1106 874819037 874819069
    0xf0405240d0b0a0519080706110606010f17040308090106081f1805060108100c0e10080901091b1419030b06010c0602281805062107020c 60
    0x109801146c010400144240307000028070910601354141e81803a4140540100d0300e03143c0041d582c1070540002c0c101440400680071002000020300c003882180130303a40d403a6160801100c040c0c03c41d4002e821083c0590000c0014000740440c13484000f4004a00c40b400003100c40300001d948031107400000005205020707010000aa903e00060b2286a00c0d00c1d004080003613000c450b0080d81c4070001c0000540d0080c5540100c0d40440303001d0344d0361a9211212100104404e0f01c296203000407031410031b80c00c00e491034000c0d006100ca04c5c000c0c039074030100d0741003980c0c042100c1c0c0010042d400580c1e1580b100404120b81ca9002940d103074030070030080143c560301080a40d111103070020314500d162003152880220031098512820142e201d50040603010300041c00b60300b1030605040c28084550700244140061007030040c2c01d068546c3c2c41e01003a1b44640c0156020309000f0461204021141107600c2040d = true := by decide +kernel

theorem cover : BRFrame.Cov 874640287 874820143 := by
  have h0 := BRFrame.cov_init 874640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 874640287 ≤ n) (h2 : n < 874820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
