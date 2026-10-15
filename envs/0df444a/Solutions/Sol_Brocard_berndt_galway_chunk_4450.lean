-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4450
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:39:28.484312+00:00
-- url     : https://prove2.me/submissions/bb6f130e-4517-425c-b1f1-640c281b36fc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 800179856 ≤ n < 800359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 800181106 1250 800179856 800179907
    0x6180902070c0608010501020f0a170d0f0b1318020f12160807050604150c080c010609020c3d29010f2c03010219090312020606060301090507 62
    0x70b500445558001e07000014040d81c0005a19840042c00c0b0003500e1241e0054074981566903581c22030195001d85444c2840e509020760000c00f04c41c0d105041c05c10560708000f04090441c1401c0010b05030000e802e0f00caa20b864044607612a900540d0103d10240c3d06071511403c10700d00b080003c06910b48042d0643e41842908a10003d00303c0ca0f000c0c980813200ca403011104d00b540c8903020410140181e00910030441452000300303445903c0380e07403c01040c47c0155990303442c001d07802046a0a4030030640054021303d13000600114550010403040681180d1190b58100707a002c0002c92085034440350340b000c000c50002200201c1603000325070003c1c15102c1d04a2218511040d400c3c989030140c03402c87c001d54081040f022904000501800344000000209240c10108007003d1001264205c90046003a400d036600340280b00628407024201b4160102948602c1c5015245241c00062028041c0040085401c044144001c58642c0000c0e2819038103044800302b41a9649101110380b403481c070707403860284003d5052 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 800182356 1250 800181106 800181113
    0x215070b100314061902090d0b07051206060a0c0215040e1305010c0e030304050409050307060626190f061b08091203041a040c0f0e011409060a0618090207 68
    0x5500b141e1050114007501090070200e151500001c0300c54291010102c240208189801da0040000350740080804000f08080d0705c4501d81d00100b1150704010500019428441c5400050b02ca54048001c540492814007224401803050000000003801070301c8400b0a6440080e5000554001e4400301e00a00424a8071030108442d000c004041510954a030103024000e02e441107504c1c54001e50017800540c0740926010074003000307191401c420b5940f40014807000c8005000c1d030084c070004200c46a030540f00e06c01016100e031048078204010702900d9200c0381c000002d80b1013250a032621a501b000044021100d82d003450701c0940a00e08000380c25260980004600e01d810443d014050a0300744110707000c1b08200781034903559100503079003d0041c00d21800c42012b483c1c038071035019500c0751250700c0c10300301903940350b2041d0351101c0f10790045400c0880c050014044c61141c40e01c0303a203009001b01c0c0c0f811060f050400101c1c406410500030f4200f0401e000e1400d4034005102c031102c00c001c0450402c21580c501c0701d0704 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 800183606 1250 800182356 800182381
    0x4030305030c040e04080324030a1209211110020d0503040606171c02010903021c230d050615072d0308010510050f03160306090c080405060601050f070215070b 70
    0x2d45114200c0500030114402c0c4800230a0200d01e1b44015001342404102503c80008822441c040744c0200010401d0104100e1031045513402010300000010800d40c1680c43c0028a07451407a0101d40107085062a070008180d000402203031034034050804030340d00d840720b0604070041c0c0b40076045001603000e49881140d141d07100086d209030541c140d00400c0106014924101d00740c4205001c0600141d0010580c0240220703401090743c0e8502c0c49003019260010400c0000b20001c2c10034055420880c0c003c540000304035000d0080b158810812607038102c1225441d1698442c602230701c039001c0c00d030303c1090001c12010300c48188040c0c1c11400303600c02c0d107510075480c0c40c0c002c00e071440900650b030250041003509101c2c5405101603d140c90070344803c01d030569540ca44007131910501520500c041603150000045c1c1e0003030a210300340c4000416560200c1c00d01c0c060420903d0f104018024604020041054502d03c07034015041e01c4102c5d07811120701c401c01051940a41c02805000006460304810200348125041c109 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 800184856 1250 800183606 800183611
    0x601030b180601030f0606090302090a0e01060e04050f0c150c010902130209120633060d1b02060c18030a0b09010e10090309050108090312040606060e030a050304030305030c040e040803 81
    0x2641d06101040d01c01c8822000e031b6400d40301d4000800c54402d010b00051030a201c0055101c1c0c1c80e10000a43c0300f03007403041031703080d103416903c85509191480b0511041c0001481031111421205004041528034907002c1444000c600104c100c80c0302c008070f81d03040604420b41124000d590020882c02d880018600000e00a44c010400684505001d8840c0d0030f800c0c070017194013485016016540041d4003d5140810070060070503031250402d6000382c41d03148035580e448010b0455148000b5002413501c4040401c46000c0b03007024040000d650154003040328207200300089900c11000710310415160644000130901c1d080d2120b1004200c80d0a00c02080885041503000f00290040b030400c03a100d5001c101500421550304040140002e0103070703034060105500682c14a50050101070842e460009401e1160203440400d9504071171154032400100005540411140e03c4140201d01426440c04c5580d01c590707a9108500c4001c081c0000400000e0f009134400c2c0c00c1e2001040e9841d10041103142074500314906030b204 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 800186106 1250 800184856 800184859
    0x804051c08062b060e030f041410020a022d040f140f0f010e0414031201030c1a03040b07050408070b070303060e060303030a09170406200a0b0f0601030b1806 69
    0x43d500320141c0d20900c4602d10301001440c06031100c103144c0c0b1032101401c00c98440114501c010000c00f00700706034040040000b07155212141c40210020820415003900e556142401c43d8444404000580e07103509180500c460403003070b01180041e11220499110746010110f5a10501e0003003542a100e0341d0f50400418458200090440303595802c000080c0c844065503080d00341c80c00c03c001804500018240c50790131900910820030781400c0c5501503072560b031022030781c9120002e00c24010000c10001d066850041c000354200369540c2c0d070b802e40d1048020f020007000900f2010800020a170518000c10840300a450b40724141c8407240e85940503020300d40c1c880c00003280003d2070010b0008201a40e081c0690044034001e0107035286883c1c0950351005030950541c07d4400713000c00d4200700d01e00d040e6900144028003003501c501182c200004103070b4044220b0128412950780001c0c0c041780006002510031030344003082c0130007005d0580341d00004030b0082000450031500500c000301c4035034a808080a03080d101e200b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 800187356 1250 800186106 800186119
    0x605150904060f0b07110118091d0f0a0b0a09020904080c0d03020a120b0a090e010c1209030807110a06020a080f060f06030c07030e06040b030915010f060804051c0806 73
    0x1e8440f030039500e4003001d02c5506441c40f02408110000b80d40540c0d1001a0141407418121031821400118102d0b881a880144210354407160708540c0c40010004d020603410003000b03048484490240c81e91070303c0200308010a4601100000364410311213034443c0d1070030341d00500030342000c1c070745031403c4910f03580070340305d11000c521071101001103161113402198000034940d03449402400c1f6143d256400742c50350b011051b034440440500860001a10b104510f4400486000412555080321004e02540d01c200d040c841c0f000d007011440d20200e90450240c03900300c0c0b42d503c1c0c90701c18001d201d0100e5003081420003008110500000c1d4484d000303a8042c04250060042c00b0000003d41c48103010440c40100300c14103280c104d10140000f82c0512320304409800102d0090a160441c12880c50015529a1058101241e02007000c0240103001c801000500002c0c501b180c44201d00b94103020584165079a07600c03504042240c1c0d4400030302040014000f62050301000e03c0c001e102d405090710003030030800040364050b00404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 800188606 1250 800187356 800187359
    0xc150a09150c230c0a060b010f03061a07080412050102090f120a230109050f060619090b0f04020a0f080615041707031209051504080607030f060515090406 68
    0x900520920380500ca07141c40750b00d400c1c15020f0514a100e0000000302c1080340c2c080c803101190071000c0c401d00801d03a200b22000038584100341c001400e0300070061440c1c41058a4400c2c188180408090b0741c41d482c0c0510000d40343c48050700d142c803031140d01c030740d8000400301c8402c058108100401500034240d026000c0300d010700c0d01c2e1450014400e02001042e01c0e12280c0c0d000c010040041540301d085400705184501c414298842110390715820b4179020f0408a03216440b00d40d01ea200c00c0e43c280170203500224201c0d0700d941217549290b030b1280325043c240150140c13599144d101c1c6800b075a030031401e26580301001e0b000b503445070b080c104003500391510003130f1000c007284200c0002042807400180300402e5881c00c03900c650419080c01d1241c0001c09403c0003440036403080000200225414250326402c42d5699501c81c0d480c0c0d8140010b00240c2d84a01d4814144080e003071005020454011807602e501c80d0031031800089801446480d2405001290302c0150050040e050b107421040401d801003440075030948040c045d45 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 800189856 1250 800188606 800188643
    0x5010503040206221e0e010801090f0602030903090a12020906041107060902031005090f0f07060e1e15090405060306280207050304062001050106020d050c150a09 71
    0x184001c40c0d00a500c400200510300050070007980c046149000f03c98800320050b02c0700c10000c100038444c0308602d40da0305a03640c01c202072107441c19080d0162003d40001e22124030340741d95015600040c564000c203403c0c0c001c070004482c1002041513501c84c241c020001c0c10300035620301d00d2410118511605a010b01711040000e249c0e4201802502540c8003003203802468210152943c900500d030300801240e00d4010384440c0720854030700340581c5001c1d898034000740c0070780e46991044510f08490b1061500c0548c000180070868290048008001d202090b01e01496468440f03034078292940744955016803142c070445a10a00b601c0c80030140c41500020788040115450303071010103645441c01c4504e2007840440c40440710100c200850940032542c06184003606140e100d903076850458126401c0803000031134880000791181c0202091100d0300d8250002001294140b080003902c0b00066030000741072020004145c040000d01f04100c0d8140c44110040c111941094450074014210326281a142c142102c3d40e068100c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 800191106 1250 800189856 800189867
    0xb090315010303210b090c09190f06080a0f062304060503030703030c050c152d1f0e0c130e10031e0204091110180b25030c05070501 58
    0x1a82e4258644021003135650381101400070440f00c0c1100c0c0140c440c00d007207465441d0068201c1c05010f11100b4240c60f00348540504c102c05c03502000c4d0301c05d40780c03040f1420001e400144640c030301a1070340391500900c595035190300c1402511142031180760041c601000003d00c00500f02c10110150003842203004a032401404000548449028166060b0420860180001d01a5000c00740d00002801c0250800101d40c056909019407141600c00c0d0144e06007c01100c40c103501c6020200320b242c3c100303401b6080205070b0401420b1070000c01402e554002c250013086d6225803051480f0040441400d10102454000e0b410f0100342c100550001448001e601c020500780480e00c0103d01c104610360f070880e011440c54561403068082d518100b424001c02c0080c00b8050784482c058004042d0050f00702d204801030105c20b0002d0b49180607040000c200c401092000d00c400b181c100c41003103640e504030064481c0d103005c1c61072540c0e6411244060300b00810403070a07010103401c448a0340c00540240152810300c1d136503d0040d00c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 800192356 1250 800191106 800191109
    0x60a031401140702010b13020904110d050103031209080d05040c121b0f06121a040606021515100809030c06091b0a0312030f091e150608061602160b09031501 69
    0x140120034020211043e10188d025140c0007400070408505003081010404e03644e07014071100d4402d6070b250401441810b1300442c0e000304042d812002003100c0c1d020f5869440044c002d4141404595441e540890f00384a2588610005840300c811000f81c03a902d03916111600000d00f607401100c20050180016100300d440c03c02c00c040b51002e407254074a050040c0408801007c4071445141400d0b02c00140b0b01c0c01e41c403180306050141c0f5882d00103081c4d40803441d0f2090780c1124010300c1225091110181c0714102e80f1410418900300d8810304041034a80c880c82c01950a41c02a00c0c290702d014840c0c2404c0150760380300040c00511038800444128190421031003440601252400081d28414650032008546803081c0d00401c407c141103e000030b0401520398802d14820400900c8040300424000c41c40240034210140e0548039034030707003001c02855141039a5281c4a01d802040032904074075190448508500a1044540d1050040c03040c40d000d688070324106009400400e0428001d125010000b4043c2082448450 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 800193606 1250 800192356 800192359
    0xc021509060412030f0204030c1404060f090c020f0a1a10080c0105090111010e010f06052d0a0806010b0301150e09160306051e03060702070b030609060a031401140702010b 75
    0x5030707a07503d44a26051007060032060f02015580c80110f81005214405800554851414a000e1a1610210010b24511482120f1055150803020880c208048249104440c0b611901058581141c441641080000c1a1021280c05403e21440c00c100141442400451f0082a900340d59242c8040d5001041100c0c003c40406501010b0210303d198014400b92003800c0051404402c2d83c0c80c1c12500034203581c00c4100e031413140c2c1e45921100d604040785000d000702038070080d44c0401c440160b003207014030000300180c1650040600c0d04144982c9403075907030714000030b0140c0800300d81140d40e5500c2643d407998003d03c2a0160341d4401203480003040c0c46034442d1840c1146c000d2502c56943c68070500c191442c010410075405055a800d00000e05c2c0e19200900550341100d2044c00071191065014941020001413a000c115003041d401071112003000700c10381e0b40191042d145400b195484801083c54800307142c0024000540d65048948103040c150042d4440c06500e00c1301c00f90341d4641210503030aa03401d41e00b200d0b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 800194856 1250 800193606 800193613
    0x3d0b1b070b0a0504091509090605010e060607080403060209180123010e030a110303040f06081f05010801060509030a080309030c011406031e2506020613030903110102120d0c021509 79
    0x1045520655000317460501660395001b0032240d5aa44c03043c044a40c0f0f03040844d003ea803514010004030b038100242c01d078400c1064411030f26100c925a10781000d48114000103044a82c0818080b0f102e1725600c000080c003200b085031142103561540d81ca01130074660303815914100002c4219680665105400000414001500034604450655070b102c0000182240031a01803100f4000000c2507107503d004a401071029448544490030100e514a501e160075180c00c5000c0c800741030040165903803043c04541182c05501d8400c0d16400b1110000f8240000040090500d200100034000d45020100040040c644a1030081245565035401944010411101c10784d0603040b42890b00000c40c0420004420f50b0444d00030b0350741d060341400d100421410075101013148a003201c1401c1c0800d540401000e03802c030b40c2e81241d8041107103041d07030000c00c0181d882c0401440d22200c0030402d0300f9640200100c07508402881d803103585030f07000c2c0d200c0c040c0100032000160006100c0c5002d40581028031220043c050304440307015 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 800196106 1250 800194856 800194859
    0x6060103150b0304020f060d09020f0a0e01061103070f0b0109050f04020a05040f060e010308090a09022703012918090a0609170f03010306053d0b1b070b0a0504 70
    0x100b403a181c2004000366005a82141700f000380350356140c0181114560304000007208410f0740140051925034036a038a0085034504800d1202001000815044502500d4070382d0f01c2d0422401c846040d4021a030f40100400700b000c20744010003643c600b18034181c0b00444400c100030f0fa550009411031070010b1f10040c0d0410b5544400f0711443c203240d0090880d860742e040c0003140041e66040500041c030407d034815194500e010412403098502505928018908020f007907082c8001050307441c50362a0f02c6807850711461324030701c0f031007203a91800e420190003219502a031304d04280514440315070244c080240944909220b0300d00307030000160701401c68042d0340d410b00100318002c01c690750b0b0300c018050050241c5902d000c55529486680c6254005d210001a840000e9120b524506d0210305803000074000952a04c90903032108910f5440050000c0303441002d030030b20407148080050000742101c0c0c5030407030031f06000002040955000d04403402161010000c0844000c01c3e81c8201610f02030085442442c0000d0f008c200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 800197356 1250 800196106 800196119
    0xb18060d050312101a12160c0506010b0912060f060d060e1006241b110a06020a05060a0501350f010b1e0a0b09031e0109050c011b0b100503031b0606010315 68
    0x87c078043d103e420f4244100800f100382c440c3d07490f000d4240c0c0203190103900000e006503942000c03203810f002d101e903140082030749051941c3c041045280080210b40200410034070031040c0b1000d60402240200034409640d80b40190a0700c10002e4691809015107507079110711403001c0300c440c80054070401c010030381e504004810a114014815801008140e0381042d0b40c0c00301360010b5862100590040403290000c000c020b0080c902581006801404005194604801048a00150b1a28101c00e0b007445481101007160440c0002c200641c410300d1007464410903c00203008181540924000801200d4049058070340c1c1c4207000710500400015904900c8801040110340c0301580070b060310786d0000b001d40e40440462034003803203100744082c42322089a440301010010300c1414418118258400c2c40d101070300c0c0d01c0c0d01c501c510115480f00001844003e03400005040640204c150501030440141601d598007440b80e007100c0d001c4030403854a82c480c0104000b007041507020784584001c0201d11016000654900342 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 800198606 1250 800197356 800197381
    0x70c06020f160f120c0302041107030305090303130204020703021c21060b09011803060903030506100c0b07050c0708190c0f051509030a0204060305010f0b18060d050312101a12 77
    0x403000c071007217240c078080880144d51b24045c2c4281c9842010f0560f80314007103410000c081d01d201174803002c1c954200300140000603000802a89103660191005a524801031078103c3c90a140c072140c41e140c42c8031028905d20b441d60300079801d00c0d07005808c195694400004400c503d04441c02072050300d94111003001428015402103e02c0c80c079442c0c00d1849518880d80d641c03203680030b40301840c0e0101d000958070020001186403c0c1c0c070300004040b0034900071200d0441035542207030044010300034074107106000c1494481c1100402600c0302901c0d0240541d0340c41005d46004d0b12850801d00411245407040700400701c1c0d40003d051550f801c4820051a040c410305501d2420340807075201050301c40c3c05004040e06c0c2c1c80580c885000c0c050066104400004091204000c0b0404841d684000544248007803240e00505840615030190800400c43c0c41a10070240c0d4940f4a02d188118240000240501000c114405890100207001c65019107004d003440005e10642040c24402c040e00380c103500046901040d5041c5124 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 800199856 1250 800198606 800198639
    0x10e0d031a1c05100504030f03050609010b030c16120e011803060221070f0e030d050712020a0210030b0301110c2d030409020d060f050a060e0402070c06020f160f 71
    0x4000b0700580c01c000c3d8a4150030700390308441121041e5201c3c1c1c20300040560222412170340c20038600c1c040026092840c0040c0b0120070610443e03404410110200b805c1103526000c4404c0710400e50742080c1007242e9440d1180791004a01d101c3c0021803480796919600c0e5000e0b54400010f51065844000000e0465880070000c1d00040c0c6070761070041c901221030115240c0e03290810701641c010b031900070203166082d200610402d0b407182114045d80010780751102c001d80040c10b441000d94088150280f07001041c00032881c241c40c4400c040d602186c1c2e00c0c0003201d002c0d0140d01c07101c441501034001380300741c00069200050610410b650306407643d02c540074911521301c80c010030419034004080110186070490070a5403070341d00160004075201c0d500241c0c44904410030310840000306450080001300398500350014074085910310400d824008102000403642d40c45504580e051644030340e994121540b10740009584801441640142e4420b45481c441e1082200c00118100e821010440d01810308008454001c192030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 800201106 1250 800199856 800199889
    0xb0c1201030f0c090606020c030d0e0307050d1509210201020f070618050f0f0c0409080412050115150f140d0b0303040b0705010c080109060602060a020f0d0e010e0d031a 74
    0x3c00c400480c1d4200240104d2008190317950080c12261764020425049c000c85243c910180030050900b00386648000c200b6a08482c02203603160700302105030030500b2200c00a180c00000041c54080c020040100301031042c010182c0070388a2410114216000381e0803481812501200c42c9030501c81540020307001d40101e4000440408035030507c91050341e400e407401d003031191000740c5a04042c0c5581408a02040811144081144c0c2885500761680300c0c80f0682c4910b0060705000411041c009061160035044402094501e03041c0200007580c0f10307130607480104403401e40000500d0003091080079a100f095018a40144203510318036206a240c0020006c5c00d01c4640755030140024480050303e00b0f00b0001602800e40150008942c2440d401002045208144c001c3c090440c904202032158950000d0401c1d40805003410041e56145150000310751400b400d084840041e003840c50140f11003106421294110b0008000c498446540d1242582500d842446558000c0000e008056080c50310380165030440a5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 800202356 1250 800201106 800201123
    0x9030c0607021903050105150405060d0201051e070c0e0105040203040c051009170303040302061303020a080313081803010506041806020904020f1b06010905190b0a0506040f030b0c1201030f 83
    0xa043c4007808000384e6005540c0c03a5592010020584d14200c4410202d550469080059103000e00014640b81485400681049404940c00600c1c1603118503049a6140c000e005075100c0ca928580f842c0c51300c100d0b00400a06031045400051141000d00940b400349903c9031155131868100801d0018001004e00c59804220042000043c03d501c400e51407081c0d10a59000740d0385d00d28141c10b019140c964003800c255440c208410901012030b0780071400d0103815500c1061aa580d8590309100c04190380509000f524803800080c03080c40101100c83d403144c500200fa0004c2c4140d81d244000c000c01c680070800500307000c94881580d8000034550303030700420b03030313040001c0005040c01540d0b42a22000e412420640360308208000031001c1403582002000c0c0104400d02d814042072404000808080002d8840c4c1ea001c0c0392201d031b460130196250000c07071005e0b25010300007640300d07503441010201208461000340e50051080020a1100a91901300d45100b221004608900d03481c5503100000002400001c1e2140c04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 800203606 1250 800202356 800202379
    0x61d03190905060d0e0d2d0e060a1101050a061d0606070b0c040603050a0c0f080411030f100e030f1909050a14030105090628020f030711070b09030c060702 68
    0x783d40001a091050703030800300140c8101c00c00d04a0f4a0441d0718a483c8041c0b2000412503110444000800d42c1d06409a940301c02080c002e101d81900c44042511215a1009000c10781181b020b46c8454030241414244c002440107460309061541180c90a000d103036614210000c101d10b030405500511500100007419451803c4016120051890400d4079882080c1c9000030782041115810b00845030480703d0b100041088101844010b012a102080c0709424429154001418840f400014170716040000d82030f91245103d425140783c9481240ca000300d0201d14001b140a0b46410000c1600c50f910b80c082c00d414038008010540040f8000615045820000100c41c085041c8c0c440c07001c070200400f4820300d52030444c240d000405003035030401442e003e0f003648410100100720f480506a03945400850b007100b04800e01c1c115510b80a4070a800201c4800c6400100b4091804c5d032090200c06440626070a90707034030302d03203440c0f881604c0e02c1031030303101075141d4482041c6002d645009001400000e1004000c0300300304 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 800204856 1250 800203606 800203609
    0xa030209030c01030b090615040e04141524040207153e09030f0f060411010810052103070b04030e060415031a10090303080114060d0902040b0a030f061d03190905 71
    0x8001142e040323303140d071f001906031210441045030580036109140d402400f490f02c0c40d440c40010b24035a01e80c0c002c501c40140c0b40c070715644681c5c4c11180490742084900030350590758546007025003800414050b1419400c08425a410a41001c0c9001c1a02c180442c03000120064005062038000844842d4580201c4005a82e00c03041007203554401c80100b03000d42081c5c0381ca414000a43c02220a010303051141d80700410070414018042c120988000302c1c0c04000ea100030404610f941c104880c5040c1007031000240600a110706900d003980b06074840e5440300380e0f904c1e20b40c080c03054a0045200380c03c0c81c00c0b40b85400b40881800b94001a0241d01c030104000c40e80e20341360001841c118213201003240415400d61040c410305610030080c07405090300f092010603182e280b1003c03900900c1581008541c0301d40c0d5004400c2196542e41180c1e400b840000c26040070a5180d0812250f061030602003107428a10301101c0c07800c40200c44e452580200301a001650500c0c3c00c44811002155000040104000b01c888002c03465 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 800206106 1250 800204856 800204879
    0x21180f03030309071d0412030f0f090b04020406081f050c0904060303110d030e0a02060315030618011401120803190c0e1e06030415020f0a030209030c01030b09061504 73
    0x82c0c80e98100621546141008945c13602400c0b4a10011584d055810840894041c0b030119032907501c1072030300060444001c8405c80040c500494414000c43c1000c50b0503052291107440c42d80102d008890400c5450380e1000171955642c1c203d407000101c104140c43e5071221300220b602266001c503c0701895450099800005001c03601550030403004204d01d44501c081e2030804016640e10628203003400c11103e40e618007400e649150452009100f07400000c0041e006541442c100c5c0242080641120070909009410303000c460f044047c000282c0d03107410901c3c085003a01224450494551400e030700c841007001e440c4c140c40d40d40001e1850802c03050704038928071060454407400c3c0d04070702c0b0355407844c8828050744200b0442ca40815440e074400940000d80c810a80ea440b41101d41080e8010300d001c2c5071801483d41000130307005074102c0704501d010214048a905815400511151104900391025156603800540440780e0302b21005070880c0184001a90f80d0911b01b10280302c0c14200d840355400c00d5510548680c9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 800207356 1250 800206106 800206111
    0xf0909030702041e1a01120c0903060609020307021203010f0e04030203090909010615020102030412030c020a050d0e0108180a0b090313030c090c14090409021c0b0921180f030303 78
    0x1310000c0c8001203020102c282c40b4110040c0c001c00c0003988240c0e10000001d250b0f501100106072040c0c1d41d032000c100154010702040300155444030702405078903a079000940c0290011a001e1002d8010300d00c6043c05c460151f0b04580c103070380201072406207450918200f51101a0014011000d52008000c04007a40d41ca0001041c0700e50408000801c0142c10071584484010440d880802903a0060040c4000108000010240d000c0c203880c0000f21800a402e08914081240c64064a1405090401c6103c0e40d405028100c841c0403e032070300c1110362a20741c000f081e60050b2848129481e01708202510005507041d541c00e42015600c0c08590402920f110301050b01440341d4402c542e0042404070801620301c0034003800c50000c8170f609182180340b010f03001e01095881520390300e0f48210740d1400c0d80021942c49443c10034114443e4440321160401504e0201c0e2903900a1302d42a1f110b10030003d41400030001b01e6800451401540c580b00d04003a1940300c00c2142411800c051075101d0550b0342c00403900c1d1402c001452 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 800208606 1250 800207356 800207381
    0x50409020304050706090909030e090403090f0314070605090f0f060f13051008091e10020c010902130501050a03060f0906020a0819090b0708180d020714030c0f090903070204 76
    0x4030038517008029043e0603a560240350b0290403c01540d011907004441417030f04800c00e40740388210341e441b898102c1c2c501c4101d40110309070700044c510100611500c43c1c140403900b28820200c1d540d494031940291190b0060440041c4c0c01030f5005408040c0341092400301d104c1110144c04541018031300300b680d8002d5040050704c0b405000c0d052400300803610304446503544420103070038103a0260034410b5115880c0c5507119018002c205022400082c020810440b000c00585404011911151301e0780c4040c3c06407642c0c1c8410391007012143d02a000340ca4480c410f86049840080051b00e040c0d16564504001e4852520300d07242c0a0341c1e95607010085640c600080c252104140d90313452079450030f111110024084104821041443c04080f480007903a482e0803e50020b041d070520846643d070309010b103401d03050702c00150481c9002e05003110240b5900060508240c0340c3c8840402a00c080d0310051640d42d00c0352070040c5034015100d942c82c000600b008960980c2000d003070020f0760305d040003e40200c1c1c01e440107242d907507 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 800209856 1250 800208606 800208613
    0xa12021b07050909030702150d02130e070f020601170a050d0c031107031502030402030c0d03020705030708160506090109120b010504110903120904062705090304030f08030705040902030405 83
    0x26444040d06010320750240c00c045400c821036061209510fa41c0703019042d402030040e500340ea946081030b40081d09464600d0114001507665200140c0700070900b089ca880740240020340d01c004a142e150080c4c2240344402d8055005080c103a21306140b08501441442c0000e145004004090010480c01d2000c03012510750350f10352600c07004242c43c008001500c0c2d102800300b9134011000074000109141400d0214595048000d030f1030f619a400068102406500c0b4560700c85c2c050000301e820142c02190080445d50100c0584600320fa5400c100d64a61206240000e40300140810910880c42c0c80e03005010510018540040c6039501c0301ca810715208540c980c180e4940c4038003c010015880c2c1070181d084560010a4003605140307019011030740d03035410f803144e0742d00b10f0b100480c1c5c040721a212a4041e000402d461201c10802210003401e101c100140f9802c0500c21501f0003000035401080002120704896000600c0c04031110703241ca5080c00e0750409015142003140401001404440d9400954011402403025 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 800211106 1250 800209856 800209897
    0x50c030709060203070b0426030a24050a0b1e030a20120a09171b0708060103021324080d1d0d1112060f0106260703020a1202 55
    0x5055511079500c100115403040101900041c1d41904580d00107038080301107040c0700005001203640050003c440c8180b418080204200d44140340c100211060885003012a03102c101a460000410035018040d00710340898030401a040b000001441c0c9a0058800203140c5111440170b45181c9d402038590354412920307562201a054240944800c41800d071900c03071840c2400d0758038502070780c11008100102080e030b16040d15007400311200002c01200c0f403007000e00f41e07540a01e907402558250703600340728006d6224817400810020710000d00c880c1649d400074520000911a070f078409000d07080d900541c61004610480790a54914840c0021000e4044180038004840105200416055105404040544100c41c0101550301c841d2902180d003a00101d80405410400700429101d843d507181e00000384c400c0317908201c90700a5400c034160681d403960b43d81542d045240c039074a960f0034180c00d103140800c11160f00400c0d60b90303000b98024980e020890400c100d107414451690340c105c0c0c101d585004880c2141101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 800212356 1250 800211106 800211121
    0xb041404030f0903120e011e09061e05041205010b101e090509070f020c0303041413090b1306090f060c020706021219171003060605030604050c04110d050c03 69
    0x281c210002c000380b9024030071519540f80e00703042004a040c00340610548450140760b50b48200001142804075036904003c07000e003604018014001f511490001030504031041c500100303640001d1004420340d59940d41002c0c00c01da10f065140c009140f0440e100d40d82e40b120000d40382c9400c07140a4041c005600c83c0241411140c5140c0740501540713a004080180c10712007405180e50b03560720690841024584103a0101c0c0700403050b8075250500310a203a06100128000074180c540109809403d00190382100010350010304500503a885564024041d0f010003000038451100c196040c14240d000d2034010907015551b0712a0041c8002c6c0d20420f0306e885448035400c2000c2d0fa01044082e0041001e8401042c1c000c0d40c010130400503004e0610758860f031000350288000031510564007500c002041d62680c40a9041c20401068075200c907120458046080401c001252f14003c02d00314440d43d0084003070811007100004000c010a0054850007040d001446072a040003a14441c482c864400603e8084d40c9041904 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 800213606 1250 800212356 800212367
    0x801050a050703140403050313061109030d02160306110f070b0406051005010c021002010b0310020a030b060a0c063809011205030a0f0203090d060507080c0f0a080405010b04140403 79
    0x10300442c00e041c1040c0b100c0c66661a81c0d00390342d03031054140c83d005441e61242071520300704011016001d02240d0500340c0000529031060010300e4041c100710700b00c0f1442c8001d0031003681c0b04c5400784003c24043d102c5640420106a950b0083c5000c195a00d598900d404005c10000c12503800210081e5a0030111604110402140d071003640d411103419a51101903520f400002001c54801580c002d000361205c020f9050010b00175004068251801419180c844000c001400000d402007145000081c0c20700f10f15a0f118107001040340c5440c2d91542d62440a031031039881e480e000d41002c00020500ca01e81000b003d020b084104001004603032490300b022640122841002001c00045e04a002c11800c1d120b10341000950000440d8500bd12a080041c1c4104000c207043c1d086d1700428010603008448110000c08009c00760b8880d80c030554042e165425180c071014500c182e14002e400029040200400414202d03600410601c0da019100f81c1c008500300c00ca01d0301089c00d503418010b40c041c1b03107006c82044c0000c058014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 800214856 1250 800213606 800213611
    0x1091a0621010f1104080d110c090f1608060916020a1e06060e01061b11150a17010b1c06030f0b06150304050309010f0216060e0312120a0c090f0801050a05 68
    0x419110b04207828528071a840707c04c50700d001c1003844410106030841000c00c4c0b2400f08122001480c100a80c43c00f10316030030716008115a000e03861094070030007502080c080d2080b41e0240c0c0c4068090b645a5640e0070302e00041103460140c000a52041c00369002c00541881c07a86401c5020901c006280101c9618041c025030782035402101d9055400d00051000940c80808a007210340d4200742650421420300f0105050000080c1c04ca4201c450104000250b020020041a40c2d5415a4a61120819a0201d000a00310070301844449950400c2140e1440c13001b25001c0d01030b900e02c04000900c8075a0b950710b00e0001141c28104071546007034841080b107e0f24141058410f03486100d00010700c0c1d898130f556941d4480c880d10036164180100c42960410030b900c200620081c0043c140c0b10f00440603218540034203207200442d44039200c1d228100140d031980302500d06441c0d038600440101d9000c4d444d0a141640900040030900c010400c05000015005810398410002043c0c132a0000a280c14991506000d44000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 800216106 1250 800214856 800214881
    0x8060607141b030c150906070f080a17160e040507030f05010807030209091501150c0206070c0503070b090a140105131404050a1416120606081801091a0621010f 70
    0xf01c4d005c0a00207150404591b8901d9085802d03654640051030701a5003280342078809041130b5000304401001c035402949007400950f91054020050b5100010364141002040d100000501854541010740c101038004e2500328400c0c9c1004101e02c031440702c6450407154268418040c60340845020007c0d8102221000c3d0440c003250054811010407060036162464103204003100221030044440390144611741c2c0c0a0303116030042c4041d95464203030420034000e44460007214800e00034441c00040b60100041229101c0001038010b80c60140f4003c4403000014030070341d806052001c200641c20b01400c0700c1107280090001242d2900d41402d40708241300c101c0b03200400c1c030007000e03240c03500290036034145000c42e51340206414800d02138061010000c48501c0007901c04203501c1401c0034408a0603035040355640340702e00020020030a6941e2050903140c203960f12510003424208808100d90350240c21490000e52290000c1c1030400400f40400380c0320700030140d21a018400780d640e9800905840007134050b40ca001c1c0318 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 800217356 1250 800216106 800216119
    0x9090f090a141c08040204050c03061c1b060801030302070504090201050403080304170415081509180c0d060c0206060a050108061306090606020105071202070308060607141b030c 78
    0x20040c101a40d034055000c406800003142007a003055030842041101c610010400207842c50107142800500b03d04020303542207204a081000280f44181000f090b40d115890041c03103000c807084840f005007041c0040c0c110680d504610324142c7c903010ba840d18407840007070000356600034a5615604000381840c2c00c0d9040540303d01d082402180144c0e0340b0205130b606a98020920607502e88a6140c040e41c3c812071141000c0d44000080350001e45011046c0148229242c0f64a4060003035030340d02d038030041c168040d08480d58030910040c0172035645608014168030002e04502250b11160a0364005502481207003070482e0305d26240d00c69500030302d5051040311b80008040d40c442011505000c0040c1074504028411406405c4000840c50a100b16800030402080100390421802c0d485c0c0310005d029200c1220303403070041070382ea44441d10052524400c8601c0c064041da00c9400c0d503210503041100c142d0011005642d10800d0840000480009100e454118290903142c00410080c5030181401d085032030b03000900c25403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 800218606 1250 800217356 800217361
    0x3160e07170103080702060d0f290904020604170f01020f090f030d0c0602131a040501180e0408310e0627040602040803070b10050604081c2309090f 65
    0x40c1d040c4141e51720554121502622040d800070103000800c14a04c10700b810300d0a00c0d101c035400c04000400f07140958072050704c081402e80140c041c80740d00710b000d540003904900c0400c0100f01d602001b80040c00c0e11061001a103400e62142c5103540e082e0781048000301d80c0c20000280f440d880e40ba020104040441d0203a016000d0070400b00009401b1403c0e000c00135204507000260021000e000007511000b915a65503081c031616074183d03041d8001d810500401d030100c0e002c849500144031040f00640116070360301070101e036141d41b540c2d141c4d002c3e5000500f80007562030f41c40c2e00c3c071150a00408601d802c00e102e01c0e240401c000b03103800e208000c0240084c08032806151200e12455a0080000c4005000032000c81102e12603252031821000030f00c42c644c40101280404141c03001084220580c50b809003040d541000b099a03101c80800055108502c50600141d0100903042c180e400d01d00c5003213405072041d00703100000319117050f646042d030302145078108451347e400130b20031101d0310700011900c1c1c122020407040040391 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 800219856 1250 800218606 800218613
    0x204050d081306110616180602060109050f042a21060c030b030318030a0b100f052707030b060c01021e0309150406020c030f04170a030509010e03160e07170103 70
    0x840d0f0140c510810000303c0c0d940034406c180242c611340c2d030001c052000c6a140f15629580251544020700032000d2107801d0a020900610704120924040c41d0003080e0a0300740d1900c6421813060100780c0081880d11060110f00082e0140d00342016000025881c84005a80240d403814408440c041c0072400c0c2818901071074049103441c00070036034510300c0780c40c1d042514005524000030710b010030720341d0010444000003041242000807032004008030340704450725128440c0c031001003001101d00f01003889100b031200e210340c0110b2007440b0140e0390000707820309001400b440d40c0404209654841c3d02140c416a400195500183c0080d000c03100e0381da42d90344481400c6082485044c0c0c1c680701d070a09481112184d040200b0140807103039046441c445140b0040341d58401c032000f2070008981161081141da5540c9010a0004240c04110814200d42c556100c9191503924070046d901c01c6102d150641d0944907130b0000781c04e03040300300c4503d10180203000c0500080d03203840c00740107003280c00d01c02144104800d60030040000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 800221106 1250 800219856 800219863
    0x60301111b030c06250f080408090f03100501050a06081015120203130c09150b0a031e090b06030304030f03030c0c02041d10021c0e010204050d08130611 67
    0x207146250441c2101503403241d1420b1941c09001e01c400c2c1c3c0c1d0f0280d04c0c248048070075113901200c0401200340510003880c1d107048081c0c41e1040f68414400c0030529000c005400220110000c0065081c01802d4110450101d00444e01e005400325142401d10340e0b9200601451a00e1140c120040425280c074070902e282c0f5103280d1a905025109a80404011200e07405125010f900e8242c400d8400100454692409402c8000040d510403800c0da0001e08000012440c11070f41d0140c0c0031050041850001d800c0c1c50310000035010741c00884038000701036503150007000c4540b003091200d803d181361031008503200d00d0300d04040d01c4d8180b01030603c5229a00c100410800a5080135103101100c3e054180002d1070451480e06942160b080c004c0294004e1038820482d0f000c403440c0040d80c4c501a062022103003210680c10501040744500e190001020000300034160178182550401c407241ca000301c0025040035500e901182030054800da040300e100300041180c0318040160080303000100028070345103010590b00002c0d25103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 800222356 1250 800221106 800221117
    0x309090406060e090109031d0d0f020a050d030801050a0506041a07150203130b090102160816080c0304090f05151314070f0206340e030d110606030111 66
    0x582100000502401040d034800c00080114800050701c528141203114020140d4404c05c802260080c50b1044200b003003580b03140c00d0311001500710350054080c0d4903002c004140d190012030f417201c1104030100d20303911500030b400555482912500c0580d4140741c100450100030350811405450300340020002d42e01e8461080c0c0c0f0407881032136002d54849950030016003a51a884085030513500010071f01c240d004285941e50794141c002d1102d1081274035a107169034240d1181c0c01000d00140c000b4148100410080c07401403580d01c01c201c243c44052032059985031055000b003980a10b8a03000418104201c0a05000b18061412000c004001c2c9240052580d050055241e561500542c40d9070600c400b0351009138041c0c04890032282c180811494403a1006180c0c03000202c1e550014012080401c0204103c0d00c0407400460108044040139542030820b0386100c414100303090700704002d992611075252000d008500d0078440c640d80d8848040003101d201842c100015000c42e020340c0c5000800079140707542d03405860 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 800223606 1250 800222356 800222359
    0x150906080c1503100f0b070203060703050c09041a0306010e06090a0507020345190e04121205130c08061902092d04051003080708250c0e180309 63
    0x1d443e51100c032100040c0c0045508001c10514007030001140e0700340100080c00529100301c00301e0b007003a0b50f4174a0480548005540c1041c10b04424010100b603840c04d904038a1306600050614002750241c170000903c0c3c60400c0e40701601c045090401d1101900380032550a0340701c0c1d0100720a00050804a000a5480c49100410b8211005641502079914800211251001c1c4409888d213035812880700c04105081640c0002132080303003108420250780b040e0500b01d908807000c1500c0300306180c1e0343e0340380c80000d104288212000c0041c841e220040b0070009200e6980070b6004030120400100342482c2c1002503c840382c02c541000c2c0e00601c2009a01c641d4000381d02c01e04507500c1c4000d41c89501640c0440c0c0501c6019404411040701041440c61040d140801c2920308601120144910740b034240308540a020075000252a0801c20000c000100c0c402600405c612105021425000d00c40e0300081280307410329010490300803600703107410080004034402a0382c010200307903c42480301d810280041d41d613214200d40e5a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 800224856 1250 800223606 800223649
    0x5030d17040218070305100807030f110402040b070c0501031112160207080f0a0c06030b0d3302031503010b030c0d06060b16030306151d040e01150906080c 68
    0x581103445402481803020049443d110b079600f40098090080e100c03c44940d200e0112205000441c540f0014400b021240c001c04040c2c00f0b00040d4031654020141c600d80c180d007040e02000001041c000d408010441300f070085046040b003e04090005065840d00101c41c00d0304c0b0070501c190341011207004240c50308026102c03842d451203900c000043e0304111043e80a0070490045070600501011301050b074030311081c4074028070258252541d100b54110b40022808582050719040102c000070940d40c03d040107a079000c0a10803200304201f84a4100700f0802010481642d00031080c4689080d0f1402c40c03200002e0100c000388181c0c110039005c02da4802c1d030302d4042c034440e083c031907600030502506074450f2021701604901030303584134514600c0e070050303d1501004500107440d000c0000381c158490000c002900e50295035091034450600c1c0766045800b400313850550301560f26480401070640921495040000c001c0c3d0304900b25140c80e410004a0f05140e104c404144c0100e89610b07199034500508011100304941807 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 800226106 1250 800224856 800224861
    0x100219050702030a0803280204030503030c1b06070507060b0f090a15090c0504060f080105090c3009070b03060d06270507090e0a050d11030904020409020a0905030d17 73
    0x1c0c03504d5204580035141500001c03e200044002401c00b07a207499010040c4000070103c450030004900c02c500c00034005420170300c00308007501c2e201030090041c01c1110102c450401c04e032110f00303818040c0a07038200d0045200042c0000c05c1084500a1150281080762800050040c11010801c0e00000a018082155031160b08401c801240501e02024001c4220308204e04090354001414541c0140241d8001c1603107030303010803245845248258141c8801034480b200c640c6401034070002d2a0440c0e08001d02000c13055076030081c0240e4a50f00608410341096251041d4202203600e00d042c1000ca400090031400200208021a00d0b4511321000d01588858002a00e010b2001e0f541110710704e130311000c951056182105410f01c036000424038103491258000304150100712044659a451000c1c009245410010350680c4890041408900441c0880f0960307145c008407038001000ca0f07205030880016a82d0100304d000c90340c1c0d84801c00c0005010284d000309180c1a4550010f800103004461184c100200c1200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 800227356 1250 800226106 800226109
    0x40501120c03150e010e0a02190312050306042316050f030f04050703020d03030209040c0906020c1e10031d010b0a0b13120812061c0611091011100219050702 69
    0x4094000710f40082240f0319400c203161303494071fa10030700680c42203800d404003658a00498500354100e07a800341100d014914903403070645072a00010701c0981d00c180d480b1417030940f0780c1e0f2103540d1a14094030002070080a18106056243c4800c10f40c5e6154200941800f04507004408a02240d03048000c8000444083d550361611070700d07200582c2c1009410003041001c403810190190080c2000303c0040313405021084500c0c0080b54001c1c0c60b8410100168451081c0010714240901003206c0701c1e0003220f1405280012401161440c1e000402200019903182c190315241200e2041e6000580a040d00920107c0813400009240c540c0030702a040d0f2000000944020001040c1035403401801d188540484145250824080301e411100401d07000c4602140010003030725081544400d00084251290f0a031040c980798040245400601200130b020100a80e44e29644c1d101c0408801c42050303500c140803030a204921a0a0030071100300090494011b011252015400506150381e580052610b40d031500600d00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 800228606 1250 800227356 800227361
    0xa050a120905120a090504091e0c08190b0108120702100507060612050d0f020d030b03010e0f010e1009050c040b032b030c0203090d0209100e09010b040501120c0315 72
    0x40440c854040c400001c850843d000c0c3c100c81ca07243d03d820014541d03507030520007a94181c540c001c0c1000300403041d100e420002501c010300058090131505440544425441d441c003541c2928207051040200045c4040024108810340503024580c00b6040320510403000360081d001e038480091040400002c00042107110302c0070348000300d800c003500344602035540d001c3c109200c003d07140c01e86050040e03010000e00300303001e01c580901f408100e5009124031003607018110018801402032960554a848074100080410040c0c100d0301801280005001410307a11480c1c034084521003c00803183c103100c2240d000c5070f00855021304681c02500d0209042c074040c1c00090520b000e60f0300481d008403002c2514402c60314500c0340c0111080845c1c5080041e0003107041c0581c1c3c1c030f00510310919400044d04070101c005081542c8800c1d000b4081422898085450740201980c0301c40c21139625005030340d00c2c1c501402c10300d020f020f12401004200324684030300b501a00c58101d1102c01e0701015280401006082000c1c1050740d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 800229856 1250 800228606 800228621
    0x30402010c081c110c0601180b04020d0203090f061302060d0b090a0f0e03071e08070803070f0212040323030405120708061e040605151e0a08030a050a12 67
    0x2c4101d603590382c0d03042070184070810080743c03401c3c86529209448803064804000c44000c201c20300010101e81e07281c100ca040917850b49199615966886064203d0b01d0303144c90020b07040b41030b11602e0158807403500300c401c64945100314109450640c031402c04d020803000001021080c080d01940e0381c03681c030149290010042c101004549410182140400607410301070344c000180048410f4052000382c1e040c0e00300a5890040d01805401801143c0080d03600c107074480a0254124070845c0c15500744143c03900c071090a500112030280c08030740c0780c0c44044501c0da4103000503000030600c54843e904003401c1da00d40c100300c91607031250b12140490a0181d5039080804209480007410000d191804170102a400c06440b03400c540708064103440355101058806075100c880344001c80d0161416000c690312034031850040e000c09459016034118004040010b900c1384100110317410400c07a045071082c682d600a1111b054030a902001680c0c10900c40885840c1e801402c9500001c164900b95000c411280516401801c0d01d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 800231106 1250 800229856 800229863
    0x6040f29011b1b080d0e0d0f02060a1206050a060c150e030c0a051504030e091f091b0e1c08130e062821140619060f0506030402010c 58
    0x7006500070800041c1d4551103c240c0c001945501c01590702c0e1486580d90700c5007a075110202da800342d112100350928641e040e50390750141680020f08081a00411042d80c00b4944000001e034540c0b291032206680b6014400c000d10082d0303684480c451802600030b010580945000382010500e9551851014054015140040100041da0b1780d841e00d0803240d65a405103051b003195107002e48000300590351045040b1520490700340d07d80c0c128031034000d0704014134090001d1250008400d0303002c40108032000140c150780542040c40001031020840c401410a450760003075040300300482e0b20445070032a2600c00032151190003a29000a10014a1501826030301031090b0344941d00170180d00004403200031414039800340009036001d0302c48000e680000c0e0090f602c5c074000d910ba0f004812070204011071383c0049035842101c6a5450074066080c80e1341d044080c4e2584c40d80040740364021814881e00041c18121078400c2c552100c0c080040a250402100a8840c6031242c04d104000101c001810359009001c0000301c50350 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 800232356 1250 800231106 800231147
    0x16080c060f0a0b030705060307210609140105030102090d15091e03090602030f030f060d020d030e10030204050d080a03090b0a0915050f150103020409110306040f2901 73
    0x4041d2040c01400c242141d12000141c24491810308604012420f02c0581360054041803460741c9104042d582c100a206202d00d00c1d400040100b00005404c1c807492005c0d0044140100d580d08011081882031001038000522907481003046840b640d90f0900c81111241d0310440e951131110200c0d0300c210080c64440c10192010000180103e0000684000c51084900c40d4a0f0340701c1c2c0903100e0b00101e03943d0061910041c0c0240040004c00c0c4104140d1000580c013000050000424261541c086010380d0040780c82240800c266035419215844e128401c0303107110311a0301e421800c1c6407800001031059910b003000508002c0001a100700f0b00340c400d4200d00e00ca1504100001c8081c1070444408d401006581c0040d29180000980034220444901443c0d0041001900b2494a0344902c46440a46a840101c4505066003000001f0f00710055000300c110529060f500e440e00e1340b41810521007a1201640c0e03000f01d4524000b00d1584c100e042d2071440503152201100c0c4d2500d00340e14001030719596254028003491030b4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 800233606 1250 800232356 800232361
    0x1109040f02040f091b0903030206070e150f0309010f150603020c07090608071d07090302221b11030708070b0c040302130605011b020a1a0f03011401110304050616080c06 74
    0x5134141c01079051a1102d40c01d0300940034444c007080782d083d1420b000040040e00505c011a80321480303210710110128000b003040c17054201041100489600244643c549101f000c0308111200341c0c280709440d44260700940038801843c110306041c14840ca030b130080720145540420078403071540302002000054150341800b044030b1510f46203900c1c2d484107180726500d025103108507407082124078040a24001e0500341c640c2140c00e81985c1c2004110214840451200991050440340070003c5005001c03000e02e00b103902100401c10030f00001c240c00c040c502c4001c07841c0d001300038041c001607200080701c18043d0803010b10b2410b40c0b220000d070052485581e2001e036200741c2040304240f9000041d800031003100d900b6210904094510010041e0340c5039040c401a601200e1220100440307840840403001d00b08a0004d8103203002d08850364403e15230005e0304480a0b5070a401014100ba58010340d101c602c8440c404000c41c00d10f0718110000754503100c1c3c44006a001500e09640100b000b810741c0076100a00c1c0c030881911303910b1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 800234856 1250 800233606 800233619
    0x12070e01140a06050f07020405071e0e0f0303030105130c2003030f060f0a060806032a0f06040b09010f090806190f090804141804050d0906031109040f02040f 69
    0x2501a8042184144500240003d07214081c100300c4039245010400303507040002d503808010041600412007001d00c0050718441c0d940d05052041603120a4054940c80c1100d20400b0600500c2450407000078000e0380208014006c55071a1120400401000c40e0301054881c1c1c00d2034112031141e03040c030600c400d403182203620301d4503400b000c0043c6209255021072040980e0f13440d0704201440c07502e40521a084080480c0c00c0c003049200741200d0f9801040601190f0307805074845e14040c800c100342d04210907034002c224003c10180c603180400b0010081c0c100c450074202414140d106080b0300c1349c00c00b0681400103000000400d580500030b40d000804602d0142d03034103407a10740d10280c006c0d1380d00112861030310700d006a050a03180043c4036009a06030801c18941c1440d00f0020340720300c40488038180c247d001c080c9a10300071400201000d880d1203507125402a0415400c0c0d41d4000c0d02011003034004009041c100110b0001c2c60888600340c03000c0400848021031001c4d04541108001d1140750880790340c0d4200c0e4107020908 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 800236106 1250 800234856 800234879
    0x1f020d0b0d120f08010b071416080102130503060405060106260a021315020309130605060304030203040806091b10090306021603090510050703050c2409010c0c05030912070e01 77
    0x19125030b8a403600f10700118001110030790424000c1119107001448103001090f0b400c2460101d00b603164046580c203040a07207050f0a10b035460f500c1035401380c0d000605c07400c14a419641d004d00900c000e800504003400c16a42d01d503101c2d241402003000f04400d09802d02d906c51002c3d0038000b9175540070352a4100307605004400d00040d40c4044402c6480c6024098002141900020750007803100003640a1410b003507103c4200324001c0094001d00e50f01c0c0d52076007400300c0d1540d10325000b1030049110307800540c1c0c0c030b9107000c0d01281803c4005095003025081111100805281420109285030f4202d4100d401740c035801c04c094403801d94a03000640070510108904490391900010540d559020707440354007a480e41d8034104200461242400c40c00107e040c04400d00107400345010340141c034100340640d545d034a4009484161400f01c40d0003400c40070705580038040740560a1081d50398041c407a18120790500040d03112a65030340300301d03200d150080170004480403807614180005009084d03410421003e030f5039507517450101d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 800237356 1250 800236106 800236133
    0x17070f03121a240c070603050402210309040f0212070206270c0904080403050a030504060915020c010809071a1216080a180605070c0606081f020d0b0d 66
    0x1c010b02d80040001c012a03010203460800c800103102c040101150365500850500410310410600c109103c0542c254005005035400f41403103503000a001d29043c0100044003050101c42400c2a44c0009046440c9a012045441010040d20b01048441800c2d090340c0084c400c100740d0010420098050040c125408603850b0b020b03042c940180310f090f500d600c010f6051400c892055460710ba210750a002d0705030901c0100a580715001300103450901d9583d8440e41e0412001e50070440c009240010144841a0030030081d502820a04400c17405145800401070740c1d424000030528107010141001820a2004001600150003404144c0120400c490310142d669044420055440120400001c0d1501e030104007403ca400720590310a8034940750b0700c03003003c000e1062841e04001c0c3c0d100940e540c1c0100d046402005c1c05010381e03984640c0c012026080000c111001a0030082d41c980000c0580c520094088101100e0021100c00040c0e0b10340000740380400a20700c00121541009503080500d0601030180318020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 800238606 1250 800237356 800237387
    0x6180b0d050406050937021003050f1303021f021605030c0c010f020d0503091203090a02031513030305251101050703090305070b10091b020f0c0d17070f03 68
    0x20841c4c441c409402c1d190060907801512440f01c80000030800c0c803007400c0c6c0d031804680514040b488292144c02040e000622420340300d001c02e403150148404403080e408a42e600c824018044804240180d8009488a140a4560785030248111007a00d105509504072884812540d040f02c030060094500581c89801c41b0000072640e00070b0030322480055010706001c41c50b0070703c0707540070b000740d101120410364050b0000b508014461040e0a01c0440402aa40046000300302c3d4030020082260340c0d1041524000e8519400c0c2e01c0c6900c444144070b6020b501110410240d03038036080119880c0c3e10070400484010144443d00ba80c1e424070514180c07807a4001d09484041d0442d02c00901941d56500300070f03010340b4403030340e0b00500084041044d080030905100304c0c5070700104080380032907082e50398085400603140200c81e401000300740342c800004460780400030f201c0321402da180a84030420101c0002401d400c10000c020344820f11581144012000c0c0b5001c41d02104d61041d4116200b030b500b070034001e240800c200410b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 800239856 1250 800238606 800238611
    0x608070801150e01061115071d040c080601030c050f03040b0106090f080616020c030d02070f21030e01090e190b04200a0c080304050109230706180b0d050406 69
    0x14039400d000c0042800c19100034035400805039181510403903c486c90701070510894020031613844d10381c1c0001c01c0c07d140201c26070b6640301e840b00c804185444855102d020038510842c500070551840355004004140d0040c424200010b0a000681c029113017803103000e42c00c1c641c910b000802c000c00c01c070070003811034180c0d04a03944412103140c0f100c22900650303042c0c2c02050103550020b4005242c590f000c28070400034400b10f10640700000f01c41408203140500350045003015030061039040c02010885140302d0000c00002c001d685c1c0004102d42e620008404c440030103070801c548800c07a04c503640d0288030000010704504420b07074010324195103035002d00d0951111000550303080c4514410585070074010481d0881d801c40d0380503074014420341d940246500900782c410500c980121182c000c100c01e88040d52045000c3d000100d540a00c51420b01c6c020f450a602990002e5014510f90104c840c00181c0359055490762f01788014590311280402041d102c49510902d202100003490f20b0601f00a500110b00031881941d09 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 800241106 1250 800239856 800239871
    0x1101060e180d0504140a09050405011a010e011416080417161508190212061f120207050c100201021b03030135030a0f02060c030c18040f0608070801 65
    0x2a4854400010042c0018010b010510001036001d50103142414010240d0002ca42d80e03c0381701e0107642e02185c0a40d0542d64800c0341e42d000b041689a01104c484091905000130401080042c3c90414941c8010007401c0001c541c9500380081e18030040300d007035004188542c44a580c0c1541181180e0349121603003c50140e080c244c40c1c440b0000480c20191381c4038140c05400e0340750300c800480c1c1d1018020b14968030030002d403503103030b2884960740300408141603402c0f12014030f4074207103040c022a12890801e004140c0440e854000040385d210074460240740880101603a200b180e030030000d15042a00072040c0d4054200031007042040d40550080408008040c5200da1038030584041035242d00091042ca00c640181c0700440c3c80c884c05441500059007408601c04202480c0401150b10f0340d04017101001c04504041c20801c0c0c3c1d00d80402c400b076070048055180710714602d015240400c544c0a6607a00d0300034003030320780c010821680d26500300d01c00580345204100901540c5e100100d69039421403040400310351800b2036 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 800242356 1250 800241106 800241151
    0x31b1b221a0a320105041206060e100305010c03110913141807410d2d020d0308070203130e040b060306100e06011101060e 54
    0x140c04103400c110000d944005200d00c0040c0c0040d000500081400c44202000c1c0599503403910b514201820403800101110b0360b040c0c00903403034000c0205000414943c480c002d188161381c8001110242c8006881d20705000c0203d02d8100090001c82c0c0140000340340f080d01300728030245205c4c46881100d020304024040c4496204003034044079020b15850007010410010750712181004e40c901b655401403d00c0020b40b0f0103130b2481160b1001e00641e500c0c611120080240d6200b04810421400a869460701340c52001a80034824096260a21180000c08200c40c060344800e0048850100c4254000b5107222502002881d101c07421010340080b803211078800c01264031461304034030030b416241940030b4200440c0440c07035102a204444010250400c51000700900b0042c0c15008415400800854034445428103040c605031444d000f004103458040d030b00090400403c00c031203400c09000c540e100300c1a040c1c07076226100102c6400101d90900700c4150f0801400003119851607404601c20b45030000b018021000802 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 800243606 1250 800242356 800242369
    0x230f013206060a090f080f161d100503060f0612151b0f0c01091101030c2709020f12060a030507090e03040909030c03020c01050f0703030e031b1b 64
    0x409120200c40c80320006040e4100b10009006100150030b022852990b41d0002902c0c01e00a50441040b80e08401500540114200060400048841c445894039400d041c480001c6140144403003942080c6e86010601542503c04800081c081c05001d0390301034605250300c000462001c2d190346001e03115154154803000c03c00f10b00f440380764582ca85500001e48554044043c0e00c1548240c00e030a00604010341c01c89507071003030010140c141c0300c0000440c0d00b02003410311401ca085140541410305081005402159038031406c00b0000c4142490181e0810f00c00422071140f66155420903d01c00b840040c503032601040d0700018102c41444610400342c150b80351003d00c8640c00e414403004103103910080e0144122483d035040b103079a40400c441100d00745542d43c1c101c203007510b030040005d41c0454458410b00c018143e050290f11001c1c0e00c00e08120b40381c1403020410404a03c90744101408256603007054000c1088240100c3d0310340c0c60080302c800384e2009414600f035114098241841e40c040d200c1440d8400ca1708021 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 800244856 1250 800243606 800243681
    0x190e0604050d0303150e10031b2112090e04061e050a02090306130203030a0503090f0625020706091802070204111c1e0506030c0a030804090c020c0904230f01 69
    0xa15203d080c5881d642d86d004504d24680d0b603040b0270034018840803801c050204031840107440c005c04c00c501070540505082148400c8044444108a0040c006002460401c081550040e41c804030020382c01c444010264690502145003114042c2040180100c10000b50007a000e007500803016074040d9110142c212941c0342039400c00940580045c04180901406500a1640701c00c2c2c0c00191102100030070030071410404116035100c0c9855817004030070702c3c002c1c5101401a104c03d0b180002c0c01c4103400d102000d40000035130720034001790004000c2c5501941c05030380c041e0740407650b002e0418012810640b0708140d850b044011000c0f540c43e00b01038142c00141080c0240c3c25140f01c004600c40c4ca9003107062034400980300003020581c05204114204c010b0382c890800d01c800641c060500c03e80ca403800d0003008401d842030f104000f01150f000c2031102c2d5884c2d4455180ca0f410903032044021900d1021030711504820411810200201d010b240042140f032501034000480c040365030f000800114400e00050200c10010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 800246106 1250 800244856 800244871
    0x1c031e021822050a020a08060117041202012408061608040f1410060807080304030309140f031606090e190504031b0303090512190e0604050d0303150e 66
    0x398258070810b030410312200c0144400800d540000c0c0c0c1c1400c030091064810603a00c2c1c402d601d41c001040b560041c0e101e040582c014009180011008030001407004101c80c0103800540030000100100020318000d40c0700e0130090711402e06203960030541d05103c0182c48a6807081000034010b00000881c03156080c52210300a04e00350301c841d0319a44560722140c02d4400f481100310303402c0c00a2106d4000d0f510302008070707201c04a0410800700b05541400748503400e18109a2000f072003548140302c10310009070028944001d441481070078028944550001440c000205080d039905806203030392090141001c00c0b0040d05a9045454162000c1e0341c1d460700c903003800c00845803102d05420300410009044e80c55000b541c2c01c1345c001e2030441d07045980307110001c841c101d13480b0b41180072075580d0301450f040020511040b084040700440700c5060004805426080380c0481c80504104280302d0f10100059a07246c096030090000542401c019440d145406030040c00d0f41100a0b011400602e000288000a500c150b48180035 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 800247356 1250 800246106 800246137
    0xf150912070807030e090c07050106060819020d060512030415090317030a2405040506040903020a26040905181f023f0c0403030915021c031e02 63
    0x669250b140b0180c101500807803c020500c4130109031039643c00556070240449444269850003a0701d8258212603403a4885c2c3c091002d050108541b107110b1050341c522901e400c07071001d130703850810640040080480d900016032150100201010b141303000000340080d68844180d00407202c06c03600f41912421302a20004001c008481f104004d860130002c0a541c01840110000c03d14407514045140a56510490744095540001c01042103103060f0150310f4101d001918100031000c503e440003522040034140c060813000e1343e00440c6010016124481905000029521313072a141c81d101c3c928040c0105a480c0c292903003419058444010020400d0b00c008907500703144d00914481c1040307400c0a5000740b1407091001500300c106d19a40e00700170000c6a0105c2d0241c0841e8003684042c042151140d10240002c1e500030b0050100b400001d030000341030011356141d507020001e000d0720004124901501c1e0314000e013056200e03044031400d5607015000f95550b040075055030141b5081c1c0c5807901c02240908450203440340d8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 800248606 1250 800247356 800247367
    0x9091602100b09060d03030b0409060218220e0a050d0c02090c0310030303180204150806010f0311060904020c0102070507030b0109230406110a050d050a021602010815030f150912 78
    0x5080d402140d0b13006d11a09001c0760208011300098115040e949040d103a540c0c0004503142403165503014614203110840305650000d0110022070041c02c615000883d81913500d407110300300300c44c0030003030b02988941c07140450f040804001001442e04030040c5040b4001c2c0380c1d040200300b02c0903028040c2c03403003003004404500c0c0d41d03480c586086000e0204681c18503405006050030a000d0388031030081d2000c1c410b6000c00101141c1c40c0500305850800d050740001100440c0c00010700004039111104241c0d00d9044a2181c4c507107031040c000070002c0c4a0041404440c0d88001072f1881004000304182c0108da0103519640b50b04ea80e01c036141c806807101c0035010191000c044624030110402d004040c0d80190141d600002c0f00c600800301080558002088100480c0d80828654200f4185000b203950001d619001507003007825100d00342510130890403009061080e07410004d18042542d000b5180454001022078103c901504100c94803004c450340d00700b165007115000100704100011301486400b039462210313441d18 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 800249856 1250 800248606 800248609
    0xc051c02041d030c06040b0916140307050607061b05160323030414071d0103030f1403130311010504050a08220b0c010b090405070b09040209091602100b0906 69
    0x800b0070858a02ca49000b40c088190380c00d800f04060000c035030f9540f0040c00e55091074101a219544000d00c0c03421030b5844501c940c141c020b1390000c80301c116003086d061341d03640c40034007400a4101005078100be500300e10007066810900032585c0040c041c1200010380d8500310f040e9170b802240e03548625611100b24081d01410340740020302c90642c000c0e204112942d0070448050a080c107081680c81924140c2d030b5882594403010765040b00b031162074000c00040c1040045800807038841000f4000500c009018041c0c1d0a0090011070f0150310141094070100500343e51382c0c030b40400e400d8900c04c1c0303181003580050710400034121f1520341440b1340d40c0110f812000601504500b5a60060168071040350b201c2c00b21000c14a01e559048000d04c07140107000190700b40c40c1c03605420ba201a08407000c012010380305580c450300f408041500450b0000641d12202d000303507618010000881c0c040c2c415203c901d40c01074002ca08000901c28454110684860298203681a04c10100e056a040d2007210400c69488400765021869a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 800251106 1250 800249856 800249861
    0x2041e05041404030e1e090708070908070608010e091c051306052107050f0406230703121104050901080303070e120c01030c1b0f0c080d0206040f170310030c051c0204 73
    0x92540d0035002140110303c5001f060321418190b07220404a1100000c3c0007840360400d503804050000c40e002094214a01070008103001018440c41c510410703010003044440000f88101000c040064140340441c0c17000880080c120381c001c903402d07203841c04007000100d266032081084440c0007d2032100340003443d2070926100b034080341c080c0681c002d100c4100702c15403a402614000d000104010740ba08043c2600e0303c85459401e203e01d03091059001010051200042d41101145408020040300040c00e600310030704d0544940704a030030159100303418000000ba1a0b6000004603c05c4c0c01d25078440714800d03080300c14401080410034065540b5000b91100c003401d075210f82d00c03085407080d40d03292200c3d0f0090400010981140000c070251002c4a4102d0a901481410300c44840140210401003560500d0f070036009481d1640a0b10003040c0c800748040d50014094100c010210a91194804940e2800c0c56050201c144a15210843d08444030f00c01c002032510700f02141400c15074603800c1c5643c01007041c1e800c0000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 800252356 1250 800251106 800251129
    0x60207090b061c05070323040303050c090301060305011a01020a050709051e0c07140d0f0e0d240e070e0403082a0a200307030c0602041e05041404030e 66
    0x100070b03409003d48440351100c00201c0f10707000f500800018190600e03c4c00141514640c4403402c0840300440a40700c104250418a0b603440b0360036180019142e150300c45e0344250391081c51240d0b68990b08100011060007810742c8082c0c032904015400380b84980003607005980300c0300c08440180131901303c01000c1218a00c2074004ea580540114070340c40c048070a01c6a0702508400a03280c1d88140c1708082030680070881004d00c1074004001010041140154000c2d00034900c8041500700400c001c0d42d250b18481a0319020b45d5114240c0c0d2084a00070882d01c0201901a003402d400540000b0b142020f0b02000c1441000c03032003c00f5180700315621a510381d20360b1410303240702030050074480350f03006a110100c01c00210040c0101d89100001c40440d03440300d00c424014100210110041e11207241e0003003213201128000308076080700341e25003444a2001c0150a01070000d00460b40064820f185021a03039414481e528854416a602205c04210041e81044844370341c2c941120004c020a2428010303105904c0c02c3d030514203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 800253606 1250 800252356 800252359
    0x5090c1f210603050312071b02090a0c050d1b08010905100b2a070504060e0108030d091b06020607271806030507090506030118080904020a030608150a1104060207090b 73
    0xd016070740341d44045c0b0f5a8031101d04116900c0360303070382480300c91030b4403112481601d001e80c100c2001e845141d800040144a0245c02140310903035074000141c0d541d00420566440d02e0300480c00304038072140c2440b4501c5104011018000041b0900000305081609110b08c5019604003210080a40d041c08084480743d80021903141201443c0240070452031841e60906940706e020001a040c1c44d0b14000a000c15200280c00101e290111070006201300c032000016039070024030340c072000f081188040c2010051071003c4980000054030351800812101d800090a501411044d030318201040880d441d424800640f500c3d0b040c901c400324540c20400328400740320f0b603407908001c03800004e0b001d99240d40b007600c0c208282c0d100006064484042204c91300d0288600d100d0140d000110406426507551900c0305807250342c80492007640e0102e440c0c880c452095001c00050581e02003101c1000000c0111010032010894441601c0c506040c3c0541801154070700b6501102d0700d0390003e1081c00e08081c41e00300640441c02c08035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 800254856 1250 800253606 800253611
    0x11a09030a0c051c0201020c1003060314011e0606020a0210020127050c010c03080c1809070c05070f0b04062a0f0b0105011b0803090a050105090c1f21 66
    0x10082590244000351038184541020a6034030310b0007050104c0d8690090300c0c0c55002e8996103060000d40d030041000029001d00f02d584045500d102c000030b400400c1c4c0342c0c00103881c2481d10382d02c0d14404081503100403418580040d5940d14240741c03042d00b43c00d5030494080c00006800800d0324078018105921844461001030001040a021110050403481f40107105031450403050442c1d003050100034007079211043c0013840c080300c0c40681d035280688100c10251084055441c002044034030b8218070300052071141c200402a64550400302c000414220842c0380070388641c0076850700000e00c0112070204204441e9841081802c0030302e46a000d07961140542c20680503001120b00c0807a602541e001101031051280c801c2018481543c1003000340d1180c140c00550501c101309407180c00444038441c0308002d1592050020f586c039a40c0c1070b506800c1821340d54000b4019801c000134881070803000308408404d007100340e903202d21a04503c4c8010810342a400d0182010810402012a01d503500c200d55403440c80340200003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 800256106 1250 800254856 800254867
    0x110310120215220b0c0c060304060f1509050f01060801051509040c020a120305010b04170f15152725170106110d050c1f06080c0306040b011a 62
    0x1d075035a0364481c03c03d40d280b0703140d12006000a4402d004542001d0300101c19200e00f0301005100190342c0307078a06c008251080c940800014100555508040502203054105000c000030301c04a10311030142500540068500700000100030300340428240e41202d40e10340e00e480c5681d181c8000d2140d401c2d010003808082c85030401610b01c580d240c42c0204000c082082c0d000701b0b61064107041242c204417010080408150502c00104414040c40702914280ea800d4184082111403e0319240c2c900b011026000c2c4850150340d1840090050452406100300740041840100c8008101080801c50b1004911052211050141c40700c4000316101164808840c0e804254090030503150300d03560450041403040095500b49004079038101d41c62009005040c00d080c0400c09007803150311780c1e80352a810318100301000000b0512004469041080207440c138a440c13810a400007200850360003610042c09032101c1031042c210100b1141c00e001442c2c0748141d401090040b546d90070404000b0100d483c0304002d01501009004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 800257356 1250 800256106 800256139
    0x503010c0f0f4d0a1226090f030702061b0c09090c03010b010e03030a030915020f04050a0b03011a0304020604030206160201020d210e16030305030702011103101202 72
    0x11481d1103103003000c00c50b070a00100a840301c030b1160700e101e80e04800c03c4440c0c54684240200103004c82d1a10740c041c00b00a440300c0a000220383c41024910039100103102c1d0300d00003443c04024001c0c0c5000300c064405031403035000354081e029924490890002e4103c0c0040050341c18000340312030010a080e0102060796165001000020304d012015543c104140d004a15102460310b000d10550743c040a0a00345150444081000070341c0324090741c4c146405050700c5004182c10428901d43c1c2441040403d0381c00c54850303060000c0c0b8001c0f5002401801e004401c00b490104044400300e041c2c9040b01d030803035811000c0708129000284c1c1d035013010b08200c2e0400010300c004001655070001511512038410056100d1a0050000a2900350204817080c1030000422440b046824043c0100b810300800c03603c04182f03002d43d000200e181034001d40c003510062582000110400d68008001d5000f190340d5402442510441e09881c64107110544288944102c0910204044058020503950442c001803035070007210f05652 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 800258606 1250 800257356 800257397
    0x1813020d020c06010e0615030402040209040b04061d1b0306060c0340080c01181805070801150207030b0601050d09050c0333090703080403110405010503010c0f0f 71
    0x31080340043d003000005010341c1c900c1c681307807952145044410601c0201c40600c107000c2d034880540b0203409203400042c002c4040c1c035107800844125101801c100b002c02c1c0c1c0c1e2080300c00c040381c12101c1040400d000d0000300f03041000c0c03107201903803503540c0d144010300d1525008204102640902e10749a45400140811104000c0c00100c0024400c240c90307100101d00201c4221041341c00414100340300003005034000380301340710001030b20400480007802d0001640d911b181c4821964402540301818022102e91a4220318920750015401800c40c0c2d00d40c1940d43c0d0320b40c0d1441e009030208110b941c3c0180c0c4001d0301000481c140481741c2d504441d060400c1031411100d81000010345a0784642650136901c10100c2043c1401c08001c00b812041401d5a049003c6041045407c0c1e10088556000141a0904049a130449090020400443e0712001d0700c0e60362541c0e4580014607484cc0803003103200720b01d0300300001190b04040c00f4280c0240c006946510cc40c8034032800c00e940d141c0d041845401000b00d02c1c0d02c0c06106800e0700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 800259856 1250 800258606 800258617
    0x6090414030f0703171515090a1e21060911120d02240105040c050415081e01080303280608010e010506060f0313050a0f0b09060108031813020d02 64
    0x200c2d1076940c0e80f2100e08000d40000703022400c01c401d01c4c000c0c00401c00b000c41201c0e015110000100d442408803e100ca000f101540a424101c591140c84c40600281903a80007107064030140c0055020101550358501d1202c00b0082d40c689a944900c000d0075903030004065510440800b4880c03500f80d204035945070041070900e964030390701c50304940c0102e0020788455010032074410101c10041d40d0f03002d113200034403c0030504181031003942c2c01145c030b0b044404840b03405802910081c080c2c1d00340e0406942c0311500b006010300000e650682400394140510248080c00c01503207410307110000c0c010f52450301c0d2181f2000d45024103842616203004c3c034001d0011550494000e80c1d00901c64040082440e05012102d6402c4a40c098420742c03043c5000c20405006d440c0034010b895102100c46010b0a00b000c05091890414040710b0001740f60340301e0039a444d1700b000001403c40b4007410003441140c0550b81c9915085540b40300c0d1003441c114110b0300d003040c00032030300d0301e48800c2068031200400542000002135040081c1c0e0000d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 800261106 1250 800259856 800259877
    0x210304090e1c170c04050112020702060c0303041a09010c08150a0f06051209010207030f0c0303090845040b0d0b0915070e10030f0905060108060105030d020309090609041403 76
    0x45008840003e6002e02c60a4112100810301031410707282000103450b28204446040d4519008a0309405540e00e400a03210305950a0003541e13602c2c0ba05242110301c41401040e8000d4020721400844e00d508814851189501110b03100c001250b2951300d00c4c8003200a050507607a0340110351010100300000d58801c035200a0441d41c8509480d08031700d2380303e5940500300a003001071a07803041c826400071a90160548003180502e00380001c1c40255400c1c01ca001d003440180c058000c203000a440e120350700b1142c00350000118600c4e101e202c5c010080191300c10101c0443c6a40c41d2540d168500404545860303402100a40b00042043c0803824031aa5005400c0400f16040110364001c80440506494001c0c41d09500a00700d280c05c950410071a4001001c840000c1499800c01d0b030703100100101c00d0301c60303400081c0705a008021246150313501e4000c103503510310901078035020f401009411115503000106a40c204507008006034169611802403080c400c00c000c00030354051040300c2d040003d641082c0001c1c54455103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 800262356 1250 800261106 800261117
    0x20d0c0f0b151513170c0103020a110105150f100806040b1309050709110f0406030216050319021e0307320c1f170403030608100b210304090e1c 63
    0x941c04484040134005901201c20000b070340e40b1180031100c1c0401d02030601c0b00d090074010b071039803c6220b040340c0c101c032001c100714200d620340000c0c00342e42c021018606041c0e042c11203003559a103e00c1014440742e0100d008400c030108205001180760b518041d0020600400054940e80b02c0c0d603004080e03001501c018500554650300042414030a08000f030246e1702c0b031078210030901d515049c03543c1400ca0141c0710350700c00d61040503800325100f0b640e480032661229405810901700d0743c4801038180b8250039181c2003540c450140c81030601c006980212026844074076200c00f0701460421100ba04c03010200d1580e62182508500601c0d1044080002035048001010a4000500f00d00024100340039131003003a242c80d001000c24200c89904420740c00042c03840b44001d886544505a01d035440c040c0d000d820503030800d21541c0903801344000800c0071a405a28025800c540090001c40c191400005c0244401a40e07031003904104001e02800c001504404041141d0104460003400c1081c0e404608040c404d900360000342c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 800263606 1250 800262356 800262367
    0xf12010e060103051303033902010c0305010f0509040c0f0f03050114130f0f020a1503200f0310030501020f0c010b041515020715020a03020d0c0f0b1515 67
    0x24440d84015800305007070804100e1810701048014a0640c8003800408142e187c080c2510144032840340a01040307040000790f1400c604049540200c0c185600e070090045d0b00e0001c5951805119010b961304030303442e211540c2041350400c1e00744540410000c000b5903d40b8400880000e5a104444e0b46a005080610700400742c2415807403d01d0954110403241024501e52400707202a8110341c4007540003c90f4044184a90800945428981d00581050180d4400340650300003071190f81803140040f072410683e81c108148003c00d650b0319112421006c600c01c20301401d029215080715484000c50704000e00209048201d03a8907074443c1d003a85d2003240b0341d100d041c1c40420200c03d14002400b8288072004121402d200c611303500341040b48d0452191103504000110400a108080c2c02402448083c01c0d48001c108210300c010a0003030f507a0624001c046006101b0010314251043c407420b082491694003440503030500c00c0c02d0b00c51814814015028580180007216805810b42e0b0306685403610142d803444150303c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 800264856 1250 800263606 800263619
    0xa0602091002030901170a0f09150e120a050a0c0c15080c07021311071509120207060e130b131a030304050307090f0603050d050706060f0b071401020f1201 68
    0x3003107150840310955000340511015684c0112400c080000d83c01c032405000d54030450100090108000c40071b4001c0d103010340e10001d0001c04400a007541d41200d20a101500b52444e40300d5540541080c072240c0e2000038400840c00c940f05d034009041c81c0d20350b0720b00450a07241d40d0300c4400c95100c85600008170402410b07c2e4000d4150840301d05030740800c1003021641890183e80100341101180c0102140aa80e03035248541586c2c1c003a01511203a58007e5152032024203400b0b00c0b100142a1200d06403911003d2179215041c040c4005070007000d07075103996142d203104500b05041c011041014031896101039142c4051311815220088104d2000f00c02e43c9010442c1003415040b0fa0001c861081c02501a800c1040203100035280001c123002181e400e103d00241c40034a205085c80145031070b8000811500540c1c0241c12510341c40009000c0b0707540107500c1001603ea40d0344426280400714071510701c11803001c1c450ba002040a454503902c0408c0600005854800b50307505401255001c2110400d06000580040c403c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 800266106 1250 800264856 800264869
    0x601140105040b120406110f0c1c050d0b061207050a080a180b180304080304090c0c030c020d02010201110301090f0e01200c07080d050703080610141b0a060209 70
    0x412020308006282a00b030101c491544e20441341680c1d003072400540400c0c10030800b503003d01102c2d40c0004096031603050341119400d44d46d0003042c41c81445d2189030000c910188200c14441440700d099214946010249845080074024920340e450703002400344084c040868443c030449124034410381e07139182d48020300700c800b41c080314000e840900340c0f52400c1114903901f200b00050404c00c2e074101c00a00c0003540c9076466a0380003012242102c0541c000410000703007034240080680252043d61000b840b4120341000122a001c110303100c0035001500144250300981401c0381002c0d1064018070021030843c0a90b02c010312568000e80c03041e00079075500c1d8040400f102d120710a849201c69a02c00a01c481529202400010221015051308a6100040401e68136200f0000580103110001c01c2c1d6116070501d880c06040c0303402418060340450076100004003286408d61311a091400140c072411120710f940182403400390003003840408040405003c411a00c001005040c04881c400d81000da80d030791014051212 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 800267356 1250 800266106 800266139
    0x71206021b12180a0f0f0501170402090a0506030c0901030311070503030304112206030813080309101b020d0b040302160608011202010c0204021303170406020a0b090c120601 76
    0x6981c210412000b2011001e000b00c41d007840f8001c0100400c099014000350400c1940e91040004000c0302e000020140502c00e0003a048540036200c0f81c610700d1075026007440007401113400035841032140c80008c805070303020752000340c03c1040501104d254035072000100348100402c0e00300380d022030003803440201030300c0c42008100040c0000343c000e10700390704007540c4880d60410700e00700c2c461150310045070300c2c0342000e00d20200400e1968940000d01c111580d034149a00c40354000e01c2c90b004035207564600400d024400200316810a03d000d0b2464450345040c4008882c410340b103000c00c0ba40214030281c120056691840d100d2010303402400340d070500341840d2402903c0e140004039a03221408181008124090b046140e06045420b0041d070502c02d5081c45c80100d4200303c03401002584070348007049064a034840400703d1825284101006003145040120410719400b940c81820016480b0000f1040040c1d09403440641000f8000115500d840e2a8000104010001c032202c1e202944001c0041007207a030444c2c03001c2d8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 800268606 1250 800267356 800267407
    0x30f0a0c061d010c0509030a0b041a0a02030601020c040c0f1409030706050306040c030603021c02030307080301082113030f060209120a0b0a050402010e010c170a02010b0108011e051207120602 84
    0x14540506d1002094541ca003103200500710010480c001803d101581c00107400e15078400c1041c41d49850700003480c0d0000c2d0806c2d02e034180144a00780d6441614285441568640583c07030b21a881c0e00c03078025404a401585201941002400900140e070141c1c804102c04400703401d0f9a01c80d551245880d1080c8030841d1002c1032554100341c01e01d1010800341c0c80303035161946004943c1040d07899041032400401d02c1d5202d40b401c001d0604d20000300004406001281c802034100c060b204d000646001c1e600381c4007180c001d948a1140130002e004041001500d464800d8004e284034202c003506000c9203078006070f00c5210100801034603403c403080304010099815100d50784118001c4d020800c40c02c007500000c0204034002c000d41e0501a811040d18103010004903011805240c5240c1241d13030300e242e580024080d01d80040110b001c01d03175030000401c800c0100c40d0589461180b40040b070f05501e2a0500f00700036110082054909409544e40100d0451a14003c040b0041d009060150707403440c180240b824030000d03001d03ca1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 800269856 1250 800268606 800268617
    0xa08100e01170312012301140315150705071e0f060e011701062c031b0a030807060605271911030f0106020601120302030f0a0c061d010c 60
    0x24440366120140306410b41c0c045064950500040c201150702d140304003034030b880214102e800002041d0040d44804000b0301c80741c0c0d0607206031a000c0d40055548840800c0900b035038040c10b1001843c01018100b001d1034004000b00100440c402c81001a00741e40c0c0841001d80e515000050140008294041d0f07600301039407201000c1c2412031802d903810740212524040c078403c001c1005921400c980c0f03d24086100c1600c03840003901c00d035a4540e400f030702d511284184440b8010035050680240100c10300041d0f0310b4500076010f004483d100080b8003074144050750603a988020380520201c00301d03d00c04040c008040c801c2e03030001100c0d8103000411200741d0945030f80400302e02c1c1e24000054011500342105820081010078802c010045104410141800050040c0503039804010451b00900c22020181215415020344003c1e90300e0b50094042c8400f1004080c025a10070440c1c1d40303413003042000802800d01c280ca000b00700000c0e6940d65074151414003e40380549141941c180d05088800c0c42156510469414103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 800271106 1250 800269856 800269859
    0xe0a2402012d0203040f12090504050610091e03050d0305040c0509070c030e0303040506161a04030207031415090109060621060e01090f0803011e1a0a090302060d020a0810 75
    0x108401d400711080002241d0f0080085010041c140103002070f0b0680c4080d0503c90541c54120040c94540309103e103510487c20100840d01a003008030320051100c032581d84d0070300024141003250081c005102c0c2294101c421400c40080483c000340035048510702c5543c1c000c90301d07007081d042011900f41c0340c1c3c00c002e11441805050014064012800303248095050910700b0095041c07400090840c015a4002c581046000401980d4404041c0542802502c518a84d0240e08090040c034071f8901000c0f40d0003005a40102030900218415140c98011012440212191030031580520040000b003034400325026912808031604010030b23401150050072804448400100401510203048094201d005e0503041e03544d400400c47d98003e40006614036040714a0000b9005285043c2a40d54824890702c52400d0f40000702a202c0c98502c0c070040300310b50918290060054148214890560141441070113000303219400100603111500a06402400300700e0050b100e0350358010213850040c00038840320300b0384c030600710 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 800272356 1250 800271106 800271161
    0xc0602061f14040e071401080a0504020114070c09140613140a2003041103100b0f0108070c1401020417010e070b0a02120418060501050306030d0e0a240201 68
    0xc2a011241c0151000b544001d228000c81d00419010250280e140100075005c50b00d804001070580850720281d0b02c4c0d01241c2c0d5141000811901c0c1070318001d00103041e04c007403400201e008a000d821b5260040f10180307002c590302c0d404001100d1a64526094803010f04040001c2850140340c0b070440c201419100340040b042d404000307410080014115444c41d582c881880410010350b007004a00c803020f0880d00c6643c0c0c1001c0c00d007445042c0c441da0035140300c4c0c8540c103030b45414003410740642e000a10340078091481c0186514010360f072581c0c00410010802c10300c04100780219280f40b0795901031384042d000041e40c0b5030600309801d0519160032151012031f81000050140f249000074031604a0301c09464058071680108001c07810841e001c4e141d401c100c18003160120f01d00b950442405600220f403281003108070740d684010354840c0000c4402035415000702002d040c00f140070b2480280e54500040c00d914090f03449805c0080c60003038442640036085180d80082003c140c09101e01f140c4905076808205443c0316404 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 800273606 1250 800272356 800272411
    0x24060f260615041a0301140a0303020c0d11031e0607020c01171f150206130206031603060b13140909070614040f030b0402031e0d110313030c060206 65
    0xc1401d806001041c0612110109580544014180c61100f2004403180030040414607002801340080a43c03030565940c446150410a01d0704480d4141c01401c440c4144408019002d1a2440c0c00d4035103c0c0c0d50b040c800703c566002d000003103554240009510240d16510034061a100c1c00070419019944415004441c580e0804072040340d10405c0141c0f1800d90356000c1070000740358114510130300f02c000c00f220f003c95444030214107203c00b00f0051f07003118030035520396007805850428080082d41050b01040401c40e00100180c000840c240382e400d0100c3c486032b072000d40c4a030303a0703001d140031041006500c8410300c640114220311544991045801076594201205210b807600c03800d1250405000d43c83d911302c205c100c50b180a0354000c0040c44240e08401c3d6490901c016a8902103e040b4031034010f50528000e52804044554158400c9900501c01d40c4040d101c1a50b90f1902544282114070040c042d000c100d03407004241d42e014512405600352020700e011006450090064400c80003008040c0c80f400642e2001c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 800274856 1250 800273606 800273611
    0xb1e03010f030f0204090f39060518060d06080609030a0807300c1142100302030706030c02030d09031b0305090f0105090a05010324060f26 61
    0x26461803801003148000b030014120060010b040941c0805c1c100c0c00e00009040d0f0b050b22449040c823504500100005000015a02c0003801c403004210400600c000c5229401424a100382c0b0070b200b0f038180340d0100c0010086c6d04111640c0c1d10030f917182d0000b0f001c1803000740100d40d000070b28100203608242d500310002c1e0130400c00a001c00200301408195104444c444400040804196410303a414080d201403004044c0070140081c6002c03071101c48080312410400103600f0304002002c14010002030101840213000d0400466502e11018404201d516140002805900604440129011a6282d403040c941030405030b034803900a1514080b80c0728080c58010080f1200303003130308100002d4890070914003a90594030031244188c00b810501c0075002050341140c0240346000084480d500e940e298400111258843c40708165004400c0d00c6040080b94020f030062009820070201e4100c0403112410002d0b0710103007980c070030300000d400b011020203043e07007021012000e4218070740c160040c2d01c404203911104c01c102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 800276106 1250 800274856 800274863
    0x10b030604022a03030f1807270608101107030509040b010c06150f05031f0c021c0e01030b0603010806040f05010f020d140a1b030f060f0b1e03010f03 66
    0x15103c0c80c2180d40e84844910588403050903c031950f65024040c0c0c0d039001260803000601d40c5a000c1aa001a07800f5030b1025490b002006111050070300350801911103140d100034907083d000b003120300002e02540c050f5802401e00c2c2c2006040c00115503010000740d0700d030080800c000e058100401070200e43d10604807400c9242c11b07031340819103002413801204e10400000c409007c092400049400d210203188420b802c581c481401c12003440c1d103d00c20151101a4021031125110a03500c03003405030510b540011965240d50b005850400c1000e02d1105420b03560201100c00140d100c3e00305451035a00f5115043c3e582c5016101035013150b060401450317851001800290502c14002d864208101d0250803100120801d00e10641d1510710b1a007100015010f04c452040444252000140101c2d074244907000d0800c1011031203aa810981f04800c0e0300520182700d11412198540ea00810b9940d680307141d00f401080701c040025900d550f4060555000101d980e00700a403002c0808c0100a042116401401a07982 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 800277356 1250 800276106 800276111
    0x10b07080706060314060603010c2a020d0b091c050406031a0a0b180d0c060c1703100e130b0105270c070213090c180f0e010f06050603010b030604 64
    0x2840d0410480c0360281c020010321040c2010008420401c000300001c4040c038500302150580e84036607003090700381ca59002c0103500280400050700550b41e002c812031050900c00360481415400181c01144542000c2074059480550750b00500007140030400800d515140c40700900d01503440c08000c001c00503c1280b00c0c0c5800c00d40c407150031400c0b04003200c0080d51407130b5004140314400c1d070f0b4604ea0340c0ca064000d42c03111500c1c130180f41c024020b14105030184000e01c0b40d000803071046c0e050400b14240c400903e20341301a50042581480c003402c4441c144001c0d801440b4640650740f4003881c0050010104070020f04802c18021401c114000103507400c0701060540d07008450091101c14034091070590b420a1100d562842a4188240514442c49000608640e8000d036a0b1071603c0c0212854001600c280400003007000080c1780041000ca0030070603000c0c4c4810f04a5101044250094174014183c0c2d05480400034580d541c0c40e000c89141c610341c490000100700035554903046601d4080b003007115000080c6030070701654 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 800278606 1250 800277356 800277367
    0xa090201020309060f0904052409010e181f0614060702090f070c0519020a061803031b0f050d0f03090809060a0903050601181505030c10090504060e1617010b 69
    0x11707005000da596040018104114500c0c1003488441c074101d070448489802c0303a14614101403401c00398400c505890b6400d81c2c5015988070401c040380341d605064521072490203428611300303281a103e02c68a460102c12040450203a06184035909007580c1c0c058001d1061030108040c00050b155540225440340340c11442d0a440c3c2d8813000240e4210342002c80c002c04600842183d500e035125641e0006842d0b40c001e032048141c280c2c440406545d403071541540c180702d91004503c20800284603414142510440500105a100d025520030303078400c0ca1040201c0d160742208405800642d03020144150000c424942030008820545440415200c0c800140e0301500d030004030b400b9110700500302d04004541c00000c0714400c1da51944292801e04c00407411052079420508801428401c0d07403241c0c400e03180014060802c0c03800c02c80c1080b5003a440b4041c064140305400d0320000c2d041d44e442c85440018007105000480034640302d041c0b10030400e0003000d00d1051240042c0404203401d014441036040d520303242201a55072 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 800279856 1250 800278606 800278627
    0x150e100305150a0b12010608090304150201110304060203070305072a14070b0307080c070c090c0e120d0318030e060a121506030b01020f0606060f040506210a09020102030906 76
    0x1402c540c1d451074000c08414400200c1c1c519090003070107408140a841c01d6240d1b00e03080200d88080051b03440034a164400d0100b44401035207080c81000807881070000084515200c2c2880c080c641040b00d0680d20300754048208040030b41c05010f03066000c4040e14009440300c15103041c201c1301d0202200790580f203005499030703441000111407990503c00c160604442a4607941d40030101d0952048440800041000c00404d11181d00700301500d10803540200c400759a18100107020300281a1000e07088108007910b071106119407035448501c6040c0200002512950083ca031010702916882d0b002c00c85010005400400800d611103840010081c0c100d0b0481d66480e5035140c101e80c1c52026003078851506140c41207000510030700ca04810f040301c03490f0b18240400707845240103988030305846034951010781000001545503d00301c1f00500030001e1040b10b20781013070b40700d801003030325a0450381d40d005200001c0101c11000343c14031112554000d81c0c032241888400c1280d0b000030740360700804002600450700416800e461 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 800281106 1250 800279856 800279881
    0x50a090c02100902300a05070302011412071202090d0302280b060f01140a0206070809010c0806330d0b0307060e0405040606090e06072309100c0b01060801150e100305 73
    0x8817404c44100c41c004c08031410501c0e00d0710250f11080780828441443e0080310611030b4155000d90020103001b660565500e80161560101c0f0004060001d50801000707805a03603038a07409050314044d40c02003051b01e200c4940c00e4011500482000c2694105118a0001490064031554810829690f01c031400c042c1f50016607141070703440203510f60b881010404011540d8002485407156000b82c1d110010384d101e810f1030074200d5003103006180000c2c0002000030640d0900c0e1100c3c150713112584408401e0b480d84ea280e0030600340c01c1a201800c80f408001901003403041680182c40f0035503403c4010340b181625020029003468290040240225203034030025080c0301282d40201700505410409020b2526601c4810740c0b90a400c441d0580441d41c0068501200b80d116017687c0c820460000328a49024064010440160640203100040059810711000041d600c480058006c083c5c1c0e485241055040c880750740d01b5004440001c40400c450250901c03005d94900c0341400e490045804d001900703441d0003981e00f21 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 800282356 1250 800281106 800281189
    0x30405030a11012a030917210d0c080907080f06010e04060b0414070305150a030807020a15090303020705030339071403010608060f040308090304050a090c02100902 72
    0xea0310711160550050b60100044c0c0d00098440d03580c0588894071114180e03020301c8141600e026a500010840f5074460f9407403074000c10440b20040340d07401c2100c083c1304203042e1484040000002000fa0080c05085001000410302800340305010300610800d0072007442d40c6038014401c08c486110300401007000d0007103d5010180c449006001403000710480b4001e0565244151003d4001030715100000b19488082c5040c2221030400a21a01c0403501c0e540b00c03040c060b0880303a02640c2c808100035000410290032500c4551492850300c503281e455245060180c240f181030b501c064003135001005160074052045051030300b6011401d100800d014485040c024180030b07032100c006a14410300360040307040c6021181801c0c6294048000707122061b04c5030002d03519040191003640c220100200840c0c002401280a0f907030112890342120f041541e1840020940c0d10503a11807041c032542c0d0445a55410350511081001e003200c5501400000348903030204881c1c0f9010320070403008404096104000845052035002c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 800283606 1250 800282356 800282387
    0xa03060f060e0c2d1327051605180a080105040203070618090c0309120305101410050307180e2e0b0a0e06040b1b0a050309060d09140709050603030405030a1101 70
    0x105c040d151794545c800e10341148501180d601500d20240c04644840c010148102e080c3d04485521040051027940e90b500000d010394007000d0145110341e110740b180e440b01e1000300100c90000c5100e041c64018103080403559048482008411944172400200300441d600444224840010702110039940c118010209000014505038840e910107600541c96040b440c0520030720300b03204469954606060900b640390802c503031382240d00e0001d501c51190049014550140c01403d01440c0004455641000d022994001d0102c0810880030702103c40000f50702c007440c00c401402d00b02c1c0c0c0750025905198881d5070f00d124030010014000391040c65144036900003a81caa00207010b8688642d00d98480750100d03000000c586c00040003000700641e8a0350009041144e968102e4040c51a0036403c0b401c0c0405544584c081d5200d45403210410310000c2d03980c0d50300d1117400400c140500710142c10142804165000500001e1090f8010b120500c160f540100b064041c4562000340c5191008440c00143d41e000cac428400078 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 800284856 1250 800283606 800283637
    0x40c0e090d2d080106020601060509010210020d1e020d1a010e090712060b0702040e2107110a06110c0103060b090918120a020d090b03150a03060f060e0c2d 68
    0x12800b030b4000800034142e585503000e541d0540e8880c10200c07041d0042d10708044c01a40300340f4060a010f0513603402403400102f48803011500320a00c10681e00d141840c00b10100c070b00c41c0d0005040341d03020741c80e100b00918841040c1082e045c07003001200007040070242840c42846155208003165003c0c0c020624007950f001c003502d05000c40da07583c18084403150019541a8040d500305440e913204458042001c081d261104214800d0012105041c41810f8102d140304443d1603c50161080c2c1c0f50355000010402400c4954031010b800c0c111b81c0c0c803117080c100c2580845050508000c01840303a40c60034010307100a1141655102c0c042c0d81e980c0c007a500c03060710046259031103005030254210114070440092004082d11740031500c0311815000200c811140a02c41c01030b1250090001c541e41010700109025000300040c402d507001610307902e43c002200d5030000110b60903651070704104807240704034021592082c41d144489060148019004001701800c2000044106801d01c0c8004030560f02405d9030040c40040c0102c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 800286106 1250 800284856 800284937
    0x303050706060b342310202b051f06020303010b0a05070c0f1502070e010302122a040c09180b011e030c08010902090a03140a1a040c0e090d 61
    0x402401001c40400c040c3c4170b001d1a403810139407207081c1c02104481110340d034218080203200d08060690b600035074102c6113a100480210f06108c101c0d00680d41c2001c0c4060000245820145035081d4046006040031190106254041000640101c2a0f904480e04c80c000b817a61540386540c200e441e071050701070040034600401d40108610361802407100c00c2c0c1d24400780e0641c0c01d41c806181685e4600d61803081000ca160b03501d005000604000f00c85041044660b012030703640c1506800a0300e408010030210700c040c0b20202c4d030b00100c0d40c80c041c091995042001d040603400e4600781800407501c600e100b120019150b0300ca02d64015541d01c1003124002034440e802e5040d01600e011603000303001c0c00341110400d0005050f04004180001c0b0b501c2210700c4404020810580c00d807860b03958030b011010101c012140b6004101400d00440c5840020108130640c1d41c0d000a40c0e850302d440c0c03503183c3d40016000740480740c1040b4100034140500080c00c2d0810401810038404445400303003501d4811100c42503080c0ba40c19040c08 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 800287356 1250 800286106 800286143
    0xa06030b1003020907051201051012021b0c040e0c120304150201051609080a0b0a060b280305060109030b281a150409021c060303050706060b34 63
    0x1072030181c0740b080318080910f40300c0c0c1d0403c0b01d040c00707000c0c00c4550ba050804010400c5181000040316940903030b04010008480700c2c1038950072604007001d0040203281d51078a08605510512803010342010440b01006070816034501e4603550141c15810718040d00060314041203e03101002520700502e0300c4010b002c225180380344024042c1034281c0d100320340440c034040b02c4000a40200218419504040003d050010840d1207407030742c4400c05864010b641c2d56030750000c10030100c542c00601e040c0c070149500c90749400350542e9186241140d12528010549000180b1255a80c000c050301e080741c0e0860f400c17500c20b031034109404d110f00c1310360360300d100c1c00711100502c619800a8980082c603c40b154980000e821103540c0d014800303051520b14840104032810003003071050700c0150380035254072a49441c40c000f02d0301e0070000c69000c07034071550025004203074045a000c00304411409084064800a0b0701c4508140f01641e140c01c289801c584480c10b00c04981c2075803460a08580d044030030190b0400c8486228085094 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 800288606 1250 800287356 800287381
    0xa1a12060411160b010e06060d0b0d0b1008070f0501090501210f14160813050f030304030201050906220b09101a0f010305040503030114010203070b01090b280e0a06030b 74
    0x303d007165040480700000500b00003200307581d486030300c000c0c0c4102c6c90074101d586428010b0100e008001d0340000c4041080004c502c9184403d8421848803015045072408c0807401498650380d507022007031912400d9000d00c0303140d900002503001c541c804e00389021001002003440f03462a503030320032402e0740c24a0282c02401003821034020f120203400c2c40303842c26141d444680c402c1503140404892030000c44d03105804510b1200400480820080c060b1058a000160707a001c40390a40d0701c292400e50050b0b4441e024042450803d00019070411840c0241c4c07290100d075004241d40746180a1400f0b003881e0380181c00201c071200300f4014140e4074080c000003004954101d0190040d9002d0184042c0e014480641c4541141d5000b449902e0045030014000e504582c6012109214810881031070740c114013091041d42c002850a240380e5020f414451004501100d1500c00e0107400000c0c00400c0b82c209000240005820014003440c10984a111382030704c0a0750307515420701014082581c402003841e5800010400000280c9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 800289856 1250 800288606 800288647
    0xa030503191d090106080a0608030f03040201080f07080c0f0d15090c03061206020702030a020319170a080403080709050d050109020447040507020a020a1a12060411 72
    0x5840d0080c64009070000804001410000c043d004141c5070010b00c0000d000390416540301c000c03c100801c0b00740c0c881803401d003190805a4010501c20000c0148411582c21408980c2c0c05030202003004101e03d41080010700ca00d6000c1c1402c107034441c0020b0400e00c00800700088400c2c01c1040c0c0000d00150540a001034442c60343c6100d4201e4040c601103c20030018428000c20f011100100b00c54a4508915201d445c025885040100d90500c43c9010110043c0c50601c01442c070604103991036140009103081880c4460089032000403030060070002050120341007106290800d41524042199a40380d10f410f5804a0050b000282d0090b1548030000800505420098001d40f0075203080c09003158084180c035071513132036209034a0303044002a00e040d804c040d00c480a404c0c107855002c02e140c0c1038184a0101d0700f00c460603203203c40140c20480c8601c0a50600d1102c8000505081c0c100109041080f48229894000c1400141c078008181c8041441d540d1641c0106026480e42206290368940d1030f074000e04010480c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 800291106 1250 800289856 800289907
    0x201020c04061805090c0d1506120c0e07261e0a09111e0907050904150305010c0c0206220e01060525030203030112061b030e2a0f0a030503 61
    0x2002d0000d4050031011440c6014108007407e45842017116640380c0d01d2045540e4485d15200303544d072030001004101c801c2284242c902650450444074204070007845500001043d00090100c0926030031a8503403140140c1d051081d0380104455140c841c0c9449a84052004040d1084445842e0030301070b00110661281010758403e00c404042da02200c1c0074840444800d01c0c0800215240342c0088800e400c00480e13050303012042d0302d00382d4980695900001e0031075491031100d0074803030034850301031003040f000348203c50a080450412800000a07940055811700c200d08044155000780c01203600c008003950075041c040e002e00c0140303079003d43c0c55150041c140e8106c541c0d071000c490103840e9035030040d42d1313402031001d2440d8259000d903185a00306500220142d0700701204490702903940c0c40d8aa2088090420b0302d4045030155000b24110004240d410719007509410748240c910a411111040b90054402d020842078060712552440e0b040030340016a40c8200341e0000e00240800a90902d00d1203c89182c1c1841a0700d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 800292356 1250 800291106 800291111
    0x9020d0b040b0310092d17030613110408120c0606150d15080a12030c0e03060f130b1509010905070e090a1805031806190c0201020c040618 61
    0xa100070403080d165020400c5815400560300520801a03580010b21082d01800001152618000a0040b26071581e4840141c58000440c01000c10400071f01c1c65104400903d940c80c03d42c24010b00180d40740c1ca03c00030201d20150303901c90342c2d52081c400d1410f03035000b070040505031651155180444002c5030310075030f8050750300e004950015490385400420b002c05000084141da05107102a04400020302c520b44800200400c00000012548000c01c43c441c42c80f441884150b0301c8243c810707000783c00e80e6401344c8480c0501c480310b101c0c040345460010f0803540c0200d500c03500394465207911304100c641c410b54480150002072000108003020b00c64070006c12500078203540362003481c0c2e0380d000c0540c203c2d002554250002080d01c500c440941ca40800d810b50400c2007a900052803011a4990610b11190004126a107410128140700b0306c240307000755119910029940c0d00d103440c00941c0703140140e00107d54810180420f201008095901c01c020302801c100c4040c000300106a1141c1d110200c01d003a02a00101700350 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 800293606 1250 800292356 800292371
    0x6031b0806011a0a140d0221161b060501120c05010203030609040303090309230f030c06041203050c01051311192c100f090509030414030a0c09020d 65
    0x980c0096118100c0d1034820f100b44640500b2000d03820607500401001c0200400c00284d81450641c1c2e000420b1580c07002c1c05e00503070302c134070b102554955440b1001402000d0401c4800b0010055008180490f00d01414601010061122000304000c80420304000e00031500e84800802c0781a00550401c8045000310410711640380c1d2030307004980d6484200c5240303400c083c580c0c02240c0004e020341c10004420f403180c10202034240d11070704540b004481080c03c00000140c01c0082a0311802c040d0605007500314285d0242071000300d04000300c0c2c41032055104413690784842c01d83c0342050502c035500752100140002d0080c0440c0c2014074036030b11038004110083c2c4e035500101955100d940307400ca0850301501900390070f0400080c5003a40e00385c20031850f0101c0e9500986c06000e94851003070389201080c4102084c010761240e00d070030517024200001c0c2d036030006401117262000b48450280004265003c445084071451310801840703020a052408d0340000400c0c0405010f8081a1f80742a0303000341103004601c040070000d04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 800294856 1250 800293606 800293619
    0x2070507120c0302060a0e0306043f141902070302091f060302091210240e0c071a070801240507020405090106030209090c031b1f021006031b 62
    0x42400307001801600c1c005420401030410401420b9840c0c04c5080043c4507150300004603003420011203044625000000c11588003044114038808120b950041c000c50703407a0701005441034808500c2024007031280b01920700d800e0b06050b00417100b00590000c14203c10041c01c00010f5036a00280c08120302c24500100090211403184400301040c500714844050128074000d004e034029400305039516005241000e41002c106000c1091220302e550304400081d40481000740031000000c215020b04400e081c1003800c0103020081c0710225080450403943c1682e404030f514020000c0111801c0d034402400d00c4070200b1865540200209040b44e1100c00c070707484010500072000068812664004011480c103110410140c1031a80c4042c0c0d00400d004000103940380ca907000030b5403581c011201504187c4c82551480010b0030280f240c1100980408000301d142c0c00e00360000740d2405101130142d000300b003003802207000c600c0c420062680f0590400340f040103e40c3d00da040ca10740768207108d2403040d8a00e20134030002803103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 800296106 1250 800294856 800294879
    0xd12090501080c09041a190305150f04030809030412051e0d021515030111030a1413020105390c0a050307030b04060209100503060f0d1104020703030f0c0302070507 72
    0x35030f0074003526526020b03901c2e04102c018a5a59040da0100c2040005201c41c1c1c2c039038a0141c481c4080715030228400310b1561404614100c0c15002c2202c51440940030710409038240c19070a07800c9541800d0101c0280ea440c80d5981ca980030390fa0007000c0708a04103181d1030a010b4080780b2281c481404500c01201940f1440c40c80356224516408003005074080c2d80d01d044400b41c07401d07407039400c00300030440500c2105061002070700b500c18024181d41d407418004103000700200b0301c0c40f50041c3c10f00310a1854095140551080302202c2ca0810040e040c860b000462044400700c050215294000b501c16840580020500004001c907160280904620642c1d07004016840d0140041045500040c02000607600703603500d0000071000a802164000d809210b40480c03030391089200c40000036540ea84685070310300101000304c030f5400a0f05240c0100160741c51080444c081c20010000141e00352005a61030380d0b2481d04800410b4141ca0011410f807070305201140700e90349030b002854094006c404943c08240c503824060038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 800297356 1250 800296106 800296111
    0x9120109020d0c0e070c03210f1b02100b0312030402130c08090c060c030a03021309090813090504030f0302031e1501030617100b0a0e0f0901050a06230307050d1209050108 75
    0x4103a85100c0c80300716003c0618403416400100001240703514009030382c9d009507080c414110403070014142c0407111581d81084940e441c40760712081802040c041e040825102d4080000390300a0400020018081d5210801108482d4410076010400d40040c50001411600e00307450b040424000e0b03114000580c600079066841042001d4040c2d860000c010303005070700a40c0300300814014903240f00c90000381c08215104080d05030740194041c03039641c1104140d841900600340c00804000389081e05100c0030030b62041d803003e251b41040c01d00503a24ac0754062074200084e035842d0030750395203007203201040308520701c403a44810743d19000c0e00c051002580341c0d82c1464a544001c1c0c0007900035441603003100c1c18048650041840c0700d802400e9038034100e03101c007071150540382d0480d03814809020b84014810348030001d104042d440341481c4000c00c201403c2450148c40f0401c00600405e0b031140e903000315601ea0345c091001a008100c014022465004140b62039502e000f03018a03510086404160005081e5004190841c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 800298606 1250 800297356 800297363
    0xb180d06142d09070807030303051b120a0b01090f030507080d321209060411100504141c0b070e04060302010e0111010e0601121b050609120109020d0c0e070c 69
    0x2511242203441d0b80c503200c0c0d00400416451040711000100d12409000800245000c1c1c2d4000c80d2901d881036412a85500c0c8900105c0d511504100c102411030155540d0b64110b07020b0200444c4003c0d40c4c0004030366100441d0402100c7e8003200710000100040041c2c07500844142009580d1014104030341030320140c2414040840e6200000c03001556032001e40d9035000d2440640b002c85050501c007100d640d840203401c0324203010301d90014051105000c0708809400c044001240d0100703020443d000000c01c1c501951049c0c030502d00008404030304030798501c0002c03c079903803480a25801764202800c010201c2a8180c0f402004100001e071603282c2070816000318070507281c0684840a01c11506001102c10920351b1084000035581d4852403903440c0403c1c002107009052441003c030151003182032a202031303682140210040c6a80c44010020390300c90500b61440c50000321010b0050b2133010302903e0141121082c0254000100f2000b0300401c1583d148070015203200b0315420700d0320754401c141601d50b1003a1f850042c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 800299856 1250 800298606 800298661
    0x60e03070c0e010312080415150302010e09010807150320130b0309070608040515041b0605030610050c030c06010e0a0501090b131a090405010603110a0f0b180d0614 72
    0xa0f0050146c120503400c984501c5100050307985070715080c0215400c0007492440b1460000b0200150341e0311203034120000703800710b81c042d445514003000c4030b90700e44040c80342200300c9200b090203c1c00e42e03000c0d07802862040b410400b010050100042803071340d6a80610316104000380c04140109038007a0042c01d5030312a0302014010001d031802c2c82425265098010002c44244c0700745003031400700c1c20312401c046004500c200034074084411050102e44c2241480e0f04580100708003841000b805907500c0c128840d01c42e0341800e046648110075041241588034403462a02e4511990303000140c40c0c84841c01e045e02c141100fa404004990703c6040c41020f940000003101d0b4468a80d1900c0c0e40f81c2c449950020440e0742c5500c1108003400036400126100300c2c0c04131411780e0281d545d81410418040c03d00d091000c91314084910144050511070800943c4210380140d902c81d1402003590b1100b15a00110404081001407985800c6a11460988050700c29013000509554200d4003040d10904120b20b1800302c004050100d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 800301106 1250 800299856 800299883
    0xa060f0c14031b091206090f0f0c3307030f030b0121020d0618150602100c03020d06080a03090b09060d0905010902040905030a0e010f0801090b0409060e03070c0e0103 73
    0x1215480200700f606500e020000c010b0001c242e80d45226176038903404100090f200038070b0030100442c140700702030b0700c20419a000110050b000d50740208506117840401c603500000c2c0c0014941000c20490303170b40c074942480918990390300c5150546002030300c00346200e80e40c0d511084071110003c605a41c03400072600c2c08520039a02c130a0a02c02c600b010061562010a401070078005d100f4a90411b940741c0d0b42c8100d42121603410a600c01108030300680c4403d00500c103030088294a4410000d545014512072880f140c0d903600c107824101403103a01141c41c610002c1005201194540d5166610303401c01e010110082040c0300c1002400030880015114030810040001c1c2c00c1c200da0003c4000a0495604200d695550704c038503070710050f41d4510810828a020720001c684405401d00050461003404110360f060000a0a040d00d02e99403202c00d40c5c0c1907e4440c100490043c44032404200178008211b001002282001c0c6001d0003800d0000150003d0790040031074905840d5205a0150030010a000140002088c1083c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 800302356 1250 800301106 800301121
    0x20d080112020d0803070903110307051008040516030c050117150607111003060317040e040206160c0627240210020c070608150a06200a060f0c1403 65
    0x84071103000c0c0054158a084021940c1d20f25299004070f68480208649581c24401d000c01020382c410501e00c00d60040c074000b41041c0005100341080240d140410001c00002810010103000305a09400030324681505580c4a207030050034101d10b4095240081c03810041080349103030158a060198085001310500c454034441407001d9940049001e0740c1c402c0e038000c0740c1ca800351a0440710210015450b5400034250742145000e20b10709240daa6041203203101400107002d04101078071280c0e00181d0481e01c0f15039039041e91080d1950f1299003403000e451701110450000308203410032458a003026210000c800440170070103036141600703024029003140549522010083c441050300125a071021401190051050b080d03800099a00c990904070250b04120ba0403c850f0b50403c810310f400c800c130411071075020913415010800800c20b40c420700b01004100c00c9661580ea0748803c5041152142e0810356641c404682844006451030000e0642580e142c00c0702030504c944500a0303100900f000e1000180345456142 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 800303606 1250 800302356 800302379
    0x15050903190c3203040e010911180d06180506060102010506180417040e0106020c031b010c060c0905060a2d0f080601021227042343020d0801 62
    0x3c1110196035034000949010f46801c1001e440200807180700e085540d81051038440584400304968104200c05003c0049182900d2402c0101c004050342e40d0054599141010340280070468002042050025800c0d0103120340032414600c07400c400e07002404103449280c02d202030301001862480380c040020002c24000741d0b0064458080000300c41c252030819495a48520026a00ba4007507000359000255a10190034144001c03a130140ca04240451614007480000c0d15070141098003d00c0c10340c0c0d03407449881190207200354034003911014291540318241d403c0b01401ca680201c0c4500040b00308892041d00c05d80c00b0001103051810350b035854503512450401e064907810006454241980100c960b2508450545c001801d51601442c0180c4c001c8914141140a80c1701072a070308901460070b2000303d40c2d05040d04d00705528403000402e9080c0c5583e407034060500e1104040304c49040c2d40b011b42c1c58003901c07000500d2503014618031440e4080340300410710799041c0c1e50f03519a1050315001c9007072800100148800b02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 800304856 1250 800303606 800303663
    0x108160c0828050c300d140c090301060e060f06130b0706090b060307211b141017130f050f070609050d0503090d15050903190c 56
    0x88907403180303060034582d6081e404201030689030005201042d03ca040307040400c12040d24815040380a050394950400c0401c07016800c142e00401c03840005461180403c0b960721140c0c07000090a80350100c0d0502c00c0a4510302da100352842031096080040114244481e09000e42c0030300c400501d5260200507020500c4110f404c000403130800c000290b00001240d06110b0000c2506a10810001980c040305150031340031050b0143c160b900a034000c460501040c2c01001c4070720800c8044001500f01c042c0720b4a00800714916440b62035155643d0b810300001d191101c01c1181c071300b40f08100c8080c05842149201100d10740070805488008200d0440469403160307030064038000740e501594101a441711251103892078103951301d6080c0c095610258081001750b07849050702001d071804071128200c610281e102c0030341d40d00034011401d21074031510780380c0c0341002071269803491171844048082c0301c68504251040d48a0f040030b09a003803581099840310006600c07490f00e0f200d01c0c0d43d10220940d2079000c0324410708240e6106 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 800306106 1250 800304856 800304877
    0x151c0828110319030b0a0b0307030b0a080f07030204023106170c07081c0e0708071e0e09071e0905060a081b0301290316030308160c06020403050105060108160c08 71
    0x240b46d000315055034010010751048803503483c0410f110b5480c00a00880d08601e81c00244140c0007800d03034510100d00880c020f02200e40444004d0380316041c551544071255015041d00a940420400c000d0b07254414a00b04812602103845442c540103031500d1102c0000d00c200d803d5200f64a040003580c00295010019210300d1102800001c041c8030b8660080045840c03500da80714955226400800c180c00c0c0c204500e40103070501007907008102c441054264051103d42c041c005141003491300056581d402084440010019480b040b103203214540d441c1104800c1c14010030f060142483c0000303074107051444280b41201c40302401807123407070440c0390b1155890034844035844e819522100308001a0080070b03105883c100803d510f0700100e9007a9030805140040440a82e6041d101030f036030420200740c024580c6603104122908110403056102800c55216400b60701c0100160710119010040c8003055200922400e02030300ca07520705803500140b07a02280716040100c40003d080e440c540d400242d540005c4d1000401303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 800307356 1250 800306106 800306119
    0x7020d03020d06030206070803040c050a141c0b192702120a21081b040e090c03010911040c09180f090c0306090506151c0828110319030b 60
    0xc03a5400078603580e21247d070990304954003200344401d114112012100070f1008949641078245001442104040000c9001e44144416401e103e1040400001c442c5030303aa00204254481c540410703440d02c402e001905505250f840d040c24404100400e1040368841c88900c5404a020703002542040070000700c41c4000e4580307028107902c07400015407156140300c2407030001c84100f1f1350900c2031600400b190802018540c01c0c0c1c051199444094010388222820b41d2043ca8410010f0340c0e0b0840940e1800150040c600d80540c44d050030081402100c4001d071440890498052008c0d0101c4131040302c0440c0540a02c0101e0500540844400280c1d9802810100019400420350b82e0341621041c041100d907920950f007190702c2d8091030003080002e0107070b80d501001d10700b529525490958081110ba00c6500d81e0101c0c8001d0490442041c0030482050391130200031800c0c144034480315503540655105901e410344d00403c1000030250440c080c04400d80e49150000700f4120740e5100410b03000c501a01360000507e82008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 800308606 1250 800307356 800307359
    0x13080c030a081b0a140d030b330f07110f01120510050d0809011701031e170a020f06090109030219020a150c110405040201020309090411030a110a0e07020d03020d06 72
    0x401c00e1000e2404d00d0b010381c0c91400354904503000941488051052407041501d401390642c3d0382e907a40c2c44442981c0020380444d1103c01e511035202e40c030170124840610303000071020481a0000c141d5200806585100300d150303401542d00c210501100e18400300036580814400025108d00c40819440b1540c00342400f00320341c162580c3c0b0408074807810036010060354138020026542031196046510240d0054640002041e20341c90b6465020480008405c0307000400f0f00c40515a05002060141c50140203840d1911a91101d05260103507039180318135003540c82c074024000004c1c1c03601c0061003080700700b50301600074100080103d50030282e00b050203041264045c00800d40894445c01f21201543c241d5292307190000783c071580e410217401c40d0520882051040b0700341010040140d070302000707071426801c0507905408940c0f15460705022801640549030303014462030007004140031500060300b9000f441902c4400c84d40e601c5006800f04220119210400b69000d68210b00d543c0b84254001c12088406100003c0ea09 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 800309856 1250 800308606 800308657
    0xb0a0b0313062f0c0d0f0f0f090e011d0906090c0d1401020c0304140402070c030b040f1e03080a050f070810030b010b041701050f0711100504060213080c030a08 70
    0x2058101c0640780c81c81800319560300341903010071040714201d155081501c0f51b004544001041e942500c0d51080822070f460640300740545c000d903400310160130300501188a5685682080031348003144014000c0114480c0040380300c1c000045105030103209480041d00c1582070710010b00c400107042c00c1048403c03107909208490002e0082c80a400c0f14094800650750b40da18000007422808030104145204030710401100b400200c82460180849500890400c40c903035450605401e150030b0510080c01c06000110000440b9800c0852001514400d807115491922203403c4034080b00c80450303001c0c2d200f001400c0030561050184409552081064100c00805911f03690f0b00086074070280d200c82c640900204003400207035081c044500310114042c0c020862450320001c803080844000e4045818844820041404514103100c1d42c0320444e00d019050000341807030701c0c2820081d8000001003008074403c69000c128114007080500800f00014000c0801040b0b41d101ca042a601c04062116410260b00325094074 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 800311106 1250 800309856 800309921
    0x181203020705030f07081605031506031f051006031404080705122701021605130906020705150907030c05060310030b070f020120030a020d1401090b0a0b031306 70
    0x3016400c0d0085e103040d9182c04840303446d15150300d000441c0ea480301c0100f0302036a140043c10048080700000c07400810703110040400d0800601030107201041c0013052001c1010314007a08894007610141a0360540c0917a10744e4124116000e00c40341c81e0780746200700c020401050200c4040d290050042c425100780c0f801078004032005521003841800040c0d92805000d101c06005c000401c030500e0280094030a0700550403036151490f03e5401180d1117140081040e18480b10a0303032004c4100c60b4003046c1107640b01c0c8541403040d40c2d103011055844540d40d5910016803d0840826200c3c1203a501c0780c01c000301181090100143c1c0e0b0001004a4041d000c10704000020980120206d4051a03240d00d810707150072032480d0000d09540482c02070090300d41c80c0c001550442c00201c0112603211a41c80342c0140c03100343d000c0c4100080e02c0c01d508080020640c440010840e42e0309a80b0100064404507041d46926559083d1428140403c8440d08000d200d8110b011000c54495000010a610040c0320800141c1c00280c48040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 800312356 1250 800311106 800311123
    0x2d0306020c0c1207050307120201200712031119020603010e04080702090421050307020a0b090102121f08010501050f1c02040216022103040b22090209040c18120302070503 75
    0x1c40344d0001c0c2003088941000d2250354048c0200a0300e144207805c058001800507801c030701003400c000d02c485c6481244138101f404000701409030481e04807000545410003e0250f40440c5a88425000741c05035200c0b4688086100100c0660291442d400c40c0c2ca03100c100b01010000900603030340103000301b1035000141c0da08680d942c415481215080c44041d190024040c0c058405d20700101400020020b101079603400040d01604c1c41d51001e0801d00d682d40c0c60840ca40640a546000c0400c0090314051010140713105103604180b481c010300f1a0041555a104507082e00da0070b00c181500990003100c15a0305013800704000311a92104404c8001180c415804034007264000c00b41060b05c86000d00b940310440c075141d54010900c840c0389804800041d0701d80c90058584c85035200c1c90480903000207440103200e44410103520b142049840b640010303a5034446440107903100100b8580309a1402d61140030f501d015a070040e0a5041c1898000c0d01c4d10304001c04451041001102074003544100d204c001120f5800b0000c124 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 800313606 1250 800312356 800312389
    0x80a06030c0e070323150402070503070c0512060411010305060102030c0714010905060712050a110f0709050109201b12070b070507030e010804020a1205072d0306020c0c 74
    0x201450f00c6940201160100c3ca2501c1c0800803620601c4400aa0948400c0e00103001244901c0c01005510000c0c000f4402c0c808001d18030301002c074101007031182c1c0403615002c662003960a1080524204c0c001c0c0c1d20303200100c500519640890010398141d510a6000031f91241042c012246000f0880031500c2c540030282d803100010f150050014801540e00404050050406603040c82c102101507a407080680003211507401002808105940242d118000a464a04c0038009a41d011072890405545030b00e040d003d07402c05203080000014101c0185e00c104220007041c200e261070700c0000480310502c150301030120303001c444220300d030702400403101484a1a07444400e18500360380d419080c034121403010030040204085c00360034000c1e8004039400440e1803100b01800d29210041b503031280b0015289032900e4200c1d03903460200e00d528400b0002c00054030000c0d0784284d010074041c12240900300d0a000002c3c400f41034085603c14003000010030b0f41e005019001c0e6840290340240e607038940421b5540800c404281c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 800314856 1250 800313606 800313629
    0x605090705042f040b040308030f0609040f1b1d180102030103020625060f050a0608070503031b030f0307090303092c06130c02030c070b040f0303080a06030c 69
    0x254208003044964018181070750140114850307603207529901c510600000b00519042c500d8030041c0341c0d4a1049902405486644903111030700ca04020019070400c440034081c001200c00860b06920300085020b1089501014801c1301000310b54541d80740e040150952100d50900d108007142c00b1400d00c1c03446c01040e07103102c28450b0a203000482403a4034420200b4038621644104010700150f21a54111810300080c0301c4280341821003500b000d408500e0b003000251003a0310f4030300c15140007000d51f08490b00030a0882c1003403200507200e1001d1900c402240c0b01d02a80b6600c1040f11801e8582580d0004940c209030805403400c210140021034509c1c2e2003141c50800180c55010144100b5810520070006071413140700341c0001e0324880011810003c0c0d00388403441c6d41400350000810079034031501c505880b002400c800348003180310710038040d60380d41154481c800c0760b020f00d580c0030904045040545007120b03e1080800761403032554809454504c005003442d0903c5843d03002c08404681e030105120020310000c1c007030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 800316106 1250 800314856 800314861
    0x8010c0806041a06030c0d140403080610050d0b0d0b130201110c011232012309040b070c0b09100f05160e18010b030403080612061b070b040605 63
    0x1405050024100351280f0b161401036588504003201c0340c4205841940c2c1e4a6503601da0340f00d4904980100005200d155041402c07070085240c96440c054042c80c400d44410303105454410400810058101100002840a11001c1100001500702c0074179030038041d2551300e031001613440b4403248400480d40151258843c1d450705086585c0f1007140d00250704150003825a00c038080c0002007034400054886e0341110b4a540c85291044018003020f406451200842c2058440180c000b00107401d09105008841c1403003030240018110040080f4003051005002041e540c0c1d03a503a50b03812288001d411003080101c0042454001545829058020070750000180040c2014040101c15a0b40040694a88900f40400d00060007200a441205181d06050001e40f204070311001c14400020940148125403151000150902210000710b0165000b603a40c01950799403072062291800080340c04001d29441a0001028688400d030064500050300814901e0004152900d604007002030324161086640e8400b03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 800317356 1250 800316106 800316131
    0x2c0402040f09050708030a0e37150e01030b01050913020c0705060307030504261b011113080601050102060f0a110d020304030f110c060d02090f0d05030c01181707050a020a0801 77
    0x50110540b030b41100c2c030304c454101c10300c00203680102428a040f49d0324010041413445010f82031182c006031413082c1d040c3d21350100c4920000c1c040340c0440700c0c0703e01192903c0184c00d810351107002200d02d041d101510003d058a4280c0c400d100940c03002041d170407107005141001c9410380d1454015402904199004a0b079410135041010f510350400d80c0c1d000000854400604803613560a090b60a15000e0100884480c42c0f02c0064078003501080d40c00110b0081c2c00115109400722600d0640c069405401c1141e545a80303400069989080a41e1140300c4406040c001800f036001c681c00c43c2d61000710000d000d6061070500f88000090343c1050b1012004075030002d40300e004280c0d0262840c20071690b02402801000d5100740410300510800785031748a42500050b021220752100c44507004442c0026200c48030320081d07400e282c1e889811007210143d0b0340d4280902d891000d1075107141c3c02c0c2155002459050400e00c5500d0030500c2c1e034860b0170211030303600a404213000566580301c41c42c4014980b020000c15001c010a9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 800318606 1250 800317356 800317367
    0xb030708061e191505040c090915050609060c0f010213090e0604120f03060f030c1701020c0714030109140616180501031e152c0402040f09050708030a 66
    0x40c07031007401882c4141040100345800c000e400c2a00d00c409000180702a00300d501e1400f166854001980150400c0714141c40035038001e070414100e990011081005001c001d0110407418503500c100c692003501840518003520f44100103101c00e200b003200312900d036203100000909a03041400200741c5442400c00400c002c46241c0075010200010001906141c5003c2c0d82c0c504101e501c8040900410198101d9410703654080e5008002800c0b00c1e441075401c85640b17181c100110303a8103000d0281c030710400307001d00b0140308414026a8480001d20300540813403400c004100d002403a811413450303403541d07d9030148400304080c0004800d40c06200e00c080c1100b46071640c1c180d9036030843d03501035004006240207000340d010561250300c01915024079001c90401d2841c00c4107215600410203a8058174504005c00c49403410390700301c0300201c5849400422a5400a5a02c01007165404c0e00e0800483c280d1380014005281c5540840b05d40c98040500040070f0080e5142ca618007491900300344030795400014074090303250300709 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 800319856 1250 800318606 800318641
    0x3020f03030c101b0309050a0303021b06090a060b0102120a0309080d0207050109140d35130209060108010506120705130602151003080a0503090c040e010506010f02031e0d0b03070806 80
    0x509041c01b08504035615103907280c2443e000502096400b02c0e1095000c5055419128644c090741c0813038916040518405482d41c4000c5021600e492410001d14511750011950f03107841200d4029450400149280030b8010b407203018021182c0c104100000c4d04088154805003484900400002695580030314004c400f6500c07001110115a1221500c021081d03440b0500c86030608080030f070040340c49030344070b540c005d10003a11040600103200d03441080701040d482d13400d80c410b56000703e5854116848110054030016002e002d0715421031810001440b040d060794514503040101458054948041d01006000201003600b0a50058101d411052700703040c500c02034203401c100440000d60752640783da606c540d203502c1740c0d20801c414840d010000414800c01404201000c0e04054014440d407a0a048028000c2030b0032075105000c585480407850b8aa0710000c1550b6006801d45510001c09a90112100964200f880200403580e15000d8201c0300e503c05010240040c40d007800200000d0800100122030b11146 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 800321106 1250 800319856 800319911
    0x210140906011e0b1c020417010f062301090e07090603051f030b220f050607020d20030d020d06210b060603060105120f090f06010f03020f03030c10 65
    0x2801000100311031080034500403a400d13138044907a20600450400c000100281d80104900e00c007007000602400079118583d6200740c01d00081085281c0c000c03400c4101c84403802200c00d040c01426001200340700ca400007001e5a1b00c14181440ea940c1d480c0c090b0403204400311000c0b80042c0c8074103000c02042d07816000700360300481a1224010038507031811070311000400301c0c440031381000610004a0441d0202200e000321380c48049801c1000100d042c203159080c1683e04508a13183c1c0b00303403000541c01070310202e41e1183c003914a9a0300d03c003581240032010301e4688111150103d9000c00c110b0840c1601c074610081c408031a8202c0f012810b02c1c80c1142c00711245512085010340825122880c000060b00b0480090b0f02c42d90171100740d51603440f142e004032800c0c000c002c005d0718030200040922840102040c14980300e107900c98115007070320440e0910103490700000c3c42801e20031071481c0018001840e010741500c0d90490090112414100040c10780c0f450710301c425001d044215658036910202c085030082ea82c84c4190b5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 800322356 1250 800321106 800321129
    0xf0e011b05130e01030303021209160b3108011425030b03011509110c0c0f0111031303030e0618040c050f0c160504060501020d08040201021014090601 66
    0x1180a44000315181000446080280c0060384840c009680c500b800003030200000c110340c0c990303183d14001d80258000c4c000348007010807030000600456400109404002c084824640c00039140075602e00464000c0041440740080e555110080300c82c402d4075030506007041001d80311100c3e00e44000c6608407100341c62000f800804c01410041c50111883c41c00d00400745203c2c10a04c0c81d041102c00301d00410800014079415420321540340c040854a001040a40c1c0d01c4e15010400d00c0c2c41c0001d425074078443d031003941030780d508920650411890052051a8080818100510705502d180030f40c4e400c5d580031201446801240700d41c1030003495400030070003004900c15141c0354905a152a4118035880307400c56564070440e140c5070303102100c91242d07055a48044003091031503140e44503407185545a09450390f24488000220b000060b00f4602402010100d59060300900308102040500325541c0e10028030583c15489200d015984005081c46029406081d0348200300040c10b0031101d1904101040c0d110320340a12 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 800323606 1250 800322356 800322371
    0x40209101401110138040b01170601140a080a050901020a0e04111b1c020303061e0a0521190f08160c0e0403180602071202040905030c010b1518090a021c0f0e01 70
    0x9800982e480c00080c038103086009e140d906d00004035254052004401c0e5400e2000ca005c00d81603402c820003038010590082c00344015030703454610a0803402102c00f06400140105258511828950b11040348491080c1c5464076120f228140c0780d021121800e46c140803503010f090101410103140030314800c1802c00303201a602d1400c00000040801c035408103441022041c540b20002c199503858400d0008140240014840540900c03003213103e80070010340c500490242461040c4c0e00b40011440010096224652112110b55a00c6c1d40446400c0030400740c1318580050084004506d0703038010500141b9103a10000402d140900d00140104115021041c507106054414806240c020030712005441401ea11041a14a02d00001c7c0180c880300c0c0780a0460301000900e042181010340104407001025103401c81e0341c0c01c0250f0084510f00c40e08180801d850741d016442e0300c0901e021101030350080701e400000340c01c15403940015004111342070700341045a941d501c2820b03146e80700c501540000094000007080300f003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 800324856 1250 800323606 800323609
    0xe0105190513121a0630010f0c020f0303060901060f12061404271707020603040c060905060c07060c0c03200406150516051501030803040209101401110138040b 70
    0x10300204060b403011690242c002d40e9a00b41b450280b0520503081009204c4410040c100c1c1c0010819038400720014000c42c208400e03140f00010403240035140180404003180c2c0307418800c40781c003c0740340d6032542000107280e1032010b84d070719900a09014040d1420070300000011481007008444090030030450b41d4060f0402c8821145208115080442d0841c89600d00f203203940701510003a200311803009521140100600081c0020120801c00392884c40e101d40c1c24040d15001081507030f0040765680714040d40110350070303c80d95200d0f0b001014024462203103584020340301c0c0d54003054480d2104840d1103070f10300d0b2000402c0d28541401707a10300800000100c4111049200e8004269108a41c02e00740b03001031070a007450400004101600b41c5104200c00020707556141e1529681e1a031050303a00780d00c0740c0c4120f404204891180c0e03407040100c8201a014100b00d446490055440480000321950b50303540c0c3d44200310344920380c1040085010480810640410f01186005011220340c00443e4082c610b03002d040c134100d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 800326106 1250 800324856 800324869
    0x6030c190f0507030f0207180203100806091b0d02060703020c090c0a090e060a08030a1d060301061e020111040609051801120305160606030807060c0e0105190513121a06 74
    0x555070549000320310001d001d04141c0c9006000c1c1d10048402c00a608008c050340703000d6000c0d5000b900c54204c6022080d07a02c42c100c1d5a14902500d06824036040010240c10403180d2100c55081404050040740500030b5a400050a5130881c1106a0140e000304c05084a10310f00072300c100d5071001002c2c1c0394030304210764060010308030103282c0140f00448001c2c00214006503126142c00004048071812254ae4aa03208401070407000c2040100340081184d6481d060308c2d241030401d503416189c0c1e03581c48282510f07140039080c2201141c0c002030710035075580320b00c0c440c2ca0b07039800b80081003d070520b900c61910071890316044c0f0520151801200010301401c100501c25091412500c0c1006d503014901039480b9102207e061034030051207040105210303d809000810018400d019000140c00b503078041000012840301550440507140010b40056030810445a0400c181c40000b07000340716500d4501d041420f800c00c04402040a03410003d005502c02104c0c408016000080000150701100030040b01d041040c0841c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 800327356 1250 800326106 800326117
    0x3060b0a060801210210020a0b010b07081e0d06171006031104020f1605010c12020a09051207030b180f1f02092b050d030903020604020f0a0506030c190f05 68
    0xf40e00500f10f000c84860710b030021090071381c80d0000c000007402c01d442c480195646c1040f0382c00b1902000003034000030701d044000c000c1d9400c00c0e404c600c1c040c0c40c001030040c0703140c0303008e003511182a24030a041c0b00c00c81404806200b804040d0205801958080c0c149a41039403510030b4201c0400c10a504181c0148006502144150034980c0b082d00c0258076a0302116200c1e41c5809140a00303102401e441c8101428840e05404c00d01281072107844440203070301401d0606080c0d2258821400103c0d41d03060041100d8106283e4403e100c10b451401d55050345d89960301c1803211300d030545030181e00d440c02000460500f40140030111000d0070510041c41104041200b4005e216507490340010003550100f00c224043e11644a01c0c4000d0b01c0c0c540b18103001e120b0710140c2401055440c003041e02e440c440d0b448441162400788c81404d05054245c1c004040d25911542001201d0350f8019860380c00411012000038281c072164003031401340104144580e02d940d000d0507c03006e100c1e05404e80804220207102e42d407030240c0e08036040300d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 800328606 1250 800327356 800327369
    0x160f03031b0e0f010c14010c1b02100e0103060512071701091208091005011701060602070f0b03040203010e0307050a0b0f0f0c130b04140108010b07030e09070e0603070903060b0a060801 81
    0xf81214a280058907610505000901562061044010b1b24001944450700b0354590380c8a98a80705411000e50303007815030100c0000c0d000740121410015140c0907511000040310149000709220f600c59010503030343c038403842c110340c4140d11810313041c001d030f48441d000305482c1032001001300150b4500c1c2e107926002c446541850b45c1440711031404a800e46405022120030816012000d00c0a540d5441c2130406140c0308608902840d4a00540400d1141c400302e00301049030403050728000f0031814842c62100702d40c40600220781c5503694151000a401043c00074020b881c2c0981c0c050710140755a814100c26469000300784180300342041042102202814804a400000100b03459445401401e0502c02c1da08032078021110703101d400304001814011420385d040c4601020307a6502030b1341e6a10b111041e20b0b4003410100501203604000829541d08000c0b030b1080c3d00c103a2920305440100c6048000c6581c6900c00d40d0038100085000c501070051010034014003503011019103c203404503203081402801d000060160a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 800329856 1250 800328606 800328619
    0x9090b0616050f010513050d080412031e11030708010b0c12070302010b0a08030a03060f05031b010909022205060304052805070e10052b020105160f03031b0e 69
    0x20a0240800444401c0f12460b070080040c1e0502d0843e8160021034030710115103034450710310244031544c8640c004d1401140e01c40c1c9480c9403003000300c10680240030b025a007401c08096586001d94454454029042c2c011100c1717021680d2070400d508001e107041c905800241d40c0f028200f00351082480005172500d124200c0b583c041d5160344051030304a02511000d1401d5501a8000401044401d4088002c10007070b440c41d1801c03c1400e40d44d1001a00c1c0b600da504c0742603490b8101107010961448009405400c08005161034100035807606503000c2240c00042030100c040304200b140304000d40140c1c03602c002030841107400c9419450903940352952031814442c03082e1100d40864451010884034884152000d42c0401621107440d1038061160020004a4900902009a040005980c103000f00c0c9089403d10a4846e2076600c81000b01c03143e802081c00c1001c904108007085090300301c043c0807001400c2c55101d402100c0840c40300e410b00400380c1e08130b905005100c80600030740050301500701c106604042d4064480 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 800331106 1250 800329856 800329897
    0x804030f0201090503011a0f030a17031308042705041212021c0b10030504050706031512060e010b010e180a11120103030212040e151306090b0109090b06 67
    0x40310f4014440e80322503019800c0c1000c2c04081c108440e000443c0400590350203c20000000400d55203454900010306400c0024401c1040419024000c2d80c1c0541c02c0c10307000c0600d0b1031070781e6400895070080e401240748112080c50100302d20003105401d00780300c4500c1803c0c0118109915164001424110600f09102200350354981c04100d0f5015140141c4070541c4c4800c0b0b500e014211440903040258201c0c0c42105540c80c400c016a0280c4200c2c0e0045030080001c0c03069a06142086c0d00400d44100c804407082910300c070026090300c01d42c026401c00c0f0310824010420b0640350759001d095880d0142150306001200001301480d440300c103010ba55800030034a0001003500d42100c120001c0c1804038010320300c110001248400071700c10042c218102c1c1d2103075007102c0e444180c0c0901950103004038003803210507072183c1d000314601d4043c01c0345412030303e0320003010000e010954401800450707107140d2040c2001915175001c02e1080da0081c2d480b03001080c4580040c442c000d0031500203105403142181d800480f2102003003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 800332356 1250 800331106 800331109
    0x4080f030411031b040b0307030c1a09030d1101051501050a030b0f040203100e1308090603061807020718020301082107080409050f06100c031103120406060806060105070804030f02 79
    0x3141d071040000941a2413011940803080c0d00041e07880503600e4021070621014440718200040c81c3c0088075004050f211440c0d061240203040141d11204404650106214a028a80e0240b2201c00403207041d89a4103005070234440700c02d094034801000800c0401f03801044010b40d903001408c44820000500c0c0001d0610034038400582080f070100c1142d50498404800c1141280000784100706a5007481c00c0c0c0d9400e41c3c1c82c0001002101024040100030341000d1191075002c2c1400c1c009103401c039000a0125565010080d20f83c811007108075a82801640701520030844000305001f520381e160000c80055103550305126555a40303810f5111455072150503500c0c015101c608410035076690950080800d56581d60782d2440d40040e040c1542e80003111700815000c0b0352649040503601d00c1c8d00d100c07a1074500500c41e0a0310306941c0c0c0040280850203602040145406220385001c09500c1584a280c000903480c0c00c080c00d0710b192640091074103060180c1080030078003040c0c01e0ba065070100d03a40b0140c1307003c80400620 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 800333606 1250 800332356 800332373
    0x21010c26010515041d04050c0d0302030702040f113f16030e03070303020a12020702091513090303020d1103040203030d0f0b130507021510120f0c12050d02030304080f0304 75
    0x1400f05d44a50003078001c0360b5121001081040c060b50255084400d003492403002c00140140f030000007805030b40708100410040c2402e4018101c03003c1c81d02000a1540c5415101d050705922141d40d400761158021010684c0005030118001c2d45805584001b032603100e80d0401c11100040640082c140c005040b028600561180e04451622039642055907110412450040d010f9000240ca280101d90b011071b07075522141061090340d42040e001020783e0040e8544402e0a9140c0e0007105600d0342113522544046102c0ca41805040c11240c4a65401650345040c840041e00712001820068508a4100148405a980002903402c0030907401000112240002c2418008000203240e254121052282c51402c144c081d600c068170400154003503819100b40b10138a00c082540031118200110034044040c00000342c10004040fa0030710441c00564110916140c1d0340404a8139801680b04030f40464807801004014000c00441035a02d000a40c02e508059656030b103103000d414001210740c0c2010000500740100c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 800334856 1250 800333606 800333609
    0x5090d0c030e1315060f1b030f0228020f101e030e0607120f05040210140d020f0406021c0f030c021c020303090d140f0921010c2601051504 61
    0x2200130400c2c03c103020402444045503100c0d960110b00360b80d1540e908503003e0402044004803c400d034400b140641d682c103640500c8130b507080c0001c501c94070407440d2444d005c40c01d5055205a240302c10300c0740700b407840c410030000074812000e40d402480300740300e1182c51a40001007031204c0c3c03150b909140d50038038030040200c0c01040b455039605181d10401c000d20401d80e400450080010480715401c5c08142c03440c880000c189c40042d10020f4001d4006840103070454454110601600d60a4000c2440d007105084414188c1e040104c400e180500001810000030303030100010844800509500c13141c1c0d0a00010203400d008540d0785070030506032283c6120100754401c0c043c09000d0300803503440046c8805690320095803070300129601552842440150948a030003048800200105c940d03a0328a0a207158455031040e40000c20740f541c20600304020b0703114101401c1e0403c20300c2c609004c00001c030500c0000008041003203298010030403081084000c00403c4c49901c20364159501034405684012204609800074482c0307 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 800336106 1250 800334856 800334889
    0x30318030d061d07020c0f01050309010f0509070e01081b04022a0d020705010504030c150201110c03090406090207020d14030910170717150303040b030a05040605090d0c030e 76
    0x600c480403d21542c900400c61604920b40c400801c1c3c0c0d0b40e42c2c50240c0e640d00711403e60036030000b5600c6010040c0d610030001103038084000400403a00300d4100d4218801e65005442c107031000e800c424410b020286460001900500b00c3c14018040039072015081a0250195003070f03207000e40e0300080d8207034290200c113150412143c0c070500610300b4650800500c5032900745043e03002d001401991000140b039131007802a10141c1390040040c403076141c5082e100340207240e024805001035540701e099048080018402409419090101031a0307038000c20010002200c110790064003241d48103004020140e2680e101c00c1d00400e5100c24030b4914989405541c0e440e50148000b05070f80050003a40d1000650392182025800320a040c0040c1c40c261284070b41904d01c14070450704c403941a40444002414446507041c803039803e0310003a00741c130324050711180424190340c01102c111400070346450600040051911442c0d0b401303d07803800a850a60401c800041001c1c0e4541c0b0041c003003026010403003c0740c0d6182505030341c00d0000e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 800337356 1250 800336106 800336111
    0x906070e090118092010020d02102304120e0312070305090f120a060b060c19030905030a0b16030b0105090d0c12050d020d05030106171801060f0807060c0203030318030d 74
    0x510940c90b000320448900305d900030406419490b860a0000443c0d05505446030003800c90b28010070304135402000d80399841240281120221490441c0901d401d41c040c40c0140760720102c0f450101c6010b44106040c59220b4081d911102c3e100b155180c0c40b0003510201585464a80d54502101000401ca00b51f5640601d40c082401c200c64403558a0020754007040900c03441c01400000d01d43c1d4100012405030000c2e6440c19044000c0100054000c0400c0ca44030340d219041c5020011b8664010900c0d007241407204a500c40b4180c014041e910104030204001c200241c41c082c40b040000742c00080490080140c0c0c14021a486c848000c200300130075242c2406044d00c41c030003e0410100d418940c0d0f4a2441c2c141c58005402801c450840c918414801c4034180c1d0341130340b1001400320b03050020414030840280140e1841c84403240c0040c40748c4c0700b801403400401125140901c4141881c000c01c1c280012540705205006800c0148001070b10040140da5008005070b14016080b0703803204030a421442078102d2665140c6c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 800338606 1250 800337356 800337383
    0x41a01080705040c02010908040b1b010507170906101509051305010e0f04050a1e0516060e191205010b100c0b010e01080a0221010e060906070e09011809 67
    0x3000180c04000c8034000c680c00c1c4610101d80b04140c0c221250b106001d03051800800087c04650160340c018040030302100f000ca050603414040d1242142c0003929403000082a581c41080980c0510500d15040b03203c0fa40a0a42800d25441794001d92400748280803230201c2c80c0c8004003005000d40c0c2414020030024009a00b104113040c002c000a040034002c00d4890f41030700d008036258829200714540300356408802061031f50701503281d50751068524900501c51081b022074a01c00508280540001e06000342c062001c10390074508007410b5043e19841250007004903090280c025045c01c01c00004883c00d0701000050035006060550161445c200203903040240103d110100746d0313001505e207445078003603601e4004503601c4034007481d80c440c000c0c810001241c0c8011280009460850020200303e40c006048845900c540d04840d030a498038403408448540100c001c12140c15400d124103580710b042d605d041c00c0e0711044503000905072720b0b0600803034041054070b0b0b6801c00415100e07484905180d400403005500300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 800339856 1250 800338606 800338619
    0x415030c0810020c0d051804021902060705190c02120f030a110a0c0618051002010609140f07080a091502030108010b040b031b1504060e032b08041a01 66
    0x8031a0384641e807074511501180d005084418426030b038641c182d00c1d010348042c16544004840f0743c1c00c00d941e81c540c0150b58000e40409a17031103100a0034241d11000361907030a13002400001c2d0804000500e05000d00008201809840c071402003d2030854605043c07540100c020360020401c1d864010860310400d10480c54403481c3d42c1030010203026807200c2030b680d01e00e80008104d00b403602e410714081c4c010300712504500248920b80c00b900c800d04a4440b03071b0300d100d100c02d640d8400003091042480000e00242c4d42d070b1081400580d42902070a0b1881e5050310a0f0180b40c00c10310024038900b200245018101721214000c28450130490b0030080c541604450384011700d000090004c4000c3d4070071b00c80c1072419880c0400d0461641040c2c0500302d004072000340a08140c1d4045042c02c00409001d00c00c0c240c0c0211104c403400000820000a440034007aa0341e20020313105d0481d014149000f2001c1c108001001d02e82809000b8110354140c80b0303441c0d12552412a055484030720f00940b009400304880540641d080740040f814 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 800341106 1250 800339856 800339873
    0xa0207030b1503060c0a0c061802100504060210090807060c1403070206070e01020607080f1506030901050103021c05100908070b0906071202180f01090f170606041415041503 76
    0x800b004505030380703140d11110a415601e109000100010800041c0041c000c104c8552080b004480c00c07090481c070000e050b0780000c0f207024050100402042000c038041c4180342d41003001c1105070344818002c01c480000760712401654051480001d040d02d440750768406c40903100315200c000349208640348a03107070300f01400c020f5125501144c0350f00001d100c101c0469219840010710901502d0300c0e8450103030f642c440c0b00035841c62040003440a00c01001c010030410040e1902d000541c0304d0090040001043c0d4118410011440398010851251031811400d60780030035404521110b03610010380700010203603d246030040b000d008040000e0880c55124040018804020035844d204808503900c2c01804121049100e04074040d89a80b0148650800c43c1140b43e0300389003200700c42d0710380d0506241c001580c1d43d00201d031840304030b80c2052558400300c1d8800310043d001001030300d40146040b40c050140101211444045000081c400c04407a1070000c50706409844a86c02140c003042080794240d204e84d2241041c202 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 800342356 1250 800341106 800341141
    0xc03050703050606011412070e13051501020307020303040608100317030403020d030e12032a0a020c010e0d0602072d020112060b0301050d110d1103012904020a0207030b 74
    0xc01d4083c0400242680d841010791a004030050000d050030310324000c1d24202ca10000400c1c03003081c843c05800100003039855002a409803869001c000c01c051900b013100304085500c2003240b1341550b1050101c000140d0740403058809031011450003c040b0394030300c56410308000d0030b40c0c000780070503000040c003104001101c402148524040d80840b6148440a9011000c460f14141c00340141e410104070041c404590324011074010301d80c0010690b09104001c0e455295800c0c1803440066407a0003c5c0000c18260140038111305003d00b420700d10502c07030810011411810300c0b02c10091001354002049000c00c441e06c02d458404401600b040315a00c403202003180c254000c000c4040e80803440c0c025207152820365500441007035881c0c00c80101d0442c1d20306001c1c422025480303076003250418141808054940c82c0c0c80303080380c2040d004a1450591a184c0003d243c21942140024462018442114140381019242058614500361001aa5003000c402c08034100303403841d0002010304031074005010041d070000800d42e1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 800343606 1250 800342356 800342363
    0x1e071a0c0607080f13060e070801090212010203091903020102211b07080703030b01051b0c0405010e06220908030f151c030c021c1b050607080f0a09030c03050703 71
    0x441c50784500c481507462610803103a8544c110f58610016a00140c0d1840740721095105803008103100f03400e07000031810f110803900f003584541c1d5921550310541c41e18805d5600c806c800f0600031444e50902250298460411030404030809056440040405100354101c07880035a03200e41c0c00e0200c036852505004980402c1e65100da02603e2610502140300001381185e0301d403a401030b03c083c94030410303607015406004120300040c1401800c0c00000d0752040b80000483da6140c1020180c100b135054141044101e03041a0011940c01540d903003004601c0c0ca07203800d40780100e690308a0740411007205803851000751003501c0000340801c001100380103444103828000c0d030281e055088090400f000401c1403000805944066030003522201c0c07110004a4050020702c98180e002401c0b404449500fa0030302250701000c540111050b00e001180c1e10301da0041d008010018003030440310b441c07822402d81c032820303001e028203d1100031030640011040758260041c03030520300035503100c140610312130307500d00303005407100341c3c600c4190b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 800344856 1250 800343606 800343613
    0x30507060f14010b040e04023a0b070507020108060d150c0804060c0c02181f0e150301060f0e0a060909200d0b010e090a060e0c120a051e071a0c 63
    0x4103900900006175020b507108000602aa80e48039000c102191080408145642c0d2400c0c00c04030b0380c3d440c0420f18010864000b0440084004503140c0111102c0f0010183d008200080c840f03400140c1c0d0129a0b1900a4011114048002c4d454200006804c041140b000246451300c2c1034410704c0d07508581158400c40c01400208085e0485840c241e50304401150000e60180b00c01c0044a15200c1c0300d07107d10f41040024040d2260b070300d0000741068002c01183c02c100a0050050b041003020800751140407040d5500341c6c0240701062074410b96280b115002d014511000c2d514000045400310350b80e101c0801040c01040c1800742c4041360800000804820581c1894010441e0700c4074014104200c2468402c0d41c030141c0303080c7e90b0f0718160010404040c0901003403814007e00c00c0c0c40d00401c480d800703100e81d20307010200900040341904c0308002144003032200703561440e0024034019020450100b03610381554813500b034550840b50904c1c1403900b00549a04000170490000c0084805107100c0409401ca100221045 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 800346106 1250 800344856 800344859
    0x311101a060c1c0e06180f1906030207020d1e0b0708060306010504020a021507090f080c0d02060318030705031801020a2102150c030a0b060a0c0609030507060f1401 72
    0x80c001075224032005114594420307011000e000984600440c80440385280000300d0084c01d4001886a40c44440451601c05c008035410809141000140c0244841140e090507190740b80300707507030107020b420f8401c2c5020b05601199a2041d51240d54501142c280d02c4100c04240c0340c040c5070700006080b2409002d4a01160349030005911500440806009640c02001000036a1910b820400690301c140d00e03d2017180241e92807080013540e0b13500620b0061280b901c1e0868524106003905d1041043c1c0da00401103544503101040554072102504148190165010f9230b4969410b20901200d400c410303007071032031803200042c81c00501501002130324003820380980c005102006030004903510302c060b40c1c000e0220108240f07004000907008041300404001401031f151b00d02400d102001c9884401c42d1264007403040042080422000c6105640f4442000c650050501c49a01f078000c1c80c0c102c1d840801000c0c15681c00000f424140920295206142e0000003804601010b0003820b000d030172442039104155290400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 800347356 1250 800346106 800346109
    0x20d020a14030f13032604020f0109210c0305033006100c150903020f06010905040f0b04020301020405120a020a050a150302090a0b040806150103020f03130311101a 72
    0x480f800340d01c280351581420744850f03041c1d90081d41804c0003102800100c0d02c40a4500051041340c51040340d081e0100c170391900e03050040c40050540e0940490400078100030911a0b040d03030144107030100d4402e4540030701c9840349240c1012507403140c1d080038140340705c0411440142610781c00c001807802c6011034503040c40084003042c0c40540c0c4080e40c074981e00141d00f0b940c109200b403060001d034000074029511144041110b004030804c481c08540c00b54010b0704180a440c1191390704224035070041911060812103441e00d602c40e112a984070702e000a00a8460030013050965038250162030180000400030f1010000340c0c20800e5a40c02c600b07800f2409030341c031110001454078100c0c450b8800c0314036480e4165044410b019040340250711100180e5070040722240c0110b28100300b20b0141000d40342c604002c2081c5c2c2087d44446800c04281088a4100340c01009a000790202c51001e40e034014002c0e01980700498058507044d65601308102020000d84689803000c0c6d040d255a4002c5000c9c80e0f00c2c1400810a041c0900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 800348606 1250 800347356 800347397
    0x91c140303070509060a0c020a080a06060b3a1d0c030a0b060402130f030302030318070b0912100f0c090815040308091603030504050901060f020601060f050c01020d020a 74
    0x490314400310f1030503c0005128200f94000f841715900d28540001031b04c130f040e0300142c80403003250080900c680c4010102010040f040c880c010140c108142c18038141f6502c4500d0323200b0007000c0044d1140301d00fa0310070007107501610031511729586a4001c1c814004400003100c0e4040c40d59605600188620500e11142007e00b40071900036002038021105090303d681c1c010500c80030b0740c0f00302c0301d541c0c0c030310480308001640c4602030b005280610b11030340c041c2da40c030708100900803540f01c0402c003200210317008464100700036180007089a000d64402e07101c22403a40000ca8019090101c040c005d03890184c1008134400641c44644e100426200b6942c984810054035110740c2136440500c000c101101c0400100450086801040f0382030340320480c4000c503030fa00000001084891111907104502050021405004d1487d01161060152a061604074880c07203101e0b0780255102e406103d10000e00085624a03400daa118004035084114500000d41d03a61002c0c0c00f40d84000c0d1f22821103d0005100d01041d8101000ea01 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 800349856 1250 800348606 800348611
    0x305030a1211160615051e03070f0b0d0c031803020f010c030c17060a05100f021e0a030f030221010e01120f200904030f0e030304180207020303091c140303 68
    0x4501c031641002c8207a4444e002420401c84001120911910008141d500c000c0032500310107075145107000d022500f00905103801415001104070070340406040c04003001404c1580c4030319115080110302c80511020550080001a61000301000a0140b0105040d00000c80030b84401d4104000c108440c0b400d00203c04541e002080f03c0001070754051084814546040c070542c00000c020040106980c1d1400003c0c1ca004600d486400442c402a40381144190144050080c00c18000909060104040c40d0700e61036910485001b4103110914075004079451080e41034405111006202c08840d00e400c40d800c00020000340f0a207400b200d20b0500104e00082040910071060794000641ca001807402c0d0780c5d01d10900c862541030800c0c2c0300c403103601403990354400400601560094032846080e0b08801ca000b8007620120300040e0185e4010401003017410441c800c0610f110415103030050704c640d001d01c00a400e5100d20304010b0307407207120720151030455445131101101051046854245030f14041e1542d5803a0f0108 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 800351106 1250 800349856 800349877
    0x60302041206242709020114030405070b1c0617191e14010f090203071505040801060e070228030815191502030301050f0f0a0305030a1211 61
    0x1c0c10407220000e202600119201d00300c1d40e04001010000c60f1007070380700000c21341c4801000003020550b000c1d10314040030b0380343e65003002050a21040a5507000a042c1c208243d42c50000080004000740c103001003400301e10081e040340c14180e0740e2540141141c1d0040c0410741d65a990261a198000501e40301070520f8020f01d030410b10250000300f4400b400c0c00c84058820005991543d052400c6044007920118103201c440c2c415660710220701c9540c0d1b21503003181c544050705030354145400c11541c05694000762990031500040c5683c100039406040c11902170041d9844602c042d800c1c2040400c400e018840140e00c80c0010341d00316141c0c041d01c10340404c3e02e4114102d880d01d0000084c0f4034500441d00c1108103603031162981d1245040445424045003503990604009415030b10b12301c006108204081044049400040c0300560965040c00001740c02e4035940b4001920804401c0d4a01220b03490f5014410000c541110589403900005d000c00303440850359400c1101d01e9460300e0350403204211180c00342c45001e240e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 800352356 1250 800351106 800351129
    0x6021c0e2509020705030c01050901090b060409240e0f01020c0c0d0b070e0a030f110108070e03030301180912030606180b1b0111040b0418060815070c020a060806030706030204 77
    0x140c001182d000b98050300f41900e903400100700e5894801003d00650b07002c0c1400c4000010f901d201d60400500011015000e144280c1c1000200b4004c40c180030011000005402c100f000700910000000c03001b060507080100b02800780c00200c403200c1e1019400f070402c4890503c16200d054044104105103120f41200040c080310505000c80c103a50b2103144040c9030340380013070302003644940c40391100d12003480c500038111741e40ba44002c0c814040e0350303009250b9070301b0850070b0400c1c0e0f050b900795600082d03e0380014012114040c14441c0d000741401743d950040120686c001c01c2c409110010000024003620550140c1804910000d1801a4801c150071900b41181c0c41c228001d42010500c401c96511403054140e1041191b4842240904010100c4010070040c291060810780c0c9a140201d85041e07950b8031a20141c2c0a86014810040f1310b202003404240c0d802341ca01c5080b10303583c1e480e0040e5941c0a40400194114003001008584903800900150141c0001c4048841780d541d5070104030203032b111b1401503292001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 800353606 1250 800352356 800352359
    0x3020307080a091a0a0906030501050d0f0602070611040e1509010909150c03060503010b03070617040c1e140d030207050f03070b0310180b0a030f06021c0e25 69
    0xa0301c01000c0c08000450b031074007015203507403410140c016010034000c0707100c541e0000a54410031078110000300700070803d904041c0034542c900b01c0012074041800c280a0060b20504a000301040200d50484403801c1d40701c2010401000c011f036401e01141c000b4042e00501c60034030030105841c1d42c0d45044013038104000030003441d102e03820044c0c00b40c09414039000845000440348a12182c80c28280940105c807100359500182e0f29240c04101420740344e17001580b0740a07801c03518040c040c0d141c0c000d0b15100302440344d0124510345e4403107140522503500c4503480b58803000c55a203007144101e49044a100d080300d0001d002040169100000c0096904001c0340040150303000d010108110700700000c1541505200900ba2240107580f0b01c80c110b041e0340100d445086401c4682001c1c044100d050410484010032101c0400090150300042850340d1400d00018000c001507012510410036550100c92040d00b40b20728800404035003040010181a00359076400c55809034804400080710116a44c0103c0e040b820800020103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 800354856 1250 800353606 800353613
    0x32a0f050c0d02150a271e05060a06380c070f0e0f1311010e060c0105160c05101a1c060b120303061504080a1b0b0406020303150102010b13140601050703020307 70
    0x140d00142c400c4070240f11f040c8085441c90341c1ea40c000c6a40c940170780081c04161602c40c4000d811548150021b080d401d1241c0410003144d0090051102070039200003400842d0036505032000702d03a00807003070254540d100d611404108004564003400490389181303001c05182d26100d00c2003000e0402200c13006007540401c071396070012810300b0400c980c3e906410306042c0070303050750100820701c19844038640041c180e442c8c1052011106020040c21400c0300300b4a050101e0385115642c0ca500c5800c2030501221a940301e0185244500c102200041d1401004201603660341020801e0110f600520314141c500c01d01c2c2c411030003844e08121842c0600c6902d500040c0d40345984440410219030100000301c0e010048c14000810041c0e001c00442c209a8041c0b810140500407184034105000345940118645500501c01000401c0d0000240e07070b007010643c14080b9819041c240100e004001c0541940d0b440703003c000c08054011865131040d0071000c49030b01070003080c0d51058010b4540d84204080200144c1c0304000f1003000c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 800356106 1250 800354856 800354921
    0x30b070f170606090d08090a0803032202010e0a080d11010b060703080c07020409030507141c110a0b0114010311040b0f030c160602030601032a0f050c0d02150a 70
    0x101600a1180e0706291440001c42c3d017140d60400121404400000e1141407407402d003080d207000b0711896000390314600d440b00010046845c107840c0e00112420910409045a00031f1482d021041e801800d01400145d4a0748450786d03c1d01d02c1003036800032a4081005140383c15040c05805090f60000d446189021201d43d021205044c1c01011128403010611094005940d00e000c0c006115001c3da485e25106c0030f00f8200500c180350032061095580c1d214034010000c40301d400824051030001411b20740710b15a0301b2140c05003403540341c0f14020047d040c030500110301601003803034010380c41d202070340c0c10068007508400005007846a4025417520300400c0c0300511885c0c2d548002194841301c3c400302c1e141441c141038420080030928400031200c540d0080104945e6592521503100385042d11b41c480b00c007000e00780410550319102c0e4082c0c0c2c1c040103c000ca124040d18010821110110788103012140700d0030000c00020748a44400103804085409403012a42031152070040c02d8032580806c6444a5001007201000c14 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 800357356 1250 800356106 800356111
    0x15170c090112360c0302010f03241802030f0f090a0b0901020909091605010f021612021807090b07060902100c02090c0c0a0f0311030403060204030b070f17 68
    0x1001076000c400c0300c14900900400e10b0703d080c02c0e22100c0c0302da54681070300d039001e15070011900740036210240d48070041512443c41804598081c24100000380713008400301d014001e000d0341c06909029561011541211004120741140c9880030403502020900c442c48042c0e00c000d48540e0503203610180030554a40c01418060f0304182d88500b19511503880341d460707542034081103500503002d950205460300c49050440005500480c0e8002030001c1a81c0701416407600b60b854007807035041004140c24100610300800c5142555403414640301c95040d41c0300003801600c1012002240140038610009240058114010b0b02610050f2198001503040c00f040c0c403000d070003009060f1681501d43c00750350b001d070b1141c2c01d0020340c4103a10ba494014002142c0140540d1000140c0002d40287c0704014802d4191700c0494181c0c1010350143c0c1001c42c507441c2d403c0840b08a64203451015160200007400410801558010001c4038070601c03414490341d40b80704081e5001407065248001051b9250011640c0318100414160f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 800358606 1250 800357356 800357359
    0x30304020922030e0306010f061707050f0c0703021302030f16020703080301170f0304050d230619060e0106050904020307030e01020c010236060d020c030f0415170c09 73
    0x400829a07040400c45004200d4815404144140d42c040136905040c0b000d035000d89503025440e02d046240c02002060981c55981540b618080d040c0428101e81c07150045440c00424500750135103c03002c9050385920f40c504e9200032445403440e09501046d80c10b0900a43c0d12400304200f0440940e6903100c211000c0b01d40c2c140e0400c0841c055620080001a200340155020700861000d2904810040c4031940c54400b800442c0303010f07a031090008010965980c018039000b60303801500300074000b4004e06580502c40d880c080c042c1040c0110070030000b51074041060015204038815080c030825581d280d280c0000c005c20f0040c40d0006404001a81150520743c00039070300103d0300e140c00140c810100c800d442c00c80e080555452000d0750009500341101440c0b0980d42c00500c200840100403104a1442000d0b0880181d800c40c029034001c40e8584012007541d05544821510302c00740c030381c0d444e4440728a49495015010703040d010001c84248001d0b643c4140d90034102c81c0186049508151204401840990014082903 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 800359712 1106 800358606 800358631
    0x10e03040506090a050301020a03020a140301030b060d020303130303090504110f07031808070e040b071e031a030f0304060e1c02060d14091e010e0303040209 69
    0x1501100c104464481d80c5418400c0404c0c400d80d4958095540340d40702003904c08416030542c00030500d1180c1c82e0780341d20390581e003c1ea103a40b41c3d0000380005000700b001c070000100c450510000c110b9400380020212800d00c020703d0024003e89105403c12000a042208100710608060048a9904c0452100c00d410b0411002500c41c081c040c40602404011102070100042c3d413a00c14030101621002c42600d01e0151217460300d210620b001d44048411110b0711300042c030428030407a4010031400740400110912030010300b04a000d0100b91000700300314945d44031401c1c0785540401c440404040100c0c00707952036901c0c041001d040d4440e5019240c0c0615081072030b00c4410307040b10348407150013541240c14a807214000001000200003880d11800a0300d01e210900c0307120100000d049030000640b41507940800041060507090b50418010003800364414804507005180150003a640000b21640d031 = true := by decide +kernel

theorem cover : BRFrame.Cov 800179856 800359712 := by
  have h0 := BRFrame.cov_init 800179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 800179856 ≤ n) (h2 : n < 800359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
