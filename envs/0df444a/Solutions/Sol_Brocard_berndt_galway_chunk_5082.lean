-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5082
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:41:04.943468+00:00
-- url     : https://prove2.me/submissions/7f30059a-571e-4185-9536-947bd45c8259

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 913848920 ≤ n < 914028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 913850170 1250 913848920 913848953
    0xa09051002070f12020a0f061415011d13050403270609031401022206031401030f020609190303030203040317162a0f210c06050a29010e060403050a 65
    0x61b02c2d060a01c03900c030018140d8000c001510499219450f035118915800c560952141d08400c0755504d032031640d00000c00b03400c2d00d0844a00002d00e2080944400e580d03100d640080c201710401c0610a528040c94010041c801c10407008141400e020360b030000365084070001c0340030707100c041d500e50036018910f407200807400724008800c0d041c65608222071503403030f13019000024500c4201242d504030b4514c1d0044c0102124080c032040e840480300000140b0005001c1411000036070b804aa5a545903c918000030741800c0c603001480d240a004004000105501500a903200c1c034001e448020705800486041000c030b90040b00c01885a846c01d0360130550050180307030162441c1c00ea880e6000008130070680d0301c2c074110600c2801545c20b00d07845c86880c3d040120070500c0114250044107040c40c011800130340903244c003c3d030b010002e002684600004510038219441f0f00e0300f1401905015180c1c2040040380348a10b0000846a0700089008088000905000d411a41240d42c4800103120140340c0382c03161041042a81d28 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 913851420 1250 913850170 913850173
    0x5190311160f020f01030618051e090a230604060c0210061212110601090e010912030203151c0f0c0b0a020f0d0e01120504020d0b0a09051002070f1202 66
    0x15851105000281c0307070382031511603403030180c81080720f00401c00000343c2040d0840c10141450018800c5040700302d10140a07a5040f040440c035a140c04074002c030307083c40044041d03803440d10000c104104102e001510002d0103001350b55103800032040d940360f02251004a4510340c014ad1004020070006100b9a01410312502c861050343c10103882410108283ea061780e11108036a04181c045209200303090283e13211003021400d001c2000380c401d190301070312144144034814000350b075151581c9900701e083d04010310042d8044407242d08400014070250003500700745c039084000600d182020109003011100400309103070540304081010555078038035045c000408000c4885480c800e400103074004800025204d8140e00e5000f5000c20b0529514080c90f080b64082180100a02080c0d1011141d070410b00b558810007244001140603a281d0004c102e20f422041d0008142d0f4a07018100b084445c1d084d4046042c90380b0641c241c0d5541a0585041000e9014a41d409008681c0296100d80091003134900d4180d151480e00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 913852670 1250 913851420 913851427
    0x1902010621021516060506040b030d05032508090f060603100b12010203070e1f0504030209041b18060806010b03010b0318030d09020f12071e051e01030c05190311 71
    0x142c0f0501c65001901d10514082c0c0300307200c4604010043c094964030403010340d02080140484c0001a039240c0c01e502c65881440400408075408030840c0743d00703000c003000c114440000c5821541c001000740d40c080b1984c1805000f44022840a0500410a0350140c44000e008040c11089d20b690758008024500c1095030140883c012415100d40030f00146101d8001a143c9011084590050142c0c034500c07044861400c500e200c40d0220030607000340c1a10140c0340c0554400c0040d41c1c440c680350b0542c90543c01154941090700f14006250038207089980d00c04084a1400c1c4180b55446800c19900c0300d0078000c184114605200601c050000d80014661090418050408000402c03804500399441061081845a1210300c61010b41c00c01c2c08079070075690400d0780c80d00c25441e940750307242307032508813074001d01240ca20207503013103c820030910b04544c0141c000180700c0c2001c0091001c159460313201c10b64640740800d050031075800f81075002d4016188210000b80c04401d049652900c00c500410a60b24070035000c18091 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 913853920 1250 913852670 913852699
    0x250e0f1210180b270d08010b030429040611250623010f0b1c050a111209010501330315080604020406081207021905030a0305190201062102 61
    0x1164100c2c003440ba42c45441d8842c5130000c003000304074003c0c0c1c1c092503110741c0b08810100510f43d001e500181102c041c404d40903242d132030341c0c035000e65a0741904c00b00f0b01418109000001c4500602d01c2d00c64041c0d40f003030304208030015100d815102c440c064034841040044007640f407100c0c4d49040d005a011010b00c101c0c00004c814001148c001181c1055091024102950b080103012941484203d84d01409200e8403075814065070440c44220300750402526205551180085210b021144e088031850000421205440343c14181540240c110708903449030036907003030000004440d456506001b0086111aa03010f40111020700c0d13019011000c50298002c0590398038203081405200c50512001e00190000783c499810240100710030789040c4c0d00840300310f420120303040d4035012554044804940d030556400d807041c1c40b44e0301035081441803544603a4260189100e15400c25071311000410709030041c0b1810005605050008a0894806025019905030800d50713401103882000450300b6424030040991040904a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 913855170 1250 913853920 913853933
    0x1104020408030c030c010e0307080318011b020c04050f1e04080c0a0606050906040b0603011a0408010e010c09080601030206071e020411041a03040b04030503250e0f121018 75
    0x2c003039a15080d400101740c02d0314140081c01000201c5114000070750400d10b039600c42c1400d42c800540304840d84c02c07c105907040800e10079040a241a400341d8650a803417240b505000e03454800c1c003e80c032442289880d001034041e0740c0070f46019002c0c64500c0c0c40c141d076030310684054445824010300203840040d421310810a4005007006141845031003510046940c030300d05024070250000c0542014812828541c259211b9114502905d0455000022014001c100300d60f101c1058071a0381c00503001e40d401c08201c450018015046109104c2c001d50706e00b910142e56919007030321404280030003540180704010307100201d042e88260940c0095503040d040c401e425954001000c0320103c0005402c03c0030b000c6000c100039500b028821341800301d01e80c4c1d03071072035850b0035600ea41e90103800a10003018400c0200100c0c806218500411120b40d5020700107401111180e9400361807481c003080c01c00d2140141030302c0800b85080c0240c00f40b064442100013441c440c03404140220141005041c82c8801c5074081c540032022070751 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 913856420 1250 913855170 913855177
    0x1112010312110c0f060d060b03010902191d012a060c09061d04020f090604080106050918030901300b150a05070b04020f090106020606090919110402040803 68
    0x41240c0800e88400c01c0c0310301801c080a081c044500c20b40002d42107100644071800c00131401d0b03030101d0b0103998175850303144102c00401407508502c00c09440803002091315440e550040000b11040302c640c00c00c540c001c900455049002140c03040d1080706041804081e07500500b060610292843e82141415860319801c8041f40900d4405031201601c07085510303002604441400c1c041c101070b2520000118101c03603507204400704003c005000d694001600c2c510b00c1c55010580300c680b00c004242d00d40c1e8940d039010a902901150103914030070104c01e408034544000b101e0004450082c0d26000c0c60600e91a07000558501c8681c00381d183d12414064603000d96502500010040400a20300004241007541d062042003c504d1264855980c42084100c2407203405c0001d440c840c42d070103803010609170b80f0340c8041911105580708960300b002000c000410410703000b0501505c95501901d40403516515001629034504400d40c984038110300202004000c204000a000350f407500250001d03180c107a444e0f000518543c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 913857670 1250 913856420 913856423
    0x6050d06030807051515060a1409030613032703060b040e1e0105010e04030504290714060f0411120c03030a111618090f0f06051506070803070311120103 67
    0x100000c01040c00040035421546d0007100200d01c2480500d03009010503c0ca2081d50750460038005410329480c444c3d1400030441d886ca21010301541d0060405000f1121807161654080300851882c00010034804005c5022440704515503142002c0d091071511114000d01c400034107144c1050b140c048214607010308200341c40140c04800310305000c00065100807402c65030183c01c005090804502804040780d404000c2d203056440c3c0d0150039048030841da090a80c140c3c142d04210450140c0801d41d03005001c20070704181480e928910545445540b081540c1d2400e00d0122401400c20442c00880015410300e04100e0303d03502c4144007251a018200340c002450754104800c201c0028080c041000e41d1582c041c1b29040f030301854541c0096a441c280030781c07201056000308043d084656200c42c05400d00c00c4a40c440301109410068070010b5044908205020b08421501c0e000720300000c1c0780426244c14050211079000f50019140c03401c40e01c0e080c50071400303032074094840e55582e44107104501e942c04603041203a0085 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 913858920 1250 913857670 913857673
    0x10030f030c06060e1605030928150515120d030c020304091401080f060403020c040b0d020d21110a1203020f040b0315010309020d0b0907080f061e010b0406050d0603080705 75
    0x614082404186500107854690100701c003e100323100c0b00d0400051003403003c04001d060800c058040209240103507580300005491081d145a41c0c4400c0c1c511580300b0703401860301108224402c1114420300240e47d00c2c00802c40d80c40d500c0420703085c2000788030f940406151101071050302c3c40c00c1c0c0d42e52890f605480052203101e001c14403080041000d23000030001da407410070590026204500c0c1949001e9211041d40185034010b40e00e515007031115984051002d0a15907000f0303c217603007080d505d040800110015000c0120740c40a074245501c000c9008101d100c00040c8000000c05544040c3d0341c41c14195110348032003500b41502400f45032841ca198002400141c00341c420f12940f00c1c64146090f80e0a0545101980e0500d850064800c016884144402c0051900070710444450340707500c408a07160441690001403e40035070480280d120b080811442d00400744044210001202400c55461a4100b840b0f00c1d80214000c00003001f9245c01403015080d40400030400051881e500c1d1514065603101003021142c9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 913860170 1250 913858920 913858949
    0xf07050712110d0908070501020a0803150112050403022a03030403110d0c08030a030c030b0f04021606180203071a160f050303012d05061b100c170703020310030f030c0606 75
    0x21700404102d0000180824401014501c005460300003682c0700191020fa04003100340341c003002d943d0082e40c50801100060000f00510f241c107003002501c5600b0303400d141003001c10412030029503034200710403c851418000c0c041c40ca05455643d500403041c03500300c10070340c0102d01e03403030f150002c04c14002c0d0150041c11294003541d0f440503002c600500302d68500703422505062500310109043e80715481000506207050f038005a680103c240350501c00c1150050003000241044600040c1d0080c502a5041c1280b0035011908199114601d08a4150b1500e150103c80f207020f1141d071140e00b02c40351200c0701440c001c00c0e40c280f02c0011516158155070098001d5168400d025922107190a01b0708220400c03484080340114a6a06180001c0e120b4800d4a0041201e603008140000043c0320030304c00c880464031040020000028542d001500d41c01d40f1303c0602001040340000900300c81e010b0700840c1d1065a9003882c450200d8159522441030403c1c0200075001c025010350424000340c41d601c1441e001e002103902c124103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 913861420 1250 913860170 913860179
    0x601060509331c060f0501110109061118040b090708060607050a110108060d050705090703020d0603150b060a17040c23031204030203060a05040f0803040303050a050f07050712110d09 80
    0x1c0c10030380c3c040d9204514900401009511005105042642d800346440304641c80c41080c4127000d8081c12902a24843c41c003840c0381a0880220010219001810031000140001c00d0400c02200c00c0c40f5100d036040b031b04520003e2100d41c0708101080e488000207010342d00740460303621780910f0007880038411200729015190380082c560300100440d52000d021a21361072081295603a0a071141c0c0b0920660340155090004030b240c0740e00980507103c3c1c84046040c00c1002c3c039568240a010b901102c000180c255251007000310003030403c00100c65500c10a030325107005240780e040300c1c0c40040b81e001300240ca55405942d0701040364000300e030402c1a0302074403c85903040d10307500000301802c048000390080e000c110304000c00c00058a01080380c40d4000b140311800901d41c0d030b4a00b4020399218144c00000c04c00300d0300108010815402d5404540038041d0128100040e03550380340c08040c8a0350640b200c00120350140300034400909600a00c1c0310034201071810302e403084d000060140c9000340e074079100c83c081100c1200a20 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 913862670 1250 913861420 913861447
    0x3030106021504022107051215010617040807030309020424080607090501141308030304110402040302180628090e010c0905060a020c090c12060102060106050933 71
    0x14514078080d050381c4030b50400754002840c00c0d814007900c441417549401401e440d01018002d03100100000740c41e00f041d83c9034460219441d01e550040c1407201640d084004248180300306111002e801000294a52948558451f80c400e900040e000702c08041d164071141d001600c5901030031a0f40607000c5600203104025070802e500c1d521840d00001d401e03a02c01801c100005500500c40b40c02c8410a00703002d5540c000d40c0030014201c0c0b044588018210410607800544ac80c0300000451140740500402c440c1c00b1100c03c00c02c0103034419440040c0d0321011115a6521056000308004d40280c030040c0300a0404c8042d001403943d5402c19a448079110b00791107010402241d05025060b075180c113610003000340749002c10004e0000312203400f800e4069180401c516421500810140040000c01450716800d447c0501402c0c00d10360010380180740011449003c1405540002100e80c10b80c0c8440d1101d40c20250600c0500c0039106803110f0b1462038208c15140004013110a04040120741150b980181d5a01100070590b07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 913863920 1250 913862670 913862683
    0xc090d0602040e1b03130302070519060f140a1b06050906180304051c020d0804080307150c080a050c0403080f071109011d071e0c0605060a030807060e071203020303010602 75
    0x40d1000380d550b040d100603a084c44100e070740c005c000904c11009041d440c00c0480c640200b40d004203403c91030441464409001d1404c016048843c50703030b602040d482100504031035000e2540e1442c020700350103001c108625402a284540c07480c0d90230801c20907c1506450300c40c2901d1007900d0708201030304150180082070000000080c00c0c1814600110b140c00d00d07100205480b5a0740704001003910141e11400411965880940300c0c100d6080040c880d200e82c1ca03110743e181c8030f1b401030f542140d00a00f023100c40c030f0407108a405660320425054440c0300c09903a81a8007803001c2d0400a1000d41840c0d010440800002c01010141808a21001c8a03d803260240d14000c0e1b04061b0500e0568401c11911004100a04e0782061043c280c0941009540c450344441d102035441c0000c19295280070141c512a00d10a07582c04140382613001e010310030900c042e031203d80a00c02c0008840c00007074019a4104030780c00101d60580c200c20114501c1c0360407240c3e026070320810f4400310b0011090807130058000000401c091981004076 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 913865170 1250 913863920 913863931
    0x1f030506010306031e03171806011d06090405072c06040509060c0901181202040f02090604060e03030405091e0603010b2817010212091c080c090d0602040e 68
    0xc1103c00d0964540704d0011a0525006801c569103245410415100ba13080405030001d4078021951801c000b44440441071904481c240184140c0000103100000200349616030f04801e00300740c45a841d00010b220a8000c000c4c026500b07071141c1c4c1e0001600b01003010125501961044201a0780308070321107080012940609410311480c2000284410541c02251454105075802000c03aa039442520058a6405507c0312034490758082403400224090820260b000b84c42c07084408005807001d202420049025885989130018018001070041c24000e4806449607070008027100c2c14203940e2000160040e60480b5080c1003d110000b0b9030004d910090000f43c0c000608800074010079007540d012030f11070950958203142500320a404058442c001030481805031130003100480c0110880040940070b58084090036881c07401c1e40c00040d20f800030216007080c007480f9010301100007680e0223400721092880a0701070280c514040050040783d80d12002d24500c1036205103005a2622b07d400130168412100912 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 913866420 1250 913865170 913865177
    0x50909010e011a0f1c1704062c0f030f0601061e0203040b0f031f240c120f120e10060b090f090c0d1107060e21181f03050601 55
    0x1411030f90380c9a1040e00103009050f80d041010300340ea20501100c280b18058080c0100d2a66140c8480320341c0d980c4010401e40e00103032208800300c6014280c03039480c51800b00082c03100800040c1007010700d28029502030040d9000a0488600200486005003480c0703081c1d004da130104085490301c10902549528502a84246001960400c0c0c6413458800b164490801c135516900c200000003010744138603100c6000b28908a2656003419500d40a40e038080d1a0a0540c450a0307091000f5050500e901c46e111144149030700007229041006d1080303041e0388028004109c1e4040c044040e805450404080c807844140d054a0360040820094001c020b200b2039840360840c2d4039a42003007044440d140c03615000c0c1041003c007510f214106644031901c0341030f01d02560b001c42088a080444020900300d07007034050304119000e01c0d1b08120340c0c02481d15180d69010b070705000b1401301c4144042040300c0e10660001d0000d407010803170342c256034200480003c1e04034403da02e68240440749508003020303003942c540f007200d5000c0001e09 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 913867670 1250 913866420 913866461
    0xe071b030806010804020d0b0703091e03050f030a0204170d09060f081305030d0f0605040e0114151c05100e03040b220e090304080609010b09011e050909010e01 70
    0x31801080031800800e00742c140141000850119290240000070450b004115581c0c242403c100040140c141102d0640d0814050f889031030341001075404400000350f260f07c89500e07100e80307600c160030242c02c0240040013440e800e102c009081010340342008141c40c080c0b03029060b00340301c214003c1d0000002e900802d00300840c04101040c00c42d0003040b03d940102500c89029a8880c440c03500300e29501c91103c4824110f4140030a2261071403041c3c001006031081201c00f40401702040105034221140900031549000c81c40000c140852941c0860703518001024049803410340d140a801d2200300a0400209c85640c82404010a44004d034454010341d50f005030007940c0341500d0002400824000c0c5603207081551410100141000aa900c90000070221040065002c1c5032514666450340c0081c8034a00c1f0350b001c0c00c4005880e860040c4256801d2140c000c00d14400d990070011901c3c4a0328214502071081c2c815804d010899030750701c0c400580f10380601800864514030148106094860140e01103102d510001c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 913868920 1250 913867670 913867673
    0x602042918060c0109081317010507020a020d05100c0c030f090b03160e090108010b0a0807050a03060c02010b0927150403080709090906020a1704110621010e071b 71
    0x40704020700ca04461140d100c6003894021801492003860081000700002000014040c048665504440c00c080004030360710710300c0d45071a00f41c50040b5190801a000302952500500e01403151900c442d01401c01c840441c010304d4442011601d441d424007011070303031743c0440d40c003015804908099840e100d450800d8210b4603001d00510a40006046600384149500045a4646c42084640e2140100030004425965a04400c82c000c01c00c00412a0181d094131501140498000441508450005c0c04082d0f100d0b00d15154000144810007018045540380d1450f5400c44d0355079002c0a0103119101d244268841c0b0005032580b0010281d5503070f003415044494007400b915400003003590301a80604040080d9034030401c0c120754089c80c5810510440d0f1504c6214001d003d0b0b1540030700703010109900c0b565070010940c4c0b42691030510480d0000d00703458030740289102c2410301d400a4051000c030000400804810800c403018860000d8201e40500b1580700d08001031180c2c00401000b05400406800b460074a46 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 913870170 1250 913868920 913868947
    0x30421290601110a0506041b0609060207090f0906020a110616020613030c020907120501050607110f0f040e0309030705090c0a0c031b120e01050405032806020429 71
    0x2050310b818481c0000640e05109024001c1d0010160721005490082c5014500a426541d03400c0700641041d058480100308103000c1c6500b4416226280c008190007403401d070340c0d04090300c1528882d01d40c01c0d03201e103c00000240305002801a10f20941c40388500c1c00d00c41c0c010146050341c002c0c003a66078a038a01c6c800003000d41c1c0125940703030480e9003030880d004064064101501e071715850f90380094002c54900200300b422544422082124820850305121a90742d4000b080101e02410101030100344062088440e00d203441000c0041da100040c00356840c181041d000101110051011103180740c01c0003a406881c0d01d420300401313020307000c11a150365040c00c022000d5002c901403580000240180c08010f1030074540681d6241c5030f4509c2c4002c410401071030701e01d810400d104500718041b002c02d6070021625984c6d03002d91f0546090314405002003501110740081c2e06261141603014500c80400e202d04070010813010f000070006003001008000702d0139004402e2600516540060316070101043c00ba400c40b0840 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 913871420 1250 913870170 913870253
    0xe0a09170906042d150e01090e0a0203180d03020d06081605121903050901080f0f1f0f03030804120302030103050a060e0c130e0d090305061602030421 66
    0x24080340c610300640001d5050119200d0030b00c4d04480389a6052400110743c14840c60103141401240e4540d100b810b030361401541ca00000c1c0c01081280380b000d20001c0c1b0314410395400b031a440403415100c8203401624452190519a0401c850700009400003442c14214550b40168001441881d00600e4940f1030000e0b80fa109000030700a07544039010f103500000b2541c41c20040324411910004509805404624002d0071984c81a41c1c03040c0490081c0000942103d0007808039031003480036110400c616034440d0010354080c2100c2c2c0614000d00c088031004110840c2424150002d144280c9030322040d410300341001a4207450728a000b108150040005000241d0082040100f05522420100b04000da2407401c504282e119840203800107406e50b49540c03000c84603080450702d00a40e00c156405800c400004540540c198007028005a100202080c1010203003ca9601055503d02c141ca0802c0d40302da03400080300242c7d00d0381410000c60f11403030205100685045d0305c0740d01d5062920381842c50700d29007181242030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 913872670 1250 913871420 913871429
    0x8070e0f0c0a0908100f1109132019110303091011090d0b1008161e03080a020f1b0310090602160b011404020903071205070e0a0917090604 61
    0x15010481610441c010b0403040060610102034403e0050041070000050481b01813103801c035420040707100f0407400460215014a940a040381e8400940d01d4080c00c094000c4042018007460940d02d1004403540c41809082548400c41d56000900b41003800184583c0e0280300c0d2400c25001002031051801e80020790004650f4540c10109600e12640c0d00b200c42c1d8000e160030603400215810301d400c1080080c1c80310270721070320324080009061a01c0300c26869840d0020030212140c0c1010020522400030035014003c0d8500002101c910110780780c0e40d405216030032610002002d40e01403404401c50030802d112050103158440107001c2d01f004150000303551a0504455070240c01d5550b10000180300090701166900b02040c4841040b01e0024900030140030024030802485c11403043c10511285070a00071070b0b408200c000c00030802d06003080d001d1410200160300840340c1d44501800000d0020405080c644500544e400000309038915007003200c03c01c81035120100c003101c002c0040c0c01c1181d6418068a0035039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 913873920 1250 913872670 913872691
    0x606020a150612050c031b0607020607020a050301020a17060907050d0b010306031709031e07051c06180302100504240e0f1e070b270a03030908070e0f 66
    0x8990004480246010f0f04140c95001c010260141480307400514844c0042c401c2d02101c50103403007103507100221038054520540c0700004000b41405132610001904170f841c002020b1030000c507581c0000030308981c000f440000100310100090300413488580d91355540070390169070001c020320b096400105144280300b03c1c2c0d100780f5600c5900a40d1039100b64800b41c051a800b6403803100761050742070454480d0b0800c080c0640700748200c7c0700c240154400003081c1c1410702010030040c5840c2d81002c040100d080b281d0307088030300181c5d0085a10008161140580e41d01d0000707803400500c050302030f030500904010411003940d2580e41070070140000150600c080150b001180b0b00008002000d180095000d4141d1245c2c48400307120f43d40c610041d012020445007107043c0340f840c484c1c0080c66106041500c0e00c140748220801d03c4424401084184c00c804160245044444103060710b484140c0002801c1108540040c0c0000789407240c02c2c00b404204200d83c1c4050052a9152041d528080c00351000000d402070207540745 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 913875170 1250 913873920 913873943
    0x504030f1d0d03200106140d02270f06030d0c060c0c0f0c140a0308040504020a030b030313170a0f141f0903020d0801080c1210020f07020405060102010606020a 70
    0x20580726000312940400a11000101c0502d00b80100341600c9603400a200c890740100030a00d02c041441694110307070b100d0003805800040201007056090344414141d80100101c7c1c505142c961025004080040680740c80070860308000d2440089071788000c081e076020340c6c043c40050700380581000811a810703900c01804900102c40520448100300c140c000281800a103000800c1023182c0c24800d003007960001c21000181840e5802040900e000900c4060281d1804200501c91400c0070b4000f04000e41c0182004100c02495601082c5541c2c010b130b220030082e0805200900a907448821500b01d8100d502c4001c0041c01c400d42c82d2400c0140494400070840c9400111107080386500740400d4803c0c50140440d00d11040f00d040d1103d019104c00201180140515041012024054000e90f4143da44d98002040b10080c0c000501410394100c0c8001c2c0e80d1480350018410713000790a40001c00491954254694803903100b44103200c15120050401410b40e418103209105040c0d0015078220f004c0d4010210032030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 913876420 1250 913875170 913875197
    0x18061101180b160e100c02040b030c0607030e0f060706020a09050906060d1805060f010e1303120b240d0e01020702030c0603040f0221061b16050c0901030b18010504030f 74
    0x442d0f454591030076802c9480069500701e06a00320751070506d03050003582d00b40104d003091410180c99010020540b54010701c00e2140e00701080c0300700722100807650041e0066054082600000d40c5a4200e43e2049806607000142c0d1f11446038003001da0f10003410140c481e07050b43e003000c00c00182ca40c0261140a1901c03681c90b2507028918100618081c40590004152440ca00300025202d4040c1c000740a07100141d84000c011694180c860f400d80040281c140e0340e0511410f446881d00400f41080240031940000d0000c0b2a112050b49401065407403080c200e09681ea43e1010b440040554180601100c0c0c0340e4418411000540c4001c0380802600f08211411340e5a5034441c6400350304007000146c00794000c42d0080164290074402c0e141c00c0407040700c01048a001c5d54900280038543c140044005980300010301c0002034103044003251500c941d11400136100c8040000300840d001020907401a145442660203005040704000d80c02860710415500038041d510305628041e00103800da8010004203c8040076049 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 913877670 1250 913876420 913876427
    0x10c05030f0705030a0906021207061806140619050a0620100504110909121c0519110a0801050f040e010911040e0703020114070318061101180b16 64
    0x4010744214101c098481101d401c02e240c0c0c03074002101034804540301d8000492802d00010304400ca030013a80801525240e06070703031214083c01e650740045481c00c0c0000210000201240035144017803d0384000d65245140c05030810401c0c150498081239403100040c000d01640d151044940c0541f603241c00c0030101d241041ea02a4800c40036514440700300d0050b09111424041c054220307038000d070700035440f1081043c104010480100300503103d00c1c0a030381c090705a042d044c034013001c041c2040031100f0400305000560b4001c608180c4001711b40150300703542c0c042c0d070481444040d8802c0c81c13482c21103070002d1410308440600203404440107015140c4605030048145445a80f80d400400f00351403250300900002c41503250681c0481c02541d1200d00c140d003071201c0c420301d0500c0007400038122a0143d403102c10403403805402040c0c0e54484413040e8200038840c1c1d03031900ca1090420103600101072565421600008071003c05084460600400807a001441c4440c00440c941154440e004030500e080c1c8ae081a2400358240d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 913878920 1250 913877670 913877677
    0x5010b0405063907090f020c0d0c050c0303040e011511070e04020f040c02010c030e0d120203060f0d050d03140112151e020403020a05030625170a06080d03060501020c010c0503 77
    0x211403143e0300a043d540503100070651408945191500303000c14003c0e510317010164010302803020602d51012841e40f100b184034100100e030441c016803e641e94108400f0100341598403d0b040310445075400307401004001040b13203260160040c6881d10f881610303000303581c06031541964444d050262000d80080b8080d5543c0d02540040303900020820080030312208006406008460380e075102181c58601d0150107030340c011442100c03140240c0c0c1c41c036000b42e0048811200a40004d81425040480300042c1d64450702c0e0000e00301e051034001c20062202904150000b000e82e09000d600c2e4150650034801044401c1601c4a41c480465001c058038426910f0507107400d000b0204201100108003da10001c84070b50341a030b004005890094840c00c9442e925541419500c120a8900c014400018404004210400d070400407150b00301e440c1184440084442c0101d0301ca8042e1200c4c078185c0d907a01810000f020040240e1404030105040c107116440c07600c00080d490303242240a140c140005200c00c3c1d010043c040c400c9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 913880170 1250 913878920 913878997
    0x610270204090606030e0c1c06110301030f17040501140703030e010501230a0f14060c010c1e0309020f10030b09090309030c15030a110d090302010b0405010b040506 72
    0x3191500d6440394100064500361060300701080c94603455a1081300046000c0e56a00b002524410a4001030030f522104a19460002e480c0306549003c07180ca0700118030b000b10700039170140c07406070005041418031024200346000c01b659040b80c01c000420050760000d242d0103000404d0a240b0380c07030303195609094015020f61340070103400b9440e2900206283c04050b4441c189501200d011003000404181800102d640f240548070b07100092250412021001111500c086140503080600b000c940280a07401d42d020b195105002c83c0300c035152507012440b410307009030101d074080c03400380059000c83c1c020030b20040c1a070f01d0560181010b40c40900e0164080e41064075061000760410500d40340502c48152650410318900b4030a00807680c09034058500345400c00440d6000c61052840e40e152203d06074000c1c0100820302400314010703c5a844401154480c0f5584180079800226044488108101c01c03100141c018001c104014841402a911080305849030b0000c000728180c07448850400200071304084125 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 913881420 1250 913880170 913880249
    0x150c030e030a0506091c0207050f03120703170a0b1e010201060f0608010815010b030a180c030b0f0708161211210106080106141e0f0a110610 62
    0x2d205040020010b540341c419003c9005491134001031190b640c00000544045400507885460140309515010710620a80c800080c200c641010231345c1c40e03085880e0000c20051340420001d40d80c3c0e02c052110111456070103041e54030108480b28551001442a2414604500c07841420404041d200d90003544040f001d098a24004641a40d03290070007030142c00e003409800070b00d00802514404440b2026486410f07a940404000e086655071a035800051a00c010b003580300c0180c88400c030000c00c01e01c100750780186000c0d00310380074649801d80301d003400080050700400401407070300104000031005000040c096002403400c0f00043c0c001500e898003070100104111603260700025902c404600f100c00034890004c6c071040e048040c1c0c0e03039248242d034100c000b42304400c0803d15440300c03000041c60303000040041041c00c040c11000946c200040307000e0750f00311f02e1440300c5d410710006001d10159005141d10131a140c1c60002407940b03141ca0707040707511441081c1c8607a1030500740a14142081c0703404000d205048060703412 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 913882670 1250 913881420 913881433
    0xe0c0421030e21010e19080c1501181b050a12060b0301120201350a0f090c0512160510020a050f0109060b0306041703060a090e030a0f0504150c030e03 66
    0x528800d80d60040404503940c0b0340001011200e501241051b21580a000c030510400100e80381c064040e03100740d44100f09800307000d480e02100490010401d010b08401c559014041d0001170145007101c2d9000c1c0b0003080031070320081011916903c002220700c2550940303001c0500d0100210b02c000036200c1900240b645840c040000300300a0706d11b15500d0049070003665429031036007140301e03408440403a090b1501d0b410344039108584280c10405078800d130080d07085040080c10b501d03c5a41c0d10102c52071204100ca111042030310400442c5000400103280c0f013425070140a4240b00080d103814113484078400c80340a4500d0910202210740203000103200f0a1300a03041d00e1807030fa01d00355003d00802c1000d0741191402e160035140141d900300002d003e80300c0c56000101d580c030380d6401c90b14081b85d0341004007a50360050900c0303008a02d40707426000318004012403034010354550200140252814000c07003086401c10905200410007420300b0090b10582c403545061a8004103401c0c01c00300c0d44e0001c2503000399014030920 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 913883920 1250 913882670 913882699
    0x2404090203060a0b070b0a0504021819060b090303091309020306040f0203010c05090d0609140a08040e09060601091a0706020c030703030f0507050702010e030309040c02070e0c0421030e 81
    0x5400861266004541c2a0311240e01c4811401300c902500002034080080000051004038040d40301940150009240114421042c1d02e4050031031801c56540c1c1024082d40e42c1d5400c02c8240d03015900c09001102740040c03c0c00e0b01d440120350303a070054025151068506901075803032800c40c0e80c4a01c21031500502a18103915082c10800e51006d8004400c0340250700c3c00307210340091841641036808800b8002d01c4606080e00300d4482102520303071410180c50f1000c210214402c1720b00100088546c41c0d109406c3e1544031450000340038400d01c07006142500a800c020104181d5a80c04001c103002d444002012241217140f003142c9000c140900e0f0781c0100307110f20000355640304420000c081e041c898407a642c240b100c840c0d441024000d4940030713a80d520214030140200030056014020b2020300c010058200c0382010b403400700140c1170343c9000c002040941c0042c0c2052140140307107000c0e83c3c0c1c07150f101458285864078110300304242214900ea10109a00e101000104151280d800d1040c0c0d00b6000700301d01d8104610 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 913885170 1250 913883920 913883939
    0xa06090e0d1707090b0318011803021b1c080f28021b040c020a050a0b041a01050607060b060c070f05040f0923030d020408010b0127052404 61
    0x2108485000c91100340b080120101d500402501c83c00c050743d02d0180b840e250180006164001611001c01d40100307080c40450283c091042c0c16140076040d411243d030000d1b9040190800800038840c801820f100b00c01d1100684402c0800340c0c5c0c030142c0c050f0324403c240b141d01340348402c0d006100d00c2440e0039100050b86500b4101d9800c0f40c00c07410440d4941c1c1070329600c020f0416640e40540f000c9403007512a002404142c54035017540162040d80e40c500644200941542c2c44034101080c05008540e100d12203014481030004010b000d40384203900d6012101e055041000044440c0141c1d90010502c58071041c0c00c49040d1192003d0714440300c2000e0481c1c10040d21684001e2200d05240039943c0075030314100321400c1e03102e45405008221504400750410b614518007061004071941c0440140a200421088410107883c2c8000c2c401071041d00700019400e0342540004004003d0800d40e020355401c40006d03607410b51010310400d021030300202c030f2016803d110840c14080a100204010070000401b10340021030064 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 913886420 1250 913885170 913885183
    0x180709030b070305150402250f1a0705070f060b06070b09010507140d020a170a060306110c0d1d0402040807080f0708190303090c0803180402090d03080a06090e 70
    0x100e40490003a82d036031030200310222030003100e0040e507201c003040318011a801c19a0040003454010801d004000710b80e00440c5c1c2d10f480c000304040303c90010b0b1071031802c01c0c0712030f00302141c48030003481d11500d50700d04184c40020054000c0704805400350741d8500c04182040320300c0e031140103004c00280015850b00a0340c03c0003a1300b903108640f10034880d420f0000154005116612602d80030b035440421720304025102c02440029082480c012090090a1203100c030b02c0d00b800c4103110b20825520740c0c045805401c600d040800e64085280142c60004180304c100f102940116407074840790101e24056140c2020b0310052001e5a018106040d045031000030085038107600494500c1c20b8440413003c90f0310041500f40e0640e5240220310608240d07400c4020b107075901c4d103091110185c03164001d20300800e902140b529140e51402003603001e16400d40c0009030200c0d40b2001c0c0912081d18440c11102181450865000309155803440300006042028000020b202800d0070f5004102074001c501c010001030040c100c1240d610350 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 913887670 1250 913886420 913886423
    0x14060708100b0a05130f12110409080d15050411040609050d0302060c1b2a040509060a0e031314012d0c06090b0a06061106040b0103030e18070903 64
    0x12604400504510000201d1104640542d014280b50200d41c0b07608641d11781000181d0300400409035030000b042d0103c1012030018100003007681c00a02651704d0003400c5240c41500050040341007000c980c0c00b240d2450140c5910501c400800310702c280d00c00705490385041150b007010b64454a0311440106c0c1500c1240681300f90b881540310703d51100e882d54100324015004c4200180140c1c401e0001402c0754400501400702004042e20840d0407208030f1190340d00f000750a145000c507501c0b50101c258048003c131403030803c07804400d89041119091080c803158860300d00404102c088c0707859001041c51400104200c92195500b1998104042e0321090101210301c8884611030010303407441d0b200c40d40020040700b070b40f0301000c800258082d0b140c99541c00b910124002c24040e02c6c5240d44031004000300758660318151040c1401c00d0001145402d1180180942605102c40002030f480700c1c1c1000001400c1c1c51840e41500d0b0941000c154403d0000d001a1503125000b00100148001e0700a0052a5412504060030349 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 913888920 1250 913887670 913887677
    0x9130603150f0506060d020c070f0b2503020c01050306030312010308040311090702030304030c020a090903020d09080a031409041503060e19020f010e04060f080a1208061e0d140607 79
    0xc401e11000b440c2520800e50b000307a0b005100f008840c4440c0c865600500e203420410069800150340c0c1c3c10701c10310800f01c1d68840403880f2400218044441082008041301418041c03440c1e1003100c082c2c80080d40c0e01c4d0364107241d6040c03140000108015507800c1058171444410710388000c00e81d68480c501600c29030450f02c000c607000c1f1200a4210300c280b4100c00300c0e03440b40b400f91b4000c40c01c55490303072405c44010340e48400a07070b004003421401180c1460540507da880601036001004607060b2030300018800c1c040f03640000941c0c6c0183e034040703000960184840e542000928203c61701c86240a00260041007242221110302c1c0c49240000b04100030b07a00704010180410081d41d280e1400300c2c01c06050041780440003940705000310040106907010307440d01d0800a101a000061507510f0300e0046050b0251500310742c0007540282541c401f041400038103500001c046203015242420b00030085442291036402442c0e1200881f1007100d00d41d250032002220740d84d000940a5100e220500c403264541505982d042d001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 913890170 1250 913888920 913888931
    0x4050f19110108070503130501150902180103020304081c02070803040308160503010807060302090f0409050a05010b0a051c0311102a021e0a0203010203070e180907090b010306090c0e180f0c0913060315 88
    0x94fc001d109482c82650410a828a807000507100340100703680300e0100b000360a030309200481c0800d400c040034500c00c6110b6142ea0b00030b8207160803080c80c41c584c001e44400c00c110007000140104040070510b070084030410704001d40c0700c0e00d20340005104800300442250b0404e24007480c54080c0880005da5080c0580203a000b004186101004d000409445000e441e400a501d4481100d08000345588003a045000786403c062091030101e0340b48c20120181c02c0240407917241c18401c0862440030407092000074292119240c0509621030280d00c84100d40002c0b5020080d0050b0700c1502c01080c0503080c646079004000715601c0c5454074010b055002e1b18107505000e04a2041d8130301180000e280264060350021000b002040d10b08240300003d01201003804d810507031103400001d29843d2900800004400a807940440e079040799040c030030b145903160b2940c80321964034418002c0e40d9104105668000d50400d001d01e64880700080072031844520b02b00c5882406143c094000280640c1e403101c0c50301b000d1040b1040c0b06 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 913891420 1250 913890170 913890217
    0x1050903190f210c02011103070b091c0323040f0512120117100b01110f0102030a0c020a030f2609060402030106060306140904050f19110108070503130501150902 71
    0x90044140320090045441955510050747c0101c0009000c142141c2c2220300d4050301c0d641d84e00545000b07070344409140c0e1020170050b00c02c04540301111010351403440c041000300210480d8903480b103268a030708030200c1d0081010030288000140c0e9585070b145c00c001102d0443c1c2d011000441c1940c40703072a105500c8103a641c00401c8090496444c0c5490030703802c90092429500b079003c101d008002d1b10301014144801000001310649061110003500320700c1c0000140c50385090000f80042c0c60b003050040d01103401602c007400000e0b42090f4508842c01080c40c00b46440003a5441900c500f42c500880340205408420802c14010300c00200640300300d10a40c02484002e640da44140d003a120305018400982c031000740201d03100d0a2041145500c14080e008035524890209401d03420f00000718000505244005424000d1110840caa128841001c2c80d00350b0381441d220100030b0840c000a0441712004000001080500400350400d40b000154684c040703c0c0b00303035100340010095024041d4000c80e111100c7c1d02c1d20 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 913892670 1250 913891420 913891463
    0xb0609010617070f030209040c0306051c0210080603030f1215091627080303010911070b0f190e100e01020f0304080f0f031014030a02030c01050903190f 67
    0x15041c2034034542c40e00541d01d440300c0c01c0e12224600c29101080550900c40344045a48a008083c002c04040d1000203803941004c0034003034002c030a8143c4010b202610180b40c001a103555081c031000200ea441c03c51200d85030341001a0030751103008441d0680300d502003441d43d10803d1030440389000e04061036051140c4194501400a000b01c2200c02c0c0000b0b90010b441070120038001c0f0742011054035000e0b44412860008140d041c1c9070f0a20f07402c0509150b101200502850445100f038610303018042e140141000090fa42e0347c000c0c0c500041040b40409c0710000403a074000d0f1003802404507030360030392405d108001c55501c81ca517907003000d2036420301d10504001040700d8002c01032088989840550074107034034649e220388908070349511010b22280b16890420840300310000e030358041c41c0100300a0417900720b450716241d2001100d80e092551a4441d410000c00100140c4d000910380c0e40300c04013130130000d803100d0300340c000682420720024200c0304254441860b403040000d61150100200e210380e8090f5030548011340900d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 913893920 1250 913892670 913892687
    0x9090103061a01181a04030209160206130f020d08090d060c180302030703111305090304090f020309280503031602010612110904060e0102180a14010e0907030b030a0b06090106 77
    0x1c00c98076400d0130140169104441c5080710080c0008a41d03140950304c6d40401c070810011075084d030084020f141070b4040650f0601c03905070480c10002c8840038000844e11000780110031280001e114141400c440410040c0c040c1c142c03207440d1402804120044454200700c0007926030302800386e0002d1420088039141c81d11051440060740c0d001b070010111107045a90710900209056005035000d46122240464071b1400d00070a8490700340440915100c0340380600401c1580c00560050000301d0061003000b101d00c00c00208010880780c00c4811a81520f103541d031041c0300c1c4d81c070504083c120b40000020002204000300f600441c1914940c020814256200c20409040c0e030a454001d080007051007815a50745040015160030900507200040c1024a0303006050882c1d010349106001195044035202031464404440c20003032408a0170319000d0702002000034800d026006006118410200201d5600e40c400c0c2d0040c90600405811241c1d40b50007404c12080c0b15400726400b6116944600002c98181c3c0b2800300c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 913895170 1250 913893920 913893947
    0x150405161406070501110a020109050c0405070e0112021b01060f140102120d0b09040b040312110f07060b0411070618211e12050c0a0e060c0309090103061a01 69
    0xd00480e0040c1e07000c0101076400520150303181d41d00d449102024400c2c800007007005d2005034000068100080c85e0650502510150081c4218030b44001c0011450300030400700d0300d1401c01d18007044600c0101c16a90020b0041101c41070b107235181c00340050301c0300c0815804081910f01003188100200c0d640c0072410640c5a0a8400700d0040e00720360b0b0716000c1070b43d00c8400b411160140380d034040342012042000c961003050449040e100c7d0b01090080c0710603d500700000c1c4103115400101400aa58602c80c889807a109203800b0b800e18100018101013408003030f500041100398001c00522400d404d4415040c0d003500501c509480b0725203071500a02d584500020300540c8d0030b42c02401c40b500e5807554901f04c44841c030743c034a81c001031205110709205c003010302c00d8840030010019182e0124181d018070806040316401070440445150030040100d0090300b04251a0240c1d10403284540d44101000c12a82180a503101c03890700003c0c0c410020080022980181b01200c1c0600e00364001c0550761401100c600c0703000d040c07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 913896420 1250 913895170 913895189
    0x10c030b010e1c08070816080702011805090106051c020307020d1b0b060103090204150605191404030b0403051c020406030b030a11040216210216062f15040516 70
    0x4840700004c030768402408445e805000d643d420007403010400110b40c2d0519004580054000400000b1584c0001413142000b03001c55207245050b040102050402d003041c000c04052040115031100400e114145412018400a20540d281d08040070040e507210898a80c2c180441d440c9030007400f0713181001d007041e112150480304141c1c1ca51200b00056008002082d0180d800a480350310004040300d0758030003c00242100ea1701c966444203001b4002c103440728080c40302000c104104000404586c504020707102640e0b0840c2c241400d580f65460107903180e100300c807030010360310710b108180d10a8010182e01a100702d807407945080c4003104d0664100360f11605603c0c0002c3c4088031807016540e070390030580d0240802e580c60003024081c84c0742a4a91902c045d007041201c10642c2c090500071146240c2c14840c0c2c0d220084104000c84400c6d092000281200ca80c2c07003140d02d09440da40324140000c20070400c20800700c607400000e8501401000940741d2901000300d8050b80c141c800c2494402c1070900300300c00101100d0041c2c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 913897670 1250 913896420 913896469
    0x16020609060f0c070f0f06180203030702100c140304031205030609130309120c05040605040e030d0203061f02160608010602100f110c070801060501031401090e0f010c030b010e 77
    0x6104002c84002900c0039011400511016002622a03403004441c80e0050700588080d00712480d0078010340701104203896516140030303606c40050f100081541c1c0f034039504940301c4506141d80ca0040302d50b84031000c80500000c031020100c0d81d04680100007031054174000c680a00341c40c0d180d810151064070064501c16003102d000000122150b40c001d80c7c10a03000c0c0700e481d00f244d8403a40c035031b070700b0b071010080c1102900c00340202c8404022503d490b1054400402e02a58140018004400d8041c0c59016801104002d90b40020000e2880c0c0d559071402040001009034a544241c84410300941c1d40c007140c4004683d00006010100d4014040e208480c12500240c0c01420725000c203c410102130702c04400000543c68554070101103a20038100a824a03105d03a000800d440c2e032515240d142901c0a0303a00090503d0301d050a843c0d000c4a410320b034581564040302d00803410209501450b440c1401000c004810340d481d0016400240d0707410f4000b4040e0120036641d1030282c020440411040840035091040c2412440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 913898920 1250 913897670 913897681
    0x6050403050c06090d0b0a0f1a120106050102120309010204080d0e040c030504080f130801060b0a1704020108130f060906240b19050f1303060c050c0c06030a091a1602060906 76
    0x440c0f0030356004800d80c7c008101c1807200c41c800800d13500d00502d202520801c2c2c4403070708032500300aa8241c482c010aa0000d0251500d0080041d48070200c1c2d281d004c100010010000d15840800d404550080c0301031003c85030255a80c20000b80030350156400d491140c2d007801031441580b40300c0c0c01110f0150380c1101346545081c41c0405a00116800301c80d000c00d00d45400800010b0a04003846104004c084110701680c2c4c0da010040c00030812040c000448000032007010070700000d41da12807000390784940440c2d2010341c00710a5041ca0101c050038010000d20b01400c024040c1c0400090350030240b014620415010840c08401551071601c4c0c02074016092408000d014040000002c02c40002c1c20386070505080d8507002d01c1c09056085980000304a00a05610302420020000c0900c206103d1240c2442c1513030a03c00322074045034407900342405c0c0502ca0030b004004200780c610a43d210000c0036510003c4404c2c0d0034400c00121601c6201141c600c01c8214a00029580c21400802c40c54031852001d03002c1c20899440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 913900170 1250 913898920 913898933
    0x907050901020c180618090706180e191b1403280917040b090f04330614070b04150c170622090f02040606050403050c06090d 55
    0x44000d03604510601072001059107a140100783c41102e03e460704041d9103401d0b41844540d403106100c00c5030040c0000d003000181c640101c0d155040e1410307880d0800410411041c1682c80055a4014074203051410082c088181c0b080300d015a8150002d8006005507a0700200c4116040e4400c8e10240100c0c0c00050040300c0c8840c40e8004681c801007076149a2100c01040440c4503100f1010009001c0c442c1ea6540001d00b40400300d507074500f51003990b494092070b2030706249040246010b45565a8003900540e0701c40261641c60b81c200d00c03040441c2008039400c2c010b405800c1020219080c83c80c0e280d00c5490f40c008540d940c4186682500030b001c006800c0c4c5800015940c00d016608003c2007502c0307036801d00f00030194204907402800b204c1c20090b40c402c038009000215003107400c900908a01e208a03084150140c0501031a0144074001140c0400028100f8003800d14003d0381f01410002940a481d11001059440d0000040d10560f80503804542ea00c08403241880030502c00d8400c0540e0110b1440c5620300059413 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 913901420 1250 913900170 913900177
    0x207090207050f060f041115160c09020c0718052203090e0708040302010b030c0a180e0307030203040e070507020f09150a03060c020c04050c0d0b0a030b07120b04020702090705 77
    0x400c0c0c2c100e8414441c00c1c002c1c5401c01105a034100010103801d0140f106001d052013094146a80071141d99401a5512001001e030703104090b500034844243d44041010302c019001094000c0100103400e540d200c4c010400240c43e0401030144110b030359084100c01e2540781c0544104d51140350580080089903598500d084109480c051044041101c020008110071100c08003040c0180056212191981000d24010342900c00b4608001e009a009a0204034141c3c5d94420860454a2121400301c404a51240d1840176021034245002d05100c0000c4d50401c25500000070022201703a60640e0320030751108103045407240b103000e40c065805804540d07103a07000c1c0f900c00c0105d900300c00d81d41014506858100007159038188681d1040e100319550742000424a90103100c0c0f05000b101c1140c1c208801d240c401070904403809052080050a907a95100440d16180c9103280c001642d00300c1d0041070246002d21000b01481840e540b0380200d01d0400d540d015050600e03000f40d5040c01e500508501c4160380780f4100300c03200c0c3c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 913902670 1250 913901420 913901423
    0xc0111361c080409050a0f020705120d060f1d01063621053a050f040308030603010f09110f040b0604060309170903120a140307030e010e0d0207090207 66
    0x410380340c1c0500041e1200001d000030804030302e010402e4a00340c8a40703000c44d500d05040d1151180100020700024102182c000060a18a41420b031901d003450310040041045410460340c0d41100c41c0c021034284403d04000c0120b20001c1c013035195580e26510212a603d0b151002101205003511011079469000358100039005802e0090040c4d040d0f0380c56204800e50203501c1c002d2080b158512488090000512428440885200d200843d4030500080c00c095005c070201107405034540101040d94852141f01180c02c4440400c1449483d5030f12420900d0040c0e0054681034825880c0080b200c07000110b9020342003140740c1103000040560024401c2c03182840404601741d6110b0ba5856043c001a5280405000a0b2140c0c1e40c002030b011100786400c90383c14008030007040e000e01060200070380780e50300042c94101500c04000150307207504c100b01003940c03030f2042910608030140011007000891a4968407204000701124028414400f01682e01b649480c080a46540180c1000c1d20501c0030041035001400081e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 913903920 1250 913902670 913902709
    0x70513090e060c090f2205100f05030d14090301060807080d0305060a0302100f110a12121103010b09060d0908040614031005040504080c011136 63
    0x12104584140809505420030403800d0341c0c808041e48a000100011903001e405400c085241c00741420000c1c0c042504000a14407440b03945141701589000025420a40285c5060030300c15411b00f45c0d109040c0d5603460103013019412201c000003405180028140721090a0380e00c80b80f00c01d082c2d82c489088030354407084000d5055900c90400140c0180104880c0004005080152214451403c0e0080542d403014000754840e070104c00042c0056030750300443c0000034610342001399190b0107114050740ca410302101c0313024081c02040300001c140b040a0302c2250708060241c0d074024828406000c0b8200319240300c890b442d5074840610040c00b00ca11130000810a641c40100311b18245200520400300303864926104540069010604100080d00048884050f00d42190070a0540c03506a540290b810701a110740c0b846982c5880105080c03140c59400c903540e40c0103460085c40b03200b02c50200d5a0003944580c0c4e41a02c010b030404e5401c03d0340f4828080b191414542c0341d150052215a160800803040d4020078a418075 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 913905170 1250 913903920 913903927
    0x180d0f2f100510060e1c0f0813030605160804020906060c0708011a0a030b0406110706022a0d0801030b091c09050f1c0312020c102f120705 61
    0x400410072450901503200500811203241c03600d541c10159407150711030b00c24030042d803080382c441d60b962004902d20ba04806807122103107255030030400360006011401a04040b00000c81c5114500b1004059040d6030190740b0910481d02e4040068443c0c000040702d482c00508000041001450652811500908010032b010300b000e80c032641141c202109a840324009031754a4147d85001008100e190000c1d0320304481092001e0b1039512130f989440c40040001340001d83c0e854490003030344001000d0380c3c88540c10000454485010072001c8144600103030340c03d0f40710080d0854684010030000b4500c0c41e1280c40d43d440420076441c580d15001c1051024000340100c0c055429007101c480c4c0401da00360442c080c965107070b1407500d16001c1888480142c100c0028054276000c502c048024100504c450034480d414540a01c1c002c509800b80002409128010307610f0340034040301030415075000d030071200b9880350031142079130707204a80d03240c003050310229800c3d26001308400c2c400014142c641c03035903180d0700c0501420003070315 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 913906420 1250 913905170 913905257
    0x90e0a05070504170c10080603061801180302010207030905120a02151b150708040309060f0c02030f210403030c24091401141b0702010e09180d0f 64
    0x1a107407403106090032030350111784400142e14102c40d91140003042e5060402c45400e00a0100740c0b10000200040c03111054181d4980080d9425404001000e11042540d91704032140e00c0c009002c0d51251a059001900d43c4401060501d007070345150104141c0500180b41e004142d500b40240000800007032a038041b02448155100c030303e00380001442c4402c68000e0700001e02c2c03001e512581c40d00041c0101080020480c10400042d402000f000c0c00e4034828104541518004002150b1800302084000c1d050301650039010049a80060303a900c040f82c1407a0002c94504282c14044a18080c0b4800070300003801180c15200499941090595507856109413124003a0515070036000b5a509060101c0d2000b54100c480420010280300b80b410352880c1d161082582e04100b1802c0e245034805d00c03150342034440f000078124216800780032080070521002d0700407070700303454081e85012880f5607a802c1c62065010340c08801503514404c00d070180447d02d1540314007070010b1010350920301c0c4400c1907900c1d003070f5903100c4c0c0e0380d008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 913907670 1250 913906420 913906439
    0x20406120510050d0323040305060721050919060506031b09060f0a0b0a0c021302030402010e01300912210f0b031504061a0a17160906080607090e0a05070504 69
    0x10550075600001b17a503141d1440c83d00e24903080c40100b4010411a50f040002d486010001c0c0c60054801040400700d036544500465500f00f040125034101c0120807007804008010703a0b43c00540c0b04103011019240c1c011072a9140100c00d840103425181c1c0040100d00046c82e9141c50300d01c01c10201005040640220b0b12144440c0499001e9a500070119000d598400110314007c102181c039082c0b048019400c504150340042d100c00051a40d4034103220740b400701c001b40442a084502e0a4004c070307245424401160000d0503006000d02c00f402c3e25011012441494942d01402e8451a4210411400c092a00c01c680303c103402029490550001175448160360100c0ba9000c100303140d4841d101e07880707445440c00c3c14500801241d0344804c0076184056800500f0380541c0c0e4001c001d000320b4141001c0f0403c40e5003482c00560802e1034a4107001c00d044002280856100f500713030710410681351128110b60300758481c100150f4004806201d11250000542c0c000398080c10680c0180d83c1000c0242451360515031640c40c0c45 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 913908920 1250 913907670 913907717
    0x1202060322141b180a11130e06190312180b0301060509210d0302031e1609210201050d06261b030303040f031e03020406120510050d03 59
    0x450481d800a800c541044a4114030070300c049400b00c611054203c180341e81403202c10002821059502d5607041042c4034060104102c0b87c44108459075501c4007a210085d182d003216054a290713004003046600e90314034400704284031003600c3e0011400244c90100c05401c460700e41c03011449035052005003000007203006a200c05540078080b55150180c503203104000b4022250044400e001d0000044540b4030f85a890100702c800b1405150b00e030151340c0b540e03102c01030502d85030801800400515440104520031000620b1183d03210890b6583c0c031030042d0386070109103081c628044d20640c269240d400d044010360180005101d011481c840215401d607a5500c80103030002040304200386903c100e28403001c00c51050080b400c01c0d5603404010140200548007180d40d90100800003440201c10b840d25409150090300014102441180b145410b02841840200a90051300c07505001c0f0b4520851207000070483d010f081e11561000001401c1d0618003001c001030300c0d0001c1400c0e4284588500741011070180941503 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 913910170 1250 913908920 913908953
    0x80f0403080c0c0a03170912060a0203040506090105010f140310050106031a010207031524031b050d0506040312021c0e1203070507060b0f0405040506070201061202060322 75
    0x45031941e1441d2086401d06890f0005103108020070360040c40010062001d1352140301503000210b13141d00d09600882c8030426400030300708a500c03a201c10890b00d82d0080d001107100f1840341081d56582d03250080b1300b600780c031070a0046000850001d24284041605000c1072202620010304075a01c0d40a4181d03030700111202a00310100003600d600750581c040d040318010452981e42803005000042c80c64031819100102c008914119030345541d21140c80500303035104110004031400591240c660b40f882d010380c208100800302e03c90748040300e500050307900c1e004e510840750325008405407215541d159000c42d44a00c2240800c00c1192b800d00580c1260051481c032252961403040e8005480c001c40164a2700c1c00010500b541c2c0f400904200b000009913010013034510055110354040fa60381060707030028003038961482503107030003a00d407104100c10710000082e0180280d0154000301b2a0303036166800c2000244111102039000101007000c10301540c003180e04010310205055031b03481c00000555684120001d020341 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 913911420 1250 913910170 913910183
    0xb04092001090618050915060307020703110a0506070f05031303051e0d05190e0907050d11030601050a05070512070f050d0219080a021203130506160804020d080f0403 73
    0x5460495600b00d44444007a00440c20031001c00c5480c00ba8036040c9a66500403a40030f800f294020030340203418841d0109241800901481d16441c03c80d90003542e8034800c0c442525501c000c8070704442c075401c10b038006d1405d548006d090603141c10181d0322000103c44003584103e845102c1000100c0c00321401c23085c20405988508042d1500000045039007510011024901d00c2a0704001d00420b810f0707420004881050144c0300c0e1816003117000001c1501d031641104031540d00021190100034030310b9030080c02441e4940c079407242045680781000580007240001c60704580450f50070400c4079411402071000e004124072401c2160b41081c0d8201d4515415041004201d80c030603806080f91007081030511400303800b11224402014003001c255601101200c008202401c00c3d900000c0e0181300c5071090050045289404581031360702d080024172400b00c212100402d0b5040d01404021901304141c40080c448132208983d148406034646408008400d00049003c0b40d45040420400d09441135070030203400154000c41 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 913912670 1250 913911420 913911473
    0xa030803060a090e07180c0e090717072c0102070b0f1306050c1b090a0c0324080d140702041e0504080a2615030a0c0905040302010612150b0409 63
    0x440c0526211070146d54409840d003880c1555000701c0d401014000c2e008021036230080c154542003010744034943e00c48030790445251500b01700031116400540d0f45100701c02200d505034142c540000c01129058146c0d480900503000442c00700410740b05080070b8106010154411860801083c0040c40340006c0c40e030020001c10030104400403141d100740010070550a000c0507109103801c0b1400000d0311510000c10321641c4a42e9050b009030282d109900009072520b004072040c1d5003540f03006200030095030303521419441d8801d4a42940c11648076141200c030352058560b05500b0214940d00300400303003900c0d0b4100c0ca80e000a2881c1414400c20354001c0c0c5002d540540f0016544e0807400310014020083e07480e1900c540035070041030410009a400c1d0281e48083c3c21840b5200d06d019243c00603003806001840030749001070306040464181c10550180d40200e00ca90002c0003403540d9590f08055141c0100005425020300c1a11040c800c1d00f0ba8000b204040801800003030906e5040c0da81d10610b0b8214810303a100e01000c46c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 913913920 1250 913912670 913912679
    0xe030d05040b0105030d0c06020f04120f12140d020a11060a022101060c0209060406170625020307080306030a14030a091a07110307081f06060e0a030803060a090e07 72
    0xb18040350241401783c014007034450201e04080c08003000c0c8440200304542c0040c4007441c000d10a0b0541f00900070964021805600300d09183c8075000d0700303400036500b03150004449481d5a02609011007030307000c8000503a0800c00449416002904080090340c1032020708400b0100e94030042c00340902c1000b81c1c000050f1142d200c0750307000382050503031074440b444018030790f0050100980040c0c030800181e0341100d8240d816519100400e015086d44d82c0b0900b9400c0d11042510380741a00440c200d48111010b10740c00503004503003a00144114207403010040503800411041000c140e1b4040210b9001d003000d4100c41800c007080e911a180402c00c008104c801381c00102d0350052071707076208418000034030580e4002080407030703c3e4000712240e1081c1c5000a1140c490040303a00301c2c03524140100300040400c1070550300c412031a182d40741030500f01c8104103280e840c54180041003030783c012401207600c440701400708541c5038299500d1000b9a0b1024084652003805180c0001c0c0a6020340180c1810380b10500c064030085190 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 913915170 1250 913913920 913913933
    0x170703230708010b0d06150306020c01020a030b03010b09061e0a150f031413050a020d050f0f030c0a0b190c0e0a0e01030f0f230a0b16020c130e030d0504 67
    0x241c02c0180141d0400d1201a016641e10400e03040903500070100040d00d5035a8600c03010001384541c4000c11040c000300b09410321101c194003900180b2280e440610900a4640401d800c070b4051500590303000404201245150400002000080d000c484040c820010030f4000611482c00607400a0b08074008010000342203984044042407500ca40e0078140400303040070310003018070040182007515842c1d0002607001804030800c000252070380c01a0005c03515046605202d921400e01c000405054418005000143e00d0000101d951404090001d0280d200b82941d80d400c0c1d081c4047d002c01c2625000c041c0c8914006c00900c02c80c5040034503500d60b07440c04100c2070b041c010144026030200748988601703001003020904800801007002d40c0001016054000303468043c4121821002100052620201c114156070001503001b035014080c1030030408960342c440d809420541420804001600410030303180e0710342881100c05510031025440452000c00c02c241e62440d5402c26031a040c80151200f0070b000a1244 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 913916420 1250 913915170 913915183
    0x2160e01051017180a0204020417010e030c030a181805040b061002070b03040f0c030f15020901020d0f020f0f03090906060703230706060b0702090c031017070323 71
    0x502e424010002040c0c82e0800c407121400822000b1501480c00801036815810300903255460350081046407610744a988104004549400c204070035842c009160322038003000070507038044030f140e000150300d0300f0350043c421a05200c00100c1201480e010010204903603100d4107041c910b4081020002890f03140c1410041c0c04004003400341800790402c1210022859404550b4100380c130060003c0ca60340c0d403940d00d8107041891901a0190441c9804d04000c810130812141c050002c07809219070020000b414000181203120301c19040d80942d011071002001c83d070052101c4140300d0003500554041c1140141c9003030a080e02d0a10300b140395080020250b0203480c0c050a0950021019030741107040a44035a0080c0049a201000c90440c0f50700e2480f15a02921980c0cc9070201c2d58842410312600e030344d40400d0444d43d080802c04034840c05801000130034001c1c2d0707001520320680d40003504545e03040c5401a640412007903410301c0451030045c4d290100101b201101c021505c4140c50421100c00003c00f2642400d211 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 913917670 1250 913916420 913916449
    0xa140304090615410c19030e030619050a0e0d0e15030c030c03090a170c390612070207050916080a0c020102070c0f050111010b0d0602070302160e0105 66
    0x80131000f407052070240181464060b00d01d050901948011121130fa2092805510407510980c070944520a8074669400054003103680300fa1240380f109030100003015220360045440b5042030401000344680d000301d41d003040e85c01c420001d20015454446d00da00e1820a6141c610b000c000c25069010a40d003401c0003080211101d540450550440c00c10341481e183c2e40c80040c008001c40307800400030480c415400e10140301800e03400201826030a90380b94201005410180b02c003c00c9004c0e500702d40070301035144148046039071006014002d00e1000075900c80c404000c0712107110380081083c4001aa0211b102803424002c20032600280141071802c010422f803e400103003000389151651041c0e044071a0000000c0c0d804c480c1c0c0307520105a001000000304d00a0040c2e00c00545901c0f00b400b4001a181c455840724000c0d41d4081c0c0e50008071074806285c2a007a0790381040500c0d00941d401d60032201240303940c0d000c0d206c40b5205c0d1054456a070303c0405c020500c190310360403c6594000200c010005450a903a0009800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 913918920 1250 913917670 913917707
    0x1020105011503092102070303030b030105090d0f0201110c0304050a05060708090d0206090907031a010f14030c04030c03030806040c030c0e0f01050d0227030309030a140304090615 79
    0x66050000642e080c2c20b55803481401d00d9100c1c0391080411010000c0500f54502c090a41546000c00000095a4201511040d80400d01d0241110000e04060107100c0c0701e100404018241c041e2805011a0500c0030178503001c04555036540c03007884098200c00100890400440115244c5007020100314264030154000b5115032400c008000014440c2e409498180380102c411403004055800495401e11810a0680c4e0014120040102e040c0c0c159020281000903181e803442c241d2426801503a0460841000300082000c108c082c81c408003d0300019648000381e41d00541c142582c076070311201c811b155908210003240d01c04082050601741441401413410240c41d0620030b01c8510007007c0c0056041e00d15150048245a0140405034094801c03a02145a028021541c3d004e040d0340c40a203076600d101550148070202181850140740010954840172002005000c2c60078540e903440c3c002c458401c01c0141c0300d0005110018100c3c0d042d00c105001406d801848546401c0c0c94035008040d4400da581c6800320 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 913920170 1250 913918920 913918931
    0x111090916090b070510050702150606130911041505030109050f0402060906070204090b15030c190e10080703120e09070e1003090c0b09030f0f030a0c2f0a05010201 72
    0x40c0d800341900003120801c64841d6910344c1d05041803400c04010500d14002c550401088c05003480c0d001448400c2110782d440441c0c0c203a201c030001c02800f0b00c00d04104000d0112651024170072103e0690000104614160405103000e030f1307070425001581c0720340311010007007040800104080c07205c502420b644004c004100b520ba5203041d6000811070b010320701030f45008001c0481c01c1c5003103481d80d9000680300c2c3e40052010050389001407105000031000300015000303000c2c0d4800c1380c03600d05001c01c0c00300305000c848003800c041d00d0910101444e880380040460048040420b0000b610850901c003000296008401c0225204002c1601420360700003142c40d83c0c05030304a0740400444580c0104c050a1202049a0342300d40c0c0c1c110000c048010b4400203001a09544e0400000912070003003a003b001a4101039040d034000c00910108240ca5844c40395100c1000c0d0000c1040e0342c402da100f46841d944017407180d204041c0000c030050a0001361924480240310109201c00e10071058507100306c1c05002031000344001e10a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 913921420 1250 913920170 913920211
    0x507120807030809032208011a0d060533012601140a09060e040327031e1a18010b0d02040e2a011d030a032001110909 52
    0x301881080009000c101803400440c5600806000b1225410004115a40065854218034280e41d20a2241524942c68908491a0340c070313912101400030640103080a5143c5101d072164805404010315151001c0c220200c00314035807407403c40d095400b0700c0c145400007100b0305500004d071124052040c101903a5018004406400342c0c8203a80d07505480e5242c0200048200f09001729a80f806141c101d4204036050003000301c1c4c43c2c6200880548914000d0352040369601003158103408200c50f288040c242d1030141c0c8018804202d602d0103180c035440740c9080004a99110780c036540742c440e41d00c02066240d0060f100604c0100300820552a070302c9060a00208051104000000d4410f95403010007802503031204c9003003007101414081c3d00000006803a1884010039010304d0103a200c202c51449a02007a500c01e4031300254403825a41800d8620040d000b041084115242580c0702c132801e0404844c0c96088811046070341800380505181070f079119004903100c1c2021801c02c110000b00400c00651900250210103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 913922670 1250 913921420 913921433
    0xa030b041401060b07060902090f01150c050a0b0a090c081b0f040906020a0503041a331002030d051b04060513080a0b0115020a0b31030903050712 64
    0x64000394407084205020100d0204640503101c607600900070b0950100e012818030600d41c0021100303034402c54034944296034403650000514001c1c05a039410030f4074030440422a078010141404901e005100320cc00c108215580ca842203c0201d40ac0f440c6641c882c03c2010400c440c01c031a0701d0140440c0d001510054040c5228881607507125464580300796100d6040100503141c590000702c0f40c40d000501590303078400080c0e000e0080d50094400329440700702074000d4101640b03140b48a44c000d0221304030340b10100c1c0c4042085d800d03040b14411b6200f40614a213852150981ea1003020000340c8510350081e540300d155103404070080304c0009000701515403c0740d04041003040c003a401c42d01954402c2c1441501c0309010f803010804541c05400c100500c1c40b40304403032410b02c00c4900a060407550403a009959821400340c04a07112103112070010701c4842c8420118209a4200090401111000b003030305a00e0b55916941c89043c0d01801016004188403034002e10622400b40307c91300240180d100108404039542e030740c20 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 913923920 1250 913922670 913922693
    0x32f01020303070e0a080706031b030b0102060606030c0d0e07091d0c0d0503041701021e0703090623030a0203090607020f07030605100503031308010b0a0e0117190506150a03 76
    0x1641080b503244c4020710035607074005408000e4450b520455010944564024005003484812510700c4100078000c0c01d9607500c240140c000b1180c06a000c3c20660f1039a5052000700e40000d04226980e21080c840c001c840c1c40381e8410000c07660024001406164a80a514800c452400032406085590341144011441c00000c07215020a0141d078540542c0016023080da0541c0202d8111b9040c0034010301c1c410710110015000340c80d0342101d00e04015044060a165150980f0030410010017080f440c02080054500420701c69003400000e10203001e0104486092408a074012034202d40599800b106100300450704001c1c080d480700c0d0030b000904200102070300590b61404c035884014110b5031200300244510f00c10b0700210b0010800902220b840324904c40301c040510b18031f800f9641c2c1c15880c100d2904e0192406817075100448401c6040a0304c240d08002d440000519503078907548892152800c0c82c0c48494940d03400200d43c0340204c4c05082304d42000c20401c0b855a0754289600e1140d50000700500101c0d40c803203481c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 913925170 1250 913923920 913923931
    0xc030905010e03150615030a1505010302180d02190308040e100303140c0c15031b0a0e0f06070503160b0a090b0c0307110d0903050c040203040c061d0a032f01020303 72
    0x1003101660b80d480000c0021041c11704d051b4440c0300100500403400100d0b0030000000d222074040c004800d4644004408a005011103642c03242c280306034a1245003000e40d400307103803240040c2400c542c5000c010050b25042c545580212070790000041d08000f03c03080c14001c140c0041c00c2c04900d98050345552002000b03e008000c410b40301000c0040d480c0404442004131000e44034001d8448107400c0340300c001c070000356001201e841480805442c0701201800c004000c43d01398a50710b450b00f1210301002028880c6002ca411041d580100c1c0c104418000b00e02e0030006448000c2c1c1000b104000303070300c00e8984100030800141c81d602066050403550310019150700c2c180ca40c8018060902502c96449200442c0e03556080c3e80c031545640036921510b0320169000031070310141c0e4043d1044840464424041c8001ca100458001d00544000c0d0806d002c042d115040301d50424900d07011216000c4c40510014055151540c41126201007200c4c09242e11800010041500f02441d848076107030030b40307006c0040d40340d2100419 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 913926420 1250 913925170 913925203
    0x12030f0d020c06130303050a0e061807030606080307020a09020304051905150106030f1d0a02190b180103050c2a0307150e06090601120803070306050607030c030905010e03 75
    0xc10040c0312005506441c0002466001c40d640e6082c02507148403420b4030010140d00090811000483c1c0800f180030b14600d5030b21081c0204000c2c0e0306d00650b070001e2a1004000c0c2e600340195600040400d58500481c40980386100c007460f40c030600d07841000700201c215848111124014020800818000304844250030566444002d20148500d06241441300b024460910241440d00208966034168001d00d02440c0820003081240711080c50901101034803400c0302c04961022f080c080c01820004e2103507207450a44101d11140940361000d42c0c801d0b402c20f0407042c540c00200403081d180d81d03034940202500800d1000c1054030f4070661000c1d0082d540000c0e1001000304611741c442c070303203401c00800445a50a8000c9400f4400744000c1100354017401c030401c803550342c52084c01e01085c0f101a0108146040310040c40d8120104100c1356511030701c54000a01c0f000c181360391800001483e840341401080349501c240c0c3c900d60106040e1402410400e13030350302700c14104688000079210944002402d00c180018411 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 913927670 1250 913926420 913926427
    0x20a030f0c020a09140106110c0303040b0a021905031c0b060306010c0201020705210c0f131505060307030c020f030a09170c150a080a09150507090b040803041412030f 73
    0x40f03031809035294044000285040d00c00c8418051000e03044d810785040da600c0407055a6130005060341ca802c000311499040d0405c000070005074030349078002c0c80c000c01c00b801650f45c0f4007614680301c12545a4600181e40d103401c0007031002c41c10005000803815212600004121464400c0041109408024902d50502400c1880601903a008020a00c02800010440c1440d000701c0508031880e44411704406086104242440e400ca107010070100d070070708501810f0a5030342c40c5600d0003280034044001c0340d0204070308038040109140e00c03140020340c0f00301101c1c2c40214000307030400b00081c5000b00c840350346003441c0c006004950125a0104400081344d0301c203481a100061004550760070110b681c81400d0303022460820b01000c10200201419184502d500d64a0f010358a000d4001c082c0c0c1e07481e02c0002d0000d0203407604030716980d9042c0c1c0b05c2d0f40c20846900d030141d03807640c0320072446485500c240c00250031039002040411501c0442c540c1c1d491310300c10a0320401e00c000130b00c190301540c902590103002507448010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 913928920 1250 913927670 913927673
    0x7060b060f04090c390c0602070512030a02060f0a0f061508060f011b060b0a0f1a12012303120309160b040b0f0d0c03090606051807030b0613030c05030d020a030f0c 72
    0x100e174158821030300030074800725969440c1e40c0a03554803458445c25000300d104a0011035000c40c00700a40d210f25007160040c1c6143d0791099440080c20200500580302159503024004981c4001d00c2540050852020b00440300100404041c0669030010606407160062001c19038890340d00820041150310780c0e800041500301f141c90b1402c05072003030000d1260000d0ba00c00c0006400320002000714210b03041b6100102d0000050300050074070384500d0200e0f40c00303002c54000402a04ca05450684030144048100354034100304140002d082a0212600180200c0084140190840184452140c84501c45140e40b11149802c61804180c003803489001940d10f07001c1007680c03180088200310b0f59180300742c600800c00c41c00020b20280060040000946109141020110b03542c00c02203100d0022240b9100c21112a5895074400c070090103401c1ca0355508010180312130801c0403501d605d13090285100d024028140d504040500d454640080140421940090a000d010a401410018148426242040326000c0c2c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 913930170 1250 913928920 913929017
    0x806040b1f0e0d0803041a070203040519030b0f06040507050c1b010c050a12031a060d0c021e030304291b070b0903030a060605040b040b07060b060f04090c 68
    0x165160b158008014030f0120080103521002517100350304c01d1035140c060141130b150540f101c4900300c1d189809079101300700501103460f04400440e115400d28002312000d03501c3c1c0c1d46d143c0c2e0722130042d203104010707800b40741c1071015501d0b190007180d80c08140c1d45440c504006000311115a0703a11844410200203181104c071052a901c19040011410340010451300b1f60039003450181d4541000042c0100002d150402110008428142a9240c0c440c001c04c1c0c07a0406c2c00041130b070b00040409039019000c3d4030074140315034040c0c034444841e030b1113034984c050282d501d034913240c01c0103a210031004d49112601c802400410102c08092000c054101507904400c6d0350b9542800140c41652190f00000707840d002880c1c0402940340000001180f14019140b400c0c1321079980e8600940c2c0b41e014074081c040d9855018402402a0b111210103040841d028106c00310b1440d40b1000032a82c0b990100507040d04003070000509002c120018095a2622000c5240042c001c2038071100c01c010102803051604040c0e912100503200340140e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 913931420 1250 913930170 913930187
    0x1802071e030e240f090913030201180b01030605271501080307082203060f0b19050a06030c020c0604090501230a06050d091b051908070506070201020a050105010e070806040b1f 77
    0x8020700b60b2550b5042c418101d031f590340003040702103005600303020b403070003003003000000ba07800c000d5010240c0c07007a590955030798501524006240e0b0710184459040213200c0c2c036050444614200352040a03001d4100380000c0b9440c044016003151800354020045040040c2c2c1c00380440300c0007aa880b0445502d26070b440013440000d46503600103420f4608010328500c204000340c0c0501c209500031030b22410f07500500c460b81e903841d4a1604c07403680e1104c880c2e042013140d00e002c0d4002281c1c0301c0462058995021041000900e260402c0e081944055078030300051210100d5030917010b202d14101100c2c61009005000096110071442c02214100500400c0c820086002c0380c119049450348a4018542e08648040c1d0640c40c041c1031094612423008040481ca036042024140026a04401c01410080d8100424400b01740c1c405030040f07045214062a960104000f032007514041c0940c10000034150502103401804040e025080500c207602c1c00441d0807055075400c3d003c6040003400d4692003000c065081c0e050b00c480c2c8c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 913932670 1250 913931420 913931437
    0x3151a0c0a0c1d0601080708070c05031603271413050f062416080c070f05090115080424060323010507091802071e030e240f 55
    0x101d80001d81c0e0030001d805600344250750030200620075036003590b041c0d420000f0f03080d1070040c040303242c04000c503112a00c01d000031540000541051704444140c1d42e5018559031000b240d2055009203590960201a072042291005c1c07a86103086109034001801010150b0300c0c580b046071781503100450503104649038101440e141c0300710464100114a020540200d10384400c4031014400c41004442007003008440000882d0520700c01d180e181001c6c048001601320070343d090010b40348084144010307110110100419030203001c01d280002021840c0c40240450300406030050b55146101000404c4521341c840f8005d64069004060a0516060310130001401ca00c6c80c5100c190301424844c0c00310501901d060800500040d12260143e0b000d0700d000554202c2d03800380e42c20000100803c3d410000d031804c00000c8a211860a040140345c511540d54155525001c420504030158a42441c00c0a15402030204508200191442c030115610f15004040f0003a00040e02c240000c0c0201e140640d0204a80c142c0d180e04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 913933920 1250 913932670 913932673
    0xd0c1e0204110f3f10090609020c07090507052b0903022401152d1106100b07080c10050a05041401061a070c420e130f05071e03151a0c 59
    0x103855008d4540a0f51060202106c9842200300000c0c07070354270600c10340b44149650b613641400c03c20b02c00c45500030303c50072105801d43c0021845483d40340b04e03c0b030310443c0040c0344030382c005003000c1b000307041c0a0030f4040130400701c02d01c3d11945d8001004260401d0424880a42c0f00d46003d04d0208080e0588144014140003014000c00c08030084a40141d049604c1d00d0405000204917102a07440c40f42082c0d50300d02d00d00036009004403d000800004210310040c114080302c640a84103e1401300c5208412150308440000c8855120b2040c00140590030381103800700c80056000340716040c203204519000081c0a0464641a4000510082070000d101c141034040c0030003061003002da8491400065400d03401103c41880b48400e0444d00300301aa82101d80801c819007911440c001814007001c0062032070240620300006a222410329020780d007180306081c807509403074880b074a840109080c581100740c11407090b007091500d41007803903412031440d84050080710001d41140e40005404424010309005111000c860b9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 913935170 1250 913933920 913933931
    0x3060103150314070503010501230a09110a0305070f0206040b150904060b0a05010f090501050f0412051b012a050106031b080d0c1e0204110f3f1009 65
    0xc102203d007400d02141c0a460864008940310000c1600329034007803003900e065060701501c05030701d250074201038550400f0043c410340c8010303a9243c1e004140e42d141e00c1c3c4914408400104550f1440c0c151240c213400459514141d001c4031111400650ba0f0f50024101801c00c5407054000380e0701009442c80120140030160085000d4146450194058108900200c0c450480000045015485140e00d05516020356491a142c18502801500c044d030241606130003c042c01c10010801c03010354030000c3e041d10301c20b900500004201c00100c1944d00c00c8200b116041203066a4039488841c4440108007038000061520b801035000c1e464907a0040895070300050000005039800010580a42a403404403030b00c4200383c40003d000003204440c4c001d8403042c01400388042c2013100d15812800140e0100b180d10141c4005400a00e0b45100725203a001070919400003a000102410704c48580c10440d1004502c2810f40915012190400e5017200022110304007410f09200000790b40d056181c0c101001803840d00400c211 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 913936420 1250 913935170 913935173
    0x50d0b040b0609130624060c0605010512070b18030d020f1c120504020d08160312050103080403120905092e05011416060f0b0306090a1502030601031503 67
    0x1005181200d064500c840e01c0400a80749041c0040d82c54032482e050b503a911207506003170707680000501043c2c0445070011404a510303030030701585140510142056455031a90040c803440c0c03080542d54140c010394014144002c3c0b005803e140060340303000b43c030b00d000c240c641c4603414110507024114022a459a0501c82c0d82c0704103410980200d03000c9003120050090740c099020405020001d0780200300d000b00025441070f8101109543c40c3c0c02950807620081c00d8120303c4aa070b861707049042d00301940c868562000340804404140e000414500c0d1020118030501466265031160741c130b103024510010380714210050102520a101e99030ba900900401020903003941404100d0703440100c3c06401d1800000703441c049400280303c1c18885282120070507074070083c040543c8803002c0c40756008121903501480003c4c145800181e454003414041d2840b040000a42903600f070708043c42c2c1100944034074403e4100d505480041081202c4041c0b01400b07000016a694898000403401008945032042041d69480400300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 913937670 1250 913936420 913936433
    0x20a0306060501020d1b0f030e03100c0f02190b0601090807060207050f01022d07080f030c1903050327060910050105030d091203090b0d0c030515011710050d 69
    0x2041d0b4100307034222207100e60980e4064034109014020b042c607003406601c21200141580408000d41442860505401c83d40748000c40c1c0303008070a0f80340428250b181c0081e04151944803480c1c2602c441c0f40c0c8001e106400c1e0034620021042095035018000700c18800000300182d01410802004180c1e60045490260303031407500a446070118085c03c0e1007200c00400610296200040264100c071980515040329079000c92161440d1030040300810350b5000c0c1c4140050317041428002d04490300b000001075a030301d030745981ca018184250300510030290708855020300080ba600c00142e940c400d01200f281402c1c030401021294290b040e08040c40500c0c07040c8401c000200303d021401b4170030b90030065403d005a9880790201601e46241d1418400001c80c0c0320400c004907611807403a160080d00a082c6001404d403641c140906076440920591324441d20703030248440d91503051040940c080b500203c3d140400516000090401d507405a40550414050002c10440400e0500702d070010000246110741040d003505c0c103507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 913938920 1250 913937670 913937681
    0x903070819080c03061804050c1903020906010903050303070807021507320901080c070b01060801030c2103030c02100203070c0c090509031c0e03040f031506140609030a020a0306 78
    0x4000244542c001c0b800c81c101820540f405444018042c422400401c200306005840080c801e803410310494154820701e890b442005030501c0742e09981c00341c3c200e056005010103032101420300e50400031041c0081000c0743c40402503d4200c1c1c178500e044441911403c0c001c0b403a0400102900d090528010180062036070041c4442d44451616644900c000950501d5180318509200c404940b00d14100880c0080751b204003106a44807021a1a55043c407044d616100c0100501740c00000100e85000f0044c400e001c858046c400080c9242011803681d46007000000c5d282c242580d00040515840303c112034a03041c000d00c025182d13802c5d0000e0464491828120007010742d44421801e5507a141c1d0003c001c00c0001b803030f0203400e1244a030003004600c2c00322010361030300747d200a014032800c03502e60701c4180d8400084103200400060640c0d0083e0340f0580e0070750910454040c2d14185000c4c607a490b1090800103c00111080c814855049801c1d688440303490000c6410101c100320000d600c45403e51005c410012070f688007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 913940170 1250 913938920 913938967
    0xa0f1a07051213080306211b01270303050f1902210306030d0e1512061018170c04090f0c0b0a05040308030a1d0c030d0903020d0b09030708 61
    0x44150ba2901d81003d0040040590081d06003203040001521a04100c900c0381010ba0b5a811a03481c11107550b0242410081500b01038100600c0c000e840c2a401d41e0320501a0901040380d100c0b482040c0403410b040780203a000c521005003800303804030b4403110074406003094464002d0165401c0c03458448801009443c1d0301d4408c5454441100a141c0f80340c01d070301040c107a03481220301400502d0320b6440d81d40e094640030300707603036203d42c1c0049000910740880f510040038102900a40c51700c0c0c030305400d204040110882e4000340110400019040702c1012180d0b04422404480c0c03410760200310300049031003450600b82148081a003040c181202c45040140c1c0829000c0300501854601141540320040703090307944100c40d02100041c0c810720050001c20114401160441c40c200c00008407040c034415132042c07284a20b915030b5041e4110714460015800c0600c0280e05060143c500090707994203590000750304410184010f441002c02000045207000208221201250490717052030700c5031418100c1102007400f2281 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 913941420 1250 913940170 913940197
    0x7150b040510080607050418050603011104090c1425020f031e0105010f08061513060b07110102030306031e0705060c06090705040203070c1b0e0a02120609090a0f1a0705 74
    0x544017621610a60f81901c405c0641c0242c403898005252020b48000380c40158555620030050111502010040000b010700d580046202d00000300f025084c50f02a18207071405444c10442c014110000c0c40880c040d1100a00409030905011b0010440d00202500ba40360503110744041095001104c1c0b40350504080c2680c002d1103507030788801600440f00b08902c1011030303940c05407010400f40b001010f101050b00780080c0440c00e82c241006007120641d51242d01400c3c3c0341c04005014000d02107140c002035285882800151300d5070520201090341c804400b404000100080c002010b008030081c407a82c002080c0040c481a150f08103040c1d0540c540c1c5064a02c84018070a80400150030305007402528440e1400382c44404060165403180c14165401c0036406040070b503500804039000b0004041c00e4000c00b2035503401600c44a0361000c151a0100103014980301c3c0408034108040e1240c00900c0b080314a03405200042414460b00c1c0c030110b2207807411075142c0d0b1114550104040198440c0c054814075000c1d58 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 913942670 1250 913941420 913941433
    0x6192d0609230f0d0311030a080601120908030601110703060e3307050c0c0411220326070b040312110a090614040f0905040b071407150b04051008 64
    0x1151a01030100001d070440d0040160382206001d8030f000301091307154a019041508580448000b000e007150710034000c0e0400715074181c09200f401e5901030384110031494411020020402651075603d4180001407105040095401040d690401c080c003040004580c07024090007040d04000300692203100d15429411403131012020b844c0c0c0403059044050b410b4004100380e10301d9480d801c00448443d440100c41d40e242d8856403c01c000c01e915207118a025200d8881e9903e41c94000c080c0c000082c004c81c40310016581c0701460030610202d5141c20240040c6d00c40c2490080315611a07169200341401007103009010342e04401d04100c1450307000100080b07101303400081000440b50154242c412405034100010018507000400c1c0085806000703003081c00328981c1400c4e41000d950313030226403c50256400549419864009004c2040383c001e44880d0810502d0400c1e524648200c0581415406440409030071821220820203054885900c800c1d00c50388003a0047c030291408558800e0843d0203803080050920644 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 913943920 1250 913942670 913942709
    0x30f07030b0306071d0103020705061603050a060803160606080a08030a0b0a15080702070f0303120e01020301051320030a0c0e03010c1704081303030906020606192d0609 74
    0x2292684c400c50007038841ca03240c2000203421000c00048001c010741410342c20064a00826020000303a4480c0108001c00040300488000c002c0c1a01d2005e40000001400c203002444440d8020054500c2c0f49100e42030810900210b04007800580b4070b5501c05400c60140003086800c0c0900713000207520070040b01d4000c4c80140216403d101c0e004c0680e210344d4080450050943c280c00b442450100d0700500e0520403103040d0764031858030028240d2203600c00ca002c00c0c0070f45c0e034114182c15107008001c1d441c00900001c60666142030089250000560041c00055030784401400140d000110843c5442c018072108945038500340260000412001d1101380c00310311511a014094031b014000c01036818526500d114809441e540703210406ca130040c204446114042c80681c40704500c04111100860107a555017107500d00d8404080e0a01101506c07490282121717243e80004407407080400300440321724840c50b080ca01003140030040b1a211401021401c18426240044c0703d0358810b8804083e01ca00c10011020314410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 913945170 1250 913943920 913943923
    0xc020f0c030a024b1e060c0a120302090a051203161713080f0c010e0d06111911030406020a080a11011b020d0c020a06080c0c0105040f0c0806091c14030f07030b03 71
    0x483c080c4c8545c0d0b0030541d28507045042240140448441c00c01c12604003034841da0364103100c076103003514140000c0e80c08601d20041d403a050344da140040c101559202204c0d001f90014684070f101f151050141e4002600c4590104480034103074a10700131541c2031494031995041d0205003070b042188901020340c414100b244013945404160088a580140c66030103005401105014014079100000d035281d5903130710640d50400c7c1c0e04c2c2c0d00810345103e0402d1884032900090001400540b00006a01d03242e5105010074028180c000a540044030b401540f015201c440300c07401118500c26550781400356500b800c1c01a00010082c10418192003035680a4441005404008890700c0d5000203000e0f502214141c0300300a804d000da101ca680001c41e106450749420760400b001030a4880c1941c0c00c5800e56000000d4200b403040d5000180302605a99001c0c0546041500006596a45508014076003c00440c0346540701c5008041480364a105548843c0e00c0303141c0307a201069441b404171911030100342400c0d0300ca03501d880e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 913946420 1250 913945170 913945189
    0x1090e10060f020c03011509060e010608060d11100c0605010915120c03020a080a02040605060c0a03081005131e0605030601090f0216060c020f0c030a024b 68
    0x500d005411840340c07030807404441140c81d5060060540c010040c5030180c5131004e0140d0003400301441c90400000c0d1800e41020304640e0654020b14001c3c01550041c811198019515900007504a640c2c000450729404d03e40070b40080803070b480e9401030082080d0308405400540c0516014010038041109070f99907241402a82c100740700d00000700480900600040d06146440d02c4414025541d04102c40e4486c0d000c107034102c0e0607402ca509e650388881141d104503c2c0600034100604401d49a00c0e0500c50101c070b103140da8000071000101400f100030001170343c0f03032000035868005100091809201d8100425000000d02c917030582a40d0101e4251100302c56070f1040e0090394110ba07000b03401055282c1c42c0c117039000024000c11054584c225020061004400e10f80000d0030002409010001003085000001a28006c000c010100d1150401c0320340083c00d40e004140a440d01d0b0f0141ea81c080386080100006640307540a206110f517200c880303440f0b0051614808001c4a40c54610a01040b9a24940307081150024 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 913947670 1250 913946420 913946431
    0x30b0405060f0c09090c0409020c0a0b0a1104090c0201140c0c15060105270303070b060102060a060503030a121d01140c030c1b0313140f1503010e040309030515010501090e 75
    0x203608005150a40c2005003072958001b00c00d820850500d6115404403090382e00804111104d6802869100107014010b040c00340c0089002c0c004100201d099030504100340140c0c4100c071200c46c1c0d980c41e28203c040c000e42084015500b20714812403d441d086000710019040308551240500c15528046107281040300324901a01058440900300b0b002000003044880c407141850105941d80020703500c29071010809080503600c14405100325103020400285096402450b46507c80c0c18028100b046440100c11201407030034500e802c800303c588440d8884c0c0501808036410703003420100308a40c0395001042d486204100194440225240c031801c0280e0194042503500021108080140841601402070000040116501500d090116281d03001701c03c0d65081e44050708000c041040c2d1005441c0c0102515400c3c501240d50400c000700c1240c200204e0b010500840460850a078042410b140c010780c40c4400959000d011244e0740d146030303603d0580040080c8110341c0811003150012403200c900c583c001e8800c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 913948920 1250 913947670 913947691
    0x8071a0d021b03040602241e060303090a030b2e060815091801060605040635090c030c040513020d0201050c01151502031327020301030b0405060f 64
    0x1035450381a4025404a2008480e2044a00005402103000c0c0054401081e1a0f0094030f6030314842e030f6103400032010710285c00311210384110402070914a402182c502d04034054529415540e1000c3c003182c5580f046000d4298400b103049000000c0040c10a01d5511400260060840d01c13422290540c0010445800300004040d0000c401d0020901c01e018059024210401840d00d610004000c10a0703d40c0a4480403030744000c0655603035030f0324400d0085034010035092074003601d0700349440002012120005051b15a52412a00b00341083e1001d0030010101d141c1c1825181c0f4900b0000c0500d42c1d2210b11a40107070181c001d810400002d0324141c483c0c1e9102c0da0409c0c48445c00000f85508112007420b0b030010413810b101d01030250389031014013480340d0800741070003500c0d01c2e02d51030a1807400108030300d042e040d01086600c10000d500100214280444c1251141040380c000410b10300003180240508602029050707102000004c203011040200f5030045010b0313410340e07005880b9030000b03600c450390460f4050401c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 913950170 1250 913948920 913948927
    0x41205151b030603070b071101030b01180303050c030903010c02061e060f040c021608010b0906240304030201110a080a0e2d03040905070507030f090609090b0d02180108071a 76
    0xc616040000c0d40e000f04001d007a10140c0d80c9402043c0d04680002c1030544031229140320185095805105841400c4400d09100c81c04008206450b0b1240740207010040420002040000f4015810415280c51100060083c860300c5086000250750b0780c411255000001c030f400010f0b15440a8030141036020300c3e0301900a81c500f0041806001c050300310811980c0440c031504050844503502a00d07c00040d024000c00881c40a0b448010011744280161076244a00c4009030500054120034a018581d00480502e40f5103a65a60509a005004800b4150340c5170300000303072944030554800c181034815084140c1c10490400400800342d522204010a11218007110158034500c85034200c1d006c0603100701104680c50251260002e406590007502c080000c10400309603c0109a0060040490b000c00307850441c507038606d07100c0c00904d482418810a207074969640c1420005850340c82d240360001e5005080e00c150201c4031a0305544960b024401e181c003034000c10f600407403880c810180441001d0b0003260010704 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 913951420 1250 913950170 913950211
    0x303090d030c0f080403050706090b161e08060607060510170109020a091e0608030408010c1707140c0d02101d030904150512010b01090509060d0b09070b04120515 71
    0x81c00c001c040e02c146d051050906c440b10018186000c1c50300d2207445081150014101070004095207201100d01009210308008441080c62851007a03c455840030b142c154000e458035070114400d4840c80c02e0180c14203003401c080181c0c4116001c401021280c50340e0842c1605003454901500721103088078020340c84860300e40d0401201125402c0549944034207100b8800800c1105002021a0241e03030000a0729040400c040102c07030004e02c10004150014244940100070ba00700e50b01d02c081c0000c04d50024007002c41e0041c0c40700f042e004151030781402c909007100c401210a00029540e4400d6040004100341424070100e040c101041c0c070300b2480321000004508000d0468104409000c0810f40b02907020401080010983c0e40c1d03126003011140c41e000001110303070300e80000410882c240d8200130b00600100c4144000d50b00d0791228121f2181d080304400c006034440c254001d007040601e6002029043c0702007001310300303505030070681c0c0c150503c20000c503015075003910310800c1c08140841e0300d2020311032000400c04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 913952670 1250 913951420 913951427
    0x113606011412100f27150603051909030c05070501030c051b0a0209131a010f090f0f0e0c130b0303040320041a030114240a03080c0303090d030c0f 64
    0x3e4001100a0000108035110102c00c0113940403036004020f05c81005d4000c29920a40000000940320b1801c4140300d08920500740c0340b8010840e21504041650b9600001c046070310507a00d42c6807902d4400c00510004c0b01c1420001c040800010007680c250280003800151036000b44544104840d40391251030030414183d050310070359801c01001a500d0300411501c10010b986c0c0d6419903100321200c1403070b07000c1c100040c2012105030b0808444004060941d400520000c0d001100b20350441d143d5500c04115481080b081002400d40c2401440026080890b0020120700204901c40341a070b05442c40d010305e107185580c80701650700d10441c00e070701500204402d0010a00010b078950390340280c6031204d0146040b10300802d04480500119003510911001d0b8043c0a207030070f0041181d40d110011008015003801020240100400d8079422041c4030505148050358446070203100082d900030110303a44a4500704895a01ca42c07080325404458018000c0e100e54a6000c1d05c15048160050303554242c0e658114070007034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 913953920 1250 913952670 913952707
    0xb0301050c09061c0f1d34030510060f06020309130b010302070c151103310b0a03090303060857011701060c0615170705090618041136060114 62
    0xb8100036047c000200c0481d808000044a1500013030000810b03d143c40c40000030350740641c11440440d00f08000d00c2c680c69a0711001c00403410078844001451515000069009100c0d410f0020b081b110280400548600e88544422284101e5120f034150011000001d0ba12886408483c0c460005050140400010b01600900c044000a820017411684858426034180c00c6488918002501e5854100c20540d060040034010245c41c802042e01c0808044460800c2490002c4c0e003510b030182140510030079213481c080303945801701140d0000655081810307450754008a0083c15004c528801408105d01da503106002d412650b0503581c041c011451035072410003501c43c40100300407180c0b42d920080f5910002600c0d10b41c04640790030050040034903103001c2c40641301000704003d01c50160302e0046d801d1624043c404640c003030340c81940e00d0302c000c1075000090607090480a1190f58900a00b03040600303006d507003122921130082d041c500c04171540e40000464002208440d034004004041c001c80e402c0403c91030a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 913955170 1250 913953920 913954003
    0xa330915230c03071115010609050108070206060411090411040f0f030f1403070b0f070815031207170a09033f210603060b0301050c09061c0f1d 63
    0xc85917104140c40360380c2c50308002580e5002c1125440d070040044540080304c20b00100703420300f005101e6141c0104041e44900c0000d0040380aa40c0319035502a4590b8503030200c0e110840c0041c0b042000248501218885412901496140050040020903100c1d284c80050003100d52040740b0342243e140b45d507101c04480c120071070f81c09014402403102400007085203141c83d106502901d01d1280518015000805000000c1d01c2c0507140c101e10403e6081d1a00c01080c440c40007404a18955504d27036191034280c41c04002c00710307614113080740410842040795016401c403003100d001e4014154441c0242c0c9101c2000075051380ca00800c201142ca07480c094041c00070200c514a11581004541801b00e20500701c0c0403049541051320981d0b42e940c0a1040003001d100b8440e6094040e0002c204515191000300c1c0c4510403803005071300c02c40e40401c89400703c03500420703040300c80801c4c0c0742c00340120b5004200d8a0f01074550440b1a0804040100e40070100980000d4021031030100307141e040041d030322343c1c1d001c940755410704226 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 913956420 1250 913955170 913955177
    0x91201200a0915030203190c0927020c010204050109090e03071716080c10090c260a0507091802010e060a0e0603040b01090e0a330915230c0307 63
    0xc0003c01440759407403554501c1c2103860159503450032040005181448001e01105540303003170070507089035070b1005440003500c03005941c1c06a46500da0700301e503100301001018040c80ca800060302410f0018190090070850740c083c0c07250016292902d0003502529425a140c00039984140441c0f808510b00f8070340554070341c41d02c105162030000c0944a9031110700081d801910429800036070004912010000000010102030702048035088690300c103c80d2200d00d02c51316002801406105480e2142c0486105440d100d0070111020800245441a10380c0c025220f481c0105251040ca00d084084200300301c1e000b190305039160640200c4a40c10072609810103052401004a04403480382030ba22540001c50244d030040b01003204540c506102d84003900c0708074294585a8010304129400505846617103180c02e156000d40b29501480508680c220281e100140044141411202c00a000640d0380c10b031160503060740140300c40c0b00d0149503035041a40c80c1b22407098401d06600000c039444d9071503002d140c01101c50700c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 913957670 1250 913956420 913956437
    0x30103150b0609040f0c0e030708072d06020601030b010e09062e090207020a0f1d0702010b060f03071404080a0f020301150e18010b0603040605060a0306060b091201200a 74
    0x40101d01114828a40400400c0d6100340c0e11b24255002403259402090403002015020305011070580c4901c428420392800328134500ca20100d009a565102e03001c0021b44801446055540c1e0340207542e0760084c4020340300c1c403007450008240d10142c100c3c014805d8019100910480e1102040c45910b910040c0301c0005c100c0c2842c00d4040c9401560340b0020060107060340150312451103004104010800d41d00508031002e010400b0000c030066920907109450003201c0048603030742c400d8016070160404140a0b40e00080001d41d0952014501005e140078200a80c0d0b44240c004540500c0c4120b4801c44c010301129a001c030340341c4c20024000300c59062001d48090004100c0320a4050b100624042315084041c000300808208a40300300c20405d01c50701e030130604000f804221200000726200340f001400140a0f0b0b911480000c1480e1a2400640001d41c1e0003401004215a10902d150050308110000c61051004000e8013079007503814062601200445404d00310321540404032104542d00948820082c0f000c0d02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 913958920 1250 913957670 913957687
    0x5071e082404060f27061d13080d05070e01030605011e030b0307060207180b060315060c10050601030605010e09150112110301030605010e04050715031409070812030103150b06 77
    0x12000e8400030074070300303c81d00141d414100304540403150703465176a28480d03c2c0400801020401114514000d00395003a0400c0e5038541012440c00400484e002034916174000407070450808142c2c0c0500c0c840c0d082546d45000d00000107004509a4a06129050005000e801d816203900107120702075070780c04864200001c0d0107801d04003090070508558050030158000c845d0401c04070f440001c0c0c0752907447d0311030420410b001550b000154a4080500242d01e003008401d4040300b00d84440040300c18084810b4101c038202220b018240000d00800c0b81d4250000341010740008165004184002d1043e00040501d0f049036554500c1d99402d1045040c058100030001c0e020701c0c1c80d24914458204c0140100c030301940d40f5810341c1001700c02d584041e80002014a2514204800329501080003810f0f11040c281700d008198407020101d020b402e41c0c4001e8203840000209001070314400103841c8089a8848d415103c820349500c0030700c81a800240b1014100c440c0c03002c0170300503070140e90340040450385000300b0290524142 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 913960170 1250 913958920 913958939
    0xa03180218090a0c03080a020115212a210b040605040f0b09010e0d0e10121e09050f010905030a0e010210090506090c0402090a03020f040f05071e08240406 68
    0xe5441980d440c2030004080c104c3c40d6082c0207100d44c810202e03042d568018644004813001d2116400e42010b000d0342f486c990010480b1429403611503850401003104001100550415804040e11800c00c08400010022210f6416505c81d500d1044c1c100c90008216601d507100d02c009054014400c4840b420704101500020f1010801107005180c40c40000648410320701c40c6030b140c09042029602031099840c41070002e40e035001c030105410007552406000c101080101000034001a400e00c090ba58610020240310a042e503205840c1e060280e4104c82801629050242c22554001000b4219400c100b00303510110340901c0007018078410610440b02000c40255007582292040346044a05070840b100f0b12500d40300030054200e802000722411480d004080001036648169840001c6c000c580d600d184210300d80da1680410512407001ca01070041e0f1404c0e1030700030f040483e4600c038000705a51180403100c01e80d02c5188180e108401c10f440c00c650f201c640075101a0001100b8058542c410340313650020905011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 913961420 1250 913960170 913960193
    0x1e10141f020303040c0609050907050d0e1207030e04140c1b060709030203062521140601080703050103080d0b06090a0816050108090c010f12050403050a03180218090a 73
    0x295806180c0f642013030315200c0071122959004100300f184d00c600901207030781c4001e4080d400078000d003407003681c07042c2c0301d00383c10f010301a14888603000f40540ca00c4811040400c10091400301c0c401d03070329011000650010081140d176441a42e6183c80c80203030000307150503c1c6000901880b00102c40c0001d090000d034410f81d1914404850b04000905401401c00c00c41c1001c1044540100354119881c040308001d880140481a005822100f00510b02c101c03441801d550100780b00303a0083d0320000303001070301562000c4c114080d020744002c3e000603c01400030707034598800d100302810b03243e000001c6882d080152000e036016006001c051a03100b0410402d02d51540e80341c810101c01402200e000e000e41c0318911600180482030743d403055050000304e4041200c41d41000c01d00d0702c455103003402c04502d895144070b81120b50380403a2001d075040e5450b100030301040c560000040c2078050210f039428080401d0501410f4401100b0303d00094101800c00e00700504000001c00081d4490030400c203d03510059a034580900540 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 913962670 1250 913961420 913961479
    0xc0303011d0c0702030c0108071b06020a0f0c050c0402070309090e010b0f12061602070b04080c19060e1e1801380a05041d1e1014 57
    0xd806041c50700c0c00115040003076019981c2c94000303042ca012034000c02d803a510100b1b000e43c100f04041c1c00080001d4000c00700071028820610078400c0e0b004141c50403d00a500ca001b121020401130b6001100251080e41100400ca40c80f401030602259841d0900001c1d40240706d0440a0003d141000704080c603680c411035241450103400403403102c0d084400e020001600c444e240e80502c01049819496060010790300d0b42001d200c2940064650700352608a00b02082504400085a00000e0004d403800d000600c2002c0c0180413074201000742081c040130302105100e442204007082d0500c280d40c00c3ca2070003074400701d5460071074501d00c0c0c4a20318a40000300c40700c4c1030786191180e01078100d00510884044030b00c4070150400940120540a41001107050a041c94015041c540b00001400b02040b51013003042d070700104014144c0641800f40c007410030500f1101214001d10f10294030310003c0c4008280740c40280921961005111000d0502c07491030008031081c01486d4000e985144241c54018140303403001d1002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 913963920 1250 913962670 913962689
    0x40e06071b080f0a0f1205060604050f0a030f0b010801060e010e04060213081c080a09081c02070f2a0e0c0a020a05030d06030b090c06030a020c0f12090301200304030309080c030301 79
    0x517503065005808030700c02c0d0a000d1090340c5440100b200584880d011503040e280b04850003c0c4100440d40051181c2102d604002c1003200c5c40280c0d5003c0000c41110b071416211580300900450307455484500000307509200f40200c0ca0480742c0403801103601036006000001c41c56001d102603545410b1f01d01e00e8000e1040703c0b0416908a002c9052180e80d1200311382d600096840014009801c498850290b07600404a01c40b01036001c214082007182d405070304440241d035000c440c0b10040c10450a042c0c1110450722105d02c000343c04075225444070050854014250760b0741c02081d810644804200b412a5041801100b0a500c1382d22a20030204008102801401400f48400305040d410340c582910f80c2100541085040e621106200f051079480106603a4001441e050040e102d071108070f20246040c000500303203800d5000b00b80f42050762017201030040c864828280c0017030080e010210704c1d468223075400d04d038000702401052000c00c001a10a07000004806e00890202e0305098034100e072542103030f02c00c0e0f2040519 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 913965170 1250 913963920 913963937
    0x14010e0702010b03030309070608100e0c04030606060305040b040b07050409051f05010f020601030609080f0c0705030d020a050c060d06030c0b0c0111070f06090c080a0501020306040e06071b080f0a 86
    0x480e076090048111201e4294040c508500382034601c0e542e00d24aa00610742441555000a031407000d40c000c02034000d02651403011070506141c0078124140c1e1150105450b290304000d80401c01c24041c2c05458042c0750b10140c50059070f0ba4079103909080c942c1c040d000c0c1c41000700400000403110300c280541401111602c00c5403510038084841e4880c00c40560340102e040c40006980d0700300c1e2540101e40a41100c1e001480440d108040c4c1c9031125152007074900398204190702103014071540c8000248001504e105408a8080910b0164240d9842c004114010320b50f07400200b0941c61410180d001d01010151000e0101e165902d90f55412240d0708640c0041c58848000f048165880c4400d020b10300d520000c000b0740c0c43c5000f43c591501c80002d15a920050b114548071031041d002c1000c44080c1e00c006051030340aa410b0f26007585041170203544181c031828483da06100480e0000740002c240c042c02296640c5402c00031080581d1160b0840307000140a032215001880090b4900e01808010701e006a880c0d0380d960034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 913966420 1250 913965170 913965181
    0x1b07062c0c040b090c0711191502100b0f010c02040f090b04121d060703090b0d2009180c0d181a0c090f040b06040e012918030114010e 59
    0x4540b07603c0c2c030030340c441d10511040c004485691030488581c0f940003440d51520b03000620110f0f201c0b040c0e00c64014001d4080300400246a2130184280d907401046034207440c01ea00b0b0345580c181c2501e2800360729903801106519545001d600038444854501d10152010840b4100c0c4100001141e80184c02654643c50510400c0300300103c1508901c2e84d41c2c05401c10030721214046c00000110703640c08130514001e0701d00082c000306040c012021000144803a5981542d03d201000e541d2010307002c000c980d00c000c280a8089000e507103200381c043d11080c2c030024181e913250900700c07009008c01120240c00c802d4108401c03c021507480600d4050102c010740f400b0903a00ba40b03c1c0926146c50f1100031140748000d94103d100c10720109070f1a080840b2103032842110083c41c24468880014010301786001c8040d40b1542c00034001805601c00303007886040742e402c080d8408000c04c250400200806c40d604800107809810402440c0702d405014600ca84e01401030000542e0299680420041c4c180a0300712421a842e03040401c035 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 913967670 1250 913966420 913966429
    0x8011407050a2c090a06080106080102040e0a0504020a03060c02030a0e010201050f04030f05040f0807030210090608040b040606171617060a0c020f0303010b121b07062c0c 75
    0xd40080305864200e2600460140040401c1d12a0503086003c0b00201001e21986902480e0510340b040c0080c001c84032428103041c000024400342c485c0305520350030031038001254841842900e040b00c0c818440b005950740c1b180c510704000e0200820882c0c0c0020f5052021012800d1403181e00440e001c076400441d80c4000c1150041d0032640d006104904584c100000c00c58040740100c41d070b5800c160306003040310440800c41707415201405542c00545031004080300000720b0f0705e00086d02d4030440f070082d540181c15001c024000ca540a00703d0180d040070410b104040740000e00b03040c03421580980a0b40000511544070801a4034607449100c55801d2540041840d10700700c1002d450000c020440003c0d406000c0e0300001d0155150507000340441012a0b4450700d00031550300074850783e4600c01c0039500340ca503a50f0f1190003122076501b02c203200103a803240401c002031042c20128010f1140703440b81d030461402e2000503607a550107080c00d100b0000713141240200f2031502d00b480b03080001c1251402805042c200c0242420f21 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 913968920 1250 913967670 913967711
    0x90b0f0304170702130f020c15100801060308030f060604053115090b03010603060903110706020c1f09080d23190c05010b0a0905190b0f040f14010801 66
    0x2c0e032240404020750001a41e4060702518015407980011440c80d8000c48400001d001e09107909089001c2c0082000c9001c8203181558030992840c40d590b41c2c82c54640e0316003070880300940001084a00200081100340690070310031079014038003d0026140c262241c0c041805400c441c1100381c0113010b000e540003102ca011000041c0c1001808008000311410303032120040c4c10300d9520461035140c1d83d80c000c40a80e41c4082d000b00b030207550441e07070900c690701085c42d0081100f410146071741e0241c021043c01090152003c9605145282e0040189074942d8400d00c01381040402c00903658140950110300240320f250074003109114103840d031079100588215003c211603c003441d80c1000303105030003003040351031901da00210802501d0701c03850001c040301e169203030083c010507403000410760003440e0760000a030044598000d24032910200e01e02c03ca40c400f00304148070965100d9001300d60b00c44e4011800c0003850505901c240081000c6100c0490b020016810801f400c5100380c00224469440e8031410220f0b840c147c514 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 913970170 1250 913968920 913968953
    0x102130b0f04410111010e1b0604050d08040518070207030b0c120907080106060201061d19020723010b032e09081809010f0b0f04170706030606091a0307090b0f0304 72
    0x80c009016070b07c40e0b058039844c03071859404e55044503010740241501c90809583c080c0c40045d0100c12183c14031308054455401611440340701d051200910740190319100c100902901c2c903030b0000d001c254150b640349500d651000382031450445051010310004541c15038010b005080d040b01401c2c010b070414612901b5904203030401c5080d0381c1016800c02451f40c141500705008010b50481039542d44501075100c00c1c1b6401d03600100e070141d001240443c2401420f0300d0354070618441d443c100c05150302c0312030060300f640e14020801f030385034210003800e0a420710405004204000c0060494107000c445030f0b002d1045a08803001601e080302e020506030000d6526190813001d11808030b07442c0f0794640c0742c0100c12440350260b003d041c445140c08100e04a00b99a8a41907801074840d8005480040501a42242d91105584a54800241041000602c070b901904200042e81c038135801030000460441d912500075071002d02002c041140300c0d000040e043e00e01e00d02030410541c0d00300c12284d41c0d00b01400d141049007506901d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 913971420 1250 913970170 913970173
    0x70f020f12120c071208030f011202010804061e1d06100e0a09060623090106030e0309041a0a03051c080c040302131d0102130b0f04410111 61
    0x141d40c0c19804001035241c880203600d950700350f55a14146525050101c6a80560800f401d4070010301d04000f4064007651142c3d60580c2c0f0070030903a036290101c0c0040d24080310040d002c20a080081404203200350459202d81d00c0b12402c0080b14082c0203104811039881150030300c6240b114203045100082e043c0001034001980701c05001e1041c0c100243c424550402a01c2c40c00e00b540e6510903030301008038540060340205407950f860748010301c03000c030038490b035203982c413242440b804640c0c0000ca0628064403407410590140d000960904060100740001006840e108040c0040f0248820280e9602c030496a07020318800c0c000361804079030005c03040044000b840c0c0c5580c2441608820440b8800782031040d581103e80489481c9103071040000303003c004284807070202d404a04952814126054150000c0c01d040c040d4020056105599019880040c005c01509080d02d0748104800c0215140c040c1448194010b038001d06d210003c90494413060640b100e40d0f00000b1180d4814002c040380d80c100b406071654404010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 913972670 1250 913971420 913971439
    0x1413031101022b090c0f051801140d0c031707031b02030a0f14060c130803030103080313051203090d030614010f0807030b0604120b1f03080a0e06070f020f 68
    0xa008030b10301002c41c0c240c0c41c0d400d260301c20300c030900d58020382101000542011217800c4082c0c072002c0030008205a0f015140c0034100380318a806600d00718000f658101e40a00c144004094144420071420000303943c4142e42c90508144044003180c0d102207280071007000c003510260f9400b4103140203000822030f25925580c60008810403009078a0200e11071018030b078840d5601c00c01820500d09003500f0f01001c1d0780981345101d420204203c0000312001042c0c4001c1600400c0040344d0b440c903100d541c07440240401014800c0920100d41c00b510880c2000380442d1040341602d401c003904802a5216820443c0c04248940c400c000c02080942c051142c1005003441da081032600c002c0820018050a0403114020100504013000681261003035105058102e4004d120940c1c4950b200016000700301144410f036034030107891010a0550b00b2030104c1c416084202c2e11140b48081c556200c44003a504903220740400e101014110447c96078a600090400c18841d1510004400310742c0140407000303421040c0d2900800c0d026 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 913973920 1250 913972670 913972687
    0x90213060905100b030c090a153b1c050307060504120809061303031e02130b25060605040e030a030c08060a23030a030908010b040605010e04020d141303110102 70
    0x130011030f54801d030640300c420395132144400031904508081e4050030500c0c4281140c1c040d0031340d22030036602d1030030511380e4500890919142078400140d0905400d10127090680405281070510700702e03426000503c10102c1291600310b8588034159480114103c2c2e029036500b04003c10041050305548144010f403170214518038162108030755605c1c0103059074034405103040d2484209480380d045105560318411036004100e60100201c000303500b082480d8003081440007808910a10440b043c1e0f0b00400300b13451221415400c1000034294840c1081040d03d03002d4030b940c0040703000c0d02e40e4001c044131814800c00039590b9040700c100040495070306a0440e420400354000f4030040e40d4a60140740c040c0e50504500b200300404c07640c11130024070092090a81c05009817002c0000381500130a41004a44400000780012940c9030108402c03101c0f41d0040b1804140c1c030b61b168801e503040c19409009640100b060029186517058804403038040e044a40a038880c01d4031036860101944195440700d0034504000942c00c01200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 913975170 1250 913973920 913973939
    0x803010306090c091a01020c030c030d0c0c080109031d030c0a050f06070b15240304151d1c0504080a0305030705070c08010902101d04020d09021306090510 68
    0x6200107803125848400311410710049001c0d502c02090703000010401c60028a03038201003001302090880c058011880300c2c03081400c0100b10300711459001070140048407080760003a9107569201d24280c2e20014114804201804248991002c1c0c074025214a402031b0303203002050780c20942060180b4040e0304880400d40c41900c60803450001c1d520200c03003880d0068184008203c46024a9030302500080341401803019150b00304501340b4607051b06588030740e60341c1d50304442989003091802068158000820010340401e901420b10140d80ea001c4101184086058141d0321410030340b1071180d20f007078104403e03504200c07440c20403403070b554105800c0c40781c1030528021080d0b44405064401a060120000000e11122f110b00115106158000c140700340d5161500c000a000f080703521002c034000d1044d640c02e06082c50143c41c0400115040c00b40400b0201c51303803018400a50403403103600c070600b504d604143c0c0050355100300c440b006100181000402a152403880001e403000940550300c0c1e40030741c09051080c0c058 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 913976420 1250 913975170 913975177
    0x405101d04020d020d02030112050c0a1d070c050a0c2405090d08040506030a0203090d05250809031005090d03270f0f050102070506060a050a1a040806010816080a08 72
    0x404460050f1904005583c41000e885040d002c2254144000300214031940303c002240d45250158007124210407a10046c030580688600401c4035a80440042070181f0b5080b0300d00e143c3c40b00d0946024a5521a182c0d2103d03d0004440c80c11213010000482c00e001114621214808000a0f0002c07018101c142c214050414410054118001c0f00c0b122400780910401400b01c400501001e40070a0303032840d24101d00c0009420990f0204001d010b000c02002c040b500c14030a4030070f40341c1170340851032210303100e440f412800c0c40701e032202100d18001c10310003101b050343e0034001d107004000f0034500400c3c2440e00b0080b8a04010110102405040c0f0f00256050704000d071221a171a1190755460620030f44455040502090b5a0460010054034039859011f00b0000306401403c103091041c4200e94041e00c4140c10818440d081d8004d25404c400c2c400000c0007151503810034000310001d80b190705440c0070b452b15142800c1039401d810520300d41d400082142003c0c6040031042d002040030f10040c2c07200c4101d07035540141c3c82c031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 913977670 1250 913976420 913976477
    0x9090c0f010302030c19091403010b0604051c080c1509070602060106080a110d020d0f0e0c0103020901031b020c01090b190e010201150303180b030105060301051011070605040510 78
    0x40e408400228205d074030f00704991a940c10500030303200203820020018800181800b9280f0201d051410310b82d80d50038140106a039102e0002c10071385c2010705003818001480c1642070b000b943c0701503100d40c040115500c45c000302000c1811402400d4160140e102c50022501c000e400140c1c070703a01013041000381c103030b010a9050540f940e911703116085840d0250b43d0350242404030400e001d0070000041c00098004240d00401c00707000b1500040c01844043c2200504071080c406880c03002d50000c0c0560b2050b503110764000d0440c40e81c14100000c214054100398000c4404035501000903904c006080c038829a00300e4800801810190062440d001100c654503040143c8070310a030042c80360204280002d82c0c000c0d000710035042414401c071401c1c00c0d070300d040003030100c020121a440340061030031000c60070301c6900e0102d03810794902034a824650392034001032243d24442c805421040041d0070810100a20051120100070440369480988a42c105010062041d0026a4820a00038103050b6440702108440c0a1800c0c1d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 913978920 1250 913977670 913977677
    0x2f2d0703110a150c0f050309100c1205040b1012150504140d0306140a03020a12030c02090c070b15010c0f05010617030c0d080403090b0903030d0e0a0209090c0f01 71
    0x200305004020b450002c0c6084020480d518920b803601c41a0070941c0541c110150950f100e021140c50400103640a120075201194a03800482c61440ca100054000c4840c8140b80e20b04481450142c680040480c1c4050340c0c00c407070a0034503a081c02065092458280041d1000c1e040c1c0401c1800316680d045d004402003001c549401c6d80f01d0307001400707120340b542d140c0c4d115034120015510384100c406d00081c0240a20301446990084031034601c44e8500341303000c15400360b990180c100c42810f8101001c1c64003104103c3d20032003c00003528608401a251000a01e0182c111034240e40e4580100d4a4440320401e0001e02041100295808a074030581e800070001c00140d4012140c0b00d00c071100f0341061030250020f5003210008002d18460100104030000c02003c04201a800713549003174203000b5048484080940d00640000c920340014415510a180103040a070401411a0314228016046c00c3c01d544042c05400501d41000321028154208114840d50180d03800c0041c0a02051090010300c003140c0103064641003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 913980170 1250 913978920 913978937
    0x506150d0c05090402070303020304050f1c23040b0a09050121050a0e030c070609080303090d050f0904060b0414030a03020d110106030b0f1f0f03062f2d0703 69
    0x14080c100702c3c0c0c001000500155a1580f003414054040c2d8402e03502150f141c86008051840c409000c078007a510484400400d058040303e81104494001020000109504000300719080700c000c5940108020040102c84a4541d00e131300c070001c0d01501559000c5414440742d00103070a00650342e01c000045814070440009219241e03000c000001700004940c500052100040241d040000001c078030041300d0180c1d81714418a5211010607443e8081520f4501e8a94090706a1200d0035002d40d000e08080c500c2e8146450410070700300005019618a5031080c5000c1000043c1400800c50300d043d22004800e05400400c0d599580342c5e4001c0d6910015202e00b010420240d0240d9802c00d02908445c0085030000300001407402c1000704c00307065800031b450500162950800c40105030b203848049070f086903003441215500c1b42c615110140031340f030b10901d03100104005421140b010f6030441e05460380c5104000c44141c5440c0340800004028140c1d1884011b01000c0343c8901109441c0c06003141c52550341890110320 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 913981420 1250 913980170 913980191
    0x30507020c0405040b22050703020114070c181a030604030e0103061a0a0806120c01050f04080d0e03071a0306040b030a150203340c1407090209040506150d 68
    0xc280300803655a5009040c0f01c180010310000207406405140300000b00400840070b046020100c44060070020410340000340e04101543c01a88242200f024036940c0c2454140b099a40389142c042c035400c440b1503000300340d0f02c1c02d60150591080388140146001059840700c108000242d43d80d41c002e00c0101040080340401c120b5920a0f00000014092600249055a507841001c00c480e0040014840040d50002c0062910701d4041a8121740500c824054900003107510b004546960003044c2c95140c01804100010701d1200030410400c43c01328a58503003a04a00c03110805061440c0381e40b142c0b002014400c2200b899a80e100100c0741c0159048a0000e1140c200c0808030307060100c41d0102412070074a6080058991109400642c820141c90951341001e0200c0c244e4100c1c9854020f017a0f00c4802c5002c21042183d0307003e01a01c00d01a4042d40a0341c82c51400344d669586081d1540e000100516000b040c543d080d0708083c001d554020310112620010700d42882103208140c042c030302e951102c864480d6007a01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 913982670 1250 913981420 913981423
    0x309050904081c0b03010e0c2404150e060a080603070b3109051017010c1b061d030a0315080a15021c050609090c060a0f030b0a030311060c071203050702 67
    0x100680d601174020311451200c40c40e1540c4811211502d0340c042d03c1d01d0807080c0a100c204203880910107028001c0e4500b480d007002ea0002c13240e07051060681c14072000b041001c0c46541d860b030113000000442e9641d0358451403c4001d01d42086c2407035110b071172200000e00c07002c00031086070307450318a100ca50000b4904003000301d10384184660f4a181d200121051401c801d101b400ea404191001c01d5844040b000c9030302c074100c2039800e0700300d415040303c4200250212a1420740c07048a000b00c000c10b94003400e070105044030f4070814862000d6031441c0300c1c585a4000100a4070854040c002c01001c1d5101c0c842d2060b40e5071031b0041c1c00b0b4444444607801409110309818120740a0a42d505403108841407030b83c2d13050500501c5c140da00042000b40d403030318403a1807a6800229010f200180104030300c1005040c2c142882115102511000e10407410f050915864095041980d1105116071000794026510802003100c0e5541a50400d20094030b5054040341c2003101c103002c0b8444030404a0640c0d51454002540c0c0c1d64418100d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 913983920 1250 913982670 913982681
    0x605030f010e0d1805040501140a06181203050705010c09060f0503060f120a06051f0b0a27030209041b0e10031b080f01150501050a17060f120a0309050904081c 70
    0x16a06c00c2c035040001c40c9183c60020045076011081d242101d809494070313026a145680301d0301212010b0f110b0384050003610b400405d00c5e140540302e0b06201c2d0900c03102e0b40c2c5440c01e555000410600090000c00100400c3c1c0d40100594a0b100302c60a249107181803c3d404111917107100e00c00b8601954002c407207207002010030400030f11440c1c4c1000e010401d6061a00301c810210342c1d00c0060b542d01308500580822040c248a00710b9032000b6054403243c880f041c16403650b0320000500d041400c03c1c00307210b42d40000507894500651744034074455200070281c204214a10b0b0f1310b80c0c04940094203614014010801000030003482c5e03405036600000b0342c0310545884524044100d226400060081c0180504400007010540040c13106071300c10312070054400d495800440d070314004c0c07030178400c001b410848607600b0040300240da05802490190100d40541d10390b40c00302d08086054046c1c117a80c1d502c05041042403580c0200e111001e01005c80b20500e036401d294994450340d0041020042500c2c4016a001c0d10f40910340d44a03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 913985170 1250 913983920 913983929
    0x1302030c0d0b07090e0c0307080405071203020102220305071404061a0703080a0b0d02060928140d21020c091e101514040e01090605030f010e0d18 64
    0xa09a07841c0c150316000e40070b50800e881620104091441c042201c0040c009071910a00d5030940132800d50380e034188200c80e000e01c060410303034441c00b44102c0491402250b140c41d842081c043d40015950300740c030010844504205881d42d090b141030528051000410205410303044038450014080c401c0e00e11000600280031542c0940d010300003800c100f0761b80c0303000340d000b07422401d000c0d0312450015624034004d4801d5a80034012954404020413404005240c00006410400000b5060000048084024001e8427a03a009502c4103844541001c00c8105540c01c401040001e0a907415085490107036110f801142c00702030164070001c0c101541c0c102081c400c02c08503215003001081183d403814103c0b00850101070a11940f001e2100f40d40000f402004c2c0c030200c0340c1c2202c007143c4203c2115120644c003245c2482c80c2d04c200f03c1000c03008000c00100721403480c12080c01b03010203650020f03109161600301468148828115403040c0d0404400b4110b9860104002010000d2400c1c0505a5030a02c0503a03002040107802 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 913986420 1250 913985170 913985179
    0x11030106180b030a0603050d0c170703180603020415030b060a0e04380415050607080f04030309050906030a2013020d091a041205090d02040f0c02010b06040e1302030c 73
    0x8000b04c3d803140d5040801107901540598a214030780000894050720900c00107000b18449821441e10141c0100c01070072058068949008510210401d4074103040c042e60140d40004d03000300e018820b16192038020040c0d4406c3d0b050400000b105807000ca0441c3c043e030303440e05081c8aa800000f40068485401000000040e80d40c0b4168610030040111020b0000c0410403905c20041d1140c440b40c0d040622990008032610303017261b401585800b0810055910003102110038010500c00507440700a81006040518803c0e01c451071214202424000104001043c0314484e82c024074000b0301013025840401c46030903400a40c1c032952080325000c00c482c0845a541c6203112807002031701c1190801942c2c00440d08901c920b130740c10b084403207181481c220104c0684025207014141070000d542a8000d500404c400f09002c0d00403020780082c1d0300003a08960040c404580841d441d8100581e60a81c280704079003401e80216075190030941803c0c4600f08281c00102030094580c9080740000c15950104811001c0950040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 913987670 1250 913986420 913986427
    0x20f09041b1703040506030405071706040213060e13061e020913020708030a0e07030804080d080c190309021810061403040b0a0902280e010911030106180b 68
    0xa0034505004000c46910740348041c0100120302100222940c890b5180c03a00002c608050910302081074580c0098030803101807054181c0010310180c4182010b59801004001e0078113440c00b4010b0201e88801d01c208101250f1070180c050100d602c41019043c0c10859004105508031540c0c03170f0400c01407104a001411200a031903100051041c250010200140241d41c80c0148070501041a001d90203010320040103a0307802d000140840c80a81e001c1403071b0f20b902504440c0c1407552a1202003896005402c03c00c40d07600320307113a1403401d5030f042400581c008105030595440c2002e00480d0304051007582508404040d29918840150755410f890b00e200c14002c1c844074140b81c1400112a149010607214030f4002c12007000036654a1610b030700640348101e07002405100a03543c0c8158100050595100c12a0700101251224007001100c984a0304075003948111800003504200c1282c9002805905c120364440c00c0402c10840b10b50150181d904540032410290082400004603103080d0341c846d04000340006012 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 913988920 1250 913987670 913987673
    0x30f031801090f03020f0114070c0e2208090409030e030d0f1719050a020d050406020d060f08030414030703140304030c120b180102091306080705011701050d020f0904 73
    0x180030040001007621080d03640340d0342e54922041c008444c0f2010354456008100310911354040c210103250307041c0441805261802c80d981c0c500b1a1340460701704012140354141004541c070744503640041080c951030080405084245e4440c0f41a02c078800c2c01c28001c0341c46100c0310040601501845840100080c1a60144c0d849504010719104076000d445c80050030200c0d031100c1245015a420b4012070345c01d100c01546030711401416000e000e020300400c2d01c0f01d40c20841101e070204076119440c052481824050b81e9000401062025140913800c4000485424a81001901c01c000215000c60754100d8104c0d1030104203500190400c03846074070207000e040000e054199066404002001a40d00c43c0164031038440d00e682c540c80c180107030407000611a15103030002c0798070b8000c1d8100501d602c440070340c00503151560340d001081c07492885810784c0d004503444240621401d4000d0055001034074003071801d040740301074074220842e2580061141038081d0501c9941002552504418401056809055040345080c01e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 913990170 1250 913988920 913988947
    0x1d06091006061b060911060a0c020f0a1d130f08130f0b07111c060b15030f01210f0320070b0d1e0c0f1103090901060509030f03 56
    0x14000e032a04520700d02540803500c00e02491600c485000b12000002400d1038650b280002070103c2001030325040b1215103565038590305c80c8010b003211401c542c1c0e02d180d14046c51040c440d103081c480e030405118031103001061101c56400c41000e03c0036a0741c070840d00c841d1b4803190100712960031954005044d05059203c14030074843e00000a01d81000c3c903246100f8419034a46001e01d245403580078152078000100040808107001c5580506048030080c48a4613a000745a0450b101841080d4100c510704d450b000002020b1610514002800030800e40791407440c1341000000e55099014003a00e4255035010550403c1d4050000d940354545038001740c81854000642000f400c0400711480244034004444400c55485601252403011902040d10303e5083c040d44905a40240c043c00e0716030002500c283c41902c0c0104594080c01801c845203884401e80d01c408507000800d586881514803c60340e000300310080c034903102d50000c54110385081c6001510340c90b0040c0028200220518842c06c00e100c085600f0f0350b02d060 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 913991420 1250 913990170 913990183
    0xf0c0e0c070b0718052223011a0714010b150c061f18110435060a05040501150608100503010e0309040c050c061509091504061d0609 58
    0x42c100d42d81e59580d0704001107440c0601100c0301c0c800010401020041814039060203048440342900045201d4482030300c030401c641d44407440e010a43c4010038004075484801402c1405809074a8032078159049000d4130002c03074495903100030b141c5048243c00d465108401e50044d80058001009a007c0701c0386409200d0064002100305142401210301140e00603030032010301400200f00d01040000d0705d207404042c84450201214819506441d84a240390054051006001600900e40502d00300d52034030036040b0f08150044110602c01201d540d40d07004803100090842e62005c550500803c0b5681c032071814502501801982040d81c138100b903000300d0708640021403035200e48803070032440100540e5501058240da5042c1c200840503041003164a0310750510340c0040910b500b07a07082c006e1404005102003803a000c022500d003000c1c80e24206d40f003025450440400b54000d01c1540c024401005a80c030003840288001c0c2004100e16591180140c100c4080154158103810250030746038145803841d24103403502c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 913992670 1250 913991420 913991423
    0xf18041a0c09090402120c0303040e010e13030c24020d050106020c011b0f021f051e0933070305030a0b012c04061a07050f190f0c0e0c07 60
    0x2180000244924403100d00b40d0329410340007860b18115864a4007404461040365a42d44144d0081c10b113000607e483c200014030043c000020300860a6243c841301860581014104c103c00d48a05c17802c45002c00c1c1d20100c12901c03980c204d0003140091040c0c9084807001c4000c0c008103200f1707074000300e920780008038603a00c040d04840003902030741c640240003001120404070094100343c0011000d484800841c0c040c2401740c2959102402e8030703802c465414070003203a002c558800340700003800c0020303d002c0c042c0c0c0d000030b802d42c0c01141062007400c04403503000141071008480c2e85d20002d0f0308100d4640d2100e6003648410300307140d40c40c40d941507940c0c1801d0900800c1540708441081006041c600822050752003427040d950883c0c02405105046401505000c0002030180507083e0b1081e15104086800781155803555036011b5032004031036880e0101d1074120706050001411102d60341100943c1c080311032540d030300141680d40c2300300400b9011000d0300d0400300e0030b002500903a00c204000000c000c40051504000c0865a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 913993920 1250 913992670 913992713
    0x8010c090608101206091a041205070228090e07030b1506070b04030201090203030d0c02061b0a03020901090f06081e060a050f0d1a0610090b07020f1804 67
    0x110340311181611401c10a880410002489400412035024003200e40f0381000d1003020080780c0600346441f200300c1444000361502c1109200d4062000700411032042d20000c25590030311600384a81a00060b50800308110300c01c1c480044c2ea4081c15000900803420400b918950300c040081801440ca070b00d903940303071034003080b42c00c1d01e02e640104640740302d041c84820ba03080000b4003da140031165600d05070108000b03802201599241c7d659400142e405002902140e19640c3c00024902650721000385000b41c080c00307090090707403551a140002041c00c021200102141e00740541e86403001d0004880e4404164002040700e120740c440030a800c0d6001c0c05481c010f50213143c0d0310702040180441420f50481c00d540c2a9403001180c00300b00301038149042820801900140030f0203a07011b02d81c42d682c00c2d1031140b080c822040a20a010006140740a8183c440041d81030300d400000d09040007101403152144040c0070707100c2c0d546074052604590301e442d01d01c110b840c0a80940c603002c0c1454075144080180310700004c0c41c40c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 913995170 1250 913993920 913993937
    0x307090609050f0f0102030f0409090c0905090c040b0f030a05030901021c08041e0501020a08180102071e17040b0a0905010c0209060904060608011a030106080a02150310090608010c 79
    0x40c0320726840d1041c0d4500811609814100340d0030040f840b500d5881d01d80c15400240400740c00d07641c05801030402403a01e80c0b4041030b070070003a00d0541c040010a03088501c00c10720f81004e0001c011800940206a07401c04e42d00010700c0d82a040c00915803402e804c001940c54407450060000b00303d008806449803620a800721007181c0c030003141075201c0d010407681410000e403c880c0020042411030404000701013908000c07090300d101c6902c0e41400d90380200e0315040864201000c0c4841103949840c02c2101510341c50085040c0413242d0f07a2020310b00460684a80c5042c07400c0f0300402449441c0001801c803036201c800c0261361f96030313a900302d05603504061494004074804610014245d4001c414030702c0707070640c01000b00845545003003c12801d40c0c006001030ba0a5942e802c8003084000091040403052600340d200452a058603400305820b554954105d401c040d04021814801070f220b415500046c0d12034102015100da580c0c1d110780041c02043c0d8804180c2ca410640000340080040d0701a155100b01a0346521a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 913996420 1250 913995170 913995179
    0xf093f1d03030306010c122a120521041707050d090b030c03010623040f0e0a02070f031b0203010c0c0201020f07050a140a09020403060203160314071220030709 70
    0x2c50340411103600d030108007100840c00c0000c2c07014040003003090031f5040c90131040300d0150f0407003440c02106680428a0341c1921584003400150360880400607036914010b464403d00c500981021034034034410b600c4400401c07000c075007002060100c0345010100f01c945039480d40c05908007165204081001900411203134400410f0f104050000c4a20411244407940e24503441c01c101102d1502c28a03850040c050030705400305500d248035200a000411034080e052000300e0030071140a802034030242200500e60704c100705c080e0000e5120101601a1138040c104201c0507810b00c3d54031106514038640c020b505501c0e00c0080c055132500240c884215900030307401c6445072400713000300070f0380c680c0d80b4011507a1140840d4801c1022a58405000c10b803144040e00f51191a030b5201c600300c05a80043c1c004964540e004002c2054000c2c4060400360186017034a02880b06c2c07200400b42c03084040c1e024002c002000000150b451583c03034660402c48000d00c0654100c8014145400d101c6903640041d0380381ca000034014900000e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 913997670 1250 913996420 913996423
    0x5030d1416030203060f100c0c080c010f11120703090807060801240c0b13170c010b03030412021e0319020102060105040c02031902070b03011203030f093f1d03 70
    0x82c0f1489011b4071040503618104204160a082d110361102040800986d030300010340c0984120000b407095600a2888070003078070014207004038001e000b46c1005030740180450340540000b01e072007241448800e490f40c0c0d400d850404544001d020380100e04e084c4030301000002d81690006002d4101e0350040c9407216864900c0114155175070681c10140d0018401110a201241c0003025460b08500c41c9514803445019603a1010181001003072600c42401000c180301c0510030080c0a451a2004210080e40c541801e1100340c0f40c16a00030040030b402181c0e801304402c1064098840000f030204000c1c1150740400c044031141120350f2204204a00502a40000007a10305141c002d01c07105140c1c0e43c02841c281000d80040c0c211804d916040f400451195030300c0054213000794001507001e02507440200039400c069041c013400352081c20345400c0030316107048084e8002c600d00502d2021883d40c42140802080b02c1e400e90700f140c0d044075010b1020100402e8646880442d00850701d031030000542c03241510b00751011070405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 913998920 1250 913997670 913997677
    0x6071a041511090f03010219090e010602061905060102010f0204030b15040204080a020111010204170601081513020d0c23040b10080c071e03080a14101205030d14160302 74
    0x2c02c40700905014030491450034240f030001c1c4201c0980018281400c801c03188001c049548240004200040d00c2400306900003d016030240503a400200b080c0c0c10b104080d00304001649038882111a17544000c224268402e40000300040c01b804419522141c80e4186141c200406640c60000032039504c620400506160080ea42107031021400b41c00c8040782074005640c0078426805039035455508000105556041c55582c43c2d80e003200704010402d9604140d03c144c9004042e000d240c0b081c15000041101020418048686955065841c405031041030310f00548252a160005207505a43c4803502801001c160051407001e08111350038000c1c18030600502001c0002074505a0001b6880700005120004090062803c284141c03910602407907408442c282d2901c1c0c407101240010401420b11440701c449000711b080c0f4824041e404001030601008440a41c4103521a0b800c010440c4100c4070305100060050391a00300c5000e00074490f03000c41d2010b00082200c00c4070740080e8400302450030341c142480392003036 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 914000170 1250 913998920 913998941
    0x60b010e03010c020d030207020609030114011805040c1403030d240b19050304140f01090209010e0f0412110102340317061c05010b12031606050606071a0415 69
    0x90000c030003054101b10041c1d0b000c924140d820075010803682d00e454400348076640482240d00c2045509504208994204c024403c8880911508150600020901000e0841c0440d0900314440044035003000109045002d90036214054902c1c1184515103c901c052001d064104a854001e8021792a9a200303100e134003d0b01c0700098036281e070191007100310307006000039a08140903800d003900c03610310600c40d546881212071035031900b83d44500b448411801d000340b40317501420140302e41102c10310f1700e2503685070500e07001000607041e8010000f020051b58082c0c550030b5060300f4840000d5540700e0100751820586004400308100c2e551140d00c9144404138030400080341c4d41c1d4942e40d00200030400304501c01c00d1560181040c1d902000030350f410304038018504c00d03080400c0d1040c07002103212116101080a100544c1c0b841c80004e4104004c3c4010b10b00555800c051140e902400019240e1076203404aa141c0c050010002c0c54955001502c40280c0d00b01501c441c0700e1881a00d0201088000060080540e0040c2c00c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 914001420 1250 914000170 914000173
    0x60605032809082d18120a02090c040329070309080d2d140c09040b040f090b0711190c030516030506060f0a1211040f0b04050c03090d0f0e030307060b010e03010c02 72
    0x200c101c81d0340340c088103651003400d180d82219a0181c49800281c4882700070348440c80d407846c00080070001c20207041c240c9c4002001c3c9a007610101514810030f40300c0d104005018808050b070318403001c0704002d03c8005841e001e9070002c1040005c25075400d191a00c4034181c3d5400102d021029001e950528001d004e00702d0010340da0000340c2c1e0240c88402408000790070040c1d101d64040d0700c074010a4915200c0d80706100c0d2040a2640c0814061041d003402066102d001e0b1138001001884143e203c1503000000b600c0302000300c0800c07000742d0507505060110b055a141d820003401401100c400110303828100d45078000b924042c2060f640192610750030010002568482241c00400d90003007003162103900c1d040c1c6400280140181c00c1d0780c1c201040000e040300c412184205d006540c0303501c141550708140c466507a0007034074000307180c1c82c5051480070700e503850a011491100700071071081040740c07840c070400a501c00348402404613a200c91442c134094024042102c0d04500199101e90980e0a80c601400b91740c0300072100340c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 914002670 1250 914001420 914001457
    0x20702010207030b040521180d02060406050f0705100504030207081506220f2301050906040510030807060b010f0203191112040e0901060605032809082d 67
    0x103440c004c1c400e070010019070303e900031802d00310980074506194440c0301e0565428556034244050080004030b03081030703180d401030071389030342440060301c0b15012034041d182503040807030725611540282030f82c40c41601c0c03006006001e00c408046100081d0742046016901c650203440c07050340c60302506aa0b4040c2000110400070304000805d5240c100910780c0340c41d820a40c0e8080b0700030b603010141801602e48102818a24540e20005084580340600b0103034440c4100405103241c5504d024001120100c0c003a1400348030760383d5030020400070068000c5060096a03c001c0701c1e51280d4041c1000c00040030b000c03100d0b9010482401e02060000d10101c1107038004295041d0700314612440c5038040300c802c41c000c018000c49100c1e00d900580482810806480146501c059020913403518003421800d6810710751001c0c040c00014020301851030901c1020090060b682c03003c2c188040c00e5481c1c42409080100c801a00701e081c00182e100c901d960a103004504100d407450301d41e441d02d0b44550040c24500c1220302c0e80c41c5060048 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 914003920 1250 914002670 914002673
    0x512030316030615020601170312010317071b050a090b01020a0b060f0d050a05011d0d030b21100b0603071706030309040204080303090705030102192d020f1002070201020703 76
    0xc07101c01c0707061258a00040c010b030321890315101e003092070644c44015901031401005910b02c07031401d16103891510070240d400d240c01c0415059800206000c0100341e20044d00070203542803043c0d0199002281c101c2e02d0510600c81c640d2541c2624040d501559000348403001c0c011500d81020300a01840805c180d00610006069440da0400c644000c0c2400b0760050f003403c48800c00d556112440100b5a00400281041e018a071a2003421994844c810001e81844490348860f1054003140600048085041c007280b01c5c00ca040000e02c50b65120703400e05113103800c02d1030804c0e130390f000004485848000d19101002103003d03000400c103103404215881d0300050b404440c00c1c0c00d14540c0196064200c01d002e4112818044207000140980c1c001e500901c8260384048200040e040d01000810002c0c85d0a90085151080302880294540080c0321210180f0040f46c0d401a000340e030ba25040d004502c003456540600005010b0000e4481060b1841401c1d41c1c4990600c1140a181c2e0788200e98603654141c00804c6941c0c0356 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 914005170 1250 914003920 914003941
    0x108010e040c050307090c02010b0a3b1006033602040f02030c070b070807020a060209030a05010606020d020c040e0a12110303040b04030f052706040f090207060605120303 75
    0x20002c6031050080d000000380764408101e00b00240401002c0452402480f84000742101d080981080c400c60030100304100300c1c4a40885828005044402880300b07034404050310f41d20040d2241c5121000c0c0742034040020380040c22407164295601c503507050007420141c0340001d604007080c5450f5200c5111201c2d2044400303c40c503040d20b01c40d601c0904042840c011500080d0201e0f00f08076100080c0c0c0700000b81d06401c1107808200d8951001e001c0c1840c4a80e0f08000c90001c0d99080d16a42c01440990300180a070b103150f500700100f400d900d60140090200c1d17521244020f449a408014400140c440c0138444983d03481d0500030307203000207140c030028145000240c03107014503105d0a03004c4a003408079203100122012414001980f0a5010b4070040d202410a450001d00f0207801340c3c064020440d09000740811903441c540c1003a480f1611074418801c9103c1c6000060540c400c0340c0c401c140030300035150009841180b41d00600300385401820700304000c030381d6841400362450261090a03000d810410008840c0d054 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 914006420 1250 914005170 914005199
    0x10e070807120e0a05191103060f061c080c0106030506070912020f06070f0f050c15030412121e0605011110020a03090b091e01020901020c01120f0c0c030906020309010801 75
    0xa000450b91011100d8440030300b050f01d600010918070341e60450a105200310a18101003444081c8e00605980c80c0841d0882e00959001c0c0c1b83e030b44941d58000f0703a032403008132001594440da40c02c503001c0c540c1c4503402c1c40c0845c000c00c8030348011240f9001e5400001d0300d80b8026012003044a6139041d01040108417907003000b0400c02600303107050b80a41e00744151008540701e42002c4005501c105403130b02c2800c009047c0249005120010944140018111203110304e00e00810f0341d820640c85440c00314080c10f448c0c829030340c1d050042c49110505d881c03c4998411509580f519290424290004010541d251001101c120641c0f03000c16207254015505140340f02a164000e00c9120710a01d00020620740b05c3c0d40e070f0840300500380d0300030076030394050300b80d00b034030103402c10865400b008130800214034202d54100081d440e520640c05240c18042110401082c1a4103908981405c0e09007030700c2007041e0540c0150140000d6089007003680060030541005c00e20380d000004441031410142c5a03204c0d6a864542c1002c003d00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 914007670 1250 914006420 914006441
    0x309090a06210507080106261e1b030a12110102090406060314130c0b0901052101080f03040612020f1e1b07030c060e0303130b03010e07080712 63
    0x41d620301c0006031901181441d9007608020300c2410b08080c0040c2081850b1540b02e411a072200d9150050403c00240504c1b2841c480300c03180d440f200499100c02d10300c20f080c000d1071a02d0440300d00c400385c01914005004100f608030034405080c1c409903280004285641d4040540004000c42c4c00d085003902214003440e902243c494403040003610f02203401000c43d0684203103038405000729031610050010751110004890388203c00c0c0001c501803403500c1d00c546d95071232000c0c41040e0780c408000504a006901c980200c1382010314403038200c0a888803c1c8018180e40c0424810003003079020380042c0d00300f0750001008960442d00180e0390700069440908000c4020f521403c3c810030444404c1041c1c0c036502140480d049049a80d03421110f03122001b40141c0007807110b084041c1c46a540103048144001041e202114080e61042d2406481c1c044007040132030320f50f00c12209001a1000d20100000750003048200442c1600c122414101c5261503504e8107031106002500c424007c18040600c40f1010945540550f100c403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 914008920 1250 914007670 914007691
    0xa0c03181122090c170709050c0f040305030403030f1d040c090306140f070e0306040602181507060f020909070c080f0c0105150d03022a0402120a0c0e03030909 70
    0x20440d000900c0e41c04a000341c90b0034070151210f00c401d0a1101500d1548024508540b05024203100e0400d481d0312044140a0050b8807551f81001c00d0542c00240e05a0725401c594041c8580c0d29078482c28030550703a07000340c4402c900141c0b105080006035031117100f080d0007912044400d020000380040412026120600e2040c08002000e240000032075998002d2041364a4400400003c0c2c0c1021000305002c80c00081601c828007441c2c0c1017012403901c001079140d90180e08640016140c841d028403010321404110289948042d8003002c540414507907600820460384507100c100110071852071641e040e40504448542d0011113840083c83c0301d4000d0f00048440c500c00c040540c90050032041c030800c55041405030001d01c0e990780042100d500e40792405044200400c851041180c07201c0d540080d41c4618112545042241c11000300608005038013648940c80c40c000d00641d200c682c000301185055808452058580cbe050a03041c102c041d018903142d29070b00b08064060341c81e200a400a00c504800d02524103c80f2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 914010170 1250 914008920 914008939
    0x409060c030902030f06012d050a1805071803150b06032e031122050103110910060e0111030c0601080a20240d050a02030a0c031811 58
    0x40952154001003403160310001120440b60042c146010030b401c3c1c001c0344961110006000380c00498413100f000c00d010f40c61071052881800d500c3d001c0d2030b5141d0302464002d402144c0100d429144040d41c0c04070a540008100800e80d03c400d81201c00340c0c490310418868080c00c400c1800803410440c03d007130705821000d901080f20a82c56000c03030f40c264002c41d4804001001c0240182c0c900c402442003501568270004051615070454840e00d40320080e42241318880d54401c0c44000c0d544216440040c0140c04841d1f0402c819a5207043c61070320303802c41c2203e06215010010000d10760f0340c7c070b0000c804217072113440c1c2d1600d00b402c8100006641500d801e08118a20b80f00a00c101104e00c0d40400185028004c0800138046400356031900d1010070500c0c41c4000b2300003401003801c000544558902c0d80c252981c14030740307200344a203a2011707481070702c941030300e445840d4140410000882400d400544c001d0101c65020002c0010a074011000c64281596194109174070340002000710700c07940781002002500400301c20a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 914011420 1250 914010170 914010173
    0xb3301031d0601060912150506130603080a08090102120109051f0906080c06030717060a211403070c0e0915010305100c0c03021509010b0607150501050f0604140409 72
    0x201d0401c0c44220342255020000501516511554007001010340180b000e4503d1500d03642d003100b29424440c1105101d68503400940c090303807691003104641a042e1001c203e080d803603040040e511391090010b5408102420049800036205200300d49102c040140c030501c169080c680e000018000250800303017466410080110307161111605000140040c0200085552920310701c9030038214a050454410002401003020f29504070754020028680b00c18035950581c0c51000141c20090181c0001caa0f0014a07102c080e09000c048000426050080300d070101d100c04151051640c1344540900244003000303044082100e58801f540007908461580e05030383c1d1008010b1554104e40c10300341d00554442e841211038865000c0c0c5c0d8444c118141d0164078020080340341d56107020f9901c0c466040c1c030b5000f0103074640c001041880294011a1840c000400095079214607040c80301c0f140c68004107595115107072500004462070411030802400b4006011a81810f24214103da03525110190103030b0455201c001c03030f40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 914012670 1250 914011420 914011451
    0x4120f051306020303101202031203281e1a06030a02070b07120e0715080403090312020a03030e1c0c0309090213031e0816020d08030a090b330103 64
    0x400b401159005680b42e2600c2403055000c042070358060001c4a00c20340310040540c8000c511041c5403142c0c410920703900e44504292011445190700d890201e010b169020b000e03802c0041d0016118255004030030340001d00c551b450302c0119410007003030101c0d0301180c1d19101300d6418160091503019407050401420300c1e40b1030303c5030038049500700e81c41d000040c05103007068018105482211840c000b2107000340310307150600c1403140d25002c80078015018400710400040426104814800c00385034000341e082c904040d40c0c0406540d03120300d5401200843d06180c54400480c40000b52080d01042da4070174400400241841076440c001400001c1c0c0c20480300399408039004400d130000300000d2848040c03145034240785040c0081a0b25071084280000740011f04840e012030340c040c040e514001c0c2d000c40042c04880300d84c4005440501c840d000140002004010042c51b0015039200c0b030040ca0042585502036505e0038000c000c803071074081100300101c00340103070f2203420803542c0c0714941031440605000440156204202 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 914013920 1250 914012670 914012707
    0x3090203120f0a081308070f020619120b030f1c121404110102010b0109030212010b09040501150501020f030a0302030717131103011104030809011b050c0901050904120f05 75
    0x41c503103500005040c861055201c942d0030342c8150300b41c2004400e20041c2c0c0d06c2e550584200351014255200184154055541e071804075102d201d0460303000141c01010700005130259001109001840e0702e000d03005c400311f04001c1013280400d0400d00c041c04410443c0c200710703002c07058024a0002000a45200480160750901c1010060017491038484402e00c0e0500c2c211f8400c642002e0100c0c11a4100f024015040c6d80041c985070035694101c400056080c08848814010107070420a164031009840501080c04019030000303080a120740d216a1081c2c0e2a280160b0383c07581110b205440580c001c00048280d284260b01441c1c10241d82e1904c0241001000c010700d41300c8400f95220560824680c0710311701000841c000340042d945041d00240300380118a25120214019484042d210030303400900741240d41e10804802001c040d004411a001c10024180a079035a10441b84190140d0820030012409142c1705c80c0b440d101343d5010b0404280403250071411100825041c60789d40600006021841c440d88504030704 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 914015170 1250 914013920 914013937
    0x510021c030e06161e1e05030f010905040c0303081e011d0702120403030c0f0804030f0b2404020703020c1f02070b04050a121b0e010306140708070309020312 69
    0x3189541070084410f0900c10081c2028841d0300c0a00c81384071505030000820413160f080a00b698000c0240301c007003074070f8180c8012a1103034140300700c0300752000590700840078500030a040440342c0740583e07c4402040c215081600c0c050072405292100700006881801090390207010104c0d4103040c05010110607030784070400e0300a00307000816803421105a403842034069602c00c0291004159007101550303030681d28883d6009c0a42044002c03282c01060160030440840482d0703012000c0da5459a4a04149003542d4a007402100c140b6001804141c90055203896820070444c58a40c0303d40d202d264404200096200180c204c0a5020f101881500340c1d443d0b44548800f0110441e00498140d410400242800301d1074001d95401c0c18280020722860721050120003e1351090f9003000c21111490600c46c8440040c01f0284e9aa40c0a100c00403d5510103032070502e0481b88034660500c01d1050f80040020020021181c210014502c100090a01442a040038480c240064290303000040c1c0d01d041d418560703110b95803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 914016420 1250 914015170 914015177
    0x61b030f09040f1505010c081c060501090905060307060c0f0203060109020a09050d21050d2c0309130c030905010905070510091d0c2b0f14010510021c 66
    0x50a041c982040d004090301e0345140801086a45405000040501083d002e8541007004150000c410441c440303086484400c100d1512641071480c851050015083e103020786400180e174444000754800060045500070315004002d0a10395082241c00c80740310709100c03030603240c0f403882c40113581c0561800c3c0015400703040388000150303486005e02c001030145001503002c5801590690307000340c0400c3c80e142501c001403250422841c2e801c41503500850b17141c0201e0b51010308140c41e008207403080300e080c221210302084400e8030003040b40c800303145200e480b070040411984d006156507101851541c03113030744900d000c0c104070300340010303010220b884e11400c49078041c00455055001c1c210a00041c607000c80102148802481c091290754180792166021116100d00140b4440c007075004682000c002a080d00c40341c10a80306007100080141ea00f96020907019110308200c0c030300d41004d03440c2c0c04100e8041c00e41e4415807440049c04030b0b40382c901440014082907080800b140140d00d014031484604407c0d03600040d00c00d99 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 914017670 1250 914016420 914016427
    0x9060c0303020405120105151c0818030607020a031206060e010e150d1d060103030c290a231e0a200d0506010c02011d011e18050f0f061b030f 62
    0x1c1184048d030288003580c3c4a5580708180d401d030a4001c2502c81c0000d0740c0103c00e9601e4105420015038140d107074401c81c503410f0203283c04005036154002214540180a50780b003403e0070300700c06501c00c22600d280c007030f0340c000500346004001e4950155036508100000600110542c9818030112911908104038600d18161107605050000801e0107044820001c00006001c0c5545140d03000303000d104030014000c0082980824403030304882c00506d0520102c101c284550042d01d825840070700202414410a2002c0b100c4032120107042111045292040409508440c8412101c4900c1c0c120040000c1c800b00c881a00c42c0b9246040002c108042e141100c8041001901d0340ca041c14102c2c00d41e00000c0c078190400600f80e0545c000b6030783c0300c8400382e103050100341320b12109081400126401c2041d5020180e145c414030042c2450746500c0740d9205141c42d42c0e00004860f41d62201c0422101c1c0710701c020010383c04038a250343d0344982c1c58108000d1243c1c4241010009040b480c50a1031401c60708280031280c0c0b0b014010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 914018920 1250 914017670 914017681
    0x140102220803190c05121c14070801050112020d0c050a260a27051c0207050a1403072102100309170a0c02090a05090705060a09060c0303020405120105 66
    0xc0a200e0090701d5144080c6081c41102c0c030410b221244000d50810070451024070038030034844103020320001e07860040929641d400d00e107802c90409590b0f0b140041b00c6540b801840d0a07000402d148254091116540d40862503484e1100455180c0e9000c41300c84c1c000c6900f08100708582c011071240d020b40900c90f4940c580c40c0c03101a02d01403c3c1514a000e03208003000f809000080701e00406403600c0d884084031200152034440c680c1c03459600901c00703100031065460119503030144840000e40386450100000943c01c00d00a80308100e8503a0b010f481901d030040c503410b20034800d01580640ca0404402d018044408143d55049503c400044040c2d92455503908089180c00354240094510b5948649050901c007002d6169610205041c1d0f10451090600700400d8900c1c90b188035025045103107400074441349450034072801a000400060343c040d9441d09c200c02000400d0700700042982c01c0c00e00f07641c41c0c6810240c944042596070f5070b0321340400ca01f055400c10001c130742551012102540121440c000180d2890301 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 914020170 1250 914018920 914018977
    0x50907120b06011707120c12050403111902060313020312030f1605030411240c0105090601080c0a120f060e0d0306060201060f05010c08250506070c0b13140102 70
    0x808500c20901c6884c3d42c1002400d07034201022889100815400191050228030110340b25152001039140ca103050070284030a041d480041e001008412009903441c3d90347c08401201d40c1009104002e410102c1480058003220714042c184180d10f00141c252181c00f00c1c0d01d00c252071540e108980d605040000d210a20034140c240312001890b43c90700782041d42c0341d41001c3d01c821140982226204c4d2181c01c1f5a10350484001545104e655802c0d100e480a540720100241d546002c0c10301103c00709086d01c140313000056200d0300003943e146a1413014014200f0282404005c3c4004c2100d06015a8800144010640020100e1080741e84034492500646800012400001c017611700c982c0c0441f045a04010701849130f90344680300002243c00900b02401b50000c2440c0245035406240e141c001d0741d58400454186000f00007481001903441103082c1e405030760342e11000785c9070059060b501030205d9450a0000c0c42081d0b2402c0f01d402464045c8050305041039010851a00766409010060742e8250010b0000221080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 914021420 1250 914020170 914020187
    0xc0c031507080f070c0b0a0f05090a030219030c151e0203090f1501090e0a0609080c0709090b010512160f060f02150a240806100b1c050907120b0601 65
    0x301c8500701400d83c240413000500b814240c1c0740c064420610034001c51201902c55220981903901d0709000c0c003140c80c120052a4603800700b100c0903000740c0265800c1d07919000c001070368020f1680d0b054840c07441512494480000c1501c03502c100360a01c0399145000340c440d402c100c2e510390401c02000000350b03603880d00072074460514009642c001040c2d48045401d103040f405003d81181903980c42200000d8602a003480d03540fa286030942d02a201918148104043c0914000103008017104031040f561031079a90b03085d02007120f00324034001d0a08401c40005010310b240449440c8845030a034030864030754042c0c00d5004415809a64003003032a15244490420500750001002413203036445001405008407222419552a4801031010303481d1a0b48061140792022503941b2544500440500c031005591140c00b1560f482d00180c6a2860411b00c9040000701c1050031000c642c2c0d111261a40c4010500d403604203c4041c00340600541c02c10700a117880070540050311072202904c940101d01c0b1180c10300b00800058009603 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 914022670 1250 914021420 914021431
    0x1104030b04111f0c0b060f0a03080316020601060e060d27170f090f01111002030106031d0a0f03030b0d050c090928031808060402030d080702070b0c0c03150708 70
    0x8071a0303000582c581c4c0203800c5108040d0003181c401001c2d601e0078009000e8461391000654010440c01000c028407401d01c0156200b41c4406840c0c0c065104d0442050b681c0707008c00d20520001520801036440982400c030042c0000d0032000d140840e4411005001302d0700380c0f0700641d0340307007403034400c0c1c0303003034418000c0c913095030048580102c00c071034030704500c600220300703148903000d1f1540c0518646c4c00f0020084c1d2082a841c4014040c280079200a549407401d41b501a40c801e120b1000024140302100c4c007840b8040c4140b00c2c480c0c3c01040100a0101a40c0d10104000300c0c409040d030505580f4280031460ba200c65805401d030238440c5002c1c1080880e040100300d4901000351504c50b8650102da00b006480714124141601e10200c070a10380090390441c90f049078a0340c02c0ea444200400404580003400304000100b950081c0c0c802c505803804007241d800201c6070101c1c2162084d00503846407104108640040c0000d20610b03c03813000b070f45da0a0080304046894007161240c01a02c050b240e00421207003650180d01700d40c000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 914023920 1250 914022670 914022709
    0x90510020a090314030c03190f180303030f0905121c0e0303061210060906080f0a08030c071a0403231e091804030f18050a06031104030b0411 62
    0x11104203008080e8100b90000900c00c16a5a0305840980020400e4034600a948012260f5503001d1500c02c4c04001510810b800204810314012480c8901a000300800e003074070811541030051460f10110060400c40c0c2c01001620761310004600440c505222741c01c90241000074a42d0b403200c0718601c0003215100f080a10302d2207498018108008038001c0200c0c0d4011400301c846861020084800c0303410448510202c0c10140d250490011340040c3c950808002c99003400141c0d10b00300600c01c00113490b40400080106298000c00026240034845005402518082c1c481c02d88c11301a44824540d102e00150340a40201d10036200303030810008214811006c00e200900c0ca181002001900910101c1a601c0701402c40c0c4000b2601080c02d0301c030447c0081a501c54203c58954500f051305004e402400e20b124090300140c5001e5001c9800b4003d001c4510413960701411a15281d40303062003c07402000c0400c48186c1103401008000003242030340000c0d50095019416642e02e0b14510700801050300040d41e4138088a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 914025170 1250 914023920 914023927
    0x105100519050d1a0f06041103100e0907090207060b0a0618142d1e0f060a0c0818040f060323100f0b040f090b01090e15040609051002 59
    0x10621100740c603000700c07a019a0f84483d001001e02e4443c0044102c10040e5080b0451032007007090741003502c012a8040c49007503c003003000b1508400094124801211000e608095450741040401c02152010381e101c086401911485902c40b1004801d980c0b01d00010744005847d0307400c03a562464001c171024010052424038640150400030401c41c10217446c03140322591409607483c13009646441c00c5a280750840002c0882488408922002c020300c0d15000107401011044002001c803010912480d0307051000401a01c0c0030001c0c541008020340c04903000e40200b01c981200400050203103005003009041000704030303001d1020700b41403100b01c0c0c42c3c030f030804181142014001c00224088014100c0f00c0e151240d039003040341010302030703492500100030500340c25546000346044441000fa0312210024804a900780400403405040000780c8a012901500b92280030300100051b0905520502a41034100b0035240000380045000b20011000c480030303140d180c1c03210303006410040f050140400000e030102d0304505 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 914026420 1250 914025170 914025199
    0xc171308090310021b070303270b070311100501120f0213060e070e0a06080718170714030106030b180705040513060e0714060a111915020301050108040816020d0501051005 75
    0x7105400d82c02782070210b0103000102d05145c0340300c010b0101410743c1e00102640d030821850300501d00400211040100d0103002c100c526001228041c0c0313030407103001c075100400c00509038503055450b001070b61b000c07030380b000000e501015600840d004650007007200c103424140034902a50042c02080110400b03e03c502000c4005029a64010804a030050f1240c45c061004940d0f42c40040c85046954010640c000520f80c0c1c00c3c44c005100190b8136058483c15151805000d4485c0181402c1c1d0761140001070225007400c000841c60900c1c00d460a1810507228111220345d6554008074046500c00c1d41c1010b0514404c1c460441401011701480c48860107910040c00d81c01d18001e40081054800190140704e1440042c0b06504180300e001160401130740181510162119070030001004240240c085130038051101d01601d1495244c42038030304030752060311001d18a40c0c1d9a07039280e1065011682e0850603054040381c900c0580c80340d504a8405612071000014641015050301d40341c81a1580300c80d00c6040000f00152 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 914027670 1250 914026420 914026427
    0xc040602060a09020607030c1a0a0204080f01091203020a090e0103050c100c0308070e030109050106080109020f0907090e04060f05070206100f030827030a080a030c171308090310021b070303 83
    0x5032619098070340008040396900c1c08083c100750030022100d0271031114041c00040c50280e8020003c4525040407540d000c0e041d00c12a5081c1d5070003103c00303054454030603040c0050b20302940042040c000545009000c0c55101c82e440100382c0002e0300103445030b5100300c801c1035031403c040748400620031060034110508a46964000c01d00c4074000e0580c01040b0400c0003051440d2000d40152000b40d51120003400b0454441d41001d00038140d410040e4420100c5501c0013515091120440d030158900d5030303d150615041c46010230080740b000e0001c880e100ea550041e152420903620503503010f01728660240c511420031b4005442601465080a41c01030003111082000940c0c802c100c0f00350402100c2403407240c5816242c01002541092a61074050086041020030040307a03500403ca02001074400300109100d081c0e040750140071301c00c4d40400020010b00403541d402c0c1004140e4200074801c100e550728240001022904080410115050458001c6048500003a030802039001d5014400018503181d49140ca004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 914028776 1106 914027670 914027677
    0xf100c15090503031617070c0605010503190b090f070f090515131806150509130308130c08030f0307110a0323120c040602060a090206 59
    0x40c85034261034401c4482441e00640214103564401003c13541800412180c9414000480d18040351446034180140c8140c41a0b0b8a4210820142c03400c2c10035281d068001a21940080c0d228001c0c8040e40c005001c80e5a41010501c08162504554282404803041c5004110b018000300442e0411515042d10200c800e50300d0104540c0c0d0b2171480740185c407001e05c0210350b400001c82c10040c66071000b40c1c10107c40000e50110410b25011a540d8050489a02c1c202407140d00502070420002841c195140b05d40c08070400a4403030a803043da030350003005010010506482800450104014031036178901141c00b0708094030071039644800c0c02109044e2600308640204c0061001c0803810100321001c115038440c00d03815210b818070000c1c8544540988000480380d50002c01084c8041004100180c0005010702c2010030041c0da502c0c10030750f0003810000020b08880b20f9074180301d003183c0180c640d01c086 = true := by decide +kernel

theorem cover : BRFrame.Cov 913848920 914028776 := by
  have h0 := BRFrame.cov_init 913848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 913848920 ≤ n) (h2 : n < 914028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
