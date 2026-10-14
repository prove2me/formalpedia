-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0634
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:50:41.499804+00:00
-- url     : https://prove2.me/submissions/05ef4da2-68ae-4b10-8eca-4393214dce07

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 113848920 ≤ n < 114028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 113850170 1250 113848920 113848951
    0x804020306010501140c010908040e06010203030403080609060a08100c0e0307180b010c0c06080403020d0302070b070c14030c0c090c030f0106180506040b130e0c0f160c060903120305 80
    0xf5580500e0340d100c2c1c640b001c00348062502c0c005406003030a49092071030499540d0300220b818081c407045506100d920640070320095086181503180140401c0016096502440c13141000c41c045485038100d40c07025040b03840032a010142d03070500603c01030541b0003041000072a600e00402070761034041440c00072030b516070101100c18607482070500c006040b00712456044c4042d20704154005a0301d061420300510f0142c40b003c440c2d20f41402d019040940181d145401c041c4100030680001e0919600290030171034501d400c07941c90820f890500c00c490101e40b5490300034800810500413145002070548540101610708255989032042400541d0105481d20050303111205c0040c042030f0b20800d10002140000d080010220396214007103582540983c000f04405400080d141810354010350202c03008200205c9410b9252070102480f2040340103035559418043c03000940190980c0c0340c0c122020310303150003a680342c1c0500e51312280508542c0e40d91100311140c0f40451001c4140501901c1114070850381002c04014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 113851420 1250 113850170 113850179
    0x506090402090d02100206070906030204030f03050327010e0f0a0503091017040b010806070c050607030b0118080d08071803081b0f16050604050a0905060d12030903030606080402030601 81
    0x207500001002e940002003000b2075800340e615041410f11096190b005458142481100105502483c0d003000080c940100020030000c0c40ba006090b41154041c60229141d498042a50f01001c05440312000c000c02e9080111100c4030701075003d65001c00206040750101c040c0c0780d2125490f803070f00f0380c0f020304250020320012103d4100b108144070b0317401080c038102681e003042c03451610402c80203079415130b81800300500500402d042006455040300d80b40c03c00228a603a1a074581c2c0e0341d0000205103c0403d41c81c0e0b40382d02c080d42d0090b1032840c40307a81c0050b0000c041c9900c40c600b070b9556102000c07415000422000105440e607002c5c5580c4600442d058000c502c07002e0541e10b890a140c1d00a46180320b5601c00e051020720122002e11124452000c00d10160915030120031180c1018030140c0c010b00d20030041003108005c2d41d039500400c201140d000301c0b80403a0641e10000043c00d80d50f0404d4014100d01007042c01582e442d80d25900c40008288170f914100401a10307001d04403070021048130000e406502c490010f00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 113852670 1250 113851420 113851429
    0xc0c011403010905130f0302160b070f080a0c06060e07080705030c0703050306060d1d0d09061d010201020c030c060105040f05060603130c120309081e07090b0604091107060e07050609 80
    0x517480a2041840366040c400e40e07562903445585c02c0d80680c0184c1001c10203003100300c1042c100314000c00c82c01042c541130040700d0b142d40d60b42e10000b0710020030101c40014030f0000c2900a10300c02c0300240c0c11400800c000c541d1000101240101180d103200020044030005140700e0040d41a00d0285089152103424101075940649141d030010300001c1c0d00941c11300c81d0703030302d98041d070701419800900300c2c081c0400f00740840150368a0b0800010046003030002e0440240b00083d03000b207c207190145200b4078080c842030740c2c1005074024441c000300d0000310f000004a204000303c00051590403241e003039400300306044103040030038200c450a0303454544c4178804201046d5441082c1941008031030050314143c81d85a5903400000c44c05d051120102e002c0360703048108111030358080c0015542c039229090030f031a1801100900c01d846403040c1c0914032440b40d0754104103050f51070350070070f072000b40c000f400f400c001c21040c0c1c0000191030703048a03404981031820100da0800c00030303000c02c0b810100c4a0240005050100800400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 113853920 1250 113852670 113852681
    0x1201080f0a0807081314040b040b01270b0415080702031c0b0111060a090212030c0a12030e010203010e0901180507120f15090b010801090506040312140108030c0c0114030109 76
    0x1582c41c204c0600c10600400c650202030130003000c03000b02e182000c0200c1c0003400b06403421501e40c9481603103400c1d207002c2142d030400a0080d0a00c08905550b00d01503080640407204461900706120715400418003003640c00c40c0451610b0000c449848030102640ca44101300d9070392084185411017882e417142000d101c3c0384503030424258054141080030072833400245c2c2c103207001c1c412100740e0b02c2140c80301120025410140008407000302d800000c0d40c9003180300d4505641d6924240b40040c11803800c102c11001803442940f01c0b85844000b00d000307541e2540c1d40c6100202d00307582501c150354154a000e00da100824101c000740c0c582d066010b03015220061a09222000b148120310b019100c0c11b2401070741c8400140c96082c00b14541520000c0000c02e0b00c01802c000390b1045050300088140ea24050f00b0030082580012040c0e403065061070031300000f1405082c070502810b2010b46e0071421020000000c03907040f5000c00500328403006042101c0c40168000d00458520034646403040018100700010b1000d0b940300d4000b07 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 113855170 1250 113853920 113853923
    0x30c07031d03010c03050a0f02030603030714190b0106110a05070501030c05040e010e10050d03021002090a0914010302100e060417010b03030706061a0306033403081201080f0a0807 79
    0x800703004400020100c1d094400340141340c00001d40d95000c10407000c100303200f800c00d50020800300318154a40300340401e9482c412454040e0041d0702145004011300410004240c1d01e2501c4070300705103402d144e854074800d600000c0c00b0b2940807075904007416007039180004030350072000c0d003003c0104040c074980740041d40241103240c403020410a0030800030400000040c03d05001f042a207020682030720f032040c2e005a500d0780707a821040c425540307400d201c004258005010221a110380304010b07529143e142c00036103402e06c15441442e9040c1400c240c0714800c0820b03000d540c1242c0c020f03194040c4003501400225251001120a0383d80654288014050b00c5080c1c0d07a804000c840c02000010a10b10010000346507401c0010129081d68954105000c40c6000c04038164544080349200750850070194002622003852045804a402c00e1240c10280da81c04440807080d11003200c640d020b101500d0781440f5600c0d52026210f4001c4421500c00041d000000080c10781c420703006040504508569a5a003546940c0310701c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 113856420 1250 113855170 113855207
    0x1406030f0405100e07140406060206010605090a030f200102010b100e04021e0706060605040b0417010b060c0102070c2309041106030c0901080901050609060d081b01090512030c0703 79
    0x8118003e80c003944103040d800b200e100b004020052510300d140b08010b501162007801541000030800c0044e4000411a05452250400e00c7c2c440118070089000303400c00b94009000c000c0c0c4008440c060203102c3e0002ea0001d0100400c81484c4003c080042e82030f85d5401001c1130304500305400e5141c103540301e801e0106900c200140050f11b4003188440b444036030000702511001407400003400d002000741e0351044130000c2031141016801c0c030303107000c46182181c011486030302c80104070340902c0b0306181401e50100c21011001400c95440f00074400c5c0d103a00039045010100c51072031070000e01241c8041a0820348152201e1461444884c0052000344048840e0140c01203800704e5070b50181b07601c19036400c00550311645018405070f0b100e0500350001001c22101420300401d59252109105490321360f86a501d40c04841524400810720340b510f0030b00d03d41c1c4200b00825510040e00040107a01c500190040022280102c040b03842c40d1150744240f40e080e20090b00c21183d4040300700003501c0020700404011078000007100c07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 113857670 1250 113856420 113856433
    0x1802150c1009121106010806130807020a08030d0608071809050f010c020c0406060e0907140f030103260f03220516080709060f0519030218060301061406030f0405 71
    0xd080750165075140300211070303000d804100c4402a640c800295405042c4100050580e9458001d44540390711000d81103010b0640c861800f2014000040701b03c51503d80c0c09040d0045280d41e40700302c15100e401c002d107040c27406401d03c9030000d24200005040d000b42e0b24007904901305146480403900090900e0358040710342c0e00a404060010f0502031007007a150302c20503005400b4a035003000c100401c8581eaa08404140510341e00d408400d5100e03926101c0e40030075030341889000359010300450301c050f0050451002004200200110411030f04c2c0c002403003071008100c090040401c40e54100c0f000c9004130a04482420010300001e81101500c43d8102a080100d9030b28000000f50340e10781e5800c00ca10021240c0b44942c141c18200013040c0704004403002000044810070005051030070103126858580310b0284034100d40403c49110503c06840300c4000c0d1340c0200f009810340c1c181490410054003c4554a129510302800018005001e20710280c000400a01a42c51a0b413194090b80400c0000742c016141c5101c1d84 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 113858920 1250 113857670 113857693
    0x7080906030a09080a08040308060103021207080711070b071221020304170c03190e310c09030302060f040c0b0304030c140c0f120715030207020d03050a031802150c 72
    0xf4030080409944c5d40d501c281042c506803c2c043c2110300041c00240c100740c410490100c061002d2500c0c0d540207026868050340507192000c00301e03611a41001c1080b10b6000f0201d0008038041c2c0a07006180305441007402a80114503e00d054406003040f000c0041586108000792090324401d5000390f5000740705030303051104503201c0e15030380303445811042c01d0f900036620000f861505050742c2c0e054108030314581e00d000e04101d030303003a40802c0002c0e40001410301019401200c003116609a0400380c290600c8800741040000c00d01800100300d07030074a01c0241d01501581c800300d8a19170f0402c01440c0b04a4022112001e85072410780d584200340c0c0300030010380403c00521110300028400c408450b0100d003a01c001805c211000108124003a1200c60107180300380c1940300d120703546102c041820811141d021843c2c96070070201e984294080d2003111002540509404d4046c010035800030f0140907403000903603040181445015110031159100c07017002e035000001070010044001003000030000102c145094030040182c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 113860170 1250 113858920 113858933
    0x40c05030f04050a0b101e21030e030609030405121c120b03070f090609050405060f0612060705071e050c0f01030b18010e060102030315100c0b180601090207080906030a09 75
    0xd880e00621985c01c90010096094820581110421f54005280c455454158a03000000b003da105001010341f80c4540020315010b541017110441c009000d9807440e14107654110745a03405401800e1040041098044d0019800039258440d5400070454205000c401402500c07034a00040201c0c03004c0b038480c4103c0c0385e640c605100103002004081040150a42016020300984805030003020300c00d0715000410001c0b8000142041c0c2001e94084000b60540300c050201d80481c011050b000aa8401d0a060002192384000241031060084403200c07581030f10051a003c4a6015460141082d400707501c1d545000e185c011410401ca600506002075506081404550211440480b54128120f440010846d020342501002c0d80164244040d51441c030f4038896a00d1840181810b481c0554103e8a075201c01d0790140490b41d131180d4001440043c5807030004071401c0c86050362408490340b0f0061100010f001062030098610841c0e010802d00d0030b00011100740046a000101903035485a02c0c2c03000c01010a07007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 113861420 1250 113860170 113860193
    0x60f04140d03151403030f0903011d060403091203051207030b1003020405030d0c0206030109020a0903020607080903010606020f030a050d0209180a05011d07030b0f1306080705040c05030f04050a 85
    0x2850300c0100c3e072040003c80b81c1c20501c055511501a441800c3d20001c040d55003c011606005610800b107030300d5045080c0801e004222040c01e01f4413070b00d60040840a0310b140061054401c40c8603a07510b010b0715450310700c2448010b1034004000d020401c2400607030760141c03d040640d90f110b40180740004141c091400060000a0f840040c0c00100c0d03400074040c40582000d021411403c0c0050500510b03641503540401c2c441e01c070500c62040025404a000c01420b4842d404040c01541c00524682c1c51745841d00308a105036122440551181d8030700100016920300200780c8040c411751001c013540c1415102641661907910441071911074603404c218880311542d407400810000703c03d00c0d0707220307105180a4000008a0741f041e0001c11480400450000c0d0003660044015404a150f05d0040f4a812800020402d18040074030320f075070b00c0f840e5840e0151a21341e107984180c00300c80d1014102c2c0e800c2a50b50041c00308079540b0348000d4000a03020000a200304501c0c69007039400c107106604503000d14000d92108103140c84e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 113862670 1250 113861420 113861443
    0x1030f0e06182505011d03010606030e0f0d0f050a02071205010912031107062711130b0303040905060613030803060a05040b0108070e0a1809170c060f0414 68
    0x2942107800001c2e14010000c001021103080070a5400b0081010654120f4400d4030a60f0304000c0940b200f00c540d10061101e55401c00000740c02840380640792100680582107450f0200014170908180304040d034000a68a190708441e41c603070600b5103017142e8080b08d2542c000208001548111440001c01d10b40e822140b0303002c076004000001d1401035900d440d003101e0315050100c404150034071100d05908080002103600840d03020b280060913204580d56500010f030b034801c5a9600c5800c42e5406428805400f00c1c0201200007155103004840d4004064030858504050140d0103900c140000d1003000004d510194210307100a1985040481c803488a000d003903016041229101000300a010107402d2013070400c80502021a01440358180120008100c5080103003c8810407951070041601e5442d00e41c00100500214010f04442e1240c01001e1405400001802c485000328442500c001141507825030701d9843c8604058034803910341804440c01e441c009081954419144511941380f20030400404a00c04c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 113863920 1250 113862670 113862691
    0x3070801020304060b0a03050c01030c03111603030606090308180409051207020f0111030a08060423010e06040e210d020318060105190611070509010305060f06100e01030f0e06 77
    0xe20301413078120203542403621010700602008000703100044010800c00010744081c40c0c005100704440c40b01b100580901c10b140e0a600f000091002e180000605405441d240281c07001d00c01d0391350782c00c000c0700c010f14280305c00740c0040c4040c400c0b902c182c051000b800e4110301d002070000c6481a080d41342c140c00c0c000110100c80300c1010004603401141001100c50310429003d0030300098916100803911340701d00c10b450240040184400010310070f035607154440f0b00c07000b4440d4480340d444200311003c441d2041c000e004141c3c500081800050381490300d405045c0b9a2440040600350350225160708c000c402c4a452426140d000c4280302030b140100f801d201440c487e040ca8400c4002e42c00d10b40041504281040c3c124500518074010700c5000c5040c0480c540e400c8402c03925003c150802c6200b0300c0d0342060b0700d40d048940e00c82085000042845400550306000c2c1180e035040010548828080000840036140c041c0045042c034104554150702070390141807001c10807440070980c1880d10520f41c2c1012422144030150 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 113865170 1250 113863920 113863927
    0xf2d06050c06070305040b062403070f03050c090102030909040f08070f12020d0504150e030a030806130605010807051b0a0b071404030f1b0306020c0a11030d0f0e030102090307080102 80
    0x740c1048602d070407100900f0100030b40d00b4241c4852800f282c0c001d0006008d803801496810309002048000d81c0c0d84501c43c1d0140392282413035030004140c041148100c2e400203003400003140c185a5500211014110141c0095190200d208144161900010420b803880070706151001c1c0070443d50401001c2d05446011661818117030341c41d0642000600881c10700c21988420321000240b074104044800f50380c40c039100403482501019003254100240540070b905805400318100425400880b01401064111084c4541c011044071820032100782d88a07460000380030b14007103404580036000401c81c055200101c500c4a0180c0103a203483c000301440100c4644492000308143c0c2a0300000101036030390300c0c00c56180f4142c9946c43d0810322100e6400b014240c814241e260106142014107060002d560014003951a8090060b4582c0c5038529041c05851415614120900078075012170b48944034510f90b10384008403044100203d840e0010007039103a80541d404c010052096600b0003040000b00102c0e0005a039 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 113866420 1250 113865170 113865187
    0x106080304052b060209041d070501030b1008041506080f100609020408060c03071e0207081c080f06060d110301090e010209010903060e1504050a03180f2d0605 70
    0x14101c00c02e1043c2110324002828060300451242e54580e8000c0d0094005a260301412000a009210240d4240090407141600c44690b01c1c001c90050111035090724100603640820047c0501c048580000c1d00014151000050000780304401d001101180c280e03001843c15210510149004502400780c240e9074004441004009260702608000d03041c50b50301542040d1030310030741540d41d42d0043c04590f4000030100000e1882031242d100d0110030450203800c0301440300d0000700a0b449101038025441790740910116820300403001c0e48452110089607403541c40c2a40d880c2180021035002603c501e034041c0c0200401c28601e4498000c0300788010152224660380e5242c6440344040340c11154041740b241c7d0042c080e050840c0c1c2c11186203003c4079009140484c0700030b00031682c00c0c05d1914140142c40b44040303440c03d020500100181030f900e00361080e10392140002c0d440b034814205010328454504c84410310341050040c4541c03040c000c0031100d00035a2030f5030745a8a503c0316442d800a290081c1c000544041085c0c030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 113867670 1250 113866420 113866429
    0x2a070b07020c0a12060b19060207091107030e01090b0c0c0a050a03080922060b071101320f121603090b042a1e1e06030c02030c010608030405 62
    0x540146a0340014038040c1c2c1c1e480041802185a44605044051070500141c144449900b15140d113440041c518604640701d0006444150450700030800144280800420401e55521640c44a0041c034a8003d003404410343d400c440030441ca907103250401c400d15600042450906000e000c0c1061100d000e4481d01c442070042c001c09005990045219038200c61040011404440803100d06030000e86281c001140b0791403024820041841000d030311070b483e005000401c1c0343c03c800682000c62044403940c856032140001103031131481030785c4d14641c0b5056080780c5140001003d4608a0f12411075050340b410a20069081800e82d000080c10b000840d030018100505a241810031488030340f02030030104404001e83e261140d1110000340001c02c0c1c010310008403000000084086181a03484a4104110f20744400740ca0100300601000c3c409440420b1501007003038100030300102c03140c0780c40c150601025442c00d0401c130068a8292000c8080d8001007010610003400be00a203809400f00c07500440e5118030701024003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 113868920 1250 113867670 113867693
    0x1809030a0f0e09040602030c041703090f04090c1511060103050105070f0801032406090903030b0109170c090a090c0803090a06031406010f020c0a030309050a05030303040b040b2a07 79
    0x100021084440450f0b5940d00d2a50340150f00001c0068590380c07400e441c84140e22480c0c03c580650065940d0b203900c1c0d040004000c148003201130361135441c8100c000c000c2c001901c00c4070034004e180800360030084c4004007107401903091851484c0f0f002030751040251803540c10040c0c2a002904d80341d44034401c00051039000209006590b420346403d4106600d99100c4210104c182d40e080c600051034003000c450742e4030b0703540c01810240088000402c9440c41620300036009140500c1e03d00c1c040340c40c038540040c50320919920800c0761641d0070050b04440960000b00503e80000400c440107040e40e9084100201c0d07a100b1040c0042c004410003156115003500400540c041c0e184e101508150502040f403a82003803009980b80c0101003800c5c20710804800100582c01d0170243c4420a4004801950000c14194003451580403203100340c5007a15610345803014551248007c032406000704099030301050010302080e8003107900010010030480c610b006072414400e00d200e50700300d40442d4180401c4890500032040c08a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 113870170 1250 113868920 113868947
    0x925260c101205060102070e012301051c1d0304060906080609100b0d1e0606030b090f010b03100302090103150b030d080a0e120a0f02060a09030c111809030a 69
    0xc1da0005144008001e003800d0b0080901554880d004502e090b4020044070000d0100441f45111ba5038503080340f00341d5900401424800151052420b403450b5000d002215240060701e4040ca40d4000201c0c00d2034080d2080c5100c2007604591134034079502c254030038800303400039040300c0d56104106440c00d00010800310010748424413035903054003031100d525951130108040b035a0b030134140c0d0b8490b904254003000400e114030215020404054920009030401d07030004e0141d400700d4608001d010558814810202c0c41120007500d0040050f0050000c404044081c5602040a560407020710703440c1d45c04142c00200a074003c40705041480703a0b6608014582c0260201d488041c0c00900d502c00c0c030300380028115031010b4009050340790f4490112200e060240210b2001d409a10241651030031a00c4004103500e83d6415848018090303040481c0800c0280d0180207000d5030503503144400c030501c03074842c5e4000382c0c41c08004581c000250750803100d041d000082154800c02c210009151140096000a0641c00c14504c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 113871420 1250 113870170 113870179
    0x90f06171012030e19091d0304030c05060c03041701021b0d0207030219030f1505071803031209060f060f06020c01020604080702010c08030f011a030925260c 69
    0x209100d1501444040858960103140c0319500120300c50200e40000000c01940d4428244820080b07544406504512220f1076082c60240c0483c007000d040d646c88c4d009a00004260f484c8400307040185280c804064215900d00d0801d0300d1406039178404c1c8001c4403501003101042a5004150f40e101103415580780b09080414002030000c0303903000d000c000e407100c0f49070100900c690104100000c002c001e01c403080e0007540d03000e000e040000a190807c00350015a282002e8801c0c3c0c2807d00142440f44a0086034a0070320f14034885903400ea09540d02995512502c005007006c0e66079801d88840425420300440c102a2262600010b4007800c05100e0351200d80160840c0d0b0035136000352400c001c1d5983c0001c040741c1c00750300886120380320007a07840100e440088114001d400142c1c00310620020307e002d00d00d00c9049502c6071840c0090358400b20014041808119091185074001d881a001e007290b161800d1451107100724001500c840c0c03540c610781c01117410070f0604900c054104110a8050724104806229060103d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 113872670 1250 113871420 113871451
    0x909100614040503030306040f15090b030c0102070e0103121707050304020f120a0b040606030605180106080c061204111002240103170f0c0d030506042f0a090f0617 72
    0x8080f0759248800360029009030703542c10403000c44841d540d10040d03003005103080c004ad800f40da9a07040f002400268812600c00d000f83d00108a207907000003480001c54860b071100014680c659151203180c0115551000240309250102600c02400d01013007030702c103580355154141c580c186401808501d10140780000e001d0f002120252808000010311004202e902610b11801c40d56a031504c18050090b035400101814200310070b00411f90200c2c203440f40e000c1e0601000f044180d548035080c03076498010080541d007040040000b0409013078003a0b0a1a0b0141c0140401801c405681000ca044448000c50000040c0c000d00c13034003103055181d1714003000004039180b810b403190350440c0c49000e0443e0f000101100761001c005800858410f110003951200ca0b02c94081d1401c1d29030008000d0080c150896241784150720340a852811aa100d0f607204581d003c1400382403605000035070300c0ba1459846622482c05000e020140001c0d4038018400110180500f80e81c3c54448000d0165a40e01e0820080e008022400c10715 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 113873920 1250 113872670 113872679
    0x70f03151a10020703051b01110304050d020904030201020c06010608060a0618091805010f0f0b060711100306050a03120201050105060708090405072f0d050a080a11090910061404 78
    0x8402000041c504896500c41d007118108140d2a00483e070b800145507016020803070410020b9804010405c00082e04e40304d04600a4100081e01c0340320324041e807680b00f8030214140303002d410061404c90b40300e0f12174000149080030092450b450700a09920030300018a2080c104112401c1c1010350f41c0c01400d40d0300340f01484410a01a03142d17000654001c10804903540c041146640ca80c41d00c0399000181c00c100200138034841d0300289005026400400515281000e03841101c50810750210b03a0583d802c40310460440d002c01d400c124a4811800210781010b407281c1d0041000d64a4006800c02584078030000384c03955010740000317821b50340168050303403040300c0900011020891600888250b800110f074005000c3c3e03904401900e00003001c04481510071310200d501c865030302603083d02d854107540348001c80e500d80c2510300c801c403880d03c1703558144400500034801107145207030290040441119800740c2241040c5908001c2580440221010342d500e40c0241010803d0036005503203100e401c000039844d00d25040c02d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 113875170 1250 113873920 113873951
    0x902040609020d0b12160b0a18060203091806030c01110313080c1305070f0c05121c060824150303030408071a0c030708070e310501050306010323070f0315 68
    0x40d1f201d00b403204c80700040c0300c07281580f0404045400b040c13200c81040a01d601c420000390ba9030410030b5400c0c0540481c070b07031500c24000701c41400341c4103010050040010002c070400449a50701c1500070f0702c0885c401031182090711064000c00c0300103080400010702c2204c84210401402d4161240c0c0d03016114a00703014801d0180d404208042001145d0421417008a01890305514003401d0307024800c240c1d2004610307901c4c124202120965580000b1000b80321a5445080454860040c1e101c20010104030140c50403002c41c48845581d4041d9007895000304800444010070706680c012601210f03441800110041000480700c0e5010350700440030034503603c5e4034001038550f10310310001d04050240800c11000070106813080700200302c50400542111280210300301c0b4084440116451740310650301c0f0000c1190840309621445049860040c010422a403a40d11030014002840b140d11007600d480e4220003011010030031510004003d0160240d84540ca1400c140c3c008440020031829202e081500c084400d008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 113876420 1250 113875170 113875213
    0x308040b030c1e04030308091614030a08040f170c0d02040f1805100b090408040501050304050a0f080306041103060d140c121507020a05100902040609020d0b12 70
    0x803400202656900c86a034111814081c4481805840b403002030041078107504203001d08100c0c0e129803030310141a2200040207031940340c40645a8007241c02800c3c1001100300e80302c0355254100c00034080d01d04480264880140952103a0040c00c40d1821840080040d170141d2404000705114082c003528407902c4681c0058007802e890b90300030f0310450700c85028100e00c0b0710035800902c481e0a16402c950204007545402622003202c0c3e5a0b04085a142820003162030401c00720151140364081c00711450729003400e00566003904094401e43e05840f48a11301800945d404903182002402101c1c0c1940b02d1a00e0000c000a940070840c5d40120080180244500e40d29281041c03801203078840f03070b000780482c52442c0c401d00e82600f0702d00c015488001100c4101d06558040740d2040c03121207600d110380c25541c038030000740d9681c2560340000b0b0a90748108901d20b030f80c0b465540800d0348144001d0000c24000d0380d501040003603810400900350350740e0b41d40040218a00d0b0540c000e88000e08203c000e89101610020304009425 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 113877670 1250 113876420 113876429
    0x901080d14040803070609021c0206040b03070e09010902040806060628020111070b0115050310030b07030b0604080102030601031a0f010e0f030a050d090f03080a0315090f0b130204030804 82
    0x5040c01d01945041101402d032000307440340ca81101e846a815041000103002c0840040c1c3c000d03100340f0507900191018408844810b6005000340d49001e25065204840b503000826502c10090502c0c0c007243d09641d1125000d009180201c40036031114107280109051034000340000d403203840c0c00c010b03c4640031240c1e030f0045079102203030030b00f44411050104103034003402c0c420175035035080c4c0c00015101e0200400c000f0460b0603a40c1014030840f0608510b64243c4803448140c907011007070280e0140400020b48050195940950b4500d4080388070301907c0701145175900b0030703045440b05075004403c20400703590501c5050001003000840c076280c00c12060124480c1c0c2d1701501042d0400c09203e00301e003c02e803078000740018240005000c5418544081c149540c840b0142600781d0001001c1c480e001481e00440c03200d0300705490301b004a441c40d0001403034054004041c03075024a0b8030182c201c5400101c550701845103111581c004040401d01038560010000d103011074a6003200014030501090020500b6481524141d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 113878920 1250 113877670 113877677
    0x7050a0e0415031e15060b2d04181404020f0402340c06020309060a1b0506100821041a120c0406080f040b040b19020c010c020c0901080d 60
    0x105220b040c0b498203441c50b5080a054100491154040d00440410001c180d60103801c668024082d04030351381c0182d4400e8498155454070a11050040660f4a020480c008625200c0928200d088442e002425002a40182151502081c11200d00310142c02520a0620007118415540c03615500143c86070a1300031106024640c0492407a181c5002100c1110b25018000b0b00c001052080140703420420b804094200c0700e8034100c02d40004d03054000010f460700504000c001904200c11040100d6100c5800c0019556000d20550341e40301161051055600611341c405401c0465401c25103814981500000104010190018011070790b16200c2d0540701a500400c11400100c2c199107400d4596025103d4451a060a00c109001c070701c1103203034001c000300c400702d8131054025030b1a100e202c0c115a0382220054200e00042c0c00080021b03000310320a07540f050601030000d00040b4482858000c13030304185204000c582d5907078116140705804000b03869142a00300c41c1d0008640c1400e00141d2911030150301031090 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 113880170 1250 113878920 113878931
    0xe0d08090f0106080d0f09030809041107020402070507050a0b04060804080f0c030d020c0606091e0a240f2909030106050405040809040501080f190203010e070b03090607050a0e04 78
    0x50860501401d0012031407030000707100041d1140d0040d030b1103a805020800200348041741c0011040d00510b040811241c110507400d0a000b112004d10019001004100c402d10601700300350001aa04d038806850b8107802440203261303180c20712060161007200c50304814407015080c40204051540300551587c086d612100c01b50321001d481c14220418015080c21001c0e0740804204034070080550b40c054402c10094108a40242c0c60320030901418443c1580c4000e440b80c1d1403100341140d11403950400d90800e0103c0000910003a49480030a1220510108044880c510386410400e007104040914041c00500030641010058403440344882184020506280c6101044a4255a03400e501c201c00400c4d01030428030540c42c251038201c00c640e1040403107074482c41c40c100000c0390300240001c070001650341c0c20005107004242d40c00c510128000000040360325640f1241103180c1d113002070216800818101c0c01340d603268144a8512801e298000301488200841400700e200d410f43e01401d4182d004209840005a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 113881420 1250 113880170 113880181
    0x40b030d05070c0e010b0a021b0d030c051213060201050603300408030f0c0613050c010e0604050604030b01060807020a0302120307020114090c011205010b090613120605040c05040e0d08 81
    0xb810405512900f00044d604000180441341c100007825043e4180e0300361800400d464011915080745c2d0f081071508802600070210000780100d0881c80300c1ca00034422100701c1c00c101080d290b080c1d0b100307005200904400040800049409019180d0420700c00c501800584484803a40421400346603c020702815026640d444001c442104840c013800e507407002c0d00d40e1503001010f1904241c0c80f1400032425031240000169050054642100c26154880040c20305050f0700390044910b426581c441c1980040304000005403552490010402984a14044121580f61090180c0074440040c8a00d06640041e2031150000707a000c68500000003005039015180d441d03810f0101c6c01050f0307a500c00b494200452052142034200080d480309104400d80e00c2215402a414042c025603e0a22441300510b20501c07003552a89450000307003052426080740da1074005d40d600d0b224032060060342c806541881d40c400c24030040c000404103010140c0b100b038605115070405e0205503681c0781500d03800c076000c10546001080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 113882670 1250 113881420 113881433
    0x9060f0d0b0c1305030d08010902030a02040801060e090c090c0f0304060b040c0215060103020408120304080705060112110f01020604063c0f0506011b080403021e0f040b030d0507 78
    0xd40098100d60462240c0c03420840241c030310380c0b00920020300c0c1655440c00040c00d2400040c8680d8402c850f541d0202c0f071b6481e0526110280d000504080c514540900000c201400c1c00d114100040181c03c1e042087c504006440500700200301c0101d5005285513401c2005e4022110226140d607541644415039941d5181071100040144020341540241001c18503905680d0010f20a5004040c2c5048501c6030344503080150102e00c514810302003607400000480502d02d09090242d41c0c403601801c0030501d0070b54543c2e5200d06101d000d8000c000e0741c0e440e25654000780329050001c1d400c0403030141c402620b0700340d2110010b90b4030440200014901074031034001c0398003c1480803070348104408000f000c100840f44910590140650360010380d1005d880c02041c1c3d00c0080c0315025a900803001a101d20300e12583c584041da0701d8940c6484c0c1034503100020040040183c6a11354520010149802c0d49107254205400b0070181c0308600181510460a000754000c040d50302080e43d00c210005810301c4c3e69109420b28258 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 113883920 1250 113882670 113882689
    0x20a1d010c1401020d1b2a020d150b01020307020a030b1017010603031b0f08160b10060f030603050d05070203010608011119180b03091516030e03040509060f 69
    0x1800100b01000384008000c0540207000c0d15122420107008219098121103541e40400c0c01c0d00c000141400c0789040d018407080c94100040445201c0c4201024464022a5035228040000c41e1510000b00c0001c0080c2103521404480030003d1018501e00f80c20b580005150312150b0001504011540d008378001801d1070b07404d0070040445940d010203040c0c0d07407011640280f20900c419001b10780380010540300e400c17858282d0700c41240c1c055021030744c001c07007034454a0454001001030f2900ea020498100b000c6100141d02506ca03c1d6003200c2c4840f101c1c20b011005120101c421001c4042c9410004140000b46001c18000e902002c03501d0107076203d40d46800003c0c05092140e0086207a9403a2441c01f80039202408001c108202c82000002c40d10354500c0004c595a9608820075407103104820405d002c4201000011034000c0d5122080351900351244070603038020b82c3c0985055058010040045450703d825000c3d165070707400884091420240f40c02c2c0032481c8400c00030181031082407158071142d100d650303448a2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 113885170 1250 113883920 113883923
    0xe150609040c0302131e03111201020309070303090617010e06030a02060409060302010908120d0b0a0e07080f16050706090206040b070605100e040f0b04060b060a0504090f020a1d010c 80
    0x7400320b030a044401034001d500c01c0b40da000714180c00321408680503410068001841e00400540c5c50124a152034504440c81d14941c0d0550090401c041d030700545a00340040c500515051000d00207503484e626004d001414580e0000003030011307600c011281200c003021540d04403002c011004401e60784d68070003e800d28007261b40c006e41c0030002180100c1c440400b0381c02407042d20b00c00c1e00c8594000303484200c22a65405c4141804900900800c14580c020225070008004404041c00d03007150a5107410b10603581c0c10086540c0c400180c401c00400c5201088101d04170781042c500b101061f5038800b1050003c04900c42c0c908040d10440d100c41e00e0b24115260381080341d0050000b0410552100550318018000d45410344403d16510040382d004101c20131900a02405103a100b0401c1d201c16905945d0000e0280c0006c209617038080d980c510031409501d0700002410301c100c803980c90315903c1d420b03c20400100c480e00922181d149105014000e03045030010703a0341c580800c807011112a40c0c070030300c0012240f41210090 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 113886420 1250 113885170 113885179
    0x18060408030d050910021201030f030306050909010506010e0a12020607021302031626060d060e030a0e09090a030807210603060605090604110d0902010e0303131e0e150609 75
    0x46403082902d9550005028100c1e81d005d98000c060905003071020380c028504a00100c40d4071000400008518040000c3c1c001e1003420085600c039601d10001d004c6610131100200030742d44910070003481d583d101007040b124401c100e441c41865401d0201c040b84419880c0d0000303004100014012041d503842c9103815501c80003940081d583ea1400d011070014410700340381d0020100d0460b01000720012500c90b02d06505602183d5090a40d41e2800c0800c00038203403609003620300c199500400c02c00d140080c8014120615541c8440001007900710602904200041c403d0b00c00350064000d28001a510030b884079041541071a203501c002e2800d04100c003008a900c00101907451030240000204680d80d00801d04507141106d000c80341d56142402d010070344400016200213200100318181855190303030310a481103030062501c1e074800e001031008a03103160302060099210717841d41d5400b00b00041c1440d40340802c030034000700340b119081e00d4a14040c0561074040e1001d81e101c015412101180e1302d0f41d4040d125034030001030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 113887670 1250 113886420 113886427
    0x711060a0906140418050c0706060b0315040e120a02070e010303020606130515060c19080408010605010f0c03051b1005090f01060302010e10030605120601080601060f02031806040803 80
    0x110252400d03401d40300d10b034080b81250a040d040030802805503012142c4a002400c0d43c5a0750540c1c042c01410020700d1115090720a101010104000e40f0a00d0302600d11030000540c0d070300300109080d03e100c1640c44114030036400d018415401150104071f840c102d050100b64141c0315214040c082e81000031541209541c1000c079400001410f5000810034000c41c001c0d5101c03164105048404800d07a80100c8003000e211100780050002c2d800d10fa8010f100b43c070984000d82d644048550708455144400352810b80340c258020030305000207034080c860100100000d08055854901542024060500a45000d01482804030310042481009441c0c51350030010401a035400a80d140405c1c00105020b880d0302c0900c0c8580810051001414850542981c1c4c05071202e8031039007000f90400441c07401c0c5120302804c06072160000505074464400c203200d040d4810001d07102a605010306545850300c1640214104080407503076503126500441100c00c8036420b206012080d1040e00040380041c801ca600c026014800007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 113888920 1250 113887670 113887687
    0xa031209020109080d05071e1a04030210021803010e0a020a14040204090e0109060608071d0c0909013305090603040c0e070c03090806010510112401050f01091a071106 73
    0x180003000214825410b0114406c540001900f140c060842c00030710b141c2c4060320070070070024240502030340b042c800e10440d37001c1c02d001441c010603604115013100c0304207480c0540350202e00d020b00440400c0300d214401010b603a501038000440118051141020151401c0d0b00030200c3d40f21501180d0240040d03400610800c5000b000a900900480070280c2d140f51801e41d022a01100203e00caa01304c521166070201030340360048000b4003020028080a1140c1810401a1000c0d03d9100700c840c028103080640180308041040078075058a2084440d1031211800c00100780255080b02c01c0d100d01c03010640c3c43c0f41d103036512440d00700044101504412a8040e159040146459001c410003904c18031a9a0b641d00ca10764405485640d00402c0c040c181e403119014181e561140e00c2542c200107107205c460122801300c80b0701800c0c400b00988150210317101c24030b02070060145060511901341d40400c00c2ca002c0184910f804040d00100d640c1c610381c82d03580800000c0da1010b000084a1000c201d410040920b503a03a43e05 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 113890170 1250 113888920 113888927
    0x60f070201063606030209060f010c1a060312040f031410061707120506150a0308040603020d0606110d0f0207030605010b0c012a0e120615120a031209020109080d 71
    0x10341e1032034038214050300d5110080e0143ca01410084070b034044c064000b551500c070100800360210312283e504001011880c08003080120f07040900007030805002d1078003400e00c1c1c005e041c00e240070400c2100c0c0c14102004108081000c0d202c9903001c40760070400000c100501e0a1209081145000b0307400c035854100072000c55a0300c0e14820342100b10b4011b804554140350780e803262064130f428050303000d03002c0c1c0c128070009012401001e400c1041d00d50014001304001d030b00d950f6400401e07001900154002070b408520207038800080c2c03141030090213590078507030500c0c1c000180055844030510000800c2200b807508800449000308040006181e02031414010740d038590140c81110b0704181c5a0468039030034140700a41040803070902101c55140000707011204540b0350710545180b0055180540c01c0080c4110030840200706010460003214402811205000340c03008000034140c1810340300700540c001c542c0010010307400c01401030b41c1c00f505030b20206040c403140c00103850b600030580c0450f20600446200f140c0c0c1c0caa0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 113891420 1250 113890170 113890229
    0x519030f030f2705120f0a170f0403030203030a150b03240301060909110a03030504031e0209090a0303050601050307020312060307030210050403120c0b190e01060609050109090e060f07020106 84
    0x500f0b07541c9001c080020131015030b1b10210084120081d130040500310010070245141c9400c0580100c090300e1510b4440560011254400d03403043d001a0000b03c24801100c0c80350280e01d1000d50140c56000702503040201c0e64403d448041c007039001c03030407030102021b0100820b00e100c8251010000c00800000d070352a034484016150217041120000c48810003900c145c907199040005a0342c1585e12981090f00316940c040341013040a502044801d20201000c00680d10b8464036031080010401900c4501e03400c0c80c2c050b00341c03500500b00d0390611005208104205500009503050540300300001000c0d903d4520220782000b0f034a4002030740010307172027051004198200d4024001c581c81220510004000c0c0300044540f1012082d0003018000c8540110f083c18180035002802c104003040000340990780700030300701d0844040d5441440422400e02d0100000e40c2c1007a60300c40285011036050142c54803480a45c0e071102d2005059190000702c50020600d128800d600060181003404001400e68201c1160f0049184c1d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 113892670 1250 113891420 113891429
    0xb1c06030209010f0512030a050f0a020705031009110102010b010509040b1f03051602210f12041103100509060112031b111201020702030c010807031e060519030f030f27 74
    0x14529484480130060010855a10310010780d270349400c114078024151211381c880502801144a00007002c01c280c3c6c0c050000d0b9045071262407000800489515044038049080c03070096066915100c2d0300100740c0d81220846031040402c440010307868072001c0000e0030441c030750b0400034111600d1401c44928580c042d40242d004100310019900c003040d00d00e100700d9840000c0d4040c0542040e0590141d040780d19103001419101140460982c00d25801c05003100d001482210300780c1c0d5044814a0140d01d42c201070044a6441c10a82d40c144505d241c070f014040d543d80018400c220341c1e05230200124007031600c01d00c980410b8502c0c2d61440000706185003005202100f0390030341c4901ca03040d44c800c41c11002105108850000380d0180c06003032002d110300b00544900c0c200500003401c2c95102d03400200800f00341541c118204903041d6000500790309140500000c0062240e0741b03042280c00103002d0010600c01d80d15803030401d0341450188000407046008071000d8446403540b01500d500118940c0070752000d070441005a4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 113893920 1250 113892670 113892679
    0x2030c0705030712080f0403121e09030314060607030e090a18030e1c030c030f230c0606040905121e04080d1211040b03100e01081005100b1c06030209010f05 69
    0x151070700c00c07807090751b140c050300c00030007280c103044604400c401c5541000b80d8918101e9101225801ca868120b4140d4002d0002100001d540e903107a5800244c80a02290301b204081c5c441500308080341c5d07030280c6100e00710a0550310580d07241000545030031598100c1c034441c00700c01d115844206010325018111494079550140300304045800d40d07010400ea0f0a8158500360140c0e03501014100d940c50a0340c40c0480c00321a1810450502d000710030f208125808004202c0d40001a565109603030400242070645c0605503a10a41c1800702205c0030540000e0302e05400402243d1841d41d07040070450a0800d03440026982c100201e01060020700c21a0108020411103c2034a803100d200081108440460399124180035040c2414003050182c1440d00c4051540100030343d00740c40407640ca440e10030031407002c02d9125902070703800821101040b002d035001c3c00381c101040c1c04041d4001420110300c018140940c01504200380e0980c00c20581003e144c0d0058401990040c007007104950311160340156501d21402050b008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 113895170 1250 113893920 113893937
    0x90a06050d0509030a0512061f020a0501050108060105033d05060f040b01080a1d100c0908150708070c0210020606010e01020721020a09020c0601050a051002060a02030c0705030712 79
    0x143d007004011030384840c041c2d07601c25240441c00040b40703107622400b40c038003600f28042d8040011082c0160401280e038000070340003071845400c00d103005030030355805810604294005c040108120b0700d0000d100142c0031204420b401d50100c80005904040803c00c20101442c2061002c816038581540c0c40340f40901c0d41a03039203400c02543d120600c800c0e605d8000e00b1900003841f090005446840c03030b900c940319040401240c4003800329190b0aa52414180d1203032019a165980550401d0b00d421104100040a085000c1d000101440d400708110760001004041032045100000e24480d10904011648590050024a03442414000296146022200c2a02090511714500080d60000802504481c0146600b9510410b100252041c1e40c4a01d0000c9030020014940810a0b01560001c0c01040f0050b0000b01038941c50207040000d07190240d4081c6001e500050000c094107540480e94035417040590b613001d41d0f04d84892103844214814600050510b000c081005000c0180750040f01d40c1c80041ca599a844 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 113896420 1250 113895170 113895181
    0x140a032006040213180203010f0516020a03052203050d020d0e04020903100b06121e0c07080a08150607030c02040605061201030314070c06080423030901050f090a06050d05 75
    0x2501c92080d41d01a5200c000e1840b071520044458200080117100c0300039a500340940d55002c2402c0d103c0c00c0550300d82007501c9004005e0482014500b00250050b01d00c0184042c004a840151052260440c3d13103416006454002c4105200101c43e8001150720404541d07180007480002502c07411081e1501000500c4110602001d06c1c02c1e00076a4681c0c8002000390000c50322036041c80700100801611160001003d12041c8042030384200c4440c464880740c0000580200d2000344582c03101801404001d0a4409204100c0071a05540580303104031042e06054405844007403009050261070008198402c100180c05c0f02050303032100c004814144240d40901581340c544040100d2801603020708074124281c1d50040010030321414040d030b0b5110329040c64610781002d50302c030305141c556550000c80215900d0f0090104000b5000c1220020000b480c03c0141d00c800b0300841d850b00ca22a25915a04100700070074a9110001e56a08941050300c005001250496546074050840d07013000b0021010b40707140100299 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 113897670 1250 113896420 113896423
    0xf07030b010e0402210408070c0e0c070b060307090204090e010b1005160303150905060102060a1b0c1502190906020303010302010503040204020708120f180a110d140a0320 75
    0x1040030405845071001c2000b09401d21000f034000440c1d00d59491803084400d101280f0b40b18040b4000c40c0103507240780e55210b0a08140c11011101c0c0e0000780650201c10800880c40808416903102c61380c030160000862701c81e980003d10f0006c06400406440d4400140010300b0b001651210300805400c030000c0c0800242c1c2d104010300070b1092003c0b600810401c215460201100400c2d920707800c2d1007030900140300a100030000c1c4030302010707400c40c0265035034400c2442095a010460513a02030102c54050010401030002003041000da10780c00d40c00c0c0301025011100700000340702c4c2e8024041c0e10314401c6441c1c4017042c00c0040107010300d4002d100401c45804011400724400b0086a042e0394041e12601d2442c1c4840e03090200940c0b2234031058402c00320a111a6410310301e0b0035610750040400c1106841e0905010003c02c0407030f1071000a50350035600210030500058030003144010002c00c1191107076010300c61820620846090300c0420b442c1406042803030303010142c00c045a5804003c2ca0490710130000103440055 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 113898920 1250 113897670 113897681
    0x110111030610030203070c05011407080a051302060d020c0303090105040b0906040b01140f0904030807111902090402010903051c034a120403020f03010506010c060506150403030201050f0703 83
    0x380e007020b080280c0080b190b00a400550300000585450304400740580c1320282100d4100546c0d81c81c1c030766600e00340030086038001c0c041b0307801c080e400304108064200280c0814200340384500080c0102008211990b00f000e195042d95401d1404105590341e0f40fa02e04202c5000701812282107c400003401e0105644400001e1030503c00d59002c0c0ba41061039081c1080502003200010007207502001c000030350034172070304c6d10b81d440d50007503110351120b518034200700030003401c40d80300a03200c104640c4c42861325030b00f002041004840c800360191041681600d0b9400101c40c4080180c2000d08140b141450303607210030f4201c20754030100d03102a035420021040c2d0840f100c90418070352014104040d048410603000f8480c0d030107100c00c91003115103280000b80050240d240c03c01d0013090320364620141c082410401d6045c42088802e04510480003002940b50220000e01600c01d0440c0203400c0c20350395000503c82d510f0308404801103200d18040d042d100d0b03503241b0f0001d02a11003100c111030b10781070450211740e0844c005d0050703 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 113900170 1250 113898920 113898931
    0x90f02091c08030708090c0d1a15060a120e0f030301090b010305060108061207080708101808070f050c060d1a04060e0c220b0a08160503040b0603031911011103 70
    0x1203203551101c0300c0450f00c3d280050a04000c1c2d009807a40303085582d440b40c5080443d60b1140480c032700c212403203107184004018024604d5801d62038280b81c11000c0d580300700850756000710038244021400d400400c5140206202e8400c070b201845907034445082c000c0004007a60480c0c901d000309020b190305420046060700c03c15240180400c00500216106d45840d603441e8505440d001c1c02c440c04a41c0e2400c0c2d540c5004402c0d8400350a90300072044a0704900315a00640c16010303003090740c240b40c0ea010b65030703410fa45205507000a03010000d0405034008002050210556040000b05105e841d4103008100310300030025000c1e840c04400240a10000c6404c1c50300030740c82215404442642d00c1c4d44e80d404038030b460354090700c2c0c10600703c0e2414010000102c0b0480b5070030007402c420b20105440d81c1d41800b02034592500a00640000c6560510740074a00c1d9100341240c0e84290704c0010854291154000b2910b0f601031f10041c0c1c0c00740b160030041440c2041d0300c60401c7c520a81000000d0050594885c8880d4041c841643c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 113901420 1250 113900170 113900183
    0x619050303070816060903030b0102070b07080901032003010602070e0609100603051003050109080408010617121c0f050f0106050406053106020a0506150d0b0709090f02091c 76
    0x403600410f40c101e01410089070519401c039601d0210355140350480313002801c110086583d9030041444c03541c0c1000001e02801c0703405c211628286240d1580c10050080d03c00c100c1c10151100e4060340040301004421415180501d0056100c0d43c4540010b900c40c8814003c4254814403600090100c0ca40b0b03c5a035802030342060b05203001c103400d20304120064000202903400000e004980000010b42c00d10642d084580500650380e225418046000d007500c0d140d503c007141c80c000ca5188281419000b182c508420507032984240c3e581c0a00b03943c281818107050000b48682c0d46000040001c0ba181e40d0071135480741d58071000e00b6600340e0302d607039050381e0600590103202e00250081c08504551034007801111a40d00d141d44500c0c594400030149a000250580c21100041e0420344580b4208101040069049540b15034107035000700200002c508000c070300c007001500c403000250100c3c200c00c0c0200107103805822521303000d014035510150100043d42c03002e9115401045500d42800030340707484c001d00c007010903803284 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 113902670 1250 113901420 113901427
    0xb011205060a0506040e01080f0c030d0f02012307020c1504032402070807030f1d04020738010f05010c0b0405010b100f0206070215180f1002030619050303 68
    0x10a0200400c0028060382e04003186400c0890b00b5a240e01c0903200402c03c46040074401d60600d80071134282030300716455181c00e43c8920084140d0341d0b80400c030342500048610f000184601c802030120702424008a64100f00701c401503c000140200489840c40b44a03180c007207400b901200020312109000800301100441e00c01d1105100185d1605034003694246404424120a40c0191107030040340e000c2c030400c4034803c0c0e002600508044e0000b286034400c1d062820000b000018080c80341c1d0f80c00303400c06001441140d00007a40c3c070811240c84101c1d110803202010b018070351004a960341c94281c0307020408042004d2144000540172090942e610252441a50342d030034040140d80e1600031108001d44101c50359501d034604403040b40c84541b52501c12030f4490703032640c0d42031603005c07808dd040800c01f400795811504078964410418031211a003d4100000681c040d000201002c4001c0c10088a4100003205000d58120300d005d0f20744030340185014000882d0382c094030424800c243e0310b81c41214800c4a825420a2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 113903920 1250 113902670 113902697
    0x1a0601090303080105041815090c0803040b04120320060702010e03090f150d1104090b100804120c021801031b0602151e09010e1207051525021506040b01 67
    0x540118204540d841c20347c1d0345002665030f41101e40107500138080c1415543e50709817801e02c404154500020803007100910b10380381c1007140402282c440c0340a0000c404288080c0b080c2010320409003045181c00012500b90405406540292550400c0e01c0d014015800e0081442081901200f110b00c841d41c01450880d842036035406220960602504c0082a04011f00c5407031080f51140c05481101c8480c420003a03900c6d803d0501c84003c035002401940e005400c00c03d940e118198004500c2a00550400d080840c0e41040d50000c1b50341c03079107988009401240aa180442c25020021403034181c900c206400b44045100012611086000307101c0d000c0180d100f590280d9104105169540d0081c40401440b48015002220003c5000007551100c0407a0b55420b6450301c0403106001c10040d07401d03450015460800c140c0c94503541d03109034000790140301000c5008100750451040540303030660307402903240e01c66a68200001e1f450f100e005d845441d8045002000440c5ca19040c4183c030000c0d44142c40f10503c81c42d08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 113905170 1250 113903920 113903929
    0x1e0623040f0503041d0a110306010807080a0f110702040c030b011e02120313110f010e04050c070512120618041202010605060d062102091812071a0601090303080105 72
    0x240c003010742d11400100702c0440c009120407040010309012110111050a1000700041243c181c034081c800a54010f0007408aa6a805880c0e03a41010952500102944440c02000020f000444131031041520f805000c000301c852020243c048540211010401c2d03104041c410340c180d4000003101d0340011b0b9002080200d14203400280102c8903000d20440e900d644031300311004030030780c8181e5400c000150074841f42c030200071700508082d690390415503403040d4a07064100007070040a4540501846140c81d040082c1160b5400c40580c3e540325000411610030000084103002d880c4c2c031804041c440740081d400051400e041045010a43c0310078044089001d03078881d1180184c80040825140440d5201c40001416030b90307aa015014540d54040b0000c0c9080ca041c86102d12000704540e0350b6800c4000512807009aa0740d1800c05900c00717242c01000d40324911b009040b078100000c0e90f00b1036480e4880440d0440c20720842e81901c00c4c903030200e09182d5982e61a4440190f80a101da84801400221003200502041c1071 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 113906420 1250 113905170 113905193
    0x3110303012706120c2402030301060e0414040f020a06111e15190c0c050c0f010210020c0303070311031302040b060c071805131e02010c1e062304 64
    0x842d500060f142d4680b40c501c8801002d200040d982012003810903c82c0702000051302940d00111980402c890003e0301c406902d0307000500c50030050041c0e8010401c0c16480e01e07003101003101e8040b40200760a180c28034041c0002140714400b40d01074060803801095850058095040c012003000c0241076034a1000000907900f28800c102045501408060550003807518440e107001c1c1d1034003138201510030f81d04c40340e0500312200303444942c04200007911014007003540410b9104407900261450703200c040c00200140d02e0403500c140e0124800b4030000716100c850348040302a500411603640c050190112449a1400721302050340c1911760300c4c0c0004842d0005160662180d290500c0250480d030600040c2d0301801d0505800d94480100a18600e6800b400c0000038443c0541c40301e00c0001f0b00000528503101c0d50b144412044000030080c1001c5541c20540e0f010b80d403605c030084d501803c50540f20000d1790900000d607150140840710b0a00b4544070601d00f003060b01443c1c10100b8031034801142541c071345e180e00c1030824 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 113907670 1250 113906420 113906489
    0x1605040e132102010b011805060405061b030c03090112060302011704031224051203220b040b1201090b03031e070606060801030b070503070504060e031e0a0311030301 73
    0x4031150361840da00b192842e24908012060340000400c800e4440000d42200c52602c0c45d02c0204c1040e600502c10fa42d03804049e036042c1c1d0b07002d850490300d8420300b62060036586900181003c10388008142c1c05500300e00040100b08003482030303851304820305446e101d02080d10600d0100034081440480104c0c4500303880608554010300078a080e0b80050510f103483c108441d12030782113002900798640c3c0814070300030080522005003402e4903001c900c45a4000c00c503489005482051702c2c0d20b401034050703139905002101d0fa4800b03084587c1510365903d5a030301c0341483c1c95003c00034440c0e518178008000156484c992148418135400640614a400841c403000d07005c00407003441070302885106005040200f03865100d81000b5003030740e480b14202c65045060140314064024002c1007000317403c004004035603602205444c1202c20380c0c2003520b40c0f141040300003414400316000b4075064100c5503d83e000d00c0f0070002200000e507406500c1345000302d4802400240c03030b48000d0080590740640b503120785052201d905000325550 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 113908920 1250 113907670 113907683
    0x210c041401030603170c0105101a07030c021503180a0201051615060314100b0f01030509030d090b1f0509060910030503040801090b070c020109060e0d06050a051605040e13 75
    0x2d80300d41d51400082e0094035904d040b024041b5540000100134841c40b40c1049074105204d8447e45400d05060480001180c02c1c0e515240120301001054040d4040310a0558000c01840742c0310900141840c094000b02da40915032440103113480c5131481d002c580044c00075010303134405190944100e0741c0c108004401004840c0310b081180c0041005800d07103c2c0001a600c81c00401040e01c0d083c002d118501100b0940100c3c01c02d11707040645607159640290307a507580b0b10a00340420740c0d40d6080c014505500a030140c5090060802410b031040000d00c0142c14481c041c01c8465032002011102d07082b04490450050a4101c1c90b1040071440078a070030701d800b0754407120b80100c1010858803581c03001c0c250303009a4000c11050391030380440c10810401d017040c0796010085103032030300c18610701d03400084c0105890300c9420140f01700c00c40100015111410030402c540d0308944203120508103240d0700e20080004480c56200b4111440d05000d000f407194040300c08650300625034000380c0e03c40e800b100300c044c00300c52411a0788 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 113910170 1250 113908920 113908931
    0x3020405090c030a060b030c011b0b040606150e031b0102070b1e0c0c03060c07020906010f0509030d0c020a0801020301030c09020306130e0d11030c0a03030221010b210c04140103 78
    0x55030782008504c0380d542c80303100c01283d1820854103152400b04600f900380d040c840c80d2624810020742e5420f85a840c0c40e000b5006802c6a221802c04000a021a400903040492840d400700807058202110b5440d0305ca05070200d030107902c2c0b0405a81b0741c990b21041a640140c2201004021104042e0041c24a007825031000d03d0181001c000c0c00d40e00d95026102c180d80c1c40d0010349408449103800c0c0905a842145100784501d8190b503540002d5504a00034903d60503c00480080c02030b00d4454016600300f40381c05001c841d902d800d40300c1d01401c4900042d2049118805c00100032901002c18000e41e1304036540003c04047c851305101c402d6019400013899135130403401441803082c80401c6801180324440310344d40900542c400b0082c0c0201500c003440002c00c0e05500c00c04c14107140b1600000c0030001e454040c540180c84009803141200020091013441c000c1351114000460301c8070700a4000c10110400c4202da594113400104d491601c02c10441c0c1d04101408280410042c4100b0500c01d03c5240703c0502d0001503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 113911420 1250 113910170 113910193
    0x305100b0307022404020607031b0606080307050601050418170c0105010603050105040f1b12090b010311010f030504030219020d0501050901050114010207140607150e06070f080702070302040509 85
    0x3494108031075010050748080090003070428102514940b041e14a41040c2035807a00e50042a0203101c0d11000504022814034017190303410740b161400d0055640940b0a00c903850b52260416580c0d002190152100c3c014480006298582032081c111800740c00c22008140b504503489891049590b440d102e804880c0c10845d81d0a10780303081c400c907406041c082d10002101d5042c003080c481140d0201c0a442c4031186440317100e40801106c0582010003041c10300d00300709540d010350900c074054031320604010510404840044104000103c0841c000307642a42d401d4180c4050030700071070640c1c0d42514043d02580001e1041e11ba4203a03d42d201e01c054600281410307e140d1041e50343c82d821a00308458213030039a5074490041c400454000349000e01c110b001d1004117501e60800c41000d0004004410081c480c01000a80004010350314000d243e6040100c0020844103c5c0b02c0300590f12443e04941400c00101e0b02c500e221501030242d6038480c062021503004090003411039089c00010f02c03010b4208481c601c108001e601 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 113912670 1250 113911420 113911439
    0x20901032f1b10050f0603030a1d030102040302131a09040807030e01050c060f07110120030a0b0a0306020d06050607050303070807020f070816060206070804030f0c080711030625030510 81
    0x108096070a49002031310b803814105a10f40c041c1c01410300ea110790030400440d101c5071f83c4403414200c1454903c9010541c040c030840080d00912860f80700940207040d00848034600c0c5201e9020880d074a803242e00003809800c90204100c1040c0b01210001c02c0c000c1c003409818082841032218414a0350181031451414100d82e0820340b03811401c84a07451000305190412003034035070044c40303010464024802840011801022204107014009201c01c1041d4003000080525810343c04c41e10445a01911030600c8584908200b00a580243e50506840d82461000155410b040003150141d076082030181d070071a00d40703000c106e80060001c0c102000718884c551044180d1a030a1100740000c040f8500202100c0001719216038a1046a0303022400307540080080109094020030700325800b1b641840e2844004140413030907200742c6034460000c2e010010102c0c4090401198a6034011641400c504860455036440c048092003248001c030000920105000466840e020360416508481544620503c1e2074580c0c6190 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 113913920 1250 113912670 113912683
    0x703060e0a03020d0302030c070b0411060a0f0207060203091003090212060c1c02090a1203051201060309020111010c020706050702030c0303030c09120a03020a02060d140406020901032f1b 82
    0x98000760045202001015010041603c2480e11400e0560551a0401d00c40a550040ca14003421219075480050104150a40d501100d0b510042056440d0040e0b0100204038000d80f943c001301500c510070000c250b460000058908800d0b00a01482c0f1103801004101d000c0c01100320220307004040003018000c1c13013106100307092144111002150700e59003c45403030141d03081d003a098000f101e0b20410202240c4c0d00c6400344007007640c007070b0001810540d036070349011516403096100b01d10103507501074004944180e054100c02c6016000342da0380c0ba11100d80041d0182240e111000d40400369010b10010412103000b900600000c40c0000c041d10100300480e00840d00f1035008130340300d45881400081074102468402d51401e00c0c0344009000700403030529554069540c034401d05020344200b002240410560282d40c0207508a18030001c141109801c2c940741c44000ba40080c680302d4086814150f800d0301e071109146505035201c4082181e507051218514103442d45500c004040a030300d60003186030455125081280 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 113915170 1250 113913920 113913941
    0x3030d0f020c070605130501050715060321020f0d0806010905090f04140706080a0203040804260d2d050c060705070c0509070f030c0912050105100501090510050c070306 74
    0x96510420502c082e07091010941051081c490180104c0e2680380c2801441c9054030002c1c240950b8450141c180240c00c5a01e00789083c5620341020000300070060065410700600030401d61131560199829416602c401c5003981644c283e6002d006210b210b54410340c00c5c103400c40010b04000204a80b03032008510702150803107840c1c0d280c10b8000b0a01081103a00d81d0300d0720700c3c40704c0c1d20040e101060802c5030040017100c02418800f0345540110105050041c0c4004a80062180d0301b085120203051030210555281d00021031507050140c0c0d1000700d802d5000d43e9901c1088180300b2017a02032000c42c3c08900c1d0902c00c00307145c180e00f000024000700c51a079004105660041c1444d4607840d443e400c052a14207000701a9030840b9015461001c1400041d64000165890704e0205083c0450807000e1075901300c84c000e00b1580014800064501c4203018006e0652103e4000c0c0c0b615003a0001480d191801552441100d11030b03a1342221090300030550f514820b10242c0680391180c015211490b5681c1c41d90415150180b51 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 113916420 1250 113915170 113915201
    0x10020721050d092604030314031b0714061f06120204031e1205041d0402030c0307060c0b090a020d0201050c120f09040c0201060e0c09040603080a020106080d020f06041103030d 77
    0x8072050110281c0d00d407001d040e584a013520b46054115a0014203044000303018540495005c40031079000302c02d14140200c2c01c03a150b0284c984032141402c01855903180c2580102c564041c1c04045031556021161321600c012125800c80d09240c40d01104860036400c041c0e03a03255981e401e12000c400510300d42d8078100d940014640c1c21224000a0900c401c0c03030480d05880b0414000100020041c43d030040e0301d036901280f01603941c002d05681d18008203050030b41035a1101c0c7d1501032800045a0700f038100c06e0034140720780204001203165640510950390b85800d03580103503100d0300c1c14210308015840f610082c841b1342c00c500251000283d40103000c0420303412940602420b148080ba4004940c10544158070b40c18103203100034405a49042e0000090940107040d00d21340344c00000e02c0c2c0312291241c0c0c2040006581c0801641d035680c00f8120700a0080480303000c4c1581c54016881c0b11a010340c40081c45130302e08500e003070203810583c4860340c0e4180500d41c41c1c140300740c241c0024000307029018254820400c0418900e070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 113917670 1250 113916420 113916443
    0x303090f042901080702010204061d04150b0a030f050103020a03120917030703080f060a14241b15070309030c0203030d090302070909050307020f040b060409020c10020721050d09 78
    0xb00241c20004020988011a0301c140800c0000640c801c92058041c0d4428000202c000c90000200d4050050854001c40409840100003404e02c0c10a00070203004a041d43c08025800101100380180d400a10010303511001008041c0082410b151b6030a112001c00c0c01c0940c40310780d132090360796154a02001d00701000d40010860005040c2c01c44840c0364004101c0e240c00303520b0b15006c0d000034101d044034020f0429855009a4412103078868008411404c1c0400b00c240e4030024020380c1c0d00d0903d41c004001c07003101010600c1c605140d82e50000e505844040c00420141407543c0d5100214000c0000000980c204100403c0174800368a040c0028030b8120310f1312030042070000542c10041c1ca4080d5607030004542c185005050000302d000482601c0c6511360480d404071501c44140000380150094104859107e0700018001510368140da00818800003040d0030394140000e05045c810032801812000307445400301203501883d100c40381e411025409040e0801c54101400c0800c1c0f03008892451808a60700320303054 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 113918920 1250 113917670 113917751
    0x60c0604051b0a060215070908340609060305040816080a09081204061808030f1308070e01090510091a0a0506040501050a05030c0c19031209020303090f04 68
    0x482d080d0080e0030250354004000707203403c00081d80c6111840c250540c204d00030b0b01207880513125100031001054050f044800240c2c4449054000041b2418684005040c040040240101a2100404541d107545035100c0c021318019003600075001c014022078004208110b145c07030500d2101c41000c1c8003402780f22229152524100d0290034005550021070f00b0b64008440080c400000400300d40c21303141c1d1454130f501051816602e88070358801c01c0c3c1241d48a07000c081124969a00070b00050038a00d0300801c51104815994810355440d0040d03401602080c00d0584018000c85d01076411003a0401552181c42c8400350f5241b03492403c0f54403604103d201a1411490503416140c911408809807908491032440d0a00d1322001030442c2c45008108001d2010100000740d01d03016160641e03180528010581e41030301c2450109400c00d1341403420440c042940c0000f1800540158860100c02c03c0c0d015005500d8228094104000c8066024181d580151500603038140c0616507141503d044240c809000b4025a00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 113920170 1250 113918920 113918953
    0x10903080621010204120201082a0903070f031b1403190807020406090b0a090b0f09090712060903080a02180f0d1401140f040b06091009020304110a060504080a11060c060405 76
    0x5000c04002b00300d42e200d2030402c0449845800d40c080c17a840c4000d903680c201840403d04000c4c0c5a40054051018a0800030a01c407034203440401c42000c9100805100e9103410000401d040400c0c80c00d41c05900c60110f150400c000504002d947c103020f02e211074185034055001030300761482e68001c03015858a552035140e141c00c00700c4429000d04140304d02400103a04840120b003039015280c0c0424402c5081c54041604010180900c0c009004c040200805807002d9041a5000d04800ba208074005807141b8001003a00782288250b460100e548180d03032002411820030445100c0106420a5000030b5100840d800110540b0140088000c003000102c0c03404c074206450340d00c00c0c80c001c20b810000c590890412000605280d22284d000f941214107084540760740e0940986c1c4403140d00314085480c4004280400e00c00241050003071290100c03541c007081f43d00c5407411642402144502c1c101c0380d102c199140006440c1c44000a16080042d001328105264445024500001550f064405410030854080d41c041e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 113921420 1250 113920170 113920187
    0x804230103110703020a08210c071a0402011b080910120e060f0a050a02070210080402030f120a032004030c080c0109050a090207142d010903080621010204120201 71
    0x2c040c11078204511078034081e413a2004650001c1a1071000990301110444545111680070743e05e000b00512483c0c2000c4444640c8d0090704255818980d44803000c0001c2c42ca292203d03c0b81c1d41c1a56180b4a001c101488031420080d01001200c00c00400d2080e2495070700c800036500326840340e13942c03015441e205001480c800c542c0c1c400507840d03050b0400300420102e141d0b480c40898000102c100300107400ea85149040c0028090104029800000c0c20108802d9560181209004e503000301c00b51180c5040306180300380d0b03e60304041403aa001e541400320514240c0607600030400b000c8103406200b2401a0300700d000d49180c0c000e0700100c3d0480c0b40301d4414402081c08000c030800d02c04003800c1650304541007100145455489101c7c21790016000280d10041010f18020600082402c204540d41e2180c0380d03035181c80d0642c50341d0003d034181034100c00840c0108014000c285555806441d800425100c410a004003405410740008654840300f01000c680002440180000c1900c480009402d02c01391000502100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 113922670 1250 113921420 113921441
    0x18010c09091a091006110c060405060c15040602032205100b01020708030a09150302090105070f02030c04150503011a0a0608071707081803070b010e1b040906080c06030103030215040804230103 84
    0x3445403003000e50a07202c07201290251041112f51079150340d0079002e09481c02100c91103515010108400340700c10001d5940145000c0e219641164042e05420300f04440c80b9014050080c1c2564032002c1c10f080003281c9071740090781221041c819180c0c03a0b0f072603024851843e030281e807681000a08056003088100e03107000280c6117680ca14501540b81005960008205000e00e07900a0b0517149100f40003021940d0800c20003100b6a40030f8030174444142d4004400d2020290361080714020b50824000c03c1a0341c0015801c200183c0c00100040c00303090510310304980c4040d00030a4901802825032095651001103010280300b0101d80e03a9084152810b12519411240c2e05031000d00c0992050180c0000291411207950544081504514480d903555103c454400d104220800c1e800000080115030722420b500514203603a400c9003103505810020003800384a21003448003078016046030300f038210b41e40e0070482441d070007500644802e401c042d22024021400c00440f0903024824001480b5140c141d40c140c02400d5890 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 113923920 1250 113922670 113922673
    0x10506030f030403020112020904050a0603211b05030f0f03242d060a020123060603150d020a0905090c03010608031b0a050706020618010c09091a09100611 68
    0x28400c40301c40c681e403401903000c000e050190740d55212162146c2035040e201c50320002071050041342004174000b001011203000035034290840004903000010589881007442c0041e039136504001500b580b1108000a80e404110b4140c0020882c0d00c00d403a44000251200c0020407841d2039580c03d00ca5a9400036a050000c40301100000c0010712140303550303160301d0f4400600030b074148036035000b415600f01c1c040c589a8000a540500c0208200719159415401200691600c2c0b20b00d500700d170130885491110751011109a94000c00c100000307901d00c06a02480c40100c0005410401a14030a500150501d045034000c024119541c40801900150070010298102d130248c2c020410b41f8100301503c0e8a85c89440441c81e01d80700d40003000050144c080090b0701105070840150b0303c14070f8646030000c2d2217a205071640d9001c40c00840202e030307481d0411320032213484101981300e10090910344100023000e428040640480291210411301c2103485104455210390301c2d02c1001803020f800c0050242080f100080340044a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 113925170 1250 113923920 113923933
    0xf04050604270605090c071a130501060506031b0d0f060b09090703050c0d0c090803030108011401080708213f041e0c0906151202090328020604080c0301050603 70
    0x81c2c0f81c00b07441701c6c1c0242c44000381603550005403d01d00340003908900e9681104e642034007000b140d410448001e0385007d100e10000d01080380d89104028042c041a100107003071400d0308000f800b015640c040207102c4405505c402091424182212500700d606581c17107450012000155043c2c0c0d86880c4080961200300ea050810003403c00c0250140a40280040c480c002aa41d14041a00c14020b0102d10020403403481200c0d66036071030f0001c1d180600740c0c5022861607000701400100e0090400f1440400b5a12081c00a064402001004a41350b900d9918100c1c01201d0030000e868035030b0310904076604002c5401d051041c0480074403540300d0120b40317a1a00b1400f0200c42009010000c0d1321503d00c000c03c0c14041034125803c0845e424119840c50b059407044102c240341c80c50000b5a10040361050a00340c0d1252141b401001c801d96540e41a80f00703007135175503a040c0c0217003e8041c0402041c0d003044030702511a102c0703421601d01c44d41c007059459000b41c0107041e2690014410a2051070b0900a25a0040c015000703040c6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 113926420 1250 113925170 113925179
    0x110703080105040b031213050a06110607050306010309060f0b01180315020706020c060403090e0f0702150907080a06021201090606090608090a0b0403050304060c0e0a03080f040506042706 82
    0x3800c6060164070700c00d82e00c44e496000d80e41e41c1000400149281d00b0113855959044002c5407400c11041d100d414010901242c0001d07019000c0c0c11076966068000c0007a00d51750f6a4603108503940d07800145198145555900c000c40410390b2071084860303960032048002090b0856900140c41c07050303003070100c1682d0361080c0310510024940515400c2d1803100c42c0b00160312260b003031030000040e0295002030055881418100300a0640c04031a03201210702c044855a010b0b12403811620520300e08072072100c0503a0010704031000403100c041081d980700d10f40b038043d1840c00340c840301c509013003a808000c2924015000b20300ea2001c8560605840e004020003d41005401c1c9084c0f0061305004d5548207200c28000000001210508180021602c00c0d80c8200f419840c4d20385490084c1182d0400d850949460b4078191046a185002d207100390b22031390f001001621810729503920008035502402c03100e1030682c0240000100d64444030040e02c00b40800f20207001c131001d0518085040c0c280d6101d2010101c6007000e00400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 113927670 1250 113926420 113926427
    0x1090b010303030f05060913060203090c19090e03030c1207170a020a0206060406211b0b07110123090d0c0608041a060612060415081c110706030504051903050d110703 73
    0x4180368800800f603200d40d5460102410100c02c415450382100c40040000000b81410303801a053f90701111003008450080840c20303980e4082280c100c124400200200001c51a010f10100c1c0e002045280c40381e00c0341954402400050b1003503401220950300030414801681e014003415078094015101040305a04d400c44800000c007660190041d220362030344000d03003030100300b001415050350a000b0440d5501e03503480009031070758080142175030101b000001c12000e030f41c410158068007407028460079000e25000703003020495030f02407460f040e4410400354403200090003404070301c0d00429980d102c10a103403500b41410b0784c0f010410306106100301428400c00c0581d6a0301e030b040d0b9001f180503001d00c220075500c400101c0c0052040c2e160f1103008810040d80040c0d01c8400240c500d0410401c96004040450010380c1a16510b6086512404980010106000940c440e41c4150740c4240150f04640900762500d050070105a1b0035082500028000240042c510551b0b00542071807203030882590346020101d49004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 113928920 1250 113927670 113927701
    0x410c06090901030b060a0306092105120a020a0224090f031c020a0314041223031306150f081203060d03030b0a05041a1002030309030703080901090b010303030f050609 73
    0x30818881310002c15070948500940002070759100c04204000c0a150900a012401c40741425580c054074903405080a442501510410030000044030940d403940c4202c43e0103500700140b1001184580102c100d082c02104070074a9162219400003042402d007151881d04288010140c0f01e001d5204100710351000081d03008040803a2150703100141c81d00202e210880103030030807081458400074400140010302c100c81c0480d840e08022610350700b8000c1440000c1d071100d600d01c20b0b40811a0380d0b080c40000c0010900b9643c021050384118000509640360640081541d009500080d2202c0c0039100140042c04007004614040201e03500b1a1341540307014800100c825409035001010140c441081e000c2548814035110017410b401001882160070000080b00c0041c91040c0c018070034402620000840c030f0011003124041d0034584051440e095468400b5624900080c08481e000d41d61823081c00d001c5510340d0881c0d4042c41c8241d070082904445060805e09451000c1c200300d00c11541402808541c42402160 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 113930170 1250 113928920 113928923
    0xa02060109090201020a0204050c0909070e010e0105071a130b070903020d11033904050106020703080c100203040b160906080a150905101e05010507410c0609090103 72
    0x2207142509440102c0c2400c06c5030600a401c503060200b0300100c2c00762907019140d6403005840380212569182011940071828039582c40c040390103003c0c034001035480f410040008600640500180c2816035148400c2d140044420b8000c89002076a9072040013085001a5001070482c600303510102c3c191303000180c030070819501c01801e41c4002c2061401588091040e0b14481e0802da0b03102007400c51b0218032144d1401000c070403400002000d859800c203440e00744150307070603611994010100719055640e40c09031603001c1c003880091486003100a0054040900045105038410607841c5401c0c00e1900108059425805004081c044a844140071032a8400e90003503000d40800d0001c207820f42c0d20020810718458941000c0034041c104030404c602402c620300ca40049541c40c2d01121416182d01552021500040c09507a000076001c20004012515100070085803819032144000c3d81280c4141e4101800c040e0b00d08034100a040c15160000c0d14014400b000120300d0968111389465042d05c001102d84a05000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 113931420 1250 113930170 113930189
    0xf051014070c0201020a020301060f06090e0c0d02070201090b030403020c0405010b0a020a0308070507020306130515010b091e0301050415150305120a020a020307060207030605010f0605070201210f020403060c050a020601 96
    0x1000003e5a200300031000410750040d000b0444591649a09440c041d0213014400c0818820b5800142524001034158407440ca0400c001d4103111181c944180a5400f0301003d0307041140c60007020441c2110fa000650107284660010b0003845148018071007581c0d016031001c10422018480c40381016008181d0110a65052400e681a5540d0310401d0304d941c0038003003000c2d41510440d81000310602001c3e1600c05458003400072118140d0180c182046180024002c4249a80c018072107505941402c614144a10240100e42058109070307402103400c4440844040d610003180703040c0000d0301c8001d8841c1440c10120101e20594050858482a95500502031030341d42c08000051641e0000340b0034040d0b0001903a004040d50b007000d5590358001c2d9103114a010645610b8a86000050141c01d0168101c0807a1010b0300d039581031410980064030401141600180982e200b805e960302da9092501ca00712600041010050f201c81c21800c1c81c0c81240d14036a2000140401088000442500060018110340c6141d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 113932670 1250 113931420 113931437
    0xa170c010f12020c0309041a03190204090b0f1602010501210c05040204150e031f0914030f0d0501050a06051b030c01020d050f06010207060f1107080a0f05101407 71
    0x704a650b0b5051820b8104840d1010404004c00c1801000420703443c2c1c1c0031141440f00005a5001008410404030103d40c10340c40045200441d04103a80c1c407441481c0020b10002d0f40d10b01c5611041e000441c1216825030440800c0104490303c640c40100d8240301140d4402000340f90b0401111016000c50603208181103022021130708100908855408007030f09015000750345a0340d0741c072000141502030a103400003290080018442c03506000a884001c0c0501320002260700c0f40107500040244106001a21032211022001c0344904003000140b40311440c059440b80c0d207200c8015808100c401c1a040144103144c1c841c0200b0019601c5025542480b40300400707407402c0c9a20312202841c1d4400e060751072800c0e500205001000c5540c55015034840d14002c130300c1090550300c507401280c82d03003418002c4c0c0010911f00d64104c80d030309200740701c0d0f4410300d1801d400f210b00c51500d440340b00b882e150b03490740c0c2240c5141204c628901040802d001442110340c1c59001808005d075086548020f540c001001b46080000700c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 113933920 1250 113932670 113932697
    0x91a010b1b10090302032104030804020409030e040e03030106031a09071b0f080403020f04020a08072f0a1b080c1003020f0c060405190308160507020907020304050a170c01 75
    0xa01c501c0b00c00001c0b0100c100041c05041c54081d44076044149050281108100e040d042c13a024800518410340d45a039990105680e1075007080000c10b0030742c10940411080e602e45c0c541d02d44540c4680f414180064000707544070742c904580107060759818400f59501408400e8240c4007512281c15054109501e410003040c0b42021600036031107a41d41c22009480341c089108220b00740b0010724003c0007628000e80c1c103006072110690a01050f40b080c2160034000030140c0c1c0004040c684a4010600c01003020000076140c440d01300c0030f02c0000c030442100300c082900300340d0441040000e40346100c24007001d800c80d041002c0745408803968588005000f01401801c0c0c0148042446201f0b60403a00041c40c2e020b039503074403480038004141da504412175003240c6501c00d110b0f05c1c14032340f6071309401075050a52541c0e508603250303550344c0b0341c0c1d05070b03291168034405004040c000c01005903108000c1e64411980c2d40c2c015502c86203004104190407801d1b501c10401d0308061248440d02110101c0c8480c03c0c0d880c01c0c2000e09000e1300c107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 113935170 1250 113933920 113933923
    0x60601090806191e06081522020609030d0201140a0b100810050a090b040507021911030c03010c0c05060c0304020a0312020c0301020a0201021e0c1f0f020d091a010b1b 73
    0x450340e000e61504110380c0241e6030032aa01c85e105440820044564010301c80020412241050307a04041c240302c82240703601400d1000c0440e260303951015000b07034141480c5102207071030031021129140151351113116071000c00c0340c00b0f808968401071010741070010085090210310451000c0c1030f4041040003a070300045140d0000f1140400412018180301c4003141d440803060010012544601c1c0300381e090001003a132041c8000f030b404a80061000c0603030a41c2c0d4040d509d05280207814903c541d098021004410b00540e4284030f03031100c0c42c0c059160051128105c0c80c1403810080c00400d0704101e00300620504c00503840310310b20700b429680e0010242c5400c01407144140c0c5020032840c0c0c003561540c00003c0f100d580543c19000340c030500a00030b400307840148a1021151321030084d00c0c81c42c1c94943c00091281c0380ca1000018000c0205003911000a491020411480c160780c41060411102510340084c03400708403807113140d50000c100c00603414115504100c042c2d0070510401041080c1c42880c100300c2100c0d04030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 113936420 1250 113935170 113935181
    0x9060c010b090708090f0105010e01060f0207090903080417030c0d02210903040f060e03150c07060501030803040c060c0203100c02070806011d07050c070504023906060109080619 78
    0x100700709403610300260f000b4031101044580224500a030507405040c00014012581a240d240c112003c80d270382417440c104c0d1490841c865240861058410000c0c59010900c5181200c82c0a0b90710112149003605010101140b144110211101c0c1007080009514100060700c044200100002d41d4403282018507038020750510381c3c1c061316032603010180039200c44000024012911611014240303107540e058141c030348940344e901e038a4041c0c00410300e400c400c00c0008456548404104002c5042c0006e540301c43e000c4803802d800403075a0704000018803003400071040400c2d00901c0c0900e00104424016400309032111380c000c1c80404240d80710748211146034000c1c00041c01070075100c01110300c07542e9142d21000003003041034002c880980340c0401280300350b440344c1c0c200c42c188154240207060305460700b4240002580031180414a00c00051001c01d81c0c01c1107144a49075009600040301e411841450b0564240303000640400e05100080c80100546500400d090b94000303414844140c01d070100e020868007802 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 113937670 1250 113936420 113936441
    0x11160506070204091a06040b03011515180314060c0301120605101706060915010507030e061306050307031109100302160f1202060f0705040509060409020307120b0c04050609060c01 79
    0x341d071000030b17809101d42c071955841074104450502c42004040103141c200c07200e80021001645220340140311003032034800c0c079421500d86881c140b040316403480d54a00d02103900d034004941d000e203a0390ba01d0b50040702c100001c0341c2001491040b140345514100f00703291048402c00d0300400c001e40319030001b905400104070039001004280d1031091f0b0304400c80344481d02c1d200c1c226a4144180900c1c0041141201400a603011060060312a9480c00103a42c07019243c2480c201c400c1c0754050000c200d000d01c540000c00760500205501e441e001e80b03a00380984081d09503065584a030b040b44806001504059440826440c0d000c6494100181d0301d03c00309000010110080300042c00300c1581c403888030704104420890078000040ea9080e6140e5489a01510801e680b080d81c0e45e100041062009006a19140c15201e070000c8004000140c400216070110f41817074180d6104c118080700d030101100c244a40011801d03801040d00003518645420700c00040c0050054007400d074020340f000300f008906030b0002d601051a02 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 113938920 1250 113937670 113937683
    0x140105070504090501090615080907081603050c03060411040e0102120405210a0c0b060f0a0305071502010b03060a020a0c050307060b010e010509010903020906150c0303071116050607020409 83
    0x40c504250064079a90052140450310f0749058000101e00f8403070720428094400e605d019140e0070f0b103013003800c58208202030412051781c01070303c1001a00420802404c80400071600c004002c0d5071440c2080303400c040c07038800254020b4100d0810003000505401c0403803a240c600b11000520300301118895030080c01183c05108031491048148000d00600040310059440a00d4141c200665003014103400d9026419a403404140c1c1007071420300042e951100300d45c0c040001b070241c036910b454042c0020040c038415402601c2c5500140c03c01e000d5a0700c000d61640c40304100d400288074000c1d94501107691141e0081c142041c2d00c0d404514484070500c07030084500120b4029007101d886001c0c900300300c0014200c00c6130320ba02140090740070707080c01e50144050328216101615410032543c5140c0038060a042e0080c00c641e48102000e8041050b01c04100182441c285410300451326031030051000390404146a600e01e21a40c01650281c03800000c82040b402901c00030703100540c0f68440752020401402074204d004042 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 113940170 1250 113938920 113938931
    0x11e050912030c0909011203170c1204060b031903021c020109050d020d0e0f030312150604030f02030708070b04060c030e0405010e0403080105040605010e06070f0b09030409050109020a1b1401 84
    0xa11030b0f01e20242090320310403261141d03240d07a2100c41641c401d5034401d000300820751003100a4618400d07211200e6104004c00b00c2c407440c04607858414041b914085a04490090707490764002c41c103040400094002c052041b004410640c50f68030080d41d03030098a11003058000354400d060042c28400c5d04800b82e09a40034088800c64002c400c0065102d0f08541e4481d40001c2c1300c640054038500c3c1540501c00c520402801039444c112024486090390300000301030032448100e00350b44500607228007006000075405000706047d120300c648100b41c20802190b0001149500c800c01c00d0000e0b4004000300c03003c4840d6410020031700c0c03000346026210001203070604c42d40540b8001c000165000c0304140039208900c02c4c1c1c2e80c6d12050303882d40c04100440d0058000d00340000c45a41d0140c45604084c4000c0c0b41340ca0043d01284401241907903204e002181c01c03a051030366030700b0108003040364940500456025007600c1a0940c02e00c142444002d01840d140e6048015644002001a09002c110940b96114041d1a80240716 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 113941420 1250 113940170 113940181
    0x111030c0a030c091d0403020a15090203070e0f070f121a0f010c030e010311090909011d0304030b06010503040602120a060f060306080304060e030f07031208010602011e05091203 78
    0x160360010160301d03020a00340320801451900c201d0880c0166411340e078600801a1014810b143d55050042080b410740c801c03100a03030b01040d1004e5601d24a40d800c100301040039800b520602d820450940e01c10308030134030511700b8042000c40d000e14060b4814141d1030080c0e080407101404070340c440303884500b82c180c003031070200141e900c550402900d8481f03e206a45c80c49000c1d284000440d034040c442480503001a484400c42d0010b50304c207802c41b00ba0001d08201c9503040007988030014018032001d407031190041e03541c1c140511510114102000d960302c3c3c6035010718181491034452070f80d040c8008000b103040200000c00901000441d6040e9180c004c5114410005131408818202c024045402041280303151054001440e501c04d005060a07210b90302c001c1d500702403030208240ca841c458010712070351502415041041c00d100c10468800114061220b00c450240c0c0c0350800313000c411040c0c00010469050503c070031a10380340405116003040404000040c0b5a54104400342440b5064000e00280e0000105010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 113942670 1250 113941420 113941441
    0x1302131d0402100c0b150d020301020f04140105030c03070c170d06030510020c10020903120d020d15060c11030106210605010b0a0207150309060f2306150c011103 71
    0x14840c520a03620803d110301200c1e000e83d03200601d400c1c000c107403400c0b0034001035900d5454615000700358800740404a685500ea0b0019003a42c20004941d0b401c0324002c1001c008000750344410702031211003804c0c5180342d030414403180b00d0a880014001018090207030144006c2004149035a4882d9039800c4080f0740380c41c441e41d45040a489030744402d54141c85601c0382000007140d07501c01c540e81e5440a03002440394100020b4120040c0d00410081581802814164030031030390a076000385550801e55070010707522411140b40700100c1d000f0400d0314402019825041c4080b075000504660080c0d0001c401c07012111802c00080c0c09000b55400c2512000740c00c88006213504003440702c0c0d50310300d0700c601c00a0040c5d80c0c03540c025000d68065050007a0050340f00003000c200003200010400b101e280d070f43c58041041d48007034032030000b44c1c0e60504d0180d902d242d403448440140501504504c1c645c000880d5065514100a0005400d1581c20030480c10040030004170317807042c1400bd5100003140c0ba5248170040d1280740200140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 113943920 1250 113942670 113942729
    0x207061413030f0c06021b0d0503191e03090804030818130c0314090705060307030f0c0507052e0209040605100203091c051911220b0906130213 63
    0x312201e014140d13000c20000d0000c1022846803219480c1c40301c60104100070000729041c125030035101c5010802880c0141500ca034038020040d20b040e160428101d58030318019085402c2e250b040c40815141c0070242c40000c2a040c111012a904501c0f40b644424000c452400c40c900c5e41045198801a02030401c619851250005980803072036403030030082d6054185203942503d4007290701040e550002e00303003405a440c00002030358002050f445d0006140d03c58582417011035021441c11004504046030348020803204000940402c111014583e299600d122100c90514103445a100000b54006c24104c043c4d89555000740000d0100800212100710110700c0a501c0b0361020080500414128480c030040d91000b48500040f96884801810b60b01d9800602c10410621801c0807100c40c0c1c01003110301503581e00e40c0e0011b2142d0ba8028130441541e00707001c02c1c50341100d000f001c21601078140c5ca8100321441e940d515295140c2d20b0403e4002d1b9850000710201408031076035410007500005c803903010322010b01c1e141185 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 113945170 1250 113943920 113943923
    0xc0e040b06070c0603200c011b052b02091e01090807060507020108040804121a0117070b0901090e01030b0603060a1a01030e120d1407030603030207061413030f 70
    0x2005003503540410300c0075078800c0c2100a400c07404401010031105100e90300c502c94008203103860111046e8048409460b41d8001c4d40d45100c240c0d101c940040b40844050500580c031035007410315514244142200045c0e000c00c4450303038404d0a10709200000000400d4040b0350040000902c00301036080b22080800d043d03e881c0c195240040d201e00c0c0c0100e802a0700040e44419941540c4940382407040da0b42c0112502d0310002e1080324010020301000501c01c0070301c042c0340c0400f4031807540314900d070340c1113001c2201007035050303000214400300c0c1d10703402c0c941100104a800a0f980c2c940c0b0425580c0456900603554040c02d030740000031991100c0000014171031102255402040c04900766013142e02c0700c2c410041030703d80305603d01340000781c0b140d10084658080ea0002c0410030003501550710a031800031740000c00360041e4514100594039485101e81c00010f4401065002e0700394141008942d00b140c400035604c040c20b000741c1c4180503082035207260600402d0107481a0301c0b4148022185e40d5200e01d0201c0b12500720910 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 113946420 1250 113945170 113945179
    0x5030316020307080d02030402011b0501020912030a0c030c0606080303090604050709090b0711120a050a08130f0b04110409080c0c0306010608150616030314010605090102030406050a050c010c0e 85
    0x10300d40e8038500c084219403006030050348090034060020b0101c4000d52010303208905220a140c2c483c191007400003000440c69025000040c2c98116150a12211190003020403846401c01c000c0c000c17026030000b03540c05160b6054a0082c0b0840d11600e4008020501500009100d00c004020072200708400230320f00348514410416141070540d114110000d8410801005190130807480010350342e140700ea9990f044049000301101c003c10829040440a0307400388415200049001554020031508104519003041260311081c91505850b161891201000700000701107481030707130104040c0b004880d201d400940000308100721484003440d180d000b41c0d10483c030080d0070340141e5400032428600440c880d17040343d4840d10b90700d50315a80c50402c2c41407214083e0300c0643c400003e00ca0400000a04400610624420388000441c2995140e413844480d034142c2c8370a042200411400c03c860368044185ca08071441410050746809422200380c41034010200da4217000c0d840d00c022030350680d41c8444900d100000548 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 113947670 1250 113946420 113946451
    0x1503010f060f02030f1c02070c03060204050f0d020f040207050a05010606120c0f020a030315030605011403060c031e040f0b040501050a110f09060306060f030406091e032c0d050303 79
    0x1441680c903409079482c11710540000744100758170803005016200101d071201c440149401400d50b101c2c141d0017000d030020b0342e003d0b40c0401d040c001da0070100d0492030151030407101c07070f01180b5550b4000303002c107895000b100d070055070042010340030002d0801c444a50181c0c000020f000140e20307520018441e400700c4078080080d5042440f4074100301c0c0290b881d5031400c01913034040c0050130010346054015204040302400c5411200500101041c05449590302a011058003005081d00c0c3d030b0109407618001424044c00d00e0300c20028840c0d160480458410189440210080240c2d40c9050082c02e0081c101d0016168143c80000c200800c0410f41c4858803540313208904010011a4100c01c0441d03000300c400340840c00d08200029103d900d0104003550707011000810f17007840c0c100c16146c1e034001030b00140ca04803196922141464200000a13207000c041c0781d041801000c0c3c1c51904d8400610001c3d0620041c0440400c1c1e40a0600ba1039900803c502d80c0c0c04c014054490b00100342c60a59aa079004842242d543d05540 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 113948920 1250 113947670 113947697
    0xf06080f010e0606040509150c04081002030105040f0203060d030e0609060c030c010c1d0607080c0a0f03080604020a0905040b03100213050f09040506070822080703020c010921021503010f06 83
    0x92180d58007424041c4028144580c19140240803123001419164a1000a000c002039640042000e880003038a00c0c8400740c0c60307500d45018402036601030050310a90600501c1004050b844010410420a415240c108540c440d0400401e4440c0300b180c030001d030840c100156143c102c8800100901c84058040c0081250407142c3c4000c541103001000048064100f01d010050a1703c2e02a003e48000c9004661052400d000d2510441c5059640e00084901c4000880d0075018503800c410340c1640030500350b506515140520310002d18410042c014240309541d20b00d400421518100b000c41241850b50808560b03c1c0307034000702c92010145602c6654402e89a0103058a402e0900621860045070b00c04010152030f121038038240c4102134020320880215500c0c904400e920b0758514090203055000e004001e03921811810003d052241103e007050503c02c8401c0100a0102c05c2e409040b643c000c5c0380007410100445100048010000320f00c600030320f4a0200c0040742d00c007094034070801110b10701c0d00c8100142004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 113950170 1250 113948920 113948929
    0x807110a0609060c03031b080603070b0c03070204020c010906060e0a2f0c0f1501060f02160302040b0d0f120305071715060c03070c0501020105060319060f06080f010e0606 75
    0x80e00407403002a00b080710410000740202a044040b501c42d040c00714140741000c2030044001c045060b00c04c0092030300c60500c0b00906051105901405507516014605240350341c80c6030b40d03031141d504000e0045a00241c4032801e00c2d820352044d090366030700c14000d100721603850003c00c654040650740c1f04411803411000f4800300f103020142d204110030728100310880c1c4040355040310322a000001908124066000e501401000178030150400406110558101e5414011300900b9440e04400c0c05003554441d03841820702c00c000744070000c02c907581120003050001d800c10200d40011088140248260b120343c0000f41040284101e012055056a4042000c0d982d242d0046072101c160741d1101c0020002a00032881c3e14030100b0b030321911550043c0c0501d1804004040c0c0d036246a06c03200080c0c41c503410030700007844213603428014a50409400c0700244441d00c1c0340b41c4800c0c8408a4440000e1200c2d580d40d106d005048441c2e005040108a0030054651050f03060503128048c100d00590501e0601844000990a240 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 113951420 1250 113950170 113950189
    0x180501090f0e070b0d0b060c03070c140105033d051002010507080c03060307030228052d03010e0106060908010f060b0304151b0f1b211209080711 64
    0x82d030003466014649154440298000101001142d03240c866002d0740c1e0301c500b00107140060003600210f684640d18100400c1010303207034011604a00c1600d140c45401da0340130054a03048180c01c60102c5d149001200000e04040f20341130449a6100d008000001ca403078410800c0b805c82d1001e948514014200010480c00c8440449031103003c034644c1000b040c00c03803100380040c40d804500a002c030341d101600d0ba00003d0319100009075040e22042c100940e408510981c1503084001c100540304100c5900865240d07806801405411480200484000d8081640e094110b0b00040c003940e0000c00c4411f80b0303000010038858043c05800d12560070300215840310b000390b224800c02c80b0000d000040c11a00c1e42d41d51103520780ea01d034800c5d0320f805480344179031410441103a9a9849840e540c0e00c5100700348140300005040019201c411a02d20b080140c1d0170400300300188202c0d8032101012110008240d0040c10030b603842c40034400c0c01c1403054903084801c410000000010512076020f020905940c54045080295002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 113952670 1250 113951420 113951441
    0x30203060f060907110c130b0f0d02011202070c050901060c0302160302010c02010509041401090209030d0216030f1a0703060e0901020901090501030c111002091203070b01031b180501090f 82
    0x1403060f0009001c58415484403c01d190b0301c82c166440aa69072000031103507a0101405003016680e61741480240c40c0032044040c01c030704240e03007021428504c1d1b00040c1491406039184152250005041810011505580009414002c1101129507101d00004280e400071404c11000362080c42c14030101d8607452118802140c0d4140e450b129010503070307401150550000c9401a8100b0349440380c2c0400c030102a15a41d000c3c20700340700c005845006400800d450601c44000080c1550403068002c401c0c1900c6405e041e054075004006560a0001d6181c50504514140e0000d1000e100d081c0a2004160b03060b0000c000b200d18058504c412910760038199402c1707115200802c2d0102b4512032081141d0f501a82040c40b1a801c40e042a400b81d242c000c2c0214140354000d481d100d02c0640c00600c280807803804408a041d0f0100190080d0304203840c40d07503888441ca41c10f0201078034484421018100e00f008800c441d402030683c1c000391504e503071102c2c10ba1501404080c01080100703401c1100314900c01206100d03800c042c0e03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 113953920 1250 113952670 113952679
    0x6040b040506130b0a0c1707020f01180b0a0203090a02030313050102010605090105030a11061e042c0403142a0c0405100612020904050f011a072001030f060609030203060f06 76
    0x5840345c030320450040c00b0340344036001880061190b80521001c13034070300540704036200c0d0060180154202450740c00c403400c001e1503002c21a1019454000b02e02e0450015a011050f400016030ba07856209540c1d151141c4c0840003036051000103040004200100f4501c422148207070000c0c440c9a4079181006a80c05090084542542c803840d03860b0040340025000c0000c402014200354504880b0020707400c0598884070011011820018003000b0000025020881d40221407240c081d203032031500504107000d00302500160030000c4010030307950900f0000c4102c0d103592160300f85070019402404d40000300390b185440740719168002c01a1050303440c20319004d424451115038102d6071000c1e041c0207040e41c0030000c2c0f00c4200c038550b5003448014000c0c0c641c0c1c400c140c0a0800c07516903030030f103614040c0f4081e0401c000c40c8850030481e10510081000512000d40503200020005031000e68131000d40c0101c000b07110b4240c20100c10b90074a00e002403041d801240300d1040e41e000f070301511030319901c1d80100c0e07031101020350726103801 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 113955170 1250 113953920 113953943
    0xf0801140c07030c1109130302150702070b0c03040f230f0a0618030804090506030d020c010504090504020103020c070605342a09050a061706040803060d0506040b04050613 75
    0x81c800c00d1001c4840c0d1084100851284185e0085000200211001c054070140c407070240c0e06060301040a80e07e1800f402024209614010034001d40f501158402c4504507180850b10b205074031018402c1da400780501e58114030a05580d41188138490284000714040105101c40604150912120150803007201501c207100d20b0303252000403901181c4008002444100e54840400082c0c00c0d4002003000f080c41846c040b5241c24030204040c100b50203820000d0a65001c0d80e031504940c0d1700702c0c007954112070707030645c00240c2c0782c0c0e0f04d00058000c0c1c42405e50b1001c440c01507010108000ba0424040e1181c00341c45600020b82c0710b1004c440603c0a2032401070401703032400b0b0048450016a80020081200c0d02410344400c00111205204c989001150001c002c003070303218000c200c0d185040748a20340013010210380c200303503540c003c2c01110380300c8030302800c090001080000014030f40d8a03203031500209240c0c404100c1d050380c540790514071607035270064408a0b41e6001d1600403a49099540d0158102203030001008100b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 113956420 1250 113955170 113955173
    0x513051207030203010f020d0606022b0306030f260c030301090b0f0303030a0b01180303050a0c03110d080609090607080f040516082116020111070504060f0801140c07 73
    0x811511034004440c9072103a01000700050b1000e010b0000c02c4500410b001d40c0700c08800486c5015101c19410401c2150b00080003900b03208014401c4020a4201c40c03005000208014411000350106400180c004525035081e10200f20343d00146400c4c900b443c4003c00341440d103007030f01d00005101b8403403048182d6209100602c940701c1c00380d110450103200242504410301c690f1020a007950021140300e601a541c0300c50803e0b40c0d503000b0b081c9a8000000c0d084100d03845046990240850188103141e0702000345c140300300010180120659614031040504a801ca0b0380b910200504a403030840f60b542c01a0801d401040480e400012418040c107295100c0c40e602e66203000071010050001801911103101c0d00b1030142000d115844000c000e8500003000c0c0600500b103d1500031541090715081c8046242000648000804001084107056091070581301200400440a2400041d81c22040e405032074444001100014a4030341811a1300f03140007400314003d03c4c04201c0e80c4480c22112215840404c011220 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 113957670 1250 113956420 113956429
    0xa0509030f0c07050a032609010903061e020d02090a08070605040e1012030e0f0a06021b1305091f11071e1a0a06121109040302031b0d03060501051305 66
    0x1e281c1940a0443c0c01e00caa840700040c14070141076005031501c40220542035415004d10a640f14910312000740140342004c003500090250080d0700c005000c0031b90b9034030701c2060114100c00c20b000c90b9000d804203548500daa031240304001c1d800094050f01c61a80240c1c000707080c903030120b4003008803402c4d600c0322400c0510b0140340745600c0c07000410030100b000c055031011420903004203c1c801414026036442c040e0139003000034020101d0b540441d10740b08a0400c40204000c40e400242d12402c0c20845008424105c421408992a042041d003090b1403035040c602040080d40002031a9540e80d400c04482d8480358040804150865500c2c103002d10030500c0070400c0f00003140b03e9010055a40c00e074058080005005500c80c1001d404168268520b9110b4150611201e81d9043c014000a40080f00e08201f801d02d451780c0b040b181a8107420400c0c051608600014180f5009000391061418500c050141080c1d085c03040b01e0711611449031801c0400e2034030f07001050390351181d41512042150404030801c050b01341070410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 113958920 1250 113957670 113957677
    0x1020f061b0f040f0e0103020901050405040c090b03161202090c0301030809061804020c06070806060a08060f0303041505040f0f06021015080d030906050604050402010c08160f080a03050a0509030f 86
    0x2c820b414410840055002041c102c03440090408256402c00c1c1d5066104028008006074817052085040006000200798040035003001c40d4208030380000c0e00b80848003c2801c04144459140c5680340245000607103004a18044001038400c94107084140d6954102c50b45500007808050041c603401d115005582c1401001407210203140c01444a0f03812454000030240d034441a100c41c40358200201f80400a50042d22190700008100d54443c202642418000c0140c04000d140601c5404c03032140c08481074030300b44102c4015229450086540700844007010b0096406071040111204030014002032a8444424801c103030740069000c3e040310829556150050300b460010950b50503840c17080041c1c001d104000b0080e84c4007090310003190031240c45c2815011120018030700c6000300d027030204100c0140ea00010009529501041c3d180e110400080c642c410a84a020700402108543c0e0307910040c000b41201502c4203950b42e6034140440d51b00c01c5d42040580e030b4140c0d11041c80750701c02d1120000e94807820018 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 113960170 1250 113958920 113958937
    0x70f031109041d06070519030504080d060602030c0c0303040e04260c0a021f02031204051204030609060f09021f05090405070c050d0906080c090301020706050f0601020f061b 76
    0xa80d820719051200141c201c50404000005a0b1407151203c9907050080c404640e0007007281c203100b420070082d5004a80800d500c0b404007820540e17200300080401502c03c0580d1100c02c1034240802045480f818081d650b03501515003504c80d0300c44c009001e08246400800c0360b0690f80d880d03a5082583d1110b07030310501d1406141c0c24100140c004003000454041400018140001015004003d031174480d0061002d05502d5110201d07100d0980724400c1d51058001040b501c0ca6280381d511100741c0c0d5250b003020740c05d080048400d01c000d0740000900000340031782a00203848540c040c1070200000e075404400d6200325244480029004150080d40c0740b90805500c04800e020701d03041c1880761410560b600044e044a0382241c00344042807036001c0c68010f00c00200040d03031500c0202d0501810031418250701410100e401000e4007041c40340010f288010380c4003034060b034480542c003010500c55810325030700140341c1e900c044500034014490342000000d030620010b1035034024107008004080c032508202c80b0440c9644044034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 113961420 1250 113960170 113960201
    0x1e030a0803074503050304060c0f0503040306091509020f28030b01030303141009090c0503060403090905070e0105030c07110306040b0403090909110f0406211109070f03 74
    0x40318a068001420350380c500c481034040128201c0d036610f10080005081d810340900190700800c140002000001201e0564046040c80350312117100d85040048060348500043ca103000200e030003c02c001f044d400450308103101c8d400008044940400309400c0754420000a94001b07001c600811050800c01109084280d00004c60001c281101d9140c42d807690565004640c41c010b484010030500d54141302c0c90304400300c0400c101c007041c1801c40601015055600a43c05107031b6403a030701001000070892160b4000c4c0400b5007a40e00d94602401c1c040e28048451040048150902d00000c0141d84609440207629034140c40d19810758440f6440e03440340390000c041c201d0700200e82c481c010080350750800c2414400e5102d1102d688440c5001c1c41c0040485500c2d92107414040d080c0361140000034640c9054030401f60781a0b8804000803001400140038110342d5000c1a03941001c840741002d04105004803943c00c3c0d0103030600d0940507241c9018040f041d0740031124400000c02018200100c42d01c644c0058055018400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 113962670 1250 113961420 113961437
    0xc09070302090a0e01031b12140106030c1e05010f050d02030907030204110d0b01030b010c0f05070509100801060b070b0f071101050c071208010e0a020904090c060203091e030a080307 80
    0xca101d142c41e5030065004044c0c444010010410480102c6d43c0020310561070034000c52a096090240e410040d0f00100410b20342e001c02d1380c0d244001d50145005507007040c074000c980380d41d91307000500c1c05071b24520a103500502c194010425502942020503010340c166101440c1c141c03000e0220000b500050600000c0b07004041000001d80d50b180103000d14281400d12550b5101241c0e030b5400c0898900001e080d040c503040941c03a107940d0307802c426090700d42038000302c55520102c018908103013010600c1d0406a0700c031401d01c06210031000c0c440c50708029610040c000f048138036183c0c16405024014614003c01c000c2080f00081d03d482ca0b41d90a60f600310f903550610103959520b0010705400e6840c01c0700d08580c00c00002c155181409503800e8144400b00d41400c0c030324260b50501856124020008001c485040d800260b0f07a10075803a141d02000c0825004280003180a480e01c000a442e80e02c284261442507002c020728050307441e4a001080034101000b40103100380c141070b603606a07090700018812400e100480 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 113963920 1250 113962670 113962687
    0x5060c03091201150e0106050304060c021c2601051003090305120c130e060306040b070e090a0c08071b06050c090612040c080a050705190b0d050105030607050702030c09070302 77
    0x40700810355882d00d400042030201196000c0459000707aa44a15040715008004028240e04002225041604254046450015070506a1401040310100504034001010406d0b41d240c3c07000c11080d14525a11042c0e001c9583c0a40006504c2001c0c0100e95100c45101041c0803494025804124868440c1c1420f504111a8001e0038007200380442e800002d0007000558518240e4090b403280c00a130074040810040303800c01e0f00c007183c0d071008003c0004103c91005404600404d01410100b10045001000d0120707903e440070540c8054101c4044c80c0c0e021a21100200d0201030060164000c0100c000701e40010000c0b05480d8000030b40030140c4100ca40e80b208104040c060745481005000c02c414108100010b41424503260710840308a500055840c0c1203548403a000550215100781101c20031200d01004007000c584041c6014103540c080c00c508140003424504c012907941200c0d040355400c0301039402d141d845a200780c41c46d01c200c0034003d5054100045106075842c00102d0b481d04586a4a401401e14942 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 113965170 1250 113963920 113963929
    0x190b1302180a061a0301030b040201110c030d110609010e0a08030703060909050f101109041a030a0b0108070b091005030a0605030d021f1404030c080f131514030105060c0309 76
    0xc2d94039640c1282c8800f03003481052460824202c880c0e1125031181d18542c5940c460300f50039100604001d0405c4803e03031400e44c020700304220707207101ca00c40217080d5680702c6646040501030f081c004802442c54043c660010300c080e41c06200301c5c0d4542605202514949c0200e03134440102c0d900007004001450307620000811903007418412075080b9803103640244944010030b0066490881d0324440303a810b85d820040c0304008a4501426200045400e0b14017103612544030744945032206c081084940c06104000b11403045c0b0140e000814100c40154050724002c0703480321085c1c0e0301d501c1900b52140d008880402c59a21240c17144008650200046034000341103078448000905100050b0000c02c0182e11007840100c2e007402102c07903016002c03e003000802c80980c25007410130039000010000350600600c3c010100c144249032007210780d12803000100994641c648248500e0140003805002c080c044159200307800390b40640b400d510082c01211103541036a1030b00013007211a0340100c0180341280024420f1180e41e40701d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 113966420 1250 113965170 113965219
    0x110a02012106091e2d021606020a09180b0f01121803050307090f03050d030b0d0c03080304110f0306060909070308070803060316030c15050f07030c0203190b1302 71
    0x407141003140b903144c40004001d00390342042210010389407031810525421000080702140242c440c0c280507817903e03007a4030b10303550505003498081c00d840d00002d880c01c1c12680c0210b4030410343e0540e0801071b0000c091030030204d04803410045116000480140354002e698042c905661640d040d0800210b1034007420500c00354042420f0390110302052010052107209a002080b01c0058580c1d13410310b100071031468550395915240d64088405040ea900310125054680310018203006401c6405038401c56a030f458504083e5200311001d030b6142c460302040316080d15140d000800a020000c00600090701d681e070400011810103850b814540c480d068001000075030944c080d010300c9001c0d00c401516071130020309150030f064004140c044104e281a5040c030000e0107440880f41690b40f0301a58241018a14070159120302c038082d629204d05401050030800c26501019491070140300350241c0d01c414074003412001c5182c00340d9000405407408100054400a034030240c1c010402d000400c4048001c4080d10480241c0c40c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 113967670 1250 113966420 113966441
    0x40504020402160f12030b03070b0d0e030a020a2006090f010302041503090203070501080603120c0325020112060b0a11031603080f06010503100b130f090606110a0201210609 76
    0x540304580f00c1408501c440780483c81481b41400d00c80c0c1654280000d0f25601a8050501502008900c00170000510ba0082071100610000c80790f45152402000e55603002d541c0d006c0ba00710101654001108403869040345010703c0c054029030400040100f00181099000e0125040660138000040d60f000d5203980d4140214480c0c40000e03654185006150412803150442130500110b002440050b88002402c40009092107240342d88807030107500035a04601c641d20500074030307149011465901080440c0c0e2803000394401d03200d0724908000844c22006641607072003401d052002c04e00039400c1e02801040c0b010004016601524a40b441a484400e100c05070440145d002829103030400c4001c1a641010301d0700306000342041c505602e00810392100b0b1080a0140403000c10011890b441c0d410b403e00c0c1d00102401c00c4030704031500c0a86070349100008011510400d40014088001c450704100080741d662103031601079451060f03206a45121160342d400030750345500b40075541c00c1c0000d00a4860700ca41d06045 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 113968920 1250 113967670 113967683
    0x1140310030212010c0509010f1404030303021c05090d030207030c0804090c0908010b0604210b010e150f06030103060506060c070b04230f0108100e10030210050f0904050402040216 79
    0x650540c01070010043d0040311860040c2e140031101c3d00d1081e0060141c8000d010b00b480d110300441803500c4101c459801001b6074141c1d4003000300340802099099000340407160728403c000301c0381040304104442501c4095481c0c40c080c0c1c0243c5070741c81000d4825001403148500071f0510126a90b4542c0e511082903000340d100d080140c3d5281c1d5006003540d80038100d4401403002400901944030f8840005556114501c05c06034000b201c0345141c01d0442060000d507895942140d41d41d1842d6a4070012402840300444401c1035500c0b0b82944100c1c9840c0001d8030250b11007000c0c00c0036040d40e003966120002400301410f0305030301c858103015a0000d54030402440c005000d145002c01e40b9a490459050188032001d10a40810050b440e134007009600c501c146212308117000d1170802c980e501c40c500d022085120940009680240000800545002000074041164400d40d141070b0101c2c1002402c484034002d001c4542d100400403c111142c0780b501c0c2d004150001d0006000614040e4031540003407600c4440981210039 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 113970170 1250 113968920 113968951
    0x31b030c040510140904020d0e030a020705010801150210050a021b0307020a0e010b120402040b030706031401080a05060f07090f0303210b0109031403040e0403020303041b0b030402040b011403 84
    0x30390410210304900003c05007020282c00520b600c004a031400f820f80d4107800703035502050b00803800100b60000b502d000581005c3e265114502c4070000e4032030b080303406100d000c1420765000151308c0d214005041780b02580c0b640034240482090410750040e100c09446070181071380901c2500c0c109010001d4070300c400c803071070002141e8401e500e1041c00340c0066554803800b6845104001000103071010b100319403480030540210403840d0b5984c0300080041503443c01903600b52150000200c2c5050301940841900c0d0707030904000030240ea0b5041c1480e600e90b900d00c0d0003400c540040000c5a04040d04451701504901340c5d08180b1503458a0380d540d5044102e041d030060740082d0009081d151000304000d00d01c04103058403081403180c0c4009800180c042e9280784002080034507034081003d80d811090094501600903681d400b02542000d060080d0f40ea002920142d4019903410384a21a07181ca02c0d1130390701151103544009003103503919002c201c01442e0a0358030905201001400e00f1681c41010015072081d4549440f1264 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 113971420 1250 113970170 113970179
    0x80316020c01030b130c0306091a1305090a02121002031612110301180b1002070314030c07050609040e1e010b090c0d05040807050703050105040b091b0105031b030c04 73
    0x240c81c100d800c40c1410f1620f826000c3c1e07030345d89a004032034424100924001c00c3d0604240411001030400c4d502095525290400c040481800400620704101048511000c03c1c50340c00103d8040381c1c0f09441c403c48540c40a03598000604200765442c4e108100c176016952845100d61103c4160303801107038034100c01100300c10040d181f19084042e40304442c4001c0d400300a0019411b10b2240c0c07610060080c2407201c04d880340010225070058014030f0350400050541d21084134041030196462085000c115098206241a0404440000107940380400b01400409440b80b07404184452a841034140f42d8100e912840754100c00c4804210884c0340b240303200d00c0900c60320080d80c88982103411402c5007611078141e240c1444014152082902c10046208000080c29101c0e894a88442d120b0440003c0c4140101000041840b0041d48800d00c00e0740103e180055a68036107000075221000c1c0211400407400310b05410700154410005107901ca100d01c43c8524408640e00308a02198104445a04d5000c900207410b21 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 113972670 1250 113971420 113971423
    0x50f1c06020d0e1c11030d06080c030c01111f1404030e0a050a0f0e06030c0315011802040302010503071805040e1608010c050712170a0b0a0e01060e01030906060308031602 75
    0x10074104958000c1c2c08000c013101420180a803a480355001000411003031540c03d03000074001c0b610903075550301c01044040c0c0d46000854440b40480805441f0707026078040c9448035409104050411079610380a00500407664070091071100030006e0401c0200d5aa4051f201c0342c51080d03c0c3c483c0218003a884030300d402100342b01008482200d5070005070040400e02010004240c0d000c4282d416110f60034404c2c000d964030040883d1520746020691170f498801c4410604144003c170039940d040e1410581241e40c4200e02a0584050784184c0c84001e0014804000160fa07030303445004161741c008002c452511b591541c2c0c400190980300342d031030380c8955500702c5004840400111305400e070080c4803d10080c0580c0c404200c0140030b138000e5044c081c1540b4150340550203030910600382c800c2c52a10010103c142802c151014400401000c510540078400c112004940c81600791401d44c1210702c60340d81c003180c0f110b40c007004602421821078101e48542d201c080100006000201031407046a10403000005010580f4000b07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 113973920 1250 113972670 113972681
    0x406080907270c030218040e030c01020f0c0d020304060e09040309080d0525230307150203041104050f0106050702060403020a060305060a12030801060c050c03060108010204150216050f1c06020d 85
    0x3c900385481000621100c4590118000c02c0310b40458000070420b40b40e64100b41036100e82005021554400075414841c001c24101501121805400f1141e240240d0001a65240b146000d0000030a00341d0302a50040c1c80c010644270385c0030b4400d28012100030755525115140180e40003d0401191000c45c2001c5083d065168400e2492060030145000b5015625407429500d040161b0300d00705805843c5209411b48100215130540d548004c080e24803001959050000f5002030b0341c2103c0034007000e40359245030705d01b07406160b002d08640004400f940c1d190940a442e00d234400a0102d80200d000c2c80000096030300e501d6500028215501c2c0490300745805c000300b1680007900d0b001070704440c480398001c0020039130061078181581c4880c20070100e01e00882c10910710305440329900d26807510446001295400c1c040d000740c4215019102d4007005d00c1001c03e0180d80b952114520185600007442c001c03c0545026007c82d103050300007605495504040002c00c440b105030300481a10560f03000508091350101902c01d6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 113975170 1250 113973920 113973941
    0xf030306040b01091d090a0b04210c03080601080712050408090a0b040305101d0f0703050f0304060813020402041206090b0105010c02060904050612030703020109060f02030c040608090727 82
    0x151409034180300060044d1000a0405c03060040f04d9800102c2c0010f0800108840e0343d0020101c1043c3d28103860703d500d2044030300302c076260a402c00807003c0d502d05000c0c4035014075503945525454000c0d500c40e0011620200000d14070820014408845001000c580c8140e5008074010074056980300001c1c8107000013081c459001c070040784010170041012403030110340c0c000c01c08414600130400c140d0383f8075004141d00d0140940561030080c64400410410002420400c5a00c14815560080e410b2140c4039200d010300d21030403000c00c1503070b00043c42d07020480c000700001910043c0014117142c0c0b6541180801902c41c0310488103107a445100c001030114404c6110f004200900e49902e822129a0115000d800707072100300360181c0d1f215000704202740e0307400700036040003481d410407240c5510490500078042c2904140030340b541481c01c4800707810040540200d034071440100110520342860308008440c0c2080083c414001401140070200728060307407211a07109012001491803182894180385011181d001a5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 113976420 1250 113975170 113975177
    0x8060c0703020712020f041404150209180a020c030a0917060c071b0314011e050c070f030e060a050405011827060b03040605070912050307080a110f030306040b01 71
    0x4a00282c0c0c00214503040e18561060f1070010a024030108a90340003004c1d60551090070718607041c04140d40c0010640c8107900a0a2080040101d05582d108034440c450100341c2140100141101d6000c40c000c009400c1160080c0040c50180251050350454020000c0180041d50306c4800300304a56100300d01c0884022b00c00040e00543c02e10401081440c4960100103060a800f404035040e5400032a8400c002943c014000c421441640c0071a5030092100740300030b1202e00300c5202c00c2100c503e480d125080c4249011800c0c245040541c0e122000182c041031812802c01c940da29614046445040260201c5001c6485180d01d41c2d0500002400b1903001008030300071540c640504006001507640a00c403540c0e91103000103011040300400d0b00240409030084088a20000107120411149a2001d84101d01c0355881c030643c0c41d1508082a16041480406040303030f07006100c40720225105400800b40000c490900c070b00515042b02c031a9041902c0e1791000042a000030041240700e0900e805400800602447c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 113977670 1250 113976420 113976427
    0x15130303080c030c1803030903070305010c12050609060d0203160b070c06030b03070603021305031e0106051e0427030807020c0609060f071704090917070b060904031808060108060c 79
    0x40e55030380c0b8015003141117210007450b40e1044082d2018000c444e40c1c414041c0564048640305d00344503001c4c05004004000260704c59669103203649281c49103501503100240036500948500c0300700700d1001480401130740d0500030001c035410310080781101c08000340f08000107503032602d58600740301c0048030181e03000342c080c14204074501c052664003059001c103032b41407801c0040e100d182084265030045882c0d0052034061003401d10b0509134003c0342d5106604070700010028410b660f224814007000300d41011041600d8900c0d00e81c81d40180c6044c2e00040080f15032a036460542031840c0c0181c0e188508a403d0030350224010714144801e49134180008208000142c582526040000c0e000c01e41921481d0040102507402055510070000390003e45074045080600098991362141e04610003003c2c4240203c0d85610040000700068821900765802d0782d41080c0000f0b044e0369030009006844000500480030401503241180c440c010424000024040e403100410b05076051065891500c0c0b4050f1041001a1007803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 113978920 1250 113977670 113977681
    0x20d030207050c24040e09100c092702070b061305070e120111070c0e0f070503010512010e0d030603170c0706110a0206070821010812070215130303080c03 68
    0x2d000d0400f20000c0c4d528480140100c0080480004100128403040d8000140020412505100d450040c5000002d075003841c1601c0c140401129416000d02d03011900c8800704010780d0031802d10240c40d0111030351000c0513007032003100090f0490b40082011603010b2800b074140001e82c20100c1c000c8a41d03440c4c0e881c082000d03041c030660140110000d08906889517040d03843c00c040112003074020b20204d48111602903180d01d00e92a098205c0d0365240600c00c07100f101a80010000c180248185005240c1511014656400c000c00d1080740c85c0f11843c0000ba66494030061100802c003044202241d0030142d4001070420304510301070400c140303118404400c0d07041c18427000740e548201044c100200c0d0618204141250120030109040941d2404060350040c00401c0c10002d10030010000d018102d41c0032155482e0f526000d402001ca001c0a0050207000d5001054003400c3c1c03109000140841800201550b000c0c026103030000450b0fa102c035a00d1003a00300c0e5200704204060300000c203183c201466840d000e003142340c42c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 113980170 1250 113978920 113978923
    0x6040b01120305070c170d0306050105090f0402070b0c0d0614030d030c020f1006060806010305100e1e04050a0506010608160f0e03030a0e090901060e04020d1a01080607020d03020705 80
    0x1030040d0075415048900940c1054068000c84400c1c1d580410390655041c0e03151141e404100d84002c6403d841d00401c0102c1185504c01e02c951400c1e40c4050715468200b40c12503090204884800d0300c40d6400a03800c100f41000309500c80300d4035110750181d20a06075074402d528480300603206550300c002c02100b00c1400e440d03826039003c0f4010904007401d2a00041d080f628000483c900501d4903001040da020783c14130f0881300f03401c541105064840c0d1b5164003d943e00d89100441c2101c0084404052205050005003d100302041c0003e400070341c9181442007824a40d4407a80c80703084140c0d0301700c850b0741c4000c0407401041401d018103401401c440c01d1a5845140c40400030300d020003001e0200c000c0200d02d02444002034003520a07030201c603001070304980d01c0d1a02510080c081c4114180154414034140c000140e0f0710b0014084c4030140c544094454409445a40c240100001006421207a01420008281d5242504030b041c038001e021250080002e0305045030040d083c00501070020007058010032018000c02e00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 113981420 1250 113980170 113980193
    0x140102190f020705090a02070501061a0a0f0f020604030f0504050a06170f04020a0b0d0f0507050d061a0f030a110c100510030b0609040203100e01090b0109150e0c090d080a030e0604 79
    0x551b0303e015907203a12901e041ca00500a680101e041c100d03600c500b1744010003400c00036103541b0350380e511000036030303144c4000030341c1d80c620f644c1c104000580c080000240001e01c131b6005141130510701c2c2030040c03c041c1c42e100013400100d4150030030310015144200019503024121100c6411600c080070701c10320cc0c185a000f2590069060146082980c000a81008007840551180e8a42401c1240802040c1400c20340200a980300e07041200c5140d003400400300c1d902880010081c00b0f80780301c4110611340380803c00e1001d40382d00001c00c8401001d40d030f00800540c19081d0b5005100618011010b0040c0109154142e001c450020b01020000e00d14604288009800d610455030059001c941d880080c1d0790306d1000a20b0072101700302c0f4091140c01c00d4400304000b9815004016010f1081c668014180e0321030b503c2d04116882c107110403c610407111400c010145510b00a5038228180728005850100f40c1c01c00f00b030340001e40c040111032868000801c0780049505100b40c400110301e80001c2d0084d814a62601d064805 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 113982670 1250 113981420 113981431
    0x2150c0309030702060a18031103060f010e190902090a0c0f0203040609050405370b0411030402010c0f1407180902090601030f1d0303040605100819140102190f02070509 74
    0x203000100040f0341e501503047c0c0c900c01c81c02207420340c105580700e1400c01c101c1440196054002e1203070360081408400101c200ba0b058840440d218681590b842c03808415103282409001103180da14020500543c9801c0c4250f40304005040700070800030b96614004051160b11108081150010300c0103100065003d824842143d40032200440e003619194070003e10300352000001c18400103100300c40f40b034216580704071484100c00903808010320202f600501003a00c003182d9582103008000c10000b401980a80109901c0ca405000c1092484601d680c039440c2c034418502000c04150300502041007455802c0c035000400c09000a0306024940c1d8a03070200302c8603140a40301a0600d9103482e04142c05600d03039031101030141d0103100752850212004130301c41d0301daa00070ba400799100da05140009000901854000741141d0f2554010040c03500d40542201c5040520201110425405842070400000074005415044100c03001c0100a20b4020406001040040920310664000b88c00400084d41c514455580c0075 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 113983920 1250 113982670 113982679
    0x901120f0606210215070b06040507112a1005030403031a0607080c010612240f06060e030c040606050a08060a0506120f01050603150d05010e060702150c0309030702 72
    0x110180c5004000380c94160402040c41a0b056a2407106100c9600b0b403d01c0c460098030314064040d0710f0841c56000c0d100d51007000c0c10f40815035001c201c40d0304040d4032407a807012440c0340014407840412615810503800c1c82c604114000819903440c0801804104582c001074200d400c06523036071031078501401306e005c0100041c1c10306a488110b01101c08440780251100103000b000e4580d54070040c50002e8540d0490121a09198605100400c0c088105507003043e0094101480e003a9070a00010244d0b41d014541c00358003d455151203100640000500072000034042948132202c8414044050615000403a4a0280300d981000020800603401808558860301d0f20302d0558580e607180004118046910b50200b60490000a0340210305254130520500409a04900c3c0d44c040c3d81e90340402050340000c0d1040080b81d91860784081084c905400b40303841d154031440001c14a498455006420301c8006c80c1e2023800360b08280701d20000704900000385580810050342440c114140004820390724080e40304000c1c040c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 113985170 1250 113983920 113983943
    0x6080f0a05091c0203040303080a0b060f0a0203040f03080a0f02011e0c11030712110c0312180405190b0d0c050d330e030712120f020412020a05090112 66
    0x1a82c400340054841d11900c920281440612004025a242c1c8944810f8001643c01d101045100899004040d0401c0740182500d0610140c03010b04030982e03109803a4030056104c2004005894407a556424000358000e00b08982c50380070f02e40c0b0241810014004450840e4502080c2040c40d08900140880102d0206400108c2007810802900c2042e054410942c251101040500030088a080ca182107200e590337440c2d41d1404900d07403401d551041e81d04e5107280c0c140c11150301101d00c404030360041c1588001000c84581d40c13100c00c0b00032404442040e24112191244170101902d8140d1034069208424000e84000c1c10400164450245002c0d480c09510b1281c002490704a0622403075144070040b03006604d07283e8035202c0d1624000c4031f14008850b05140118103100c6480c00d0160080181e40c402034014900780414001e503881216010481501c040201e550380200010701882c2d880a08058612508007010030703010740c010803410200a501051080d40d2610041c4041c82c81e10207840180c0b640819070900307 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 113986420 1250 113985170 113985181
    0x2090a03050109230610030b06130c120c090b03010e060d080d0506030d1706040c140f041d271908090a060806031e070305060f010f06080f0a05 63
    0x4022040d500161540d0f0070305140d14140141d1804040000a103455a58145808810255220b08049541500b0024080b000f0404a058504c4503684408010118510154102c0c40c0d641115440c2a5130030004182100000c03001101e032103102c0f00c12306503081581c03401d40f038442203c840784014040c0f24003600d681c0c004902151a141400a1129882400192698200c0c56154020801190350500ca481940f80481e9614001c0351050883c640c03202e00c540e6256140e10070702001e02003034152081041200c801c2d140943c0c80c403001034007d4003281e0074a40d60752490700146042c012042440c118180e9001404e100601146c0098861003c80b8281c009800d2443c2d801180c1c1010920300c40c074148038500c0340c2544100f05041c0020072965400700d440355200c0e44c071460b04960790003040314800e4169001840180c0a8581d0388401da80000b142011500300d241c60390748090034058143c400c100c4010881006001d100d425404e0000076103000e2408030054540309000c104030040c094905d01d0f1040d42d5601144 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 113987670 1250 113986420 113986429
    0x6060303161e0803040803070305010b1206040c0207050312090103110f04050d1a1302040e010522061e0509073501020c120309070608090d050c03040e090c090a0b090103060209 77
    0x12400340c104000545034a4a810041d48547c0b00b2103400c00040d21341800400c0c542c4c87c0c034003690b0411010340340010182e5501030074880284002070069003944039000740000d507550304105d0701d10503900940a807621900040b0004d41500c00140f091640300c00c050100301811000202520100c82007211000010356860030301d404070f6840c2e005030300308403c4041c08018003001e400d45241085d9109440401415a415481500b220010340c0c1c42c040030580118041c01c800350210a4060003401142e001a480c1d007007141e9041c048510b070042c0c00b05981c484003000300c0300400788400d00c01000f0030a02100b000b1102c07807001c1e151207101c684094040b1500200e06101c10001d505a4021500d41022100c0012024480e0768080c0c00880d401d001c1c0d48689c80f40801c41d6445411a240540003010040034401030b03002c1c00303540f03d41040c0c00001603484148030000f80d51403850b030a2400317540340700043c040c041050401d01a0451004007050407440c00c110109425841c0c100d00c940c1100d801c0074006841d0b844000004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 113988920 1250 113987670 113987723
    0x5160b2809090c0201020a0801120209060f0111060405071703040b090114041e05040b1005030109241212030506090a15090906020c1e0a060203100b0304140606030316 73
    0x194603a0302e40f2a042e10380c990150300500f150300081d1203041c9030b0b0380d80c0c0f040541d902e1900b0400a4000c144000481e6690030b01001c2e64445c1c40050400681104444d06564503180d001c480559041d44100000c1244042400e45601c0084140d0084d500d89410108810302c50301c034400469040203010100750541c0700e1001d040d80c0182c1040d00c9081e071807107070940d40e4610000c1c0900505104600d460804451442c2500c4d00300c20700103180d100c40d41180c0c41c01c0e1065004003140050006c040401c00c45048280d111260b20740d029010621112040c841103041440d41141e180320114107152609091080664649540590048840c0d030082041e2080c4120169400e0701940007902440c207085c40d890420000ba005003a004441d2b004a41c4030715800a01405840d06030f52a03540641c1101501101041d0141c0081d688030880c0741c401c01680c0c2c1e0b51518100d00c0d9004030340c1600e000760203003200c1440000034008a90811804c50045080805501448881003d01d001c0280b000110f100c240c0c0c1115648800d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 113990170 1250 113988920 113988929
    0xe03030307140d020304060e0705060a210603060c08190b0d0b06030703050102031302130203040b0415020903030f0d0c03050f01150e06040f170a031d011b05160b2809 73
    0x40d5101c6c00c0c00d140c940045d00400012162901400300041051f0600105a401c1080587d07607200074444070f001c4c0d4000641b12042080e1915440b2003000c400b0034001e01650300310300d002c0d03503502c46103240094052520690289061048509004030a11596280c1a06641715600170450700910f8a401001170316000340780d4001841c40d4000310801c20312803a81c2d06104c0030365009a42c2e182100401c450030340c04a20040742d004058195220201e80410700c011214031070307a01040401458007030500000ba1941c0c10a80002443c130350005040314009040e40183e1115004a0905200d903017011500100303180c0c41409982d542000042241d100d092044050b10300c4404042c00c4140d072a034590722a5640e92500d402442c1503060951201ca4803003000096003000c1c0d58240e9a1445000040001170300c1da0001d001645041099140100c9a201c1e2445d1840140e588504002d0041e207400710380003507002e19158411408c00f0000e02101c1e0194404070030402412551b592648407100e044d0324242d6030700006811 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 113991420 1250 113990170 113990197
    0x90e01021c06060f0221030912041401120c120b01030207020d08072a05010507030504080105070c0209060109080a02090a090b04050a0506060a0602030a080934060e0303030714 77
    0x40d204010a00d95102c2001c0d1943d60395100e01c080000307841079a0b90302c40082d40100300c0c4102090088400c0d150030103181c111346500305403803103611801424069074110740c0060a0740d0418140c20405581c000215601c00b29000c001842000c9020001605550081014202540d141c0300610701583c030071f074111100c45500400844a01c0302d00e0800c0c09485c0c10600f0101c07041844102e0300103002c00c0d403d10300362080d45841c1d00b8655003400d1600444550b0070503201281405014880462644028007450f803084195540701e44a5218900400ca0703079881c00381c41e19060005440061099410104404403210f030141e0700580c043d1140108680240b088103000380c0045200c0061000304400816038503032480c0500100c40c515260001040480ca00314818100540d104001da0f5425074054000e003944032681e1016501411004030a2418580440840510301c4a42d03003450740000390442101400360909180010f418505400072070750364440540340c1014010b11141e0314001c81c00240881e8a407088850 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 113992670 1250 113991420 113991457
    0x1e060d060b2215050a020304090f09060c05090a120521030403020d2618060a06061101050106210e030d0e01140603071401020a02031203040c0f0807090e0102 69
    0xc180208a40014144682c1d00c0305415110407a9182c440920040c0ca6103071080d0490046145420781d5281c0c00102c8110650000388400030341003803684500b90310a62404000f181101041c6049000c03a0007030341100d0240300c028025500c4a403121440d14099803030904214248190500f0304902d800c0e0003d4520107115400e126503250411a41c0c00f5501662182d001c4030b401520a007015544070b888100321491120001402c0541e00d150b442c656078028016443d484d0a0f00c40e401c60f1141041c0c0200d55502c007064486108000709940b00f03094580b11900400200040e504080f40245420f100350401000da0401c5000d0200441072036201d80e5040401004032599003420107501c40103001c20140d80e1a21b540f0309118a4456400150b40621680005014000c05410030203540d050030700f41c010460443c450291034a006031020842c0010940117070508644034913145c9480c0041070b00c113070450342e02d03c0c1618804012150000035080c0544090380340c08140b81010300003640c0207000c1d85604555081219 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 113993920 1250 113992670 113992679
    0x714100c1202160f0803030a021b0124060503190905100c030519090f0b070201060509011214030a1d0d060504060f0605030309030618070f15030612021e060d06 70
    0x1980b00c241c030104500031400f43c0d5120400b41c8100014070070300203180c008000140d9408450360007816070520325440f901d04100312000607401c507159040076000c501103403885441d450341100790b558000c10703a503d000752071490140d000e1805000000d070038125103611020014100a07081c4044955025940b01c10032084819110040241400b0340c0d10902d035610324005400c00c00703464042d01105039000f01060400411580c1c0303200c03034800001e00034421075582c0c482c04101661500c02032030081812118000f440781c038030b00f045070300c10715040d100800030b07441044290002c1d90080c00814005003280c00e4640303801000804603d03051400c0b00002c140b1454081000700300481c5a10440c0e91281c020410001d060b00c55003410b80d244210b18074981d00d5408040029442c185c1c101c0f003900709290300c130166810f071a03070307401091940f6089812135841c4801e0103102c2c00c149541071040c000281401241e45118859580114880c0b14020004101d510302c01f02c6011810b49401d81110460b2400c02c00070000c20703580d07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 113995170 1250 113993920 113993923
    0x714030a0515070f090815040c051e030601050d0309060503040303150b0c010e19110d1a07020c0612010303050a23040e060609090105060304050109150606020c030714100c1202 77
    0x803500344010a20101c5104d441c1881081d4030010303610254000e040c4190b104031009101c120061007100d1b0011040c0b030202d01615890704e00c00c3c003001916400a4500d04150415003003c0e01600802e000c1d451040300140803a03030001c1501c0450313042e810175580c0d030b0b112401c003207018000c142e280101041d00010000f841540002c000c0104e840e4600003040b02814456103aa12100e49120380c0b4410303401d04421002143c01c05030000041440204000d800c044d441e40c5e400803040b10515100c0000d0240d40401c030303416406101c4550646011600c2c5860030940d60900d0185000c180000b03810480c000c00c1da22441070040703c2c000075000c01200800d5070050300c1c41140707609502074002c0f0a81a5070070008255181421002d4030791143d001480c1701c02d240e00b0a410f118191300018030690301d40d0340310030300c103004680d58482c00310140303000c003074046612030a20b14082e04e40798640d03410710f00036441848100300c2030180da143c60764004021560007411070302c040405c403507008104801a0030b4841244079280150740 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 113996420 1250 113995170 113995213
    0x2030919090501180c03110f0922050612010c0c12200f0c0d02030c010305040c0e161103031e060102120d1d12030f0c04080613050f010e0714030a05 65
    0x181d0070117202d801303121482103003610002142c2071001c40d805e000210781200302901030840310f50003034058014103103210030440d185240c00f120710300303c240e0703890601c105820002030700c550800c14000284a51013800d01700610a00810001502c55040c004031421803500c5021303c0c0741ca40d092001c2c4c2c00c00c6038504814040d00c0b043c2402c2c03240814401c0380482d0466061150a001905400801800000103200015006084000c0c011030f0f40d0012414003040d02c6140304c03130090140c0c2022401c80300320208227901030041100c104100005504c08e208100c1036901681c00c0d1104941d900c0b06600c103944500c00140e103440410103e803001601c0c08a0015900402640001ca804444c2d400700f0403002d000d800419159900100034652a10741040007034942100e140000ea042a5a565058074190303941c075055080c90700507201191020580780e45001808400c01c03000d1000701c6004000c2007606821010b669030342d0810310400070700d03040c4001c403845940e9090100c080c019400505a4404040d030380880c41c14a178 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 113997670 1250 113996420 113996459
    0x130b0f0603060619090f060b0c010b0f040506090a091707080d0518150903040302040c020102030703060b0f0405011d040606020a0519110d060608120a1e02030919090501 74
    0x40b550700041c449203007501864640e90031041c40390000d9820a00c1032809040180d00525031540c41e0301d400620140d030b4400501d140b01c0102c00020b090003c04c01000f080e0844c54032402c0c407d5007007006005095949030390507030700701100c210700041a410b41d00c0c0403411002d15000040101c03001299413814082403100401114010704001c0000d42d44800700ba0306410340c540b1484845501c9405c00c5070080c0c00c0040400c4d0000105411641001d0b036982c00902a66183d811041c0103135004400d0004480d01400ba02000d171052141d02d508010107058411803070f0142d4030507541001844c1002c4045104800702c3d140d0f0040d0050003c1c080b0a445a00196403040f0000e030480c6c0078468084c00380d0070641001120004103511090a0f034400c1160b0007084034800c110442528026540c980001c1c800384100110840c214070301400c0780e1100d9581034050106000b840d98403116104a2a400740d50365408000c680c0220811500c088100818448048003000507401042e1107519040010402c01600540c82c1d5082 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 113998920 1250 113997670 113997673
    0x90712050c0a0804080313050709020712021209010f05090612090f15060d050f01050a050106020111090d02300a0212030c07030201050306130f05040515010605040608130b0f0603 78
    0xd444418880310980b0495001d807000401c000081000502600e00458000300119a1405200c10a4460a0402083d07a10944c8101d80c00540ca80400c40034007a40c410b0303110180040e20f0702d89200c801c20f09851003180c41050401480d6658095220300a5040d144003802c05442c0030b44030030b501704148240d10800d031600c0125207e2040f440148a1000605c1c4406144a28442242da1210820b1041c12290904d00b00c0c0d0b5030040041e801261802440307124401d5100480100b02545000e80c081d08403140e00c01d102c0c3c90742004203c01009034990740043d030810b40e0f051b140d5080d402c0f4602500c541c59090900b804024a10804507880490000a00800d0203802150be50b91325035510300f001d0b80c5c2c3c1e12a1860310400754010031020805980244003860380a01c024040b030380c1401c50040070b8422034852445160280c0d5440c8144070a010703041200701c6844a110700c0132549941051006072050065100310740800c03000b60009212a0f455080118906138401d0030f044843c1001e42d088500e1010885109019 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 114000170 1250 113998920 113998931
    0x3070306120807020102160612020a090b1204030908030f0f0d090807120305010501080121031e0201090c050301020f120702030912010902010305091204030b0402190b040f0e0f0c0a0e090712 83
    0x1245c110041c81c20480f48e450720b80111240900880c030001e50025040c0500f0302c00c401c4c100045001c0340000600310b034038085000c038609281600c0c0c060014490750304610300310380c818002610340002140880ba4013446c1048001d0f160700d04101006c02410743d246006080c6200410060300300490307004003c441a1103901d082c8001d0383c0307540046440e401c1c24440c004255088890010180113144200464203002e1314042c00c420821110107030200910301071040043c0e66851010060100019644014102c00c40003035140101c600140e01c1e6a006401100002c0000d60012488140c020400c48a0b040da0181158402c0d010701040b10f4000c04003100164013280c00c0c0310020700501004940c8812a10455a40a0401e03046840d680c2072114010030498001c1172035251413000c0e62098140c40c0007040d00d0b005d910f580d2428104010180c1e842030384442580e85140081c014000d5070394001e6070f8048480000a41c44005040084030725240c58040340c1d80141d90310f8180b10314594001c5080e00c2901d601e000134400d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 114001420 1250 114000170 114000193
    0x1050a0203070c0209130602130e0604020702030a0b190f02032502030d0c03020c01090c15031802280603020307020d0806030c011b05030d090605090c0a0b03070306120807020102 78
    0xa92000311078500010703202d0701400f00180f60000c402038114249045c8014180c0140d6610b8040780d010181081421248480400210b003041c0005503002100392015402c1c4000d0fa8080390f82c440440c0401426100f0030000540040c0d501e075036460010090001c107200e240c0010032150002c0d4000d440c15120743d000201c2c01c4659a0340005075544d065003075030003985000d4001810b03400800360541d5050825408101e0b150500300f0901906483d94000d14640030214a80602030140c0d9410301d0500040c50704000507440303101c1843c0603506c3c50540540b6032410102c000d0303c07608038030b00384010011603a000d090400b045042d0b145e805148102c4039602240c06002855009581001c011100c40d44d00d940a10b1060300c4039481108805900314628185508103071581d03403180d0554102c240400c50455851031880280101409443d0300400d00394094440001c65002003404070001c1c0c055090300c0ca1002003c1001c02e803096010348014004044100c40620407890303c080300d60f0103e0b00036030051080d55140c84 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 114002670 1250 114001420 114001441
    0x203190507120503090a060203060a17071d040b0105040b0609100c111203090409020f1002010902040b180601030c020f15010e16080412030f1406090921030907080d110105 75
    0x1e005c0c500b01c60040c54044815900c02002e58030003065581c02210b00c035000142520342401c050814034044018201990409001c140e4410b04103218800ca211400188400b288080d00d005044d00c50640d000f00d07000c11101e0102c0c0d018801c05008541200e02d0800300414658001d4003c1a580c0c411b000498961418004009100740085000c00540d0810041008540f41a51109491503c06080e0802c03580443e00015071610f4003100207005070b5150440c100442ca403511408110460480781d04101c00b1200d80030b0703100f0300320080c5203906240c0d40304c4940401c039008002070300d0b10080311403c460042100c5480c0001281c0300f880394181d402410000b0840080384104e09600c00000d07943c1e42181c556480e1140c190061400003000280360b0b0740c0e20b00c6400509180540302400c0d03105030064901d81040424424040d0009064800380c1d00409030b507001d05000d50441d03920408803407800d02c0d243d80f104060345050101f11340c03026426204101903100c540b90000f080100c5010ba200080001e99151000c41c1d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 114003920 1250 114002670 114002677
    0xa020705060708090334080c010e011a0409140303070507200121060806101805061c0203031c0c0801081b0d050c0405091609141602031905071205 64
    0x2101e41c2c2041c061100d000a48128101440781c18424010341415000720208511000607001e41f4615070000e90400109024001d0b80c1d6003842400080101050f40280c816043d1300c0f150500e84a5515118070400b400880481c02d0b007000300d1141901c0da60700b051000a00254004002107980c1501201c00259422100e40010300340c5030107840f404c41c2c0440101180d09030301c10300c400340c220040d80d400005c1081442001420301c00e8480381613800026040c000c001416161119092015505000c10012a51940703100040160307201b00455801f5000d610002c0e0550042c1400c2036061044420380b08980300081d080741d88000d0894035401c64a0b40c035031035410b841c0c0300441c2008100881c42442032000741840851440c60794090400d95960240f4540041c040e03030030644440415a110141c624440328852521230010405e8040070801d01070750000c050841c51000342000748000c0407868440707e06e4000e00c11a844c950b10f0990441070110b940c0409000354100900564240100c00e00001400780110b045 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 114005170 1250 114003920 114003931
    0x5010305010e180312070f0e0402030702100f0209060708030402040e0f0309010503100e07020c01090915140f09040b01080c0103020903060a0b21030309060702010b0a030818090a020705060708 84
    0x30301d0030039079074288008501e1105425a61982c4020084c4003001c4010085907030143c002c6d50303966484d442c0d0b003110081121010301c0c660b81c89680b0400070301240580010f40b100e000e4803811000b02d2502c6031000c24038028001c003e10301e130f04100b001440004100d51000294425842190b04102e1340c4425030820780d407175181d90b426a071552b008101c012425800fa4020355889140041d8010001e500c0361300b140081c1c481a5040009a4843c1c03907107410940c3c200101e40058007004004004040461900c840012000d108015107203132002e52252890f124000e20314a6a40041d042e20050f041c64a00b41c095810244030b102c00c1c90044100d0441130f5803090007180d21550300100201a44c1d00da0800c030340020100c5050140e0b110800c26400d200c00010b00d900782000c0c5001c0c4015681700c2c640040303128204440200508216454107210381220780e40c4498100940f600b1003101600c1e10320010000c007501544045c1294042558070030070400e0305180d00181021445041601c1a60b1542e020581d80020305481 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 114006420 1250 114005170 114005189
    0x1e05162609060319021603110c0f1507020a0f080a15140705160501050a0c02010b040c050a0c0302030c19030f170a02091507030905091f03140a120f090501030501 71
    0xb04d0750441c0c1505503451903000381500145032819002462541c0a42500202d0101d01020315600020714180459070f1050030a4800d42c804040d100005410004060070444103c00041555070564651418a101824101c0da003d80b0b403a859607047c6640e801d0640d0102d070103000c7d80c8182c4103107002900400320740c3c60700300c09140456290f592042c0c8a940082a03803540c11002458030f64007180007405680c2c050520f600001816810001c002401e4602004240780100e04010034481403651090031035941004c58a040190401c492074100d0551094480403e450f206081e510314502c1c0c0c01c010f209051f18030a07202c10384504c081c0d44064035945e1171800c5da141c00608582c00030749249800c1c2c00034040644010141c0ba4964008481502c140e08145400e0340000e41c40c403018040383c24096841900442034280307085480c0c900300d1303c2e5000025103020050485803130000207000c0000c2009260100359021204462503811014000c1c40c0c1120300440c1800952808000074855000e0312845060740c10150 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 114007670 1250 114006420 114006427
    0xe090a08040608060415030b07170402031203130f120f02060603070902130e0f010503060601090e071d13090c0b07030504140303120c070c090c1e0516260906 69
    0x41a070f4002c02c0201115081900d13007244c520b00103000d402d0751000d1841200f2a21840c1802c501c014a19003482e001c682e00e4020310000e00025a400154035144900d0003000b2a81d0796131220260752000700085030003000708240180d01d01c10045081c464000046490341c0700d00c400c1d504c00808980c0d0707440c16a0300b1a01070704031100601c9040c3c26500145606232005203466552581e540042d0101e000c00c85000c035000820b41c00502c094a818450142c100c0000d103000c2606506004001020243c094445001c1c004803400070807007440c05482c6003141c04c0004241001c8c14000003011750241c00701490031612140e20300004a0708030b100200740c903100e03901562511300341403c10702c0201b00c000002c1c1115605200c00c3c04a5545004c681121303520403409038503c0f58886045107441c01c040501900405002818044402c004a500118030000c00f40b03510859a6042040002901c0e1031080306074442860102141310b000f4001502007551122090f4007420010360310440195682d801016001d0740d000700b040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 114008920 1250 114007670 114007679
    0x60f04120e010212040609140904201c0302030304050d090f032d1a0c0a080a02210a02130e01030308071d0a0f030b1f09020f0d0e070e090a0804 63
    0x74030003214042010b00483d180f010144103c0c02c0a034000b40e00406c0090714028080c4034070410b103041c10390b0300b01c0d080e40c9003130303507811f03d030781c80401400004c0c01ca4240040340040c80c1c2c1181e80c2d18480c05165000c3e81810b012040000e003802901c03540119400c0d1024031540356080c1c1040d102e27003000400c0700c2c0684c400100c81800d41d136076410003940c4640110003080e8580130f86003003030010740151040f1134820f000410240301500c80c14986518000d244481d80c0e035040c8500e030006900551043d501c1103001307500503644c00c45d808040f900072480112204911881d541002480344540c3e00800100d014203030707811181c5a0b20792080c500000e00b4040200060b0040021071007060041e21905440c4580880c421849940c180c003003100454581d001c4502e1000c001010418001031001c116004802d0800742d6140da55201006072100341d40e4071032a0000b60380003851260202c100c1d030030384162465050090001c0990b850406540341254040ca05603501902c0114a2860700020b81c00d040c1ca074403820050410303141 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 114010170 1250 114008920 114008927
    0x20a0929030613020903010e210301050616020d0b070e0f04060b0a030b120a0c061704020d110402040306020711010e01080702070905071707030608010b1207090209010e03030403080403020102060f0412 88
    0x20f48968400298081c020005103540a0103030040e0202c140008120244414500040c1a001c02c020300b42c106074104018031a5456203c2112160b844510204444100900c0410701c3c10300c02d2040a4600800b00341408202d90b846030132001400f40c212503d65007020700c04100710444d00795109601030803100b0050121000e0090300080d00c00c00d402410743d1009041d4102c16400e10b01100320459103060a0b0318244105500030460055005000309010100c0c601640070500e6203202c450702500030103654100e003050f5078541e0102e501a60348110150344907915840d0036244144404c807403c1c08620500d9094005501c6180c0c01c1d8401c0c01140c0c018031100d40b8100c6007200030080a01084e08002400344410308010701c10401e5401034072035650000d0707041c0c549041c2038211103404c00c041c1e100390750344100c02c40d91100018102d01550702d81075005a80342c08410040c1c0708004010b8210b078060101241c000284585c0001230001ca9000b0b03002e03280b4950300d01c2120390b081c1c0b40842d8028007101c11450310828141c030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 114011420 1250 114010170 114010189
    0x115051615060f090212010617040f110303270904350703020309010212040605040611210309060105040203060d03030e0a020402130302010e03070303140715020a09290306 75
    0x404101c0014020340300c24401ca22200ca0342c0103002455000900c2054424092080500402d8207203003940c84404d06200c00300340200082c2024159603966640ea0003407107061172404c1e6244000030304407581e480c90450154842a1a8a203210191040b002c82094034207080d51840d00c80e945c016403c81901d1084c0c59102003003d8910304d400c83c1d8510300e200003003801b00d807040200301050003500216103405000000a1801120700c401e0310511005020805c07a00c0d802c401030390b090f034200c0d0a0800748490b02007801841d00d081089681880078000807216039035440200118040e801c00020303900c0c580e80341c3c03052006911080c0c40700c50700300c940180c0b00000b10340b00307074490910b50001d0700a40f21b8484040c0c0009050380c02a095600d198200200c0400444d0317002000c54001c51810760107080c00500d035442c00b0b0f2081c0502c07000781002c600001007400c100000201d200c245100c90070700840d210000340b0802809170b0054000c5c00500301c800c51240d03000c0404582040d481500c107038501071031a511142030019152 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 114012670 1250 114011420 114011453
    0x6051903060522030507080c0a030314131101030e0f0709050412020703030f0507110a090c0314041505090703060e060f0a0b0906040b0a0305030d0209030d0807020a0308040212010c0801150516 84
    0x78410700c09100081d00a000114419001c0c0c0d4bc0030403200b40e200e00684402c2c01c00780c5030106540c5131070b0074130002441d00341e10a021410242800038481c44c0008070181858008401c8030340c180902140841ca080d803542c00301d4000d60003100c551082d5000c11b0010f0b0390b2101c1502001c1c001c079140502e410401e070712800040280d103114481080f80d00c0d00700400308021f40310b6904000c2c00c403600c42000c144003c0d0305100e0b100c04441501a01c1610b41003603219080c0703c0000d030800703031440c5448000089001c4000c0221000841c0e000c8010003c1d50b0559420139200d61096920003070380d5608201150340e8048078050414481c60062a46c550382e2184001c20000341300314000903070005402600000422014005000880308280c005a41c0300d0b40c0c2070030141040b83c0c1000740d41c2131100400131320020f103600048503004541d050030508003e40b03c900003ea001b91003403640d031103550b08021482d003510b0303030041c6003504032600340c511071945004864040d16036001c0d4000b80a820076500d1101800314203520176008103070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 114013920 1250 114012670 114012683
    0xe06040c030e1906051005090f0a2301030506010509040b24030d030e0d05040e011202040b06030114030606010f021513050a08130503010203010308090f030106051903060522030507 79
    0x8042a80595041103c80b1800c1403070040320a03445000d0100e01d024599214403007182000f0300703078104800501940d602511101c89041264009105030a6a0b48010b80601e10b101022075402c0d030444200c48000d90034002107909001c5d900c0001441d0800c5410103008071707071089504079981d40d2000d050007250213400d409107500b0b191f0f040c10729040c2c80a000d104118240c41d60041240d15841044030300e80401c0c01170761410840100410050380301d41500090554081201058144d5507500000300504480e055031030380301c88000000500c55055400102c11880300345e098845555034400192101c803040b02d40384000d0303000fa0a001b0b42041c90405056030140124609103c44e040c1916a40d15201407400111180030340021842c2060400004410040ac0114020751942d03042d84e0707602c10240900d000c018000c14901809041c1a41c0a400c25400b034030003d000001c24940142411020200b03c0c481034031b80350714040114250315503000c6000071110f5905280301207841d0543d07044925900013541130302e40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 114015170 1250 114013920 114013931
    0x30513141501080a050714010f0503090709060f0e3102030a050303010e10080304030f060f0f1b030c02010203090c010c03120c02030304030e010e0f091005121e06010e06040c03 77
    0x5140021a940d40a40f500c0d0008010440b41454091315209154021001c0040c0c44001c05c0b00682e80005450106a024508a42c890300c1e5000102c2c03030302c10315811210b8030314100b0b0000703c3c01c001c1c1c096030b0754110340c20019441031903190607a942065213445400304c070b03120702c2c03800c00c10388401142d103200c0c0d9200344054125449019162501c5040da0001e030080c49404001d0001c1c040c5200007248800080c10000e07014500c0c081c5141c0d102c4103068000603000700b41d2521020451040381060b4003480d030b00481c0034011300c6210500f80e1920144001043c802c80402d2420030505d081034814402d491050615000500141c03920000554000c1d005010480402040c00414640c87c00d0b14050308208800c0e6400640d183e0a141c9405401000070006842c10043c880ca0359045951380c02c031384003800740d0b0203403032041440d1580c034100d01d00302d481900516081440080d100301d05c080c3c00075a040a00b158100300c4690481c9000c0101d455140038400c041500d50382c500402c032580780139800f0b40448461401d00281 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 114016420 1250 114015170 114015193
    0x70f02060322050109051606120f020d0f0903020118020d060e0307051b010210110306040b1f23070302070e060609100e0a08071514130b0309070603051314 68
    0x440b81d4414000ca0307407a5140c2e8100805c1220402213600718024100d0240101030030a44014080c50b2074050013074006460700c08404010900e5411201d101e44001c2051181a480c001090068503d41c101100150f107006489600d200c07082c120521500c1e80184114030b10607840d126640a000c51a040076000d0100300101d00005200301304c5a00000304103102e009400d407005001a042c00c540150418010b07042001501c1c0d03880440003100d510a40c1210300199088400d000300343c05125064030f4000164001612451980c1c010b101c6407410003010f2480100c580d17140d5012403041c05143c6004015900550050000c1400c040d042a40103c01928a5050000b00e82c00214100391012013200803a20000048402d400d0007698217002e406c5110051610350b203008101c154a50901d40c0c0c8204000f038451500750190000411510804141c80591a42544401a05003a03a00507201214280b21b0300b00c001845034042e0041c2ca206107404440708450340b0441d15008041c03020040820400d0145140c2c001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 114017670 1250 114016420 114016471
    0x402030a141608060306060105040302100c14152508071205070903060b01020f070b0912030a0f09090c020d030207080c0d02011a0301110d020715061d01060302070f020603 75
    0x148a55225510300031003640384007003d45220800342901e4040c1c0c2081c02000116600002280c080b03a60540f030503e480034101381d080720450100ca40041c101c0c0f80716805211032001c00500366a003c20141441c485c15101c50281d650b44402088c07600740c481c4030061111148901942103240d02007040e0400780030310100700c120f40d811100101d406801080000d5402e2050058921810408001c02e000800c0943d1811000b607079a50110f2080300741c10700300050000640e0f142c040403aa901c07085001140e4464a001c000034105010309405800044c01884000800221074094001c942d034182d0007400c1501b00042c0b04802075440814142e4100c07030208018040804100514600e01000380d0002075a481d000c01c044051601e0102006d2203681842410245a103d50044030301d180410380f40140d51b50381c5450588840c0c0002c0550040c0c240c5402e100195800c0d0318982000050703c2d000390010540e0301c07540254105c0c080e21402a10040744003c0250042c00c00c0c00c011034111700c001d00c2840203000710104c1c0f078 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 114018920 1250 114017670 114017711
    0x60807080607050a021f020304031b0b01140102010905010513020312040609060e010917071701020a0e06070c050a0b03040c1d0a09110303070c050f1f1b0b0702030a02070902090303090402030a 84
    0x806c1c500f940002044241548090001202c881c100805880e0180302e89403007810b1300040c010321000f44400708024070982e000b540100714075035000c0024812450311400b003006140318448103a0080c010590362409508082c0112000d4032495141e102c0f0341c0c0d0419808032800000048030303a06000001101240c0050041c0002c03682680c0b00700100115800d00c0c002d001c43c40e00440e064141d40e0300621036007084940103101203107408015244076480388070904000a41f01e945500c415006544864003180c1c00100078000c0d44513078090564800c44d0341d41d0300e510b10707064006005105100f5500b0310100740314461035000100035902400d48203c1d032004030000241580d00802c2c003180e40d01d462039070810450800c03043c41c84500070201c0781c900c40405850074080c588150341c003409080201c14071407401001d801e08080042a5040040e0012a141081c006503980e07209100c0c940240c8904c14001900d1640ba00803070740704060242c0614203008200b824800030b500041c00502e120f40c1c6a5904c40026111120700 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 114020170 1250 114018920 114018973
    0x8070e010e09040b06100e0a030f0809040203040506041704030209010303111005190b0301061413020705030d0c0e04050108070501030e070503061e07051608030910110409060807080607050a02 84
    0x100303113080c1851020050420450700030780090040c004d040c0041030780d44040400440380c01c00308540c0780040a00e0aa0350078450452400d600900c00f100784014000f0001d056486144103000600000421420f4070306180030380d02c4001c0d4000405401800080d21419082085400940845942c80c51030b00f60201a500c0c00c03240c44101031408601001c0410b01402004514141940208100350038011404200b04190b2805070141d40c2a211b003951f01c04042d411144440d40290550381c80d000304c081c0c590f0160400e03e0301407001980521040ca2a442c05100d490304849140b03000700b0070b080c64840150007a001c04c8585c08c01500880710000303410b48051000510881c0552140d101001552403210701c550030240c501010020140242c0c20036048241d1590101d6030441c64051b2641e94151850f0310b484100f007218444182418031440d001e0303d1072005070054820021052004584a4150310341e00c0c0028032448034954090070216510b58000e0008001c0b0070700d14070580300d442c2c0102035900c40304bc110214 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 114021420 1250 114020170 114020183
    0x50616022e051e07020d0c0f0512062e030c15090b0a080a090206040b0a09090b01050f091903020d05030d050a061206050a06180501050301060602030a08070e010e0904 73
    0xd40c000068000d000c0c003421a41410090b0400c05000c400f4401d40743c20100d50501c042001900d4001d540d6120741c44840035a000c5c3e800407203143c0702ca800303400c054501c2c440d2034041c05003c41d91001b19940411014071480c840c2da04c111003200d0324400d01c0040005603401b00c0c0480900c440c048085910507125002400345030710800502d03007065400500c01c40855014a034210818840c000100e5400005981c02030107046010500803040e0002030f20611640e0701c1003090710350000714002250740280c0410200d4042440c1048880d00301801551a03100b9001c0c1c1100c406010411200c0ca072401164100e00840c503d00a184c0e0142c49a0200301502e451a000b903070030ba4000b0030f100c20300b44480c0c054241c0c0010704040a1050502e0026040141c05101d48028003017621800060840c080952002d0005c0200480104008050000c0d6100501003805081c3c001d5003822800300310075000008480c100f020319520540c85a490001c201c54000012031820704004542c50740080301e9445800c0f01e40158090103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 114022670 1250 114021420 114021469
    0x527060d060509060f0a032604080609101107030305091002270a030c05060d0e010203070e01090806060105040e070903080f030a1805030d24060504080d0c0c05061602 73
    0xb041211084004001d10b00c00c40049280032010784420800c9000c80380e005140c00c16118647c0040324100d500c1c0c7c54540701b4034401080c0041d14003000904503024032244001d580d03038441d80d44128001d540034208041c1900b20700300300c00000a4400d900c02e6a01200c250300752054814082482c2040c1e9025501000c400c3c41d0096103203503202600001240044030407103072200860701d5030313640746c00309a00f522907144124400b080c40203090030241c20240c200c031003200c02159030789401c180280420415050950014100041c080344070103001030698050301d0142c494a0070a0720300902444440f200410100030000c0400300000007607a548081c2000c801c00701d0f9041e44900e40365a0a40844003220019040b6048510405020400101c00c407030240c2e2211304003081e004841c160704018420510254008030b02048000180c16070300001520560b140d14082d42d0b0032015400c001c45209008a00117003030a00d40a00400a078078120006001c403401c0b5808101070051941c000910004401a0500c13040301c544 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 114023920 1250 114022670 114022679
    0x31204050c130b09060f0f0301150603060603060807031128031101052a0c0307030605010611030301180207170c0a150911101e020c01020c0409030527060d06 69
    0x3045904104504110100b12003072150001407407000e030141003580600b404d00485015621001c000e0b1f4600074015000307001110450548400300602da10030790f0b0002c0d140030b074086101882130090508840d6544014844c0c1801c42d107400350380100c00b0444aa01c101c901c8014000000138004000f030482d001d0b0300c0b5020003072450902c4421800030b4454941007000c100205030609003a0b60112070450000000010310b0102500c03002d1a001108201940c148901a0000204401c50700058141c404c5540c0c1ca000c01c05030b4003821076981c0004c1c05465286d1010418030018008150302070f02c400c070700550185c0c8101c44032201c200d4656008009040c07242d00540e89100611003c0300b540002c1d080781d100c00300301518054450310701c1d020443c0d070258404c4520101040c0080c1c0305080741c024081290004403145c02919102940e914690400f560243c003903040c421034180780c244602c17110b0b143c258641705e20707151407624846041080c08001410303a441c2141c07001072648803035025000d49008202d0014455040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 114025170 1250 114023920 114023929
    0x71506050406050a0303050d0e0304091409010f09020607060e0c0a150e090c0706020d0204030b070504030c08060f0f07030f1a0a0506040b0f030901021c0b130c14070203031204050c 79
    0x30743c02c11405043c0400d07080000903030102c110307a2402c02d01c3d070001500318440c050460440c4074651000348180d0030035228148415003041d481c1e0180c0c0200c8001c10107201045204000d94010200180d40a00c0603c040b1000c194150000d00030008404103451510b260f074170000b4400f85080d0031804400c0c1000a80190068003c0004103040004440300d00d1589810360740c4c00303c02d118052000342000c4c1c0206034880340f80c8064040d640a5580104940320600c0d04200040440c0c200e84000d40f103401c1c80c58000101182c000c2001c502450b00d2034040748003039036400b00c0c1b130100040150034142019519560b03507082c40c11512502c81030340018407120014000503000c21001103030360780200748038400400003042842c181c40121207880981d04d591648036034400e960540280030300030300503007140e11810000a4604090b4030100034203004035266403414071403403005800c564102e00e41102041800c400795200403010009420128401005c50345803480c0d480044020f0302094a0440340b99104140c8564140340 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 114026420 1250 114025170 114025181
    0x130302030a1515080c01030e01090b0109020705060c090f120f1501261903021203040b0109050c0a020c0f0a0911030609160207031509020607030e030606030f060606090103020715060504 81
    0x3d00002c08500d040100481d112049100814141a95a003000e500d031a402e4102c404801c1e00b04e8a020b840d981d54a0b040703400b941c40381d13104403aa8040c0100007025200e040b03003a50700303064002d4501d02c1c100135001c050190301d0307407901e080140500c1500078807600300700104000040507500c1c942c2103117154500441e001d502080407a01c601c181d030b0b10310015060700100180201081d0440c840b01c3c1e100140320700b020703818a1103050704510800c9000081000303011150b4001d03812030740112820056a550041203c1d400e001c2e0094920060704944540840391800800d00c1c00788403001019110300ca907580c003031001110000a403550f061540801080751520341040c03003681c01701c031503040000030f01020340c0020b440e089207000040c55040071440206030560150b00002c0b00c9580030b403100e070b40c0c0c100b83d05024000d4600f440c1070620900c07408001814034100400c40c4800c0c40204401000c150b2030b10700c100182500018034207410541d00b4015a0081020214003020820750500005403890400c03040c00305880 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 114027670 1250 114026420 114026441
    0x60603040f140a1b05090a0f020c030a020a030e060f03041b0b120103060e0f0a080c100c05030a0b0f0d0f050111210f1501050309010605060d0b040e06070c0305130302030a15 76
    0x1040e030301e02042940c6501b003c0d15400044100000350008610600708020700039500b20b10a43d10000c903078541240c3c0c000900c84140350080c1c9541c15980014810803c06215a40211200180500c0810001030b441b04503050a4180010540346058a41030700503843e8110031352101d034a12042c40100180482d902c01d41001600301c0e409007001140f950708d0f40d55989494000140340c0740300001ea030907040e4000c2c44641c0c81c42c07240100900c05891031340703030041068009403224480d80e454498845164541200380724030940d0040c0101d510040d1507103e03a000c01c1c500d51f40546003075490741c412042a01c0e5002c01030000c02400051a00c2405051025400701c050003440003000f181d0303440a0100000408142c114460824078019a4a9450f8120b6501509055000582141020032181c0d00d5150300d802068070301c0d4050307804003ea120485000da0344d421058850402241c0c4245c04080803c0c800e400505240a8000181c52080e82c0c070340c0420710303000700d1240580d009411000c04d9045040f10380159420034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 114028776 1106 114027670 114027713
    0x130810020711010e031f06030f0c08070602060c0706050402030a060501030803150103060b09151b030a0f17010509090a080f03061203070506060603040f140a 69
    0x1d400c0444111450100b5008121440d48518118206050b008008146030301c6075104059900501d0034669000645410010000c59101c0600d190050701c0350b085103034018500400f144c20144207412034000c54101c4414004da6015403030540d20000d07003010780004d040e150781c40081d01e03003e80300380c005009508040000050240d000069449454040c004440880200004408903002402080f52491090100007081d04003071051070350a4052450b4189080c01019690b81c43c0720080c441031205610024072188507550240c02040d9402c602d0515090342c808600074031040000502809005020150000d100c04100700101c001c116000080c4036030700c003290351243c0380c1a4011200c55000d403451b50005060307203400004540585400002a1225032120030422440da400030304180c0d070843c00d00101002040b14080f01741c00201d10480113181d82040e6103091401400480c3d80410340 = true := by decide +kernel

theorem cover : BRFrame.Cov 113848920 114028776 := by
  have h0 := BRFrame.cov_init 113848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 113848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 113848920 ≤ n) (h2 : n < 114028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
