-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4646
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:17:17.652405+00:00
-- url     : https://prove2.me/submissions/ddd9d4fa-b46b-4882-b8af-06bdde2e9a4d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 835431654 ≤ n < 835611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 835432904 1250 835431654 835431659
    0x812090a080f0d110106030314070302011b020304080c180c07081c02030106110606031b2101020309063103031404031d0102150106030c122306030105090709020c0102041e03030207 79
    0x608881c6c10b40801070104000240a590519105015204291107440007040c4103000d000d09a548400d03403400d20004d41d0001c01d003070243c08414806040000000c3d03400c1e044403804042c1c0302050103005460f842642000103019000d01c4030000444aa02c24811048075060f025411204002d510074404c4c2000a40034254210748014049403440c007030f2600500910710003c01e07130304d60780c00120009401355024402c0003000402d9285802c0807883e05040c80001a2603181802e41241019001880100d441c1448138080505840404803100319841095401c40800711514040d03000301807507400702c0c200c1c1035940d040208041d4015010000702e218400c90701e41410491005a0744c5400c291005078014040744018000940309034000e41c2c2c009030600d03140100720a0765020b00c04a5580c80b400104c01002060b0140d07070030103180d4100d0381000d829030080200380b0380700001545a242c1d40c001c91205580018244400da00300f5019500540140c012500e001c1d412410701d0742082565100450150185a100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 835434154 1250 835432904 835432937
    0x60c120708130209060d0b1303020d02031303060c120e0105060109140618011803050f011a0607150209130209040c080403020601140102072301020f070812090a080f0d 73
    0x2150080c600c10b44500c1c5401c0c415403c0040240005144c0c90f04440c0d948a40780104100003001801070007020b000303130040403043c01d0083c1405040e2080c0ca05550003040044100c040300d040c5201104d821800c009601006084c044a414640c080c1c09007a05043c043e01c0c803a00724040d48007501625098030350760a259603074020840c8150040619a51100086c01007403103c02580c95000c815039014035141e07a0301d01c08403150901c1e40d1090b4100b960143e100c1544400c00183c24410030521040c0b030300c424600f010b100c0c0b002815503c16603200030315850328840e034098000c01c0c48c1c0503240d01401c01419019408201030f2480000c4d0401618175214038200754034076440354098003005024903055801b4080903801c002e000306400703800b58122411840b030b0000c00a50720303542e40200d04d0f04000b026a42c0c0700400130705000a1030240c103809418082e0700300d4402048000800102440583d00d004101da80b150002c0d00060981811a4000b00560094016802c1011000f182c40307180700100352200061000c11418 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 835435404 1250 835434154 835434167
    0x60108070c080c010621060c0804020a06120e01020a0f030f05090309010503090c040c090608061e22020726070c0603020319060e090f060c090103090212060c1207 71
    0xc0000c04910040d0020000ca00140300510342c40c0300681c00450f040d642d070704202d91094120038020542a20b80000042042028003c0314040c6016160801260400342c000503400c8141c2c1c491a4203100b0b00d54210041e520301c60300320b02104d0600320004c45d140c0395030070005054480d0040b000b1000a151280032030381010f0610070507010b0741c4000021400d284d015001554554406440c3e42001d02c500030410b40b1303c0c0c2c0c2c2c5002c0c8400c0070320195900340c00d880c80c2c114040d2031258041d001c28840c1003200d4074051140ca01c2d02c030900c202c00d0215900d500d000c50302c00c000ca40c140281e1054203121400040d02d2000e010084851900f941010b0300900c4005000c0d01340d110940c00340c3d90006015105296081142520940107941c00001c2c6210036806c0300c0c1c404a2040c00c0f5030345a401800701c81d080c4010407845e007105001050b40310580001410051800c1540e0031643e105103020103041c95a5018a42c0640d180e08208011081099040310306506140680e00b400d90400000000f00c51095070014030081e22400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 835436654 1250 835435404 835435411
    0x100c0f0815040207020607060e0307030f02010b031015030611030609281e09050d1e2012030703090c06050a0e01120209100c140705030703060c170c0909060108 70
    0x14001800403201d00400c40690710a403000da901c084148850f03000f280941c4030703014410503604010355883e201c034a80544010302c1c00c000c10003503916161074011140c80c0071a4003032200051007000201d070564004107440302441600042c8c400ea15001c2800c0b501c2e1913140056000300070845a03141a660f940507035030100d44058000d0002c050807911200c64507844c41c0c1110810708103500c0f500305101100c807006000c41e4250b9600f61240e52215024a2080360000115480740505201071217412800d900e0252031880d0700c40d5810b070322880c0300312050000c16045c0300c42092089600501503907410811001009008131442c140c4502d50040400101c903070080080b58084021600d868907007451040044d640031703030f002c582021030640030130484030305940d55000f01c1d91244a644824400000c24144000f40d03c1c1c0600c180d000942c010b079001d01040e0740c00500002180e91001c00807507080d0804404440039a010700d203d000a020b114240510341e41c6d00c601030041540c00350b41c0c241c801c0d07a441d0011170301540c082c3d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 835437904 1250 835436654 835436671
    0x120303090a0b070909110a08060402030615030402061312030f0903150b0a09150609080a0c1211030712150501230a050306100f0e070807110f100c0f08 66
    0x148107480014000c801481c2e800042410900d503451358403100641030b2880c28200075151407000402041c40b6030070268154010301d00f40c40071803c51070520b002c01d113941062014400c0608021000a0031951100b00712000400d003081404c0809aa85461358154100003900f18042003003810811034580c42001d245048a4202c40162101030080e0310420082c440054916001804014045070110392070280c0c49158a586400e100e0b9203213418001001022703550403161254000422640110f4000824542030385c500c07080800d4007039450314080c0b0500240d0200980c050180d07210004000c0c11440404d0311080c05000b941c4017080098240000310358090107450b00c03810119281d4490403104c48100220302102424103e44035480d080000d15000c822140c000e000f0351700c514203103d1303210382030b407050b004080070581c032101c60030301741c902420302c20300241664200702130748204400024007000744080031150103055800100c21064014064207040030f40b980171070f01c404050200c55114403400380c400c1055 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 835439154 1250 835437904 835437913
    0x19170105011505160f0503090a140109091103041118040309030b090102130b0c030c120304050c0607050309012f0d11070503070b0a140406020f070506030613090c09020a0503010512030309 82
    0x1641d41c048121602041c21b581c1444144038444098585404c1d0340050070302500c61002c0c41d96450001001d03060140c100c00c1c0303034505064490001c00e0049080c0e1f600aa80300d8035291022201e0b0000ca00b4481184101d514243d0a203414801803542144e0701c03038107981c010b00c0781c21318036a21035004609230b202d811f1840343c0c200e410510810640b04004050b0038150030181c01c0c1d1340740c01d000c2e11030f40c0d250400e403008100d0303440400010310042080800c00085006410f403116030504815845035a100c0c09403108180c1400942303604010100d43c01d0420711803c04102c0741c42003036020403a010a80e01c00020162601180c02550360111001c2d00151150898000034010b04415007012044001d64005140b99010f0100c01400003280744400f101800c040c0980343c4c018a400d02c0c8001829140c080554496805900204240f091544032081012241010464003190103041807074070f914241d602e41c0c0a814140c0c404200e91004580c00307401141268404c803103901200005400c411703120b1106840d00b00c0c01c0e500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 835440404 1250 835439154 835439197
    0x11130902090405012c04060b060d0b0307080d02102c01021b0c0f06181f080a020f0a030902180a0605190501020d110c060f04060f1d19170105011505 65
    0x45c44103d29074010300c41d10002c07504a960350081880d0350007802210041c9621410510030070f04003080600000c25040d4010071403241301b10f4010b134031001c0d01d80211640644070365043c80c6130400d03032042880061000d0406000d05005a001ca03000f90404d581c0c091103514100e0b80c01c1280040040c4452034a14000c00c05445a56058108001c96020710001d0a0a00003a100703054190794584082c119104a01280340d060040400c1c010442e0f07200070308800141c6d1040c4404415202c50f0810b80c0c031410079034140083e40c1d03491800000d103c950300044203007104d4611410014408042d82001d42114010b60b804041c41503180200d4100040c1806945e0041e0311200401b25410302c205e01400c0810f410b0380c2541c900f50540340104055a0008004650003440080c08110f5164800041d014010042c506018034001040b68842c6010394001c007a441050600040b180042e02c1003907000051110030340f000c00003408050a1406820240700e0040c8502240b040801d200c1e00400483d0442d00c60381740c00011011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 835441654 1250 835440404 835440479
    0x151c02060712120b1f03060f030302030304120512060603060102031b0f0d0201090b04030e0a0e010b18041817040b0c01061e03030c0818030303042d0b01091113090209040501 76
    0x2c001750401c0070540c0310383c00010100c1e51140c261001d1406a800346903607213000d0400010501c9150305100030040b040010081c0c1082e000152500407008071641d5903640c0b18400103e145000d241d000c24140506400442c00d915400a00d45410000d00401e40307044007000b034030603400c071101c410020b001c004010380000c001030b00c200d00c0b4140416009110228142d1102c40f50900d0b020300b41c0080c01100c03000503074400502800000c4048100d4215002c0c40304041e0110250100048000300030035003410f2000c03034070341a902c05050341c02505000280c192100d40741003509000c0c0019100d403400c01c8201d6180b6002c0d40803140d141310f0907690140c8403c03280d036040d41da448031b0991151420130755950440141ea4015601840110f016034000c00c0180c0c41c2d8119101c05094425a101d0b5034010f00c410805da090001c1c01800c1924111204ac2c0390010322110190360600c07a0b03200d031450781002202c101c01e0105060f039003640034040c01001607500304040d030f0700c8941d09551150103801314024115946002d10201 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 835442904 1250 835441654 835441699
    0x11a03011e0c052106010314040f0f0213092102030405030a031218030e10051801030b0301140f0a0c21020c070b030a09050c030303151c02060712120b 66
    0x2019180151600c164020485080e5000092141c403030380b041d00170f10040d903038103010700d25511101008040c1c240c00c06a83c0d9004d41907811200900c150300d02c1e5482000d560700e030040320000d5080c181091207011994a001070f02c464484c860f0150040c0f80e66403243c0750a1000080c0c03400d90700c01800500705ea4105490680d280e600c0da10044403900c0d00e60140120b0851070101424942c1e00ca078445201d16a907410806c41c2aa031903c031807504100b014001003d0001d41c003040c2031103800082c28001061034520010a0141c40e03508200c804030320316901800303061110700c40f07014850000050100552121600c084400840303585a17031040d42000240840c001a030399001700030f1801c078401210405542c070448129280c004546c2140d4042c3d550b81148240801030114416114040380035615511344000c0c00c0d20240d004080c018018090401c03200383d0103c1c3e02040341807144d001002140c458481d403074507028602000f01420000707004458000c1280005015161000400030701801c40201695107641e00c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 835444154 1250 835442904 835442921
    0x51002042904031203020a02100b060f2d03040308070e060706050a020d0f0b01142104031202070c0f1d0c030a020f040b0d140906060d0f0b0702011a03011e 68
    0x100d800300400000a075407022900401c02d2242c80141c1c1320747e03540394042d0400d0320b5108203004040c1003601d07005d407030f6984030200e9800d0320010034240d48480071190a9100c00410313540c401c0020384a40d2a54a22440600185201c1d0b88a0350380d00c085a900c4060071600195810314454014500703001c60000900c140e080300b58050601e20300141004251440d8905441c06201010b081551b1841040c02959010f15421404800042c0ca1031420700c0c3d449645d440200000c0310804511404000706003014851040752951035110081552101501e050040100480d8800e64030402d8800038002107036881d24480600c1e070f00044c00d8000540d07a5001c002111540700400e0702c540c1a03400c024401c1b010003154091710280c03448840058840c1074910072401280c06031040c019900130700c030007040011440020b00541c050302c113031100480c080d06880e004d42c0110311408001c209500000c10001c440d941580544c800030032103207940d4100a151000d050132144125040f00030075418040b4501200c04a070022000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 835445404 1250 835444154 835444229
    0x504020103090f0b01050103060f06140f0f04030605060918061311180103050105060f03100e010b0414040b010501110a1113060e10060905061207030e0f03040305100204 74
    0x1c2c00515581d460352040300c461011500125000018010345d68540706982c041c0004804400319103003440005045c0d4143c1d0300310704c485080c00040c1e24452211700360603648902c001c030040070b450316160300d0800044c110860724140602500c500180032680c4180001061181399400b42c074040c0c4880c3c0036004240030f030f13060580301e9450780741d41881a43c890740596000c41c500401002d410b54150719265003903c80190009206030f10350004004565400700315409903404458000070082e0001e41201d02425031441d0050744641350200c4000c0c02040c4441a500c100d114481c0c01c03116a88410054a5401c0e600030a050980d1020f1051702c0010242c525880000d00000c0080d0340d0380504440c64800d03501990002101181941c0910001b400400d6240703000d000c00b42090b141460822001c0381060013099084124201d0301000b15000c5400b940c00600c4401d0f255054450441c07c007107108d540d0ba4000d1000311142c2c482e14501c020305050a07c2528140c51403092008542e1040e44440101071514009880 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 835446654 1250 835445404 835445411
    0x304120e041e02120f01030c0510030e10060e0a061a0f0c0a050a03090f05010c080307030207020307030c14010302030f040b18060412091212050307270e09070303120504020103 77
    0x51100380b03565104004032408070760140c0d90b0401034032110000e20001c5d05982402e0304035801800010441d8078450240e401c2500c03c00b4034500386d11411805094440341c9808240a40380a00e02d0b0100c0d25049481645e030410114250b07603c4a80c00001194442d104000d145481941e0650b100d24501000f4540800745060799070806075824000742c140300f84224102da040d40080d0001c001c02d0f402c0083c4200034070707a0311030051096180c1400a003c00c0414040101100e50000c0062625170080e415140019006002c075500c0d15102e02d0100c0e2010003074084c2050440c0c203140404102d61090007107034483d44000001002c179403a1941d4000c4540c1018101c681110f06060104000041c03c00202d480b40d40142c000500400b13044001400082c5150808018001304080f50008101e4120000c0c3c194030303440c50425565600e020301110305601544800f100e214204041a81d80004003409100340c80c0c103007800151540721101700a84d9034403117100080101c0c0d100001c20310306906540c4099441030043c100403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 835447904 1250 835446654 835446671
    0x1202070e0c041a120a050a112a0a03051804140f0a0501150806240c07090f0621030c06061511010e1209180c1b030304120e04 55
    0x200d00306a04503209880c2900202c1e0820030f040c8888240e4940d0040418064645060310803601c0c0c90007002425400b90a44a402086100001d42c0c00000b405403485009900d44e610707203080181815261034400011028003004404202e00403805100e1141c0c076032905840c0c91100e00c1c600c0f03007003070350811102d41c442e82c0c44240700e600d5120078100a05c94019200306090b540f8282ca0380d4000ca83c01038216041c244e0600d45c1501d07a29030012103481d007103c01116040d0752414080200340e0003240c0c13200e00c08100f010106020213405000502141500e0071400107000101036982c4140072522035104000c022454010242e00c03e0140e0517102c100309000e8038009078a41c0b055242c00003560495840216811865000610300f030b94808078060400c604400240704840a0500c0587d4440c0840b204998048001891184541d90340001c54518001c50007050200e14014078040c4280d0041126130180024103c3d40368189031020049911a035840b40b26031040c0c001c0004210b400d0031103240703000e0b0080d0b40d40044 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 835449154 1250 835447904 835447919
    0x8061909090804092a0503061804020f10050903010b09040f031d03030a0e03061807060509121e10110307050304330b0409021e03070e040b1014010804120207 69
    0x300c81c135411030310040b60404817500a01c170100382e00203043d14082000c03e10a20074645e450020181207107415000801d1940c41e00c0c00065058910112065480f5100070180c03800c103a04000075003d40c4808400801101b40300e40300b0301c0001e1100301e4000301740b0380c003030849c240001c0d00806500140021940c0407480a1000c81d020030301d964014180040400c6d84004051040e160400c640760f07014030b01e8103000302c41c07401116800740d03256a54001e00c002e01c20302017038030415a161810740c101e101d40440c2c112440680e00809104445030106070040050180c21440c040302c003420300030301802c032080319191071565403484411900d0341c101500172640340f0085a049500b800d01001c100c1d01c8040303c40442c0004500c0d03c0400d400b01c411035440c89000718240484207015984480000884017901d040342c40000403003000080c1010702580103280c400b4100c405020500c44c4000b900c3d0300c5030340b40804401c042610340d04014400e00c000c130885d600041c84500001d0020703520200e84107404901d801280d0500d51110030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 835450404 1250 835449154 835449161
    0xb060702190816140d0314180a0e010306050601020a080409200a0f020106060e090c03040f020909010c0f08091b04020f0a020609070e091005060a03080a0f0806190909080409 76
    0x40103c20004036040502414048200940644d10101c3d1142061841950040d100400c01c01c400003e00b1004158000a048204400c00c62841d004100484694444a0103405807c080c0070a450080c9008009000c6500004044007119003060724641402c0c078201120020f00889828034801e0030710040409c00700c603914009810000200e4403404c041c0c5d400c4120003404c45050340d000c1020400300491320802a00c0303001c00f45400256503c13845540340d445003800d407002840408000d41010b0400c04100c0742d400194070207492007005540d508000c0800103422100c0e0803050b1540700c8140c0007801c400f4070b51164000d01c0c00c7c454a018001609007420f2900468407a0840c00328040940c1000382001001001442004080c0001c02120360306c0381444c032500d0790f0301d910030f1445803800341d41c81c0d022626070707960703075250100640c6e0100180c2d6441c4082c010050a640c1c0c24454003000c6503122001c03451b680340c601041030255071b4105010201c989403443c1c2e040a4000300300240c580304020440450041c14030302 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 835451654 1250 835450404 835450423
    0x31209030a08060a050a090e0a0519060b0d020f01050d1d330105270c070b090708031c15080606030f0f060606070302030c01060e0610030b0607021908 66
    0x40515140c0e5440000900b95801c020001c5200e0812500300340126501d841d00c0e001501d0303800c0c00020303488480c03c003503910b040703080c0034007420512807400040c044c40e140c0c0f00705c0410580302c0c040902100180c402401101014604003e50001d0b144d0b255a00c55481880075207000c400141000c03c1c2114403590341c40c0130000d14004040d00d85c019402e0500d0100401c1200490f02c40b0104038400d0340e100c008852060400180640c034400c000360180040d42c0d00408025165000d5801d08981ea5400c1c200201c0c00141c0c00b054086179200d40c80d10004124546c0418550b08032076403080594035104401c2d50303250300b401e0080e1115203156070b940030ba00d019801c41d032180c5015085480040080d400c00d40100b601d44400880c0d000d82c10360140c2107041910394040360154101e601502c0c41602d4488130710b416030850107603094910282d0b281400014000700b00e4072181d070107018152410002d4600c0f18104074140c64803040602d4008004211000042c10003c85820b0841d8080c40035425450322441c0490a0aa219 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 835452904 1250 835451654 835451671
    0x2030916031b080606060406201f0606021615030f020d140907060c030e0d05100609060b040e0f0c07021203090117010612090809060a050705070503010c09170312 71
    0x8034502e100a10312481c1e81c001e003a00c403004040c01d19045000400500c0b886c000c1d102001b01400101d903065076105c1208100c0d5180401341c900340103c8080000e4040714080c01d18110b01e003003c80c00110704d400803c6035980341c031101c42c1c6030f40c5580c180441d4442071280020500304065890380c05056540c0d0070b10103050018580840800d04070b004101c0105c4210780076003821560340051504105141e0003004409034554141010040340f02d880c00010000300034050060454082c80d03842e4082040d655010340141c03051000c080109540791a40040d250180340940c00d0141400008a2401e80403001e51640c0000b00e00400d0f441c0000139404101e011611001101c05030340042084041c41d0b030442031280c0001045200c05099602d4810000c1c014004030301d4900c22669196000300c24404441e048650424001d44070a07961b001c0c03460010520b910104e03094540d4040c8a2010480b4581030007803c001080c2991744804680c100510300380402544540783d41c040c0701c100300e0340d0350540d44801e18900c10241d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 835454154 1250 835452904 835452923
    0x10020a080a0b0604150305070203251208010f09090c0305010c080709050402120103120c05010e0f0f01110405100e0d0804050f01020718022209060602070603050709090203091603 78
    0x74600c01000d41d081d186038203106403800c1c00b091001c40c864070001006155a450b02158075119000160f04501c03034050003600c04000e90505410344003120030140c4da814840c1e0444040301002401c1124041800c1c010b604040d80841d00800103101181c014100840c01148001c00965880d0b542900f1500702c0d034440004142c0c0c00341040090f0340c0001d0301c4802400c00b61415490136042d0040981450030500008007005c4142c0d4442c0e000c540b00344920134245921100811a900d0564052542e40481c075140c6507540c803d4001002d802c22060107030800550301c001b4910b040504207010007480031b0485032000100041141c4c000080e6850403e8090028000c80e4599a00e41c100400c1c0040030121a203514159131000c442046034101c001d5481654220f400801a00d0707170f003072181080c0382c0100d0072003c200c40e120344840131640c4805540827604558080d02280c440310f94070390341a8250342c81121840085070346101c08200c80b025980045a01000b8074081d83c55100100e21442182c4081d41c0094072081ca1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 835455404 1250 835454154 835454161
    0xb150a0906110c0d060216050f060610170c0307110607050403060c03180212070509040b0f1608040b190911130b060403060c0e120a122f10020a08 64
    0x3040300c030b007001403000032002d802c6074124800400d2070105030100080c81c0650003c0c0c55811a508500c2800641e9404010303200540b05056409588040543c2c545110340401e0b03c40e005070368085c200741564096501c3c01003240740d40342d4284031100d8000510000c00e1048c98085801081c0080c00391901c14642c40d2101e5032614211304103c4120341ca10303a159000d1602d04414810104071400706151066412541850711040e1552034506000b41d40d0320a58010300c0382410711003000511110680b042151907035040c6641c0e52aa44c0c40301c1c04801c40d0610700402c04075070102d0301040300f41300015840384000b003010343d1207a00a00c908040f5200c840003502d07454040400940f80c0d261209071282e0b01c0c0f01c03006003072004041b2100059103510442c0b2000303040c0da540d0702c035041c15079019a01203440e0280c000d0421584400c01c5281c9074440c40e074ac5034220794890340c0001000c5007501490010746c0c0f642c4014030f000301a41ca4030b51046e1a41c9003c5031340018274803038036030101509941c0f40000c25030102150b56004542c01c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 835456654 1250 835455404 835455407
    0x60f07050a052a03070303020306040f060308040b03100e010311040e03041a0702192c0f06060c070f1211040203010303050a0c08161a0708090705040b150a0906 70
    0x4029025404204040009609166108050301c180040039180310b0031900101c00f11855840d415481c840c802d00004c2a403100341030301607010f0340c0301c1d10054a0600a6000c07080e01c01d001c403499400020490342c0188001c0c040d016108020f140d00140e0101d84400641d00e484590342250001d91003110000f6a59441c91002c0c1020700515526111a1006500303143c00c0418014141c003c0d04c001d1181d200c40400c4590a540d9400c00461051140d01e42c00240a92944680c008019017007002c4031000b0110320300140c15908003c001c44c4189400c2180c3d00d110b8941c1010010643d0007140a03c401d071250802c04512800700c5003025004140400300c000f104100307032800075000701c180194640301d01c0c810300041010a400c0030458550034501c1c60110100045460014810b014102c1001c28001301c2c840d40500308180e0b01c416000508640500c02034036583c04404881d41c1c101141c4020740b075000b1480400450405030480e1120000041401c55031214503807641c1c40c1034001c0780c0352200140c100d10040200a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 835457904 1250 835456654 835456681
    0x504090b1806070801150926070b0306031b030a06050c0d0e1203010b0f0c0106090c0306082d010f181209030804061b1506080c121b010201110c06 64
    0x21034001c000e02aa89440034000c4c00f40b490511079124050303032001e900114644141200c4010b401000785030180000c0400124100004c00c1c0c81d0a075403031140702c002282020402040d41d2003800300900800e03440007102a282e184c80740c0030503260b4051040021001c00600c660184c3d038450394180041541fa25100349400080e191214601203058001544c50035400c1c094800301c906688403040056520414136028020501c6402c0300401c003540f91440c0485d041e0219001103070074000380e980900c18103885600160b103c00d5034040070560a141c0046d00e05400410818605105101d000000b9101451445c3d020540b00c00c00d070305003510042007120f0410401d00f10b901d04211050341c85c040208504550740c03519188141d00500041c00207501c00110b02148001851030740d558000f9995841107041141000500254003d03000c07a4003c0c0d0100701807604140c0d031b2140d11001581e00920300c3c68020f0400c0c40010800c500b0041c1107548410400d42d1100001c8028498507252400800c007510f0a683e00307a248 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 835459154 1250 835457904 835457941
    0x1e0e011407020303180d140d20100f0618021909032406210b0105040b010903080c19050718020306011e0c05070b12010b040b0403080a03060504090b 65
    0x1031100303100510150b1000000da4074540350241480304004006030000d078070002c1506000300181d91113640200d5680011402d0480c078001900c584600e5014140740002416510100594550000000070100c20250304401c074250484032001410b1511203103a403d940308800300906082d81c0010700042000002c4030721203441131080c0b810308403850a507502c55045820012614103500e00303440350050f00440c3c5522540c0140b0700c0b44844100c601c0b202408110f000d40300d50040c4c4145c2c00303d000020b010b0800b80980038811005075941c207a0103003559250358480c0c100082056441c400c4100c400030440341d14028184007406403005040c030b01e00c2c16201c80f1424000310b00000c0f0444c01401442840d0341c0184259250345c21107141c0e185620f810000440300070142c03540140640c82010400100d205102004200e800081d02102100e03030303291095410103124520454108050800040002c1600c88014000001c118600451241d0740e0300009070a540b042e6005880480c440024000003a07400c9030914178 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 835460404 1250 835459154 835459187
    0x12051308060609010b13051809241303170103030c0506010b040f051e030a0b070207240806030a061a04050a05061e03120403060b0a050316050d031e0e01 67
    0x64601500860f15110062007901c2e080c00d4041603000010f400085040003400010f00340e000d00d0354083c60400d201e0300c01074501d055a40102074648860900359420401482c1002c82e62071902c2d01c60f6034080d03400031160a0164204103403c140381040d481ca201d6458000c40c020754030020510110308041d800c120041e8002c0001d44401c120800a2a03042e0802c4400c507a0211034401800c00010398905014401a420030b030f044c01065013560030008901e84a600410072030782120540c0380c40c0c14074404102102d15101903107101725009102e0242c41a528a6070120740907042d9504405642d848005803004000700360111419042c82c0b01c6c01d0704003445030a0b40324100140078481400c20714040307600d00d0718201d41a0031038207080e036643d01c00e07450810064080c0081c156902d0340d01e41c0d503824400010140410700c0c3d80704080c1c948002a00d854002070f62800088080c480002c003510302070801c1025007080c2c40840c1484080700f6510074501c0f490f010340803140442d440b0000c9100170b1000061440c916149500c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 835461654 1250 835460404 835460413
    0x3010509030c011b0e040b1513290d09050703020604030b070206060603160f14070f061b020607031e0f0e0f1f15170a031706180403090312051308 64
    0x82e103c5e034000200e010300c01c0281c400041c8554642c001c034002040e4010b091210203000a1040c00c45c1c5400c0700e500c0200c811440d0140030b907111580c6501142e001c01076075440a8036040c02011180201c1d030340000701862003001140c9806039660301140791508150b2094a82075405010050803c1d0180100e5070f1007a811200f0034034524101c0701d5240480768641001003004400c4801401060040c04840300741e001c80180382e500c032403451610342d810750042d8004503445402e1001e040085807032038102c040340f0740c5250040d24040c1c0d980b110885c0200058404000110a5190328480184c0c1612458458100b16100801c4d420351407418a46044a101e90301c0229900c603021002c0c0082d10740c40707500a2030070749140204158030b940581c4016151075400000b18030078407405661041500056901903c1d2017a1540314508080200b00300481c041100d06642081e80b0884035454000026007865000d4481d042807101c1039180d40320765581d061300a10a4020034800240c008403400640d400c075004000120050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 835462904 1250 835461654 835461701
    0x61509040f0b1509010b07140a08120415050a1b11030d0c0c050313030203060a15050603090114040c0830030402120a2306130201051803010509030c01 66
    0x450007010104005080030a41d8070200711a000b20100e000003202e801014801256110280c5401030751003a1021074050386500c0320200162000b26030101180d800c008001c0c1040c41e016082e014100c4010710172502031044071944d860352340c0c041c070505000c0c1c1428080010074a006c0c82000c40300d5001d005915092041400c1200d64614000080301c0c03070382c541d1400218100b00c50060964410114000080940c00041840c05001e40400e01020072a40206d080b01e0007600c429490b4400c4032809851814034641c0250184160304003500250340120014000050404074405903110204050f1012070b00600000f00800100000700060109100720b80076042e149a11060300c0b5072103440001d442e01c0d444030040009025980e40c0a0b240744c44185d081c0c15030307000c000f4514200c2000d074070403040d08880d2031540390300303a940c10000502207116081000345050024800d80040d9403d07001080810b080a0307100c1601007841d1001c1c003401f80141042e600468132060014042030070345440f5041070002501013100c9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 835464154 1250 835462904 835462913
    0x201111515010c0215090d0f081e04060c0605131505150612060d02150a270305191407060c0b180a0b0939090c1e0d0e06150904 56
    0x21003e50468440046e550780c04010102d01000319650002c0c01d200f6042c0380035020f0060303c238018100106600e18110342e200050b040c144c0c19010741c3c0160703000551061101400a14280e0140760071900407a1141c014030051ba880000112a4410540d8125202c1090000e0100c0c40880903140c0343c812680381c0d090400100403000280002000c040c86203c504180c0e50640d220382e140c41c14071b1a01100e0302a070b51000d000c4041e04002c1500c541040c1680c0f050144070300c40c418024201d050742c3d8444040d2581c44046e42a1074401201c1034421707201c6101488030312401c0f0504005c640c00030101a1581480c65183e4140124400c0d401848021014410300030020a00f001142c681070359507000c03028608a480303105d5458503018401c0c40b1440704610640d0300c100078004c82101d040c1e600e1744c10410107661140403c00d2103200c0e5815540020700030428400d0b00d0400e09503e0501e14000d202d0784132581015548080e030400d654880d007030781a858100030240f191160f00c1c155041096681650700d2941c0e800c3c42d548 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 835465404 1250 835464154 835464169
    0x90b480d020607050909102d0503061b0a030e0115031b030506010e1f06080103230d05070501020c01050a05060a170a030c061b0f031406030601050d0201111515010c02 73
    0x91710300c941007039030001d2035034150400c03c14050004c00504210303145610035800e002280440c8401040950044000b800b40343c005002c522a02003100803808a28072003030815200d1304400c4582d010b2540310540c501c204c0c1d200340318400d00455040313006813030545141003181d0005138103503a11045000c1d60006101140d00060828115901c001d5003008980c1d0760010000f280001c142c0c0000e4042090700001221030307200038003e060700d0080712180c1500701010024a001d0040000c000540e80100000030503a60142c0003429604e40203030009440c203070340b180d01c40c2d0841e00216004552582e0319001d0000038142209450041d05e103149003026000190910303107541d0520b290740282049443d00c10202048034541020500c1c0f2901000552035084099001d807500c51950881e9000034036001140e0784620301c0301c540038004c0308090050b01c0140d007000184403401144c0f4505906003d9881c0b00344880f043c0400a11201e4180d588075400e4500300b1203140328004100709031480c100020b400c414005030b50780c200f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 835466654 1250 835465404 835465417
    0x902070f02100c080f1b0d090302210a0b1503030c10200a0909050c130513021b010606090e2202040f021b010507090b480d02060705 58
    0xc8240022020b07224040312054000c0300014030b07031400881c0c4040d101417940d024044520307030031b0800700b400c01c6040301c0c0341c0c0c0d901400c2c0b0300f610000301000e504101505000b00c04000100b00c0300c00540c01743c245448420710b00740e01c0704000c80d1204140702c01c0190800c0c488051102114084016500e0046207000032a0b80d1507a00b401a4095682c4050901e101140442c4085e012000c8400c404c0c0c9418012801a1030f54079244251050507041000140c100034410088489000c0307034a58103803400b424001849450096a80e02580b588c0d400c1020080c4150700501c0c81d01d00326003060011035120700f0f00700000c1c1922074541c80805228038500611415507010074840d1020301620462401441c00342c0009400345c04030ba480b004420740300098410b801100e0140b41000604070000078040741c1c40340c00c4100d070091100e10030700c80400c20601000000020400c138451441800700c07204109421202000501400200403000926000b641c0c0920700c002c3c14000c002e9000d01c0342c0054010f038900501c1c050418407580703 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 835467904 1250 835466654 835466659
    0x30d020622082b14040b0a051006051806071b0501050406090e0411060c1b0603040b0f040c0e0705030a1a100e120706030b120d02100203070c0218010f0902070f02 71
    0x521502442e128802c00c10b0908034207a0b80f061040f54140d0711143d81800d003d44066136004000e0340043d18224041c040e440c003800d00440115040c03031818004071450340000b800a4030900104654002c41c0d0ba405000c1c00009000b09501110002c1c0c42191100e205566403006042c4201844100042c6400c40c441f04c2c115000c00725920345642e00d6207810040071031041c54075640010003040b020444000021420b04040c174903115000164608010011035000840740103155488200008422503048107806070040d100e11054060b294490a4100f0100310442d9940000b039008010403140000b01d000700310807500084080c0414030740388000310346208481100c100a0044980c8100c800380c80750401d0403038034402d600a80701c4403500e07680014042c100309a401071164403502c0c49c501d84448045180a000c40150300100f801c54001c00e02d410294000510040902c40981c83c3c60000d42c46031b8040f2410405043d00c11401076041503010686803001c0d0f0014829507206200c2c83d40040c3c4000b600307600b50f9404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 835469154 1250 835467904 835467937
    0x1d04020418060501090c020f01020f0301120311070303020a110609090c130f090902150a08010509101212030c0c0f14010e0a0c06031a091b09030d02062208 68
    0x51040100001d100325030041180d8641000061404410344c4103d61428840c4c0c25114000021503043d800c2c0d000f030760311000000504100401056200c45c5100c00800d210341401c040307284182c900326041c030344c940d8800c1e00947c00c00d80c24081008030004a2042651080b1400c90804583c00c000c01d00c0c2d090001c200d0030000000040294070403030490030840050200401039a03485807240707043c40207804420f0049019a8040003564840b00d54441552000e07a001e03510764819a20305010000d00c9080507080024050201c800414003921084641c120705004e091048011034441c0740013000c440206240e4000c2007918481c03440054801c6c0b610021803500082d00c60344481c1c024500394018000c0389160307401441110f680902300300c0d0f400404411501c598408005400b059400205210400400107901801e49000120744509803110741e40f50100c0c0c01c10050801c010398012034500501c20009002581c403420400c80308800300144c13034072250326200043c0140d0440707541c5c5041c180208826180040700 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 835470404 1250 835469154 835469171
    0xb0c0a03030f0f090501060815010b0d0b0402040b07030302071b060c110f190602010c030c0804060e0703170c101a120a0b040f110114091002010b18010f1d040204 71
    0xa55400c20039202500c0f4008001d101011320381203000349218401c1c01414001c85c88100f0190014198040c100c0f143c10030b09502d4051071509001c0284440e0803a10340c090340c01e01c8040340d0b03114040c015003065072190720300503130b40c3c186e43c02d040090700031754005c20302002d002090a10405502c07141c810041d5030721490103060200640c0010b418030500e0500150080001c00485507042e44010b03002c42124500d80081084401105044003551480821800800c4594001c240000ca860740a14a4001e206040d01e400c90b07240d03564034801185e51201030715008004101c0694159041c442640e1a402905080200e1080d640103a03031742143d20900d56204041000d0a5000c1034400d01c0803a07031165000403921000d2500307260409c11075020320f0060f070b111070480481320500e501502d640452542101e850a043c40da40e00200500103400d0341030f840440d500da5000c039002ea2a0040000941072029001c1c1c0340035814540030601c011310642c0324540c18038820754400c080705414800700d07420607010348010401c0c42 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 835471654 1250 835470404 835470431
    0x140913030e060723010617030703080106111c0203090f0105070b0402240406021c0e09010e0a06170a0506070f1209020103060b03130c0605072411070309030203070b0c0a0303 76
    0x1c03881c80510034414100301c460136080d44190310000503901120710340003035146181a503550340e005010b40100440e89010051004d540180a6106241014000c4444d01b41c0c24110722540d03207000c3d242200c0940e00120701c000d19131428034403041580ca4286400c0c1d007411802d032601000110041c01c0a8042e00e0204064030f071a6003403038600780d2580e003448141a0359640d03d220007984d680c4c032015100c00d02859070722540b010380c0c0f144a0400707044000030028407950742840c2d00c3c100b41100181203041407980c5d506000031800386011214100304003400c05041d4040d03040c2400f604181004102e482001704030500140c0380c036000030003041c003d5146c9100207a0610b01d403005800406031070f005a1809c94000c810000c1ca540e0030b011042c80c0902c03656044621661703807841a2458003880d10014508181001c510941104030041a54105040031000c150014070501d074100c940c0c0426800d50015000c060300b80150f04082010b0703001403801c40701030303490940c01d01c5d0031540b5100300882c01000c154035810500ca020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 835472904 1250 835471654 835471673
    0x190c0c1e0b0a0e090424060b0a110709060e100602010b010503190f0504060f0c050405010c26041e060903080912100e030a0e030319080c070c140913030e0607 69
    0x1040c01400642c130070305040c10031200b0800d0702c0304904018580d0700c4000110912500410307003180c0c250342000d400c19000350320990b42c81c1c00c180040d0010b44240d0000083c15032403800760700003c10314074404070382c1401c00e0154425201c1c1190420f0041d0383c1002c50307006650346e0242c1100e07031080120444c44070400103e503030760b00030780190250030050b54107201c14001407100300e03800217003640d2000c1c204005090314100180c0389030103203100d60350114911040040101d408064018a0310f040101d100c64580800102040301d900140c2000310007480704031426000307107900c2003a80301030551410990394207032460b42c45150b2845460030650042209000c0070708050700421100d1003691400f9010b0240c04d049000c07056880e00402040d000050380d444180d6081d0070080308071121890300d009405c6c1c082241e68000d6540d0280a007000f08011000c2103205e010642d000841400b500300381a00c03031240703845a401c1003e203030005003e64012580102c0040000b0350080301c001204c2e0b405641094480540742001041c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 835474154 1250 835472904 835472927
    0x41d030406032903071e260c22020f0f0301033807050c0118121b0c0b09030a1a0402040b192108070b090118050c0114190c0c1e0b0a 58
    0xc0b1800c0029031708605103107a1f01070b1586001012030b03814540e81010009104078200001d1180352102e03001c0361001d8190b80081034408005080c00d89030080380c1039400c0144c0c0c8240d105454000781c40e1044004070394030000c2e01e00c010650702c295070f8110990702c10756407a0a40180a0710b080c00400204688540000c0d042a000280d414604030890305170760030034200005418110000103070300000140c10140945135a203240d26004041a180c060030300500401c9903000c012072560610032096000002142200c121100e4141001007034028181803050100f40c940048c0740c41d00c2200071045801001c11500c0500c011641d00400c5039920071003000300c4500d094240321000d042850002500b205004164000b540540d6a01c2d00030407400e0075404094403031902c000ca00034040e40005480300d0142d0312070100c603940c1414151503145810300d040b40340101700100324002800300c0c04010210080c401318440080091584841141001054286c521640200341c0034a44100001049028485108007004c018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 835475404 1250 835474154 835474169
    0x112b0b0910030201030f020c071809080d0204140105040b0715061a1b07081c030227040b0108090a0b04050c0d0b010e010603090f02041d030406032903071e 68
    0xe540c18400c0d06424003050310701050740840d040441d100350001e29031003264841c007941c0b000740a41c5402c10201c10108640c4680c0360241a84032050080843d9504c8002c0c81e020404850040c0d4561400741c140750f01d0b890162000d4103111051000304005c00090080315000c0360b002902c0c00f181c9240b8021071000306041e030450a00000142ca050300780b000d822005055200001d00782072041d40d08038001340d5903410580690900368004d0005101e0690300611120392480050401504100c682c80c02c1a413655108800c138103414180b06440c213086c0c2858401d40810705400c2c6030521040c0303000d102059441a5014001304107460b040d0025060200900020012007401001c0390122082810007188800b020b003e8a00e60007956000054080d000742705020005522000304030706011103808100091070340001012103000854440500ca08c0f0500050018286c1c1d6200091110040c007202c0e2405880e10f400320600e0200e4415500d0300741c1d000255202280c44281a141505081003d00c22400b107450b80000c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 835476654 1250 835475404 835475419
    0xf0821010b07021309080910230415080708011412010f02041e050a151b05100605180a021b0102190e010320031b0715112b0b 55
    0x1d1101038031402010494000ca40324500000444401d008072251250002e0070400c0802060003507060048400403020607600349502c90642442010b40140f109600301411064002001d02060040c0140d02084410b00d01c3d241d0528075200c2c0015040406c1806410308006000b661714459944a0200c40a180c011100070700c501d03034503800840040c0d0014040c003403125110321800c1b128200d14400d1001200c0004001440003072516945d901c28049038002d10003000060441101107444480d100348500b07120b10000e060801c0ca0901030821211240c00c800d204180e40b070b8001503220041d0040503046801e440b40140d4036505004600c00f001c0050011000550020440e180348040c1c401e1140c801114680b1170080b81c03d51500110202d44c01e0b03003045211144602c00c01c802d926225400703964040404188141c0d0242d010b40306405079080860304841c1c0514810204030f11502501444a503032030192031903401d0060710743c00d070340c02d00194460403480a281698440c4000f00d02c0d0304003000100c8040c200d03c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 835477904 1250 835476654 835476659
    0x20303120103020a21020d1e0b0f060d02010905040e03071b0303091202090a1d010207050f120c0607080601120903200601080d05090d0605070203071407030f082101 72
    0x221030542440242d200c0d400420707000400c200210400700100d504034551507144c00352a420001000d801c0031040da40d80700842003d03240700c1c43e02480c0e003240c00d000e4000002a480c2c1450211011100101414042c2c10803800140050f41c1010510050724030884002c11042d020400031847c5006000000c1e101541e06405451a03800c00d00c0080b040e00d001c1d0355080042c68989002e0f00001030100d50081d00240d4080015104000c5a40b01440280c114002c807290b49803a240000d09a0b001214180c2c0d01d6003002c40c14203a102030801c9100040c800204080b804c06400400c4280c85a0000302054284980d0a0009401c0da225048000300c6416401080105401354240202a040101040340c1c54a1030071300340c50120310001503118100d520520041405200c40038044426802481020303400c050a00240000240b0900685104620030750041d84c45401500b0b000140c031403020761468064200e00f0317040c00418050310141100035003000800d035407a000040513038082411003046541a55107503001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 835479154 1250 835477904 835477927
    0x180c0a06031a1f020f060f0f041406090c01031a0d0305160218040501050f0405031803030c011416050f0915090306090c011d06040e0718030b010e1510030f020403020303 74
    0x1a00b640143c0d600315850443c03007201c45980c0d0031003500c80c085481030501c00101d040000d65862079001e4800e0103003000032031080740c04034074003642514032400300d800112000c1920350389072042c0200342c16511212064151034002141d0003003801c0030094100000040e02e00091040c0c5000c12540340c1d40034140f0340707800300c0100d1451b80c21201501c0480c0c40d94280b502003400100324402d0140901d8005010b1403821000d091401c040c130802e0b90303205426001c01d10140c29200c07001c1c460440162854121840e43d840d02c0100c141c43c01c0c100460034824031000f0301030f01c002c000801041e15021082075074403014041808040501c0c40c0281b4184947c5445036504002c12881d0200d43d064032170b03c081c0c07034151112000c08000c0e030700320030011003058102105200030800803820f000d2007500000320781000140304031694440c5402d51182e80090b00c0c1c0180c030700010402d038200c1e10035159100d81d03480e0300700060051103800900301160340b07a4003504150301ea05216004c20000d038102c60040d580241100d41d030382d0b034804e003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 835480404 1250 835479154 835479199
    0x3090706030e0d0e1215040b091903020c01080606040305060403120605010311030f06010504031208060118120201111606022805030d0513021305180c0a06031a 70
    0x281100080c1000c00803182c1da1000944030080c00c8158440d41c2015180c1018044100c650300700e902d00328410030054841000301070041500a074011a218081351030106002403505142c00844924001c00383c141401187e40403442c651012400d20380704030740307490381e00025595014540010f402c502a920503c402c04d600210480b000102101c404d200050ba00d200540849039191900e0640c2d84080000442440c1000d5500c1e134040d0f8141811800c082e02ca0b281d4030b54910412840c000462101d2051001660300600075841070a40c00980294035420401400911501108001c0c14887c545108280030340701800039a001800f040c0701010740c03035940ca00081d90b89500078520340301c401540c0c0c420700300d81c00e44182c41c212480d0840700035460300b2803548080008100003003180b48a08000c004207801030b52285a012800f100741c85000c2140d09100c4800e4142d02d580c8070049510754424520002c0f2500c0344000c070021200181800a200660180d020560350041d454840e4080011101d0b184400c241c800c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 835481654 1250 835480404 835480409
    0x1b0206040c0501050a02072706031505010906050a2702180a082b03020c030d0203070e0315150609040c020a05101118220e0c011d24030907 61
    0x400c40c162056540b001562030748641e02c071020050f0030441c020b1200000000c00d084046055483e010302019000041c001251078035081100c50f2812603410000c0911140602405002c0b001e404002c40c030300e4600000c8510716948154030019240000e10f0203000404d4440c0c1802e042861030956035a91304103407a5a041081e902c0640c8185d00c89070300800c60800c0022007000c81c00512681d44085100040c6886001044000c5042016000c020080740044240094a45075601c043c0258890428080141c5080c0c600c503103580c017170b1340204403d8440c403c8450440c3c3d0022210906c6840c000d8000c80403d0461041d02d242540281c18000b52071407440d400902e14146038040c0c019658020f140108000568a595245c0702c0c003c00280302c810201094101e03202d2007504002d2181d800c0c2580800602c100d030180d40082d16000d50790364540c02400c1002d010114a0380c0003460500142c5004100c20244d1200c3e00f4001d80c01594000300820a202c00c48092243c03480d0342c00c1105403a8070304002d80d95503c24060 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 835482904 1250 835481654 835481663
    0x8060709090e060a051b13150224060f030105090304140108100510030608010c0f02010b030304121b0b0304060221090a0b0c090d030315080c01090b0306041b020604 72
    0xa800041c058600d200c0c080109104001510458840701c403c140640b6020b41503004150121601c00342200044000b08841010019032280052404110b8039801d0840b4140030b055400c859020701101c8119095480c2900214441e0806922680082803032840803080840e01580790a052100164001001d0411603049400d4400310444644c01120405010b450542032543d4000f01800f0a24040d500350040aa41c1e240004e9407c1e6158030712403c1d035400b00246130104514105006070309a081c041c1c00f1003e44150000d510342840d14902000070700710180003801d80c003040707a0301c2c0d5a06418400322400908000408a440342803230708022000713510a002500c11420020f030b007409048200d60390544034a40c0e240107010780e144691600c90280e00002d012100ca400d0070062031903580e550310b0040a50500070740d000204c0c01c00f0045c400301030400740d801091181c3c3c4241c411104580c1e000c02c4580035241000e00b5281c8039103a11380814007400c02000328500c2122042148010a98001030241c482d83c001d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 835484154 1250 835482904 835482917
    0x11090d0c14010504030215070f0c090504020109151d040e011112010503150a050604150b070524071d0d08190807140a0e030303090a050609070f05040513020406080607 73
    0x35031006480c030741310b60f1200940128002440c10f92480014018086440c0030302403032181e40a0b035640320308002d941074228819032640d46050009650b0300540e2003014251902c01c0515000e51480b02900f260004501c1c40e4144000849043c10ba032181c1e00824980130110000740a0782a804c1c0b10761129400071720344640c410b0046000007505140c0002c0301c0760b18100c2a040750301191942803c100c040c0400070001604592507441540c95862000b5500c00104002c102d40c0d900c6041c070349002800c00e14003840c8403200f000880300c40f050b006d80c1484220b400c441c26061007a442e841d2011808944a10541c51030740c00201e0f941c0120510940800070a558880148013400c07805402c0d1081d58070080680e0300380001528207450351220400400240044190340c03d228980881c4040042e10352340c011610040f00da004041d0302810008100f08054008540b140a00401814044000d20f81c0803140303d014410364640005c00c4040740255840f01c030382074000d072052001545a40701a5030712801030b290781d0000340340e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 835485404 1250 835484154 835484189
    0x30905010f0201110301030807020609030d03050105030c030a0b06010f1202120a110a09030803090708010e0d092301140c01020d1e140a0203060a08030c010b01090f1811090d0c 77
    0x1041c40b4004a104c1030900a43c190390841e119034900d50005038040340c01c114200720035a4659010031020404a800c0e0394042501d604000a16007000440c81050f8001c2d80420980000140400c4450358804400c0c6000681c9541602c001c1701c14502d24000c42c3c81c0c281c030001e58240c0018540e0790481c42806182424005000c0d80365010340c10b44217802650000501c80c0ea0140000384140c00250f0b0440502d204803000306840e900e906003140e8141001d040303183c2c0980c0c20205c00542005202d80101301c1820704c0c04007081201c40300c0d810300024003080ea0400c00c200c001108920100001d852800a07958000c5449001c589680d100900451301c80355a8074528100e008004050303070141c4d21030307181000c500078201e455048005000c0c0d0009007800c1c1d40200340403008a58444200040c03c404054480080303602501c50300090404482504008170a03c08800305002c1c1600700320651920301c111301000034a200310301e1b5211403180624142694403d0504961a050100c0200d4480a13640708c0280c4180159 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 835486654 1250 835485404 835485407
    0x41a0d0f021903290c0909060a080313030218093711031203010506070318030605270606060702100201110406050a1205070e011209080d1b030b1e030a0c03030905010f 73
    0x80003145d02e8600340303408004903002414140c00c0d440d04400084e01880c3e404c2c1d11440c505007507802c6071800f002e0007c0e11490400641c039050481d2032601001c40005201c40c1000d02c000da4980b40c00c104a152082c980e0040d0f101c05420402031111082d58000401c0359140080c03601e801d41a403040c0400c0c0c400e00c2500285050300c007481040340c1c100d6400030070080c540051558180c6030000140b40034a041404000004041000360003218840c3c0e04140c1004e842034484e02e511085d1a4010711400c3d8550f00210422a0585032a4115105640c04403900321461403006401c901526403000c540190241c0400c00140003a0424051b2030303000400d032601c041e15181d00c020042160011030340003001556101c40c2c41d8065010740c40039568885110307008101c80000e40c80d03082035940009210346500d075866160b106035201e041603421609009240500c0300080500005020000c2c90f07070004452150300e035052100b40d9003003004032102c66000d85410507865881c2000f0f41070300090f01c0341382d011565900551080c01e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 835487904 1250 835486654 835486733
    0x18041103191401060c0503190c0201200703030809010f060618120b0708180f070509130c03080a030207022101061d0a0b0a05031b041a0d0f021903 64
    0x101080e480340c00580e10303100e130440d6901440541a03500380010811455858580159841624001d882c3c030800100244001401840320014102a1100072452138024031008601001201d4040c600a14191590400b040c01880d10805001075946000000210390b138016505c45582e0010030203841840b076507121202407036051103800425416061000901450140351400d4001d041c181054080820b20780030b03549404060031044840c1d90001c1e201704002d02e020440c882d403182007225000766001c03543d940c0302e00075104c40c00003c240900105004030b00620a50540da4515001486018034065000c2c02d1a03182c1d24042258809500740740d004621300c2241c020054041d1040c0f00c14050a0303036204005070040460b4450641e1205240100055903501000301c24034619110128140352001041003004a498082c0d039040305441a0400e079691340e0700c018480d6160354102c01001c1c155882480001e803614a0540c1011022491400c00f000b8000344020001c1d40c1491280f0340d24042c45a08150104c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 835489154 1250 835487904 835487921
    0x1090f06120b1e0c13060e01020a030f0509060a030b0f09060918010b091e061c0609021c0f1703060a0303031e0e0f0712020a05061804110319 62
    0x1070040719000400060740d000d0041c3d404916800d442d0034402e52400004000d40b42a500f0203890070001ca0380c080c803101c0c090041c4008003030a04001c0340081442c00040c0d11000043e07070240922030f11500d20b52443d4012021692084c1000f01010781d90040b0150103402820300311f902c64001c10381b03103240c1215820640b0f9418011000100011030b15621040c1081c0c40a0118401005654131090082c0c52910361004050003881a0040c6607004c1d20075030b01c5441d2400c4000e06485c8a01c0110000c407513011198200c1440d4503420440100e00c410241c000302e070a400184181c0840d201d4641b581c6800d100d064001104100d2117816031880d14103c0110402d003e01003a680e5550180c1c1449042000a000b0350101842c14101c40c51802004a400040300840d14100500c0c803c3c0e82008282e07400002050004c3c202600703001c60412280042c54010603072402c107a00400380291400645041d650310240007800110300d0080050091103807140d060709160700180c48980744117860103650309611510340150b181 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 835490404 1250 835489154 835489169
    0x31d0609031b010f1b0f230a03020c1e15060108061012110901020c0108190c1209060b0f040506090412032705071205060a090606080a060501090f06 65
    0x4210b00707982109034100c1a882c0002c020344d602e020344c42e0600c2650250a040410b0a0398803090309484280140039500c54402c000200000ea0f403803404002c180344660b20480c2c05180c846500c441d0100000d60080c81201046030407441118000c4445800c1248118600c1c26200e050722508102c2117070381c1d548501d003524443e0200d0100c2c0001402030078180d880d0f09480102c1d140507031044035408000d0f000c85d20500b603105c0035040d0000d40419030f542c0400c10320701c03580300a103400d03101441c010a641e80c80081c803201d1040d105882d9605a0302782072041070780c40b6003040d80e01c034200a0341c2c43c40d14101004015400c1035500035041001c00841c40c4c9070a104452048101800e920300031ba46a0b6242c1412284152540080c15911400220b036043c01e800c40c82c07000342d5404130325000644503080130351408409500c40c200400900c10400c000640c04070340c0c2900404001c00204207241c80d850702d040a011240c116031050b200b100312402c14002c0d5900002e0403603400d030711304200d4100b40a02d0700701614a00d024451 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 835491654 1250 835490404 835490407
    0x140102160b0f0904090219090516020303041e0203102009010c02040e0717060a05060609061e0f12100906081f0b040903051c020406081321031d060903 66
    0x4980b00c0403034014036506400034400506081c03e07500003640166100c0c120004003050140500c03824546204081e080840b03076900d50072803002e50000030b50307910005000031302440b50042c03504a031041014800500d40ea00800b540c081d207149420f6540108580c001e41c082c982c0b0700780440b240b03541605045500b14074041e501d49807949500c0d02408098031045041a51511a4050010b400000c20f00e28488601c0c940014001900b0079002c24400e44401400061050b0b40811200707071a55600c1e0110340400302d2608420560303003a4100c100e00240103500d035a0980000000c3c07000d4503500400c10b0306201c3d24402200080d00c0b91500f60000c222100ca008620440d40410200c03800758841d6a0034034841e40b00301a010810703031031401c045030598040c00412070102d4404540c1c08120550020b14840f4045880000c5082514051000708044009809112200f0048030034205000195050908480003c0340100c094010b06100400404000c407256410031001c001a83c8201404280240100444e40065 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 835492904 1250 835491654 835491667
    0x270405060a0e1009020f04060306081b0d0309241e230c070f051005070210030b0117160908010905030f0a02161202040b0603040c03060e010b0901140102160b 69
    0x1070300c0ea140068100c0400f480076080001d983e1810f4001020f11702450f0a40c186c94925054014080e6401504403414a40003400150795501c030105c0038201c1250215000f070350540882c1010786881017070303800400085004648a0500100080c084082e001e6540d5a0401006120081140e03505103000701100048881c000c403511000d40c0c07515000c00301360300400d003440c12041002403407800c01e1076880703000342e00c0c04000e0400c014940800580003800701420458685550355001a9410711000644010701d0b130b03142031490303690340700d5000744451880c141304030125400e181300d481200000a214100008480080100d8404018014680ba203640100118101014a810405140c1048070b00700110310030310411043c50001c4207040001000c0c051290806c0e241c85004ac8001c0d604092030300f5000da032040081c071000481c80d00c072100c100e80d0012000507142015111040c00360a91062003648403100c84000705280714803101961001c5801d07001c880300714030304080b030444600c164440c94a440c0340600c0310 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 835494154 1250 835492904 835492919
    0x5060a0f0b120601090c050a0e1905060d0b130e0a0b04170315010905010914240c0319030b0102120a0903060f0506011101020c0c040b040908270405060a 67
    0x14040c0c41a4000c00403480d04021400308900108024240403698403c50040010706000c1c4124408010a480d1042c5440c421706400392006c14640c48190103107401041406405483c10b8070360000e4000101600e0743c55055091400180000100c42031040d894003041c0288600da034803075a00035a07c01000f030700848549841d48041418006d00c00d41c1c0d480c025402c0102ea50030a10021845100040c034203418810a0500040008100360000c605004642005002c0007d540f165980103280454001401e5501480c013440b5402c40007150b102c2c402004141c1c1410b2076800f001424198110070807080c0041d000030700490581722a4458980582c20000100d81501c050030010700d800c0b040c90034070114261b900d0740c44000b1598000030060141e0380d80c5040c492950b03407004030700c48280034200095080840040d00c89844654500e205da202382c0e0707148800740c1c3c2912a034002c100c04580000c1e0b001d0301c610b118181e88010a66218145400d82090042900f15103040e114990186002a00c0044543d051405 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 835495404 1250 835494154 835494161
    0x15110d29120a0f0c03060e070b0d021605071211041503120c050d270303020d05130509042a060c0326041103100513080906040306020304061a010c05060a 67
    0x1042894000d058030300b0082041c0d642121036091240039004807151460030b0040440d0203c045040709604918005c002c0c5101c0c41d0240c40054021450060352007008841c500800d8199050040641c0500780001031031000d068001c3c41581d0107440000800c00255003000100c450304801c1741c8102003d104140046110400700c45046440d5041c004101d00b4a0340320035282c80c031142101000610b43c40c01100d800140c05000c0913160105100c000016411a41c0103034486409001e85801c0010214941100741042c0350100c0017040c01500002941c10941428014070071028040400301040314403424071301c0d00701600a0102c0300c09a40344030340c0c2e1015540482e0380040900c100d00420700715200340c15540710249001e5024500c503280c14040d600c40002407508000740301e060030640303502d001e080107618203ca80c0d090001c1d961010403071380c1d83e80c0b91500255941c061034001404141c8044100410800c4990144884407138881801087c0012a0700444401c015000d00401a1300424080784503488181c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 835496654 1250 835495404 835495429
    0x3070f060b0a0f090c0e03031918090e07060f020304030804030204090c0504020c010f0c02070f0b1b19150915050901020415030510090504020d0b0415110d29 69
    0x5000c0c8035003641d118254000c5141613003203101300035503500130303021501d810910380c010184099000d1410291a00542c200525001c98a041484140c01319240b410701a0200740020344210030307041000700f00e4200c0c082c0d40c401d02d074010b00d4042000380503114907150001059600b282c0c0e00072401071030700703041d6824070001d04440c40c01100c1c014001d14001c251560b40707001804121075503c0000810303e40c54503200080d03458112540c0150341024805000041244030814207441140c03030142d40e0360740c90004d00100501c02c10344481060051000c01d61041c8951100e100c100c85c000c681d100403084020481200b11550510300612001b9031510488050100342c1019520403100310005080582e101001b0f00800c02070b500c0c1c040001d03580c0c820003800c20081c13581c000140c8019103040100e89082d90114801d0082244050103040402c00000c0402c011680c00740c0308007461081c24010a02100341600d02c540001101d03210450030720600c004615000101c002694681007802c00c03c2e04460310034042e144c18200c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 835497904 1250 835496654 835496659
    0xc03070b070e15090a05150306180606040b1803061602120f09010c03171e0a020301050f13200306130e06010b0d1b0804050f0105010317090d0b0c0a030b0303070f060b 73
    0x10702c3d03a07c0d580003207a81440b440c90b0342e80d40d03d8950108030301486619000000b0490305400c0c0000307511108180d4007030340d0b001d14460382e403440800210703032418003c03403640d581c03501c00c200420244580401e1201c2d4184d8680e001c071a000f140c141c07400d200d64080e201c050000d04006002c1082658811442800418064100354004151050900008030400c6500810b6811041005043c821400981550102c8100021800c1d9414500011580e0240303280c454030409441c05000b100b160070398868034040312041c000b040500a11002c0c0040c039041210114171920445000442802250052201617008030300680f45c039a0a104007400b035030300020030a2417020707501e2001d1000035606416038040240b254440046030314191070300a02d825803042000985d07904010040001401040409116459500b81d0070b48601c83e08021a0401703200d900d0280c0507081810a020486540600400010101b07527000c0c07011000c28418180e69102d01e1800524400c40c2c58050030101d403942e8000a20344400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 835499154 1250 835497904 835497919
    0xa030e041a030f010c1d100e12150106030b181810060e01030212030c0304260a1109070207060918060f0906050907031815110c03070b070e1509 63
    0x8520120380740072154070082c10305039900c600014140b60403003104201721395590004010890000041481e42c41d94aa040c010720040c18201107144c2d49c0e449036003001000e40402c41d10381501480300041c0004082c4141c9001c04d24020300b80d000390401340841d03e50301320281e5150780780b5110250f01c924003003c00c0041f041d0901500310050b41e0305003a40204001804549402c10895046004001482c58000c101e60416801000500c8008002005484c102d490f90302840400c030780d800e011500090032441d521420350203481820030030002403594002c2810790642d0b000250755079203d03040e80c0e15151400b48201103408041c1c00c120030502c50601518180d4800400715001c0e50715488040041c8940c0c010021003070325502e0500c010305061201c0f691107417040c0340c28410030160100041104405040150028687c1c66040e00c2d101c88a420131b400000b0148081541c403014481c0180d185d82101e40c046031000c50407008102c1c070300d00c200180c501c0c28100030910406210411003104043d4414124a40c018a4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 835500404 1250 835499154 835499201
    0x40b150f06040801060e0c030f011707030819030f0b031509010605100215150907110a020a0f0f0b04051809150709090507181406071712090a030e04 65
    0x1c0c0c0c40d0140009055940012540504141c2e141d80103800c010868040c828041c070030070052001700301c0c07440d0440720110340b2201c1c2c3d04034008086081c41084d40001c0d00184002440696459800b0358003118000d91b41c0e010014110202c0364a02646c0d00d41e4015645a4841c6c10b00880c03524489000c99005044c0c82e0000400715517071404200700c080044030100140e0800d01106000c003241e0a21640c1c4005210080380131100d0a00009504041c0508a041080766114075111408410060001c1c1a90001c0034122070f69a2502e03074035185002801400b83e194440c000000e0f80d20001401d072420f441d0006d010044c4103980e00016850260014000c201314840c11101e85110900004c0d09401204035030f4928690604103003400040e604080c118004201d0135000e80340003a0322203e040c1c01503424401b001c1440920580000306d05008500000d03010f10b49410000c1c00415100000307000382e2082d208028000d50300d1064003a00c7c1c102c0040094085850340d00e083d100c031f24280e2720030480d000794080c580c1800030f07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 835501654 1250 835500404 835500409
    0x81f03050d0905011d0901030807050f12040f05040e030f030c0715141e0103020105031504050a022206122a0c020f191811161703040b150f 61
    0x41c031150003040441d061400030320103540d00050f6032a032000e541503031000038041035000c9444104148405413a58602240480410405024903803031511000d0031501402c8800c00c2d51b4100350700c41d22809100c15050080094182410300803894101100c01c007440c1000c044d861408401c0e80010840c0c400100104180303c001001445156101d04d03080500040c907800f15145038003c000c01800c240c1c141c1207062030401d1140c035060f11142c1501d40c2071a01d580c490311810b0349401c80400d10005140d006040c0b5041100c10a015806000c02005480b008810703111000401c03190001d19001d0440041d0860300403541d00381190304400c40c01c00b480030040306507100000f00d2140c1c01805007a16000511058201c40551510384410f07030088500300c0302c0d124148500740d41c031ba6a1083c90f200e00381d2250f80d504180c2d0400003955002d9040b061070031400c5a5180c0342421180b07030340c018030300701160000d80b4000d4107160b0601c02d00035a8415075200c1125010340c2c079075400c2041150b1b50300d031143e6802244404001c8598 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 835502904 1250 835501654 835501663
    0xb160b0a020a030506040504110d08162a0f0311010509060d14010b19110f0304121202010203011d06210706031a01050406180306090b1501030c081f0305 67
    0x44158030401038550344142c01c010250b4030060016446503040c1b80c14030010954111741d40d925484212007200320381ca4186842d214502950b110342c5114800d40280c2c82c01d10181d82c1098184032003044001c6c030510707091828880d0141d0319010301204041d4060007440081c1d80701d0134403651000305041450a00c1c0084001902070740c40364130b15045603621403c1c14020080d41d100028013600b4124419410102000d0781c0340303000810120848100207001c80c05507807d81c0c0910241c0d08e07170040307202500d5684d901d88800c031600d104080310032201141900d00a010305407041c401ea0f816106040880d00c1d00b03c800300034100320110094145a4001001c503490051407076040e845414400d4110060580c2c0d5140401c054200c0c0d841c0803503446004032255a01c441680e200c0115400d65800b8100780c0280362502200340c046401d950801070880c0c0c6001311800a000444135068800e900301d21443c8440d0403440011401d40c1c400307403040c4000c00e03150800302d0340c02446841224030345c170010491104581c1c0e80e45c9401d40742 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 835504154 1250 835502904 835502911
    0x1101020708190e040b1e040213081509060610050a03140703060602121c09140307030c0c140a06081801022701090e0a11090603040b091e070b160b 64
    0x802c054016040300494214881ca008207604035800c00c0070003005000301d8803080d00030321240d114030394800c2c0d0758482c0d0750f8503070580342000c0650942c0c6e90310340c2d00c5907091a581e91400b08224400c03810540002c4540500050703413440b64001501c024801403903c04241e032590020358410040c03540760481c61840010b21091a031080c0a50366000c00c82524005010b41010701221000c50079510800180d40d0305416942e0107011030b589000005032150b41402c02d0360300c8d600c0800d01146a130200103107400900d68408080308c07403035001e000d0702580241c2c4d5a483c0807108c6032403140d1a0f00045030060400c0110301a1014943c003240041c400c412800118034600c0c2268400b0034800020007c00100c2102d20a1078140c01c9046c207005c0c24400d40d02c2c0d00b0100391262a41d002031800580e240c480703581c1071300c41031000141d0b840c1c41d034058904c6860342400e241c212a03007503085419569901c189070714103440c6c20319030064070300354803044028080382c605010f01c0200c6540801c1008010001004021001442c14185c8610 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 835505404 1250 835504154 835504177
    0x90307020906101b08250c06050f1b070f0e010e100e06040504020a0b040306060e0a020903071a040f03060f05150120070b0f0a081f0b0304020a030506071218030806011101020708 78
    0x48074500f440c0c21f04204035075400503801c00400344902400501d030b8070125501c00d079140070061040c1c1000501540303000c1651304020110414088006000e01c00a64850b05959021030103c4c02c0c0e60ba4540d4070141518548501c0c42000f28040100d11542880e9002d240c00038000f6110070380711626001000041d80c4194070480d0400d980e00c1c010425200701d8040a84c02021040e015880e2400c1b5900003a591071590081841c41280300744020400d07403807013003110700a010840307010341900c0e40ca090000003004002c12922100381020001030090900294031122035605840c5c15060900080107040c40800d0315500140a10441c4000b0601c4104500a03280039928075441c141c2d01c545641008008100150044039007040c440ea0550303590480e01d2a20381950790a20407a5105e030740340e00004440c428240c2c07028040c0d018860601005980c0082620403417102d030001030066180031100c0940d2481c075001c018002501c03150201c1c0d12584038800b80640a0400310000d0b00740f074219100e0100980c04090f2084 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 835506654 1250 835505404 835505467
    0x108042a1203110604030519020102120106110606040c05040b0c0f100e15040c0905130c0303081b070b06010e0d081912051e070c0506090307020906101b08 68
    0x404242e0302039000401c80b8410300c044d04003414240e81c00790a90207400c1d61800c01c941d00c01c4803500d41038802d6040d940b090140740c0724a5160359603401c018100b1055045074444500416000030f0755401c0502a502803500700c1e548082c603240c41e00840c810a9008080f608805010701c103110100754008100705041d0202d43e400009242c0f03003c3d043c0500c1d00c0c19000020001d009954100300225505c0407400c0304075170954030042402d80d51818040c4001c1c0380c4000c0140b903409409404002d0540c40201f1a11070100305640c440c07000a440080c03071060180c50002040c540ca201c000a4140d440b4070001108503a028200610415a1350b540d4101900000810501400140c40c1c0c001125801961240503030100d0b1002c11240c20051200500380000203501e488011440022410030351041c400e089110350080141c03045030409040c1151260300503c0140e01c14048403000c50f1417850819500305100030b5a03190010b415400c1440085000d014840585484000b0310901201c41500303801034026280c0c480c03241 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 835507904 1250 835506654 835506689
    0x90a0b0c01150b090103050709031a01210213020c12030406021801080c09101103210106050a020709050a02090603070201020913180b060307090e030c0c09060108042a 73
    0x282141c0c0060246500c0e80101e100402c0f0350703038098040ba10000400e00c0c000c202503440c4c403402e49080020b588010084d54071903c1c0f11043e003084820850580745107206d500000c13040200408411f80703980e48080d601420981d104c240841941d801000e4002a290507680c0c82a0b070a0074000e056001100e040d20030540001d200e854903507001c00801c201400034204031855007400c6800742000e01405030500d001c0c0311721035500410a40200e40490151443ca01201c0d035602550003090581c15114080040102c084800811440d000310290345040b8065802041c541d45403229640103000050110682d1607402c010708541030300c03180c000b54400d00158001580d113400250510500d000711820710112245450102c07620303203c88014070b050039600001c1c0b0b440d164482d030001030b0601000b54802c55a0500e01003030030001950100103044401c1c129000d44007040215000c2c04420813003194903d0008554800107070000b04d032111800c3c5001407070034049248284114003110b03101c070660070031000410303003d64a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 835509154 1250 835507904 835507927
    0x2503050a03181a0a090b070315080a050a080a14160308060f0a05041a0414010513050705040911070b0903130f0b070b33040f0e21090a0b 60
    0x2102504007401ca084a000711080e11071040d0103041e5403e5100c140008000701d100401075410502e0b1898014100c41500d0510140181c0103084015924002446036280003500340d802198464110ba00100580300c070b151195211905a846100400c040c0722803880050060ba81e404098544440500042a10711941d41000b0748061001843c482c0700b101c06800c0c003c082d0300c2d01c411260403100c003524007042c2c0d007800e866800003500c01c0340d01e0a9000741c607140c0d00d0000120003d82ca6412500250707542003035208010036102c280c81088a058001c144100401c00203601c55900c144501c000301161a81803d600d942c58040d14141035960203441ea00110b004094858400180c130000d0281400102c2014a004c44482c540d0081c944054101070704000000c075580f14840790040111414031034041010340782d5441207104041c5016250040303240c0f402031070502c010351080c010782c0d00710701009002c1007160110340c7c004040c0e5a407030f500c1c0308001030008902c1c0761a00002070300038101141c1059292803000c0603 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 835510404 1250 835509154 835509161
    0x2010c210309061a030a0305130e0f04020f030d0206010302090402060405090a050901060602070303021209060903030f030103201f300b090f01090f060f03030503060306061e062503050a03 82
    0x1408100801c0380101402503a900140340c02035268182403154840c43e500601700270504981c1e1000c80f0b0007428501b0070807007040c0b000d40d00d0711861084940d06803160200080c16a94442404110056070204005102624042040d190b10030b00c000d020b58035141e2108045002d82400391055401d9507140c9060007402c680a00601024054604c0107002051454800a644401c4406021703101400020354110b076880d000304840c10064007904403035982900649000ba0f42e802440207540c44c10700422140040000b14001c5802c80000800c04030160986080b06540c91840005880c1444007011206d0148100d400c0b89489040c6100400e8070104194207401c1d080c0d60322464464404c0c0007a508201140401d5400203040d980fa01c0c0740050302050144014004003807039002906880c1c2c41040020030158440021807140b2400d90613135015481c0d280900c4001401902640b60001c0190342100150500a000c1c020b00244100380c4452405550b440507844504a00d09400041e400a00703240c0d607a41601 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 835511654 1250 835510404 835510421
    0x5120313060f050403080904270314070210030c1707090f0905010b0313080906121e010506031303020703061112010f05060702010c151401051003061202010c21030906 73
    0x3010b841d0515001001003191045010080c940900814076900310744031a4019131521610501481e0440080a411040300100350001c80006400c88100e142006503501500c1c045940035284d2321098030140004d8024203041f002c1d4104009a000c2d0300c0d580c03640d0100c0a240512a26155044803a0078400b4180c07001070a600700005003810300c4010001902c10b20210780d800811441ca100e020503092030f00841910078030a9080d40008c3c08260150784a251031071580c061145003000074240114180406108182407041743da10075400c0c000100e884142100c02e04045102e0703c16201e0280c2c80e0354400003140c0040100c1c51480743d0114105010082d02d440d8039000d0240100180c203010f2400001405c5071040c100000d0400c044403640d10100550b810413101e0f95820460280640c040c1d0040a860201c405d1140c0740c031841c0401103144146020748142400e070f642eaa0303410101141c054005685011052808a4010300d00d555441d8514824042164803c601c96602040d074034000c1c100b0f08103807070084 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 835512904 1250 835511654 835511657
    0x2210d0c080f0406052a0d1a030703061e0501030b1b13030305160605070e100e0307030b06060c10050a060501033c0606180f2601060512031306 63
    0x40040c400c044000c2d0582591040e80701a0100340f075a218801c5846843d540e0030350390440d42001002182c4000c2c001d000e0889540301420412441c100b0304680d01d0525000c02c002c0d90141c118000c1800464456009580c11544c44d00703106040050615244044070401d90090b02e00140150a2120f02c0300c0c42203042e00c04c0b01164007940e0400005840340854003019100043c2444000070f182c80300c803c4551a01c0e80d506810000c10011403400071000751000200042d403a105030105c1602c031220900a034045042c00134054010b010441c150307540c0d6526400b0103020703564000c80034040b4105040c000c00c0360611000346034074007040c20308242c40d500d410703224103070440d6041c5414038440d82c010b0000c03a40400d039160111b550840700f02c0040000030b8408103801d80788101c042e00385000494110740108000710903c08106113040b600340c0e60030034690142903070301440340b1008040c01c1c442100c803800701c1003406000a01000090072652040050012848980341341695080481d51400311b510f19001140101001d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 835514154 1250 835512904 835512917
    0x1140f03070b070201020a140d02070501020d0f0302070f0503031306141501082a1e040f03030c060204080102040e150907080c160c0915120c060e0102210d0c 69
    0x45000080e1244580c1c01095201500403c0c0c4809682c420000325941c243c11810b1310308180b620540b0b8584071442c240c100700241c45407490008480d440064100d08010407543c0e404280088071908a011354001801680c0480c640050704010802c14002940111081c405619a5500c186001c60a480c0c0d8003803402030300006d50080140320b1440100000c04c807102441d00c032a00fa039131000d0550700e00c0490f01c1d032003c440c01001d101030704d0754007680020000d0280e9100d241d0050a01030030307240160300c6513000d484000e900d4600208006070150248a90181c8034201c050f09150700c03101c02d43d0898015500006200d038080041c170000030f03990b198a102c00041511039600d145400d8002801010010f001403441d040000741180d40d9410f01c1e8070040303005600041085030150358030308507070103001c04454043c100c0c905040001100070400340c140030143d0b4005441a41c051400e0000e540300c07110803030305074194001c1c40209080b405552040103041e140c062440c07034541c00c4854076582229240035041060011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 835515404 1250 835514154 835514179
    0xa090b0a050315040905010501030b0a0b0a03170a09180203071214061302070602041806050a03110103051b03040501090b060103060609120206042121170603011b080114 74
    0x6019007100d80c020449000c1c01c0004a40f200802c00038001102c018007654070700000401004510000c1c64060b1114040c1407249184501c02c124004109120040907418401d07500040c5907042c070040c0160228030304098190b551740703482d039551505400010f0307907240c0d6000041010140e0803103102e00508101481c00c100b1090380b400c50700400b400c0034080c1807040301d515000100824403a012205420344c07201c815500c503986c5464070034542d00071040c94039003a400c00c1d4020609042c8543e144040380e400089061106e1a02c000640c01448d01404021103649030342d00d05c0107078000110003107004a1080340005020301003824400083d49016107510304144c2400c8041052592203101c038016240303000781070039019040d840001d10500c142e5005040c562040500d50f1030710092200d034841414007515200d140f03030444080b440c0e80d26807001c02c0080407840038051850240c02001c00300c3e82c05040540000303800c04024010207090341c1003e047c040060b4104005210100031a1a2903003108010756400d0251342 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 835516654 1250 835515404 835515407
    0x1120606050d0f0605060f0912060c12060109170a03080c04050d02040e2409070626060103090519030914150c010b1c02100c15150801060b0a090b0a 65
    0x2255010789030400f80c50b08030302d0f048298280c0c06403005005c001c003000d517140060908080701d0342120021702d02c20524020345605031000400c002d88200789180c2424900344030824030801c440c0c0c019120714100021200c01103000007210711810500d1255000410000c2c05611300180340510080c1042c400007418481042691100c032880003215038102c8000c21044216145603242010b1014000b030014006101c80c0400e80e04000c3c02401140e0201c00c6c0d50550707484e841c050f140001c01c59024140d00104014079580704c01c841405582114052501050b0a03a19844040c0703448072608940a019040960520416403c03420500040c0303d409421102144208000b03208100c450301c0003101a040018848040c03030080d8031078244214010408010062a144000c60800c54807004a01a408174441c10030746601032600010103907400b2100240ca13000d602c1c032260140010030440e980c0f5800c9003c010a004c40280140c0010303088120380b481e02c40e020318000820722181548140320590f400c00c440c6034441d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 835517904 1250 835516654 835516657
    0x3180e0a0c1701050d140d09080d0e030a030309020f04110a2601030f0302030f0310050f03010228140d0b09010e0732120901050105060429070807030e0112060605 71
    0x50340b0803250b40043d501c0d0381c00c0c095a0882501b12042c614000d0402850083ea000302c411000d6803617240c116518615600016100355080c840d540364103600240c02240001d10a8000c0d040c075a10185c1051181c22030326000c41c0076280341c070408159141c0c001ca1091103140d4002e0324118800301c070354a0780030b103e00d0203a6400c040110600014226440c540002c0c000e060013081240c10010f1740c850000d9680c900b0b810480f86012407400307080e101e10001c0e48044010718050003501d4083c46103a24055501d5000d02c1c43d030420301e100018440034001280454442c6190000107408a804400c00c00320304040c1a13002c00c094080d050300481d081d440f5807018009440d0b44a180e02160860b03446001c681e02210b4013254821401c40040e070300350b60700002400e460180e0765480d054003d0002100900543e41c0320810030085018030302404160341f40400c0d140403c1c5980409200d80c803084500610720b03041c215101c008060784120740a80104142d00900c003a19688050000d2029010440800c100c505141d0028480d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 835519154 1250 835517904 835517909
    0x604030b011206180308010e010611031c0b10050903160e0a05151210060504061d0a020909040c0314030a0c0201080601020705030708010c120614060703180e0a0c1701 73
    0x690b090719a035a0100085940030180d03000d5201c02c0750100082e00c3c134000341500400d004800c0c1013441c42c400001c055026241a1006070040805941029481881002501c0340144811030b1903495046000d8141c0b559000d40075243d0541d980c8550360000807040c54608101e020400051600c008800c020503250480c00a81007292070340c0201c0c0b9a180d44415038a40320100c003505900050300c000b0706041c102c0010f0f030002c1c0703865458800d2100950f90000c100441d411885450341003402c00b10300d103504000710300c0c403e5840900c80c00014102a80c0c07802003030b03a5100448003100e004810000c140180070b0400002c021601c95400194507110540800520b40d00c040a0001c0c10322008502140d540e81c000e001c1e2001a01001d42115406569002014082c0c00138841081c0030840050180b403018525008541c00d681400b000100009207a109001059100d40300540820043c101940c03014200104490014800785083d250542024071a80044076911204002400000410404403c4135440007604 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 835520404 1250 835519154 835519169
    0x201110702090105061810030f14060f060d02040f2d1409040f050a0605071b0b070516080a030b0f1f05030603100f0e0c100203031504090b0a060302040b0604030b01 72
    0x4480d00142d0060400e8940c1019051f44103031903800400610383e03d0760100c4101514001d041c1301c0c0c1c0c039500407010041c6070309031280c0d50840d9145c8002009802d0500060031600c04080f0010700c0c1c070b503440902103060802a04a2480e0f09a400c800f0f008070302010028540d241c03100080c440400b483c0c6104041340008005045001c0c40f6490005400e1180300a40c102015422100307035181c4480c1450074400400044540d800421540340300020184400403010ba0440c0c1e03c80c0021915488030304064900303801400110b00e82004420103040000da000002d0502200903072804240f403440c000811400c0800816003a024512000307800c04d14401e130307080c441500403072803c1c440c1d901c0d26680b0200e4142029500c00b204603901b803000c00c0c07410140961100903002001c000f0303910442106401c021400035401007400043c0e109002040c071901401d00341014200006000084e81e104a40d0b07200004001140c80100003607451500304154102070003070040d0381c01f040300d42900d40b5003190b440300100d40041c066440d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 835521654 1250 835520404 835520407
    0x3111309090f23010c0903020105090405060a080f03072303120601030f06180e01140f071803030e03010608010b01020312040c0b040b0403110d0f081c020c030703020111070209010506 80
    0x1041c450300400c1001d00343e40112110080c88003d481116000000e1900a032040d86021008980c2c41d1051401e2410b40768143c4d55249056010401c02016240180925074410700c59140015036580803c282c0007441310540c00307075454242e43d0504180108520310503034005d05c901140e00c03903d03107004022100c00001381442d0314142d4484000403801070030b654500040062a14201086100c0f1751264030859a0ba1500140700c03a1919020090980f200400c0303480035245c14a0100d01c10201d40304005a001d21145000e100440d601c100c00d9260701c080d07030310903004581034071001c0c40c2c10304003030150102900d8820000d108007440300c00002d60702e00c03605c03d0782c0c02d40c20741000214040101c200c0c00310700100070314106680c8a58031440080304075841032004903506003854840c03032158102403200d5030b10305421110a101e440c80e1900c0ea00c0c5d40354019225140e0690042c2c151004000442c07004e410541c00c03143c002c50322034406250190031940844041700d042c440070301000c801650b88011050554900356000b9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 835522904 1250 835521654 835521671
    0x7031808120d02071406190f060b0f0a17042102060403050301060f03060f060314070c0c1419061d030105010e0c16080a0210110306030a08180d0b060103111309 70
    0x405c035840205154400b2801064244200028031149110403404005403c10828603491000b408036a041e01c614230109c0000d1240d10300c0036075031802078943c90165050008201190106003402401c0441c0e086495004180b610400307040820741c078800b509001d00050040d810706844c003402a00051003100c00304100ca1000d0101b40e882500320700001d00401c95241052911a10043c0192012030350408215910744000354115204198003025203420081c68000311b810305d40311070400c480d1040703a070b0f0300416024214080383d420340d07070507400a1000350b60f000340842d040941c1103003140120b40410710aa040c100140903d000302714280c2d4000f600486030316510041c040360b05100d000d129070b001d02107000114004c411241c01180c0225814208182006440a0746508100328001a140d031601580025000800500e0307080c01024401d07000410303602219410300c0000c1c0650703441e840c00c45449418105004141d40c00d80100c00011000344503440c1407404a0544402c072041c18480c5640c070075214400c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 835524154 1250 835522904 835522913
    0x1e03170709120c060e0316050405040f0f06050601020105090c0105120411033a020a020f19030807020f010903030c0f02150d0c0e1e060f040b07031808120d0207 70
    0xe080007050203542807000d02d603681c02d080c24182c5141c03003001c01003a0b120400302420720700403030000320040c074100400c0d6506042105000082030014001c94000c0c3c1050080404a40d20340540d003022441100c1c04501c03440c00780002408e480c0090202c031004c0c1e22860460905a170084161000b0b00c1a8185185095655007030046489004881a0703405000314892040c03001c0d40b00c80c03075aa05415801d08503011a25180700c10a03484843c18000c001600680070003001031400c00340d40072900c840109404800400701e000c0402d440c03004e510440d000200021810114104007000076000c88090803c0117a851139920042c0c510b2000c00f00007024613030702828a2045540d040800d84010340010b5100703407141c072400c910000409054100c0e1000c50b0142450a0b61890310901c061202c0d980c2d15601d400c12050305042c0401904030703016a44404805220200709400e007100500000c600a90f038050760400514807010b07a4820a402400003600006056400f1280c440102c58144101440045c0c0e00d03440b5007803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 835525404 1250 835524154 835524167
    0x60608010b0726030915010b030103020901140a050a0f06031103040f020108040305120a0605010e0d0507091a0409030315090203010b0403081812070f060503060f101701030f1e031707 80
    0x2c0c5400f0061012007403022a00000400795107003241094440303066600d0b9448012680000d220003940f102d20080107221503030580c44d031059640c10107040e09600944800001d825601c198100381c40b0b86a95000402c07040d0340c9030058480443c0121080c502d1420651100215000e9101c0c1c003906005a000100701058401c00c204d544500240c0c65007042c40c00d0418a00000e07056610a05000940040d19003240d403402d5025890445c0e44030380101a800d2401006402410b81243c408094540c98054170665031154082d19180d5840f03980c00180241404030880e20041d4980c04c40d4848a03c1840140240c503003a1046605603900920110b44900250320710000507030b0521416030f0001480740c010b01144200180f11400e0715151440030444985a000c100d60a00013200e21681c8007040c00f90000c01420501c540b000c0d090041e1411100001c50320840c0c0c0c50b61042a40212a4070001c001c840c1c06000480c410064000621140c940c400704103900c0080c444403451601e000414000707030204207018064074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 835526654 1250 835525404 835525463
    0x210c041107020f210a15141b090a09050f0115020a080d020c01090302010c1223181f0b0d11090c1c0207020301200a0f171306060608010b07 61
    0x115807811181c041101c0c0ca4641064480884006d0f400e200c0d000380e030300b003240102688002ea2840000540da0382110a030509011030880840d02d080410864816403195071140025000c07401c00841c80b800c09050460130454140e01c0802d1001c3c9101040200c13a41c0032803482546a00b0201c85c0c1c1d1140c000c940386400900c109014025158602400c450805806410030700e10601146c843c9980118410345a40649050000a841401c2c2c04086858034085810181e0340140f4850784154442e640d00070450304c0c1001d41902e0007804403000620300f034203082a000e6040420000d580100c010700481c0d0794610031654489c0d440c0c1c071540d101400101d020050409036801c0380c8050010020f003080d0b6031150310095000d15001d80c000d50038540b10094141310030003001d00f4211030f003440b5031414008840c100c443e402c0e02c420a6080040c001d1501011034800007069006100341c052040c0c40004d41d103400c00407502280d03c05d400b40040740c0010080c100308030095503902504110301e281c4102e44101c02c4c6180301e1010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 835527904 1250 835526654 835526689
    0x150102010f060e07092304051902030106080103120512070c020334051c03081f0312080a0e0319090e01090605090a02030c0d0b03010b210c041107020f 66
    0x8000807002081c0f18554004d40941c0c0f0380c8203030b041d20368040030074500f449035a914255201c2c0b0b0b200109030805c1e034480c55000d20218004d6421180d59405001603030301c02e034402400a5150310040c0103012007101400d5110742c03d805c00030300e0084550204200f6600051046081c8030010b4034903c2903450034440500b910b1501d08203000065004940d0203240c0115080005111940e400c01182d2030070f08440c481c207005c012021981c051007080d80c0403515800c2c001d040b001d0703040d800105250b440c81201c0035030000d5441461965035001205000412606000380f0050455003411181c18101c01f01000710740d0008030300c51140711016103051064030381203800da00994a00e0b43e803030000100410603a108800742c0d001140c06202d41d40720003030f0980990105a43c5640c40039810044400f50000f80c0d40701c0c0c0705240c00034001145000c00c10340050301d0b4218440b40e0314030303001022012225404062116510841046034108000303103da80d130050080c040d450000f4000e1b82503640c1c0242540e10545000c50550341d2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 835529154 1250 835527904 835527911
    0x50d08070c06050c010b060414040902120105010e071b170901050f0d0203040507050d1203231e13050a0f080f0c03070605070905130b1c1406090d0206150102010f 71
    0x599500505903445640012015440c18200311410711f8480304440441e0380030074031000483c0c03112040000402811008a82c4400b0b05040801404400c0c0502d500070090100b132034002d0f141401002e880348183c080082d0000c09880760940018413002025503640103e00c4130300d82c032118400300598a0b44240301a410140c20702040f8190418030a4005501c0b40384601c0903145c0c0296503c00384080c446120300300070002201020403041840c0301c1c0d030080c2c004049142207a400742c00c2400403a15880701c1580e50300c80c071140549100c80314044203a036454109504080f451244051900c41ea503e90718960001041c85501c000c2c0001482668002d40300c1e4012030f424a1513441103041e02c420f0b6294021001180c4042c142000500c1da10b00541e114000c07580068810994450102c1c0c0c0d00b402007001103029076010517040010282400a034403503000c01e41c8266403510840490310041d41c0b5021300281aa8402c2d40005006c040c0c045e404520070381c1080c00212802400441480180c3c0134000280258a12924 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 835530404 1250 835529154 835529159
    0x3100212130602090604240c0c06080c0f0c010c1d0d0803100518040b07090f150309050d051b071a1e0706050a0c0306082806060b030106020d1701050d08070c 69
    0x158906e008110800303560b4107d0014507942c0151140e0080c507401601c0605103c904011160052032459448a20481000c0c50504170b0f141c0c00c42c564114180c24401699a04403a911280c2c0014007026554000500121040080f4000407100c030300f01c0303400520982010011900385512011070a029210041c141e024020742000c10880e103c1d0100c40a40d260788503217020901007070090390300809484207591140d150a007024012031101442e503030842c0c02c155450303684d078000c208240f000d030b120100d00b0382c1c882d9500d03007034041e24254027000101e01d0f040e20340041c0d004002c4030021010010707000d04036001d0300391100741e2903540158003250f032000b030a01c8850004101e41084015803080d88640b80c01a8100403802d02080c0c11002c55403503004035940769120380d580d8050312010a80d4000111400882c0c00300014240d5a07450070344c2e8269210f10790240008c030050102c0d030303010f206d03400354801e452130521241c010700d0f80b100b40801010700c50b442c040c0b40d08032040720520021404840d4519000707c24421400d9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 835531654 1250 835530404 835530419
    0x30905061515070c030803041416090e031c0e1903031b0206040309030206031b040305030409062918040c020601090c020d02030717070213090203100212130602090604 73
    0x40381c030030005109041210311a011404100c042e101000d404c00844102c2e10700b903036580102680007030070580d955525800d080c104c02c5802c01c042000d08007641c0ca2080c9051078041d007d801d8801c8002016126002441940c0c0e1002d940c560107030403d24030b2364000c101c080403075107814105402c5290b1808031842180ca004203154050700320758104180b001200c440c2c095601d204a880d8101a54000c1c0090310324002000940750180146401541441405070611003072004001aa0304c142d00c1100e507070b00045020496003840384078503401010341c0c203441c0c024070340c1c0e4402580b103c0c8030388002c6000c82c010100d40f08410b8100044d05c8114444090010007800310310a201075075600c0e00344280105c0300d007411082008148007041c4540c0802d003603001907052034019a2151340e190400c80898036062000d10503040541d6681c4a1140640a0300800040d000a140141410704002d8050b0315481c9004103d9150030300c0307901c0b060707990012020b00019200c035647e181c0b4074007034032801d41c8840d44800c0c041004241c0f503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 835532904 1250 835531654 835531681
    0x20d2a05060c18060906190e12150c0901050d09110d08090a060e0d0f11210712020f040f1e0b040b0d02100c08130303110f1606030c03090506 62
    0x30030f8441e68400d49110441040214466188125000b0304244005182003140000340c400c0051a400d200c4040451800440e807031003071040d1500800e034410503441507116049161190041c6031200003619290440c0d001030301c188a216942c0b42c501e940c0b02c040100707000c0038041480c84104000e014108460312410000349903088107500500c1642320100019901d80510b103844050070b4040d210005406107911450318422007841c090314151818200d00b039195460750140740a18009800110380320a0000d03c072840e055098100700c6e074540e620361403140940c0e110007100c900c80f1000c55000c5400202e0721100c4c3c026125080e44201083d041800c42e0464070300641004804d004241d9040080d5030301c4508100d41c02404c10300282d005500b0052050866125401100c04280902680c5246c07a50400f1040810002680140c0029001c0c1c81040c1e940705052001102010080340188003240b00b5903680000c441c15482030400b4036603917030182610f860103030f0440005d0030f4001003998030b1b628040c00c03ea00007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 835534154 1250 835532904 835532917
    0x50d0809160608070f020d080106050d02090603090105040506012c0702100e0304050102162322050a0c050306030d110106080f070614040b0702060d0e0a05011506020d2a05060c 77
    0x400d0b202031003000e111b403000030050724007082503499042903440c1c01c6c01030319143d01c8034074001d00311502041000c0d010b807581401103001d41110400041d017841c0508100d82420302c107030820203805060b0701800600c850340420700e640041c440302d403c01d0700751140c04003030b850100784010b0442e800e410a41c900348a008084050b0003100c2080e001d07200084011040c50000700900d001d200801c4039441d04101d000070a4a0a0b5001c850b400380650018190061407580213001030300035080c2240d20f5900700810f04845004007842446182411800d5040c0440000e4680162520810402a448628940300402500807900a00c1007000347c5444000d0422120344604060141601040a03c01c0348000c45c50250211070441d0600d20401c0d04200c45035082100da035009a1410b80803d0301c0b400c121051185c1802030602c039500c0781000141c80c140443d01803c0780e44103070707000405541003487e90b40320843d08940c1070741c100c0c01d040814002c070080880c2800500713000074801400a20520301004022100f1388000c000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 835535404 1250 835534154 835534157
    0x1a030a12030c030c050403110409050a20011b0204050727080114040c0303270b0903010c020d1d0d0c06050d050a06120233180904050d080916060807 65
    0x10005802c8041d400d80e840c0d81d400a00140d002c100420214500c2c5001e60a00a0b0003000400c114019407241480c1a01c407400917280280a0026160042038079201404880c00030f0034099980498841c03505107140e1030303d5003e4041d548800010b03030310342d10403800000d1801c100101500032004613a2928100c00680c0600340840d868124a2140c0c065902d480d00d10480e40004c040500c581142d80440b002034a40c01d1080c2d00c55044070107001c01007203155040d006410300002140d29842c000b81010309441a40c3d41003029500309081420420303500028007080100501c80400d40e06070741d4070110b00c3d103d142c0703500603205002c0f0020210301d80f9407010040000c41909013080c01641c44500c0c4a100300c640d40d01c034004032103204a051000508114401c00940c91464a8803d841a47c1e41410ba4003ea003c0f0800607000c00d0029400b1940d00e000501440d811405489903403152810741c0c0c0c1e4a5072843c1080c94001400010400250071140400441c1038040410392070b0161103039216405400d80409a44c400c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 835536654 1250 835535404 835535411
    0x1104110a0e040605030a02130209030303010303121a09130c03170327060a05070201021b071e08030901030e0f0106081b011d120307050102030c090901050603090705041a030a1203 78
    0x510b040e00810b0242d0341e0080c0502400c0c1c000d42c3c204000c5100d41e40150b501b071a000d0200f9800e542d4140040c2d0300070340c02521760452000c25031360103a0840e0b0340024045400549091038a105484074582603502c0044034190310000045030500f00c4942001f81d10050004401581711907240b80000055801081c05c20154558440d070341150180242000c2103041d5154016000152a000650041600800140001803405101c9034144079003111400004903203a00c40081081191642c000403204090107040f078607004e07418031010648038818103008a0405803a9103980051403c148503441c0d42d000381500810000d40d079642d0485d00d0342808040c0b0000c420114101281550090001640c008281801c00c66600d142d0300c1000360700d0070712030107110355807205200050002e2000d20040d80184a0640400d40700d4181408000742c000050700414040d40050051000d5003100007240402d9170700494021800c041e02000901500e200034400e01d5051043c0d000c50b609001c0c402c441d04d1070048440e50f050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 835537904 1250 835536654 835536677
    0x306060819020f400b0f04200705010c0801050d02010c170c07080c030d020c091603150b03091506010f1101090b07110d02010b06030c071104110a 64
    0x10360316240329286811040c00403000d020018902a90000303581030700188084a803500c240320102880e0414074201da2104d24081c0007458000c04054144104000303108140480c89034000400c480350740c00035a846c01192211403204540000b8541011000718468106071a03070315606002e03000c0d00d00304680f42c001c030301050008140c600f400038030318010940684544507486000c1d82c0c0c00c030700d109a1000080b000c02043c0044451064288010401804414000c00111911104250405000105503015940040618a00d90311061301d899800f81140b060310f50100384100054011301880f00c0a220080700c0c40002089200d211800b03903024403d2841118010b16859032418405001510520b011031030400050740c0d40c511030b581d0f02c2c0442ea030290010403031507000d42c0d0b0a0000d08d000c0d5044004219107540c2c0310700d50b0310100580a0b0407510b620082c869910102e002c5052440082e0909071300350400940300051118a1003541502180070300100301c503a03130041040c0780c185c1090307004100160036041c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 835539154 1250 835537904 835537919
    0x2d0a12030c05180d06090203030f040806090c150a03060b300417070203030d060e040510291f0206060a0e0915060d0605040b0f22151113030606 63
    0x3500c28043c0740300380400440c01d15000300000c0d400000e40c12101c0c0c544070300c4e070307107006884c10300191000040b011030540e2154145100700303003450b600600284040c3e2200c120090380341d032006d400300b91440c10105802c2c4e56080c0518103c0191020303410030f0950880004000b044020a0740e50700c2e04e60040e1100c0040550000c0c0e00755100350351b050390040c0506e404a041c0d0450248101d004104141c4010201c0386080004080f680694815500680c48040d031542007006008003444134806198042008000c2c1c0c2d001040c44490031441d540100160301680202070080d44c4403100e14443c10494986051802c06ca1030000940d01e140495190307018281003a0300080900030340c2d01d128002c051000160100740c11864110102003002400035a0120170440c510001c50010704c1424001c601900c40d100e19031030300301000e4090043c081c0002c1c1c1a4020503455141880c20354800e0942c1e80c1e4058041d25482da140140c60000e0101c01c2102c40f20b81000190304180d00e0401042030040301c1c81480f052003510f0340c4030305 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 835540404 1250 835539154 835539157
    0x7080f06010905010e040f061502060f190b1302030405010c0f0e0108061903021c1e1a0709080f011508010516050d062106060905010501022d0a12030c05 67
    0x6a260100d60b82050a00c07580d0700076810710400030005072002845280c403446220586100b0b03881000150704070171b200d031036899060124030741c0203403030307100c484110f003464081c00c503448814040343c40f102691096144410b80d0307030904a0f80041c081180a540742d0400e030034018000e11041030b2003408103c013900d40201e11070007440480c19001c1d050316010001e54900083c09502005040f14880c811200500400140c3c1c03860a0300100c01901d108401c03110040e031900c40700d0441c50b500c02c0c44003205c10030303540800910000070b0300032071000d60140e00e030543d2100042943c03103400f280c01100c0d030f0b8026020707404c40061055102c40c200c92400c103030103d4140ea8400d032242c2200d2069072003a21420b0460000c0790740034054401850b02c1c000c01500040e940b0707900c10f5164610400d50b4110071070801440c4015003808003600949015040115080080c2d514200c0080e649541411400580c002d20140003070340c540003018054203405c5043d081c0c0d503504a2a20f0607a160001c0312044601282c5404041c1c520107110b00f0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 835541654 1250 835540404 835540411
    0x6050709050a1203110a0512040819170c100c0f45050a03110405090714130e0114040201020d0e01050708090d05100213050f030a260a0807080f 63
    0xf4800e07140c8205880885003c0c071800c0000c2d4451061409400c0086c5e42000103440c07051030f101e2055103c0f41443c0c0301074101010191020170b010704e0303001584041200e94120507044040e4407a5107599160031140f042c1400d0b080c0a110b15408d01e0b000c0c8144003181c00500c02900e250a982d2160301c20691302c1c81080100c01c1d42c070031440c0500e04904051407641e0900401040040c802c0d0b00c0c0000295942c00003821040c0b464104840408070b8081000750b50404e4001c0f0b540101c92803014004141c1092444802c40c0c2c211840356110340c0382210a00005c03d0140d00440d120090900280440800150003506520054804900510500c0b00301c480c500d01c6010701140b5208141c0d90a403400e000c644407071009400001e81726601150501801000039000c005844005146d43c202684130080034140941800c0c580d031050340625010b88800010350340c04680d106d00c5c00d921251520f002c41940e402e000408440445440da2a08000703508180540c100041d40e204a2203540d5405180c0d8401007042d41d90038068 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 835542904 1250 835541654 835541669
    0x109420f0b040213061b0b0a020a0e030a02090406020a050403061d0c09100605090423040c0614040512031201060305060301050627041e030c0c0506090d0b06031906050709050a 77
    0x2500030700141c0d00c61051086c1d60b0211348160704001a071a1540c1070413101c26a0b181c0c9146500043d5181c2040c2c01000c0d0080001c4120040d21400f4481d4003c19400100100020403169001400e01e0225004609440207143c0041040100030351034003810703c1080f4840a25079181c0b00f01c864402c414505103214510603040401c041030100d04c0c01c5c600380c43c1508414041ca0380561030b18240001c00503003054500d8010a00c201c001e6171343c1414100003c5a2465410200c1008400c0842c0020051410308603000c443e015552099500621034009056005040c81e1016400b5210000520558181c00050041c80101c00801840d290a4204840d10000e900d003807107080f85071031084d4038010003a02070725406405020401c8811780d1406a00700d07101c0e40340c0401c40108003145031110500c001c0130f020030301900040e18414038200c13904000590f401e410100040012902c4800680340f61010f2160390b00656002c11220100901c524100c07014001c00c82d6100b0001c2c0a0344000202850500c96140855001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 835544154 1250 835542904 835542937
    0x1b07051515031e0a02040222061d010c02030a0b0906150904030903061a0406060c140102030108061b0d231005010f03240e010303110109420f0b0402 65
    0x200020010f00c1c07190011007150f04d014140703800003d6100c2c1d0004110303448082da0007006c001c0d1148103000c5008882d4124030204044550440418001c03d20088411074007428071030001d95a920004e40f0302a091800107003003100000c2480412034000480e64040c04d41c0c02e820983c8112000c2c00d106544d9012070b4080d0020b000490200080b40039580010000100300c100804016150804501a40d03060350001c80003d42c1d208502003031025010580181c80240c4c4025891545005002a034458001d850b82d522a0f29690f0140107008000040f1424450004802d101c4803001d014401001034001040640c1c1141c4040001d0410107808108000e0307c905031104494003c6000088000309065001d0741c20801040d402880d802468803070310070040501464441507076045250040150b0f4590b82d81000c0c981c1044c0301d500003d0700001c8108a24061141e00742d404422014890040d01c14901c99685c0c94000303201300c101d07182180e80181c81d01c2403401d40c0c02d0115102c20b00030b0004900c1501407280103e00c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 835545404 1250 835544154 835544173
    0xd0905031219050726040501031104030c0302120a0c24020303070c0305180a0e0a0e07030803070c2a050a1e0302040e0f0d0504050306061012051b0705151503 69
    0x184002c1e01d40e0600401503030140070740301c1007503840700f040c5400170041e83c1c0f4010404029079a89801440501f00800d02200e04140c83c5a843c1e90708040f039800028410788504a07903085001e420482a02b100c1e400a4556800d148c0d200100180c241400c12441301102c00781d804a810b40d070000003164041e20a50351507860750361a0342c800329a29080051000050341c0c0d041162000355503021300003409400e0859640c1520b0500030085000c4501d400510038282d00182000c00c00f207000b60040c0da501080a050008804001d031030007107160060402c1080c91900d0707481d05862000e01210300f0f001503400541d005913445c0c2d102c8650010811003a00c03911010520b1960510040c2019042580402e03a540203d4070b0410040710481e0810540086100024401003030801003441c00304116500244241e0b211000310207440001081004a6600144284c0d1210042064001030300710801200407a5908031f40c0311f01e0a0310b0001e8440c080c201c40c162066210401007080c2e0040b420b6071941c028002001007480c0074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 835546654 1250 835545404 835545407
    0x60b09040e070b0c06011409070516020604090e03130e090c040f020c0304060c06050a020a0c030e0f0907180509060a15120203191b0e210d0905031219 66
    0x601200007140c901400c0c5001903000084000341c06468004009400d1541c1400d0039120001c0800c4080703441045480180f0200d503800c48101e5104001800001a140c2c078203001240151069610103500189450080e841c0345e800440a01000c81d2203001300100c003980c405010801110580c5c4600143c1c00c512001d07406840c280d07018145151540c00094108030b2220800c50460304150720190124070701c16030b00810047c0c41c3c40383d286c0c0130310290300441c02e00103040c0c801400c1001000c0b005090000028821041e0b5031003104401600034020f10f00f460070301d48001e009120703d4400003685040d03407110781c0214951810790301441c0b00e400301400d0481c0d0940703040c5500044038210780054040c040808030500c018012400191f22034030709500d01ea0100300041c20310000300c070300f000525992070340f00ad0b070600b030f055034401c000c5001c903078080741c20790010341442040d000840d01c01440800c1510410b150040d042c0d0f0000c0e131250855404505a800c40014590440e0440c0f05600c4007065044c0c000740303241d001c107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 835547904 1250 835546654 835546661
    0x150d020a120219080102070c091e05041109042109210c0b0a0c0201091d04151e0501031106032a0c0d0810051221120a0504110103060b0904 61
    0x3140002c00e24610000c203410083d200200640000d2440d0b5000038a2005000044024030010030b141c1008016182d0404106610650f00a58055105480d2804102131051600740d0480b07584d001444105942801e18007103e007058103c840c2101e1015a9814003143c5001e01c0303d240859202d400540440031401c07080ca0f0b81c074116203000312020035085c1000704200c4156006003403c0300c5591501003e0315810300015011a1207a400040300e010f2640c81600c003202d00c681540e800c00da02c00ca03900049901c50001101404480c03c8040c0f501c054040108182d90264101034122401181c2000c2b42554110901c40319100846402038201102d01030304d10f482d1200c2da6005803296140310154202080044483c1c1086500002342002070b000c0c50500c404480402a4200100b0088810350700c1014000e0009884002c9910801c2c4900b0451002e00200101c40d030480c1c0810b40a0740c4c4e54181884d105044100130034056070f042e05c440000b44905c40140d400382c880e60060711043e00b0310b1401c0c08082c20410000c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 835549154 1250 835547904 835547939
    0x50d02011e02010e0f0705010815030d030e030c250f0b0708090d0807031709030315190e010e010314160302190b1c05150a0501080a0e1203150d020a 65
    0x310343d030781e8010000101341400703030b5680c2101490280085504d004001882c0520103030001c101d802c4032131300d800c182d641d0025a04007091003a04011400d024081060740c198040c59040180368010030b440141001c490700c40800030b2504005100700c04a4450001c00845002801650022a010400f20300400c09000180808000042880304000d03c1380e541c907183d6800c01541100850b445020701100f20702c1c01894a6404001c480085040d841c005002080444005458070701a00030301c40402000705510055102428011203900314659580350b9103003103032000f44000d940780541201e400c40c1e040d001090f04001808070b060780c5421182503408010028040c00c0400c1005194518000740615002c0003900c0030341c18103200e036038081c2540e040160a03100e004010501030545d070384074600c00342d850086510650b1401e2a007160b2560381c0300e03c10001010303444100c85440c0310355030505017864070381c00c01103104a8001380c0191203d0200014042e0b200d60310a002580000452018000540740c240b00c0c200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 835550404 1250 835549154 835549157
    0xf080a050d0503090a150f05070e060409020a052208060c070f0b0702011d0d02150c0a030216050703051c0516030318020d0b091e150c0d05070c020109050d02011e 71
    0x4040125603910312007041c60458202d41c0360b121030f17004031950761f14803c0550004075810170500a03083e4400050315032145004020301039501051105a01e0302c200155940d0358400319840f12000f0302e44004100c0701d0709500c00c1841300d02c50f0500003904905004143c40071180d210740c0c0080c1c511111381d50f959100c24001c000c070302190358520a000d81c01c0c11440c6514080d401c00c5019182d01c41a100d0b00070f0900544942c0c02c0541c070804828090100715000417500c0840ea103150050301c800800c8629003d0984c002c1c00509140700d042408024840d010645400c041c1d15407910550214480200369103d02500c05220341160b401d2115401080c0282c1020803007400c101108881d0018235030000344441824902920806550300420000c01c0041222400c54901d0304078002c82000c61410290390740c80e44d00c20b8002c02107954000b01d4074484511041c4d44e82548025800c0c00300380790082c0000d081406114007a400141c803034400007201d00309444403508454041c0e40380c00d1410024800880c3c1004003609080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 835551654 1250 835550404 835550413
    0x30a0b0103090f030c021906020303060913050d112b08090c1201020301050907020c100c03020a0209041506090b0a0308090f040216032c0d0501060f060203040f080a050d050309 77
    0x1c00202000f401c103c0e007620070744407a10b004481d4010302100c10a00801c02e108041681000d120680e000400d69031300c40012581e01c000c40e40c60010814419112030030051075407141500841e00550001300c80c2d1500a0000100c81101f90030710074507100840200d07903201c10003c149146c65141840780c1036031907000380010111162000400c0128484100441030141684d60100041c0814500759920681050407403008010321185040050000c2201c8100e00c0d051103101c01c0501c08050080c06840c0b103490300200411460329290800c1d010801182070054000c920702040401c4000003440b48480001001c0c00701c0c0c00107400c543e5100303801c0c0c0c8240900d691003580e01c0e0a941071a03469000501c11204000038074600b80420f454040e046407080f0301a140c403010144031940d00d207081c401c150072840504850300524030344030341005030040c94180c010f03e010201d0124085046c50b0000000d00440f1006c6082c10781c00b0b60f940c0582ea0303c038088600010701d190040100041c80b00c0c0303d02e002e56000f0110320280d9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 835552904 1250 835551654 835551671
    0x40905010608331b03040c08030304030306080c0a06120b1203040b04030506010b070b040f0f0228080f06010501030b120619050c09091801060f0806040b010812030a0b0103 75
    0x5140140410704188007000c0101e5003a07014041401038450614421004026800d1800c1d13540000f2942d413100500101c0c0c0800000e00707004100d4103400044c02824140d950340d00f130a00f40140580500e0282d010b40e4420100d04828a0030100c1015048812aa461508101e800b44400001e4032409400c03a40c8070142c41c486076038219007070004000a0a014030159030f0382d407841c5070050900e00141d0044030001418010030002c07030b2051030480d50096000b940c100e90005d01c0c1c9000a429894208069000160328003819580791040700030301e0003888520035440026a40c4c507000c544c0e0740c510020102080d00060010401e40d4084c1c0c103d0440800c000b02000c415201c0c03030800d0303843d00c407007151440021510b007610190080802c0c401c807600001440f08142ca0442010007040b280038020342825003520104521207409103081d407000b40030303108401440c070f9410b94608819507200c3c02501d09036038070128100001086000000c00e0f41803143c3c034400b898103558900350170400602c1c400c0015410b06884a13601c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 835554154 1250 835552904 835552919
    0x30e040e2b020c1e090a060902071209231908030d06090b040e0c0907261f0f03030c021816120c090e04060b0604150e010219020409050106 61
    0x2108001c0d001044908032104a00d1002440c0a02d0244070301d000e030300c8010094441c107000161541d08280103950f9401c0030b440d5002060002d000300e5000004282c800700d400c8042014400f0010036000d007075236a5010680d219000080c03c5802c80c070707003512085600010b112103401c08081818440302c5601015600c569a04816800e59021442540c3c12940d102c0091050b032a80d1f2240c100f10850075030341000358000b0868041d030f0f540003071546144106590b0000445046c40ba0380e40d00ca015809060000d0300e071400545c000c1d01110709680760b040c6a01c0c140c001c0d6203102c0100c6600300c00c95055824090a5a00c0d544054031124403a41c03090f0b8028101508103039441019202c2c0e54001d101000da0540b8000fa4110020302c06418810903146160030500003102d001e900000c1e00040d40c3e50b0509050007a101c4c3c0c500b440003054800a1181c026102140000b1900ba58041000c140b00e425100e8008a1040c1001241c842d000c2e040c40c44125140c0d4001c0360003604240e44503d40c920703c80d1300001502504d4105c1e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 835555404 1250 835554154 835554193
    0x906020a020304030303050c0423030a0501060b0405090f040c151e091409040b0a0f02070b011d0a050f1612050f0702070603270f0f03050301050a050d030e040e 70
    0x40d030056440090204109a0315128561340081107400032801c25051402c0100f2000329800c00c52008060140c0d00d04142c3c7d014480c1d2242142c2c410000c100c0e81e41d6803070600116801a22550740f040c41c5800014021790612100b01d1b114a41c0248003076841418440504082e00e00203d558040048100801500c42d040b891180500301081c1c598501e0075241000101600448101c424042d61502003404000340725445004d4110318403c3d404245004601c1c4044001d015081c3c014010710840b800004607800c50b0641a1540a004810400305075a0401000300340c0b1403c4d5200100d0380000400a010290001001e00c803100152400b0040f8071203140328501a0f8000769010051040c40406000400c0e07010030501005000300c0c1018050211040c00b112202546140c800d0300000303030600d032101003110030406004201d520180c4041841c0c282c0c10b0080007074100340240c0d40250441e100103d000c0ca0706007001643c0c01d41c0740e9034404a801541091002074080140700510341d11130f84480040c03000c0d00700c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 835556654 1250 835555404 835555417
    0x3090b070b0a0b030a03080105120c090a14070c03020307030c0c12230a030c1e080c010e100b09270a080d0c26150913021207060918090602 61
    0x241030482410b020821008640010019a01c03a5010f001c200001a810612040c111101120a8011080322a40241c2040300e010281ca500501840401c060803c84e40c0c44050340040d01e0449a0a6654a420907514480b5a281c050003607813083c0400ca000030311400c80d01d4500d901c41c00c4009900c90ba140c05404d10781e1013203c400c4510145203c44011800c0d00e050154a80e4049903000f000d041400d03840240030000d0300e4401401c0ca005100041d003044000c1c0c0b005140260f4072080050b034400120122074020a82e102200406007d0325030412240d00690245601141006182c542251140004a084490000c000100207c0515031442200303000380301c2100c140c2d00840010380ea6006941d2080e08032070791119104203000e20301005841084661058062500020709405400e441c0d035030700c1808240c1c640140b150712020150070014002ca0483c0c0d9003880368803c0d100e400751600d00c400d8a60700d0307070010f000d1000040c2c16040304000501c80340840f00c0c80004643c1c4001100c0150742c40300c0302603074080d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 835557904 1250 835556654 835556663
    0xc020607050d02010c08061012230103030f0503150f040e01020f0d05010510020706140d050c1b013b1501150507020f130e100615020319080403090b07 66
    0x1940b11a2030b0580a02030111655003901c0c05868510341980061540c1761981c82840030840c240b15400da11002d50341c0100050041541c1c81c40316030b2640d0011b1288100c0074002100011886190902018020130940b4010055030382d68040c1500228144020446400295644030752113140b1140360400c02c2c8020611110320313901c1190750b101162401d2080d103c0c1a40440d0160500041c00d000c0c040c4d0105101c001d88001c3e151401c0c42e899104204001d40c0035025070480618135100902c040040300b50010600381101c1d605034040c480211141c0c608071a500340d00070800020860214941c0800c2c60420586078090440104001c1c1c90100711600d0b10104c480c8a1140e8111a8014803100c400311408031000602c500c0c0840c40c10600360b0116081c49425034000340180480301d0301d1900151550000304060007400d084500b40d28000b0a90320180ca074600c10a8840145440c0700c86140c0c0c4044201c0d0f6035031400503e20541111414821124010020815000c00c00490000301e00c562030200180502d6000707 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 835559154 1250 835557904 835557913
    0x20309040510090c020f071e0e09030d290603090708060a06051c031d0619170604090809060706060510020709180218070207120b04050d14030c09010c02060705 70
    0x2c00816804507400315103413070250b6005850103d1031504c0040e064060740c590344105000701c1010140039085175404c0c0c100b100080c40000030030030524400409803c7c006403c14081c000d107502d440414440c8000034110240380c5d4141610000349042c07843c021a04180d0410464034256959464141020400e4034260407654035100100841e2400b9071f041c203100d040032034908031f031854a80d4010302104039440300f403003000c2141c031841e40e400d075607030001e1b40e41c1c000b40110300804005000b4801006000188100503158100c43c001c01c10a0420f40328600b6000d5000c01d0305490261188108034a641002e6400c485880c1c0360900498140c917448801e510340002c0d50018038030503082c41c00020988140301102013500031004410340259031807414480c04030307120300944201510f030000100c2c103101c015003104411240201c1040c04000c902c290752407080e40a44280e46500a540100f11103680f203980708024244824004180d414075400000d040030300d014108422201c8081d804138240340c01811040d10103401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 835560404 1250 835559154 835559159
    0x1e1a061611060f0d0c030605060a12110a09060509060403020a0e040c150905040207110405011e08060f040803090a0c031a0f07050a031104090207210309030509010f020309040510 78
    0x140900000700a0044881c1800e001e055501d481c20340c0902044264200e450303039200c00045020f0b0348140090400a0030160399203040c028054100350340403090b03840c0c0030300d054411161102c5503415101116410382e600ca101515024040f1450b810456085901280401000005079605a0040700601c2144402c1449191074101100d180915a212030040003201e0034280d1001d44c05040c40050751411140181c07039410300e0034014449201403000540092074000045140390268040051409608e940902a00d8441010a4907904140c50070160305981ca40403400140300040950f80c4482c140044849245207910380035004201c5e17501c151804001416001c100728044004a0703881032000c40000300b2070030b1040000b0f180e0700c00c8092032000c2594400003105086400c0c02250000e00e5444401d42d00c0d6062400d2660190961191050b040903d46510b800c0407070107409440071203a00740e11031074240010b110055130214103c9942c1d200718041006820b2081e55144a40c07400740b00b411030381d0100e0703a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 835561654 1250 835560404 835560413
    0xf04050114011e0219060f1409010b18070503190504030f0306060c020d06051801110417151302040b04050f0f010b0f180609060a0302030a06091e1a0616 67
    0x500380104501e038588050802c2034158000075445c50107254020300f001c0c0c0c50702c02e040040080c03201620034404541000ca82c07440c4d0b8031607820301070701801e0000020072281c41544200300300032102e90340f40f83c11100f080d0009032500b4010006194080031683c0c166985040408414040f03d00031641100400c01d01c180d940e03070071070389841201b0103046141401c051141c01074001629204591070020403558540000a100590700b1111007400302c420002800580446405042c09030000c2c003864079000852541c502004000050281142402801750282c50b11401803065001401c101c1c2070340c005485882d04400b81d2210302c50244242e00c81781c502002414850422240315006074030541d5081d500f0300114a0710245401120000610014040d80c040d02d1100461454000c44100310780c80440030610b0300300245c06d900158840c030440507081190984811200080705c201d805500508030002d0240402c501e110351246070526109040e840f60b031061750000603019801a80c0441c0d020909004000400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 835562904 1250 835561654 835561667
    0xf010c0305060d0f170d060b0714010b0d06090c03080301060305091e0d080912040b18030106060903020f0d060509101107050303270303180d0e060412020f0405011401 73
    0x41001c540050840032207403101600c42c00607101c003a19200b41003c3c10600380d0501c05c102c0c3c20f102a10700d000e0200a651741e1086080d604495000d03510000703281d5000d03010200602c44c3d080c10150007407217505000243e483d100000c1c1402c144c00c40c0c60012610012001c215500c010b14000c02050b580480c90b86085499182040921103070119203080401c024680b203a000b164a142c0f0410034a000311507903460041c16440c0c5561524400c4918038006004100d401c108401810495101050030030448054000d06080b20360030301c81c0000149005006000500e0050b9008400ea000200681c40c0d2200329102d400803542e0580b6243e0650b445080d01d40e074545001c0c0100380c42115800348080c00e08902d81c40e000e48920006244000c000420f08580e884140d100500e20200210032088030f0f00c070310780352005144560301810241898030ae400c0d50382c85403a00c620b41c00380d81c2541c00b8060170709040c40d0100011203040c14000403640310741c5a0044580e07c1e1543d115140c000e03c483c42803d0100c030312050015128 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 835564154 1250 835562904 835562911
    0xf0c041a0c01140c040501110c090412020f070f090c02031225020303220317040c06110a05070303030e010e1b0f09040b01180216051f0c0e040507030605030f010c0305 73
    0x80403080800c0980104d40b01581d00f160001c0c24004141596058600c0c10555541c0300607500c003490409000c140142c5010700244140f50b03808840318680c0c003400039a5500300600c00e03040d101210542c203016504040d04480801c01003401241d0030400d14190a00000c0022100344103250141192120801e04100710000000f2050001d5459030a04100c4101112180d82601c540311180d05c0c2c0040801d88180c401d455272401c0d1180711412420f0902e001c29000b080c0d48659000909007034210307120f17500080350316081168000c004250840c40c581e011350242042c49200307155035680e8103510400290a12404105150804681076144408c00402c54601380c1c0300d40d264054001401000300013071b81141240e041d80c41c0d11614012840003450700d000a84141c0e075404030074170000c020718000c00500150410b001c40d82d1810f05200008400080412a08035041030750029141c081400304508055000c603800002c14500810000e45440101e46042000101140581c0d5922800d50266a061068031341 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 835565404 1250 835564154 835564181
    0x131a13021810090b0a1805100c0f020f03030a03060f0b190305131e050106080c03151b040e1008030f04031104060e07050417010c02060f0c041a0c01 65
    0x30a003220018204884820300d4042c0107407103984241c19424000c204940091820411540c1d035500301070801003030917811165224641195580c040703883d20b402401d0b2220780c90140d80c0c2146000550315544074000e810381080e81c000b6800000c0307282e1070314144000c1021074507584010034440d18141c1c6000e00708207030394402101c0700428018042012010141d00301d00b11640e180c04103c5445210314201b17103101c8008010041c65000f00391420307560214809040300c601036002008040d580d0840180c8950024502c0f0b540f640002c2d60300020358041007000c5400c103501480452001444040b0110f00d0390054002c0d000e402c48807070800000214100c850800303490310380042c6040001c0341d00302e00c4c00c6000354040140f10920f05901400c607925a50301040040c031801e500d00380c09080142025080740d01500691448011114425410510501800070300c078419078010300701540c8500d180000c3e510007504505103407004000003d081500c07031102404100380c15031075aa555184109060840e140d070000c2c0350 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 835566654 1250 835565404 835565407
    0x3090c05091510050d090311210301120f0609060902090c0f0a0305060d0614150d05210705250501020a0507090e0f010f0605041d07060c02131a1302 65
    0x201c20310b8441000341d00100c151180342c24400d03031030410340d910300074006130300e400500d07148000c000e060b8480b0011040c0c3c107003802500d60500e0744068a60000e020550040329100c010001048040c45101c941c40c580ca00505801c401c511a0fa561034050712140c040076900c49480c0e00f2141d0640c90a0001d0b107411006d000301c454544400309001d11020700401940c001032542d10000200e090701ea00c21074040c1113030301070000c001c070030556111544018016107075040c891214038414981d0b81844c080ca20483c40d040402004000f071864030b1000b03000a00c42007040c9583d818000c500000d041000361a40c06da048024282100c0c0aa0921000d042030990225046510007804900440c10100b180c4041d166520808034107003c50a105926020501010030095881e22409203400d840b241e010b44142c58040b0707411702000f00c508040c10302c0d81c0d541d507404030000c1e082690300f00103031030003065a01886480500000c60702c60415001038203c0b07408c1c100c0c2510410440300c3d059610725100c0e101014194480c40c045 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 835567904 1250 835566654 835566661
    0x110f1e0606030706020d2616030c14090f010c021507170901050d09110a030303060e0703020708040909020d0b070302091906090515040e101a041406031504060603090c0509 75
    0x179036580c1d03121b400f00700f40088038540f41008820284145640b03440074842e1a00307420041114070b1000d820003030010010f4a03080c4000e64040c03040c650f140c11800b03034600315410b2030805c40030003034200c00003843c0c0703410b02280c107020b00016207030072802054210400c80419281ca00c40d04008084500d42041ca06001d40100f0005c40e44d81c2e0408142c94540032102c0b4001105140c81c90031400c0d91900000741a0f01a60340d010004c1010361580103101507c104134103905803078480c1d1209605a0203000301c010042031040c803040c000fa00003a40400e1403540020940b5000030742a84581000260a45020000913000152489141080a0050620080c0e0042c0c40f080350b1402c400142104070350700a0b81d114110009401807040c082d14140c801401c4117088201c4503040101d40134142c501c1910548048070782071903a02540c56119019a42143c0110340e100c01c41e80d10000801c1902d6200408181034030b41850b101c0c01d1252642e00c950b030f0142c10750791000110381030a42850903004900341d108501c1110007a082 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 835569154 1250 835567904 835567907
    0xd050c04030c0609271e0605040e19080a0c020409060218010905060d02090d0b0702210c03041502030d050c18030604150510091e0e030c070303110f1e0606030706 71
    0x285000012042d1105c2640c548030381031340068500c880c01e41c0c80210104000101611030395100c4000c0b030344201d800304134107061034428070b4036004003021a6828851421160001c00e200c0c0d401010425600d261141904001d07074002412251380007002d94050340c0c04102c0b110504105070582140c0042401c04081c1e191510b00080e500b0701c520500031401316004980000582c0300c5004503550251701844810b5035182110000359942c1c0d400300d11380e116180c000044d040c0d00f490321080781c4440385942d01a5180c5410326500240c101c64007000b860440c44108880b00c2c004960b84030f414042d42c20001c82507502c0030350109200001000c94011442500300c0b009000020b120b000011013120541540400d4540d40d00c400d4018513507055201d54150760500d411071040c092000504021a0304c0c5146c02c00000350503c410580c5c0b80562116908207a100c1101800803900554030b80c0d4120a03180115034038120007102450a042000020301e640f901100c200404404040c041c0a03440034007070300105034491a0800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 835570404 1250 835569154 835569179
    0x509101403030f03040b0a060b0a0507110a320315150f030a1a0c0301120318090612060c02010b012703080307050a180501051e0d050c04030c0609 64
    0xd9403010420311844080c0a4405100b5142c0c0d404048201d9030320b916060804891601003120700400b03061514502090704114003069a84103042a9111418038401f5550b141480164030b0715183c2c44a00303040b00090000300900b95000d2144901115092102555452008540501003031842500104400c4140c1c02860729807513400580d0301500356524210380042554800441e249507054010340c40c00c00c090186010302030030340c0c10b40001d820342107613103400d00e0010038002030160500c1d03000c1504120700860b100d031a05a004400044001c06c0c9165110100c40840384103a0109425a40461542081c40f034280b0800800f000135000074010054100002494203003060808a082da5540c1c560f85004040768820303030301941d80194180da036410b000c1400340070358002240000008240c844103003480c91841e03e03d60111101a125a0b090682154041c0c107100410b19540c03071001814008040e211415004581c09074000345150356545007503051210060000e41c0080007880b403d144100408044000b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 835571654 1250 835570404 835570409
    0xa08060112080d1d03040303080a0b0609042019020705030a120f030213142121300a0e1c1e09090b030f030702010c240203010609050910 60
    0x1415a5a0f4146440b40350050081c00700025401d0004c031502600400000300400c00e0b280251a1111960340386204407040d55410407a564022100340000b51560415400229002210040c5003e440301d074005501081c1e0404c004c07440d0001da80f01b0402c40015014000c0d880a82403d8001c0e03d080340c841d8840c1c10301c034001c00000800f004030340c80303940c22010720960540d100c00000701403003402c5640c0d440f020f014080d82c040c0315912903480488440072032410300704040741900d0300304080c241c4284415880e15a9241008151440b140200715800c41042c1c40c07081c0e41441114189081072032282c16600c0315403100000c09040c0d80300d1801d402c03c07000450000b1103050b124160060208640010340d0700b241c90084c104c185881703102c42c034140c5e4450b2a800400e0f010540707040c0d000070030800968004255643c98119582005500b040240c0d1025520404080a0a034000c204824207420306002900740d0340e09092540c0c0c1c0e42c82d0b003c001403040c03a61040c081001410708885059490805900fa0042c00b035051 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 835572904 1250 835571654 835571663
    0x515030c100804050a120503150619030c0c0602040b0d110313080703031103151003090206040504090c0b0307030c020115140904050f0a111003060605190c17090a08060112 75
    0x40c000070108881000019142076026260303403486e00b0f403410041c12a410684190401b000c043d034429800303081c0041036a500c844001322031001450340f02019401810301c07900d500100010410720001003501400208001c2490221242e96100d042404c0c034101e60041c000502d4464040041c042c1c039116402d00b2141250300411816580d032440c0c581034000306003000868a0342c4a003c0100710303280403840924425184c05590b403100c540d1039010210101c400103039000758080020310040c841802c0c80c0e07020900803803245250104543d00c50800499a400855101c00002c0e200c210302d005550b0b080c0180d10502c421000c20720410b60514640c0412003c101c01201d0082c80d00200080a001c410403230a903c0004076030503241c0900c41e03400d000d04140a910034840c0204d114001044603540300c0d1269000722071955817610308040c81040f01c4d43c02513810a06010800071001c0d500d802050380b03401000340d285c2c01c032850755586205410511520034a5544010581d4002e40010409922025980c24280364007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 835574154 1250 835572904 835572917
    0x501111309020306012c0907050418020c030d06030b040309140105030105061c0e030a020f070806010b160b070504180504050d050904060b03070203030702070f05010e04020f0d09060515030c10 84
    0x2131800490b1006402e00001030014002584039945d034400d41c04031444420140c420030704650312090309030349620036445500003008541c401c819011115a01034454003c1000542e03290071f500302c60100aa4079150000e9582402c5002403004040d00041e6103402001525030303003ca040384e104000303800b40c00144145030140200140d401e00102541d102c0701c802802d2080100501400e1080c0c1c0c0c0d0340d036000006040f0151040543d541c14180300026044101c0e042480286400da00308041c041541d040850002840140301010f44001603002c01600d00c0b50829644490b1107903d040c1285090100e8040344040076403500d424440030420114903203940d40ca860601c01e54480303190021030300401c1650b006841010010060100c065030200080d80103403860341c2214609070700d071346001314030140600c50280070a103403101424050070076401400060000618083c104011271040100ba00c1000c442196580d0f0380c0d90800c000c01c3e11801c1f01154a5209500411344000c0c8080421408460301c0c05078000d0010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 835575404 1250 835574154 835574161
    0x1090f03051605011b030e030c0703170d050a0213050603040c2114010905070509090a03030515041802090928020a1701090c060c03230f0a050705011113090203 70
    0x4000020350940c0c0e43c080000c2100090301040a01c2c000c403c071040c000001d06066188407050306c00003d6034110203801020b410040d10316038443c0400140101c24040e08a0107100c0c204001c5450302c55503100e4440b4035070140c2d984103000d404200103509504220b104040601c00e00000c5400c24800c181030300d690902941c11850342490310010a86c5001c0018009055054020541c6a042d000501c089209008880130340b40c6a0040080492086410855a501c41c6601c000031a110703422085d0440c1000e520054141a1b410118040d1030078032801c486011210484141181801d608040d0702a800c44054001c181082900070503425010040b008038060a8104e1429551540000e100501094141c1c9961000c1c041d000360181c0050403084c0e8034541000b0000403468014144050340c0d40c0d060395459481c2c0181ca0100058446000b00c0b00040401886504d2040301071030000e01600019441d1540c0312421440c00509696440a000c0d101c2c150910000d01c0b82800301d400071003682c400303082c09070b00ea98 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 835576654 1250 835575404 835575427
    0x21c150c090819110901050114070813030506061005030c0a030207080c0a1505130f0b071701091a0402090319080706050a2f04061805190e070201090f0305 68
    0x40d26000400c843c01280e008010b0030740c0780b640700107806214214110555140e5010005200e81c01d11650303010a00125502c000501c1040c01410014800c00f4580c1c200000000c0b100d0800405410031106a03001c0405e0001d2132130321009a000110403441d100d480c0d460000744014041c043c0b000141e09158006c15800c0c1040001c40035150314030b10315000c9400800080c00d00b090304890700c00d9021035461400703010030504111060000482e035001607231410310350402d684504691000509103410048401d121848540c400c8802c18001c02c400e143c003050b02c0036000c1c2348507001c0481d2008284240e20401000d0072b1614003081494215040b032183d807200321842e0805001602c0f41c070100824039460041005401d51141c6d1019060500036803c070304440507420f000a0500c40c2c00c070291a04201c0034003003003048510654030940039035090340080100507651404200c03640d6080d5144103503c1d07200754007840511200031070b0342d0344583c0a10003403100030720b40e80f50007180807100c640141c1000390001d000709080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 835577904 1250 835576654 835576667
    0x2010305360a0b1f0e0601020312190609050a29040203071209051b0409020901090506060c1204090c0c08040e132003010c1d041a0901090504021c150c 66
    0x2036080b6000950a1401110204500510400300521302c1400580440e030940800d4215100c0c0c0c106800644ca01060f241101c148100024940101e103039801035550b900c138200f0300401d0020304202c8008552420654040c109840c0d080f00b50305040304180842c4091029540c2001e540e0034825240140c1d40d0311082011200c010301808104081c3d41001411001c110340000c40b03894410303100d021000313070000b00700800c41034400104c400f0f5070000b81039005021604441d4040c3d40c200070001e10349071908080d9a842810032030a030159607941c54021904104440050055030688451840d02d121000103568801080b40101e00a240441920780001020311249844074448143c11858010302c5103207005814024a0b0b102070746d00e000b0350800850581c2107000c5c2018400484c92980380d01070703102d100c6041c84001c1400400d0407000d480d4080b0b40f0502034403100c000c680a4088540c0200e850b1511340140500701041480340c0d000307001207080007408612885980841c140c40e0203404510440c01842c211600c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 835579154 1250 835577904 835577923
    0x18020f16050f150105041409030304021e0d0c050a050409080d020c123c0904090203100207051b1507031b0503040b09090903040b0406050a1103030406090201030536 72
    0x203031280c0c1c40790708000f4020000c030398100c0b80103e4040c070803c2da60040b2101d0805094440400d5a8000c1c4045001842c191283c1074941242c2c40c04040030505150000c0c080803071608040d0384007040742805106500f0045c103400080d00e019502800300401c160f5174a01c1a114402000c04070310b40c00300300720009140510410760320954100c0125110901d0040c1d0381d680031081c055615200e210711200d0701c81503e601c03c821902252004945060003650340512002e8180580c080783d05014107490b07403620360100d2014008207801764009008004000700c038a0b280d207482c03180203071080d0f48401004a44a00c80e0f03045a0f17803241d041c907056800d0403c0c0c1f9101079880102e088002e08500000c540840c00b40b1b16400501400d02085464042c1c90b2034000002d91248603500030581608400c000034806c0d18013440c002c0211401700d142007428860120303e041c2c02d640040d10200c803a01d0300c441d110420756030b06000d030301e401004c9110403c080010001c13074442071000f00c4c5030001614003014128100313001c2c00e000035882d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 835580404 1250 835579154 835579183
    0x1a09090a020a020c030a11040c12020a090f081603060c031e05090c01140f0f0c011a01080a1503150e030c0105060a121115071b18020f1605 61
    0x4190808000d140082e4000c085110014852420b2034107640c074002520042c0250000c0c1502c1e180d92003075083c00040c1c11541c48101c00c1c0300741c41d80280b00010503440140200c031119070ba200707206400c12100c09140c04555200c3c01956001050441400002d440c941080302c0c1c0c0204001461011a007085c2c2c06131106450703180d00d0640440c0c04035203003801c507009688620011001d0310782c1d85c1c6154005440742c00d10000003034450030081c0b216000020b60400144000e100204040d810f10b06030000f801d0940f81551001090314070344240001440d600b1049268020303102280138041c00d000002c1c590404201444040c2121041da9610a442c1c00c003548200700d80047d48055998510620340954040e04040d6901801540c1e070242c00141e180f4108000d000b850340c4554014409101c000800c031a07126106040000c03200e04110b450005958044494003401140d0345030b030b4120745845d007a099050000e002c2d101b8801d00401002d95030100f100d04440607000321006810000c42607081c280d280800300c06040d40c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 835581654 1250 835580404 835580419
    0xc140d0809161e1d180102180d050a0206070c030b010906051c0623220209010e07052a06150a03061a06070803041b0e0c07050a0c091a09010e011a09 65
    0x11030350101510140c80b17946058554503504032a1034040f4203e22070700b20400c0e900b40b091000884649049000348008a0140342112458491a0005030350356000403000c45802480d03d0f4108100094982c90f580100350003041006010b1506020030002205030010795045201e28a4200800c481e50340300c2c01501416032070741488003855090010300c507841a83d80d103c0c0c4894615030402c07003201d00c081c20b9038503d50261040310280d1801c0403c42d613105018040e00140002440101c401041030691804070300681c443e40a2741900000ea61428040040d2000e83c10400c00c49824040340c5541c01c286003102c5d4040303070008071500b0006424021043e010080e0b1b52110b000940340e024864980c01542c081ca000c7e0781e4410380c0084210100582602611500074121115000160880ca4982c06030802070f0103682600c96200d850380d03c15054284c40d801081c030080e580c00182c0c088052141c112030445c0c82c00c0e18508010b506062040e000301d4014842c0a880110548aa84602488400b034900011024040d803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 835582904 1250 835581654 835581689
    0x17040c08030c070504060504153c050906010206011a2a030909101202061b10051e010f091104080a03030506270402010509010c140d0809161e 62
    0x640f035a225114041c8202d0038058081114a058452880c18012000101c1009450b02042c2c640c03095a100310702c8194070340010040903c4000783da0781113600c0801090148240e0510f010000c00d940098070650455004800600421102080d460186030000e10816141c07401581e1518500070150a020300c890b009205a0040c048000041c00c100322080342c0d20001c9a40d000c0c1c050304c80d0503480c4141898203003103000e0311003d42010401404001c494400307000510050646040c076000d81811480c0348250385a04100d160381c00104040c0e81350b04d130246c44040f5035140c10245502c44c2814096450b115031b03500c80420710780101c2400c4800500b454402c1da24068075605000c0d00034102203d4003030107880d100c00b01034218405290744009140d40102041d00075202c60300115a20b401074030f60341d03041c40328403101c04000c6030051020070a080c1c4200c0007001103140e05040100807200140c241c0196031700084a29072001210042a0123031080100381c0751201074421650b0b44035480c1e0703501000e002d86e070f00300c0321 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 835584154 1250 835582904 835582927
    0x5091c08061c0f0b0f07170406180b01050405010911030f06060408060106030e0610180f020c010216050c0406050306150303270a0e091b12030313060605040b0117040c0803 75
    0x2000f20b40c44c00344c0c5801c3c03166582d0042d4001c0408045504400080c0c1085034191fa12040d00002c9030043d00801001030a101c04a0580101e0f48070000296040340b10540104050f00e8503008041c0907004080051091f010b5900d0051800e001c06030001101011000c00505140c5540040d1001407000c00c0444038656543c0502034018000444001c5d003038000c910019403462800082101100c0b03c4500da855034413600556080106900c45189240716004c21940c2d1100f9424005081b210a910200c0e030004d0f9603e19085180c2001804418003032418031a081100c0d90300800c0103a07008c03115503030b20000070b102500040d0861050101c040401a402004091035079001000588400070940b201c101c810703220b03040d82450b100c040300c1c0c0c00035503801842c1d80415805c119840014418010344900340042c2c2807030b400b07030542c0c0086641d0070040455030701110070b10045000d8030300108410b9a04100d185542c0b00001c2207818103812a007001c10748a008541040b06103035504000704a0103080e01c1d00e41c22070206 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 835585404 1250 835584154 835584173
    0xd14070909140f0403032a0e0a090e060402130f0212060102150405120a020705031c2a0b190504050f071e03030e01090b040306050a05091c08061c 64
    0x4207030140b46001015818480303842e08141c007442d04401002d14998460307070120050401c1100c0d0809002c0181d10b01215010322071810680c4c01e0403070326201000f003840c0c1c080c40030490381ca0380101e1b2541c0c1084400c2d0106500400d04542158040d03620711a42e005c0c920703400024100300c0c07070442e5079240300042e111440d030300228186000d0302c4241d00351101001035104100c02841e040c2d8010b001a00201005000008840000c16400c0e8603801621000ca5880e40000e082c408a150501c1c440114012600c041c190b0041e9481052140548004d8030144c412044032003100c41110004c1034112120080342e40403424013100300c034881c1c1d8a001840940303858a0010344841140c092442e15118009000c5414212007660310f86403110b4408498032585581c4084841401d02c4810703605000184401040c2c46101d00000d10103540201c0020459042c005200021540c00602c501202d8000801041c0c00c90408403840a403108c030307458040d016450f00c000043e81641c2d103d06041030030240034042010044c0d01007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 835586654 1250 835585404 835585409
    0xb0723090906010206040533010e090c0a1d0403050c0d090e090c01140306040914062d04020409020a0b0c0115170604060507140a020f010f110904020d140709 69
    0x40385496a900d41c20010381e17981c03100b40c80082594029080d001d40d060a040e08884080c1c03682c1420021000f60f80241e03220040c002e800200e16a04803c0402851407410048920720b44010b40d0b000403481d2400d100c0d48490701c2c02030340c0e51020510741004541850302c00c10030382d101c0c00090b1040c1c070600b00040f14041c107480b420740b007120b00101c007200008000c0e2402080d26043d0440c1a1915001440e01d08511040c0342c0c03004002c241d109648403540000300382c001c03001c8100300410741c00030100c50510001c00c501c0ba0751500000b000c074041c070035014042100c6080c2030642150703056a01007030030744640c400034500c241c1541080c0e81d40c0002064072007407444c054020b00c0300c232502d008058100c540c031040701e840103d0300e0310034094081c1d01410101d00081c6081d031002c3e038004400e1400c560039200014044006601154050005038401c00004050302400c2c802d109a44181103c10405003400841505160044003c0b56128540c041903042009409030482ca01401022500141d9032030b000c0700250050300d060 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 835587904 1250 835586654 835586659
    0x1504090903090f0f050108060d0515040308100b0d0207020301091b0612020c0a031214010b0703122a0519030219030c0203070b09011506030e0f0313030b072309 70
    0x8440c0003401c0e0121018010031380d1125048420311509100c019115018003a14094100d1900341e0440d0100c0c600b400043d615240344442d1180320306044c140204800c1c2c02070010400d0321a01442040f50064500c04c59440582c0740700c0250b110140c600000340140510380d40901f41441ca400c00c1e500301d000c005075846c01e032915601c64018006114142c40c00301d005408036442654007a00e00240403c0c0241b1140c11075422607100401e803030031010b070320301689902a030100711217403c0424600c0805030040280446404401e401304880504603005250100c2e2091080d03401140041400e51224400c4c0201c40070030307011203500b0f00e2019034440010000d620550540d9809007240c0c80f10255107100b4080c40508120030340c000c40c100900c6d03480e8001d40c0701001c0e0040d40e8543d602e10000212854056004000b000181c0740041c0c4081711048150a0405101403c0c032150810002d085404441e0a110003e407a01f00c0c0c2ca02140b9a03400c8010f481000e03682c503801d042c145446c441d241000c50356034010216104103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 835589154 1250 835587904 835587917
    0x20a0f140c0a0302030415090503060105190306020a02010b010809030327010204080303010f0302010e06120103170c0a03113f0906030405030c12360402070302030c070803040614091504090903 84
    0x826100311108c4156000c2c0c294580c100c0c000400141c54901016039403503103a07401000e04543d0b695644000c070b91203120820090f03519546020019071f0484e914540c05500b076400b552071071503e03280e06100140c800c2002c200041200199403282142581501c016080d502d00b00c90356540c6658901000803003900c02207000408002c25030b4030340c1c1071540070380d1250600623000364050790071079885110b0220308000e1848a0b46040c4583c00140384200701d00190580070303842e640452803140808a0405410450082501076251401c0c01400c05032040402d50685c15050410664003980507185c440c0b2031205040d5000c1004001c0c030060000100040842649400488180d070f911140e00d14414000e000203500030400d2120381c4c80c444a68011142c55031444030000701c0c02d84c4092000502280c12400c0305600503403002c40c0d00320084100f0030541c030180400200035424545050001401c0070806440c82216100c00710308550240c581000300700c059110403801544030741d207503101840140341400c0143c0003e00c3c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 835590404 1250 835589154 835589189
    0xb04020108041b2405131526060405180304261e2406041509060f0e0c07080708070606050d06020703030c03060f3b040b010603020a0f140c0a03020304 66
    0x2900803035002c6e1130218505c520007460070011490850715290b6090620041c42d85016481c0452540c1d8420030320080100c5205007040030500c82124801807051207550490314220810be0000025581105c03000044080e040f0380344130941207040480c000c00d221034480e503002400d40c0300d030003600c0c0070480030014100d9001401882c40c0411034003988200c510b18000c040c02103070180c180354004031000e100c0c3d40010030a8a07620400402140c0003580a018104580b40301401005103150136183c00c503030b501403d94100b8084e5140d42c100d5102d11400100031541c0000c91100700122500f2800040ca001041d080c80310000e0b040c00e0740a503100c2c03a41200068907054240311410f02070301c80d40c0d041d50041500035a41030b040010311750080300b1900c0c550004451041d68508140921050840086100c0c4500030752811b082c94030b1864040180c202c002030600500529100ca07031300200d840e40450261a020785640f0400350044138a20600c20960020700031404000e041c0340d0000000c0c0121001072411641004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 835591654 1250 835590404 835590407
    0xc05091306060c030507050321060112020705070509100f06020c010f0809070501120f111308120d050a0608030307030c0f0c08120c0c030a020a0507120b04020108041b24 74
    0x1007650040001040c10f40e030507100132038481d0010b41502440340003103a113043c482c191030380c2c03410301c00c00500c0c0040a071441c204481035902c84950300070303071018131410360424440e41d58040e180c00c880e015286c0901e14500019050302c41d01c281103001000c0c02650311307909039180d00e03009480c0c410070b20f607990224420040c1c10000a00c50106135105840c00c1000d070a9640c242401100c0c0200170741d2120643e42d4940105600f0303a50244104940469251400b80d40c4424522003503510f40d5443c1d1000c41160002990600c02d4a80c1004650866800c1e003000602603076481c80b418018a610b030000300346c030301c00481041030040d059404002c4442064075405800b194100c0300311001c00b08084000c2241c031003030240030684240c0c04a03503900268003000050404121400d0300e4519040081284010b178030200400050006c10b001d2400035184005a2010b207100035241c488030050007910090410040740c0000e400c0c80b1607185442041986001100c680960f11007100303051140300301e5040c40c441e001c85815552103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 835592904 1250 835591654 835591661
    0x703060f03050a060902040221010504050903040b03070f0c060c050705070905070c0818060a0c0b060603070e100c0c0b070b010b0702240c01090b01170708100c0e040c050913 76
    0x241ea010b00245006001a552030340039011045040b0380180c1c003480310b0451040380d48402c115803d10301c0c0d5291030701d40c5410108070039590054611052034000300014048203945030f04907a400381407400c0040d442e604403002112410760b0541d02420396807070000d80100d400d501030000c10417680610120342282d62585000070442c1c0084da089004200308000759030000d038628000e000360164622040403020010b40c04110340c7e50003070380c80900040208140c2000c020450300321603081070050b241c0f2802e514007040f000d0022811a21203610540d0000801030784036200d602400f0301caa074070080d508211541c0c1c500241d155001000116807270030b2900c0021a9203490304042d0380b04a50010550744003010a4075005c4488a1034400c0712901d00800c010050b45003c00f4010912501c0c4143c85d0007500b9850182e140d542c1c40d000b41c50f56010341e04121000c0052460002c0d14150074010240b000076107410b40c103810740e000680e0710507582e0071608040b100d541c000d8208000e80210b01055680c4400ca2560030050303400c9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 835594154 1250 835592904 835592909
    0x501150e0f130902040f050915060117090f07061d01020a0804090506060d0e1006060f080106050a02010f1b0206010608041a04171206010f022b091703030703060f 71
    0x4804010a60000d1900141c60401288030b0800000c1120340c0d50003140c03e40c0c0d5021072101081d902e0b0b405001c42024200301c2022040c0ea000a0f100b07990400c500020903c0203000f1490800c444002d02040000200b44000010400e1460480e104181d85407405003e1141d06400f6841000714191950180d5001248a05120382c0c01a10a4134207401d05194000030100a00f030180c00c14410300c004180107045205450010618070010900080b4000b007450554405030400410001d1202c4c11502c101c0e0003103110b030b06413070603800c1250726054182e001728010190502d00ca18540c0c100a0b200ea0078200c02d0081010000b99542a1080390fa00e07010152035201043d613005148101c038800808684c21081c40140c0c1117441200c032030500c00d400200d0781d01d0ba500907404220024581c80300f80001036030052044134900c0402d0010701090104201c40f003050500c170006000d444216001d216100a12802c200070140c500b4104180c5049681416155070f038204844500101e8509000403c1c4020805242400c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 835595404 1250 835594154 835594159
    0xb27060604020c01111c050c0405130e12040e1006021c0c030c1505090c0f03100506030a0b010b0309060a0b130b0409060c03140f090d080910020d0501150e 68
    0x21911524248002580003595410309556943c0010760011002e0303004044c03c01000e608041c29040e028880d80c201c0c0c601409000200360104410402600e419602221a1a41c00310000d021410034441c1820815002901c080c00303040000c001c901484140d010f14041c003088000c01410136101c403420380e41c4503819607a1781c003110385080e40402580d02c91004034080038440c7c5449102010f5640e2200a01c01f412003402d0f140d0340d20348040024611040001080588040740da04a0728410080442e8a80c5d1688208001c040d440310300203041500c0070448401c039690b01c807041d2006507a65030814006a00305682d95600342c002c1c140130682040c0c10f070050742c4460380300910104071a0b20300080caa000b81603406050340c102d030300d900d4040b010442e1440b070316403100c555460128800c00e030380301402002c80e0f004200e0340c00c80d03041c4400c3c030080b60700000d40ba40b0036145604102c00c650300d0701c4454034034000d80384285491590000a48452011407608070300d048558003115090794854007201a618010602c0d00c20380c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 835596654 1250 835595404 835595413
    0x110703180501140c0c04052e0b031b0405060f07030801080a08120612010608101d03040b0901020a200f062b06180c11070b07030e060c0a0b27 62
    0x1e00760440f8100802407401c8610440f20059007620110b001c0d21011500b031405002150552080300303040c4035103445038040307149a00a2032800e100c0c0c0c46032070f07000103054180d94401c00380880714a04090801c460241c07000074001c076251400450703141c1c00c581c03098000310001802c4c4400094000800a0740d40705040c0d000d045181032007000500c030408440300804a0b0303401021481c000700c1210084c494a80506050005020a488400708410607580c03164012227901200030a5a699503038040151400ea81c0e03505003040d07983d4480c20040b403818403c44005000144a0018100c82080c04600009503c1042d121074200101c40c000f0400940a00881208000a030320041851400507a52403846180340f10360014038035440b14107910070740c40385a20990380c0035902d200c864083c5810000640006400c08000c1c0b07211401d01c1703184001030050b00002800c2c0035030ac2c0d0710321882c1c1d85d40c54181c4003504e69000440b20300706950705180311800020385502c624201c8003a183e44a040c540104240d0310101c000080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 835597904 1250 835596654 835596677
    0x1a0c030f060a05061b010b010903020102030d0507171602012318101e0b0604050a210f030206041a011409040f05030415120b0906120a06110703180501 66
    0x5086141009280c560b0040741050049503940e140d0020380301c1c165104080502c8412034007900f50858007004070301b80c1402074491007040140ea00008031a0480100790307004c901c2e92100320083e1208016840d095200000d000c1c200a800701702c440c01802c0e4017001740c2c002c3c0400706000e01081104100c20322240d0300c2401d598006845245e0b142e00d400e0101040b0320880d14144c0c2c14440c150102c406481101d054001149500c03002030082d070107181014903045070309514103447d0100042468155104494011350782c802d00884c0b10500050004201d90806502d048141003882c009441d0b190494040b00c600e0307080800d50300515503002245041e00c20668001849240030750400c0301c140d42c02001101c0c8011341e0021100001c000b03002400c010301c1a28031900007000c00c0b200160400b03003a0391511034940e1034a440c140340e030354400c0811500850161150f60421907c3d480107410050000c001900c02030410300c0580d420082c2c04000c007501c90284c0d41e04003000746805115010803402d40320303540c0022102c101d41c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 835599154 1250 835597904 835597921
    0x30703030f020d03050601051215030f0307020f090106080f07031808040e0f0c03360a021003050708060105071a07051c09050615060409060303053a02341a0c03 70
    0x2462b0400b02441641c04140c84000010b40351840e1544d80300c081e03400100b4018114280400747d051503103c121004603596050002c000d120400042c01c4039112009000441c04080c06a40800a8407002c60071520391320020741007001c044c0c1e0041c400c0403030b004150380010f0080a018441b45015100c150403540c40c540700c4440d66219400244032815a08035044142a224140041c002403070381c0344100a00f00905950040044080404004a0515041408002d41c15030301100007580f00109003002030b195201c905080886000c0c500c040002d562805040c09059134100c40038240b82c0103804800d0200e2900700d12942c058400c1c1d00402402da6008001040f42c1050107034035001c0d01c2001030049404d05075203079000415140e10368016000b14400040c4070715a00c41340c40b5104100800c04544011250708251501c0320b0303141540d008802258081010300c011802914a0405620214005810466410001481d04445040c111010404191074605111041b050705202d0304504c1440f03402d5940d60b0700c1c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 835600404 1250 835599154 835599187
    0xb03090a080d140f16020a030804020114090402030f1b0f0403120c1e02031614010c33060f15080c040b0c010506030c030c0d0303020c0705030703030f020d0305060105 73
    0x3945820b081d103801210040102040089200f400540070410440c245010802c424040055070f502c1190807500f0014003183d0020f080c1e980195080c42c0c01f040700c1e2200101c408a40c02508840c0c0d82c054000014403122600480c003185c02642e0350305200030707850700310001c0701c07024030400c60080c5160809000402c040345ca007150b100519803481c2400c0c4401419599550441480190340640b41801840d400c410b506081140340e102c0807013501050551410700d10741410707045041010034108404a10071104105400140068081000008014034071a007000c27810201011510780403200d18103a8002141d0b160400760b04104c0d076242280580710300d00e019088071002002040c0d401c1c4900300300300c0020750a10b440010405080d5440002032581090f008040c1020300c0c82c51541d200e076225000d501d00565442c00c0c0700d00155410708006a80300900010300d4100304c81680020361600800000000b810b40001644000156a500792811002d049900343c0c01c440c41543d407640001d0702030100c152001002103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 835601654 1250 835600404 835600417
    0x70806030d02120f0c0a050a1203060f090b180907081002040e0601080703141005091303080c0c0a0c0321080928020a0f091a03151e09060f010b03090a08 67
    0x4025178500b040c40688503280070a0b40004445a502c1111801c090140c1e10311282410602031805101c81441d20202c64074035112030280c00c00280c1c2d1155004d50950360b45100c0c240d540798003d4615218a4180d00c95500c2c0c50a0307100d1258240901450b04840400074400c41c1c0503aa42c501424a145c0c59140044604000081021090596440e11006081d0031708164500c00c0b100303001944591410141880940d400141800844101c2111001c00003500080b511307600142d000342850301d0b00c0c60402603515042003c480903003441c0c0901e402000780a141c203a8648003004400e00380c0d84118031503c3c221000300040307070141000d801250340c00b40c01e00101e84071001c0d0150400164002600ca540000308007410585c0a9801004600401c1101e82a5030251481203541ca10701041420303182404207481d9a103020303044800840100028040f08100e00806840070031032002d0000c03a02d420368003c2e64810f41541d015100500143c0006a046040700480c0d205020001c06800d00d210941d440b80240d80004c0e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 835602904 1250 835601654 835601677
    0x60c020a0b01030b16020307020f090a0605091509060d03020c010503280501050103060504090f30020f0c0901060509150d0e0106090b04060b0403140316050303070806030d0212 77
    0x20540010070396410350a8069030054810000c80c0c240000d00c4a910701c04950a941036400501c800c202607030ba403000542d1103880541e0b403003ca0f40e0703a4256050080480d40c105582c0300c2c1d83c04041c4900344400003c03004a0502c00d448581a036260002000500315081800030010b81c0519014030955120348051a000103001800503114680443c1c03d188040b6072501100760780f80d9800040126603454050721000340001d540c1040801c0c10b40c0c131100d611014000014040c5807480080407240000300c4013441d04146c0340d00f141c0d8080820300c10025290849092184e07000d01c04d0806038800c500e44510900d0480e82d845e1a074900d002211020b200703442d2000200c101d120711060110515002e45400350b800700d60480400000c843d0b040410b15000c07251840315150199240036420301c1f071b130a10b203801c460a60b6006114116a8144141b00703038a0742c42448190340d02124444080d40400030b0000c0030f035010b5210f540350030079650394190903da55010300300c80720801640046180c0f001c00ea140d00041407450fa04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 835604154 1250 835602904 835602913
    0x302070609050c090a0c0f030213080a08030a050a02040b09040f0e06090f0f03030f011802091008090d02010e03091e0d2303030907180b49060c02 64
    0x4035251203044075604601603078150040c0320089824a014843c4551160000408029440311640c2c001c0092001590b10f4003855400a0184520014401e014000b482c15000300c03600303005c440c40d00307020703d400030b590101c40c031402e18011400482250080e2416512000d01c658100420401000050f0030031642c448031055540c03400e0140924103100840c400d58580b170040000902c981c4800389048100e481030070031504184144010151242000780c1100c0f1104034030307009566245202c20081c443e400080e64015503044440708007076000030300035128488000541c1c8035040100026801c4ea4054100312003150403c200308076040c84d0862100c19401c0c2e01d000c1028000c0071400125035081303061081075815940948507030b00414a421b10311100c03808503101840c00c50406022840d0785140300e000c0c2142c1c1e50080c0d900010344981c60351001403154002456500000800c402114420300c500c10186400400d000211400540843d01429074044902442c03c0c03854282e1207440090501071043d0086004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 835605404 1250 835604154 835604167
    0x503040f02130506011b02210f060709050a0501020c091906080f030d0605010c110405180d200a170c0c0d0501020a091a2a07080c03070902090901150302 67
    0xb00c9001080c070311400c040b000211400d21100151000f40d105a00700380744040c0704601001610b404003505c0c80e49110300b0580c205608820329843c104440703100c10152a105d51000c00c030400307a0194001e01145c4e010b90700c503000140c98000498032840014942600190319030b001c03407182c11510b441a564440480d40001d000e41d2141e40003070401c0e00d4054500c106600c085255100a0a00e100d403000800003401e06281621003542ea020402d450b5410f442c0c800c0782c4c4d99001540f5001c1404140c58040106030594480c40c05618000e41111050075581d40300f0408180c1c00b000e100400203014251a4022400000295140c0d604c120643c1c841140c40c0d4250082c20b02404107501c1d040303084910503105100141c2c907818100d500401c165030580c0b0207803880c11440640100e05800d081203840e410789004405425519080d0141e29084d0100c1a0b64240e11454000007086140841e40589145040b41901c0000f81c0e1500d003a0240d004141790310b0b44c0320007402e004100e0b01a6648e140384110b145409e0140c01c002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 835606654 1250 835605404 835605409
    0xb0a0e0111070f03110d0506040809040f0518010f02030705090d17030f04050c03060112030807110712050c030105070e120a0219030303050f0c0301090e10050a2406050306010503040f02 81
    0x1401a0302003030748030039600e0301401002200017940d080e0f07440a0742c040e607003480c0a46903d540e40c84047c002a084080000d07040c2419290341d08110982801040184611b0410b40c50b030b0820455001c814400369442c6c0340c0f01142a00d1240222800313070185550716810800220300700041d594010380211500000480c02c00b00003c0c180c400303503201b10319070010041280780a0411500305100d8480c01442034100c8001442900c1d030034803a03512800c0d0503181c94003150b40c070b002c03080d10300110100d2038030300c18894100c0000b04844541c0d0281015031151041c3c0d03c40040d01014982642c0094904a0114441c40e07218503903802c0803402450a4454901100c0c40c0380c2e582c2d00031900300103a4404d03071580450a004140b05241d058040c01c1d402504260303031060380345004462007841e40010300649035856290001d03840380d80d408002500c82100710801c00c000501b42580090003c00c4502c0401e141c14540500100c0c0c08540c500c4e003c01228519128149076a803102d004480640c0300500480d015402d5656800258 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 835607904 1250 835606654 835606663
    0x708220528170307030906030b0a090e19050606040b0a0b0f0c030f070c03120c020a090f0b040203130521030103060c120f090b060f0d02090a020f0a270b0a0e0111 71
    0x990003409180d0704d8295080003481c81040e90098014503040000664003a182e0812580840324104000200c07030040c05009404d20102d09004404031a00604800c1804408a03405000e604100c0d010800407030880f0074400805214441c2c4111420180718060b01d4090460082010040c6a000d07246840c0d0082801c0141d6040f03600c0c01d9411032001d6131705000700328000e4445440390946040c259a0324042d070740010b0010b03161780650395090340c44400c0c41d01031003540e8102d82c070300f1a0018030030b540f649401001200701120039841a11580300e1036500c143c0c00346480710610641c070070071302e00c0f0361441e801e580300c00001d001000c284004003d2241d502c10300710080c5205240c4a010303081c001055185107800c1400010502070141c030310402c002c03103a100c0366646070b00007010300a0b4150f680c10801d0351904402030007030080721168603005030000343e0b881e412607000802b803c40d096005040094202541c2010a1040150081a9030a4070070040c200000d80682d20007120802c0526040919012004030607050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 835609154 1250 835607904 835607939
    0x9080f0a0224070315080a060f0612140705012d09030f0f110906030a030810120c08100212281a0406091b051e0708220528 54
    0x2c01c4403103014803800c240e0501503400c20001040c02d0b143c41a0a20410907101c1d4106100207000680d651071103907004019802100041002801528104800e81440c6840d80900c01d003d42a40c05410400310351343d0701810003060301110100c0703007031400c800f641a00e20203010a40300070003d01c40c90810000000f2142100f00d40741e280f03d4614180710550503c3d041c9400880320801d140f088c1c00d000d00704042610000340400b44250940303443d08503906c40e840204401300c1d85400511207440400c07115402c2c80b040107160011070f070413034040f185c00050300e8480c072049020303003841c01e601a480c010201710202d0800c0c806138140001c03ea5081891042504580100c0704070782416000f65810300d00b00780042c94203104010061151801c140407a254840c100420908041c001c00c007804804910107404546a0203101c1c04904181000b0766100c0041c24802072581142d4207022040410700c040300925070041c4180d20441c0d4002d80800c44604e24078145416020480158080d849047c0c00e0000c3d000840c00e50300c1d500e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 835610404 1250 835609154 835609213
    0x30c0702040f0b01200303070f030608100b0a080d120209132a02060105100f0504120305030a18020a090e030919030311070f0e06010c060c08061309080f0a02 69
    0x1000f940c42000135101400768203c042d40c00b03c080c06480c2240b64040704880d4001c07400d00e0042d00001000200382c00800260304007401501c900e410041d048ca20b0b40c5c1c403070b02c0800800c030b07400f152807a40e803401540e0342d6001030102000282c0b01d00101208407101d4014000290004003041c1a424056502000300ea100e0300c0d2410805041c084204504509004507004811940c4054222036040c20089051000c4682200b001c000d0300341b141114061142058030b015000e01d040c0241d907242c060070010700170380041d03810b01d40452400c6580e005142c08840f070094480c6c0e02030240038155162154000c02403144107500f1003640001c200216881e0f0750b440211800e01041e464140f8040c0c10f50030300030030400c0c200071145615481170b1802e00c0701400c07200b0190221400344a1458a0783d6640004850741e54084200406031030501010503c03164010316118851402510008035122003861000141c6d41c10400203014500c0402040c0c08040700a00201208580e900460f011040212032052500700465034174035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 835611510 1106 835610404 835610411
    0x70308130f050a03020604050d050307021e012705150f041403090603190b060a050412140d02030301060f090302091302030a050102031009060812030705030c0702040f 73
    0x44541d80d2000039076589000b1450f000c0c0d5500e0082e40c04aa9a00504404030701c25840f1340240ca1145076143d0007840b202d1a600720000100e261134030740d03000300d5407110700b070200c3c90b540305c0380c810805115181c80c4480a205d50034814140f0551000c0d131042000080c0500c02040d80c0704850641103070300b102c1c090803c20314400340c140c40c5124864030719800010210401082411074000f0400300c444c0c0d81028030182045d6800c00036544241c03540c1c0004034105100c14041c0c140b210b074240e109075208900784121100c0c404501c501d86552103c0c1800141c2c800030061041c1e0794051698180005c1070f080045501d81954006580f654008007074030f050b2030308040c0d403405550701000300c2408642c200c0021960b07030400c80c180200f50a0240102a041420504002080d850004001d480175000ca40024216113036010300301c0d042d0744081c2003072120b60401c0c0880c03000742e5258407904000000c20440003 = true := by decide +kernel

theorem cover : BRFrame.Cov 835431654 835611510 := by
  have h0 := BRFrame.cov_init 835431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 835431654 ≤ n) (h2 : n < 835611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
