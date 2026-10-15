-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4633
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:14:54.433357+00:00
-- url     : https://prove2.me/submissions/94156a7e-7b89-4d07-bb14-28d75b2973d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 833093525 ≤ n < 833273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 833094775 1250 833093525 833093537
    0x5040603152405100e04142a03060622030308010602010c0e060f0313060608030703110a0c2c0a20070f0215040b0c0c090c0c070e2e06 59
    0x300050356119903060050200701d440b01d101d82480e0070000305591100c0384400f80000d0031400c560759104d030b01170492501030804140d901c81c80c0545602d4400802000a0749810600350741407031800c1c1c46401a00c1c0c01c264103542c00368403501c141d400e0210344000700d403140d200070300d0000d4000304066010070000d040c0c4086500034401d40d41b040100f81c4107001e1921880b588440c0900000c110004c8410285601c82c2261a4440500885807101c50031124290400c000680001402c0c0d82410303000386070f00d501c5169200003861801c0341ca8480e901601c0043c06030b038244c010408104007510803610700003c224080b081c1982280e00b051034500c00117103a025501605000003545007030b008240c000c01d032900150441000c054901081e820050500c0c0050418080104103200c0031030205648009055404201d0004028002d891130801c03850800091140141d00030400c001c005400001c10007a089981c126508083c03a00c501c91246201007640d401040340d0a081c6200d0f8611207039100040007103a810351541 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 833096025 1250 833094775 833094791
    0x2010606140d05150d08072d0609050106090f02041401050a020706142503090f080a0b0901091202071401080106171f06050405010306120308011e0504060315 69
    0x594061100c0e103441981c8050500416a001580d03400c4183d00c004800207012550110b200040d56901d0145010f0311011008a056020499624007a108100664180b015035680e01884245410041c080090000d038864041740e04011003500000043c10841005000003046000301d44004e4105200e01200e461851042001c43e501a4040f210010307445d6001e010440c1c1050030a0700e40c025281d02400c043c60081055184500480040555078500b100211000c0020390900400100d13840c1c21800f11145081e800700103031800001c00020440c0c0c0801030540d0340d5a01d0802038010480540003900c0f00a103a4007414845a0210700c06094030140c0039440c0d13580d8440c400440e4419024001c0c28082140b910111120f4407141d151a5030011034490950400780c201290803404c581c107640810041540858240840d68040c040c2c0c0d005000001010500e00000307480c001d00004c07040c4200b00e074040c56085c10400761540960342401500c009401404803d03030320700d07041c1500c8020308000061b0526020007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 833097275 1250 833096025 833096027
    0x207021c0206070b040314030c12060108011503090602040302180402030d080420060d06150908122b0510150e030c060a0c0516061e09030602031815040302010606 71
    0x58a402412860815401d9a1074440e461310182c0140e00380021038024060180c03110009521410180181607240d1399041d410342c05008001e440c40381806450401072280000030094800f801171030317203400b0800303800030b0400d0741c028403c68002941000c41c041c0b14211603681888114052407094040380e00003100d6140450f014a400e0b0b5008101c1780c24030001c0001400c2d018444a48460010075091030046d59210ba10121a080d9004030280026040047d00194104046000401c80d86000d0418200030441c10100741c410b0380c51183c00040ca06070b0102c0e03400040b9a81d1054200c008108000500300141264980209442001d0256500c44112484a8410301c2c0c0703125964005801800c0d9013180400300169074103c448200e0402c54449041008650308110403000c041c8078900c940206400c100c03000b002000c48008d07040301c01e88529407105046074000b0313101040f40e0b006600181c0741c0c2c50b0070300d02080001d491444000b00e803003182c1c2c0c1d0b4480303410740c5e40669008500c02d80080000c2c0740c7e9848 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 833098525 1250 833097275 833097319
    0x191d0a0524040308040807020f180402090702070810020d0209060d0605040c0e0603072d0e0307050402190302070512071b0510141614070608090601121410050a020702 73
    0xa0b005001038440004035001440c0359018100d40c0b40b000b410841d6061005002c250100304c04070b116004e449541007400b00f54280980c0281e0000da03584081d010580c109104290f8501c400075004581540c00110305264030701d0359046e54a007180050040303503107a82e801c40841c0034090034040d40307209515250440c0046801000490004000500818259515590155440c450b01030040c89245064003ca054103800c036180b040138114181c8800851075662802d2610b00000c61300000e014610400405600f030816a503030601e8031055260140e6101d14929055007884021400c1c0610303140013041c10002c00050b803072201d503c0103007a2441e52a27aa03562040000300c0c4c038104152004502e0241404002c000441700a1030700041d5a13418400f44c02581c0d40c0d4007524255400c4850705900120403e000903130b400007969070001c9614005040329410f180b02d0140c55012018000d00086140c00c503041106070502c640c0c03c40c2400e04508100c1807402c281408041d40c030012040384a07114084880d6061501a8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 833099775 1250 833098525 833098531
    0xa06050307020c0f150703020c220b0409030203070b091c09060e0a2d0315050f09070f211a0114040504050d030902030708060705130905191d0a0524 65
    0x9024503106039a02088517001c6d800394805034114003485a00c2e1101c1e0301c801c0418042000c0c0030ad41c60a0980320010100112440901d00d640300d00d040c05d4913900401c6e400030030f40f00c1c015000301d000ba6540d2120f2840c03c0c40c06c4800d0342d001100c281c0d07015501c20100d8100561204641203521540303200c000b01020411241c0c49400f800001071035000c800790b6400b04120044400882c40f1030325800702902c94843c0b001c20182c1114410300301d03403907070208041c80701a800381c07540000d0990028030b003c6090403d039070b038001468050108103814940c5100103441c02444846142078104140e900f450426028481c0403000034080d43d000303000f0300f82c3c11090f02d0134036100782c030b10442d0000040c144086d50f28004a000e4011841c040c0e0b414440c441d4081005038092003024025442907c0e000c0c2c0c1d58032002c3c2100c0c0b5201c09079020800713452500041200300c0781c01420030440d400f940307000000d01d0845076041600b00d2001103040e864503c9290031000422100094440c01e5501d44070700c0b030440d80c10300105d42c03103002412 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 833101025 1250 833099775 833099779
    0x27070c0c0e2802070204020f030601030c0c080316050706050a0c0906050a090b09010e060301060249450506070f150207030c110a1d150a06050307020c0f 67
    0x703050b0441080e04160a4084002d1000102626244d1190002400d0340c208800e0000041d10010034881c0e1580c01d442000c40301b486600300410a150941c4960f06a404028030a5403002c0c01c81041c026280d11603801c4a0700585c0c007441c03c000340d041c00d0804c14020f24401e01c0c080d001c41c0d9180c10204226000700103443c600b007143c5e61881d5615007001ca480865800203c2481e041c003501a1030503a036540c82c00007440c060301040e8010030000b42c0540e00f03c0d0b0b140400005000f00c20070720742032b04076909450080590490b40c1d012514518048150270490340c0c518526040c140001404044495504840d8400300c40b0444004042510b0301d042005010030300c200c0d20810780d0149080000c400024298104025154021071002d0322951035914034205036400450120300081c1d0010000d000c02c003140d85c0c2d84240c00401c1d81d031620410b040000c04141800c0c04c082e40018107081d40c000803801d4070380c406030f401c07842c4018000c604426500e8030050600e40003961100054042c041090615042c4501420502440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 833102275 1250 833101025 833101051
    0x6050a05150303072003070e07032f160605090a021203030f06091015030c021c0f0c080d060303051207020c010203030a050c090306010803090a09020301031127070c0c0e 74
    0x915a50940d500c0809220801e20002610301d00c1e05d0742d80c1c148a44402840c1c140a020304034034100c04010100c400071004034203011540760403400d8502005000d0211800482c034416615404c4015141800d964290001e2503181400704000041c04d0100300c10807107034800d85200c10071140007148d00781c89000845400c2c0412464500140941c0742c550302e107a40010728000c0b4880d905407569140301c0e03180c00c1c4a5460010030b46414031004620b60401c4540da04143c2c1c040c1e1502d000b03a540000500640e0700d030101904002c1c405880d8410701030070030102c3c0c0340c02c41a22010001c0503030300d2070040d045410007101011142010400520881e002040c148000c00050340551300e559900f0101c80024a00a45480c808400034031900c2901d840410090340a4684100195100d07d1000d0801c1100140360300000b84150043c40100006070115402141d180302c200c2c2c80da02250154000c2500e44201c0324080c1041c0740700101403058a80d00218907106130b43c054140c85400daa11206c0d040384110003600c400c00a500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 833103525 1250 833102275 833102287
    0x3130b04120b1806070e0109081b120115032306161d0315040506070509010824060418050a020405010e0f031603050105010e0901050702070e04030309080706050a05150303 75
    0x105800866200c0401860f110300020400b80e0940350910032950000070502d00c01d03c421140d0380141e02c902c0100888002030803256043d203014110314400000340c501614006483e40c0211400303400005081c0d00f410400052941c0c1c070308101c2c941111181341c603100c034840d440100030b0a04001c40c0003403090318403111241c2e0800314600304850201a01c1054045490100703180c5000307580c00d00040445102400310f021190609080c01c504105001e0800000e200c000c00480c94566006101c03a0b9110007540520381c4194600b44e0a55003c08002d000c680c1d010b00c0004d00403038440b2039401e8101c0504d81c4403004104a0392541800c80c2280f28502980d804180802d00c001c0e038501e01350f03a40240c80c002c081e003030340c01054040c081800c0040c1c031904121801d94484005000100f0842c07140c952001ca200c0081c080789c1040e010280d02c4403c42c1c05402e0b90718104400160505001f900860001903000306e5036070340c0d84150309154000b44010b44021035800d04020104401c00d40719a00300042e10001030103145049 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 833104775 1250 833103525 833103533
    0xf0803071118070f0f0305010f0e0a09050303090a0c0501030605060d050915010611010b04111b011413030816120c0c0501090c0503071a0a030b010e0d030203130b0412 73
    0x46408201a4458460000300782c2c0e03441c4440c042c82c000c440e683c881c2030941d6030701c030400b801100c50404910101480c040042040002d10782501d03003260410f990f803590544480080310041c0080502c05002c9100000030700480ba000000d0790172045004054010740c0a17220b0004505840840c4920f0340e1080b0244030b045440d030305607803080740c0102c07170501103840b541250640200e03840001d030311a40c0801e90342d0301d0f0055106000e000e40c51040b681103030208501c0000d030402d14901d009140782c01c0e00c11040503407241550042588500c2080c01c2d0707101d207450303c1d14003508c2202c4900b000d54030450000300c0180c0816070802108995a11080064585401d017428000c8428000c0483c00c0f091000c00c11480a44004240c0038070903000c0e014054040e00d801941080c06152400311164840c1001a141d50900e044000c0c20205942c0c40e00c1c128940802c03560006801202c0c0c6001d480843c641c48400e0b1310f030030400c241e00040140b11071440039110110140c0e941ca01040140194400d0b00003082c2c0c4004184001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 833106025 1250 833104775 833104793
    0x601030c030f06030308191407180f03080a11010b01080403390b06030a03170601030e3408210412120818030703030902030709020c160f080307 63
    0x120105140c006071075400900700e203090743c80c168005c1e0045801d50090018110342003500700800030301d800040c44220f0340b080c402800c0c0c100061a01c410800c0c1280d101c1e02c808640400c4100900c0c2451070702041540b40e04044090b41d0100c2004c0e80496808040581400018000d51a4140058503204501d13519900c007a00c00000c0d110310a0a02c1c41d00c0702c00704500c0d0030110510100d00c43c0c1411300c14004c001525100800d01005040d240c4030f030b848420b1030303000607510404440f504c0c80c07015540c81207902c924005902a066503042c0300424003808000e182203030340c10001103028000781750004095543c1a007280e9000c1c0400d007d40d0800707402404240c85004220400c0b400c004d2800c91230700d880d00340c0e103d041e1168150b4a400448000750303c51070ac20051540704035984d8000e400e00c5882551594003c1c071281e5203100e2034a00034281034940d04800195074062144000400401c40103540e160300387c01410340c0b140302c803000c1180c111840c048040768a2045130084000d2b503100700b0046151225a898807861 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 833107275 1250 833106025 833106041
    0x14060c0414010806030c09100f08060603070b0c072102040501030809030705220509030f0a02030d200d092d0303230408030c070206120405061f181d0a0210020a0b060103 74
    0x48c101004200040300e42c03014050000038407014010786030f030341040410503080010340d901811211509000d6480b4000000c110041115113003050040b60a01017110707245410700310f841c0603610914100000092085c03640040660a40413000c1c1d801c400e40303038002c200f140c012040031b070524030400001703186224215130f0200c0d81060001040f07a04108650074004007075440040c0840c0140c101141801c1019058000c08500d02c154001c040750100040704210b40034020401c00038000b80e11070650030300b401803a880d603488440c2c140d0703001800c1442e554a00300b821074003540d0840020b03142c620042030050000511425140e520700030310010b511191200c3c507a40c0c101401c00810510100458001a41d5240c0100b0b80c0341c80c03a0145075441e20b0103003001820300600400c2c10a00e5000c80919146840b961050001565806011890070f0303444d40301c01d00010100308114419442403c004019811130016a41c03200c18400c49180682000d5004100d854404030680145020860300c0403030001d6000e5009240 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 833108525 1250 833107275 833107291
    0x12081809041716051207021207050334230303030f06040917130e06010c0f02040e07030206030a06080d050f040603051302030d0315170303040204050414060c0414010806030c09 77
    0x12120584e456060401030032400031110418002184000c5050004426801c0209030002d400304500d40004203403203056190840c41e40c040c84030080e003d20101003400c0c482c4003481c075000030700c3c00303440705110408220000708120b05a84105169085450004101c92040344207a82c07840098483c4070a000c050668040c0898101100040c81c130950810706000e0503001c0309040000113480c0c6418100701c1c4d00c50014001c5810003c20090301400714900c4501c040c00c00b0f90540340058040e02001000b81000d0064100940c0028000180005881940c202a0680d0104410f0303480c040030744c600a840c60310a440410303251510501c400c100583c0a50b002640c48805581481207d9444d5070000f418103042d43d0918020aa841503210140562505080040c0003203082407510040100f01d6240d0300e00004000074415a1260001030800400300f11080801c5410720441c0e160b410890500300e82d0340c2041c011007851110180c1000a03662003001060300414001c1c0c0070b850306591070818003181c6100244254 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 833109775 1250 833108525 833108557
    0x50d02062a0607031e06060503060909010204080106030501091e031d01031e240f0315150602060702060c0403020a03260d060314071a0c07120818090417 67
    0x10081d040070312820344259a260760009400b5842c20700c107901d004600c0c81d446502440e0003024007000f9000401c5941142c1c00712280d0b0310030754841c20845d0180c4610b8011440b55401d1400010070400c0540103400c1da0362088074050a15541c4841d02420240010b001600103140d031942d0554020312050078610a690614012589044100c01d684800d80c421a2084180da070321541c4c1003960010510f0400a0900d80d680010f501d4607100411041611341e00001e0000014a100c1c10215035042d03022900600c80c443c5043e001030741c1c5402c0652500021150900035018107800550f052f085a4200d40c240c0740d004000383c11440c11621040fa40205100d00510940303507901d51141400100e0340607051841c1c0d00800880c1c4103003549082d096065122202c41d82c1d42c1d22200c2c060146036500c801c01000b002051070300544848243c460140f0b40706069002c0428100e1142003001401143c0000302000c244002401810510030750034802030003070480740540400c07812a5951400c1003000028041c40e0740c050040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 833111025 1250 833109775 833109847
    0x100516050a180b04030605071e260c1e1c090615080601050103230604090201050714031315020a17040302030f07030611070b011a040918030306050d0206 67
    0x80b116015403508128030b481c0e4081410001c002c81030082075404503061800c01c01440000c0300207000d20741120780303d100748070055041104544010b1741c3d001c0c10303c0c00002a80070350f061540c48a20564051240c2240d085034050746255140f0700b0408071000750080c00481c030080b0001d0b60111000702050b034400c540c4203446264100030f40c00a404410007901101c8040c00c5e19514002c009402c690911050300c8040d0b240d803440d020103000c0515441d43c80f00c0b081d200030800c0ca03c0c620040f141441180c100074220307803403420580391401c0004007070645004021700c44400c40392a640190054480b0883c0d000c010307481803045a001810288440d14048000c801403820103880b0380c002410015044d00c030400035407101d1410001d1041c00d0103061b20043c914a80300e803500009403528440108140170b08145070103c01495066100808102e50062030858010825035113130443d840081c02d0300082c20b60010303090050216552815550440c10540e00401291418410300b440c00e40800c076441d025410380c4009410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 833112275 1250 833111025 833111057
    0x60306041512142418031c180b060607020f0904060504120507120e01020f0d0507050d081009090f1e11060408100e010609090f14060c07060e010e0d11100516050a 71
    0x107000c47c1050040e00384003441080300240101c0d20b066620741c0c022040200a407022070203086d201a080007040c0d8150760b84242c1e6002243c0c40018030802c0f260444011401c110600c0030b203a100d1401244503c03100389094000000c00c075450700076031078042c0c403520404403508103043c05000c45601142c018015180705004505490703003000320710314040022a00020300201004000c0c407030509404c8103401c0084050416103440f001310700b62401076034121641d50500d80148402100300c5012107074010f820b0700c1184001003800d000c1a000540071100d00720500021030030351905000755000d4514080003092220303203040c884405040c0d4034621420556035100089800e603d540a048155802441501807034003441c607045200c105200035404490704071900703201c00f14a0340da08581c4406e800280119921400404141c010324120004031114425144490318254101000c0440520a081500d858511031601002900e00c101e0b4440d4071004500d174180d0035203000d074002d003d42c201c10346000c101c01002c0000b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 833113525 1250 833112275 833112277
    0x91a01080102120642030c041409090d0311040503070303030e0d05041a0a0509090a0b040c031a0919020a0e040606050a0e06030604151214241803 64
    0xc4965280d40000e03500701d400c610b2a000a411440c00d80300045901030704049400d00d06198205140001c60368100300001450344044000340c0702c5c200000f0381c0d50b03052a600c084031551051150f040c14803443d141105035803501800f0180314000d124041c210101c4c003c4011802091611043c2d40c0940f400d000c0071400c3d03201045070b00051803103a1030014042140d020000e180c030904074585020004100410701040310f210a110405481000d02c0d140c440707140380750980c0d280c014011001e4214101a082000c4e0440c0b54208801c82402554100046152004101c041c0e034030b0b03a911125051004c1d079403c4010305200c01542d5022010007000c551103d00d1039000c1d401d81c0d10940980b00000d986841d0210a49000d2190380020a010300740140380ca01540c60241400f404803100b0351144c60080002007603a15035804c00711001000b944c0340a807580c1c4032010032502c88500708055407011041001039140c1030380012900140022116903d81075020940c116007200d00c01054500845d60b0700c4140249010104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 833114775 1250 833113525 833113529
    0x203040b0d0b09090307050703120905031606030c0c021c0614040609050d050703120b030f0304080604151509020a050910050304050114100302040b0d0c1211010806090703091a01 78
    0x114010501c0303020302e030400041c1c1c4405040c000d0280c104110f810000380c0c00140080880b5440741c0064400c40e440300058501202d035a00c01c68150113900303141c000d00712040c14103005842d0591020800a10010720803203514048a60080d08a2640300122650301070504250102c4c600c114004500440d081e80324403075074181900d00b1035501e900d0b03802403c10000c0c10b00030130910244a02c0d000c1c4c20081c0355103000b07007a80d109087d0701e00b46075540e2040705502d1324240032100c2d41806040c112030752240d41c0d503101661245d04850664400c1030303009a1210312211401803e900381d252007440b01c0300030704007040304000f94814001c10781807100405c51100b02d500c8201c030810342000e40b51101600c914060601d1425201000140140c00d2144c40800c01020000000941540d4064500180f0340c00000c012a244020b082d501a0060428080016501c0c103c00c00400125204901204016111000540b10800150b4156a10100200000d54014400d900c1904080d01a080c0d41e010f1202030181d0550041c000c2e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 833116025 1250 833114775 833114797
    0x110606030a06050a061d16080415050423031b0102160305030a0b040504061b0801061b0503130f06110d020a0605060d140f0d02190b0c042304060e061f0203040b 70
    0x40c108000032082d0114158420450b1802e02303181c0d61419980705609000c01a40c2c501c84941d0b40c40120f001c0c4a604400f51043c20801007103905000c61440c2c00e60341d82e400001000b640c070405c00e0184141e406060090704c41641034050040c1c580045541d0545154000422800c10079a44110b80c402a030340c0d03401401d001c0c501070280011011243c12440711a244075086601c180550b0400400c2856404041041110001c1c941d00c19843c4251030203904520445803a84919105500b000c80c000c009020a0021140562507062034034000105c040d898400300d040480c0581c010349032075804249950403245e4014001408015445a03aa0b2010744841a005010304164040c01c40001170007010003a800001903030f40020a03203a00c0c500c404010103401c00308020152100d410106954941d84000d840c0540100c2e41510012400340322a100c500700f6500c5c105204505000c03001441e64003a0780020301858028043c0c05040511151400540300054004011840208000a8070503816006001000e0003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 833117275 1250 833116025 833116079
    0x1110090611070f020105030a0b0904050601050901062303060a180510050a050603040206090a120b0a1d0606010c020102070911090439020c100f110606030a06050a06 72
    0x20506085003103403a50a260030a4039001c01816002c03407031640301030485a9091070025507950302c250409000d00f2340c1500b89038004114009000401a0110310141030710300c16601603030340703a0340d419044994003800c50045445210040c41000d0341072421006550284010704103039003481d940c16408120740f10106002d03407626503034801c0c0008182103111020081c2001c44016141d5801d00000800c6444080c0000b8490075001545c100d4603101c10021200500204040148203001402c0010700904101c90340d9000c02c1c5061001c61020105a0714480c9a0740c90070010601580c5100c019207414039901c0c4241d05520600b0400600500e0b0f034020f0001040065000c6034503402c1e82014001031340c40c00708215051a9070340740542e1340d0510f42c003030100394a070503600350402c0c40003861401da0402d01e15581c0e1642010a50803880c81150300700b0481800841c8035603881c1000c06c1218401c5440c2c0e1001d9804a90641004141c080400c4003a04140d4000310000c800040081c2d030f400b540e40040c58000141886010b0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 833118525 1250 833117275 833117291
    0x17150403020f060601020c0307092003070f0201241521090203010b040209060906130503010903050a020610030b07050c0c060a0c021c0305030112141002131a0d0c1110 73
    0x2014806144c10034001e00080c8029903113140040c1d2100c485000f0500c00c0e81d901c01e42c1d140c0e040c40e0350702010600d0b450b021900fa6a410010b400604d414104a4010095828440d51070064145075544030050490140c1800b42e0038180500510b60340d441c401500c04212190004a102051801c884003904619001c006904c039038071705c185420342d1494010640314501c14000752069441c0c0504032440d0242c1202c0650341e6000f0141c02680d4804903402080d0950303e003031011410950002c00601400040da001c4540903512518882c8900065003c000d0078500400c02103021940280003818400c1103c0064805541003c1c000c038100f500074285007800669440800b80544c1420f03000e010600b001c501a004038009540c03400b6001344810320807010014030748060704040c01064800070200d25a16015144002030201c0d000c400782d007096004a00d1450102000907481d070318652448502c08082c40b4550402941e40d201030000e04049400c9014450071000e8a0000d00013401454540b10310080e00182c202 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 833119775 1250 833118525 833118553
    0x90a0b030601141014040905041e110a0b07020f150d05090c040510061e03022101051c02090412090510052a0312040302121b01050603030708041715040302 68
    0x1615113207424040c401d58030140201080850100c5080c0e131800600843ca6840e5480d00700300b0007010350400e00d10050310006035400c02840c500c001c84100001c44a0340602c5481da032000754030b4418110020b42c000c41e050454400c42c10019052048058400c071802e00b811641c2221000b07407141101c1c015520380080d210400c2078501885066005400b1400f58800c0030305003200500300b0301042c0742594080c50b9000310f881c0c2452085d01203801764440813041da40140032100055080001c00c0c09010f1190b401000c0140285c54048100d4035026001402040d65840e07984a49400d844031143c184108040f100d0081003503280e14440518241c5e003651940d40e40d40303400c0c00301d01d1070500b0200703500c038024210f007002c4044403000015a14102260001910f55444903d4241e01d80407006010441170382000c103221080d9101c0b07003074202340d4040301402400345985402c2010780364400c0c0003000348082d00600091007194112088d0568045150040b40c1d1760060240c00309030921030840d01107005070b000b040640d04072 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 833121025 1250 833119775 833119789
    0xf030b120f0d0c1a0405100c0503060f03010e030a030b030a0807050313050a032112060b12090a170d141503150c0a03020f09042f030903040302090a0b03060114 70
    0x5420ba40342940e0700500f00e5540c3c0c9a9030040c904604803070700300b40020506124090114000c3c02c040c0c020300304117a134681640684a80c1040312244d101d00c998940100c0a400c041c01608200295680510301d0190308030701c103500402c428802030342c05226045441300000d030070f800140042401000155250b014400e840640706840c0d801c85402100c061000700001040032540c1c59000711102802c1103001803144003140e42c602111000c1c20054200703100000e4191002009000c001a42082c009103950b451910b5542c031000c07410001c105002c1c2c0401e060306034040b040a080d10501149011a4010612034050485407080c2d07211244d0450f90000740d95603250801602051403100601503001303160a850170000c40c029100540b0505400241c0c12703440c02c0700041110020f80008104200c0301c000c0325412510000c11000b58045c0b0051004994161940081a2407203a50004001c510f00742c00d5a0038050318010140002072165214070303180760b290707a0620602c0d0190a941400720300000e02e00040049e4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 833122275 1250 833121025 833121043
    0x20a0803090913030c0f0c050310061a0a02030418050f07020c01170604090503030c03180a0f031812060c0801060c03080402090c0f0703051305060a0e010f030b120f 72
    0x40c0e10401201c01c49071a41100250311000740055500c02e100c550a040d5203208010b600141800c1010582c0020080201e01e0f00007500c000380e0071203405040060b80c081c1213031400c3c025981d5044000200c42020300c410340c010030440703610b841941d003800da480f806000c03c08201e6516601081d11641007111813008282810b600c5007041c4000c1540c445c6200010700100081036403054442903000000340e0589031500301e80b0341a0ba100003282d40c0e034038000800c1e5616400c02c2d101c001c02220f4201c96452036060002e21a1465030f00844a1000f2480030380d81910b50460502c400c20203800c480c01c0000d518121104501c00b407038000c180100304d0b00c0e184d480c001c00c1d5101c1604a0401c0c4450301c41120003003507206000d02e50056040c0c46241030b40d1178a00c01d107419406070696501480314000340380c0007015440009400e042d0396045140848076114010801140685001040050054205200258454949800310304200d040c0001d1148509020850880154406050070780c071000500b20b80000400492030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 833123525 1250 833122275 833122289
    0x3031005030d03020301050906010c02151209060f0408270d1101030f060f21021009030311070614031f1d390904050f04050f010c0206190f0203040c03020a 68
    0x444e5604190008e10b00b0340000d05100e0422040c5540d141c11034541304042d215204120101c59220780400d884a084032000b210452041d00940020810003c4009040c80c01954402c8210b424101e64150300641044220a1400c460f03508000e4251151605400e0901e51405100b0303805004076030f0310014055490050310340d000903140a40400000001c0314640c0140c40c01410300c1c000d180c5444c40d41a648141410f0080c1d808a642ca211841d000e420040d40000c481c420380f543c50780e1841c08040d03152104458403645010450b01c0300ba074032660f10448000c60740b00c0e04011003288100300708018814842115004000750b1043c09807803030031a49401381ca069001c0c40301c840f4042d88224400380c140300d280c0107000711a070300b4003c1d002c503018020002041d80c18568000d8801c000b076150100c00a00f86160950741544c06004206050103055018000c4016150f02d0307400a20345610340300003a070301c14680c0603e440300603942c41c0400c030080d00303030740c0011030049020300030a42142e411801044101a402e5205d80c5c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 833124775 1250 833123525 833123527
    0x4060f05040e0724021c080f0a0501080c06030727080f01060b090f18040b0609070f0e090712140106080601090806040204051b1c0c030212011203020f03031005030d0302 74
    0x1050b008036132002c00400d0909800301e403458000a00903450028809a5100c46904501e010304115601c039415500c200562002c00304e4641322110b10300d049400a000720005a04a4070481e0980d0038000c000b07540200c40b502e842d425000006519076403034500d5181e116002c078046941045111030800000805a1b00c00c002001900d1514810b003600d80300300102d29005072801c0504804039070341c1001000d4020100c14610320685060f10340391048850880f8080e21030004040442e000c0f601c01c281d88000d02aa5480ea01c041e0701c644c404000808000501803010020043e1414144000c40d005480b0101544c00241c40075504000010f0001d5000412150401c918013074100414100041e0440d04a601514009119126000da814a2084405002800701d200080b5000c10420012134620481e52844003000fa503235500d841203041c2d1148440e42040480301038014403038052511110400d1510170300488540052203c0c80c0390a6070030884006000003071828082049003400d100b8002501c07001d103411 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 833126025 1250 833124775 833124779
    0x22505210c191505093604020f150c01090c08071a030f13020607050a0201141c0e03070203060708071101150909061113050a140a06050a020c04060f05040e07 69
    0x508000d0710f4803442082160180c0600502409501200c40200c0701400d20b0311000c0741e4595101000c040c00d8101140c95190000034590300c4882e08080c1c1c040e56000780403204107030030f44040013030202d1064000c084040d403c22500203500d000744500b0707090620a01c50151010720b4542d043e400c000036940320840051110740c64200021545045961141d541d88900e103070340d02c41c07202c490310700f0381c110000a40021001031a81d05004000900410040c800d90310945002213440c5c1885203070103508203850301e525608500100401940d0403004460b130032082104d00305421b540019152000c02d0f1190800b00c0c52200620400369401016100c1c0000c0b0803000b400074240f600218190380025104000c08149d542c4c21400c2004041d0300100301350a0342c0c030120790f16402c040180c4100b1080d18032545100343d1f0340310703000a420500800c402c5030340c010043c0b401c14142d1601c8415a0a03a00546003442107000300c40280f059640c80348036500284c21001c6a95030791604000910045403480102e20189500003001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 833127275 1250 833126025 833126059
    0x106140312030f0f040507051302030f0a1505011d130c1b0203101107050106031103010b15030c070c0906031115160305090105040803040e1006050a022505210c 70
    0x154540064940310000541d50b2079040483c01c000480c0c10865120340b00c1480c110781c09a040e00a0b60042d030040c0c05c41a0301751200b379103900031180c0358800002c8038489800304002e00d60140ea00e4610404010030800500b43c150300c001807907107030040710725000c5941c2c40d0196682d8950110f1501d050200034611140c4803002070b00020740c5c400b030400c00c45107000d46031264500d101600c0825107000c99401002400010b85a250182c2c0d40c00c5014440c43c00780d0b1804103101c0c25442c000c000d10f11003043c000f80061079130315144002d000c2c99204040c00e5035155802c200000700c6070f08510401c401140a4080968050502d13810008015442141c1c007070021000c1c004941251304014001c81900d5050511a50303400710403005a40500403030380402254040840c001545c800001e0880d0b10401c40095130388030440d100d0200799a9409a90004c0006a100d800f0741c21100d0300e10703105009004035140880d160345a0f280002907112030018909109520508003403201280100f1002090350400c44003008400480c40c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 833128525 1250 833127275 833127301
    0x603060f041104020f07060504110d0c0e18030a080f0f04050303161b050708120f1e0f0a02010b01030b030d0f08061f05120a060e010302041d010614031203 68
    0x400a0808010440681400e5a450b8100c44001c00040c1241b0f40304c0f983c9080034801400d0840302501c99041d82e051000707592034800355551701554408050203505060008900704a200204007805d03011400302108414442000a000444203580e40d04141c0d107020315030382070f04480161100841103804414000058000b00540c4d41c001c0e2202840c80307014000000c121510307401201c6078510031007030404410503c40e01045180540d000001118805c0315503913102c0c0300a01c1003042040740d0038030502840811001d1009100040345010380c2083c10204074070a920f00c1903102d0280080940c2d035520900c102540c0600076118852401c401402441e003108001a1000b45034144180420200d100040d4403960b89181501d80c0001463f41c50000d5103500c54041c213698030400000601c00c0224000a480a045001d03301c241c0b40c1c1e4141440b5241d1869003400081c1004140d000d807228850800c1814564091242e42c004090100d4210200f40d5998141410301c002140c111007a03400800c100582024504 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 833129775 1250 833128525 833128531
    0x1b0b04030609020a090203011205120a05030105090405030403170406030c0c120e040e0604060903120e0a0b0702031903061503090b0121241407021509070f0f030303050603060f 77
    0xc020448a002e807001400440280d084005841e10100010407182a5412803070565803042c402c03603500d281c1000d401230840c01103012490024074104018403941c10080ca181ba0031600c00c008481c24980c40e55200a80c5a1010714450342d072280c003080c1004000d07894022102c20b18027900b001103500c05e031504c500410100c00c06c80300c4284000d000e10b41c44e540d01d0740e62210070b0000d01740041d5216130400f454400702034002d0030703416030005017011100500b1384100d203c0c0312001803603c0c0080c98040b50030b9441e404202801041c02c0207501081c03001c400814000b450000102c1200d94000410703a082001d84110614450840c0c0708141c58090f80100180d0070098050540340c0e03030385100b40102d000c0d5051100d01040900b004107900449004207040c00f40301c2e410501070516008081c80000812501001604021a030706401a407000c40c550500742c040d07070226500400309078150740f10300f03803a02c0b810058060710341d002001e40d40900a0030020305905228481e0010001c0740035241605003205405140c0c603007d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 833131025 1250 833129775 833129783
    0xc030c0b0709120b1527130b040b100b0408030f07050c03071202090f0603060610050c010c020a050d0311030a24120b07091a0c0708191b0b0403 63
    0x1404100820b0058a41d000202030070540c0c0ca090008900c1c10400b0050243d500003500000b01c07500040520301003101000c2e504138042daa00b161110030494052039000075020340b000e213403120340e5000880d14440c2c581c0d2180f130050401040710f0a0200d0245011940c0380c0c80300854143c180000d209110010003103036140340104502d107440307608504019042c9481e210100d580352140a00c0010b1141000003a4113403240200d400721600c0d5503a024201c920b40d8110f40142e0315070030140002c2c41a2401e210f03543c42140c540e1070614101120480b25070f013128602c1d544c02000d070740000c41c00700400104022104524455250520601c040c49064000501014000601c003e403651840700740c0d00541411800300003208901c1800c03d5a454411040c02c0c44840c00545013003800600140405000380b86240854013014000340c0441c030020045c680607044812508810b024507000091000b80c01c1140d141c14011000201c00354420700d152852a81c800030280c0c201100702d0180800c40c1c011440305076401c89400c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 833132275 1250 833131025 833131043
    0x1090e0307060e07080607110c010207050108071b0215270d02101e0c0311010c0e06070c18020a020616020703060509190c06090603090213020903030d02070b06100c030c 74
    0x1004810341c10701c101364000341d0341031180d0f030100111154040348000394050382030140c440c4204944012a02d502141c041d8074041803060b804144002c3c8210990b0001420f0040e408030240ca103540041d0104c04400e605901504011418407005544440000c11a6800769151280303080c0100114680d5802014040d01c600c0e601812200402d00580c5144e010400c280c01c5020070103a4007101400050540000fa0001190080c1482c2e83e9001442450380c8040c158580e4408008000100451540028012206d50b90031280008505055035608a444100c1c50750160312540c001d000289001d030018648070a00011081045843cad4010a0100c103481d00f0600c049403075640e40c1c803010f2410314000301c41240790a03050020403e0060590700300080c2c6050381d54062010796140c900710107540c41445c0117540300c0750072034080102d403255074014a84044041c060724208842103050b40d080343c2040c0425104400c16200708802880c0c440000d08100380d440c14002c942d22221389004020032143d020081c003805c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 833133525 1250 833132275 833132291
    0x302160b06030a0c090c142a1509100509070b03190e0607020c010908031c0b030f0d03060302040609050f04030e040b0a1205070608131b1d040b01090e030706 69
    0x80074421035254581100c131410346a584c2d041e680c0002d00400c06403000003040300c0c1c00328040320428403c8821f148018a26461810070003460f4400b503000c2d01c9880c1041d4803a00e9060140801000707800c911410800c0b0103050100307184140135046e180010b160b00c1407030304111800d200f02c402c00001e0f25002000021101013209100d00604000c0840805a00041c4100c2080100706a800129202800c10a07660254802c1c0d07100c881c130b0380c4d90140c10356620220070410100543c8101c3d581c02030400480040899110b0381d0400c20b428103104030001403000181d1102030510032750030705004240090024500070025890042c2c8840b810200180c4000c0400c07941205000382540c441d04814030700d490042045040e0366540d6141e004480220808075100c4c00b6881c8001507050140b00d286104a03006660b9001050095450740100c0e422042c0d4640303883d00724000841c1028002d0b0565085412240c000341090a1a08000c484040144d002c009518105032030015482c0c0b000c820f65501d10303031025000c0382d120 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 833134775 1250 833133525 833133529
    0x905030c010311042709050d0e2b0501020d0212010f0e100302091305070810060e0610051b01020d021209010903140d0603060c02010213060c02090c0309030d090b160302160b06 77
    0x390b0042d4017880042c4c06c3c0392940d014040c0100359502d1030300c400d880b403021108480301440748003070441c0040003261084465220b00071200001c00c9604910078800180782c00810072100d02282c00c00200c00181030080c40040c030a0208000a10000e00311860762035041e8a001001194140d480d800000e0044003040085110007014400160185501c0000c1e15009622004442d5a0320348900c903a039085410004c0001e050b031812211903010300c00c068101c80304103078802c5040d140342d801000042d1128840000c83c002406007880035014042c01a007000d40c2d6009150b001c2115044003500003480c5925107a403034070000703810070ba51540c0180500c14698440c00c070466404014105948040c0015042c00c180005442d410350050401c10400740c1c103a03285503100c000c11030310b02d281c10300b00941040d01c09010450788049003004d15441000401124504540310040e101036840c40d40c0e0440f819004070b028401d040b050702500c2c00950407545400c508020300c0c060208500c02c68010003603d414403110100d2915 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 833136025 1250 833134775 833134829
    0x1a1914160c0203070b180a0515030c21010501200601090b0d0501020715051308070609140f0a06050a0c05090607023c040b030604200d030905030c01031104 68
    0x201d5001015200c0e03c5984210400240d0711100c0c485050741350801d8034039524909a0401800d640b0041c140c0c080171441c1070882d0800d81c1c8040c4c0ba1540d50302050203070134401844201050307005640121510a1940740000140c00008054802601c40c9814007010764144000500345044503410407001c9000400070300411225403409a0190280d4000105517041c0100c103014082041c0180004200070b58a03883c2d0a003c540712140c0080002004015580110741c05030800035556006620032800042c10000c03040c945400d519008145410146140090000ca4410554441c203030100900040318070007001441e40c8900030ba05e5214140101e82d15065489555289860006042200300c10300c1c00c00c108a4286204008000019030342c1d03180304600360600d030244844110000e00100740c9621255903c5442c0d0034454600d8903503141c0b0040c6803a00761703100e13044003581e64001d17207580b42e40504110a15040c00d4042c07000c42d050500f8495038501500c0b1a0003100c08544003200c20700c00b219202e407414042 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 833137275 1250 833136025 833136047
    0x3910051509042a0f12121107120f2307051509120f0d0311070204390206010e01030f032a11031608030a030b0d1a191416 53
    0x5946a4101c24483c2804419020b0090340ca007400c3c03003c030003691104070600c0411102d20007800907801d007404d40100b5000d026184020324140d415510b240d40c5409100130104444402a6210102c01d079051081c841d401c0400e24010f865094200441d0000e0303401690303039040600c101c60085aa004d03264613803166031000c0c0c0d0500d0304001c1624011110320b0000d241d444514101040480c01030358030b0209880c0c02441201000301c001c0241030704110b000c1c0c003004014609001e040190001d164041c040d00c1d10440980302c3c10b030f905006c03040300e5282481e4000b880d01c0f8050b00032503101034942d001803011a41c10301590f414140d0514040114500031a01d100800d01c404c3c0010b00f8025664074248100000b01000020040050f0100c58440101d00403000c800d0801d44507221454000704988065180b294200140c01c46028082141c4000280d498032910701065902040201c613030000d00404030035146403d820000305140901045904c00c121203411000580503070b40d180b1441c084103444c180600d0600384 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 833138525 1250 833137275 833137313
    0x1d07050306150315040c030510140103060c170703060f0f050609040902150705150a09110105030709271b0509010c020a03020306040302010b0a08010903080408391005150904 76
    0xc4d00d410300d0301d800c441d4000640011107080c0036100290024011603c140c03a0305c18039009007250315074a151a546c0092100703403100c4040000c031070803e010384c00d50818030030b025044950700080c407545008145007100f52a600128404144c11008100315541c020950310f44480490300094003075040d00c0003d1001d00e40000103910340d0000300e12032041c0b00e400710b034898a05a918104820350768540c400b90003151280d0b84001d1683d02c0e00c2c1c540071441c5d4441c201071136001e101401d145105945a40b09032000d05501d10980e242680c2002441015084502a4621405c2030188019180400e10809041d6005001902e410030103084860300a5503520701980f002560040d0641ea024141420004e003c0d00044a00c0c1e800b1f441c41d00c80010701202d0510424007c640c066503151080c1e04d5a54403040180d1100da16480c05042030712070030028204105218407074001c1d88890910040e180c014260800020700c8600c1c280c1031400003000314400a4000e50414000e003100c61b501141d03100d1406400501403122449 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 833139775 1250 833138525 833138563
    0xe010b030708010b01020c1507120201060504111e030105010c1101090b0318060711070b0c010f0608030c060c1903021620030f0105011a030403211d070503061503 71
    0x40c2c040065101c01003154080c4d003600d000007041414000344140074400342c400d110701001880c010480600c4443c54008003440041071043d40c0b4400030b01650071807003080b051540c00180e40300f029100c2c00003048200c11849a1103045615050010b40300c000300c1e02025000000e1040d00e060030340e100f0054480a8184880080c0d1641020b0f0204e04400d04840c01200c468840c4c5070219654034002d08007003105c0c140c4ac50003041142d040c903000c003000b600808030004442d901ca0390700c0c0340d100e000790040d8005482c05c24000c6880b0340c0000c4a803464114090b008071042041000024070301d40c1c0896403004800e00904005d65039414400d04829014984071000d0507140101c05060066202c2e89038002145008800b240e001c003040ca1556400c840c020320440000313213a07011121340c204217801c001c0d5a205000382001d03c4c0c41c121494903440c03a540c1c403046812009a03500308891510120304070003074500072088010107040e424140400d03681c200141c9080d800500d8013441c0781c1c25503030410581c0e0421114801e10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 833141025 1250 833139775 833139779
    0x1b1c02120c03160905060d090c05030d05070507060807120902060d060b040501111b21010501083d0b0a0b0d09050f0a120807030231060e03030304060e010b0307 70
    0x65a00c640094600f842d03d81078128515030118410440c820540d50b0042c0800d280005c1024100300502c0380001c02c07191610b062100144994092002c54580b20341074640c59512900b07464018144012600040c0601642c9410301c104254850030071000c84819020008543d002800016224015031180700300007800c040011648029084c0984200c0d030003a2600003400244101890716a008404002e500103218103120129181201045040c2201001c0d09108400b041740503a0035514241c000310900d0780107100d180b041600c6801210001c00d540c0101c0300501200300f00001c00c0b080c040200510241d1a042100e0007a070341e030001178004010500d0003643e03d111031040340c0e0241840c000c1c161713483d024084050360745420118507544241e40c094000c80401592030740c01e0310f614001600950405a00380000880300d2070040e81150b50403046ca5601c01c4c0b414035210f0798840c01d001f0b82c100f0410041010300e88803503038800000303481d00964004804160300e00381c2d4020500521001070000c4e8035100b01000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 833142275 1250 833141025 833141041
    0xc0109060621030e0420030c0408070b040513050621011b030b0607060905030d050108010b090a0c021209060d06060f08160801050108040203210d051b1c0212 69
    0x1101040b621441180d41d03940c550510440420160003801901181c00d080742c0716500d16007a44a840c01460304214070540d607202600c50066078004440005200c84000703030901906400308034000003494400c403100c2c9041d0800022854050b80d6000b40d05204e9142c0020540b01d0f6160040d503400d0210812101f20105011880315003c0c10400c240e44c2081009244034440c5a4400d00602c85e0307205c1c1c00b4114038640782d00350b03541d0030090024000a9540c0c4c081440142d0b05502c150082500030407042c400400c000f480401041140040a00107181d01c0780303803100c545819a00400d80c4410706946c0355105440d010804046079940c8680706a00050030315000b40400d1442c1c0100d001d8031918907950325803034640d550200c201007a440729600003002c2036425004222641c400c0e80340640c000d1014050b51944440105014113400103003000a03460b4a0102d01403896011324401c0c941e00c0322100701c01807106c2601100880c140c1c803030b08004441c001e40d07100d00b190b02c404494044602103801c84081155610700805 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 833143525 1250 833142275 833142281
    0xe030a081c05010906080a0f3e01020a0224070f0b0f1006142209050105030c09040c030b0408190903020109080a350f0901091a0a140c010906 62
    0x803540d1540703020004903c1d0242d601c604419a05040018201d0403056116640b00486280088403020240e040140c107880c90b240649c912030b401d02c8000b0600520b0300c4840c58080300c03510410342c110760200c404a40940d946e0078a1410f500c0b140e0040103402820880100c101c2d10800c03e01803c801c401407800300410000001240c841c1d00400e07454401d03504c03801c0350180300d05400e11854001813030022070000e14294160003080010b04110020203c1080803004c2521904103500c400906540e07500100882c0c102840010b0b4461b1045680c4000c0d45000c0d034030400b0041044c080605118a03180010f8204a01c690407030308007003010f00f0314402802d0401001014411207020403400154468000502c07144002810301295030300070580400000c0d81800750304002840c008a20324403042c0002d05820020010040030ad8450340480203554408060026024202d25803200c4040c25110800045182050b0140ca4400c48640b5050b050964402e24110003400764211024541d40790070844020044558 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 833144775 1250 833143525 833143567
    0x203090606010905091b0f04030f060b0a0617010e04061d0616080103050c12030f130e0c070203030a0e010207050a060c0501050132040212070c1716030e030a08 70
    0x10361003c0060340c40b0780501940d6101900c4003180c08500e02e9030000241d102d4030180c400c0c02d046551990a2940e640c27240ca0b09180c01e80010f8032031395030f107014400840c00d0101000018012a0401c2070444c0a00e080350201940c0501c03440701075081c848081010860142c20220002071024810780e00621307807200c900d13150801a14149000b209000703080f240305004009580c102d036040400741044078685008d0161843c08001040791070300040094a50b100d140f08040e0048800c503e062144540c14030320781d0803000201030000d0401c2c074000e03c40b001c0145d40000c21a007280d0604e10304241c1d40d064020060780b82045075005240d0000744600c02180c065444040303110400c0c002d03402441305903a00c4d04d90b8150340c105000100454044081441c1e05c10030120300b607405622000c1c20062900200d81c0c00c00c0351804040e14800c00045044141105000603107a41c0a420382c030359200103103460007a1110049402c0510001030038400b41e10480030556406106400c025900203180982eaa5030902040d000b2074801 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 833146025 1250 833144775 833144777
    0x406050a030b07122315040e0d02102d02040e01030f02101718070f08070302010906030c0206130510060305010510120f0b1008030a0e010807080f040b0910020309060601 74
    0x120105407104a030302400e01c0070030345c0c04000d0340302002440d00084c40100041000002c1d481d0420981c0d11625139124001c5c074900b0788009000c290000b070500a003454200391510011034100080c07451100c4828110303050000210002080e071880246441c0080c0c003440c0e200d484140c0d00003000100384059200520010b5108658941d48103106400c00d4558051090704610030341010400a4410520176100c1b0007803a081e881100e941654500d584614220260411307443c80e00103540c104210750b041414100074107c1400d043c041c1c07514800c0003d59401d0020800001c1c0e240305031040040c01424001584180142d440c280000d68076270500c2c3d40a01404d0b285005500c58201000954a405160080d29207034846007620540c422902e2380410204d0160a040440540d40400240c55804000400022000b51076686003001d04070009025040001c29400c14080140100301d802c204a8401c954890752043c02da0019171549902c01340f504810b04d82000e20203200000b80121030200043c0c4501c60390302 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 833147275 1250 833146025 833146037
    0xe131d150a050601050705060c16050102071a10080d081803030f0f060f01050f0a020325030210050910090305090301060b031b0a0c030305040201030b1003020705070b031b03060406050a030b07 84
    0x1519004480d10303c6001b038040e11176007104003c10390191012008000440c001601c21010705130b2900c580f03089a02241040364503880700340d458076a00c1c240c9240554442125284804294900344040e9280c011a40092042214a500082106910380d2010800b80c000b141200d4482c50102c0f0040302c1804165656484003141e0070014043c0d00d806190781da800901a0b507010f0030415015110105900304011490560100b80300504000c07850000f0b1001c9242d66507100140410f5508001e130400b9000030443c00e800b03040204120340080009012070040d02c0d031400c002612000c40c20121030a01134071025070b03819400d001c00011600a010041d6028040c1c2d0000644125242c014201e071501c0f914400401150119a460700400e01030780c0301e1a44980181008100001c0a500269020b8942c03d1804046640424544103101c000c012040c0500300300c032002440d5043c09a010f28619060b0009164001400400584585c0340c035001000100386c05000b0401c070b1922443c0c0f41c498220125240400150 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 833148525 1250 833147275 833147281
    0x108010b0408071e08012a08100b1b011a0f0303040602150405120708120603300d02030c0405011706010905102f010c0e131d150a05 58
    0x2002030841d030403140b02c50014411940303005594081119003d01450b590201ca03040090488002c0c002d0380b40703002448000390442040c03502c5aa10920841c102101004240000c2100100b0504814400d40d0003002845441e1055240c01c02c1000f40091406030a40d428040500c1014050030a0391498600c00c4995568618600c0c0506030703603004d02c0c42401c0c0180d101d0103042980060b00112150054013038001e40c0e041080e0780c0b0840c06540c2c0a01001c9a961400250a9405d0071140c10866040300003117002e8030800c0c1c200c00d22032008003800b09c88a941c109018008400213001ea00840c2c1550301000025500c034682140e06020f03a4002e445898085410b444c85095900040780c0c84601c501d0058540e8480c10341060244a0260703050103070362042c40b08401603000342c1c0320481420520f00e034a81c02225801e206800d541e5081d0750b211001d1009100c1004211503055a403004149055403440c500061f00030005501d5202d41c00140700c000c00306001310341c1080002c00d0b40764269031090910300d00502171a1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 833149775 1250 833148525 833148539
    0x150f040513051e0c0d0c0e04080d0e07060e0303120f0903041707090e060108100f0207020d0b180a230106030c030303020307090f080309040f0f110c060106030c0f1107030c14010801 79
    0x1084140c024412a251b10050000001e21030a59404c28020700c1e145040003095507914044070540b06050205a102840800c01d0513840139500061100a802544c200720300c0040c004a00d4102030001040341c0c42c40d400054500da001c209680007070500d0300c04401d07800e801b500c1d2561204d60038003501101c24100a40d9401800b40010150b040312940c1e80101182d00103c440d460041110008405880380c00300300907030241c3c0d92040c00d02080b90140002d54103500f4414901443e40d141d42000840e540c01c08800003011400d52240107500413002e000c0340c000c115009000500400c4a17410040076188405c00202c10b0580c560b01541c855821616018603054550980600c108900d11691207660300800140241d81043e4121000034002c0e50000b007601107a0012440646103105504e500c0000c001c101c040800b8410031280d4014051707420300f08080303140d14400800358500e10019070b0500c28402d42c07650f21040200310b04001550815003410542da140c005451007004040c2c15507000403800000440c00b4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 833151025 1250 833149775 833149789
    0x13022716030506010f0e010311030a02180312040b071a04050a050705040510150306050a060210060e040c050d0807060903090501030507080106050a0f23030906150f040513051e0c 78
    0x1e5005845541c844800448206e618650541d04581015115800b40c941c10243e54040c41c0580301c20f041c05601e500c3c2217041211915200d01c0090300c00c0e400a05501c0180080c80111030942c0c42c20587d8540e1001c540c102216146c10640b0718483d062807040030441405008200f01a82d6481602038507203082e0349204100a80d8000e03205207410001849041001100609125501900d5400e0104015540e500003540010a41c0e0107070b4090382000308070400d10b030b80901c242c001800c0198442a40d034105502c45140c9010140945402002814100001e0003045400c1e5145507034040810f00404166140c018528a481e2003864040707414040803498440c022100705041c2d80c525980c82c0d0a02c1c1c40e0711400c80795080d00310855418841000d03041c0240d00d482502e5540c48043e41d500c00d43e640d05214100c0383c43e04800500c0c14016610b9072a051603da0303986886461210070031200858141c480300205c03003011072003407001070641c86040d00540000c08180000210201103c0c03c0c0e407400c0000605201700 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 833152275 1250 833151025 833151031
    0xa0b0a150603020a0c0204050f061002030412030f0c05070603090c0509091c09050a080106030c0b0a21060b0c0f010f02090102100507051308031c02070209130227160305 74
    0x484003084405002031842039000e8596100c0b180b8182c24242203e40105044440a503586600040e00c6010000281005554510140c2c820710046150034a0b15520960308a020480103007004050b0a0344280d080c400d410604040382c0020a0341c400300d44d100c5000d0b0091000c804121206081468001124a402c094030340c401d4a500016211031032240e4160f100211401c00040240442c1c090046101e403a10403d00d00a07001d0340c400010303214114100214139010a900c01d51724034a0402c08003907007a17071019420001d4401003c1200c0c6448a03040440701401880e04424986900420b840b101031000082040d140d40300030008000b066107016049041e803190000c2035001d60702280d074a0950b001280e00030740c0e02070f9040c80c00d941003000c1c0080c420081e00742584500c450740d03c0402c2c2c4911084072003020080311000b1403001c41c07904400e070740400c0d80004003d1007021408081007010065484100f1040242641041101c121065213403031400070a00035a10341d1200c102508640d4006c07400b912940340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 833153525 1250 833152275 833152301
    0x807060f0c050613230a020a08060105011205150d050a1a33030d08090d05090d03050c0c12031210051f05070b18190b01050f010c02060a020a0b0a 64
    0x1141d95558044e02e0181c8160f400899200803942030040808180c03803200416800513502130300c0d03200d1190040019141440c3c0002c2c00b1504404010090340c0c0c2c1214448070942000c44000c501942c0345400038024075280300071503800c403000d000902d04100d404100d1007103091041d20940310201c1c070020f111000c070f1821240c0d803181440c611140b00b0700240540104889105440407415106001c2010904000e003c04000c00428202c0c41803040c50002480750951403501c030b240031401c04480d0000581d111800d52006010300c070b40060030403051141404005e02810703001e019031440c1c01215010580e6035104040c8060013001c4000030852120340002c11408841c2c0003048941e2410481c00d5045450401c4811036051007000c100c1040020340b40c1d030300c080c89070b0f00310f4119003480d170050f175081c50030098a00c06a4030300c40c00080ea80000a1082a078035419610180e8242964062800059400d07070004400a540400081494486903034001000420f1910411102d4019203d2501307450603110000c003d52 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 833154775 1250 833153525 833153533
    0x240e1807090b030c04142a0a030b010e1504090c0509030c01050906070c03060f0609051e0c160b330d0804030209070f020105240909070b040807060f0c05 67
    0x12954070340c0011012200c001c00b52008a80d4900000e0704448804402281c200c00c0b01080200c407a1041441c510401c040d80f05611896074080030860061207100082030a02d6a0f90700703a00c3c00345e4401c0407040b01040010b031401c8180c03040455845156041480f9001074541031000c91102d092048007650004d00000d00100005a08280150b8147d00810041900b19006010403404503143c801c040c0021801850f00062030312070203541005070360740c07900039a1182c1d05060600c010380d9213200d422110381c0d2171030f80d00c40b105403560801106644107811400302c0c0d00041c0200c12042c00310030b820036801129039000034200391910300980b020b4000d40700f18445164404600c90902401c00000455406104403c003e1410740c0701d83c001002403800351103520000314100070360261280c091040340c3c3c1290104003900031100500c105584a04d1085a04501541c00c10020a031456030410a040162a0f00c9203815240c03a110811a6641c4200b031040d800000c80811207504801c0c0124a60300106030800050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 833156025 1250 833154775 833154779
    0x130b15150d020c0d0507171c0f0605030307051e07050d150b0402070f060605010908100209191e0501030203040b010e070c06110a08010b030603190501240e1807 70
    0x8030566421811800200e15000c00034014a200144000b40202071141c0703400780c8494003402c01c02180b108103468541d076000c04002c0300c102030610303100c00002c604801c04007007002c029089410340946110340c04240c2611021807240c0c2001000714191036903560801c180460329400500480d920b90480c4105500004503040000105140403c3c0070304a11001c0404903800c1c0411010400320382c070140c01a2024400301c000031041003100d00a140050500f46001022141400040341e00e9540940035564a0355000904414944807820030440070001e00708202d0b0404c1d50340c0c070b030303c80c40e640780109124080c8005040030859601900c2600d00540c0c00c0300a902b420382c01c1201c5000e203041c020300000c0510506401030350000724680030f02c440025520902c59102c02826401516000041c0c005590b03021040c0304001c1c694500082c03060302d4501d5070440350b84d10f4010f030400a0061041003121240d00b1070850264580e000700b800041e003212030b401c82d80d29460380c40c0e44401015510314050030220743c00c40142 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 833157275 1250 833156025 833156059
    0xc0504080610140d050c030d0f080702072103020c090a02040305070b071e02130e0c03010b0d120c03051207050315031507120f0509010b0a083012130b15 67
    0x1101684921500c12140f10201c50400280b48c2000e10041400103850250f414148548c040b0940d900100750340020983c83d41403007140500403404810f8424101c09810940040c58400c004910701c004016090903d141414410301020f58030a0109448034810701800007001949141147c0d0125040880d144090800308240400e0100000060368029a1620f1795007031650340d4407404100301c04503801070080c0a1140189800d50354411051442421402207a902141901005482840d074503d03114610a0080c035064840e4003604840c94141c1c45030000304003115400000840c0904c0094114040c102444000c1560f05d1144070583d8041035000404500102d02075184069010414800030035403a016580980464408540c603803103680d110b0120540385d041410410300a0044800a440c010070550f203009848030304110340800010007a00c010310070a003000203442d0700c12a541c49179a00c074103101035030b1100100c3c5081c2c2520078588100c0401d46000100d0311081755440058001c00d1141002c41c9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 833158525 1250 833157275 833157289
    0x60b040b0313141c1d0d120309050709060303030f1806110d140105093303150112200d0816020a03050708062206020d0f0c050408061014 60
    0x8000c40f0b03000c2c0001038030a14400180320070300c1600f15058000140400c49403000788401405890600c0c1c414004400341299200ca030003544501e80c01103404a2040c06141081740207100c8084042e10a000b20700c0f000c110104036820a8040320b00a035814410320031000400d10880350311070b420040512221a0050000e84290455070181c5141e011035400c1c400c51415035410307503c03003659021700042c1c030600602152a0078156207800c810080424041080c40d42031010310380601e4540030454040382d00100317090b0754081040c510709030050780030010656924080080001c00c2108229200000e20729558110700d011051840c4814000340442c9a2000075280d0b45034903448000501c040400c101b00003c00350b194413000100951290006000261410246a0505c4d2005d41012103400110001107a4820420522200c194100c0c10040c2e48180c1c0b400307020700402094000c18952400c0211281c1030942220180c0216244a000e80303016690b21130b68a0380078101e90181401c1008a00084102400c01c41 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 833159775 1250 833158525 833158561
    0x405060301060b0d0915180308040f12030614190501140d1a03061501201c0e0301060503031c0209220207031209050d11030f160204060b040b03 63
    0xc0c000050a035140c640001c0103900528410b9021512841c0c0c0e40c0802440b0744541001e400d0304c0c3c00811600014041e40d00c0980c8250801078100020f541c041002e000b20b50030f1a10140e50b0028284400700c002100140203000188115800c24a101c480156075041c0034440c803195a2056107851489403c0800565021500b1880c0c145d407106d040c40f0400380200745118581b910202d40d00300c100b580e45081e040610b02a00200040189c01020741e400000741d0300001456120b905042e490168158000c072400d03d0728041c170781404d00c205a42d241102030607822007410040c0c01004e50003484265181c4041c199a4460110301000100e0312546c0d00300810001d070b0181800c104010882d80c0c000800711301d00010b00460034081c02e41664006080ca0825802051b0081010302600007802500c2941c0c6500b170300d03144e810b01c030300080c07103072460b541004140144102c0f40c2d10200c0044240c1c59240c14180310403442b84842c4100c0c0514908140403e94a0040007910116070070310070a0383c40c0d07075210700480c1e1f40d0b00d2900c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 833161025 1250 833159775 833159779
    0xa0e04210302130315270b04030e041b0807020a030210020c120301030501050a181101200a030504090c0203041212020723100311090424030305070605091b040506 71
    0x2072040105031480c1030700f890010f501030380e80742e00c440507001c980a0407124030f1702c0301c00b90480589003088040000c2c49601c221880c2c102c10460300a03615401d0649071101015400c5911601d004009207186004400090101c2103550310300c00d560755a0a42a41d0781c50824001a0151f4045a034035400821150014041c100c02070b4166600c54100014082540c2c00070b820880b10381e51680c1c01c0090403215032103908403502d000006070741010ba0795215800e02008a108050403c05044452800d840001041c2030700499040203d5140070030605006000790458010958031030700301458010360b40e1001054605036540800341c1030f40403181e651056444a04274441800794000d800303001900300d81c070700ca4a9100c20822001190201c0048080024000344100c280f41894a44801d620480045206031440914240c50002c2d01001203501500e0603480030131408034130000810007104056101340a81800f51144100740020380325440d00b41d40319154a540c0400c0384910004282180c0740035003000b9002580 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 833162275 1250 833161025 833161027
    0xc090405041e03231215010c02130b1e03070b0a0c0c090f0b04050408090f061b010b011d0d20090406061d010f0e1b03040507050a0e04210302 62
    0x302e2031a20035081c1c004401c2d0040703441c50720300c00030050382d03100a0141400c034105207524000d0503c00c0d511103070b080900400e2404800901c100f42d144d005800d0045425002070024001701e81c01c0d000340c0d0103000c020f51554010341018400004403141e000c11070400e5400140a40400c0e41400e43c040001c1e00040307803403000c1040445608011881c1140c650000d812103800102d00988500d5041050302c02c541c595500840c50300003000041003800003654980b0008460010810710303001c0000b00d040c0541013a0040300c030340d4081149100c2205500405200f13000380c0700e076103a04040009960414420b0121642c00540e4443d0305e0300000e0014612940b03180300c40b00c0e520803041903900419502101200c08039105941c440b0300b484440d40d4040c60a00000541c8940380d55036051405840e1600524030510924414407400304100c0304501654150031840101c4c2103849240905040750351300b403540b140134000d00c4204804500814039044551007590040c031680c100b2500140c0340e03440d1902d5403c241c810154 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 833163525 1250 833162275 833162303
    0xf0b06090d051905010504020f0d0c17011d0c010905090f060f010c05010e0c0301151202040906020c0a06060e070309050303041202070510051e0703020a060b0103151e06080c09040504 80
    0x9078143ca040d00f03d401000001707040d203024030500200401044815214a202403600400909500003280c1910b190080c1d407680074400c01c610038054420a203514290140d540b1002051440008098441c10782c260b841e17810103503544c81408101c580c1a105c80c071070006840c0001e401401c1000c00e060308041c1c10b2403c5040706056889031400c580c4030034858000b5070040166a450f61800740101c42d5800b054a4103143c045160200100016011020090107942c036000c4031402e001c43d9034180e54188d47d26400b40e80c107400461515200800c138a02800c04407900060110345030350720921465a2003076010004600d03540701e58407140b4651081540100440c07180480118450b181d043d02d0081d102d92649a40351509500c01421058100f291004070301d5103418070040b40400d60008251a40940201001907c20241e1004034090700200c56400d00b2910710280000e6151210b03403102184420032104207480715202c10003120003070303070649040e014400140080340452415600440e00644102d00301031081d0303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 833164775 1250 833163525 833163553
    0x142803020901080604110906010e090a0f1401031205130303081005040c050d1a01020d121503030906171014030c19030302151b09060d0e060601030f0b06090d05 70
    0x2003d03000b03d00c25810841c1030008202807402c4a0701800030031180f2220514003100020000d144800c074082c40380c035003034000c40c103410318035884904520000c41051001c02020801901000710a1004481401031403001c15148e80c0b068095545000829020071a46440c50b10200d0b03030410040c1c81c0195422040000041680d40d0784074a941d0003905031906500c442c8030041910480740b43d04100000c410f5040416941680d003c1a03500e0610401e0400b0300302540d00381c9040300181504903401090f0514160080245504004c00008450040da01c1d11201c180e10750307a804854006407100c417250740340d41b1018021010055001c1e052010040c0c01c0302c81101e00100010b440d100c4030340d046101014140030034014160b0501031901ca00c00c0440e03580041d030a01c8142d0600b16103400c41c144030650000700c0c012410365184000c540d01d44480920178084c0700341d00301407240c0311b42040e510280441c0c03901e0340c0180c0358919802104d5841000812070b6003040a51810b10074040c01c890012660340c0190045000d0030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 833166025 1250 833164775 833164789
    0x509040809040603200604050612220506180c090a022d180607030e010e0a0b1c0e2a041d0607170412031d0a0303140114280302 56
    0x10360084041c0552440065005d50464407a20102401148200000d0006889000c00c9a0528442180700303215640c0e601c120140c030080306503000f0452400c1c0c90f0f400080c00310020305140540d0b6480e05000200400f003104a0f62074818110715138208000341c0015103004d0059001d04400780c2422510f00c0ea8200841030f030300c89242120200150f2401c085510501c04200300b100040b00c100075124180703000d0f4035450241800c030181c500e443c1000003001040d50380740c55940c0204014090315420f540c80b0031008181e1003905e1410081d040a10340f030070101110180000580c24036442c588000680d541c0071510004400315295600b458100391a134002628410308055074100344000c080182000e03041540c801001c00b4400d12400e11468505010f20020860320380d9003020400d894200002e8000040601c000361411a0014100354000c1c036184209141d01600074480d9041030842001e40e60780c9030703031407440b2080011003080d820034103d0407049890701c40300c518400d124a0228045103c3d59403580040d1503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 833167275 1250 833166025 833166029
    0x13080a0f17010e130804090624020304050a180b0402270a180e07080601060513060e01081501090806130203070b070b07050a0908030409020d180506190905010f150602070f05090408090406 82
    0x142d070320421410b8001d427044403c40807050781900c003540c48c140c40c102c0003c9a41082d030150440d80c00d820080c1160b605150345c029046240042d0065403501150f000d0140f40b45860724580c2c181c112488001001ca1402407a401c050700c1c044081d6200f04662420042e0052802e24280c0050384100440400c003c442041f0403030091080384c0d80d10303907500a800c080d905c0000e079944c085001d0103580c01280c98280e030003590701980052010001d80320703403089400403104803000e5480808140a01000e0145070b1660188108106009500b15400c150b50382810903018810500003905d015040408034403641d1217080107049064080c03921035011511002124155401030b4020040950300242e4801d0160090050b0000e025558540385030750199500e44d0f64860310000d0a0000d0000302078090701800900f907201d00c0b0603d0f01328008000d4030001c100e5500080c0b1445c8000d03151885401c2002038224400241c16080e510580c40039082d0a20348401c0c854422406801101c030500d080c000c44005440f141b040c000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 833168525 1250 833167275 833167289
    0x11b02220207021c0309060504080316061b09140f06071e080a091a09031c090e09010c1403100302092203180503010204050d080313080a0f17010e1308040906 69
    0x13400c420b0ba49030140041005074010030900100f40010400c0d003c3c0031043c1d6455014840e45004682424074141000300340440c00f407003a55404420102503e540a0003d005482011001c04603041c03019041104100d90604060f40c4440100b050323030001603c500c80752100c10b080030900d03801c0680b0741d52018074a0700b103c6041000916412000c03c01c1b0380410010901c90010124554600078480c0c01080d2203444821400002e00040c070040705c1000e200b941c3c020010310305034440140358209218024082e000c402c060200060051552143d52010402141d004000d0310030f016006510b17590900940c2d080003061411081020100326403a040403d0100380072510940c1e074150425003e440181c1d40c06039a411070740c0660310502091150b0f448040d0811046500120300c1916555441c002c960076051103500103106d2540480c2c41d00b421030300510340001d450354948682011110040030110000003d1080d1402c242203d000f090265880f000034202c03081c0964030080c5015220881c400a03616140e110803 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 833169775 1250 833168525 833168569
    0x30b13020a080f0c0103053909120c100e0a090e011b020a0501050c0f0d0b0d05010912090608040c151106100f0f03050d080a06051c02011b0222020702 66
    0x41119a4103200b8203600c052109003d2464202e818445108841d41c00681482d40300540303544e108415a44095441402000341050402e072000c0c0c041c2b548418801d89520b01960703d109008030014090308094100c000d000d060704540c107281c440380c800500b070700c0507001019560302c0010340b821511502c0304c80c4010906400910004040b40b40450840e1001098118001005e104546d0170032a020200d6492007890040450a09102d1000a080700c1181400038102c0d0704e80011402041480e81101046801d80d0301c941501c1c0f40e03126403d0703610b00404c6070010100078183c081880b04103850300c04120000140d160003041054100c101030300d843c0c0140c0e851a502810007204005030300e007007030101c00900130341c0e80740002180c69560b07a5a03032101c0680314030040c400032000141c0b040c100c2d0b80c01440280401403441c900100c4000c060301c61261120002e03800128244500040864038802003801e159028003003114190718030a4a4500c1080c1c1c1c07c2002107103408101c0c01015a807410b0b04130414440080a403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 833171025 1250 833169775 833169793
    0x40818040c20070e1303090e01030b0403121b08150a030503030114030102090906041d0a06020a081305120a03020d05040b06031c081308040b0d06060f0306030b13020a080f 75
    0x510348459034810801c0b00741d440400c00f409000c0355040000d8011101011000d81c4140520f4191440c92051b042603ea40601070000000d0100c28079110740034034001e4a90a1412080000d4002991041d91054203083d40002c0d000024502c2050855131007041c81ca0000100360301c540c0010031901d5241c0c0103a50070351022005010502d050380e000c0c0b40200f030490085203002182c2e00820b4a02ca00100010b104d0f6a880c5520810098035188425404906105452f1054803d107820030080d080040300000148140000444503010303030021040c82c03600700004062154004044401e603510147c00501055000e100310754043c0d0300c900032280554414401c041c002d2a185060601e0290114043c0406100c814100200785402c508400c0c0c118104450a04229a41c2d08046400c0d120720b901c00b40b0100000101580385042580c041410b44480b5500c014085c03640d603104800759082400050080c07000c100115000c0501104084a400d00c00392880c0c00d81907452240a040160b101400309082e0841100c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 833172275 1250 833171025 833171057
    0x302010902091012061a100c0302010516020a0b1b0d06091404080307050705120a0c140304060f23130914041101030902010215100602010f0b0603040818040c 69
    0xb15900120500d0309020651801d03c2000030701c4d910701d0010f80345640d151610640603408905a81e1284009841303c8002845440001c0041410080640041d440d01022a45005000c603100b50780d2900c9600800d074907841a2507246800b5400391242c5890421170032801034880703ea0740646600c00610308001100f87c60f016403c415944c4503050701900990800c03c00c0700181842080c0d9400102916001341c03202590702d0440e1914001002c95420302c400442c040c1907440d4000c00c114441c91095041d0b961015413005050759a000300e000308004100e0140b5503000c510300c120461041845032040080300d500030145484035a40c000d040390707007014000b0700301440305201da40144826140d040700d42561600d03264454680a0703441c118024105a00c45d50900c0079688200404040440ea18445060701c2c1040b107103803542d000440c8500b0016500f03128a481c0e242e0002d202c0c0280c0c920014001a00c1c40ea41c560b5080c00da944101d080303002e248540e001c0040c2c0c0780ca9520402c8004141038540107074071604001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 833173525 1250 833172275 833172289
    0x90406020a031e150b03070207030f0f0807060207030f2a1b1e080f0c1c140f0c2d030304080f01061d09100209030709050c0a110a030c150f090302010902 67
    0x11007980640c08006007d44071ba07000510070220f80e0411001d1003401d2080c0b40800e650105e449002e400038070080f640f071040c410154001e0025612030b4032980f5004286110644408a00c2c2000c005110140c14126061145524929641d14401c85c3d039a00203405a40c1c800d406100540c01c100f0034410608904d81c1500c0c0c00410a40141602400500413100c8070440780350740c0c01344000914007034003248102010f80c1e0038054010410b95070207183c542581d40314124560351010200002561031060000302c0d4602d05080c01c50107030072107100140c7c3c410307401c003101c02980c104648155181c1502c0304100024000f842032040818000030000049805460300c59020342d64584403070740c4440e15540009001244800065a45d285201e105002d40c4030041400042c0c24030440e9401400780714106006c03c0240c0d02103000820074413106d919103945680e05451616a5400050b10040200352903081400201e00010701075185030009000c003181c1c0100002c0ea40c0c040d81d04084089000d40c0d1110142d10031464040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 833174775 1250 833173525 833173529
    0x50f0a060506041203140906070f02040f020408210903060a14160f080a061508180c01080703180c1511010b1318061409071202090406020a031e15 64
    0x49000e0b00341410001c4c000c00c00d800412004080c4044005501030115903501540c3c0c20b60340041c1603d49841440c00c02d04603a5011300780c102c0c4514589400c44408984a02c260b5069039610001055209801000455031401076200c05003007940600020000d65403c0001070700c00c100e03180c0701040080705002165280744c40039003850508840e04034400d40c081c1d848504030aa10859150162180e260102500e00411954001e8588891401c0140340c04030f402150705401104200b00001c3d04920383d82d0003a03200c4400d101d40380d00055400021070101c1e44a80c010030900c044980006c00b14014580c0c940100140560207800110882c05107030300200c2d0803002e00901d52406800078003584500500040004201c001034103a407665402140f00c041c4507140012003003586c0440c040010340040250242e481c1400c48042c0301510070340c2070205d1800004030500f4422680640a01529210380d40d60130040e400004604080503520f08891501294060742d8111100842c10001102c503a040c00e01080d4104030307 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 833176025 1250 833174775 833174779
    0x15020607030b060910090305060c130b0903070302090403180f0617010608160c080c01051603090203030405040222030b090d020705030a0f080c07091b0206100306050a0e01050f0a0605 80
    0x1050b40d860311521a036045800d00801111000000380b01c403c0d042d55007170500c6d003010300f030743c802d800802442141d0180180f00d00000101e00c2d1850302d1313a41e68080c10922078505015015001b030a13081006050000a030b5800621906100b00d0a829103081c1d44400c00c03d55100680c0c01c42151020400c043d0808004000e00a03204003400c05913050a20240000388040c3c40c00400100e07204840510038840c0e50020b52203540031300c00f69590046490f0103401380c501a60182d4500d0758100c4541010b070b002c6d104421380b10381d002c2c010b54103143c9407800b00002900580d2095620580a290032144c5001240c8139001940c821104402d9604240c80340728503256014440d44103650005030b05100c1503030b00140010000c1d40c86400107914250380d10f003d091500451007600c00e14410050003048041e030325000083c03020f0748480000c004030b000e40c00890b510310042e6015078810801d414144041100c980100e98044541720020861603c400c0000b400c46004a6010b29110318034410300441c2c40c03a50003604003c0c070301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 833177275 1250 833176025 833176031
    0xc010f11090a06121806060614040e0c07030c02090906101707140f1503010618050f040c090f0b1e07081c06030b0903031e0c041e0b041502060703 64
    0x79a02040701200207002d07076804d000064510f104d0f80002504400702c0300d9611044480070b080d107032030040081c01c018094071011a842c50500c800d8150b0150940b4219154040142010b80707601d400c600700350784940c1e006da0402c0910403544004d81c6541840e00d020b204a2001000189000d0844001040301e5401070001e11540a650010b00c08002620b00700b56541c84bca14200c000c12030000405800300b00d844240c204070403130701b99440c01c18410003450403204280c4419081ca011103220518420107405001d520a41d1640030f0002c0d418240e21040e2042c1042c00c0450f40d00380c455010140c0400c0c41e91142e1488040043d4068480c62401c2c00c401d40c480c075841405007440c146503510581400f501c05210410300c1c0c00408070011040a070003c000550300f010903880941000c0d800c4030f0310f0740e0040302c0300704c4010030600c40c0300300340140500024455800200340c54209070420018443d00c941c0d10161130210000c0200105540400c1070082c001000f00007040c48441c524404083e08017103004184c0d10502d85 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 833178525 1250 833177275 833177287
    0x30501140d02130f0507020a0b1e13061d0309030f010c0c0f050312040f030f09030206040b0d021209010b190b090402030c0d09030201020301080c0f0307061803080c010f11 75
    0x151001401c040d00c1c2d04840491403d4080502d0381d00811452450340015820082401549500441c81d01d40e101c0c05082462056601c0045540390840c026100c9440a0018070000ea03c0c2100114000c610a10580000c00c2c00c00e00f52a150700720705440c01440300e40f40c000081c001d907940342c108440703142490384000034455442440d002400582a00c80007400c0f030780036540d1210030800705100721900c1c0500c07911556240c0c101402c1560454140180403004a03070780c80c4007001003601a164002c2100e0340240600e10f000e040c4410401d83d030b08120000a62560244883d08589001e00400c42c803540c0c25500001d8a440c00c1e40030800080d00040b50400030522011050050580080403078041e40c1e800d039400f583c3d945a444190009114100c804000f0500d00542e6104040c0c0c19002507048419800032100981a880200300c044445101280c2c0c3c1580121020000c2e10b008880b00001a40348610701e100140d81d940b03035141180d0200d4008900f0340d64030441205002c481348a01c90070310004d04e0f200c600b429 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 833179775 1250 833178525 833178529
    0xc12010c09270b030307050607030903090b1801120b120307020102370c15170903040e0a0506011b0605070305072a050c0d0614090a030c0f05030f0301031203050114 72
    0x55111894042a0343c1c550b80d1189890b2800c1088480d069800001c8402c2464001c200038010401d4079000c0700001c10040001034030807401000e840707103418001300e41030240a060006466032591600201e4005031640b51244040d5104201d100d99098010003855555440d031000a040030000403118100211014a00c8401050300c12401d5203034203008240304074840d00341011001c01000d030744040d007407400c1c40110029455100a900b00e604213121900e02c800d445150741c20f6101d0103640980400c540d01840001e056060035000b103034001c075060501b8528840c240603400c59020035110305680b17198a86082c0070010f58103210b141c0e40b044c0710b49001c00340e0045c1115940240788211003802d020703981002c40102480418454559880170090114094008078504100a4191000401d09542c04000002c84cc04400b1520502440d45030f0781d542e00300d0400707503200010540f040c1001d40d0544002e2028030303c040303003610003940a18020204105150710b41a0f00500381e6105130440903000d1001803401d02d8076 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 833181025 1250 833179775 833179829
    0x30e100804051905070e090c0a14060d0504021503071106070201140c0d152306070c0e040804030f030801240203042715051806030a0204020c0c12010c09 67
    0x44850306072618083d42d0740e00340b192828079250425031405a0305070a004070200300180300c0401210984075954015902e00c0113190412083c21600d41141c010400c502080702641e126030f61191006210b2000700c0c041440e4003440d03800c11540b0700080346054414042100003000070580c801442e00c0244080d00418589402d91000074201c5441c0f00c001040c1d044e0302078290b0f0012003407842d40414403e02c103581c942d840c0d400380c0c1a0b140c00c842421440c0203001c4880c2442002c0b11000e40d000f820004610b440c141c80c080303440e0001001628181d000780408000141350852009407a0702940d5070030303900e504016101a0941d02100760b04071007209080c240b05a0754010040d01c0443c0c0080d4245640030604264030f40740c0047e09404410030070b103003031544d4940b4070381080e030340094585c1500c0600c1c00343c900d0b04605600340d0702541c445505900c460b515500602c0c0940080a010350403034251000ca507102008101c900718508030130503169440341600d03652950301c216a4401070105c0044100c041c081c1285003800 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 833182275 1250 833181025 833181043
    0x110105060109090b0f0409210215010b07140102040b03010509091c1206080703151401030c14060d1803080c0a0c022e0e0f06070308060103051b07030e10080405 70
    0x9540c1e00d84011a00d036540c0c00305e074140740180c0640b0030300044100c0e00d8918000c0301d00b0051172109494004001680610001d01802115010750201d500340e400c00150910301d0700060003c60301703982500c58030713003400f4404c1c0080c2c0300421005a880761a541440308200d90000001d148000c168898a04202c1182d2000607800300c000c00c1d410441c0002d07075000c0d60000a040280c10003a2903100b405030010401401d004080f1045000c40c4040241503514847c00301c90100078480540500b424001c00d0145075140c3c00e0441000f980200445d10340000410032506440f8440901054440540903010515070411a856888184412554604414058054100c00e88028003a020300086050396144448000c0300303100754190080401c84007070030014001c0000ca8501c81c154003a0286031040001070400c40d0540705d0f03255141c0c540694a40e1271364011070040000070030556607241207050104a44404c5801081d58070b000e03650380400381c2c000c94140035505200b01c00c801d0821003c041000045100403503c050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 833183525 1250 833182275 833182289
    0x9030c0906090a15080102070b0406050703050c0409110d050c0c0d18141c0c0801270b0a06091d07142b0803180f0a05190204020f030403050901110105060109 69
    0x5108100f1100a00c00c5038030310740242805c0e40c4000f4019080c0a102180035110b1032040c030007803080b0394408000f1429200195000a003441c014001403100c1d01644d00016043e408403444c0c5410085011501c030140c4c1c905581e03407078000400042003130a0060900400c4240c18560400807580c42200b51000b0f440c408501c0781c1c0100004011103c481543e4a248020510320050f020703541030390a508104429005e28412001503601c0c14202c03001044030710340308020344c1041c10090070b202c80c0980c0303a40700f583c10f00515a105561b5039840214035030215100b08102c601c803c0101503041403060382d0306481c14001d42c0090020f4520f910a0907820703a901c10003000003481c1088980d801e040b0f0701115003c2c580c0303a08801050700b07601004000004601d8100c8403903180c0c5c00400c54201602008026490f60107911025205400405100a1030452021034201c1c551000d00010700d80840d00c91804541c0e00700340c0d0f048002035030000380c0c0c60306507901030300c00c00001ca50b41000300014105800041d0421100f44580c08d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 833184775 1250 833183525 833183531
    0x80601030e0c0a1a04030506010e061807120506030a0c0f18110906090102190b1b0901021b030c041d0f15010504050a0e0f2d06011e030804060509030c0906090a 70
    0x262070706044d602a180115800b2040f11040e50b150448503401c0c50045591714011051102c1c4003c10014004640740207400c142c4407a5914a00440c0c10000340c00003c21454052044407941070000e660107400f00e0007050059540b40c0c0340e81c146207a6026000c02099100c129038240307032a180d02040803d0484816490440f00c403544c2d403a02078010b078180445417042501445c195440d0006001a01d0b1303200d4400c07640e0040280302c0402c1140c40046600640a44500507800040f1a0108240107061011450801000c540c1c10b51010030004040c2c906070102640c018090408421300c01108100c259800ea1480001e8021f840c442c1880150b60003051141903c03c0e9200d0012896044003948801c84000c070f81c030b06448000c40101095030755101e000b148074018060300c181c0403403041003403241e03034455203980405801c4030b920b072100c032400c00c000f40c26001e0300302c40000c800000090b000c100200002c082d40c0d01d070a074450140c81d040604140906040c0360107200e00008004d444d60750300781c0c0c070fa0344002804800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 833186025 1250 833184775 833184809
    0x30d020a021503420409081207020f0f160608160e010c021302031509011a0d0e011506020715090e0403020a17120907050d1e0210080601030e0c0a 64
    0x3008090509444144c252011100104035032480d20443da501440140e40340303080f103142c24207100c00c80310303170700b6020b0400c0d0070504c016003443c1945a030003030b000f554920454600e01030161030350b8100347c02044480342c60303407041611201482d010400600145030508105070b01b841c00c2c840c0002d8007080281042c00700300000b004004240c3c0a1079039010b880390080d1140c0008814140100700039401500c17050465018140f203022a480c003100b04a050742c8212051030b007000f1300c0340fa034141d86811a9608040306520b0342c52141e80e0309403d1203903010070000b0384000d000080c602440a401c105042d08101890b81c00e03a0300c040603d40c1c0000841f0100c0d680e0b0b0001a059a840b4101282480910100203010181d00c440300042880e0b000060020540e130210b41c24141d84518044640c0e56040344241508800344821880101d07580e043c45280850400200c1c404100d016400201c42d50781c03000d0880301141a40c0e0602500c0c0d40c1c184a00711aa00c040001800c01426003400205800c58500c140110440c4025031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 833187275 1250 833186025 833186041
    0x71a04140312010e090601080c06090301110d0c0f0c03020715020c030601150f090305060708041a040609030e0d020a03021917010f0e031e0d180b06030d020a021503 72
    0x903082508020041d6501d401d94007124100c01e82003845803103803c0010401141004d080030a10604840c0164010845503000405111880d0405074400b0303455541e034190034000382c10000007041044510030b00002e4a29041e00c7c0034128a01001c0b8910802c1144140c490010390002500401d13502501103542d0a40c0b4491012031170250b28081c145d0300360181c0400091484800441099004040c0d207992614100301e043c102c1d0380072000e21000c0c0880c0e01900100f045c00307001c2d2003500d40190107052083c65207918450141c6643c607094a080380c415503034031900818181d1000f480c1c40700071030494030048100100d80002d6540751050001900c1904040c001c7c01910241070024002000b81e610000d80a2600310100c500801c885038a40c5901801e081d4001c2d1280004000c4403140b2050b079500c801448500f40c103800c2c00d9041440d107140c80c2c0354bc6003984c104c001200b01c650428a48100c68000d01d030f180c00410b15081c07100055100c1c0035548805500401030703039030b50030032220f0841c00705106440340e0325100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 833188525 1250 833187275 833187293
    0x5011b0f020906371502150a09050307031836020d060305010b090a050702031803100203040b0a060b040f03020f2b14030f0904020915030c070215071a04 67
    0x10120384404080003c01e6070072051061107489801c0e4404250520302d42c0c460043d800d9070017814507000140c200b410960035000c003400c1d480d60007403016440090000200c3e075034286154000c01055000c0340341869203c03081c001e05c03074a000113445c1d140600c5144035408800b5a05180f0003501880100d0b2802072294240c95090b41640e00c02001d24170203210f15556130524a0080022881060050480d0400504035030120b0240350f005001c81d500a61030011940054000d0245c5544d405505010f00107200d8040c4500c2c3c009540201d000340260a81d90400200d51821a80d141d4811a200c0505200030480b426548181408807501900c405151002500014080d0681c16100c0c03144140c0311103200c0180d410207500c3c00415441030300f14040710380c401151141d5a005105900814000400c00101e860034590054412203a0252450020008031100c0b002103400848040a0701c041c0400c144095281000d140303101440d640c40001d20706001d03030721400c201464800384024104488030225080152041d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 833189775 1250 833188525 833188549
    0x1820220c030c05182d150703081b130f15032007060209030f01140f04120c1506140f0910051216060f0305010503010510090509070e010f05011b0f020906 67
    0x1c070b100c00300d02c010b45090a403018094403054000c1058075410031b0854026802ca922540e091b1b2140c0d0015910102041c9006081490809580f24240001c0245d440c0d0f40f581800545040c040d00342d001801c10174411078980d2004421000c05040003501c041c00031501410320180640c29034407a6440d0441d041c00400392003650a00c503058490226881092181948504465100c9185407503c1d9250b82090300c16460090718040c151742109520012010300481540d50042e10604801100703513080c0752010100d6105500081010022464416103850248950a07080714200d034090620f003054040d032003060103940501d41c001d00241c03c000c40c04000421090260f207051004d000303006510f03500c00a000d040c4c17000f220008a070424001040d01d15043c055648038800da0440544000e10f840e000d907028140191210301640140c1c1d001045041c20007011380d01074045941340a8409103800001040c4d4144568070401190388c0c0c032035003400070ba1140d200c9440113030100da0a66150f203844000540740c04030b0b8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 833191025 1250 833189775 833189809
    0x9030a1e1b0501020a201507110105042303042d080a080702010e0604140d020a0510020609060c0307020d030b0109050d030e0a091820220c030c0518 65
    0x3a03400e082040c15001800c5c08078044da11900900d54010740b40c89540c08980c0944c0c41c0e42c0080040c0c0070a0000820756136030040c0b0760300c0c0c4400390315a408c030742d00c1c211482554240c441d40c075400706c001c289141048070000100d032010000c0d4580f61810303c600748105142d0000c0700070308010352114001c50a02c03801d000d018000310300a689030120036142130055a03002213400c0340030544a2091442034034000040d2000c50700c04c0300c924031282030846e040203024080414100d0b4440360354400070890b0340700c154008604142c1034009203140c1c01c0a094051400350001c00548640d030b0200100032405602003010600303400c5e2401d012403050040c50040c1c07918000c0c0e0b00101d4100211040360024103510401100c04108165000b0000c180c491070304809943c0c0107180921010150350380b00340005c1502000d08192100300c0d07030fa040d16154142c005a01000c0c49541d914818600d4600800020043d22490014255a080c2009008002140a40396005a1008164403610140401c0d510f07202c80828415070382407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 833192275 1250 833191025 833191067
    0x6063003040801050f0f131101180918060b0f0307030b13060c0305160f0f1d0604030f020a0e090c060d0b10031b170f040c0911030402040509030a1e 65
    0x45c054100390f004101c0d13090f003903244088003040145031000c0b14240f58035005004082c1503005c4500540d4012220980c0500d6028580400610400640724910780300b0b045082002801d041030400609540b0300504440c444c401074031484280ba6400121001100d030f01c0100c0c112581d46690000a6080c1a6003010306401d05110040c43c501e84d055120704d00c500c441004100081c3d2207100100c850324001c11415001c00e4039265a140194043c5400500240c240c01001c0c6a1400c0e42002c1002070b04560300454400056010110131841d10030046c001a1000c1c0c0c1c0459128944000615074920440c0501f50103104009190402e80840f03800c144041c0402920401e030880e04640000d00070b00c2d02240390300f215007101c000f04100354480d94100d900c512403006200c0713082d221701d00c2c80851740c0303030180c411520505406800611030b9038600a44059032440054030782c40f0718050060105949004222441d071790030801641c2480c0e5002103120ba149400c840b0190801080501c080c0c0e140742c8003540311561400303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 833193525 1250 833192275 833192281
    0xf0106060306030308160917071226070c05090a02090301150501080a0612021e0a090608060f25030b03070f0927060203040309260606300304080105 65
    0x70301a0050b50480e44203503640381d825034403450440c154844c03440c54000080e08008040103901c101a48072021501840281c0d010310ba655543e62a820300d912004980303802c0c104102c0384031100c0b01e12107140300e2031300388402074130301502030340c0d0006d403000c55001d410310540310340e0007180003007540b03906540035004050000c000c00c0081000360444080c0f24401c180c001044880012130802c3e01380101003c45005008008000016034200101240c11241070311700c04400741d81c00c02542e0707a00c0c10214002e03e2444000141d03141000581c908022006000355484604803081c845a003c191024102c410030700060300038190560001140a04aa980e9156040c45030100109030400c1c00f4207150129005000108080d0301441040340f00701602a10602c08030700d0a80076200401c043e50015070b070092103882d00703060f07298a80b201c6600d4040c110803200b0740e03907000e185119002070f410440160441c100311412000c40c4075041812502004070240f485051900c00c02d4884080000c105480c0a884020001c1c4543e20b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 833194775 1250 833193525 833193527
    0x807030f0903051209010b03150c070506010b030108010609020a0527090903270603071206050306041518020f060d020d1b080705040f06031d15071805060301050d0201020f010606 78
    0x4d004140d03084007940004010a8465405108019800f140a0090310308200007803010440c08000415452410600700280e1001500511103a406000b40031011303600d07941051798880c00c482d20f54020100017441000718420f00c5411500b6101d01c02d1a2280f42410660002d144c90592030341d08042c15001b41003901030000280010010f005010303210b1000d820344141042e07201d044500448603c5030442c5d01000030900c101d01c286c881c2c80d03000310a0b140c00700c1d0740c50369140880c2c038118040b10180c56801d103984000e076211202d40914601c00d50f9092050340444403580002d5038014203450070720300c03c2c40c0c0080c020300004800c1d01038581503040c01c98100034600c42c0205035004e181c6400a0840003e504100090015001e00191070035110005a2840528107245059006208100300ca00141580460526440c003007084500304025000c008250b8904000201803c807140c0146a03840b001e107605010312103503c0d18416641110710494004607503c01500050b41403a1004d02921115424000301040342 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 833196025 1250 833194775 833194777
    0x15040e011e0515030102030408030f0c1e0703031416050d0b15031b1608090406030f120906210213120c08070902030c2a1615020f0703030807030f090305 67
    0x845000f0b402030300d00840c1030201800c0307100450f00108008010b002090780c80b03104000040d4400c04144042c2d1802c02442100c9565419035407040070740300c50002d103034810590f05000702c02c40c00c8690b05019040382820581003200103a904000001c100300403c0340f660b40c10305504845007a01003e0420002b1645030886d054442e84201e0701c1c11503030081201071040b0500c8020440f400281d004814100c01e800550310800d1a83c030031455568442e4450b4000b03c0440c201c2c11119407402d11600d900352414144100c06040f100180e80032006003d07a03800310b0800d0051041030f03109000c2d408000140e0b41d614075000d02c04100516040894240400616901007007040590300c4140e42c4c02134100c0e038045541e0080341c410781c03004031003403a000c403410320041c0c800100d424030704c640c000b51910021501320f68203014180b510050a1032000c000c0c8900c00204202e2035400c980c0240003426102510920600001084c2e40d15041d210003402c20628000144025101c2d41c0a80350004244030148540c2d4001c3c1402030075 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 833197275 1250 833196025 833196031
    0x20d111011220e070804060b1003020904050702010510030609050304081f06080a080414010212271c03080a11070807030e0924010c080304230615040e011e05 69
    0x80561042e100841d245100300c02084416203010094107665013441110711981c09002100c0c40c5031600c0f0300820030340c0c807000c440300e114206540040e11062440c00300000d591015002c0f07000c0da45010280040760310030016220540303802c8400403a19410a1510600e18416076001c03820702d000302d4428600702c2c00344000002c440900300406201d202c0c3c442002c5519280040c000405000081008006103142a200c480300b00c801401600d212104100014000c0c0d40108a0743c0501055084194035550041009103010070701900d0000e8000c9151070300b92410740c0c0000d000b40520844900042462820303030407004074031070031001007611903883d851b01886603080703140f046010440010304c6c100300c0c0c00d2030140c7e240320b810480d0685000022010006601d6001c91000c1da042080014901d408a68418001e40c010752041071030002c2900386d07150300d40d05140554480227003600300704240071074130f0042c0750340e1550349004460020f03500c0034149900340100a004810300f424994030101c051800102d40c03100748 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 833198525 1250 833197275 833197297
    0x17010b030709080303010b04031514040305030a0f0e28080a2f0706080a0f02041d0133120e06070f020106030b2a0f041e06020d111011 59
    0x107402da103d481003501d83c0424000c18280e42c2d0148010400719000707400d00104c1c105420400180074050340040304400707000305c400f51301207080007061004030130b420300c5000300261205004000c14600107c0441d210044c2d0b036000309114540c03403c4111a40303c040280c0d0709070b81d406220360f07540d0f032100b0a01a10050410742e90741c00502c42030240701c5010f0441050b0032103510040380a040041d00348642034034100740151151082c03955600b41e1a480c01e99610041010345600c034050540000c0c010842c502c110070503004444c0c4424506541c40d042000400303d046802600001c001780c01104038011036401c114084a5802075050082456100901103901401454a83e94105900b8045070003642a1a194407005140d59403280002c1e101143d514031440308491299112504d41030086c0402045810581440d104220300103010040300310300510241d4040800106000c48a01d0482d001c1d442d640c1002444c4180074030701110756004202440a500b00d00c20b208020070000b000b0b82c6a100940c0c1010038109 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 833199775 1250 833198525 833198537
    0x30c010f060e0c09040c0212071b0803040f12032f01050f010609140607081210050411030402040216060e010b010809070f050616020a090906050612190317010b0307 72
    0x100b00075029014182c860700407110384500c1c005506090200404401214108601600781084000c040e000700400341c070b6000b039030000c0c2c20245150901080c1c0601ea4032500c11640108010047d00c0320000003102150050000740340110710606040e80c50700094144020b69a21100307036048540c1000c96000b0408440b03e000700702554a5141602e1002c90038024500400d004180c10040c46001544201c440000070b00502d0406100790b556075040d8000d03411501100490b9020482d808902030344080041c00c00300c0d4240000160420616441e00c809000a4010781d0001000784440d01218070303400784150711a004010a0403103a20b80c07030007801d07280016800210140041402c0d29800200103040e1403022090141c0c0368584004c000341c42c2c0c0400c14550040107a54240c10144e035604000600401041c4400706a85503146010001c840009240902c00c450f0020368040d4407100042ea6071207880000358403038035098030782825a802c401da040443d2040c810f0100119601c507108024500500d51a1104 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 833201025 1250 833199775 833199779
    0xf0409091202010b0634050706141c020f07140c03070801111602010915020105072a0308070c0c0f15090311150d0216110109080604020d0212030c010f06 67
    0x100c3c01c1c2c480740380714207030301200c144840c142d40751580c02c0c0c071840c01d210102100011100406001910700c25020705a500343c21800c41004140c0d009050b906000c4941201140b802103012003440c3c100100140301c1e4802a8007041108028008104540761560008400d510050400e030115a41e0b008802649013313020b07924000603688414001d003801e88600300002e07400c100245215983d540442c520583c10003080c01800500000c20840844040d80507900104130b03482c0522010b0540c84c44403030350b000012800211380f4020741d60000d944400e55403515124115898501c41214a8142d0007005030016410300c4001905640c2c0c0f0404804035540441e14091800f101001130300c0e441824030000e003440c52600541d580741d10f800101c400002841d000141c4c00c100003401004100d82014811184c4180344070203500034412085110701c2004802d1800100715410700b940e481d16405c020380f000f0301640040c0c41c04000c41d543c220307a03a007081d002ea9003120b44401d003902c9a00d0290180d00c1100c8090b42ca00080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 833202275 1250 833201025 833201027
    0x71e02032d34031d0103180c150503281e0e06060f1302160b011203020c0603070906030207140a0b010e09010203041a0a06030618030816020d0f050f04090912 69
    0x2c44040394140e299008240c1c40440300101d0884904007840c105541e4400801c0881d01102030f00281074010b0241004850030000562107400c940c0c0140400c2c84418010410035082001c080a40204000e916401c41e441c552103d1000e0110403641e8448800c0d146942e5003102c3d40ea80c003100c1c150300d02004170f075007544440007070001c0d941960304095049401c007141940110b04503001003506094503400180000c00c50f0b1251603480200380c12501030240032411030420300d641007000380c0e8190341c2101c4030707840d6007001100a03000b22003600c00c000500d9000300f800410300611125070030170400800d081e41e400107881d140141a0800c00d014001c0303c255101d000c2400c00c0b0f01442540e20503030748655414609100400b40c44038100004240c001140d841e12004000101075008081540a41400e4840d09841c54a030241144000030425410010409800080594001030500c038941180c100404501c004007400c46651040170030105410700009000510039205a004940c85401481c2e07500303200880e404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 833203525 1250 833202275 833202367
    0x140702010f0b190b03070c06020f0a020c10080711100207080a080109060303080a020714010c1e050c060c09030a1703060109052d030f06010e071e02032d 67
    0xf055060003951010b00000501500a40e0886040d041032101c50526070f6030101030364000385004c0000c000100b0340c0c18030149c04202c3d40f01c0d030802c201c3e2004011f181e0700e24001c181000080c02e4408200d1102441000e4140901140015007008841599210782d05d0501c60a960b0100207040001303040300300005000b0702984a500c0540e603056032603001540700c080d444001f0307400c0780c5000c1d544092202510305240070f09100b002c1001c2c0c07541c0c95211309a0650b00076002003044003001082486404c01180071030080210b02c00b03078041c0c00310b0034a40d1504080c1c0c012a02c0c000092400810b5038500c508000621051a4040c6220711000d03601d80f000030340c844040c040290080c1c510031a02d10128441c0703e0b4042018111750303043c100c2c060700322442d1510303c05000b4074108003a400980741c010a6402d02031180da100c2c48106031203054a40c920810750350392400035542c1c40703550300c3d0702e2541c0d48003400040007040d00a18004213441c00369140380c58034240e400e40e513189601c80100b000414800e1000096640b1501 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 833204775 1250 833203525 833203549
    0x8070314070b15060d0c081515070b0c090918061e070804050f0a0f0c09020415030c02070e04140f0f07030206090d08120405120306130c0201140702010f0b 68
    0x490002c610b5110f48242580304802c0072002544000184441c0520701103620070008925660b80e10f02186040054074030703089030342e030709240c40c00b5001026095400504100c12240c6183d4030600303c4025076144000100c13540624000c0c254050900d10501a15800000c8030074552a0800b090f00c20355118184007401c050032542a80240d0700c11800000c10b158000d20589a109002c1c40030b032050310441d0603455042102c0c1c0318080b1902041188100144460310101401030901e81c3d00c110f182c030381800b031295200109108200c042586402050600c0e40c401c0c4444030007003040e034004041c0c5040034940305000030248181e4000340d110780c495000d403030300001610440b540b030348201421040b4110b400b808180e9101d052201c1e0460f003403078a1742000a2100005040041006c0c0b40310906003018030303046040214209810041e041c013070050000a41d10451217070481a0640000a101e0b130820b80168050304071070202404181845e01000310564041d0403804c3c4401c64003804210f0070980700100f0282007040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 833206025 1250 833204775 833204783
    0x142d04030f120833120304090506040e1c0323060102010c0e010f0e0d0507061809020f0d09060905011d0c030f150c300f060127050306040807031407 65
    0x130000c610000d460380c49002c0030b004000c42500350f004407010201c1d0495034032903800c04040d80009010454090203110b030b260000700845060281d0601480b2840e5103080d0004000000d04903010401c008501991100d40350350541100e8801d00d00707074200b0000ca403c40444406001d9401d15102410541c0300d0b141c1b007214104161a000c01400c00400c04482c1c0a02881215070401c3c01e1005c1d90300407940400a080081a141d5183c810b0744545001d031070651030841c2d02c01e101090061100c40b44c0c01c1150819200c010485a00c00142070480e820113801a006021f40074050f9442c0882d2040d800c42c80103c2202440404070031103103001d29403014140c1d250120b42100103140c03c40b0403c5604208002040c41d0403004c203001c000d0070b148180d0b0b41c0300d02c1e52590b034544854041e007060401c0002075070501c005922002c051a51052407800f000040c3c031080c904409144c604039184ea119070314418802c01c58000c0c110240403a0401c0c42c0500c5c02c4d10701544040016400f04102e1050314006c18507060441e03002c05da04c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 833207275 1250 833206025 833206051
    0x7120915060b09030d051c0501032901030c090f090807050610150c080c1606090302090c190c0521070b0c0307050a03020705150405030d0c142d04030f1208 68
    0xc0140451b22600921001700d5594035104024445000e00e02800740614051a00c160100082c000000708003141c406404018109810040001c9019204080116007584c036000c10202464000c8000401003808010703c03102000c1500d400780140010900c1c032030000c0003021015240c407481d440302400e400d00d00d02e4001034441007080000442c00400351811640c6142240c10060401c50070841880942c0c2103032000548180080081d46890f00d00c480c0c018070345070045858a904c0c1060145042c604000140c18440b55413140020080d08214544640c240860b00c00100b003071950807101d03e0750108900340c038810300002c0459001c080744001c49001c1c18150302d03421718280800001740c000e0340000c40c040d40d0030300500c580004a4000e092681d4030480c8118061581c0c4e80302100003600300c42c030507900348040140e04406a420702d0501012107481c07a500f40e0b14080c500041c446000854140003100b02e0307100c03034007280010030440e00040400d600f501c110001e107210109248116648401114000241c1031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 833208525 1250 833207275 833207293
    0x1150b09061c181104050f1f0f090614040c051b03070b07081608010515131a040608070e0d11030a02191d100306020307120915060b0903 60
    0x54010010091003503180e101035501c004402c6000c00700c5180081803003610141030003103020080a00b030410180039003164208424180000325200c507407001007402d4400000d1030a0107551303d00d840c12801c020030141940d45030310394132101d0943c050b241c60b20030420454000446252940340c180180c800060442d81c816007814030b540d4900151452485810712a070000f0006c46021441c8046442e00c24101c07525504224100102d10102020100f0184010803081000600440d541d044603810a05500d01000d5154224404c09981c9060107a10441d9425030a21840e00c041550501a004541d010344401005035a100400e845081c81051010b50141181000e000000d030050b0300e850200700d02804985800e40c0c154081215003425400101801440c200c2c10004500c500180c600d400c611404a200342e03040104440340512910b0100800076500400050910f603c50301d0b0315410140414000c0c084a43e040c1030541101d1043c00103c580030b81003480c046814480c1500729181039001030000e01180c6c0f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 833209775 1250 833208525 833208529
    0x40b042f1903020f070b0a14090a02090604020c07080a0b0402091e0c130305060711010c02030f160512070803070e09010602030d050408041d0105210d0c0c1d070201150b09 75
    0xd40903001c0c0d1040c1003c188490004901b00a12051040c2c01d03a18001541d040c04241001d0618001003180b000d982c0005030010058541c80c945c0303900a101038901580350b6109072800d50402145800054251103070b030740b42d4000c0c404641d03149800b45000341d80b040d10b244ca90100c081c2020320415400300c640c1c00b40c680402e5081405200030102d01500054904030306441e580c5e22800c00c142500c45400081840b01d1806080ea800e12440c40c52901c1ea0000714a0000c241c002440b1901801000d00036404d010700440b01440030038000d8181504801d540c043c2d440b0325038030340a80b65400c2680e0300300014114000d0307002c1d282013008015050311100c0c0c00031030400c440c956000d0041c0c00001d1045a40744c00030f0000091001c0c03030441c0d0400405084228400b10342c1050180106e10800c490030340b0036607842400c090424000442c80d0741c0889040e14201124802d5410440c03810b611950200c80124442d0f1504140b4050120002d40144c50300d6009100c0304443c0608006584070740e019482c80c110003000542654 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 833211025 1250 833209775 833209777
    0xe0637030216110303041a180609180a0b04020304030c05060f0f0c030403121506110d0c14031606050a0e0d0206070e190303020106051518060306040b042f190302 71
    0x580f00c000c0480f031520b6200e1500c00128550032010000c0c0d244045542107a030305020b140b4800d4801c040d10441d051010b02d000040308009122100b1030540b01110103d549662190000d0300f5188000e4030035075407420980f500903c4490a04000d0f1441e025100102d40707920002c1d030341540180d001d042c09a0068a4a01240d04a64000360044060062000d4141081680c0380100e8020865403460103a00c1890450082c02c0910120b041c42140d0b044141040040c03600010313000305603604007281d130800d00403c0d0401c40c0f071841000c03c10303140320807403003041e104010082d00180e104901d504014480240307000300e1a50350306007104088016070040800179002c2c501c0303207411361001500201025800e0402d0602a40c6200080e002500141d450385428402420400d40400d690b03800208020328101600b808103a0480c03800164510510001010810744d50300d5404c4800d103581d000700100704200790b2000400c200c1d00c103050301c80105000304504607100b00e0080e0503501c101202288611020303600030012402 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 833212275 1250 833211025 833211053
    0x908061006050d14280e031b030403050307151a03061609030b0a02070501051f030b04020402070b0a0510051203041401090e090c0310110a0e0637030216 67
    0x4541d507841e010300d001d4245181240500c04203c1102000811402c0e001c1d2840680c0d0300c545d05440c141004a107902500200300c90403152a009400c00a0110f0070b00981544940c0e400a4024800440d0070001e1200d9107080c0c0107002c07503c202c02c010309003880709036104c80c403c48041c0e903615406c1100080c0700d1117005468a101d484e03803840c1810401e0f40ba039442c1004910299610148a80c1c081b07002400c0103024455107802044c02030180b80595a221039460495000703000c010290598000858219102c0d5010ba41d2516449540c40d0018901009040000c1c0b804071600c2507240029800002c040c20110b0360034040442120145140a0800c60b000b00c006074040b900b04d040084070300c000902644803c80300d5000d542110094481c0d0301d1110201440d02d0303038010040243c030f451700317400c41c4800450710102e480080c180d09004601ca000c00c00050f001c1d00034010a0701c03101140c00c0f803500c3c03c083c80c11142140408030500041040c2d0720903404408a004080000503545d0000c01c40001040e07200c00c3d20a1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 833213525 1250 833212275 833212297
    0x80f130501020f0432060d022a150609191d0a300c031b080414011404050603010e090a020414060f101407032706090806100605 56
    0xc5819154001808598442e6225004d6892402007505030342011550711140050503c01c0b05ca640c50454000031000c0c4190501243e100307500081d032800325100c240f019031040d00802c1d1103144035403218940c6a1905000f003800d01003d203900c80000c0300340ca40004568051020302000c02112104064003500821001c481e070002e064140d84100e000c400104111510684180100241e601c40c1c400300051f0301d00d00340c64124005d0f04840a05404560003400c40c5030041d05031800380064102c4490510410340d403000040e0100b04002404100389030340e02e0640a0600c8203a903450514500b04ca22100c40b07002d503028242d03110104000400c69010343ca90000d80041c1140700b65130002080d035000a044170000c140051203030394141d003006007030b00d081d0030300000d1010292484904210b62910040c0242d600458440850901085040134144076198003840040c1880001000344a8010201622151440380c1c1000419008001c6031400300852071b540619000380402d2081428400d00b074075686c0090f06c001e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 833214775 1250 833213525 833213527
    0x101104051c02091612091a0a06170a150b01051213060c05130614070602040e010f0b0712120b2d030f1c0903051f0c080f13050102 57
    0x822140c1d682006a14007050005611003042035620600c200248010600782c02d210202c0c0c0c90092182c0c11503426960300622040011303042080f440c0428000443d8096004005004800c10403c3e000c2d41c0e01c501305a50720702c1d281400c005640002d16503100e59800780200380c0340200c040b400e01c184094014103a0300c0414180702e4181241b08a400100e0309086440e5070110b0912002c0905110b032500c80c40f03c491906282c1140703401c40f040d011030700340c0165200308010415400c207109040500481620b80d43ca500c080d09642d01c40d62250300701280c28081c000d600e40580142c2c2d00103030341004481219101a4012084250440003000a41d40f80d04800491040310f520f40351220419644c01140b0410118002c0c2d005074001028641a45140c16882845010740c2c845030401c15070740000500c600f10222943c540b01580203000f04100c42007000b40e400240030740b1400d040800403a030507080342a00c08243c22000c00190102c4d4500700c03041001914155003008060001c20152800c240e01a074007140144009 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 833216025 1250 833214775 833214779
    0x810120f02131b02010b130b0f0d0501060909080403060c0503010501020a0303050903091203070c051c060f0905030c07141005030105120f1c110111091018150f11101104 74
    0x90203204100143c1c140180d540c1c0801074031500d031440380704000808000080103134613400404140300e100348404440c03107860400e241e0740c10001c00750009801b034943c0310300901000106140010131a0441d00084070000e0400c418089128480e4056034100c41c0140d00910a000c0ba9031000c0c0d000307100203883c550490004111084143d10b0344103400003aa041040155551402824904c00e0030016412003846000501c01d40002d801c8005883c94080b03801c840c000030314110361341209000f09980c0074014010f002c0492028450341c4040303121421507003101c0d881200240010204038030721400b07400c2e03000490701c00d00040c41182001600080e07104d00817000c8405598041041524140c5512240c80c084c00d0030048103200c80d80d01001001100c85000020302c4031060b071115640b8140984264180280682c8002c94102441813541c1042d09018110380c4a10036151203140c19108240d0441d9000321750420402031880c0e00c1201c0141c3c003140b8400160101680703040d001c2024111203d81007411881c28040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 833217275 1250 833216025 833216051
    0x62a0304140a032c01051b0a060504060b0120030d05180708160f030512070c0906061716020a110a17010b04060803160305090406030f030810120f0213 66
    0x4041c02a40030703844101a404d042d00716141d405021103804e03c0141d50716900c5180300c0c0d030408141c4640300302030841ca020303144240000c24505000c500019206e10b007000300380001e112403136100e802002001c0e6581d41c4403d0160000300c0446204080c1491564010060010b443c0c1d1103a02944e00401c444001064803450400410315042c0c0039044140c03103801c00c2107460340c14035990303081d600204070211401d5240e900d140c4940c1e440f80c8012680550100c0006001c5d02040a8107003008091300c8208420002c0c16102c0300000c20740712240c0d0b40160103c0103d030100d50500a044441c0c25100100c0c6d0007007021a019694840444220340f4501d03400000610740400d07001602c0307a4502d01030150100001c3c0d501c04010812007070b00d40e103910102032a00300704600d50444003640701d4080310a826051950b81d070803251000c80e004100e2580081c1c100403040d2807040405601c46155030140e8400007044882940740c000a8078072859800e00204500314901208006051058091030b0040809800003072024038224 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 833218525 1250 833217275 833217283
    0x180c0102070b1e1b0c0109270b06040506040303090305060109090b0402011409040216050607050a14220b0a03150503100923100501150e0d050c130b03062a030414 71
    0x132415500e422201c500291564021034500c01050a1001c454038210080b0200c40307a0040440451034150b00c50f00543d0f026141c4800700c400900f130282699031760f1590307410000e1210000e800210713024006d0742e000242a83e401d0203064045600301004842913181e583c0107550044903804440c00d0090103008452080d40c030362014100048140380b4400543c14103103005400c03c0c4004106400380241405141c144131342c070074211043d03c0a0b00c04c0f125910501c2d2115544543c412642c804080c0307880074008110307801e024001c0c050100681c0c90034801d94196a0000d400544240120780d05540301d070181c601c481a03550080074415000d840000418000703000d1700030030f01400d0785040069a00041a00c60943c80340d21a580c01044d0404c8409c10001c105203004080040d44004a8480c02d116000c00b0103110b002c2c031444119800080454101e990807440c058060600b0f01c0405102c1c1c003a440c0098a081c040c4000c040d00005401c1010b0609184105880601c1d00090403e5601d4442c0e10900040850200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 833219775 1250 833218525 833218567
    0x3090b0705011418120c34030c08010b1e1e0d05030c1002030603060628140109051e150f0406170109090209160e0405180c0102070b1e 59
    0x251411a04443c03103003841e190417000c100c035608641c0700300420f2046400100e4106070765040c0d540d1200006000103030010101074807090401003259603e02c00410460f0070311490f0100ca11440c002d1250600280030000da00450074020074006ca00c0ba0012800743c03a03c031121510903243d16a2004d4000d92000108094240d45201142d156000040d00c03803005404002004804c12490001d501e14a42440483c2c2c0b035090150a00f4040c5240f03c1603c45450000702181b909000c4400c11034040c181d031540780854568445030303122b0110780e040e800480c80b4141101d6003135044a0400030384544510583c240201300e00501596500c801090101401c10420f400080c0020002070f40c80040c02c2000d112050500070069010b220040c1c5814600760040c0c0703a81c80060703808503c441703100700a44440901581c50303056100f4081d60083c07601081008110104049041c0442c2a42c02c0382e008104072001a81d1780e209500500c20380c2202441220070840321803100e9510b5582c2c0064913070502451104100e0140302030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 833221025 1250 833219775 833219791
    0x11060706020705030d060f080a0f11100c0b0702030c1b0a0b1306200c090603190f0c09060807140d020a0608040204110315060313020d1a070c03090b07050114 69
    0x1703030600032110700c0c01180060071901c101c5c61400d9181c030b00f019030307180d0703004100074505404148030b4000c0c400d107120461861b08020780300b0040b05041c0c040003003004420b581d084841103007080110350b080707200000b0380d0200040325000349401c04440300341d40032010070841180d5000300300344004034042a105000d8540028080760403003070182001000f40100146e203c011554842c100302524140000240700f050b20101983d01d10459212640402d00302580620985010713601c40b00408104200420b03240d000714000c281c80842a0307191011101a40e1030303480303240311b07a510940e030074000640c80a4030f600440100034041c21811542e40e010820301901540b007000030500c81e00400c4198141405074000025006a286241d4070340302c6080c1d403c0c0d604c1d5a0015001d00004000221010311840e004240e0f540c00a003141401c100b85c3ca0108001206149905807a00800c000b190016000300303482c0400c154152503d00f100c03414840140306507001048155042c3d1340703c98090441c0040c9000ca2400342d896 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 833222275 1250 833221025 833221027
    0x61808030c06090f120301050607030315080706120e07210b0a0504051b09071b0b0109020c16060e1002010213140f0f0901091e0c05070c0518041106070602070503 71
    0x1d41855040039500c005005050300403010085e0000b00caa400c81c3d05559040300e00b540c98085504044006260301c0c045044001c04104020403052000696401120002c1e5224000000358901100c140e62030010000081d034810b00c001c1c45039403201d1400d8005180f140703140e4041a071103a1114101403d00791075072083c1c070765242c041c07009000c0c1c280f08070f0241e07100b100c41d9020a4261840030030341341d4500078071003010802e18200c0346540d00c0d0303c4480c200003241c0050200c4500e5848445050095114032000b01c00b504c540c001c240000962903031504100c44150b110345900c142d40e142403110600c0030020003001c42d54204811302e43ca0103404c0484001e0800300d207c0741800c144c84000d02c1082880c2c101e14511407070408222118695800c8502c6066880f43c520200e14a24092403110441c024224810081800e2402d00b40203294040094030480d401141d0750340c03030666100b0501c1600003c5130311403680412900b0009000c203d00c040c0c14410050302400007480c2c1020780c0c0f254001c030303040440100c8013604 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 833223525 1250 833222275 833222281
    0x20a060614010906020123090a050109050c0a0e041a100305060403020606010201061d1f03080417070f2d0b2209110406030b0a180e010f02030c04061808030c06 70
    0x6440003190004d800c450000f00301ea1110711310101080c00f41c04611241ca100044c0009114034814801a281140c0c42030080c0001c0b503d601d01586c454446548040c001e00d41c0e0400006c141c82c11502c15405550041500c08901c201c1a21000600000034103022600000d140e00200040b8104031f0341d03120768080d50240c40e0714280301e4002804d46d01294440c1031810900c0405010b000e0b006600b19821803045445a21000310f802001c04001e082903101401244000c5400075412a0a0706044040100401550308803921078144a0a01c4264002c0c803a10f0003031004034078400209812118035a030712120b80807544030381c0c0d50f0140913240d0104460544096110007140424108144130394003800b030480040c40100107006000d03a4074010f43c031138101016240c65170141c45468040500d00075040c1c81821942400c1d0300c5004101528100355030281c2ca40c82e244140c403041c038492003903900410b40c04050710728040c503008049030071401000421860f851102c2000485150400090001c407000304041c1800345 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 833224775 1250 833223525 833223527
    0x70825021b0303340c0f320409050c12010f0b030109260405100507050f0d09092309150907290c01090c080705270601020a06061401 58
    0x3100a070715260090740306102c58180d8884044240006100c104540c00300101d007040900c05080c00c403180903000307154405001c9400f81d40800c00d24180c072400d100340300040b81c8400460203694a803200241481c014000c0310f00030352900b604118815070090044032a007284000c00120034030b01c80220a52160343d520300d8605d21403507038001c05940940c2203000304468075558481381e181da810039019807010050f110003003440780d0b804402d850240c0005030a08010390300030100582940d0000c10241c40600c6480000f00b03606000087c42d040f09200e1703544a003402c51404815038040e00f030f64908600740390040411882403040c1c0e1f858482c03082c000345009119103808850721800d200009880304001d0b800000081c800101180340b015031066421410086400607904c00600c103000c0c01e980054154203155901c418406498190b4054901c1e04064684207aa80c03810003c0c845982c0700051a9482194038000900350020081760b409101801501d00704400c0341c0d00c0408807078180e00601103001d1140f0f5014529 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 833226025 1250 833224775 833224813
    0xd050f06012102100c05190b060103240603020c0109021507110a0e0f060d020d0c1403010b01091403150109020703030501090902030a06110904060602010f0510050907082502 76
    0x60b40e51a9880d41001407680204180d0305402c0240403d10001d851080b08008040000b0011038800e00c00800e014092840c101d000504155a800e00003800c0c00c0e02c0c6060b1210a84109075580015014118101e15000b415800b035006004124a55503880210002503204e403540d40d10320280c0b4141c42c0741d680c0c556181242054200c148114020800f58405000f8245040c500d150804103042c00c15680751340e2080026540160220002d402c491058445402c004141c41d0390300c1660f071030b03600202e030b01a491400e01d4229a1014814ad0000e28000810003080380c00e09401840084041e095545c0b41c0580c000b5000040c40a0703024100c0c048d800a07814081c0f56045c803a42e03000d8007403201c2c1804181c100f500020380d601003444c4050100d0703640310003451a083c11242142d45c107000280041c042c1d25994000680245071300c0b6a910442414a00005c4007640740d526079805688001341142d42c1522804003c5a042034024016801d19040c50440c4401d07144100d480840190264024001050045500181 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 833227275 1250 833226025 833226059
    0x415140108150103020d0f0807081b01200f1803070602031b07230103200d1802090f0c0906070804090b15031302060d0f090b090a120e0d050f0601 64
    0xba15403001800183c2d01d5000300c5900035082100d0380c002a00c13031708083c481c920614000030800c00e000a035035030000c03261122411480d06403600030001960600700d8281c80340d500c0c508a0083c0380c000c00c0302d41b03440700c1100041c000d000500d003100744e544010100800c3c40c0512a42200026078400701d01160500c150304054001000d17042c0107001c0345440c2041198001c4e400800c0b41d00740d06a1501c8140b05a4440c3d8041825007041210300d15401a6140c014030f26a8010341034420103a041c040d44140e112426248060007030b81c00341ca59a0701b0790b19442441008000a4054845500104101c080a41d50000a840b01c035014040681d92586805694401c44138008111805000b8003004e680701c680a03031041c1c9038402007000607402c10150728400601c15200305001140c4443c646804071441180c66845003101c030f841062090300d0740c1c507001080d907511008542c0007030004c150340c01541100ea00c654186002e83c107002d442c0451615541c0d88803810007040c5e02c013400f401e500200c0100501000010035441c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 833228525 1250 833227275 833227303
    0x10120209121c1b02040e031908011d010b0702060c1f0203010e010905040f140307060906060305120f040501031107060203040303200f0304021903050a060218040e0a0201080415140108 80
    0xe00164182d0403403007400391500e0043c0c4030f03d98a96240b142c2c120140100c1e84820548d43d029255610581d0002e0002c00382805a045078072407068090f904400010744140c1651035000703183d8100000c1c0d608201c1240e0210743c142e40366000d001d42d100401c20100410014034100e02401603140e6050080354050140142c2c05000418100800d0102107800b03c80c000d03903d903801019040004046094162451240d08c5006150743d1030284004140203a50307000700140c82c0300d82c0580781e480c0d20f46003a072541e5000351641c00d1003034042004200316a60180d8441007040703059608550500030b80d0f440307041c02c07600308884c00d0300800c1e280d43c4030340d40034090200314001d06000c2c11001030130001c1e180750600ea50301004000a01484654001501c6405e0a0705a42c0066601504640c220304483c981b85010b500441d0150303c0000d0090b10544c20791a0a004110004249500400031b0005a400440724804050400d070f03003100244010001010441c02607611086215541d5801303545403100c6070749060100d000032a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 833229775 1250 833228525 833228537
    0xb04050a0c12110d031b05030405031906060605090105030123120a02150412060b060d110c1002040e070e01030e070f0302090105120304060c03030e0a060515030c10120209121c 77
    0x2d0b001a4110980301310070707a50611000c00780041441c0440c031350702c04c034ac214581c944a4503001c0030740e49038110140e0403203070310504c4207001c40c586d1901d040d1840d0040c00307030b1135000c650300340010321600700790303e49600d00d040072203c074600018030900120704107003440a68110341e60040386581c1300750b041c98240140307501d0003114510b240a240002c6a11410040310008010a48403031400525954207801c0c0c42608a100204001d1440e08a1003c0c090f0350180844004c14001d01d0244c146040340352003514120f8060150300745007035450031021106040d806d994a81455038036900e50400f0002007212310040d01d5401501e102e41b60860042180341c1c0d030164820303403103100040f2140e24420b402005440844101c2d0030001803800380352406601403e440b0300a40b44138864100c0e10780074401584c000501030111400a0342440d5151002d1580711291425003941142c141100ca1483c03130310500f1901012030010304010304010b4100002286144501000e40700c503448051142011034014280c0c0c8804d81d0079003020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 833231025 1250 833229775 833229799
    0x9060906010503130c03020a0902190302041a090d150b0117100312230324011e05130f0311010203180d150216050118020108040b04050a0c1211 63
    0x80840c4401005102000c0c90384c6200070400219034201c0c0c010b07550084c03000d200e10784c07034100d6100250081081200c581e002088484406400791086409489280800c920004440d0041285552000380002e030400300a90000003c03403000d1181100c00e4441160103e068000c1d54001131907096001543c0f4440c1501c02d0034080c980708041c038403800b1030b648508403148049842c0e0080e1280c1287c00141200409244510140ca110800041d4800c400c40c800c10350302e9560800e40c0403a0b456a02e2152400700d014098502e140700d0f0160340002c87e40c103c600c0c100d8948410380c8885a0307d4141035020036680688040706108000d032440c2c50344041e00081c0300071802c1c90329180494015058203200f07076004061640d031460a121140e400d05009071403140c4150f6036401c0c50300b01401018601340c1c00780c419500c1c1c1a014001002908410b444480c5c050307441c4006c81e2515144c1c00b0000704090402c40e81481080c014100003400c02c0d03040ca00601e88103126418116007414010745040d000d0480c240704120307403d59 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 833232275 1250 833231025 833231027
    0xe010e03031810031808090418150e010e0d03060503060a0b0901090e01110c150106090f05011103120106080a1505090f0603010f050c040801060b1602100201060905070804020906090601 81
    0x82c1080d01503084988203038a140e8142c2c2a001440040810944a6100c06043c0b042c4280103000748110501a1000c04c0310540101203056008a014002000c4400a005490740c02c20f05800510200030b0010000406030503048aa61070004001141d10200382c40300000c20080c82c0a00604ea40304511032000d1000030050400900300e41014081c50650581d6610040da1915003584920745950703a500409035030380102001d99a9a91804102e0b00300501d00400202d4045d21650311941106c2c044481840014109001900d0290740020740d07842c14401804043c801400c440c13441c500800507a116410305040005000d41a100301080c14a1041c901d03400400240c0c0f0784080052380300900d002c4184130794803400f00080c058112049550506400c003400d11400300c4058000300211801e400c0200404d075680d0384071308420b0141c0450050030440b2500b4000260078000210b2441503103500c00040e40b83d440c1c1d00800110303141500c0aa00181101d42000700b1810000d00c0709801c000304442d6082240307040c40c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 833233525 1250 833232275 833232307
    0x100f080f010b03010c1707020313092f0d0b130f0608060a0204120609080912010b19030c0302090c04030b130606061b1e050304080c2706010315050d030e010e0303 71
    0x49040f1b6905480c40009241c6842401500c50761707403c040210300925941d811000103003c640640c1255220761842c4400a40c80440380c00502c0c0c2c8403901d1207400d1840c9038552000401c4130b010600d07003040da104004c02700c0033709911400442800700c40300004c86034240074460389403280c018000c0045910402090158503544508281e05a07031146e0080f41843c0140350a10745405139001c07071038100b54900095600f210040d00402d610b10380a4a09a07180c1e40c114400c048204a603120181c0440d91203035045c00503042c1a842d5540c8010076100e03c5140035541c0c3d4030f01c03000c080c040b1010700c10702d24140780d2041001004d008030302c003c2c1038514014820284115031284c20455000c401030014000849400c6404250b01404078180e4202c0b040c1c030b8482d43d44100094988042c40511445100070304040030035000c0302d82e8009000000342404d0300707507139070390000640003841880c0c26085134004060001820380c0c3d8004001c0c0070ba5100303136507524804040100140089080100c2948607404c00e021149030a06000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 833234775 1250 833233525 833233547
    0xa080106050403050715270303020d0c08032706150307050d03021c02210909010914011e0e04030519050c03072009010b131401080708100f080f010b03010c 68
    0x84611154030300c06110680e00c240c1032012903005024031101c4000e820840b1f000302d0003143d0298003901c1011100d044221269240d100c4000c00d50030062000c07900344002e184c00e90300e41c455244070741c008880341050018501403007125281006515400d0024041c103050046400500d41901c204004129640d000b9465200c5148844c00004603904040e202d5442000021100900940c102090340e401007600a555030003145081e0140c52400c0001800f01400e124603600c41e83d10600390302960f405e2800c4141030b08916002e050300383e40d9000700801d02c0081ea0140c107005500c07a440f0359541350814901d12051035800e911035800d1100600840d40c0307000001c03080b207450903800044044040002d15501402001c62801990424210ba0010621800000003040c2180d441c031108015aa5140d121411071115038040038000342d0f207880820070050003030110301d401c80100d0816a10707841d00c8005440040e101a4800c40c9107501000c1c212800d40700a03c2041501501540207000b419402500074110440791 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 833236025 1250 833234775 833234789
    0x1e0c0d0507120606030e0f070b09010c1a0f0708070c020a062607030e10200912120a18120b10080d020d030e0a3507080a0801060504030507 61
    0x20400110071510565000c00c031840b54810402c981611228010000c080e21070715213426219400c0c0c0b4200354100060184221032015140c28a000014001118400d80e909000c5595407020700d64418030321b0402d0386031072081414003207000c640d14080100400705031000e00400e0510151100810150b254441c40301c0985009091040c20340b4001b80ea9404002c3c80d4001101090601000740540c3c43c0d4190010702280c140c40b0102c420031440143d10408842c2c1c6691100b04608584042c8184100350002500b40881c0003072014080d0311180380e44c0c608004003a01c203180105c10000d0340800c41c80e04150091409072401e6503214035a4141211148507040301c90002e0014042d050018480d07654009003040501a1007042d190700511095002e543ca03a40586620003180c10408030955448001914016158000c0c4403104a5140da8180c0b001071808101020149404040c4101d1003155402c000d08000d03120794940c80da603554101c002800e40506800507810000108001c10100300300168603015142c1c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 833237275 1250 833236025 833236031
    0x1502030a12021e181e090f01080d08040201030f0509070e01150c06090606080f060f0f0613090c050616050706031407030b1f02030d0b0301061d100b121e0c0d 69
    0x24041d83c0f004213404110555802180d421400c10417460310380d42e0110421080c3c599800a445410240c800b00d0024040d00e8100e60001c43c002c500e5901c40c4003120b070801d0043c100001d0308624403104c002551400c58181240e540500c80c10801006c5c001b00e080e00506003a490082800c019010061110806c6400075201a4503a5200414031040381e010000800c0114115080e00d401540320b1521340e44100c8103084003074107410010700802d45451480703110b90300080a440148421030b220300e004200180040d00c0b41e003036200703010880da2644001810a490610300945c02c4204919000d4a042c9a0f500a50105418a950301c01c2150302c040e0816046820384c180820b0a185500205102c10350020084880203a402c0c10908210340100044c04003181205080c8070202c0c1389401d01d0700703032942032040d051000d4546005228a030784210b011600700c6d41c01c40840091556550032029070381c1200d4581c4040d207070600c051201c40d01100b44a13421031120258881c0161500b45180b031035500039411042440780c4c0b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 833238525 1250 833237275 833237287
    0xa0b2a15100509040b0f0903120c1b030d15090c02071a0d0204090e15010509070507051009080a0210062301030b0904030f020f061009151502030a12021e 67
    0x582401103000b810000c0d095495a107400d040c4092100740950724103603d04030700c10104000c0e0030080104d480390300e0450100c03001a202c0030340310350203036200c1d03412000c48412465400741086424002080d50f540c820750040748400e514941c0c600b20a40d141d1000084034a0701403c40601e070703004038100d011242c00380c0c4001c040303100c0d0f408800094800e480e0b0401a4510008000c40d856030300b64041204907804c0800c0703030519071031a18040303103920307003030242c2e507404580340c00010001c40c40340c0000c190061081007236841c1450300d440401c00780c41c0d840314102c400c00008200500003684c100628089200c50f0b203006c1c00424900f2202881074048070014044050b50449540e105074042c1c0c0003c0c5941c0b20141507103549240c2400c0041c1241c0211030150014040d0030a4403840300e900151250150517207100900880d880c100c6464010700201c081004d00840b68180081e0074082e8400044501d0143d4010307581e04c0410031801000c2c08882110000100d1041c040045c400c420755041c96256118019500c0c1e40701 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 833239775 1250 833238525 833238541
    0x7110f07180c0203070f0303050703181a0c0c150106031415040c032909010b040e0c070201180b03090c0a03030e040b0604091113080a030f03050c090a0b2a15 69
    0x4410104058103145a07098041b04143d0b0503401248980050b41d400c1198520304c01409004a1100c000a440310b08503500326508202107901d0f26811030044501e80b403410726880310550825070408083c483c1d41386403000402542e0340cd4003403001c4141e80c002c91405c1034900403907111640b151282500d80074948d41e0506080007030295010340c1417180300081c08500011200b840d108001803001c015030040c4881000025011454010b440651342104a00701280c0e58240c034540c0316401c4284241d041047e0250151080540000f0120140c0a40c442240e52807030080c5d01c0f03074585180c29100d07900410a81c2410808a82d00000454800078100c41c0440c1019419001440c2d9000b10340002100510301100001003410000040555a071101d40310034605513959906911a1b070000c201078041603d444404c660b40c2e120340e00041d40715050750345850074014117030042554a036507a0400744a0001c002810814003c0c80d0407a01e81e140c0c810003124003a80e40c4070a07040c0d101c4551b000300c440e546070f403800450248 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 833241025 1250 833239775 833239777
    0xf15010314150a06020610090f06030b13060c080118020715020d0603060b030a08070206070606090203271621050d080105090a061d090a060507110f07180c0203 70
    0x1180e001c0c52090400d00744a181c440000c0950b48095128129802c0006141070011540d10b03c0703418290711001c10f40d032034400e2020141c42c0e1001c008180300d940d00c00120000c1c900c2c917841406545407401c4078246030030303918007881215007103d038035020300203060010080740c02d00340d8114180c8039030fa4130b0260300e4811501e800780d902e4903082c030400009400415a640341c1035007a030040701201c0c0129400d021003540d10042c0b41d05d5405086020308400300c01c000900150a01c1c40050661354814080051103030744d12200d10302241c0080d22100b0400c00c450340e280390102c26050886001080d400041c006202c85a052803d412820348034040717408084080459107405401c46000407071b81c01030b058440303841400301d008001150034000c541c4201d0b00c90303012503d501c040d0710a03402528030905200701c10480c41d16001c502c8510040c902c6240d4810080b130b020001d607040c043c0f0303405501c0b43d850700c41e82030710401d00d00d0f8103100d411000c80d540c3c1d9001c803c1c204002d8490700340c282d0050070f4003140000c0003040f0348404c0b415 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 833242275 1250 833241025 833241041
    0x3020d031e02030910080903070f0c0906030c090606050a1215240f1412042d02030106060c030c020d1103070e060a06050c03031915060507020f030102030f150103 71
    0x869003911001c03201034002c40107000b111022200403d0190712210180c0e400c80058a0241d91540107002c10800640755204890000380140c1c4625161961402c0d808142d0b40c00c2d40084403034141783d0808120307020341800348074003802d0281803036400c0600d003a00082c9004115200401c0c0180c441070000b011400e103503852001740c00c0c50340f12a1625246041c684064030300281e48440003554824105800178858880381401400d218411f5140080701c2c6030082e420342e0050002c0c2c5001010041e840341046259040c2d000c0c080c081840c002204016004041c01c588a0b80e1000c02800701c1190b50300c0020354840800c0c056540d0465810603125502d017031100300c2a0201d003c0345d0b01803050a01c0413501030700701082107106220403500580c9031603c03200c049445010341014800c0036401840400d02c01c0082490754091600080800100f0340d5140c0140e4a0740c4055510420104900041c08010340c10324054030080b00c1d0b42580207618504101c2528403400c000140540c0703d1541c481201d0003160b00c00d80240350 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 833243525 1250 833242275 833242307
    0x12030e0a0504020d1d0f0d030c03141302040506041512170331080f09012d1403040f02011d030601061d0306070909020f0f2101080601030c03020d03 65
    0x14803501c1c0000041d00801045013000000080d05c07410b40015032000403103c0011030711101800b00c3c1c4594100980c0130b000c0030700d60074060684640c50100108031000e8014843d891300029017141002d82d00501c0200c51024041900031820305c1103c0e1034800c0003406031803c40e5200a100292410b00d42441c0d5031414280e0360441d08070b0000014880b54080f030f1030460844400c2c2e035010b1980341080d1203006045030b43c0709400500840c0e0600040c10041070000c094500b404c0103042c010b62441c000c80c200c4900b00340e002100c9110800b0800604940d07980461034002800f1036200341882c5082585030390480c1c0c080701c0302c0241000809814003c0c0031900c5c02c0c6070080c00c0b00c05000c80b45256101d17a0080c00d0200301844021000919040c0d01c403d5240006205004014980340e00c036881e030600d0400c0e4042c3d8091000003030205010020641c0340d000c1e85008040003110074129880000e408249c1903801003040c1d02c41d000c25071003c0700501c00310710071440c1682201e0781241d0541c11400586029580c400c64140381c24 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 833244775 1250 833243525 833243527
    0x207050a050d111003050415090b040816022808010605061e07080c0607080606181215010b090901080a05070501200f060405120a090e10031718010912030e0a050402 72
    0xc213134260550012409180300c1c2c505240209200c1e504d180842d0320412020f0804d000040c017050104034000700500c8030702c05d801c5049040c1101e507000310703007a80d001400030051412105080c0b007990328850354240241070020028441c4034070b0007000070160700a980340e00381400c014034404400008540215000c1690090406441d42c5d81c813421b0319103c1c0c00460b200e6001c11403110000d00c1c1441d0980c1101d091281424141c60100540b205110500c90389552082c4030f44101c20b010200e800c40c4510781e0b802000313242c11590f40e8000e82018443c9081c01039000d00d08550200d4401c00c000340000c160441692001e00c0c0c10100070000344212801c00d203482245c03401d00d0040440420034410042041486940a0012a41114107000040e1614454998101d0004096607000c6c4500040501c01903000120701380c40400c41604c0f602c904e00c480c0744819142212090004104c070084900004d04e1080d00c0003400c1012503549072040030148050701440040400071110204a0320780d4070b01d070f00310b405090050021 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 833246025 1250 833244775 833244799
    0x4050a09090b34050c0a0b09010b010903020102060c0309070f1d2a0d020f030f070e09010b121801021c0b0402040b1902030c06070f0f0207050a050d11 66
    0x840001c080c0a40107541c04105240020b08950070000d40c22580e4903004501014420416142107050031106801010024108607211403c1c80410244240358000c0707040710510305082c0d80c0c1a00712507607140101e040c0244041f0400240c0c3e0042250380d40520b1011505990360f49488000c1d040811903081340c0110382e04200003140d03a042c94031801c00000d0303c14140810341d071501d14280c480060304583c60142007103c0004038124000c00f0000d800114030101c1c0c090304060304034102d4403042c0c008031140b5043c660480e04011030b890380b0007a20b09880d84142d9511000d941032800c0f404182c4600210103007252607041c0030031900e89d080344055561085101c000c43d12000481ca9200300e18003c1000780c00103e09100141d0000e19040c03084030200e0780f460410710314000001540a500758080c000c1d00066001c28410300940200c28400c061141e1502d030b0728841c500741c091030040c01c0000060582c90440d40302032020300254580191704d81c25900b046810003c083c44038a85203c0302e034080607025030060920091 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 833247275 1250 833246025 833246039
    0x31b13180804031505040c17070b0403210f0c063206030c0f1e0114030106030902040e0a0f030509060d0f02090418051f0b0904350702060d0204050a 65
    0x600250b92164181d4800c079041601381c8400d840c82036130b01900303c082210040054042c2480d8540d00c43c065402541d10140da50103680f59290400d60090b500c02070100c1d004c1034501210350781c00c401c40c0000d04000c401c0d144162802001c605030b00d43d00500d001d5480915202e0803d0401e10807203000d5400c1c1d003030000d2055920382c03200800800e0310403d020388210004c490151500c00345100c400180500700d139000344c480303484048028403e54207188c10321801620a00030400010011806082141c0700401d419020748188400c03038950250300007641e04071030f03501000901100280e5406a0f0185415512a080b8000094440c030138294403042c00b174a441c070245a4840c2d0358003d404408800c0310100003100340c00e03071681c001100441c0e00401e80d82000010307030304241d1000d5001044010142001402400e15404940380840a80f03040c0c801c00310080c1d28500d02d007070403c92080748000e108441c10a1303d0811920400a02511000030b120b001d02050200c1d10802d141d05070341c010400208511200703a50341d14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 833248525 1250 833247275 833247277
    0x30d0605040c0903080319091a0906070c1e1401020703020f0c0102121213020405071d24070f170d0c18090e070302040f0218031b131808 60
    0x1145a000e40d0820045031001c0f40103d2040c0308490300505498610b07564840e5085031050b000d00e40b00c1c1002c0d911003840011881e03c0c2d030f000079041e1140104440c1810001c540b585003100080c5894204a101c1115000250880d42c0380c0d44406881c009011240d0840d1400c44090311610405280070340c40802d02c40185940090340c40740d40d41d1550180c1d1800304010004a031501c40c070400c211803410017000480301d407015150340e0580c8040a010b00540c005401d50008059070350598140c000601e503058664010f801d010a8840c0b040f10480e10080010043e100c1c50109405000141c4003020002c0360705001e000310143d0341700c01250b1062035060064104148000c141d000903c031b080245280292200d41c40d070082140c2c0080d407184222503000c180c03034440c01d180034004a00c080900b50082c4480000140c982e800744010642c0c040902580b00c04258011060603541044424030035805100b41c44080c4040c001020030022041d604a29040410f1041f88040c14400444038081100c081c421400d01240d50 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 833249775 1250 833248525 833248529
    0x906022b0309150e07061e08060919091a0a090b0606090a030b04081903050618091608010c020c060f03041e050a080304021201050702100509011103040c32040209040608030d06 77
    0x40c54400302c0ca05959054407401400704110340100354400b020032403511b002e688ac0741c0e2000c000b01c844880900c100e9542c1e010780d060514100c51210021008000c2509280f4000d507001821800800c20307000300740c4415000000c090800d9004074800954001c490301c90180303e5000d1038128a01c00f0312801c262401044a80c0000054642000d5040301c0b070650601c42e00419004420080c51810f41c0818401c001d00000c40c040c082130414440c00c500500f000d41141d020740000c00c3c02800003e036040c846000a410208654407080c4546820410840413003143c205880c0c205800408151a02c0c58a002c01102e2104552015049224104000c01000700384d00046101e03520903250b50f44417441e280c01e010300b80c0d081541c0c0e000258110501c4145c001055600155015555000124140d00105844402a4415181070b51040d00d4210140f100314503000b060f0f1121a1401a20103804450002e010103840384100041c0c0b1460b00024203002c0e683d02c5400000143c500071003074a5543c1540c00740310000381014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 833251025 1250 833249775 833249777
    0xb16050319030518100c0e030d090e0a0204030b0a0506242106030d111603052b0210090204060f120b0c0313020904140d0906022b0309150e0706 63
    0x1003c0012420106002602000c4000c0001040603050102c0003902629902c411002004540340c00c44d000c665040160114624841c0c5400d280b00c1c0c1070449023244080d00030002c03044103004200400001c0c80544030640d100e100c00d400040c00f52030341d0f40000c021202080c2c503007007007440100554000e4076980d001072001000d0410f8498012640319041c0e968100c2c1240c0d1554150008160a04203c1c0940c5811000c80c4620060761003018640501a011100135003003941da0368032462110300726032580b031300104514010400035042007042001c025078888206000d01c900380d480d21030310400c64031541c0054015080804900a1042e01ca48403083e2003106c0b003400740c0d68440d6140118100ca07041c0002c03240211a4031141001c0300c5816000d2240101000c0e104840006489050300e0f106071044c410321444100c10780e0740005191422030004c1c80c103449040c0d400c81c5800003003080b000f00b10920400700c105c500542000301301041d241c1094200342a40c280d079401c3c55420441001700350700c00818a030040d2051 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 833252275 1250 833251025 833251031
    0x70c0e1b090904020d0c080309040e01062403060e0a052409310803090708060106201501030c060f0503010e0f180a060603020f010f02070b1605031903 66
    0x2591035545031400c1000e0215200c21020040040039040004400d0742c4140090210b0041c40020ba892810200503a8050714003a0000300702c0e00001c0c5801c0c06103400d84512036000b03016003030809024231440c4440003030b1181c00c03031941c0c0c0b00403501c00c1c0250042ca0040038403044040e014a460038044014107403c44219075032a800440d4805841c6452242c1034041e44050403a806981d1071040c0c0c2400251b282c421401c255080c007905042d04c0359030204043c13000b031060a0380ca4403801c0007442180740c042185c20140107a0410390040c090681d1040003807644070504200004905c1084003010308140400c065100600030702c50002c010702182c0383d004000c48046544074007055034400310032102e5000a00510b1500000c80c4c1c0840c0145108141c0315401c10000b00000314941e80c4049014600b40b4440380469225407141002c0040d03240400f40301c26114020709024070000f114200003501c5804601a12524400128000801c0035622070b03c0c428159100f0101c0356503000342d503018900e00315070300300510000b41 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 833253525 1250 833252275 833252281
    0x1101111509151608061512040c0f0806040305120a2c071e36050114040207080706200c0a150e0304030b190f090c05033f070c0e 56
    0x44000c4030f410480c1c03142d52450a40d4803090700700192600b480c0c10321000242c051010855002803010326070700941c03050180282c224030300b04140070315071661303844150550009070070000072030341001c01c0780c0107090164481d9150703a40d503450702d200600e044003030308444103010040c920390422110400c40490400c0411a64090341c1c2d101494405e07003c90000c1c840c9480030700410059000804105604130300000004801010062041c10854003203113170002580d13448000401464404241c1c3c00070014090754254603081c8642c552107507601c10304e140148a0b980d522105822855005114540b40c0c4504501c02d56502040851665811100f00c09030340e1820fa001350516803803c030303109035040407000300f0141d0f007098603545030610281c4d4000d22000052245008074450103905210700b058007034820000060001141c00e20030320804541e00213038003951180d82d5040c400c918030790280d4111040300f01c40c1805490400d1003c030a900d007080c6840703844000800d00c04104182d440318403080d6a1072040401007a6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 833254775 1250 833253525 833253541
    0xb0705010b090a06081f0e03160c0806070512090705030d17061e0105070602040b03010f080d0f120902040e031305031203040201050406050901050c07030c05030c0d110111150915 78
    0x244440c4160341d420350144001c6c52006180001003035414445c40400140c052a45094508640c8030b09800d1180300041081b003810015504416006080f2440003481c40303291000000e00039124082c54105600c0d08507000a2148404225603800303800e024013900c2d030b401400300c2d02905032102204075556840e4003900288040c18000350418090021000c81c60850340b8000055469030300c44034040e40c005400300000f0a000030303128011802400c0d140b00c1c490745945800156800e124280c544c1c4410052000007d45d1199030160040c0107482000794005115a26440020010074280c2c0c86000300e40800f240003c83c10720022018002c0325810340540c0c0d280100a0300015541c03200b202d0090210368203000512034070f84510068500e07400107042a515001c1d40210f142d140a1695000319602102420b09100303500b01400f0030f441c45101612020440b00c030b02c0d071350f210300c0084a800160400100245000201c00e0030009501581d107601000300799070902441d1740d5280c0000d1080c41c0c224041c4480802d1840f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 833256025 1250 833254775 833254781
    0x60305031c0e070302040c020f0105012c0720010207020307240f1407030903080c0105091605031b0a1806050f15090918120310061b080a05040b0705010b090a 69
    0x2c0c06076026007981c07800c5500708801000364040c80e60440c811802c400704e004009100e070701d001c2d050342900c50280c842c0b02e5400a500031081009132202c4011003081c400700d59003240d040040c00b504500340203031506580d40e1140c024024218040d40c1485103202c002001c055200340720f400002e81c261070031002c6000c0070042d45c0c0c0340283c485503400100a00210403c0184d03400113442054800e00c0c00d46201c0303590351600d0455803c1180d410580303942d0b54091001c540b0040020100c40080e514121501c189081c000175280d221484e100c0c40a844204205810740d501c01300c1d00320144c0b02251005a2040820803002d00402042c066140580340c500000d049614000d00d500350004040d405481ca44810841400480c600103004141c0c9100451442c801c0260280205041040c06d011201c0c0c9a107812030500782c1100c920b9001205001c1120a15082003c04201d052440c5400c840d400c0d603546032181c0221421300c15503200001d80580440c4210030000190443c0d42103100445015aa507150303d0110703012 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 833257275 1250 833256025 833256041
    0x424030203011805041110030b03010b090105101202160302070905090c0901030f050c03030c01020a020c0a08060c030c04030203100e1b032a0402040801091b060e22060305031c 77
    0xc10900550115044116400c0f5917801845101c0711000e0603d01404540303052004170711a0302090700c2d0078801c215403c0c00d100d402c0010004031840001c40d4900030129255203829031490302000900320003134850651640440c3c84540f42c1300d060000b00046400e00945510860081080031828003000c10503007000010840c8080c80b0007801c180099103107585050406260301c1c821100303400360385a00f0040340e03000c0c4003074100500120005640c0d90250b92000b4186000e1000c0c041c8105601403041c46140700c0010425403000300350301003569a483e0074414505038080c0e64402035151040c0700300140600c41d42d400504030034080f4404c40b0800c1d201421607040c0074804544250301544064900f0126850441c09035116150a05116119070010350125090364456040380d034060b0344900d100000c0101d02c214801208452403140740242d030420800070844010031100034072401c0c08843d141141d0128649140f99103807101000c006a580e01c0c54101d0700c030f030004000040b64020100010602c03d40300c0c020444 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 833258525 1250 833257275 833257289
    0x130f140910081e190c1418270f031803030a2106180902010212131401050c1605040606050f0d1d0703141002090f010c06020f042403020301 61
    0x2041015500080c0d0301e440d60100e556a1045000c010320748894840e021090600501034404590705007891b4280204103410300c1c2d401078440204590440c004118a1900094000034140d800f4800640c258903c15043c1f0340c203145406580100380d495000000181048403c0c0700074060703011042c000b019142e01414400c5030106001801c540da04011101d84402ca903d44084001034460703c03070940000120701042c0340140e0340d60321030014040d5a010041900d480420840303580c90444910941e410a480d40c1c8100324001c400f8a40c0810680c0c0105c059031750481d888030455000c807503058099502001d6034401d03507000328582003001c500710380f0810880342c40c05000b0548902c2d014811100c4002800c50348843c1c601c4403000300191303030484d0040c003140006600810ae1075540300d1802d401c05007040c10900311700c000d0a00c10480d035031042c0c030f40b1100061449002d0800190812050902c24080e01c500d00c0c034a501e003000050003007150420b8030032000d0030060800700e44002d840c441d2420b600701d100070b01442d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 833259775 1250 833258525 833258533
    0x90804140906220509100e01090c0807032123090f0a060c140a1a0109060e010302090c0309151303111605061605030a08011d0403080c130f14091008 65
    0x105900b4095000300e5000b0182034206c40031012843c240310100c0d03c481c22240007070f945440b81b420510414400c0a406002040b0280002c00d203165108000c0709021280601a10b50f207200501941c0d01943c0740c440f900d40d2103010030200c0021009813900c150322000560380b04003918050440141410a0400103407411500c071521180450380702c409a10304524402004c2e441940820800a401603054112603150001a8200c03135040c1400c2c1410f85400340c00046a0850100040000d40d50344001e10707401c403025150341643c079203d1440c06070030500b2440350011541900f000b8003010343c0340c5001020100780030f41d0b85c0c2d035a04006c0c0d4181a03111070204902d818040d0404205200d14030b8070b500107040401c0d80425aa041d4400c555075241540c2204032000081211503004028103220710000950f8114a20805601880c099134003900080000e440105010800302d8250341400001076400040d000444103003014550302c4510720081540c030064140944800c1d40420007480301d00000c9000d031016030b8058 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 833261025 1250 833259775 833259829
    0x120a03050a0c060b06040b0301060f05030402010c0209092a030705010215040303051816060e0d0210030b010905060f030103020f060a0f080c04090e2d070b030a090804140906 76
    0x1100c1c001d006210584200b0742d82c00e81915203545845c0207000801202c006c4940fa0f41c03402e4406003511400502e0901800000c208110050f80c0c40413802841684c103e031380e101e031900c450100c00d01e00841d0350032603903540400304442c0d0380d2640305980e88000d801e0110f0440d1840e6446a00481c0c0f907000e003c01e03403c8050340c00404100024082d07001254804c61240d000904d080f951919180b400d003c04002c10036001d039018092010907404030501d40d0300300c0b080d5400303c040c825540c0030079500c95100481c00b08055803101d0b030110613032181030440001d00004140305d4803182c042600700b880e5030007071008912940018138012950b040c29030658481c0c80b050384845408403030b22182696554401450110a00800c0201103601c100d20f22a141981c0c04660007002109445008545100e050b042100a0000300d1146a5180940080c1c100e0543d086080180e44075210601d43c0d2015210092004226801c082008100b031451403034151114481254008a66140c40d0140818404d281c0e5121240e61031000781 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 833262275 1250 833261025 833261027
    0x705010e012d091a0403050a030c1103030412140d020301090f150320040e0d1112160203010917030a06090b0a03030e0a0306180c1a0714030903100b120a03050a 70
    0xc00f02e500861070540d0341c80c0d294a88070440b6400711401c0300412030114000c41140d038540704a4242010381e09114100304060350103969039010040000700a0341c40c084000e08421312481048408031080780816841700d991044210294109024244141d0b10303010310348400342c400303000704581c030340300b02120810103070a64035645c00c24612000a0b491a160240c61100151541c2c810359003154501c4000d044100300c1040e0040840b04415800c0510751b01441d91114075144003001c840143c450740700071000300d42c15403010034098680840c5c00380c5815803407914800c0c0203031413500071440340065140400056032291780c000d040705c001404840d0080c510840c20300c002800b850200031b10900c01001c44018595070354450050f80d180e000c2101d10a81d00340507030400c0000740361403000070701070070300c1410319020340b500b440d0207035004031603000c0c25420060b82c0716138120400b40129001003001038240da02e10b034448081c82024208403140c182c001e2904041108017090041071055096905548480c940254108 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 833263525 1250 833262275 833262281
    0x10f2904030b0903091503180c030705010e01021f02191e050d020c120d0f0509062e080601050109081c050c070f0e18060f0420060705010e012d 63
    0x4003d410f07038481003165000300c1d541d600700c03210302d81400d205543e56403030840c58402c07905031414400303002c56102d8010700400b550041200c005961081c40c100504c0110302c00103c0c03400008903c45030100d050080c4081030140c03190020710b041e01c140c01000c0412001080d088680000810250001034030b24032500990501ca44d0040c441d0843c0d0b96405820b18540940180c18050400e80c500780340e84000640a40304503103400380c0e0516001040040201d8a484251aa10b4140041c0040040707500d400010408400500184a80004501552074000d4840071010380e40c00c1c0a0207030754082804003600060380800090403140140f40940c00240850189600351204d420801c0d2181c140e008548010a02280d041140e10050440c40984d403018100f0f4072519075041841c0812a199800c807000f040103112280d05696003003584421156801c1a200d690000ca08000b00ba840d54024000201141480815000540d20145441c000c1110304e20360b00e4a40403c80c40d008040c0140401000301c50380f0000a68 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 833264775 1250 833263525 833263531
    0x114041a031518040510020f070b0c1c0902130c0e04050606040504020c01020d0605030304030507061d090c030f0c030105100311041e0e0601030515040221010f2904030b 74
    0x50060640d042e079000000741c8280208002e80c0580700b00307000300024420108103454607440c401c03e0031494a1070b000c1c2030340120310810074050150000310000c542c0c404103500c115000c54803031803417682c00c00e04080000e101a1009400592080c1c08500340c64030071680d1f41c03154107461a000d481d2228100c0c0280140806840028240b5900602c00e100006207902d4500081113004c0303800d0001070307868a401c4015811038400381c2289000754401e102c02e00004a001503610182c545d1400c01489a03034048007450300f0a80900382c40307a007240c4410140a004014030020b5800f4188040d001c0989560341000c0d8100c90109100c0c06a02c6130088214442c4280241c0c0b00c00d0754242380e10415840c0c039842d9918074414082e9811820380004a0701010056180d14100003600407409190602690034082040303801d500024402c0b45c0304a600051000d14002903290003a6441038414001040d036954410f03912800c5003511842286020180401d410382e122a080341c00840018001c45060a0030b54540100e085801 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 833266025 1250 833264775 833264791
    0x20a0c06050421020c0a080a03051c09020a0b0703030c0c030e0d081e0901140a0504090e011506111608030412141204090e1902090603010207020607060b0114041a03 72
    0x40b4015003801da04085409410f0890750010441451504103100100d402c0c0d6005400e69084001a030000a5122007120030850007111402da4168040311140010582c071380b402035011450350310010f01148014050048240252002c205002101d6400e03075070614007000080004403280007244080c030b482c08421440310f0007034040e0350411801d1081811600d210032070515541001007007031401d42d0f03440b00f501468000c941c130485003026034825000c0c0c224080c6021b24540d282e00c0c0d81d94130000540075400400d0358000c00142542c08d9548240241032040c8049400030940550b48287c07401c0c4601003140ca00300d95542c00154505444c005c140c044050710f80404450b65445c4078884d440102d8200f014100103002505120340d62454140c4240890b00c03a01421000c94009a41341c4488180f4803109100540d0180c0c1e0902e9035a42d01b200090081c418003d00039444179002c0340c04818001c080d80300d110241000c1c5c991080c5280d21040110755809680314683c2440032402c2c00c600e541000350007540e001070903 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 833267275 1250 833266025 833266043
    0xf180105120f0f0c03120c10020708280905040e030405090a290109150f0e041803050309240a152607090e030a1809020c06070801050103020a0c060504 66
    0x141503107608203412016034281d40c2e44600e40c4c02030585002d1003030941c210b5071086070038500810203e00a403212000051400a10703400f241c40c80a002000003116032031580700888004e50281603100810800b0100b10f100000340d200000171881e41414403070075046039005002141001d141c102000032410008040050043c1c403028001146065440c0314624115034900042d03072081d02c440010030b807022640c0309403160780c0100030f4900210b8001c1c10020b04004a884c0c1110b18410b4003010401502e17406514124100c104403440301811740c00030103140078088400c2900c402040030003402e0740d0351555450040303580c80300c44046030740c40307509510465410301c2c4a0030a220040d40c84075003082d00c80b00e2082c900b003049490a0114100398042c84140050990844104140100c0d0b1103aa66603001c4e444224050010100d003000020035080908001403250301c009650b10341048968503140c2da0b0580d84400812a03620000c601903002e40241c410004041c2e030341c04c1c40b0007020703207801c2d011300700103801640e002c52 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 833268525 1250 833267275 833267293
    0x9080702030d020307030806040506011409030a23070509070504052806170601020109080d0213120326010302090f0a02160831090b0622050f18010512 66
    0x3030901c040100040d01d0f80280d9100d400070b00740903081d13030802828944076a24000401c40141e0304622000041c0c44a070300155260310401e8040381c98010310140140c80b0304581c0c0070700301e09840903810b0310300884429825545440d40d0b510074816200410b07900709000c00e80c14001481941442c900103845420a218921071800041c1800419154181c112000040c030b9056900540c031281c1c8910750704040b00b840200103890142c0c60303c203414021980c40700c882c69000214400c3d286003480d00000508038071020480558480e00d0b0141403402c0c0c1c51440345095500d040503000501d401003040d41202e0300503001984a503600c51418050080080c1101c04da10780c240603145c48520b4401802c02a00e01c40e80b1169034030310360b07841000000038076003100c0e050000940300b10948481c0903110384d5003210346100d0003155a812080001d078003070040611200200258410410303000d00070001580458609a94110051080320103001c00d082c04007603501c001015040c010800c030308241c1e18244849000c1c07016501d00ca9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 833269775 1250 833268525 833268529
    0x100b03010b0a110d02060105040c0507051c020111040b0d090f0f0c030c1208071e082106010801030201020c28090510060507020913030c1a09011a031009080702 70
    0x2820a80120406100200e51a800c25402460320b80c0c2e4542104002c104400301d032030300203644200500a181c0510f49031400420340501580c1590920342d03125003680d40b500740d000d440381d1030071020700401001982050003950582a100701100c081d100820180c6180444004d038040142c12440e49c01c48450016041000101e050f000251f5209485840720542442c5107003042c0703186440c86d8000760141800040745000013100241102d0710a5030000248640d1550b20140305241d08200c9400362004800207105400c580c0d4a011341c0d40d4080c0300d41c042c41003a031184001150080c03000d00000b405a40903034480d40481c03910100710602440d890304602080704243d00c04000299290348980a51900c0c0c1c020b00012040d802c440070060601803601a041c080d1980000320711000141194000800030503180041c14400c10b50642d44907001040718440000c0d00601d04c0d0391500469442080c0d51904012800490f202360f011b28813080024010a0381e070071059440001007041038811500c0c02e204010703940050f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 833271025 1250 833269775 833269777
    0x8070c02010519020a0318120b0405030d0c021005091b01081b0f0c060603010b15031b030f04051b130c050408010c0504290301060e010e0405010f05190e0609100b 71
    0x1941994041c10050020380340107030403a081201d07401b45160030441f00344041034081d829a82e01a400074203110a503140d5080090441c1704060322542114141850600300035000292401c0758154107408114a980d0f041307515440b80b41203502c1e2140341040c46c01c800300a6100b01116034020303101c44c109000f81491109006c050340d0001e010355908020105880c511941d060200a5010400780c0081c007594010400180e2005000b040c5043c0004002c00400d02c0802d803000006802080f1121442d0303217040c001c2c480124898111001ca449210b03c818050481e007603001c0c00100d03020301070000410303c40e019104074064010041c0b82020801c05000000d4105001d000d42e4a00da41d076034403260350b514100030684035403130407180f4500c211301c5810700c0e144014060041104c0c1140c0c00751070b00c0445d03003580c90f004031440084070018560242c01c00002082135803040d00c2820407100100d030440005020650120a10303450341c818054081d5621000840c2c0d418251501d41d03200c1c800229900b08240c07151a50441c2d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 833272275 1250 833271025 833271067
    0x5060f0a2a020f01020408030405240304030905040506012c040b0a090f0b060a0203090103180f0606230303071415070221162003010f020304110f0108070c020105 71
    0x1c0d00219502450100c0c0c05100168082d1003420003541303000c1c02c008481b5503900c0340e440b6003405101b8215601001d4050310b08860103003504801c000b552070400e414000c3c0510a980205441545040d0200741690301a821240080c040d010929400203511f508040301e02042c803503e0341d04651210042000395a410441c007000e400004400500b0a030001c1c00c100440e0422800d00f0f010341000c000084030361703400109035000d060091801280032450f101c421019508010401400102414500010800d5079003122090fa80c2034403010031109161510500c1c40c09400c1881a05504100600400b00709160105030b56403854030304840d005a40700c88111010030084917020016084000e41c20f18031518161180149d1408522603030601c04a0300140c404c80721b6031000140300c00521002d03100500800c035140070215000038001c00040c81c1c1044400041d5004807421200e40141407207010461900031220614601c061303540c01c0d000d550390340c420346e8182003550040c0e040c45030500c407659840c0c3d84c51134280d80d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 833273381 1106 833272275 833272331
    0x13061b0b100b280503010b0403080f0c0607090f0506070213051824010e0112230316030806011d010320040803031e0405060f0a 56
    0x6034406140d030104002c5180842e00000084445402200c01c01c1103d0b80b600c1d00840103401104e00c1c0c0b00c240a003051500e803d00c0280040b60541014010009041d00c41364a0046070410607440c00c10120303030030b40008440b50810303c418807041041174014401030310300c10f007018240d82c0001c036225403076240c80c1041e0b41d540c80019036000f030100d01c0300c52400d04041a501e4844014a201c440104094090780d0030486030b100000b610030303072640c5481c1240c10111b61007410302207580c0c80d07444504607004020b20701250408090b0500505000400002e800003e10625040e51482c001c2c040000003000c0c541400b00858414030308007050458203005070424a400a000100900044c03450003511440711441000814041941080040194011054100750085000c0810401c41500310304503001843c0da040000840d4803103901c0200941c0040b440e100124010101001d0840c80900740c042240d = true := by decide +kernel

theorem cover : BRFrame.Cov 833093525 833273381 := by
  have h0 := BRFrame.cov_init 833093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 833093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 833093525 ≤ n) (h2 : n < 833273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
