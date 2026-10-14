-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3184
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:54:47.577077+00:00
-- url     : https://prove2.me/submissions/69147ce2-e6fa-4a89-a681-c14c56292355

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 572482014 ≤ n < 572661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 572483264 1250 572482014 572482033
    0x40b18011820070c1a120906070c1b120f2901061b0501050a0b01090909030903060b01050c0a0303021b0105010e012616061d0904030311092808 63
    0x60841c1030b60503204003441d08001182c4041200d0400c4441c014440c40c0b4041c8800903074800d05441c503603c0380088203030140c0410702085030003d000c141c0c58080e601c03645a0035403000d815a1781405448c0030702c0405160f402501c400007440d0500d4a485c00001d1310030400d5000c0703246c1d2882c003001c0c2c5143e00c803189610100c031501001c03407000c40c4001140c151070003410007500318040c40415041c40b03090850024820350074481032000505880c1c220200d115002d072103002c02c00b51128900c0d4101d5184000103000109801c40400c00704079240c1c041c0301004010f00d04240341203507500a1a00d80440050f046002a13030000b8101c0a42080c0030014004104620003441154900b00521544040c18000c400c1e902a10190b4503044051b030465022151031000143d0742c1d602c01040070003007402c0c0d031031042c1c1f03000c628000500508411030b005e00844849004103c074030583c0b9582c4041f0b0050141a0f00061801d00c1041460a19640c0383c0c4801c00d01c814614149446000c10306000d001c00c811039111071103d81c400500d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 572484514 1250 572483264 572483291
    0x705031b03122202220506180a02165c010e03150106080a050c1902030c01090809210a120909110702011103040602100902040b180118 59
    0x1250000d40c0d0001d900030304850100803d1052000c00c0340254481c2000d0360004100d0f00c840f0036002040540c4800b084140d40d0102484020078250b464241c81c98503540009510803026406403145d011003221014451003e50b94041007069907806a81410328824078580d0711039019049114040804108440b02480d0704000c02d15074061034466002580d0650090440d80c0d104482580340204001c0864034020810700d00021003010a02402000802d1000040c2c00300007180289401054201076852822420040e8200b41005140064046010420191040301c6c42400b804200c0e030300410400703580d4021801000001c10242118590f5041407000700c85201c00003240300c0c0e0135107801c98080c0710b60b001014400c540080301070700035009080c030380000d81511400d070001a0420500c01c0c0ca404404c51030750302c0001da0b030340524894034005921012880d85105410b40041a1280c8084c00c042150001c005c0091a442d8101302080c2012880000401c1110000103002d8503a01c20100100071040f49000c5c07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 572485764 1250 572484514 572484547
    0x3112d0609011505010e1302030f090606060901090303031e0c0914120a0f031e030203010305010b0a05150901050417011b03110909040218040302010e0106060e030a0204110f0705031b03 81
    0x4c0b0350611403503d403900351b1a107802013030110543c0c000f8401c40d0b9919001a040084030f00582d01a2128802d06002511030f0810201300c07481c86005840707018929140d1b40d411800b800d000f91100da030001c00101c120284003002c8c02000c4480b40240c8589503c0d41c01d080e82940012079501d03443d44100000f0a0048641401003114501e040d002a10550045094102030b00c48101611041c00480c100824041c01d180d4954041c5051301d2207500203000000c583c0003000411440d9000c1d03d030780425016210300d44019480000c003c04c8070306041c11420f02d0340d0780304c1070103807190f100d8187c80c0035945601d0146034140500c2c0060b500c0c1190b81c02c0400503041400300fa445a4003c0401c801c0c040d84043d004141590313100da003203212100b000a8085180d151501e0001e02030312009408a545600700840858141c0c0280030340b14520034064010f006a0032580c00f0807019000010b1264542e81003002211001c3c145c41c0b0040401e40c0c011401566500c811448145844640d4007010310190000e10100040804495 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 572487014 1250 572485764 572485769
    0xf03040303020c190501051009090507091a06070627030e010311270f060a020c10110d05040e010b120721020d09050c031903112d06090115 61
    0x20740141c841028842041ca8049011403101101c407990b15118108070054112500c6690440b40b121995656180450166009180000c24980000b6000d00420740c90758040c7c1ca0391050041d01020074004203000c1000399003c128143c619070348070b1780f035140748003106001c1d13441184140260400002c000d80f4010100d0080742c040c203040680380d9180604183d8460203031102403580e00780c0350029151015001c101c03e82072440309405091002e944144a1402c002500c64030702d2640c0140c11720060b013408000180142800d00c5040c441030749040401f00c2e504101140140c1c10742e0b11030995507800c10121064241d4144e0200e4469441007160040d4000380d0403045800807a81d05041c81000e0303038983c010703d550280d0001c40480610118078640441c003240c00000d0000d0184081e40c14001000050581783d15600386040c08a008031000c100000c0c1c07180c10f2804004400a003030341c03034001c241500600d900c0072601405a40340c200e401c5041c4050800d010141e00006400020003421100d2203141440b0341492 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 572488264 1250 572487014 572487017
    0xf04020417120a0210110d0f02190302040810020f04210b0a0203012d08030d060302120105090c011209050114040318060e040c022b08010b0906030109020307030216060e0d02030f030403 81
    0x2500d1075031b01c505080341901c000703916103201401408007107038507000203400800b88200030300d0529020054480c003a02c00c032401d640c0004040c0c03880005d81894000654003006141e011410200000180018070109002142e0f814001204141603181005a00d003480031b4200000b40c1e00c1000100520000c80d1018614090043c07030030718280c030000c00e15580c0b0340d00d19481b904030790000003000c910030359131984560103880c4200c07851100c104401d00081c1c200d41c0200e8038140294031604c1e10403142d602849a80c0410140c2500110b0030030301c1540da840c02c3d10881402c0310405240003042c0020150000d0f03050001c28078440c0000196464000b0042807030790380c0c0000074025039568100c0c0540c24400c0c000c1801429101c0c05113902c00c04c190035400c0c02d2091080c0303001c000600403800440c61000301d108444503240c0050074117003140d080086407c000c0d40090b200a0034964200003500254410b403603403c0031607000f12000110079401c0080141805040105802150400c00c10740951001c040709494105415 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 572489514 1250 572488264 572488271
    0x80c12060303120108240f06010507021c0c09060b12060603100905040503041d09060c09041803080402030601060f1e090305070e0a0c05090319020f04020417120a0210 73
    0x24800800d04500c658070b0003c520b00007280000c6070101000610040790849250313102564120701b4400b010104041e00e40b11001d003070102c0401d1082d0f00c504050055140000c0481c1c204c08010520ba8400c201412000c644c201a0800100b0522106104103c0101415441031b41b4010300c9080040c48142d008102078414840070000ca01d00b4052401540c020707190550301000709003414200b81d503580e00644103610f283c0a1b6402f1101306200003610741d81c02010543c00612040d15180d409070b05581100590076007040d560280045111006809001d8084c000e8403401445e0a00f070044c1410590160031201c24415240d40000d01c0d1a03000c02d033240c4804005d58284082100458120382d4035405a0028190344907a07600855800d241c8040e035400340d1080c040070401c500307040805451034015001390603810f0b000713011140703407501c201e80c0e02e2403489100500c200c0c45401c640c8002412030304140c0102020000b1519000c543e01d40400404a00c5841107503441d04020001200a64924100c1d0141503150384 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 572490764 1250 572489514 572489521
    0x40608030d1e0c1e030b010215060d120e01030c1103091302040e07120c091203030c120f06090b0337080a0503040b0609240604050a0f0510080c12 64
    0x9419480c4442d030705403400240190b880e0110002d00075410210f8510181403071401101506000e4400c0c560300702c406030094072541d4440e10036109000402003009400c00104491480000c58803541d41404c031840340c5404c698510360000040c11908400d150409019008024044101000040c0e491442088480764202640741340308c5070117030045900c54411564902c0901100d2600511424941d840344403040180101010048846100d54850400d800c1c008082000c00b0908c65045840f030038100e802c0003004240380e1420b95046664813000c26030850fa60350f03000d10080105006400c01e401c81240102041818140e100403201070160804000349010b28084a4640180040d01c4c211500448520f4a4150860020301a944101c81c00c03a0b03020380400002d079091402001c440e000e0358840c9084449030401c400d1400707244820710411580701105000024081d40c0302400342001d0407000d0301074200c0d14545020f115203488520034101c180982002084411140304094a030800c0361071111000c03945 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 572492014 1250 572490764 572490791
    0x7030f1e1b03120c030902180103020604180b0d12090803032e09020a0909050109090b0609070309050f0a141f0b0607140618010c051815121005040608030d 68
    0x55004086199081040c80d107036131030701644070f00e81450090300e51901c24058685004001c10003408000d5200c130b0180410300400344001c2c40c2082d4401c41e01800500100d03440d000402d8840006021601c02aa15a070b440a5551003000f010081c2403002c01182581041c02d4131818040c105041c0c0c1d43e0104100394514851255082c103c0000c3c42119011075550160380d900902140450103500b07145401c3c030000154000b80d501c40d400c015500107800a19503250b0303208002d51030a01600520400d9100e03120b00003c280203100a0152000541c01003906940c035160110403c0d00e62100c92101c1c1e000001d00036076844030014001c1d00104c01d90400245140c2030400140c10b8007400d4005005043c0020703007001e46210014030140556a0307211a20740007000341d031a80e4244d800100201002810a0003050300c0944501842d4200840c0280385049500b03015503961425084030303a210401c1d203200820300c42965401004c40020b8001035505110341c50421003c590b60b40700b02000e6031003440d50ad250704030b07000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 572493264 1250 572492014 572492027
    0x406090b090d240f022a01150801020304030f0f120e030c0d030e010e0601081009170706290a090e030c0303040804030b0f010617070c0512041406040f05060a050c0307030f1e1b03 78
    0xf4123418030400b4015031240b46640c000c0d0011a021004101001010760042d801070a0348180c01903650354116040043e0710220000e042c040040040324030080c004e25200101c2403050184002c01a90000703110101c19481d80e0a41e000c46201000541103200148214a004201e05010601045000c58130341003074500f00c42410500403940da20750801250100400405411220b80c0800800e56001100100d00c00098a4480c2e1307401c6940c0200340d600c08024004041c0c104070000500c5800b2750b401c3c520a9080c1c141954400c6a0403200180e00027800d0082200300e0041d180c000171348043c080440c2d0b040070703009031401d00001c001d001050f501c040000e00042c410101032400c16440410380300701d020b8a00240c80b042d04180103000078180726070030b16201c41c1401c60965049405000115110525110600041d6446014102c0411400308800c5a482600301b005101c190300c26600e080710713652440790007459501402090180c1001480410025542c800c080f1401101c4001e00c0512a02851405541a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 572494514 1250 572493264 572493281
    0xa08010b0a082811030708070e09130305040f0f170f100b041506030c020f06040f020402030403021212010501080105100f08070905040e0105090d050406090b090d240f022a01 76
    0x2082c1c20101c0104034080340c0130103103018803a50784491000d602c40700703030603038070344816041440c0c11201820000d1140385014001120b5a8002e040940c40c0c980ca9105c00c1c4086030382038101103c0c6d40c1c0d259000f0071080007440b00034440c9400f01005060040c50081119071546519401010b00a80383e40340003015648592003108460000c0300c01607072495590300003030050315036468044098065100324030420000401c0c400c2c460703603004440403401500b40e401c0200a40002d03000b60210311900491108807501d081c002d00e218040b509548c21590314020004107400c805810131400340700c101d000071050030b42142d1200c0c0003844a051021107a0340d1440d08895a289503842642c0c0b1600740300a101c1e0064040d0711207401581e0318000d80300c0300b08025600b5a0700344540d11904000804a6078104200b002c504090310318080d0080c000005140740d03480e0b600b50110500c105107904400c1b0303600202560402d10540a1005a99200b5401c1140c3c8501500070404008070345186816010b0301d10020b20000c0d4044c004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 572495764 1250 572494514 572494591
    0x31b13080d0e010f02010c1707110a11090106030606170c0c12030a060b0a08011a131401020c01033e072306040809120c0301020c030a08010b0a08 64
    0x24504040e400003403010304100c2c03405021a068100100040f4410b0040303900c4850641c03264030004c051078107190f901a0004041100b00300c040140a00300e00b800303101e407101e201d00030559501110100c1080241124041c0e10200925241c91802c08c940742d041000c0030700030040402041d145617944400c10149100c1c41c1201b000c0740c040d000c0c807295081603030380145008844d280b01c01c0102e0381d1600320210051090b0f014000102d03126100410049210790360400c8075400780160542481c032640d60070100403a903904940000078414005210551381001b46084006092a00b40440d03000325503140740a0a0300400d80404800300030014282c00c18445082c6259281d01e0441c0ea80c4281a05068070300307640e42445d80b1140302c884512600d01e8440014030740d00940e003100a042c070f00014a4100400d05129050310030440c0154400c012080d5420301c040d00d10701c00070380003031561008880801044010140c0000380100030902c20075120503804030b9040d43c8440c109503803000349110071600b082000750400b240c96 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 572497014 1250 572495764 572495773
    0xa050d03030f180c0503070b030c0a020106120b010608070309080a1412010b0715090b061c0c06030b0406051c110d060219201519061415031b1308 64
    0xf4100030100302c0141c0403600076499450311075268001c244d00c0780705900c100c80d01a44240003054000505a0003050303044500d000000c0c066903140f02a13072640401c0c0c103090342d0400202004200164001c0341d419402981c034502081000010b5584c0882c034012074500c5010003104c240f00c0c080c085400001c60f03c41d4014901851900c0da519102c00056900c805401ca070a012002ca0a07aa0710036180200240507501c0f02d00510301da1b5a0b00c0600194240d460313500842c41095444090115040440d4440580019540880d400052100740000d503046a4841809070300790194540e010840c1c0d485003058250310290040038262034100040040e1600304001d440c1a1000500e40c900742c51168001103c1c081c207484411000d284008440003510320200e03141d000d6000344c00c4c4046401000d0055aa1020300080c40c0d00c440c7d01e24041180441e9040d8100d1507000d60b4408000c860740ca0012215044c007000e07000514918503000c0c0400c545002d050102003150708010685052041c42480110080c1000ba42200d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 572498264 1250 572497014 572497031
    0x14120408160e010b03060d0c15020601091820011e02160506210402010302210114190905071b03030911030304081905071e081b0a050d03030f 62
    0xd803140044860320340c0780a045100003803881109290700b412a074200520606640d5001c087c44419049450b040341c034109800d00c08941c40e00340d60242d401d510200c2d4002d211640c18100803a00321491500c507003007100c4840a0301c000280c0050342040403625910f101145200d008001a20403405502120b040090072102a024071540010781100f07200b5041c8002041540e240c080c0007592003800c0c4e0b0f505e50710000300301c0d6500045182c4c1c80d464021f80306140051812100c01000c1440311034910410225000c3d0300c00411051055081040064400f101c00340100d04510b8480411807980748528003095445000190035140a0b0f1400c411241d80c41c2181e94a0500900d4010f00401910070129880c4408082502040c01c0c008261420ba481900007042855000c154100602400400c00c94892252003808600f24445a4001c00011040b04440366542d081c140501d00300002c0c1441c98100103483c8541499a90701d201c881c0003240c43c03e03504a285581503060440c058411020480c50b02c60034081c54 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 572499514 1250 572498264 572498279
    0x2040e120c0d080408160203150a0f0509030f03070c030c05011a09090a200d020a03030203030420010801180213080c040608070e0a05180105090303040c05120703141204 74
    0x4002140031074040d5250401c5240055031810401e0310081d22802040c005069015407001905000600040495020302c03400c40e40888d0b802000c81d00000c1594694810b010200182c0c01031a40002c24203003d541001e001690f82202400000c1c03494007002a0503001e00c09240c05480c0001203a600a0000d10400503c03407a05003003640f0b9a04400d0050b50030300002251802e011804200301903000641500104031003500744260040d014100780d01448000c2e1007070050351003007601e00007584a0340242d6124a010308000100d050741a1012584411241d442e0711103130792007000300d0f05558101520b0480c1c0010040380b44000c4c02003100c2500103007040c4802140f00c05c000620704155502c215814080135442d0391005458000b0f510410030b5074506103001c41c4d85000c1c160001540700300000002e900640141c660103007500d00c241da140100c1d8100005000030b000504410f034001e04800e5449880796481142007a94800d0307148009044541c555003400d110407001d200b40544000000040e98607550ac480b030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 572500764 1250 572499514 572499517
    0x2091f0305060a060c020901030b07031d07061b0c05041109030d0206180703030905100203120c0711060c0d27060206010806150108010603110d180c08011107060902040e12 75
    0x855620a000b0f0343c50014003207100348030364205264060f0529206034030b903a45524000d400601440c0c10b041d140d240e44100140c215003246109240240101091031074120081d0041e4100040e540c04214090008008150340110404c2200c1040e40c000680741d0360306403d040c007070144400455040c094401e000c0c0c40c03164000341c0c0314000e001d00320307202402c0d4014080e407507175070603082c03000034013003400d16104000c1481c100c00c0c4207400d01840d005880c40d04110405e003003030301034084400081d031042c041400350070700180c81500d0304400b000750381007881c4c960200042580e445050410b40c003041006612a020749601071907800c6c0d841d403035501b80c03070b1f0598a556019480c0c01c424000c1c441c2512840b0300144044100c440d00170285d50301078655803100d908000b0708a018049917079030795515900070801500034610b240319030f00103030382c05000035040310b08903240142c0040a20740c03103d441c0b40c0c10700c880d40718103c030144210703400554170940005003504644041009450703d8802c1c41594000d901c103001010340b9110 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 572502014 1250 572500764 572500771
    0x20409021c0f0b030a020114130b030f060307030c120c050402030a0f0e1603140f0304062001052809020907030e25180b031006050f04021c02091f0305 66
    0x20300a000700b5101041040480b00c00b141c003030758154007051032031001d94055481c1c6040501c1c4038510a01d403d03481d9419898290316544001d006490004c10021f4031041c0c01000c80e0407103c1200900712551442d200d8420b40c03507044c006c089080d4075044242c0200441d0b20f121200401019005549130329191300300740014895000c9400116007403800c148416180824242d008480030510b16140500355147e0300407040c201c11013551207201d0814144c0b001c90080000e400181101d58400032030312040c00c80205520703c800000d40c02c5038107180c14001038080c100c0314902e100b14129403080351080c031440c030394018101128019400c04c00b09001c0c00b50259160300180c031900001d1045070181059559801c01c00d11303c000c1d00c0e154402c01804240000c4201c5e012440d105c00200c140400c650101100280c1401904c0c96840c1c00d8594480040003641040501100c6030300c41210110308000d09001b09007590603c1c0c9000d0029140c0c0000d1040d0103545040d83c07900d641c19280d491035803044c084240500104000d5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 572503264 1250 572502014 572502067
    0x105210601021b151c0504050606150735070c0608011707030807140105090a02010f09050a120201031b12060e0c220b0a0804150b15030a02040902 64
    0x801981c402000840b03503d054980150060003516075000900105401c40000c00619019145079420900c0c0580075280c002c502900240425040c50300c04c000d81c2c249018035407031166070103012079401f148000d003440071882204914456500c58859403404040442a056007420a020070440300703000c686c1641005482040d143d04040da43c981d5541950070a07010420003041e406004288002a41c0d8800740c090030344101a48448000030311705150a5549c00c48500303040758050200344041d0b41c2d000c18241c03449803040c100329039040d00340400300c0c003641803034050945000c4000b6850011a407003644416040a5240398070b191401c88001c1c001d00c89a00004080089424400d003c05c4803030001c44502e000d594080c540784d20b0107010301500d2111701a1400b0007940402462400a543d0700c0280003070547e0305195403501d005103072078a0650725030001803018065040c64102d40c03104a8035400d00110b1850321b810710007500c9a4a43c44514041d1080d500303c520b00900200b01203030464168000c425002c0500d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 572504514 1250 572503264 572503273
    0x6090509070306050616021507050f2802010e0d06050708040c050604050612060f0406090209010305100608071812080c0c040506010819060509070804031d0915010521060102 76
    0x2a03640440554500d0302902d85e0200040041c0d0b140c2181c1e000c1c1d000c00b0103202a01c1901a0b02c80c04446010340d401a540603900f0350803200c840c1c41201c0c403d1080c040b001407031003120a03540008042c42a40000d407444024144840760303142043c1903441cac014044109922800500c40d61070306580082ca14842554100d4200c0540a000b25003458103c1c00d03901a10005044942098440c0006004151028001c40d80194000d115060203071124090316001d00081f8001517943c12001e40010129400142030180441022506101d4190b001407110b402019a11380410b00304181c00100441608960241092080d07241c0100100000d800140222000c1d8070b09480c00f40c1c401c08140000e41d4400c40ba01070010b40c04e5000920180d0500303402e14411502d128000801c50b4940f80456840f00c0280c40e0000401c03c1c41d4100030070564021038404664480f2a81d0709400612400400e00e10036000c0e1200d41c100e241000d401c00a80d2144041d2000c241040308008070100f19060810310702102611054018003c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 572505764 1250 572504514 572504521
    0xf0b190e0c12070c031b0c1a090f0f1206070c03080f07080403030c03180f0c060203070809010305070c120c03090b1c090302010603140708010506100f0305100b0406090509 75
    0x201505903444840400c110140c1907483c0c03981100c1d0854200012028008503040500480b1206118102c0c1c4030700c91502c80115030f080196481d002e0134001c00c240e40d04c603000c00100015032141c169424003404c0c15241e1210400f032010002c0c03049590350300d01038000c1c421101001a080d81c0060000c400d94044e444451940e1200041c1d000400400c82d52500480d070500b0202c1c00080c8203520005901006184c0014000d070002d207642010b4401c0441542c240d4560000304052040c00d4207044001c046c203000031450000d403135940c041e10f409000040f9051541d683c0c0080c1d900ea001c0c22000541c55031150385030b4005c1941000c042d245144003a81900020f42075200466400301ca8021140140c2c1d41404000c13000d4a0b41d000380002e810052812030031035403290400000a60241a080042e8207980054008541059481400c481d030091050b4401c1070100c90800346540c0004c0140c014001c1447d01051641c0c909072500c44104413a48007a60009001030f002030100e1341300d0740840540d0003c490b02001c0340c0303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 572507014 1250 572505764 572505781
    0xf0215031b0702093c06030c0d030903061a09130b06090c0d050c09100f120203100b03180f0f01150b1c0603061b0f030905030d0f0b190e 60
    0xc0b07110080d0001c400e403020402d569000729070045021294400c880c05001107507112419550313400c06100d00b8040b01d0013400000d00d014070690038804400e945032958000c19807001002d071021840054400e540e19404007141040d5030007008059003000c0d0a03462107040a42d00301010094140d8140c481c8142071020510a181c0710410781c2c05600303031083e402d041030100c1101100520014045101000c400c01c982582d0781c88070110b00e19138807851b4035803201d0f001c1056400350018200800384443c280c4101b08020680c00c02d9000340c0244c03513101101e6a260340d02e128008203440c41c480307149481d82c415440c101400100015a0b374015504003402840145042800a4800d101a0045401c4440c061101c4881030000802c000c102d03c80b000c03008a03001d42e903500c0b40b0084650f90000001066810300390b6540203038205034004006c11007407401f00074800442d140e00c0d0b264010005500010790b1103c400d074143c440580c000340c940800050100e0b0305800d603001c081c180491640b080b00300340e1002800054409 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 572508264 1250 572507014 572507017
    0x60706050612014d1308150601031b21060801090f0201020714031b030c03010603060203060f0d020d0204021e030106020d2c060d09080f040510020d09141305240f0a120f0215031b 78
    0x4c403442d1544200745030cc52103440d080318450380c1801c011a0750390900140081c001d0003101d10490083e5841e03420b03082503000090030b007007150f0810a41307800444402d07141c40d00c0004100004c141000d80c2c00841c821003000003801c0044c400c400c1a0b1560034140c0201c14040107a009500944088440c0074901d4a2501400701107100120041e6100141388a140701505003900100080045809100c4034011103510a80858000307800c000016484250404000c50300950910600200580302d8842c540a00400c03200903040400d405015a2012480f1581e82c84640c1002050560101403070b07403a03e0187c0070603121034102d445014441ea10b01c0b04115002400481c24600042d22036442c0f0400c18202030074044181c5100501d01c0e00090701c1c410f00f21946006204090080c07070301c29041c144c1e0540c0d1703e469801c2021074844a82c0b0031420034214040c590b90f440908811100710304c0300304440031800e01340440015510b00d40a5042a20240400e541d0050700004604c0b9841104034071041d41350380d07141d00d44207 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 572509514 1250 572508264 572508311
    0x5120706062706080d02030d0e0a0b16081308090d030e0423100e0a020c030403060c050a03060806070207060e031e1501090b060706050612014d130815060103 69
    0x35801c08c1103a5910070655030020425180010210b9071420a650b03103079409940110f6440e074000d02804001c0184560141c0940d410001d4501801440756094030750f50740b188200b80000d4400d5103030203203800c00c141c09040410b0103014014403c016800300e200c1a072030070f401404000d03800008118001400240c0300080715040e43c1403071014010a03503540046500075404541040e40610081c800000007078440d004051540c00190340e1261221355958014051303d00a4020072490340200b003c1201c030079800900e41c0c044610914001c072221890b0340200b8184102c4c8801000610800c0560f04500503000602214410180c80441007a03170740d4074400c01c21034a0010300c0c030b68405c008000c1c0001250a40e080141c001c1001085000120001c0c0589400c56180075444a100415254100c10002c5020086012004203402e2242e2201c0d40c00c00451900d0201100800c640201242c00e2203004950350b054005800c80c6c1048982c213681102108544060490f0200d000030b05041c807100320882c00200d040d1340c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 572510764 1250 572509514 572509517
    0xc1005070f1404180207050c120d1b0b09012301060c0201030207030e09010f050a0611060103120c0501020c07051c020d120c0b190c0c05120706062706080d 68
    0x2018414050226100d091803003800d060b0340700a100200d40c861000380892040d99000c0c0e0b0060307440110b86007031420200b01c201c06520030030b01c0e810071b02000e210200740e0720882c100601d03090141d490300111280c0700c00820321b006000c80d00420f0030403c440702c0540c0a02c1284802040242c1603440501201c0b225002c2400b030540040c50040381080154000e0300602a8240b0a05210740c070000c2590202d00c004400364400280252030070b40811071400c010080001800c1e03546000100040a06050350b62000180b00c020082480807603000203082c0302d0f01b4803216260b0303c48000e56441d80f868402d179907554401c0c0501807248030407469800c10042e0b0300003108038065002e00314010401141e201c00a80c10b00c0ca0b40d4840030f00440e40700e030200090409078054403980c0b458110441c0015003250040841d028442c0c10000d10030b0b03240001000c6003000030452000a00e03200c506907680c1151503d007014220b01d0344880c03070441c1c0c09210000c008007a14140500780c0950602003001c1c0e540e4283c100d6480800c04203900 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 572512014 1250 572510764 572510777
    0x706060f08030712050c0a05070509060f0d0809030718020a0813032c040c12050f01050315060303160605150a0614161703040b0f01030b01090507090801110c100507 72
    0x14001518100c181c1359141207424601c0c2020000311060b41020074283d41214a90400c0700140071a1402c05042d86d0899000c2e204600354040c80400705101b11902040541414404908003a0a603010421040641070460700c0015001c00c024454001c0e401c0b20903c0004107121000241d1000c0c1c40d5079940401c2a01990740043c8090030341e2040050018156a0025000e070068840000340c455014085039801c4540d90b4029030407849244204903000580f09040c0c0d006464010032059400081d210041384040001c65076588411000a00d58402c000a0780d1560300052400800c1c4205507000c28801d082012502080c40d480804104021070315009586c04144400d9107504414a004040c00e50b13404010814904880103460f88420390318101090a03010400000b04801c0200004407290000303020010f010b40340d41160b503410307280c0d9070502809100d180c0d64800074115901c116004002020404000c2280d011501e404080580c84491303504880e1107105100d608105981c441c00c7c0c403801086c0d6861 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 572513264 1250 572512014 572512027
    0x207150c080705032a130305120307021f090c0b0a1205160c1713240203030114010302130e071107031112101418010e120c0a0f080706060f0803 63
    0x203640d481a4400c03079203600a60b101c001002d2000c008000c240c0d00c0306d504034400f8050300e145015860106650342c0166100404c0c420301c0049900000caa0369800610401383c03407209400000b1034000e2555100c00752400451020001d05e1110000060410072820343e41d90414201c07a040440984609a94001140c024030064407101c61040c0c2c102501d1034820380e03100200521101c040c10103904540000c00e43c2d003c5802c070401030210310342c3c5004181d2107403103034007455444001c0340603480f40014429481d03d0b0381035000140300707603100740d0480e03c0409101040150071502c450b400c50141c0c604940c2c01c400301e80d4a6550020740d81c030001d40b2000b1694001e0401150001d60024020031540d40c0c03840e000c952050a0b800d40f00701c038950140c14203c1b0016000c0e08440d240c050724001140b0348480c4004c08036498021400c40403e40421005a4840c103824519554200503061524120790454041d080140400f40c500070070607650000d1418601519040c01502d440b144062110107191290944642c000c0003074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 572514514 1250 572513264 572513281
    0x17030c16050117072c0414071b0812101203030507090f080a060e01090b0109140601111005070219050703260a0e01031811040c1805060d090203010207150c08070503 72
    0x102604070b035900c40200d5121780500440c050f2008035400343d09880441d8208070110b98002c000080d244054200d446140751a51502c00e014420080140006400d903400280c160805424403c014007070403100541c00e4030076050050044c1825074803e000944100d60009000a0000d448d9055a022070090a18120195a42c6008180202c1c4603a00c0795250200c0c0d40100c1d40d50344005008020b50000410350fa0011114940c8042e4010451818407140900c11400310400240c12603103900d14013000111919144001d0346000071001c03c41e02c220041c00901001c01c100800e020341104d11030943d2910480048200e03014202c0c0c001c4880c50520401c0c408003095038407407070100999880c18100000d01c6124031041c903048400142c07040d42d88081c1e181900c042414180b00e8041e16003203038a4404a80817940d80701c1c03007042401c0d220303080c810072000c0303960495101c255005500180d4003d00843d0750354038924201954040e048010400103151031801005c841c02000c0030346c07081c207081d41c4503880c5503104480f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 572515764 1250 572514514 572514557
    0x15060f1011010f05130314030c07030e0d02090a0e01050c071205030c0702060d090b090705030d050c10240f1508040f0501110c0f120417030c1605011707 67
    0x141401c1c1c0b5034903001c019042d00c0d0184140c50040e06840c007132072000145400d001e8005120f01488000c2c5550820812030b1614440f015168481d9051822555040810f07001039161392202001942c4621094180214138046512500d000c20f40708000f8845550b0b4070070003441c01d00030050081d0103860f420030b244407141c0c880c80085030f102c5910022241081e50a40200b07a190b0405d0880c0e80c0c213203558035032102c28030443d0030109500410150081500c20b00701301c0400c1e1900c600c03000c50002c0c0000820362211420080c481f031220f1000f801010806001103c09250b00b52041a5660352803045c0414081414a80045d400d41a50105000020b0719141b824040341d103558010302c103031401c00e070b600401000502c080c0100700361034109000e900e4680c00c007200340d64103004c04224415039940c80074883e299450341c81001c0d01c085501d00401c55209861f14402c0c6070641c81041c403400e40c80c3c09039040e01c082c07000c548800030040d10030a903600301c2560800180180b20902c02d407240008991600302c507101c5403541c40f8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 572517014 1250 572515764 572515787
    0x6150e0604150c060207030e28050618090a0b0a05101b0f050a050c04061d1305030702120304090c03020a08061504050402040f080f0105191503021215060f10 69
    0x2030901c19110b01130f25040101e0308022421000a103000700d03550714520b010001c9940c0d001d0300c121405c4c15000900214800e0301010b109040c024400494880c004044040031a207a5880c06000c0c01907918010080310000e146040b817a0f442a000c4443c0400c17582051204900320300c0c2c042d25500001ca82d240341c501e800440d080411a040042450a000016014480b2840c1c0078402d800800c00342c9201e90070002601c260f9001080700d1400d90803265401602c160701143c1001c42ca082d4000e07010014201641140701d40700d0080e410003060101584445c20001c001d1040350130840c0100b0175a6541c003c1207040e03100d89110000080e5910f070110b4114a0310125078802d80c800200301ca45000c2c2d84902042c2607030480d07803044800d22080c09080103c0c44050040c10300f1001c00000802541c50500c100044008648803008015562410303400c0004a8810070a00619001041818a40d900c0400980e442c92600b00e4040c5807083c40d03000c100c40e030401d020210300c0b080c001040c46503081d210040c00c03110740a840 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 572518264 1250 572517014 572517017
    0xe010c230403080a050904051b09091f0b040e070306050d150603061b110706080106110304121110030506030d031104051c0224120a0e01050a06150e060415 68
    0x1040000b0000c1c10050040031100c1a5803100703600c4001c03001c108002c4440c003d000081084010384030a004548c04811504030b110704036213030f030f082d601c81c901a80c0d29109039195010100700b9004021400c49000c0c000b400c01c603909020810380d20b68139210b01b1000d482032131144030703080205d00342003100041d08400f4180031401c9a200010710740750f407900c88d0802c2d215540140030f0b02003041903000d010f07150302010b0740c5907901c0d004000f41307503070341c070303245000f4009003051080d03000300310482034080a950300620407100201030041d80c0281d28211070400142600c4086000d41c42800e0300c0441c0e002c4103000e40281442288010f029060740c40c40c8810075405840420040070074200e00704004100d554418540d10706a0f810075071810440403403841800300040151020807403516509003002c900420b034a00302c649103480e440071a08184c03500050340e4098001e004070001c0365401c1008214a0511550080d003c80c0c100c2141407101012083c81598020050238545410110130407060184202022807145940e025 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 572519514 1250 572518264 572518267
    0x9010302011b0b040c1d090d0c03020f160626010603020c190b04020307060203180402090406030519110a050f12071503020711060c0c011d0a0f090e010c23 68
    0x2203545a40503640f084030b04035401580f0090601250320041011110b03d510380c8003068803130400001241e61100c209070030400308041030340e01c1e5040520901100f22448a079a044440f0480c02140746141d410442c0903080c00074403040210002d03a030300c019215540300d840c403085604590800d2030032800303503010443d141498031078420b0600b0411a0040c0802c20940034040c040550f06051041505042d11584800b085600601500f203071003d818130401130740c2108440040eaa0b007418000310f07010303080f1a03101401c1e81c002e0081040030709011043d80c0e9421032041d041c0d0121040b02d2070801490b0306590080c0354100c00c20460260007420410750740c02580310b09508540c401648c401841d501ea1018a4400000031740104080d010407100d004002445101151924140407000291560740c0030705021040c108138511580c40f046c025203001d0310b180c400d0044e100300d00c0c0b0382d101c0c5440c00303003051180b00d440c07140351030000c20b100c00010610613000030040c0313990b886000c040b0117901c03040a50204000b401203d0030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 572520764 1250 572519514 572519567
    0x80a0f0c08150a0503030c010f050c0705070b07030909020301120c0b03221704081e010c0e10180b0714073f0c06081503060a0c020708070906031e020901030201 70
    0x2420001ba00c5010080c0c7e0000c00c0d110900b0860310305440d406404550070314014019580003e4000c03c42d282615000d544554554141e41411079240c500c0e0790003108120710001c00400c41009c6620b0110417079020b494812003403903032002c003580349100c12540320403510f4041141e1003030345102d0943d1100c2240541e000b88000c902040b200801da070b003c1d51010506500110003990100e404580d60721880320004020803a0001480e4040c00088010198a104608031113402008038000c22042d260000004015205aa1035481060702a40040c8044d500e5081d000740100384030000080311810b43c1c4050040600e00c0b07040c500305a41c00c032090301c241100103c105000030600124203200701d8545000b4800c00145911700000a0050324014000740800128200c1c1d4030002d4600040003078100c404da810009441d004040101d06000641e0001081402103e00c00584201c19401c4441038a006042d04505000c1003003101c01c003012481c10007900040d20360010400f541c0160311441c485120700450840d0341e0b6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 572522014 1250 572520764 572520769
    0x120303020903010c051b0d05070b040204020d0c11010e0102040b0f0f070614010e0c0306010c1b051c0605090703210c21080105220513050607080a0f0c08150a05 70
    0x864003210036001170b20100b96900c1e02e2001b400c881e810b9100d014080c104003100c41c00010306c0c5119122014090955603000f050031501e55904442642840700c108200384040c80000902d61450643c0b00c860640c01c03c036060321700c40810310840d801c0b2003e000d00707180360051040290f05c4035000002c2c035401e060000d00030100480c1160040341101030f004031115000b50b06041c844403042c0006012804100c0c014410005641d07003001d1025011500321030403505050903851a026400b1700c030b81009030400c0042e00d032900c2c400d0341415206d94079441100c0c00c0c0910b5503280c011540d1684c2c144800713841a5940070b10a22580c20721010810300e26200c2c500b14009205588400d01c2e24400d80c8d82c0702c1840c940c50001222500d5119034124054101102d104448c070f86041041c450b81911000f8286d0901c0e07443d000300c0c581002c40301c0050501580722041d200d0a141810340a001c85a040351594140c0342000702069039500303140305584480a2507160a010760700d9009440c0c0141038121001600403c0e041c4011955a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 572523264 1250 572522014 572522021
    0x51e040f0c0b031303090b040b1c0f09030309020f0405040c09020d021207020a12020303070c061109120a060612081804090203010f0606030f0b0609090703270318030c12030302090301 80
    0x30540003101500c4c2001390300c1c00912510403139000310f010010030b2009001c3d0451140841c1c05550007034400d0900e55200d4200000100320883c00100c509242120341020190103401801c4010b00854802c220200400309020a44104550040001d2811917061217031300815805040040701110005040c0111008a40e401c69000d40d40319000d03034003003036040081000c1050182e0418080344090740c20f6091014018000319a0500024402503e80c00043e2102d20501c0030b5804c11140180f00b054a000d0818110ba11100301d01e0083d1540c40c1002404145105000d001451240e0301401c0d041c0f42c484001103641c2186c142e01c2c0301a9001d52210540d0015940c24000c0f00c401c5c0d40c0101c000141649482c4d000f80c03c40b11400d002e0355041d814217001810990b41d030015215500f000b5a5401402d94039030404030020800000e145100207041a2602a00c844807804203a00038800d0700c81442038000000c81e04101d02e404d00c00100f9a0402c42c5040c0035002050804551052183c1000350420b035050f0002803c0d03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 572524514 1250 572523264 572523271
    0x11d1807060801080105070f02120c0309101e1b020f0d0b0c03090f010b0604030f02011709060103020a14030d03110c0109050615120c010503071b0501090204051e040f0c0b03 76
    0x40e1155005010b0684284103103500f01f1200d05125828411100c800303506d400070045c507082c084002041c2000400c205200701d80d040740e802010400351911891018101ca45542d0042200100b50904c03c80014001c5040300341c100d0505003c603400b5076540d0708011804051440c11500060440700c1c80300065410042c0341d020381103001a6503202d18041d0345617403512040399a815040e80c1000c1032038a0513210702c004c070780a50b0b400407150300c0741c1d40f01400141d524000220301110071640007c03c000030000c0120b030140c162842100c880c03010300d6807291070b108003285403600b2035455009407181d00301a0340a030340580300700d0011002c1c41d810038074424840d0303003128000b200a0741c09411080401c0091215502240c0c5003444c12a418582c0e681c405070b2150f87c0e8100c0010860600c40b0000c08504c929001e0a81c14021303030045940d0140e1500c1c20302c0c00300d000e0704170800c003207015a080c03501058003101645658541c0621154480d012a503d58542d001080c01801c416608146400d001180450130302c00103510 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 572525764 1250 572524514 572524517
    0x31106030a060b030f162a050115060903110907050d050a0b100c0506070503040c060e01050702100c050105061c0209040204020909070c1104020a080609190509150f011d180706 77
    0xb450b14580400003d4901c04a0804000000d003002100c0032421f41600200c6c10b01040c1400380800919281c0e00411504030f58265445201e8400109181e000a00d01c2c1078a20410403162218089001e20100b200c06603242408642d00340310362a21025250703c442d60262050030b002c20108a000c01007400030ba080b60120000503802042071007804010407609030410b0f850b00d001499803400b52107468198840c1c0c05004200306103101c181c0e0044e8421800d40b17001c503400400324030102a00c510040c0c02043c2e50796040343d165080c1800618640750421030f070140c01610b405240010021a8204503d111000340300326031041d070038009ca44130f544482181074804c3d2419204c0d07044510b03017420810409540c1c1c80c030b694442c5004011a0a4031503000f1402c1d80c00c5802560b00803001e40360000c00302030a040d0810000021403801081182803000060303080d0408021091002650710b840710241002c0d03000340603110011440043c0701c901c03e44000d1031541e04c070001e6640b40402881c400c030141d08040d410341c0402e0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 572527014 1250 572525764 572525791
    0x10609290a090515040501050a03020907180806070f0e04060311040e0a0f2f0f0f0d0f03020d0f022b050708030a05070f020604050a120314160207050a031106030a060b03 74
    0x405041500c6410302410742280c276800c1c540d1956002031600580149100c1c1040403a014008130381b0000084500540440c2065922510f8940801000405400340c001e00040e030506503810b160420744a2a0103803a00207612801c480315031400d02000e800c414511245500c10800c42d000442c04200780d41001c24401c00c0034442e008c01c80da0300362940707070718000302d40c1e04441c905a05442c40c2c2c0c1da115070484102d20f0035690030043c845110001030300d40503401406000e95210300d555000701a400320300c51000c94240c0d100e40380810000c400032643c8143c8001000410144542e40701c0c071b03c1c41c1c031500b030140c500c003140381c0145441e085540d114100d401c2a038006601076150802d01040c1c542040180e4010f0403540b0051080d40780a03104c50b6540c421a501c0078040341c0940d080700b20800e110b6084071071038427040c491800c00c80c24000558200c601a40359014014000c0c02004505468034402400440b9041481680c40c2401b8400f0803000d03600c041c202c0402155542c9000031003c00c00320256200c1c1a003807810b0f4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 572528264 1250 572527014 572527051
    0x406020609150f100801090303050a050c0f03010e0c041505040501090b030c090d140d080f0a0e07180f050103050102130b0c2107020a08030705010609290a0905 70
    0x2928103040a07200044940010800c8a40386400390b200b590700c03281200c002041600c400344110035203d440d400c040d005508200c9900245505608098050b180b050006c100c0c40d910740c92084294006e41d149101001e07800c0004203c00f1428909a58200903120f41c29482c0c00e903903000c450612030420680351f01040d00803a00300525038112003007d0040420741110f602c0c500d81030081810502c11007008501c40c1520400362018011103007d01d95a045030031303080320314090f8220030181400c0e208481c0300340350f00280f00000e01406c40b54043c4103a111075000007009030300e045c0300304035403406034113160154660742e44c0340030755600416400f48500850040000603503c1000000c0b01c0d16800709604160f0350500f00300801e038000400081d106101a061522000702d001401e520060075101d0a840694041001400070030038503004001818594441d4008010b030564079a04c1c001601d45408102c02e0000315804101401c05242805070702203000244502d40c01350700c441000e022213030140c4040d40243c8141085 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 572529514 1250 572528264 572528267
    0x5160627110103090305040306020c010621020909030909010312020f061905100e01090b060409020a030501060f090e0609040201022b020c0405100501030b0a0f0b07060c0c15020a090801020c030406 86
    0x101c2260083c030f414000180303592000f403c42e00c600c2c130000b0040f40d40042d000314825401c0d0b1008004d00314401140c0c02c40c600d000a124501d00845100780d2180001401060700228000221581c040015103240703840d0b0302c4c5450311407030301c008060050158060841c1d480d41c03801043c0306291054034a10300824521560139000011a08010701100911450680502101001e02401070445a8000c00030405c011000049000c074000c648c40340958a001240a02c090f94250300f02c507041c0c889940d034039107941d01c1c520811141848184901c40c1182c41220100d00e0a090540d9041d62003030040c0101c42880e0440d407032441364440c5034100e6190644602c0c00790200c040d8103001c610030361901141d0901640c2048904a2080103023071103450f05040d9692941800d40e140c0341c120b08001c1130b00203c03004106039220540809070744149400c846017850b08203034036443c0380100b200c020307420381104090b40112584440c0400a6021100482c00d100c00c0090001d0010303024002004100622006951070720306d010700 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 572530764 1250 572529514 572529533
    0x1215060f08070c060b0303090a080c090f0c07061a0603070c030e03071809050c1203130902030c09010806040e01060807030b1006050a0302090f06040306050907080d05160627 76
    0x240c5000c10a00350309021045920801d05255a600f103000010811000340c0002e196210300d118894104144540000d2107120224184041000c1611050640c0d55011b001040d03034501240c10744047c1c0b80030700200000c190340f9031020703022010203480e151012070107000040c0e41390012212200095039803141d820405622402001c80e12105a009020b40350800e580ca5807081c0d158810590c0c455601c81021091003c1042510310b4164050026446480d04004480e181d501110745a114a000408000b600b0f0441c0d00c01c903489922843d180d603062a030300344011581c503000503020b41c0d40a40c85101c0080c1015007845407600400c0000c00400c85c0d2451454800a0920300500c000d1280d128084100301c0c1c4c2d50440111422800702e480c0c0144d0311507590001415103142001b100c2d409c1200800d0100030400d00e50700543c01400d40c142240d9900e03039a4111103076160740445e0300400141c814005c40d5030207070713240d076100c0301091180340007044031012842c8442035408040485140f8280610340001070088040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 572532014 1250 572530764 572530787
    0x60708030a0b0103231308070308010f05032a0406090c050c1207030f05070305070b0117100905120c0723091f0b030718180c03060e010e0403121506 65
    0x2010701c45403100c6044084130002c00350f09017021080460010fa106810b01040c1000140d2104c2c080f41c81e142c0360b06008003000d07024007072680140c3c031100c0c01042034640062a03010402c44039803003140400081820244104103180800c0d08141c03a840003058410341c6000e4900070300f4072607860387d40b03d0707000c0307007800d0f2401c480c08924000c6558100301400100f0350142440504d00354a00301590780c0c0d0403070f02d01158107110305c3c0c0025000169000000c945d44824440e83c0d031100f58150103d84520003081382c050216040500300400790350010070094807004c1d51102070442180b03844250350000d0790355140c140c0340308200d400600032600610802541c52510710141604900d00c0091070400c9030704154030319407421803030080d1144407501200150100d40f1440003000c8010410b01c44061003552a4100c502d030700c1c0c0080502d84c03110705041d40d07102030900c00d1090100301c0d103140322052116440c000803508410300160068082050305c803901c0019000901480310580200b0075190450751070307c40001d00b00f86402 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 572533264 1250 572532014 572532017
    0x3070905161d010c03020a080706090b09030c0c1513090204092a0305131a010501021b0a030602090409050316050c100206060f01021c0302030a0e0c0d03080606040302060708030a0b01 80
    0x2c0e5480080349500003103500c1e200c020b09211010000c130341070591914002410040c200b140000d841020400c241c0c0009840510440d0160341903100c120030903071280210301c000742e42c952010141c42c0c21807134040040703002031440203001882d0283c440c161220b80501c5030048941c0039000601000055541d1040394850034003030841ca0110b02004c0b08084041c01005102c50800d07480303102080001c41140b400c60895030380200f95070209200c80d600415200401d1084a015004100c130100c1e020001d9440d000c52501c00074807c230480790079542c848d0b009411141d0400e80086d03654078803400240f4100300409410044c43e01d204100501c500d0724626062128203010f0041c080310855200c0190001620b6402240c00c440e02980d103000700004034a017160040840c14000c0c200c2a4029504e50942d004500034036215105101c149114500c0c1039035010150540c0b504004011417020100740308001c02c2d03400000c010511480c0c150303a41c00040c119040317280180c84400380001448555503481c0f01d00351018900b03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 572534514 1250 572533264 572533277
    0x61e0f05031c180311040b03060720010e03032701060f120203010e060c0a09080a1a15100e042003150301140a1401062d02010b0307090516 61
    0xd02000c80c0c1c0307030a40c003000742150300700c019406881c480c040c0f207079800c0400008049101007981c90500e0b2003c45002c0c00c90074021841c103040341400741004035449104859981303400d44400201540b0f40ca2000b004004502d4a5603202d4040701c0141d800e000860052a00303800b0201c551080180710040d0598202000c40242e00d00702c01002100140243e000071a0040c0420780e0b1311808600110b40034210b00c0203050320714000c1c003040158000428003d020001d159548142500b0f840d41c045598881c552070002c2c0042da00910b015031039a646002460788000b1858030400a04e240d880407a1500c0031196014001c1748542c00410781030f00707291040d0310a07501001c0404c6038042e0074040d005400d200181400c80c0c0c42c031580444800544094108251147c0307076840c404110315180030424018404201441c014400c81c40000400d64802c0505c3c2004190f0321009001800b03071040300705417411a0380c600c241175540725028162933540c280507007002861080804039040c80c01c803001c0107950515544030800c0c0031070b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 572535764 1250 572534514 572534519
    0x604050a0318080d030b040f0903020313120c140a030606030f0308150d03050c010603150204090506060a0e040f0902030f012a0507080a0201090b090f0c0906180402060c01061e0f 78
    0x141c08a13024659040015420403050040340291102c209110845418541c541d4105540040248601c8004501c0b0010341904e6410031f1401000b00d01d000307462650b11050501c0308803032859035084002c20041820950301d50320b0b51843c0a6034407135407041d00d219103885a40c00905421004042d400b5150301d000800d848864030006084100100b0050200840483e207034440050035400040510341104100b0156032642402201030740c880d00600c4440c500b480080b5a1500300501919200310907030b00e420500082e600c00b070000030b2605002200c40161500c9454002d0386040c01313240e080b01c010000200d0b00100030b800380b1402c026480300003a0140c040f5070718186a190710009890415501c505403035514070750100100c0c007411054401400b5040b1748e1041c08948030000910a4002c1e00c0f05059403c10200c2d413080103001c9804883d030070780245849021100b0600c000e2403031540284024240c60809100305c6040b4219400d0341c00400c00300800318600d00b084540780004400400d4400c1000d00000d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 572537014 1250 572535764 572535779
    0x80106021c05040f090501090609050606032a120405010518030f210718050f01080114150a0f020609030918071b1217040b1303020c030604050a0318 65
    0x2845a04000480c04110460306500e8824403c0b64018190408030701e6100f40c0351000007004100038803550a14074549080001c0500240c0255441000001e100c0d0307056903944241d65110091030141079450503000e541c46400c0708000806445c800c002040b0f00542ca103440c2c64090f08440005d0070010b21041c68803982c5a010000208039015040000401d603103c1602c00503050003102030154141801d20078104002445600c0b900180740903500c8107041d1026075031801403222403010055468006207441005001c05800c00300020f00b040d6000e004807200ca000c0180d1910300b500124a81000504d8408900c62202e904000c0d0a40200c03041c030145140121020001e14103200b080b6a000682c000307107002420a41c0180c6c0301200c8040c4042c042c54228081d4a07203100010440d8101c00082940c3c0821b90b02205903031658148142d0b8050810601a102c071156100c0c030102d02c03d821011480b851300c4101d03040d1024007000e80030700d10480013401c00c848240703000b81c14020544102410341124403010030410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 572538264 1250 572537014 572537023
    0x709050a18020a0b3603070e061f3e0f0606010c1a040f0b010b0a09050f1504090911090403051e070b040c14042318120a020d08010602 59
    0x940314615010350710241241001c031703400714a8200800c401c9480b80d454035140d00d0420500307a400401c40a803514547c85a040c0300702680b003501c2c4190030800d07a01c549a16039882c040302e1007425615003401100c0c4100002e4104007442000445030506400a20074804550304100c0c29020340003080c040c1113290311162905566034001440341d0b04002a8940900034044c40c296906603440d0b6816483c0f9507440c02d03007050f10390419120700450b030340c40380e0300000140700038914141c1d24241c00941c0e9414070607180a040095040410302c469901100c001c83c10411003440c5001000103101500e03012900c0581424890101303001046800c0c09015503004100010b5800001c8400d8802104486848002200b9a02446001e011001041c00814100340b0041c4081410759500311142c10300c0c2950015070260034001640c2d81c2c0c0c2c0c038880381d0340304448c001213241e152540c03070541c0050700750701d0080d1030701301103007036528020821309090013010300041d81614290781441a0116621242881c0105502d4810005e41e03c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 572539514 1250 572538264 572538269
    0x12120e1b060708030c03130c090c02101a0909191401050106020718050a0204180e0c01021c0e1207031406010605091c050f0318130e1c02010b030709050a18020a 70
    0xb0004000341d8410388085c607c0f88459042440c07072829070303156490700c0010202604003001520403100300c400070500600a00c15110355003070f1a824400254824065007441c00381140c0c1c03840c09072000080c400074981c011011203a000d03880111050a04014050858134185c01020464101d03204c244401455001110303002240000c00242c640e175200e441300000c1c0a00d8000300b000c1d501c00905d00a42110641000d05070310040001e507800e682003a4016030395840752080c031000411860010b0f021641c05040702640380762000e4912015600051111400c1c850103410417a5018030900546540c41c0041003001e014040c0d5044c40307858a2040b500240701000e0b1805007245410b004502351003000020700481d0507071440c0d50200c94481148120f5012601c06160480740a900450440000049140642c906510742d65015080350359150040454500180c51110f00f550348500f000155510f0800240c4020010614000f034182054440708054a20500c41d182c0b500000c0c031003a10251760740410300c404 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 572540764 1250 572539514 572539531
    0x110705030307032016051819240602060702060a050603150606070c0306050105120c0f090403140a03020414030d02060a020306180a06051503040f12120e1b06070803 72
    0x1207005820580e8008400c82c211341c075418002c0201040d01c045221144006507841100c05404a5800c3e071648071007120206c401d000b0043c801d1444140aa52139400703a0303c411802c140700c0c0c0200c10740405400500141c0c3c0e2152005030700123410400032036410310000b500580e414009116130300306880025074894120b900300003a00c0310f43e0081050395855600301c844081d070241000424582e44d0400e8002401d0901c45d003800740384190010039281c0000300f005d0031704140080c0340400305c0c00c0c107405004031808011300071003e101500da8800c19030694240600700503c5940d9001d42d4550030001d80c4401044945e03803440c0a035010300390380384003176801154040c2d1061f5100030060f16661000000b40c2000481c0d402c54440200c01c1e820300040760f14a070022003d840d001d40d0814906040c8601041c410300c42160042d0081c1c07055551180080d4a81c403000c1d45551040c5411300c032029030700100004032601c4290050b1940e01048505140d0300350504884020102196503030f040c3320480d16240c0140c8401400d580 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 572542014 1250 572540764 572540777
    0x30203090f1b10140946050a030f08070305040b070818091e07020c1207050406140d06050a09020a08010b1011070b0f070b070206040b0c030705181810030311070503030703 75
    0xa14510944403200704a01920401000480e203403030320b1036506d1110441e9004401600c010104050510000d000126a0700c80d0032600801e40c0c2d030f141c030441070308052000c80030801c0400001410782504800340c07003094044c0900326a00e600c100c80503a00501e0640d440b5009145403803c0050b040340c400400e4508a0383d610740c4441662b01c411040f41000008203489911100c6c442940c0d030328801c001903241c15150300f07841c00c00c01151a40000c03000490142c1c401039100a072040c0400028200790410760b006110071030007241259607540050440343d0f0682296080ba95030b20040282d91514449070404110b25040c500101300800b101c20362141301900a4034980c2d940041c280323072035020680880d0816900310701d0701001d0b400e2190000f5126442030314150789201100002c9115404c4a90489010fa80d840e05d401c1e20303002032134080c44c1d4180e10110129034010074140300c218001004039081c5115540003800b804c005401e40c0740280c0044005405000141d12001c0240410b803400400c817030050fa050f0038001d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 572543264 1250 572542014 572542039
    0x60320030106051207030302010630030903020d06020d0525031e0c0f0206070f0509040f0f060306230103020907110f100207020a09090b0601030203090f1b101409 71
    0xa0142c03201d03600c09504143e8040300c94001000c00302e614000e81e4804d42c0280300556841c915128071072604210f0700e403103006401201d00010b0244070b4880d03030309100742010341c281c555a80002d942103a00d9541560480c0c0c001440600f150550b200b0039074000900306c00c00c0b41240d50002d8a0348100c2000c0310a1301451780e2852030b005038409045140c3d6142c400e940c028404c110114000074800110581d03008094820900400d0480e4061040905595096510303a418803c21104102c003800c42561200441a55441c0030740c0101035034060040650b02405006c0344000d51000d003000840d4000780141a1108080300500042c0c2d24102c0790340e040580d0b440c01c05071106804800c2030902000810311202071182e00d4003443c802140d9001b4102541c001c88088d20310a0b41d0711116400c1e40c246100041080201d103000980e00d40c0039501035500440030100700d07150000d00c1803501c1c1c80d0000040300f0364046c43e102a102d01c4286000800e11003100042e140104420709500c180c0400390040d494501e2040f010030424 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 572544514 1250 572543264 572543269
    0xf04060b0616050a0203060702060405030d0c050903010c031415181e130309090203090d0305090705040603031d030c100c021c03110106080f1902060c0109140709060320 74
    0x2076409140d6100b07007060303015050b4070b0700b15a205070307609040340079011b0f490008500e07500111304a4400d94001c4050f520b01409500c4450007022030030322140611905201d12142c5440034410038079506003607100040c5e4041201c5045542c00802441a030380c00e094540824220f45802c0007410366031200018103a4a51a003004032009000a25054100854100100062a404403040f19100b41c003988034640155180c2c11541d083c1c5c841215400302940c4400c0c4015100780c404c5d0300156110001d030080d50042c80d25440001e040d03590f00d910690024929a0300e403114032548070210003a11808030000d20a40c00b503034021907004010364002800740428110241e0540d2280032005c01e04281000c07401400d0f04041c0f801078404014103100c0000c43d841c10b0404900b4031800244071205084020090442c2c8414510460280740300d204101d0f0400f00c280000307019003909004010525100e842c2100d02120314040040c45c1100c01d51005a516080007000c20100e0814071201108041800d102c18003000200003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 572545764 1250 572544514 572544517
    0x150d0c0306020c06010906081b1c02030607021005062e0507020303030f18010b030c0616060e0715090308030601080c1204080d06081b061b0111070b010b030f04060b06 73
    0xc003519403030002801c80102600412030a0513034480e1042084025202c144095641c80d54881d428901d0317100c4410f0340d0f2549016980701c401030003400524032250007907a010909021081d80c1c204056070042d00c1c403200307800b850301039a40d212400340c50781c02c804c1b05044002001e4075501100c00e1600c00f40c41c2c002d5500d05110b1b00c00c85220315006400c4983c0c80c140303240041c103c14804c4032040c0d00120900550541c02d1018000c4654455004000300b404c0d100010030024194010500c440448020390140c0000408500a2141010410000e02410ba1030b0044055010480d0680c100070407500b00c4091000a840d0000d42e60071450030728100d08541d4804031300f074070341d8031404186100a0341c0300401c00c03040041860040841040034407060000c50340e0382c440036a690303800b1902c1020041030340d010742d07455040c548082c1411014043c80c460b0702d625031607111800c440d0311480025a2074800602c0d42d003442040c603501401090800c01c0321385107107030200c9119080000984014446d5460b1013801001d0fa54540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 572547014 1250 572545764 572545769
    0xe060f041a03121905031906062c0f01140d0609050106020f0f12070f050a050a030311040e0118090218071404060c061122030210090e0f0a150e1e150d0c 67
    0x80c1f0402807161903100282851442041e0100344600d000e10307140e01040765405402110201410503107091608034015982c1201c032440129400e00d09021143c0400005d0190000600750721034001059410248000c0c1020400200b08690383c0c800e69000e03195140004e40195240b012201c031544480407481d29a5013891074490250491046914000c144a00480c4048443d446a00c04020811400c000c15000f1b008601c100641c5174200783c0100a01c00b803c10307898820002c9544c0c00150320b4550f41c00107850303410040d03c18000300054400c016465410010715000d00c080c100845042c6442c00e840184485103e01c0000e000a0300c460b0007520180c44d03030040e1800c800340c03a403c0400400c601500b401050710980300a900c54a1401c098980365030041c3c0c1c00005030b446020311a440d40e5148007030303252080c4003e880410038951b506030344014460a4030401010700000e82d009003403401c00f6208050404128805940d03880004418024890013600b08140125030680b001900303c8120309080a841120f0ba = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 572548264 1250 572547014 572547061
    0x60301140d170a09080d020a0303090606150f02010509010b09011202030f0f0a05071706010308280c1101020d08071815090f080a03090e060f041a0312190503 69
    0xc04007407402e1604015041c100219a540e180341507840502698403c101171103030b000b513080380000340c001c03903c69041801018000e0b20007007146540c2e04d000814000e20480e00e040001c0100660f5090f455082c05907580084019009003c60494100010300840040c0324a40f8101070080500c4119181840b02d4010b00340a402900c0102070090f400c0313a295841050308450901800c3c50200d080c1c1c500d081c200030791152020042407583c0c25591a0701c0386a11030b0800030051322000b104030b5030900d072100c01488418400d41d10340c070080600c1d00c0e041d641d040803c488076040d03420501050510b15031219072035a1004040c603088400b08075241c0f900c00888a0341d004000381450860740b285a80340c01c1641e0703404a4500f10004080d06542d03207030450301d4119164000b400102c030000c0c10800c0c128500304c56504603200a0585403071600e05000a02169410b04601c0b242d06420311900703620f45030130f10030310340075100c0c081c920703850060080c0c40b00b4150000b10100300c090020100c08101c400c07000b60202c01004210 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 572549514 1250 572548264 572548283
    0x7120b0a0801060f0b0c120a0207090203101a07032705090103140d08010608041101030605090a0506030c0406051f0311030c03010e07030207150b0402160c050f0402030402060301140d 80
    0x8418a0364040c2c44140110f5203010044c003000109101160704480c4503400b8007000d08020709050007034199a502c0a0305007011445280340c045401c40661000714091b014454807580341a2070000451051501d034070106a40e844244440c40109401c06008000b150400440c03440511060108540000881e000795030004e008030008002c1103441e00711905c0c02e801d084100c542a07401d92400321a181c1c07003400707082d0018110340040350000d128a600011411014100441c1c025141c0011500d803100c101c1d0340300e0601d0703101c04c24084541418400320196040a403018808581490089a5200200821491601520002800c1d0755100358018903114880400720791352420041b40072041c42e0803e015440e50000c2c0b450114602901071301c00c45d0051396016050303003001d01480d01c0c0d40004145007000c041d0010780030003c0904140000304111111449600d05428050422080c00114034051603014060751041042c04056900c4805807811030304590041d0400e0300350346003c90803c03002034a000704201503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 572550764 1250 572549514 572549519
    0x60402251b08060609061207060806130c0c1703010f061b06091506080d090603020a230a0e04050103020a0b030411090a0207061b140f0f0a02060609180607120b0a 71
    0x2000c201a4050030089071283c00649401c130420003a1380e41f4200c0c09000f503103c44802c00100740070360301242d481200203048250703201041005509039800c0702d103000300049800820104006058800d92002d000c140600e90540d810f00304000c0c2c2860643c0100d10034404200310b0004c0220300d943e00011b62a9102e0018000307003a4500d081c800e000707000034680000700d00341132021607140340c00950710314201c130941e0311070301110314011040e4003c0d8043c440450030401100841c89109020142102d138540d40b0b098803691b904a000e000030865103c9041807446103007000010001743c0d41cbc1c20059000d9070340e49a10140d0342e07111440c02110100c0035540e89504054a80104000f000c100c2d40605040c60141c1403e0000300c0c8201e15071074920341c00c00034820102d03080402d02c2c030351360410310040c02c581600c1250715440e12141c1d240486460b04802c0c0d8040040c1c4c014000c010342e42c24582c010940040d050759240820a8005541c0c0707032502e0000f4221020400581c0046005a086410034014004040e2454a6258 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 572552014 1250 572550764 572550779
    0xe1f05130b120102090a21060606020709111305040c17070801030b060603040209070305060a0b0304050d030e2103060604031b08070b0901020316080715050708060402251b 75
    0x824440e49922403002c1d15814820503a041c003c59203040c00007003008841a0514120780c102103118400c480820281c034100c6000030b0640d02c51400503048d25001020418507092180d029a0000107683d803190106100204000c0014004503003519000c1758045010192250308440f803a40840300000f03000304a6050042580d00b100d0343c035060b00e010f054000c1040e910340781401410b00c01540c009401406140008000611a40c852604040c009080c100e045994640ca02400e07007007540c3c1604c840e000308104410340354251058201280030034000d403040e0030640c0602c49400321120100102a040080011001d9075034404940184d6405403080701e0b000d00c00481801c4100d03003030040f0460f51061a90125014203540b041da04030400581c01585012451026101c445c240128202d90700170b000e0184000240b1948940b030030000107610001403038034200200070140500503020382e0003644100308541000d110350300c1050300121030b15070080d03c02d013851801c3c0c0c2e00080c003104e0b0030341031154217400410b280 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 572553264 1250 572552014 572552021
    0x1707051603051b090a0b040e030a030212010f080a0602130e0a0e0106080610050f040e0d0807030b0d21090801060b0d0f0203010b030f34020f070e1f0513 67
    0x80c0c0c0103004581050f01d2a040300560102d41c0085070b1351000b00d00c0001458120303903401400c40c800000d0320100b003809041d4016450364009803101c001098002c204400d56602454100b0b004204180100941e01d03e80b80d240da8803041100303009402590005682034410760b14010102c0108601c149018032440c05403006401004400d002400e030354204000000c210340300007409030040c2c401e0101e1407001c603c0c2a003040550141c0c400e08542081c4c41d1100d8029403641804503006400c90794480c0d44652420420040403150880e1310244154003100c480c0300401c0948600500544064003421444014504140c41c000c40c070341d101e43c41d1507080076070125500700920090080081c548205012110024038407500b0b0340024001c100912000340000f0340c07016080c102c0b154200c815280c14141c10a0385031064a0025598044412000c00d001c002080d00781e4100b00a1010314084405080c40c1420406000100c100103020944400032900340d0000064041e00c1e41001000010b1200c10038047d1b15056070060b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 572554514 1250 572553264 572553269
    0x1110a0b010f05101e1d041503021008010303140a1b151103010b0702010c0804090e07061101090f0605091009050d081003050703240c020105180d0c17070516 69
    0x501d000c111201c0c20913000380300c0d5448904804454004211790604e0803150b08907183c5050120304001603142d80246c5451203050046240c088a071034103030b0300794014001d080030300c00120400c10441800402c0440c2d4450340b606100302c1d0b400c9980390381b0718001808a403540d0f482407203d41400e51058400c4100300300c0b6002ca40385100e20b01010300c82462201c062543c1030000748192950000104100401580301da0710000d030b020322502d43c25007041d803a800c1c2c51040750f500c82d4500c44079a201d03000900c15660400e9291108400d408002e0000604503a284010031207056001080f09464a000c42c0c0070000a000c0005141444401001200381c03d0606d00c0d5201e000c0e0b817910003c92114004900344454041c80c08041e250007600424807946913640f820011754002c036100c035015a02c0a20802c07244224003401007031880b80d0b400810b09042c018038240701803c3c1d01045000c0c0e9030001c0c0c000304000350002070400340350743c0046110301c80d458490b00300d1034180300d5484001c1c19800740d0b000c60303005660008dc1c40ca05 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 572555764 1250 572554514 572554519
    0x19020a0f0806040b03121b1b0a12030e0d060e0f030d05130206071103070b0c010905011d0c04020c0109050a0f15020307050f0d09050709060302180609040201110a0b010f05 75
    0x105450342c40a0000b11090441d4407500350700403c0d41c600001c4520402464446480c0940081d8010420320355410b02c16050004080d040004890301642c0c41c190852101500c8004440f019000b2540d1780541410315a85030a805010104400024407000c3e6111101c025407000c00e81c3c01d803d411048042c1c032640100c3d554040c99141c8400300b198a01c0503012820a0703540604031500c1d1a00700c1e1175441500010440c583c0c1e02d841902c0c0c0105405d000c0001515400300307100004109840d140c42c0440c03d4400000c10944401d201121110100c0d83c00102c5a01d1510240c40059a52205011507400340c41c00e050040c0180c403642102404008059040c101030300d002c1c03142c00c0040740c1e035841e03050700381d100540d2900d00085090024101c50f031403080050140c03902d41a000100062980e81d1581014019401141c0b141e56842042081d4201080080c1c2a07800321f0480701d04a1411000040982c540644041d0400c0808052124030b001d0400001d04507503001507900d00290f071b580c41040003040300303801a80e0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 572557014 1250 572555764 572555777
    0x201050609061903022107150512100b1b101509020705100213030203100b10030507120504080406110a050307111504140f1e06130e011503060522020319020a0f 70
    0x501c421248d030b00c12000c00481e61000e24124a8901c00c2c07070700e481d0152a0300174155205800040c04400030380100070080d105c0e01c1c4c400d15070004080321802d0242d40d61650030004e0400c00801510712107411143c069442c1000010303251902d40c1402440c11807040d042d074080610004440020480c40307050030080343d1084040342c03040458407000f2030a4440c410400ca41045000c480030441034040d4000690020300ca280030030b00d130000401c0c81402d9441c1501e0965150381c0c001030900a40d82d01a00b04d002c0c0680c0c803402400e0958480d615180d481c42441c10280900e140600e840b13245650f0842100c5a041ca410320460301e1387e1301c0b040301803101041c074507100e80301b0b104602602001d420b0002d0240c0c408a24101e10300901524401400301c50f41c8040a04101c0100c0c1c2040801e2842404c03580d44c1c0030f044c60503840041c6080042e00601110719035085544204100c1b14034080204083c03c00d20000c2c0d44c3c400c4056201d464241e512100940310100b02c1500a0000c5604044240c0c40002005520500e940300f6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 572558264 1250 572557014 572557019
    0x703020f0312040b030c120a0e120705071503200a03140127020f04060e2403071b020d030206151906030b0d020405010e0a05070201050609061903022107 67
    0x55603482041041c80b2845010700082010348103120146a101103000e102500d040500c822000310154200e1706075215640ea010829440d80080101d528101c002403001444d00d00340e034542d143e07941100c0c40740441407500002c00154443c400d0300409070148400d40403011041c08995012055000320b0051000070b80b81006030401b0160a0b180c0504071421481d070001c5a02c403803003048120a62050140f00d5041d000c1049022040040d0010001040140d9074030f005001c0d84401c01804a00d640311130802c40c91140c1c80580c511a06d2401c03a81c20030302d107041c541140840c0d040141c0c00059420b1001c4c3d80b00318040602404c0c0f54004c103460b4030a460700f550803003013188a04100300341300400755103101000303881c88070500c00540660b01c58800030500074402c1c07102800780c0d0300080036203400760030989000d00414144202040240142504000329000911030307440c0c151f0100301c0a503402881c9900c1466620650408440b1071500034010310340140c01d006c0e09200c02c40448440d8002441c1c20b03542480346c000700 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 572559514 1250 572558264 572558269
    0x50c0307120b1219120206100b0d06050a150207083d1109040b010f05090d0305090a15080f06010c03080403260916050a0e04051603060b10030c0903061d030c0703020f 73
    0xe64841c2e140c0b842d0744181d41d4204808148960485074180d2b0300c40b540c2c0c01022a1681d503000d4500010162411448100406440020f003040701c0c40d8450345142e400401945081141550b04512400f500d25038500c103001d03408031181240a410b0036411240d460401c1e40c84901c1c1e009002409502020b40742805603584074801100d18425404181c00041c8040c400ba030f2261400c00800f0031403500900d89141070100f00c80c00100d0520031a03000343c06019504640342c0364690003d51280d03003e40c03c507001d03001624220001038544000c20000130100210080090109030240e001441c1c03449045c403428100c80a9440c0b00c02400906641c0681ca5124100610341781810316864441503e40c0641100c00e580e180040a04c082c2c0340180080390a4050782006043e8480c034448041c0013507000e0040411070042c90001c0c02014440c08051408042c00e03c0000040e154010b0850340c21030364072030340001d000d04071000310a1071200c4a03901c0303040394000055441d0041c0000540902a40d00840f0384404280390b1104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 572560764 1250 572559514 572559523
    0x3020a0f080f040b090703140601210c0501050a030914060702070909030215040203031905030a050f060f10030f1409070602030406270504110d050c0307120b12191202 73
    0x42d0b004072600500001400101c4030407500d41c0000c1114126100c80e603c03551a40b070a0344001c5400007080d03200d031004101010000c0184c1c0d00464507a00030811030121901c0f1400b508445d030240c81d060050010b25144403610030741c0080040b40e0480c070109108000c000d811034880c0320540d42e44005206030078001c200c801c0140704d54040d083e410780041510060310340e4250454000140280c2e4140000d1000f18408001ca080c1d680b802d00c02541e64035a030345001d039000301c1121400740425a03400380050170400c41d070311182c6000c0b0041008a80d445030346013000904801400c20525403106d1035003861032001d440e43ea01100300340965449800d80d04d0040c0c075054205d950340103500c10030b8005205c483c0407a07500c506800d20500b0810075076445010442d1280c003c01e044e96040a0326004013030000800d5440e62820f4490326800c10211503d061071400c04040042900280c2d10400c0021640c41c1007292041d5180c802c02e41e8115a00c1054680206400303040110462081e01c0903554201d1810301948078a20105 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 572562014 1250 572560764 572560771
    0x90112030e1f0e030a020603070207090c14090112110a0903020f03032109030c0d0c121d0f040207060c030507020f010902010504030b07050d09081818130305120703020a0f08 76
    0x800c81030340b81034103410444154070407082c0c43e9058040c00c1c10754005038031440f009612402190300140307003442c83c100c012401c07140c480005030b04005250300d61040c9045148110b8036848000d02e04008441801004000205021181548000400a02130035015000840700c000c07203000312060500120b8140074141c80740318044010742046203020708001c500142c1668260040b600740100c9041c1035503859900d02c2c101071039000344089001c1400900400480040d200d07011929840c0501140703103004a9411080f040d410364501c03500d04a080b0340303d00e40392941940c01c11900413800380a03000040501400070030081d03c100e4014050807a100000354014040d0304400c590680d40e641c9080d00d540c540000e0080c0c05003c8108020b002c002d017002c204414000c0c0740c03c0c640a9801207070f80d641a5640641d800445481c0d46004103568041d222580031490403156010f100015041c085805914044800348907821b64005140c1d0038100b84024594968082e0555509036183d00301c0c660b10400d81a40c41c580300300d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 572563264 1250 572562014 572562049
    0x3191803080603280b070c08031024021203130606031101260a0203040606091506180807030212030909011e1d15010e060c010213090501080d0804050a02090112030e 72
    0x840344001030303170a00c07405034400c030185800b082401d096580d14100754810764000c0040c810000303041c41a41540c50b0300c9043c0391083c03084031031400114030010351255550404003484400100000b6503242c0707001c21503841e4a40c05402009400d481e8a0081000002c081c075a13030004144c2c41144200d004d00110404000115008401a90f9204c4c03403014040c0d4401041100c010b611904000b420f25114001d0ac904159030300010410107090860041846100f6801008542942441013003106008228002980d406440845007403140d940f41030b2451040b881e800303820812100001441000c000341e4540c864031007043c3e00d81107a907200c1c610440d014030032001300a4840003c000c41c00d0310300c44084241070010706062424104041340300290668004e02011802030b5000140d40d4201c90703a0352408000307400810382c200310707550420218030341e585c450010300414000682c01190600c481046402000e0b50b0003011841c2c59a100d40400f940e42d42074404c21004603030619000031084c50f01000001c10740201 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 572564514 1250 572563264 572563333
    0x28080c060f0328092105040f05280e070201180b01170a0611210408040b03040804050d030302091806011e050c03030a0507020d020c010503191803080603 67
    0x6091402d8507108410030000c402001983c0c01c400c450300c0d02c1c00388240c0b4502901c81c80311462050100fa00c840b00c240c1c1507200c200203080000b03100c04a50003104c48160b4105a4a440c2c0720b4420080744030004c203441d64110f14880c099640040d06140192409109500340e5009001c400c608005110707401d1180c0400904840380d04005029007086480c803040003106010131952002c040b61540403c13196800c00d8000d10050014a1800340c0302101c04420b10b03403a01c10b80d030303405918264407501080c0c0500e00820301031100000220301480342100941e00908002044c1d141811003d18000d4029801044203900441d00c03078040409200c16110000e00c90b550684950951030310020b120116040f4004490003400001e1200c2004203000700017030342c8030b20f040d080b0008042c1001180a8a07154040260004540c41b840c0c1c4101c80c1d9a128050300c2e003003c958070050b4039442c0c0000303080c0040c04101e1103005c4008103040d410024544d0000b1407a000341026011744031801203045003400003030750112107d21048003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 572565764 1250 572564514 572564521
    0x112e090e070804020102102c0616080601020304031b05100302090f012001050a0e010e070305030708090f030a0b0103030801060507031e0c020d0807021512070c0228080c060f03 77
    0x1407250181d003e407051064130020000c00980004603401c0c000e61461409102003580303000c1015546c5000e00ca140e48d0020240d61030880d800944811001d564270041000500218030164002c005450103158005c0f0075601429040b004010003080317030f02c15140b1800c4500e40f1825068002e201316080c4000181000c0d8240d070003140190740ca01802214480e40160703003c0d03524010746080c8952401070b221090046140312079204a242501c1105010b11000d41002100b0400600004226010b6603405503041e5100c45040c2d0001e140700d2030040c0c0c07658050007094050002c200790500c901d41600d100b6107403a812a40c075a8000c0307506000750307400280440d152402001e440c100d4560045004070b0341c0e1804410b180324540c080b03a00605602c0382140c5402000c600c0c1c43c00c61400041c6440703080a004a0b003070401c217240c050484159009000e1509105500640d01c0c255143c05220960054025003844204540c0168100303104145109899103802500c0c04424289081c1d0300300c4154a40c1c0418035800c41d01d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 572567014 1250 572565764 572565767
    0xe0f13030e0918070e04061a0618060909070201020901020f01050c0a080c0d02041203080109110921030f0406140a08041401060f06050d0c09081009112e090e07 70
    0x1000a00b448514071401d8110f1518800c0c100440400340c1a40407080d07a85041c1445c01c44180c07084420741450442c80d40400b0105034944e0415512030a00722880340480031507400c0443d0040c440e900c402a08001d111003000700e12a0150000d0005540c20307803c490b8590405000c00d402c07144184c40035404c44400f08401e0480504c244482c6400851829211345004901c02c0110200d81c01988004250700009102c1d805254000388401d00604003041d003402400194261041d962182c1d030700179842000c0b10080c1d50040a5001c199036010328101d0b0807260380d81080744000545820520805001403281909481c80300d0b000302c1600d140e600c054032481807545480c0d80700d00c40c20300d100507001c40703543da10400000e40c080182e40c128001e11321501c7c0c82d07545034074040c60002516445121581404030040c41004130f44000111110b03a0402d43c0c10000d01d01001d4903000c0b170820948000241c0c42031201c18244150076081c58084601003c0600040004882d540e05035003490755445460f81c041c503a480010b4141c2d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 572568264 1250 572567014 572567029
    0x109020f1303050708060708070e120c15030118090b040f1703011d060d0c0306020d060f1e0e10030f0305070203060403091a0906090f06040e010e0f13030e 68
    0x144400d055905104076420301c664140c019600c1501c481d801440c082103c1c5101b071001c42c1d0401c0043c40d0019652410010190460b40202c0256000b003d40f00c06840441c1020b04c17074142d9410000789020f42c1c140d803054024101c0c0c0c00a0007141c2100700101030354000c1000038031403c211b19500c0002e82c0140c5d655916914650040140141c4283c0d10148807240c1d203103441c0004501038030002d07202c0001c28a02d5690321030705400090003180245014004940407a509a43c103200701ca07030180026a5806103030340f4881c0500060340c46141e1070903c030000856035058042c210603442182200740e030311550b90f84002d1200408199200a850a0180303010300111302e142c407041072107602a0924500c1c0480783d0b404640b51250440e015000500800c0301800507111a081620920304140c60050420701c0240c0010803d00caa0211a172080e0308011450006464581c162802811000b0080788d9940c0d46138501d0100c00707000c590a820b00c22612000030444003507284412406901030380ca40f000b41c0203640511011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 572569514 1250 572568264 572568277
    0x50d0503040305030d020d060906030f0605100b0a1205070206070c060504030c080d0504030305013204060506040303110d051c0c2024070e13090f08210103020108010902 74
    0x140e00040001001190040000f08046103103580010780d203140c901251011a103881e0040004141842c0040002c910406150820707240c0001c8000307a2500ca10448202c0d00034258006400741d4400300b0640004c0d034000ca1a2060000503103c180800c0d0380b680001c030307107031401241c02d80042140f5480d18408108140c0c09282d0061107401c2100b40c0b81c05507102c81c9143e07007011840d201c1c81d03503d4104110815500d8007542d80140801208140514004000d403070070181d07101000c40095442802c1e007405991180c0100b0010007000c0e03c010354494032030400618110354510380f00b000b8820600c00103034241c81481156080c51030442002030103d0010140000781c420240b0080070085580132020750b03014018080701101064200502040c4055404000404012401620700e64070210802c1122600525101c210f4a02110520110703092031495200a11500c030010b40709201d200806000c00000d28000d055441400030700c2281f8034143c02001c82e420340c09001c001d000980c5900100100b2255802910350f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 572570764 1250 572569514 572569523
    0x8092e05070b0a0522030c05010609021b07140d1a070216080601030309030f0206070b151032210f0105030309240403061103010302010f0207060c120c0b0718150207050d 74
    0x100b06408c0e2640350030b5170b1a40d04503000159001075110381031040c0b2180c14000d0b4030f4a101810b64289406c048002c4014900481c90141041c202c00500b0003610b08002603c6d80d4a0754010005410002c0000b955115528038540001c481007201040100c40015030754120380c0d250340d401d0307201811a5900030100100500c02ca80100085c0030000000340204041c40c0300b02c01411505030520301d03040402416105141441c01030040382e08440701d5100021220001010320300b40a0400580d052034450450721502041c50816483d4182400b09864100e54060141d000130b040942c090741c81d0f800301600c0e0321a24109641c403c16020156460880d2840b2640075a01000f04a40c20f065803030703c5090607a2444200c903c0d880c100000144110740e0807501c902c500d000c0701e100422225040100140044540381030141064510040103407015110340080d000b01c030b502441d0311031907041240c406440806001a14030000c103502401144402d284040340811443c0f40d80107100351482d001c1445003120707280030281c6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 572572014 1250 572570764 572570777
    0x3060c080609163e010b0a050108011a0c0f0309040b0a080d03111306020309030607050702030622061b09061409010e0a0306050405072108092e05070b0a052203 70
    0x200a64440c0c583c030305822100c4c50300c0403010700380402a00e08540420356031920860101c80140301907640825060b05446464003174a81001c0ac003241590540148000701010b8810078819598440b008805030041c0001a01d0500c062080d4070208100d00e889402401c1056100005100741203102e0741100c80781d40c2c000d181180c900074403407000706030440c05a001540983d00028880c40c150800304038072a401301c65450f019041c0100b075270000341c4405000c0d082502c20240b0810f419500790444103400380e003c0d4013407410006003074440054441c00d1055110400400c03202d220002e003c2c2e004049010004440303003c0113203446800c500540d8401075800148d42c111060000200010b103442c4142d502450140009100003450700c405c1181c03e4070a41e0292a1078a05c1001c6040090f0581c0180c9403020022980b401c1d4004942212040c0e161214448030300c80003001e0040d009543d084001019040d0040b80840c005a07105c90400c03050782d400340c070044402d43c45098440c40264280300380c601030622a2400b030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 572573264 1250 572572014 572572067
    0x10318150e0c03010203041a07210504030e030f0c1908030c030c12040e040b040f1b060f0509030c190b12060a060e01120f020409020403060c08060916 66
    0x5200400014160126912403000700c020404001040080d10100c000394034510701507440c0d0171010b6a8034003d500c1404104041041d02d0b009000c0340d0200200d00e210303a15495100e181c501c001e000c041d582900072901c4580000d00d58140031a40e04030155600c0c00603c0021141c400340b0480824641c410402c0001c600750224041100f40020081c50300e070100216100c00345601d0007414458404828502e0007410001084a00da4000d1400e9215802c41d50304141941c440c00c100c070910012001c0185800007880061362120051031400b42034441a6450000a480440003a140d520590302129410351280b65075800620b8040120003d05142220110080355112880f024a4000790103294800d0541400c1004500b0042d40e880001d080915203042200e90900c0040d10001000442c02da4007900c40ca852074100b80b543c2c04850041c800352004554490b40c1382408001404803031440740018420401040300c03803909924040c01424a9049903800300d140c1e80069950404c03689031003000b5029010300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 572574514 1250 572573264 572573273
    0x5090612061003060b01050c06150d02030d08010f0b04050609210a03020c011209080324060a050304110301231e01170d110d23030103082214010318 65
    0x10750340991440103034041a00c0c1540f8140f0241d030050045141008024060103a94100014440c0d070481c41014a6080b09040580852143c420058000e90107110b000c4a4204603a44480f0140c121032040848886481e2140c5003550144124400c0356440401801108810f20340003080311091001081c41d48400104c0c44013090078140604019800b6800440003500350307503089080b4021302c4042c2e81c41005101c0e860f40e1a010240005484080c480d004001030070b000180f8042040c5201d100201a03940f01c000906000f44960300458080b03070001c40150700e881082c2014002c1c2010315000384440e40301d0100c503480d0001e0504000303000d81581c6840d42c0c0c61000960709210240c2c003800e0141e075520f11020303420300b001c0d19184030905040c5c10049104030000c00100080352007400d0314510302c1c5c860a080502503016103490040c3c052002000c600000000401c07285800a1070600400c81c17140841c80070011400007018994030415a504510803041c00084d8070079484039510810642403040143d840c0e403113 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 572575764 1250 572574514 572574523
    0x1b0c030d090f03021b10111204080f1c0801050d0c09020f0301030302150403021c120501170d02011b030e031b0102031909020d1b1e0e160905090612 65
    0x141c0d601c070000c00442c4181503040c0401c03d83c01c418000088081d00c540c001085141c44004164801c10009000c200b4022005218954000041791030341512151030307491403a122000c0640c1c540f1144500c0488c0407441c1426030040c041403030162200d203090380c40d040900c00003407090441292600d03410440800c1c00c030324502c040d140740d010402d403c544039815490040d1601c0580400703050044010f2080000103607002030a40e4080e280d00300000d60300d010016040d55800e20444005282c20300341030000c01da10701e424103e10322009000c81200d20194648006034200e5080c4a18200312030401e0329211501070007074110b440f00e5040101101e01e4880c0a200a00742051006140007499400009000640801941034103008042c120208000103803603002440f05504040020000e040341c9111400c0c0a1000030110000c180a507420701c01402544100c091103000c41c0210b44d100c0c50520003003a50350303e540f10391510030101512001140c078284404c10180500040c40d441d4407450600030b48040303042c18070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 572577014 1250 572575764 572575781
    0x306060418090303051f15140c010e07061805040c0c050607022a0607062a020c0a140913020303040f260604050a030305070207121410051b0c030d 64
    0x481c0020300d4030403031400600b034840103800c0142c403900d59043c020440003007202800490700801d0040100c0d0301426000c0e41e010034401c051040034034000c03c02c09401c100641105122003034076826035084588030300c010b990044a0b64a524000c94000109100f1406d00b0742c07101d0244000341c108000042c98640c0c1c0c0900d0004111130b4540103800100121441c030f60754005076904490041d410b407045000d03400c0450001d00810b4409002c00752660b207240c007480e8900041c814101c1c080034203107202d2464100b000e99501c201d00090350260044501c00901c0c000d072102c0f0764503581c00003851074080780c5840b0101402d5201c03c0e4001e99250004100c006003d0b017419000400402c002150301d080310315004a10f0b15200454903212a032134100404100009a0102c2d1003468190700d03090000b07490b2a4038030704a02e40326154009084990b02020a44107002c0d80070031580c410020101110a1141c00410718401d840c02600c020821140f11150074880c000c1c2d8070701805080413104202c0781041d0700f4401d0202501c0303285 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 572578264 1250 572577014 572577059
    0x70804030614090d0e01080a0e0f0a1a06090708070908010203010f080f0a03052b18050c3309030106090e25090203090102070615060f020703050a030503060604 70
    0x80b0340c615082c2510301803255120000002030058048501006001c4520504040c0d0400001c54009903440c1460390041300c082d00000f0494449200c0301c090303035503035205000081c1c0e90b6000c03030b211144007032010000c2507100e0400544038181d29214254250340d03104014103083d040c410052030100d606007091002d140240429649020b43c1032414404074180010b0050400c802c1e08121415004250060115910b178405040084009041c0070300000154440401880c00d13141002c44d105000c481d00200150100c0c0504141c82480178008104001200e400c841c24104144041142c04048002007180c0201c90107101c410740b4008007500002d085484a400c0401d40a50310b0f40c40203000c0e182041030410035a11941d050702d403e0900008800c2c060035511400150076000000150303910002c0d0161802140d201f003050141143c0000c02d600c188880e4090100007a15100803003258900c000703070b02001c6a80240c09002a0150b9403001c80b00756000428036071308400c1c10000003488500001c140d09584200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 572579514 1250 572578264 572578271
    0x120102090d0309320609060c06070c0303060b0a0c02090903070b09060a0e0d050d09060603050a03110d232a150a090203031605100e07050f0d08030406050c0708040306 73
    0x81200310607520312580b04c404400b58200c0c207043c203c1e2421940c001301d00780c400c44101d078a4403503200c0003640d180301d40c1c070780c40381580109000d1013040b94020b0024910203129031001d1100d40c1d180c41d020b86850040f42c3e03514001810b004024070160070001011368111000e01c082c3e030700e006402c0d22061524981606d1528240d4040342c00c003c1c0100aa120741c030910701c0424003504200c0d40d00310b0014000c0c01a100d034035018a0340c41c400390040140940c800c0004550100aa0f9840076160501411410450884071000d010b01111011580d114581001e84a080203800c0034010540d2003284103c2e400c51504203020040580c43c6a08403011002d0000d10180804010581c41c85900c0c4049400c1300041c024050090030002e0010050768007000756090b808200040440200003800c20300d2400394455110072146240c003018441410b000314010056035400d031185804d04031887c082c407078032441020000e82545000d10100740020102d8110710b400c8500b485010341030007a41d480b0010789500071761048412694 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 572580764 1250 572579514 572579519
    0xc080a030903020310140c16140c10050a09120c3302011416020715020304080c030a0b04080a030f050c221811070f05062205070302120102090d0309 65
    0x3c0822540825600904090064980704114054041005080051710740e0f00818084050715020741c00c1a80723180c00448440c55000000302c015202d541d80126140914007128260001c0c038021780450340c281090780c1e5080c0200780342100081011100700c00486034020740344400200e141c0491803084130240c00101e4841030010703102c0b005480301c0041c041c000c15039060001300b0007185402004a680702c441c01e0303191200300740f6442c8220309241c0d01d5040840d40d0340c0850411001e40e54000064815a001d4070b040304c3c0400d8400702050707515201e201004240c0c02104c400100056500700142c0001d5117541400f146140714440c55000343c400484841b100480c1c0803407040029074400c414510486055480c108205040248401190310a00c1d44842219202c11401c1d980c0c0082d08100c3d19895000140c0d06175840441c6400e42e02d920068903240103102c1d0600c602c007032071200d000056500c0d980c400e0051540a140d5420b1104180c015100c00141d95402d000b099031903250321182000c81c52107540c2d010492030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 572582014 1250 572580764 572580769
    0x1030507062c06030601020313060f020d020c060904090203100603030e0f09072f0a150507050406021510180506011112030f04232a030d0c0c080a03090302 68
    0x201c2000c01d941c0c000c141600b0000250715101000c50100c1c0040d5003032030b80d9079140ca00607403941c07107a680e070a46d0300902c94200043c1c0c194095000c450508117582515130001144604983d01c600003400c455205c0d50800000c4118901540207000080c1301070b0a03a4a82a00e182e6a5011030360103034026401319002582c2d503480f501c0c086d0544900040b04480350403490030028002428002013001c0c113107145007250001e007110200b06034030130a80051142240c151241c6450406482c804070314071181c0050409010417200c60042c010754059a00c01c0d40204040c490b0324540281980000d0721100090440c004042080d0490800d01c3c104005611070110312814540b000603c0c2003280b810018840d0805c00900c05107074000300840b0340224a034a803485850721a0f0401240d200d4958511a10280030003404154611b004604004014012100e00c0090030400307102d00701421048552941c190801440c81d0030690040c0c0c0384002103806604240c05198440040a107420030b0400d041c0d01181c40d2071000c00451 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 572583264 1250 572582014 572582027
    0x1413020a06050c030a0c06020c070b070213111606062c09071a031509090a05160f0611010603020a081605060403210e18040201181a0d020708030103050706 68
    0x70070341454a40d14014403500440c1d202c0c011117082c01e0400c6980e40309002804141e8050306c3d200100a820b4806e40b541e1423007444029400703490100e02030054040c0c0000000c080d4800c0116900808600314680f9045264044ca80468030313100311010f83e600c2d100480c1c10000704c0b00da0421080b90707145610682c401c05a000780c41d84030040c20806640d01c0408d0a11079500c40151600c1d2003e0500c0c031807034a035103941c140c0e00e14030202c81a5180e0407061000c01c1000e2914000b40101416000700c0a139180400302810641d82001c0358098800f1100c0005030030800035100700001400415048000600580c5a030700040d840e940b80c1d13000d00241e5104016007038aa00380002108010641224907510b0945542d036082c0d05003078410707114443d20341012503400c04103000d03148035034403804000c0c0800c0314100c00b80b1000e82c80a10689041e80020f24400529052036410268242a2404800003508400481c4070598080c1d01021003482815000c0c0041d0700007581920103180a180b00b500906901d83c00c001c1d005109 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 572584514 1250 572583264 572583269
    0x11221050702032505010c080d0908030103021306080606060a0e03070305011506110c0d03090f0b0d0605060309060414030c030f04090b1804020d061b0e090a0b090c030a1413020a 78
    0x2407801d00f211381050598030000504a400a003881050079240707003062030701c03805180b044403001410044194100b001000040d0b040c1c910880b42008010600d0720460100c40710350040c071039164400c80101d005450000b014003110070b91494004100e800305800320f428640950310031952607448118110329001d50903040380c060400349c0390840007048442565603590b4082e003e6940105007480d182c0c418180700e0740480000d00180a00904120b544014016955000380b0401407882c0c0390410116981c0b801d241180c1c003e000480003010780340c882d03449900e012078140e0f1001001d480100a500c08a007410b0000c1d0250110f20000756031a14034044a94041d250540d00d051701c2105045200b01035210010701c0c0b550010f8041e15140c80c0c200652500c40020407101000c0070b04d01c0c0c00505c6141080b54086000c2c010b580c0155000006600c52110000c1510b05e600350313855100c42840c00103080620443c0203035034803841812010940c8114030b10703070541c8005c040e15400340029141c0400000e504011100400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 572585764 1250 572584514 572584543
    0x80f06040b1f0c060f09020102250e011203030f180b060102101a0a0501021c0f050904020409050405012417120318190b071206050303030a0b1f02030301122105070203 73
    0x2006c84182d00003900d64000ea01c200c01c1d40d00a00750b200102c642181e8095025002001c0802d90a5031100c541c600b007500028000c400003030500f6035010580f600c2c0d00944141c500d6400c42d00240111030f6035500070b06140144684e04500c640808036012030b849000e010340b000b80921000031907910752402c1c40035500c002e4211070b05561142c4141c60b250840100c010a842c0d2103490407190140032807034110360510901703610b42e0b030145c0003081c0411029801d501140c051031140c03008011151a00301030762010a14000c41c641e000d220008200b1107c0355500040b0302c0b40302050144c42000075132441c0c106864009032000d11100740302a502050210041104507004980f8007041407100380d0710340d5000f4001e040200440104030000400400120302c50b00840041c001c001c040c0c0703403a8a0400181d0004000400c01244142c01c0f1480344032040c12a0304016003200f01039805146180c9c00c0a45a451a4502e000704403680041402003402080800c0f04074036901c00342e5507032141da41159004051410815202c1c004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 572587014 1250 572585764 572585771
    0x30e010f020702030636010e0a03030f0f1104060c030203070f0c03020a06030509101a0307080c0a24030518030d0501050112051510050f040803070201030c080f06040b1f0c060f 77
    0xd46c011105d48000300721034007030301007910000c6c048800380503041049407000b407485080700d89000c160b0540c0040031001070b8444200180107542001506032a242a512494400c0400061212078403621030140702c10b00a0040320310b044002d95a071241d60340e00c43e01c00d9540d0500c1c41414000c6152140d1700500400c0185010700c140d040c02c4004d191904082140300540903078945006403121846811102c9402004080e2529581e07645004d640790120b904030300d07105030204180450801c1c01d20320701c20035000100b50b4a500d1514406001e60003818058240599400e00340d5045a071304404100401540c00f060748081119490300c4005040c0c2c041840003000820b0905d010408c0d01041d400035206000300403036900e5543e121414083c4c0d840e00c6114190340d0444400030740410960310000007080d885100387c4c0d0030091442c494404403100442030392011f25004c4160080781083c601a00003500b0120300030140a95060000d1910185003427107200500414403042c60b0409204d010320607502050344007001807 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 572588264 1250 572587014 572587051
    0x1150e09101806050d03020d03060639020d03050903010506010c0b071d030304030f1106030705040605180a060c17090319060e01090b0103140c090403050703030e010f0207020306 78
    0xe00207007000b4016441c191228405402e07000d0b074250058402040c001d4000401d030b20301410000c1d180c84c017000302e04010a0070b00341c0c0012000e100d600c4410501c2041c03c00e074515203241018119400c120b141e040ca040000390342e03c000c0545d1381c40c05407020041c41b0b034890f0341d5903000c60000d250a60360020069414046500d140d0804910141c0c080c0b90b22603c245801150b9441d800700b1840101e02e0a04060f4040c84041004010072840340c401d11042e501802010716a403c08204105030303880300b180e03414005401840300300045030260001d060b41c800e528404020714107000d004180b00c440503510801c0029001d441032009e00207009484003401c2141124107251403d0b90f00400d43c2c80c0003082111701411103800d004000d1000c564003861340608003800038004400e0358140304100c11420b01084e2130030a450002e102d001c060008616a80203070142032210699100e48003920190800a801d0341410740ba24503400303036a8400c2c441c0301e12401001c01c0040c2c13500500d005143c40c010005004100060079622039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 572589514 1250 572588264 572588281
    0x20d02210304020a090f0209030c09040c05091504020a032a0816050c01020309032101150804050109050f1b0402120109020322060b0112050f010b0a140301150e09 71
    0x24140c5403254000d10681d01c1d1141d1020481100301c540c0070703242035440c0903008101c1996540050804440440c21104460046010054021000c0d100142400c2001c2c0c800c1242e401d0241e101a4810408000030301c50034249000300c1d050760300800c0300c0b0b00000d1340d5403d00080d00300c0703c10300c0c2010031007a061035060703003003c0790005424010701400548044044120403014940f14404581c0e801a1000003036441c1e0400d555407903a41c1d01310000020361944032000050740103400244450496078001000c403e0069501e0f0240c4400c00050800d032600d540f81e40500022503c20402122100d86800040401485e07489003940d91002e2000910b1103540100054034001da5280009410b480c1500d000580d252980c00c03007510905002829001c407401100d41600c240046076000c03904081d801c2e00c424019850000300807040b1a012204a0840030028006000d42c040c440042d140d2081c02c0e00b03000c075001c641c0d40003070411034000b648007800a510300141221000e621028040c0e00c2d0070240d83c0100f060400303052 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 572590764 1250 572589514 572589553
    0xe16030b090313030c05010f11074b1d0114030f0601060801050405100501200102250215040e1302060d02030c0702040501051c0305090f060c030703020d02 68
    0x101900050300c0030042141440c06000325183c25001c0480c2c03a40b015030344d280501051120748140790102d202d032040c544a00d40901d01981407102282c02402c5800e041054051050b103000054052078110140c891100114920b50035990783c54030342ca40c110010106030004414a05900b014280c3c0740b002c8100c01102c0814110385054481000702c28010901190100e071070310020804c0e420540c414030000140d0b8075081104141078130405d4605020715a180d49012040310080d00c100d5001030700d0103038428030100362011550600800301001514007002e4041ba00603032165400e001c242c030305c0c0c03061202c0c0852408002c030f120207040201086080502e008001c98180e000100501486a07030100c1400444d6035640c201c810031141c03074004540b01e04101004990f240c0040d441240210b00d06400403c6900c0c01c0b4010101c80300c295120100c24004075581201e02d500310207202504101f42d0302c8455000c0d55110060415240030100441e16280c0c83c0c14001d2030000c00f11a01402d640050707071036251518840c0c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 572592014 1250 572590764 572590769
    0x80313060f0207261c08010501231303170d1a01080601050c07090c0f020c0915131503080901080106030c05070f080c10150b120a05090312041101030e16 67
    0x11462146007124500ea0240020800c00c1c441d140d015a8100034520f02e91600d0b41403040170150303a0b80c2d52036a200c1c801034840c110781001c040c0b6003a0455103030304614454400184600c9000a05211009646e40e90718108401d0340c0c045000f0329a1b0209003190804418030948107140070656011740003c0700440040c142440c0070f8901410445c7c001640301c02503004000403c010301ca005000c02a0803440030380103240d0000854100014000c842003120706190141c0c0e114041c4000050031840c3c603000400f0805525200400321001e0342c3c82e0401c062140e014024018001d60207491782c81c0e80c442d101000182140d1058102106040c6001d02c080007041e405800c3d1081c03198498407041250300e032401e0501d490b01031000784808910030440401d0f504802d079003100c00c800c01300080f01c0c1040c40c1c4400e254142e60240c2c03044141c65146030400034160f41c00c0c40d009160401c1e081400d0364900340540e1800303030302e01d0012941525003099151400300b03030b03580c0762081c030246c01010000b80130040004800c0f148102e5151 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 572593264 1250 572592014 572592029
    0x11a0f070201050c0f0307050a0b072c1305010b0706140108031204110907090302150405060d0209150a08090c0904030e12010608071215050603071503090c080313060f0207 75
    0x440c0b10000030f0b6080002000440c8030400310f07a220b07c12481d080b60740d0110301c03000f02d074150155404200035038001c22000005900a01400c91160001e00e200075104004003003080e80f08000620a860b403004034802d041c0030b0301c0c48140080e0756220b170303051110a6840a040d8081c11020f0b507401040b01c86004416071314001ca005454026544a9080050120822138010740d84540138605002c00b242e045625402168825034a0203074039801600140040e0185104454115604219608440000d6401000c019100800400003e5500d070340078085070300002100d101080c645c07030a21089030320401c240e5070a6482102c031055603103450740e0300610000c00749460600a178030a64600204079400e41000014101042c01c4501c076560b90789040b90320100c0d01205407030080041a00d408001e18500641e0701c207060280051500c40d14100100001111000c1590101039440e00f540c070000c2c12401140c0001d25800000707540725804000c031080d080382d1640c089028080d40e40c000300301d6950041031803070441d040c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 572594514 1250 572593264 572593267
    0x70e250c020a030b070c020102010f1b0804050f03040f17010203070c150b03030c010b0406090e190302150a02040305010e0c0112090503040504022101150c080c0321011a0f07020105 79
    0x861010507101006600f0003018041c4070010460322a510400c8405194001d9000388800c8041c03044282c1140d001d40c483c580c9074040d688014452a0103981500c2d0007511510440788a10110000c06003150440d810074091a0401d1904105810b0a0326661080035402c80007146141010503010303090704240c2c00000d0541c029902d03c40900f23201e52b402600c1c0d989003d01900e580d4406425114020a140d80255205a04d020b50100b10366032144035070035184149600611a4040d4260729807402070940000310114400c41081c1c80000d582924624002c907283d24015843c0c504602d0600c0c2564003003040b01106074050b1032642031a80e070042d010010600e00b00c40c000b8000340c1604110381144201e0708800c0c0c015000286d80280255000681c1c084901a404062406d9884541c00038203c1409002d610000e00304101000100312200d0081c04094070240032207242c0f4444540c005d515140010540d41d51440e41001002002c0551410081100e00710708020301c3c092900e5048041c5000703241e4042c1c10400f0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 572595764 1250 572594514 572594537
    0x5190609060e130e0115170706051b070b1b0c0904060c09050d0c0305010e0d050a0302130518090106050402071e02010507020d051b04180609150e070e25 67
    0xc40000c0580d50820101c42400340c50b80307050190707000c3c00c81e46d42c1c3e0450042c0400c50000711b000749024070310402248080a0310840389415001c0710150000e032101d405011000c0e0395815a41000c000204c010247c114142d51183c400c00b4050704084102110504140c01409080c1c000c1c0d5250180aa84103a200304009076070664102c00301c43c1d2075400e80202d43c01600040300301e01072043c1e00108a08580c8980020303c200398590800a4035201c07221500c00c007191301031040d00c0c180744c0030703402038501c0750a000b40440c882d503500c20005055441c540e0455892210741014002a95030038003810005d0b06040d10150b03d0580c042c0e81d115a07800366503000a00c54007a515540c4110ba2181084400350798004250411503403da040858881ca402801001c03000405440d04540b41070034050f9014601d01c040002e420242140c80c1c04000c0c1c0800c0e031040343e5901500504100503070b41c900c1842c1b1440c107e00300401c072041c00c100104400303010140c50301c540e03420b181d640729492104240c1c540c01001c00d50301c0e02340d480c0d01c13 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 572597014 1250 572595764 572595769
    0x70e092203020f01060e09190c062316030e1215152e03090f110d0b070e010306050f030a1520032e150e030d030605190609060e 56
    0x10041080c00301d20713508101c400500d01a1005041d4020b600003030a8a0b082d02c030140c0520280480420300a1010307400c0313441085041e0007400d070009805c11000b210110003c07085201c104a0b4804810125843c09030741002042c103a102c1808074020340300303940c0481482540e030b46141d5074074540c1000369603105810002556586641c0051150150050005582c07080b8501070410258003a8214044403050210b030070403954800c1c01082001034210301d11048106c0c060b01ca40b400c5800700c00d80302d85c010708140c03190000541e081c0b42c1c59116000943c2c501d010401294001800d454881c0d2000380f203410a1103100b61255004601c12000175440482c2d98402038078884120050000810710200f408000388100c20580c03030a100945c0b14410711032900030360710700c1c0c50402020210420501c680d0341c0080c501c103105060310ba46c00c0d841c0080d41130410b5034030202c140e000a490000482240f0000940b40c1604001a0074200e030b0b0f00c0900081080c210316841d0601a0040c4420340d9403182d00200101c14210102a4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 572598264 1250 572597014 572597023
    0xe1203130212070b030f090c0d1509020315010510030209060909070c0b09011a10020d110a2114030f040f020109080105070e280302040b0a08030301080105070e09220302 74
    0xe0001d4002d94071015a145050102c0350400c6500c1b0346000c0c41100040c0c0950404900340095001c0100310002c407180680b02d18103800400348913000202d503039203030107009a5004c2103c40c169600d90140050a903040405101ea4004040c42e038400341801031000c40455078420701a11012001039910100c103644100007122100140400038000104a0b000c2c0000d00606410100b000d1249444c0b20010301c546800f8400030030034007900d039070060704100c0281210501c2110190305401c1840e040b05c00036415911004402001d0010000d51034150a0803115242d40100b46103090032031265041c0d046140141c080c103401100240001c0c9880d414210303010841e1702900704840903200a200030001c910b440003015050680c008210780c0f2031034401041c0140111a00c81e1010154002d00c02d03200c00600d181e09102c0500003100e0040d42c413071607a02c00451100700c00c02c003450007044907100119540c00c110b0806486550011201402041440108000a01381c600d9050300c001c0c060244007082d08007405c0c102e003032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 572599514 1250 572598264 572598289
    0x1a040b1503010305030702030c010807080703090303020c01060801021b0604081b150916080f030d0213030f08031f0e0f0405010f1505010e0603220c0e0a0f0e12031302 73
    0x141000720001c01070000000140408034400e5049031625040e02006641d281c0c41182c04200040328440090480c40c400c0d001044403131711a00b805401c02d000d055105003564440d07003080c49169804038075043c4500d08a03518030991180d4001815003400d103900ca85503203100d2404d503005107580229005044000c02c01c2103442c082d290b0220b070038440c106910301e152501041154044031583d45540400d03000e202040054800046400841c070b031812039000c00300603402000f803144030402c0c03114000001c91406184044058400d6800f00d9980c0f0741b03502c40d5444814404280344103610445401e0081211800019400a2207940740c1c0b01155554548140034003104035003101105c4c100035101000d501c1c50340e140e00c26190240c0f1444036034840c0e607052020034082140c2e652072081070904149501d0b28158001020a40141c540c7c403051900c580441c0e4145c0000e0301c006c94480e640d81030103a2101014426202107542420240440e81000101030013380400742400d0b0603292049039981c115070380c0d02c1d1310b0780c039 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 572600764 1250 572599514 572599549
    0x421612020c0901030b090c03071512090803040302060108100629070c0e0601020c060c031204020a080d020c0112020702150310030b131205070506040305030613050a0b0a091a040b 78
    0x2ca6859151009042c081650b0308a0b02d03100300041e80100d03140200d804001e0349d0301a030501035001480001196500355003c1da00e103159a980c000607001c40c0b1380d0b100451045010750010026545030400491405d6020103503000300918020090005005030079802042010380f00d8090540300104120101501c15900c008225216404000a41c0508515440c3c071030720090b02669400e1949105020300e82c0b1803500c2d0310113150006c0241d40f144100c100c0c0040d81190028101c11030103278880400c00e02e0110b0f548506005603200011018040d82d0112051000074030880080d8200b0385c10358007160300c01c0c0d05800d007000d91800c0403001420b60a00324140c00021504008018090f00b08a950030008448116040d5003240c014000601014000c00860300c00942c060b000b44440d036100e84041724070fa00068440741c0e01865100130b100c40401c85005482c026441004005515240c4908000301c01216a001100072418580c5051070080c10903a0881040815940461003c07d50400240404043d1800c00b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 572602014 1250 572600764 572600779
    0x206160c08092d030a02060319110a050408010606090509040605060301240801180b131a010611060a110a030213050901030506190506090109020702421612020c 70
    0x200103142540c0303c42c09a40040c05003d034004200e0700340b40d21040c1c40c04004e0f410990400c04a80140d0101c4060050080481308c0000d04401480c0703114000da001000110004901140500240d074083c440c80740100803604003210024500345c0464001400180040c2c40c29640f0300004070b41d51001e4100781810224221030381c021401c2d01310240440c1020740a2030b05650303c3d0204101101110018011850750011005045c0f907543c04103481d0002441039044440c81c0000d001040c0e801e000e0480c0324042c20040c3c4841c62041c554a00007071401400130b011840315401c085106003a01e0942d41242c10029407854090380d9000d0708082c110702c0749616404190088012400001031010115002d03000f4402401c2c041d1110152205840c1516025a641c41d403100c0c19030010001102903034010401c142c8044c2c03040112450031000c144103894407514032401e08007100c0c10003040c021130392141c01c0e8040c5043c45130707030a107201d41e07228a00c00030041078024210361031032001d04612070007008203911b070180041c10107 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 572603264 1250 572602014 572602039
    0xf0103110a03090507080a0c0315020d11040e0a110315010e03100c140703051801031e0c11030301121b0b0a0e04060b0a08072118120206160c0809 64
    0x10b005140408003520300c4d00840901241002010030380350391080d0481c8440401070300b142c0314200a0146080c5104030240d00304200a000c0005000f44480f100d0030252040d01c0d14135121400c428041e00818a614082c688900c8040c0d448001050b6a040080600e5104078603002030016250080500005549441031100e003402c001c4542d0814000d0750201c3d5641100101344400b00c0310140654134001300814001c0c0550f00038048504c080c8070203140140f40218200704100311001c000b21644500b46006500c681c54140c1140c1c01c48034541518603120000c600d10340c580168801f071038001010051403c00310951401c1c00c008921a00c9001d448480b00059842c041da81011784918407107d0001d0141d8144140000d01e0320116007918000f580c65214400541d441d04011900c0180070382c60b003000c454520b404414070340c4061040400c1016907500b280f00351003540c01d00160a1260890007011940700c1030400400300480044411604410f050050f81c1300094945030b0054043c59003580c1d0030003440c0d4940d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 572604514 1250 572603264 572603267
    0x1f0213090209032e1805070303052a07061404050d0212120a0f080c03040b0a11160803040c091104030b1302090702060a0f0b031207050c042f090f0f0103110a 69
    0x202c040c0e05480d801000030170410000c0b103403c3d02e0b80d2903011700780b608039080c1000404e00070001404040d11200b200301c1c030700100c840c1952505410340031003045d5502808092208941045003515414009030307840381054500b4000403009207010030007c0c00340a42d050740d9444100104030b0300000c2c80d5400041500c0b1804024014045080d45124030000f991034404035031400c400f902183c1c080c5801c810888041e6984072104000ba04c0c60b40c004100c0d0f1802040300032030710003101c40a0201e41d441949860350b40d04040c200484d180c4000d40090800e1440c00c56101d1480440200710303821030382e02980c05109684d61801f40b240f100c01c01900603401040c0d85041121440e03010072140c2c8948462003041156840800041048178100d81e0496016440380c0094035022010401400c45148128212180c800364540410b042d42c103210b000359003103c1c810301141514a41d0070b20141860008403410350500484000040d040007039144010f001d00c5503410b100307000e84d1081e0015403c00e00e00300072190b59885000d40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 572605764 1250 572604514 572604583
    0x70b1204060c0305150f0310060803130807060203092403010f08060703050103022110020d0c0f0c0b07030506040b0307060f180f0303050c07080706021f021309020903 73
    0x30200e031868500708400c81c03200e009100c1c0c0350188480144400d519040141444420720710a00056450b1040182a0500c56910f02501d030180a00c4000f840c1c44109407a080c2d441e005480d00326510742e0b00100028013800d13030700100380c6040e90340c01c03a900c8065200c111072104210b1103180140b200600000000b046e01240f00d294081210003400465845640c0e4500031001c8503c2808000d501804280c4010b211417074a0405010100054080d00e48008118070010102e078006010042055154515450f00f04c3d0020b021003072014180c1400d88600f502950b0309040d00800500b480281a60f8002003000c035100d0f9400540b0142c40035045440507501c40c840502445c1c4641f00d0030000401105003d06607030780c4001b0403800c4074041c490101c2c0150950398103481e61341000710501c40601c9a02400500d01008011002c010701058018141c910070b20f441010315000209081250180104008074940c6c1d03072800e00b0012140d60780300040e2221038580000341008100f0700e01409a451b50120390160b01c40c4140d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 572607014 1250 572605764 572605771
    0x3032f030103030e011706090702030c071401020d090f051c0b0709031e0b010b0708120709080d08090a24020403080d0c09180c1e050304110906060d0e070b12 69
    0x304c45440f144a00d600440c1d0341c1c6c6201e107030301c8140c1d102c80c0702242e52401d00c01400394200c0030798015242496481c1045521f820340c142d020320411540c20002e00303480e580510034281844480c0c038100c4100c904100342c1c006100494440d541c040d54003458450051403181849040c855885090301c07249003404034000317010203442e0100b0760710030074100c0820011101e082c8442140d03a5001e203004a06030300c0e0071181040c80c0c00c142420303110752404000144003030302244042d41c8184099291140070500742000c1900d45402803800209202594003404800c1e4800111184182d0b0301c40200074051200301455000c0e1039a00010704100707800440e01104104400029142c401e9866070100180608800300700c440000501c5101540f032000d2150402d09580b5400070404580142009103c00078074240d60a034407041e80503010001203010041c0010080950f00a0a1543e401c441803a598200480059098419080c54854490307561003190301e400020f0141d440188250b6003440d0729100c40c108102d19100303044 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 572608264 1250 572607014 572607017
    0x2011403070e0306060102010c09030f0f02030304180510031109071701090c14041a03090f12070b060f090601031d010207050a0b0f040c14130e07051507050a03032f03010303 76
    0x134000b801c41e52051183c440c0040c040c4d6a518819440c0d600d030706d80c08100c110f000351860024214107902503281080100b00600342c1c2e840084200c0c64201500c0100d40f0060f24904c50b60812002c100041605241c03144800300e0210b030007800c0741e00c0d0b14a01f138640301111440503103d005c062000050080c01035000760740d40c203001c3c1c42e0080300b9620fa05110440b441540281c0b12020b205e2204075900680c00740c042d540c040c00d028111529102e43d081590f1804c03800b0080e00c40f4280c0b000466204002c0c01e204466084541130315014104501c080c00200c0440009042504250303070f403100003001301c513686d490043c40502c4800842d900c400508007a51038109101c0c0c107842070280d40d404900111207082000303108603008522526061306000000c18a000d40301d1007180c0c420a0352040e518107191500c2440507001e0b01d803000309607840c40c140504c1400c80d140d0b240c01c600400c0620030080856400315200a46551500d80050000c2e80c1020103075003040a0840207044d4020b03ca140c020088208c401036050b03e009 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 572609514 1250 572608264 572608273
    0x9072105011706011d041b03080310080a120509010203040e15040c140f090f0303030a0510060c03080f060d050d050706062102010806030c120709060608060105120402011403070e03 79
    0xc112010f03030756080c2842070400515159201c0400e0405450348141c1007171003030b03059203075041022102000c00400b507002a20400300c00020f00c00d0700b800c0c4403a800d0007454060003a05082c0e145840342c101510840042d00c2c00c2c0701000454a60580c400c1c011100940003c015a40300d9050400040c010520b5221045015900d40224203005a0250701ca035105052100310741850b04800750b4038500d961300509506900700d00c0c071646840031a942400a54400d03140c212001800d8500f600c040c081500965001d68103101d03061500e5000710b9400180c660780a134160781145403540b102404500e00d401d502c14064824001c09100890090340f100040c0307019402207505004054a829454810540c5d00c040c3d0310360103905c4040302d401940181e41d1294050b2005040c3e8124503074860105940030100302034005550421001444500441d20459015194614180b02c15140840010380b0034070800d4620a000e8072201c00080840e032151180c00c0310b00344c070070301c15903101c0c1056800a0701d06111280700d0391080c0038 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 572610764 1250 572609514 572609549
    0x601030e0312041b171b1c020a0b0a030504031d03070302061312080a09080c0a0324181502041d0408070203102306030715020f15060a0e010302030c0907210501 70
    0x350b16140c08180e4001f002c00041d040907034201d40c0d2071082000100c0c3c001c003081c0e00015102007084054102e100342c0792000702e9a403410b0716004105820015400149200e21421851961400070304182601d40c155200303559100340d02550348964440d80d004d40c80c401c0c2c2c591050300410440790040d00440925855284e0aa40c56140c0d05482d1141042900e4214500b00410000301d8a00030710008982c040307525500c49000c80216040961700221007440d01021607201107002c1240701614451010900341c2c00318200350401d0003540c50381046c0c050408a80e65071401107018081441c08580301160300070203d44043c6801c2031325001420300003118400c2c0c1c3c540841d01207520307400541141d20030300d4000e000c0c10000b0b003460304865000b03c60824010840c41001850010b46d00308100b150500032801014000c0f030300e0510100001408990012004005640c0040005880002d40c1905121007206d640500341d868132802c403414046c4000800010340d18001c1c10421500980c0b203541611071890b000d200140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 572612014 1250 572610764 572610793
    0x10e0d06020a0909021608090f0d030906020d14040b0703090915030b06030303071e11070905160c050d0c0303090615080609160e070c05070803120601030e0312041b17 73
    0x1405038500506c03440481c0010005182c6001400507140c020036407030031522280e0200c2d4020725440300480c08203018074414000300b6010404407480074254500705014114101c656102802644900720700b02c0004a80c0e18200341c01000700401400fa00002002645502c41c07000800c2c0c807261200fa242d100b041d00c0490070701e090200c11a4840c01554032148408254a1406441c0204185041c01007181c00c881189013280d0a0048100600312640040345c103040c0041218031403066000d0070010310600c5100180052000b155804242842d818412511111410123401070301c420140200011324042c042042d1804c042c0140c801d41d20b11408451031950b4078002c803a0340d032074002da00c0001009191020402c2580a46d41d15620050303610b01014441d00c280d448500d407141d103411038501608082849208840c1140c803003940b2590034601400340c5624040110f841c2d10640b1700c404035407100b880010301070001c0d401c440242540002501d101607a5940c4002080b0101003a80c1300307150003036601404409 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 572613264 1250 572612014 572612017
    0x801110403241d01150f050d0b0630010f0c0801060804061b1107050f0105090f15030c03012907030f20070f050d0b06010f1106070816210b010e0d06020a090902 70
    0x2207d0150400f6000e440c076480b2510700034030003881c05901c0a40d8005520002c44041d0552424106185985000c0c0101c507111900b0750390a08212046149440d4151039044d0f48244050304480242c1805042922603007808070192a0b02140707002c50b01d1641000f26000c0ea0b0180e0100201041e06c420b03504029200d80800051404041000307000074800e01580c151450700483c0c0080c0100700508001e2100e80c0b84900c9a01c54000711210061040007000410465040048201d81c00c4800c0310300e0311480d191100c3c525114022604003030100f00c200204100c0c4140504a030503040784180f44040305e0510020091a0746850b0342c029011824801c2e10001564181040000701c0c1075880101540315949050044030080b0003800000308200070b20a1941d49142c0a00c07900c0d0188403280d8402e42c192174444400040c00300c51008807020095a0203241102c0b02200c4503d5003200400c030400b107100306034940100e070501c90f00c80c04254480b1800d020001080590707030040c8845e49141d100c80110075680d4070444200d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 572614514 1250 572613264 572613269
    0x60801081c120e19030c050d02030c0604030e22020a0905010c0c031205121509150a0302040b0a0513050a1b1209060f090c0801110403241d01150f 64
    0x118400c0561070003a0899608000800c803081e0040b151409041504030311034140000c1d083d170100344d0903200c43c0c00344202400448030300d40d103e00045240130401000700d03a03909070041c406400c0120140a10510740c0d200c0290186d40003a40c0c01502d10082c80c0100c0702c00960105c040f1030042042d01d00002042c0d409007100c2901590040841401d0070310b0f60300d8020760b00d00050340b8203040260420540500b502c40c000e289000307846104016038101c00302402e2100c42d080140040b0004080e0000303402d02640c07010000c1059950581d4085044801d84000ca810070740260440d82d8000b000c4a44d0710b0700944680e06c414492441501c0610902d58060341d03d0400f55a035403070400000d2070f6407058011000e0716070002d59025102d07450000740c0b95208401d0908540c41c01100310f41c0380450120800090f14240181303c078149426040c00d141606d159141e040540c0c080d0481c045010007000c05040030801075204914440050814070701500040c0700031802040b440b0148a086c100035100400eaa5610b0304080c000e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 572615764 1250 572614514 572614517
    0x10207030e03192a0506030a09111519020106120516120b0417070c0311030d0912030e130e0703120c0308070318050708030d140f0c0c0a0606060801081c 67
    0x1441600e5000c56401c44e2003000758414107101040d8001104d480f03c0c00114495000f80100103544043d515211440040e0891400c0c031070821140498292800b62040f2044100c8205203400344400b1601c043c1e0141260b0780c80a800144030b100c04200340301c00071512455429884074035049842c2c60310036217000c0c9400558064903028001d00028001f50700c80740803100e040c0404020783c0c1007000503078400c02c84881a420450f44000221000c2035035003400c1200c81424625801e0008d803440c00d011003910b1800048901804111400c40130504c2e949441035440381440c0d0451003480400491051913a07a550700f84002c4034450710b440d12944009200c0c58203030f40d403141c3c1030b41ca0444680b00c0d40000c401400c0b281c4410004503040c080c2030b10006504110b40c074020140c1c0d0000e591590410840003045800e40c8c148155106036a5080280000c409a4030a40c8403100e10107640e00e80351559280d038580f9010050050002d8500b0348085800354004016070b040b65040030880e03000a802e0407a18045882d100030010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 572617014 1250 572615764 572615783
    0x41d091b060c070527070e010e04020d0f0608030403030908030f16051e1b040902182d0105150c0715121104080f03032a0c010207030e0319 61
    0x100c0c20314000d0000c042000c0100704a40109448100091141840f02201040b083e00440091440c2c2031550f03010398443e280d400c2030407011039510b0002c1c04401c0310a5a5038400c0780e000407039800381101039104184282c080201006080d45030f07908244d5950190100381d012503509140001c80050000c22181e0b4524909460360824990340200da010341c425410407150f6020f10300e00d10180f0142d04020305a00984a8010302c083c081074076820300c50b40c1c4040c1400e8011400c0602c4200543c0302d1200164070100400e0702d4950aa039500003000304450052041025403a204000001084200c0d02c0141a260210340b81c0070000c4480c41c005605116070805407909800a200c204202d1841c9101144030043c182442a04585405071203401c603074494085441940010405014210080061007962404000194a50b00b0b16900310b5549000000e0081d01c0d011040d000644d140440509880f0318240c2d9030300a54403140725140184c4882d83c0681000d0180c80380c1824440e5180b00d00c01103041d4241c2003407804 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 572618264 1250 572617014 572617063
    0xf03160b060d05030d09060615051e09030a0f02010206060109120f2108011502011e0b04090b0f18190206030c070507170706182108041d09 61
    0x400d4420340105a00c0d40000903840c00c01c0869014001060f800c0c66211000a500c4018542441142c055400c20b00030310b60700e800d0080c4480c0e00304040300c0092404c217108140082d1009140c40c2c0314440c0581003600f5000d400c680340208550100d644042500c02d0b0280c5180f07a441200458000000e4401c90600000014801010407000304040120300c4c020982c000b4030b00700645440318103184101b034540000329542c00412280da28180d04089280301d5100a0180c1400c5040341c04038840520000300c2c03a0b5648030b1442e03015a0b590703840407680550100300c0c00100c0c588070000252550382241d10030f401d640b00b100f6440c0c01e040c010440b01500425446e0b4a0303000403658082c0a40c0b40c0008101c0401c0c0501040b520010640400511b001000441a1200c241850030180c030704014440c0d000e20184858443e442004968500340d200941e4000001840d4015054a03a4020080c08a2018100316000540812113400c09581461601c1112004801540f52001e102e030351490003600705281c0d0203180101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 572619514 1250 572618264 572618273
    0xf12020a120c0909050c04140d050706080c04230324070c0c080a0c150309020108071101091502090a05060f07020108091219080601020d0c030302030901150b0703020f0316 75
    0x1050081c0d2092510400441d144d50341803088410555805000d600702203402c120607030000b06040c2c4415000ea031611000b060a41e80c060b0740302410b0084000380720113240000c64804200050790010250310400002150010343c4084a00b40300e816210702a00900400c420040c1400c03007000068414405001c800d0359076903000319109824030108030b503160161786c030024555104200e40d0360b0141c010350306003045624080320200410000c4583e5400c2c1820b003c183c20260303801c0040170f0360191441c00c008180000c0c02c00c140d8010108854010028500c411500400c03500d56806040030780000c2e04c0140703c072919a020130103035005440f006080150100411001548204d00c1e072a00424501e04a417524698901b00c691540c0007043d420b440d2100b1044613045280d4030400b0250013440078000380c2041c4011000082100c0c4060002a09060b0000085000c5100962000700720100500181040030b0326982c0c1042d082c0d1080e2030540062190b1000340f50541800b02c22501510740401c00c000600e91142d54 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 572620764 1250 572619514 572619521
    0x1a0f151e0a05130608071a032205032b110f0d02040b0a0c03090905011811090d0305040503100e0d1202070218060415080a030c0c05100f12020a12 64
    0x14503076009581d28500203095260349070410314804015001107241c03400c11248901c0d010060b4004a08581c102c43c0380a803840b1003600300c5c0d80100504880d10100c403070f1204030241e81c61165900605512001494442e50700c068150954802c003401d42c0e9414401102001406440c8050b900188104003000f8010f981d1510390001d11285038181005410565105189030043c1c10807907a407000300b1600c41c0503004041d0f0041c602d01c003910032004100015418030f180c00f420300c07003140b4030b0f5544107a8494556160810201c1599850078000305101d005010501c0d00620136001449028003038031442d803440780007075514000c40e00211100d0b4000c00e0b0031141220204c40c0c103111006468040c907820000b03000540c4500285022170f04400c010264141441c0040c8820ac0c1c4e01055104090401d8840034005100041000101c00d40c2501c1d0031040b46a04e03003803980009007a0780c40b050380709019001d000d203240e030004d03009440790704140c4030041807100340600314043e0300c0380c4041c000008280c1c0c0003810f42000325a1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 572622014 1250 572620764 572620819
    0xa0f05011401020709200f0d0b18040204090201200f010b03010905210706050a1d151f050a080105040b070906090b0d14070201061e0b030c161a0f15 65
    0x1070726071044500103011010b1b03d500004048440a6002848150200341801150b074801c50035030b0701c1000c0450008504c2180c0d080030300020f115545031612501035a10598541e290840002c0680049140d00316442d6074803542c8402003421542013504800300c2c1d14040c45001d01350794006029003800072605a00000c00c0300c84910401b940c280c280b10044c0891190b105840c400c0100300c000283c0040e0f80034013104584980720400d500c642c002a90b4001c41003816003100d0700120100c4400f118048420b028500c203403402e42025030003d140c184002818074054110a0080b4010302841005441d800d04c2164003c1440c09124081a002601042154000340040890900300240001c41c001c0c2900007054030401a6460801030b074686400380300c440259064601261a035000b0303241402d01d40010650300d800001c180c4680d0180c0840c0c540640303119400883c540e0303175006c044a18909402001100300d4039096070499041c0c03041d00005039807000f01007002d5900c160000d091200030605e410807a500d408010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 572623264 1250 572622014 572622041
    0xe1207020105130807061b050c04051b030408030708130c1401090509130b0702151b070b0709030b13050604020915030717010b060a0c1401140a0f05011401020709 71
    0xc100c11030070f152100011001a11141001d446000d16160b030007454040b014400525038a8802c0c1200c0c0004e0000843d4400c40806907008640c9540d0030a161a282c120315005c1680c0a10010400041000c01d0b00150b02c503c08603100c00e20982c035403018050b01c0111200c00100300903482d400c140810295640c0c40c4c14051414034000c1180303600c410110b0101001075412241e1105290040000c2040120f4030b01d9000b040c5200410310720007084003000007020054841a071225140c0030102d114000d101c00c8888840d0001e0b9030081c10300340354100405c0e0a003188015146090803c011405c01c000c410740034107445070888010406901c1e03c0d006c1000500000d4103400c100011040a540d09880c14459000188000c011525080094045c0e05007540e5004607030901c1007208021080c0f4464000c4840034030341d0b130000c100741c040d418010b820500602401010321914485101003150203401d54000010504801c42c09000590303071520300d0070b0119906108180560031082041c441c000065200f01c007000d414 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 572624514 1250 572623264 572623267
    0x513030204020a0815010e030a030c08130621090305091c150e01180302300d0c0f031509020a0c080c060402031b010f030b01030f0e0d120e1207020105 66
    0x480d40081c003280d01c006020400702d510601000b0801c0c086050284d4544000e081c60721402030520300207501c0d0031540d00c0041c20721038500c803440248240c400a5400384010000880d812035160038015001c03210710042040c00c50082c0e102c038801000e15029900e40f13150716444141c101600358003003024006a843c0c5148680c5e10302c0301c0140108003034140035110026070000010300c440704070304401e01391090510200c41c05086040c034100025800a030319040384803243c0f0401202c071400480403280c41941c640080e40c616010440c0428940c41d90b20004442600c1c3c0c6945d0080038000c0001e80940794040c04c0d484403046e041d0710410001c5c41a0700100181c501e80e04c1d0400000d60b00303903a0f501451300700080c031103202d0303001c0002c120840c01c0810103005018078a0302d100c51400c85044c002407c0b80040000da10405454201c03e081c3c40c2d0080e0410b00b0b10039203690040c440142100620307036480d520400c0c00d0000450240d03400d1251015445992150074510010788000c20b481c541c00c01040d403007414100d0402c00d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 572625764 1250 572624514 572624519
    0x5061812040f0504021c1e060f0503060c0f070b0c030604060e1006200102070f020a08030715022116031d070b0306030a02090903030907140d1b0807030501060f090b0109060513 77
    0x50901c80c0c1403503505220501c2c441c1c4061f164445040300d00e81d400c0300805402d8100c040c0728958001440ca81e02040310104a561001d41182105050140090050030710110109210b0500e030240c000c0c61003000103540400c041d03a40c0d0001c0361807011099841a8080707540b59030034401580309101241c01b4041c0341c400f0845940100030000e01b2039200f10826500410302911040451504a0440c0c000b860a040150308054481d140d8826046080c84107088580c0d0009103128685030031800710020b00400c0e4242091803030a0601d4032003500d9001d940c1c0d80002d14122080944100c8900151404038030b0b44000e103d020700705511510703554000790495905d48261441e04005989080705035210303004c800d004d16120b041c081c0d1041c0c585050b680101d4074580b001e0101c1c0501c0d44502e40d8181c903103600701c2004c0e000448138480c0c0c0380400206400c64000780c06919408030074000150008402c884a8011a280c03039030344c2c0c043c000300705c9101034003660000d0070b40c10080082e140f241e00600b40f00c14540446280d2241e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 572627014 1250 572625764 572625817
    0xf030201020f1602040c0c0b011205011d0d0306081b090912031f0b03010b03040b040213020d0603021203090a0323030703090e06090411011101020705061812040f050402 74
    0xc00c80c070f10341014000140141411414103000303500f03c0c40c00c0d60900755400700c410b50f1560b64441050040b420307202ca114002c8014071a00b50007840e150701c0b0b07110444413070302c6140c40e00c1e50f140d00f00c084020010078100000014203450002d250f00c3c40000b038051410003001028200000210058a0302e0558814140c40b02e4403000c0303280c002c6016603030030b6100f49000701580742c1c6c002c4000303441e910801442000740010444041002c1c00c5070b0b4095400b1100c002c19a03a248002005c074140062140c001d50b101041c52850a40b8581c0a20240c0f80201d4045584404a00c100c40c3da91003030025007604100c200301d04000040c611080318502103003045110b064a22840656442d6422000c026070009440300c0d0100f00c0f0600d590612074111005503001503e83c81c160700c5404501b5003500f4403c0c1088500d2081015401c0e013135069030b016561003001c2c4c3c0d001c1d00381800403c0207101c4295000300701e4000c0c8410700c640c07a24843c0494044503040003a494181c0d28000801000b9045004003503801d51001e0321000900 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 572628264 1250 572627014 572627017
    0x2130306060602030307020d02211b0a0b06030c0a120803060a0b070605160f09150e091e0f0f1609050402130807080c090109020a030e03030103120f05090108040f030201020f 76
    0x420880c0d0013140c4034540000001c0ca014068120941035402601c18a915403401d20b100b244001c1110145980d1166122201c003448004168011054007403000c0b014200b100008505004110850231943c400500d42d04000317686c001881080c1001f43c030b224202e00010309140285600c80d0004188101166848540b00322541c481142200d1044e9184100300c1121032410340804049020304c1d14210000e10404003400c01030560240c01c2010030020258070001d40b0800c41600102c07070103082002d00c0d0412040786920014000f4100000d034011a00203510b0000420f00386102d4406100c22080545406d0003207000001c3d101415410000d040101280a40341c90006024400c141c0c01646800751401c3c601c2d60030060641c00800e40340d08115212190755a039201c0482c196500b500d00140ea600080200740c0080c4803400c4460098080800000280a004e07100900903a003c0c0e156226100d031030840031a43c5201e40c00166010440030380c00b05002c40c0188480032003043c441e000040c540400071440050a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 572629514 1250 572628264 572628269
    0xf011a0904020307050d080a09060804080909040501060803042c040f06050c071421040b0a0813061b03050105060304120509010c0615030302120307090b0d09020d08030f06180a0213030606 82
    0x2a45000645482003e921000e62710051806107440c0e2114245a174071080d8610038078500900c03c03e969008078050210a60000c4000c2408008580c3d407640e544403202d4030311311206440b225440120786040408010002514030942d48203008a8092406540c1c800c001d1402803c1e00a50784000d0000400041c2c06e1594500c007141100c0050040714807046502d85180d0003650b0825104a003800100240301141060f49c102e07000d1801c11015582da00c400c800402000300402030a042e06050f040a0350074504004000e503103031156001d00c070b0380c0c5e2100b0074080c152100350340c014a80646202d0b0f00060720322640181101031414134100640074407076200c041c00d40b80001c160958400c00c0e12410000c00da01081984401070f11010100d00714603040c44098a0b0140318441c1039842c0200080c894001000b03a1b00c41d10b00b06034001c1000920380d0050816024a4004079944960068004081102b5240001c20b54159688852a2010700d99450f01108080d40200765a00400d051803c008000110b02c1d0284070007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 572630764 1250 572629514 572629523
    0x9170a1b08070b0d180809091303050d0902040e0625020109110d060f0525020109120f1b1505070509090606130b0c030909060a0e010e040f0b180f011a0904020307050d 73
    0x1181c110f541f003044801a006025811000c03003207503142c0000f0790080f041d0307070044440031000074001286001080281015201c051158040c64080140020b001155a04102100300c101007003104031074002c2e4200c038903c140c041c0c490742c49030340300400901c0c7c01401d40342080e1044401091000c202000001035030f00540e650580e0b02070b43c6036002d1408504525501030040c040c4000e1110307281c1d0361038007817103080a154404100407070b800842c1807140c0102400c02340e05801c0d032800c412110a9080130340140b141c041003e01c425003031034003140a03e8403030780941c0ca100754020080f1086449500402c101a88400f210310580321b0f4144002034100d20700e0001c0c01c40d0180c0038003d540e4800a07078042150709080184503500c645000c0000b0702c8503041141c42641503c00c024150030454523a403c0c242040c0c0180340c00202501c000c5030401c00f05560703450b40b00352488414400c8502902c401100700c4d003600c0d00c40745803060f10b112000c00c0480c145060b04000740c0050000d025500030310303150808102d1105035088280c6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 572632014 1250 572630764 572630767
    0x3110d23210a080a0b010c0b040c030c12020631030c0f0b0f04060e010212071214030903251a1e010303050403080a09170a1b08070b0d1808 61
    0x10151251104005030245800078210b00d041c040301d00142250300c0191a0052443e541c54241c1200c0e40038030103201c0c01c59001407030380105142a1500e4900f44405000485040002400c0051352503455071f815000c0640c010070490030a09824100207050000010544000781071405c2106152214840d10b40618062140c0c0118581000c083d03000c0c09206900860034250100201c0b40812460340c141c406580130f13440c041c814503d42c000104c0c0391185040c5c80e440d41d0340c00020b52008000410110501075091a12085400c0406028a2401d400110340040f45a002040300d0004cd04c00e10342d5807200d0302803040d0304040000860f1a007c1500b40e088581501e0031055005100e042019503464145c15000340c8180301403036040d5500100140140e10009040f21404075180e58400e0003480480c0262065001c8030000d440440c1144d0342d21140c4c40c1068401600b03210041e40b20496013400301e4242c0f06800c009000c403c0c9001040c1699030310a804407420300b80c2e603140140369401412030710b540c0309020b0f40002c2d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 572633264 1250 572632014 572632033
    0x11090108150105030f0c010809010b130c030b1e2205070201051f0501090b030402010c050a03031d1b09060d080a050405101e030e030706231003110d23 66
    0x401e080407040e00082d11075400880380c01512000010341e1031032a00d003031070034800d80c0c0c4460140d64050007400a1440d0f0140c1083d07070840384111380350311914500d422a81d050001042000074801c400907403480143e131488045004d441a401d00b8404900c0004126061303c860f01038242e004822500159030300070042c0d449034103005210300180c4c0d44000140481c03a100844a24010020b4034541981c802e902c0405000720024080d07a0040d0140f000310b41c0c00c18152240d2601d1032400a0040c81c420004090b00249080001c0d07404600040500c180c0d2411a1010031021454042045000004003c2e5a00c100c4104e10303040011040c201401c4000140d4032855100d07400c1c0401c00c01181805888032041100000141082280f80007481207007200c2410000f55244500141608600c140a8082c2007117080c548112080e030204054401ba030704000c80c0b100119100c64288018104251201828840948400702d04502c3e0152409901c544208185d03000306080e003030a002c610390090010155500720103000c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 572634514 1250 572633264 572633293
    0x50d030e04230f010501090e0c1c110c07060801060e1813021305190c0206070f0315080303150603190f0b09070503040201090918030302070602043506130f11090108 72
    0x1c10001e41807411848c8924a810a040456400341c240d00340c1600c0d60b0600c40003d6604d290b0700c880d140300d0382c03102140da45040c1d0b0040559554207900c201000200d1f00800043d15a200302c0c4076a030038440c000c22041c0e101d0001400c10307503803ca020384500300c5860940f10802c01030b690018440b043c0300000c0d101084a00e41180b40801c44101c00e1410707507840d401c00c00041c000d1a400704056520442904003540c0c894034080e81240105801101e40401040361400400c03520b20000103144508503000703802c3c2010031001c09000082c08242c5200014141c0116150500645a0481c69103c0c406010014070902030700002002c2c48001d0314110701007a030000511041d0b5910444140250a1542d0b06008000c0038949000f50181e0b400f0f80503080583c00b06041040080c107404690050002c00100e849440c61080d488108404295107a043d840c0043d124464403600440c04500c1021201d900303040b0312a29855030303110000916003c40305010321500182c441d5413071a400341d028200c050700500c1004121001c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 572635764 1250 572634514 572634527
    0x31e010f080f030a0c0b091e030408011d0c27011508130201021b0604030602030702240c0406050c01020913052212210c0201021201050d030e04230f010501 68
    0x42c106180c10070418207002c40c0c0c111280385501c0d0740c0074401c0c038602d40e508202103051841e0015041d00a055120030400070000000103001901da401000f000141c80c1100400340c0c0c10742d45481d005158004036400c13407140ca40300c940500307085660440d00c40401b09501c0c0c91403c15509802440c4505010b500300c440d4103501c0303910039a0080401e400d9052841a07900040d58441025407140d03200080c17680c90000940307d0a059a0007160b0051082d0340300d04010740701944030222009050380c0384520082800c541c03042c1c011007a010b100c12044261419042c400e003100c06911440410b01c1c070707640030000c45080e5203440070224803000490a00003010300f0410382e1002814000c1c0c02921202915201c0403011031000ba04143c11488507040250800c00345684150000342072456901e040d6181108581e007803501034004065090010141003150ba803100100013000360a8040039002038040c501c0e80300c0d41c0c02c059001030303990180c05105030300b41506141003040ae1407046800008040d018801000705503000034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 572637014 1250 572635764 572635783
    0x51203090a060c1d18160c0219080c22020304030905030a03080a0605060a1725180b16060e0f0322050a0614090d08040305010c080703020313030302031e010f08 70
    0x1a0506010402e00011844031000a000ca170030f02c10805444490147c059121144100d60245c0381110b4400103802c510303d03210701417240040350b002d01c03000140c040c0340402c40d1a8911f02400030018401481c0324030070009410080041f0244651080041070310b40c0e00304042e1980070b210b80d580403142c0c41c00d1103903001500e24644c0014042c007414031900b038011f90442d0280a00e80d68441d0030401564035800c44001d2004880400c40304020889090800554881c1c41e0940030318441d61400c0b8690351390001c3c18603600c22a0054244411060650000940160004000e002c000f1045907078451542d111541598003200d8034040ba003980690306540c045a281c0008010081181d003140060710305000906401c410690850481000140a040907603d96503400ca03141d80180c20346880d2a02d07841c1c00c1e4000c22a00c901d44011540010008210b20311034000c0b00c1c41900c10f020b540d43c044240b603805074042d410150801055940c01107250041005916540b402003049000f603e604c1c0c0d1400308006d04001442 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 572638264 1250 572637014 572637019
    0x309030d110705042403030504090b010206040c060f03200d0e03042709060f0f050f0c090409061103070903030f0c0809090402010302070203011a030c090103051203090a060c1d 77
    0x2000e0350a1007280491001c2c1154000d0710301050404418078407040701001030401c000e1200b4298008030515600c0005001543da0075482013180d41d003880c006a9484408072001044014203d4050065501c2180c65158150f40e0b8107004c5182d000ca03503010900c445401c400e10414090104030009004040d0107100403016614001d546407a051a19006400c21150350308041703c0803554820220401d254444111140c00c080c08120301100c01008001030701c101e0211084a40c106004a90500c14002946004a00c0c8024032890081114144009055540c0c42138820340d41d502c02440c5c034100354400942c0709491640d1008801c0742903103000391101e004502041c2c20029540034810000b081841203401c94803045a4008056a0303e10048010b88500030340290194200341881c8400c2d0b40a00c4450780c0b011040381915849402c550521481c1d003403d02c8040c20341da00007400080c0840a200046800c0501031080d541140081e48841c0140e6003844419000101860300034070a1046400b928a4a48400c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 572639514 1250 572638264 572638277
    0xc0a05010615180f060e0307080a0b0105010e090f01061812080c01060b190e131802030c0f180907030b04050312060d03171f08240f0f0915090309030d 66
    0x18001044e0361074400340030710400e00100d003405d0301c0c581d82c0420842c0010328449003210040401864a803400d45420303c42c5c41e01080501121540758509131140c584100d81c00140d8907590381c42d100c0e003104c6a10107050743c00300010800d04040313000b0310544000d000301d40c052140e0660b60308021400500b11a001c1d4080c0b102c4410132b204141101c8907030304091091003182e14000f50500419400582800c071501e2a103181d01d40307460102c10040b1440c51240d9000c40c02240be80d81c1c03d2009505001a411140c4500b40e40080700020311010503140e641c0c1550400c8840048030015a22a80c50525004081d6400e541d141e102003202e2061400030280168485404c4d20020f03900c1419030b50140c824400c0c40e031101290291003001901304440b40103001c00789800030000941d0306640d03a03000ca44039200340030200e02c0c02034403040940020340e0481b4a03a0281503100c1400ca0b083d510903090030b040c1c80d8060030540190203641c0101e480d803000b09441c82d00413551000030716a0f030031000c0304051a220785a01e41c0f4050181 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 572640764 1250 572639514 572639519
    0x3140309030d210204060e01090b03010f0306020c0703020d1a15060904020309011410050108090706050712050904110408061623132c04080f0c0a0501061518 69
    0x1000325410110355010f08003140383c880c10301c009081c1e81e060503541103141407010400180155004001c0445048207072120008071351554161030407840240034081c50000039200810002e4011750050030303080b148805030f48505490f94002140e041d01803d007513501403d00c110700d4840300704409070f541e000449130740e11416540742d000c0407450303a0003240080d41c403d950200c0003d9080d102908030403440c9036010400082817905020310115041c4a00416001070840c0c00051a4800c0000d03801c0140c42c403c0d2103290910039541d440d5881d0402071b25028042000c140020300070391300c0343d001d90b040181d459000d950325982801d0070203141000041c0307601c0040070689850003155800004400c0d4036080207210804010304c2d0402c200703161007130041c128840284810300207011842c007003d814250ba00b10030106000080c1482c0c800000c101503e020308020010040308034050900401014204004c800ba10494446a00e9070380c05c4030302641c0407400c0201d40300d40d00d00e8600c0d0301034801e1403803558510345d00a4a60 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 572642014 1250 572640764 572640769
    0x70803031015080115020c100203030702010c03060f09090c0812030a0b03011e180206161a01031205090d150f0e0d2f030a020d0e1c02221503140309 65
    0x3c181324244c2c190f0214500c14000b54070a010904c4460005840a0440f10100900035669481120f2503030042d468250040380d400d120b4000c4a04a030030f850645142c103400c02c8842401800050320480744844801c60020385141c090041c844a222020300803501c0f4a00b000c03100b0152860721910134400c0e458000341c120000582e1268605107045150005600c00d4032105041c2080798907200603510410102d00da210f186106040450218441ea01c602c4181c074940359407106010007800000c0c0101d06910314a0621449900076003075400004000014401d900c3c9c440c10b0300da000b00c00340c00141540300d4144101100c8179010f188000340e071f580c0040c54007801014000382000c0b0019840701c2030042d20886a0300181115810141e0004160b00741c940d502419540a50744004252102c1c02280c40c800c0140054074003040e6103d18622411f151120045e425400c0011a000c01240b50010408175840d400303441100c1c0c4500c42c80301e1140a2601407035419810099010200d440030340c415035000700305058894 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 572643264 1250 572642014 572642027
    0x90703111f0810050a0b030405010e011506110316050d020d02120f09210307030908030406140c01060306020a020a05070e0405030a08090f030706140f0408031503030705070803031015 80
    0x42880d10304070031a51541e90f01c0b1180200d060340140e521a05644000c01c164680360300460007984242c00030400303001180e44150a03110040300340700c4500c0303942004104203401400008002000a800e0300e180c80d0b0418550030b808080d008082d10168425440344055580410180404c00c2d414002440b1588280511141c548070b20711218052942c0482c400c1c6050f00c90315108100b0083d010090b00300060401d030640d0f680e4200340d03c15070000f03400100005200e007021044500f9250b0f59511401400b0340310f0f0b51429294010b6007101010b40d070720f1000002054051000e0050285103502400400d941404c2c0b0a00d000e0807074000ca505c0c0340c0b18005000000d1b0000046400703c03291428003682c155103c00c0510709190381c001c80e040301e6000014105080180d1a07000754119442114078007040d4031048441d040c0c031700d411140100033510400204007001c107440702c10341c20f10000a044a1804155594503802c221130341d449144140e00110500951615840041002d012511407005015028400c000c202 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 572644514 1250 572643264 572643319
    0x91c05160b0418091e0c0b030f0c0702180108031c06080a0b040206040f08010b1309020d030e13110306091f060c030e041a040e0a0308010b2109070311 66
    0x60f01c8001035021014082500310310940d54001c0c1d0119603020345e040d042d2040c81101c00c070481c0d2882018101155411070301050b07a0203920a030780b490f042942d5440441c00164442c84059034004058403480ea181465050320321f029160b034001540e05d0720301e000201c812a0040410190320103080100912240c0d1001481c100c1054203c201c1c44815140c0d400401c0c0e0901c0786400403103018441235404255203a0540040b030500314141c0381c0c8160030807500d00000c122a543d41009511100545c2c40d4000710b80b1624039483d817004001c1c110741c204200d1703011300f030708541d0b0366042001c00e101e000c001c000c07091800004165000c1e0b560400d004000350903410001541a0381d000d00800c3c0458803007520305152260030312441d0f52034054010025841d41c2d0070064100140b1160141c0309070704004282c01c42c5103001c14665042541501c070905039900b0016544004c0d0407204440c445201d0010384c03003404c0800060301c01c1c000c02600006d00300050541c2000003261481103907060050020816603410b802440c22213a69 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 572645764 1250 572644514 572644529
    0x615060c170a050903120a0f0e06031303021e0105270631060213140f04180803070f0e030615010809010905010501090f050f040f031202091c05160b04 66
    0x599192400302503a07540138019500b5018400d24a2003040701e600c120040c900f000c0c40b51503040c2141d08201c011944802d9510081d500180140041406d46024151382c0f851103107e40103403450302c0082858504441e045244010710f5039101c6043c0400e01c0200b100102040091040601140d0340c040c001c07035a100c4001d000c03c103c0641c4240310b000203070700540d48801c540441d481000c40c868494140003001c1c1d00001102c210b403c1c040744001a080c900080b5030b83c0004c0d80a0701c0802c0d8115464100001040081c090000c25046003400c100088c503040001c5205a260b5154900440d899013001002c00b0329091500f1b0080c0c0c0b2010074000b40c0a040c6404a003200000d2070132158541e00d5a0800d0b015100d03104009040750b00f0300c000803e01c005141c00c08003104005c004100115600d400360202164016074010304600304000b0b0b21000300b81706014040449401c4900907141c00030903c04200c810500c00508441103031072504541c1017010a20034108180056056091014101503007074a46115030701c121300c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 572647014 1250 572645764 572645767
    0xd09200d15090b310c1202040b040608030a0206010e0411040c020a05010c050406020f0a02060301050f240a030c300908030c070c050a03030206040201080a180615060c17 74
    0x4003060440c0d0055010319902030341c8207003e0f003070014070351544002d6402c4401c2c007101c02d07194854010303509585040155030804090a4280d140038645a4101c90703012060b6049629160012111703101d9004036401071614070019952a4480c41000741011b606800c650899000e80091002044044c8841d04501804031000145180050b1040e40f4081213244024219404e010340d600b06550030030042c20850302c5c15026070320701c4e0f803a20451030307182c206000c0b000303601c00d13024070041c4803a080031300c219240c07a24041d01e8200006400700114103403000541c141e084000002805d414059850f020b81711001d0224104001c0301d000000301955101c041d01c0d24181804100ca4688140c1c4103144c105c0850513401c4112a60717607080c59003000c400b551000e101a03d100000c1d040c001018100348100f1800c49402d540604904d48841e8011248050080c04240296407286040d030b004505205401048078070420000540101110210a98039050380c01001030042c4102d200c4042080043c0b440d00c100c002d0b9607280d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 572648264 1250 572647014 572647043
    0xc080c030c0a1214160e01080130060b041401030f060b060d0f0603020f030f19020114030906040c210f1a04030c0c080606060f091201020d09200d 64
    0x4481c3c5607504441d400c0300340e0030044401801c0d08260100c5014031003841c00c40c25103e903481e0341921414010034000c0d0008224000401607101e00d0100945418200704800f40d200504e424880309003d805141031780c2d1103a454000f00000d2400344644d000711303030001801c11425071541e100c2080d003001d90900a4070160b1120000340c03103540c54008a079500240e2781c400b005003541c0451440700802d901e00049008450800c02c0401524000030078540783e0007840000d02102802049102c000b40e41c08004038107010090159988990500e005035116000d0301006100914050801c1e0f00b4140d690740c0100c3c1c000003100e9080c960310740f9003410040d5507500903450005003000e17403502c441c0440074003903507a01c03114642090000b0541e00800808040303003d6540d80c1c40f0325071201109030300d40381c0583e0b08a85c00941000108102a0920060a40040e00030b0880b00f22010200f007060036a448415551441961584120b007000780b480308004520640085031300201c0c00c0130000c00e5810541441c060a82220070101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 572649514 1250 572648264 572648267
    0xc12340f0305030a111c1808040302120705060f03160e030715110a05060405060a05091b18010b03071407050d0c1401060303050a0906110d18081f0c080c030c0a 70
    0x11284d945c030306100780d650868091a14204042d100749102020f08000701c0a103050000d0305c13201002d940017400d03580740c603166030f0802c844003550704220811170040722800126580c0b21009002400010080c503550b0745440104101102e65403a440d0080c0804e03070f5840c080313076240040c2e980c0c03c3c0ca0322400c1c428401007204c039054a81091411101440f84a0007881c04100040418018054ac0c440c0d411100c40d42c03030b08407040003900d03011151420580e01c244030007215522108000c0401440182910396400c45a10002407030603003d800c1801401c0d400030500541540c00f00001007200005203a81d824491380f942c0b40758881c2c1d505000030080107039540442092000d902d03807600200c40b8400080001d03c2d505d1801404c035400240c0340c0000301c0d41d01100003c420f405560740e071341c9030202c00029280412280c1c0b001c1d10242009a6012010800f0030404500c0c90003c10070702031100d001e030401800e201159072440302039890440c41d130f42c01c00c124041848410f50110080e240c002c1074220000d41c665421050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 572650764 1250 572649514 572649521
    0x10f1517060609040e013207050702010e030307060b1f050412050c03100f050c030c0901270b032e06110c0d11030d050405060f0c12340f0305030a 64
    0x780aa40549000001840c009055200d14043e6458240e036407c032042483c501d0781c3c0441e003410032072200f425450028941900c40d070018200c0510504206441d0031070580424959000240304450965a94010f603400f85172590203550004400800c1d040e03d00b05400005080d40582d118035852000500c001c8020000e0600140007005806403c94244205c00b2007600090070b00d000303030b45131401c2c5420302180405400c041140d11a007000c40f08140382c0b0240d9070045035090401c074030b00c4140c13100b50058180d0300624200081c0003004007103900c40c0c40303091103c1d422010741503190503172070130302c504c0300031004203031100c9042c5000c0319151300300021100c450300e603001e0902c810085e80c80c0d8400700c0340035210100040c20485410351001a0704590502c5000c1c0c0080d640d9101c0c900800b6403001081c4440e240840000d001010f86e61211800e0300d907100e1101d15001600d410000c01009d40c0ca4441c10721111035120700b0502950b680d264143c48440400d25210a05805c50240e0050104000000002c010740900d80 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 572652014 1250 572650764 572650777
    0x40c0507110d080c07240c0210030f050a020c010f090201090303081b0f04080f0a0809040f020408010e0d0f02010b0a09051f0303180812040902090a1d010f15170606 72
    0x188036513208141004241c845185002c0d03666203028034403070401078414151120712203506c03030340741c40300d44020079000c1045901c0002c0c42413041644410741c0c01d401d00b0b141d0003503900074480104050f03242c101d24040035007540c0619a900c25071600d02400790015070b0f4000480000c0b2030305420020515140e1080030501034070702e0801e060315040001003400314070a008000300b0071283d1f07020a0b41c1280c011060000e44501c2e05020250000a05000040003440c040e0300c1300d29222042e000041c50140d80d0f150b01408d41c1d03203c100c1491103401101d41d4185180d080125803e0110551000f080104190000034a802900780540c00d42241d40d040010070000c014410725907181f03600802440c8466491400600c50785924000f018890b51200307000400e21000100e030071800351035000c42e504180c1061041802500305c044042c0e400341000400156024001b11031180c1c441c901d004007041d960500c0104241e26140358044100140c43e5200c0c12440385c0d010b08410003083e540d6810281d2520b40b00005090b81c015407 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 572653264 1250 572652014 572652023
    0x16110706050c0a0c080703110909070512010e060a0f14090703030509040204052116080c24070b0a1406090412090b0c07150305010810090611040305030702040b040c0507110d 76
    0x130b8001080024000400c201181c1c80b81d586114141d0703191050025041003600c40714007980c03040d1810b2199251092504240c51855000050304c801c502300743c14a0324100391100e40d01c10390b4410901c0300c48003290140c842039410b107001c10060b0381884c54281d5a540a03520024007008000710760300f4044d40c0c864040701c0c0101002469898445205450306d00c00030030000c1d0703483d450300c22901c40c05050f1002032040000c90f8290005007880501e00b00c18030002e421910b80000d1040c1d00381c8404480020440d014104490103030080000500d03091740c00d5803c4500c9103500505c85805402000507990703d030316805912660101c18020202c414010036204a412500302100100f40420000320010000542401300d94000789800c00d0f81800714415012250203010700315442d0409000c81c101c0319401d0300035802d094420140003403801c40c03001c40e05c02e40d50410380049546410021b802d4007075180c94022040341e220225001c1004540444001d4254842d083c0b0080003030302e1032030020960343d503076400701741100c1e801 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 572654514 1250 572653264 572653283
    0xa0608040309030821090105060135010f031109190b0d0501020c01020a1b0201050f030405030c1204030b0a050f1321050918010305031c09061416110706050c0a 70
    0x400118400f44407100b2902c5e40d00ca6041c00001c02c40c49050103103078042c1b00c041e1521540325041e0000100080c41c40f42c900ca0031000803503801c076640c9a03020342ca40d0091080400c44031240e4190328000c0080f41c1e102d0501886154018244407840759440c0e40010740c9621000c0009005943c030003c903030021724218000e010341d40b01090003610040190010100c0e40483d688a180a600581051361102c0607550007900144040c0300002142a12000940c1c02c50b000360f0480303080c41c401184030361800365048004a003988011408108121a43c1a07042c0c000200b10000e100c1407516a42080e40388a00034064880400840c050000303105244482800c1c512104542e40e00c042c5007690040c000f41c3c80894200d020704420003a40b401044290442d070305072903121019528218de80c0c0c0740c1c001700744140d4082d20b96050b40c0740710303a200069040c0f06030001064120301b8003103a4a002c0d0f18403200300344d40701a04400d20007078a207049a004008074000c400d88890741006074a48003442146440e001c01c0203401400c08030fa = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 572655764 1250 572654514 572654527
    0x50c06190905060c0a0e04060b0d05090316151a0306040809190920030c0a08150907030f0509010204030507050d0303060b0403060207051b01020d0f30050603010b0a06080403090308 79
    0x6008001c00c0200c5e0245c545a50724120141440308983c070030702c104001c40009201130f2042d841680c1143e5040122075040385d0500e00c1040e00d4200340351038010215561003c4110309815012070340a100d00032180d03200781004002c5a1400719450f844006e000800e0303a4000200741411f5614a0b105802c688082c4040780180703070302c0e21028001008201000d02c444100070f0014000074030210200e0340305866400080d4241818080705841400000c2e08800807050009401c42d081e40b29030f26854400c1c800c5a4010074100c4007940c0341d02c201e48024001e04181d0b40100410320110b00c00064041c11a00242c0303103a0054032003420210014200c5401000c1d601304d0009002003440341c10b4020301840b501981c04c0d907040c444081550030303440080d2500940981c00030841c043d40b181c001c003034000040c8110704020540041c505030b0301e400e00d040c402d1402e005160310700034500103030064401c159020030305030b000b000400702080004814095070711440040140a00018082500c03074021000110b078400515070b296074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 572657014 1250 572655764 572655781
    0x114040f09050a180c03060b0301091406180609070302010809030c030a051305100806130609050c0a083d0f06050c0c04050420150d1506050c0619090506 67
    0x401550745880702e07414009520b90f0880d0212401d510700d076000f108082011b04d940c0e2050040e203610b0150340d6165680d0440400424284a4210310002000f806400e451409030f200310740981044035440480d0307120b40c0402034401d40000311501a603409091240f1155203942840d4518862152150720500020604e00c6625400002601c1d550707101014406069841d60140810380c01403a00e52400215520045a180c1c140604016640c2d004440c1c041040780d21000401c0a540e0155121900c44600103248442c059110340401e410800c0419400c2070403000d584103401c5000d42e100d520010281c2e05480e8000c450010b10f1a000070040c00320750050207039840c0c03006410f40d08440101c074a280508028603410303141600c502c5d0f20a0b5800142098900080710600c240c5084602c011500074a002180b004080904009416000c150440c0420a1080350b0b4643c0103180c0b01d0380c084011300c0f1091101e16000a13020640550094640c0f4841c103042e8000c8511001510484001400a0040c0d03418003a401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 572658264 1250 572657014 572657021
    0x50102030a11032a0f03030c0a0309031107030c1703040308070b07020f060a050106090e160503090309040e010506120a1115040306090c0503060c040608010e06010e0a080312060a06020c0114040f09 86
    0x44400c4c00a4039100c010810410f80c40344030841d1128001d603004c0005490f814001d80c0640481402490121211107000e07482918049441c0c01c240c800c1c0e581c929040001c0d000001b001a0408514000345092515580e00e0000074018610010101d20100d80094681ea20802901008112607000c442c0e042c1000d2038548000e100a00842e80085c1c091900070a0b0b00c1003201c100c0c1d00a0540150740034400603214022100d64002034032000c1280810850319607980d4450280d031240e900610000140703414844108138004801c015142001c0d00649000c07030104481989095030004c0644000130380c8006800f6103c03552081e508018050f81c41c1c03c41c15400e1008130708000080d180d00390101d503415242c1c5441d00459000700c2c4504e10000e40d00c500184000d070301a200712a00300c07030181084480c07850440000b580520680d000040c443e40042401d1301030301c0100710f00d04c1c2c0000080d500400c0c406d0600324000e44131003000c2c1d01035051000d10a400558088001c0444000300f2074901400714107520341c0700c501c0c007a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 572659514 1250 572658264 572658337
    0x22805030a0b04060608070c050f0a143013030204020d050718150e15120901060b070b01090911091602120f030609070203070209070e120601050102030a1103 69
    0x2001c2c0780000c1032845080c075218840aa0326a9100c3e803507a40d8526004503480381c103046044a0500030b0526261818404100069615100e0340d04c0c0348140c903130380b111a40b0f44102da1081d040182e9400010f00911005a44c0900b482c0204010789540c80965040c4420043c0480c1d000940080c0300240395072400c0c03c286d0210340507000765aa01e11564142e08090306a603412030041150f00305c00c019411401030b02944c1d400b4a41203025080510b00030b0030181002007074224524070108440160300f0409503403001c0c80f540018260072208142400215202c20031030550500510355030ba503a4043c28020b00c0002c5a00107034014009003141c1242c905182d540303101044881c041e00140c822055088070106410b02900c0c1c0c1e40101103203460442e07440504000054102420a0041d40800c001c00350160712801c444034803680080e21689480e401040501000c42c90076140c039030342da4020500502180e0f0b804002c4500e0665145003400840b0362929000b07040d07106250100703080310702e00401c5001e0102032050300001c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 572660764 1250 572659514 572659531
    0x5090105060d0b07031808030709150302180402030601032a0905040e0307120c0b10320f04020d020721020d1e030905060f04060b0d0506010902280503 66
    0x11a07120001880710142c88540010019000b54002500b0030380b00ea8840001d05c17844615040602000341c03036540d40c0b640107540001c002111a1000d0042c2c517070254258500302c0261030114544611000c02220302610300780322901c501e8000010441584c801d03040b808007665800c0140748070417103032410405071500088030800490606c10b00018a407400e44503d454200f521000b4520b80079036651928442080e60102405001d035045080700483c0d442c20001b8401e1140c0c0849a01b05401d001c408144074085644d001c4080d20140c03030300d040500b90140c4045030b91f1015074031650354144c9a000034001c0e00030b211004c0006480481c48030140800701d91001c10406139141c11001040c40c0400c100d031038030301000d030880206542242e41c111080422003030004160b810311b400510205e80b640c9050901001f540ca42010300809010b0005100d0148121211480b04a0703c82c4a0f200d2107950350342d00c0ea00140705000b1440d40c0852120b268140d035803240700b9119501c01f103440c40012140d0000d0110f810036034540300c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 572661870 1106 572660764 572660771
    0x160602250b060102070b1c0f0209041401030b060a1208071e05010b010906051305060d0b0306091005010b040614030a06032012030a0801120f0203070603050901 70
    0x8103401c0c45811040c0250904070002440c201c6960003403400d0001c00c2005061007420180100d104102c0d03200c005c18245000c0380071500030b004090940390018140782003004e001e250741031024140e0703219600890094070382e070061111103e401d00070b0130101c400c00c1c480b10b0003158644010b030104a00c01d109071220b5684224510f8030810358220100d99a0791954022499980c01c420154081c00c01ca04d00b42c1c0c02c1c0715a0a4101003175a405214643c014103001644a1002401d60810071a224000d0100c8610341480580070795540b00055250000502d40350012074000981012641100c003140c1d40c2e20f010b0428440401826030015001e00712956a03844000002051801901801c2c0c1801046500303002c0d030312007801f0150f40c04102210803030300204084900a50444d070018191241e84003100300301c0e071013480c0c00d00101c042800081c0d498890108000385040d40f607049184a042010000d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 572482014 572661870 := by
  have h0 := BRFrame.cov_init 572482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 572482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 572482014 ≤ n) (h2 : n < 572661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
