-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2725
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:33:21.328089+00:00
-- url     : https://prove2.me/submissions/26748cbd-9df8-4558-9b80-86e6a272593b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 489928057 ≤ n < 490107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 489929307 1250 489928057 489928093
    0x61d250e010513090b1026030304150209061c14130f060906020318060c04080309130f0203040f0b01090b0a030209060d020a060e13020c1e0307021c060c02 68
    0x44030025602034201e00d4808243d100140340341580186049641802d1000c0c0c900b0000745041998041e5850145102000d01c442d03604a5180d03c1004140e8820800100018080421507044c0f05d034555015040c0150132000a60701c0d000320241c41202c8010f0041170400d01b036503000326a0ba40b280140116a41d04101c401d201400c4454413002d42546100d021800800030030b50f00c03154105400100031503d908280344030410703640d107659070201f8a00c07484000c01c2c14001c01c43c04680803205000000d51030100d07014280720300c880c031780c00c040b500c203541e50f5128941c03041d503900043d44554070402c029102c2d15110724000040d10410303086aa082c524004000c1e0054540f0002e80b020703250110381c810600e0f981c2c4400070301000380c1540001d40080380c03640300144031900480400030244003151f01d1701c142c80050718464128014003100302580ea00c076401020300006124560486400356105032441d00301d00b500440c41d40b1200a018210b4152007554400c00c0c4000c40c450101007415070701c042d02d82c54850401d2264 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 489930557 1250 489929307 489929309
    0x152a0f02010f0e0d0602090909010c05090f0a050a08031210141e120c0102011410140109080d09050f0103020a02071e03150e0f150a09061d250e01 64
    0x10501641c1c00d80c0b05045809030003a00c3c40303010024181019415189851000f07508602143c9000b5144900855180c941c18052900d00c0c1c0b40581d207141c00c0100000c10000f40b00410070580c1d4000c0b083c1c4c000030550380c80b0403d061002e4400c040045664a50074201c040500e0b800400034410589400024441111120080190081e0469000c15a6588a590f003010140000c40f03541e48924841494104044080741a8400030402d030003c010500c40d08610726103040e01250040d051122640080c4034240c09180c03914054a410f02d81503451b683c0328048146014852001040410b0903034100300610715014844820242c0e0030300e03095040014041010f580c03105a030107900c12000f4180c1d960125006c403882c40000445e040003c40950051182e0070000510741762042180900411007020107041d000035039410310840c2c0305001500d5070383e01c2103440000e041407581294a40e46440d005401744420003140c0071406070301c00250091141103100090815004c554100c000381e0800301c2040001c2500a01c58 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 489931807 1250 489930557 489930559
    0x20909030c15011d1005030118020108011a0304171308071802040e060d020102030d020d020d050c12040f0501021216020f0c060d021e040b040e010509012d152a0f02 72
    0x464517155507a00d4403031380704140c001c1c607015842c0030300d46a420005075444115580c001e80310700219980785e25121206c49202640420099406c001040001d0003160b04401c600000200184c00c0c601c062401c002915002d900034800c5522583d030500114415025070701c1c2e0150880003c61805d0318020703070f4000031907000b440310388070340801c142180640e402401100c0d900c40c1c190780110b50b40e601c00440c010003504000d910158a5140c00c0000b515162840121014515500071000d036a6480303645402013194089001c580954080c0030202800380c41da10030302e0140d44400980e454005071500001d190000407480c07072000c0c0c0d00c111f4100300d145e11001c044995607002500091398500242510405d14099035603921800712000400154401026000e801621401018110b55036a540d003040f1204600380228800f49020310068590580400c508144030f002d1800f10a006999402c030080c00350b08026001e00c081101154900015425290448821000603a810310600c25070b4990504400c0302c10002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 489933057 1250 489931807 489931859
    0x1020313050d110a0602030d150b030609070c060204030605010312230706020c1501180b2d030a240e03070b0405070810020d05010e040b0c03070903020909030c1501 72
    0x34440043c0f40090a81006400301d0036403695241d000f541e0350b001201c2c0c041e08034940127003d024000072170842d031b00700c9440312419400c0d900e60400b04101c18002425100511161910240009040d400580002d60080c00006110b61541c104105003c402e543c0310b401f04101003074143c04c900400380100d40b03a00c500101541e02d45449140101c02440303a03a076841001d1061004c0507288807480b40906041e194501c50541003545254903d0781a40c000c8011680d105003516111079140f11125036004060340c03442611000c00e1603510110303040c4031407000c0071b844030800d011007030502c1207a080810b0002200c0960030840d0840d8824040d4680c014440014501301000000c641400002c0044102411080303051304c0224010100c010000d5008558a52101d420304000148094841160f0b61165030011030440443e511500b0b07c41c1d0a40c0000c00f52010b001e8410701c0031000d030702d50a000034458141d08004503a1b40911420441c075090040c00b5200136184494014020581c1d2030a000d2003040104820b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 489934307 1250 489933057 489933079
    0xb040c03150303080a1503060917070c0e0430030b030d0504030602030a0e07080a05120a0f0c06020f0a090e130f060f110a03090303060602191704171b0102031305 71
    0x452001b4102c1d4103080040300059100110a02c80b03180e20020700d0512441d15204d4070324010049a416001d086805800720815250820480651618460b030240c4150264586150604001e041030035104d042000610b01500d9400f0600d90540b1a0b41c0f4504411001081c000380703215001002c900c124000201021780110115100e010960828042e20400e0803c0d10000c0392211407140d51505d003054181e8071441070303901811928800740b08446251107207544a192400e08402d06841c12251a102102c200e81d003041030729903034103040c00904048007141c1d40701002685801041454414040c1540e61114900486a00053300d5003500c0309480d07078800c4020400f07040c10300b024030044c403c06401c0054860001070b041081a803544c042d540b2503200c2d40341008816101d008c101d036140814041f032050075907450083d0740030609408950059141e00c4030000e20f02912040c4c80c6103940f88481c3e0045440d8041e42c000d41c0311851000100c19804400e200450501e016082103a001105a00c80d282c020300203084 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 489935557 1250 489934307 489934321
    0x822050f1c15060803180108060901170f01020a020c01030b0402041401120207020301050112020915150c071502030c15040c03120e041103060111060415050601050d0c030b040c0315030308 82
    0x2000e03180d09800e240d0400c085075a80030341359102c0d0b12120a880c00c90110400804142d8015206070303004010181820910760f0030f01c0c010001c0344000c400c60700d04600c280310100e6185042400180802c828640c060260581014005410340b1114171419220300c0c01400b040c45040300345117515070740d1070b800d2030940780ea201c145041e10001d00c64210065011350a040020481c01d030a41880190907200b40d500b6202c2e542c541c0004540e4086500b0b100d07034010426104052049882c1024104c0a0116005d980c0030a551301846c11410030000c21800c09030300041180d240600041c421001c508940380710321201c5113000c0d0369a010240039408020080071100700c40c80003080c416030401410420250007001041100c0d1f80c003003503d17001180c803e030009010010b4040711100c042030060140303501c07902d11220482000322903405404004e10442c10040140942c045215442c01014103800c1c2a480c005014027081040c0825524044c209a051505120105101c5018021040100c035010300d04001181c41d542 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 489936807 1250 489935557 489935573
    0x40209011206120215030405060f09150f0a420305100e16030201140a0e03060106050408060f041e0503160803010f061704031b0822050f1c 61
    0x104280e146240b0700303240403d69500c0007641090a07802252804090310281c15030188030b00c01101d00402c40d0300103001040c3c0c85600c1e480c1450304843e10310240c403411a4161f01c509425542100c0e400c140350b840c4014001031804c68400c1a2421945140e095040d490358448400350014648003010004604003c1390004c0c2007e0038140041c643c001c0554400341140d048050282499107641e008a0007640655901c111001d00004100c0741d041c2c4170001c0b960b019801204c215000500341d001400a003080d00d69682d5414400140030b0900c0f80c9413251958140001185407000003006880c4c040c0380041808003188000104420f004542d50021401540900d803203400d42c0207400400300e007040003050000420000c40d010354180d4070840d103490354160381c801d811140f02030b01030407511490f407605000c180401d02c203c0790000b4002c6c541141c001681107550b101100d0b641f180309904a072404500081c948000c00d403c1d104001d0504a0b1540c603804030050026803003c4201e004030118071403106240d000c01c0135207 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 489938057 1250 489936807 489936827
    0xf0b0309030706050901090201020f0705130e0309061611040c090909150c0306050306060607020d120e130b010f080f010b0c0c0a0609050102070f142229030a1104020901 74
    0x1c41c000340100e0801d11540e0f8040c241f4054201e000d0f000e5101034001d40c03440052144103c400041400c00340340003d0700071400400740700506200070300081110390241d480d01d1008040350302c0280c1614000e079190f424003403000c816102c0038600c22810850070324140d40c1d00011107402c1e981000000034500d074443c500012040c2c16030700416026414400b91040460305684440103ca500340e0654080d540c0320000c00080c0d00c58224000d600c00000f8900d840800c0f024900d00746a100c140c205516210802c00c00294003044c1414104590b50f1185000703046946d000111030761742d106070706008040d0304203d604440c3c030301070500403008000d0001c01e41c8015030b4010420119041e202500840b8099251040184528164001e0382d02512810f032000420b5030800c501b40040380d0300e0001c9017000514000412000000034a004210500001826052004540304091100820a41c500d4021503c0d6a6524a10150404040c42a080b82da00c440c0400d0710012041d000003021603005a03520b81280040e1110541 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 489939307 1250 489938057 489938063
    0x10e0601020109050a0b060a06093605100f0501030c270302090906250e010302070c18090303061401020709090f080f28050a0305040804080a0f1101090f0b03090307 72
    0x2c58001780705201c0030f0525980102c005641401c90b240c1c4506050301c82c0355a510601450060038040030350841b8000800c04e4034001c102d1058900300345410800b00c1502c0e819545040c96501040040103410021821500141000c1c01d00340300b5149483e01c0a0003144003034892803012072110261103080c669003100390000e19070080c4121802d050000c0119a42d11044565400c803a60f5131246c05002004030442035170015040c0d4074907200009a81c0114040e40014404803801e600356a0080fa130240c00100401e010a00c90000060500031410020240e07a0b40e0f500140e100d00b0304092075405640c0c00300f02e2100783c40d81c0d6400802c40d0501e070300d80711241c1090350314080d059000101c1c0b40d45024907000001c010840b0558646000c4201c20402100004c0d660321303074040401c80c1044640c241078002d0304031544c071600410f00e60703003403d5407420580e040691400301103c184d46854100f00c20807031201462034180000b864800c040509102080010312075030301802a12010200c00144004410000c9841e06a8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 489940557 1250 489939307 489939313
    0x4050c04060608061009030c0b0a0e0913020906010318080f070803070f0e0a05130f06080102040b0408100e0a020909010e0109031106180c0f0102010e060103080a080a060e010e060102010905 83
    0xd502d42d03000b0902c08003034030388521860040605065582c49092281c0541e600060400c2c0e18a16001b41011154000c00ca414244000025506544d65a40100e144181c1c5444155400b030913151041000410340202a54141890940702d210000341c3d82d030b0f5640c24190b2004e00d495031030303030407103441c404034042d9040007040000004200104a0b51002c20184100b1854444080160500d0100601c601d03580c052107400c03030343e401982c2101e6492034024800c01e50f0b10703440001d1000d8a4040482c01c0e64459005400143d20004041001c00d0f001c012801e10001204410059900628585519011805030280c8114045030200380a00400c0d405a03001c0b2540d000200241d1080d031501420b14070005404024030701400300010701d5107801c1c00d05a0541d0140d20f01030f0228602182c2000340c034900c203580007411590381b200d00003101f41c42040407502a43c001c3c00c00c10340b5a81c22210040081400501161140b030908500300603003402000c003241076405d100101c62442c2d40b0306004034010f10350380d080644588 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 489941807 1250 489940557 489940559
    0x1c02040503010f1e0203240d0f030f0e0102060115080912031f06020d120c050906040f0905010b1801081b160506090a020d0212030708042c1e04050c0406 67
    0x11544d004031180030f42c5140d1401c43c003101380030100803804100c03103169600c41c0200c20050001d40640003a890450028800910013050b034840c0445607001d03401c101c0208070041d4449484642184d225804440248024500c641c18541c9880600003503c02e8401440000c202240b00d810b010302055403e041e010504903141c0c90043c1c4050244000d984207940d080c8140f80d408a007040c4046166600b41d49a9103c05461094040c40b400082c0080348074001009014003c8244640e20f09008200508002d4603280c075090030702a6100c1110f0060748841c03101c0c0c00030000e5402088050b96011513102090078000c40b81ea5440d82c1c00103078213140e112811800e04001807808401d00c041c80107501503600490032140303036680342018150380e1114294060740c000500e1080c2401413a101c9d003040040c1c1d11110036070b800e091042d50345504642190f002440160005100c0c03441c56240011050081460315041d0138a5090030310510340100307003010020032000b4105001a047c0f200030015000030a1300039100b00030072 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 489943057 1250 489941807 489941831
    0xf04150e0103060e040206031303110d0201050a0506090103170d02091002100b2b060e010203180d091401030c032904050901020403030906050706060e1612060b1c0204050301 76
    0x4144400d034035000c0391401c4408a0703840e0750200030030700c01e59010700418a90746510001c1822005040f81c11002c0100d418901c4504c1181807000380848201600042014100029507409a070707401850203029841840040001c5100d410340c00c511582d140354000e07036030300300925014081e1040002c103070f800850258001c080540e0001c3c0d80401c01005400800c07069400c0410020700c1202c0d0680142d09503d00c1c04061000c8140b03207400c0802c40e02c12200040c409694170566801c0e46c000320b8260f550864401004115284103010011038000c851400c0d803111030514070200200280c07a00c00ba410141d41e032004000c21406079001c0100403944480110309040441c0200090180c03000c18a8021414400840c101007014006c0d902980d44c56103641d0107160811000300c078aa0405a001c1e40c1054450000051047d80e0055050044428410741d842e040365000d07000c0c0c04406400f921001c141e01d0051f0800012920605135010000f2110004048600e0030865501030701450b00b00c0c0e54107500c0d0011610b08 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 489944307 1250 489943057 489943067
    0x60804031205010501210b0a0306090317090d0e010e0a0f081e0604020103150909030503010302010f1b151d071e03051002030406060b1c06050406060c080f0415 70
    0x81180300e6500d8100303800520040c1e0041d034000307208281c0855544150030122101001c02c0700b10512149070002441200100090080000c030b0703100307403a410380e0380c042407052580c0004d00641200d0700c41403100c030509281c0400d0b0f83d0780c070180c940e03102040340030781064036541c7c86081d015850179070003041030468980f1002002c0c07814070241b00301d40b601c1c452400b190501440004040c1d8140d504200901001c0e5603e40040d4046c1000d40f151a0f01c1b40038598012514840320710900400300d0103662241c0e125819480050044000d110b902001c0c01000d0002c1348175407000da400800040e900290740fa404020704503003640a06140340031a00c407030486070007510290600041020840c0d0400444440008503c0440303001041540000f030450b402402d5004034820701d40e001907401a12810b000074030280c3e110354180080d00620b80086000e581e1405401482c02c9a01030f04000e000d0032039003008554a040405407200544210090050001184ca0b0000c01400b400341c6d4000c000484000c00364038106180101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 489945557 1250 489944307 489944311
    0x110609060d0e011401080f03030f090316030e0a0506030903091e10113003090307020901090c0e100507300c0b01061e05130503070b0d0b0603070e061803070608 70
    0x4900d00c02d01340002000c0b040016810510001400603500e181c6035400301e004030b203100900b02e4503544410080350000741d90450013209040d000340d840d0040b961420342000941c22460f403016204200510500c401144084101c94a140c0c0850b06210b03807912003009030804540c0a20030650150340300000e2101207421402d08607016082d8000e03200d403071800c40604801c0c0074a445208080d00001e00402c44035190f64801550889514006c43c0d080c18600e81c00200c03000401d0300101e5903242c40e4640c0344a180c3d0015000d8102d1801102c1885100d981480003c08901039290042c00d6000041013841126114004090300c8000f600301c001140381040002412580800341d00310741c5111408000142c807032148241131650424907402c4035104071101c00c00c030f03495004100d44500072080c0c1d41000910380d800b00042c00007000d002501170303101d00941245404403440b88561a000c2c9404008128801c0c3e40140708011060086506548407400701c040241c400c680010031a81500c0703900000710351160010b402d00c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 489946807 1250 489945557 489945581
    0xa0c15060504050a0207030503161112092e1d04020309010b03060a020c0a02091e18070f08121b06090a0c06020c0d03031a06070804150c110609060d0e01 67
    0x4400f039102c1202c0c090880c42205406400103500b0710204e0f1004111212038100c840451915104160001c114035082c8500e0a05c03290940000060303042c2541444810910f185010701071541c2c5804101908299144d104142242001368415410f045512500514003082d24084c0c02103460b80b501c2d40c0054020010814035a2181c0702d030500082002185000320303903c100719140602500c2840340d081c0b151a0308043c0c41390034482c0a0002c8106140100aa0036210300d075600000c8031004c1202c00351904004054201702d40c0205440c10500541e200025855540c441100200c0e40d6588c4c02c0b203903aa00d000340c885142d0014001e00c01403010301c1d100007d599240328029030a86540d1a640e4000b43e035201d100645594006541c3c8900f000803030b009901c040b06c81540445540a0800c1010000c2c400c1d0703100810846000d80081014401c1503000901030f40245400c0c01c02c200c03042c2180e01e80d0114400c1c0041d0f034522038000050b5408a64071140144c8030203c00120040c0114540c0502e454080c00001d1452 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 489948057 1250 489946807 489946811
    0x1060e0606070f060b0103090807230111040b0304051c020105060f0a060f080603030c010e0f12030108070308070c051e1504050f09060d0c0611190206040b0a0c15060504 74
    0x8585240341003000c40b40060750003200070200d520642d5510000c0c0014401d2541070561703c0c220100412134101c01814618440c05e241e02080c0d20240c00c03291951088810018903a140c055a194036000c20070499040d85c070310903031030750b100c1d541ea2401390f180680c841c0111f0003e5103135004440001c1d405401a42c090182114843c082c09416401e0060003801ea204660000d18444604a0300502940709203802031030150503079103041a160715507400c0d603100c003100c01c1707040e44444181c05082c4400e0205804001c4440280c91655141c2035156565901c54040544100800207140c400c00c1200602c000051801421001070304640c50100f80807009000303136140c010301c05d2207035952150582404403419550001c007403050800048040c0a11100000e20840e049030712080e81d04d020071800c14004000b02034036500d5400f10003414403824200340700a41c1c451079080c038145480005940b2481030f1010b0703a01c88086542ca03491100412501e0f40883c100150036405849029000d00c1a00d80001c01910016181 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 489949307 1250 489948057 489948061
    0xc05190b010f06050901080406020a0c170c0f0c0901030b090703060c09080f150c0d06090e1e01050c070828120e1209090c07081305041103040f0b0712090501060e 71
    0x3003503a180c485d001e000d42c0060b401030000740008850398041c0440380c0c0c50b80ba25050154542d40d542000400d07000025900000200b481103054000304605810a070200c4060710302d4021050200c0c03144441030200808603030f4800002590603608000e800010754000e00103118150035043c01a00350681c82c00b03122160b008440208400c040300084443c4250038200a41a007aa00d8012555850b0801c103404100e80e0f441d0707080010940210b00030300074101000c03c068402d5900680c0c407580c817400d0410032201e03540d04000400c90400050803d03940c400da084a0581d0390354558100d010542041640304a072500140700c0030001013580031038984007210903d83c04001c8864511b030540e603a041c1801541216100420500c00036080118040e9007200c107002c50181000060f80d1028030b113800440041c403c1115821007040744d49007030702801044808560482d440c50400c5d0b00c80b40070960380c101c0041c00e6408002e020800c2e903481140f105001400403c0c1c20442c1c90ba052070400c1c01f0340858403c40c2c1c110100400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 489950557 1250 489949307 489949319
    0x14030106090f1d0a0c090b070c1d0903030a320718080309060702030106080a030c02090703020301050108060f0a2d050103061d13062f0f07030c05190b010f 68
    0x103080f141c2c605142c07008000b2582c846a080c006440300e0800b0b04100081c0c800b00184841121000d400480d119400024205040825002c180742400ca400c9020360900e100344440030f8404000c07643c10841c07981000c50b90501800c0d014908041003c0c0d108400b40c1c0101c10003c2451030592014001c0d511640da1940c1c0c0881100c02507110902c80c045d100c140e42003082844c4c540d192203401407414038400340001c10020350741d0724040d080c41e48900c000d80106840003034400840c83e01070240c0e5400b003d141421400c5504100008250300401082c01d800360a215080da8410355a00030f2020041170881c0320000c08001c1c403901c40c010380400340c60444000c1d00b0b0f1040442c596000380915026281c0e009105907451481d4a040c401200d805803d04508203010b1040602045850080040800f0740c0074541040508514401460845068070040e90120a101410b40540204101c03015541c051921400380e1400d810315900f0195440382d0100c150135002d1030501002000b0244ca412110000b10008400c1c0d6031308 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 489951807 1250 489950557 489950579
    0x1106071119050a06230f0703020715080117160b090109050d08090d080f0703030e0c010207030c050411040e0a050603150c0304080c0c0a030b011e0e04110114030106090f 74
    0x2000301c0e640304080c00d5090000380e228051320310075655005400e0017809228100258a5409000300c1a030511000985038140b64040210034024000da00c00d01c18004c01c40000248000f40600846040b00500368500100c19420002d24040581404050200035601c80c1220190783c000e10321140800e0080000090358540b054040354441d400840140c40d003c0b00800300241803038080340464001c0420700c02d56403808420006400e0302846a1000602285015500c0f407030300d003541c1c0030141154000e40b010320018802468540480c0c0701610b002c5803110b414504004507000c0c40e0000e22102c030140c41007045400b019000940640001d40c20b440c600e10b10010082b060200440e00301d21558070402c04240040c007400010141c030191082034484104074040000e0040a2980c400d403401144a07005100c4000c0000c2401401103244800ca9a1301d442c105014000f104001d0020700710200307407000d0b4020383e40a51300b43c03881e0205100d00310b9507a41e11000081e00000b25402803038080c01c2da4001c00304092440c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 489953057 1250 489951807 489951809
    0x317100519050f010302030718320f040c05070618170a0e01080711031c050601020f0c091e10080c0f03031608040f03030207081c1403041106071119 65
    0x42c0c100f408403083e41005502952001e8501c070104582c407440118898001d49224003d4a0f100c00003551003003404016011196890000c011071072202c0c04041841d41e00c016505852560503035001c40e0041c0214001c0d240390050303041c00350555050210948280f00402d52180c41c03140304110300d4180350418014003031b450269650640100c0c16041031f80ca60781d801500003ea0019881c5000b031040300343c0d152514195089404051480444515011610701710303401010b900c04820b01c000c4c50648414000260707200b58000c0f0712402a080c0801042c1b0025502125541002003141d00d01007034100364018102080291041e1411400f440c0405200782c6807006042c10f0315003000b001103041600d00d8803c0070607422002c4040b22110300c1040001800c2c1c4684541600440c082c5c4c000e41481c610b820303980341c01d1a403071104440f0521174a40c5441d03896500b0100b120034440d40c140c6c0c101d8403075039607280c00200460103081040e444079001c20b05208001100007070310740c40c12041c0d404001c0082804101401c030040c2d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 489954307 1250 489953057 489953059
    0x807030b0a02030903070c03050616020c0303040603020706060e0403020f070906031709032d120a0c031101090204020706020a02010b091515070f2a06050412031710051905 75
    0x840030119800c076426030095a00b005100058034544041a40c40d540000050380c02158a07030800c0d410450b540890060824900e4504d00140014010305400a07071a403066001d45420b0542c0807a140e024030030f45034000d50143c1450710240c000c5040a0038080c1d6a181c12000003015407007040408a4041014021101100c0d885801111509012803015203282c11016001d6058401d00c806010181205642901c40702e911220880381c507042d100c2f0311820b261040d004040e4603002080140045588035843d40d2881d6014a09250080d980ca01c00078007610031b10310007a40c032174004a0780c0c6040c0001035008005210054008100c07101004082c0840050304032180720024064241d1058035041194121308004070303400d401307840c00c1610350740c01d0000901020260f40000d011107035010b0b000d01600f00880001c4250056800d1245412801402441a8004c1083d44400103070000d00f010301803010b201d1205508000742007a8502280b4882e025040c910404e4817800f51481008011007540c4442404da444c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 489955557 1250 489954307 489954323
    0x50a090e030a0e0310050415060f0b090405090f070b04170604030207060e0126060102010b0316030318150806040b0a080c10110d0e01020105070549020c07080703 71
    0x40b604003a070b0129441c0c00b0081e05405807030084d07805000b4612440c1d200fa41715280290f007100960000e002146c04a821429401d480c118061040c4c6560070b055884c1c00e101250049500d940700400607080c0100f80c0c0c2c854101d440b4100000c12002500000b420640c0d00580c01c01c100913a101807250b98a02040d0380260240e0050070003800041e1141c074130415180c006040c90504200d804203511040315801c00c0840300d42d10500c0501580d5a428042c0700e0205200b2001018107404003c0c0c05100c52401e4032008040c8078540c82c160341108030701c07003150004107004a540c00d40351420070f40280c60180204e5129201d02d103081d0791080300317260041215059907079510040c480c4000360400d010020000d484960240618124019004642003181c01c0c09005540d80d8050800c1089001909440c4c0c00752801c0c00740705084c0310803c01d4507c7d45401c0180e1b04d600c044000d101300da20103009054030a4616108950342a81d03550703403030000342c150000d00d0301401c50740031242e55590306c0d2030464483e00207000040c4048 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 489956807 1250 489955557 489955567
    0x1a0c0d0305040209160201060b1606060e04080315010c0b09011d06010f1e0f080721110112110c0106080c120705090702030d021602010e0907080a0c1b0c050a090e03 72
    0x145c0c1c0989640340700a56800000b80c40c80e00d6240042107a08071407404100710205642c0350041114500582005100c4400c941c10241403075900e0700740ca03010003400c904a00541c900043c003a030780720b000c0a003105a00700000b040b09003045140c90380640403140c0f00d0f0078800d41800794107103581c00024115040340c05801a11030014102030346c2c0c0188088510803008002061200803d120310442c80f52001000c140b00104401850180e100800c070454141c141120f00c0342901b0304011030110b0134902d03060002460041c0c120f001c80c110340c00003842100c4101d80c2e0b03040040750a03011410150310510586080d1000ca07403c440700a8100070700ca07040c1c40d80ba0019a000a4010802411300d208841d41044160054a00b03040c0144e002900301e82080460b0300c0e114040041100665800a4202007042015030b80031255140c80c80c8054910b580c007400c0017071110742d100c03500318070302b440780310298103840410308904900500c506040c00340401e14051350740300380100f10300014030390483c1c464006081020380180d800c117 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 489958057 1250 489956807 489956821
    0x160b0c07060e0f12070c030b1e0a06031203020307050d060902180d020a0608040221100605010c030221120103060606030c171611060906040302070506090307030f0c1a0c0d0305040209 80
    0x980c0005e40103c0e00004000310101c00213400b1441207202e0319000e071342001a081c0040440000d458091700d000d00180c03524405001140428581030a40741c21800d025a80391a069800c56a030b1080c24001c0050500e0000c000c601000c041e0001c21101a40e1207540b19000f0f007030382c104000050784040c000e500803101203041007540d001d103422a51082c0011701c00c0c16001c003002c0200711845004020310301a03400007c80280a8940e03440360101821b0f0a00e8050400040c070ba8000e591903001c0203519210303070030300309440c5180c41314042250120f00072000719074210750752032401402501c40c501031360021a05182c0040819032290710000440701d4210780c01440c90f2503075041100d001c00801030200030401c4080100c03a00172000c000540c06019280000d00c010700d82402c00a040c4000303a00010f10510b410004920f0541d00090300341300f901d801c10a10400325085180482e40b01100740e002c4003054121a81070307000409a172015101100c00c00042d929100d40e484c50840807940101d80c0207501c00c40c0306c0003040302d07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 489959307 1250 489958057 489958093
    0x70f09140105041a2a120922020c030f0705060703020c07290403030804020a0803390a0f0308061941010212030108070506160b0c07060e0f 61
    0x80d00c0e00c20420301c1c981121500c0c0e0351207441894202071008010301040c468111020410a06e10089100c03115040031103102c0002d252021141c0788041580e4000310741440382600340d0488140e110050100c80d9101d1051000040310b130010441560207018200014829501034000c449480040a010300041814000320121001c0729806095808140815114603c4c035200700a00c051070107a03c41c12500e19083c4100820074500b42c00400160b0003d0003400e0241c80c0c021f010310254480f013030582802401031140b00700e0724504024400310b07510541c003c1400780200c01c19521070480c0240c0c1e580e41d180da40c00c000e0103400c240c80c402200b8070103146d18080081c0d20820000700c035500c0100548034081c080e0001101c0e01d0b4413140725626010401c0c8001c0d60160340c2c04009081e941045d40038841c0c00d640c508801c2c10f840b010580300b105d010740400a03c599003101d0710181c20301c035640c1c00030fa08205410001100407075038124100499001e4604550011800c1000403d480c21800c08402001c80504601003840 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 489960557 1250 489959307 489959339
    0x6200609120d1401140f040c020706110f070303080106080903090102030d02031e04050102250b2217270d1b030212010b01030c0c0506010e1b03070f0914010504 70
    0x6903041e0399940d81108100540b01c45402072043c1c1080a541703058483c10045000d010702421440b45143c50089034071070380c021510108886c5c541c11303c146108103070044c0c6800c1000f980d0030000c0a024090b804001c15400c00d0354503043c0c40f05581c58403000d55817401502c3e0780e1310481900601680c0300b4048000401416001035904c02c0502d6000c4503994009171000f00706610655003100e20f6500811103c594031888140310200300900308212081400d5030b01e54000303071f48010340401f03e02c0559080c0c8075903d900722a09012000e034011018070001c60319030700031100344d0050351603100c422050301d0402c003244040c070700340c2c09103020000c04881c0d0b554071640d540540111504500b80031704136881400000369513040c0e041c80c1002c07078030360020456210a41c001401c0707990b000e4031441400014210580421382c0024000d054032550b0101c0011034640c02e0700201e01c103440c7d500685c4035000000c100b06082e0741c090041030b02030704c0903140c1c0e00019840710085444c01c8041c07941036001420600c420003050b480742401075 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 489961807 1250 489960557 489960577
    0x80901120e0c030d0905060904050604270506060607200415091406040c0f0516020a0b13170d030209040608010204060801180504080f0a0311040620060912 68
    0x18100544420424261001c00d44030501e6a0440004455241814003801104000c18904101000d0425000619602a00d0100340c0139541e43e40c0014699100d65110712000c0300c6000003020f0a460540c840c4224141c1c1c0c040841d424010311001c580349040c00c405030303100d00354402c1303580b0000d6074030b280c800980315408280c680d40719885a020044116002468502401c845800480c51640d454020302e180013000c0d103180d0080745445803080941f5407191000c0d0300700c501482c005603140f13500c881004800c46280000b9521014480000410742c0b1007100401d03400c00d1100c901c0c0c2c0d100d0783d00c1001c00d40541c0b0100b400703000c5800a13145110118420350080841040080000514540300d0403c9402ca070416005640850702000c0140101c009456a170385040700d02200622442c507181d40d41102d40c0c0034451956107000d9010503485903180c0607400403a020840c5550460b11b41ba80c901e0001c03d2400c18460303540743c49000f64940c800905012560300c2c4503400410007402c0422083d8a10110303503100070184 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 489963057 1250 489961807 489961817
    0x1e03020705060d020405010305010f0e0705131d0105040b181b0c1608071203050418180302060610020609060408071e0c0504050a0c0801050907020f010e010c09060203030112080901 79
    0x100c1d072965818090702035802c520070016259800e00300050f0032140c068022501c54400690f04010318a29006c1556000100d8980580c2304c01400c0100010b46580c2d0b0010701c030716030a000e40348044007006405d06048840c00c90302072000007000b0040c080c00300c0d0741304164800345400c80d002442141141042112103000408200e24100d05c00641c079040240c0aa044150b8044154040041480420590028191003a4501d040803441c0e940949284114030907500c1c0e00b0709000548445001c1580b040a60001d46420040c900c40c0c180340007501c42c8007c4170414480c030b284842d00c40003548001501031041001f88010b00c2c0a45a0707032910202900b0091046075030380307158010081101c01030f007c0b9218082c400c1d0740d0702c030f00340303043c4800c00069a20040546041e180303004c10401c055544801030340c1c1102c0c010756440c4016161000202e0500c80c940d079040d8559800c01c540c4203502501548800304981890b943d4a9687d61603a00c201d031a48400e1107005400341d180e2030040b021031000c200409a0078014140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 489964307 1250 489963057 489963059
    0x2031e06010216081c020f031204030504030605040609030315050112020d0e070b04032906010c0201030b3d05030403030f0615020a0c080c0307180b121b09041e030207 73
    0x51903c0d041041d8000e04826041507903508050f49410345054010040d41c00500040184040000c0da03078000e0f0b07030100c0e0f46071107038001040a040c0100c0490b000340d40c00040a01061a01c2e042c144050527500604400080c5440d4001c410070f5130300d13071182003030f80d00580d1103044034003041b072081020b034001410000f00140e46a241c0a4031500402003100113007140d101c0c55403a00e10750305148001c9807400354000418100d4405a148107012100300540c01032003402c244c0c10101460004030000c0c9484058039810011320806c00e1b40b203600205d020b040041c04800c3c6100388100112003c044400c0541100010440038000705001070b009400c4401d029010210004105984203504414405c0800701900075070400400700302400f0070408400c0107400020010000401d055012035540d82c1c05200d20803c01d4009070641c601121b294205030b014100041c520030404102201d2580c9580000d10b50415800d8102c180101c6030404000381c0c1d100c0c2d43c0000444590116044040111140d0301100303c00f18056400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 489965557 1250 489964307 489964333
    0x40803070f050c030a0b0105100c12030204051c020604030f290609130503030c1b01050703141012080711090703320412020f07060e0901060302031e060102 68
    0x10160503218003a05503180c0822450400714200b2540c4000c007400b941080c805600403c142c1c1c040e150440e071003681c2080f404450100c0449401020003002020b03101006244c01280c1e030316401800135180d040711883d440342c45003000103003162034034540250451070910080010500e16215441c240d0700440d201028040c106580040d400c0d81d55a010010109030400d000b10703401d14a041542c0440710040741000c1146907100c03183c2d00d0000038094040c2d20703400600003c1c1603d06500e0b140750740302c0d000024020750500c05c1025014204d00b1000800c4506441c0000304440089000141141d40b079143d61007060f001619402d032603a02400d019900240c11036203040c09a21854070b05c52040c1d5069600150614959040c1030440d200c2510400c11401e800c8a101a2a580300d02a0354201e940000500309140c030201d010390510700c0c85078540c4d250b401214070001d407480d003080161a0000d0100c1d00049240c0c0c031070506030100e01080d54920f09811003280c0c020080004205403a40020f0140115007004c03070411 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 489966807 1250 489965557 489965563
    0xc1a04081b01090b090102130b0901030212010b04050103111201030f0c0302211c020c0906040b210613030f030b010516140106081c140d0905060709050a0f14060408 72
    0x603070100e28681d501d50459052010464500f41c110b28030b00000d5140502c00b03124074403c5801801039110410001030110810f0780250b04603062882212100c05442d80d41b1034051a56030014030599000c28102180300e011014110308450182a9003209004a030b42162601ca00e5010300d5142190001d07404070001c009a80c40c0032400002a44d01000d46281c803184030011801c01c2c000d082102041c1100c0902c119510b6001b05924805001c1a600049207a60f008000f801820041c840690080300070b03c80301c030507281182c080d988410088800c9074440d40300c04545140c0c4103640d140180005540d190590b500e64400d40224500c0181492b11500746810300300004c070a4448808121401e02d050500c590403400f00380210001001010080c0c07004803502d05401030820004e0743e00804000308246031845000c03404d010b640c400294079404100c250024640a0380d80d04050310044046000c066000900c0e02d82107801c5030503980d040d5a4040c0c46858081c1440c5158061407409901c071702d0600000c80c02403410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 489968057 1250 489966807 489966847
    0x40b040303110c0303250507030e040b04060e04060e06010b04030f03141605150402010504051003020d1401030203010516140d0605280b0304020d0f0f0c060305090705010c1a0408 78
    0x102004d5a0b9070f04100040d564029801d1414081c444041e000c41c5450b15040320685407016090304040504221000024000f00304000701982d0051428401107a803943c40003009104500c600c1003040240007001480390354440902c41c2e080c8840341004140002a190f51803440d00d00c2c4a030900d059541d4a079107040100d90042d60001c2003d074418044281400340400c2250507030035501d0b80900b40c0782031940008209200b10700405000e868234101740c940c218420390440703640090441d420007140740c0c01078150451040a10003a4403e41c00d210118001e415200180b0510745030301d488035100760f120306c0454040c0b070300201c441c503102e5690348000140c141c885044500400c56006c0d030307070a4001401d0b841c012480c0f44a4100d0036403802c0c14030403c00117807102d500010311150000d801300b840b80000e00c4c00001c001507802000702070240c80100000d1070780c0c040d0481c42c040c0300014182d80c0c0300ea45031001140c3d0500690380181c045484c0e80d4000d600f200c03455089903005030003949510319113001079030313071459100c3c1d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 489969307 1250 489968057 489968077
    0x30c03060705130e1302010507051f0f0b06120f13020a0b040303200d03051b070c0306061703180102070b040f080c1f080c0d14010510030c08040b04030311 68
    0x382d0812a080b102e1521002d41841e80c00a601410041c21003140d1740022030000381844000a46242442020000102d0100000707607200c40c0c04148400280c040c1c400f02c5110040d4908042031105d00e031a2103010b40b21148110103c80350565103401d00a1240030000e44110044080b1401901c05600c4c1d200c0210003400c0100340352682d4074918640184500e80c1110342c910780c2400802c1c4240d0001c80803800c041d002c80321f4940858562110043d45514044180040380039071702c00500681001004500e00d4110f03405007104101d0307207554440c94520403840b64482041508200601c80000c440c4100020b0360000620480d6040c98031601c0503000c0b9400360300700c0035100038148010807000c201008805840c00c41030701e80d0040c165000c480c0380d030040c5e40c0c06046800c0c03001140003e20180d0391101a101d020900010070b000c3c2440c038084003030707890500b8003801d4084c3c072241e090381402a0182c090094000c48607980c0c1800ca60395070300e0b800c8005038040c00850415464046501c0c18401c0a0b010b4445165 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 489970557 1250 489969307 489969317
    0x30102040b0712030c050717040e070c0506070201020f0d09060f0203130501200a0318020a17060a0506060306010807030905030403061410080c01030e010f02030c09120c0a090902030c030607 83
    0x905403c0c2440704050b0302441c03104060402c42101d003400e610006841d80c0503403000801500001c501c2035411503019580051440011101c2000840e6605c07070382c0b0300440d900481c1681d04546426500b203090703125440b094a080b1008011052078104150b2020300c009000301d04c001f410280009210080c1ea00550f0b281c002907004012840c1840001c1c414942c26002000c82100c000c00d06054159050050980c500203142c0d550001c005285401d913050603c0303d0780144081c3d46d0f01d89801003031420441480314200e40d0f102da000020303251105441044d014000c020300041c25607403408011681c0140080c880020540c981c251403002030b8080000e8000b17540b203400040307a0480200b0242001200084c8a58020600003104214081c401b00d40140c1002003880c01068040401c800356000d071802d010325450f0b052002007080801304d5082d0142800301e10443d90820215524100c10b41d48079800f59070580c0c000381690081040454540c04a003180c0c0c4050f0a0b40c00700c190540c002410000100c071517a020903 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 489971807 1250 489970557 489970567
    0x30f03030615080f070503090f0f011b0306030203070e09120301140f010c0b0604150506040e0117030403030f031a060721051608161403091807020a02010c0809030102040b 75
    0xc0c81c040c030b0009180d2240b501c2215440e00c00307240200441c02a010500340316001001c02e50008041c003d622414608030f0894104441c9504183c1c000d0142040f40141030022020100328a440303401607004880c0c0040003031102500740fa401c031012600c0580110024814201900f03d03c507900d00246000b0005e5454003640d400d40d4100340f00840d09006001350421000411050004100c0d01d249038200388203403000120340c081e04480442c2d806164000e544d01940100d000075040340f941503058140c40c240340c410028180004500c40c0c0e24011400024080f5245000c00da010034400d07441510700e114016072100e00c0450b04000300740b46030301100c01920302000c280807214600311800b61000c040065803074441e04d4007030301100c2c19000080c1244003c0021800080f441410260341c822850042d0300b0104211810300c1c10b5000a03944e500c4201d44034004c5114072031a00041c0c04100740c09208000076009096810184d034011501d9040e0940e08031900b207000d121602070b685003403000c2e10160001840b410350b69 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 489973057 1250 489971807 489971819
    0xa03090e0601080103150504140f0303010807050906010503160513030807030305010e0112080702030f06010e011a07031d1807020a0b1f0b0d060305011439070606030f030306 76
    0x1240d8010a22418440440010000103088507100303940f02c1648040081e640e112460704640400300040034a4241c80383c00ae0030209007078080011030407a1054403c58007244d6980060010031a0708451150100b4400e0000035039070030034002c4030b0350440d605140542c613040c0403112001c02003d96800980740e10f10041404420181c00d84900303805440512071001c1e81d0361400c05288000204400c000344203110202d141000c42d102008000c51004200e0b09441c8a587c54420440a400091041c1c00c200440010103550b491000411216101d825a80f544038101c40326400b0a261803842c09181d4000902d246484024029000064010b1005030301500501d502c60801003041d0300054409603a00301395005ca1040368103140700550441d600400324940320071014900d1001001954030107400c550030101c24540701e042c2400c025210740c10085107141031190058610700800d514900b40c00e5101445602c0d0018284910042c086c0300b4450400407a006450b5540c903010034440910440100c2d44841041c440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 489974307 1250 489973057 489973079
    0xe150918091906110d0516181403100f020c0601060f050315120616030606050405090103060504021f020a14161a070c1509050303030907030b04060f09030804061a06090613080a0309 79
    0x2080700c0c07600d0103200c41e200310b030002340321101c40b4480e480030b1480c1100701d1209900c5c02d2202020100220904014035041e40034610042e6000e0241c02e50799000b03001c0041503580c0140d045440307071241d507034910317085503104d42d082e0042264503860581e0101007107926040c0000308020f683d2258140f901c2c0e81c01d41c4d62010343d0140070340d030281d04900180f01c0140010301c1562906608036044941100004c900c40d1200c0c00440c02c0d6600b021003103074044100c3d542e514030007034000170b41d038030050f00c00c0e80c0000c01c01c100e01044640300c801c02504110000380030721042003035880e00c06c01608204034a0301e006103841c1050703070f46101e0284907500029006140c0248020942c0d00100400c000f0002a0091440d528041201580f1440280402012001c28501040a102c0543d11003220a105001c00304012181800c01800c404011281102d088d824403e41d80700000342d03072164008184010346828204401d4000b040950340203040c50240004a0840010342a04100b1548000398001e84880350010706084200d04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 489975557 1250 489974307 489974341
    0x7060905010905090c0f04030c0e09060c0c0307060b010201020f04030c0509070c0b070810051012060504150308031905011701110306010e040c0e150918091906110d05 73
    0x2040c00b050200400c03640d00d03103603072095124025064135681c445440034018044e01030760f040500070800d8248042070100d06014601d00806030042100c00a6541038041e04942c458000080c005400a02514000034401d40101e012410305000140c00c10303098801c0004503401942c004c1c0c174106214642001581042c00c08990001a01e207060345400480e42c5481c0383c004000b80c2458108030015002070310030036201c8503010140c08001c1c02c102161005c0c1c5002483c2881c5021000301031450300c203000629191074440c90b55100d20380e0011a00742455070312106c0c0107400040100300510b00c195a000310b112168451a8042c5c42c0720175070159804e01496150303007120a0024040c1c0441d42c100b00703002c216a080800c0c1d101540c2c0444012904190000e0704a920591180c0d040341c01c45d031070861401c2c015039100e01031701007154256030b22000800c04140c905a203001c15189118550030040c240000c0d517503001c6140c205c15000b50702c0890201052504985658000c0e4154001166504140184055280407800c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 489976807 1250 489975557 489975559
    0xb0a030819031d03070201080c04120606172107021305040506091204050109170f0f0f1018060905030c120307030c1d091b1612140306040216080c07060905 68
    0x103400f940030b40c1c069654a2050800c082d05011060000806000e20a81101e010b45402120040154001e19200d405864a0f000341040c0021880003100307048400a241c90040038004282030402e031400070b400e42980d0280500f44c0c0c10902c0c130701c07071022010321501400e030085119100409140c42c0460348207042064a010408401000b00410040e41c0c5c2d00c044d00400b43c0318a003500410480000c001141b400500d003010400c1c9000340d4580d122941408036014044040b0741c2c00351100d0384408070001f8111250314100318a24030041c1300c04400319a49a00840d01944140101e034a0050801400e5181015071012346074540313000810070900a0f45801694003072812420b00700182501503900012000402c82000e0007182c800000400c92403a003a819056100e0407590325688503049446010a0003030004c042c0e81c3e10426100d4803901a100303044481170700401050300c81c216121402040069848146800b0101c0c0745a507080700840d07640303001001d11070848402001000e141000107041c0001550180b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 489978057 1250 489976807 489976841
    0x10603170903010b12061914090c0f030a1e02010c0b010f060909060b160c09180501061a0316021507050d06082e18050a050c0303090f01030b0a03081903 67
    0x44180060005100d50003c0c2c18030100301001c09503240f1039005001901e044208da0b0345074014040c0e0403d01160076a5000000d441d0302d00e03580090030030305a07940d24608000f00707288400c5ca40d07540e0403500000a0007255105140413800c0000c0790b00c840304850402e030807a01c5040b1041d4420004590020462002480008001d01483c0e2500f4801411405841c90a0f031400c0c0c108144031040005c10949040074150045041040e902d50303030600d031012040b40800703c07200d610300140824403000d052103804040c445128100e103156165040c031183c86440d91005800d5115000c254452a503c110150f4890a000c2c0c4e141a02c0325050102001956526030215402c0d400c01f80302c0c1c3c000d094401e182d020940b1500069401622810581e41001344184c40240e05401a860300082c100140800c20107011030084007250f4011015070300701500c1c0d10035004065031000c100b030300080055000e40c2050724140402004c0790380856894440b41d1540d40003404003041401c0100c1d12070301c100e80504c586005075004843e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 489979307 1250 489978057 489978079
    0x12050304090c140301030209060a08100e19120f0c05030d0219030c05250b0702030a0215010b03060111010e0a060c02010c0e0a030224070c2402060f09010603170903010b 74
    0x81050f1920060002a005900a0300003490b0394545c1d43c041001000a0000c44004d0380624581ca001011184078400290103814001d01c92611100807011949421040201c0340281d8a04182c070340e003551803017043c148211186180c011840900140c00c81200e10200580e4071441c02c400c14480818550b880001d0518007817038003a025034010b041d40d070207800800c0706c1c0e08203803c0d600403003100100403040103000b01182d0f000c104803943d020024000c150313010340860304003034404031a0b100d03011000d01030740480312814000030341e01e9889034850002c0c403041000001030010082d0344107400c14864101c01e9400325200c40349640015824800d41d290510185450070544040000048044001c5d2102030322940c006030108010076640d020018151001c1c0015030f5031501c10707140c014075001c40e40c03040e80040c0c002240031260f441603001007004130800c584c1c0901103d13640e0002c0041d052038050080c07111590b0343c26000c80040c000b00c8403c800c201c0141c102a40310550001018290307080302c3c45450207803003603441c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 489980557 1250 489979307 489979337
    0x80715050705060612010207080d02090405090714150408010507080105011d0109090e010b061c060f0b030708150a0603051f0b1207023f030601050a081012050304090c 73
    0x1007054020780c0c100c500740d040421032145d89001e40550030018240d5600000e00703c2d0842100d80c000c0441600a49050101d43d8491a455803603500764802c111040100c3e00c0c01d55002d14103038a144e4004004000201d09240d1150b10311421070340100da4480c00715580d031006007c2c1e581c200c5c48581320301c00c41d10072030808500080002000e1103128490802e0054890700102d040c82c1080d0040340c040b0742d01404003526880451021410488031990060440f8909100860408620031228050728103220302d0625540f1104000c444082e402841056624040110580b19a44241100340104034a560200b2a41000c0300c0035140d0031480c4130003100a010b401c508000b0484c6480a40b100850030301400078040d500d85c032090382400d0740450340c0c01c044403101c2004104c002120250104d140403c02100500260101c10307140a4030042c1c40d610b01243c0288074505980c2d11074140c044d0b004049503038080032907955080c40c0074a5032031038004403a140c1011a0610124410744990031254050307140021400c40c00c12 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 489981807 1250 489980557 489980563
    0x120e1207060905010c06092f010c0b06010e0a172a0d030c03050c01050a33050411090306070c02151c050604020c0708010213050f06191701080715050705 67
    0x1124650500c072031702d01d1070404d0003259881a0b80c2943c00c84550420760345041100721000c140318030045800000782d980d05200f94850740c21004069403240c1e03404520744034500150b07490800b00203440e502080c03450010817240107001054040d181c1e244000c120b81c0e40da00c0d440004070100341d0118040d101c1804550456541c403480c0c000600d54050502e80c90f243c0c818107049800344210050106d10f03600740410302107580c015901c08450398032502c26036079040a09c8101442c040f80c60030344040070002e5450040c03040303281070781c0000d03602640744190502d0201c402020900b0f00000b100c1c0c071004a02e41074500c900750308100da1411160117814500030300c0c1c000404826100c51040c0e03003c80b00d095654100107445522107904031901c45201200702d4440c20794030080e1a02030b40c005200203001c900000000205030401908911070b20740f00614060500e1907035426000800b8078254440100540c000750f07081c22400901415002c0e1a01c00007801c080f5060244041c2014142542041000740c10414035020802c04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 489983057 1250 489981807 489981809
    0x50a0809130b030c1915050310080c09070f021906060e1803030a27061505040b06340501050106020d0f0203070b090705030708010509060604060506041503020403120e12070609 77
    0xb101c00400d0b942c1c021110608000300c076005402d032011200c054202050b002409540300c0d1801c0d00d10301003010f072a1400107031200e50342f8030410b42004503280130070011401007039a640c440d41c0910465488000031103104108001002c1c0507600359a540c3d0061025001d403400281d40a504c1d856044809040c80400c0355030f81c40700600700e088644c2d450040b00c1d284070891052000e041d003518101030450b0403d04040009048c4000603140a1101880c006000d00b454040c002c0b80c00341c010107860501ca100080c03100380700c0d0700c1400d107490725140700f290040c0030301c1600306d00b020035000b0f6000290960601e08080d28044c04180d003c000d208451100c8181e41c0c1e4004122040709501c240420103d40310300035001d2410150b43c200e0742e41409003007400702e4602d405600039032041e540d070022210280c41e8403080c041140d55900469801c40004c200c103001140002c172401000c40b00742d2400500d4a03540e0345482c1c14400403e1804000101504a038024603e0041c1c110108107503000c01406580303107841d2001e412207050f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 489984307 1250 489983057 489983059
    0x6081603110411040e0703050601020f0706080c0f0a20030906090d150c022b020a08032802071a370207030207030c06050a1d0d050a0809130b030c 64
    0x126815070a1103403542d8020751120407203c00035a44030303515040e0003030b6401000c4880c07500192608001034503541c0b00091421512600d10081c0135210f0609204440e0fa9800508070404007004109810068250324024905540541ea44000042002c2d105041c442c2888188011562091045001c16501d0700110f0741e040c20222150811000d032131401078803184100032528005071500c060b486040b6000f054103110b1030300d4000414180074400d108108002490320340203006030300200c4140c0010b20040001d42d0048084020100035503401036070b52100c0c00e8201018802e8070f40101e8804200302550402c182d4500340505510a5460b00003443d801c0310f4400c85520300a01c1c10f84009a20403910030744c4140c42c40c2c10300360042d503980c00b42d401d01940e07c0036188022903076184021000036406100b90305980b030324605990340902c00491001541748082003001415448040c85411100050007040072346c02c4a44680e0b00291252400020043e4140341503411140c0f26003440352001c0250380120b203407125400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 489985557 1250 489984307 489984323
    0x806150d060b03011505030c010207031e03020a08070305121602151f0b0316140702042021060f030c040f0204050904050102031b0c0c090403030e010c110106081603 72
    0x149424039202a1400002260309540f03003014070016171824284581c161b80c000e80480d000400c00c0401281d490a0070301c00501503500010100c03258600e10801c6051060180c4100d031003c03503080e01c4d508050791110340300310b001c40c2c400600482c19020510341a5400346100606142d10001041d003c0e480f400c00c101420030100300380001a01c024865007000c41c007186180b45039000307180c0719111400c0c0780e4030940d915401904200201d044880c441c1810b54100c0651007605824008190301b8000500840000504080710207550809019101c41c054516000d640e020700c00c00005100e0302e51a0344c0c001501e1a40602d60032000c000390783c2c80024028000e450140da00180201404009000a0007140c00030ba0b441500c003018803062010540145000e00c1413450181c4e841000c00220b20072510034419961460340101c1207005442c50401051603000e4000d0401113005103c006449003100e61012240000c00c605d41003ca054040c02d2203424017030034060740101011000d41d010341c0b40c2c00318030f8031000744449 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 489986807 1250 489985557 489985579
    0x1060c0503070b07021c020a061a010c14070b0c0a030908030c0a0308100305070b04181806050a0b06040915090e061918150f090b0c0a0201062409080615 67
    0x17442007010341350b8040d00e00f00c80040103640c950002d444144480040e1800c030304141003002100d246081511001d48140c544070399165403699403920303064030108017054601480ca40000d141030580000c0034038603e400d0203001e0051f031070700e00a0202400c6400802c403135401070081016010f00081c42c0008580c05007000002075545035149540d00806400040242c09040030004910400c2c0024105a5010520050b03001200040040c1210403d041042d04282500f4206e008901705500c499001480040b020451100d2240428031715031090b402844074550351100000c12030550400f9402070006804d0a00c8a000208040f90750782d0405000c7d41c2d038078a201c1c00c241d03100c41c556034440c41c1142640300ca44200b0040d1800d090300c0d05000340250010311410700d40640d82400c200d1265124103a4003071801149a2130302240c80c005600f103800d040041d07659800b4082031101c0c0000c0b942c10030129402c02c00326502d505000017001c00c0050f510100c0c2c40e43c024814450f140400e2110f07015505000d4a403082c4807 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 489988057 1250 489986807 489986821
    0xe030318040b15120f0702150c070b040c050f090f0109050709080a030503010e01050103020702030714060c03070c05041107051209010c061505011e140d0605061603020601060c0503070b 81
    0x1000d200d4403065000c0f02c0400e030003146988080191210411a801c4000c45a40f5a0507104040004488420068100540ba407540c0c0900c0303000c4075001100d00f00c080f4200211175880416540c0283c0741920302d100c940108000526080c1c10040141c030042e00c0900ca1030a200560541c0340e80c4c18010007410f242c440c0f00055840b4403a10000c40280291f10489095041d60300380074102d940280074640741520464004150b55000e80200ca1801307038042e00520581e842c4c0110f48081c402c62110260780024100481d070183c90f8100050001103005401911607586040200000c807101c00c1d5401918003414070054000c50300c08107500740e08600d002c1c509540c550b02100100c440e1011820010030b118034010740403908023162811002510000e8035600d003945240785035050000319840030080007c05040800303006081e5640640a0010b8030b84000c18078640316000140b02da000000107881030f00614540c1030500d0f5041090b0350040600b801c02031460306160302c961791644140c0700045c2c240c81e6080081245 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 489989307 1250 489988057 489988061
    0xb102604050a083603030d1127040c0e10050a0e0414040506060a080c04091e2010080103020d0c051207080f06010b04031709031009120e03031804 64
    0xa01d503840545244e45591001d032003a084840848001d072001480d00700d2141070004040c4460703100350020000c5040c41d000c0600303140600340d45400c1b0303680144144007040003005088007240840191110b40c0240e42c1c1480b06010468800108900c100b11907011042015140c040e1b080d040501185410f40d40c40100f07041c1540c03000101c4c1581030f049860910340c1420032030300c2e040e02c40c0102e22a106840e08d68641c002000b02401c030034028209288c1051aa5140925159020000c1c90788249404002c0c54802e500c12142d118403001e0a82d500d0040d03140403a900302000f03046c0c0d2940c5100705c40c0002d8804040c140207040c4401400000d0281e04c045000f2010701828804810082c44010030302030f2101c81c071814058a412091080e139041c0d20851201d45800103021481e07034181da6210b82400c3c00c1038516250070000b1034100348041c40340d200400100500f0b13201070000c860b15040c402c03000305200321180350807080111054001000c20081c02c1c5540c00c10b503004003c681803500c484040004c40078401c070000d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 489990557 1250 489989307 489989323
    0x6010504060f0e19031e0b01091e060303090602240105011407150e010e03041a0f270f04150e0c130e09070f030b01060c080904020309010b10260405 65
    0xa4480705120003083c4c0540520a41e030b0a90f88919003050180c0300910810681c1c03400107000801c1411401d0040c081c4141c1d941c40302c26062601003201c0c03010f80520111a0845900b0b42090740040e205500502440d90100300400c02d0181e9409034800c210004e80e0511482501801050b0401a40ba80301c4c480500008040d07030001600803904003580049100d13444010104c42414603200d5081c10f04174840b214000c003d80c0e084404440b61481a00040d080c907510795130013418414510030062210100400302c1c070841b002c0c0f4680c0450110001e008030b100700200c505458950034412404c20007080d2900c07240c490f40208403a41d020012203251205060101d10f0f0184084500d00118002800219074038029a15130042000b030080c2c918182d11404883c2159010303000250440f1481d200400c40117106900300a4914080d5450b5410b00c600d01c40028180e92040d110b003d030030780d15101f00e003c452a0504500300403007040e0034800c2c0030b44140c220040300480f585031071407260580207000506001090040702 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 489991807 1250 489990557 489990559
    0x903032312010305070512030405060c010e0a050f12041d06040e030a082505030408030601020c0a0e07090b092101020c010203041a0708040f301106060906010504060f0e 74
    0x3078403450490581800240244000e56583c420030000103180e04001a0395074881c03503040003540c50b05041c0814001c659208080180880d035071405001c810701c60920089079090722074000303010f007940745274a150714051196031003880c007171000c0008015003c000c403611499045004400c001030394a02000a00a21f002e01030b082c0c40c1d0000083d4090420743c06420030707100c5d200c58502d40021441c030310344404108000c180f4000c003055041000c1004120048061a0301010500c1100c41818441000c180000c5d0790743d1048105600c498103019800da00140f81d1406491510142030034180d030701000a1035483c14405a014030656041250b0303511100390100c07003003d00c0003002503503203040c5441c1500d000f002401440d049005260045494603101c2d45034980100d400580d4280303001000d4460b04544801035000e0070070041001024a1080e440e10702e20840030787c268640134150120f0060381414510b00419181c07141ca030403810400240e81203026070b010786003546089409540604800e4950015003590700d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 489993057 1250 489991807 489991877
    0x609030207031b06090b040305060613060306020a030203070f020f060c0f0403060204060f0f0306060905090a290f090118020f0c0714011412150102010221090106080d090303 76
    0x20311038440d4254400c1142c4c00d07956011030301ca5903200d0f4a825030240b400000c1141d00b1000208001d4a44807502d0705210800c01c90015101e6907a6071003004a9200e06805804640c0200400100c4ca0b023003c0d0744480310300c160000d0080d00703104a5042c0c0c1c884a00401c0c400c0d41107000300c2c440001507514801c0d200a554406400c55540b511980f0103060f4041e0080094006641c600ca07007250f01744240280c408075a83c54942c12500c03030406041111354500244144809641c0d1603040220701000318000000708000211100082031400500c18405440c881d000c1c050480f41d4010049000c07110f412804100030100010f880355250250b03003007140320341c10b0f40108030311031501d0110707695070b0070710304d0840003c807d03211005140b014188207440c500504551043d1002c0c03901c005100c45203200380200c82044144001864851025801d0b400d405243c2c030140b488026034400c002090304240300e003c010709071450084c4985109950010800c840e03500009080101d42c00301215011a0b02c07008140882c005404 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 489994307 1250 489993057 489993083
    0xc061605030c06040219150309080c15010e011205070e0c2106010f030b370b070b22080c0712060e15060a030204110d0e0a150209010804060903020703 66
    0x40340340d565905032410b901c01e611b4901e408154000c1c440c1260708440c415480700380407400d11102540100340013401a55004420026001c0044081c044040301c81ca001007409415410f044000d04040700580012402c2c0c420703903d40d640400e600003011011500080c0c07480c003050342c0700005803105018403510520206441d02d28200078240060080d4480e100a136142d4100c1c4103500302c00c90903605411101c03600201030415601001551400e482c0380000440c3d008030000c0d021014103062195940d02c05802d1400c0850040100100c080c2c005411020f074071092440c0c44410000c0e001a40c1a1900082c00c0d00800035604852440074800140203240e4060301211600302e40c00c150f005001c103650b801c101d50042124210049850020740e6000302030103000c80484c3d605603400c0c00000c181e0341203154058042408000c0c82c5000c1e60007102d01640034000540046010380c945003810300184150a000345005000c252041e0340d02814295025400010100c0c82e640ba60a080e41000742a030009001d101184003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 489995557 1250 489994307 489994327
    0x506070c0b0604091a060a0b0f0c0f15060d050a05030711040c03050f16050405060301090902090a141b19031a060c0d05130902070c090b060c0c06160503 67
    0x20210324000d10151041d80e4a500c200b008a42e110b400c02800700303c100b02c40c403510320b40c0e45030304030b900140103000c6182198940031003612540102810301051030000804406a082c184182d20200a100000f865110100302d401d140d0042c00515280c0107640d079403c0c01d01845020801250203580000990f65282c1c100d08010565440714040c49000790f0414010480c51480780c0708080c030403512000c00300116100d40e4207481c00521541e80c2c0808102041c000800e89698a02c0214003c00200790002000c10851040c0320078004002d203440c0c4002c3c50100320441040740652000d910404c039288140151442c0c0d01682d205003d00c8040e9444150120300c110300741c5401d0703880440d840310502078014448510004002c99840b80300c4c01080326400055072800000d008102401000c00c1d0506524041030b00c0303400540890300811804d44240400c03480401c6004601d1103184550103042d2002481d2130ba0b4a170f031480c0c0d00c03501c200300940070f4880021450050090201000d14031603000c3d06032603031150259 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 489996807 1250 489995557 489995567
    0x304020604090c1206050904120806130e0618070b0a051303050a030305061504121203090213240b090d030509060c0a050f030702010804030c020d0c260c0f061303050607 74
    0xa113000070918600240032400c0d01c3c06040c614403665109004c015030502d80e690494906001414058004940112540340c001182c098908201a0322008000030f24015113040030703c031000c00d003090403034000700020701000521104440c1c1d0304006050903669803c1400000301802e01c198000760083c000c0100c2e01c402c06502d50440360084904440c44010b404103005180018852071085859030800d45c5040000075a604030401010986410002820b480729004542c60081c00d40e2003001c01d554801c58016068071524100b100d1110074454035088500340075078800b1504c100d41a89104900c1c9d0f0054900700341c4220121014544058102c3d0f8451000a044582c3c403070191008903240c0c091b0510350088458000280c40c2100d40580d00d92905840d02c2d201991400340044040c4d0704044004200801305810400b05d500411142f690402040508120b01c2c4000403802e01d46255500b06108180303050f81c4ea800b280741d010104403100e5986064140c200c50480c1d07907690000300b1030701403981040400d40d044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 489998057 1250 489996807 489996827
    0x40812090616051305010e04022505010501080601030201091e08010f060501020f03071e0c05150c0609060403021b03031c06180e030f0c0307140706020f0a11060304020604090c 77
    0x181210a00b200d01040a440781c0c000c0e2101c400d00004806010405503120300e02100301c448029000500e0407158004400c0145198420044540b0000003441c003000300900c601d500603c00e240c090042941164002410103a4034420502c04540032501c818031800058048801002510004c10420780c0c00701120028084c2445a54050b02451400c501c201d0000310032100c009600c61042c144040c1d0002084c0700d400c8400c1019940e1507041000800e2603107902c1d0b0104640c10308801266201c048031304e0003078a410001480a4481e0f0000707014040000d8000448140c00c001d40c0c000443c20103c00401709180d4081d003404401c10807101d60380041550201c4c0d01000c2903842100307071002a0400030304840e00351102e1021211555004000d09043c0b4850b00c0080d050450300c0000343c910749071a646480310100040c01141c005d5030030480302000b196404000f0700c242441c6820240460304110740314401205112030080f8004c46000002800310765a140c126000703401d0050307042190100c851401412601c0c2d07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 489999307 1250 489998057 489998071
    0x70c03030902310f05101502070801020406080a0506060c1e0114040b1503210702150705070906090c08011203112a0d080901030c0e03010609051603230408120906 71
    0x5031a04080f010144d501071240306006489900003080d02d0141041e1a103006000f900c81140500300001c50200c00030b00091000f040a5a111000c034104034034040c0c2101c1d80030f40181d12801082085940c07003003000c0b41000c1010149140c150448191507941405400034400d2205400c082c4001c1004001944c0741042c02205420483d00701e0382e20610505680d081089264030002d80105010200d103007400e00103003400c51014205e0a640120b06c14070001d0350b04140001c46083d08400310611101c0aa4440c0400038040e0044c107000010160001424040060040c442d400144502d2481454024152017152410410407038140041c1c06605585207a0001c0d65011500803a481684d024588241c02d410800e8215000900d0601030f20b00540041c20801d850005001101e5958181a90300f0b114100042101642c08901c0f842e2820f041d80164480130480414580742040807014546c1a096149070b01c2c080d0a6614031f552184d04241416018805600c400701c2c0b100800c00c6079484002c40c40c1401012 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 490000557 1250 489999307 489999311
    0x60f0a0b040314280f03120501080f0c010801120b090a0f0b010911030c030c0d06030501020a0302130e09071809053a0509060a0908250e070c0303090231 67
    0x6045000052001d241300c0c40382c0e01c0030010441d002055030005c4000015210b800e00301080b400643ea03420035200c0c26404040280c00407036840034082c070240411524840b00b4640344107198144154001c284c1039070003005e0840c0038400c1c005480d00c081003004e4404150000a41d524030905880e084041150034000d0140d001d09151120044105210035680586014082a400c1d0794984c40500b007550803801c203485141d6200ca4000001c100e080c0300800711020699005a81c0d03c8890b4126003800d8000d601032202c00040c4020041000c03030201e05042a588411914040c0b20803465460b8003814240703c000d080350244130200304091201c034400509408000c107440d11100e00030b0007980350440d510071462012840801c1000c6151800600801c51b6980a080c19000503880c2d8510629020400a2541c0d00491031122032903078070300043c41c0704001d00d90820305a00c980f424100007444c582228a00078185030b01d4011407000c65444044a03007400c410007018429031101b03030842c41d60220703c00d442800c56038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 490001807 1250 490000557 490000573
    0xf210f0b10080121061803031a06042303120c0a06051302130b21010f0608120901030c09030515011401030207020a0512070314010b0a1d060f0a0b040314 67
    0x1e4012a0228125846416100e859603030540034144654007034942100e0041c0d58860004101c940c8906403003283c3c0c002d03038001580182409160310b11010340207005228460501c003c000c034802d00c0c0002c0132031903840c0c1200c1c210f03a50b1000200b07141203144012184850030220700f0302c1c610400014101c280900402e005e001a440d0880703080c122600c9400041d40281111006046844058120815005024100c0c4d0146515142c40011800c45103408a40c16510340003c103143d2079841c000c01020b04518806800c071000c20444101a0b4400e880c45036040c03507219241842494001c0c03e0f154003d42d00300342542c1c582c0d500b111a82d552450240298001454a40d090020552281c4251811140d0160074040f1241c289003c00c50f40390b502980300d040341d205003034011000800401d051406045440004680005080308006061b403958204992003075030000150203d84207450342c136400040680702407100e51036007000700c0c0b02054590003036014040001000010000541201c484081443c001e550031030b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 490003057 1250 490001807 490001839
    0x3031b2109030e040507020c0315010f060207050603280c05130b04210503190819090803070e1206190e190311010b09160807030c0f210f0b 61
    0x440201401800140b0f80305a14510360905510241c0c020344d5500481e00101110340001e0b24191075141d01921008448004103c4005503000c010b0141820b40050040c0c107080034045091800000c2c8003c2400c80b00a5038000642281902244006030010051004194100c0007800c95403040190001e507101e1103030300103403c260320b030141c1c0c05031118a0683c1c1e0061010881410020103480e0381591070f404104240071100702d4810409411280f00d440c0d044241c600781050000c010a501c0c000c0c0d06c92403c001810002032001c0044a5008485051060012120f0004100c1d001581353c0180624851041481b1001140301601440d08442d646c00b401110258080c5070340341c82494000110800f0760b90000c1000a018000b85a90340112500000b11850150000703580300300181d4075078000c501c2030b01844400c0c940c0101015403220382824203100c2500c6001c80101004405400001002440340300c103002815440e01c48819245550f9007800340303840d61020300000700710318580b80b03210750f00c2400d4920304 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 490004307 1250 490003057 490003061
    0x82e0e090d02031902150103060e151e13060c03051012020d02040c1101020307050a110f070b0d0e0102030a0b030c01180504050c0c06090c030c010c020603060d03031b21 74
    0x29209950b01542c1441080c2d1104200c030310483c24554203600070359009000e0300c0c90035040c0074000c5001e020040ba101a08a16150908920041c680002643d980c01c0241100b2540964006245801c90281d480c1c2d031055028082c0c1c44d88420010111030500410303c0d90558580c02c00c0e402404e0301c12880c482d5503643d8082d05415008003a00039040306000c203564015142560107210112500e060240d003944000c3e580700e08a07801180e03480c020680100c1c42d0f0240d6603002e0141c940300c0d03610000408070142969a880d40d070b4502440390f056400c900082d03080384010242c00510766050080000d6440f4203008510101030305040390784a01a203d5045491420f6201d03a040c02d400060b010415070056040805000207090700502030b0005010410007071030303140002c101451161030502e025060105800c1c0405003444051508541003190044210016a070f45400716034204004403520001c40c0220300d0244d000c3d10104660100030004500d1551500790003125130200920701c0c490065889503403803d8801 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 490005557 1250 490004307 490004323
    0x5030a0c17030f16030f050708190212040e150604030b01090f02070804090504031409060d050402040902040c05030403090609061d0a09050a090b100b0703082e0e09 72
    0x820940d04000400c9200200d1800035560310340102a00d140101000d0b12000503400108000071045102844506242d804203050117021264505145010310303c1e21481701c85d00a50f1020f07541ca8010750f802d030003514000c20885140e115030821098445075908011084100c08403500c2070070300d40002c01200c0d5450200111410780342c0c0850704081c16400c000101c0001d140720705a0705c1d48190f0030803814021842520191000745003110010a55140c58035009103402086160150a5141406104216514801a5071514215001c00546a41c8034000580980200c84010350040d00e0f110038581455840320081d40310701d01a88400b00d029076102821201076046200f4000020000241540510b000c13000a0196085c000d04203400d01d62561301200889500380d4141a00654510b8400100500030f0015030f8440b40705810b8002041c40d20549000d03e01c01c4030300040030003039004c001401c030641403c0e0310048035220a2001280100c400032098450900f8080e0401100404000452020000442803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 490006807 1250 490005557 490005563
    0x50c1e0a0f08041b0b0903010e0703051b0406090905010b120a020109030807140f1014090601061407060f05060f0f152a03280c1214071b05030a 63
    0x254030008101141d40d64800342086901320103400759980c82c032900b0000c5101601210180582e01c1440300c003050300715903070990b01400d42c1d0044075080000c1352010441d03914450442c6003c403100803010002500408058200503415460f1103045824003e0540c440e0510071410b860070780c206c00420803541c0d55100f10744c0d00240080e140311340c14800501604090b04400388648104001c0076151059130b41403a44007186415943d010024202030700003980120301d010610040410702c0c07810111f15240d11040c05001384c2082c40712440011800034170b254121a492500700704c08020103e00b000c603900c0501806d4039140c1c460803299240098901d09101e40b010940f200400c440480000e40b0070101c1903810080301140011115003003085003d2520074a080d90620040146540700b82c0c400f0000e02c1a81d22000110070380e0700c46201000d5460300540c2080c021500a0301000074051030341402c45910300c10881040d0b40d010f01190070403c1004800010075540b000444032601c140e1900245540c81680c1f0f4409 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 490008057 1250 490006807 490006817
    0x140412140304020f0409060507030c140403080f0f04210201090e0f06010c0c080a030c0b180d0302070804120b060301060923060a05060f12010e01050109050919050c1e0a 74
    0x407800520301304803007280c0090040c0c00442c038485140c94840445904451440c0884c0e200e0180c508510340c400c01188255440301221740c05c0ca030841d21419030500230310301402c0700580c6c00100e050100e001801590010202c030320030540844d010128542d290408500b08902144114401180c0d000e0030150f010300c1083c0c0c0c1f059025203a51050b004603a403802d00b890503104c0307061101000c03c80800c1440000c40b942c0c084d840d81d8a412400b8944002591002000301c0421301c00d40c12580d81e0a03001180c42c02050165140158555510381400c00301c42c81141c0c440c0004c40d0f40f0a880108101024204070320910b0b00724020040180c1e1051144207031241c000c03012a10454582842c03522150f0052410340141000c0c0c0750a09568403203022940316400a11064007400d004209810b0706400d1306202405088900c089d0306d00742d450800003074245841070180510542c0240001800f4050741c48040c261540d0030441070100e4185400705950b164005070410300005450b060080210045504840100c03d031a80c1d6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 490009307 1250 490008057 490008061
    0x102070e040f0f0b070e0906040b0a0303050a022a030c01030b0a0909060608070b090a080c01020a080a0e0405040602040f08190b100b0a051b1c08090307061404121403 73
    0x180040b91031a01422107641c42d900381c40314085914482d940d0321803002ca8031159014800d6408000b500600100340ca413140781040306c40d07125500c07100d02c00300880c0d5050070029240d00041405070b041400f0810b11401c024403041c07001d070306868100c03070041c01c12005030155604440c1690044059454074500542c20070700c200d2080141c291a980f008282c503008490026030a500c03099a241462842d030302c0601080300100f030702480b03442d0080b801001442204002c20340c580c50000041d454914200000d41041000304000104034043c0041d0115980014010060391174207142034402034105014014400000c0f0502203500e82e0005a1030310f085100403081c520508955030f0b0f0300c81071b65000b000311560102c444030020349803008102030329680d401c90b00c1d2291500180c40d850440c60030030507a083c402da8448265100d01c1c000c4000000c41c05085071900f07044658899511614510411100815030b51518400030502e15183c3d03484c0b409035100d248825104c1c205c40c1c0040340c1e010008a500401000b003000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 490010557 1250 490009307 490009313
    0x1403070b1f0504020d090c0e280209030d09080d050418020702030703081305040b060702010509010e120d1106060a030309090e070b0304050102070c060323040212030a050a09050102070e04 82
    0x440764100740602000411015100d402040c2641c100030f40345113200f6103505594041142c080320b0480034000030601c28000e132034040e1716403031034045540172103002211104071541400340503011904456400b80849121703149850009162281511500038680502e01d09108447e2280085408560003201e00c0e02c1c03003c02118808000303521003a02240e00d440381c03c40010001d440c4201600c0c0000c0e5200b9010440e0389004244015152171a10451181e04208107401c0180e801405803000c0410070302e0428104008040072510300640305640c0c81b180e1085070940d0680a610113410b0720030500000a81d0030940f2035106100c01c000003804000c001c1183d122007401812900da010688648400b01103950071a035a1540328030540c0140c8003620f0f56500014a1028408000070007001040e203441c2c01c00c500300c5469165030140d40c04200d201c04200040c80454195514800865099480b40c0180c03541d0f0160150060500d0344840b0780070340800c040c1000051558004036041c030442c0c030030503400c101c1596aaa = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 490011807 1250 490010557 490010581
    0x513230d2f0a050706051801050a090902090a1a2203020102060609091603030507050615060912010b2e09080a08090d060c08010618030218190e0a1403070b 68
    0x100d030405051082d242d200010039420413483e0010002d1b522183e549070f084144000c0700034102c40140341880b03001c20441c130b68107600807408011a10160401604c804a01c4006030007503205030b000d08400c81c220640403440c00040002001200382501500c3c46258070004508245401c612002c0e0240c1c12007030004045051410420798045021b03c1600c000109058102141024a8005500269020a6034406c1200c108440d5801407001d0880305402c0080c0400504941301c0d5403040c0d400b4148812910000110075009140c441000420340100c1c0e4018090b080f403940480c0d0400400e4101600e0b4103c0b1807405100303801e080e110420090001030140b5101e40f00140c0c800550790382c000036208203400c0030800a1003410300168090740c07080c1c83c951404000524014026000c0601012031143c10001607440c0b040c44900707000e036040c1041e8669182c0c5411613820030304505000c2418141074032001d08110105001d42824411900300391070100c4070541a0f62030003040360003055084070102280240c4000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 490013057 1250 490011807 490011887
    0x3090304030f081306020c0d1b0b030112060c0c080f030403090e0f01060801060207120b04022103030406110315010305270c0306060415090513230d 65
    0x1501240d19140d41d99540c140c1844500c001511140d030089114190031806000d168020a040e10040c0002200800040d00d00880806c1c020300c00044104080e20001d81921040d0061190680082d165a13542c0c000c1e2500e5201c2c010100c880e10701e0030b860b5400c03c1c3d0242d0000100b03945c00881d4542400002d03810000b9540c0050000da05112141c0c00c000784000c01510010300c5920340d044490400d501d4044003170500c0d401a0007190564103d440180604030301c242d480700b81150484102e800c1915540003007600c0d40c400c00c400741da000c0380c541910502100000000c502492180710308200b100c100100001d000d01041d00d900038020200041610198400d411490700800b00404036558006903460b000b40020f05081c03001c201e6040714100343c2c920300d014480701d0342c4103405907001d04c02d20038030286d00c9240d00380c07900441d4840c5d669030000c252515044510407a50a510600c224104c0440341c40d1a62035002c0a000e0100d14441d02d409681c91300d100b0300b60f071104440ca0710862140441c420403a07440030080e03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 490014307 1250 490013057 490013071
    0x40b0112110a06110601080607020a08030a0f0203041b08010b09060603090f06150301060f0b07031d030a0b34030e010e0717070801060609050405042103051504050103021503 76
    0xca07806a015a510b846080d0000c01942c0ca401015600700d42ca0282400e83c160300c4199950481000c000702c182e00400c035440815400342c42a07540350366440c85907008240b00307456200040e03c00700c01c000400001d00300c0560500368114003441c0f02a81c60714203500382c2d442240b126402182d81004103406081000155070000341600a480500340c010702143d140103801c8a050400c64064110604c90f0700b420310500014110300a00445d8540c100761501c203140c81350440090400810401c1041c81921280707520a14000040130749a81d135100341401c54150380161010070300c102c030740a08a0000c0d07608005024002c684080c0200600800c1082540101080f0035200c0c0195240c0c0b0441d01d02c010180400c00c054000440400412004180210320b099046d82000005c0d030315010091040d2a0800d80344003c85204560104117030303503036180c050f005170140304610822901c0c1c071090040c91601074106610410315619025a0a06404100415904282b02c06908446151180b400802c00c4200540d40900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 490015557 1250 490014307 490014323
    0x90f01050714071104111e040b0a0f110f03040311030a05070302060921060117030a080103240f0606110d0507060207110303030705041409010303020606220c020106090c0305040b0112 80
    0x50000100e8150b44007260681909040001e81da0600c075001c0181f618002100d20000b810241403682203017241c4a01403401d814021803244292000d4401c004040080320f2407010740342516020041c85a49030024081100d046005c901e84910314100061000d81c090703044001841c00a145800303000190b40000f014940003004284181e0b003030702800100705007450559000b02015850402c241031380100301d805184454104001a95109500461040c1500e40200843c0540c034200c0c6200480194904a0b074288581420003856520b410f0740c0c0440212000e42c0c0390b4251690216422030f07201c0c2d03442910781011403405e02160b400f0442c2c69001d801010310405010310301401e5100040e1460300200c44040002d00001000c0c400940c00c0b5601c0c4000c218156008a86541150360194440c6c2c001055103008448000c0c1d115601d440d400e4007206200c4a120b420800b8810703c44000303000e021240100c00c10355042003503155005200388a0030b4440c5810a42c145103990034404290b1070050744013000ea0301c0384 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 490016807 1250 490015557 490015583
    0x3030e01021e07021009032a0e09030c160f0b18280e04020a050f0409020402040f0501020f0601080c060c2103011403070f090f02070c0e090f0105071407 67
    0xb060001500b108440403070115200c00c6140b04201034085440c0c00e002c200103892004000289070f012405940039070104403001c0c60f00100600724120425a409086a10110070030b0020424000c0028980500c0d40710603143c1c2603058280c078201d0000070b48a079158520011400300328146013600a00b82c00d000310304500d82410016030014411452110180d41101418105552007170f030301900760801009503425008880c54160001060b608036441124040e03110b082c0751850030750740c507400103407a03035801882152919129244540701100d980901405445150788441d42840b000400c01d040300c05580c0240440400441441243e802001c501002c03072240a15075281421018061074400390032004d40d80c1c0325850100000c0e180040b0440142c00f0ba00568002d000d01911000c0c0c80d000d813082410081303100e520680c0010000e10840c00007034240039041e00f010030800c0790840c155004d105244125451940c1d07400442d03089840907502c4801007580d01464002c0200e052010300401c41c040c03030b0040058 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 490018057 1250 490016807 490016827
    0x90e16060e060d180b0f0a09030e1e0a0e070306050102031222050604120f05071505100b0403080406031b021506040e0f0a0303060b0901020a0609050307021002010f0f0b090403030e0102 81
    0x100003490403031700000200d0030804403141040007294010304010040c010410542c0300500300f80c015820503401070712118501c11000c011341003850362100c0d001d85a6505181e5a60216011043c1510240006414181300046940c4000156000d01050100c054650740700c42000499400c2000c50b941850a4000300782808548140440f600c1140203400341c0b0145c800c00c0d0001041c412001a942d424000b060042d20041004824484800e41000b400040c086c1c4036141144080401c941c0007629540c0700080100070810b041c0060400c941703050300c09010400d070002ca00026034511034800c1006174456100b000c200d007040705c0b201e07400c480090400959901803030b118034280650759507003400740d41c490b903551402c15505219180041224580c400e00b070000d8000000d40b244080754010b0511600c844d50300c0e05021060044480480d0b005006d5020700320103413000380c042c1c611810700110071468030500188030402401400c2821800514a00081e659607905a0080841c1c00d401c1e40c0e41d40d824000740c460 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 490019307 1250 490018057 490018091
    0x902120a030503010302010816050316030608010906060801050609160807120603060e060c1314060906210a0b010c12200304170f071802090a090e16060e060d 69
    0x31140c02035030741075500d41c150300002d081c2e07450151409010320705074180b0070710243c3e014003a260451440040381c8044090036000714041c0199070000c0a80d946401003800c100185a4001021904a0f100a11065452901300f008950080b00d60100c4644000303509101305104560342a4480000d04150710b8000c400c0b8981d20480307003150800c4490035a543da2800545800704a8603038807d100340502450700600492140b0340710241d11804441a510619803200c660302c1c08196095881d000d88410b4072401c00007504080c00d111540c1100c404951240480c100f0302ea1760046031130340001a1200030503040c46540760802c0004102d415410087c00d002072902c1c00290a035400328031040d401c0115200c0341080c94140801e06c5445a01c0e501e54008006030716102408500001110aa00741004214000c10b00341c0019104030001194007469400000c6041d00d400c1d405000030205580071201020580d5a00c40c040e642e042c0901d01c0420b03400f108040191030701c08000d03c840a0003001c0407031184d18220600308 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 490020557 1250 490019307 490019323
    0x70212031216030e0a110d03110d02070e0106050403050327041a030d03020c0a0308042301050103110306090a02060c0a05070b0a02010c0f0e27070c0209130308010504090212 76
    0xb003181c02141030030400903454041c1052600182000d408400c0031035485140c51420751241a02420520881c441414000d51071406007000c401705540c83c0200d060402900c1d82c000f4042c8190501204c0c0011030003d02c91030130750b001e80380c0c0440218588407a9100480b4b0b04460b610000c03504040c414036000f0183c0b11409a1100d20744645005400c2c40b12410400d8102188902140304052050002d285041c6000079000c502d03c0e05400c1110842d01d40c0e0410103111000580c07245600c03001412008062581540000c2c100d0f4025882e502007602c08000305a1a01c01c1528405095405440d241c00903180000050418100d01021148105455641d160901107154030228900c075020507100071094081c000c01c01c44030818680304240381d82040d009044c0d21140211140103020211060784092041c100540c03200e5500741d005c030b03260714000350001d04020f1041012401151043c02084483e2310501c04000c01561540740d084403a801c010901005041031242680d000341800d5072041b01c8501406804 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 490021807 1250 490020557 490020571
    0xe0741220b042901030b030f060121050606091807090f0f0908030417280306150504050114131805010b0f070305090a0305030c160909080702120312 65
    0x850800d4003294039045560000d5418091410005616048040b103108811600c20b9040c0c0a080701c014400120000c108a0400c5134140c4280c20612a44e010001207180c1241c040c800e0004403c0c02c11521038400c00100c510003032451780104041906480d02111a0394840c00b048240540c0b40c07018020185030a8441d482400e940d5941c82d20310800d4106801400d000b420700360b80500c21031800746c3e514085448000c1c00030700403c0c402084a519100e0030742c1201d00c0c01c1e110382022003144619940d20003d103429520a0f8001c07902d000b04c0006c03559452803111160074466142c4500f464a05801901d0440c0301810541404070704006200040301c1c01c01d02c103405400141d00710906c100e81000003000b200d1068200114440c0300b403015070b404081142c01c03070b80d58541c940b42c600d40f074400e14408a03511141c5604000d101c0e0002040c006001203000424000c000740c21020090f0180c3d503803020034215888135401916112040112070054102901c881c009400c0450440780f070107070941340c0101e02145c10703140c0c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 490023057 1250 490021807 490021849
    0x1a040c03020901090b070f03080c09061201180c140702010210060f05010212030c0a050705030c06010e0a0c080c0d050c0f04060c0c090b01170919060e0741 68
    0x42c240950b800303804c80c0702911500b00c0e01031a0030610740f942c000c012003001000f0104070500d0001007001340d91005581c241440500066102c1c07505240c00080d0180c00d014040c0a0080130380d114101c40d6003030090036004480d545801c0c8a55a01661b802d21f16444100181c1c103500c1001e032040b40240e21803142c10001c240b1600300c0810582084002810480c00160f41610b04c8000d10a21104054560031690a11010b0400a507a0744c02480c1c11801c5005002011060707020b0b42000003240781700381c4002880303010030780c008209000c2e10fa00300b030340d03007aa003034a2504400f4003e101e41c0d148001c207680810303000100120142d0a042002c1040341544d80548c00907000111840d130940c0403c14805d0182d0082c0c542e494003440400701d0200001c041200d100310b500390007820030300814030101043c0044a0f21862450800d00782e40c0080c1000c5002d004200d0340014580305c0c2c22800a01c500340d6012407030352024003001d00360381d82e00302403d501d90808228002110321006c1240f0041345988640c00b240f5020448411 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 490024307 1250 490023057 490023067
    0xf041a12190f0c060503070f050a1103120a05130507030210022b090617061306090903050715051b18060c060403021e15100b2205060901121a040c0302 66
    0x90f03100301080c0d100f0011302c907040c0184001c407074000c01481c803030101c40d1034075540f285010901164030141c800500c07001400005010300802003400405889600043c1c1e0a208039140c2d82c0450014080000010b03180381c212100074001442c08180d0149010711610441c4c50007840310268641c03c84400000c54007800483c402c10a8107034128800310010216410040400480c40d6040c980d040302c01401207110b01100900320564440c2540b00101922418008101650040c40c019105500030701003a905985840d61075080143d80c2c2c004c0e1b03841181e01040e2a40120405807810300140c001c0503500c501300c411000c010b43d040d00d90b4000747c4a100440e50040030b10341402d050181c1800c241004110320fa10300e208440010000000d03002c1e155002d1100003076825503501c00d100c118002c02e60007020080c9000521160701007041c0c07642c0260700585165402035a99184200309807403140c0c0344000d0100c2e200c0c20758020400215400490380c1d41c4000a510b10b00c0c40d110f0000b40c1240e0b442c00c08100032990110f1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 490025557 1250 490024307 490024313
    0x60d0b091b0414010506130306020d060305150c070212010f0203040308070305070207080d050c070806011d090c0f0d0201030e06190b030c1305071407110f041a12190f 73
    0xa4115007071038103a0b003c020040400c02003d4030040305000b40d5024150020703880b8900324031507803464000d41d017240086448100c905801009000548010b47c0c45c3d10a01c900616030032000c0c14500e0081c0d40d0709900c0d5242241e41c2d070074440d2074074070016001e183e956140380c902c14120b150b0005600c036511aa845000317515011501404444000c2c0480c5c04543c0582814402d044000070300c490300324000d0408584030320510703e4107842c001c4283c04c401428004e0b41d00026004103107000c690011301c0f81084951050740c543e0009991004646205603104c52410900c2d0703034038246400e228200c580185004190380040d40070307103842c110b0706991541c44440400303030712810b082c801c3c810302d1000348044024010305a5a000000c0c2d1108044604012140d5a100411406401520b685400c1010090495203600c1d003070030030036902c070102040079004840344601c80d03c15240c14810450200d41c148081c2c0081070a020501c000c01581c22a10130241c41094003804006903091050040c851160140c000391180500d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 490026807 1250 490025557 490025593
    0x1201061214060310360309080303090c0409080c01020a0c1103030922180c060201151d07120f050a0c0c030504140a030b0a050a0507050406090509060d0b09 68
    0x1245480e0003010040c00e1007071940d00450020344c1148420008991300c400f203081140c0c003504810b14251440d907120724090707600300010072000400303000303456000035184e403078072110346a2004031098080c0f41c0040240c1002450594055a04030703018088442c201a020105642247c0c07120000c00b0100c4c803181c00c90700802c001c0204201004505501a604154110004c140a40000300c9030341c032440087c80c003d0802a6556001c0c031191000741000c035507004441c1c2050741d084c00090007120015420308910401c0361400d40c81c0002200d500000c0d000084a107406070401c0903102a12040c102304c80c1041c215464007040c000c11210b680c01e040002228200b042d00401116491011003041c046c4078038440001c00d07040025034049880082d0340003c4e00005000082050019404c0107007080d07140018014604c803294002445070040b42070800444c1c4a0b140240c4450003184207090002e90b4405007230003030303041c01c1400c2e80d041071000e4284100700925680d0744150060880c0c10f80700a60054400c14625280d42e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 490028057 1250 490026807 490026821
    0xf020709020a0804170a1b060f020f1b060106090522060924050a030f06090602070f02040b090108060a0b010203070c0611060f2202120a031d03030c060106031112010612 74
    0x500245001b25005c0c019182015046200001081540610b018408203400941103181c65180440d038030a648e40015a0036006000c80015141e010084c040d62107600280c85c506841c49034603410542031074a020810009450541005186440030620b00040b44a0286201070004030401141e01c080e902d01c08c40385070030941e40c2d9110f60310580e0030810050b1200211207060300d4106452010b151101e0030148080d01000000500a61000440009101e14101c44d8105d07544200e034103010120f204010030810040a0140075402c0d081700c0e0101d0072150084d4002d6014610600560382000c1994a4641c04c81c0c405900c01c2c0046441c141c44100701120030f00c8241d81c84010b084840d403560804600a251980e4203001c50f480d0091040006010355540380c1d01c8010034681c4030102d03002440545070092400c0c0c0d0b254513541c035184484c0c400d1080d510703001c01550031603c4c50300020111b0f603203058401c07400b90940551440001400f040a091003451400e4503502030034a9481d40d081c14501d0b46030000442e070b14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 490029307 1250 490028057 490028093
    0x15090308010b16122c101b120519020c100318050303010306020315240d29031b0105220510080601020706111f0e030406020a05011104050a060f020709020a0804 70
    0x92101e1803543e6454906d41e04840b00c1c03515001e18808000d1400c6a00b01d01d800c1409040c0824041c0704030482c1d85d0000052503001100300340c042180c401840700342d070f5038130f000700e44581d00c070317240f40d0200c5649032007548008240040b6403680c0f40100d070541c0312142180e0080e0010745a1075000406c1080c50304100480d0204c1071800e0354000a4403c403d215417121100c004501040440c00003000c3c0400b100903080b40b200d0b0118003003c0394080c1040100a4070010f800d03203c59000b03004211714000808160f0100d000c2124041c0c486515020101045100c01d6803400101540a06410380206003500d90300030a41c1103110715102c1d01220304003070300064501b003600e6000e80704000300c1c03031220040e64202249400e814410f40c030701304500080c0030300c00310050006100104400d100106000032079a40c0015506141c0e405200200441124164288040c4c0701e14042c61760020b2155808010702841082d00c00361422041c4159900c0da0b41300c00c8541c05aa11004071100054507000c01d00c024411601180c454030b0b42 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 490030557 1250 490029307 490029377
    0xb0303040b12040b090c0d1b23040605030c010e04020714010e0d0305091c0f020a02031b01090f030c1a070507060f0f0305040308011502030408070b03010315090308010b1612 76
    0x25075030f0020b540145141401000b0507086100c3d003a0805c8584030301d01c09421041c0360f4444004031608212701001d5048201441942803000c0015141004038100d0a4210306941da40e507885140018000650302c0000115040042a05500e040503020b02c40d480c003044201025010220030f44400805541d0041c211408581000c41d107025180031160f050010b9001c141800407d4003d205403c3e03041c10034006020350140521020a00b0144410508140c0c0d40b40980700e000c1507940740c96a2268070049404001d00c1291001810700030358040800161807024014245842c0400d695240e605150283c0e20038800b14084e0000a4200c40d040982452103104d05e2404102918282d01c009001c0078040c41202624091b942c40b800c48030784284125005060744100303c98040b541c4150780303051903009200035103182d00c2e08614403190290501810401e680c0513a01c480650742081e441d640203a00035281140b041201c0c50010002480502c118001980380d84c64082250300100800e41201850784e8039181d4406d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 490031807 1250 490030557 490030573
    0x6060e090d090803190c021002030318010e10090c03150603020a0e0f012903090d030e07060206011823071101021e0a02070b030a021c050c0307030b0303040b12040b09 73
    0xc07800000350350540c19010385d001000d0040740001c0c0c450307807400c140117900540e401d0224040d00b50000021400f0b501d500384c418141401e4581414200c682000c0140781c540c1100768400440071103a00242e80d03081c02183c10250666032941c1d810520031085c861800701c15203442c020025845c00f10813000080070751018400b03483c070303110601c41c2029005000c0e084e05c18544141002c15002d00c0d100c682c621101d031183c80790b0b5038101481d1495031074080f0509000020705120580c0e1b4000b02c045254002c540142d0020701440c1d003801d600c0c60016a40c1c807900100c0c0382c1d0312075440400c4c0315503540c000310f4800f05c1065800306040c900802003900030001c00d402c84688c0100800021100b00900c01ca4020864002040d20788030340441c120700744140350b80126182840842841540380c800e90040c08011111540c0f120342070300c96440385064036012a810401c0803028000a1100d41c02a04100350a48006040d86e02d081c3d00c031101c0152075000101c044410440000401041011034000310b41c0012a40780205130751 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 490033057 1250 490031807 490031819
    0x40203070c140102040b2206051c02030a0f0c180504050c09041a060a0816030908041404090b070201060e010905100b0d140f0f070f05031303090306060e090d09 70
    0x40401c000000744410742d20781e01000d02c2c00082d415030f0301074514030103c5a51082c00b01c0341d8940c104219140890450100e403400176100340290100d0340f4041c4a40b89428940641801101c025040100701b40042c44c0c450b5a0410000568451400f9880c07151300c031605a150012220000b01c04540c0020340a1485c20040c080d03101c07861410b0f503002089c11180480c541400f00600080d0040c460b8146410410100b803560380326400c1150180b05e04a400750200298240c0d45046003540c9141601034140b080800090180940c8600c445810800203480401c843c9290b42c6c0304c00e41724000702d034050b0050755204014002984102c1485d401040300440038405402c290728814444c00685c804c1a120640000c2c540d02c04c035200d5081550b00305598602078425183c070402002d0010401c1700c810b02002d0300d400c0000d00d124007580501e1301c1c1120643c0c84a055568003100c010f60b54070a50025428070980c1c4034000700251150007803601400f41400561864202101400d140ca210a0b0280c01170003035680040c001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 490034307 1250 490033057 490033067
    0x6030b040e070b07170d1b1e110a0512030907050103110a03020a0909060602100b0306070e01050a03090b0c040f0e04030804020906130903031b021b091f150e04020307 73
    0x50740d00c90f0812558a0101d45031001c88500d01100c22014240080303040d40c1c4110a540c01090011901c101e4011414020308040350300b0004204c8101d01c4c4661f030541890014414802000005070003021580000c950b5100d50b03181038141c009440c00703100c2c000308114800f9014030020300104020708040c0a10041003c851a8a00812460508255010681220b010304c80c040e03001c000d0080d0a41005040e440c0c000003920303003035003909090345e240c00c01510711018100010710600c40c207203594912548030110001111660b115260350000c058580000e00003241c0303110310003400750001c1480203642c0c51804a41001500c196403101c0c44a035104030802c00030070380005245612640c1214400748994a1000046083c4040d4146031101d524108420040640583c048040101e000c10000c05040443c00200c2e9201c03035161940d41c48424401d0561360504000c1300d03081c1c11108801d0011101200352200c5800070a0380d1303001c0a40c20396045030b84141290007214170340340c80109403404c0d855440c00042c0902 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 490035557 1250 490034307 490034309
    0x207140603041e1202060405070533130608060a05220f021309020a0e04020405010c03031a04140103030809070e2a16020f030a020f0d03090f03030906030b040e07 71
    0x80e4201a110043c60312194810340c5004540c8010061a1408a0740c0c4c020342e54481143c0407030300d92140f03200204140c941807480c180840c80c128114a40e01202160365040e00076145400003040505002c0070f00070310a2807510402504160740d800b44140b83c0041003107072003401944514000d0320000000c450243c4044907000c2003c031010360106041e6030480d0100000c0c480c1905d0503003070b03969a075800708402e4042d8008001010003540c540000389120350401040b0b00c035500c00c00f03001c1030701811180700290003a0040d120b0044101454460400440d01040680d240080a104010f09941c014420143c00000403504030b20114000c01c030240c05c080c586a11143d000d00750032000740c0d00050f0114414143c00348119154a038145c025100c0c00300b20076020184045540c124414810031111401ea410000f0b203034940c03640c0051142070f8070540300b0148046e1948840064040265190010a50780d05103150b50000710f100baa1051145840c020307000b0102e441580d529031145080255640d011200007441c40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 490036807 1250 490035557 490035563
    0x703081f05100221040501030f06060e130609020409020a020f07030c210501060801020c1b2b0c180507030c09170304050d050d03060f031716150903020714060304 71
    0x10040686640d000c0c3e1030248055000708501101030f80390f130402004540944100c03042a00c00f4054004110608004da031060701038040004c10f48000c800c0c8902d03040b207034040460b407625030014043d82c5520740300c0280e0341720f0340058100c01d4000403034500c2503904000b1601c0041801c009090b405040d641d43e01d0203042e60703114201126203840f2407030041d40040090b02400c141e03c2030080051307135030f605d80c1180030303410103850040705000e0500c1450450042804601080d68000c04500f144c1c1c20582042130303040300c00d04607414501d460703055002c0022440012280500030842490000d010700d000040c040d00e200402c580101401d02602545481d00805204140c502062842e2007001903250786514500882e4001c07903010781180480c506000d000305030340317254030a036236800d208642e243c0e40b40711181502803100521029422460020028400c3d01030122a01269904507644840e925005000811a10307404081039680c06e10b0410142c04000c0c2c0401002c41c540c004140600d47c03000034400340401070003d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 490038057 1250 490036807 490036819
    0x5070c060807030e1c1103041809030207080703050a061b081825080607051c020f040b0703030e0c0a0612050a0902030d0c0615050a03020103020711060f0703081f05 72
    0x1103101da034042c1d00641c803c121580c04666101c4445c41141400041600c41507010450319000011890408000ca40664801c800140c4100c075810751003100514501c0802e500b1030003481e2001c5042d0106000358001103028800418030715443d400c0802c2243c04401030061034140c201000321110303801c0304d0500e038803c4500f0801d120700b4610485c005d003007000c1c0e900451070314070344207070b805801700104000c0030141c070041000ca5840703660303600082d90a0700c034982180032507564600b0b4038074600c0219001000c0c204120b50505040c175650f4813403060541c02c041e0080780401c0d2100003110040b10f0402460b25900022640503204610b0110090100085041045c5005440300c00041d00781b10300f5001103024035030140c1111080140d00350b00034001d9007000d03400c44005d03080008400883d100da01010040c3c4000400e04062149154019402544140400c440009448081004540e6054050042650000203c03555140903140c01072400314024820241e21039090321104c0380b404407000b60401d07504203903a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 490039307 1250 490038057 490038061
    0x15050304030c08040b1e0703170a110f0306040e0a0b0c0d090f12110606060d020c10050103060c03060b130b0c030d15150e03060f0a06031703010f0605070c0608 70
    0x700d031011018500900510300000b000a518885c4400030404810400084040b220300c4080c0c00b142803081c1e550140002c3c007807549444407045a007458682003240c3c10000511890101c00021035900110a0216142c00201c100b140302d0619000f602400c105400180840d00c0a41d500e00c00645006000038200000105034528034a40036846444880e801581c1481c4447c520710b80121600c403088401f80010340030701c1182594000c001420b50160390020f0081d8100500484800007d402401c00d400c81072142e060303195040c40840c40390a010314051040401c04c01c0520a000d01920199400301300d04517020020740300407000d0761a4070700c1692800101290b80300700100500345540101e2140d860b400c0c0c945285003d0390080181a041200c50200d8100a500d400420135500c0b11780c24040039805801c0800060401c4058114841d40482001e0000a40e035031030391a586504c9240c584201172144c0300000502c80b1003c00b4280d00014519464210b02e0030426a40c1e02d040d500e018030880d01400b900c000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 490040557 1250 490039307 490039313
    0x305010f15210f06091d03030705160c030f03020c030105070e030309040e030f120402190b09010e010908070906031a0402030712030507021e0f06030636280615050304 73
    0x43d0580c25007000c02e04c10582c8948041c40205900c0918030070781e441c010b00f014202c4c2008401d0341c2c86440d046d2030f032504001801c11254440d84c5140c8084511a00152020001545d105207080f080ba000398000c02640071100d080c1421a000500110240a83c14429240c56940007003141d05000050b00d000c81d40c4510500510318501641c04642d0300301002244c03820b0034502e01c09201e4403c9000311443c4001401030b00b00000c84200b03901902ca8411010410b4034000d501801007032202d00010f2411100707042d9643c1645060581e40d03044110300c41e8540c0010414013007a0008640c030041020701e040c1c034504240d03000a5954060b40304180800d1051400d1005050142003610200b0b03030003400983e51502900101590007081d204094030903c6082262452030a0000590b84162805000aa05070240301002030301180e280361101241c00c085a005410000c0c0c9849071405150310380003642c5c031900c400c1800c1500c80014a0302c3d020b5180380090810440d046800182035648081c1099552034803681 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 490041807 1250 490040557 490040561
    0x50a0e0d1107080624040219030e150c0703020601050a0501051228091a0606030604091401020a03060515090d080c010e0f0601090606080f0406050603100c0305010f1521 74
    0xa031205181340075034001c00030b80e8040110b5112030351008a100c411303001805800c0108a01070f101c04e001000d0084504002403070302035031042450b804502d0032034404030107011006001d104222203888070201c0c041910300800d601000100c0c0503110031154500d11074100800240716010728100d440c8608441004908961141840e844c0029059404a0030b00113064815001918100c54121807003200f621440b082c01504091050003420010015481c3d5182c0d4420007002d801480400c3c0c400050705403e120801d0780901c020040c1039029100400d146150408003d100d40089414007002c0d0b00030068000307642d503240a4650003542c040030054031101c0030b0381250b0051400200b251294801d50482408000e40043c006048a2807181c0034801180c40c0d103004c4600c1c1c10f055481c841c0c0012000c0c041000034450ba001990300c980302408503004c1c9034405c0340d00c005031200713142182c010a66820040c0700e81f050100082c8090261003104107112509980700404038509900c03080381d5044006200b02004140b9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 490043057 1250 490041807 490041809
    0x16050109030203120a0b010e01050a091d060f0d152c0109140a080d1a0a03110a05040c05070f0c0f080106091d0d050a0e060c0d03050a0e0d1107 63
    0x10020811240c49190281d5654494056001d1000da010000b8403030910500540c9852036040e501d10f0107041c100c0c0700545d075a811441004003400b1040360041120700481c4040c400c0b4101c21140c50502c0e04015040c02500c89803624a1801031030000503000c00301f0420201084400400400000c400754030640e42d2403148501450b4082c18014206405d1011405420030034509000e105903210300380c03255000c40d5071800380e050010050b1200340314804007030150b91700c0b0401c0079030104c51520400320b0040c0085c1441910b9081110200355080341103601e400d1a145010142000365030811900302405c2000d09103002d200c50007403004070996070940030010803165a000401d4590032101000e03840d4201203020707200ca4081d51841038a4a0a803801150082c010f00b0040001c86028007000a01400101e850750310825541c81404100c181190303a680300c140c01414030380c03248000340410360080e8000409881c4007a080354a440c0c20f001085044440115404459070181c0c20081d18482e00031410f5400e20b056 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 490044307 1250 490043057 490043063
    0x12122208280807021309050106150906140d0e0d180303050d0515040e011a0a0317031308070b0106120b1f030905150403180e01050f0d0f0309210f0816 66
    0x5641030414581c80a81c11151a2074401c1f0006c0c081a03454a03881030584000d14009400221140c03c100a003501440751460301107a20b4003200d00e040d2144400b001910f4000181c0412944000e9483c486154411208150720410300c005446840c55a01c0040660081940c0441c4041c5d5540110700321800c480340350402c0120144c41440303080c40c50001c1a00a01800b80d0b44007601901c5c11200036075181c0300e00c04d201a29400b0791890b04100b180d10640107103802c0206401d200c01d111000348004611810f001e400014894030640c08290304100005041c0c1078030b0518000c4440c2406903211584c0d5405d0350240003402c0e10003e5001510003004201c010302403180020303006010b108074011001e9191800603219a0003504c450780e460301e03010040b5050300500d2045142000c00240103005903d095110100407500081c02210583c06644800c036110400c000200c0201c1c40e8a1003c10031a84602140c0c050342c4072100204d0700d252481d4071450a5990700d40001844008000341ca10742590500307002d0300030150 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 490045557 1250 490044307 490044319
    0x60b0304080a261b0306090406090c0b070f03090b07020a0312030b04060305070e0906090601090c0924030b030f06010b13241713021212220828080702 66
    0x115000da0140c1540d0203442c00c01c030103613554400413030120318481128016074001c0c101000c5541d41c0d1301d0f0480148a040b03002c5800c0c071701c01c40000481115010241480710b010f10340c0c0e00e482c1d2206280150800095921600d100e090510018003d640d5a460100849030004100703840d1000041048004202c282101ea5020303103414008800c4c024001800d10075145071b02044e80854561880704c035a50f080849802c80d0301e0380414014810341405400521303c29005040000880d07885102e03502e50000007080b41140b1005041d51850095410f0081401d0320004ac0c002d03026a01c01001c91075110841401382d40c12140c0700040641484c02105420b1000f003030b01400444183c0b00883d200c05080f61401244000a400005001c00640c0390801190254480191070580703a0410790030300422101203007481c50382d4016181244900341c10080202524602600c04451000c00302a0281e559074035030b086610150700c200b020484480c408640c80d91a19088548842107005c60b241c0349945105046000390094 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 490046807 1250 490045557 490045607
    0xb041502040b0405040c0305041e03020a0f05030c01050f010b0f090a08030f07060501051c122c1212030112060e1903120e030a140702030105090a030f03060b0304080a 73
    0x10202c501400c15076504035002e010072078034600c045040d128244c402518841c4103055600344500e201d580306500e144280107a44030b684140d140c00300f03007103812a000d4400e0b4100180c2500c1c900d50a20030107510081001c90a0300c0c030f50404070341200c2c5004402004440d058002074003101c0b0b588665440d40204400b00c02c696940d624100304da09260880401125054100341c004a21450f05400140c41030031075454601111816466514181da04040c140003404104100c0f0310451500100c0300036444c22a08a001e005a070001c00d100d25840840f139114141e41000c0703042c22034503a0203030031681101c007100aa020301c0b403880e0074010001c022603800107180d44152089003903441e80e05a410740800b80683c48130003000d03544a00c0101031f84d85142c013203482c58104008040d1500c5c011540c101e0b01c61543ca00b2103042085030b0303012078211b40080c0d50600702c60740540c0303074030b01010350002d100c1103208520325081c4001843c0a40d20380c0b1600004c1c000804418021821036611845841408480946045800c800c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 490048057 1250 490046807 490046819
    0xe0f06070c08061005150a0e04050c041a0f1909091a12031e1b0a050a0b0c070b0f0a1b0905010f03020a090e060a17010509100501060c0b04150204 64
    0x40c1c0c60510034907181d03020b03190005180c4110112000c040718405040d00e6002e04245401d001aa4403656041003030109080d1246019119445031030300c5500350403d02c6e03540d9410507540c44003d0708040000901034504005c21088a40101d0a030f401c41040c10001104542c0d1004050344c282d00c2d00d402044c510b921b002081c0b48a251500340010303490304181c444880b00810300900c1916071046a0400020080110400c0c0d1002d5941d0010242d509241e0642c0c07400900c101c6080c0c0c1080c2c980a401d4806520400e0428240001683c120fa044803035548050b141900c40e83e9500004500284420219107440000500400e01c0c7d4001003401ca207210b880c589841308500300a841c40f000c6004050001e07104401c0351420a009108032116142d807030f224902d4480c0340c42c2400e05540002014181c00082246001464807500c40d580c0000c50708070000810b80380b80400006191540301584603c8550900f40108042e54004c003c407407200744c0000e1420210b960b08d003000240c2c030081d05900c01109200040010f00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 490049307 1250 490048057 490048073
    0x405130903030b010804080a2007060305150a030b0112050316120f112508010204080703060b0a15030e01060e10050103111305061c0501090204050301050604050103120e0f0607 77
    0x103080c0c440e85007000343c048048011500c2da20100d071300a05400b420446c44410320702030f0710031280c2c4240c4a0b508810b001d041d4481582040065800040417984901c18050707000d00004503002c41d0601a42c100d45000e14503125802e4501044c4150001440b07070003681014440103004990460100d0010401c6424051420030155000a10120005510290782d419043d10610001660f03500d104000c00e15242c040f088003e850550f12500b400245040b04005030800007070003d0f2000f00342c03150140c00121701c4d50030610305817494028540c0c46410820302c00d00c41c5480d2a0702001c6495140d2600281102d03420704880e00400705034201030a004040010410081c00091440b41a100203903424842410480f01c600e602e40903901481c40150b00c940d100744680d041190181c103420044030074444016040d0796460044070320070b0b00000c118640025041c045da0801f4059a81c000074103031802c0095600d5520342c0310b800903101d41468204015400ca0350700a5035406d206410406006206070390b00c549518005031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 490050557 1250 490049307 490049321
    0xb03010512010908090103240305010203010e1302130c03020d050a0e010e01140411031005011211010c020f04020f040801060b030a32040c0806070e0f04020405010e15040513 76
    0x4440c0d0900c10141e244041c041c051144010f41c00101c950803c10800015009000060303000c2c0c001c485000480140030350104507100082d0300031000140d4035410030325041010340c030040003591565442c012001c0162a41d80d607000c5061001c078000160000951011406882100482034030181001c0500803420b1095002c00041e98a400c001c05c002d01003a00c526007a20001c003042e0129518610010300411220755100d600a003005094805090301e00001d40c045a00a030031407c01c3e2800300100300c0030040700030503403c060282420552a40d200550020340103203060301e10640100c0e004114000032100750fa00351406807212030000d0050580f203112240301904211014040641004100b1281c6800c05d111030410360466112400000780a181003a07400e040904120b4414031f0b0509d000440d0001444024003c90481e50389029548901040043e003c000e940c0c420321440c4104001c100580e040754141c00b49040c103641401c100c0c00a125000b80f00d009541c0115001a600081c02c01c101c0410f0313110741 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 490051807 1250 490050557 490050559
    0x4030b06010c060f0615110316081c0614010503010806070e130e0a02091e07080613090503030f0a061415090d0c080d020a1707020a0b04090609060b1926010b030105 72
    0x1030600e6010300c500320f90b00303401c0b0407022609400c100100c0d0034460301032741c0c4a46100c1c01103100c1854403801c10660260069050740344601c0700c1e0303981400d200440304400e05610855091030180e0135035040c20301440d200c80015040e117052080d0000704030090f07100d115404e003c4d20348404007000340e00d02e032040c1943c803844903140880c800c02083c0b00058075404080b416450b000f190070a110744a96981c18191340381d000203441c15030f2002d0048510301c01c00d9040e00a2051441c0b00d84051a02c03170528851450601c1d2020303003109603d44c1407203028804000c8680040c03400c0b000445103001040c6071007411214610451074120340100d03540c200700d0140482d01c1004412a0b08110803a80c2c1000300200490f191810484000c003a629446d000c00102619040500909400149410001541d8403158a165030103030780708010254944200b0811480580300741320090010400b01450404620709404d456080750902c10700f48141c01030031110040240d04562401c2041401c0c101d240d503110540c52280350001d00c185 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 490053057 1250 490051807 490051829
    0xe06040b13121101080c040e0a09110a030210050924030403120b060d0515130b040e0a0c0b0703050f040305010b04060602031317011113090c0507050304030b06010c060f06 75
    0x9810000a262002d869000503402e4054400c1d9401154480000341580e86081340901c400305031144014030762802968610301c0080c1411480c502010455400d4880320311401401c1002c10140e280c0300d001c07007410641d85c0380c0699100c1d03411001a483d61003c008200e080003103846c1c40c0070303108804030045002d50300030b8850300090528210300381e084e0303002581656000542442100c2501c2029000250004418a0210210341c00140452018084e4041c501101500d8904400f510300f4144640c4c0d0400e01d042e006807011021a4542550448603072080c0803110300f00085110605105005a8032602c141d4000326503550303901d040030380c043c0ca03481030b90900c91860407500141181c000000c4600048042c0c0d0010103161070440170076404081240d214010b5522181014030300f1440d070006140d41201d8030a008101ca04241c610b0003280c0c01d24032200188081045030002184001045d50100e0707a0240c3c110b070342551610700484400c000204000d010f03605081c04d03144c03407802d0343d00b1000544483ca910 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 490054307 1250 490053057 490053059
    0x201003270605070e100905040c0c0b09072105030306190e01120c060302040e0a0b0f03010c0302030f0c0301030818030703080408031b063d030f0309090b1309030e06040b13 75
    0x400145000d205c01d004049a02da0780e0810142c01c084e040302607140103908001a03000840d803a600f98441040354414181d0300600300501c086007802403040c1d456a035140200ca143c50869072165075a101c0980903a100d2000070755800800c5c1d1100d4042c101902140d070304905a56900d000907920009900c1c011030f40311019a60205030700e071282c400e4500320b035680308545c100c540b5000303035010080401d800440d4120404030b151443c903460034040c0010803541d03a580140c0d80d29106003551012b10000e001120754041c00c000400111b5940001c0d40c10b0b000b0507240c1c001903110790b000006e180000550000300086c0000c42c00249842001c80604214440b4108a0310040c2c1541d47d15078880c01c0880d030196800e080340e01e51013008001c1c400c086280c1007291125042c807020301c1c503904010241c10780c0b00f22004456072468000701580000e1040c000e08211400b4004401d100f00000d07190551560f0382002c19a0b5440880107052091400c2520900701504295680d61a081100d42c070b54041404599014500c4c44 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 490055557 1250 490054307 490054309
    0x291501210612120e060a09120203070801051303021501060f210513031e02060c0703181527030204020c0c0d0305031503060f070503090307061404201003270605070e 72
    0x102c850b0103906c3d640f00c01d665418502100b20b40c013038964041c0e03094442c4420201d0300c02d02c01d1140318011250100b1000d1260b605250091070460880f07804645100b03500c00402c0006e41243c200c0344078603001d00b894460f0200c00945210884181d031a00300006050000380054442c40c1c0486121160003995800384107050b80d2011744400499034076130001680204002162400d00c031010388a100e101c1d15101c00d100030b01d14074203443c5c901550842400c41110115049809400922641112115480d814695001030045003070714800b51001034003483d000281824003007814460030b441c900d0000e110702e00461150400400381c2d0001c4961101210000c40c041d41340f46800220a4491f000c4c109110ba001c0d510f60b803088401c2d800207402c0b500540710030701c40c0c280012050700400712100c64000001d41507141906001e4540d07018981e43c40c15407502d940250780e05403141c2400b0b40309041075007030100702220311404004e1010b4044a1200311002c181028008104c402d1304218011502c07699200d0000709100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 490056807 1250 490055557 490055569
    0xc0b2506060323060f0a0f0501080609070f080613110d0c291c0b031509010f020a021506060d1a031b130507020703291501210612120e 59
    0x1041044940c2c0118009928030103035000c1d459025650311b002160b81d50551226006542003a00107100a8015004004112a040200c64014a0440398031200540b520462584501703003d4400101d0b4615401307a0428410701a0689450000c06401d138407204009040010420a05008882000942003400f45458503098100c04810311110402c5140581d506100504841d411001d60259901d0f00c4c50003009d41d4041c410803000640c3c03013550340035502d0940c400c2c0c0d08441d003054070b500ca1544140305480d1841d900041c0c1c48580038180ca042602604c4550008055025001c101104181407031a0441c5002c0143c0b104102c040c0f056089402e00038a0261041d0300c601d114001c241c2003070078589021440f01d5942c104940028003401502c001c071f5104c0d2910105a140050010048100b00b00b400c1e400c00c04601c1850381c040c0d224140003401612040000300030008400c0814460100c400f03440010703191650101d00101031031111364980a00718a0108050342c05107240c24003041c005c6900c40c481741041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 490058057 1250 490056807 490056863
    0x90f030c07060305040f020d080705010b010c0b0a020c011401060201150905040b040f06090b040c031b0305070b13240813050c0d050c040c020105061306030c0b25060603 74
    0x400081e01000c0e0400c2c0d011002008002c0c400d450400d540d03800c66001d41c44400d04490114010220166141c01e942012070035034031404000c504110403915004003107100d800b5981e4021056072400b69480e9007030500e00e800350103a10708400914040000000701241c05503c80c03442c0350601480300b14059580d420700411600200d8019000503284800900026000141e4080c3d441c45504002450401901c1c0c240e1080c01c100d07812501c450b107560f010701c03e004201030916120610300101100e55411665242d807240b0311442540074801c0045896142c02c1100498100540224020010aa402d507800b007000090081d0340705001ca19010046845a040d03030303941e0009580c02c00024044149041c0c20310240413103010003a1042d02a000e20919a560f85003c2c8808543e500c1d4004a240c0c20208100102e4042c02100c01105a2601c2c0040000440700c010b09800c58541303619281e12040075035903400b90044102860010710940c0da0810007003050503800002647d0103410624075039030b0301170507400005e021707 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 490059307 1250 490058057 490058077
    0xc070e060321041d1b070305070b040c0315020703021b1203071506050108041a22060608010605030d0816110303100801050c040e130809040606030204092f03060118060305090f03 78
    0x28007034145c0c076001041750040c400140721f4a001c43c0ba0480d16150940403850a80b0200ca034404242c404000f400070310380b05100381424010b8210b24080c030301c0d50041c3d40c5001c40802c08162400d400843d01c4c3c1981c8404e1007140f001c16400c00d480c0c0d43e1060707152000d00304940c01c00c024200751910320045840e512407618588180d078850101440320f0ba02c100403181560000b45000000000b034110391140d9002c2d1000d1000582c42000080341841c18800349501303440701a0040d41c0a9031000e6403c4010b942e000c0b0314990440d546590180c00406102c03000c40e04010141411819403000001740603019400550000c225110a002008961208001d2004a00c241d214055802c0c526002040e07112403d12680891940b0580100d45000c1c4148082015200c00f5031005c00401d5010404000014030b038044e07440b44803100f41e40310092004410541000190301c41c0b0403404c8107000f02c0024600d9015154000c007140089501800c25540c0e82402001f800b0200c4800e1040d000d004040840e0500010079500e803086 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 490060557 1250 490059307 490059331
    0x512010902310f0609020a0201020c01240506130b12160c230a02043204050307030f02010b19031a0426070206071b0b0c070e060321041d 60
    0xb525007000024005020141210580d1903000203100700d00e03403005081264094002507117400440c5001030840c0c41602c01c2852074994035807011690104c11105c0016038030122603042c0c407a072210354401c8010019400500310301034006808169940180300e000e105c3c0d0700031401c450000681080c00c448034000030760028183c00b000d08680c6940c3c5202c0c0480c1141414480c03c0350f02403e010380026003031306c00446d03030f06070324409191560351340d4020300000c50030202d80c40c4440d40113803c060740c403666203101e50f44014040051083c1001c0100d4802e4008403250300c0020401d09007000c1c0c0c141100081070062000301c0740e10441c0c500115243d5558101d0512458100303200d251040000041c88209500c0030410108100041141a0060f6208409444420b0180101c903240f40d1440900d94002c007416003000902c0c020601c00001c2c80440087c0c3d0344203a0b5003009142e400c1d80c43e002c0100e480c0c02c10352051290f48001000ca81c240d10f18025003e001202c070780ea503078504104200b98100c81c0c608025100840400303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 490061807 1250 490060557 490060639
    0x90602060a050421081503030315060304050703060905061503010c1709030f0403080405210a060c1403040302011a010507030c02092703030615190e04060512010902 72
    0xc0150381c40540c0c0b160042010010414003c00344d50101c071001d612040c041208002441102100c014a0b10200902540214514240780503034000c80003d00da00144280000000101008024040c90000351f0388828144000c214600d0303c03d031038810440d2500742c4640440b100c0c01c5146014000c0303504140f456101c40821240b0884006c5400c0b8006002741001e00c0104118560301c48402c0c01030005501981500391034900300810403e0002941e8101d0181e221546016040400045110344549920500000780400308107003e0b10103c8002030300050f650700110810060580641010120020604204420a003001d00544180c0509400500084c1c81400c50500600301242000e400008100c88010841801d03001e00321001c0d20030080b00300b60342010083c00781a0500c4610300840ca041000c441d42440000244010100801e44980041152044007192203449641c00b000150a000e0721050f844110318082d180600380c81e200403801140d032209000c944141e500c820040b1410b02810742500c803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 490063057 1250 490061807 490061821
    0x11113081b181b07060b04060b0a090b0d15090e010606140f0304080f0a110f070b090d0204271e0209011511150103150c0f0f0905031506090709060206 66
    0x582c00101a140701c142c21003406a0484150009008134520a00d40815104d58000c140800d660031640900805a0f080c88a0b48640390018410b5080d9546100030523102c000110100c400342914080540c003040100d0307404284000c0b144c118501034644180240181d80d50f400b000c599040c4c21420303042c02e2160030b000a01c107202c210300c001d6400a009401450a01c86855038450383e55200a200074045003007a1400b24910100707200400d04086840301801a280c60320924200034810040e51a200d000c001c810101107681d280d004803c02408075840c400e036400580c81c00361401e2242441a01e070300f142c00d4004511004c40010440d00d0301d9015084442030703442d18a04540d0407039043c264205101c410750611b4400b0000700710700e0351a0b81843c0d40180a551550909010756056103100c07002403801d01c180c2c1c0d1a0150000000744010034607240032440350080e4001112031400e503800050f814024400c0100308400c030090300502501d81183c030a013480c0c441402c03c4e02d842c0514030a603c05600000005000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 490064307 1250 490063057 490063099
    0x41e1a0705010605042412080712120911010e030102040f0506070c12080316020f0c010503100b0c0a020109242d110601090b0a050d05011113081b 64
    0x34107840780c0e001040b59500c64000030150741008050f0f02100c520981d1070040a401032400c4401401c0d1131075200344001403506c030f154a600c1034013009081c1d00e61500c200301c045441164441c4030b600000b038040141d0500351420401021030001d01e18005a041c4c0b041000758941842120300b1a481e40750001902c178580014000c45410403001a5040d0044a9001440c0d801c4640c034410701c50b100c0c20000b50380b45081080c00d800b002100c07a00c9011503000170a05141e0400004181c0c66031142424903580f01d60300d503041e013400605643c0000c1c041d03542c0800c404501400005031010103031b100b40c0320003012940340e0006000e901c24030300440c0c00201404581710060717030180f42c2c081c0320f0811240314001ca140c0c4041c1c14140d50202d031403181000907800001011210011b01016002d00b9414100780030002e01c0e000010b0750708040340144c0b03100e1402481d001041103000d501c10320740c808010001070b0301c42c0303500c8502d034034050964440e1050f98000d0100c110448241c6080014040da0014003a40c62855802d05083c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 490065557 1250 490064307 490064317
    0x70b1204060c030e1903021011070303110c0712050607022a060d06060c03030510082104030512040608070e150901020a0606090905070f0e04140109020a0b041e1a 71
    0x1803507a6084d41005440f000d2082c0d0701d0b840b01500031440500001d01c0e0003131914100150030b910391850000c0d80b40e9400384050880b41e0b62034240c83c02040300750700c010350450244501d19080142d84501c0c01c00058501c044100032115a000303106031041039840300c0c4141d803103900f00307280b081c89502400f0201c1814990030700c0403101204040c110604011180d20300320100d50131a080345000c55210080e100405a06000301e0794808030800c4259085880c244100b55118901d0342000c007140d2034002e0203050020014282e5005640060845441d1600035210185690090084100042410000a40c6a0b001380840c015005d005031a030110720402c01c20aa40e15003003407048a046004000000c004111140207000145c0500313800004e0503003161a00c00d141001c0c0742c1c040c21444006007803c0126034204010340e07a020360080281c2c50300e01ca14542380d900400c2d0388180294403843c0103c011904078588000380c41035502140380821070301b2000300c403541e007440c4034400c1c000c00c128042a220781881728000540b03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 490066807 1250 490065557 490065581
    0x19020106090e060f040f0f0303020d0b0f150a051204111206090d050a111e0d031401030209040206071205030a0608060405121b030408010906060f06080a1a0306040f0203070b120406 79
    0x68a010056683c2c07d10071441d80400d40001e50041800071044900d8420001c0642d0f04403486c0c1c0000403640d0110301c1d4140082030f0f031400380c80007140b8080c44901074805c0f030344906e00c3c2c810810014501403070310b084410501d06803580154000d40c0c0b121503d00001400601650100c0010010a00041000c481d10390102c01c03101c040110b0081d8159041804205500032405181654403103139180b150072516017544c0129085c04c040c00c00d4660716070007007440c1c5c800d81501cbd010340c1e11022668130317400032030f41038070031100300415584072450501c1c20b582d07002021718000e03008004140001541d038584643c0d510400d0390054500d0f0041e41c40011400b4150000705910420400c140b64852003120790141542c20035446094140d460ba9452000c001947c458a00a00301c02c0c00700074605810071000810001c0d00070030a5000c03540da0391018681c5083d948035454045001022208075182c54544000c07070b0240c4035012402440768280226050040400352030b07005081494004083c0c0c4d41351202000f50541239155 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 490068057 1250 490066807 490066823
    0x1709010509060a170a0c0e090402030f06010b030406150b120402041d06090d0f050d02280c020901090c05070f1a160806010e06040902090f0619020106090e060f04 71
    0x2001c075625101e0190440c1d840030707142ca035024a510454202c080000404170914140380031100c3c9800d42e0030052880c100d5000341c0720401c80b03585610100b454140722030703440d9103103104690000541e004844005c501c601e01ca0321040c42621284d02c000c074180e165500500c46503084c2440308034403044d0048100d55000b40020004501c00c900308002d0002001401600f00030f0343c10010801034201e00c104110040c1c1950740c40c0807039862241c0003006015000e41c9000e01d0000342c00145003080b07a0400640d84110800b040c070f0328005c01c507607040c000d001d9503040403040b80145002c0000240750101c0c0d10038000d001c441030f141c0d5490b04029039201d86085100c100121a01440b018000301304201040400d03102e024480c4517404110103404014101803030003001c03d810090940180303c5d2a80b11001135508480c01c5481c0907803902ca042d070010304a61124042c1a070819804603400d112003064000c94880c0a94a80080140c0741d141c0a100040d075046c08804580350340300402140d5a0300c108655158007902136244 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 490069307 1250 490068057 490068067
    0x1b0206070f0b1003060b030601050a060f0315060309060c0908061b120a0c17011a0c1e0d030e070311100909050f0f1305061b160605090d0c17090105 65
    0x4800300540156803d010000d90300d007081c410818603128061241000700c0080c05198580000948042d0990040b00b0030014180340b01e201190090300001000250304a407514100c0d100c1e00000d00800c10301c0c0c002d5030b2217801d046007101c42e540620380c0141582c0fa278101620550751061541500c0d24030004040f007101c90108548600c00c0712050180b4066005620003151040d500c05004205014505000300d403003000f000104801180103c44c40b4a148a2a80080d155100f15504034100314041ca000c50046000c07100c401d200e2080460351003a1a03189032010030418000303481255440e00e00e40401805521040f1010000703207060007007904003490903d481c820881c5c484c94154181c82043d140c0725508600c20b418000c1b20800f8840041d0301428140030040000d00b1502e59035656440940030401002c840c5c10105140e000c01030454082c121900340104103c442d600e4400014001159550302c01d014100c3c400740307030030701c640740340702031180c02406411041b0f40302a12141d03107600940c0c106052080402c6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 490070557 1250 490069307 490069313
    0x206010b1c02040810110a02030702040f24030203100e07050402090f06070c151b0605100f120b010b0906120a090b01030f1406061e06040b030f070207061b0206070f 72
    0x81c009880b154019000a903d184c908005848000038001c1b00b502d005d01142c8032032079000064584031501190045410b00c000f41c101e40052950078500500c101e00501c4450408a40d881c0d2241224420380132500010b4080c001c0e04100c0e1211032501d45a90848001046079207090f030054600504020401060344080c240061180d41c4544001c885008810b0700800a117052050024280350365030502003070880c0030341942c1030503440941000305240e58841c0450210079030b0b00887c0e0702800c200000407000c152034101d17041900440031011100300c500680080f03140707003604007a00c2e80494081e0946092445100c007400c1340d840e0081560801c05d1f52028040042900c0e0b0211600a60007900d00c0c1c01081a107042c074000d04408042c03e41c1c241e034424418040031b43c4841343c03243c005158000300601c025502e42d00103801d6100e1941b000c00409408024040f4107103150282c0d0340030343d00c03035002c131400141d17034030000c0c1d80d40d080c6599407142c00c440c0c00c054a409410050b0090a60900c10410121900070540d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 490071807 1250 490070557 490070561
    0x4141003051608090f010c1e08060d0b09150c2d0301180b0310020a030c0c0209010b092701150c030503010b0f07020a0f050316080c040e0f070e0618070206010b1c 71
    0x900c108001090419074400c107038800c84050082840c0b40c6009c6c171480c6002400301c3c0d4505022000100352a01140000391101c0e0f06000700c040d00010300002d14181d0500c940089044d0f003000080701040181c50320080101509140140307401801c0d03218240c11a8a04403800c80f00d003404002004205844203801d0180d80d50a02a0414044a298005071580f059080007021614400c41e154140304000b11044007594603001014115500ca190b01d80c1e664549101007541d0b0302810320741526001c515130507075000311003030304119050b52071241d000c80c81080050011245500000c0f4040c0210b04100014483c4410300e400070101e043e6a890184e1400195601081243c0d031070307600010880b0300e40c100030b210a2900380100209840104500014281400c61854480e000026028031681e96a1181440b0403414881e030b4403c2131044060320542503944440c00702c10a81100c0c01445840303a00614101c2001070684030317000e006960f0040003e40c1c00d20303654640030b80c007500d02080b142003580085219600c540c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 490073057 1250 490071807 490071821
    0x3030e03190c0e01060206060109090e030705120c062410030b06160507060306061b020120030306100302030f15060412050f07060507030203120a06090204141003051608090f01 77
    0x98400b00c1c007103070310300442d4000e001d8040e0800740031904100140880360f0307800041802540c5c010540015580d40c011911840c43c480c03400001d106000d43c40b01000d0b02485500038080101c0100d0a0b00e005070740d05000c4c400004202c1e03050440300c0303410303541c8050281014038001011740403e00f00095443e10120014200350000000d04074054480e1031480c0401078180140002402581014001c060030404041c01101e459842c109078000c80880250030b6a02c190000500084094030b941090b240c40d00030580c81e544103c0762140241a6a401d5440d42486442142d110f5100703e8403406082d01c590380340d8002d0403016500b40b940100300b400301240c4082110a05480140308400802d5050104045503040620390340c849800e1100601c000c00100f50040100c40c0381110f80954107111340d0358250440010591608010b214507c04600810030010102e2501b00011045070180c111010044080702960307401c40701c83c1b802d080041c0d400c10807640070300d03034240d0404003034003e803000d8009082e499800c688103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 490074307 1250 490073057 490073063
    0x40b0604030807020a0e060d061125050f0307021e0102010f05130c1409010b0c190305210c0a030914060a0b090f0405030906030405010209090c09130b0a03030e0319 72
    0x40007070040f0452a126480c88014a01c0c03261100c0c0301d241400019110400e21000941059100e084005404000d042110141c811000b04444100070726031404040840031389044403d4410805860b80442c4000b013a103a080398010405442c4010601da2405441c0f0034003070040c107540d201c0380c12901c07078141e6006141c8907070152120107034400300501380035081032488c0d4401469240d403c0169007081c0c840050050540301098001d6542e4005d41450500d041c451200c50105541114422010035174880d000701907445521040440c0d50303c10410101d40e00a041e500d01c04108010030003403054600a80114072080c0c010031001303100508501025060850842d00450510b5403142035031014500b08103200e0b005008083c8551882c0745c03550701c06980c0e11030009058400e000c00f00001d010800250101d695415000e400c01000c1d003414500c4040b00d0700203c035040c0c4651480200c1c8140080b030b601c1001e64025008121944461550302c0a55406824840f400c0e01800307081042109404440095000c0c944 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 490075557 1250 490074307 490074323
    0x111801090b030c01031b030c110607050415050307020a03080702070b04031401060608040c1211180f0106030b150f070f080a02010c0804031707180611073002040b060403 74
    0xc07040109400c000c00c40d0880d6060510704120b1240001d00c104800040702440d04000907442040d00d825108032045d8801019035102d80c0d42001981075116024000b1102c603040780e000072040c80705d01074030706000440740d910045e403140e0310344030110b40b0600b0903d4004540c0c1c01612003441c0c40d100c000901e6031140e00306880c6c1104e441900358810109100744002010140342c90919801d0a0790391181c14030552084840c00841e1013480002d1107003e40c0310703030b2031040d00900403540701205c1c1881070b00ca81c004841200144400000005240b402800382105452004040b80c5103194420362503c2103030040c5804011010007408004001203d080124a0080c040d100d90f0340c54610208009007034520b05541403003040400028400040d82002c03031814080d0094a940a07540c0e01c100c0e00b2a0008110b060702d0031100c5404600180403078010f00d054447c060007500b624942a02c500320070481c44500c2540c1c1c10000051913200041c0004001c000344071501c02080840d15601d000f00250494101d40c10030f4603880 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 490076807 1250 490075557 490075571
    0x503030a170c160f0804091811030f1f0209060c06010315061a0702041b090e010509151504090c03050a0506030f1908090a03050f07140d11180109 64
    0x700350701851a921058005955240918005840801034060382c030042100d4000990701c0c0800042c40e058501070300310350740c0070000ca04041104c0424070544031420340d103091212808100508011828240e020003d0b0010f1008001b0303c401e0034041050481400072840d400c2c40075240c2e1340e0300d010041c2050307a1000010101035040d420550040c541d07810789060080d107848020040c400000d40e001d240c02c59548800d81e294000d034008503000c0c08500c400078080080c1103903084842a0005901001d07a85080b050410aa0300c4109000130720038140d810b004186110161001d82d840c100461200d20070903280810b081942c0d4883c83d030156401c148142012a8441041101194807441842d0740034404800405501a9030400b050b110b0750720707640c040d070041c9681c2149400e0284110440d801c0403001b07821181210350b00c0c10110386690700302da0105500d0007218030014504418407090705403560018800b08013080d040d500c00600c10460b1509a400407500d004584888031000ca41034024064414046849 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 490078057 1250 490076807 490076837
    0xe0601060206040b0106050c0a060c12050a0c0e040b060d090819030524010f140403150507020609070e060108040c0801020c16050109120b040f02031902010909090302100c090503030a 80
    0x544416001b82040140620000504000c00610303000400e1700000000380d00d60b1050411260741c1100c03151269040d040109100840b60581c1c041000402503554290041c4440c404000c1510031305207009900010502136180042510f030b000f002098410300303565152005010b80c440c480c42c1d01c80010320100341d4420401041e40b01440d0041440140c10b01c0c25900b1040c02400600043c80c155040420044203500400d0010f81400c1110040c68021a004e20607d40002800002e40fa04495070801401002e0109080000000700b91080d5505140d600318950354850044402000060042e507040c0c9080f440021064002e20007006d1070080c0305c0140880100a0084040d2106151f200904020101100708251922040045a882c0c0d0100204049032070301d007018000748421a401941c18081e05440760302c1c1080c10401601041d200303895543c0d0702903441b800b10084a04000d0013401603040b200f0300d42920902a403041e820160355003000789400e074403480403e1071604803cbc3c01a01040070f0201000314 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 490079307 1250 490078057 490078073
    0x1915050702041a130f110414130b1e030307061410060503070f05070206040803040b0d05150a0303080403091a0a03050f0c16110904060f0e0c010f050d0e060106020604 73
    0x9010203095410380c090b400d01011138045081148042c2c01e040d910f0381e1203190402550024468209440c1c2d50381d44841d165280040c592400d882031038030a1142d80e107515206e10840c01020640c44004141c00300310f104c0d864074085008400f450b040d626020410840e40029114456074500f42080c2d5001c2d100c61402000300981600d00c3d8102500744a4184100020f00e130340888904203520781d9250a80e1174102910128102e802542c000c640f240c000410080303883c2d00c01d00086e012420304c084c004d0080741c5402c030700d84044a01142d25103401c001101c0050000ca405403c0664105102e4580079120300e50702e440420320700d1001070408540b0308000844c41841a4180181e58009808400300d44040c100b9440b494010f109407000b8050070400f41d001d040c240820030100c601c040078050404501480d051030038500404101051424551801491044654001070045034802068441c0e20b60b49040f80703419122074000c10199000c0c0c60321505800315008050080c1402014640c00621160503d85801c681c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 490080557 1250 490079307 490079321
    0x3150c0f030905030306010f0c0c090b0108010b070503040311060909151801080a020f03160905010302131406040b0604030501020c01090b06240a0504090c020a030e01030c0e191505070204 82
    0x400c040c1441d0414000c60008005c40c0d401003000d003081e0481c0c0840b95002d070351080e1b01c5440584205425640020710225a400401881d0030980e00e0b10501c0c1c5c2c03960100000350090240261056000307110510004408800140744a04002c0040d4180419440050400d0004890010408030a00302030001402c0c00c80c25401e2408800c40c80e441c056040100150342c8029064004c2e100320038611620003039890134401201d100e0040c0000200036074440c001040580f17000c1c48220b014280e183c035480f0326000140b1a024420404070301d00e0a0036100d200401c405000440b4035594404803c120000000d1000d00c010412808008004141c01009003010305103203c0003480980a107079046d00329405035003a54003400c0a00d50a0042c10f4440000343e0048a0070b016039040400030350b1600e501c03201700540024103141d056110790342d1340310500b40000044082e030b200252010040341c1c01541d0846946048240d81a103060b02055000305161360300e480051b0804044e01c1c4e207011450000364101075003018003070701c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 490081807 1250 490080557 490080587
    0x8010f0606030b06280e120c010e0a06050d151d0103020a0510052203060c110d0201020c0d0c02030a0b1306050108070b0d020d060e0907080105150d0803090703150c 72
    0x10b05000000c0e0042c4655041114142c01d445a0000f5011046000b603001106c15940500b000c9002608092020394a8001c08550380c042a0a046803803414a04185128141c0b100c6540340307400e20703004c090701c0d20141102846c16924a41e8680c0046038449066601504c00c5443c0c001a05c082d500d54010b20060826a0308aa4000c454280c00d240200344c1000c200e40d0b400312070000078455044020366400120940742c10044c070003824000c40318030a9030700c03440d03400e02c0080d0541034845c4802151401c2c0c1c01c0b485101802000c0d50880040304540300e00030034a00680b140050152a10441c50342c8c2d400c062580100c079100d1000203460023036814000544600c0c2d01422100001b04a818144840d040442c040d511902840a070009a01e103056032054101400502000107131011a050001409485004030b000d640c0d120762030840040c0c00c0ea0304803202211010030142103000050034a4645403240e510040400383d040c4500400040020302030140244002c9610500068a18017198000d1205030101c3c031079 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 490083057 1250 490081807 490081819
    0x60e07090e0c0121110406110c0109062a05160f060314010905150306010e1509131716051e010203060a050910030b0903030402030f0a08180a08010f0606030b 69
    0x400056600110a801008400c40c10401007491320f100420103007900340c5400c0c1c15080c0118001075110340040035030380f100c10320105482584059900440c3d0381005071282d00c0004000000c400c1441d181502168003d8010001040192904d0344910f07250444469a40c06401000e600c10802c04007464a120041c200e02d00d801d00009980a9402c406103006008400c181555100030500e000c410441c1006c654070044e0640c0c2c040d680d540d25503032122108464480a4100b0102c00c10200d1030500103c0344909140c40e11042200360f10348071450510a00140f030f00c0d914004120f020643c081d603503011400e0b1881a401060300810300d41e084c2c4c01441d40350707444a00c8be03030051080c40025550048200243c5906551a440b00d0b5034440e03484525240f20340c8040c224030070703940c1400790440e804001988100e0084c0c048810703000680c140551b894040c08006042460184416011801442c0d00da46003100c0041006500e40d40f218070450031140c0c1d469030410850f0740ca540801c01c440d054000c5e910469011161 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 490084307 1250 490083057 490083073
    0x1703132a05031515280f090c1d010903020a0f03060c030b0102030910090504060b12090c18040f020909010f060b0a050403020409021512071407031b020a03060e07090e 73
    0xc08043c0540142c40107003075190904031100e41c0e4465070656006010146280c081d4500308429003c01c541280c040c2c01250b158951010aa403103c42c0620703514000c20b0741e1480c6449801c1d10118420341d282c05402d03410810031784400400360f900c0350400c801408401d25481100c0c0d207145400011110300d80060403d2500f4821016035070f070703004801d44440c00d200341c4950b440707207000000807200740c016600110750040c580705000c2044140c501c060880e6240b41013a0660a80703660a0217959031812101480e8800c09404d0340c140c08003881c88a6540092240110042c0c0e074103030703a00003101007104640c0640903039521180002708201e40c2c020140207108081050740f510111034402802c9214a0202034052501d03102d0042c21074464429003000c51520280c00c0352602d031550b01c00c2c003020381c00351002c40c00500c030184821091003c050487d103002307070301d604c81e030301800d4800c9100318240442c1c007803d0b80c0c0040c000303c0020114000d402420034034003040340035200c0c06003006810001c17111f205403100010ba0000311 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 490085557 1250 490084307 490084333
    0x510080a0c0f090315061a18030a0c1809050303040f020103050a0603050c1002250e01080c010509121c2006040525081203010518041703132a0503 64
    0x4640411344c5d40054081259241c81c40120010b407606900170108918403d02d00b051001841c009407004d50a402c0100303002c01141420541d4840011801a05d4000d2664041101080d501c130340e85480d0b50250b00c08a26098151640b81c00c54100b182c09840b1400c610b01000301315079161043c96400400c218040003820f0854807072569075546082d00782d00402c0403809903240c40d0b008002c034146091012002600383c400c3c000102c00011031a100b5410044c078000004544240c0101e80f141c03071a04183c1d50b0a05180040d03040084003800b005a0707192a00540301540302c0001c01e28040403c581c070584402822034010b45500c40310210340704401005410010900000032404075004900c41040c81940f42e000c0c00c1e085d1049100d890340d611140d40c42c0310f41880d50042c0300a40d0060350413150100c03403228082c40c12401039801094200c1d001044901c0004400901d0780a8001031904031021030503042c0d0090f0700d5034840039565000130310840c204501d08e40303a03100090740c105024041d200550203458604a031003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 490086807 1250 490085557 490085567
    0xa08010303030b1c12031d030703030b0f1c0b1305250e040f050c0108041109071b050312011703030a0c0c020a090c08250c0c0510080a0c0f 61
    0x200000781056110750341d240d0076640798005800722404080001d9804c1015240c032a0326049030000c0c40380480d0410803441e590105110507181202c001d40c002c2d505c0d05410769002c40051684840e4540c1c810841c6800044503140c000b0305155001d003076252451940101e0501c0a00b4120003845c0c0a8240024143c0500040000c0340007031410400c0c1c41b1b000700300003010120000e091056045407031101c13001020441400340a034070114419000e18152041c0024420045031006c13411503000d040da44420680140c107041403240258001614580ba050f018103011100700c2c6d031224500700340c410358804107120400101d41d41c5201d00401e08228041d82c1c80325115149a00e9000c020140d000b0550745014280009002d80010101da81c3d00030406440c05443e50f80030701c014a0388100342d20005039280b000a04800c0c0c902d040e22841204a11013502d803c0c59190119102020610220342401c2c0385200014281c0301d401c0100c040e206541c43c0d0010500d00300301584215042090200100070f0100010603c141c1c000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 490088057 1250 490086807 490086809
    0xa05251406070204020304030c0b1b070b04060b03030a03200702090c030c09030303070c031e140901021f050103170414060a0315081b0402040b1621081b0a0801 70
    0x400c000c2400c0c800c54000900c85004824000e5002400081048101035100208601e0140308000d00c2c4d21544540020350008545034008815401c0708108483c04079001d0152650f016102d507101041c2100440c1c0400c1c1103800420341180071917140c16805440c4101c3d01180c000219810355101d051040c84d4002030460580a400c580d005000000418124520242107806071040902181d59909010344014020300e04010107030300088281c55104e50b40082181d100c42110760079030310708a40b4840059041400c4d40182c0c1c000303042d03100c0c0002100d100400c070540900c10700740440c0c001078151324505140c013041113000b000c2c00c174000d01000140300010302c00343c032140324400507540580c68882c0c140b001d9000346510b10010300801051a0000b030244000507039404075400c44014080802c91001c11300003030380141d01a00c56601d03010300c00400414112221000d0081c0194000d45401070446c1035156240c62518480700090060010000351140309149036400100000e10b203807404401c40c0005118006c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 490089307 1250 490088057 490088069
    0x130b03060c07050a05030406170c0304021e04090c090207061b0906030207080909181905100b270f070c03020a03030b0f0a080304150201090b0f0c1b0a0525 68
    0x8041803002c24840d0421400490591201c1280d648036110400a0440510f00ca250f82841c0f205000254410f680310080c1c0303000d5a8040c1114408051035507001c00000e00d200c0381181c00c99605c0ca101c6010500c20311030741c4005c08c0142001a038800d80d504224003515031629264001c0c1450702d4400115560140400701100c103585001038580926140003030380ea2080c0c12a059002c0501011f025204070003d440a41c4203180c10200e03a020541c0200645200d091000c0191443c0c00080c0a00794840c0250003c03001078070000d021003d000c00e542c146e41c181280d00760003038030783d08080000c101c41504848202904060305042a6030355040c0f59600965592240200504150b1107491488140e1900074075031400c080001c3c014101c1c0307034448280725036980003031003404106213041c02c1441c1b00900610030040003170f07000a0b0300100c03079640c80303405042c0400c0544000c401c01810000700505404c0902000400d1000c0d201400b212030b42820302c3c1c2d10300282c6d10000005ca000403072820301d24074021100d520031984 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 490090557 1250 490089307 490089331
    0x30b070c0302210c060901050c0906092103271003152301180b040614071b05190f1202010c140604260904021804060303050306130b0306 60
    0x314038080b801c0081ca00b81a44840301410044180540c0c0807024208101c40e46044034100c0d03032451480c500380c0350103689500c54041e04000110803800c2100042c01d100303102825200d0740b11005043c0214100c40000c14107010741001c910410702c0c4001000c145005220b0804122040c0c41c030000083c4050414104102803640c0c40035501c80f0724401c007100300d00510300400c60099001401407940d03124541340e1303120790005511900c01d1a800980c03082c804192026100c2d000e04241c10702c1c1c41030312003c10141851020000501030b0400088107401142d90100300c075142810a1403404040c44280c90720780b400001031248001080c00b00d04c0000d074074481124840c1943c00c50700103050005940e20510000701808442e0030101c441e072030310000544a80070310301c46c00071040114054400a40075600411f94140c207502e00304040040e030300c1d0a4015049180700d01e8192040b2580c20800541142c19981c0110003041c80403040151070b2520301039440b904846003c00303004050740480029140d00d001070011100700 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 490091807 1250 490090557 490090577
    0x5060703061401200f0706020106060c0f1b0b030a1a0603090d081e090c011e0906050d0e0d092402120a11030a020106052106042607030c02031006030b07 67
    0x41901c10b1011900b606210545070b590060b6411716840341e00318000d0380c02640c01c6c6003000401c00e100b510301c4400315820410030483d15200e81c0d1107600302000500c1649800c2d06020012454a8091300158014034076401c2c0001e803910625240c980d00c80102e100f1600c5a9000e204120190f40045650301507042e140c5000051075070341d00c6080c236058a2801040825146050412041c4400094048030a1034241c94150402034400114410310003a0144000050fa90400402c001d03030140c0f0207030030000042c0030702250309641c45d0302140c50000c5a03042000018400b500070003400d01d0b14a49194a18010032003501884840480650390b0381d44654001c4800703200113000105548a029040c10040101041d240e0b140c80118000b070103080e6a000b05440b41240541100001300e00c00b00480c204803441c00070300200d07901c40d12600304040410300c051281800c680e85051012660700010034409100b51a40e02c400000e50051510b0601c0c0051185000d600d80b0b9402c0c00801c400031a055408000391400125003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 490093057 1250 490091807 490091837
    0x51e09180406020d110310170a15111206040f1a09041a01060804150501031208100b030705120108060403020c10020312010b0d0c14041404060b03011205060703061401 73
    0x284500d91413000c0b40381c41d02514101500c0110010341c000c0085608046203140c45000d9031354100c0c000c0c0100d10a036400144400d0014149400400802c50120800240c0c480c0d003130341480d6140e001c461150720440540341000342d5454580300c0c0000d54500c1c1c6100300030034495049444500c041c900c05130f5119084c81c400080030031141c4006550340c10780701e940082ca556954100a4104403040d0307011140a03c42c0240306145002d1407091904032a009108a195181103113016269040003400d0207180b10880d480101d60303202000000c6000d401e5030b981da51307550352a0381c00c0c0e003040002c181c0059607260060818440400d50008054030240c00446401a0390141040241e103541b15515614400142d0321000043c0b240d41080a060f10202c3ca40d001d1208880c80441142c90000201c5460b44041d81804288110f050b092400301c480180504000750f520784074510440c2c40c0d002640040e1280389140807400c100b01041c40540e411120030f040600403c2c2c1404124496009203421860402040054541c0b030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 490094307 1250 490093057 490093061
    0x1b020c0f031906050106111903140c0a03020c150c1b010c06091112010e06010e0604061a0910020d05040e1003060c1d0f0a1a0415051e09180406 63
    0x514941040280d008000c140f41c040050002445040d021071443c10740f2500c1c845010440b692a02c82000201c0e06801c8166015520344c0000142c52030060000d024890150008110642c42c9500907002403030307505400340030001c0c91203900c1d00303c03075601e0b00600140e40508400074048401c2001c414002070b500c410301c40100d540402000001c0c01042c1810124014482c035410007451048068030070703250002400e9011801c2e600741c40c0c009a0a030f0b206d20010040b009508040302d800c548001d001058469650a556040c0800c1015803200c4080004100c00c00b0f2410000034a40407a440c0094035a040994002412502480c482d00d01c0103442c0c1d40000d0f195a401d00341ea60055680424108241c400340803008050081482000c6100d9030080207207812880c001034000202d607001042c220b2100c1c00c0041641c07241552031550860482d09100120701020b44514280d89007100707076507582e162072551a1544c0c0c4440d114ac00e1010004080008422540318500003000d14140000e209407036071074914150b40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 490095557 1250 490094307 490094323
    0xd2f040b0903120d050a06050612070806040b03010c08010e073609110706050f010807090b2106160807080412110d0302090a0b16030c14060403121b020c0f03 69
    0xb900c80c400200c1c400c80d1035007030317115a0240214040c200304a9480b40700b4041e952240b1410480048a002c000a8496101d42c9840c1e610540c00f41c804150f40380081d0200f8251045d0140c19004620201c006002082c0d80c4000b240c1e1014407071404c04030380780640c025401030403150756481941c190409003020031103070b140c6595802002c40c0c110800c00340c0c0c8154201138035608a580300f121020304210100719128000700503207059808120280947c1ca142c042d10900600800000a4006203000035142c01c5079a9401c0c409083c0c0c2864015081d54035003c05801e80c6c000048884c0d40601c02140305000c0102d03404040c190f80140d0091a920880d240d0520927646c1d07003002071269000b44120070707404591952580190903040802e50f91440c0e80303503c9100c110003600404002c240c04030f03060307441800442c1c42901c03035141250181803154000c2e19400300850402d84221402d0700411180612213144020718400d051080703601c405c92654800c80448000e4940070840b18440c419140c0c80429000d40c0e40a202060f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 490096807 1250 490095557 490095583
    0x70806101707120b0d020306130c050613060807030e0a0803091c02010c03060504020412110a03060c020102090a090e0c100203040806090a03110a08091504050301020d2f040b0903 78
    0x103060720707004500800720b0720510f190321401410700304040c03801d04200070b800821950040141c11281c2c1d501c60a00c0f005c03010a80c06448600c0e00280000d00d54540c100141000d80c01000c248101034148903001e80f1844029040e0802c151804120059007074020a0b841030712035001c21a03907940e03114808101d1801500031404400fa02d00d00030348081580d015401000c50803540e49041c403105076100c0800c01240114031070801c01054450203036001514540b10072a40185c0186054602c9440751506401c0b01c0101d1800b00c0944c2d40001c281f03085140125440c03008181014080c082928450b00c1c042d01ea00c80414100e003d10b50103034040800b54002c3c003e4401030480401290080d1400302c20156035101c501d881900860305069024a12000100317a060080750400c10b01c51401e80c681d000c2c0075148107002c0c48040000400c2c030020400b56000e00040200740362500020800c0003045401d01c0c0c4285021461804440c04080300170700ca82906401e840490792207558150b140c0500002203400d04400b40b4001c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 490098057 1250 490096807 490096847
    0xc0201050912060912070c0b03040f0c0e0a0b22050903190c0c0918080c15040b0415021801080604060f0810110a0e100c0816030e0907080610 62
    0xc0107402c001900510802d079030f408030f543c0c4440001d9038440c01e124481000e0b015880c0350b41c05000e6049140c3c003c68005d84540b100100703401031034442e00416001500584c00880a40042c04540340c064000c440500d0300803520506605001c040211604010030b4400394401c2d100c4000440c910b400b40240d842c00d0b207105c82408801c440c2114000e000c0190400e040780c40d070f0841c24000c154101a8031426000501d00a1151030707107201038076500c01942103606039410501c522415080104404031b45203000321300c5904400040e013010b02d0510601c604c0c01b0501c000d0184140000718804400068a40614200382041a0581c4804000c01c0c0038000300e80203a800c8002500c00020103020002c0d0700790050024074410040c00e0304880c0340702c0c041d1145030070180c005040d54032038032000d00e00101c0800e80b649190821292071407a43c0d4960080d60041d4204403010382c2d8098000c400e2540241626900c0002181e140d125854250400340000b01e026041134086c42c420350038410490300568040c6180e1105080c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 490099307 1250 490098057 490098079
    0x4032313030615050f0607050f010c050a120506130e0f0d051312170c031306030c020f060c040b070201020a08131a121b040f0b0a080121030c02010509 66
    0x2200520340c000d1000700c40003460101c003200c207855a54580d1058460040003081040018400c2014a030441d84040d038180c040c0c0e02000300d01850034401c1e84105005030b00d42585035128940040c100c080d68a0358031400c81c1c01c242c1041403d9851041120b81800c640100182d03c06500d030071076107024000c0842065501c11701040c100c2050f00007010340510700b2244081c0c88895140c07040d00d424000319100c028400750101181003003491050003d0728802c6402002c0b43c0c100403680d0701c41d07440028181d106402003503644002d00c0d9666814041d8018070607403007005241509000c01404070601c41d0f40700e00a00402d02007081d00c21a07100340000000070385c200e01d22035220b414074482c1a02c480703d64441c04207859090310000b0082140c032019211703001584100c01142e5501c101000301d060510b04401d054800b400c200100b609852414064080e20301c040c5a291a0509a107024240c6401a00000d00d5600301c6c074031000149641c00d030307280e14281d41490044d4001485200580f03032401000f540c1d0380d2004298607 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 490100557 1250 490099307 490099327
    0x20d0204080c0906030708030901030902010c1e0b0c1e090109050a090203010f09051341161211040207080714120a02101e02040303020601060e0117040323 68
    0x408486000701243c400041e903d510f002c144d0b0790741241c442d42c2000d42042c4007210031507009a20420500340103041c24810422240d4401018807007148160f8400c00010745240e040c003094100f215400000c504a147c0b812482440350450070f0311240085e00d4034000080c91a001da4400d0b040040244030103016015002c0c1c44810f408041d400c2409945503800080000142c00b142d0390080d10300411460854112002d403d8582485000040b0416140c040054100c91007000d00020741300100c000c209078a040070fa91504a15081c415003103400310003c4215041889120b1004c40301a40d4603078020000d14130480004082400390088440c060550900840c1200900009036401440f00540106503a880840441140454060155114010f0f0300491000180f48880d9214131200d003025810803000481400001c410303603000750021030040e08200c004001060300500402c064400c01d0905602603080300e00c858811301c400500141c2003140a5405800700f1040c8100101c0c1c0c0040d000340a41d42e121000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 490101807 1250 490100557 490100563
    0x807180e130c0e01060315051c060b03060a0c030e060402010e010804060e070b12060d0b0c0d06090e07080d05040312140c0f07140a080703260309062215020d020d020408 74
    0x120949010a0511450402c14503247c2109010350350300401c00c071005c140035601403401d8001028116100c0b0350b1100c00c500507a03410492903110f4464690041807410204000500342c81c1d002000082644c002c90038440140e81100b082ca001c1c030300a103002c4105984904042000e80204403441c0d14a00424401290050081340100340c0304141e40503100e280e4441c00d0520010341d45440c000b500b20907040300410120030030000180a004036102004c03c100b6160590f142c1202c4003d01c00110944c4449410050b600052220300c049521b14240103090918548030000030100581400c400c101c103914032000e00f801c0030000c2d9034103680c4884c00c4401881000c940140d86001900400348103080c41224042d4529003021114140c2e10f419018203000c80c0b031550f441c500070104c0701c1460051040303c03466403100c000040295100d01026001042c007414110792448804840c0202e01a41a001c81c10400c0440c00c00400c5540e8641c0c1000e006a980480c901c01d0700090103980c844d038180900018000800d0300c400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 490103057 1250 490101807 490101809
    0x50424120605070813170f280f0e010f350c040f090c050720180f0601112d06011403061603020403150504030807180e130c0e01 56
    0x4a00c1001540c45025060300d202000f124000600c82070740c5d02800015640100c0e4a641c599100c002c41d00304030840c04250101c0d0030403030f0240c502030140260300d49003041ca19040e0040441d942040704460141000042ca245a034188450501140c91010164544107500c0802844401310384880100b50180001140207001c0c100c400302d40707100d01c003c54040d800300d02c01c4074111801d0001075543c0a02e40303240c640c040c20303c80c6507100038020280034240200b80d441071200e18280c0b000d44800540c051020800070108007010445501c1408002000240e08100b01541e40011007400e110380c030000a070b40d81500c0c0039005003e580c42d200d000c13400a41500406400700043c540741500b901c00781d030303200c01052007080d58085003180c0c943e00410110704a010811600690311768185000761400e52a078444103190710341c0d0008110441c0c0d9136030401041c160302484107030f003014641c03505001a03400b855000d440d1442c9401800c02054400340410640d1486120003c0c00e144d11481501c070803030351001c00c2800e480013 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 490104307 1250 490103057 490103063
    0xf06020d06050a080307170c01020a110d0903030903110d080a0228050d0f090510080a050f040c0b0c0a0f03080615030906130213051018090203030405042412 69
    0x20018007182c20f00d40045101c050300c00f140011810f040068841e61605c0109a07611003c81d0300400444011980030300007400d6040b0700f07840c3c4051280080d00341524201c0070302d002404102d40d126003400007940c031403403030030440c1e400c01602c9500303101141c005120b074000700d400142410750001e1100c88042d000f007161030000c01c00c00c0035010007210b02d2044e001072001954000b041600f0205840b03d03040e0266002d0390b0744580038940068050307207400c04103540d2400c1c0460440400e508070308100b030603d0a4010241d10582d00355607802c89082c565902031080b81603001e041444400841c110266400030040c03102c01c41c1d0c000b0380504103c1e50034100074205100c180e071503074014503152519482c0540b15030304590051610200910480da61005070310404d800480c000c03680240c6900d03503c4d030500c040380038407806240441b10007001035240c00101034414402c442d81d00416414150300c1805030fa030100c140e404030fa40503500801c0f071008a00c500ca014144c804441c0c19100ba014001207101c428891030320202500c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 490105557 1250 490104307 490104311
    0xe0307060818011a060304170f1207020307020f01270306060501090b120a0b1309150b0a06080412050403050f030c010b06040e060111030421060b0411070f050a0f06020d 74
    0x30380062942c2030f2041420029030242c601d00300341107117040c44402194440e005201034000c42c400040c1e81e28055100303120100340a00d0200300e0700300c07801c00041c40c030740c01c0000c41c002540351031499800300c1c922020400359a0705116040303842501c1c030018034401c0c00303048071000c0c6804d21007030f2a446c1a000402c1e150185d20700044002502040043c0d02004540b03600b02010948802c0d6a9031b203129038003910b2030300440c5821544079000c04000075410700036803590a00c10280d00d611003c01e611110101d81024010902c01d648815042214903004490541c0150b0082202da411000341d89080e9000d200340d40c0001d10380d01c12103486c920542c40200140c0351412030b401c02440701e80c0702d1004000c2d490003140604040d8400341c10200e140366018081d140d40e451302040c2130b05d0800365154802e054410f8134000030700259803900c04102c1080700031301c100b0202c240100d8080055403a1020802d0090282000041c041c0c1503003041841131040422980012a50010080c50819414a0008043c0d001700c511071800c28 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 490106807 1250 490105557 490105591
    0x1413090f020a080c0304110d1214031303051303210311070210030b01031e1e05040812041401050c0a17040b070302090d0506090307051c1b030e03070608 67
    0x1030050084070381d84900c603511000c45450310007400d035155101a0040f90f0142060b034149009854805488005078010104005003115900015200304c0703800d040c404081608004002c0703032640b1200381004403a014030f081600e550b00d00b0b8020300404000d80001d007210a03074075203102046055540c1401d2404040d9400c0c0203c1b241400e50300202d0081c043c0081d40208150001c8201c04c0c4658010207405805140114800c1d080c00304659086005e03008890000d1b444410320706c0c860126010700750614403000ca0800071490513848103c0e01d03004105a100201d01900c1c0400c0c00c0c441011022080300b00081e000300058209509407041d93b5200d4035450340424002c201592880c50100e01c464825034210006842550f0364400c1200203510200c40b040d0f02101010a11020540801100b4810410300c2c008542d01c1c845401c08610302400c410514083da4a154104800c90794403400088000b001d0300341710494030620b490240e40c50100ea0074806d80503c02d802c400a0f6040c1d001b81d98030b001e800781080c049041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 490107913 1106 490106807 490106831
    0x72907020a080601210f060b0310050901020301140d17091203071103011b0c02100c051c030c0903030c0803060307120b040209220b07141309 62
    0x5a003e1401800003000c04500b403400304d61101103006005100b507840401c40003080c60003d200c3d80c1c45411180e8507440c01c00141118000301c110078016131600f2480300c1d0007504244070701e03040080f84c415101824144801500705054105042c4c0c003c01d01e0071290f1030b0f01544504030b440e4016051280344034055078244040c1890340d1107984064040d507c0c100401d425900e669075001d1010a2034036180140c140c12050581c03085a0545104a80d8800c044098a007004120700141103402031200b010255030a0700c0052290701d01340d440c01c0050f90070305502120540c440340401008200c0c1c074402040400c40380d41c0a982d1040c8010111071155032240400e01e606600701904558481c001401d00046113040c41b6265400320084401e640750340409044840c40c0e1040b080c000e07244000d0701010030940c9220754447c08154441c03140241d9110320781c0580c1280c03102c251240d140000e213040e000e203101c = true := by decide +kernel

theorem cover : BRFrame.Cov 489928057 490107913 := by
  have h0 := BRFrame.cov_init 489928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 489928057 ≤ n) (h2 : n < 490107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
