-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1206
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:45:34.871347+00:00
-- url     : https://prove2.me/submissions/09b1ffa8-b848-4465-a8b3-53dade42090d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 216726618 ≤ n < 216906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 216727868 1250 216726618 216726623
    0x306032402040b030c070c0e0c03040f05030c0d03270803010303050a02030d0e3007020d020f030d11070b0a05070b0703110d0b0a0f0f0b0711040c0f1701180207 70
    0x2402d01c00480d0b0b003070601c4007544c4556851048240d4910306400c3c1a08000600d6002240c41500c040c10030408810903026a40c0007030344524605000e54003850924114010f0006000c114030070041580362003a8580c1290030440c00809052450b12268030b44136520700c0c0e0180025009032410401000002e224034010080a169841903e08090210340359905450a03111940c2441c0d04c9080003a00400c04001910032683c01d07101c030300c2800b0f50b011410842900030034101920601c02001e0100a5480d4000c1940c080e000c000c2c2030314140000c000c400307480c141600204646921600c0e10116903e4000000c0f035001008a0300e800b41001c030305a695040da02c2c001811502015290f40301180250a0a0042c1c107840010841c003240c166028014414408019404641d03801c4101104000c0c10102054a100740d80290305116501c400314140b0b0014891f090360503e411034a0000c411841c1f6a00c48542c0301c017842c03a5510902d1021001d020700b840d4074800c0c09240c2c04038901188010b919030b140d80c0104009407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 216729118 1250 216727868 216727871
    0x4050901050405210d060608011706060a0b0703030b09310b161106040b09011103240a120602031504140a1508070e07031b1205060418140c0103060324 66
    0x8104080c405c01e8034201e030310603400300c0c92844c0144541e1003000c00078981c2d482c40900421113464102c4c0064441e40144c460b0800c601d00c0069104103140c425041005144009001003801f41080010f64602c4058262034668080384c040380d039003400000d10700c0e1742c4285400c01240c085544550040c210501d4002480750227021001b801411150000c0c09224822802407041220b82d240030382d0050301b996000654542c40010400421542d00c400700e54920050381249044c0b04210035800101c1e032491950b80105e1039061007200200c04002a98009620468a0700300400b00500d08909000035a554600d2a51088143e03000042d0101c215600c8820002e4812070610003540d40d0380500340c10300b10150000c407100c900280c01c008d100c507054080c0048001e4225a2585039032007200000740450101d00c084121983c580c030101d80d00d90b45a401c240f400070f105401013030400c4103502d41400c1070210903808031000d014002c0521095802031043c0c9040342d070001c40080c20b000904a0700360411071820101514903 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 216730368 1250 216729118 216729127
    0x3010f1518210f050a110f010527030f010204030210030b0f040906022a01050105090606040608060a031202030d0510260328080105031219020a120e0405090105040521 73
    0xf0f2101c01407000380314081d50141409150505101c3c14001e40c6500c0f4a0107405012880d11003a42d0000859091402c2030b0f48542c003441840515158607941c0c0720689a00d84a0b90000d000716031019030081c001c503482116065400001c500d0140c060307901c90079100d544814904402e05181c107080d00020388883c4134120051030140c4144150200105103a10213622403c10102504e10031000d116590141c041103441d41c116180001c001002c80c826030080390f040100a5000c111240c8407014100d01469101c01c0e10f86e0f01040342d11009640307801c00c0c00341503000303400c080108910303a144166031410365208081007a001411070314140f101204040840d2454402000f0114104000c1e119083c0020a6111418a0740c2d080d604014240d001c11382005110344c00c50300300c1c4c110a0b80d01108541400c0340e00e00c0c45007810181a0030a0341480180c010162690356644220011282c2c0103100705042c440444080140c0e03214000030b03908a410840d0001c10f640e00c000d030440e48041940b4030340300840e00309814041c5003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 216731618 1250 216730368 216730373
    0x211104050a09020301150312230a031b030b0a060c0f02060301080304050a090509070e04050a050a050d090b12070e0a080d03050a1a09060613080303010f151821 70
    0x8403141116007001403a0355940b0003046280a0160052041030650400082030440c1c03907221422042c440060f0610200505090300d640d00c06a94180100d0f02c0d070080382c1c65506840024001c1c05542a45001d40140100190b05081c06841401c1a5a1000c1c01c3d040c0c10707a0a01d4800d4440c40d0756401d060300c0c1c6900341c007001401659204d00450107054002e0103552910700d002c080c070000032140e42000461a081400300003071090001703001c0003120130a10302c1c2034407a2200d05025040c80108a00580140290314020040c001c00090050f100050750f600c0c41d910540c0c6130b180a4003401340c6508a00b01c01c50700701c0402d2449115904c45000c4140040c91010802d076202d09040c9000d4022041001203a254410001c01c11102e20403041d01400c40b030b03010100e682c01c0b0700c001640c007007008060a2007030b480480c08034030301180144030002411440c01143d50307a5840b440c407083c0348010351059030700150f0102c00b91350b001d80c481c6000c0305501d135031400c00340c9056080140c0c01c1480d14011181c2c14403101c1c00d5842901 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 216732868 1250 216731618 216731621
    0x20a03020c0609010c030606020a0b0a1a0603070309030e0105090a14042405010801050f030a02090a180302160911040902030a0b040204090c0306050405011a07141203090d020106211104 81
    0x99901c00f000020076441049001e800d49100303138842020341d0043e0030303980c2c041012031484035403145440700009203200c0d1000c0a000d10030440240304cd0081c401204200f40300b909036000e80103a500a440e04440c0100030740c01183c16105080e0541d4004482c030404200c510b50540d05c000340e40c1c80042010070201200aa42060041c1c1030701d1201107401c0741d0004210f107581000300c590243c00c066a00400f80928070001c25950400094000c1c02406d1180c00105080c419a000750b15090b0f000c0f201e03900100b920b003002583c8000590a10241034610140052404207520407060303c0100f40e00c00b5800c1c0362400340e0020081d00020124402a82c6075000e01007070303945920050002c0c0810980003d160568a80b0060440c0d542e40c001c6405a0b10f010014000740101d403440c4c0300803d05d2402c0ca9940d03031949107041d404400700700d0f055685d00d1103441c2400c8501c00c00c10014500c2005483d0032101400f00269080742070301d04c5407040102007662030706101142005a01c01004aa02401c2c00c81d0800602001140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 216734118 1250 216732868 216732871
    0xc222307080103120207060516230a020406090236040f050f070c0302030f16020406090e060c0a0819090b09030405030c1e040b031623190603020a03020c06 68
    0xc0001d070184014003c10850190750031402005100604801d820280064401d102c1d0405002c1c1040398811414204002d0803a07140d0b81b5041210000100c0707080c402542c1c0da640100c1012442241006000325001c807a602c01e0314032020700e5480c91030140a910840c10656110300c4ca044403a0200068069101d4940340960400030001c48000202031070603902c81d0085107005080003040102d151184804a41d0010540d11140410b8414541e68114041c035100000601e15000790458207080000940300c540b0b500090ac00d001d440140c8680d6a18000900840e205201d0b800021a101c1800b0495420701007003103543e41c03948203400081001c03564540c281090b40c1154046400d500002c0c040c0806c0c02c05104e0440441c1d002d450030b800c69000e003c1f010041758a06011a4011a036030b6071038280075034003000132140c240e030a46000300b000d0380c5520300f44105031429178058000002d941a13010780b80c1030285000d07034000030381c2810740c074000e0500000710040e5003e0350440e420103400780031111000006003d910b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 216735368 1250 216734118 216734131
    0xa032d0e0f1c03050708060a0b0f04050d050c01020d090f03081605060f09070510090905060f090703090c150c03030510080d0207050a0608010509130501090f03030e0c2223 75
    0xc0c61000c5090b40c01010355200030315460401000900b4080c00791a41040341c01600c0400000302e84840d0180031580d1a030080d68005a800542c0700002e105110000c5241d084182d002e900f960f84a20743c1803000d032603501e090321030710041d807001d84010008124004040e151000c3c0300c070034288040540e61600c44c50041d060341c946500d000100280310728408100045001024203651401f21041201005480c1c0c034014482c2c1c01c111520742c0b0004e041a99401242080c0c103000504207882ca041c40200200141113110040710048007400d408240400c040e00d110240d10303800c0e0b4a20310300000656040300904000303400c0c0043d0800e0300c8804643c8641c1800354200440007640140364140c5807204200d01011594400380a0040510051085448086032194414107035082c219000d800e42c42e169004103034050019148207000010707802016071617002500035402080481e1023140c00001000740442d030450b0320350346480704d03106110001080740c0c01c51807142c10001d1904001086154650002c0e14080301c06 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 216736618 1250 216735368 216735403
    0x403060504060b18130b040f080a020d02060121030e01140406050a03050f01080703020d080c070b0a110705011b020f0306010303030c1b0807080705160305030a032d0e0f 74
    0x3c002c950708000c2d010700d080b80080d0b8500141c5081c0f951030b0700c0305450b8541000c2c1c0168841000502032007045000007000c207900c00c022980e181030500000303488000011414006014010000412040c1c2c80f00482503042c4807240303040904200e0b9001d40b07410301c2102007030b070510910842d40100071421602600003403c7d10f45885940d0401c92030018211a002031044206003481d00040c0180c810004008041d40e074181c40054515246003410181c5000324001041c8520880b540441e049962002400c0c04419a0311140107078003000000030741358242c0e40202c07800a4010b0780400b00241a403100c0200b0300b030010b04095502c6000302d0109003001c0d03007600258003003500d03002e9048142d0307070054030f105a901e40d20149481a90090303540e02914445d144000e07041c00c00204180042c080203100c0340c0340d43c10300c0c00718500086641c2d181c0709441750010101000441e1130038004c4d000507016881c04a851402030040c03603808486009914000300041110202e03a489a100804080007040211500c103400000b0b2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 216737868 1250 216736618 216736631
    0xc0c030a080d0b0d1a04140f0106031a070e010f09030206040f05010806030a050a020d03090801050f0115030606020709020a02030403081b0c01030603050c01030b01030e0a03050315092505040306050406 88
    0x401e0340580700a0103a10340540e0b040115800400d840c040c0c0b20085c2e16500301c1da05072075250342c03c10340f41e004410311301151107004129181d851204158000021248159076000319801500180c400d1034200302e800b00302040001107000c3c003c1d8841d12030010b10340c805080000c2c1494494000c10460b41168000080f1350703a524806203e25170700480c22550148089000340710b5200d80d6680e85480c2c000f80a0000c0c0100c503907260144c1014080c44011000d0480e05000304554a0400080c0000c200284a80710b41c00ca1729021490845109015440940c0c00c150001c0118a10b0030007004029402540800218001407001100080c0460001c00a034030000d941d5411b0104126101403d00e0007001c100c906252600f1020000207801007000280e10b4400d0030b0000d0803081700001a0043c0c0b211004880311170040050890070941c10102031406446c03244c0c000308200400c402400654032081d500000d108080c4612a0038103c44045d401403003054900e04241015900d644d0f41003074590580c1d00322001c903113400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 216739118 1250 216737868 216737887
    0x15080d050c10110f03060d0b0c1c0e1504050a14030a1206051005090a0f080d020f010903020304180b0904060609150605041a09032b02120a050c0c030a08 67
    0x40650070b444001d01c4104070301d044800302d50300a403181121122003840e022000071482e6a1300c004605a0707542003001791101d803901900e4140035030310400102150600c6403c03001d900400034400d26041c41d40d800c00800715441004000e102e040700084c42103465201d45a004000902c54503442006401c0941c010340d10f4040c0170700040c000c2802451802c1c006450030100b04103950341d00d030b00c1541002c02820f049984805440c082035583d0155003000800426119001607401300005050350041c0d240d600342c41305001201181402c1e9401190040c0041c0d1081c881401095220507180003401101e80c0001018240d04011403040c030400c41c0e040d550b0598900003005021081d0142e03070b1604060316100c1210500f00750020305607004a0046125480c94003228407541b507000c5044a810001c02011600d031a40001091035a6040c81110018800400140500034500001d02001110425032540e42850313201c00f000c44840c2c101c4040ca01d0030b441740c00b00c7c484864600f8811a182c9034016003005540d8188071 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 216740368 1250 216739118 216739123
    0x30621100608070b030f060d060e010c050a090e0c03041b0321030507030516030b0a09050c0405030c0108041502090a1508010e130f020d030311030907090605090c0306010315080d050c 80
    0xa134040c8456800c100308020030703080311190381580240222128030040c0640d0078140000c1c0300619000c94a9172900c825000f034190043d0103890019025942e4400142c0ca40c40110381c88102919542c134807550610110740081d0030b643c069071581c643d44d9160040c5d0b9561703032078999034100c56120080000700b102240c0d60320030f9807500446a010003641014010703800c000b400c2800d80320310559040b04041c0d0f5a155000c06641d0030f00400010301e030580007030000d401c20302002d030340070b602510880d44a8450903070001c15a500802c038440c03045420203400309109a81c1010380f40a5404030280b60703480014120042103c5100002c0307003002a56540e1407082e19810034206644810010301319000e19141d55401c00b0014048005800d409a410344582c2000c4c502d5280c15805000b40c101c0c8110f11b030780003100b0044141d000003030b40c0e41100e0003641c040c80041c1d0307150140700b070010b426199030300c00e8981040010025402070b00036140b40b00b0810950403106580755240b504040624012500286001400142c041c008 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 216741618 1250 216740368 216740383
    0x30a1a0a0f051c1a0402210c04060608090604080d0b09010b03060a060918020f0c010207140c0a060509041e0e031b03030609190618021914030621100608 67
    0x43d000e94040c44090384469245503500c108102500010800080c219116130b00c02103180600d0104c1d1441e04c10340401d00300d03203440c902031129003d540b40c0758001841900c64100b150007143d82e84007822683d180c075111109240c0c01f5900303102c421030716035113400700c5510381341c06507402007411116590f00da003044010880300444d9540a4810800d41e03000a00c04038280d4480c913040169220801079546c81c000f01d2000342809880902c1009500c08201031083c810261440300a002c1e5a03019101c890a2410800c03c4642c464003580b00091400d00c4000c00d1070800d503000c0640807030070002d6181100c85080c0784c036041e55480b00c1c0060030354201180d441c00340c054181d00c00d0b02015609020b07506501d0098007050703208400801c0003034205584080d03840d0007416071b8444e00180048244d50042c4c2120008407001035801080400749840455a4500001d440f440c0003040b42080000700c28a1515a02c08119604112560380b290a880030740d4551b0000300100305100c95801541408100103241074101400c0085 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 216742868 1250 216741618 216741649
    0x3070c2013060303080106051c14180610140d0501060f15030204080322030b250509010207060f02010f09060501060e0d03050702010c0305070206031e0604090206030a1a0a0f05 77
    0x2c1907014000079030084103040c1565003034989251030302d4400245140784003071140c5902100d0710344413600b02d03d6140c10362068487c41480da00c07880482410608155540c800b158001083c0c66105000d01c0404400c14041100c1103008004240b401c5503601c0b1203084030311903400701040109220040200301c800000c0c0010756482800d045082610348100144c59105104201c00c2c44a400f14107400542580445203015682041c040351040c036040b0070094820480800b07203184102c1d4452090354441c440e0048800020042e8040c007030103854803905032590f007132410700704040d5503c407241c81c40c0054240c0b150000c40c0b4000d074800304603540f4040000c0d00108640d10242d0007514a944920013080d001000c84101070380c2840e14000080250070100d41a025020001b54030a1000041c42022200f0030301c005440403c03207c800600e80c03070784401c02084510030704000350484c50a100040c0c404039641c3c060f1314000318103ca10000c55012200050031007200d03030424558810542d00500143c20a01c0c0100b06409 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 216744118 1250 216742868 216742871
    0xb0301020a0504091812020115050418020d050c030a15141308090a15080402030f060603101a030102040b0a0210020f0d050a0e060a0e0613110603070c2013 68
    0x622820000c18500c074900804025648640407031842c10300c4400317407824030f42c0c00c07200a44e105020f904009018212402c4041c07400501880003203a940b401e40f03c0e410b480108010800351070380082c4e0034400f8010600748161401e0298101c00701c5a40c6050183c0201c0074443ea06104240e407007a0322040854010500390754500d0b100c6000c200c0e80d0341004814055481d00000001e899841d1000003800c2070070242c0103041818022954140d80c190072250440c050740c805c40642d41f208404c00406903550100b11003080d41a0320910380000b414a00d03a02031040484101050088903441d14003203801da038002c1d844443d00007000070300360407120790520100360706129031351056150a965903490070180c003401003a1502203035100042440054940d22058504518406940451402840d80c000400c04100d185400c1d000e80f170001011961000b00b09107070b10350f00014850030800c01005020094200130201024042401c02080110f1070050900b40092900c0980e42c15030309007a0301380903840c003d4903549140300f03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 216745368 1250 216744118 216744127
    0x4050c0c0114090a0212070f1403100c0e0105130b0c0f0609010605031f0209090c0c0d050903060f09030c011401060909020a0806010503100905090601030303110c1209060f0c0706030b030102 83
    0x1003004210320613000c4d011a44d0f000019440c0c0d0026007820011340c05641e03030b0001c0010000d101d0b01e400c40c5c800d003d008110142c030f0395070508010304829100d00b040f556000806071800c0c50a82e43c003650242ca43d508403030032408c2c841c6444070300382480d81c1d0020711000942e070f000300c51f21303074414800300301581d8445071140c004e00c4030618281c08665a0405451862600400484d590101c10703540d40c1540c0e001c000051182200d801c01841090b00c580c4880f142e2003c3c2d000c0e07515070300d1149003e441200d089072000f4008000a03a41d4140112100c0005420529035000801412030f40c60000d0140c200880c90180000c809540750480c09000510b00b03600c141030940c0140030b4098000c6c0c02101d00755204600382412643e95844407842e2001c0170140c0c00c80c1e004d5514103014440c00b80000a0054141da00c00d0b1000c00c02e6401040c1d41203c10f000d41c6010014550107004c0349507c5482501c0074046003080541194141130700fa00360307001e00346c11411400c5065889200e003000880c0e4140105000d5240a4000f103281 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 216746618 1250 216745368 216745381
    0x30a0b040b1e0f0403051c0c18030b0a090606080f01060f1508070806010e030f010f05130807080c1c0e010905060c0322090612110901060c030f0c0204050c0c0114 71
    0x15540020f01401e01c08405100050a0501603011103242013101c03a030040e000042d800c801c6c8000c001c0034403220001840d27816008000c005400707004003920b0300800c20000a17903440080c0e0020340710308241124010b80315074001500c404100010071001083d83c0011410038203190203254282000c0e484007804601c03034a000019035400c01040d81d080441d038500300c500ea5030341c0c1c0010395841110811b881d4162281e51424104044194042402d141d07101809000179128aa50865103010f2500054080f810810010000614940040998060038016190040300c00b08203200e1240c400c41b0746002007440b000e120906036074000c0c80d06000d0f003021038005041200c0066440e50302d00a5010350b112071040030f03c014000b071041c2c0c0f85c90030051034816820320034a9101e40c5000b40018081c1d004aa203800b104040d07180700e25140c9c805a040c0d800c5aa101140000075450442e5070030040350980f03081c01103a044040160f1a1802098400e84400204a5503000f100d40110f084407200100a038007442ca820a0115 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 216747868 1250 216746618 216746671
    0x1b090509011b05090a030c170f0a030504060c030e15040801050603300409060303051b0f061306090506040b011a160f0227040606060c0c06120209030a0b040b 69
    0xb0950301d40d2800d03580b00c64010010600c180003035040500380004601c000100c480040442c1c0e003006000009031401c601141c040103960b6005910010b000c0340d400e100038800948a00380002120b0302074545440c591a10320086088c4080c280201f0b440d0000000342030103900424001c0c517400c418158001d150f20165000854003030301402010310414441e00401c0fa440e02c1c407210668000c0d0241c800704015413981e03031030050265030003184641034550201c0000c02500d80c0100f640007240030080003404031b81c0c1c0d82039071841e681036000d68200d40542e030340c030102c20205a04009031449188510b080702d032113505010041a20f48100c018030301018004100d049002070950098038002c541c01100113610b03240071710015805a0308414249440ca58150500b001d25021440c0035000d940035980400034542c413a0411590800341280c00f400606000b18100704091140707068070714803102c00704010300b8000c500f000a0b00b000d42a5806070b1f4098036100034001805400c3c0442d54009014000194001d081e1415540 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 216749118 1250 216747868 216747911
    0x80c010c150f020c0a06140408180105040909060e070f030c050609030a0f0f15060608060904060615020304090b06070201140304030903060504080304030807110c15071b09050901 78
    0x80803101180c2401685600340e4110210403050102d0554603507520400503944c0d642e1070407068426609041c59034051086100c0054003841d00280c109160440e40180d580030b00c00b6108009041001c1084006007000c003070703c1100095031191f01d002c500e031906011020b1625a91b80c02030108000c81030302c100000380a444403001215019201c141c0c440c142200060b0500c4140349020706500c1c40403644008000e5590004649113200c1d0004091101503445030344200c0b1001d0103650049000180801c00c20300c0d00308800744d40588100c2c004244103444660410f0305500d0500981c0140c0d001050074070942c00305002d00340d0170b06d00945003182400c0c11500000e00400c03444034000d419400000128080c98459104140559080107061102d07060a18203c3d440b5841101d040c1d001510620220b0310036403041e00d201d4001c24108000b8072400701280c00b00b1070032087c100b40c0350103134041c108451000541c0d9000552808a0054882d088661600f407040068800007010f40410745d01d1b264800c10740300008404407 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 216750368 1250 216749118 216749123
    0x903020c1504060e040b04050c0a0816090302041815062102010c0b0c04150c03030b0306090c10090905102303030a080c090406140a170303070503100e0705070c080c010c 74
    0x100e60b901d000313002260007000c0b03d1004035042030909017042000c0c44e080c00203003174054181e1f440c01165075452042d081031a0760f9410600c001800c4400420151800b5000341100e0b003070161039040d60450030f0391000e0f100c04c0540b00001041c1d0322100c0411000c080002802c1444000030221603590b100366000030003521031520001c08482947c400306a40890030812b8601038084640052035400307041001809210301c0c080d007103001030300705070142d68203003000f1036024082d2400300300a00c00c0d80300400402c4200c0c0800c140ca001001a001400140300403180182c60007001c0a450054000742000e4441094600d2080c0c110001e02c4d0000840806d130718000201c0c2c140700b1642c540514903417520110110345210350075800d542319003054008510403002c0881200c1c5140219080410a40e80710407800c100c0b8042514141190010310000c0d52090081004503404407000402d000c401b80c96210802c1c000c002942c144000803804640b01080104640b4031401900300000203100c22030118000038040d45da0b56400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 216751618 1250 216750368 216750377
    0xf17251502030f0304081c020409091118180f100603210905092508062b0206070204090f08090a06092405090d0b04021008060105070b071e030903020c150406 69
    0x10f01c040800090182e05820900510640d0f55658ae07101c034401034640d444084c0c803400c6a0f041c00ca14207183c09481910220401c0a8041083e941e000385016482c07403100c00103103207003d0f0300600b207044a0709110f4420110391800e00003071000e09508214462801e490303441c510f101024421004d201d43c0112002084500861750301c102503407108840102d642d040103c5040700d241007110304080f1608120700b00e20410090b14465a420704820405400a070220302518107500c4050040d030250400400601c107140c0080c2001c18030307004581d0f88088044c000c00080e03400d0031000c60340450918001c0c0f00340008244525000d01d090382032400034482000e018100090700c408084111801500490a03202c08410041040c01a215241801201c2c0c12048900320b116034500d0403d160040c0c01000c9550103203206035035640c00c4c042b00780c2d641e402e003d8028160300140480060704084030f4801076843d4000701159039000c14032140624020780b5003007486100911501001449083c411003d1099030100c5000d0b241 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 216752868 1250 216751618 216751627
    0xc1506040b0120070e0a021209070b0d0911060703020307061b1706030a080f0a12050c09090a09170c1506011e09050301020c010c0908070f17251502030f030408 70
    0x110514210180c0d0102140301c299008021091b003040d400f030822085001d00c1200030b9036501c08120344072041d501807054880000d12100c03403d00481d034800c108031407054007608592004040040d400b50000031080300140c0c000100801001241e003c0e0009003001071181d440013441c0d200010341244070008402d8850449030340002d2903035404100020132150071110b0103540720100c07400e02c2c15a501904062012550a50541054200780d201381845400c1001c1040d09101c00c40e820072224400103000d88000f00d8481c0350100c0850f581000a254078207002d00034035690500c00e0101810074401e9500c0307003180c1d4008400c00440766002440b40303080050510042155906a000c00d903250312860b0843d581561012460000002c0c0551003150040500d0b1144541c4541e80d03409144d40e00f15a005400a8900324041000403000740c0303200c01d03699410301c41540ca2010800e40107801740400b001443c2d5580f8280d01d410080c805001c04c1c0f800e0b124440d031000d1860a107070000f00c540d1601c80504001e00700c2e02e0008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 216754118 1250 216752868 216752927
    0x50d031a01121e050601140f0a05030c0408030a020a11030c09010603050604090b0f0105010305280b040b0415030606062307050c030a0506160e0f0919020c1506040b01 73
    0x5010784190000c03001280c00c01c503c04002c180082c5001c07a0b206000c01c2080801003034a9100400742c500d09944046594502101000304450340d0304040c140c416122014040490400c2040c0301500c1101101d600070204070145080031803100c80c51280450003908510070340e40203a1a207003082d80c1503d0040c103000c40c403034850501260080c401c2d0351016002e076480740140304c100342c20182a241256400d80e81480580c8500701090894003040188071840344090315002e0701c00c2c040360031041e01868000d200040900301034010030160303a00038109442e004580402801000300034812000546078078034001050018500940180416080304000c0103000030480700f041003000c002e41700280c50701400b42c030010021840c000390744584c04d41c0d8600d2416800781d040582284203800403840c500000744003e0005040c2001d00840c034402920342107880c0e8045c0c11110b0b48800600042c02c6450402008002d0950b00c03000740c00002d400a41410302c124207080d4080f04683c0d10203410302c075054100b1110000b40b04c0301d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 216755368 1250 216754118 216754121
    0x9020c0606010324170c2b02040207080c060414010203010b160206040306021216030c0503011203030e011a01020606060414060c0307050d0306030b06120706030b06040b07050a050d031a0112 83
    0x41c1e04100c404c0c00c009800300364240d2195410b6005641e242c21144594081010030665408075a20004480710181440383c400c1400b200b00041c0300d001800040c0f4040d6141c9130b40d19540e000040200c81507100b102404100000c0d030000d07200d50003070100218203550504002410300d2080e400d0308100f07442c00480c91010756130340c1400c5a00842d40118119512000300c2d80d44245d001b411264200410180e0500760f560b00c0c06801802c1034254a50350752803860f0f080401032101c0b02c1c18620242c0400d40d4540b03103807074200e100f4424002c1c4c08803040c07524039007488a88d00080c036003080148000d004490612040050081da80751150068108444050f110554810740900d50701a01e0350142862103804003020805030980d2208050380d0084443c482c50b5500c3c6414803020712110b00c001f200e01c0e402180d0030003007940300398090311002c040148018585641d61829501c00e4000e440181c5460f086038034000c04110041144100f203c03c5030805210582412506075003001e44d0f014841d050100c4c0c0b512006a100c0d66 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 216756618 1250 216755368 216755411
    0x921070c090f0b150a020721140c130b060a030b0d05061918020f280e090d020607020a0201080a06051e030601140d0f0f0b0702030a0909020c06060103 66
    0x35100c0400088414421900c09840304003c0700340101054400555045082022640007001c0781e0005c2c0b01a1385401a02d40d144d40e45190510190700b00301d0444d800207031010304d1002d84013811400815100f02c0c0c4504019015011640000ca864900065540180c0382c00c010b50b40c0320703c1030781400240d00340c0d600040b4000e0700a1003002000c2e03016076010000030100d01c00184441503205002080000300651982c51035500c0b002c00030358048408051001e05107000c0303100761540d544c00200e83d024140361516028071407460b50001d04003031500000b0014000302c01c0181d07000e07800c1d440c0f004000a052041c806922103640e4030020303041007441000111400d20300d4100d0300041201510450b104803d6541c600c40e12a20340070f43e284203000c0c1100001e05040301617490b004007440100844991413113550741c44011000d5807021669040c040800e840419000c800962081071550051766945405400051100600350007460301c80e80b042c0051a094000015081d40c80b0740d0a00340051841c4c020042d14001420 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 216757868 1250 216756618 216756629
    0x60102010e120f0f0a03050103050d0509030303280c0507110d0807030c060209090c071b0f170109051207060501050d1a15030f0109020117090604240507170921070c 72
    0x200002d2441c05c8035811351060b4102e9000c6ca09a4103120982e502c2101c0c144100c0c200203500d540240f02003404c082c1d00d180811504032490411300307240180e030030f448000c1e1350312442e040c0c02203480031801006100010440c400e120b48201c0d550300540302145e0382c42c50356028540b405001c0260522489081004590480305c2c0c101004200425501c0c10b810b981100780c1c803000381190342150b40d85c100c90302d0f00758a0420740d06852440d418003002034200540c501111810150490307580d901e9031415000f056043c042114100034070781d101030340e6406d181061403d407001a40024040c10000510a0200310390000070000e540e0b07445181003068907150a109000024800c0d41540340c010b10a10035007000b81540510a030038800e1301d6044500c030000e151285410822110250729401850004001502030305003140c02440301c0305142603070040c1c10b211208a41080b140310300412030302110003a42103a000c100d00c0d400300580c001050f68007891102a003046180301e01c2d0701110040030641004101403c0112009440d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 216759118 1250 216757868 216757897
    0xf130801051003140d09051c0602030f160c02130506040b032b0305012d0b03010f0f08010c090603051e09010209100c0b060108040201030e030a0207030308060102010e120f 75
    0x424507401640c41c402d61104403001c680365508030198140210b600745109140351900b4407200d1809007400080911424462007000444241100050b22407000d14024841452070340000e01d0203082c410b12074a030b03014142043c41840d120ba0b000680c0c0e5901c0802401d01c02d0300c0003007910340b1030f070008c140176055442126505025000311249030718842018a4600200200c520600040001c4180d00f10f500c03c3c050314a511010f01c081d5030000c2c4c841e10b2508890102050392a13141d564440c2c2d010707055082a040300c0c04202005508008c0a4580c480d4007000c0e08500c0001c20024058a41c09080f5031504d01c50542415200c50004070901d584003601c0d60306440c11002c58005180041a45000350300c00f00091b4401c180d0400320b107484e640f03d80184450198040c902203101c1c3c50300760040d80d2100b40100100d04068581d000842c00d900180301400744082150010700005046280203408808002c000700e04580c94004140820500026412a8030422150107903454030340300c100441d9841606d206400d80c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 216760368 1250 216759118 216759121
    0x209130c0210051008060103020d083c04050d06050a020d0905030408071203020607140d1802040b01030b030a03030207080c030c06010806010815011701060801060b0a140f0f13080105 80
    0x340c001c20703821030745001080304003c1c56a4281020703c010100c2d000300d403944c0c1e2020006000500b81850750f40310241c002d5030014181400079101c107000741d105011040403100e00203001141d200c9903042d101c454001d014149424281001c0214100c4034003d10701811064880c0d02090040c41141e0403100b04a41c00c1d0414800d080b030324100741740d90340e01c544128000d81c0704106000860002d0301b01c079107000580c181d0140c070745515540c0046131070003101200d80f0200c860412121504040f1441a0001c9824022a10b1010b450500400c0102c480b0f91561505050030306100c0e00300d5590204024031a41e5042c1801038550b10b003070812016a0049ca40c1c560102e120000b07500e0300c08800010024100d4120004031071a980e01c54070401d8803601c0121280c00d40706800001070000110303040c040e41b081c03840e003c0000380d0207a5034081d041c02e4441c0ea0340301001141000400c03410459101c41031070710040940e00c010b8070384405c4003201c652910911034105004103002c03078004080d0381e0b1001448000d181c0c0400a00c401d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 216761618 1250 216760368 216760391
    0x2160b0702011b20180c070807060b0904030807030506030a03050a05070c091a03070909230c0307030b0703111303230a0317150906010e0607050712030f0503010810020913 75
    0xb115403007505803260740c030170300e44121030003010040c28896102900c0c00350501c01150342e10903182c4c010801c1220b44688440352045a52100200c140c070950081d95142000d0810000280483d0005440a80680c01c10f07015007000c650400c041340c0740319501d03140c040c0d83c03500d00f42040d500d200216003118045505202404408050b803e0701c550100108a007a02e841964070b401d400f0446098000081aa401c18100a94201608050840074110401c255880c0038041d2002900785400307a042111140403034400e0145e000c3c0d05100350b800c0c01b112010140d240000c003204504d505141444002c0000c40e4203680c845600030100040c8034600c9109080310308403a82c526000d0041c8191840e07813800d01d6520b070000b90065450480848142e200a021550140c035214011108429007030320084e0801020028280040c100308000c90050941111031503002480e403030000c06140800001c4410441305000511000714081103a100d2862101801a0b0b1040e6001c0812905000343e4405180203240030340c01c218 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 216762868 1250 216761618 216761663
    0x20105091c12110d05010f031a04030903050604050f070524180d0b060f0f102328020105010f090902041103090105040b0105030102132c07090602160b0702011b 70
    0x41052070884e00303002c0c507a2039000c43e0800c41c038035200152404c0c804040c941c00348034120390350719049800303407600d148940d403280c880c103151480907141140c00342d100a0707004910140c24002a400b5000840e210300a0a054804d05803007001201da005164190000f1080c1c0c0801c00d550008510503806400c00c221120306090603494001d044030224043da03d9000203c007a4504102e02814208008000c0c0c15224503054089500b88226007860100222510600c0308062070031020380030001d000b46504a006c41407a8040b82680301042c0031100356810305005020b14a1030381070740030036510000700000f41e2149d240001000b07000d50440059105e40c00100340b006604041d044580f1450251210700c0d0b5507640c85051508038810030f1000d180080c4500e505101044144c691a210908510071104102c1181c1c01041c1c0d04200a0b60140040350803060104540c0b134040c0417507090308500003601c0c81c80c14509090700070700d880f038541c000f410028681400d0021146013482014440c0e00003401c61010001521b4101 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 216764118 1250 216762868 216762877
    0x211c1b032f0c0d091a1305130606140702010e0904110402030408030a0e0f030301060323011d22020d03020f011d15040c1a0f030a1407020105091c1211 66
    0x6020f100200511640503824020854010b0807107070300c1001e94180c0b4210603820034170582e0046200b540c000140c6545202141903800d0291000150851400384041d00103811041c54242c4c0d100c05000b9a030150b80c000008800e4040d040c3c0b0350345d820b9a52841c09130b10050040840c941d1151000c02400103024661015510480441b40c2c100030415480e02601d5403606100481d1550340e00070401440f0360b81c0b20380c1090304207481d03080341407444004490701c071411008242c1201003818451030800342d0782080209071035006894040b40501c0d10703070311043c615080402d400b0080e025000456050b01050710801c1449800d01800340200702034070503071400d4410003880b0001c0100c030f44135002030640300c010701070390f564000d076803040300d04100500e080090070100d10115802d8110100074070038403002a01c001c0c000c52144000c880005000d540a42284400e50b134040e000a04680c54403042003c42c16002030107007102281c0034211070364000002000c464800a00100701541401e003613642d0b010304510400341 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 216765368 1250 216764118 216764137
    0x20a0303060b03091e070513090b0106050c0307080f070503070b010303020f0d1b0c0509010b130e190b0f030706050405120d0801030303020c211c1b032f 67
    0x6100207651900340c000b450005541c0705a0a411480101085400c041003154000c00301c0c000350b909041d0b4440000e4440203003141441640c0d502da11484040013404685140540504d04140d410702009800c05170b62400b075010300038110100025074032070000044003942d40169005081b2031341c0e03000c14984401519000c4c0b1040f405485041c81d0b450300c20a01203104500580e0702da031082c0c1e0800c007007e5000c20f04c8400c9071007660081a10305000c0707038030380712014640e028044203d01305584070760180e50200107500d2684105a0700c400780d0b007071188811040312544254807621101080f0121381e500010044241c0003800e0b0ba141c41100760000d802c1d90400003400445004541850f10a02a100c61a8844450ac901840094a450f0050000034000d5020300000ca031518122200c092850141f00a200c1e014002518031403000310704401444151401c1c00e40303030034100c00103120901d20902c80e5260b0b02401100cbc03d045c1134840000c18074400041282c84045d045026840c12811003003910311046620207901c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 216766618 1250 216765368 216765371
    0x151701090b1501020d0f05160f0b04030f0206060420031f1203030e07030b060919060b190c020907050c03070b0a0209240d090809030d0203190813060504030c060c020a0303 75
    0x102e00b11074003c240806d0364030350a48540789480f2048514881c0c140c02000202c440d402d0303a40d904804110300c0100d15225030b1181e200c41c6081c5140c001701a00d041c1c030040c9a10700c200d05180c4822003015030248a500310041040d8240d0316621150038004011800b05800c0451b000d811034006140c80030110b6054003030780203403810000555800181ca840c0c010b680006072502d21142c0c0880c2d490308080000c140d2002130880a101007c0003100c1d000c094405540c0320f03985824002c00c41d9601c1c900403020342d001c0441c42e0f05180c1d00b0b1085960101d41d040384000c0100040c40000300300101001020300c110f6a403a42e03c048414114641b500b421002074000b007030341038001c011849810002c7d49000860000e0401e8518030b450503d00c440c1d05541c090482e4a804645c040740c180100b2442e80c030b00f00400c210010742e40e00a9902c1d0146a03000e107549a0130f034020102048481420311148504041064a455400c0f08020a15a0360307420241c442e40140f02d001443c1034a00f030f10300034a5a5001c241c280f13407144256070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 216767868 1250 216766618 216766633
    0x507020414070e0a120807080f16020907020102030403021b01020307020a0e0406110c060c07060b120601030201030509031602060a09080a03030506100f05030f06012609070603151701090b150102 85
    0xb8020804e05a000b030344803c066400440d004203c003800944a01d03842a82030b545070488216200e11250407441c00040d8030100a4034080451400e07803c0300f03901000c641300842c19490151002036075080d0505528030444401c001e994400e0b4800c0c8112290550082c02d5601c09a5594508100110040350192000392074007002c201d81007084011141920300c808000e280d143c6511610f02c600307a2000c1c40840d803680ea40d4060340c107540c43d00300d0280b14032640070016201c150b14500000d02904c0c402420044c0300d41080080c0c00303521440c80c020310341c80358064401c00d40b1801802015588140c0503000340c003071842512080010964941c025a10800c000d80f500341c2144103202042d940f260b8642c02c0d00e07000c208280002403030085180042544131405160100d041114004080e2104d01d1400c2c904003010681010004502001c02c07100d4002c000601c0c08100d1610b491084240102ea5401045e0041d101010881d03032840c025045006001e0f00030b00030b07800074102145081c165080b0f11404a0150182c580d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 216769118 1250 216767868 216767897
    0x1d03010e15010b0703050a0f0302070b0f060306090106050a1a040803041205011104050a09020304061407031505030c06071202010b030d0c150c120209060d02120f09030703021b01050702041407 84
    0x56031302041d81a290142442015041655460300040f0444205070b424000b0b03c0101d0b80c0c0d42900341c082c20b40e5004650042c01c00304145420010014940d10160307043c41030030002d640780d045c0300404994201c5e07078511095002903e105141c3c4030b01e41c4a2420341c48041404a01c41d154174400c0420306100c0e00c000c2081c04d44501a00c40c05005601c20385070b01201e08d43d010003103841c098008540c030038458000000d036002e082114102e040e000307443d02800a0750b10121500d0218820b034141019110403001090b0041880002458031321404e0740c0141132425082c0751840050003504803226040004056540f4180c1191000301103400848082d01d03c60070441003032940c0390303044c490b420442a00740e9a01c03008002c14603800b0301079844121300a030002c0c0204140c45003803d01344023602c400c903440c000007005814002c04001403080301501c20602500304004031000250001200262494448100b6440003c07500060710306001c0e0180c0607401504042210205510314864648101c0300e54441540300705011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 216770368 1250 216769118 216769139
    0x8042f010c050f010207060b1c030f080604020c0a0606050111030c07050d15060308070201080106030e101a090a02130e1e0714031807151704020a03140607080112050c011d03010e1501 80
    0x481c27015003c50401c00c4a0714007144520043d640c4100d000d0409880d2a0014001c2458040c40302020f403419a0740d040144655a40080541d41e1025004001d44c02d0112a070007054407803000e88507080c403800c2d41e545a0780400c0311445149a4030301106504100c0d050b602d0600d4400e60b401000c0c100d000400203000400c1040c001e1041c0100e00030701c200100040c841034440b20740148600340446e2403140e0f80e04801c45082d560b00105510407405100c0240e100c1d010041e10005040c0d0507000f00841c01041420800c0d00d154046081c595440e117402d0990307042d101c2140540c0c10319042000649240000010448906419100900c17190480c0084030311880d91099860030f20092020003c3c00154200a2240c1819900c0b03202d0b40c00c24001400e00c004d05590340d03200040380d080070100c1002034025a04000c107460f08000918014940c4c680b4084449106030b44a03900d076044180f10905000c245031003940070041d038030340792419a44058000c0185841243c021a41d4281c003142001000741c5010011642c1441c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 216771618 1250 216770368 216770419
    0x403030201141608041502040f08150c0f070c090c050705210406031a10020a03080906280f0f0f050c04060206070f030e01090308042f010c050f010207060b 68
    0x20f4801280c011038204604503688940508155101c442d80c070100480d1410074801407000b0070a040c005100c05181030842c90030861451b100308180c407101070410404215140444940c2951200800e42e110741234a80210780116a40003029840d24050255040c01e820200401300d05d80940e00f100d4852a0303501c8c4d00d414110014184401001c014402000071034003079008050180d0140242031081125000031446480b1030010f403c005034000c1802109140d00058003d4200400501400315480c028400c01042540c1841400710407404050010440d40c01d64003902c0c24030b00030325081c0440c07610701d851440585400c0e030b80c00c40103500d080e02041c400448041210100c42e5903401428160b0340710601591107140440085c4141a1117010300c0810030030a12640c0c00c180d100e81c076840000d00742410242030f0203c0440d4801180180b40d1482130368003000030b640d226504003d20780505003410510342903050044a00140c002503001050720001c014243e0018030720800191500d51000249405040400c180d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 216772868 1250 216771618 216771631
    0x1050405040b010c0533010807060c030e040c0305061008010513150e04031707050a09090509030403080304050a0201030b090f010e040f0f03090609050f010e0d1703010b040303020114 80
    0x404010401250809401c5070041180505204d0035042c81502c68505001341d0754510741c0039003800300030344001795a880750344101e4059180c145c418960405600360381e43e8055000d01c06c2840148101d00003050b01c510712480c20500007074424840d0702c005e031300090302500f010f5071600d00c10b00d001244821203d104045850480724014424074400707400c110b003540141024462003580100c0c0d03090208249a810342841c3c05a0b01c01d90b40c0041c503001203e60b84290100c054517a104016080228006d119804041042a540c100310002601cad00c84511040c51441039900c010100703a000310400c02400404241901c1c00742c000c3c0c070705000c140000400c100300054110307804654040010014450b550900448650180c1b02d809130083c1c02e002c648404418071031503042207001039451007092111551090561000704000c2d00d40c4001440d9400c0041d01003080f8245a500aa40c85542170b800d01c000310345543c1c80c1c09801a61b1541e2541c5070600312030280c0c81070100703a001d5800c00c031040501c8507041c00304520070751 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 216774118 1250 216772868 216772877
    0x1030e0303010e09010b09010e0604060509090606090c1902010b030709140c0c0c1305060406050f033004060519050301150c030c0203011d06090318121f050403080a0b01 74
    0x7070820000200000340504014003a660701c44c406e1001c0e413292032481c2c0c00f030b25900641c1821860030b80c0420055442c0c607004540525503000501101c0e0000052040d0041e4088504860590324040da004250041188401c1c0115440c0008004d003901036100d40824030058099403034003515400000c080e51030100114030484545000588450400b402070001d484940e0203480084039048005064071b032010b02c04400c0c46940740140000da00c0c10b4030540004120031707117440000d2201100066190081e00f5114010009802e10078500b90200d00ca04120901060441544441d1251001040c0e904030140c2040b00181070080300c0f0805004a003941d0407950300c0d00790b1203c2e5100d510021162840b00c9c01c4d040b014022901c005000581e030a029402c070b40c0c0e0440c1154101440281a102c1c502403003d440c4400c690402c00455140318000c031803a400b900030544050103031046c154001840c00c204040e00d8214024031100e120314030741098005500541c0669100850b41d105c8500000448280c0c240c1c540c00f14 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 216775368 1250 216774118 216774121
    0x110f0c01121e0e060906071b020d051501030308130f0609031808100b06070812090307060e0102090f190e0a0204030609050c01110a03020703031407080d0c020c01030e0303 75
    0x290301c00c204600085652140101c0c030304059031001030301c1c2c6864098240c40d440e11084040241c0c0010849140d00225407001803005062140024158680520303e14074101001b1043c40d0a40d00d40740400700403154000c01715680042580304006800100717010403000602d5550218420340315504041c100c1c075800c14100301e550340d403540c0c40400511b130090b012418081b52150342c1560102d01040702e030040107403c02914226079040119011140c40d04200c2e403065000340929008100b50b48140d40f0020154122424551030b6000c400c0c0c554069020700811041c01d000090800c8101074003e003001c1e400a84000b05079011000804c01400c40e2002c0d012200d6085400410100c004602c0e2a5002007840000518260312a203035141500c3e4440f40565066104001d50340c81ca5902245d42008a040c41c4040c0902c058180c0d002502c54015100290811070010002c2c81040203480440321210350012026950303003207006204029180c1125450098001c12144010a5001c2c0c0107422000031500081c5103113 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 216776618 1250 216775368 216775393
    0xf150305070e030f0a020103110a050409020c0705030f070608060d0503071104020d0905072108030c09010e061b0c030706121a0315010306060902070c0603050601022506110f 76
    0x8110040c024401c2000d401c6244409450901800f140013003188064040000d04d40009003d45648255280d0103400800c0003021646d4403e0503035007905da4001000d2780e581043e01801e40b6144454200c150705008020f1011a00c0c2400110342c800c0b902503031240109581c65030100528000240e80141164004010280c0051076421840c0c4140d1402000142800e03486081c1d9011a0310381c500072507041d808024107201da10b04e000018601c001c120025000b0303842d956a91070703d030b1380406429010310010225a00005a0240d0103030718850401421454840d042e2401d824070315080c00e00b01360717054011540000c000c0e040c041181801e486c00c40d11345400070b00b081d004000080048948680d94030520b10915102503a0a010010013040318030072080b82c650660401c0c20456050707500c142085841080b804000030603110705071044828500700010b02d9a100d0300140c2c2080e0719030a003506d050300c0d906250500800c5103107110007915a00d03a58005442d816150550b80d07000c41e818143c5c2203030300103a0300248 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 216777868 1250 216776618 216776621
    0x6020f0319050c0a080c0d150605040e0609011202060a0212030f22020108150609131b0207060e060d0e0a0302011b0305011a1308150106031803210b0a120c0f1503 71
    0x580c52180e0500040c1a983c00c04140d08c0c130025504098001480040d0400c020207405c8a40d40c0c00c00340c00c030b50042c000c0d4503100100d841c101c0f81400003401a940450409400c0d0300a00c000c12141100b03140c4690b0b20f1070001c40b1040107440803994103002580311a43d0070b0101151a0718101a1941a11104415120382e514000e9800f1621035041d0b015401700001d030950348803580c0e504d403c070b40e2000c40030410b5180c040301c01c107c114003400801c0440d84100703030800c50294450048241c0d5802940c1e150b5988602c0981c0401030072120f280c240c650b101c2c0b0040c44080507815400090100c0e007050000003202c14889003181694028440c101c006600c84a018401220390f05c000c1c60030000101c05c40c11078566410702c05081c81d140ca4441e904100041c001000a00e4060107045030070286445c1c583d424241a55010b00351443c11030500800351a500c0319141c2c0c8040c07075802003901410003800300721803a580382c914040d20755010344221502901d42d40005240c00031560802c0030b0303540d5800c0807400b07840660030840 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 216779118 1250 216777868 216777877
    0x1413080306060705030d140c03090a110406050d0f030f09030c09230103050604110406031e02030123100f030314132c0f0106050d0906020f0319050c0a080c 68
    0x42c2d1000c403c000c00c80024034104010214840900343c085151b1400c28030540303c810b001800e0a0a0000400030400ca8203c081030030000268440c80704507c45103e05c001c03d000742465040580c000105602c0740d014031030b2404081155074442d0313440e409258140300d41210361284900c00103005c855066002e100142c4660060424280300900024024965001101a0110a07442a122504a2000e00c07040c0004032940c04070a9400b69014031240c4e00e1551f0b401240c5150320a0000494032012000046613030a41085120200b103800796404110109003903181142c00340c5218003070a140744c0b000502c140d483c6d0034103400c80b50541c903214210201c2c10102c0ba100d42c805c2040030380211440c8808a25004045042501c81c8841c3c17150700080701c070650305a0800000038200d05200700036000100300843c1c1c09022100600d10310400030600742a036245c10f030043e000c2c00c0b000c880945000f000b040300194011b40c141c41c1d81002c840061199442c0c0300401542841524107a1002854401c0041e07003c103075150041 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 216780368 1250 216779118 216779131
    0x90c01020102090102150a0b1807020d030212070f0210060b040e06030c031c050409020d020406120510060e031f0b010f0e09040308090c030f0102090102011505061614100f14130803 79
    0x41a01c00902c0f0020311841d2001409127071402040d0280700b90207504004a0200c9500c1e0b040c110f1a0600c06d00c0307406c0814030b000300900304003c40b6a2903852003d10910203445101e00c12401441030701c0d11007418181d036400c28041c0802401c800e01c0000d449150020f0b001c061050090042c101c01c6003117000c54000041a6840c5600f071017010070000a110301944000d140c0307400a0f000058990741800002804105041c2e400c0e07034402d003480c043c006079031807580c000e0088901034100360010f00f100e000400d0030000410301d00c95010010840401081e541ca800002c1c4418091380e414030030022a840c16180840d180c845a50071141c44000031b4002800b80344560303002402d000031512411048400a807421605008080c4a65001700e140000d65070240034840b01503101c0d10341e001c01182060302040b11070203054060307840718039803010711010b114011070048411011502615900d04519040502030701c0580020803d00b460079018203580342c0124852030103540c1c80c002c64440d44080c3e03212810b80d80c0010300003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 216781618 1250 216780368 216780371
    0xa181a0c071205040504060518061014040f0e07020d140f0d0c0c1506061d060c0a0302150c04060c030c03030f0204091506053112030503090c01020102090102150a 71
    0x2440d0102d0504100c009000c00d5a5503115962400c042c1400181c9101c0d0380014064150789a03614441000c1701ea11951211094a00900d8001408000c071100325030000400c1c0101c10000300810b01440c82c581c5c28042d02d0740d1244c0003015403901001280d40e0583d40c1504000140c11801c4000409042c9008281c1284840442c6080801440401307048600c0064081c000c124000040c2041014140034004000150001002118604400138102400703888038501c60f0f00c044040100c007583c0790002d0f03600c0001c1c0d60045135002103061030081e5071440e52001100003945c4900c005050581070200300d13800c0c4c403525a20501e258806903030680313840c0d00080044003415150741d4042e0b1010514406080100303402c0c03d002c20020040059490b1407c2030360821300030040d04120b02180303400d0030f078281e03404076460588403a0203c030155401002103402d5040402800726080412092540c00300223275000750003c005481d00741c2401c60045e07080744a040a61805600301c20000c1c48a128403501c066809279400b0b00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 216782868 1250 216781618 216781627
    0xa0210140d050c090a080615061801031d15040b101508041a0c09150909061201020c1009060f0b210c0a03030203040608100e220f030302030a181a0c 65
    0x11100062504075914551040d800c200c41d10402414411035140300b6030321240352920240140c402b4401c80079000d070506440d90728030003146080100390b0380400001c106072000d4401c45151000355080a0b41d064403410011404903102c41d40301c0b0540c20840c2e5021103071021290b000881554400c13030062050701c0240307459038440a08103011515510400045044641e40c800704020400100d0004141c2407115609110024454039030303c14580d0082c00441d2440c0300100320381e403200d001e03108888404e0414080d11034003406041860300001c203464400c440c00c2c03219101200140c0112900003840c907500a0781ca4400c9490750380405662643c0301400c8080d03480c184a16030115860760060791040740180d000042c10850f05070300600c1240c02c541c5070800f924241d8501700000d080c0704c501800903020b807080c500c80c07001b400f00d40600580e011603101b411104a007540e4113001d070082d00216045420681040b10003a2949610f00381b500c200340c0c3c020b2407003503a182e18140d050b95a200080c00007411010401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 216784118 1250 216782868 216782887
    0x30c040b13060e160305100902070f14060609010803030f0406020309070504061d07140a0315081006090f02040b0304140c090a0f0b0405090a0201140d0603050a0210140d050c 76
    0x50000030340f21080f26088a41441440d1103520842504c50208040c90075092240c0d614181072010107c401c0b1074009a103844041c20180040001e90b4030040c03000e41c0c02c0401c806440740100c2c14502c180e600300c40c821196a65182c0168680c0300c100c0d440900c3c1040c4800180c0010343c603902440d00301e0300101c1114000350712140400d04965140c0c2000345850f45405100d1030200d40100070581c0a200382c074219140c0c420303003040901940520f510300c0c424103484402140c12040d01401d07060040031a5000c692030700010744000c0000b00040d0040e01c42a504101600b003111209008441c102c800d0103940600e150743c4d0342c5070f056824905100e078007100d000b001050441c07591031102d10750081024420008090359038029040848900c1209240524100303001c20010690104070846110340a013042c025040e0780d46400303a40c0e4425058400115407421002000b44a40002e15074982482680c14000320b1007080000e44102c030450101c0760403100100600d020720a0603800c0584c104892980c91403c048c043c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 216785368 1250 216784118 216784121
    0x3070308070e130608160e151302030f04020406170309040f060f030506090f060103020f06070510020f04091a0f0d03050424180b2d0705060907090b030c040b13 70
    0x21a03158180c4c1d103410007441035420074003282c082640c4003c481a041c5107407108100d104000200302c190b040000640c4901c2540f2001c00d072401441050303008565910300300141c40f41c441002d0300c0a9009034a00103010415200d400400050011007a00a50030840820100300c09030541c0d8a08009250300c808000a004007894200b2016600c103802404040c40c040444a10740903c40b40c0c0700c90030303070b1000b001040980c841c107030f85440024040e14100e5554051341010b601e403103202900e06003035601c00290000c00c1c0d40d6a102410541e140301c2400c0c406000540b079507a8800d03003640039035a031100d405214800705103001255140c00911a0420301d0910750741d125000c03010305000178000304000139062040c20540c1d002d0300341040c01980380c101501c020308215211060740030700219041c07030032000042a42c0c0701d4081d0000c0c0000d8041c1d8030009540e2000e031300e08161203d1081d00c0c07142c058400c076100070030f204000b40a1181290006001800100400b0f81000041c0c0301c010149074103d000030110b40011500d9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 216786618 1250 216785368 216785389
    0x81b030c040f200a05030c0f0712021c020111030705090a09091a060d050d080a0e0703060603120504060e04020711060c01090212030906160804080708070807090c0203070308070e 78
    0x1a00243c0241c0480c0314180f01466500d072205404000c000340b03040c09801c8010b0301e0304881d104a0703103510b654007000b003030141d4420b00034050686108044844d000c0c0b5400100e001d1402002c04411040f07c1d40c4007002e0742030b50b91100c6a001294401e10000384094400d1010700b80c448130040c268032103140d844c4a408215480c080d800d403403401000b0800e042480c100c1480d1a005801561030700000707510303901d900b0b07141d1014403005401c04c03144502040f48140150801500080e030401510380280d40c0303250040040405101c03c40e80c03108520b201c0980300d0f0060301501c048400c2c9417540110004c00102300002503028000c101c4141c0520115510b044d124100a040c4031f18400d00001018140b40c01042080312081007559a981d03c01c00004030151141030560b1a130107180845030a20788464901451b890046800241091060010019200ea00050a0421034500c8000c1e21100c50f01c0351724000545085c01d0200015034800c2001c0750000344201c58807584000949800c8040195100014100080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 216787868 1250 216786618 216786641
    0x50c0607020d140c030c010912020d0204111b010c0305040b011518030809030106080304060c150e060f100b0702060304030516150c171608071101020d0c080a06081b030c04 75
    0x10b13240e42c8419040c10014060080001d0030300200d010700d40702c22001c030711102d80700090013880b18100b4003045480701e40100001010501909846031000d03c140032224039000c0c0d10400301d41c20b100a03041a540241719a03400f89800c052040c1143c1c0c207107403848440d21013100d03001040104107569911000240c00c441d402451040309025500c0c1c61080070103082d6941504a451190400c00c000c03c6003a03002544862200d501030042e5204403a080300d01d40c01010300000c4003030540242001c00141c11600c241c45072040d040320343d14078419034690260304564012400003c1d001041000032034003090054000d003004030f5916035101904803080c4d803a0703900c0c442e122041d102d038503031107008028440307400001000c039a00505062458038030b00548146d00d04d1400c44588014401640041401e26208561545110500b500250b64900242002e8402403d40070104800580c420011811104060044004842a2074000c0003810040b420000001038074a000550502c0b815003078960310313259809041d460b6107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 216789118 1250 216787868 216787873
    0x206250f050d02060702071a04030c03031106070806010503070305040f0c090203070f0c0c15050d14191b18090905031e120408090103060b1222050c0607020d14 70
    0x8400d071401c24904030907107240e9002d40d0060820020700d180d000a14104032180800764454a10300340354090a28402e903007003d4400c1c0070f0202d0200905402c50018114001c8440881d082540c1c2e503081100d2440013035450300e00281042001c100798502c650004d42c6c010b405a201c3e200034203065520741c44400340031391102003c260040100320300c41e40c100c100d01c0d82841803800c240b1a0400b0380d503a2207200d000c090050801c0071504480904506111f10181c1d401e803041034030100f02c0301d00c85040840280300100c0e26058240ba85404102d43c020150040f2240b800820000100112940406541d0088072414903814400722660000d090306542c000d0740040b50050000c0d42ea11007003c80000001f1040e12100d0301d2042e002c0003003025000d280150281c3c4150480d5060303407034803034410040b4058040c071f6011504000c4089047c808040600784854000c962520440802c0e4140411040309080401d0026100c0c0d0410014450303607091500082c400c0b030344000e2483c038046600e5940c9010f0009103545a81441c6d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 216790368 1250 216789118 216789143
    0x60f0e0c0901080f030d0e010608061906050103020a0c1104240e010611060f0c09061804050708130308060301140907060e010c111210051609090612020625 68
    0x40c01c005400902403c2000013520320440f4013111241d80b44100031242d40d40359580c0001d030381e4441003940141c2c09880c40c0002d443c40b0303080000040b440520140a0320101c3e44ca0207034001504d40c02442114405002e035203c41c41c103000c0302e480d0082d02049090045400070344400e1004040031507050480004200700c19181c44490500603000031384a816001481880301d29a036500c2a02c500017801030740101514249511581c40500c1e1070900e020708050243c000d10041040303a11121035111803800910292401c104d0355407000c00072500044151400d080080c1c03511303c0b0001180c80348500ca6440381d40500081000034921b0810f0450131001c0782c81e0005500f11801c203201099201840099007a02440d01c4900031071030303031a2103590800103800540710304004220030311100c0041c840380b441c0a150a0042240e0303d0125100c441744550b60740d2000004813803100201f01c902051081c8002e4540070815404155203c0d424045640d000440040b40400400d59101c001d0a44815000750700f84501944d0100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 216791618 1250 216790368 216790393
    0x19060e1519060513081908071e0303021804090312150b12060a0902030c12070e030106030c090e070b0702040203070c1e030f030b010f0e040e100c0f090b03070c060f0e 73
    0x207010b040e04807006a4002c4c040305190502c4100c0c6d40c02950380c0244906648400601d854542c81e4500888807485041c07200059040c99050f60103031988640d802210700d5140c858200304012140003001c0140810403051030850651266805003c41400b8610120501a103400c1c0c0c10985420412054000301003000401c141424558242c2c402016042c2d025402c1d42040b61615100340901c0c46010034140c6880c0014201500c5500b5100c01003502800801c101903c0c0d0801c004800042d00035410020300340001100900c10014450040740e80b0202194105002c40d42003201035030028010701c0401c898860000301060b0072001c12140380c035604c0030765840421075103000342c1850441c0609105151402100e0000d50340c104003030840c14801840d01a0043c84640300080040900ca80e904409200d080c01300031441d1141d5000c600005551348644411180d40202107995010307601440086c4401800804c00d0305d40100e00000c2d80d288280030205000502480388808c88a0500d41d44080c0e03805005407021 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 216792868 1250 216791618 216791647
    0x1a0712020c0f010e1b1c061107021801090608071d0c0408150402031b0303070321020d0902090a0e300c060402120c030318030709090b19060e15190605 66
    0x80b00c0b04165040b00d205183c1946c8001c44951129010f0700c85034488070211071135401c84080301e2419a0007000744045542c0003080f401d485009004046105250010200340d0080010340071003140c0c0e2080715040c81803d0b54030a070f030003c803010342030300d4186800703002c0420010000d03c003c1e1035026001595038484c1c0340c075004051504408580c3c030401e0030145007002030a42c501108332429250075007014042a0703403404280c1428003038501d080000c10720104203158881180c0d0403080003030780202c8080400c0d0f282c00c0d0001045a9040c03010130410ba00117481c4950418500348880100814804507051fa03800e818840c0c00360360300c41d449400b21034000008020440c0380507243c0c0341d0056030020041c940a010080460f56a00c100400074869407440186034485607010400c80002e0800c40409100d44291407a210785180700039a0400802d40300f10007002d088030340600c20101102e59042c41d0010075121026000d00ca0301004a6150b000550701c203040141c0c17004208414014050340d0345e0a5500d1111403643e50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 216794118 1250 216792868 216792913
    0x10e03280507111e0603100f091512080408061824070516080408010b0108090a0302120d29031603050d0e0616030c1a0712020c0f010e 59
    0x202408401d011100118200c4005a035858405980200c40304284000358901c010f04c5140d1150700590000401c1100076244460404543e004000522503584130307950041641d803d80d00f02c0e000d1680080e400c00140380c3c0e60103840c916a0240c40c449141ca5100c00200d4100442180c0d605048001c4021040c2d2180c001c1001c210340e84080c4e0761084103a080f1140c1030b1807140c00030305010300f0440003261a440090b944158103400da035000034900c0c1d80310b030340e8013046018040c015102c602013400d00300012550880130402d600e00f10752544c042c041852043c0301c4051076820405400400c1070f96000300c401c01500000301c502441440c01c002c0c041a013254070805140000d0109402c228542c00542000001d40000d0180e0840341c1d1824a181e51040c0c0c0030200e801070190840b08140040d0702081d81042c16000001030b03000600940c10a5240c04050600981e00d9005079200302c00914622003101c081d10840d030180458510342019150014050b107500c60130356001c80d113400042e401c61072890885070700700702040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 216795368 1250 216794118 216794197
    0xd02030601052106091305100b03101406031207080403121b0b040b07020d0806060915030a0524010206240a180c03050f1605090406031a010503030f0a0c05010e03 71
    0x1002084c0c40b47d0303651034403280c5011000c0d400341c0e200c80a034041980e0500114001c0c0c02c198504011144451800f01c85103402500d201d8002c1c0226288910a00301da441101c200742e400400080c0b034070f4a0750359100341e02d1401d01c3c90341080111004180c4041910114055602801446a00110b04090802d451040790141900c0290342c1b081c4444d2580b02d8100744095480380d41100c6d1280c4a03004074000c1000d0030b0180502071440380d000020001c2d040303c186d0003240224a03100c01c292100d00c1180d00d03051613034401c540c214050f0f40300708002a282e040c0900c0510102510035441407070041d80c8404a0b44458403a00215401c000d00c1c10841d9142c207180c0300d4010941002d145c20f01c110300b802c1c41c40040b0302034081e00c000c400a03500304403103e219004208035180d4190103441000303456034a0410342c482062090380040e840c900c0200001356440c002040e902c91246850425241998070750040d03501441100c011107007552a4400311401c00b0301403016210050b044c00354000c0f842c0c00e0311b1001e8080f4000d000351 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 216796618 1250 216795368 216795391
    0x10c0f050a021b0609040c02060106020111041409040c09150305010b041503020d0c030506271b040b0a050406060816031506050307021f0e10050c0d0203060105210609 73
    0x14001c0340d0750010b0300300d207125614801d21030848900c40c0880e44520400342c03100d0708581000300700d610f45680080c006040701c10a034000c200c682025800100c0a200d544902e01c000c04240b44481b00c0c41c130f400060325410901c81c0581c2e07589240e80d680880261103205440c0e0010078100c14041003403003001c0c0100750800300308990800180e00024044240c5a1080c04064010400c1070140c00c03c01203039100300d20203103402a040b5680c0b464440c1c0386145010381031000c404000114480b0842840d00000d9084030308031829000803d200c0c8182c1030100501c0c0001c0d0300c9030701001e0118005204c0d1140d1180201a103441c0c0d0b40c01e00e1518000035413580d1802c0360380000042618020102092220b0302c00c0f10300c140c80092800958948a5000c01c0b4079080064620304c01404032415400d941895540c0700750960320461003900c00d49079610094008032030080b5040c01490340100205c132000740e119802154400e00c1410320030b0511207540c020b840407200d0006900c498094280500c403d80c41d00200903680400e03404103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 216797868 1250 216796618 216796627
    0x1020a032f0a020a080301150f050c0606190308030a050103060e19020f0604030b1f0602010c05040308070c0305060f06040f0c121a100314060d050703120e0909010c0f05 74
    0x45258140003000000844a0340c003142c1900c4107031003845010041034000c40001d4503561207125801004107641c00210200c3e1948064a03030580c020810f13550300c0d4008070058030259039a0001d200d03010110480c10810101014000b00c00280701c0800785024a17042d1400280d550f046103401400c4581040d092556940000d250740300c04030542082c00c2940b035040e01c500309a0f582c00c1011601d07600441d08014150040382041004420301d09000a07510307401c1040d9501d00d190307904000d9080300c101091f80e00c0007841c100014008680d6803002000c10034440c24000001581d40d8856034180b44080c6d840d442c010080e2001c0c040580380074010b41c031030740303040c4d000c200805080400080c00480f00c100c0381e80846a1515100e0032807118500d100325004c10b020300800c0802100742002070040107140381d044004980400800c1c6c141c01d04010380380210f60f10000800311203086032034508244140d00d50000802c18101c1140c01d20340c0b02c1c641c4041c000c6012100208454245000183c800080d0b8105401004410300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 216799118 1250 216797868 216797921
    0x209031902091303050417010b03060f071d0a0902120a0f020901090e040203070e011403100c2c060f0403030219112b03020c10080105010503040b060409021201020a03 73
    0x8400b240c1005180d0300c205056070700b514041d40d6a000d142e0206480d0810699415041d40c419001540440d00850903607074a66240c4641c0314024134241d800a001800300801c1080c0c0030200b040c4003084600041100441300c0d542e00c46501607a00640416004445c1c0c0014406484210700560071700c0085c81c0010743c100302805c00024250f405610984008001110126040d52020b00070900608810b043c001c00725038407510b0b0742001c03650f902480d500070720500e20840095142881610030000080d44d40100405c80c1c9031080800480710344205552581d5000705511969404008099011054914603185c51030b41c00d0103802c000384007803c0102443c40d030450b000007400c00791042d52003ca0458003400101035003071001c1d00280f51051a20300410000400405040c0c0000d9485e410500c1118096100c4003804403c1315040d100380300352404601c060000c900005da20000581e409000035000099070720045d00000c5021300000f0199049e6540003c0c16081c19a02d8040d5001c802c440c1000441e0111000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 216800368 1250 216799118 216799129
    0x170f030a141803100b0a0b070c05060702031504051608060f0105060a021011090f1f030207031e0f0201051302060d0b0307051503090712201c060209031902 68
    0x204225110100050410104241c0100c010a0b001c1c0c06411542041c045124420050904c001141e100365400311000070020318000c2190b4010780e1110055200381d2034141401400c0d049110102d0f0b06015800030743c0290707072807440d4151045000b00010a00503850303a0164204002e107400207181070700410200b2032354140c070303007115411140203403141555283c868604900700b03603041c241d0100950418070140001e1200e9806080070312001c4460202c460030200c00c00944c49140301c0a140c3c00704207100c0001c030b858029070181036124000d00380026494402d10720126001c2d50340c80c4103400301d03c4c3d200012224640c240f00c0d455000c800300e00030b50f0b28110250002000c03401140712410740541c03142040b03036203901c040c00114010302c8043c10410300c00c140228901981e41040b2070006e50b910400200080c18401110310f1604a82c0001d59a4407044250310600a8030050345c0d02240c1201402030040c180050003d01044d200b40203040c0180c0300d4030540101800c12130580e00a6142c10520b40e80c03100940d80300c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 216801618 1250 216800368 216800387
    0x504020315060120061005090402030a08090301090206040b07030201270f060e01050405031801081b180916021506011707181502010b1203191107170f030a 68
    0x1d44461807800d95407500100c81ca0050480130000b40007200220302042c007000650140107070f00361030f40380040545800900808880c22180a503040d440b907035960010448860062044140240022841d445150007141e050b900607442104203075000540202410381c203100307070782c151040c075131008440403140c0342c9101c2048000000074208041d0400c0f003d0400034550700c40a540a031132402840355290500f04140c0305d8200341d20300c0c0104004482644090341c812032010b803052030b88914204446040c0da140060302c1e0410001c100b1000c68100d29914a5690032804e58418014040d108041460700400203003803951000c03650a880c1103950501c122683c10900002c4680480105000b640c1d032507d40c00c0b1100c1d80d02c080c2400d00b80c03500d4800840c00518005c41204142d80c540c009001d4405103009004961000b20101c0c0a0368106201c1425000601d590701e0140c4a41e6113800318203900386101c9107080c20422341c084101c0e00c0c1103c90070700203a03030148040205c62500c04061420000f8000d0040e102800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 216802868 1250 216801618 216801643
    0x10050405041a1f0302040e010b04050907090503122b0f0b06120a0509070f09060608090a02030a03110a0618231c0c0605160e220c0302041d0106030b010305040203 71
    0x21440100000f284a607058030001c000c42160741216507551642c50140d80e1142c01101d0103a00eaa2002501c0d050255201030708035500038009140390046600c96400c15080b003000141c419501d2100006140300f4103240c10558868070400240d510b001c0d01d620801c441564942c1d03030140c8000e11440a043d03070404056580610b4014010a2940d9505a00b03420318000d5085003c002502580203c0c07048c92a500400903943d180c0c0f030320502901c504403d10ba880c3e42c49c0c44002e60661021002d03200080c451040004041c00c000c045070315103c0c00b640c4402c2545c00c05030b81504172422008496007404004e04030f100f0300c80044c031802003200ca05030068a89664880311038074480002c44040038000c902c038040351103070541c0110701046103060001d6003041142440303071041c0001c0e6103141c00c60740c10300d002070083ca080c5454140c2659205400d009400c050000721039443c3c00d069003031100141c0c28610010705441d1181031140070544d0341c10288040c044859810340f41d410140b0706020000143c8001424400354030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 216804118 1250 216802868 216802909
    0x10203071712010b09011d031f060f03050f0c0f1c0f021005120f13170708071407290c1c0e0909010908040b071110050405041a 56
    0x5261512000d4548108103035a00c040301c0342c00c00003650300c00201c0a001401000d0741c1d0621111101c3c83e5840048100e869680d234160081c0c000440802c6908910800800011901094940d5103085400d590320b43c40d4000e86064004c40000c00d01e159003400390080082c801c81d4410109068070009c910020a81001a1000c090b200086002e019814980d605800d074018000008920041c400928507048071006625250310340002c207090416054031244100b41d01040d856038548076484420b690143c0c1d4105224960007007000a01040c8104001c021407401403040d1441d2030b03522081c00e441c1c504107600500c00103250880c0d03200ca0341d00d18208021003040707446c00162111824000b040c20b200004038065042d20b01c14000c04485030700f080000e900540115108200b95456100641c00d0307910b51003005204040c200030910000c50b80c8409400c0c514081c0c034017420341c60185000714110450240c1900c0201c0c4020508129074174140c05000b4014150444403003100640c480030a011b005014942c080d402e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 216805368 1250 216804118 216804143
    0x518011b020c13020702090106170604050f2217040e07050c030a0521330a030b0c070605042001020a120e040f090606031209150f031409060601090501030b01020307 72
    0xe00c03c0d038050307506a0780c00810510842d6521140034101049480d01485403409980000b00545058401d8510840150000d110759a0307481c45100c03801200560303d9a5116003800e81400821000200707003002c4811122802c0c0d0315814080c0b0304000030f00040c80c1c8070070041d081114500184010054030710000d4141460ba4544101c02003a44440400c15140400f20a043e070401c041c0100b10a0011480303149107000088c008056540c48021412610010750018007003042080011000850298000162004d40d814a03d966961409550069900762231159070841054495400152250f610301d800f40014450510a90344215640240038544418441610800030740c54540c0d030804040650091001c003d21001c51511a0081200d40815500e0389a2180003880c3c8038026094002551100046242c0c0080c80c0720084800c2d21818a200003016100d40c618800040341d100050b01510f20701c0042c0640e45411f400040c51500103134010303410541010405880390b42c01104070f40c456500a0080b0405 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 216806618 1250 216805368 216805399
    0x1204120c15030f1a090105121504050703020307050f030a1b150201140604090b0a0b0d12030c11120f071103030301030f03091d06060307030f0518011b020c 68
    0x495050340059804000010740c580819450f512038044102e1441d42080084c0e4036a01140c0f400241e00d1140e504442c040b001404180381c82c813003c03e030300440e50040703078002ca0001c00d0008200c0c1040e00c08070b81d141d001e443c09008603d414801840906015901b0042410030b1000103540d525101c003028154071668018540f41501d02c08450000e480d0b02040241c218000d200300a000b0510191075000340118080850401d00c0c180c05418421f80d00300c1e162030500c0d110419403000030074600000ea6404844e8558071000140c85511060b820001501e0000e10101c40300d201400c00448021018540c0d0030400d01c171710301c10299509441300c80a458076025120007142c5031020320007103c0b8400c0c0361301d840040000402c0003403107101700f00c516219541e40d42c1240d90b00e12082085210580c2c2014400c0c4600c00051b507141410b2016650062084c0b9010946100ca80e08020417201d0545040c600781d0005014920040c00901580201d00d0f0140c1000f80c00c401109402904d40c0e6501801034420401e01440104 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 216807868 1250 216806618 216806633
    0x30a020901110f101a0a0512030d0f050103060b01030902033003090705120f0c0409030e0a030303020307020f1603020108040c090e030910020d0818100e030714120412 73
    0x4607800008607202188074410503607071207400b100440d50150400c043c1c984c144405c0a103006000c1c00140c2490700d014146403c0001226110201540510050001046059032401441d84900c840c00b00016194118105142a60140324006041c9400e00c0c1c00300c80145c0300094102072012000480340001c9001c00003c0d04c42e0b821040010b01c40204c08400d0140348400403c0d40c3c4211041141d12079030242e10f40300d4240e145d090ba5560034402e03803c0a0120801414140c12420074140710b45071440c2203605c110f000980000e00e0b6081503001950100c06c1015a80e01007100200410380000106030019100485900c08030043c08024104108a00442c0400031704200d04005410b011909200c584e1950017955a2500300c0c00300a8070991032017148684c03c50011505601e90f240c140d03035110382036881d030351103900260303c071454040548618000306c1e00b5030040c0d11a01c1100c244440246560304602c3c01d019102cae8a00c801c40382044d410925500444203c40d0040780e045440080c401100541203003800c64 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 216809118 1250 216807868 216807887
    0x10030207050a08040f0501141218030a02100c03020c0a08070f0803240a060806100e19030c050613030609020103090f050303060a0e06100c0f06020714070605030c030a020901 76
    0x10038500c1540808000c203c40107000c3c0094808141d9850f4586654200444a8802061003455020020401041e40b0344074025000e5000076200d030814080609800d580f072865101004210040c2c0055022202120444c010000000c48600d81075007080d5203c040f440d00c460803070800608070720700040c1080400800c1c424044016411500080c1c903842d04940304c481e41002010440d124051381c3e6685102454031b40540b13010380c0d28030ba60740d030110340d1450103001a84007260000000d200e1800b840480ea80c0d1001d060b0452090070040c1280130900d03514020002c03c890fa000a4428841804040b028080900c8810b0450380c200401151000407800140c00400613103c01810b0020029240001d01100000075401850305840c103000c400d82d40e4202c0c00084006480c91a4007000c242e02544840d440b03041014440c50240c41c030741c0c40041150b9a004109d07401310702c00326407c98440c801c50440070b0091104800a181c1800e0052451400c003200040c00e120041c503a080e0310b64042010302090b4403403010702c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 216810368 1250 216809118 216809123
    0x14040b0a082e0305100203040b0109091104020c03130b040e0610030f14070e090108070b0a1e09030210030509031209030d0606030524060306101202190e04020a0c0210030207 76
    0x604014510340d02d044900001d000942c0d45105200604060803054030880c0c2c821600915004196401c0140804c0a050740c90b8042c1c0b05140c0c2c0f04403140280c1d803540300806000510b039005607510039909140703050003000c65100d244540c05c00e2104002d000c14088403694400310480d40307080c4003005030034103400800c14111403082052601000e500b41080c1500200d0145407141c403000da0840b0441c0810140c903509028600d06a00031000820900c142400545060705a0342040e00d500c507441d48042104090389504980014240101041076080000310400992854902402a49403042c100c0e65603200b0002c0080c0c00600c0340000804000701401a1004d14942c0c00e400d100091350b0780b500501503c2d00352002d00c5e0a10801e51010500194854a4060a400909424110358070b031402c011490030205460010b12036a14440110103010744018204a50711540001c0c1c42c0207600f900406001890203148c0c000d0740b0421500040f1500007150134032195044584500742040c10004801a01407480d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 216811618 1250 216810368 216810421
    0xb01020a17070b0c09030d031802130b010e03120f2104030e120109050a02040203180607080109060b0307020613030e03010f0506040b03070b03070503091f090314040b0a08 75
    0x44400001080042c8200d50140c03042c51450344030300064030902e1280044003035055112101c00128207000b50000401d0651071401c80c000b040e400e0300422400d0364969602c0fa0800d0b1381d1503140c8415070308130600544400d8160004d094a508a1442d1000340c40303441201d203403d03400440c0c50445428a843d51007480b0002c0044141c490402d450042d00716021607604604c07070380b00000d01c403011402c1442014010b5410030014a14080d07e03030203100081d8400b410030502c4566207100c1d0740001c0c0d000c12915001d8245603440c8141585002d607110100c070780720342100750090700810078094081d60000e00103400501820300464001054501614000c5402c3d032580e401d0350a00e000d21621008540c400c501c034030004d54040c070240c0311000425440e000180108181c0200900c0407403c07072441000915072004a002c12070340c1d0611f006201001d8901d2000550128680b00d241c2d19040580c410000da03064a02c81e82c0351400e00b4105515095180110035210f800c1200c0640010f0135218203021201030000e8940301f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 216812868 1250 216811618 216811643
    0x1051e060f0d0302060f0a0b0a030609080d02120108010b010c020f010807020f01050c18030601051005031308270a030803010902130f060f0207080c01050904111c15050303040503070303030b01020a 86
    0x20065124030041b164610148088000141d4421042c02411054000104000c10745d50035950350000a20303405909485e0310701e003402180005c03825840105020420007103a080e107903251517207003802d4a4221002504102040d05020300580b150a801a291384007400c00f501217a480e80b03000c031b04d8004540c044035269030900d41482900610311004008804c0c501d05203003401d6000c2401d250365803a080c400c15410400c09250f100d10588100701442d0041e038002c0c1c80c192000580c0d2941d907031541010034400c011003010040680020400c0380880c04001064035401481f6245841e101a035010500ca008c50164000482045400741403804001804861214106803512883c00a00001d410403108000d84940c50b070204400070005000c2d43c00e20b005a40303d42c40c0116090030b001c0901030b88004044c40500a100c14011300041c0111928407280902c00060114401d009880c03601c07001d17a101c24001e4204002c00c2c84241c901156040a982e014240030030743d22003190040b840c05c120281c01422141c1e1184 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 216814118 1250 216812868 216812873
    0x90405010b0d21110c09040201170702060106030e010903020d03020d090c030c060f140304030f0c120e0307060903020f09090c0d0602040e07050315090405070b0d050a0e01051e060f0d 80
    0x40541c82a075440c480801411400c1c0b5019901c0401d40c4401c2c84c0b00c0c0c0e0020035003103106d2400844090740944103150040c503d0203109440001c05100741c520740c01580201d4014000c05074584924070f0f01810000090080603c1500d000c1e4449070a801309504140c2c001410742441507494100b40c1c10b2a900c09a40c0c1c240d03682e83e09080e5086501401000000b881c10b40340003032418403c542a404803045055640c1c51500c8079602601c01c060b096050005110a040100b00070810420b406450301c2c150b80c5940d6041511002050306060007030308040144800b808082c40961076021000c4c14040040d143d090b02c0b5202c01e07094515100c4058065540700b290204040308001c00764015000302e4101c042408000d071183e4106803414041281d900408800640008003d8a020190681c10a00079419220b01a80301e841240d620380c03010524000320707038441c0f062203000c103145d116200904600c07200803c45818007499903986554050364403c1111242804a141079480c80d0a100f4003143c02401c1d0110a00c01c0d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 216815368 1250 216814118 216814133
    0x90607060207060e0303061c020112020406030e070602061006030203041407031a0112020105121b031003030206060d020619210e06151f0302070c0f0e130b06090405010b0d 75
    0x82d01c00c4580d02c2c10040c000c032241d00c000003601e02450f4010030b0005480450404100c29616000040c3c0c104030322a03000c888800300340e200030400751505640109003803560112151810410342c2c003210444d07103c181003100014a0802c10743c191901c070300e0701603529100d500300010f10380341d0204822850f0082500000401c641c6084810003d00d2091035044240e90342e138030072039201d11840c03c080e000c107030308004100072030800407081503200425803611684411303c82c040301c109810445948041c82000c240a000b03040e01040f080398000c03030480703640ccc0510f40158013094850141c500c88508050b00049800c020301d004004401c0c2c1c045608803400c0c5804024103804c0c0150007281c41d40c2e441c034000c29020411b420045030b0344880d2140043c02c08540a030020942c0c42d84110004034207003c056080c0840b0b00001e180422420042c8800c04100316070710304000703400c400c0200c0038000049010140415030002203419070000e40c0464111a11020b50362a403c0c91400350008400c041d500034800c2c00d002c000c10480 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 216816618 1250 216815368 216815377
    0x3070504050709170610030807062a020115050a05210d0c021512060111010e0a050609010507080112080901050427060909030c02041d0304270b0d0303050c0906070602 73
    0x844691424100403814091740700d034015609010514989501800464400300045c0309052042c840040c03161852080d07488035800da481105031003581038601c2c2c201c4550900500301294000090700b245117107484005149240144982406104015000704428003c00c0c0070b40ca0000b00d145c241c0d0035116036508024480440305008070b108074840010b500d1040c2455084e541c45e0200000603040d541c461800545444000710030725500380d900c851030040710031024880c0d255103a114030001c01290902d02c180a00350b402c0100000c041010000c01007020095000280101e0794210840c241e4428051004880385e100c1c0303400000d80d05440c514006205c142140c594100e000440b5000c12103140c8036401c4074140c0340b040b800580000c0000d1240070141c60301d64807000d5228040781800a025021006460554000b0b6018003009407000e01c078851414481c01d150740c1503146000c03040101619000000b080d5807125400034041554440c001130107010114101e03015100300800d40c5444481d81d24010019600 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 216817868 1250 216816618 216816629
    0x21c1403280203040b06210d08151903061509050c1b0105060114030c07060903020715050a05030f06010201090813050f090c091507080403030306210507050f03070504050709 76
    0x800340e140285010076482540e002d1903001d0401107003500c0380801c008003140c507041d809115030001c0c0c4846080c2c810400c94064040c596890b220114504070000130240d1800880180c040e0548420704040f41a5840303825040d81d0b417007000003c068102c0081c0c103108002c103421405502d4034050510405c1da50110107049224a0404540c4c081890700003042d09840060b0b40c20307808508040907a000e111046005140c0c00640194902d00703001c03194603401c05880c4091010750141c0c0241405015852002a891483c2d90f030364202680b42c0005210014081d21006000c203002c1c0440001084503680b00b9080030702d0f11504005450f850b0100c0d403045200c10314051080d640f08100b030305072003007503420040c108902c203d402810700e5091001040c18081001c0070150340c0010130000b04080f000180d10b502c0500091400f1b681c00040c00350070100d42141c00d0140b00d00030220542401c100ea8001100090f05034240c40b8282e541c040c00c0681440803d103850810b400040d4000d080038108201107600c2418a422203c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 216819118 1250 216817868 216817921
    0x5010e16030b0303030129070f140304050d03030b040e0a080406180b04090203040321050a0b010c0209160c02040f02030f010605070305070602091503070c02040c0e01021c1403 77
    0x1a092030041c1d048950003020316805800a0004020040d05440211403003140081c2c466841e4030700c0400503145034031010f011141050540308003070901040080006c040094000113600d098240342c0050b80803c1c2c481001000c01d41c41d01280e680c1515150880d8542407840005c4923180e06182c50000c40e175420600440c0002858184e041c003903806403403014021603000046031442c26091441d0034000c0c0d4030040055091014080200c001c20441410400f2040b484801c00113150402c001540141c582c10505a81002841030440000d82d84a4044603049034440c00540e00642e00f03030000b03450101c101d0300080d601c1440e0001c44c2d480d02c84540c00a5200c3c01c1040088149aa03c03405c0684d80e9010351200500000d00500c100c0b030000f400c540c000e0040460081c400c40589000c1c04840b10307107601c110f489030001840300003107500314101070251030724140003130030403c2e06d0300003940c0001d40e5140300454000202c07040d8010480b105000745a40300e091400503820710b40c0c80c030300b00d42c2080c03100d400381994200d100d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 216820368 1250 216819118 216819151
    0xd0c080a0311010f0c080a0f11070302030913060605180102071a0d050106020307050a080d020f0d020d0b0603090d1407020a0f0807080304150305040507050301060f0f09090c0b13050405010e 83
    0x142d5510179041d040c441d0b80c44125290300c83c82280f07401003403140b203003140480d0f50b10380440e24510300d08003070020b1714480c2e4015030303962105900b402410301c0b000c4112602142064020300c138081d004420b48020503a00c2c5585c0800c0c04e8a900101d2505103654031031864250014081c0a8543c4400001c29144c803203140280010390b6030f11300480c1d40b8030602c000038109401c50b5907034600285c1c029005150500f4a1400507040c40780c034651695840d40080e052040c0b203580000e41020300c08080c000d0403a8190304031030741c03400d41c50408001a11604114480d40400c143c0b80d07040c40c0140e1000082e61140c1e074025003552800c903102c024001c004825801042d1030f91040001c0020740c03482c0042140c0682d030403040c0e0012030250590080e0050b0a01500446903400b5903000407646403003d1240000500c655141c040040b0301d482c2e05100b445625800c07000202c1e00f00030040b004101902c20510848484042c0365135254603444000410740003640055601600700000000d0a031a1413040700d0155007440c5403503501 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 216821618 1250 216820368 216820391
    0x70b060303090d080d0e030313060e070b091302070f0804081504200619020618010e0705010e0a0f060e13090c1a07060f0504030e030d020703020d0c080a031101 70
    0x20790055000d00c0743d02881481c0300000081103c07001d40546104041d01050300c403082d1aa260440d001161150050200318010300c05202c124040c070019041d41d0b201074800b09040c4000f405091103221075080c040d00d025842c1510344045c550450b0f030f10740e410080300200c0241a2a0581c402d84c02071041074483e10401d440b0343c0e449100044010300456004d802e04510544041c148540b00341c0821019500c40d80a1110078030300000ca44400780d0b030488a6000d40b40600d070106c110324800e12402c444502c0380c0e14180b44400c040000250450644d6006d0801c1519416144d0005030784454680242111031940c1c0300000d030b02c5030001e0241d01c148504482c0c0315400c00e00c4000030012140100341c0036114640981c0204600100c4245940581000e6141c40389040040c1d01c0c0d250035100c807004010f8241d96954100824103510a5000c41c680104030081d041e4417010700b00003540c1712841e000180c4140021040d00c410842c80d051544000c0000005940e4858254240540b141c51030340280440d550801681008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 216822868 1250 216821618 216821623
    0x60b01030c080114131103090607110312241f030f09020d120302090301061e0b0408030f130f140108010509091504020d063801090306020c07150302070b0603 69
    0x58900c42c44d0108900100e40b410020b074040c0d84c1000d600141da862000003103200c0445c006610070100d401c01090203051290b0018121500b09070001c80e142c1060100d10a059200c0707104d90703084a1781011f130113409510403140158000d4015500c0c0d0b40030a03044400704100218203151146030105480c200f056515050f840c07000c0d2041004020343c0400d0324203118000802030f6103d00b551740351514005040c0391401010a08464403a0000c42011011281815030856074244074000f23000050051350030685490151996401a440d00101886000c40c0c0e00f00c0f44806009080020038094000c0d8429a66030310103403c420407100e400600058216001107003078105510f500d070080603900700800310115900e0114050a1b17002e0400c0303a12401c2001100c010070700a0150081d85072048004900321b406600802050711201d1014800051055003010850307a0485050030469401a20141ea200340d4410500c1c02d001943d000200c5c90352103903900f40c1e20154183d002d050168818411041561918400c00d903 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 216824118 1250 216822868 216822871
    0x1b2205010318030f121107051b0913050a02030703141e0d050d09080f0307120c0207120f17030106090503010e1015080f0a1104050f06061305030109060b01030c08 71
    0x40b082d6920a9203000034490080c0c58400c0d00c441c074204500c1400410280155502440c010095000104201080c400113104052103100240d1003030818805089c0480e1000304001d01c0c3c98056034114000202303001040c011507001c02d500900340c4202c50b4803442d016004127030445c0844030600c2050202c454911500e0042e01c804000750000388001e4a07024001c071a640e200305c9030140025188c0c00700c0d4000800351405807001085444ca5130b170300d07807804c41001001040405226403003a800c203644400d5482c0c02260075001c0c1d655070400b200d0710040b82c0c14095100081603030000d00304000c2c07024119064450001440c140c8a0070f98503910181e94038009c040c2178039802a00125507802464000b403449074203600c640e0000b501001c089107060340d101821030500751900352850303503600100400d50801c41740e060341c10981101200d0030000f500746242d4012840f10b000703010501540c0e00141c90301455804c0c6407000002e0a00800030b110710101850f10340301070599526810f01003801d1038a01c8001500491045 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 216825368 1250 216824118 216824141
    0x30403090e1e090111041403120315010f030b030d030e06011a090907022a011403010e04031d100207092307030f02040b07060203060a0f060f03051b22050103 69
    0x25040300b1545480014000024045041540d40c0c2c1001003203001901010300000c21049255255005448041c10704040c640d0701c01201450040040080c1e108401c0c43e00e40002cad60078a440c008601c03c1d41c200390002c1c4a54840160701d446071a4840d81c10580c07503049052880d490b0002d6a559990383d480050003540c60303098150145000f8011801c503410b050101580c840303d00c3c4100c840141001c03e41c0026140b07040c43c100002c7c021860418455600179070828810040b09518914662402d8019151100b020f800101040b8103440750424440c014a000d000c0c16400a100300c1200d040010041e65423903186c856100c80c10308040e0407004030001183c0c46100c505124580d0016030341e070418102c004001020701040040e40c00d000c04120030240b01c0180207401d10840e07006945e400c2c180c081199002e070300e60181d031700c142040c01c0600c04294040c500401d161290f080100d0983c913017940051101c0f80300700c5044141c0300041550007603c0b0401e40125604000f500e0340c0c078000ea448a0046003920f05c03c2c00c09 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 216826618 1250 216825368 216825391
    0x207050a14010e340b13150e060d150f03050c0a05010e090a0e030a09140f130f0207020904030e1311070803090c1f03060801091a0705041802030403090e 67
    0x144c02103004000d1035a1920140c1c5005004031582c91030021040101d5400044c0402c130f010801c1e034003410400561074054030048900581840f100140249000120340791940951008500002e045010ba00202e11141c41d032810110310b00d40f9041002006c941c24070054885100d1382320a800d0500380381c0002c41c15100c06a4440c0300100103041400f809110141030348403010741d5220911040d0206102814050800d5954680d1840c80c001411700c90200007011240700c3d07015076041040654661f00612468411448040b038030b000100311150090040c40b00203500f00c10820108005c140d4400407116115104442007200b03000e44201030011560039407940c1d14940c1c4100030340d80118103c64041c6510001c8042200d4010020303401080c0c44403111940b50182404045000080d690580540000b0308140d0b4000c00c00c500444e03d030780c401a4096120103c0e29008000030030b00441c41a81158058501d00403030300c4d8104c5218002c50001c0d80121025030001d40c440b400851003442811590b030041d14103480 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 216827868 1250 216826618 216826633
    0x23010c050c0c0420070303060f08010519050c070b0a140f133206250915020c0603010e0f0106080402091f080a1b0b0301030302031e09040207050a14010e 67
    0x1408001c004252000a4071101c4201c41071310304020500030190b2500c80e40d40421385910304001c0c06030b6800340d50005296070b41480104002c00030703005060142c5560009010880303460300c10710801c0c40c0c401c0d40d001515040b40d49042260124181d04072110901c2a00040d04156403400100c241d555003d40c0d030000b00c60040c05021010410301c1801e108014207803070b00b2400e000d21441c0c4009040561301040c2145400c2941040910781040c03a00340d04403050320394186041030b06020000c203095824060b800c0c0c00301d07081d414044424420004060000c20140200d540c80d6110040114101d804546082400d80780c1400850f40c14411125580520750140c40c050154482c20300d4042c1c00c1001040c0e4560701801c00c4000500f00324108140121035015203502844020026a0307401904008d03003041175440000c00040000070f5000003168000d02a002c0750100f802d00e00000c882c900c0c070450054552150001c510f840c14000c01184054155101e038026440050000e0b101d03038241c901c01103614001ea080046c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 216829118 1250 216827868 216827893
    0xb0a210e06070c0804090204030b190203060a031712010f03060e0a0b070503091c031415010806100509030102040b091003060e0c07050f0a0308090d180306021623010c050c 75
    0x100c1d031880b114413800b00181130540301d8501000b06d80166009885821114003407003480c401c055801c41e0300311a1060258554604a00410004080c1d440000d080c4140741c20111403071001070041e50881c40e90b4415842140d40d4072161844501810f0005031103003480d140e1034001e82000080c6c1d005865a000502c0003207581d400b10150742e5500020055404e40c0201170000101c0418203109904001858800040306010301d01c801103403010083c1100a01c0f10074841d0070140d80c1e0802241c0342c1c000c004583e08100c0c4843e4450031110750140d1b40e940c48e059800401d0100c1c041021742c02500030f0312019a144046600f1081080742038609501c2403500c10400c281c081160b0048681c01004000d005008503040054a54200f525041580c2003e0300055202c0080c450780d40070900c1032081e00c00283c500995071041030501c4d4550b5070340f00e110081819900141c030040c0410113650303d104094100f5080c4d03078034407480d0703a0b140b1500500c0c25118210703510346402e144c5610b001c1c9081d01e604010681c003c00324a41c030300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 216830368 1250 216829118 216829127
    0x503090a02181504020c03030f0405032503260103020f030a0b0c1206010f0522030206070506010801060803040807092c0d020607030b0603040609020a0b0a210e0607 72
    0x282551100340554240000940c64040005070400c0d40141e40031010f00e40310707401000c00c48058a08504c076900420024201d410300005403500044220f03410780e06c5440700e18005145100b2a020032180b120495440702c0c00e55480440c81d58180d010340c51314450140d60041d441d00f03626422142c0c0c0c0d2050541c600600c05070a000c04e10184043d405012100420340c00d8840ad00100c50803641c4100d88503000982d1622028405000c9030400c5081c02e10b17003880d583c41007003c1c1141c040c8080c460803603051800c480764411082145030340150703000380059544501600b040e40d11200d090107110304540c20f102000801040010488040b0b403c40006088010304102e07214024040ca00c688060107102140d4821328200c4011013151183c201301d005010454103190080d0404000801004c18180342020380c0c2003031748818080b640e000da404403000600c5900c51000032601580c075001030303108203404600d00001903000402c82c1030746500b005140e03d520400d689060103039581c007600086250080008511803038000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 216831618 1250 216830368 216830371
    0x1c08040f050106260709060501050403030e060706050a1401080c0d0f06021e0c01050604090c1232070b03040c03080c0f01020f030609070c210309050d020c1c0b070503 73
    0x410000c14100ea80d0302c0c5128682d121011440d1466184c0f4024400000c4200009402842c0302001402140c3c6400000703480c0340507510020302404005441d1754082c0e50303100d04641480707501440c00c000074103104100000521001c44242c4000c09040300109400d00c3c0050440d10700440240f442d0341800c4141d030764401b2044034850490744680c0034459418205410b42400d81c005e2030008007592914084045282914005088180600d140503204000310b50b0100b61481070340c0e600d4450101e0000e103403030a400d0440c08441c44925610b203480e11408a008060014805203415038100c503401a140e80070307030318a44400e440082a0018400c020400a143c0c100a08902c0b88401c0550765054845070a450036a449411000460300000041000e0351400135802a0001d502d0f14041c210000f06036074000d401c69078000720040f07020038500341601789031007900300d00c032140c0c4d010040c0d40d14540902c0d07000c1d40c0c6040400c4018410350300d00501000013000b0f500043c24058100c910980350743c03207900081c0c509a20 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 216832868 1250 216831618 216831623
    0x5090f0610030f02120414060f0f0c090f15030a0b010905130902030712050a0c060e150c0a0f06050403270510120c080108060903070b040209100f06030507021c08040f 73
    0x40a000c9220780764801c0b05e000b481240100103001c1194482d44007282042001414116020f2004043c0004000d08111441c0c1c403403c641581c603510b0859100140c2840303140d800507540801443c0d41000b0340120344000c1d6008501d1035009200e008440e1006503011346040c007405820850303100c984408204103400c807040e518009070640314000d4848494040340c8443c0507065500d5072008100390204041d110342c0704014004c1c3d01d007a04001c0038cc100000d441c0060344001e07d09006001c074581d803840d0814010700700c0555100446500f060814a170020182004032002e0f07002c104103501c12018098498a0314510480310510240d0490410081003520405580d140003005801102c15841404600c0303004044003c82c0c95002e40c4e58504100b003031806400811140311070b00705000d50400189240e00c11500b2984c100c0d9101055552100c4040c0403001540c8050409803c5a400144058140e40a81d00030003455003130f10490b48080b698060444114240c0e10300141140000078003082280c203512000c00e2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 216834118 1250 216832868 216832871
    0x50604140904020613150e040506010e1011010c0e0a080d0c060c020a0b0a0207060c140a030f0207120903030206010e0c09040902040914151311130b0907030605090f0610030f 76
    0x100c12900c3c1101491246c2007072943c4244803211514645e00448880f80c09078048405000a01c1c10b0f41c0001d01169040003544e0041c0010710070401d005020310080349000003144000c00581e00d40000052a901c983e00d4800c0c00380100000c04101040003007a600400c402d95221070720084441d44c0c03108001c04914800504502030101001c0c00140c801407074501410b45a0f5015803103003030700d0805004440b080820981070262081030740b0302c5900b1580a4501c07101c2a82400500c403601c030070020002e486074050052040720030690911301c2d01e070040c0200b000e89020303a080b503440e680c82d20140503454900f038070301e010850014800b00041d80b5144e046005801c0c4041c0000c1160006940d41d18000d41c800d0312441801d801c60902008008110a10503038480003040011803005800d407150703002200c004803100c1c09280b00a0000e0b00c3d800040d000505086005090480345d4600303050000c005086034011544a4488403000c140711030102e200a600548000302090700342500340c003087e4001c0034110710300318849 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 216835368 1250 216834118 216834127
    0x106020d0c030507050a0b01031514060103090215030106020d090b0a0e09191a0117161407050f010f06051207050108060d02090f18070e070f030608030a020d02070506041409040206 79
    0x503024444101210f2291100c031403254114501480940b40c03101c243d0350360038582f4810500c07901c40c0d05123840c2c00c440f0a09001038511514000701300d9561400f90f48429039000040005003050340055250541030990b601c000390b45840d00030600399071180440503000202548080251440c3c02c07035a1581200e01815511401140c4910070000c3d24a9000c8040514000a079800e02c0d55030413110094602c8030b0b05441c800c042c41c0c43c03c801001003800280c40020401001c25120b40e00d0707000b40c111021a40c01404407074601042c8031031320f80a049821310203000d450a020002a00d401c081e0202c0c5400d0107500040c06845007031000441d981c8000400d5194002c00b807201e92005038540e6400d5500450003011030198503d40300e400d00a40560342d905180c200d611a0070308110b0082100c4080fa048100d52410003040703290f03820100c0c0a0407294002d50242c6c0000075411485903000610741400000b03a4003078a69066541041141c0ca0041d0300c01e5a201421240401100d450913481c829400b0344010f0517107040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 216836618 1250 216835368 216835373
    0x5040f021204060e0105100605040e060102031c09110f03030307030c02011b09030204050c040305030403121e020a02010215100905040204112d03040c090905010623180106020d0c030507 81
    0x80030740a039410395829039a140303680c1e14a03c00380901a40503445c2d0055029030343c0740040c0102188034900c103d000510600022070007681c4240110340c1281800404080024581c214900c01030101034011a20f004400e840030352181450904202c40a0000300a10700310b6a421406401900c104000901155a110084100d030b1104a06a2108100316a909240641903205002c1240c0c03001c0c1003250088021700c0104000b4034004210380c16079a0010662812207414041903a14200c0d1541041242d05d00b851081c144039800034804039224003da0071543c165404031440300c5008004d8452115074040070609001360840c0307820044e0401c2c405000043e142e010700100e003005800c81d0b0b41c1c1e44491404001c012442000540c0840461030043d03685510310f04203551003055940c0c0c1489442080c945402042c000d00400f98450002894185802c2180003100e001310201c2c0a50003440521981040c101200d40e1001c150680b410780d030f074a0b00140005140701d0b905030f50303084113054102c01b000002c0006000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 216837868 1250 216836618 216836647
    0x201110f01090b060301050103111003060321020c0108061c032601050915100305040218010801050a0e070e010b13090e0106030c050306041109130b1501030b010207080705040f02 78
    0x35112080400050300c8800383c80c10b26405040a400345101c4d80c1060018000b0460068411444060440750003800442070300d002d602074401d45d030000c1c0c1044210b8540d07000501a518090802150550988a03460709520054481d05420349803030707422094161560b01e00c490b84a10004a01b07002e800c048050b800c81a4a401507c5c0f010507190780e003090300400400c01c6040048080f5000741c0c45100e494004803540001c0f41055500000314002c05842c0c5000c81e06540300c2d20104a00c03e41c1c0044445003560b11009100e002c2e20007918034591031031401441e00054200407d0140036180362009424142c0d00e400e5031401142c10000070503e21142c0c2e41800148500e25118110700602220004503030f040c51800d00415054191703000d18040e8022a00700000030314500f9400c1141c2c941225040c2c15511610383c10000d203ca000f400910f6950250140020552041885500c0fa8001d0364240240c540d038000480c0c5880141c800c9204d2940311070720600c2545001c1d00284204c20500c41e0050519081591450 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 216839118 1250 216837868 216837883
    0x12070503100204050405010b0705060a0c0e030109050a0201081803091e060c01060305061303170a150308131410050a0203070204051e0f190e0304050a060504080d030501120f020111 79
    0x8031281e0b001600b0040c6003058080c460040003581d00e250b09056041c0c4441e501c98000510701252240d40e10700141748a80221818440034030003600800080500d441e0040d41c0e010400000e9010440d2100010381600c140b80a109441c44e04038061350521a03604180119402100c68010696982c4241ea0b40c20f62100e1001c3c2032100807072000800c03944e00e50700b04241400e40103030070403003150749218640c40441d4001c18070020030004081e0a0480340d6447c7d41c114002d14061030000398a0178a400c0c0042849038500181901300341c0c0035a40340c4c1040d95100340c00d82e48804250200e4014600e00c074414181802503003d0403810382c00e801920726000c1c082d400101207030340032a0710810351070588c105d240644d40c14031902540100d07661280021424042c0d0100c5001442c002c1d240c5030648c580b0b0b0703a024a00b00500650300103140140c41062055299840541075030480d0007001214861003c080c0081e901c43d01030181203503940f958204495981d6250301c03150458000c0243e0510240c1303604540000340400241 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 216840368 1250 216839118 216839143
    0x8070506070f0305130209060d06110a081e13060216150b042c0709060b03090d0e0109090f020903100203070306050f150304051609020403020103050a0203070c0212070503 75
    0x100341620740360501518402e010300715281010b2801c010410b16050307001207490501d030101d882654580d15000000c160400c20100280750350300f014422080101c00c4c40103800780000c10384030740789203a503100c90f104010354010804000d451610710205983e001002c8044139214010740b0090f10780480700780c000b0002e0b4254002281c94815806815004900c0f42c81144961401150248060555071703100d0f24210b0035413150f803400060501c84c00341c410301040004a0051008220a000c0656141c02c4420755400131280b2000b140110500c2541451162151440005c03051312160b03651420882c13220003e104466002154a500b00081001e035641000040904105080c0140e9a441d106000402b80c1c0c0b065800315001302c88030815103005a46510075444540c603074500d011344a41e200d003442c034034203942200c2100d21080e2100b400700700041541c0041c01a41e0013a2028483c940310501c92104902c011620340001a038005920070051804110b2040110171a1088926841c2c44100103402c140c880c6c0441c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 216841618 1250 216840368 216840373
    0x30339030a031d0607120b031b0a051005030a02070807060509010b04110c060610030603020d03080a050f010803071203020c07140f06040305100f090c08030a0305011e0e1003080705 79
    0x11a6074580034203c078107007120005800009601c0c010541d40e50700984800c080c00b903184a03540b00c00c3c03200d51018078640401000c4402550305070120540c2061602e03c814050445040c0c0804c80342041c0d42d0441094407a40e56507460348e03403017100c60302c000c0d00421012152001c0420042000c101a80103640c0130381c208100000c2c84850543c200821505084403400c0c6400041c003041c441e4050101c1c64540c0140290361512114002340c0046000b4a0305800096114240740c09800915134802c0550344901100d041c00c002c42c2d158001e448410020904c101c3c0300e6944100b0051002032100790034165050075900340942001624451075040c04256000100c0ca00c00c0001d0351385040c41e001040c071011141c00d40b0190314190a40d22030076200c00003c00c2a9030921b40341e940840d441c00650f0701680c0e115400c528602091601c1c4c060040d280d900603121800081c0c1000300100e040c00110720030203081c0c812a1120982c2c10f141030001c03064454002c0091001603500f0b007001001c51070041c0101000c0b80714201 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 216842868 1250 216841618 216841627
    0xe060d061b0207081605041802030f030d0b0307150c21020109060f140f0415060306090b0601020d0203041710090302070e150f0d080c010c02010614060903033903 71
    0x100240350541e25801480607910000c00d01c64174240d803070f511006a890036100820450048402010b800a81403c001e400d8030406100311210030011001d006910380101050080b130307410b2001c041d501c4840c0d024101c9229514040429150700481400704514440c0c031a200c510b1101c1801100d00c01d01c4000aa80903035181c0355082c0400001c0d20810900ba04149000c100c442800080c2c040980b4005140b05a107180b60b0300070030140a20786141c080001d042c003034284003041e101d1815001600311004211501c07080c882c08192312790f0002c24041b242999990085042038507100d00104411407a810310841c501451501c4041175011740903041601e4029001042c1da1482d04020307130301c4144028081201d4000d2072400440c56526001d007540c00e00000c468101c1074107610b080c40d0003240f050001c026001e40c1f034601030011490f0103402180807100c510141000c041c040400b809810310401103800c1d8580c004024117100403c040980001d55509184454182607049a90340d00c0100300741483c0c50740303500105 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 216844118 1250 216842868 216842921
    0xc030c0e0109080d21020f1201050402070f17090406260d140904140a0603060609020a02120a0908030301030f05070b1c0b03010b21070506030f010e060d06 68
    0x1221140030840a2030142c5142d0b242030680b40e110b803682c804c4102002030066026500d81c8590320304410311101d02d8411580c40c424004000010350100c01081010310900780000703403620309071083d900f0076500b01eaa41d0301d044885541d21760081a2290a0038002401484002000e403110320508020306000700c00003160307004032488200103190041c402d400551100703040d40b40301d540c07205050003140c030104441d50315429448005406000a07100b0140458940c0c01044060001604004200c9000e05010098942c40c0c07460304059100e42d04240b000b582c40102c00e403501c0017220300104800d0385c5a1030405035603511a94074070304680c82070f40282e034405498041d413818001c00703001031001402c184442078688810803a0544880c41c0301d61544441a07070315180c0d030b142a2400e4001c000c007580000c1400607040c82c440e401084040c46035003070b401640718120012500741810021240124240206481c0d01d81c43d10910340032080c801007003690007810f00340100001840900512400c510790911110560301e004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 216845368 1250 216844118 216844127
    0x40209060a120308040c0b03090105070909150b070c090507020f0d21020d1104090f0b0d0b16020118030c06140c180102120c06070f050315040c02010b03010c030c 71
    0x203040c461103480228410030100d058450950001641400c1c00446595541021104801640e01443c52031800000b00b001008041d801240308401c01c1c0c4030049401d0710350918508803250100e02c9035206000ba84240108a52100507108242c8907159180040b903c400215060ba50151100005a80b04256400e0256030074802c04004400300d10700300d241701e0701b120100020304082e0480200d4513540004e11140ba048079070050040c0700c0c100803c05584560311100740f4020155501448c49007407400112190b00e00d401c1c03240358617139600041d00700380f07a80724844000c0c0300d9500340c007a65003959a240c60f41d01c01c039101ca80b14014018020b80b2811240c02c4c5908041064960701d40a000c41d481015080005030417192050302c0c280e6211551883e41c1a04040c0180c0c6080d21421214510308800b051200000c40c0c00560648116680c1d556461a000da9010a5485020540303581c4038207150f0940158030ba0602d03034031501c144111440080b03500303c0d0002c007290031603042e003050000107601c41200c9410286c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 216846618 1250 216845368 216845371
    0x3110114070201020c120f1b01120b06030c220f0e0703020a080a180f06022107021906021b010507030b030c010e04150b0a02010e071202090a0c03020c030c06040209 72
    0x503a12031601d44802580005c0d02c07a280c1029003441010888011071034400c00b040a041c910301240e04607a6011007078096106030040b542d0489000880c8003420880141e414058090a00c0c009020107041d074071003034a9042160416400600c0c800000d42c1e030f100d820700860114a00901842c005141c503103050400e8412200f074020644c50505004000030710034140d00c584140d0f030103034101800041d80c0c1e0005000c80c0541d610001d02800404a4940b09170a0181d81e40c01805010131082241045600052054900d11412202c06001d6004408404205040c02d20703804111481103000616120901014041076880340c07444031102d83d03444041050084c3c051240003d210f00480081504001010000302074030300440b20340340900c0d16402048592510480b0510161048801d07031500c5e15440708000380208511846200c051080c00c00c0040da03240e1000d191000540c005c0d10107201581c40c0c5103610041c101150000d000c25508200714400407006002410003956004081d1a081c2014010010f60150 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 216847868 1250 216846618 216846647
    0x3090b04050d0f020402040b0406050d05011203080a0f06090504030c02040605030303060d060905031207180f1a1e0406090602011d03040e181b120a170c0115031101 72
    0x41084184100d0799440d81070b002040e0b0250781501450302610105000c0c2c02264410b80025601007000b180c0c00b034105010341514900c5540401080e0398a034100004061030b082d020300810140c40105800ca40e00e500520218103100001103442503840c0e03206421106c4c02c8609800141340250000110b00c0c05000d00b8005050860046080d0300304000003400b020780305040208401da841240f80301700300d824420b175140c000b520007081c125803421802c081c000b16142d800c4081a400c101ea8082800c800e0300401c407040c1c40e55118000044021840c100030700794000001450101002d524102109254a0040014090950380e113500240341040190940c0c050003e084000101d03004407003044003000017524222030b103400003002e0a40b6542c0f40c080d04444035074803c2d1114000d00407054040310b10007401e04079201c02514013170102c4030703100005500c2d004150401008015038070507280800001002500391160040b000249202084005602c0b540751035000b1210640d08055000c42e0b5030704041c0c0d100c10641d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 216849118 1250 216847868 216847889
    0x10806090d02060601050a17040f0b0106081302040c030b030609010e1e0a030e0a0e01090510060c0b060f011106040c080c0a08070b07140604030c0b07050c0c0f04090813030309 77
    0x1c20080103034840d20018800c034104000440c41065080c030500c065402301d105142d0110450a01703041025803115401740c16035100e5445000000c1e010710a401d03e51042000c1200c81240080507402c00015000c200094001c2584940c4c0c00c6c0c0c2e841e0350a01c9201e001790019000090920140c0f00e20905003075417a03103807244a40842410b0240d004000c150b0a92a6900d854264011404c07000000d00300030181e003280c001c0c0946880013050840072540051b001d1600500501c0440346d503101c0c21106000f032003500070320056844000c140c0500f8645008072649805040444028452000503854084201c6080e1b4503603030b40900030041307140248002a00101c0546404010728109001c481d540e00ca40d02c034510034004001030400510849000c1084505007403400d030f03205800d040c01e00810300c0489000c141c45946440d0701146107a8024005c5030f12000c1c01354060010018900100405648402d4060350416258103400d40040c0841c40101a904114001058100d0960800400d010040d400080200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 216850368 1250 216849118 216849133
    0xb160801080706090306020a110a060209031504030c020405090c041a0f0901051e01050706020c0a02010e041a120a0f050609160e0c031e0109090308090d14030702012301080609 77
    0xd031321003031903802d07a0b410032000b5a6130310f0016000c480d20307012098030840354010b65024038104002900103140800040381240c02000c3c400c07900519255054030014040f42110410000506054001d42c0e480001d400946141020507c0814251881703a801c04a40c1400718106800a00d0166036820344218261100e0179198180004101000300840180c84071504032017500210340e00c40c0313044500303072a80b000e030942d16044070301d021a944400c0301d00120701040710410707100220308007446042000341d0101c9160440862490070f04c011580b203c440800385029010282e4045140408420300940c410f8000b0000d518148038440d0410b00d61288035506500701801c10006154080021500604404e0030b60b41d503a1148a00990352240854900080702010400000c0001d125800224150700030703100c490042d49c400d05a541c8480d00d0141690128000407260190f8804d81d401441c0e010800e070000007a100d50700e802c1014440140560000d0300070100740140440203043c0441034020283c0f40050151 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 216851618 1250 216850368 216850379
    0x31804150518040507051504060e1f03090813171209010905010f110604031e020c0303070602070c1206020d0c18060f0212040e0402040c050708160204090b1608010807 73
    0x14411020041102c02c00303940204041c00700c11300c0b4070401080c00401d5901503202480948010360024462480803a450000c40c800c1410106114071807901b40c1d500141c103041640500340c00400a10009556011060180030001a1079030070b41005084004101446d03404100440c6c1d1600d80c01c41504000e0034400e110301c1c6210b0340c0110801003543e5090030115041d402001c0100d03003002d54205007840c81c5c03154030180030601d5000741d940745207041a10101d09101c0311900c0180c0c1c1d24111001c420341c142e84108464004120780c2d9003d407800c3d92240740da40c07458035950844d01d59030b89803101c8103440740342c0e000a42d5002c201700c2d48900507004403681403803004110310b046140401c000f01e208000a00c41100e500f40c408520900c90900c0c0f01d40075051291f01c40f074807440003440c40d1000316001ca01451602040c00c0810b40218140d03010258403089141c03a100f42e0303000c6010003803d00302040741c2080d21140ba050000b0a000601440340c55086020682c07004840303c001d00300001a844100c894100da90103114 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 216852868 1250 216851618 216851629
    0x15030607181412030a0e01110c0a030803060402040506070b010e1308030406051b040e0612071a162109090501082d0f10150609050415080318041505 65
    0x726880c030510180d000303142e200070400e5001640c580c2c4100b40000100070508541292604402d440280d86010465803590340c215500c2d100040d149500000d031020401c00155a10011a804000604054189591400443c1040d001110120f8507140344070014410341421501c1503070301444054401d0486480c58a41c0005480301810142c80e0355203138400075481754402d412581900b95005140c0e550341c1c0c0d4403801e2a10380c450035a1503610500c0302100b000c03511180012030700291807034030a000201901811000040303034003107107801540d06800303c820000315401012075020f41040c4101d10206500c6000c0c01050301410381c010115407480d120052220a100041c02201c0022500c1c0b408801140f040e064028041c4003004550944981c4252201c424400f0810012010350701c0d006201e00020190109900a250f0080800151640404000c0b92030140c0140d0b554071140d04004d00242d840b1514907055501a81d103021140e4000c0401c41114101849114915a25080548800c034104800141c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 216854118 1250 216852868 216852917
    0x1401080c0403110d0803150102060c0c030a0818030f0306010e030732060705071805040b06060318070602010507120603050604020f030312190b01020105100303050c0705040515030607 80
    0x902c10309612103d28940c4d201d00c451004100d80140c0da141d2646000d0620000801003d01d905005000d1080411003019900741503c01c51118440590b060441c150022542804020b044180001000d03000883d401e4044c4010442e00044010301c9030399181c4400050110741103070480302e0103a84450810840f000c1e2001e040003048241e04030803015042d410071550101c5000440541c0c1c001c80024202c010440001a6001218402090100380946600e800012118120b0300500a502c5000000d540c07850410000d55021000d2400b002da1880180c03402480d01102c1d40006d0b015030f56480500c50307032541010804403e1707424014140b09180c2540d4074507490b030001801c001e00462111504544135a000c3c41540c805003200c1120000924161841401c405104407444181c04d2624400e101c0c02d5106005061084011259655080b407459600301ca07507501428a20044e40607401d004500f80d070f84d6004c0c02d801030060482c0095102090410541016030103020013080c007203107144a0401260400012 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 216855368 1250 216854118 216854123
    0x1623070b030702070506040e0106080f0103050c040f0e060a0614101e09030203120706050f04051903270509071e0f0203070c0b0c16061b050703050708071401080c0403 73
    0x1641c0341d8031409400da103046220b40029038020f002060105003207228440c03180c12030b54030b03a882909540b104820005403036800c1c000617041e5003241114200307070700740703508951107201450b14006590b9400f0207540b414031505407811400700e501d1b01001c105140d0074100d5642c214200321020b8010050040d000740c00300480c50281105c0c61911005500264005d81400c001550090141d0b10002c50781c0c1302c55001544040421200d0700c0c50000443c1e11481ca580c00644607603800001003c0290700810400b01a0344241c604504012640d0b0101108805c00908141c08454140302d4070906802d010810240403402440c0c0300c2086010410812098a248080b81802e8840e041c00340794206030280480c02c600c6040c1c2d000c2d01119000c00c0009214502d2401840490008410348161705144071040200c1034241c071030341000401401c1000c417046a08901e85950754070410403148031590341d5aa07982001c55650041820742c2001104001e64081c6010841d8449002d28010145150455000700c9a02490001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 216856618 1250 216855368 216855389
    0x160f2310050903040306020a090609060e090601050912010f020a0e101707090b030f0105040f06030b071101020717121b040314010e01060816060e0d020f0a0b162307 72
    0xc10300440c1d041c0300b2070707005d5a0082015940c1e003203007000140803240300380302c1c0c44c0004d80c0010340065154411000c078402404018050820740e1603440044031250411881036500c4a000134070104858002d204d06116201c2c4d454026850714a41074011380f64006191085001d00d410059070008170b98003a40100684815190700d05454503030403402c84e1007003030396006410110400002c0c40140c0300610440d60490300c00721814440c0221903040c2c1c1d0203448aa20006040850480100d030515006110340780c0229440b07000181000c01544030b01c0310480443c9680d504084c80020a10a4240f00c4039000b903100c041254200c00b1101c003105e070007000e07204510019010112025043c2000e01d0290044500e9061a10003400b189441c3d440d029103400315010018013450b0522030000b6100d002d865000c4154070001c00c80002c442c4c035030302031104104c1080704c910b41c0200c000c500441c4860340c0070007820031a60180941035011240303103041501c04d0f084101a03000c03001100c5400303402490004060f0150382e0b07200075 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 216857868 1250 216856618 216856621
    0x5060706051305030d05040210020d020601050103112101030303051003080901080a0b04050717070f1e140f0309071d1503011e091203020a090b0c03160f231005 70
    0x110b6803480c000301c07000910900000a415010110541280e8084c42c02200c001e42003006510040e65141e00c042044009078200600410940d80241c1c80343e880301d2844202585003e000381c1d054038980300010900301304004420014001c0c16490700c2415481481c02c1140d20b03143d4219202c44649000d0720104504200180c800540d460400d41c004a030402e00c00740041c0401e0810440c00703021b10084180c0030310b000c003820000900817031061070039003000786003915509032504658510030810036051311008140186080b2040d22241550010801c1c030b045800c00c10380343e050622102e400c140c10ba82c0100482c4240400078900e199800000980100b401c555058140c1ca00c0b101083c050b100d5942042440f806a500c00071920700607030464540316120b1140c4c1a0b040ca10303102c0c05d508a009001e80301000560808080c0b00e010200c07402051581245d50490342081c42a451a40c549001e4503012140ea4a9515111040016100d02c50900020442121891207150104199242c0000d01001190754541c1d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 216859118 1250 216857868 216857881
    0x9010e0c130f1e0203090c03160605030c0408031911010c050a030209030a141509011b110f01060611010509070605160804030803090a020a0e190b040b03010e010e1203010506070605 79
    0x34400b05250f00901159100d07543c50010000c02500102d4005a031070094462a03050361a0206103000352070040a0003846050802c0d00880701500700030101c1c0c05a0908000c081030404040020303184407240840c000e8500441800014a1640720f080307200d08586c10682544000c3d9004416103895035414a001600d1300c410f60000307403402c00e45c040043d154600d2100002d403000f4003c5180e0300c496810b42400d080c29110940c4039804c854011098150344445903255543c0d43d44100a04161255644105c3d001c880042084c1c6084031803980c404000f04101400c0e0381140c2d00e0038000c0b213038810080301c080c0020506d003e101800510901d02c0b01c142c0524009400010403040c6001e43d8051a00300d41a65101d19045107041e40d640c80e0408140e10502a1030400a0035a0b014450284264101d039070522290101c0d10117003010700501c04085902984402d00755011f900c00b486902c40545c890380022404d01102402e141c01c01e240c042c1c820382038000400040c80603443d40022540d0040d80030b4800a43c560310032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 216860368 1250 216859118 216859121
    0x90108090c0d030302090414090a08030624030103021f120c020304030b04080c1e030d020912030d060f14010c0b0a06030b01030c0504060b070b0f04020112020c030309010e0c130f 78
    0x1c9960344003607111400814103030316601601001c0c401b0b03942082412030407800380c000200121260402a40000d80e41d500241042004d1600403101030181c80407038000300f1040860301060100c40840c0c0101100410a61804001c01d41c00c031281040c174038444a00d0010000e0140d024011410f421907120762416140c1c61081080b140110342055260401d0709044c83c2421050707001d244624828030410b98840140200454000208c0c0490801135184c0720110044801940024000a43c00040031240106442050000b03081c2e05545510001c2e1041c20480030f011440320940003410003072a98042e4000300c0c0d80240d80084525048444013030a9520b1000c0240070308000d4100811b140c413540c00010400811548190a40d003045a043c0b1a031034461540d1f071680d005071000a840c280e100008204090103011400d9000b170700614102030800c4c00c2e44240700c140e034400d2002e0326450b800002006101c48081c420b40d807030b00c2e03a0640508000304111b80010b8917001c140c41101c03030380e56941e5401020b40c07019 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 216861618 1250 216860368 216860383
    0x2622140108100b13031a0126070312031e050621210705010b0303031e07110105070c02040e0a1a0a02130e0402180f0106031e020403050a03020f1209010809 68
    0x845466507540e1011114440720795035100c22551b9111294000040003844890b07181654000261510a05490401c00005515140107429240140798000c00450480b0805156104032920007044000003c1d003c011003022000c52803403034070300c4c1000748005a540c2d00d5801c00341d0b990b5000f005000e0382c1003085c1f050800034080d2244542d0941c03201100301982950016201c6980260000c100c880507400900d40c9901c01200c8902c803400c450703212044c0941000303140c20f80081c01860318010703404a800e85103003183c400f42d6008010808028540007180b07054042d241d43e17045414041c01846c0034907681d503a00d0100da0929042c800300200001012a0300350740c140c807403400d41030105848030340e9166000e9207001e07015a002da00615205141d01c20000b99050030602402001d441c0d100680e286c81012002840100038020304900d040c1d20300800300c1d0031400604080c1d8002d0000d80341c20340003864041d01e03007171120560010030740018080400107049507055420310002800d180704540c0d1600345c40c9080829 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 216862868 1250 216861618 216861629
    0x1303030b030717060a0204050102070909060917040f0b0906030705160f081c050402010e060d1404230d09030201140702030d09060801062109262214010810 68
    0xb40071000800549103464140d10400540641d1119201c0c851418140d2159000311400760307000080401945045900c4080c0c030902484001074200002ea480303840d840ca0030110700f40400c00c045400c0c441d00804030307078010081c421250450702d041c2034030010400d1030000400f080107009000c0ac0300c40c1000c03528586840c40c183c3c06540d440d403103403c500d0100c11941081d8115000d0036140c403200300e905a141d100c0c007801150142c41740483c0c4980c6808111280e03100301c005040d6183c45590070140c0040020845014a10608002001c11965a81403041d2440d11400211780c1d400300003a075038040d4002940c401602d80a107810100e42207208030800040c0b14244009405110f000c40340c5a40e1a44102141e081d181d40b95a0581140d0760740c0c400300c0301060780365096000d001c2c40701e40ca0b00717903102140d1104020511862028a81002c5c1c2c400c09040d0703e41445600031000307030008003007104071403140c03180705120b10910640c40c40314140101030170b008040006450602c54854041504020314800c5000240b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 216864118 1250 216862868 216862873
    0x3020f030717030703120915090c0f0b0702090a0b060403080c0102041a0310060509010f1101150303050310090908030a0203060f19030c05041a13020d020409022a061303030b03 77
    0x403101c02d0700c00d075690b00540007900010701c2c0c603683c0f50140c0c42c107000f48804e081d0800821a02c4007404054000100700c49030048608004c4018000707026031508a0400052005c00c1d20180c8610003801400141a0010307d034000d62413414684810654500301a101640d0701310a00c161144030782c09900c2d00904c50307070b0002c1143c500c0f0b1124150801ca520001984516412007004a0542d9644020303240c41c080d4a00b03c1d804510054011a00355102d0210000400315160010528003104060700c00001c400760402e0300010360010401400070340d91036960340103281c000d504220803501520f07141e82500001d0442c200441e0000b01003a41c5945522000110303090003060b1450300c9800100800ca032030903e1000301c2d5661034070000000c00e450301c1c2c4a6000c0700c0303506440040c03402c803d580800c5004110301d403a040c1c0a590038403e07a2800c209600c041c00141940d102c0c016621040405488090542c040444081000d07500c904d50084d1030100341250804150000001d013140c203890280c0203060702d413417101e0701803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 216865368 1250 216864118 216864149
    0xd1202030f16050f0c060a2a030201090308092803171f060e06041401090312030b09060301090c060f11061e0708040c030807080d051f05061303020f0307 67
    0x401c41d07050220306030b500c20411074000425144855440300e8404402590054041c051106094000c480621140030b4254841824500388003030841c1000e000c50040d00140e556000042c10503402640c0c075600180745000505454a0290401f01010f440705220441202110948404c15020b110030705d008001c40401d00f4103c1c940809100300d110f0400001c02170002c1c0c000000030f1654040c0c0c2014013030031710140c1258502800c1a490580550181036040d041104414002002c50b025000341c200c039141c86c0e9004501400c0b1f1000b0400041405044244240d24181e082d0000400c04902c20003101ca040c2441400002c1f110020390b1704000b2110305000c0c5001d940c4c10811080860003408400c1c940c0c2021840494503100000c0b0f41c01034048130000c0c15600520b0080c40440c903003038082c088030382c81084101d240101480f0a074040d9a400d840d140304911000590000d04482c1c1c0000101071704c002da948605080104186011407d080c1c403020b400b401030a04030220a45040c01100050a80083d490091 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 216866618 1250 216865368 216865387
    0x70602120a0e010f0c08010e2d0405070e0c180a050307060c0c0f0f09020d15060f020601063f1e150f0302210d1107090b0d1202030f 58
    0x180c04000b4810b030080d441c2031808072201c03140c0e1160740d200d00c03419682c20036176a0903c04002c1c40d0450142185040600030010fa0520001100881c1d6074007008045600c02030609140183c40c081c40c50b08040f50901e400020000d2640412003a40d03401c8148950a14840031036502068900000fa00712580500800c080800c0c0c01d5080323000401e02507c00c2d03000c610029075449031181c22184c41d02900c86442c90200c0100880100e94000d094041416140040e0480e44400101e0300e050642e8000c00105a0384460034003465018400c030381c01880c0781e040c200008400c031842550091200030b075903803014286240400361594501e110741c3c07610004000c200801003102a41c080d501e0714018120307155a080038484825080300300e154000715114ac070512040c8a00316800c0044841c00a50f810100c441800718500404400300320014042c0300a03200c14801001c0070400c2810510b00760404241c0c542041e00c1100203484900c07504e0701c0c8030340081c80069407034030f1600102d0940c8140300c03034117101c0381010030806007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 216867868 1250 216866618 216866621
    0x120c0204091b03031b030507140c0607110301140f1b04050d060b100906050f090d061103090c0303090d11060c06010f360b040b12060901050711030405010302070602120a 74
    0x903213000343c0380c80c4100342c09158001030720783c40110001c1c0056001c1c04544002201c41041c04135244031103050f0b500d00c00203400400e8890308410340075a0000c2604c1c0052000c0d04082c414a1001104000070442c2880d010320105000f0b4009000210700304010300b850514403860a00351005084020080c3c9c81900050601e00050100140300901c40c0f008980303023070f030541c3c010b0002904a840316160241088400446039041d50011400c140d00249810800c030005086031061032140c00b9210744558503420500d40d00ea1411959103601c0b4080d44c0104000d490947c3d0741140220740503072280108a0441c502008284540203120380000c4d944a00d80000c01c05e00840038060003510081142610003100c404601c02a012900b0402c1c3d9034180180a40b1a000240d40c000b1299548050000300310140d07180d003c5180340c0c08242c54864103811040078022490070030f010b8070344c0042c803619103100000912482c85850b44910710034507050590000d0404104119601a50701d591142c5000108a06e0036929000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 216869118 1250 216867868 216867923
    0x2120907140303070b04030e01051902060103050606061c05150d1412040605031503070b0a030501030c0803030c030f06031005010b0912061512071a18060403120c020409 74
    0x1c0c841d42040c0e000030341000810b4904498000c2c03541c040a464645081e0303040203c001d416810024100102c014184c4010060030034285640e000300741c2036256003070560810300054034580c8190000c004038402151104040310b165589074000103441e44404420b040c80201c2218020703000080343c02c03400248029a45c1400c9440307484030595282d469801945102071296000d1600450b5062000c00c1110b034072080500d15060000d82180c0c03c04d5103600702c5240c10780100c2949400652980018000c00011368905401014498011030035820000076140590000800014024980030700241c2e403550200840080e04120800170000d9503103030f640d012309540c48000114092444000e0120550300c00240c0b141c807035601595142055154030301001400710300d19020310401d01c51014049100380c4680043c8004040004c0c01d0380c0e84400461a0641902c10300c2c120a114580c03d010400214444090b040e600740701914150024011a20020340200342c0d0102c00b4088441079400658002411103114 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 216870368 1250 216869118 216869129
    0x60316170d0302090607030c0201090302060d0b2407030c0c0b2a06040b0115050c16050a09060b0a260c03090106050904080d0e0f121b0d0804020609010302120907 71
    0x44000e54650304064043e4441c40040c1d0343c00850030001342000c2032042528400141c814906000c410340d582c1c00180315a04403105c900e404507600d00061100e403401d02044510040342c040414280e561000510a07140039501c1c015080c403941c160400c0030050605042c10190165050154840e000024900f0440210384003102802e1000d686c040520302d00010302d6481503503c1849004260701341030182c450f03c1184900708007030007004c0c4490b0745a0a014040003c601003501d407804011031501c1308028042c29240d001d142c0ca18600101804a62111021140303222860b0a04010044d00c194104420302000301000590b00d0485040c004020405130055000300d003000f0080c0011034580742045090101500c0061000e6410410400100041d40101c1d048044070002e5070441802606c0c41c5003494007802c0300303202c4c2c0c4030000b466520703c070302154201281b950300000174600c3c8600b40304040c01c0154058006881510081001c042c141e1103a01201c0e2001c030301c41070410072030811000c1241e60344000d0244 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 216871618 1250 216870368 216870373
    0x304081c08150f060a0c0605042006040f09090309090f09111210091a010e04030f0302160204110f0a03020304060e0f1005220b07020f0c0102070b0306031617 69
    0x21454600180b0188102d1400060000c90110684020460243d00c0302d40d01c2c80030b12594030400340104400b8030806210780d00980700e640101c0340013036807101038403c1046024030410060005001c111805000300060b0740c0e0340080016400200d04080d50759060580c040700d100790805002020311003064000846442c410000c0c280b400c140001000810900400c44000179444a0f412104642081d004041803e0040304070070401c122082c030307501252000740c114400851125091104040c3d024800c1e070340740034051500b1803e01c5012105001c121030300031400780c880c94450080501c1c60f405c00045a081001c07000c0e03c00d5070f600391703000098042e410449068a605140588072022507601003002e41202e14104047c0c020000c0801400e0f006240140c514024182c0c04000401300c40044004c50040b01d0148a81c00318928002000910b00802c2c0c00b014040364008001104150360002112015981c0f0140d18944070f995a4000c00e00d8502102e08030307229540c1c00f0000150403001010f02c020f04454031001d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 216872868 1250 216871618 216871621
    0x102130602010209030309040f0905010204060906080c04030f020d05101508011a03031e041203030f150f091a09100f060305040312020307020f0a0c0f050f060d0e0304081c08 76
    0x305900b01d00507078001a4040d00100061111440e19520030403142c200100009202030043d02c6450883c3c015411120100312500800e0040030340100440b5481502640b01514007419943e5043d40351819401c02030140c10025003840411406001458800522050801a40b03007150307040905c111041c410140954038084152015203481003c1d0200c40c1c00150003181b5140b003000300c0c00c2d5201c1041201c1129080d00384404a00a1000c544102c011406a540030071816100c6d03030000102c448582500610405184080100742600f1460b0012103541c16000035004a01c14074802400d0030400b8150f0f400002442000f6a1850320701100342074035030141c100014103031507a10035012180e040d81c0140100300080b444009110f03c580056074022624030541d2091554900f11500c0d01c80c4143e001c44064070001000c0c49211640e0750150000d100840c2d40b0102c11140300041520303072058181c840d241680700c00140d10040303020803c03540105030a8049038440002c0c110103c49292010000700b001484100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 216874118 1250 216872868 216872879
    0x16060b0f03061026032101120209010303030b0303161b0b120112030309021e0907030b130b0a0302030708030706060f0503032b020c070302040b0102012307021608010213 74
    0x5502d84640c80143c400c1c4003060a0400d8502406100d41a940041c0c8240701c10401c212014006403100a0003041045058072500c166141d1848050304001c0e0341d070f80e42407040030143c0c0c0e030300c000705045036054180000c0240f1400007081c10340c0314010000701c0c100e469207150402c1254440920120300306d1034418020094032680a20300f284140164961501e406000600c4090705100c14024100c0c42420002140a8140d0129840c07968082c00186102c0c5842d136007100d541803d0080560041d258a410040f14031543c0024a90140415809035a95a5031070f0586840d20340b5400d0360040d5800600325442c456035046030b169290301207003085440c107003000c00000b60500d014030800e0039580010b002e503040c022710b00030b01c0c0b030000180304e0703070040d24466458411a05200c0e44010040e441d4100060040c040c2540144401d56000c4082d5038110381c501401c1e44c50b140c41c1c0d00f20612805503941080801c030703143c401040b80b520844c00601a140c114418000409490540c01442c8460300080104417041d07598 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 216875368 1250 216874118 216874123
    0x240406030f020907110a080c071505071b05030703140c090903071109040803070f0e060a02150c030403090b0c0a020910090c0c030f050c07030c08010207020a09060f030b070516060b0f03 81
    0x351840417a40d00031007524002a41c0140a811480d0a000071203e016035202a200e903004003080303100010410004100c01400101c0b00c15502000040742e2a00e070007403510010a58600c9240301c06441003074804550241c0400070700558081c020018038041c96030901d546001e8aaa11840e403c4a511043c00c001c181d2500302541312a10442e00007000340c0c2542e07502a401c2d520b8443c01c0d19440c2c01c00030300450341d0a05580d05805440140030f1030b4010610b4483c40590004111f0000d032035243c1c422400e200b00000681c0c8101c025007610100d004881c0c41c0d220444040c0c0c6008550340000354044880d81c100003403210001c2d40c010449201c004180102d440b2000c1c1580c417a01a14405000245410341c0c1c4000319010790020001c1010007421191002e6417600d800e0380160081d00203c6969400143c28019894400a584054101502d04101c04c518001c0010000c200d41c1c072005004210b9240001c0d6640e0141003681ca503440120501c00140c0c82d00d1034044000c2c210051142e2040b00c07200e50740262401d00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 216876618 1250 216875368 216875387
    0x806090a0e03030f06040e070f061701140d080c010c031a0f2b020909060907170d0c17211509040b0c0405030a0506010801110a08240406030f020907 65
    0x40c070701962658954402208141c24018200d030b42180d2a0300c1400c01855003008050003e000d030b124080441405c00d200103008140916814030f80151080040c000c9500c0304614800c03501c4115070502d00c6046500c0c0c0030300769024039007020000f946003001004060341c141d0040c4540d072040b1506503100d074440c0781c20071071814038011000303030009407142ea80708510b0401c0c465a9a081102002c0c071003440501c2d40014041a801c0312081010303040041031100c04c1500b0005040549528a07003c4041c14400c05842e66804006140c0320802141d20108001c3c0700e0013480b0481c407030340f560664070394680703075000c03d510540182000003580414600c0058410301001c4091400100c004000c4601529141c54034014040c002d0180301c06035200300030001d001d507030800c2104241440385020b88080c0d0314280d40c0314219030141441c0c00c4015410080089159446007160746e100624504410030910f03d440c1ca50310051600840c00d400924000c800f0003440501189900f131075100722042000c0e503948803412600c1c03012 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 216877868 1250 216876618 216876641
    0xe06070302030a0e03011806091101030c050a0804030302090d0615090204122003150106080906010b030c0c07030606090e060a090503040e070507020901060c020f0d050c060c0c04020a0806090a 84
    0x240710400503d07200e50030302e81c10420000d00114400020780d41c0500c200407025800c4030155500c0480358104a03c145112081810900b401c1000070302945000d403041c4561300314481000101c03800034007014080d070b06a0350724038000703080200d0559140c0f40ca4401044111a4840c00c51400c120008121980b402103034280c403800c41d4804050742c080d5650301c00040342c002101d601d162081030103142c240c504110040c0f01c43c0003e460034980d545405400742031904041c18612054000b1001402000b0048007100c0c0c20003200b00c07001d980c0b03c112801c16403c2c9003164200030700d00c5081250025052010340c1194105d80c3c940000c0d1071146e180c0b9011901281c1840100600540041c0b204010800225070150351000081c1440c41c500481903000924000090b00201c0105010101803001c1d4281404881c40d030503810390781510810029103c82d50307100c5500c910144240000140360401e110309014816440101400035510303a01e0782c60001c0c000290496072103001d0102800003900c0c400a50050102c00f02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 216879118 1250 216877868 216877873
    0x215010e0a050f16120f0f060302130c0c0201080621030a020d020319050a020313090c091509090507051b0102030702060c040b070f03050705060711060c040311060d2a0e06070302 78
    0x100c1c030030010fa0390b20048110512851b0303501c656519031220140a40c15281c1c44841d00080c06d00c0c11881084043c14241c06c940c400d03649400f40c070101082d040104010341a4090900c0075040d601c00c40098280840040d480325007a4001000c1000e200002005e4408a2800e40a4070300c01c110400040340e5034010030800d0b0b080180300020007414a4015401001d18511920559150042c20040c4030340140e0961b2000400c4e03980c68080302c0303a0540c40107440026003421200300c80070b0b02c4000c40c010401d4105c3c2c098411a940e444011405507400b640032501484020180302e00310241205041e4001d400c1198030702c0140c01032000003803d10444030110350684d15031504440c181241f94584044c0660003a078200d09000d0200182000704208100302440382182c1e50b140240e804c0300c0f2907045c0c10031a000c0d01c000f0301c0213000d00041c0000383e85581034108640040d0760140e00e0320a502a144c0180042d00b441041c0700310141ca140d8a0090070302c01c10a0440c502c3d468440f0765a69800a00c0b0084c0309000c0b0240058 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 216880368 1250 216879118 216879151
    0x4140a030206060904080c03030705090f010e130c0e0d1104140105030303011404061706090706090b040e04050c1f0206010605120604020a021c0e090f0601021c0215010e0a050f 77
    0x1e00c4d007843d0464010b4080e25105040c01840d150040c5164001c0c1c5001c0b000c47d0010495204616151030103400704442072030102c0350204404085141c1182c06141000050703240d0100d001400c1c860010700d05242801030148200c03000a00785040e40c119a96400d84c0120705040907528828006103001e8101c480280080d45180c5c600b00c0d0070020b129200186903406512420300040000701318070301303846c0700d030703401000d4403050510302003e61400741c00350700100a015410380100300420b04402903404840c00d0034640340c0244d40c0c41ca489400d1128100d40749074403080310743c0c00c10a01d41241c40c1da2a04001d02e902112501d9883d03c1e0f096403540a5241400b41c0c0502d0000024140d0400e42c01034424502140100c0b44102d41100366034000440030600c220004850070801c0c3e03214a4020300d11500302800c00261006400c04000007034079034503407408100d4402121800003012a108000d80c00050a6000d0400c61a50710b0313500e403003900ea0702a5000e0142d542041e01140010400c40f0170a40541d4054004146a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 216881618 1250 216880368 216880381
    0xa0617070311240a080702060a1505010e01090f08060403121a04090503070b01180605041103010302060a1403040303050f0c091807020a050106140312030411041806021204140a030206 80
    0x140203040640c40307640d103c9202d48039850008001411900307102c1e071a02d000300d00c1c004100919040008142a040605050303110034040800307803181055a03820f20304401e0050500c40107035206041070f884466890008080044c4500d07011500601480c802d07551204680c02c040440402d03228170b4030111400381c640000c1084a0b00c2c0035130100c05c00c41c1c46141035900704680e58481164400b400da00c250b442e050300111803a0419854820b00f00900302c122810007003200b41900c42c01d01404140402801071000180c05c2d2040d5004011820760a845014043d5882c94180b40003409007005465811107070000c4004075401e03480007025544000b81c0a410f400e4041d241442480030000b0140c003150640c0185481d9401056080c0281400342c82110101904401c04109051070300740c04002c1c9400180c02407007400001121881c41c0d00540324112001310b000c03504071308501c091100303803000201403e100095400804011035039207481680215a02c4482c881c5074880591204451080100140c0124000808 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 216882868 1250 216881618 216881629
    0x709090c0c0503070606060813050714060403080f070507060509100e01031b0c0209071e0e010e06040303020d080603071a0d06120305070b0a02040b161401050a0617070311 75
    0x305040034542000088041d0321000c0c01c650068109589403611264140929034128241d0703601301503100041110803100b0f4541c1e944924243c0030f0001c03481c03040600c1404942d544401d80e0003441d040282d1030750b00c204040c0c00120981c04a00202c40e5030050210014495002d10305450101c41c0243c107101d1359428200c03003114101c2418641c64141655003030014100303003000702092a240102d0b00c1d00c9000c5002030040200d0064010a000d04000400d200b0850043d0306000003041c0101c035060020404030400700591308108012600c42d00584049000800c4c107030b00080500711400591a017418a0311103000341911140c0034020b004101094500b0a0030710f100242c0100b02c0114000800504152519122003110246510a42c00180003140420a02c01809962504070002d08030443c41c140c80c0100190060042040f07003018050000408014041c40300c40c043c00024210008004510740070b028000209000d020301c002c85101c6260712102c20b07130005001802d403134002d1800340d14110705100708078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 216884118 1250 216882868 216882881
    0x2030a020f010525140c1006231207090c0806011d03120a0504050411040e0702190f050a0501060b0a0306050f0901090902061c050a2304140c030304090e0106050108070909 75
    0x200140385a0030140401c40d4801b610242e4500c401901c80d00a20445841c01d41c3c126030401d60004400903452a2000c1030f207944d200c0041c0003920020680c00442124904181c0c05a1106103032030308080c0d072402016840404039120f00702c00d8031011203010418003100d07210844505925056030018007902005071040014107103030800c2d4640389103016150710101c1c0a50f00040f0a540781d4000105090104410106131150b004400d84018042c04001d0070020348444500e0380040d1420803202518414820203105266000c0c2d0407000a02126942e001003000c3c41c2d01191b4400e00007854224003041500e000180e95910810041c21220280d007400103100091248401c100d03440700c0108500000c1c021a0005c074685c4402440700050949000344008050b282e80710f15850720b0800031012108407190641c13010307030800e0b04010041e0100c5018511146040408042c080c0c2c5480301040001e0503003103030780040030691050b100a0041c6550341005550b100c105a4070314020880c40002030101c1c4410340c0c03110 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 216885368 1250 216884118 216884191
    0x303100303110a0c08060402040b18060105030415150e070c0c1a0c070306090c05040c0512060f0a08100f0b01020607050a09090207033c05220602030a020f0105 70
    0x8402c0f1150341e07502d00440d610158014019500070004100c190700d41482426044038003a0794122101002d4000300007562402450141803000200104007408020445564011280300d000c00c4010045a406900e9100d244a0400b1800c11440060800b6220b00c010b5420f2903449948400c402e030804542002c1d002d14000b400210100510244094180400191b001140181c4001460203a542848a00540c03240c00050080d814085601a80f071b80c004211079180b0034841261680b0b803142ca0004039400011001c20764056174051000c241104045004043d20641040c20402d184145d010102596810344140f80581c014100054581d40a10700030800710b100391a00344000f50700c820f01d0340c0498101c5002039001440030030910344829141000f8110000d40144241d11000041501900420421010030204000421500c808000c101080d84860003e40d02404146807649002940d03500100d0b11000184206410b074860802e041c0f145074007900034588100301c0314510602800b6a0410492903 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 216886618 1250 216885368 216885373
    0xa0309020f090408190207060f0e181e151f12022a01050105060a050d0209030f0d02071502100c02030912030405011116091d100501060908030310030311 67
    0x848000d40c2c0d2122003030300c2584150852a1504a080344440952048810034019507001070703014082e65412100100c8005980c0c90803012071216180410a84c00110081c01d00040500051010003030801c0c0c01c080ca042000181c0d1031f55a6180b801e1450180c1c1842c0c0042c3d0008034103010840d5a042480c203201c4140d0300ca040207010f600c10045440300301d90013000298a00681102410005150b1300203000c2e96020400082c4080d50400380010781c540711709200ea40c1800b00005039480c0d4095242c05480c0c206034010195010480c0d4101e529880d10444c1d481c10006000c0d00e000481c1c900840c0300359a4901980798010000d8002000040d00101001d1208006510091089501036500c880e0840420480040030390340355498800090888a00b44402c2020380d00071240320000901080020320840b84401004980004416161002450351683c4001140940c00f001d0142c204260480c6040b2001e0740d440b401401e40e1040d07441e480380410b64110462840402040010901c22410b000115110005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 216887868 1250 216886618 216886639
    0x6090319030c021c0c0504021c060305010c03060b0703140703050412151a03101503050a08180d02010f0e120f070e060103090201050a08070c0b041b14060a030902 71
    0x3a40c001161440c1022000184540b16290450900e07160007103c501004a001d8004001985e035640c0030100da0040c0c500459000c11100346155280b040c4040d41c5000c0b001c02c00c2102d450381801ca001e0540501040080ba003008000aa01611101111340458050392000780c40780420a680009500400003a010802c090002041c0e2a0031044004103a0780318940c2c0e0415110106048015600411400c5403154420001d9030b581703071400300741d11144d9401e15400041080c0c0c1100444100081c039003001e03005220b09440c910401049000070180c0130100c241e04080000c0c202c2c100f0080c0d08203600b00078001261040000c0d4440d001c0d421a6400900007840c40e00341c041c0404031149030600d0760204800d0356001c2c034001c2113401180040e0941115080c80c05000310307080e5400180291050003505410031000d0342c00103501510900c3c56800b803036031042c105030342420301d4101403035482280c40b00c1e901806590b40bc0002c1c0f0301d032115194240e21070301920150030928420015070050a11a0040c1e8000c8c00300301 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 216889118 1250 216887868 216887893
    0x24030a0209040c05030610032705030d05010e04110307060509042a030b09090c010c1506090c09030b09061b0706060306020304030503091b0105030103061802130c03111206060903 78
    0x103c0300c10550395038039240c907480c008003040720420251103101c0615203400d05041240c0c1c1c642403403154919200400881513001498490700e184038040020580c949070000109041e05070402d010300032401800003c0c1100011000c0684a0005116444c0401c10401c0700720113034100303500030707140c05400044991640340c10b006040524406d41c000100000c0d41c3c0d448020074524011008036001103012006181d40501000041d00c2400c01c803201620040b06480355080404c0b035a0072680150403050070920140c1030500c070180202d24180000c07103142c012400092014030b070008a2501c078205d004902c007050700f10701002202ea64045a401e03038003241c582c8000701c08500b0900046020364806c2c2d50307990f074926100941505058401d503a402008812910400c41681d2140959056a030061000100301c0c620b10145200490040002034215140e00c00341c90311030040d5840001c04010030f4500344048040031081c00d03040c1c414910319aa1080c44075010400d94108030010b484c004002404840d05a40040d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 216890368 1250 216889118 216889121
    0x50f09011506110a0611270f090910092906010c150207080403110906120a03080a0b09160908030408070e04050102040e0907080c0612040f03020c040c0e0306010524030a020904 77
    0x101c4005000c03c0c000144454607c401001001c48181460401000040e0b00d00c006491000516441d520030300780e86000c100150024000c4c8070042c500f070b82040101c07000518110b08100c0d14110b90b14980000b50b580c0000315000c4000191042105a44062138101150f40d14a1046da00741d40507203403035900f0f104100c0005d910100802c0a580104080b08c2500620020040c4d402e170003d010b6401010a008450040540042d40754403c96050030b001900d540c8030707440c030002800048030155120560400b8403000c60f51104813525002d90075a900e095050b100c000b026661700c0303240309000d180d6202000412504054041c49904a0310900000d03103040c0d5140350382e18100d0001d45007452680c2160703c08000c0c03488204544600950156850790805000e01580085000d0013000940428000150300742010302c248040b600b5640700402c20003828151207001881c41990250160107813181800200d000d02d01a900c0411242d6440000700c00e8000282c01003000c0e410240045044507001e1004d4800313550755 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 216891618 1250 216890368 216890381
    0x50106080d050306030f030c0d081308180f012124060504080f0c130e150903070b0108150403120e0106030602190305010b04060f05090310050f09011506110a06 70
    0xa90b5100307610384c100801054113103480210b5107070207035204011404280a001c62a40d00b8141f61703040c580c0050341c1d18402c0c0b0007004031505c4000c1c205840011070b145220074141c0d983c6003022050b03802c0e10007a9103d10040d10403850940c000350319018401108500140c55400c43c0d001180b1188002c094a051707400b0149680c0b1681c4c001700086000410113005201c0c08220680030303401c60300018003103080311b0700208040815081c03a2080b100d494416012030032800304002e001e2100f8100b80390013149081c0f100d1a40300c0d08201c104807000b060501c000600c6030000030b8241078160150000709050745442c2d40690700303941c200b490201c2d0742d40c4510034903030220401e103d20f500039401510003580c2e42d410400e010404565101c1e81c441498a840010b0103015900c0050f2420750398a0705081256800100040d01c480c02109226a854800c0801c004030744070850f000a4040c2001c03101c3c400d21604d0714180c05007a03c050825403c40c04040030340030021030340706003590382802100e8002d0700d0128815884002c00c0d00c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 216892868 1250 216891618 216891643
    0x1090c03030e1f0507060c030e100501140102060c09190e07050301060f08040f14120c0d110f0d031d010c0207150e0a05062a0604021011061305010608 66
    0x40c0200220300600381400141030041600304120320783e54043c0380c098080c0c010510040c100c1d0b039a494005140b180641e000000f0000c00c441160100d0100b842110041c100c00d000e000034241400300050510750001412b24001e000d0150000e05015044052003442041c652100f46022030100c4002411909440d129014000d40d5942036900d40c18003c0140c40008010381c4141000002c03410030001c41c040300d100c2c0c404ca0348e00c20b031511014002101c040340741090b010005502000c00003001c560135040015400c103440c1e11a02d51000190300b1641c52901d0700100e0304940313072907088401c0700c1c0001c0d48651301110b00c0741000a020036500d0208a2400d08644003000e03540007613404041e01b84805104604460710144192920020840078000450104581d034440d00d80a188041849614403666214801102030100c1c400390700001044241c41c3d49950a40b400d03030040d15203610300340c3d03500d00c40c06041c520b140d18000100919195104200702803104100180d0b01075503201342c0858140c8041c44007a01515 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 216894118 1250 216892868 216892877
    0x614010801090b130506130501061806030210080609130303110a0e09090303060a03080f040b0739050d051204120b0109050127060b04030b010306150f150201090c0303 73
    0x70100c0ca00040038440103800384d0ba100c1345a00c4102d0001d100000e030302e0f84c040303c0c4c41140e203102d07001860242d0251500750054011051b10361f444007a0072a07a540107100f1280219126400f805403900140c50303088003920a03070f820014200024081c405158105140e1a120303181c009409184002400c989030884a155800112810390421062520030300141d08590781001440c0796081000008540a003544001420b0503000300b90040d401c0e05903010364005102d0400d085030784141c0d6180c40c1311100545c190402c101540d080c0c8000d59130040703250421060038580044d1103c0c0c5c0c108001c0048510f5845800c4459200e000a4441c2e80b400c08009000140000b40245041c1d50f224601041003003016081a20480e1900004210782036298038800c255070004014644840101401003000c0d010f1074002c80e0b040c2800060010410203400983d60480e40940341c10800e0042180b1094903001e02c03031045035043c6c1080300041c49a103422a07405000c0329094000050725107943d503928a11010030358020350108 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 216895368 1250 216894118 216894131
    0x5040803040924081911130c08090604050c0f0f0409060b01020c01030203060904020f010c0503030910060b0c06010501050a09031a010608092a0612190606030606050301050402070614010801 83
    0xc03460f050408450100c41111210382c6401d0000b841c1d969902001c8410f5039200e505031950610000c031280916411000c2c284404030704e10340284138040d140c1020304000103900d140c000b540714030011070400e001c0d90b44040941504504003041210b10008480f0403680025003c0203101076075501d1003007007a001d202d00e50116921075034200190800d0b07070004805041c54010030420506590b81203100d6441541111640809001500100c42e40301c15140010040d02c40001031000043c0001384610b99802010300030301100c1d441d049006110b0189454191240e40720740c3c0140610740c0105c000e0070541c20a8680049255641e44070403a04c504521181e50040b507a000050096541c00890305074000f1040c002000540360401c42c20304803403141842d0990000c4480c100508541d610412a24401c110311403c542c242044041d043c03010040140c0b607202c1d01d00d0844002066800b03402507500b281c2041d254642145c0c640000d0102030740c0305d403104485040d0344032900b01c54081c6003c441400b91101a0001514 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 216896618 1250 216895368 216895391
    0x307050405120c0306101802030702030708030901050a051e0403031119080901060509130602090f040f0c020c0a0b040608060d0b0f040b090a02090a0c0309050106080309031b030616050408030409 85
    0x200321011701000101b81d040003082c011003d03250399880f04a01811030040c0e907aa5004022030650050003802014540c000040c0301c0c9841c0150441c034011070020508208544505006807030b542e03156030004480c64800307000100032a001c0e500c181d10b1403680002d958542102c90340840e1427600260034000c041615042401840102489a000074103000d0316103054038140030030991001042464003c00381500011440c0464580f00c140c0048103d01410a000f983c0815860402a044081e03000c401442180304110b2240f40a6181074110741890507040e28090401400301c0d0348000040c901ea030000720418140d0f00045059a0380c1d8446c0007020004403e0342407a10b00011100f60141404500d5400782d003c2da400b59039001c44880e000b404103000040c8041c103d94003034014180036400500071f5480c0140000e86100040700a00d200b04c421030070380e01030b1880140d07c00106121580c0c07081e0140c0c040000102c108142050300a0701e8100c40c18001e0400c0e581310161403440d48650000360078691159041d819 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 216897868 1250 216896618 216896623
    0xe0a1b0608060409082d030f0a0c0c020a060c050a050f0102030609010909110d03030902040c03020d1401230636010503040b070810090614090105010c030909020307050405120c03 78
    0x20800001c850031320810030951130710006406505000c8800102010741c4614080820071004c00b0b0350b0040038035a40340c0c40c0c002030240c05c11400300d401440e03450500041140072032142240d0010158002c140300042407c0101c1141e2403625031408540c5881100c44103030103d0402c02000d5141d480320000076a0700d2400034184400f9110603030100b03403a5030400b1204d0001400070303c074024018006461245805038542070480244c401404081d41003882d088244000e44c0d419002400c0c0c400b02e40b00706010075101d042d0081e01d01f0009228240c1d4841c0c8280d030003140c0c0c007604031609206400080000382088482c000e082d42181080c4140000840000009546821600514000b484007400c3c514214075003500c420041000c020040c004000c100d00010300d07100d684c81c148e8405000f4200c1d04204464a0700c1c2c2c0758003d4448a01050f00ca004007400006056110380110681150700d952a92907041c40c10300040c010390005003000c81403080030302010409840d61340f80a00c5541c0b10100512900329203105060 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 216899118 1250 216897868 216897871
    0x10c09080d0804060b0402090d060f18320303090c09010f06020c0904020a0b0c01050f06040603020105040e06131b12020f0a0c050f010204030c1509030b04060e0a1b0608 74
    0x200e641c0104000040703441c0c02c1500154002e8101c8000f1907100c4001000900a00c1640002984401510b81c60303800d0041d01d500100c01c0c80c4040101f0403c890301c0c03840340382425060003802440044880011881c1d0101801a15100526481518243c00300720451078290b801c101c1d54070400b0360181c0c4070700c24246841007600380100002c45001d0305036414850025168003000344c40714040c1e01d10b500443c045440d0622600018000c3e00700c81602c54041e80c114a01800c1c055400c906064102400308219182500c604000c40340d05841c0c41d890585042503803c0c11050040c0301f240c1c4055819110000000c480c05001280d4031f44c0002e2050a120b22000503203000c40071416880b02d18410721401c00103e0200c021551180d240e405c1005d503c120901e001803400e680d40360002c440d540089400810000c05500fa0f9003038680d014905801045140e2080710081c0240c480642400d542c4004a00441d01c0c951001e0103445686040c0e59840400782c90322040c00060900a8582c0515030f40200a525400401c45 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 216900368 1250 216899118 216899129
    0x80313030f080408041401230901030e0312010315110a0503040501150501080c0d1514030f12030406020f130608070e010305060d0b100e040813060c0215090303070501020705010c09 79
    0x1106500b40f54541000d00d000702d0040ca1191a102140c11455a005100c0c45c0200100c40e140351101075100c08034442a600140e000e180070904000d01c1d541255408010b1762283c160007041035825a103151034800110384102030f84035400342d0b100003454151a41c0001012500006d84030706030b4034201460b1060844400305e200b085030441d100c034140701d542c4e17000d001d0f1074120000200003921001d551018a0041145000000341000030400019008000002e4485050030403415150300c50203020b0307265190405101c001110000410005000404550152103401a5820114200030380c0d104095000e0040b50480004200b103602007142c00c4e0f42c005000300100e01c0a04e002c0c419810940301241d80f2042005000741031200990014009030380c0c56081c440142090581b05620341010300b4034120aa200c420681311800100030040b403481e010b0300400ca68542d0280216044884000e1002d05d603400c04411198180410010a00800d10034005004203038041c00001803442c10f54034000d0128404c0382d010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 216901618 1250 216900368 216900377
    0x19080a0203040f0b0a0213080604031b050c040c110f0a0b0603070501020a060b03032205030717030910051e0c100509030a030b0d0803180c040b0f0d060603080313030f 73
    0x7000000354000007a181da165024107a40c249807038003d00c0b20064003511b800c1601042191f20002100e640000b40320340664040e40714280080103009059881e0311610348058850392040c1080349290803d0380c441110b41d1120b20740342126010750f195260500100501030352480e8040070342030082c030291100241d00850220020f00c0f001c0d00d07140010f0745524031032001900c01a583c14441c1c1c2680c40a000f1039050071554043c010400940b910881d01028490043d1070080c454510b01040c0d1403030a803001041e070581030300114109a406820014120a4220948200a03051281030250341c40e020400591003400600d454a628409501b589820041055040c01c24108801c2c000d0034600402124a0560320b0314002c1a4540040041000030b111488003d00346000002080b004400781180178281100200582d10000c00c03c0341080300f618841007001c0c4d400303006402440142d1074480d4200e82c0745407088501055403503480d10786440c03d0f08101e0f40380791500c10010000d410590300481f03c2400034640e080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 216902868 1250 216901618 216901621
    0x4060e031603080c100e070504110d0c020303071106041a0603070b0c033006013e010c1d01050d110a1809050403050304110f0d08040801110c102019080a0203 69
    0x720b647d00e101d41c1c441c2034055950703074448030040d290703000468541d0b42000b4410303c03400c240300034001d40e00e5104070f1f10000010281c0b00580401d00022030118091340e00840303201c4c41c4270624a07601c07610b0080900002d5140c0324030100000c0c0840c0250180004103100300196848142a140c179441c6030b0700300c040c0c0c9107481000000ca840c40082c08206250054028a00829554840f000440002e130941850b541035200f150001e8100c1c211032a50f0400741c02c4050000d1100e0320f01c0c1c12064501801da160541d607002070844610f1403551199002d010201480ca00c00309041001080700d4401d0741c440301c40040000c0701041c040b134000c8000300c1420014034008034108020700e400c5d10300901c203000c060070003455000d51072520a4103540d142400d464241c3c0040504034003401c03034600000c0300da00a1003a0111942000703001c00409031060150760300c503104803001e080e8005120b080d440c000e03c03144c4807044025884012070108005180c0c085d2410903000c5040440b0303c0310411001c1c005407002403050980783d00400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 216904118 1250 216902868 216902891
    0x338060309061302010c061b0306150c0303050619030c030605011d0136140a02160609020a0b0a0906020601172109040e07090b030303070504060e031603080c10 70
    0x241c4260712451004900000f000c0a20040384e0324039a401c2e000e801142460035040c220003043c2610040c4c090207403401c100d0542d54216220545240d0f85c4c5810104510100300000301e0f01030b4000f11b6100f00000c200002c50b111458030303468090b615400c2601c0d0700910030000d100b00000ca03c40c060141040806440302125550809070222005000e50380f809800303484410500c0c14031a42c1f20303005501e0b24035442d151000d9210041e00403c413000c0d04c50b10380094480418042c0403642300b1102c000048000480740d4a04548403480504220314080b608801404030010351740744040c0103482e4005490703460112640c502080249007950603000001c080701c0404004c0c1c1c140200080141c3d4500c4000f00d802e054446d150705c00c01072400b0304151990040e09080c050180c1c2c51002c1880030548114002c10000d004281052503503900041b614070001c0f810820007440202e01460481c0100c00d40203044039810310340c0c14802d008810b4640c0c01200c40890100e4181842da5080c4030304e82c00c900d44407008024103c4002c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 216905368 1250 216904118 216904123
    0x91608070b0a0c0606060804120e0f0108150a080604030806030d05090111070504020a2106050a1a040b070b070225090c11010204080312070806030d0e010338060309 72
    0x501c9a102103000c0000c006030550302903008418100d41041c410403445560b514041c2481c842260308480350f900c0700103040545070180d10019195400034006003a180f040c1c0d001035900302c20203004c14503074004444010705d0a9541042d6407000d0702d81c0700c0207055141003500e0058213003600a0000707886030b000f5041c846003842d441300c1a40c128820034031341043c0c945800c4140506014080c3c002d141c009000081e100c11540c5c03c20050007010480c985040303513a1000c9804901200c4040c003807103030b0001a0319010468055041c0c498803006d490204441c2c0361603600c2018100c0756000c8841201e01290850420000c41c0d01400b40111920500c050030b10054400d146002280019000300d04c4401e544400c0c0303641403840380f48036620481015000315540c98990702415075a03041000c02ea00c02c8850840051400ca2250602c6030044038090010894210340c2c40b810785070312218154480c1003550781d80101c13802c001d0f004000322084010f10241e80c01024040403e0030031040403801e02e40980410414802d00a400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 216906474 1106 216905368 216905383
    0x60903180d020901141201110306040c021c030b10020c0904060f0905031210060c0c05040504020d0209100801050702030a0c200a030506070806100c17040503070e091608 74
    0x103100319542a140c080588c0c45042500303201058560a0a030003111086085005890720070780c07a44450706503a800494203100090b100d81d060520f80c140305050414055080c809008805042804205d00e500e01400040526544450546442406502006481e0f41c020180c82d81d40000384140000300324140e94400130102d10301000242c40380112040700381c9552010380782c110140307000108001040000c20a0313070004282401200180d13521040540304101e400000003010303017000552821035100500180c155401040b1002c1c540c0d80100424180551001000450082c41d9080751100c403518105c0b2500112198000700c2003000c00b0814902c01d0001d6900d01d400d40d0740342402c1188190002aa02c004070710f05560902c041840b41201c055100d40d00c0d8401440c0560fa400407030320305034a50b40403ca4a41080c002d001c10410140402d4195040700031000a4003414441c515440c0c2c0308 = true := by decide +kernel

theorem cover : BRFrame.Cov 216726618 216906474 := by
  have h0 := BRFrame.cov_init 216726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 216726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 216726618 ≤ n) (h2 : n < 216906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
