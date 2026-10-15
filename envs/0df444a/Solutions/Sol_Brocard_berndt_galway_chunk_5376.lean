-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5376
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:40:02.152302+00:00
-- url     : https://prove2.me/submissions/5d36dabe-17aa-41b6-a392-fe1b2c35de83

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 966726618 ≤ n < 966906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 966727868 1250 966726618 966726637
    0xf07032406210204080706030e100f06051008040c09230421140304060c0504030501050901060801151a030402010c1709040f051e04080d2903070305120d020d090503 72
    0x1110b08881c40c1851850086404440710540184192441d041c0708600070140100c40c070003140140e9082c21281c443c0c9010310002c01e4075110000420ba4501001c0003c1c410b21452010180520001000080790801511000b16a280700001c140400003415801c94101c01000d180781c000104414081032141103000c48007025211b502400c002c2012030740c01c2d1039440d651098254101020000036001601c0c5801c25100c1c0c0c80b4505110f4107268803a510942916012112118141c0d5141000c20244600340034006400030103194a00707010307041460505000c2052481e0941051000000c5021079105003d1150001c2c1c206c0403050001c01c101110212590008801d14400da007840140900c0108910409000e0b403400e1081c244000000002001d03041c400420594403200107124180c459040c03400f902e040c610450b945030b4003898403090b000c4001010741210a00076485000e0600025000069401c5007400c0030300e5543d1a07009110700315008e481540d00d003840346428500c40404000303001015000088 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 966729118 1250 966727868 966727907
    0x4080a050a1103030f0a0e0d06060e06030d141602030f1504110a061205090a0b0c0a1b08091e1512090607090b09010c050607170c030f07032406 63
    0x3402c0c2010556a8041c0705480203408004000154042e40600d5055a61000c0030f0701040000c0655150030048030f4065001c10b0800b2460020402c1600d000c5c042c40c00c0c8000d50313041040d0007008040141003203005440301d0705d06207030008048105668040041501c051101c0c0700b1980c801c0f80c0c601c005a400794003a0f4040381c0c0d640a000e406452803401c0017400d0151100c0d035032041494041d00325120301401b8050000400fa001d0603160394045400460302c2031003a040080c42c1691b4641b107820060844452034246950074058100000019581200300c2d400154125842004070046100c04042ca0031596440d0390b01000c210700030051a0004400750600d0704030f0f45250183c9035103215440d030f1242011a0300e180015004141030107640741103001384c400c0003810316290044030501e54506152550a81d80c03800441c101068880c2e0310302102e2081e640c011921140103041d03050a00c481040d03160081c0a21041c5510390b485044076182583c1c031380080300c05204e08503407210703030f1140064410350342407203c0c01d0b108 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 966730368 1250 966729118 966729143
    0x1103043005070611011406040513050f0d020d0504050f101809050711011406151e03040c050102070605120a090206030a0b100905031f181202010b010e01121104080a050a 74
    0x9260602c10f021b21034500716250005960f44108020007400c00400c0695440214095400030076420000650036500c4c050041c0402840301c00c0203881c0081c0d8056100030000104804d00c00d6440c0c0e040c0c0c1420b016420b44003044002441c0809803000441c00002c0c540042c3c400e80c00091f10300c0c817900700c9405803060381c580e1075102c005482a1800e036000042040d80c0d4079110f00102300e0b5070034081e44a48800c9000054503091810054a290500c4800058104030030804003c1c030090110302c5034800002c02e024001429820700e402006025130203003118003d06c001c1058001100d0120a42210081603801000656289004207a070001801d5078407102e03000e01030841a030074605028007001000e42d1801001020000d02210344480301411014035410403640b40c0100041d4803d10035551a5003600c902d014a42c0000d103071304000c0c21610304599044c100107090b10030441d142d80010002568018a440115106d401c0e040c04540c144142d0340030840300d218000506051050200345240f070544202201144d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 966731618 1250 966730368 966730397
    0xf3309020120030a081f08071a0a02070e1b0301030516050f030c091009060e0a0c0503060a0b0a03090215040503060a23100e1602060711030430050706 66
    0x58105072000d04101d030b03c208403d4143c1409183c00d00c2d80300c4040d100d00142c001e0141d2505503036203020303440281254400c03001400300540d1082014040340c40101624107140189400950ba0328141c03080003e52005807002c03414942d82c00349001052442209c041da525652842c1c0160745800c43d08401001810316400030a02e803410041d00c800b0824010002d00d92500500d0402c004448045c2042c91552404000044c0c41d840314040e04005004985800c002c900c1d05410721019951101c1720703401088820400c03c40c0c156289501c0c00141c034199851151500740b81541500200038601c4040d5000c0c8100c16440c0003a800e080c020300594106a0aa442585801c0102c000b5036400d050010f03403106001d2a000d00c0243d45504d016840b80380111031624140d0b0f600d400e19240482a0380c2e480c001402c0501949900303404008454102e415450402c20000c1c40c04541c641364000c81c0912a40603c0c44591048603005440f0b010519204a0b2601d50f1300001c1c03480e181d0b0359400d0b58442d5101280040c85c44151 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 966732868 1250 966731618 966731657
    0x209130f210e0a0b1312140d030e1504021206010b030a060603150b07050709090b0f01060c02030a060203090f03040902130b040f290a11190f33090201 66
    0x42c009480381d15a207040c070f81c91121540205480d040030342060400001d11448043d4404800b5000746604011411b07041d070101c1c1080c840407019000d1500b80800d40710060710000320110720284074603450409403174510020312641492810508a48140800030607440c0b41000110701540000d0390400c4665500e540580c242c400c0304940700140061150304008450550000384001c0384a5826590781540341c2e91644100c131000a0241c8403102c80404000d168a041c002c910302504d8141410250880d6a5001030f036510088000100310035004804070f450140b0400a40d003c08503400141d039100c9494624a81c002e4120b8100858400000b00d000159200040c1c11202034411020816550300e00301031145550040b80000c2504002c0205541d00c6040c0616000d0b205143d501c1c1d032020410308860800d42d01d03100104515503154a0203074a00400200d541d01d607c4886a84100c140070b2107000548500f00941c0b170128202911007901c52800c0040c0d0f80759011000880c0700b600d980d280121070a49029 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 966734118 1250 966732868 966732887
    0x10207031509020402190509040624140904140615040e16020a020d0b100603050c0a110a020303030924150d0c0515070b0906040209040209130f21 64
    0x4120446412003008070181d1500241ea0070340c0041c101518050700c00032038410800c0c004c58140001500820450142e207414040c038001011070407144444444440d44800030200200307412814010b00c0749140348074400c6c0301c060707801036800140104008082030100030303da201c08030307105440760b404540c0e090300c90000c11090742c060300c00b81024110503507070310040e11051141c4d1242a20951060210350300050703a400f000f101c5010301c201169000c40c00d1040b130611681440380c01a0051505200802c215030b8451000d9034116005464403e404180316002c0324241a0349100c060b400d800300204020b010b14000a0710b80980c000780890810342800300c24510407a44042d10035203003050b410390741c0c01040d2600d1100d51100500640040c0304150b03403080001d4903a10300000031818040049840f10900014080c00e41d84058200c0203032980b4501503001807032854000300000c0c420760fa000e010a00c5003c5c0b0791003a141aa50108820304981000d040400000c07030600c0040075039940e0f0423159000948284880b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 966735368 1250 966734118 966734123
    0x30103050706110307060f02090f010c11190909050d1d01090b0a03020c060702011512230703140a110f09070e01141914070c2606150102070501020703 66
    0x41c0325641c1804000c80d294002d142c1d416600340310900650010807400d02c43c0e8000b54140c2e90340140d0321000c1300c05010000031549446030600c030700e003140e600200307091040303d07180202c0c00c41e00401480b100d540480c54145a640156000c0d43c50490345804000c0e0008002d030350500c00b40c5030266021740c0c41d42d10030100034501104a00080c0c4c0124200200141003016201c1054541400f500380f940b03660a407880c02408451200061791a044200c0d801c1d215094484080c180034804a8110706880d215044030722400d0480e44c84245d47c0b03101030000c1c0401400450003a66010054000c420402080c0356a1036030020000d60300039040407800060380c94100308401d01c80001038840030b9070b41c8c1c0c0c1d4402aa40c4003500c0043c5410b024200b0412409a8002c1c00101014854801d8440c03803600f03200401840013665107041c0d40c81e480208120300200300d4081d2944110380072507807800503104020f01d20b02503e0b955039000c64824072401040c00115160351688180c210130a0b07084034034096641004a07520321086c44007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 966736618 1250 966735368 966735373
    0x50108060a0f05130f0e160933030f14060c032e08030708120105030105090a060c0e04020c06060108090c011d060c0a1a0c0a051c0b03010204080102040501120203010305 74
    0x204180e0602c40805000f694540c0400560308581d03034119002d6075203826080c0c00c146c00480d0f8903500c1204840782c0c4005019941420410001c0110f60b40450380701c40b10100b9103c107100e9407494480f08040c06102701a50340950480344400d0945080043e03020010685407071806100c00042d024920f42094900c59180e0080b82041c140303d0098208102019081408800c503640d00041405070040005000c068031541d00169600300104240c1a0204113800040c03190341800144041c1a4000604410700ea400032000552045804026039518107840741094000b800400c0305001c0500c0414a184111400c0c3c846e807001d5a144101c1903250001003a020b404506c07234018421601d40300a464544821003c1d01d540c0c0740090380c2c10403e01d00492440211140700d41030b9003c2268912a00030140c004803201401818190041c00240581c040c91040b100110070784244038901c0d418580100c0401100a0001c43d40c45480306c038140e02070340c0140200c0c4c0c08140003044001c68820503201b107a0480360484003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 966737868 1250 966736618 966736649
    0x140304170c0d0b190216110d050a021009083a200a020301020309060702150601120b03160806071b050303070309080c0601080715051801110f060c0301050108060a 71
    0x1c2e0807400301c00151895840c00014842030115806910003484d0040881c43d01c000c2c00c0c49030303180c010910207c084440d40100b405602000000700e00149048007250b044429007031440740c0c41c02c121020301182c0d0041c5134034801c9043c1c0502550002480c98100c001300c00200041c8a203501240ba40442800c0412002519114948035800c0c1c0c0c44c504034002900788829111103502d99000603080e6002910110a690044c0060083c103d404100360241048d0740c0c032960200389000c10019001054103901000340310303102e07000c010743c90340d0921044602c400d00702180300ca0709485a0071540c0d01d070340c00c40742507001c14480124524011041c10488a220740d00c5001549169504a070032005000c0182c02142c5401c828032a40c0c850314010f2112034040c029100003000300c00d1034452490b130f600720712110b001d051110401c2641c00e880c14071180314071010001c1c200350740600309294403103162460321520074600d4002c24081c0802c03c3c0171800114101c1d8000d9890f605680c840f203003040420142807141111000b070520 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 966739118 1250 966737868 966737873
    0x150c03181b01030f0204080703060f0c0c030f0e0109030b040b1945080705010f0c0203091203161a062b0f0c090e01050c0c0d0806040207140304170c0d 66
    0x100700d036401511131003000d404d0540e6074000c07501d001425001246d403a43c448011030442d85181c4980018032070a03262168a04c0c06e0340d00d02030410b0034030b50840000c0040030a100300c91a4010515100110740c0003001440c0c918107814044005030080d0740010881110681401007a00d81d030240d404c803507400d4040c01840040e0030744920070008401003008001e018080710b5822000031500c1c0403071502e000d45460ba1f907500c081d1424030b027118045441e65021910b010030f0300540e1540001074035110f1105071604050101842d1103140346010f402144e00b00ca4004103881030402c090b008491410007100c400e803031601c0c4c4614081021000e0f659006036000552005075030192075103240c00000d100c2c0120720fa03a10880254440a14012060300b00b0140ca0f0384036111a140038000b40301c2c1c20781c0300000c030458609103140004001c1d15481700c8907019080110b01c00111344a543d440c1d0407180b4441d0700168101b0f4250481840c0d5407a80c015114811003881c400030307401e080003408551b0014084004180750b88160065 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 966740368 1250 966739118 966739121
    0x6070509130e0a24050112080714060a0f051015081506180f0f060d1e02130602120c0c01080c130f1a0408060408030405150c03181b0103 60
    0x1022508445502c40550301c04080c01807060035419405002c6000d51062008030001c2c040700f41040c0014124585001084002c8640110142071548641895a2004581000b40e410100744492240b2801540e040c002040e01c01d502c500022a942203003844503a0f18082a5001c020b0240329018400c0c07020200000c8140c402c104445d80030021040d601e50f012a0341010611642202d910b1606a032141c0402040758645003141602d400000ca90401050440401040c154000c00c03410585590f00c40c00d850b0045400185844600f101144c0c1c115112507035040d944840c0b048a01c070b1302c402341c015050a07071003004101080341d41c54001d070001080410304220044802ca04002d03c404911b076014070821100c91418021500101008014251140d040090b100101d480c242403505941c081007004001d510400714106510607000b0800c2034403036a0327500301142002440c0800804051648040003482c0c0012030141d0301074102070700800401c00c100688a0395894420075a0314940d500010040d81d298801e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 966741618 1250 966740368 966740389
    0x5030c0a0e19080102040e01080f1f0b040212061002151303110312011406040501021507030e062401050c0c130f0f021e040302100c0609080a170906070509 68
    0x140800304501c0d81d084402c84454456000004540d40000d0108103043e0001907180c00b40400c035028003200a81e07007600607a600c5c1c1e02c2c1d894154440e00c4401c96020011950b1126940c8000588103642e240a403000000c0c0c403042c125040d5100b206000951701d020361002415078200d001c01103200e4001c1d10b40c60354a000c24001d0150883c01c000c0c0c0343c0a0446461010f01c040c1102501c00700c44102c2e5941891421240024060113881c040c4105100407c016a80000e9003800c490004a000300035486a074002c070013070800e031000d0304c1c000d04c290030500c41c01d00214060070744015110300c040240e25110000447d803038400c01112500c6580000c1d0180180c0c03900c0c002184052459980c0081e80c0078101070001c054404441000c0c1107070317901052a50382e1140700071050340c0002650920318901421903000540da940d81c0085d0208101c081c0c2502002c10029a0281d0003107a003086c949500c03001c22803801004d5500c481d459004c04d0b001034000c1103112000080c41406131000d500c0b4035082820b84814441142c00e13 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 966742868 1250 966741618 966741647
    0x903031b0304020303070629270a0b0d140105010f0312030e0f010e0a03080a0c17150d0605180109110111030409060b04080d08070503061005130902090a0605030c0a 72
    0x4200506e4000030312a2040c100c80b00b00305042e40602032040c1007840c4c140c40710440e9980c055002541d1520352006842c1100d0349116071880c0101003500c404a06d0002040b40b0700c0c0c0036070410111300100d028009040203a0008100180090080380e80b200000311003001c1d1448014400f181a1041b8a4100d0203600240307003050740101140c2d14451940034041c01d41d9032070300c01c00b10700b0f03086869054245580070410340d44c01031404030240481000030340028042c0e890481c604802007440c4001ca50034030428402c4400c420401803580c5500f60980c1448c2004107400e03980001d60f500b80442c03440354090306010304421250803283c61403041d0000c07401500c0c5012840d40c0c0150074002004080b404c5840c5106003800b90401800d0740d91900d0400d4502803a06024a94803014007402000300100190b0040407203070711840c1a140f00501624011080d90750380a030010740d4081e04401207010440f0302d02ca9002c0c01403650207d480c15505a61442e00b03603094801034403481e0092001300303d018003079401014a031001d81d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 966744118 1250 966742868 966742873
    0x3032e05010c11040f0203150f030d0e0102030415030b0f0d0210180f0803043f020a080f012f030a180b0f06011d011b05030408120d050903031b03040203 67
    0x43d46000203086840c0c450418008682c0030003400307074042c650012a403030808140d95105500301d2010009550301144c0b0350311010800e4001c03454015034800c1c41510014030000c140d840021901140c081c003d0515038540074000e402e0b0003482c007c1c5140881c50050b1264001d4034080c0000080342e800c0b0341c00e08c400c4152600b034090340040010b1400c1d03420104001010803001030750700c4a04040200e07106211501903091041d500305284040c60b0044048032150700d8008554020640c414408507081001e1988070352064058000614410403064014050018031000d14104881d00751450740c600c0c40c0070685150364941c0c140001081c10b0341c5940f00e49042d407a50446440d010125995001c0c54041c200d5016611044045c240511540c01c460079501c1c14081c10300c1c201c0c14250321b10000b050340c48102403156055a01640c0ca00910000f4012900506a04020b5a0a80300e624904691a41c08a2140d0301c0b210b140000117045440003100b600d001d8100d500801001d20415000c0c0f101e0303070b000580306a0b85030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 966745368 1250 966744118 966744143
    0xc0901120318050a030507030213090210050c1921050a0e0f03070504021903060819022e0908071a0f07031e090504050708010e06060a110a0503032e05010c 68
    0x783d881c1c100b02c0c4003c500c944003c1081904509c1404000b0300c40e81912142d0608200c4004010b98402907a20071240d01c3d80380c400e495600100e0b010f1301c2d02040822030006404880000020310008040c0c1641461203101c1c07002c0e00402c2094116040d203d843d11000016000d5140740382c20b464507499a401e454002001c465410740c4400009040303911000c0014140350881038807010064040c080d04c0c008241d0780014012107044070801a10101c0203120003885055404070919404500d50304c05101c00c0c4044d004500090700c4904054a9000c0900500d42c8034030030004c0024206061080700b41c0038142203000c1c541007164018100d009500032203021003d100581c001020804403c4a41c090706105564800b404c030b03803824050000722040504050100080200103003d084903009166400c10410350b0a9541c0f1084040e003114100ac0a0f0706200990043d215100280840080510b0196048040a01203034003040806402ca0000f902610f580c40748030305080100d90b004203c6020018021010004d44 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 966746618 1250 966745368 966745379
    0x606240c0328020a020913020d0c091e05040c0302010f140c060a0b0319030e060c060c0306030d08010303080c0f0f03090f070501020102270126090c0901120318 70
    0x1940c2182d881a20900060080c200e040d00c280c500000700314a0a002034030a5503d03a40104003045801424606980365488030042107403106031392480c084d03801455440c0c04c552522445006084418100c004d101c00c8112a501005410712070180204ea100c195000902c2c40d603030055070800c1022041c0424403100c4110b869449a041004243c00c40c5828042c2445160503400a0110741300c40340304500981c08a1044003025409a499421003034040c00c000d55101076040008002c0e1060940401c0140115424405e107418100c010358002e0f02c4c00c609880c03100c3c0001004031441e45003444090005016030002c9411a03200800405611501001052924018400402c00b69001307940b03094042d800b0031200e0801410900210000d040b091000f94070340414859210b40c00e800ba008085c0300404d08010b155520785c0a648404141184415001a54038000061030601c1c402100c010010f8082d0403254070b41c0d0301d07041407020f050700d04542c0454840c2c086510b04072400707030007408070010700c02c0814800711701c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 966747868 1250 966746618 966746623
    0x4120203070b090c09010b030f0a11040801020a080f0603030a0203040e04030306031a0717151e150403050105090c10053a1803090b210c040303110606240c 68
    0xb00e103c2d500010110030340282d06103c0ca240c4140d00c507000303091060040c003410007088641c05070805148900450704001d0b08410f112207116980c003916441d0b10000f152200c182e08030404a10801a2102800142ea9818240340e140e10901000300c0050300704110a100c5003401c454141d4000d8000d1500140e0241c1700d070356040c91482c41e02c41c5280c81d110807a040050995000340b0415450500b1107034061142842101c020800b150400c055204e102e00895a5801e081c2c42075030032020460091130b124402058000b4400325030300a00050301c140d420400002d140d41c0700001d0039600d48a010b0052903c0c1c00c04c80354115181e0b0001d046510300542c042d038800014911a5542c606010860518400101e60a07026070089807000f0f0922644505604040380109420580034400c60b8081810940c1d5611030a00e40e030001c03681c032031181381300140b52000e0241c0f01a000300908203907486a19403a440b01550701080e0742c0c800048400a41c400050144200c01240d00c5508800f40c61038650368a0501e2403030401c090 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 966749118 1250 966747868 966747871
    0xc0504031509051e0c030c010e0d030c120504050307061b021e1f090e0903092106040809182e08120310240f12230c1204120203070b 58
    0x26204010303c903441c80b10300c000c2c8017410340a0030032070043c0f4403ca40c20b0000b83c605a44007001138429030200c5400002c0c903010300c1440c45029406003002201c4410020060042c1d005405264003900c02d501c0007143d001d0003112880c1d4900b8843c1e40a040c81c0d0015400c1041109284100c40030810036081403000b591200e0b0405075402040130003403401c8402041e0300800611040d44084064081d000c144003603e0408022104180c00070b88030780c0070103100051480480040f00707400d050140304035030400c41400603032006046901800c03199070b651140f04044203a4104400c3e91811020702d04482c4c0b02d1150889080c10704842103901c5081c01005980b521254100b6101d20729101030f4090020403c0b18a03070180110782c0150015454400c800d0344540442c11828040b440541c0600ca104005501c8c2c0c14007075114640100c0703400209011100e03d503003d0325001d459030700d01c010071651a0000700340c0f1418a030302900d480c1a0000400041a83c854440b10081500e19480700f00391b0204001c031002003212883d009 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 966750368 1250 966749118 966749143
    0x71a0f0a0305010302131a0409110a06020607020d080105100f030b03030a08090115030b070507051e01020d0c02071a03130b10030b0a02070c1e0506190e040c050403150905 75
    0xd02c0d6266005011068240b42c10755034030246000d660f501501c01114060ba4280380a50300015401050f15011040c1e9190490b05940301010b5000003c0c40340d8002540c3c1e1007030316917900344c40c0b018000302c1003030315000c20a01a0030780c8048100354209205110b0f18044c01c0c140c44518010407808001c1c40800d00395440f010361a000602c0030810003030b003880c2c01d000e00c1c24003041460f207800b40c141c9103407240304200201901c03040801200080c1c000c00d21208100c4d00d809222030108000680814044590003503000615151690781440390680a02d4004201032045445c458030404448011120310061b84d4001005040781001d0301d01090041500d403a41c8500c2078805d15401d44440b425418920074142000341780f61015070042050400082c0440c00074000c82c1c24603406104001b080390891040c901913074002c90f8004d03c010030110304140e4582c000030720301c04098503000125600030080c0003d81c2c24a44a603408154100300c1080024040c0c0f5095221000d41000006c041115a440f50b00b441b002c10000d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 966751618 1250 966750368 966750371
    0x120c02070503150c0a0c0c0306020f0a03140402030d0f03110301170f07060909050403170702060a060501140f03060d082206030533030625020d02071a0f0a03 69
    0x24007450500b0482000002d4030700300310f11a94600000c528603148070320310403a02003042050244080098055842001e103501c000107544812044401100a801610b04031703001906220306a0419038a69007590b005a402501616851000000c01d40d200100040d42908260781c0d010ac80918026000103140030b4111942192441850b6406030752a08250b00d1010301d6940200c502040006d8001400604840031100040355039038490406480e070001115001203e52001400c0210155011035410f2048000f840d04000d2284c40b2801154610801c020b80d040b440800c001c190010412031000d180d00280062400190a006942d408059005007201c0e180000ca8600705070f200d032600001d01809416203141c00c0046180c0340c0c04d601005103200540040203100201d0210003041d0001c201c8188440240c115041810300c50607251200324a40140d8801c446e03075000341d401d04c52011401500d00c1c10160b000b421500c0c00c1c030100c2da2507981e040e034058861420030400c05410605500c041c00c1c1c0364455860 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 966752868 1250 966751618 966751633
    0x51903020102010e1b130905011505100e03120313050a030207091a010c061a06040806060a08010e0d11071d090c12070920161509120c03120c02 63
    0x607081d980910484e034403903080241101c0300b1010095050a80741000ca620a001802c83c0028000401081d076001d0316950900441d8201819200142e40840b0002d9072282da50b0390000c0005c540a65075482e80d240d06421500302c80c10460168000f07140c00000d41c0030224250010b07035680074901034803118201e016802c82070b0100300d103401c548a00107080000324521030450804000080100c5441c06000307082c0d607070f2200c514266504a4038095100080582440d0f600c940301c9840c0c07903641c13000702d0354a84500c84d8000041594241070040415021107900207000328065140c00b942d540c0c800c943e181d80648107188000403101110f42c1c80b0000051400c003620500c0c10150b446e203080c4004a40c0050146148455651040e50f0000314802180c2086034005134005804035030048243c880033005183c0d0030042a5800e0000c1c00c2c0341020159840780102d0300f0303042c0d00140000e040d10b0fa50700000c0c0c0b90034127000c68581b52902800e01c68148501c6454220b244000d00c0406404485c0c85260440c010780c4980d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 966754118 1250 966752868 966752873
    0x12090312130c1e0e042d020901210b15152109120901050c012d0b0d061a0409030801050102121216050712021516080105010e0604051903 60
    0x200c1110243c1031010f030072000c80500c2c0c14100c07030b00c03000c0c1e1240000000e00c10340010140410032440070204600c22500c40d8903e00c1d4100800b041041ba014103074030580119000081d001142c40c00c80b030a241041002c01c6002d84140c6403003401c044010090102d00c05422007090701c0b561703543d04a00c45d0f4000b915000d5202c4c2c0714450343c44406461304952001150249090026403034000503402d02e210004001e1581e03501a4200481c0c6034003076840885150741c20500c40b44540e02c000c3e502000c8030910418099144400c4195200a640b10096030541203004101c0d0b08000c540107400000c0b00d501703c100341c1c804da00980000705003287d413940015000070700200700600003503034140b00720800381035500c504505143c3d0364402c4168494000c1c1450528501189840b0101405081070300c1c041500240310000802401002a40790b1010342d5915480c02c081c1c90000700d41800b480c1000038112000d0b43d845150768280300055505c04500b07055558071441c244000591a80c07140d6070550703920004605d49002c1803461 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 966755368 1250 966754118 966754133
    0x60703050a0c050a0e061b15010e091c05030a0b09252c120601080f0616021506040615031a040203040218071218021201020f1209031213 60
    0x24148810040c040204e410140e41c82050f0200451044440c0c030340c0c500032030030401010102d4a950b18a03500480c91000c0702d40500c100c18034104e0711109a125040d5440204d4251680e800c04003210307140c071440b015200e48520810240d03038004044c420015141d00041c00040ba1488220359a083c214070f89000304408031a82e800c2c04801c0f0900e0b0516560125514000c0201e40600b1540e0440c01031803030000e9006d695554140201c0d201044042c0d4080b03507140c018607605d071944c20a500000740b01300780100d689420340b042c0c03020300b0108a03405441031400c0d03070500900d46034005e4140c1c1d5001d40c6032403002c80c075110a000032034804601c613140001d41171100c802d0100b0800c16455014404c610510030040540c6407100d4240f000e003000000c2c8003080d641c5c41e1054440604403034030707480c0c00d51411802280003986410403003042030003212000032080700d41c1d045500341e100781c44004c0300c082814002400a01c0315800b101c0d4104121801390b90078a4001000e441c1e0710b00e82110b1707030194801c01030390040511024 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 966756618 1250 966755368 966755381
    0x40c09050c07030320090904050106030609050f010608030f07060f06030503040621150521010f05040b13030207060f020a140303180a0507050d050f1c0306091401050402090a0305060703050a 83
    0xe017407002400030b83c9524107010394002d80e08014041c0c40c03a90001400c004c0f00307602c050080e40c1d001d0001c2080c40580c0c01c100744c2d50300190751020850341c0303014800b00d0708140001c03c0e110364845503000c00381b80400315500c00b00508000000705d0007e070303101c12010000580600250019041d144e0305d4040b101e83c030b00401c5000c1c0c145d803010300704041d00c3c000c0309083c0c201c17043d600102950301c103803403000302410707042114031406400103012240ca5107040545034880500e42c1000d4001c500902d81c0ea44d0507103658808039490400114000c015a01c401410440d15000d00105a204000303070041e03400200480d222500c0d0311910210403801604002708014504a080d02c00c3d0b0251301c504c2c0c1c000c01e0b80c956039545282c1e54042500a2a110b808409844410417904200305081801d42e02d0503980d00c0c0e0803030701885001d070001030880b0002c2414408085041c078480c0c49034484450340d5140407003d60f443d0006100081d03000b003090b203030040d032a036002202151040003224060412660001a9440c3c080c0d0b210382120314 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 966757868 1250 966756618 966756641
    0xd1e1a0a080d230310030c080d090509100302090a06090e0316031d040903030c020d02030c070509060d0c290913110c0106090f06051c0605040c09050c070303 69
    0x290801806a00c0000844210038080c606003e01c40740040c040e1216640c01012075030140d1403002080040d4040031500d80c008981c8201c03e40b800c016261480da40e200c800c001c40c01c6001030b03403103002041185045000b15801908101c2414601900c980100b150311400329052100c0360340702c0501704003103240b038891184141d2a44000e5800e150890000c4504d07282111009010080028900f0424511007420f99a0a000041081120782c1e40c51038040c0140c510315000f400540590807000e01045c2c00802100e004460810140c45442c0c02c0c1300c100038000c0700152410f41c200d080088140c00054903000804040c102c10140c01903221460701c01800b49102c402102c0e03101030810b10800d0f029444410515450528034000480e034031446c46840b444038090b00034422441c0d030800e440060101196400048100b403860424000740744c840041c0300c03c1039820503510615008030462000807680340e90205030460712614074001002d075141b104006852080c0d5281060b46400594041095090301c6003454021 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 966759118 1250 966757868 966757879
    0x1140d06200316050f0409110d061403100b060d0207050a06150f060309080909040609020316050906030705030a021e09190f0c05031b040b0d02030906010b03010302060a050d1e1a 78
    0x444440305015001b103110300240251034801d50307100e03052000c0541d81220f44094042021640c1c89004c00c0350b912103815828000d0040d1400c3d603011f240a40542c80e06234070b020380068606075512402d10000d611421081d10035004503020170f400a1111301410140202c0490401600c500740b4022a000c2d0075540e1003030040c14544030039600003c076080140c03401f20004a03504580d1b0303652420010090210310800035414014103181c000c7c0c4018107001082aa9416106000e0740e41c1da40c1c0c2419581d6956001f55545640010800c80052420388291554000389542040c240040c02d4040351521200340c1c0d44e0103e001c0041c0d0100500582d81c4103000b82a9030105007842142003110000e46244405807a030601043c3d030303280d403180003100c14084600070148026080d036100028a1554004d40041d191030741d080c002e00c00000307941d003100d80c181c9050342d4004143c4c900d00084d24074151150b510110303400400d20780364080b1000c2034100d245481100c43c000200891802c5040170501d9845032464036403071240 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 966760368 1250 966759118 966759127
    0x307080c03040b0610020f0d110c0103060f030206032208030708090a020a03030e0111070801060618060207090f0b040c0201140601030e0a0b072f120301140d0620031605 74
    0x2a9010043d5030881c00030350300070210051854049081c980702110b01d102c06e00c00c8202d1f001ca1681e2255000041070b2008054910440c18140114161005486182c031050078600c01400035240040040d80c00001450954503c03041050b4000b1030440d1402c1c0a032078509001c0200517060f60040c03420b550088140d006000b51078029400281500d805000147c104111519400c104c1c0e401403014003c910403070422200206c2c0d4844220340a04681c0c014170001a800fa101c0070f001062212020f0b0507140701d500600031890510005a00515440260347c00706078403041c11101c181c446100d11190f05840b82d001050703a0b04055a032659008001d041c00c0d0416142480910b00f400780403500d4007215604c840e1150058803861000c07180c1040c503500540640040001c120301129241ca0440c0e0790610480640d038100c4802040564980024810700d800480156003011b0103141c02a030703890856100c1e60340051030043c0440c0c20119803914151410940e00e0000c03d00520711000e08182c1402ea405141c16444c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 966761618 1250 966760368 966760373
    0x90d050309041d15090c03070311210d0e01020106030803090a0b060f0d0305070c0e07050406020106060810060e01030e030d02041406030114090711120421030f05070f080403080307080c0304 83
    0x214600965a0300e1203030504008038105e0441403040d03a01a4900030111030700d05840742400e1080c3d0541c052020321400300c1c103e0030b002004800d000c22450701308510280041340d0205009450b80740e25024443c1c115580c4410100c006160040954002c40a400040000325100d01d0b24803030b45040031380742e42d205000c1c0d040740c410b06903900d44007070703903400e505140407902c03070080d07103015407406455400c00c0d25080300100800460740d42c0540034000300c0d4020b5000f4051603076a540242d495070400d5a07800a880200c1005011a6000b501c20382140b0070b06140000741000d40010b2141113402c0420200911071b00020104824422260b550b1409201102d0041c51035142c683c051a45c0002402c4540c000c1002a001030310050260002e01d0302245100141e0b00340007251441c103002540076009001050740201202c44010b50081403113015640d15444148003501c0c05041601c158200100c2100c0070740c0007801380c03c0000c141e00081e000541c07141c40301a07101c0c2000c102c054143c0d48002c0c82c0e9462500d040c800c0201 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 966762868 1250 966761618 966761623
    0xb100c02100e0112050406090510020315060913050108030a02010f0212070c080d0614090f0915150d050a022403060607060b030d0804231011090d050309041d 69
    0x40156040c20620b40414903000161180d0900d844228071052034442000180902c580040d03000c140b08000351101d03030391341c1260700c02280400d480c0a1b01d400c0710b0001e14851420070b0001000708c64002045486104826240f80040c0e0b94244c00030714031600040f031401d8902e80c090041e200040c080034025414040c40d0040c0c2010000b00804040400a0902c41041448410000c45461900c1b050040c02400d80341d500d45130480544a4600f40a03c21500c000341c00b001c48005841d0203442504003411014124860484c5207010150000c1c00388600c86a11040ba65a0700b0304641c40c0510076005403a049410703004105503d0200b0f5020303011800048242e103801d030920001c4a51100c8110750786030721046a400e1200c014181350680f2a01441481c0c18400c0c020b03080441c040c4154810461500349014070141e01c0d09440110f86072000541c010340340c2d216803800b15001a0810003000d502582040c40400c002504d9a10150b400da809030000508444617003010f005605084520544212050000110f0742342e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 966764118 1250 966762868 966762889
    0x309050a0b120619080d050306150301080a0b06011b030818071a1c020a0507020f0f130f14040b041218030803060d020a090b040b1503011505040e07030b100c02 70
    0x44c85180d60004c801440509601180050809402226880514100054255441a100c031849421194040c03107952440340101da06036550340c009000c2a1001e0380d00d202c1d91003c0580068140100700501000d406182104511114041d40e1101d41608048603039612403500e0b2071010407150400081401070f007542a8404c054078403002d0b1840e41c0c811407010701d01000741c1141400c01484c0c0c00054814400f5910001502c4001d0080340e400303107800c90784010003140454044410741c00601c80000d00071007441c19800f80018882517100403504242400d00107140c141c084400701c5d5503071308501c188000c0c030902c910b0491804486081c001c00403404c0c900300780100602884020100c200c0040059100e89540035a00c04450f07002e4102140d2648502211000e0012059554041d500d0a608655149000202616003003007881d011483d6900740340c40031006000054001003842001c0000044038003034002030710302c12015560001000302c0c0390003c000000303005610b12001c10000c011303000056039411800c034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 966765368 1250 966764118 966764131
    0x1204090b0607050703024b2d04020910030912020712081b0708010605101b060507090806040809091f142103030103111c0b04080d02070309050a0b12 65
    0x84600050311f003c0c0e080c1e01d40f0405009036414001898040315156000c9107000600b14a01091f8013280304400d014003d000c001c001303c0105110702c28080d8040c00802203240c010300c01350002d0724081040c000724801c20400901c61002990720a42c5109001c2c0c01f8040704022202031024001451601041d14410050380e08090040d841c0014588484959003414104500038041680c1c42c280c1e583d100d6078000c20032031241a004142240060200902c50012100c2c6091804060300b01a07203175850711030081c0b80c014511070038804101c60200383c2447c100501c0e841075100b2500c2e980c0c0c0307403143e80501c916050301404806c4e52072018400ca400d1710800303c81d031500303680b64090f1072500d90200f00d00007684288204183c03900000554003001c8002c038007000075410380e80a880c400d02855066007c0c04158a0000c00590100242032094000030329a5445903400501902c0040d090414015400303007264003280301100411825002040541041c9a010b801441d0000c3c0e01424941120500c0c00d030a8002000b8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 966766618 1250 966765368 966765379
    0xe1503031204020a170a06110d091407080723010c08030109090c0608130204051f030b040614010b0d02030c040504060806040b010801050c0a1133060a060903020f01111204090b060705070302 83
    0x60b08e10780d51f00d003036402408180100340542540c5050114a0b070581403000d81c1a40501d884c045007a50001900c3c0d02180c08003207011400c11020341c0c8805010144513001410003002d040c0d28000700320004095406006080d400243c0284245024080030b40660b0080d020b00001c50100a80c030441014004045501900d020071240e46040303901d61030314400c0c0790b440c400c000d244001000b80f101707040d50701d44128424201080206036803280b940601000340710704441c10404201044100860350007440d00420240c08076401d040d10384000030300344c80180d0843c100c2d03944071130200400e0040ca00d0620340104454402007003a03080049400c191303845000280000e0100c003800c0c2100c010700422042c1e140781e0742501c1c0621303400e82e102c2c500c0000c0401003120190807003640300442d005150440460048601c2c50b01c1740d1811916560a0110000804440030b040c0315464000c1055900e06114025401c200d07031918660b52804c160b940001c48607107910640c02040c05000e00b0300080c400151200a89404585 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 966767868 1250 966766618 966766631
    0xc120c310e041a01090213080c0a0b0c0c060403060c0f08040b06040b1f030203061915030e010f09050708012f1b010c021b030a0c0e1503031204020a170a06 68
    0x80514810180b0f10101507004192000062850340b1070f405000013000300100030fa07a860f07944043d142d68072240c0310303080d92000e1418003c1000d5011a030080580101010075140035128502c00105160004d51046e41d0745030300c0b9031820903e2070744045c605c001c0c1d14113800c148801e82171075100c0e194070714001007090340500da07a44490b040c140d64814540e950888450101003100401d035500402070f40040c0e48040c0290700c400400b000103200c031643c650946462521f09444100840400c0313015112000b210030f0595079903c03800125000780c0c041c00c0e00d2075000348011f060581c64109002d08480c451800c8070782d0080e03540bc103150070321402c41039011142480010203031a52107440d0a281103510505040b1015840c00c00064059500401e01002c203c0e40400003000e4403007998103044d26011828002082402d60001c1840482003128060750006024045882e05035001c00110749154042d011003130f9a1030000c0208411407510b64222801340c881c40000b41d4841c412100c10594515200f68020b00141d107892 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 966769118 1250 966767868 966767873
    0x11030a0806130f050a060906050a0806040201032013060e0a08030f0333040c08060102030316050f18100309020a15140d050a0b01110a0b0c120c310e04 66
    0x100f1040640b86698810041418804402ea00810072486600030050514000040c3c41ca00031b1072003070441c0c040d9000740103075a8442c0c1c01100103040d10450007000745126058500c580401a01404440c1d0000900b40846800c0101c0035041d510007030000ea11451030a40b06100d600f402005640d0a4a0380c80c3c1c80d90307225102c44140140f008016a10404690107011070520040104491000350103010344041009900d900012a007468044540340d001da4010800f1130b1f00d110139170b801a001e4800c246040c5042080140c00c040036980807000c05030078021414054281d501c1d0052383c0710191203c034182000014456130205000719400c2c89144101c10103d88011141806100f1114104250683d440e555090710003910004100542c2c107004d0161406250340512350181040c2c060040e040b4004003000001960342c0125000000d0203098140810f00500701c1540311200414000e0040320f488684030201e5030041c07010101404004800e01c501c8041d01102001ca4140740b105880c80e0224800c00e83e552030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 966770368 1250 966769118 966769121
    0xa06030f0f0519060e010b0405060a020c060c01060501181d070903051009030e0f1507081204061b031104060503150907080615090f0603100806040b040311030a080613 73
    0x500401c0388490412081014028460f602c41e019035404080400606844415400c48070314240144091104d08000c180468035114018100b000d041d803046902040c00c50000c83c0440e0040720118a8603911403034144000e6801400030002c1c5c1400c0301d5404d000910b000320400b2214584c441044840020401040070288107045140140d500a1b045031800d114000720f0304020414402c0640c002007250303241c407400e450051150303a0a504018451800d90030003601d11415980701c94003c54403a00200660591803500318031a600c074a0066000142030074094101c0384000581504060405141051504a011703889c030a031010703500b05281840c0c9a0340c1c0d41282c214041c0703450200c9540401d0450030044881d0340426038620506040c0d4100003554802903100b511409038032800c80d40014160029282400e04002540c1d1154903442d200e040150740302c480a0504105480585111540108000505400248000300290ba9000852802c000c010000302804c03c0901100e20a05030408050f411000c0ca = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 966771618 1250 966770368 966770381
    0xf020313062307021e060709030204020a1205010b1209030f0a0810050414010f15080c0702180403050c0114060d02010e060409140103110d0803040303022104050114010807050a06030f 80
    0x2e000852030800890280d6500401501101e44502030b0781503c0e08024003080c00d40c0621071035150900c1450859003000040d4210500345c0007080358583c400c08141406000d254002c0040c142602d41d41e0700005440070800314001c05402041c3e10801c8583c000400b100c080b5a40f82c40e8a02c1c4c4690395446414040510003607561000b5446800c00d2003525004c0042e043c0107048400700754501e1601a0b071800c0031080013510741e00140110300c01c200025801d41044004002e42440100121070f100b4000b00d404440d10b0003540d003034000407000704803031a4a907024402c2c10982d031003601c00804240b0703094000078140540504001c1c100100b0034038000b41502c0b80003d44024110000062005410b01d0501140d000024407050360303924450041143e450900001c5d0300d5a150300811054519034940d1030540c045d40c03250700f0040201d1940400651502c0700004080d028500c06c0c1c00110380c801000904841101042c1c0007205580c01c104010001b50341c030843c960781115003e00740400c0c1c01c080001424000d100707 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 966772868 1250 966771618 966771671
    0x402131e030f062c1e060c07110a03050d08070909020306090a0b01030e06131106040e061c06022a0c0a1203030e0604110907020111071709040f0b03010f02031306 71
    0x3613200c0b100380003054090700a02440c01d11a8000006408243d82e10300586000c854207a040051401080d2010001800b0760b0019180ca80e02e0740daa9034401d450084480146000685228140880755600c80050402800803031002d60840c00e1407000a00021030107000e09074100c0e41c070808060543d0194122030400300e01403003500d0392480e0401c484404262508011280185190b10102c514a081810384050311320741c10030314400341d07102c07010b00054080c0304c1400490461101001000070b041070006069100c3c1c103001070084054010f80e05440103070002d2000701560072200b0028180d440c0c07200c144040b02c414902e0b40802d0040e03418250010903281c45004007038003035001004207102c6401c403104d900500a9075100401da03200c5008900700d07000218900c2000b501006102e012801100f11207140000450440749029103500c001811a100c1c1c0500d007150300d0303c2e05d01c0802245002e01c2050040c1c190b0800561070b5190106001d030f214052032318003c00480e921003035041c810b410500e0502c00c40d103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 966774118 1250 966772868 966772931
    0x50102030f31150c0b130212010204140f040c14030709030c0308091005031b0702210c0f040c09051c0b07270302060a0f05090402131e030f06 62
    0x410000c0c00d44161502e41c01400f407401100c1c42c106034039510420a40e005a500503032100825199015010300181c11180c069901c0b804003421000c0c054402c0c8018402005a03c00064449d00301c6404d004d201e0404c000404d02c564070780307245c100c1031540240106003050584024079907207035038640301600c04040c03541004e011003da4050100800a08230020604031600311000030006d0003c4100721514401107581058160076000d030f0407800403064005e00003c0d40700901c400341e07000301d00e6640c00380c00d00072910190040d4002220701e44c4d9810030340c0c0c035464414020b43d0107004d0b5000144001d00711751000c0c89103d002c0e071003400f035840040c000c124000e460103500c001401194202a240100305d502e50512411103a0840e1410500b1241324145020441e40d01400383c6041c20743e418400d440001950700081d0503c0020040c0300d1850762544024054200e207000c0c000446401d1035010150f02c0340c40240313000c0130b16901c1014004120140c00240d907940d80800003083c80c0246222500342c007180b0903200344600 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 966775368 1250 966774118 966774187
    0x12021611130207080403030c11061612092102061905070b0a090209010e0a0e0118170a05070f0f0f0f0203060f01050609010e1809011b0306050102030f 66
    0x11488501030a4410101c6105100e40c120254a500303d103d8441c00401581c2c04000402c00070340105560110640600c0d4110415519280401c040740c0c0403d682c800040540000c2408010703180021a1554000e85054843c10341010244040241c0315080c54070f02561180340b00c400c65440d00202d070b074a6280841c0c074100c501074013a00500780b50862003040b0307070404091001580106c081c1c41a03005d5290024107055550b4602201c10f091800003900b00700429407031f02002c040c42c5400340103190542c4101c1e01400046843c5d4249414104400d200d01c525512040010700d8813030341c1c084295848150040e1061070320320790368906290302c840000341c02081e501400e0854400d020711403207011003850080d804c1d02c0059036004111030524000340a0107502ca4801e0048080651050008006244000e80407460b50300d100d8400d8000400d0407a106101a0f458840c4110300301403041d05240c205001d0b0a042c48424140b0740041d44a020305240d1140c41300000c110014452107404105e04004a8800042400d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 966776618 1250 966775368 966775373
    0x4090c150905090c12070509040207170a0f05032e0314070f060804150f111209010c11120a141902070b13261e1203060d03120216 57
    0x2001d03210766032142c0d81e150b000403411544042110460075a000b100d034125030312801c0c1501d082d0481500c07150000d47c03c0c0200000a40c00781480110344c0c4440080d1510794102030030040204076400001002c101060003400304800c40112030100c0b85040000391040a110380f58015810842a4005000039181e0360f60003903c1c01c404600f4400741c400984c000641107880c2d11342034a5070701090310000c020700d0254000c0e00d0740401c948d000d0452480c60380741c04035403503140c84500341e07540c0c000311003a0a0012800051241c852400d120300d03040040c42e07040c040321042000280e02d03115032104442031103441001400079621441443ca109503040d02c20000c54554034000e012048141c1500102000352045503404900002d11000395a481540300507107115450410b80c090316a00d2038101c407401804c544503d008617020007071007404940e003041d44074010119400c4c0c003038a1502e4a01001a04861410014420301e038607030050844000d0f030141000240032500b405450000c1c4180300782c0d10013101004039100c08 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 966777868 1250 966776618 966776627
    0x3080f070c0f0501020705040e0606010806040f060306140105101b050304030f14070b1c0f0b2218030e011b0b16020105061504030b0403090e0f06210c04090c15 70
    0x140c1c3c80070f0b0f0031502840c3d21036041c402122130075602902503621200028210b5841000440d0384070030b014202290100162000005456040e0004c40d0165152404014003010304092035006100403540130015078900304c000340c03503907448200c0100c950034060b008034140700c1d040003250011913100074002d0120607a802c00a614528404100312180280b15000406400c42000c0c2c801c8262150100002c94490b40d403004003c00c6007100c0780c00015146c90b40661165110366100d004440d1820f020b0386030408001c807410407129415902c031802000c0300841800b184d0f200d10006420a03080c205100700075400880400c8500041000910811400040000c0485000002e0010f451290028851a200c64041025000c0d03c40f03094840210184400c0010511030000c4c0c3c2c0c1c10501034200240b0054a400d580c056a80c41111240c0880d041c5d40207109250030700c1120a20180308004403070510391804002191200156007400380720310349031502c10013407010160307a002c000c040013030318005c541044020280 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 966779118 1250 966777868 966777899
    0xa091805043e0d050601170d0201020f090f040e0a060c0f02060f04030c2105120a09020901030b181f05090a080a080c04080d02070905070309050703080f070c 69
    0x40746200d082c0c144201d151150314002810a8108241c1120640031200796603061202040040d031000740c0c81400004a030301449168007a01c1000280e05000202d0b007042032415000f00c0300d91086a00c10001100303400d00c0340e030a840f580c03601110001100c0b0ba014001601a02d45445495414042c04140c2c6007000507586c003000d04a580d170388a64000407501c02c03050b030311005c04940062255138010300080c0000d11070303040720341800e200303400c80291281540c21864554002c255100c1c0421000110032803031800031000076920034102941480560842da000c5003040406120081802e084031000c40d0041c551840041c045940c0c01e411184d8101c2d071111403203012540c4242c0c81800d030b4644000b06000c0007021501d19110742c0c000118070324152400d20304603803001c00240502c00000b02807201051004080c09903c10204150340104400c908101c181070844002414480515107009803030070008001007040d8040300c0d08010529152500c100c40b07020340344a1801c3c01440c1d64806213000c191074442049c040b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 966780368 1250 966779118 966779123
    0x101e0507140c040e0106030c150302040f1404110301061209080c12030a1b0206131a1602010b0907020a0f020f060c150a0902181803030702070503060a11040b0a09180504 74
    0x14000c070f0100342e503045c0c2216040e00015000b030360310700401d00440000c440644070540003450010b00e490f030390b81002d0400e18101c0d0400c0100300b180685000c0d05203450700614000c00b00680c40c240c559490454050300040f01c1e0b4510741c540303d440b524000b0612104900355078011815a043c0caa41540ba91038079607541d401201c110541030715001006501285583c031441cac45990340c0c1c0080820381c450308504c00d0b10100d141e00445075585607030f01000c6034002070104103004030307117900034441d10240410f40a8203503501607038214000c0da0520108218950300160b800c3c8038a800c014244807a18950001c030300100c400d00707021908240d00050b1641240300008072044c00d04581c08401150b5250388854500b501c800c5080a5403002c03581c00c000c04010b1154440380e0304884010301c0340e54000d40742d00d401d41c21034008640500158201c0301c010085420140102c0c0e41c030522842007044440104003840c13805000c0c0f401001d42444011801c03007106030007400034202808604420041e83c444040980014100c1210308 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 966781618 1250 966780368 966780371
    0x927070f1205010e060108061315020d02070b070c0302030913060f15020d03050c03060f0607021519090302090f0903070507030c060f05180f01020c060c1b101e0507140c04 75
    0x4c6010600206595060316100806044145c44e40f840c410035292010101380c401c50160b140c02a120343c9140b0040078121815580540c8419850812100c200d5004144c0800d0258031004180000d0b80441110ba42c138a04503060b07421118a100c1c483d0080c03d01d600000500b00000c900840c0c4084510f152172001e0b0705560071a074104911071800c07030646d001a85c40c12140382003400840c901e0b141110180c409240c01902490500450707400160400c0c0880901b84c1d4885000074040c1c0d05060b002030084d150849900744003164618540c042902d01200505108441c0083e002080d103060091040b200c071281c00c0302c11608a9a1a03080a0400502e06e2003900c2c041201d00c4410a5514001c2094400ba882d04103030f86c4402d4072111042c800e10001000c102411802403404408003a9110406080c1c603200f0b050050030b15031440f6910600146002562500c14900c071030120f4040d583c13044001d004010018016041c440c40307000c0c2582c107400703000001000f80090410958141d4800a8150140b400c101c40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 966782868 1250 966781618 966781631
    0xb0a0c0905090c0d1b080412050705100504150b03060a020c07080a240c05070b071407060504020406060e09041e020a030308062407031803060204080304140927070f120501 75
    0x8000c211005c030344041c1010810074030004012456000c020a82500745051407850078901e6036926040c50840c00c50345072020340e95000c0c0030520440e2406407841c800030070350401c0045c0030302d40040ea65a0300202000c01c01ca400049103401c1c40d0707040c1316000050031710500b10344d24203560780381002800d0311104400032065403074210507144510a00600c0b03081ba0413a11268549034035611080c041840007421030003030001d20600781c485078503100000d02016005010014940c01d00c0d10410099a039258080350400070742c01000c094a075203440039143c009070310003201c07013150701c411500706601d42180901030341c020030620002080c5031700064101c0c866601110f00400ba00c0f408042d10150001418210140300d405001140019015801d10700301404c98445545c001030380d0341e692505a900980006001e0340011601f00714039040e020003840880c0080300c1144440c5030030040d480e42e082d0b039448000d00c02d821006682501000505c144806440b40f071110000480c0c0b214611708042040d040c04449642c07901c0d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 966784118 1250 966782868 966782891
    0x20030a030e09070e0316031709060f0a09080a0f02010206060a030302120c01060504060801092306040201030b010e0907020d09081216031110150504090b0a0c0905090c0d 74
    0x148106010340d1544805105034a07040a0004204000b0324038800d003c04040342114903582005510710340c01c8207500702c0390f6550075803030808000b003c882400c144a082c10301100d5166070300c050a580e254840017041c1d07511036071003000c11a80c2c14055404a000d90140040600c240610f880070385403034a00030380840700e40f51100010700c0f0a003400c6200160041c4c0081d152110718104100092003496002380001c5101c40e00d680c0010200e0301903922640c0035030742d01c240080401800403441052602c2c071a13101214003c91141094540c44000d0000381007560307942030122107070702445085110110180c4107412074606a0030207590760030440d1941011034100100007c1c1150300103903031076074a0300680ea007d0511020440d2072000c00010081101844040c0820030040d40c02003101058842c9084804134116403440440010164107410070ba0081d8140300400010400304020f180e00301400341340009101ca00800225000102c68002c941d120301c2d000c0600125a409030080c1596910b581d41c100884000c1c7c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 966785368 1250 966784118 966784123
    0x114061603050c1e1c08070f21020d05090c030307032f03030406060609150503130c174603090f080d02010f02091c050f0a2003 56
    0x1441040d644492400003002034826000783c5078070b0b8601011144034849101804244143c00700c28012198056074a950b40f0754003442c0010441c120300c1c100901319040186005094030064450002800345404001d00e030440c032a129100800c056000443d269040220207a0240506a41c0a81944a00e480001840ca0040215040150b040e101c1810104104941c40440b08848501c40e0308142c842444500752101407004510840c80b80c40002542400e01703030701422211440c0c21061700030040c4481900302580280440f03410020f40c891041c2c401050707203424416414550051000040c0d44416a400c0410000e088040e0742000c00429640100f0500d546201c421070400425040160520401c100d03607811794100d104901a140040c074140d103542c402c2040704600c0d0301c03c0015030710131181030404079070a104280305441c820301d05616195080c400500445104000c0e00f180b009890b4510041283c100441444454080250742e640300c130508100202e440015540441c004204000070b1350b40c51702 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 966786618 1250 966785368 966785377
    0x23070206010b090f130c020f060f0c040e18030415030b04020708040501080a020708070c06170907050f060c1002070b01080c210a24111306140d060608011406 69
    0x751800b01d410603d145003000010102003808580011800c0019101141700d40076a9249545640080c441c118006010f50f1411000034200300d8411400030500001a6085040b5022560010003440032611a000d5172040100c0e00085ca102e24880010000380200346408100c40b0641c2c40e8030108480c14000044c841a4031a20034010034868003084244419030046403042c3d00305205210050401005a90f83c0c2d00c2c40d400308100340c0c2c0a0380000000c1007030307941c0702410003982100c0a0401009003008810746030303100094003c840c4a20f11740e903c800c90985846041e0b82c2c400b20b9200446110043d4011048002e5005910503600901c95400108040100242d90120b00300083e0100c8a44071070b001e140c0ca40b009019440b400306004420081d00840c0319400c0c0c14641810382450700d140d51201d620010102c9a100614200007901400001c48900d40391181c0c10071980300c1d0815550218807594480560320500b154124140d01c1c00d64041141070f48406076038140e07101614000007220442042181d00e004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 966787868 1250 966786618 966786629
    0x1e06060201110309032d04080105101e0326070b060a0501051315050f07110907030e0a0210090e01090b040635010204090e0f1b06030a0c09092307020601 67
    0x10800200f42811b00ca5130603051180c4a07044c1c40500b1203951140700c1810790082d030003e50a80c0d140c07000d1104251600b004440188149001442010b02c100e8000d60a10700500c07015204241d003014400c0481140142c1e6440144500c01c1160b503030f0001e00c0c02925030b100940e0300a003d0320200001041650082c03044078204800300302d41c4120706103418401c4954081011240d030802c2801e01a0304104c00713a60300030346102e13407042c0081c00d14480c7d04000d00c0401034005004200301800c1c103030481103101000c00c0d41c08103039405883e8107251040040742607645a025074040150401c0c00000004c0940c4954018421340384215428800a640d8041117a400c81e0709030a402041070b1200356071440d00403082203030019076012070005030802c0d80d90355801d0300300c0e01a070f154008180c0100c1c0c10407000c0c03c41071000580c03442c2c0301201c860380d04610902103681c84c00000d012003140c903a01c001c0310001303501505943c03008290707070300e4240220020380b2004a0078661000b0303070800101d900008960014008607030349040c0c2c0d2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 966789118 1250 966787868 966787873
    0x904020a2705090103080a0c15020c280b060607050a050604351305060a02100b0a0f061110110403150b01020309060702040e0318090c09030604030507020102011e06060201110309 78
    0xd0171500e5114182d4440c0a02c00c040c0001444a600022203603482e4240300b400b556401a00d411080c0821030602400c44c2c480c0580790001d01c445c09001d402401070500403a00b20140901c241d0f52400450824841c4200c040d025210303180d00d94080007800100d0b18415032042ca520080c2c07080440c050780c0a2103541d00740311451070b80719104080c503072030003400b501105000c600e1a4503440e0741c2e400072070708542c01207a070034006802c410300360b02070340d00076024607490b1500544402b050700d45480c0c0241c010303051900032142002440a58581600c40400c441484c0750340d000010080c44000080503905a4043e101c11600391010646c0d00040081e5403160061012040c0c020f1864403d50400b04940e03527000900490340f01391750394800340416100300081e042c0848002004030307514200c2c400704403915800610030740d0b410800300a400c4460301c010440079045640350401c0e41d03e50107603200517400751a00d0404043c0210160886601c0c080c07460700058200c4006800800c020100e0800300480341c842164403c2469 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 966790368 1250 966789118 966789121
    0x60906121a10090c0e0d080a030b0111030301061407050d0c12081b0a210f360215030f0406051006051605070b03010807140901030f0212030904020a270509 68
    0x2070050b5003241e004001a8034280c011100c40c83c0015038011441b98090b200807001186980b0507907094820360350703800400d09001500280da4110543c1d20710050140008000d03003a81008070804070001502e6202d03502109940c1220f4409800918036019240c00782e594260b02c140380701c0302a000702d0340c02d07000750405210000e00003040103c8100710380c0294101e2081004240e0300e014103943c2d800e500b41103c0d07075100002c200704580380d98003002d4545145480b100105228061101c001440000c01601749840c05e0310b007103000140c00003440000c05103040b401c47d000c001040020303105071049400d01c071354441c1c1c208104585540d0340e800c0302010a801088003007041046030708510b100f2001151815072044003280c0d2402d49446895086030400e0b4000c400d01c2c2c6c41440c0a00c08204007064030280000c080d0740703162482d032441d1680280e03100c0340480a40038a40c20409000d1040c0240100d6070b101c7e1010b001175541c2c45001c035006100305500000d20312640261006020022580d001c1c25044800003003202016 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 966791618 1250 966790368 966790379
    0x3070611030114010f050d060824070801121e05160801060b040e0a0b0a030803013213090605150a08071401110109023a0c090906060906121a10 63
    0x5c2c0700700080340c6007440b030203001b82d44000495005d0b400190010700040c1640c00c0d4945200c210046008046c40c0c0704503000c170100f11103544c0c8118294115910304000050200d01c034240310740d00f01c0244c002070306010200904181070150024520707100600d415080c060f4140d90f40103850803103c040c080d50034503181c108020401c61218407401c680100301c0303260020310f2075442000242071a00691084840c450f01000402c000509410602c865000c61100301d082007090b03540c00c0940b9840d000b082445100c00f070780c02c82c0c2620316940c004240181c0c450410441c50030580b241c7d024400100070410302c0760107007150200740d89802148500071112181c0500f01d2116580005651a100240032400ca940d82c0b1058900966038070800c604000b007180c9524180c01d81040c40f0003c18048101e5104030b008400b00580e4000b60030360030350f0741c01ca4444400000b2094580d180280140106520140d01a03041034001709109200260b0340d80c0d072034420b00320350654a8400009000121080301c4070070005080c0c4008200c2d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 966792868 1250 966791618 966791627
    0x18050901120204110d0c180f0b0705210408070515040b0c0f071d07020d0909020c010f0e031306020d0801051504081603050601080f03030c0a05070f050307061103011401 74
    0x351988010000701d00d00040c1520001a5001403175551803058846d451800d2154000c4d40441e69408640010401981800c0d545801121544900c203249000010400c00f840790030704c078500301142e4090104242600d2240f403c0c03455000f030b000c0c11080d809a60303400034040ca0036540340b95242d000880c000d410207103040360084040d003082404644c540141180036010382403c1c0010b6001c0e02c003203c040c0080b01420303203404a40c0200107001805661150100c016400c0c1c1084e032110440340003100159076400001c040d0790241c81042800d503841f9003407465540304a5000304c050143d019240e41401801c8cc1c2e15602203039500880501580031400107001440941801019404110240c4030450700e02036030303946e070ba52514070b01c14854450031445140c11300400006000e81d1b801442020028980e040b03009103059100d00c8042c024149101c1c0014029460030300400960300b2090f0060111501c02c444c5044c1140c8990000b001140c115151424080c10164841e040e68180c400c2c0e41c61126600900a00556 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 966794118 1250 966792868 966792899
    0x30c06050a2a1e152a02100e030c0f0106150e030304031e170c12030a0b060307090305010b01030207080d05100b04090b040f09110907110d08010618050901 68
    0x5000560b0404450041504243d00d03c02e5481d0f00414404991007030f042800d000708982070f0499144c1d05280304c02c0484207080910100124034041d4a101161209030b0591402403401440144141011540e0140e140080041e10807802c0400076103800c1d00340e030b243c801e0886080d4011420300d81c0042007088201440782034249103124020f000ca915040e142d4880c0110440758948040202034944029410440c0d2903c000700380210503016a8148001c1015960f26502c1c400c1e00d00c84481800f000190070005c650b000b0883d0f000000d05101d50340c1c2041e10008000000c580070645203582000e1b03000c011944079201b242d8400c0d800c003940300e041011101106e00500800340240300c5050b940c1e02d000c908980c95900800060000c103000040d042581e000388029243d1003200307105254a00004500840c1c0914651004402c00310740c901120b1741c40c40c1c81074a5080c880301800c21648103102e1106035194002c1d0b00c40b81a2131054844640468040c128540c4114042c082c1d10340161410004004c117125455940 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 966795368 1250 966794118 966794177
    0x13140c04170c091614040b0d1401080714060d06032f0307050d03031d0f07050a05150304020d060c02012003070f03020d06080a11010e0d0503070f080c0303090601030c06050a 76
    0x8111840c5d01c404c100d48990030540103050007500c0045c070a040d5811a20411414940400c0304900c690b14052400380c40e80e00e01d1040394501968400da002c0983d503480121800c034003c884041203419128200042034103044a90081080c03205020044802c280441188141d1001402441c0d485d040100f0b0000501081c402142455242c0c403082c0c602c075205010201c05001454003d1540000000c54589000c910340d003d20700900f003100382448551940d14101c9440401c030382c1d0044c1da1382c035944040350000b07a400c140035011070300e08244548403074dd0641040c0020000d41c41c015002c00c501e07c1d01400248815540d50700443d081c0d45220300704500a401400c00903a09900018280d070f561407a9a0078074010340000c603074081203412452002d40c2c01c02100300c0b03198019190700500305503994580f55244155075026081c0c0000441400400c40780703104a6400d020540c06403922410444c03482565081c003800101e4040720080d0002c00d8061045040d070700c00360360640e101c0000f2042c400002c8014072103503454 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 966796618 1250 966795368 966795377
    0x12020402090a080f060708100e060f1203041403010b0402040e060409060b13020c010c0504120311070504140406051b12040c0b030405070e0619030213140c04170c0916 73
    0x6000c64052051031307000c40c1a280074080c640350080d00109501c00080c04501130112402040c05400e400d40205030f40640c0640d8502034400924000030070100e28040205a6844000b9011500ca42405150322004209500a11000c5144010401640180c1c0102c4400c5060440000c5040c80c09070480e81e071103405400c0001d1110b400c0d00206e903511300c607848038080303581e000104030f00e0b00b00c801d108400e0003a50b540741c0982403500744540950303e043e0302c0b40040c0402940103011507050409225000080c64002c0c810822001c40b0000c441c050301b81102e080c0e50452174140000d40201d000003081401034841c1d0580c510f070411007124401c0074800500103a03049682d604010400e5020400154000c90151006103402840d01e400c0e035a0080e4001c2100d03014903070140264242240301d448500c1900d50403641d0101c06145040a1801400120220050b9001740d1041c801e400a540f002401074460240301c81942408180d0555034035025005080c4d080900d0030001043c1780c10110400720341c81003d191 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 966797868 1250 966796618 966796639
    0xd121a01031a031b0f0307050f060a0203041e0801050a15120f050d051b0309060d0b01020309041e1505090f07021203070f090e0420030102090a140a0e011202040209 72
    0x2c20302d00301c0c06043e03460000544161100ea14036008101d0340200f8001c80040041f242841c02103895508001c042c0c034000c034070105400d101c1b1402402030b0b80c041c10310a1044c00c2074400301c01090480c680c052080138201e503e404086400500b050081480c60b9000702e0b05401d22510300303130a8624000c1c103800c003952441402d80564001903418086108100712580da55a2210310b46103201c5244041c0c0e02d49202254030410418900c1e880e002c2c01d640a0356026100020904442e00041c1d096108070710b07203503034040c4c80d1a0400c41d10181c060310a482081882c60100300c2414030012924184519000e0389a0005184002031900b00c050b0b201a9030100b0b0364410b845851030910506107150704282d4021010450f44400e1004042e800308400d40182885a1b80c1d5103503052170740340c07034089040c00d00241061406801c462125070320250100d070510800640f500c54802da07501e81503d614411200340fa03100d44441040041d034000c1d02c1d000a4182c0d00800041c014a00383c0d5401c0200a5208851841c0c2241c0c0c01c0c1d6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 966799118 1250 966797868 966797921
    0x5010203042126071b03030e0d0504060914061303050106061d1e030717010f05070201020408100f1508030306010e1f11030c07080d121a0103 62
    0x9180160700c10a81c0700b1290340403101096090002c281003a0802500303800c900c034120303003a980c03a5a41504218822005845080f000c41d1140b400019000061070b0342d0410004042d41980600c11403900c2c0f009982c103280b00c0c003c0071120f5109a100f44c80c001154484180f040b00703002c1e110460540740c010181460000c40b8800ba620742c0d5050703842568942d40d106802c1000540120342a079485000d2485001121210400281030000c1141035103004d0100ea031459440e80c80810000d006032021b0030b540c006607140000701c2406032808a0b42680c0700d07410301c40841c80450050081e01c1c181d9500720301400c0105009a069002848801041840300c0c2e1680001800c4a540302d2414024101a001540c1c2d207152900001d0034040d03212035254040da070300302851100052881200c80b02d01409191429001c108010707800c0c5140207111002c0858059541e000940803000251100915600c0e10f80090090032005500100c0f8001441c41d105006266504e1751250300c20f80c0b210b103034056080ea490b40f8861000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 966800368 1250 966799118 966799121
    0x1b0e06030a0e16080d0305101403011d010b0114163309051618091403041409100305060114121b1809071a0d05100315020a091503090501 60
    0x1041c41c440d241c200024807400038103000e0240c041c812406c2c248500d090031170b0308117041400ca2041c040041c898550400c41035070300390001180462501c0019058a04601085008001aa00c1107010500906150300101b9503c7c00381e03501c2c885014003149039400c40740c9520301008540d40010061400c40601491090040340c1d914041c0030000d00005942152450301c1c40c940310040301007210110001d041001500303608440380107402203c0c800426100c0031458188000840500302c01c00038080810b0101c1d0411002030001d0424004030b880c03041c10748680405181500603808003030260742111006005002000c030040c160720a01801d036440c900005407100d418038400d0360440403501c207900144407a500c1d01c0315004d05980d40c229640703403007030504608081c0c2d1580181f02d030892604403940c0300c0d00c0a901880540720392401164040c0017030710f04807020001140b218041200e03900400d4901560003040b40c400e130340300e80d132550321502c8016040400640c5412135010400e4101500d5580e1480060070a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 966801618 1250 966800368 966800383
    0x30606031e0118110c0d050903030d0204081b120304060f0e091009050709140f042301061d03060403080603030c0304171014130215070b0a1b0e06030a0e 67
    0x2c40c4800b41d250f07a80107401d80755410504648402c0a2049038011100030920110100380c03418100c1d9a0415a40400d0035400f40e401c804401f10f02c08a0001840c0d0000f1810070302a4482503000c8440151007810801144151420184668001c1c00b06111390f90081c905c09105c0815030030400c0712918240c00103403039054100c601411000324840c00304981100b030b009181d0441524103010a0307031824030304042e4007034001000c0c003441495011020f000c1130312144d10000c41c2000041904044d48260510b03611609000c2c82510006000d007a10081d160419003080c02c0d1a0800074054819a101c546080702d410b000504402d602d03020801160040701e0007000100b0007860700d1000501c40c402e020806078104000c61040701440c60a041090240e031443c18052030384046030940b0b840ca064881d0002c13480d00d080000e601d032020355002503031006105000c540544580061081803114150740c250251400d100301a4100105403505180b62042c50200f029541c044503242001920024441a503071803e0070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 966802868 1250 966801618 966801629
    0x402041409010905070f0b071b080114010f062109170307021b09160c140106030b01051c0305030727170d0e06090f01031401090b040c14030606031e01 66
    0x1500c50740001000814007814000700b06d41c43c150780501d071400e41c003488248544040200900108640b048121540750881c0c2e000d4602c140080055500740403010220035407c4c00f400340c40c01041c900003d4054410748020381100701c0e900d01540302a038409591800b80408280849013071b84044c00301d070000c03002e000c00b85102c1c808641c0100352044558100070720891404a11034003405020702001000d058082000c09103040901c0e145150441c1c41c00c0402100340141c1407a545542403a00c00400e100d400300d00c85040e035008942c1e84003000b60403c41e04590000f40c1c0b0008010170070600000303002500400040c0c0784100003000c4a0312401e030b0001d00400540c0f103600300d1061032140421280b4601c204110011041c207150415240004806002a14500071400c00501c100140a00c0d500180d20035000003c2110b062428600039513100c880d00130107004000d40e40c6010720300d42400f0500544c4140680400c1107404403101d46152210381c01c0c083d095000030000ca0384110544140c0f0b64081040e00468020170 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 966804118 1250 966802868 966802871
    0xf0b0105010f0e0a1401020307060507120c0203090a06030c120204080f120a14070201140c0a0627022404060302070209010e0903090d112d0a0608010e040204140901 72
    0x10304010001d00075000c1c090941c810020b00d100e40c001da50f103e02d200d600c240c41e031509000e8070b41005100101e2551042c418000e0819051400740000981c00c54182c541d2400082402d006c60844080101e070f4900031060b00540c000111801041020302a0f0710411105c9181d113000440d03a80c80200620580c2d22952000b040d9a029082e8282c000600f484244201c100305010305107044903600740142480d8183d5618403548400081800842e806104110f820302405044580c43c0c44039410f503661291000c2c01c05413400d60400b22146040e001c1d003d4105440d100307400a00c000354149409109040034609040c699402045605e4a00a500100900010b12070340c0e802607500c03101481809058501a4070055101c1141014441000008000d484a4503802e48a50420f0502410111500c0d01d07114880d503000364080c5c0e8488082c000c0090b24100c425038011814040745403640c140200e2090300e116081c0001c15041c0180108010340394083e8010f40024404207030030000e2243c4030301d030030020348806005a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 966805368 1250 966804118 966804121
    0xb070803090d05043b01031101080a020a14130302121e19082a1e0601050306180c090703050a0f0e03030c0c16081509010608100506030a0f0b 62
    0x12010021608812040e01d002c80c00c1910b0611031807200280c0b0b42c25600b0030003401c10011702034544903028a20b000c41071000d802e840d50b920f04000c5013281d0615445400035850b0740000b001c0c0740b224021a4007070030a5586001d60361001007d4600c2941100000d8180d24540c00c1c40003001d42e1b2000f15007600407904101400b000a81c0040c182c03103c3d4203aa46524a40c0c000c0914540b1058840480c00021600300b44101d03a552440ca18000fa618014003030354510b4120300900590030f80d800110743c1100e0103c50100780c1080b420104143e5505002d11826034158001c8001031f10300500511034465141d058412a40004040000a9030290b4225542d50000369100204039030441103000e007400c06039070701400f000000ca40d104100d4403484010400c1c9080301c00014031381006501040041004002e04801081c50703621010041e4603a001504c5c84028000a43c2c0466603e150602c12541240c00ca0b800916502c040018070001420000381819030500a001b13103500401d0090364030b150300034841d950480c0c05 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 966806618 1250 966805368 966805381
    0x50103090c051002280506041e02102c0307270c050304020f010c0209061e030a08070203010b09010e0f0705040902030702011506020c0f09130210080a270b100b070803 73
    0x3803a51721030507000c68441c44403090101e0300100b1520b030003941106101c1c10545a04003090602030300303560000e400030129900300340c4596005d19480c081200c2070751124501e0b02250328040741d001040703840507459040110100030201d0700c101c112043c0f010a40000352010f90f0581e4a0303003160801103c038400715130700104003c210310389242014050326007401c0c0611214166000300e0036440c801098103000e40400b0460b602084100350343c180d9004001411287c64141070b02e005002e9800c0500128007a41c20800c41c001c2914054038464140c6118080d8061242d071140128144080040c208005010b4100f001150314803040c00154803c580940022035041441142e201740c04505034000d108541008000c03991599508640004000048600c9401a06c4e00f0700d01c6005030418078002588000c02d114030001454200c1c1c051441090000d40400640003622135961040c00710300b440106504200300e40038000b420450072290030075407840c540300c0d080d512902e5000d210340c850f00341915920804000c0056 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 966807868 1250 966806618 966806653
    0x130302030d0503240f100c020406150203030a020a2c150a02070303030207020f18010e091504020d0f08030c070b010b0405150c0a060f0c0206061009050103090c051002 73
    0x6441e01e40307403462561510412500d19050700c0f0b060028034010301d240340e1a560355105803d800e4114010004900c400030310b80050000885c29004174012802c110001602050368100f42e10340c01170540145181d42c4c0c0b826804802544000c1220081c4a2000d41c0144031441c08a03010040e4130a07000c83d0402c141c4e007801000200c030b6200c060a940420100300918455501041d210100ea5040c100581c40e00031714400100301d0b103280980c0c146c010b1501f01d403600c4260200c0c14070604230303142600025444d071542200d8588450002c094038840c0540d000110f001070070308180300c1211600a01c1e02045100c0d40e50340780b503440d902c260741442180201181140c2030000b0304010358014143c0980040c5840c2c60040400d60800d000301c4102d5600802280507400c8890a1141e1280d89900160402c96540c10380112070007007214000c43d00061140e8800101c2c181480ca9980e421030b184d42d2036100159240c42c004601038010a081220110700e400400183e90721002c18107101510703250013820f0300440c075901180 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 966809118 1250 966807868 966807883
    0x3060b0a030e0633040905060a060f0b0310050603090c0d0809030d08130b07140705030d11070b040615080f0604140d0801091a060a020c010806190e070e0613030203 72
    0x640c8049a1250203007504407000c02e9011007459000302e004a04c0584009001000d00b018082d0a0380140300c100010501180c0c4000144d460411003c803c068070780403003a1781c0c1d000443d01d1b1100150021000d1103145080005154000c1c003210454128422007404a41d00048840c1c2c200c80e22903012401284614080c003000d00c074010701d0715003618076107804402d42c02d2011046802502c002c0d52140402c840901c60128941c003a000e1202c0e540c0d07181c001d4548070365030307174800851100346510301040440d1024000b400c6440c05500b040740114a61074648990008150110001f1345820903604005240e00d014058100403910b0f000c0603080e80d241605140d2401004401e60340b2843c0c01000c04180c000b80c1021019056079469800000c2c02940c420301c1200008078480c1041e88200003040b241121640004c02e4a0241c8081e43c484c1001e88a5034140720742207161001c0202c03181d100e10014441040180170b107591200840c0742c01078840101c42d010610325805213180040c0d103c00d4050910035810700f0000103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 966810368 1250 966809118 966809131
    0x3090c08030c07170a050d080415020c060612011b03020705070602031603030f1116121d01050c0a0615080606010c030519090806070e03100615050a03060b0a030e06 72
    0x1585030240403050b1503141c40c0607005518016419822030f410115040040c4500b15500204454540506500241c1a61801c031001c82d0101c5a00c2364250549007503000381c6089410034001000261585820072400540143ca84d60041d0750b2443d10750401040188600d90014403a200180e0795501c80c20300780c0c10301c0659045441507620400c20b00c0c1c0504004d5207145401501841c3c0011481e014a00a0010f0310300d0016940507090013240c8001104461a01d025140703114149030f4250044004090300c010041d50081c1180c85081900801c4650140000313144c1051200c041d6401220903a41300e908844129074590031542e0b580c00c091194140800c03455422072401d00708000241365a640061545c481e04801003200d00c006030040b581180210405405094440f00351190307841c0600c4003c0100c134034800010b201744900d003000215029244198002d803200043c401c020042a10000d1b1620b0f4000c0d00d59000701540d07a01d000070035080d110041d00d0030401642d0080741e02803065540910b00400074041d13 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 966811618 1250 966810368 966810373
    0x4170303011a1804050a0b100201050f010b0a050f28140301170102120c0c0d05070c090c020321040b24090a0b090a05040b3102040f02070303090c08 65
    0x18028680c6041c07601944001014000d50f4451800d9072144805070f00ca520030340c0060070030040c40400100c40d084500d212606442d8110313400b00d4040e0480c2658002d9666941f00300c11000180803681c50b15004240c941e01d98100b02c0c0c40c118800c048405558811a0100d450683c81c00c00c2822040b840c4bc0c00c1084a8410325024080b000e180c0010402c038170061040490707810115510b40722801080d01078800e22035807841060098a4000d100d46225401002202c03858066801c607001c081d40120252546141c11401d108019428010003074000c0c031135900da00c41948014848684010001c042d41084441c504041c04280c0c100340c0b0302090300f55000382c80c100850f200a801901c0d9410201c54040210108a900789200d459070801c8200410209403081d8128420600304026120b0700e4000f28016485480c0c041c140343c1c2e4841000003110f03c0303a040c010150a82413007108100c0d94003c000b03014180001c000113000c02540300e011040313034410a0118040717600c4004800500402090010003018244003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 966812868 1250 966811618 966811621
    0x714030d200906130306090f23062403030304210c0302210d0905071809020607061a1201050a05090705010207030204240e041e0b01260d0504170303 65
    0x1010003401042c1002e806404040798211030144061107240c0116008003080198442c5070070003070707542036523a1410350310a068601c40070607003400b80040c44400c280d164050603894880101001c2c00f01c0226207020b08000c090700c40d88456640500c01035006900c550b2a00b20032450210b0f1444e41112520030790801c1c01206900e03000844c0d00450204c0c4100d040d0186014114100c14015285020b001440f1300007514040e00c0c1c008200c1e00054035410f40d14507609074819000308001d420b00b070b501b907040300940007030061040d000060300359000000c030801520700c0300c004901c0c104e000c11500a14401c1e110755a03919013003406416051440740680203110b080c0608201da04110010395034000912000b0300955452228402461001d42d860b51041c141c1131007420388659800f01944258004d9500b0703a02d00360081c33100b01d249a29150780070201d941c004681943d07030303181009829010403400d02802c86d4442e08182c0140c503160030700c00c0d07004410003500d0369502d40e41040d0060100c15440121110141c2c000c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 966814118 1250 966812868 966812921
    0x702030a17071b051e0c090a02130302061c0f0501030b0906013006020409020405010207120c060f0c06050a0e0d080c2b0504030221070b0109020306010201020714030d 73
    0x344050110794500b03007420030f14214a8624500268800321141c50b201007101c000240001207060061100119041a115110924030800328400e003003c28083e01c00a1707800300b006040c80d0024200000d0b025011700402403588500300d05076015640301d480c0327080d5217100500420a41641c81a00305c982c0c10010980d81d0b05151100451b0b510300b0403030508803201c44211a00301e543d81200a00f00541c014829500d560751951610b0294126008040c0136004084011a80c0d00b07844010003c1240c101d4100c0791124509a0b06446002c03c0080d030904000704030350541d01240307441c004d181c09650340c08400901c041c417050340d80342440740e2442d040c3c003006030340803e2140303001140f001d48400801c0300540902c80715059440c415140d00c440e9449580c0343c241f4082100703241d00400d01d031800d110072402c5000c0c0c115007500e038107980c2e204480000302030883c0e20740180400c04140e8065680182c0600006140c40229211081e120404211180c240e03800041d0300409031400d4040d01c2001181022640041491803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 966815368 1250 966814118 966814127
    0xf090501150f0c032307060e0607020604050d030b0103020d24050627010203040503070905060a06300b03072303010209100513240e01050406020c01031a090702030a1707 74
    0x80d0b101404102144c0300200e6401e800d0a0004000100d02000c06d907030b1411403034038202030200c0040717445160040c6c60018140900100b15284600d078000c000c1c0c414180c600d801a4000c00e00d080740107040507800c0c82492110411072181c811100c9007011340030354002410036013040d51150764201c98015902800000380620b5403684190a100e28550f081141e030041c440102d20794080c2d40e10055040c8900c0300c000840742c00640c00540100000e031342060400b42c482605584580e0803241c0c2001f00b084203600d11540c00050703e5001c10000e001b1401140404c02c3e480001d141400f0b58216152880260742040216080c0710301606200c2c800b50002e43c1441c01040000f012a8242d113124010f0040020b4a6010382d2045220f030400351160b0200c0c0c0e007031040d6090035512012502c111420101d54401d81b1030b5265130184060310202e5209e5801401240c07101c0c40110094446002003071031040d440d001d5000ca0341e441982c400c2c800d04540d07004580b40c82808000500d00184c591072000025548002c1c44a0507034003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 966816618 1250 966815368 966815387
    0x191703251104060b2a03190801060e0a15141c050105090603062809140f01200c0f010908030708101d0705120f01091401050a140102070f090501150f 65
    0x1175911100601883c4d1041e1400e00c2c1082c04d10381118000010561a800d060820549005031107603548070080e030300c4000a94025111071000351b4000c0c0c5901041101071002a44030800c0081441c1c881000708229201070074036000340041d154051220070440c0607031500744c86080d005001c111442c0c1160b080c480042600d4000191001412925072032105a00b80d500d60215841d0b02181d610802a90b2950f04059000c00400d41d100c3c0c0440c001d244c190010400140507181014003c80c0d19202024003a1510450951100700c0303914290181c08101c0004210078072800503003500076990a030380c9280410000380403010042c030203103071001d0900052107241c1250079a4035807400012010429174440d454140c0c0c143c051003500781c1c0c5205500e410850f103503080c0d20034181281d07080001800749117075080030031a0344142406800d40240020004000107980c9043d042c0410f881130060b41d4469441e654420710458035600001c00703c40e01c07680100004010001c624680034500e05e8040c000c54645500209980c11 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 966817868 1250 966816618 966816637
    0x912091807200c040b031506040b1c0803060f01050f0405060307090e15090a0209180a06182009180901020c010c110705191703251104060b 61
    0x41030380000760010702030407441102c0c0004214508032659811051591845103108aa00460400d49880303001d00300000c80c02c5085c824080840c0d45907440e0018040140b2403040079a0388001800009104400c002d0000001d15008800c0f00340d0300d1414200f40020b840d5509003640c1002810410507452150390000d036015124122400c0b0f54a0b110803074101d80341c0b07a0f580c00560048240800b440707241d601440c000c0d14104029500c0041c5941d07114040d0040b800384504941d04141c201c4402109500d0b0024443c0d0b00c40c0d144900001d401c3d0302d0b185280c80081c81410b426400c1d542d206120709a1110500340200e60141d041c1100e840c0042c40c801103200e480701002c41c4011020001d000c600e1611080d01a0f594000d05400200b06060703841c0b50081450031040280c801d1303805001004a21420488000000c09908900094819241101c03014030a180f0381c1500714140014020005008496441c0719000034103152000e25034845400d050003040f01000c00710384a18601101000b201c04040103070360348a40d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 966819118 1250 966817868 966817909
    0x6061c021e0301030b40060e030d0b04060b0a0c060e1c0e1504090504140303071d060901020a0b0a060f0311010305310602070209071808192d0605091209 67
    0x21441c11141b22114014000340a07500708480c0010301030000000e0400c0d61359507030003030092071180c030248421112540640b4035221300400c01e8080c80c50040c0420018244074000018104030714641c40e074200081c00f2500d6503d070000402181c46107501500f44421800c04a030758126140420070003100d148241c0c0b00d4102410703281ca0000e002d010b109452a400503007030b0b00036aa604e15100c1c10041840d2051000070340142200c030300645d414140360080d1445684181c00402d103502131611400050040200069580d580b81c1c003002c10405c1418504030001c52045481e40d13030000f0b580c3d0014055440080c486400f048000c0300380c030902980700f503060400a5948030005c030000303401d00f0400b020380329031180079420620780d9003403007205a4011200d000412140c4401d010041d1035034003485e20b400900e107864501004c00c20462010440c0e101440c4500c800402e052003403c0f8144091405080594500340d07003860342c0303100700000114140600001010840f1015240205580005500e4144071417848903d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 966820368 1250 966819118 966819211
    0x30515090405150403350a2f1c05090c0f03160b0a0e15030a02161202101a0a0b07031107080304061706061c021e0301030b 54
    0x1605021003480602880028441483d02d82400350071a0460070440c4410f0320086e002d10320040c0100708400412070380380742d640c01684032012907101500480031740c403d4040c00b0302086000344070750341c18041c0c2d01c030031134045107032501868400c14a0b03200c00c2d074a41446041c200710401001d000f01266582116108549408200c0c1c62000031a01d400b5243c2d520940701401c4110204081c1011b8000d4080c441a0365078001d0000f03000e1042c040340c460360341c83d400c8031050f00340003182c0228441e030040d202008054480c40f02e210300d1500d920070030032030500c9020b0240c0c100da8418410340086014820810654412010025803041c1c042070021102c0e116550800c007011458501305841070f503000030814100d904842c20151158480c5450354082e200e04004602c5d140c088409000000e001644919801051581051004003000c890741450015020201c1c1d03080012038403403440140104c4031076900a040507100d605514003031810311710152001403131495402a6642c1e0b05041000070800341941e42603072000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 966821618 1250 966820368 966820373
    0x50103021f0311070309050f0d050d0e040915240b04090b0f031e0f0106140f130f090b0903030f0606071e060203070f030e0c3601050109060305150904 66
    0x141003c8a4203040082c000032084241035120000f001540d008403900041c5088850800500510180c00100581c0104042d10001800707401504034031100940701192602c1155904201d103415248a00412543c400c09032104106501d084003070903102d0f500c1200f4841c1010104c00040c021445060280c0d900c9101c95006921050101c415450024040303d90540c440038007080018012001c03d44284203a403480c0c0c03070f42a4140198400c4070310f60110362880214800c03d003da00c0902154079504046400d034860341d290340f2841442d442c1e282e140304c0014403000501d402c0751200006404242c4951044c801e003c614003c25030750f203070080c40c100d4100e540c9140381d01c2c01c00100402151661311969a00c0d280c45d00b4450b090700214810309850740c8000c40e010b200343c401d47c212003502e42e030001554007404403910b46041c0318184200748410b19000600209940c20500226a40c000310000c032038503107000400c05944c20284507070180400781811b1200d0b245c500c5001c0c03c10402e2482540c070614040c0041020f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 966822868 1250 966821618 966821621
    0x1109060d060513140c070c12050102070b160e0d0b0f040f05030705010f0b09040c061d040501081501060207180c09080f06060f0d08030f1b0d060612050103021f03 71
    0x100400f0701001c4080c500c01c641d2000a11960840e0900c880155001401c4014854110340381c1076030103010400340c1c500304019062238000b1104111180e6608001c00c4010540003400c40348141c801c940e00321226503030780e45e00a1008040340d41f0240120300040b156000140c000c00856407042007500440040e560307505018010102c501e4006d012400001118402d110381900903601e00c80c403d5000784244643d080c14420681ca045802500c2c41000e25802d104081c132a010781c054018012186d90034441590340080c08a03102030b400010103501242503d094a91800c40550041c01240040d0024501e088840802e140c010701001e0f0105a85100140d030080c0a001082d000e043c9100c110740942c0415012a56200d10a8038150b2040e10005007403e650300d0f1441540d0042c540c0300c40d405040d40c882a404070b1601c0c41c060003511011901200740220b5002040140040040e07001012518a1070142c000d885131046015420f000c5090800500141c2c07960201e01c4000007061509117410400d41e0001c50 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 966824118 1250 966822868 966822881
    0x1d060a1802221503090c0504060b0c12040803030103060e030f0403030e041b14090a08030a020a0b06011d190e0a0209040f020304031b0f0503130e09011109060d 70
    0x114a40c0c0455414186540e01600603002c40c11400c0220b40c800109500c0040741074030030891030249404484080610a80061901a2140c40a00d0007940c48100103015110703650001798031907202080e403c6113184200300f00000c004821049a19090400800c29224401400068000c03910740368002e41d10b013810400c580b002c21071442c0f40c0e03488640b1780c60001d10280809072b03020311960821070090034008412000307996810558503001c60161128001c44c03826044090000d900015801001440c0d031f030240300078a0840d410340d0184c000c3c400c1601e4070b44540b20014004a040007030f02d00c98566140045d10091880e02021200b00d00900b01c2d102c04004400060707042400ea1035101c0e410710507040d00c503070090b02105404980c00d0050103500f4000c17801701c1c0800c640250014402d0b071004104e68140060044003903000780700a03200354176a521214955406035801020030200d1a6040200c00340550041d5003200380500240503c00100400f4050380c020303500070078030170300b000581c910b58240a5440003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 966825368 1250 966824118 966824129
    0x1005160804300302040302190602100e01020c03030106030c1706030d120b03010e0708010e0a1a040201020f03160c080d0804033c02010b060304080406030522050607181d060a 76
    0x2c2c4880ca0500e0050194100e880201e0140403000b020880b889903a4009109484003580100158142d102003103000d00400082e00c001554200180e1103122018401540a09010348010030340413030080c0300070314400103020121014032014081c00003603500800c199180b64481c0ca45220842130900c0c4810091a070000455815881c22010124503217012410200f194601e100030031449040080316078540e400c00c8001030a505e41a00350300342d0b203448204920380203401841181d4100380703403d00b05d61843d444241100180110138529404104010504001500185000c4c000c4400e181001806000d000740c801001c0c03141c1804002c400d00300404d0085070f0781c52039045500b40707880204c980310b1703d4481030002c82c40107500300300301e5505c0b82c00d003101201e0107a40c0c8050903a1500d864010700328002d0130040e0210512022694402e480540c0c09101d4134011401400941103c0c14441380181080203541000134203028604c60402548407500d061103810311507a04404483c3d624800012140700380d98000c1e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 966826618 1250 966825368 966825443
    0x31a18010e06090601090c2f030f040906050105090f1e0a121101030504081c0b06180405010501110c0f03031209030c06060406180207020a171005160804 67
    0x74504440710010345035010700c1985056428a0741c81c1c856203025540c03421a540701103a6640264000100d120b82040549543c0103604448214910003903410755014290f00f80c10b1000c00700e42070160320070300d116040007040c0900f8541c0c41c045054020584410028504c40d105541d406e90040c8000c0080c0ca449041950080801c0000703500c5101c54064000802001d84080c81e1441c00841c1d039501900c551401103400c540214248901480c0803c075820056549420564403000c816056407901400351040700050445811042c92035000c0c4002c0307900c140e11090410200ca00c180c2a1045d02141da0183c00a095030540007404110700802d245210303840c03400094407840c60400406d414040301404140300c5501c103650554481034200f20594041d80071701500b54040f010f100d421011aa0700500e10b0701e1010780340c103280729a40c050100d0740060803445d821454005e801c0405002c0324500c1042e900c084001c50050b00c0c61a0000014200e0500400080202c1c082420010010301c982c4be4414141b07042010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 966827868 1250 966826618 966826631
    0x109151d1024080a1431030c05060907050916021504030905030d0c03120c0e120d090b07080703050a140d0b0a0605071a0c1b031b0601031a1801 63
    0x60300c1030b03405401404000080c1c0442c021480b580514094000040e40c0d019255090303032100344450840c80050400c6070107803079500c4510003032000301244900c00c00c1e01070f4807514000342035401c0c024207001e0014208696900700410510069442c03045098200c107040c104640b2000720108164a00100c40b02c3c00091040300000b04410507034885452000e88905034203403090102000030503070706400c4400c4000c010030301350f00e0307900314100450b0f101591310480e500d4000f0007a80e03180085074040c2211900c1030030390340000301c020000e1904900904002d0411032000340c0340c00d4003600e071310300c050040300d100800b009400501220454481c0d09403016a020f00000aa6100301102030180200340400000b400380300c00c880005800c07400f89042d91072a5070402c6c0a0381060594038001805000001e00d2500e13007441c02e010706c0003500c1e4103000e10f8958004070002181c0e00c40c441100501854038220b040c0c3c8050344a1801440000c2d01d42c0088540148800301000c0140c988a802d41c410f803401403219600ca600c0c060 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 966829118 1250 966827868 966827909
    0x3010e06040b0412020d020d031a060d090303050601020309150c15160f111e1c080a110702060f0a05070609080702101d360109151d10 59
    0xb5400d008034459040d0003071544101c5800c1e40c0340c030355290560b805600090055645940260845507640b6140030000c0040a4ac0100160854002404414919541e5041101015090721031207402c8602400214184030b424000203202c05541d0885481401003c00d02180d280ca0030401001400c4e40c540c1082d41c03915003006030100d054244000b10000801c40c104980c081030050b210321400075030400c00b400801c00002d071206140e0500207003030003041c4034035425400b5000142d00402d41d400980c7d9904155403d200c4a0102a00c01400300410b040270100300c2071005a54040454041d8040c5d0107030251244640802078403d40250403001d001e0a0800e8402002c100cbd0760001004458404c548400c800e00c0744001c1110310b5814102004016094000311400e03900d440243d50310000c1a94003140042440d40402802c0001c07142c899152480500e40140425035050242202c10303201140110445860013111907105151003c11112403448240460300c81007024071840c01910f10160b20108958445 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 966830368 1250 966829118 966829133
    0x9050a03030f0501030b0a180b13020a171e0f1209010f03060509060607111011060108011a0f010201180b18010e07141c0c03201e03010e0604 62
    0x914088001074944001035244510b54800c250680b81c112503042555505c10251314010140f41c1344101c49048042132841c0010071051a441c840c900b5900700b09180c0c0c3c500c0c414400f41c24403035004154a032250b440c0c000c0c40300000289100f2810003601820356500c56034452039051030030120014840b801901804400c1c0d1100304c000700081d21085c0e944074095030402104031308440e482e008855204407090003107000391030001c0c06803031003034010050541d80e80796030030014606000c2d201404000c5400628200c0d8000e60034800140104442c2c0c2c020300800c8004222441d0102400003118400d01c80082083c015034801d505c01d00ea6000c040d01c2c051290716071802e010646076012541c03640c078030301c0001182a1b5004103006040001da501e00003414240d05005014610310b44405003180c06c0184040801c52032450f0101c0600c5150040d84a0380c105420b50600141c0900300c541303291005040b00c44e101e16952500104280c00420311030b004e0242d82159400203001d444211003513007003440380106000901014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 966831618 1250 966830368 966830383
    0x203361501060e040c020a03030b19090b04060b0c030d2c15100305060c030c0f070b060316030b071808100e012a080a0f0c211104030f06020408010905 66
    0x9644850f500700310107108000a8641c0c00f0720200050b000302028900182c001d07003182104031001040d060440c5413441c032040c00c03030743c182e4408040c19032141c00d0a03c05041c14460705014002c40c0301c40030b103020a1041140d41c0c0f4440c400442c12590b95030b500720780401940680f11140e0070400104400203041c0300858071fa8400106900d44100c08540010078100107001d100d2601700c99008000c0c0400f503898494000c42508000d2800c0c003503d5013000f8a40d0304c882c440e802070803010b00c51960b001003130410302d00303141c64404000010301040c01c000340c0c14400b0880f030307280d801d81c402d0051402d030038450003119030005441160343c48440113218100d502c1d0a0410207800000c04d10041c10020491020480c0ca41103010740090340c11541e41110404203a43d040c8074203680359104010072404038014140440d41000c81d49028807402c000383c09440c8a0b46501001101400444c0030744100380030304141003515078018031440c40004c14107840003a1403010000d841d0103460041003020300800c05465541495901c4440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 966832868 1250 966831618 966831629
    0xd0207050f06061012020f0a090815101202010c2f0d0305090d08040e0c450409060c09060206010915050f030118110a06030203361501 59
    0xe011000407401e040080c000d44141e40050004040300040601500d400c04204000040c09408100045044400d84003d2801348910754800f50080d140c4220705003001d000c0ca6415000e1440e50060142c40102c0140050980701c01024208980b4140c0c0700503503022100c0c14006000250070343c00c0e030300070321000d041081d101c61406040103940488401001400719161130000d0125200380300c00e01d200e090400c09040c4161040032014a800e0311440e5491404804031090065917200040560f41114108881c1c0044506500e09061280ca0b0300218003800e00703034440e28005e038403041054072540d6846401020442d500050700700982e1001701002804100d02d0300502c0c0251040c0f000018408440e449900d10102d0141e441d25540c605003002c00c07a40d20600036030950303d0364131104207041d03c2d03003410800f0b4212885203580c401d02d403c41106000001c16264818018140305004224a482070b074081d00211000c00448808807a00c41d280c14482e0004d00a85c3d001d40340b00e016202c4003072201c980c907514143c40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 966834118 1250 966832868 966832873
    0x6050c091302030405061f030c0b031503010e100c0c1a01142b0215161101030207050601050d08131d011a0703030e01020d0f0b18060a03110a05060d020705 68
    0x4000c0301c0402a48004e4600078060b85c0114002269003100d41042c0318620f0580c0003107051581e894030751680f100320300e402140faa1140001400aa0a2400180c0d00041800e40080c0010140c540a45860724104020480300584424018212502c940b070b002d58001c0e0b01200a07c4064a032034201d00240509010744104101204512912460130a00c0d800109030301c03804040044549200d5160003400882040341c1000c01845940790703d020f08009040500c490794200b2091212605200318040700307440300d940c14180b04000120100304081003290642d42d00751142c0d50004902c0c9443c1d1a20320820b0700703118a0300c400403004a20341640724000900043c202c4078925213642c8498861825000c2c0e01035481c42080c0801102000038040d41060a0518103000010306001d00e602c0400c3c1650b04c50001e0080b0550b542e044045070f4544000300c1e012024510054100c6440c00401180300c401c55404003a028034142e11010815030b540302800300c040d240103404291508261001c0d00e01071b4105940442d400e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 966835368 1250 966834118 966834139
    0x13030324080c130510060c032a12141e090a0305030d05010b0a120e0708010c050a02061006210e01020d020c0d0809061906030803010b0c060903030709050f03010906050c09 75
    0xb0209014070b42c060403600c0b040503000d46c80c0002c1581e905660403011020721141d508500c0188003014020100c1603040250043c03810850719150840c0051500100305201c009507241e041d00141000366011602c00c594241d0715180d0407808c800b0030b4007406110541c4802050408030800100ac005814030060045040c41a079072544460510380c09410b140d100001c0d1104441c079a000200d4000f0340100c3c4002c2e0944542ca616102d1560940d6681503080b03011820010b142d01c4110f41c104111540000348011240c1c5884c2007105c01043c4000d40819490302c003e00d00d0301c400304801141e20940e01003910318021903131021202c101202940044815550034090701c03003034812990145086074425424000500704950384d032100c607580032403850306610781c00c0e0f07a40c503000c8006100701d0300460103845801b45954070384602d0720304175203010801024000188c20070304c00d001e66079810040900960720102d88054003049904003203801403030807800203041103003048140300b035480c545002004405825907052082 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 966836618 1250 966835368 966835399
    0x613231c091401050318010507031e0221250807110c0f1c06020d1b1b0b070e030a151a0109090504080c1005010e0f13030324080c 57
    0x41500d0b4440c0308681c081450740981150303c110000e60b4070004542c1c00c00c24401c0703009441821103004a401d04013290b41d81c80c13061502e43c25107403900c0e0b00382c80820301503103400c50380700429800442d50350390300360000c50003004100b40d640c0e4a6813841941c1100400003e101001600c02480c080c0252185800300d880c03000b684c2616400480c0001d0642000352182034000c1e03a020510590180c0001103058080c5902c0c0c070100003418034002041c0c1c46c0300c03185001c031b015040c03081d40c0ca0b0b0107040401ea01b411303c4004801c40c500450403074140c403403064002000051640c1c1d16482610400a9551081c1c0c3c14011511078404005500d4441100b00d48036207001c12035801c501c50302518a4403402002404118650410030140125802c0701e54058400d21569040902080d01e80d880c0046040c00c1103680354541005010210541c0c00c4584d0008400b00390803600d04254114480307151010307002404064468000340200c4c03090400380e149200c803404c00702d42c842da030322843e040e1980b0000f60450f10540059100079103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 966837868 1250 966836618 966836627
    0x15070302040803120702010e0d030b0f030a0b1302010e04050112030908030301062a1a01080d020c100509031e071403010b01091215060e040501050906090613231c 71
    0x1551402c03801545081d50200c003403607403400001c01d060110f40d02c030f040d419a040c4043c403c04c2e0300b505081c0c85c00b00380740d41e8400410455055814065003c0d510001441c000b00e00c0b00642c80d60000f401545c0c4500f00916400101d64906c40f48060035001424136000181d03021441140c80c60440c081c1c2d40ba00006911054107d0f00d0307100c00c4c821440014400d050302040a0031080a049048034105031102100f01c00c3d0381c030003100c1c424110101c2007010114004001d05201840704810b542800d1019004001c2d00c04001540301149441e02c0d02000000f08206025841c10440b007500002c01206280d03090368409080da54071030480c02030403111440c6030070752015070030705002e00b810034a01610b5860159040c20f24040003035071800f1040c1c60412254019102240340d40c8104030240031404d80e5907615151078103202c0d0075174230050611046a40300c1c2c000c101d00400d000c0340b22a0044400e0b440d010705412903050907602030b4905207042100049415090b0504040051000010410000c0d0800007801d4501d040e60b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 966839118 1250 966837868 966837877
    0x911011106070806280915080d1b1509051f1e090c0b0c0a020f010c1505091002030a2f0406032c10060f05031509030c0d0215070302 58
    0x501166180011a940d4600b400d12002c0c480580c0c4081100c91400d020585550170040d403010400d41e95400d004900740d481000680b002e048480000d20720920000d00c010701d01d13004500b910707800c0340d1903e03072143c20420343c1600403002c20b903a880b0621800402c0d083c0141c07140100c0740580345a07201d2080b201d400510700d01490b5500d000003078101100308500103528000d4038606604a40196240002240c0c0c440100c01030803c6030f0001c0001d210812851041c0100480c81c90504c0341848402c4042c00c0c001000c810864407050103980022541e501c03200e0a2515180c00000381e60321403800442001498041a4030080720403000941c4056103406540712420b03490303103060200004440810082c08154001c0e08860600f1165074043c0c0d0b403a0598400b070100700541010f0b59001ca420080c0500c240351101d000d4840902180d0041103451450540020740c0ca04103229610030a01c400e0000640c20b02c3e00340140c90302c0c803050301e0548010840b5108001d41360f541c80554040348102035000b1400780381c403034403e49 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 966840368 1250 966839118 966839131
    0x72a1e0f050405090a05060408120114030a0609020301020f07080c01050a1b0f170a0c0201060608092104090203040b070219030903020f0a0b0a050a080105031605010c060b040911011106 81
    0x14410368141402d0101810008100004502c10524404001201000746a00c100d0281c0001d64807500941c0d010002c1e40010390107105070300110038142c0d02503980407883e100c82c2603100d000001e60205c50f10102c0c5c0a40160340340502d507007a000c40d0020600c80c54038010003040620f440204482d9480014038021501030940010b80030204081d038103a0140038184600c0c0041a07801d00c45511580b01920380c0da0690119101000c1d0707501c420703c0e2040c0540902814001e4080f40c1400e40c1c0b5444e203541016079030341d200e6502d2210307d41541d82443c0b030201a44101c601804140c0010f558038901810400d62000d0107455010061007a0301c80d042e00c03681c1c1143c1d59180150315603540761045103583c00304000c01c02803481d560b41c402000e000020b0b5003100a4010132044072192140343e00d4943d07010016150840c1680128000c0e080514200a001d008203442426590700342410a844141c03414040010107203002001c1e0800c1c6045044014415401c15540c01c41109a8807410201d001c1d400d060b0f150346003541c41d03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 966841618 1250 966840368 966840389
    0xc0905090a0803090109020607032a08221203170109090c0e0c0c0a03030501050f0a0308220305030c030315010e03100518011401052403010506072a1e 66
    0x351000403800e0b80215084081080045859807042d0002506607010340011004140440001d081070020f24200c5004865031101c42d4407130724183e46035004144920780300f02804030032040303685003965541d00c14003002e015011000e03505500d091501410300080b82c4086070f00d03d0044c6e0000225a1b05600510810b280d01800445005141185500c4155406001ca18035454280420301078030b4010003004a03614001e0390301184552500c1c0c1440019014143d0850140084003c00d00200c1d08980484a59182c0700040031822511845810145000380c2c10042c42400000f400c0740200c003001010754054012080313483c042e11054001900c410030358a003410b806800c20384142d18850720702d81c04194014240305405041040a60009003104c81055035150500400d00042c001c50500d00403114006042d13a001500842d075164135242c96000500c103162007034000007040c00400510303001d45913164000e0881c07450000003114551400b200345000b03c41600d00c40c0342d000680b60005941310700407078264004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 966842868 1250 966841618 966841633
    0x2090601021e0a0629060a051207080f060d080f030901060f15020607030e0d0e060426010c0c020a12020f10050901032d051308040e04030216050f06030a0f180c090509 73
    0x2070001039008400044103109040c40304103e00d03071400c10462b1203082d01da6610a080d01c0d0064201c940c41101401d254010100701c00c000740001c1056044551045600c08626104d82e980e404180c003400207a041410b06c1d13518004c00044014212580c1e40c1002200e03000e0354507960b242c5000718215550030740e0031401e5512034a0102420b034001c400195113204007400591400f510386040c0c0c5c4100620040000805081100340352500d1000e21642d0201c4640f450008030500039500041c2c114144c40c01800e80d41c51540310f01004558402e00301103a015400b408040c205900030902801385c1c1c04c102c01c1d40e40464142800349078807071840761740c1100c500001442d010400b80c55108000040a0040414000580c0400ca08022400c52030240004140c040f80166540c60b19250003800c11078001c4034031512071400d10080c071440e607480600407150b1400341ca07860389980d200b001050251210100809429181012442c00c401e4a0034214000c103004409500c0e01507030300c1c0d64032000c4500c11541111203400c02c04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 966844118 1250 966842868 966842951
    0xd080109051023032a04062402010615030204140a0503030f1606060306060501090f24030212011e230108070507081602040e0105090a02090601021e0a06 67
    0x45103401c5903940d034034800c0c3d070f083e60000120785062140c00c0c060f04003946805200c1d803828080303401c03030209420564062080e02d141c6400c0b04125104a00d03a640a60703040d0b60174117041032003540120001c02030207030403a000c140c040030090002d6009001d10811807018014184a0f07090048441c000c560f4040c000b540ba11011090951181e0050348800e05001c44002c00b0700041a0280529000f03503018a100142e484d1911001403c01550742c0e01000501c80e190740708100c82c200340c40d41c8109170212500300c02e00e00a071301d4804400a104241c403401910351124008038603941c4807041440e0060350851400407a81d01c5003e403020660f04120840350214200b40c482255511940d105908070704d25013007081c05c01803582e4450960f070308000c120071100308101401c0c1003989428000d4450f0f9008440080005040ca103e90faa117400b1041e00c003034040c0041e1030218500ba44200700c03e123013001219108450552080c46110b448103040d00054490f24200800c100c900b070510324002421704607000c8460a0f20200c1c0b07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 966845368 1250 966844118 966844139
    0x9050f07050a030608030c03120708070c03050307030b1221090604050f0a050a09020d1a031c0e1c1109090d0f02010f02221a0d0b0406080304080d0801090510 69
    0x40000c0d0b0805880d4800050790900c2000941024a07201e4061902c40c0798400c0d03240d0b00030704020300400800030070384d040c0f000c8190450380908101d6010b242882d030325030f00c0c400140c0141515003401500311f40c0e1910005c81e0100003140602182201e1007994601110034003407900309000d00408680d002c00100410042c03450188501200300b2009071079039894643d224009140241c0903409030600036000114011004034510030320040c03d1407141c1401100708024007003955003d000710909440010780059080b0180110030f4100d18910080802400b55400100d404280203083c41c229000d0b8540d030f031051800e14140b031959124001c10002046c0700746411500f241d825004401420540d56540100040303030046000802c3e00c4844044207868106007052840380c2d003030440c1c0c0901e0140210500c0c00001441d503004841141c244c58101103107100389200002e000304407951102e980782c4800980007440c104041500940290142c0f60701000d40e03a180100401e50340c04980402c05051b40c02814090203094 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 966846618 1250 966845368 966845377
    0x501050306190e07080604210206010f2603040602030a022802090a0209031006061709032703150f090a0503030a0207050c0901060509031e0309040b030a1b05090109050f0705 76
    0x1200304070381084c0e82c0c0d404443d09011040d201503c00c4d0310404244801c01c880c4814903840d001551008004961400c0f0a201280300b4a0107503031101d170300d40340300e461642d004003406804c1156403205584c2e699640b100081e60700c0d804000c165015024628450015012000408400000e68002c5803407140c461750801861030402441500002c0d400d101c41d0310192003c10500d803101c00000f030001003160800038061701d6006121501104506d07010100b01c0140b0000c015501040e02c0301e0031103400c09014014440c0241482d001c1e8a41500c1443c04c0b403201c0d103074910807a42c000c003180352040281d903ca403d0f2968889060240140c5107034010030118103c4006c03580200b101501130340a4404484180001940c02e8000307a0160f000500b0109030f00004d40380c107101e80003110916016080c41c0101c146000c0d5220b0080c0c00d2030718419566242d410455440c24080300c210359601c40c490084101e001d400080d8054103502610f4000d402080011920600d0740c40340d2030080f034005e040000c10b5034568500b02c0700e0b40d02 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 966847868 1250 966846618 966846641
    0xd11010c08030c03190e1c02030d0e0d110d0e010f090e070c0201030b0f0a0e0a1103090304090f0b060d1532030109080d02250f020103050105030619 65
    0x180005500040341d401030207503000b540c6a864540d40ca061090060411840580c5c8200c44a458040c00c40044400050b42e41c1d07407000c1d0460300c0001c0c1c44200c182a4254020002c1011b1030701d04003504e88c5045c100c04102d1484040054a031074220003485c00f686940c0d09000c1c00b482c80840d26585590b0302c0c0b907005841e008111121842c01103200c03a1504044042c4050079904500480d000038510011903030140120801000705482807200288440c00142d262040384c031405551004180101c1d007044916040b0400c00c1c1000591140e803800c041e001d0f00c1c2e49502c28070039104030602d80074600c41d00300ea080c00368000f440c4008045901301401890303118010082c088013648030381e1300c00100040b180c0d00c2006034800481107980d6028038403081e9020901405080c24414441e034981560700c40015032440650f145200b107807000584400034800f1700c00c00e214000005100c2945a080d0702d004002c424030030011494802e9909008999946042c1551980240e407060031901c5d055074082444041070307100412445 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 966849118 1250 966847868 966847877
    0x3040e0c16140d180506030408070b04200108270106030c2c0105090c0c0106030203150405100b01120209130c0c0c060e090a020c0a120801060e06090d1101 68
    0x50459601d6091440152044400d10001032041c03001d8041800740c5801500141048a05401101d190303003070740348540c01079a20401000c404542440070160940b000140d1050081400d410b203400c040024001d001034001c2010240c840d80f400e036521880c5140d00400791302180c0d83c0141003440c400da802403c201640300e6650340c2ca11000012812600e4101c1c001c04940601500c005803050f0104c451203032203019144006a110010021500c41c004d0007988494900c200c1ca440b0004070120901500d610362010303601d8031a21482c03000240080c41c8a0740658801c504540049043d61862000d6410481a42c0d000ca4040300010104003483d400400c1054401405001c17a002030420401c2280c0342c02401000050f5010f00700401c00c18802150383c041e1400c0e00f000202c0e54148070004040020040219030015004240150741c0b41081085500742a8401a85009003035420b4000300446400d1288100141d41d2449500c20b41c1041402c450b8503903405440ea5018000c2610f82541908900e032800c0d0401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 966850368 1250 966849118 966849127
    0x90d08070507061d010c02100806060c030a03290108040b1e09010504020406080601270204082e0608060a09031e02010b0f06160f111002060103060c050403020303040e0c 74
    0x45042c020070000c0c02c025224500c0702110603020045007560650010706001c804540da02c003503510141d455111a040380f610081c1980d409022400c0c80c0500e90003202c034ad220126202d14080e030580c100c000d01308690040f884800700421014840300000819981c04039042c100410f0115400d40d05241e0700103580752059109251442d084120103004481582c03850755514103110440c5054040e400080800600904095042030030b003c508140d404001801d011030f03240710000c0c0c11100d0b01501d00810008081e00c50454201a0b80e050319004101c144101c034210b981603002d0740e0940d1066500b80c1d28182d005016950712f10901034000c1041581c1a010700900b03558640902803c40e40d160000f01c1e50758000708000c1b0840781880b0440030b13801c101c1071203480e0622014050014640307000021540095085407a1135460921511911911403419001007540c401d40310566000100c560490744102400c000c40140d000c13046656000d107010095150b00108800c201d143c1c0448041d6030000e2610041d40c0c0761 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 966851618 1250 966850368 966850373
    0x93109141e0c040501061e020c060712030e01050c07020114090312070605010929010c06021b060c07080f0a02070824090d2c0604090b03071703090d0807 67
    0x60100c0720390141526201c800c0354a018240520180c0480507050701c0070f0155505108000d0416100c0458854030f015000c880048128820000c0c0380c0b00d46006414641d80f1001400d12045a41000340d04101103410540c075034074014014407070709109030102030310682048120f07070044401030121130904560082c1404541400da60500a07103000c0b008110095585c0c0b04142350000075100d05a11082c6014030b031240b01a4044801e480c410003070341408086000c20ba800d4001a29800240070018001d148040b4604070620f5241c038441d04181d01c0201164000d99803144031904600c102031000b02200814800003c0e00700d2600054903450b07440d8010f40b4880c80c0c0b9030303480d03070300e0030a04034000200c0701c1003142c185a4480b100c400c0b246e040302e40b01c40644250300740d1140141001c4444600300d01d2034045000c2c502101c02440f00d907a200a1380042c920b55686a5400004002d002a2043c4900c20f0048042c0040d41d02c2039220b0703c8410f08420005075050403400c408000440c4100c0300305861420b42003003807100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 966852868 1250 966851618 966851623
    0x20409060b07140307030e06090d0501140601020c040b0d0807051e060604060909020906010f03060f18060e1b030a09060c110f19080a050f07030509310914 68
    0xc1c0c580720303404903150516428030040b00712041c910000b590f081004444007080d0b10640e00d081101055640594946950700800c0b038501c00c2450103401540380c90401600c02840c5a140c6008480903400c0b41c1041e1100410042250280020a5400450000c1c1c010014610002502c401c034080c500f55404480340005aa03804c1c50b1660008009070000810002189414030415002d4100208204440001030b03000c40c2e02180d000d4025410300442d18a10790f5202d12130b42100010380403844440e8052541e0700107004207101e0440400e03040c503040400100d0300044442d1301078450704a00645c081c01e1148501c010240f41e1020b4aa007100507210720300030006c40c1c11030140084d050000d41d40c09003441203900ca00c90411a01203001c0380b142d04111000c158683d94880103641d600c4e000004107a075201058415111442641482084d40c3d00c00b080d603078141500a000b80007039903019140d01d007001c86ca2040c040c9046003002c0d452034a00c05007043d003440d80c081c10342c002e035100e522480c10360500e20b513100c8a551 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 966854118 1250 966852868 966852881
    0x6010911031515161502090d06050406020c0a21210207082703010e06090a0209130c0f0f080d0f0e03070f2304022a0304090c0801080c191206020409 65
    0x21303030500700d00c00303141004100075602c0d1030103030f04403011030034810b203040010090070092101500240e12400810140003141d811210864805000c45043c441c0ba442d02e02c00881c5154210003201c0341451040400e1400360102c402425801e9841a09513508085080001d400c43c401c1992050000d0007044020300720b20340300c2000360011400d405c9416098004250079036103e001085c42ca03030041c4c1c06014919500113038000c00d02c3c1e03044440e6485590341810802c2034013006070300548180c0c0c075007034005144001d041c0c220081e280d42c88134280c2c0c51510b9082465881300707100f0f101c9001400b0700d01809011845142407086000d0010152281150b40c0d6103051440141d58010400c00c02c2c1c46110030032941410170f81030502440c141e905504002480900550f0110a4810010344c59880b114601c2e9000b01841120050300d81e0f03200c01c001c0c9420721500100580c1d001d000300d140f11302c10a40c880b500783c585135a080107644c020000f1808103a007802115076290060940403580c1903024080451060494000c04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 966855368 1250 966854118 966854137
    0x60a020705010b030a0803010605251218030506040201050d2013050102121b1c05070b0c2b090218060f0a12060b12060709060206010911031515 63
    0x258550032a030038031600311100d0168051182e0700204512000417031480950f8110b43e100d0500c281c072010741d0b588168208a011390313603580c0b800c0c9480200c0c04101301d10110300381c549001d0780c3c2d2103104900001c0c1800c20782580c2c0000b0302260712100005d001907201e00024081918a00d03000b107541000042400ca0311001c4814040b04844080740500c1d110329003400e150000c10091000b0700160740d000801c5002481703620030032025003091259082000c3d0301001901c814020007a142c0c1011f4130001340013407880d0080c1108558004251022800140010b03080e030b03506d101082c04812420001d01c51803a1070f980030303400b10911103480314441c0700540d441e00304031031042035601110001446c0c0130080142010042400d10310803400d00c0d8050042036811880043d210703600c240001550101c0b1800142120116609000e2a2003140c0030000e0041d07004c4c0004007100c081d038080318202d903240c440e00c5055072600c4080803170100040c4009466100000044040110050140c6c07100b4100015004010750201a90 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 966856618 1250 966855368 966855371
    0x31504061d15011517040204090606181523090601030e2508010525020a0f0501390c11030d080106180b040627170f0307021f030e060a 59
    0x400502c0542010850500000e01e005105c81c203076005000194000684040c0c0525079580e1407404100c050750002001c0c019042100945255440303880d406092410708910b543d0b0761101c0d00142c3c81612602c0603d0902d040c41d00900e800e2492824420341480007083e941c10591201c2c2d060b0780910003440480f00402c001140d519080615104180b41482c07070740c1c880603890389808100464005100d03584041c84c1000204680742c0d48541c0422464250061405855004c4005951007080320540c081118851880414401d03095a4a0300c0c40c600c2055848400f02017400f03280780f48911b84a01d40442c0a1880b0380d00c140e108800c00380100385022449a0703070b00c01181414005101081d0000800c00087c6004c07004c0c01c44045c10300d4101c0b02c05000d5031040d4018400030341102c0b20b0b690607180c5a420380815500280740c56a07034420800f07826000360a80500300d401038014200d0070311408800c54001d20703005482070780c1003413413001400071010000d01d0302d03c1050750b511800ca426800600045005883c0c50700c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 966857868 1250 966856618 966856621
    0xe2409130606170304030f080c1902010e0937140711030301031a06010302090d05010f060e150f0d12260f01060503070210020408010606030506031504061d15 69
    0x500e68119010b0341c010980c818208030f211222614000211002c0d650b001660a4a52602d840e0010040c06010060021805483d04003480f00032090150581c11303000340d0312810000350440901c036184405850041c064414440c1d4802caa4100e80141440c14a076228607a240036018540c00c81241c0038008044036a000c1c0c1e0003489566a8010410100c0320354000155185524560b28100710301066849451481c000d2000100503a029505403125601c1c00707000800410718510b4264020680d00342015031040c60010040380c0c40300c000007600d00c500c031144168141c4480381d20070088081c940c1d10b1070f150b114240d000540c0006e450580d2782c102007449030b1280020031400f40366005c181000103c10304040140c1404000000071013041890440b13201c0d05206c0c1c3d890321000d43c120300b05601901e140b00111b00000d0005540034055000e081160580d50701085139441d10020161609000000207191028610200d03003c01c0709503000000701030704d104101d4215101078110b1414460801c44801d041d050000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 966859118 1250 966857868 966857873
    0xf070204060608010608060f120a05101a010509280305030a12091e02120106030803010e1302010504090f0f05130b09030306030a0b0a090b0c04060909060e240913 71
    0x45401401840c2003581c803545c10140000c0c0550b400801c0c0c0d61049020b06c40f0044581c0740d040e411008003048009840d2600207500b021551940e450501e40c80d030500e44155920000350000c4802e8413000c0580d1410b00d0000c103a0f04104907069006903086401403480c0058564800c034106c104019480b94001d15141e50520f80013400201c0c080354001e1907241400116400a04c405015040301441c23071032010b0300c0d15030134000700380c4404040c5048070b295803900300080f041c807c07210003550481e0144d1020101e03030340e00e4205d072141e0340d00400c10003408254140b0017842010080d400000c41d40795002d000090681c4001404003e80300d0680c2c8802c06200c2c820701c0a414401d9000d5043d5021107404000c40c0795003040000700b6903c51030300d031000c0d01545040c80450b08043c0240c2244040f29080325141189041240f4260207980c014801d000100740540e0380019003c4c1c96008140840d1103821454030b0303a9642c2d020004e5000607038070020840c07030041d507401040b564500740b85502802c070480c002440c141d80391 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 966860368 1250 966859118 966859121
    0xf0305221415011409100834080721120806090604060e15011403040b0f090703031d011b060501090b0f030604061515180e070801140f03030f070204 65
    0x700301d0341a800014500512280620200310f5044d04400d44a0481d160380d01312002e50141c00b29080300b1034034040d1010a050580310002074255444640c40c03e0741c02d86110280024642c2c2041c841c1104640205030700300301203d008540701b8410a50041c0d800d0081e001035a842c030300058a842d1403404200000d080c4401401c03c2c83c11103a103d0402e0f01c00b000200e0901c4e0070851400c000030714642d4240c02d01e4401c46800d911031404900e500c602048403d45908051800d0724a04c02c0807100304183c11100d1001548d01034000400d86c1c03c594050f2a503c1d560b0000d080300721a03209001e08541d061041030f2071008244c01f0804103074070300c0c28007070280007510b54185280d04061f100c500d40315a05c1a02c0002c01480c1954010030104d40169200b180040d00030103a4a0180d032082c695440b0011880f240c420510071541c029044c2d803940c05044062140041d140c144601d241407040d1510400505540e0060103003030409810044054130041044580b1681540000c0c0b850340003108040c546007002c80d001085081c01e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 966861618 1250 966860368 966860383
    0x14060708101215020a03061205010c020c030312010303080c0f0a030501050f030c15210103030e180129040902040f031b03020d06020702060706060b0304030e03010c0f03052214 77
    0x30085120360b05819128180110002c4084654440c1c0c00120115100c0c0240e00c0361008001d03506218039246940e0501500800800000300054041e4441007092490080115682c4540140d071214545c1d085803030884494400400b000b1807440204054540c0c007420340701601e2034074220f40c1c0c00324040d81800b003404014200d0300d450a01030b81c00300c0310f003007140d0f0b844d0300421401c44c1d0407107100340e16a09240c032081d100300070700405102e214003a1360000c020305900c1002542029070544150f850110211101032150708240b0480b05008115035240c9600000f101400307201c4094183c5260825032140c4072401264820f50001b188030411001c20010001d03072411140d40400d11150080d0200e1664010407140d03582104001c02d85036000844c4e10440d52500d0a441c049508001c01700a1701e61107004c100c1082d0702c203a81c144d01280f00450074008520f03050094150411150782d078011100c1c1141c5058021b490003504100c42075002c0d0548904003d178204588080314014a10108088a00001203041c4800e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 966862868 1250 966861618 966861629
    0x14070f170d1104151b020a060503150a0e1911030a0b01020c150a05031f060c11030106060e10172505031003030f2f1203221406070810 59
    0x824081089a0341c00045001070b10513a03418081c01030701855a07a154044000c01000398003103042d080116440c2e6001025510521402c800070710402040c01c00c00c1111200342c801d01e0b40c4800410001a0320f0310440708806444480c1c0f0401080a0840c030310b01140982040750421010741d038640044480d5a0304100c40c42e61641e05440380590070a5002c1d031030446200d05441c0e4010720100001080009010101034800500c580c15400c10454a800c4010040050f40c80c044d143c154100704c00241d14a0103110745000c07584c0540740c8042940c4020188110610f02c0250001481142070b0002d481004c01400d40d841440883c07e100026407441031032402c07400f04958084100201801088012145079142c4000c2c1d94050515441100d911002118844001001001005020700d00c0c2006580d5a060f00320518140343c1c181d61143c059111305070b215006c2120444070910348026014041071114840e80000360085c004191100101104c0c5842c1200c00e03030300c20340080c2d03004042141082c400e803280c501909 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 966864118 1250 966862868 966862901
    0xf06140103061a1b03041802090406091503060510120c03020114130e04020604090e01090314090109170102250201020d110c090c0d0c1101050708060114070f170d 71
    0x511040402201c3c0c004c0c00b884030f40803283c030721607484000002c0050f50014040c43c05802c0d0420f9018000802035081114020b000d642802c6000c5642030b11405442c40301140080c2c080c030341c0b51664070b40002402c3d000d0054a00810024000300c0c0b040c00c211611640d40e4017543d1001c0207145140300051004040e040c0e90031800348140098000380040091140844d945150b180c0312944407800010384a2041c0d5010482d6589424201c004101040d0000030105009481c0c2c0180c80c4401c44120303280d4894290070341d0001319000d2050000341c480c401c00140b24903e0350001401c100000310761603034002910b6000c480c1e0783c1d0803800140c1190ba0400c02e0454000d90f41c50140c0ba040d0003410150384d64107a91030280e04c980b444500080980d2510002c2e6545041859000d022000400c08058034001c18001005601c1d4200000503030014050bc0039503000d9001a510220080c091a880e2100340d048103000b1148220008292004910703404014145141403910341d40d034400000c00d8a00032200511032014101 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 966865368 1250 966864118 966864149
    0xe0123120c0720040f0e0f060906150118030b1e0603010209060304030c020102150106090905090607090b13030501062d0602031605010608060702060906180a030e01030f0614010306 79
    0xb4800030440e54a00c4003c92450702954900001401510801c0c28540240e8500341d54162190400604440105051801d0300c80d42d8444811042d210f06045030115020700803640d40b401694840c41a00c45039881481e00320710702640b640e41d10b00003010140c030200d158100d0703900084070950140383c1071a00034004400852401c0c0b0702001107086400014400303024002604000000c0d64000e00c803074480007040d03114030002580c4945e4040c1c6606d282c0e0041e40340c418500000140030180002c2d0b198040d041d00d86440f04454a841d11100c0c456024070112075842002c00800800900b0074010040030305a1340c9070152010301e4400540385800000145900500c940340d8080050341d801108807a1515941e804643d4101620301304103014000b9940040f050344502d030108514103602003505400f9046607010340340e0607211448240030480d80f00021401c1070b00105040720009020b1070300b002d8450410305003c98664805000c1c6403c4680642c040c1604480c0070503004071940c1d040c03107000040d00203260442890f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 966866618 1250 966865368 966865373
    0x50d020f072102062209020318010207050c060306221b0e01080406231311030d0504050103050406060e040311060c0f0d020304020d0b0a0c030c110d0e0123120c07 71
    0xc0c2035404042c4c0140c0b00002d0880025030304c09482000205a07008808a107980c0e8880b0300c000350300c04c480308600121010aa120b007402c042c02103400241d088802401c0a00341c03101003020765840038251035403112005036080008100d181d50a20b2100741d420f00050001c420040c2d00c2c0525130040c5156040001e02c4809401503070700120002d0b000fa4201000103580e800410300840c80c00c000441d03c140c180718040c2004180d41c490035006840d6886140341c8a01010510149a6a40307030200d440e4021810521041c0300d0340d446584603e50240c06120082080d640e00e0300c0d0f500c10000b040d9420b03000a10428041c050700403040102c0340c0c03c0990500046d01c0c00f41040203920644c05403410b580300642d00000410295601d140c010520240c020500107124104180508001c040c20f5407000c010070304003100014414012803080d1716004c00c50002d02207138070745690101c0d20f4139481000d403810300081f004299003d07451040380c00070300c040d541c038001d603610325640c191810400c0013007402548001c20880d1000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 966867868 1250 966866618 966866669
    0xd060c0801050a08100902010e0a090623010c0b04050307121808060c04031b080706081e0601080705130314070f0f0302061b0109150626030322050d020f07 68
    0x80071117420000541202107200407640c0c01c00411032650b108280000c0492030480582c4003804490032190080c54041800d1401c441260074540301e01c3c0414000800d44010403003001c0559800b6108406680c504100350362081c0524100c401c12000080b244138040c48400e0040c94442c2c06840140010b00091a1204012807103104501004081c08610003000c40c0c40307140d18102c9d02c05485010240c07004140c44103c0180800c404030b89a024000c00300317408139001810021040e0103441d0607507404403555184031080c0c2d226840700e01400013a480c990380020201c0e6000900392f00c2055468041d0180d245407040785402d4642c10340002010340c82500c0d0400042e42e5280c11203883c08400b0801d50b41c49400304c0c01843c010010418044c00140b00a8000001814a980143c0c01d89020001802c16041d500340390904007070b5040301d0070304140e0080002c10003110070080305140707840540150459003852956032a00303200c039260704540983c2c0036109a0038202020300c502c0b005081e00d4501003031030b240c11301c03850f00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 966869118 1250 966867868 966867883
    0x4090c05130e060928020a121a0408191107060818030a21230a38060c0601060302030612150a06090b03120d0b0d060c0801050a08 57
    0x500c5240304241e02024000590462400840007100762850307490402816926040078140c1c1c0440182c1c50302c000345901c88080d180450250f0060584180942040c1040c0c1401000e624195280c00400703040c11303030b401c0d914410240f04505c200a020740713500b11114003051100e84c15052100b4048251601c00c0c1500000420700e04440b141c0c034240e02507886640c143c1d8094407003202c40042d60b000001d00c83d0030076a0411101e5410105491300d1940d078503100f656030340c21030311882c00c2403c0c40841c2420003412a10405d4009400000c09903000a80e10000c0711445440c400e1000c55899100c40c221240107281507202e807003510110203071203461800c1c01820b001620f40c0360500400c2d040c1640400800d0307050716004287c04601c0404000c03a20b00000703d030008444a0350032140951a0740c108240450700d0500d9010320f42e002d03c00900181800780c1070400000c16500320144505d910340e640c1d520398049590b40301310300706424040c1000064500c085a00200740d00c0c0c050f041a4010b070910380080005210004948 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 966870368 1250 966869118 966869129
    0x304060f1401030f1a01120f03030e2508010606021c180b190201110d020d0209060f030a0e0c0627060f0c010501090e0607050a0302210a0b04090c 64
    0x1600050003108500103000540001814010000021081009001510139114019242d00a41c400f40d900031a03c02c2d40c00340281c0c00407103446041000010300d004000e0184030f1007800e020072400c4004401c135161460040c40c40e8a030880440c465841c0808041510000c7d1507540001d104207030401c0c1e170180d9261150440400d004490404180b034480c410310b4030418001d050408030b000141c1d139143c40e00040d0844a1200300c45a100010707981458014802d8074214002510401d00302204410480000c1d04100603c5594035003c110301d4009503500401400941050028151642080c07801e0320102c82c446d0380f0341d480d942e2041e030203004155100000c1c0c81c075441440541c00c542d82c0080d21541041c01516180d290005c5010808041c249501c1015140c8204000c001b00b010703aa8440b6010700340c49450000010582150021910b001e100d400240002056810094601300707000312502401d0451000d0783d415042210309001a0070227034003a1060f12403084400f804003440c41e0712044610425407151 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 966871618 1250 966870368 966870371
    0xb0d0c03030c051f020a031811060d020c0a050f1203060603010509060409020d050706030e0604080a110708070b09040b0607050d12090f14060c04060906030203060a12030314011406030406 82
    0xc180403c10b0400180c04501d0003081c6450328091900845070281d0848001040402c0c01d080c40400c4500305da20200e80d0442d0009072000406410505018070ba901200d070f13010400c0e070208811055507804110912040388201e004040351100080080e00380a0380180c40f100200742003051280340ea0700c040941c0d0560f10112a040045d445220016001303100c400d80080d00b040c1160021401d1101c04500001110481d403414080300c60f41c0405280c482004581c000e042000601c10f1208607481180d00134002c0e0402030031100b1950719004c0b400e281c0882c6030301103a4109400124034800d403e090107030503640d00382904c0c614107041440e9940781d200c501d123a0600e01001001e406071085110035400040030701d900707c5669400000b2030b0070080345110502401043d54850300022414030600c0d0b804803011036109039150604981045011070181d03001400715640b010200101103000c48042100010151003a100020f903049070180b0005200700592008103140f501460405258541d04201c0340e00540c4003a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 966872868 1250 966871618 966871637
    0x5030a0b0f0d0b0f06010504032001020c21070906121202120d14010b0f03150307090e0c0415060912020d0c030309091a1f0c150b040b0d0c0303 63
    0x20503441801c1d000407075400b070389048144003032110b100c0090313003c0d00404a00c1031641e6240d10040d035952090b840000c0134908140820140f4000010841d120440c0c1481515030240d141e10006909501e80d034004190310f0404000380058480c1044004001e0145140038400c0f01c1c50403a030f88030a16180343e009003240701d0005180e8003840c4203000d14a01070342c1c0c0182058881c9400404d1000518501585140d042101c0c0e0022a8092000c001d0303c442c104468882c91440e91a421007110307000007281e142c0c2d00762056060101d2000d5080c0500160b0034808401010490400000c010030f650040c0030310b1401c4c071010b0005000307a6620007084826107100d404800307003640f014808601e040c0401c11001c1d16240400001004155100d040581181c0d450300e01481031410592a1036040c2d03080d0f000701035004010940021060600e00141d940403441d0342090300c50900c0716150083c50203c031080c00740790155210411042480c1c036109040340440180e038040581021aa217428590005000140a00c448102c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 966874118 1250 966872868 966872891
    0x1312030c0605250c0b06030c1f050c060403050306100801030c06031505030f060115090b18010e040c0201050601111b1c170304020f0402031e0a14092b05030a 69
    0x7180306100d0000c40c000d2a140307014040f0001c060f0140c0c0441100c2e0f002c00007021943d54a0000350031184e03810010100c20316698090078018842c04021210300c14001c0038002e15000384da00f400014030076402500c400d9541d01e0700794200090318840031480400c0c412480014004940c6550082c0252011814006058011204140c8039041c1503880140d062040382819803510a0104006040300c042054412003a0030440c01074030241054010601a04c200b44204a84034840503d0512503240c181400c0326841d4444010405442c80c3c0110400980e4440c02030110741e507400002000b0040051014208400c01450100646030040200038415003c80b0001e40e8400e120380180c01c02c46034080e0080c4c040b01d2220381c5403446a00121810b91182040402d88022800c0600840348103a841203003240303280880d821098904180607041080d410754448403100301c81c0d020f5a84034007485401c0c009040102c4c0ca01d400c00480710000e07000300349919851040c0c0c0b09040d0040c0549411103040314001c1001000503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 966875368 1250 966874118 966874141
    0x41406010e0f0d061401050114090d02011202130f270504030e03150603160e0f0c1306021c0203040e010b090105130909030f0e010f050d02130602031312030c0605 71
    0x9044180d1003006401c3d068100641e40d805501d03030b0600c0c0158800207a82e2030005464a44001134010f141c5a41044103100c1c0b8503120001c0d0540501c1410143c400109110691040303810014110400070301350780083c03060700810780710310008050000c001c4280c41c1a000503004228001c904141e40e494030703400441c3c100341c01075410b840119005400c6440850380da203560841c8800507220a8001c0c043e10000d94262a1520000820341e91025240506038035017207403880e24510700819621400c14107121120001100607030842c010070a580c001c080c00800828001065045110b4040541d0310400c010894000125040c2e4115000304072503a491300d0b4240c7c01030341c4c140300f08141c00d100c0424010011400c003040394040d90f480c0d8066640c108010f00615810f44200c811030b0011804241407140001c5002e114600a16019005050140c1460004244062922500d801880c0960000b00c6c48040000080f90140300800d001d590003050300b5800c0d14080e00300c0d40f1052015088a880308001503080109 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 966876618 1250 966875368 966875389
    0x4050a0b040207030906030b0603060907080a0f0e1b060c1f02220608060a081c0908030d02122208090d0f120201151520030a090302040b041406010e 65
    0x5007065544041c03e2400134200d003154080d60002c2480e0030100ca40c507060a9058038482c200152481607151540c60040c0d40a02c8004c12103000700d40c03680e01001317508070706000d8550072001d808024041c4000800490b04030001415401c1c0c001d00ac1413108880c4c010b00010008a6510005544c5111018601d045006803040441c0240e80c103041ca103400301401d542494038000c6842a50f140c064a4840340204044850a4032800c10703158007001c5842e1141c000c21174500b0142c042c174200101100d40c0c400f2480e007960001000c05c100154086000c0c4d0001c050500110703403144083e0b103007507090300c0903045800d140e144184028060303000202c2c51140540311a02c40c503000075000390680503c034070030b450700d040d990900ca08520700650818420b12540c0903110414420340301c070406a120040c107800720803604000f0f141e9040b2b0b03043c00201c81d100200e0b43c003400144910741c929030340c3c00d00150075030040c841174942080056000d0f52600c10218520704042d0b4901e60010403d181080c500c40ca84000240b88885 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 966877868 1250 966876618 966876641
    0x5030909040503070c0e0402090112020a14190f050a0f120314091306090c0f090b03090a14071a0f07020f1201020d051909031b0606090c050a0905190504050a 69
    0x1200032001c146e000407038415900c6071740308407205001c0d0781e203d0703d0702c1c41a40304048000350410f6403080c1c24011049454801450000064000c4400035119240758064102c16403200d520f0b4807094105200700c0c1000d466070320207401c01e40041000d452504a944c0921069008040d081102410402030f048000e401100c0f40114010200006c41d1b4090b03031161b00920081c81340500545c50b0084030159540110303104019103546072510b40c0e04a01e042824035596000900d0040940100c001c1000001c410510404800070900300800350903080c80c02e00b19181182598079542608180042c40c442003d4404a0322043e905441d498400c0b00c89202051b11784442102c610310950011941c901d440240750300032849070102800000044014000399030880d503c00101800140280940f501c2e460003d40b00c2c01003141c417030400026107581d00c12010007121aa50482000a8000280c00040590080242c4042d0004964885004061070402c101c95005480341c140a0b03911840021400c0c58103601c07080740c221 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 966879118 1250 966877868 966877883
    0x302060703020609070608060f1e0405041b0812041e0e01080a0b130b07050f071e0b151c020402040305240705190305040f120f1205040503090904050307 67
    0x412629002c1d4890004540642e40c0e0721070f50400060309881a101d55009034409001101505400d4044c41011010841802a207442c0c0c50348501e42516207105544c03156003e120b044888406c0c00304090040ba5007544202c03541d510132808030715401c000381e04030790071100113070242c1c5100060781001c01c0c0240003a6011407500c0380b0310000011036010204a1500d003d2080240310220355510715845040044a000601f80317108040010302ca042c00744c0024030001d0441d0518909007901070b41d5080c030700c45c8080400702101200001c02d030704204110400c0b0380c020001007041a0f05010340c00118208030007004101101d102042a007109640780c690480b8040d5411a06031a500100c20200c82001000e480d020210b00c2e1041c800109000c0c40741c410360b80b0654900c40081500c0001c00303003c50107400050426200d201020694a0005071500742422a00d0440c2e1110401d02000c020040d0200041c020000c8109041c0300c10000000c030040103d0300703071140450329401c254130756042062a500a1340070042005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 966880368 1250 966879118 966879127
    0x801090b1f030614040e0312100807080a020112020c122a0c0a050901150c020a05130e010b0f090f040c18091509081b1207060204141507080f04030206 66
    0x259890341100c015101c515107030f1203448010a017484100d8042d05031501040d041405030200c00c101c6540078681200d0101a5108250740740d409260816205900c500740c5a403058010b5030841d600000c0e4981d400c060500210f0424840203040d80d04c0d07030226100c910320b20100040c000000b0f5140280640c0780000561624201003012100c155600041c4c0c2c1400d202d003680d8940041c951514500d4641a503914034058044400c21400958001c0c204a10490f4405e084060120b41500c803035807028950304003884042840141a140642140e035918400c0d400b4a080302940d50040d00c80b52109600305108958196599a071070400d0300591045070803541d09050305040701c0060340002d0f082004902c1c005c02d1800c490488608440c1e040301c00c0c828000f007896400740030000d0728140c5040115907030300707007a0155072507505030302401c40c11544402412214964041014000c4115141e8900d10084c000e80c4c420aa801680710340002600031542c00030400400010129134918440c000d4a0045038086c2145845 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 966881618 1250 966880368 966880429
    0x110f0105221809080a0c0c03061103060406170d05090a030501090b0414071413090602040909050c040903080c0703092615010b04060e1c060b031c0801090b 68
    0x92442c1c400e1440c2d0000325940c1c01d8019000e441881da140c0c4e403084500c1c1c0750251170b54091b2018001e800040e07a0000a4150000105000c1e004114807000b14410f109c2d1385c0e14100c0100400c54a05800c01d405590842c01a1004010006030b005040801130400a40b00c483c0d0701c0000341140c07684d40006006d5401c0c40010390402640320340c1b1900540c464207000c56103140d15801943c2d1071603d84140c1103444211415000682070842c88210320880003400801d040e005a00c40c0800d0364055407080e00d485585860190620009010f01000d6a0040b902800404c0f815100180090b50140c10210400c400040135000c15008003104401415540d10180380e00d00904410300ba02041c2c2d02620b2424041d5126551610740c00071403c1e416105c00e2600a820103080c040c0464400c01c074007403d6904601500034030f0000c14201241c4180180c031800d80400c5805107030b41814207005106100b02206008000d8180c11580c001a600b819594600f0700010700d48903440006104010303441007a28502042c0501d0f509 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 966882868 1250 966881618 966881677
    0x3d0206071e030b2e0f113a0206090d020102090609061309050c12070e0310021806070501020a0201060e150f0418050610080a0206040b0c071d07030c030603110f0105 72
    0x20b030141303151a40c1322000c2c00d212090315074100c0e40f04040307450703007000c40c504500075075803240303a0310740b034039003540e6041122040b5500e980480110613a1009a80f2000070002005020404103031510442d00c02903003481d400c1404543c49006078010786100e600e0210303800248102445002c00100610f040520140c01c000c1d100c001d07207511000c03101c22010304c03400020340728034080c180340d002c00301b0082e000f08011400580400001e41103280004660801014a09020780e281005486914001c400044e55950034020284c2181c40d1544440c00002c8480100485000788a6003600101815158050219600c5000a00400325451001c02284080101000b0300000041051007450241e070806482500e80810a60310309071700000070b5110070100300c14031181803500040c14000d1040e03000c5448443c4c55205907842003e40d40d5050f01402004810450342640c140982d264540c81801c08010550130340d100d15000c1c80f40025883e002d0001902c40e03540c164496000c8440000300caa1846074403840b81d201c0da81 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 966884118 1250 966882868 966882949
    0xb0d27020f0f01021005060103020409110309100c0f030c03020f0406080415051b0912030301031a1003020105041202191203030501050f06093d0206071e030b 69
    0x28001e0030107030409070080c14050550494403a0580081242480d0100c24001070000184203074109038003030000241d1041c2502503030765280d49400c81c1c41e880c0d1402c0f890b524988004550462805420b040700380a001341c01000c50f05403e011442d0108501c546020241c010313109412500e1100e400014000544c2c60780105440c2c081e52088804103d42008101c0b1001600c4c0306643c0c038410349146031100d04109050600900c0c61650103004101291701601005d400e40d00264415036002900025010118890583c525405452182c0d400c440c141107400003002c5001c0c1c1e0140380c0784000900b200c1d00175541d0b040e51450301d1034010000d400303046403104869681d030394401c00114042030400001060034580801b080d003074060090410782c2030503000790420481003032a0041c0c200b80603c40310181e1910305804000072500b80d00420003d043c1002d007030028030b0494010b1000b020841d03c09410460101d00c1c149191103d07c1616010681400d20300000315016852526850030350910307407901002e14415200007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 966885368 1250 966884118 966884123
    0x5070f0e06100305040b27100516080411090c1c0b0f040207111c050f010204030b0f070c0b150a0e01050301140c072d0c0f09150b0d27 59
    0x182c5103004960015816a002901c0051512031040002404112801d8034414210344001c80c9910b11000300024a041010036984848500c0d241d07010004640310202c100c2c0c5620101d8904520b8621701034940700004242f22006520950b081c3d000701e004125914241c0c1c42c011152100c0da025282c242d4140b100030f000744d40700d040c000c0070b840b42c0d03e002d03503d418820303102e015400418407047d140c850030800620300d51141e690036003c2d41046180010501c01c00c103400081400100050343c413811420081950301009021900c1e130000b00c2c082010301075201c451034052643c02803040003141c4030b1030380c488001d126100034030380c000300e43d5100082c91960601841c2d04881044d4002c0218094100c001004081c0484804d030046400300041400508a16001d807100c8201005400d02540602c0c2e09841d001c8020100b13440c0c95032803420a010980c101034042008246081040000900e054030162242580d441002507080c00030915030170100854102c1d000d4507070306800529141603034420345600955031000c00d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 966886618 1250 966885368 966885379
    0x20a02010207091116060212011403070f0b1c06083c15040303021e13151b0c0506190201061d0103081804020c1506030a030e010c05070f0e06 62
    0x1600074600d00c03a510094042d0f1031342514040c14015440006400c0200480d07465600300320560501031200c0009001e850703103100d0800c040002408040c42c0040d588c10003800d415510354104503c0c4001011030326201081182490091146203001c0010100340c0c1c00711030540075030600e0340d402c10300386103c0c540714800b5030700e4034400c004c01c0900040a8081d0340244441c0c0e13a0002c1c0e1b48154008492441661241c42460007501d407000e03801c6201ca421080c140a0220034101060440140c809903500d40d001e810085c10300c4179002d09010f00144465901c400e603182104111a100c400d0000c914000300c0906406000c1c25030ba0740d00c440191402c2604050024015481c0c0000803600c82d00e0742e100c49070b050000c40c01d089210390031603c4410b52079200c3e0544a072081c0d50702c9a0b140c056107850000d01014981d91002c0e1203030b509032156000d01c084005049610030342008481d640000e400c05144072904c142031070040021403191500b50320f44038494004901d04c01640c02c00040144401e504540709002c141c03070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 966887868 1250 966886618 966886633
    0x61e0311070b130c0b0904180b0f09012a030c030b06031501140703051e191101200301050406210f03050c19290c0c0a1b090b18010513021207020a020102 67
    0x48007050201c040c00002e008409520114641e0700c03030034003a2b5810200001c0002a02c8031001c08450003000245c1c640c40320070040f0640d2001042e058490780c58110a0740c14144840309a900010703d0343e1000074400300115034601e0710040c55902c1029010080081801c01c4c0c3c0c1e0f81d1b0100d04000e015030f0021010650001e20100c030b201c40c2c210aa500355200204800d50845600304225019a41c01c0070b081c00035903c0b9036a03480c80c0d034003160000e9000b00284a850320125620350400c014401a980d00ba00000c4e050010660510300e00590380e0007122629400014000056107270785411103081c4030b0760140c0c4109114400c10202d9000c000c1e0100c40d8501e2240c0c48030400d9a9000e43c26200307000c4801e4803e8070b540304010014111103a81d10040620454ae2000d5451044c0d0a0740c0d984100310f04c00b03540c80e121116152081c00201401d1240502210040b16400482d111902c0364042c01c44c8140601401000c186500d088411a81e405590450300600e0f100d96281c544280d0095440002c01000d900621030b210 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 966889118 1250 966887868 966887891
    0x6050109050c0a0c080a030e03070c091805190302071701062105060601030b0f0a0602061005180c09011704050c030607080105210307060204061e0311070b130c0b0904 73
    0x200303c404100081c0c44015050565444680d49a048203c201090603201e042c11090540c3c180001d001d880d21030780e05940f04600301040c20045a4910600422000002c0304480201c0c1c80001d00c40c2c559000111031301d44580e4a494224240301d45a031106003aa82c13a90a908007807041034010000f41c0302801e1480346e0040f440880d118040c140703007102030718036005100801d07003d501ca0b402a001d822406020031135580c1c0b641000c990241419403003040103070008401c1c0403a241200d5229001420110740018542d00540c2d8842031269020f002403442c04800114a031199006201c1100e003030040c0c01015995107480d09140e92516508460a846801a0f400044019008042c114181c400140c4000740052600c1d0a90701164401d9030b205010b44010702003200020031a00040c4090f0202e5078484181441d540704e0000074082d00d02c00002818148002e480b1300b11420402d0303500c0c0325001120703a901c5444007410f801130481d410101a2009421000124020a4010040024a0f0143d81c00c000e0744102c2d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 966890368 1250 966889118 966889141
    0x40317040501091701091b060215040503040e0a0f0204090222081c0309050307052d0d0e0d02040f0b010e031237020604060e06090a02060c010e03070605010905 70
    0x5001d52030104002c08014410034448400903102149030000000e140c104130b03111041416690b41001c8900a5401410b20030a98180b201415114240c5200f0955060540d900c1350ac0703000314050107a0700c554200004910020035003041c40e004685075001c40d501c81c2c5404a010181d8459580f072152a88032480031060b0300130800703510341200c103038101a0070200e90524188038406821283c5030105a110500c6a011a07410b0005104d418400d80040250350000302c9100d044031502e1039541c2e06c100343c035800c070040d840e07011805440501062920b00002001c1c40e001908111040002130b40041c86c15040302e5100402d6806105400000d072120807070008241c00301a40c844031411898a10007040c8030400d502c1d860320480d2005140800041d22210700e25000c0d0b0050181c0c00b402c0c03000164000b10501040c41285d01ca00600c1d0b40150018001714902195496603821404200038040c020000300207000f41429800028122010070a403030740e800080c1810b9000d40000e0003034a20039442c100c003044000e1103e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 966891618 1250 966890368 966890377
    0x1090c0f0212090609040e0d14070b04030c0c080a1a06040b01020a08070206090909010b01030f0b09190f020f040510020a050d14040504051f08010501050607060e15010b040317 77
    0x31076006040100244901980c03c1e04a400a6a0003030300c180081881030340d46020350b80415216500511814a4607100104901140344145d20400c604010b100c0c0880d406c1458039a0154243c00c0a86c02e010b400d1504140034002d50b0300c548414024101080308000d180c2d409100c1c030340340308100e9900f10744880c41004200c0f00308400550241e802400c3c81c4c0002903601c00903280984c001030100e400d0000180c04141c0e6444100e91041c02d0381d541300850400e40d0303010310400200b140c030114100040c030649000b18151103000703000c0d81e01a2090046204004039540c00442221454440642d12190716191500050304507002c2c1a2007061455202c0090920016402c001150840000d018140c442c0d401074038003410440c0c02c604800400c0001040988642c040c06016401d2340c92000e0aa007151401252203030035682041031103904060041045645107001d840c070454005000080c241199984180781841035019000042c0e90780c0700024100700301101900031079000d1940482c41e8070449030001c44a105 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 966892868 1250 966891618 966891647
    0xb01080709060806060f070503040923071d132f0f1315082508010b090a0312021c18031202032101140307030b0f0907180501090c 57
    0x107481c001082414410754086401850282c002844c201c4d00c84d105c6940c0b680314840698160344000f40070402c802880c0f050880120081100e80311224440c144c0c00c00c41003014040408100050b0600d08200038541c00c11840d020006101c0d803c222015070603100641070507110814983c0d605030808410b50902e0540017142e5041800075440c2800040070056250054010034034484903e00c40800c51032440e00400c48043e06a45940d04c01d40b03083e1201c0c0c4142e000b03440b83d00c02000d50144100450301c0d0003a060724151003400c00301580360020b41b00070404294030740d403001c0c2041c4101050b20700c14680114544800d89a0011506003031600900182e4a00750044014900c00c0070051040020828004141081a4a510540745440010313401c101003180181000f44100200310010001c9038035a20070711640f9032041d000780c210907245807036500d0784090003065a000d07180c1032400144142414052240540300c42c030501e888855401d82c0480060000340140105945482200c1c0d01c21401903400221800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 966894118 1250 966892868 966892877
    0xd050103120906141e0d23011205060402040c14030a0501030203010c0c1a060d08190f0906080a02071a07021c110a02010c0302011107290c0f0a0e060c01050405010b010807 75
    0x7080c0f45017031401c10340d170140300c89052034180000c0804c05064000d0460210000c038250004003000e090301080c0d18410791045000342d100c80c4180c40000e102007025940180c0454000600801180060703610000e404080c800d42032000003045000101984118141c0780241c000b00000d224124050350079419100000d480782c0c050b6002c3c0000da8007041c0d1100d51001c009080a005030000d540c0d208000c0e0020781000000071141180700340f809500181481c07000038540b805074030180c905440904091303005401450a50303000a0b1220502c0f200c1810203212a0200090111600d01080000e4071103036902c190001030440701400c2c44a8500c100b1807003800c1d205007405420800d603103a00540d00102610300441c2555210000741e0741c40140c02c0080d2078241d0054600d500c01d020424039264070080e002c60081c070083d08804c04d020103900000d040d030700e0240b84808682c2c1e580913034180c10350f580500d40303803410b61003040003884c0c1c0f001ca171040d007000d805140724100074403c000309000103503040700d000c40d60540043d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 966895368 1250 966894118 966894127
    0xa3227060a0207020f0d030206060312181e090c2706030105060306030109060509150c0f0f0a0309020904060e010b01080105062a0304030b090f0f1e030d05010312090614 74
    0x700001c0d030041c81550320040450351000030f03450120b10007000a140950140c1c0181c0100100303400d00340700740500c03a6070000040386081000100700203401003c0c07281c40d0048003180a56001e1a000000794014183c005080d49034601c0c0c8a11710916651040040c03a2000c1a214880ca005c2414165a508039420040c009400c40c1c0c00c143c14000250001880710794159220f203511004680c85100300d03070040c4a100b01908000381c020b24409501d07a80a0100c0318840c1c002c10801925803404400d55540c03102c0f101d0010344d40d0301c081038210050022030360301070341c0034150606000400c441580f00c20242e541020081c80420b203400015502013000344036071038101004008280e2100a0162041400001300012040542c0480805071850f0420f4004540305051a01402a0a00c0402080700d045004400510924549200303658032101000014984400e1102184010340028400e40700d0500010320104451340c1d40341080300350790b41c60300703800c4010462086012840c248283c01400c00d42030940ba1461070b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 966896618 1250 966895368 966895381
    0x1f0b04030201050d0c120c05030601021b030c06030403110118031407020d11060c1c031503080f030c09130b0f0102030403030c111f030b01020601050604030302060a322706 75
    0xd410b0781c418060070003003083d40c06d070b190321414400c802181016550351512854203200181c0b405250a4503001d2068048000030620395000481c80400c078002e60750f003622030f1510b20341a241004080501c00a9508100040130030341c0e5150620421240245d885a001c2050142e11038143d100b00c6070040d400c80740211000010451094040500d000c001c0c104600c0c203510030b040a8107020b400c0048103048481c851002c1d4200c0d90500400000c8583c294881c05050301e56621103201d03116912552002001c040300082080c064a01075890704100640210380c60300703041240000400c04103a41d02d1207841000c45070095544004180c6045e658540c44a5990045584039540c4050309a40c5d807a82c080c25980e020301c2665904424150700c050240c8010038041c81160019041c060141c0010b802400180700420102c0c2d80021281c0e008403480b007000401d00c41d0318582520000380b00740e09141607036207070040b80f000403503810800e0b21400e0f40015960107071810540c04030740b003580e100300720350b0551012020960 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 966897868 1250 966896618 966896621
    0x60f1b120a0e0f100614042f1207050304030315050f0d080d2a02150402060d14090a0606150903140304030209010f030506150a060c0f06051f0b04030201050d 69
    0x7101d00081c04a0b000750f004440c41d54038114200342d0f0b9a0100740c03208000c004541420090107030740da804032000d0003000280c14160080101007008500032080d0700b035402180d11407400486001000c04c1c04038684500e80b6001c0030740250f01c15102140001c0c0740015030304403050300d242c42c9d4064030f0707006080e58111049203003000b400441c400002d8a01583c00c010000c9610621701c90100b40d1244d0034441000342c54810001510081200e01407819074100844000000713404049480c2c0c000d604641454540a1502c1034100500c0b61303491014140c4c01100502c00b055100183c01003500380326540a000c45910741c800c0707a054100721600304000c05d00341c010600c0040d028117841c4ca05500840120781c2459903139000601c01e054207900c40840d80d4074280c3d003032090100520405500000c0310401041d030a00d4640460b041401c00d114010400c09000610001c110100c2e805024158004005101c5420204450702c1c805d40c000c1c103507081503a5a40400592240741c0c605890803203405859080c2070a810510000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 966899118 1250 966897868 966897881
    0x804021c050c1302040f0906051e010206060904061d10061a0f0708160602090108010602012a030e032205180c09040b03030703120617060613020c060f1b120a 69
    0x1483d0325000e200c00305101000b82c6100c80105500c000104500e840c0909110140c40c0031400c1207054003150103d0031940e41c00041c82508690f064650000c159160b040c150300603e5031801a0b0844841d00301510003213500060030089074172041d00d04120007543c40310b6802c014003040c40030750503195051004d10301c400401800382c9800c50040000500e0580320050404460610910444042d0b0340800c3c0e442c043d580c0410350034054402400204101c00022160780462034000910700d040011203a260140c142c401c1d0041d0316000d144604807901da40074602c600d0b141120f5800d1402079010021400103031858142c072220030104080e510f0043e1502c0c2d039200301904c0e40c040121150001c3e110b403000d02c201c5d00c0400013842d44034025500c028071485030461250036075134564401109030140d20a40c0001c58000700b5002d411100484212100e80c00c0220540082e0042400501c1d05024010403c100030035480b4441c0d10401103040d02e4021802c06041c2c401c007074041c9800c0b48140d5409480041c040030210750144 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 966900368 1250 966899118 966899149
    0x3051005030c0901150e091f0e07120905010e070e06040c0c02090f150a060201021b0c0f0103020702030c04140405070503150a0b0a0906080c01082413020d06060804021c050c 76
    0x240d1b00d12143c900031542c82c40e02556450170002c264109000030a46e100110340140c80020f005c43c0450820040040c500007000c0488103200e555040b8000c00c200b000d5108090415440c820b4a900070b9541d0761b095800042250389a0145042414143d034071845001c4030021543d0040001c2550740b51100000c5421400a0480d0051141200e080849946510514004003450f90001d641d602d0602d5501d41d80346860150b82c001ca9024010f00c04660fa039400307107450075040a103001600c40d6100c1c0002131802100c0c00d00560401c0c9000304c0b4004041d081c01c0c0b500d01c40d601a400f11070700c1640c1c441c00e241e80d07451504090580c02c581c000100d6482e00013500800003000d070003000c190b80540c50301c1000d022107841c4e5210340c9090b40000a80001035030003c2460742d010380030600300c004102030100b220f407014a942e008a4070802450602002c0210140c2c103940b801da103029401c02c94217480b8400070f41a80001d031400c0c0d00c5617085509040c40341c214008120f40c01588034011f014030011b2030041c00601c0b406078008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 966901618 1250 966900368 966900377
    0x2070905101712120402030d020c0f2b05010b18010608130203010b040c02031812100506010504120606030b150d080a020307051603030905060a02150402011103070303051005030c090115 81
    0x1050100c000f030f4400342c0300c25011010f0118450609104141c901440d0004a40541d0094078000506588814884140c0071080d180640b01c000c0c0f0302d002ea21190b01034410000c140000000c02414404154400c600d03420081d07819650845400c20782c1440d40109216490024400000043c402884140d030090340d0b034405400890040001000101510b60324810200181d1000c611400300d0282100341e403e09620070390300942201c040350022525862401401403140340ca07079004c143c90f80d1280c821a80100341c05125801307805010301e41500540399038031068400d0540207000c5094004403000b612401c4000070400400b01e01c05544620f4142c104130052030550005100080219000380310740c41e4a8030502480c0300d000ad0030351402400c1104141c1000b80920400d21020000c550001080101d0900701000c5004a0741e503032004031100c140c00c40c28010365000c0400c0c24030805800d038001a0090038048490002580c40b103041c55aa114a10100e99001c11100c004014403000c40c0040403030760160b40740 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 966902868 1250 966901618 966901633
    0x30d022113030602030a05040c09020c060606160f031701051c030309051f021c020c031b070b04030503090109080c0105040626091c08100b0d06030b07030903020709051017 75
    0xe4007022178104403100c500483d2140108020041ca510a1354040e01c0c62401c21800d0170700e440350455072640c00510090041900280395a10f004005084480c40c0d030f0300c0301c2100c4403100145002014240d03c030010051403080100007060b0fa1802209a03408108104444150841e468904402904022a065541e8000d92440070a0740d8030445107075502003c99000035959807005d03011090012000c01c1e0b02000144140600650124040101c0f2041c26204a40c44010091401010304002241c0c2c0002c6040c2c00002e400010000044058035040109807145070115555034a403a85459001c68200d002400800040c891030780901820346900184204400c040d0030481400803802c41c096440c003101e0707801004c000c040140b4002900380c0c0359071700d440c00c0f00c1503081469605203103411030f0140c41e118000115901c03c4100c0c5a43c04030b0b000b1900000d013011346080200000c0d00810803a07a0540041c00340110100704c480340e5000d0070340107507251070720b040600e031922410203005200d04190080714000c401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 966904118 1250 966902868 966902873
    0x7082a03070903140307020f09070504120b0a05060130021306081b0903070303030e030c06390d020c03160303141f14010e0301050114030d02211303 65
    0x34611540958448620650035030400e04a5000b2190039860142e1040050200503118900004213003841a40c042d51140c8402c403054a65000703503000865041e10f503810365000d01c0300340b44140340100780c0b1000400541c1c0b203d500448408d102115000304420140c0000f003094080c140702c0450500c20707000010700309124810f04101605403680448000f0b0070460612018100e44169802e80c4400c0e16020b500d0000a03e02103902c4003e1440080c061540c4c9840001540c030003442114292409107007a50214038100d5028183c5649040d020400d048051840001c0354440941c0443c4c035008240301a8101401c4072002c1c07020b035214540c84d07002c42c04180b1405220041903075821042c80d01c251004030f20340b035002c406030300b0b101e00050018140d90340c0030007900703264000c4119645c103a519004091044c0400500140d41d6070b002d18403566010f42c40c100002610704100c91300304600e01c1048054074040c0402100c201c1c1d5078624403085034003048248a1603003644981c07000070b007207048403a4400100710b43d03030340c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 966905368 1250 966904118 966904201
    0x1209050603010f03060b012a0f0605090a0c090c1706180405070608070504060f1d12070305010c09030c15030f1113080105160309060b03030a050c0c0103050708 70
    0x1e910400740d4580f603000c2401000701e80d01500410050a2030b010000013004506220b54102d185d43c141c030103240c0d810202040c040b150171103030004e40c0c206a00b40f2840c01d1503141e190792000d020000340c03000050b940000c16031002070300030f4201a0b1303125503900400d0106004214003018010303000c42d601291012654a050710404800c030310a602600180c04018603000300a050000020041400c00104000c1400314030781040c0f0040e03601800749402140355400c003680900d1070b4500d141940d40070301d081040c0b4601e0743d0001100815248158020300000001400607150b00b00c2c0e60000a05600c040305013800101c140500c0c000c0304580914010035864002e9400800325800c00d0700c4a030007210300080d004030103894564404000c2000078020045850143c00c0c5240c43c21141140104150702e481880d030500075280c10281c080c65009060301e82d62002d4400c09082c41c1d11031003442c003d90044440c40c884940c000d00c149880380c081ca840d0000c955035109510200255103100801c403400c1e001c186544642c501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 966906474 1106 966905368 966905371
    0x3060106080a39230306090c070b010f1d040506073524090a0c02030c0708031b03090a121a0c07021206090a1209050603 53
    0x41d402803607060a40d06410140202950311215980803506400e0420340150388520304540f00544c0c200803a00c0241060040e6081c1c00d200040013070614031461075010740da82000703a2600441d5981c213140418280c20032000410051401e0000340326007449058101215a002c484503d4603583d07142d628040101700d14100f008103c5c800d0f10200006000c4048441e107821410140d00c1c107040c2550007010101d45038120702c1e550f225240c1c0055100702100005060181010075503507615118000035003180303880001144400c1241c008400f0781404004050440034024581c0c841d110041c400280540c99483c2c2d00706c0c0c10410464070142d82d524031200440f07065844101950030301e0304054a80c207890080c88000034106a040001c441c0303403d4000e00c2454421120585070a42004000c2d5441000b2582456030760300000160303010a4026040e80b45003071442c03510f51019a29200030a055800 = true := by decide +kernel

theorem cover : BRFrame.Cov 966726618 966906474 := by
  have h0 := BRFrame.cov_init 966726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 966726618 ≤ n) (h2 : n < 966906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
