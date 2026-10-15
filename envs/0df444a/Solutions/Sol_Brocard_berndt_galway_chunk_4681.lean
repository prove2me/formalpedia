-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4681
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:24:00.779696+00:00
-- url     : https://prove2.me/submissions/033276c8-7745-45d5-a518-9774a1e1969a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 841726618 ≤ n < 841906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 841727868 1250 841726618 841726687
    0x2152d0d0e010b030c19090e0115120309060e060714012403021503090712030203130e071b0201020303190b041803090b0414060d1410090f091223 64
    0x24481030b10211804840035006d000428411050035034403022015207000e00004d075400180c058465801029088450350400101d4843d04060340001d03080040c0c11503150290b4070034040c0e000729405000ea41001018040c03980d0400f40f202200b58400800d80a81e120559543c04140701020a07002d207038002030340101da07182e005014014001c000c82c2c0c09414400e00078040035103454400303c4a0201c04070120110302081141d40590000408640302074a88441060158240320801400a203525481c0500410700c00d051540541c0c1c0103c00d981d400742c5040c42c4010341c1d140c0c0003c0e19005221100f800c6a0280c03a18090360302d9407002c0541c051580d40702e500e40044445e120301e4000e01e0780c0610300c52035000d0802d05c40013a0450500031302411018502260100e03500074101e11507015036400b00ca9102c46440c40407400c01014001c0e000d420562092a01d0030070a00041e07480d0001c0c0220f500c0343c0e07070042c400400784c1c581660f040384060308001c2d610f0840044d240c0904030001c5400c203d210342000083c0801d20b9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 841729118 1250 841727868 841727893
    0x12f011406060403030e060c030706050a0b01031e0f0609060306020403030201152102041d0105040219030201090905090a021c050c0114030f2e0302152d0d0e010b03 72
    0x251402001c0c020186400c01c2d02c1c5580441d0710707000c50402aa040601404a84a0040100058600681708120201c0c0c980340005200d0200ca0051706054101414040d803005841400c0d000f281d8240302074800417458070109000c81c0090301c15580514a01031920074000280001580074000381e80c070950080c02817194440d0440c141c0300260281000d486a0542081f0308110541070140b102403016001241e858401400c00b12400120201d28855946650400c400c620302100743d14220030300542607124403419500000d004405c40c0c040d80940316550400f080c40854100502c105143d401054088503c0000c40011440c920b42c04049409110f0039003110038941c0550001c0f06001070700c41000e400c5030b481400d0700074401000352080000c450445202181d8081590301c54902410381d4080708401841e510510085880e41c0c09a000d4000041c0103214072022007005440d20710000c480c810302c0c003041000500445110380e881244120380b07000c2c242d812051041d044440c5009048055602c50407611 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 841730368 1250 841729118 841729151
    0x8060114061312030e09040308040c090c0215040212160603050609060d030e1305010b0715022a0708150105030115141315030311070b0a090e06012f01 66
    0x3201929403035514440034040700c0300d9103540740f1625000b49020070041c031941d00400d0720200c0a0b00c082c1c00145584040106214070111a40010f1031160410031005400701d01c025120100da990f440c2408030028042802e41da507468103a103c1c00e100d44103851401d200d000740e0300f00c201820310440e80480d00385000142207281039450f4600c035141c05015183c0ca00302c0d030f5800321900003801d40c0043d0b01107142c0c0d6010760170751180d10804d8060701d1450a00d994031b034460306000051503814115815503d00401c650360351100700c4040584140000404048240b420b41030141c1010040e80090b1441d12850a01c50058100102c3c614100c0300141d000300224004003604c0d9407152100d0261826011585000385242d007041e0f042d5062048051130300007208a2083c503c1c0d1003a44d415402600004d40c2004070800380d9400348050002884055145071802c904220080d00d81d047c24070840c01c80c03112240000b0556405011040da00d5203944c00081740a85100101d821020142444004103619021035842c00724000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 841731618 1250 841730368 841730377
    0xd1e2310080c0402030a02070c0b1c1817040b0f070c06030903020c0609031204030809030601150903020105070c1203021516050f0a0e060714010b0d0b1b0906040806011406 75
    0xc00d0050b12440e140039041c0406503001803c4090b00650030011107010650030241c480c0035046000342c00390b851400300c588004001c90260080c030081c1c070304050f01c035005441480100a07103900c0000030080f4001d113012090305016030391016103012000140349824502e00401030540074462449002d0454442d0422030480e229150f0040c0541d0000d030f10b008407898103001030007007514000d04031fa00124038030000f21020b40155000700c52498011551052030701e03050021a0260110206d00c41d00601d15100007040324195100107414445e00090003801c6c40700c05100c04018020a00480034000810300d802942c9951a18600c2c603084980c10120f20224040a20022055a9a03a03401d00b850050b04180065234421190f0390103000086022a0340c60f1110000340081034003c0328805410361542d41c540d401d40fa240c06500703206140c85400400016050311034107030070400b41014607000003030a510180c2c8900c5002d03031495110700d010600040500000581c54144e6501c40caa000303520940c8014082103006 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 841732868 1250 841731618 841731629
    0xb011e0f021507050307080a02040b0406081801050405070e0604140f04020112061a0c010b0a0b25020904060e2b02070f0308070f2f0f0102120d1e2310 66
    0x4080000c91806c3c2d105100c210380202c0481c80062905030766075800ca0495001d68045004901240b08202181d40c0500581103007801b10002440b9030b1909aa580d5100e80850060703060303440160000c81d00781d40741c55120180b125980c800007591800c041e030181603100e0049400324005103c0405a14205103d8001c0b14122982c084040000402c80d0080840d1600048841c0f8215940c8141c6041259a03098052004150700c4900d1980d0b000c06401502c0301011072855201c3d01c04020f00c24900503201d02d00001d0303100c4d811150000c0e800c00f900c00440c2c181020100b06144014006610f007504047c14a0b0000c0000126002c0f5600d141d9104030030f4840d04100d2201610324030f03003401a40b007c110128940e08642d840780c90300722510103a00c18864070f41c11141040d8002d5a9007084018031a0511903070345428042c00340000e0010079480f00b041440d07846135002c89000103440381c0180502c104000da82c510040c030403c90a010072611020365000141c105030012500c0c001c2d820111f0104910355a0b04000e544 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 841734118 1250 841732868 841732877
    0xc0f080606210f090d0f0206010e2d0601020714030c040c0203040909050705040b040207210504090531080423030a060501030308060604180b011e0f021507 68
    0x29208030821846800622a42481015403458000101510500d0b544207659101d044409400c28407095445c080d000c2c90100184002d00c0e958015080d00010a58115071107a210408155581c0d4a0403d40c083e0b120520102e54103082c41c175041028280980610411080c0c1c02c071a01d00d95034030301a2400305d0103090015055008010341c96801c0c00d15400030001c01559004030303441c050ba2180d84100b2078100c00c1040d182d9070000c1c0c10901551400c2d014121003070b80101d400350b081c0311682e00d400c007402e442c0b1200100890180d0800c2c0c9001406202510002c1004c59010005071824038040784e449102c02407010183e100c108525075100c20114440c106098104041f10304150901c4254617100707024100c06491030b0030719821200165000c12801640d140b0500c80401e0a52452a01030f02811001c3e024a00c40d074000d10050011070700c0d080010030281060400071a140344000300603100e018846c40704486019444018003403054010304481b03528042c590071501044000c84213004100b000b920100c0004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 841735368 1250 841734118 841734121
    0xf021b01051504090c1e080f0703050d08010b090415090903080604050601090303021c0c0803071d090106020a0b0604023721150905010f06020712030e01052d0304060c0f08 75
    0x1051b4403030142c43c190b00a54102e1a15a1200040c5244c981000d0b00c140140e80250000c0c02004024082a40484400d0a01210713550405c00c0544c0780c0e0140c40b0840f4081d540e01d8000d14010522815a50010941c51600704840c68050600402d02c0d08110340290140741003d0119420b94424080d05003102c0d00350340036003003a94401381c6540c1001d904e1344222081013006c078040c9002c1414000203601814190300d072600e414000500d814009640d140780c96104031800b500400c6240d8011404940044d8815a464015a94130000034001d008038843e203103807016040c0e003c16100348425900215151428403041100354602002c0f2114001141e9890301d4500108411b00c804515070000000290f0101c5c40b40354032900e41840e403040b100264000f600440b8000410024a501444240083d00c5422402c8a012183e500c001d04240302c04c40c466810000005043d4074409108000000c0010000e02c1801e041c0d4001c0649155582003a1401c0e16614603115060380305501594020b91040d6440c1c8844105 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 841736618 1250 841735368 841735379
    0x90204151214030c030409140612100903020118061e150b1b011514010203040b04030b0624120106050c0705120309040f0c080916090f021b01051504090c 67
    0x2049000c80b2041140702c10300c03d107510f000050020307001131300c4201000034240c0b6018910411401c03018010a0140060444801004401094007030702140140808900344c1c00ca07140480c01051144e5000d42003006100c040010424030303400c04240042c828151800f00c3c0404410401100c3c402506403609601d4040d0400c81c1810000c040c1010340454403004171442448a2038a0a440801168282c00020000140552030034001d69880d42c030f03820301c02182420b003403003908100c0e44100c0c00050b14940400000642c00d41c0d594014010360003280c40b41050720155401e500d1060382000d80d15003a401e8941e4004640c40f840742042c0d40c070003009040241141464a000e101c0340d0303402c0b40203030b40050004210701c200a444500892080d0769100c1000150002c070303000003c1c03164102910264550708004800f000040740c165070001602d4a0200c001359131240028aa002031040100d44000c00c190840f203020703481e8042d0702c024400c3c00e81d80c02e03801d45022080200000c8aa03030810007000031442c0c3c0c506100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 841737868 1250 841736618 841736633
    0x1091505090f0d1a06091501051c0902100504090623040c020709110c070501050304020d060c0e1f08010807080d05090a0509010806040312050601080103030f170a0902041512 76
    0x98041000c0c04030000300f0029103800581140e40780200903803d15001c1440f0032400c2c0456669401f03154400000c1070031202c40002450f40c8100300c0310011340592514180600c802503844140959802055504034903911800602960400d104441c60b891500400107031a0500c60030102c04441c05501941e084a01d0b0420040240144140700046125252021808400b18032514401c448210400c80d25603605140c81894052a0741190f4100031080c802d01c0010b03210713070301481580c5038004004500c101c1c510358100c0d2140e07141300079964800d4803c140c00e050184410504050003c2079614401c0c6030fa00c0300b18144e40d0702c010f8401c0c808558801000c040c0c1c0320f031081c00a41010030000b01740c2e881081e5103e000820000e0700381c2100d5100e8011400b070004254114503007449410100ca030920440c90860700107084c0ca44144409004d10510008040d490751243c600549401078641d0717060501c0c00d04006c000c005001c5410300720700440c034180d0309400240984200d4800c461540501d500b00004503900c512 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 841739118 1250 841737868 841737889
    0x1050a06140c070b0c1b0402072f03060a0b10021c03110403020409030e0321090402030603011d0609070621020918040516090b0906040b1216050109150509 68
    0x10003d005901d0f004ca84507036030303a0080441210740d0004001c0c0306020130048502c0303c80004610310071031040116600047e214460241c0440741c0d5074810514455011900c464210003809a50703050003002c04003d0313004d0195000d4030f45000e0545844800e4004003a0980e994808503031501216020115110f032858400e070040292500380180583c24a59640c1c0071401380c0b088000201c1c0031850b40524114182000c00c44003012803855458120070700c141d52010022807181081d005c0c0125000400510151401d42250140c1080030f80c09010349041c10505a40703903642038810916500078482c001130428800c00a60ba43c1d02d05803104c200c110301038071314140d00942c494a425604941c1003003046a955109110441c81079000d0809483c0803150f107404200304406a820100c8000d00d41071518074644c035034509031a88401c09aa00140001411001a60700d09449564200d1889040340000d0700e0180c081030b01080303880030b80f00d015169490b0010900800c1c0800140c200140080c031407018145024400f40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 841740368 1250 841739118 841739137
    0x80426010b22090b0a09110a030f060b0f12070303020c030f062202030604060c0f0309080304030c080d0c091502070819061b0c020a050619030e12120a0501050a0614 72
    0x10440f05940e03030010700c00f100721480c0741e034070b036450210070180180307007582c10415003040b110120303007504565075503928103000403001e40340ea40d80351031100c1d4984918a6518131408000e044900c5192440310325541c0c0c2d01d446c00101d0040c0104011003c080c10001070300d40c900ca1038200900703003954822940c14807001c802c10400e0311010002d070265000d6101402024001c500425020520400e03003000589002990f0520004241c0b03005803070404201c1c000b05882c2c000d507141c03806080f4400d0b1420300c940031f402030800c86817409161035604c0100326000b000081c2182c0e0011802d043c2c590300b4500a0761140300510500c071003500003d0078001c1c48050f144880c1101403103001c1c0050110301e5074040103840e51010100401240c0d2205643c01940b0344003181d44001e200c21119185002c2c0d150645072698403040d00c00d001816207442880280290500089180101c1d00304000c0d01c48002c0584020b0f5140e0517074208420500d0700c0000700b40303402c28200c0f60080e940769844654828441d0402c40c80640c0c8801c184 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 841741618 1250 841740368 841740371
    0x6061804020f0a02030d050702030405100f030605100c060b1827071502100606020319021219110f0a080a030e060903031603051306020703020703080426010b22 70
    0x20b03040c0904151016001d60702c4264011900c50032549120f40c11139502602000666200b0b00c03040211341da518a07907103a0003d5918080c0781c0001c52500070303005026070380c102940c81100b95003411001c0740c0c01216034001c1c3d4010041400244249420311450500c1d030981ca10801c400c1a0000d0712124410810341291b0140d6445134000301c220001300f90400d00150080ba0b105142e8000000344280d041143e4804d50301485001c00c489494480c010390790b0720541501104100d004c0e40d4585c400c9000380908074100d80780c2c1418684d200b10f851001890003185e40d0f00305020400100138071800c42c100065001d002000740d0700404684400e51200f1084c1d400c2540200d04250f1a02080c0003200c800348001402010300800868032402c0481e4800d14280c0551900c038101442c117420000c00f41a9881585600c0313401540050f540c03402410101d0038800740c2d4001801144000a00080c0001043c01125480f90039503640c4460740160801c860980703000400369640a0211402101c0c152200c42c0f5418602c0000c920 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 841742868 1250 841741618 841741627
    0x180b0f1201090603060509011514030a0c170d0908070308070f1a18030a021f060b0a09030507050103112b0c08150916081905040f06060b030606180402 66
    0x200c190342502600059007407500c0c0c002c10410004280111078000314104000d000580900312100f211401d503100782032400c000113410701702c40d071428400c1d03070300158115042018064030340601f0245400900780c0054a4482c0c0354107030341018410020142502d4200020b0800d0610390380300c114454200c010195000d0403d403c0f00c04c0010b503108e81c51710310884454880e00301c80c5800307603031050f0b41d4940281d6982c40350030400041d12081d0303005c1904034041c1180c1c041181800030303002c0e4490041c81190441d20700c0701800100c84003039907040401c8404a902c120212280d15032614011010b03103c40d0381d006400c0d400203004040700e000d4000c400c0500b1b0440c3e40c503428140044240e80740240e85e680646480440c88442c240280280c42c5080b9026191040c0d81200050070103407517041d80032681810717143c200040e00000c0307a613000c2c80544281c0c2e400107a00d07085c409c609007070900036036a04828a045030f6880c6841c2001a404050500384e9201e1240102401e0800008060441550000703400031a0f200e5420031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 841744118 1250 841742868 841742887
    0x2309073c051606020c07211703090307030309150c1116030b0105040b0f092a030907030b36150c0405060703050c010203270615040b01031404060219180b0f 68
    0x58204101d9800c10405445907005040c9011042260038030094230384810020007800c1c5000100311140e40798985400240f160150400960105640c0300e001c200509100d002c05e100c50b0b10504155040508000b6590480d204d200b100f920f0342803521005080e1110200100054176260b030120304800310280984180040940000d0b5143c102100e0545601c1e00b030000b00d140c0c0d043c0754410400c882c02d50300501455801c18110341039aa40a51100401c82051200081c61045420f80d03080e21a201c0703146045c0c20742c04c0b9550f070b00c0111100210741484a12070710075011403500030714140071f0007807046245840c03919003400b09115a652002109905120f020000515184e900b440218130400390240a22882000030902c58032910031911800d250f039000500740001d08005010607140311030210341c00241c010350100141c0180c00604c0102a003240b8240c200028040c0300d40041942400c1c00109803800806458181c5041601d8050f1080c503020301c030030503c800c040800003003245d07000305a406c5042c00a8503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 841745368 1250 841744118 841744139
    0x6040b18010501030b090c0d0b040b07210b1c030c03121119020106050603092d030304050a151a060f040b0c0a0b012309073c051606020c07 61
    0x84c1d00c200c985440e0b21040100e400e60501601d411404219a10130401082d6140c03051408030140000d0a9840100c02080e80280501c2000c413561a8a33040508034000707a40d0704000801c00209001d000f11004401c1ca4a24a00107031600015036150311402c08074041c50302e0845012482c1042d00b0896980c4181c0001651132800140c01120801c032590709184100d00d40081c00d4440315401103004240c144103002207000c01203115080043c0740c520003480c1d10303007081404804440550a1801b90700001082c0400d020f40070801c0d0a10a01480043d4600c0e0240f440c28400c41e900e8070108403021094080d192101e24011000300305108403070402c0c500317207520382a10348d20700d81c02800404400d602800c141410400302e910600c2c018055041c1c11138002d003180b43c800010703100d007140c4070744502940000a40b80c280110b03c0d40400785050940506146160311251000d5007507c4103003d6841c1d401d002203801035114500301d48070517680c1403003100846100d9466401130f4209003260903560117418008100d48002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 841746618 1250 841745368 841745371
    0xa170c0a0b0103021206010e01210b04030c0b1b12090c10050706060e011a090a030510090203011a1c0f0b070f030b0f0f060a140c0304061205040506040b180105 70
    0x100d01c6041070394503503c10005403c0342d0030001d540d180c0040e030041004080c07580501d0304484400801400c1c000030801e40b1841340c0d1500e84020414050a001d020600d40e01a480b1701d0018810300f464005502c514101002600004080d201000c4d0704200c0030204401d4442032a401010030000c9800d04118030b80001c0b0100c03051051640064804910b4405010f001d000b0080100342000640c07440394101b0918220f01e4101340c407000c6102d01b00003000344180d00c2c0c400603000156045400e40310344140f2008040c028010f40b05069101e5801c02c0006500300081451210f0b141c03100600141c10540d00c0c440305125160401c90543d00c03ca0350001000c0810103444e26180b1400d11659105031500384920082d04031034503070f2040c0c0c2c0250000800e800c4030340c030345d100510a140e00441c0c1140d03d1f5040c81d4012541540205070041d4412008030b1002c441c4800007019100359402ca44480b940c1000d0206a0011610300715406015075105034082800b00c0ca03d9000c450700419007815034034070b40c1c0c8040500350035901c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 841747868 1250 841746618 841746623
    0x8060f031216060b1c030815030606151b0615030f031614030c060f07080610050f0d1805010606171902041707050406171e010905070905190209030a170c0a 68
    0x385c508004d0815900c94103507940911414080f044000c50400400e640e418007c0145010f0340518000c1180c0007241c0c81510403405032940c0c6201021400b07003020340c0342c181c2541c400011003050110305543d031a01142e950401d4480380001e5080135000840440007080102095a500071079101d8241085401e100609140c2c403804000c0c209800e0000c0c11440c000301c02000c40e003c1121201c144041035484c0100a08418028642561500c200b822501e003035105805118409514180800c070510b009044440d5804c0c1c0284001c002c02665500c066074020440015400004003090000c0c80024000b1140840080f01e00c2d0014240b5444119a680002d18261068801c3c5c1c0130f034a04000c80d140c5805107402600c004c911018045804a0300380e83d0b20b410301174265090b01e048107441d4800200c254040308806802800300d980456a0380100c1c00208400e0381c0100d1104021278a801441c0c0b800d0084407640400540100404682520b802c1d841030000040c15140c0c1300100080303078034800c1c104285c410b07050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 841749118 1250 841747868 841747909
    0x2091c06060f0f0e070309030302220801050114131e06030b090106061412060d02060f0d0605060a0e090a1409011e0902090610090306020a08060f031216060b 69
    0x3402c012518040749034950100f114950001000c0c4418030b001d0084681080a504011989000300c0c541507002c0d000741030110070565800e02c05054068038611544044071070343c0000704407698840c1552030210342c13800d040d0703500f00c010122103500301d04103a800742641d202c00d1051038083c2071301001500300707803151640140c1e0744045940510000000078400c49005000b0340c181b0303440c000751b14040c4800034003580018040d803060520014842c3d032100b400c8001055401000c0e01d07640c0540118000c0b090f001480800103241c501040070840e404c0c0281140c481c0805500c0b107943e030b0050001000502100140358030005601c1c0d0840104c244c00f900a4180141d402600101d0007c80c03000c0660b80cbc1c54a52080d2100d524148a403460241c0c9443d23065642104058680e00ca03001c01840082d00c624070941d0000b8040c902c00604030b201c441c2d0001d0021b0061740212070121010050000301075680d800040080c0000c902001007161709400c0401151000c0d102d41c50101e071606445000542035000c0b0341c0e40301040c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 841750368 1250 841749118 841749131
    0x150302030109241a040b0d0c0941130b0118030f02090606041211120a051e0705220b0621060f0d0c0e011703030a02091c06 54
    0x303260a0080f0340180c00d15030301d030083d02c810b100c80d840c440c0c0f000c40c4034a080d84806264080c219489400884020b4140f081c10141d6074400d444a0000404411034801c000401e058404184c4001b124204a8041122001d42e40706e00d22000ba09a020b42080c1c2202510540425000306e41d0348400c010120680b12040d400a103600c0040c00241210300580c91040d2811100041400020184600300300d0f03807501940c070300c00c680d503480c1c0104042c3d12681c0c01400401c80166840c400b084642c024842c007820059940d980500700f503442e1140ea1710900c000003841d41c0c000d040744000154100440010300d00e9044100c0c0c1d8440c0d504c5020640742a003000850703600780c84606541c4100d503c18081c0060002c0184c0d5903918041603d1030b00554114a0145940c088008002041c003542e1071455608010314010101c110f500310320310303203609102c80d5840b5000c403040d8030800004000c0d02c008611040e5040303110103140b466881d903141400030340c440c0d02c4490740400403228055081c2e1000701150060740c8a01e000061a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 841751618 1250 841750368 841750379
    0x13051b0910240212030a050415111902010b1915020f0d0c03050d0e0a050105010504020f07032102030c0c0705040c091401090512010b04180512131503020301 69
    0x40800101032003450111140d04200b030342c44824020305060410054030803070501d418030407030400d1002240e5400140d404810301c0420b51607544041c0c000c0388034600c285d080d440d10704150300c103840015410303d099440c140b00014040900320075241c00c1d0390403480001900720700000010f015201c02c0f07103410040101860300744143ca940d1107500100c40311500080910b4440382002c1565200480c07240420000b4083c10a0105030141080d280c1046980c070040c404800d071420050740c0c919060300c0540c1d16608080001034030741814800c4070040ca60300e6801c2441c01c5803540b420307918100c8208402c201e040407800001c0200b2900d2010f1806502121240b550700d1801200d2a894248a40c002038400c0b0724280380300c40e8280d0000b1820702202e8038444681c41c01524100107070703075481d62a0b10841d00040070920041400c0d0341944001c0c1c00500441e07040081c800c0754254140c05400c14080203185600840218004c0b210702000b800b10507803201c00b81c001040d02da0300480602000b140e000b001003600030005100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 841752868 1250 841751618 841751629
    0x70b031510080601230418201903020f04150f080601090902090a0315090c0609060504090b040b030a0b06040c0e2b050102121503010509061906050306100f0e040c0e13051b 75
    0x402d0318440c00c0c050100d110700e60510827071050052200c0400c0c42c1069140105020390140d4240c0148240500c0c0c58554820110900c11840c207803a100107074040040c00960350140e0034076030090b103060350780350b81d114100714512000390b0200803225400889004000f001076101901045002c003040008a030f41c4000c1d2612281503110f60300711390705001e90b401c0e05108403940300f401e803400c84441d98000704161125401060003054101032558040c007944c0304500038451081d0443e0300400055030100810020b2800c1111010074104020746d108420102c51078a00070300c210304900301c880d441e8005c4500442c5a5175182280d0180e4503210342e1162060401103040c01421303504901050540080c1702c1450701161458aa510041009003039802409240c44022101c1c0d00c00005070001400b102c400b810811086071007810140b003000c0300d1040c001c80c04039030025903441945c06558049401e940c041d003095008c41e1141c4c0010301005862055482110206004000e81e003c40c3d04604601101403016030705110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 841754118 1250 841752868 841752881
    0xd0c08010e1507030203250314070c0302150c12130b010b07020108040209040314070501020903012a1407081c0b0303041d1305070b031510080601230418 67
    0xc03901d400402d032074007480240810b000e0f84070541e80307001a5242e6454110034054401880e06010a21000291690179a00b5074807024034120003041320746460317544000c01c0f20b045030041c0009006800408031240c001440b2000c0d103801c141d29030b40341810710032400c041b440868421143d00c030042da41211030b0340a04c84c480c055140541042c4045a01d0030629800103040c891000d4802809107101d02c0014041c1032103000795000000690341125658041402c166000c0d40060009910039464425000c580140e0500200c80076031402030086400b624099040c0c81040c0c2c01d00d043c114580d0100014030010310100d00030f20411029241e840c0c0c1c5e030740d05091000308070364280040c0c1d4003d90041006001072025030704141d00d4680600300014181c0e98a080007484207500e075800505a1155601c049070345601c410165100e10f401c014524a40d06050007000f2030a030848040070702041c01c54000c11441e5216562101d4070185100d03a049103011001c4039918250300940c4000c80c0e141020640d0b81095502d405104c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 841755368 1250 841754118 841754141
    0x110a0f0f08040b011814130209090607170a180b0106030b040509060117010e0609150708011811071208010519031709010903060c182117090d0c0801 65
    0x1c444070300e0306554070072005106005010450035422200c40c0e540e20741c2d410010008600324070351050340c10810b051003845100c020081707200d40405000904040400034540f48281e181d44c4d070b0447c208242c03410400d00d1100241c2104540d076107801241c1c0f00d01404482000340c09105240125103903150584c01811031b601101d0a5110b41d040509002a91300001032603419900d0089002c1c100c1d030140080c02d030040240c1d040f400400d0160004004d01000d0110303507421049420340c640c1480b030380d5060045074030203006d01404c01040000c45c0400e032078814683c04149019090781010b0301d031000f03940325144220300510b00440003402e07850050059003820a59114050b0301940d50b81c07145400c0d90380306504121805580242034001060404c00c981c8500c10704002150044010010f840c800312009103c0350414000080c506412000065444002d0503000c1d00500c06408651400324181d4420351001c22000895100d100140040340140d81e030321000c40c0c5850f215408442c10640703040301c110309464641454 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 841756618 1250 841755368 841755377
    0x5100c0305090a020603091e0a0c05010c0c060f0c061a030f0a02090a0b0d020607050a051903020c19090f021b06010602030301060c0203101e0f1808030a110a0f0f 71
    0x50182c40c40c4000307603142d055030381143c03c02d072a0b940d89481d9234034080760b040380c0303405080ca14105c42c25000000300d41055100e01903000e00001945610064861200010004200c080c20300000c2192034403541100300040e84900d0420341d802441d44884c0151400506010460341101c00202160f00e000c0203e412a07006070030141400200507000540c180d07400034210000540c80384200c0585a0350005881c0ca00c0303130b0040c04152601618209540e4034003152408070313250b01c03e0100c014010103400c02d1313120807154140d00404224044800303124030382a041c4a0300200300c0e41c0700004196030156008119014168040060f200c038940500c3c5d032a0786503c100c40c0e40542c1c1000e0010b01c111070717021040306d056402c80e04205c1008901c510203e840c00344145102258146407010400713100711040402000300490340310520003180c0c060085800c07264640f04010140303000000d400c2c00503d58402540e4403039880140040c400300702c8040d00e4510b0303000042d00b000003034209060b04880c82d0000d848104060080c44c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 841757868 1250 841756618 841756621
    0xc08270f0d03080c3a140a09030c020307150e10020d0f02070f0b040519240e15130801020301050a060c0620091201020f03061011070305100c0305 64
    0x3041c80e64116040c0a002c002642c80013450011a41040354146400c0880d0310714a0500c8041e005451000a0502024400007888080480e0568001c000e5540003501100340240c8425074400004c02030200e046092103246c01030301380542d0701401100000d001007410200c546561410003071078140103440e61413064249004800701641e0001e81b564021603076007040c2041545141e020b030324041059001c280d049209610100301240d104018000b00c5005a4801008202c03d000301a41c6c10098007a984810024211100d0b580c1509885070082e401141000c031500a2030a000c1350941ca110034100c0312421002400d16480d5151914410041c581c4070021415541001d0000d0240b01c141d10840c002c01c51101107032800d1007819846070000344900400c01c01003020781041810300350807a00285103e0b0805405680004006000b11000c002c00c41100504d90384d10741042001b241d42401c5803d00f040341001c880c101030302c0102311920156004500910181340e18003080d106882d8994004000c2508050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 841759118 1250 841757868 841757899
    0xb0901020c0312070f0320010b010e0d170d02070212030c0607020714010f050f032802070c090e01020f04060513060e011e140d02132111010c0827 64
    0xf429150030541c0140c12030100c441d2070a00322540c1d0704100384100c1320740d6140203203c00790704154000c0008030000c2c0c0300c1400340140380f010030000c10401c95020301181c0079405564003402126000f081a82c0307286e64018142481600842e03902c1c0f1a056207401c25920009644008032002c105d115803241a1384024007805003440c18076503a40041000382414484000440c04003103006e90309075068041400c000c40d48038900146030582c05511841414803143e20702c855012100064022100b016800050004420b0710b0402510001c018079a03a00001d9513003480604a80c8081d0030040009061036601d0588503a05e08020031000c0c40140d102c1028072260101c4211542d81000d426162441d07500c0c42c05480a550700000d40d40580e07141214a80400f00150340c011141603580034009002500c10490724450701c882c0360712403075005440f80e03c00d54011036815000107150200c60f503001d50010b16028100c518203a07a40b0209401c40104426410710040b008400c1c1c01400c0c1400020040031071f907550100791200c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 841760368 1250 841759118 841759153
    0x15020c031b060c040f30050604030f030204151b0b040803011a07030801181b020d1d060712020c090703020d05060103060e181603030302032208040b0304020d0b010b0901020c03 77
    0x78821034811400048404021404141c241c1b00103501e00c600101c140066803800355151401103e044010079081036024480d68401d10035107040c1c030380088904001e04050002030340c95001e8443d148807042c004041e1000084c00ba980464000d52107140f11546a50500b0148243c0910b51201b1518100f03052084402096110110070304464000101e00c21154002d41d007440038054400d0004281e2411a40c5010031a90009a0b2945800f1554419000c03070107201d00301081c81310b24010240c0c440303014000e0310041424051440920003c0340100e8080005500109140200c210340003c0800e07808a40540000182d0050b81c1d8800d00c24a400c04c0a40c1c10603603c00ca10240182c419035561180d503116003109902004101d00070040c92040c290803540c0d0340340090295200f100c22440c1c0400354001400801549001c40e40d482c0d1740110aa81044d042143c1c900403600000c10990744221b06044000110303000141c0c15001c1c1c031104554540d114480400a0314104000c034030a4041d5205000d150040d2515 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 841761618 1250 841760368 841760399
    0x63d033e06250606060518060301050a0303081e10050406080a03020a06021809040602031017030708130e04030e0102010b0303160204090f05120c012715020c031b060c04 74
    0x141c0e1022202c490703124940c5981c5022038100140303090b1805030b012a8440d040f03c0682408044001c034540da409062040c416503000a22a80c0e402035820081800024000c44500317a0040340c80f0030078030b5100c400d41c240b4030901c40242c0d5814221001c0035414440340c02c0500403403014020701e900400b4003400b2694000e41e120256080036004540c0854089829000e051080349032101c001c203800d18074149030820b90003d43c829501e0381510514000001021201110b004802c4030051000d1410940b90381c03038040190348940c451403107900e178040010034440c062080e000d00881c0680d5441c2d0b85480d40320006802c40701c10800451083d4020300000b51102101003488070019030581d80401c218005140c040b00d18986c4000081945c0148101c41c00b0a00310480a41905014a002404000300d80000040c4048000300381e2307000c4105500402000c6414150003c9520702d00f01c400601c5e140003094207500b9a04044040101184a0040032507824000c201c4190444000900641785c0307440c048030078281000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 841762868 1250 841761618 841761637
    0x3050c12070e0d1b29130e131208190e0f1e0c0904020108060f2b21091503060521063d033e06 42
    0x8014000840341482a4100450010050100f48000c966441c014910103081c03c250320180b015a40d0010f082d4140360801d03050762042c0d080d860f801c03980303106140c190356100b040e005803044840310001521103564507070fa078800c0ca01103034090303c040c645262405241014000550400201400384204048000a410060b100d00c84000400b0300c41c22111134203140610000821900840701a042c41000c040007280308030014000340c550711201c51041120003007003680c029000074500320000340f042c01c1c403401101d502440185044050b5a8220b808010a99400310600542d5025101101084040000c04069101c40300202c510a005030b00014030400c082e2140810050001c5120703020300380680d010b540585406441c5918090131800498441c0e810024080b440744941800a00100c007264852044006c04010400710800143d003ca0301038240d42c0960a455814a14000300040e80d01684a8001e50003040480381c5105840d030460318143c4001800200d0b0140b500e45101c99928003040325600361 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 841764118 1250 841762868 841762897
    0x20c100507090501180b0408010204080f010e060105120a140d0e01090b09041e05040606030308090309011e1b050a0309050312070b0a0e010e01050402040c09120f05010207020d06150603050c 83
    0x1840205d00042a540c10360200c045840c000801044c5050190000c3c000e0f0f50b01d00e0704840b480f49408450900300ca542401e00c07a2560045c60040c00a4a001e412000900f1408070840c0c0040c0c0c110348585001588101501010740d11000e21800800e0300b142c0181003030502400c00b0031915140030050f201c00d201d4445041d125030303542d000551664008000203241240b85000c00c210070b00c1c0614090008020b180800e46c0881e40c3c0304c0010b070541c5400030032201900e0061b03407110621851000c09002e800070502c504402e1003001c800c0020710850015900c9407480c003c038020280341c0518103000d000a14113800c89402608117200400d103030020501107501542e80514050001c1d5249109040180142c0e00e12001d69400c20103418000141500b14a005500880f420000703006211001d4503510207501c40c8806041e450100d070000b1400c10003403016100c3c01400058074001280d400070700004600f1070115003203541d0340051010f21558108000240960b410b041046d4204401010078900070003800200e82e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 841765368 1250 841764118 841764137
    0xa0e0a1e060204031e0302100203011203031109030d030b0f0f220617100f270f080708040e0112020105270307080c030c06040e220b0a020c100507090501 67
    0x1000764103d9005580140420840c4002c1803c544007000701d80c60190010b00c90701e15800800e01042c030031a030480e0040d140d0121106074a41d000c1c2c0152800c010b4482100d1014400140103031002c0c428003100200a65000503440d2003d001c02003000d4403031150600814240001c40120744850702501d0a545e0701e08e01002600550404010240c50f0503000303d04450000e124041c7e0703040c000561a8140c00f5a14010300038104910048012078440e03c0610031a5400f0300c3d2500e60304500e0707085003000c06014401c1d4100010701511078491070b500032482100e1882001400304200e800c03a246031030261558142d041c02000d4203400003441d80c010440300240c9010406411000303074500c0504904555030150076503031869541c0c0c160702c0d12002c4108080c0d001340102d050310030082c54513000b220700382c6001385030728111502e42e043e28502102409210b511700d04550300920b070200c4c003803240030b80c4200b15030f40e4003680e42c00010a0240c20702200c1c025100b41c06040c4800c2c0442d2540040d51402998800e29014040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 841766618 1250 841765368 841765373
    0x306030c0913020a0e07020d020105041e051203040516060e0a0504020a0e040912171e310c051e0907030f020712080105010c0305030a02131d0a0e0a1e 66
    0xc1c07202c4260003540070301010030000e4440c0300500c2140c81058103800341d902400343c80c82c0690980310112001041450001c0d42240381c8001000c401c2c0c2c006000d4005c0f1500d159081c00c802074030340d000750390568866101000421481c1c3d801f58101002d0003161401c04254141385000c00d01560f4140180c0348036540100301401f05501c20718001810030b900a00504c80001e082c10400d4031140c048440d41d0000c0c6981440b030b06510116003446000b00212a510321b140d042c05244400d0907039010748846409560030110340e028110040150301c241c00c0d06110f1003900009440d00082004056105c1030044c407524034256901c15080381c0c40c140c18001603810b40e80e070b84e440c044110018281c5040780c00e0450b10200b807240a00903030464000450f00151140540d030b07600c6000658440d101e00388010005142000003582d109050780182c046400e4080c0b54100c034549414080310a0751641130703658481d0b06042c0c02c21412004500583c1c04011344034001c3c1010603116260392500326103541102e404603403580da40004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 841767868 1250 841766618 841766641
    0x1202070209070c05061014210319031404080a08042901080c01020a0b0103030e06040f06020c09061c0303051e0f090c03060708072f030c01110306030c09 67
    0xa02035006080c80c0702480d2580c0d0203801840ca1100a49052069000040e00384101c0c06405e016185500e41c074400c1e05401004000e42c0d0080e84010031608240d1508894001070200064000d00c1840c103504504c104084100800302d03030150000c1e03a400c0c108a4244401300d40107808542010019250907a9107544605000460b00d9991350445e281e450700804c518a407520161601e4140e4014001381c905450014004996a528003100600880c64050040000a00540030042c180001400040c00c090b81d440c80c660b440007456200c18056008608008a031340740a00107640e00400403505c2c00e080b00194a444140714803a01001001d2554500200f216020b086826500940e01300b04010800d1503c03200419101c0d2040d5010100c91140700c62462a919000c5846440f0326841d9584101c04d90740d80c0c804440d080741d103941c0451a484100c04040a03d80c60840500403111420010365807064003403810b07402c58140c0301070321241c600180b06004040d039001c174102c01c90740021669880d40b41c484200106 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 841769118 1250 841767868 841767877
    0x80d0f0507122f042102012120030f13080a03020d020c01090305041a090d200a241e030c020f010606170c0a0906120f05091509070f0302011202 63
    0x7400c030f0341c5400740f8032801c00e0007003090f1030700301d9246009424001d804d103d10705484180280499500043d100c196550511140640c02c001680810300f0202c2e04000d28060458030400d070b203101c43c00810003c50100d084c0303809801540010100c510080151550445400384841100030190006015a1150417917010f0310a1484584003c00500e00da07458080c000780d0040c498000d02e20103120500c000c200c0c00b03209035103403d50041c1101c0043c01c555a5661400000220035613090344140d8585031042e2203280c04080600030ba079445040d8000400b048141d240c00ba040070104004d51041c42c400b10032100f541008009916040101d51640981410f0741030032154690b42c2155840d0000009425500c0030001040c8030161241d01c040c1d480c0c800700d0005c03600c9035851040101d01001d6007080303c18881c4081c41011028103000007040e035281c00c80041582c0c4103a036070040c9640300c01c104280e480215490150071240000043c0701161400d055210028914403000e07050101c00d5503200c0a0400640444 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 841770368 1250 841769118 841769171
    0x120306041e05040c0e041e06060b0d0e07090213051e12060601030c0509090402150f07032d0801170a081c0c050a17040507050904080d0f050712 63
    0x1804000e096807000c0c0c0c02401d00312815501803051090020340c014010031810300031500301114142c54541c0026102d00000c403444220381196071488001885c0d0248000b906d804070401c00d010400f0044186560710b0070405402c070300000c070710410075103e000d03500b814601c04982c030a0300c0d0a40e0f02040c05850040c8140551071603504052903d800c0d0614090100d001c0d031240d6401d880c20450042000c000f1901f5001c0c2c5a44640c104207000042805841c16908803856014046050340c60304000819101c00394102d072008502145102e80500601d110041030340315004d540e06000b401b00c0c48003200c01801c00318184160309620000501c225500207090201484190b041104265907070400c3d00f920340d01c4a940712700c040440e0b15203040c070b126807403007041200c0e5210b02c00e984940407a09030300b18881e0310000182080342ea81c82511030018164031403480b421300c15401014030545a403403030510f0806880022004039421441c2504005296420030307101038030340644e080d00054402c0340c1405c11080d4400760118 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 841771618 1250 841770368 841770401
    0x911120c0d140f01080303060a170a08040f031a0c040605031302180103020102150106050d1505040e01051e07080c0306030a0f110406090209030a08160b010303030b18060312030604 79
    0xc06002024518050f0240d002184052202d07a43e9681d51a100d0001f41c4900d5800704105000f00311442d141d8a50400c0003100c84290f03400390840380d440a110341d0080d8030a00b01040070600410034000411507034132204684880b040030516040032016290710840c0201310a100010011825001d04600c00b5400a81e01800d0700e07400c0d80c210044074032204802d201c124010f10510566020190032690400c0c103c800356150182000540b45101001d881103020001418801d000c00080643e41c5004014100034541c0c000110740c141081d024030141e041202080e05450700006020005600400700303075000301002d60b00d68032503c660300001d040c5420450050012100305410b18144450900d100e202d0310000c82c1d0810006546800c502c00381c0c0121032140e81d16400c942131800205c1c45181c0102402c41d07000c509540d00425982c0c9020841200ba04141c000960b81c03071025001c3c0c1070810300901c844c608000262020b01e810f50001c0d9443d0701d03805140032014404004038415071140d41100340e0141c6440348 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 841772868 1250 841771618 841771631
    0x91002090d030c24050406060902090a060e060906030f090d020a030504050d02010e06030a050f13020f100c0c0b0a14040b03071116061106061017040c05040203010611070911120c0d 79
    0x50b204c0546020344090320024503000c4000340c0d0001c9807003141c4034001d02408007884149081e00680351140c815010a41208003003018103d543d88242c0103501c58600302d04844003600f40080004d2401c45400c07016400c0d03500c0a2090390100380c2207025582101c034111140103040c0342c0340c8012220510100030042e003200000c0240035002c08182c120700d1003040c4241c5081c020742d480f0002d48040788500080a50888061680c1d0242da05014000344000289030034070203804200d81c2d84048081c1c1c11640001507040010510340203c40e03204541c005c0c5899400c1401d402c043c01d00108100911001e02004248403030000c11320240001440010003090568080303145480d55414040d14142c580c82210780e4500821000070400c0c0f92010b55040900801d0303a42711201084411940403404001c0c0040c2c0b08140d03102c900041d2540c4a0000350f02901c0a40e03903450720740c104264040e00c1c008203a003250302880c6c28503c40d40c0702c04211009442c8030b840912070344066516068082c0e0424410042290001802c010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 841774118 1250 841772868 841772933
    0x706020901140f031501090b0901080411060a0c0506060a030c06050702040917040e0a02040605070210030e010c110615150d060308040b07050f07240e18091002090d030c 74
    0x2015620901c40001703002c0c4554107400c01124181014002c8030b1180e0810b0164580d29445404020342c010301c14141d00200f0306103080000d60b20380104241a0014002c00400000c20a0900005801c0b05050700c0c1c44e11181c1c2580c0d6500305145507409940c0030410042100c01c1955103d03004142c0c910f800403650140307822140680146544280900b620001c0c08401045103408544210303801c591080d0b40c0d0500302282d550801c4400042c1c04038071010543c680101401208003886289504a0152100000030410004690503d14003d10309414207040806050441d21980e09054240140555032a80d803204034505800a01c1a034101801c1d660001c28003085075001c0d81c2c0101162409102140c81a152000d1141c0e0360b003da80c0501081200d21001e012854050321882443c2030106052010400ea031000104665100d000c0e070380010915080c0c24170010f4501809100000c814103441549400d110b880442d10b00041100001d0802041c040b0581c24840030f00204980100e0b081182114050080d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 841775368 1250 841774118 841774147
    0x50a0c030b15010203130e06060d060b030103020913121b08040b0903010e030304030905010810120f2f090c160609060c052109100e01020705070f0b070602090114 71
    0x101c1c2e00101071a006141c100c001c0d8000820717100b14030481154101c00f242003030341c010711104001e041103400c13401c1484134203440882402101c025204001c100c0f9202d61560041012070840580030340415461195480c02081c08600713406150313001c0e0b00b44044032820742852089114055180075100c0400404c0100302c183c1040c00500001d141240240101c1c0308030403c054076488281d8005021400403201004203500400191794085000c110494895552b0b10504030464551201180d8600c2c003502c5a800300919084da80c030b926180914141404411688000350090b04580030a110f0701ca0078001440c4205054100c0e59081c0c0c41c400c4070b030078802d100d14000001d0800c5800483d0803d0901105076000d600c00c0040e94074044000380c41c030ba030b002d190410b0b200030040c014141c400507024501e8411081d4040307014005000c0420701c0016620b00103406c04c1400d050240e0443c0c40c04400c44442085a251060140c44a040e0007500069503860303806c0041e14a0a40001c0c43c3d50031501c04505034410790103a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 841776618 1250 841775368 841775371
    0x10309150c0806030607050301080d14040b030a02070b0c0901050d09050304050a0b12012709020a0b03070c0b060d080703261e06030723010203270a060f051204050a0c030b 75
    0x10b50071030344146c442040071750345c43c0024000c2a0003030303020420403518603119125003024162401c0c901c45c9000d0303c50710034403032945c4102e0b15500841d4000035840708110a403424035511070850750000d41404a182d000030228440c0c500c90751f8082c0e48a980707450600c141441103800510300141502a05545c801c18014550083d00640030301070000800041e012030083c00302c4011000c84003001441c4c00f047c582e040007c00039450240c0c2c2100e4a858041920b0010400542c0214881e403180390304a25079203441c5404500003048036026a01110321000050f14000644440591600741a80d00201406621a0346200c041e45011481d0052041c401c85003418540729005120014040025a070762100707255480103a4071984070030301107008104541e03c0c80d14960f072035000b0f814030507240b81000185202c3c0305c1000c1503040314240c1991040320b0249180c29001c98000b4090760401c140c203054941d00207015400ba07110080c40c808610400102001014841c00310080d500540301a0503a0700c0342041945d02c1d00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 841777868 1250 841776618 841776631
    0x1a01112a0411030f07021006030314030711070e060a1406090f0d06090308060a0e061503070504080a0c0e0f0c070b061203160308011a0f0a0513091a0409050c010309150c08 75
    0x20307c0c0b100d820510031900900d42a203425450b900b0070303146072048c5604150700040c603100404c405107920038001081404006c000300034011a81d40e5030300f4030904004007140c143e1300c00c0c401b12101100c40d03102e0340c6030380302950308482d012200c41c0d14424105000c6459130f24040002445580780c52105410140c0020f10140200001d0307e8407292580c44100d240010358081d10480da000c107044d8a04010342c91104010b6034011400d00c0e0003800d19540300b03069884d100100c00200e0b0300c1c0c0c5030700001b809001c0d00b66a0301c603170100d240100c10740641480f0f420407290f0302c1805005030800341c0c54400102a40c8407038000140d24490241200d50319030345030000307245000a8040031000950440000034014620400c480c03a09804da4a110785001403503101500e40398400ca000381e0510500340140d00450a01c182c0c9500206400c0c5800300b9208981c00300360403008580c5d05124440c1d440c095104000c05c0d00042c2d4150321800a083c00500e101d0642004190030311045004201103007030891041c5826400221540200c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 841779118 1250 841777868 841777873
    0x2102010f14040203100f0f090b011d100303121104031b080303010614090301180c170712080a091a0d14090a030f050c011a01112a0411030f0702 63
    0x160703000c40d02401803a055078040c3d070552122049008040e1a40d1001c00c0f29182c0160010303001c010382400f20b0660703040d14070070307640700e102900101b01440d192a55422103524200b080d03c818034280c00742d101e50b1903480c0805002c000c03840c022400004442d500100298036108000c0b42c46554070f1400c248180120491081e00009941001480c0c0d4400002e0703c0c1690300503116005a41c400d644400e00c80e40154181d00e80c159203a2480d00710707d0020155182641d4020000b950469003400c039091a500a04541802c6503840200100130281086909030441d9500036001e50f50307802400800c485488032030b08486950b000c8130a074840203400c54070082c603003004200300c24000311b500c030180c20781d40d0541200c42d4103207900b1071403c0d100042c3c41800e030040b94007468140941404007100840c0c2c05c5919620118038040f01d00400c051856821280c1d0144841ca0a0010040c00905010030410380c5500c41000c602d142444400c0550f035641c5411001110110041064a914060b01c0c0390002c41c400307803113450160 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 841780368 1250 841779118 841779131
    0xb030c03070308041802190203121605030403050711130c0e0102030f030a111b0106031e030207030b090a050f0d0e010507050a0305030a0b030303100f0b040807122102010f 75
    0x505010038071400312500500c03540d04192600d0801604903403016034200d10990308100340e260003603000d45240180000c40c0e00954031080048012b05100c03a01030700082c0c0b452a12014021810350200899030710ad40d040c0380460700c0c3c18562500d00101c00c031160300c240d40203204071a6280610344a034032400354104555900624110325100680c0c80e41324400b9810881001000003950385800d50708507144d40c0d010303440780300c1c5030821000c5440c01d8020820340190f1141d4683c40c0810a020310b410310002d5080d84501e440b04498000d81d006981c541d0903100c000d0900081c10002440510103021807a02c03140c012040e03504010241080988907800288070002085d07841140b0705c2594417501c1079900b00c50f4800010041c0400da0385055460341c02c010003031501e1607142c11b0b1202c0315403400c0c406180209060741308008400c2c2806402d903c01c0e0015048603140003014002000307405000542401141c401000191903d400342c103102000c041040c05c0c80b5440328140074000750300ea038151700094011445c8402080351 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 841781618 1250 841780368 841780393
    0x10c05010c210b01020604020f0d020d030e15040602060403121506050304380603120c01020c0709020a0e040b03030412030f11010b0d020f0a0906120308090102040515070c180b03 78
    0x300d500040f041e900507400480054014207002000c01240540185205e0100b65554000f61030b21220150440c0000e400c3d011610750b5042a15160642c5452411210709090500c0b0b000ae589100080016042080a4004082c1c034600c036884420403e0960140210700c2e83c0b10390f4007401a40c81a9000c950f0050200e9941c0c201c0589000c51480c3d0a0846c2c07940a91464601050f142c0082c01030070555160141180260700065214002c002c2c5108040c000341c1c81e0140282e1550403c0507690203005420300400400c850198010300400d207449080310001948441200844e02d94040c80d04640c1003040c65075001001e240c0c1000303403401c0922a075a107030400e00d00c411000a003a54900c0d4007240d0090101c001d802c00601c0c02800c001100300c40500380344e200d9550360700300c80c3c25200d10f03a00040c1404240040f41c0b0605a0120030540d104103000001e40c07130a46410702107440742c001d10407601b40d0b03900d011440c80c0c01c20030245940c0000389100e0360950340b4170b110f85401e1402080081075090bc01d21401d03407160316 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 841782868 1250 841781618 841781621
    0x250b090d08010819031101020f030a060302090610090504021605061e0c0a140a02100c121104180e0a050109050d0905100905040b010905030102160c0506040f060e010c05010c21 77
    0x2c50400b5601c200d000c1d130800e65405d4481c0702c410b1420300401e540074000b900185510310b000c0c5103d9000c0120100d060351a41c0144681418003400c803074080d000152507440201e41001c0c0d02412030300305880040c1c0d40c10100000715500300744200020650300072401070140c8440740650000c5c081514440700c4185850301c189440b400d11840c02c1e82c10204001030300045010003000050300c0500b5041c010b4411480c40c80c92540c1c210740101c0e080c400804e9003508541c44c5022203106003038214159202c0d82d0728141c140b40f03042402a4502100e85c2440307032503240301150b403102808200d404580c00390003846504514600541c54a10324217043c80024044a400140ca103400c24210500150980b40d00c440c0c14104030030301010f0404d20784009e05024450100180d641c40900c0104042d003954842100f03140301c9072801c48084011907002520032070741032105200a20381c90100008448035811302103611420b03100140da031280c090703401901c1d65103441c14901403150410180c40d402c01070b0340291243d10008403030810 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 841784118 1250 841782868 841782883
    0x915030106080d0e0d03210504030e0103020901050d0e070302061303030e0f01080a2d02090f060f0a030f11030109090b060102030c0c0f03070812210c250b090d080108 73
    0x10005603035046481698101441d03003604046c06403820b07501c0b80c83d80710b154000b40442403481515030796440e000c03c014181e02044115071000309103403d40c900088030300002d2441c09007003910910243c0e2103070403501000040280c3c00086034081c041c0c0d0740380d200021190700950a10b00c010340200d02d89806003c00c9140070304c4685a1460140c42c1d901d40c540f151740c10f0b4801424400c5c60703c48000c1c2501c540018180da00c203100071580f880000c01603a28190030701404007448052101a0240000344800649003500c1c2060721080055490001100841c10200d00043c0180d00440c00a600e000000415003540e15046454a24080e1210840743d485200049039684030300c0c801d90045402141c4132254602d4131080c0c1941c48a0010300722641540c45120a40c1003083d114490409240d00154140c4211032641d680e840e5141c4808107240980f070012082801845002c203009402c1d511042c03031050005100d9102e20801d904114401854580510034903541c10342c865050740070450110002078040300004140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 841785368 1250 841784118 841784143
    0xd0606230403230c030610090b120703201903060b0a050f2101140609010603050f13030507140106052110051003051507080106171f05091503010608 65
    0x88803200010204821000c1c01006010420300135000403095945c0c04008850060406011070082146418440740c1101c5960684034003a1b4221071550080b400c001c14500c1c01c40ea00704e0064107000c500d8900c0504400080740d6100ea100300060340106220708920180015288141002c00441d403201081205100491207469070182040b55196003c0c00c0c5010101c004c0483c401140c1c41c42038890322818203507801d45020f00105110107007045864506400a0741c010034590404000b141402d01204254200041005070030b004843c210784105449402160402600107159a8200f0a5402d188c4d005e0041445103d10600446070b400500e1104400030608d080d946d2001807a005640e0f40c010b00203040024201c060303103d1010400808180c0c10f001070030503424240080b03000da151140b005000c444060301700b0820000f1141d13008010340002600550041c90800702d901d0b000102100d4240e035111241c004613002404030381402a02c410501080700000e200310000d0000f81e4444e0640750b501c25a55255 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 841786618 1250 841785368 841785383
    0x3030a0506031f0e10020403050c0916080a090809060706060e070228060e0607030902030d081e06030f0d120b060a120902131404060b090c0906030c0d0606230403 71
    0x6010000c0520360244088085240031794005490b070710b600800320380140e401503c41c2d0700280c4005005191403500c096210740d50100c9411440e01280000703091070401082803043d190b84411141c240210b00c0d00383d40200c00d0050503580d40d0080d91821802034280c5206803c400d08542010603241030001c12010b0211040100765444110041400380e41060142c00940307500303684550070005007805204440c0b044a4644000c901c1c0c00d45403040c1407418840302004010004e0010900c580c444504402005141d041206c0e072400e170305d408001034180004220780c2480d91040113111405241c1100e64020807144400080040502c11800d03c101d0b4030840142200040c403405811020603c564084c07940c481c0081d140750400348581020700c0883d0a6074100000c0d0602c040d0800080241c14044d0a0174818140d91601550801d00c0300f440d4030b8090f803649244109008000508080c50440580e4000030064205101465071204060904480c040e10860280c81d00b4656854039281d000455045a912010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 841787868 1250 841786618 841786663
    0x2210708240f0402040305150f040f230115051206090304061d06070309231f0309061107030807170601030c03020d0c120b0d12110f0f03030a050603 65
    0x107854110303199601942d40c810b11035200300016807128400703840618803400c010503423400c14440c02c0c1d115610082507112000b012008000c0000e0480c0018202c056020250551160b16800c0d4160442c0d02c0002004040d803819010b80c200c40c0102c101d95049400070f0340c01d003014038810141c1988401d0115142a49540100300400205103d0003404824000c8854600510254080001c0669114030720030740001d04c04030002d11a0090b21001ca909a003801c401e82d030080200c3c40003040540b054179091481005494242703d001d607000780c0052a204c0c0d07001c1800c200700c03204a03940c0c40080e0006442580042c120800045c812405032800480c01c011440f1101c40a540c0c2d440118094410a26140201134092200c59181071180c0611001d51a05841e053300803010341502000b1184025401403080118402c02004589220040084900c2d545044140b1003102011036103414448107110415100e041427001d8111408406103018a0141c0d00c18002c989070a0100f43d51001d1103980880444251031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 841789118 1250 841787868 841787911
    0x12040c05040f2714030a09060e0409030207030206090a05030604050708011103040b01140d0b0702071703070f02060d11030109051f150c03031b02030903010606261902210708 76
    0x12007207842e0352007420041c031800c0c8445034160954102d681b8900105070781060a110042c0c0003000c00841c2c0c001960104100900c47d00c009654103d1840003a000350f0001031070b0002a00c0c0d00305c400b00548800340071624141054030b4180e95821452003080881c0d441c00d0a903e40704070071542207a015035040081200b0f56400c1804282500658400291740040083c2403000081c5100f00301074461480364025100c4135241c403900400002c0100402105500100100340024200101d02c00110390140c403196241c0601581040003800e00c0704060b074040502000028208036030340c2206204040584c00c0e0320001c044c0000444403a81036009241000a00c4010150050302c035101041c0f00a0091901294916541c01660410000c010031180160000600c1d040c0d181801d01441c00205103d281c14003500b8582901a206072540050032109401d009022803041426445850320f00020700c0400c640c0d0f09100146106032018800b61058004c6c000c0c00000d80041c0a0000d40d481a02012840c280800c0c084 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 841790368 1250 841789118 841789181
    0x30c030f06030a15090c05011e030f020708070f06140613150e07090812090a03080d060e0709030b090601060516031b050f0f16030f0812040c05040f 65
    0x4218a4140c411100c00c0c0f0042980715071803580c3c2110f002c000140026240c103040b141d800d29034120506200c14524980121121400c0c80c0c54802d12074540020b103000c180d00c0c00e1000e0320920348050044c83c80483c444c07041c0302d20043c0065605100d07140821504c0d00094000002c03110407030706181d000c8074480e101c030045500e9030000c420700c02d428030340c040d00b940e140e4001049003041560003c0014074603c209214843c0104018014020341e02c80c241d04214550000611900081c00020020f140c082025038180c545900f140003c0c01c007600e052800e81c504401c0040000318144010b42d504407000020412140e00030503464146c6205546061a011489014021000d400c56044080005451541c2d2100582c0c60345511454850005400d0f94040216035078904a00c1030703c04c150a4220391311400340e00d58001d102400326540401c40500701245810a00c200d8000c4100411000d0707010020001005040d10018003079400407501005200c000d031216404a400300b410f500e81b400104d00140d212041130 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 841791618 1250 841790368 841790371
    0x906061715120c090c28080a18050d2001090b22120201151403120912010e0c040c08091510090504030903050706030c0e09040203030717040f05150a12150e04060c05030c030f 76
    0x410303909d05440030695145032402c401401c010000907003100c000c100000c01140d08400c0400340b07600074810f01c0320340c4d100c0907900c9001030403020920f00802107419814020500c42c420b51038000c610140590f9031600d000e4041d0010600c00d016a1a0842d00481c100000caa074054040780040e0003003801a0207404c941e80347c0d500003260301c1d41c040c00800002c80581c00900584201c01c82810162200e0505002848181d940101c65501400302800070840110760005038200200d0f00c451040a8a03180c59603010505040c9820101b10641814208020705811140141c00c8038460f804550401d5600c80c004c408440d81c401500b000038a14001849a9160244445420030b000405417860700784180e0f04c110b603100640301800b698840c0070408210382c058015417a0f00400c0c00b81c694210890b540c8140d000c6501c5a29010024040390170b0380891081c0c007544c00a40e80c6240d56441ca207505840f2110f00805940446003142c0c904d040020300301115105034152406941075403203080c1140c03078031400c1c0d22420a0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 841792868 1250 841791618 841791641
    0x15030c030f0608030711060f0d0207031b050a02010f0f1b1506030c0806060409080f0c1e010e010f060333060906061715120c090c28080a 60
    0x84480700c060700d503411886250010403a041c011030b59800c60b8034020460104a4100500c00d51052001c5030a04000004a48802540701710059441c142c910b01902c0f00c3c0b40c401c0c58142004048242482041000200022201c0c001d03250089817800382102190f001001800c1040001d182c903a18181c4031410042011100d80308401e243d02d1422180030354012650154800c3d5171100108004004101084c40001c0d0000b1084c1c9082c801c0c0807060702c0d052524401c6101c11450000000b40400040905000031202a8188036013520300d1131401c0190790180c20740b110389142c154079002000240d001984211070480b0f41c0410105410102d81c2c0801d0181c4140520b414200400340c0c410404000c12481100c01034079401c0360000310142001001010200540e54015000c4074120900c4214000c0b0510405060030403120440e501d84400d00765030401c1203c4040640020f0003405111445941e2006401c4141c408010115204040070a0480c00d41242c05550040f84107080450f04926284c0c01000522a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 841794118 1250 841792868 841792871
    0x2f010c030215090d18050102030418090209040302030c1006030b0a02070507080307050a0303060501080f16050714060105120a0314090406031b0302040c1103040e040212060a0608060f0115030c03 85
    0x70311810300b641d1880c8085400c600d05802801c00302000a8102140c25a1011903000001d45d860a280000c0d42d244101c3c0540f107000400d1800700360121180303070400c0c00c41d1079002d0144170f1765040c90714010355640c1212030640da4600402d40c007407040d1001440340c10120f0307803c6500844c031070f203403030b20124000e41c8026025901c078040e08801007080b180c100002c04020348a0307030080000a0150600500b12601034001e80e040200b1a014480085092081d0310b410070321108500380c00348203041040d00d40c1d00c211080240380305105048840c402002050031410ad404c2503603441c040d51404a90b070382e141c407010f000080115440c403110000302c42241c0054600120701500000d0056100d446217403402c840307400080c200b482680e01c103004500346030160b00c04036071060400001c40c8101e0311916440e8011401007024808011002405542d516598080c0c00e074a44410364000b41801007c26018001c5809906c0750351040340c003c6088800304450550489400761250071581032107510440142c82884114020503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 841795368 1250 841794118 841794133
    0x5040b030c0909010f09050106032a020c221802090c070f140a0c05060c03120c0d02131703070c27060f090f0209030606150c06040f2f010c0302 63
    0x1d440fa01c10031406010500e480205040c904040f200560340140c101d04100360030440c50070701400810044041941405511107803054041314104d280c5000105d40c10381c000b0b98404003006100780ccc40055101040000420b0000c0302c80e03613a00c900c0382124200c00035004012480000d10309110740005d4050135109089200c088070541e140c11072206400c0c196400c0540001c81810200300780100e80f20014582600e00724240341500516684030301584002c682511100380001d009000480100d4280350f401c0706046407134180b50b0700785461022180c050f9044000e07a5120040d42d5410000584640e55440001420400d0501c0c0c02400c4000040311407000f2164164000c400e43c0b003007402010007400c103101191005d06e01d001401c00c00d4036603414154204920401c05d044903a2004204030b6031000302a9107580310101d81c8101c2145d0707403241007021f1040340103020a20041004400c0c00001c040e02603041d40307803860301c041d11886820b03045014201c40003070003031005056075000320082010702d40680103841c5103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 841796618 1250 841795368 841795387
    0x40c08030a0e0120060115140711120109020906041d01090303050a0b010816110a20090f0613050901020d0e1c020304081f0e030c1b1005040b030c 64
    0x31038001012900c0400c24070100440256400307481d90000909141000d201104c0c10380782940ca40c201030081c40c045500401944100a004216403059a060103200e03950b5011142064400d606140da640c84c8295541280c0400342d03a014091070800da9001850308445880e100d0420004140150018455a00c20700356a00001001c0c852401850300980b000300d024a04880d01d481140d40c8111010706104a240510140001e0484200e01540050074007400c40c00060f04424a0440c074040c005114504000f030b800e1311032000b00705040150380255030b802c040d5200c2c54110400000100e903a290090395440001c066041c2079001150046030050006150860305e08100d000e03107442008800141d44145040011440c1d900b1038002c4e4250342c0d01c00381d41042d003401c0e0900d4543c03000c600404906030b031104c503012081100b0341c0101c0800740c201040703a0b65000d014841548400c29000410000e1740740102d00403541c1080120b00b101c203103841d526985094100710000300c1c0d81d0000340210411080c1071005494 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 841797868 1250 841796618 841796623
    0xe0301091113021215120304150201060b0702030a060f0609020705060609060d02100c03050405060307110c0411070305180307080a05010f02090f060a12050c0d0f23040c08 75
    0x581070064188080c048802814000c41e803421000100100b841003144618007007000c1d848a411500c801c01001084801034009400b105041e41042d0041c0000100050400c450758410101c1000340c1d0020700909564400743c4000d4050010b020350941c2040c640f0b00e000401c2d070350100b10000c0c1c04134000100c09443d0303400c40080342c014000444669201710244040c03864803e02c071940c0004101d88540342011154040f41390700070218026000e021001481c10101402070007030758043c0c200641103586924182030001c107081000c42071249030b805898141c1aa900b0903006a04081d64000d1400340361104903034049a40b0342c007080481a20b881c1505624007142c0d01030080200605941c4000c154160071401c3c5182100e0030a074002c084c072481040000c841d9114a0100d060b42030301141c1c002d4603500034104c1681c0114804000c14401c51800382046a130046040103001ca0070b85495081140d0340034003100f0401c594510b1203080c48040380786480d040c11040c0c0039629510030300c5252180e03441590b80c0d19081c0b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 841799118 1250 841797868 841797881
    0x9040c1404151205041703070912030302030604051303140c07090f050f0c03010807060e04141810060f050d0206040f0e0a0b030a03090506031807030c091b0206060d030e0301 76
    0x40410380000020b5120580c08040b03401c1110204a0070030490034642d90f100c10301014640d03040945a40400007455190044901c2c0c4010810f2140c0d084500c1001e190040003540200c444038412881d1402040307220054100c80021142d040d10342c145031205280d2070040940100c80000706d548182240802c51114500903c043c00510b150007040f182050b030201c40101000501c1140c240006100401448a00048000440b101401c20307010201d0300e6808207020340740c81d800721040e0b01c0078003061056540c14000b10583c1c113101710042e254405c03501701c65034013542e4051040503032a0711944d90a2000b440c000c0c52880c80c103840213007120325143c0d44458204541c85980c1c07000c07541b00d06000400140403424002c190bc400812009001280029500549100e0540c0107081c002c40c001301c0021905024000c504012007494003c8484a82d0341c1c0c07404c6028686c0c140a00d0710198200001910540b494405500b40d03100355030042d00240c0c0c0c0705001c0c00f00407040c0d0301701501003242c007900011081c1c070288542d5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 841800368 1250 841799118 841799129
    0x403081e0f0711160e09070b0a0504091e09051011070317091603031d0402040303050a0804080903070b0c240f061f0e12070b0a0305041a010e090712020609040c1404 72
    0x805d0309107000c980c11402c20900394805001120308220244a0981c424229000e45600d1540000c518024030320101c130703060302d403002c5104081c038044544041c0640002c801185816903d001d02c501e40c400303032000569001d040700040202c0e1b050f00c010003048880040480d8010304460488000c10011074040842d4560344c1d1041e40440e031410705c01c02036881002542c010b0800251030552400e803079681d00400b0741c460b81c43c10404010300c18000c5070421402e42c003251030307008008007110020341e1140c03010350465014013041c000d1445542c0130881d202c95001203102c01000140f054100c0340e61208201d1051103c0200000d90040141c0210301040114042c13007200b03030300d06a907509a9201e10703c080c420f0b0346041c10110350059000460811000c007000080300ca00401030f249c04a0241ca4a09c1c013084000098a00d20b404190220b0010071503c104900192240602c0812601b099035911156203801d03031141e2000c0e4100c1401c1100a00b0b5060541014045440c6880c00c807204107001c0b0310b14125504a070304030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 841801618 1250 841800368 841800389
    0x5090f090a39050a1e09080f0d030b04090f020d0812010e041511030a0915020a0f230412080d0912200a110114030403081e0f071116 58
    0x2804454601c0c0d03520007240c840d4103060746410303600070010700711003402a20312445c03440c03500d6110010392081e03014030300500d0700004444105070414500c41d202c140026400c40080d10b81071240310309241600a81c0d0080d40c11910b80200c0f03441a4017030040150781c40100350740011040000720714030011300040500078800c200c05010300b41031a01e0301c03140c428008072801450740e092805440781400d4000032660051409100080c85094910701840b03820b80e02200d041684d480411030700413580d00700304000828561940c4450b0142948540307108020f01c1d461081e403881c0d1081c441802211081401d441a050191000c40d00300342a40c030b48a002e403002e0300000c44071100f40c0d244014540390801c1250711b2402c2c3c104076800c691701c90b02e030203181e132074100e0741c1d01802c0b0002c03407548002164041d52150a2481e03d510405030703203240c2418090310524040e5800e41146100440000e11070240804032809401c20528101c0e1580700e8036011500903c00b00001c07119400703408420b162002072155040000e0500b041d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 841802868 1250 841801618 841801691
    0xc0f181b0f0315010201021305010818030d021206010f020d1404180b090c040303081501110304060305011a07050613112107060905010507150f0513060b0105090f090a 73
    0x503641920f9030040101030541e070050203070a0a00c00c51542d00000d41d142031070038001c03650740c101c4c101c01c0380700d443d2944a107070f40000203000440fa400c60f002400b00303c8805401145c192070f010011110590010005001604096006213002e03101d400504861010074401c0750520351118080a070030b83c8540c0c0d05446069440c11400c42034144101419800120ba441c2e05050030700d1030301d0150060000920b903c19800184402800380d038061034201351a521440120f9031141c2c2c1350340000d80105002e0081410fa5070102c00900c451055940485084079448000380c0b90790707101c0d0b52000700c0003401280c0890325064541a155207076154800d24102e03004511544400703030f4142803d242d080c00c0386900060200555a002800715981010841c0c40090788160f001040328150b18080009024100d4450921424141880352415440c00c0c0d500d01540141010020380304000015906486161481500f01c0001c1800c00d0191501c6001f89a10140d840d4003ca8201001411080030340c181c00d04080d64a580d01c02e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 841804118 1250 841802868 841802881
    0x307030209100e0901210308090f012d05010308090402070c05030d05070308090f0d0f030b0409121106010501120c050f0d0e0d020102040e0a0e0a120306080c0f181b0f03 74
    0x20b45071070041811586e141c1c100700a183c12075a903210604409420f01c4000350200d04030303410800c43c40780300010400c02005510241580d80301084004d075804003511070403204000641119100382d40c1240c4d8091025845c180d4480c05001c01317034101180584800840b041d001526450500c03c407004144590b42c0e0560300c050601d805404050081c0141d040b0394020756000c0c4240500203402010300c041428200080c4504171401c0b0060140e8000741030704039050081760010040e190382c0c45101100c0ca13888002c00c9640280c0b5640e44c0d03403000d03c610740c00a01d10000c1d03903484020b6a40211540c500514009150440100644000c0c0c3c2c017892034000010350b40c081181d9110000d1242151a11542c40254906441c2800c01c2c0d1400d44080c0250205580d20040201d40000070415030a440360300c0801700e1020701c100d610103401415248209820360040300304600301854968207020001c02c0080c48d529030340383c00c49056004914001d0071201d00c491803002d2420700f0302801000c1d00c50b02061030711b026524600f64 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 841805368 1250 841804118 841804129
    0x1d040c2d030f02090a1a0f16020405090307230a06020c0604290c09130c110601052704030e030609103206211c090b0409020307030209100e 61
    0x244110300b16510500c2194010303070320072454070111103215607200c80440c10310b18a13034101e110303403044841180707000500000300707041003003240708400d000710360420441d0340f50003102c0d4680c40b5001e0000d02e010203510140480749140302c422801c4050401c200e80d2125200c6d0ba500c0d0880c3d120709004034260b4000300410081102100702140004031201d0101b5140c1079404114002041c0980072040e07004001c100190300d070700c40f141912402038400c201031028602a5038003801c41e0030686600c1c03200d805401c0000ca802e00b4802006c4602c2c0341e649030b0040c8002c1c2d14040006070700001600c00ca00b00400b82000e000c15507420441d050181d0140e4002d81448050b840c980c1c002c60b8402800d02066100080011151344505079151a64482080c412a2140d481d80c00081985440074028542801d0038418a0b10755900020710108000012000301c43d070404081081d02d0070f600134030855001d05000c001c1889002d105402541e08540d06040141c1080b90140010b070914580080400010380c06503440035062130320 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 841806618 1250 841805368 841805381
    0x30412020c13091b0f092a08060103050c13030204020d0204120302060915070e1009080111130509061018030f14060f0405071205070f150f1d040c2d03 66
    0x281013002c41d20070725180100c40c160125124121102d50b6076200101d424240d000070340a041541d40780240c005e248140064510b840c282d070f0b0715000924000c00210505080c8003164040009621070041140c4bd50382000080c0d8041481084400d13024040007a085003001c880418051003038014103120301d000b180192805411400301c1840405403800e000089801c80c681e004800d100369403040c803080380c8903009e4131029000e9000e010903601e0b0002074090441104041c2800100c101c011107175190341c850804c2144001034550341d50105d50486030164039800786129504103844911404001030b0740e81c840110403200644141c0d0600001c5440820001c01800426840044038418480600341500d031990390b01164050704000311101c0340c0e02c10501c4001c0101d48003c10500d0103801d4804d03203803101d203020105024090720100300549080c0388064064010b40104412001da280d100c2100c1c401003201800e1440844410302049110f480307280c1075511084003901c0711060f6140c00541849000500701da02 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 841807868 1250 841806618 841806653
    0x703050d020309100806031606031a0d120309021302040e04031b122708030901080f150d020f060c0a030813080d020d0605060406020a0204140408030412020c1309 71
    0x4100034602035992040403420b80c03004e070b900d40220a44d98800c08a443c007041c107207141e004d41b11030305d500082c4507525800c82c401c00140000c500e402e0786400d400b441042e41900100070803500303032145840724044c0702e68071482290b4002000020204800105001240d000c0d030015102c5840d80c4041009150f0450101c842503400031601d4140d02c4002d855601441862040e000100510140d804174486034103c0184102a0b942e81c82d001905d540f00c0300d95940350f00c02c5101e203000c9040355000581d0b00040c10101c5103d90350180022071000502d00400140034a2058101e07800081900e0a00a075160071029001803c1c410307004181450003400c001c0c009820003090081c041030400c00d002c00068625042e9401340c4080f807009600c6036256a4000007401c42d81d00a590060004280021010b42c00508201d2042c0250790410400102c0028005000e804a41c060042c0c8010404280015400d094502102c1d69520541d0942c20b400c0740000c60a8100001381c2030074585803a01401800001d440038050b050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 841809118 1250 841807868 841807873
    0xb040303020316030905040c120e010605060d110d02030411120303090a0609020a050904081207030c0e130914030d11070317040c0909060f05092107020105070c080703050d02 76
    0x51850394020750302d2007140e04544445110030b40ba1000c140c0600318000260074020018000c00c040401d0060044400403525902e040c10040d01001111040c8030301020b449010f0a03c501d040700c80b650f10300c0500489003800e08210820408c0021900c0d15201841c00b6030310038009180e1408800082000103000340e6102403068000b0414841f401500059030014036074444408501c183c0c060000445500e1644c2c001034106150b601004208283d90f001021050040001c800464451150440440708034888c110041600c044542141c1c0ca4002a42030b03e4085180d800f2442c9503d6646092801000b811740d02030580c00400c90940c0007945020340d081c92450711203072074189025528028448a8a129007240e2071105070085424041040c2e810806030030700c11002d200586181ca4080e0050001c1702044020301d1400002c54144e200c04515501c500050b000046017629040942003c29484840300328140082080744400140040b1034a000902c108000b03095903501d141405403d222070403400780b0854 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 841810368 1250 841809118 841809127
    0x403200f040c12180b01090e1908070602180a0602030d0e1203040b1b03160e190303050309161d0615040e04110607062a14030a23040c0b 60
    0x120f90000c00f100c4480040070000c100700103107104021100c0700780440076003403850207800070681000e103030802040d00030150120f9000d503c40a001400b154461070000300303481003c200980102d40c0607000b0340301201a00701e0407480001c4e1100054050700311a446400581c10208640c03200c41c90138400c0d620702c2d000d4070002e450b4400801500c20501e12000740000c0243d40e444000c10780a107401e03444090a11100c500c9290f5900b0022080c2c0b881c400f401400300001111114480401c4c10901e0081c00c8561488440d01c80a42c10b40d80c1c10707282500000c0004a00c0d2251001303441200f004242c0c40801080c11140f12510210110080d00014200511482c0140540402d078000405d84800321002c8a807010381c1203829440d68a0110901d00b1000c844540c81140801c011090003140e6002002038401408040000c07050000d07485441e41c2c04455000100b420507601d00d0310205444011070b84039050500000c1c2c10415210300e500c1c0c070094001c4800540040c00100010013417045c3c4c600001e401e10790407290130f1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 841811618 1250 841810368 841810391
    0xc09080d090b0301170a0b0103080d05011d0412020c060d0e010c0e031c210219080606072604030305130f12022107090b091f0e0702030403200f04 64
    0xb030321042c030890407980c20300c034900c0c0502d042c140948460385501a90041482d40d490404550603003041d10120801850f100000030300819401c10b00e118905041480240342e40c86032182d28110b14045e0109055009001c030814180e6030700801031a203038460110000320650460381140c21030f1030550306882407000700f50105000341e50004a100700070029590071404260344150407682110300105462480244d0044c803e1074070348030f4014000d8200c2c281145d20440c250050215a9428180c402d240c01c800c042164401058074010b0001424042414108a0500c03010442036207034010740c0140d0014034049102d13002004808101c0c002445600d07044c000701400c04450710340740556010000d10807511a048480d4040240c81500405005903043d0741506982d801004041d05500320401d10505040000408040c01e42c06180317400740c61030324032501141c208802c100d42440d000c1c2400f825880140300010004200b11081c01d503c801070480401814146d00c20710241070f55101d010780c415410300490031072 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 841812868 1250 841811618 841811639
    0x1503140402150d0e030f0702090604290d050d0f09060905150a02010e0f0303010609240818060901150608070806040c09030501020d02220f0501030b04060503010c09080d09 75
    0xc803400c1e0b25400641d9465107031820401001d02c6035059a103800086210314040701003202810080d40250380c8201c1707666070901000115043c5c213410320b14250004440c40846094103158501d804005440c041c074010045e1103003071810f00e46402d08000100c0015445611139440002c4400811590422401301401d02700001c00c050311280480384185004034180e40083e00c01d4020b4aa07000451091710441101d85e19215103990090045602094a18100261248490321200d2880301c40e003083c44122050414200c40d0200301400201c90001d5070101d0b151058004e004841c020400d0303200010380301030303803c100354007024855208100780400442040b01042d00904402e901810840f00054000c0079444141c8140038139800c09002e540c0301082c00410194554001d02095032400c04060054408480c040309903070310b80c000d8100340b036092003040100f540250440b9807580743c000c10104505071501d003c80d0840c1d03d41c0380c0250001c0e0320b00c0c030100000e03002489080703d42141c0b0719008135140d0a00ca000c06 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 841814118 1250 841812868 841812889
    0x308040204020d06260f070602100b0102070e0a05060306060913020409151e0b121b060412060209130509120309070905341209050a06061503140402 65
    0x1c0c0901e0b0005403150100341a54490405403e10451554805050f1080d942c21400c5420f080d6400d44500035241a00c2d00380003440314100d034032580c002c141c644104004500a040001c0919065209140b008100000f460b000184241c00030540000c441c500401018074000c40504001d00601c8100b0a0040030b141d003000300c1d10490340588000c5046413062500e6010030b4440355074204000d00d0094819500c10f01000055286250071100f48184264281001007009014030b000c061a40304e01d008003405540d000c41041e049100400107414180d5a80443c0028006400119921540000c2c502201d1a21048200d584a2641e41c01c010a14040640913510350a000c50060100e038040002005220700300240c1c0e015010380e40d4184400e0410b08090840700c100c0001d011b03204449e01c50205036501d0083c01500200006d03039519401c80202e07145980c002c098160040d940c50060094210124065004041c000c002031300101c6101d0a40318001002c844204042c0020303000e42e0000e000260b9600d05510 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 841815368 1250 841814118 841814123
    0x306090a1a030d0e040b03033c04180507030b090c0705010b12060105152805070c060e0a0902130504020a12090c15080906070e151b01060e04030804 65
    0x14401a86800c940d10401e081e081c89615116812500c1d82041c1d114400300c0340080c0640e42031007615130000406482c1e0181030f54910740c03003039a8585004608423003004808082040b04103a1154200d04070340c0e28040e44541c00140b40242a4061503005100c54410241d00505c0c602d4100142002e1400003007210801a00c03005104001241000070f202e002e500c00000c42c1c02c0107082c1c40c801007580d801191200001d01c5450700c90094901561052890726084454510300c80403c10160140c0d8004007007905913040c0d90000b041800c1c4101400900310ba94184040c0c00c031b0b034554041e428140410050b0045041c3c120815903030040c80740072030f15648403c1c5042030390320494026032204000070088031001420815402e8071400c160304d40041c00100000341003610180e14002c0d000321201c0340c0c00c0c4c40d1190b00f0384942c0c0180c1c0c040300006600a11a541200380600028a00e042501c907140b01c0c40301c1074210740da018801e980c020600310b190380800d22a180c01404951050714940c90b040d10041c00da0301005101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 841816618 1250 841815368 841815371
    0x4030c0b100902040f090606080403020303060d0f0209090c0f10080a18050709050411040b180408040b04080601170d08040803060d0f050313060908031c1b020a06110306090a 76
    0xc01d61041c48041c0d07220191070950021501c50356528401521802d1501c20003400510701900802d000d4402d0f045144100d406800851454864206101c6101ca0498041d581c07002c090f80302c1c40040c0e0f50688070b5030080c044000202006102d0008100741032124070038043c0f041c050000b645154603000741019602c94030114000418070740d0a01d54108034400c1030340c000c101d4000d40a012860500c03a03801580180d000c2c00c501c0e00415048001c1c40211088043c0003640039030300551003a00b86000c1a12150300510a0309480e040035540c000903409608250004c01e200d81145005000750100c40000990f000f100d10300070004080e080340c0103840d81d00b0150004d001801c0010001c1c5540e01c80301e190b02e641d0340d8014245110141c4070f003052510b1390842250074001188200e000a00e8a10418000d8255100303440075610308422100b6681d034244150302c1c104102c580358040452001120b0030030140509880c0c0107040d18071550301d0f0001c110303504294011492034050051120507218412401e5010a61240 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 841817868 1250 841816618 841816621
    0x30a0912021f0513060c050c06220b0901090c081e0a171305100f030e0609060a0e07030215070309091119110106030c21080706091704030303050114010804030c0b 71
    0x500483c546120f600217441e19040c001c0c480d40b21076204004145002140e01a1529600d52000120484081858407605520818220f501080c59030b041e4a0f00440481c0c000a44208242d44213001c81005a2010403140c00c0100e010302038028842244084084600240c00c00d095140c1d03c0710307489503822070f0354083c02030081506d10040c6054514500a400020f00d4008151032460000309904241c250010000b41031028445c5090f000080c024003403090100a801c1035594039107440000c001041d0002481e20542c24000050384039440074481000c10444110740d10035007424054418490759000340394840c5401c0042802d110008180c60010300c91101c010350100001c841242c035040404940c0c011035107401c00c004104590034079802c003144d000c0140004203640c988c913500390a413080c1001400600c410440c6a000440640c48025141c0c07040d1221034035034203211a0220260401e4100f2404070ba03541d070060102c2d0005101c503802e19542407a2902c10b61506a034020540c8040d42c1008012145040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 841819118 1250 841817868 841817881
    0x6030f1305070e160f030c2316050705030c010503040b010608040606151107060509130b0a08070806150f030a020103050c090415031101020606181b030a0912021f05 72
    0x40320303009004003000707026541020804c1148502d0100c0d00440440d081d5200b07081c055001740520b02e802d420588030a100710310341240d0341c486c0e1251704884c9101d2000c1001040c103941c00b690050010940504010b0500344c3c00c28050601d40144554a10306210003402000002142024107505403041e0b4940510360751110b00e03201001d003143c3d0b04155201c014045049800d298001b2507503601d84402ea08540740309a031510143c40c1d0b4801d41740b4550300b24908030800918402507030842c0c650b00034040d261210850f036512045007420010b07002014940c1107502440f10200014090360002042283c041400076240d40000740d450116010003814152141c0005000c00809410b0310400340014006118141000311084010415800102d8001d004000c2100e01540b00181d070358420b0307802601100303035260411304100c0d103c0002001d1005032115180100042000303d800b46d809035280d6030b00801c544147c1d15104030850030400c40c01c0c01310740c402c50b10390510110044184482116414000403d5101c41 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 841820368 1250 841819118 841819123
    0x20307030f03020a0f0b04050c01231b240c1204110d05010606200316081e0f0702040e010506100c2d0c06080103050c060d091401020405010e06030f1305 67
    0x100b501a0280c50150648028486c07012041d603c107034496400e0741c0c01d9980710b00054031000d83da0f21040820380441100034503d202c40800426120040040321094100404500e80c80c003444c002814401d0504030700e8106000e540c58001c07607000706184103040d04128a4241c126000d00000380007801403c0d500460824a803610400d80192941000003808a107840360009052505011000300075802c1c00b85012a40c0342022080c2c6020880c8902031513000250303910b90710304541050b041e0b80d200b92080d0300c00030031100b11040105000a241030400d6190451030040104564031000540c80c6079042c9003c000c00c90740d40c0ca805003d0b1003202e09049551030a20b090a040646080384e807048407180c040c14101ca220700785000c01c05014801e81d0880e030700903200c640c1150440401c0c80300421640c464080c100144c81c244001d00034481c00e82800160001e602c1c2c40f0710300b0080610440c0c030b000d6540080c0078480c83d40d001030800f880c1c942c03e6907460302d181043c01c1030b20104040104801301c01c80b4031008100404c00c09 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 841821618 1250 841820368 841820383
    0x11d070b18010302030a0f05040822140d140102130501030b180106110c21010c1803030f0e0301050a0f0f0207030e04150b0a0302030f06180712021303030c0c0f03020307030f0302 78
    0x47c101041039280c1468410000c3d44004010011051004100c0d00301c003003000703105000d40d0a040015a1032111610901c0f02c074150001003128080015002c00d86d90407824400b80010b0945104041381c0d0601c0d00c4000340864072000080d501640c80c81c00811801405540a18112459440d01d14581c1c1d40d212800780c1001a007000147d400500f40c00c03060b80c2c0c103418009014400550314000c0051144181d000e0b12500d0000d031310401904042c107010408203010700a10792090f134442c10320000e2405c40000003403c481044030450041075894141c520005114403031545000f212410451078030065850103040365501034000e91080f900d40554500301000303d1f540724024401000b405480d410b41c110064040d41040b12480b0203170345c9600000f05a4640168000300080940f9000d440548584408440c2507440e110f00f15100c50702080303800d000c040c149521034000e601076030342c00c50031100d81c3c501a4016011039003d811040c2c0200d40500141c2e0380441d541c0100d0340d1004429498400307900e4140d00b030410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 841822868 1250 841821618 841821641
    0x190618080312101e03020a1508070f0e04050903030a050a0e0c040b060909071e03110703030b0307050901180605030631080d0501061101110a0e12011d070b18010302030a 74
    0x11001c0b800550000d00f8140c20082c0d0b4400c4552019132a200c1014204142d160b48d140380001d20340d00c02080c8a0350041504980c48081e914006540d2808403000c00c0588500b52a961040d50000040150000080c440c003034010485c0c05c0148403180700c0282c0540d941c07518000f002d2040c1c1e03035100c4424007a51a0b00844102c0000900280c040c0c1c501304070060240c0d4040f40c4e040d5103441100400c1a8120302c030f84940d28400005e03035079007800e00081b0f44084000b0005890781681600c504000414140d07030300c08582d0300809101d03600213010080424828190b44079588107074003da00540501070258040c041090030401d000200c46194504000c1c209411020a04050540300001800301c0000d04650010381c103a42daa600c03190340e0003108480c000d00f00c40c00044a50842081401483d000714880c180ba0101524006c0251040007200701da4582181c401701003114040c2c0c51301820303406848091041e82c0080c070011010f2803c00c4c410502400c200f480c0724040d00e041550000000d041192540c5c081ca00b90392 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 841824118 1250 841822868 841822889
    0x1d010302041d040c080a020108010905090114040b092407080405120d0609060b1204120e09090c04050606042907050a050109050c0f03070b070f0219061808031210 71
    0x11a01e5603400c2c0c1c40282d41c10303640c9003110540880d0001002610100c0c540d81a541d04142e6880c1015000003441e025180400035529018074801e60b81800846038060b0b4061050140d10f804c02458441c90075201c0311b0200e080c0c910b060201020500c105458551205c80307828054200d0b0365600c0c003903017000307443c1001246c00c15001c1214044071500ea440102916400e40e0108803075903c600e070780d542e41d02a481a2030401c20b19100064000340340c100003020081c140c0e08041a10180c0c000018502d10821902a90303103500050302c044040c81d181c0112a00803c00ba10103074a41410001c80c14000c50001d02410802d18084201e020303190880e404544145400c001911501d100074900396018100058003a10740e4400c44e03c04506500d042c200002d2889801001801218a810b41d0060076802224064510b5070b03004007004003580340c0c3d0011204040d409080c1c80f80d81ca04140c00501324200040d1b4020014001280c01d00c0000d4002040320505000350108070b141c0c2e41e540b00040d4a242c02d40d04501d0611 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 841825368 1250 841824118 841824149
    0x40b090a1709030115080d110f0a0b0a05060634020a06050d06090c0e04320103060507050703050a030504020d02040c020304170c0303040513020403081201080610061d01030204 77
    0x31107400060011100210001d220700c1850144261240d03169000e06030f5140c1051001d01c0303029014000040341e1580403801e888c0c00b01a10050581000780540d02901c00c8854030040104540341c40c81084e0b40403104442c0141008007003010701c180e000c9280e0003681210001030301d220382c148440b215946010f50082030005150745646009180b40c0002d80c030305500c1c500b00032000c88c45900c82c9c000d200d0612950b0341c8028468440c40c00b00710180c600f0b00320340b26041c085050740301e000f03007401c605a0030300400215211281d5495803411408481004003185d00b00041440103000080c4e0020031145040043e10b00440c2c152103074000140652941c400c000d40c07080c54002558070b4541c000c005442100e5078044002e503480700180c5210b403200302d40b083c0d4640c560410002070006107440010f120300c00143d444018107041d108c0d0f83e0b1b4a442e90040c08440400d05000303004000da641c04104a03a40030a4000c41287c5462a000002d0324080110314460030391071a02402c0c2e01305034480e82c151001000c50301310b07800e04d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 841826618 1250 841825368 841825403
    0x50102070f020f0306040201020c04020f0d090609020108070813080904140702060a0614101803060213140609030d05030912070c15090614070c0b07050c0406120506040b090a 76
    0x12168000301c200d0080381d508559604030310307021422910890b01a0081c2002d580c00504000080d44940907030b480f00340f03040c82030807030711001807140f4000184500c20006004130140000341c2010001043c2000b04001e010400c01021107005640941d158400049500e0380080c000041c00303481c400d0702561003ea030450030003500c2030303000400500800100320704000158481208520000b4030741c194641016001c000a10010b211301d9541c652914020003422445071607507510000e0741d0102d100d0508541116500f4810742c0e41c100c014440010045801514064101000ca91207110360315848081c481c02200280c988030b4103011001c0c0e8030079603201043c0d80f0401842c01100c09000f5025404000f4240c90144d1110b50099624200703036117094039159403144400240020076401424115007026030380a0000c4c403280100064518984104040c0665501d81414841107032880d0380114420f405403000003011a00c0442c1d5140c2103034000360140036540c1c90f074116a00d0300040c00c00013040741c01d40300d81d0301c0b00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 841827868 1250 841826618 841826633
    0x201032a12021c1d010606140c070e04030302040602101a01080702010b04021204110f03191703010303021c0203040b09091503032b050f1f03060e0d02070801022b0905010207 76
    0x100000e41802014001e28030580341d01b00ea82d1070290b4004a0581e0181030300039a0940080c0c42050012800c4a03601c1d034a1b0460118074240507541100441d0300824148180c1d501404458030110280004001d07a203600030702c42c1d03050000268003d0502c50070720089a0090300c00c0d0401e9100410140044d5078a8216080000300da4030112030603600fa580000304041d961408800a003d02c643c010004d043d040e03801c84420305901d0948204840c14401550215925035004002c0c5000354000d401914009684e050410191040300d80300d40115042000305112491a171001d690200303100741d07005225541e80c05c004942e08940e0020159051102041090709900412241110f0f03001150980c480c6600d040c0c0317804141e4000f580d4000c0f442075600c00060070b08110702001e0014070f40b03c0124007c3c143d9170762119812034a004008562680040c00503407007040d010040d0b44010440b19000314074281c511110b40c1ca400299a080580404030181c2c4102d41c40c1c3e068104001294008001b1566815145803514 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 841829118 1250 841827868 841827881
    0x10f03030305090c01200304440d030b01031d010203100e060904030302070303020d052703040f0e06030717070302040b100206013f0201032a12021c 65
    0x103002a06000c00a2082ea4022400584254068494242030308002c603400b401d07080c40050700c4080d803105120004940040b6802001185c2d050102064030380248280000b14141000c420f4100e41c021647c6c00e134800340001a9803202081038600081e03152801c40040300549520b14900080c1e50441c001150b540d41d066006501031210b001403503a040395a407001c200c640d6011100103074400d440d07078000b50100740250010040e09101e0715005103041e8044040b0300031130381e098800c1220b15154180002c41c0c40d5101d4581e05400e1030800046040034503000e50400350aa0500503c0c140e000050082803140c2c0702080504050101041240741c2c821401500982e101c40f10300c41684a582010014030302820401c035074526540503a400f0b00000d030300341032424035a0013090302d403c0040401c50364485d044459194020304105606d00f00c01402e000e840c00010309842007003174040c8450f00d03100030110004288150401c40c915050400303400d803520b100b00801c020300a4903114420410241845001e910040d442036 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 841830368 1250 841829118 841829123
    0x1103010810141e0717090d030b0f210307050303040818010f1d0111031b1b10320a090b030105130504110409051605090615070302011103010f03 63
    0x1c010030b142103000c80040d02d02c1511074400343c0e03a054240030082c010031002254040203038245000e00c0000105094a00320003211400b510b40c01041050b4191a0301d40901500e09400710703400354030880180d0005620018100106000960003511070000c001e0038030580790741507042010b403601d0303140506000c80300354043c000c02c2080141a000821256001d891004420141c135544c0d03038550a0840d044407101c0b010310450714103011070321420b51000b01007000104216200f20050241204181054501c0c00c10012600c2c1030801c032143e480c40c000c0d11801a0300ca5650319038039114014480c80c800c08180030f03400c442c0001e40c4006200e18800d02c1300c0c0980c02000c40c060207540340366000b42e4820807940341e4003080c0945503105005012158080080b604082c3c3c001d80608010b0082200d4540000d045509480313048038944c00c0785002ca0300100c00004803500524007900e0070b146030700d400400200c4d1140e4000107424404004506030003490b20075488a410204e1030a5078550f41d507114102c4014414591008 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 841831618 1250 841830368 841830371
    0x309150c04060f0c03080a1e021903060902040b03192901020d180b09040615021f0b130f09060c08010911040806010303200d030f06050405070e060d1103010810 70
    0x8903d07071086610041d80f6826596110803038441480203400360002d9201480c008251140c0810240c241788001e040704221003190354482850001c0190589450b644040744891041c001008003030a00c0080702d40c8030005140e680d80c0c2e00e610754050802400b40e18142810300d05e00c0a408006650302c00c146103503006090b000c41c0c8a60400c000b040f6071521070b0710980c1c21524840001081104100c0d400760200540041010400c0c503242e0700c02c04003c0848089010059005400c0107140d0030102c40f40c40c4d000103179404244881030742400810059451a140410a81d645040023165504c1e42e9011207000c5d40d104c4000e000707840240a000b0000d15003070184400041c030742a800300490f0080d0040720115094200548196840c50310152030480420700317500d01290120503e000c1c440000d0000301e10170006030b00c001915030945d40c510401c550b03242d005940900c2c90234060201d89900b04e03400d82d08281e412503103141c0e62040e40341103030064041d80503480d0380200d000c40082000ca4000c281c078030140015450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 841832868 1250 841831618 841831637
    0x1104030c090b1f0c17090306090d110a03050403030c21030b010f0504050f15040b0d050912093a0503090910050d0b07020c060c01020703020f01110f0309150c0406 71
    0xc3c228010340420003080007003821071100c000042e0300105900400304840d220141460300680c00310f41011403c0703c2400c116000340c02c100c5505900051210742c12070441000344603640c03643d90003505c1b0f44030710301001e4103020450b02000c0c20030580d1042c0d2000e20790024a1840058810712001c1c0181011262403404505540c40c1c82d01d440b4800d1094800b02c80e40203164000040c940c905101d43c00c0d2040e28813240e40c0204020100d0a440c0d1440100024030740030400040d10b1814200c100d04280201e0050100f0860400000346240c0d035000e1f01d00103040001a0452400c6460300402141000041d0451a0304940030001000c2c0403022014040f1040c05440c681d846eaa143d10050480c83c025011b007d07402010701040d00049501401d40c603030300509500448505184800005815410003c43e03502260b40018502e03040582c140f040d940901d0004000340502600032031940c6c0c0e14060781e40c2ca00b001400c0400010040242005151a85940b9000064190800769281c20341d0b07500034052800407403140d01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 841834118 1250 841832868 841832899
    0x4061101110f04030b04060b030f0601060f03020f03010501050a09090c1d040504020315130b040c06390323210402030a0b041113020a1b05030403061104030c090b 71
    0x400c0b40d041a222150281c42c207400d65488503907810018206a5810390741d02040720054908000310511451040020242c0d0341c940380c2c00404c114841e01143d800c041c0184074204000c14040180e82c1520b0090906a846500c06002203440050b203034004d1404606113040b00c40c0c140e81041208450092410110302c1ca82c03919810710058a00a840c0250540e00103050011041c81c8032a0179900429008103415456400707450f00c80034140b0550381130b1421440c1c1c000402500f0340041107805110140145c400c8a1a4a000c0349861241d94080e4480c0035596801e11700100341c032030081c841003100c0c8450300c501c0c0a41c503266200d110380c0260100054440d551030558292400800d000c40c0b08640c000c008010300300343da030740c0c04481e020040d1088cd40010780200002003551220554200c0f002d04810050706d840c0c1e004030080c0913003a5402c0401000a0000d400404207201104460503a07400c0000410540341c80700390310305644119071008d03151421500011840170303040d0700105010707001110450101007450 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 841835368 1250 841834118 841834151
    0xd0b01170a0804030803130b070503070305130b0114060f030a0504020a0f080a060b220b01020709091a0912031806010f26030c1605030d0c03023004061101 68
    0x79500902000b005110410020300b40d4801940c0c4417035031110515405455940d0011401e10542c0c051020500105c2006081d03076061140d41d5004005504156103080982c03036074880303200103019120140d1046c402e0302c001922203208581c0410b0720040354a40e01c0c0b074a6043e5000070082074a0403842030044220000306000415070030407d603440740000d462503814513620100180700e0701000759001b64079000d9043e818401c100304400f02194511011903100e142900081c280216a003107850300780d1411440c403000c2603104283c0721419850030710070200b5881c0c40012500c1c02a144c4002e06d0518000010046c104070340c0d0b030403100c0c103100072411149907980341e883c4031515000d180200d00d0324400c00300c0346500d800100c1c5244050103d0b030400340d901c0c200e07856806a007014441e03e03c20040c134000400410080c1000c110a28100c00070740b0309140d0340507541c3d6009441c0d4140c1e400183d084800048150307094030070a03072108403080015490319911682d0b050701034810010342c40d044202e035280254450088808 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 841836618 1250 841835368 841835383
    0x9051f1b020a080d0f0b0a030614090304120605041a0103050f07091b1d09070c11100f05220905010602151005120c0406030503120a090807020103090807020d0b0117 72
    0x4103207401d06100424580d5030003421122074281005d1380300c1001103010303180d04c100d11001d075006140104841e0120610114070300310141004625910810080000c082002079544189078007007400b250a0f261810030300300b00e1031118024104c01c10580000010400000342e40c00c0d0350801d200903689401e940340c3c1180220b41f01101c83c0c0341c40f200004042d140c064865200c84070410007001d900522180c888000c205215000c0341c0d242c0214a000140c0380034814911071031402c2400c1159259408901d045c0300811400c196688081032003004980d9051307220074002e1107032601070f180c00d0112031190b8914007030f80a083c00384590340140c000c0344003c2d54201c1200c0d010310b102d4503403c20346404291070501071110030003032004402018010821250031985e114090500110300038001551a01d81c90380c2000342e03c00002d17000280c814a0301011038001200501a500c40c40d0b0242030000d0550080d040c000c026128259000750300648018112041042c0595a1810ba0354142041603035110440795182d928080c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 841837868 1250 841836618 841836623
    0x3030b030706020c0111070503060f0a140a05061309020a0b070c03081603030c0215240301060b0c07050108040f0213020409051608010f030b0114060705031b150c03060409051f1b020a 80
    0x10ad0000101c007042658801504080c40c218001441e40e400d22007007001c42800e845e9106025118000d128452a0405900c040c0d02030520017003041d02ea01f98001500e50041d80700701042c012011801c002801310a04902004503040f004d1070382d541502989881c549400705104801081c900002c0d150403c2c400105412070740e180600d170184070b0b02d42d218102c2811405200940c852009101001d009440a0241800414010509030b4542004125650400c1003d810260400600070308000c0490b20904000520703070f405680d1448940c01884403e0041d124a1f04503d03001c03030801c000c0c03050240a0300743e514140340c01581c903492541d0f00c4031199140c002d00b520014182c27600c0034006000700031000350406880380e03009104924001040d81c959081d07402c000311000c8240c910b010f041c40506801c0c016170580c040d00241c45151480d00c00c00380c0c0e55600016210901440c6e94007001010414104041c1e80750202400003141c048a40700c102c200a0210445007400e0344c3e02102000895600001d0352000e40d0343d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 841839118 1250 841837868 841837873
    0x30a0b19020f090d05011d100507020d021209030a0c0b030a0b0901060f181d1006020106030201050409050709090e010b12060907171507091e0503071203030b030706020c0111070503 79
    0x4201c18104000c4001c13000e03050765203550720040102060180c10002001448600280403240391a0a006084840c02010f650a40d007045500051003640401d58800d5200304006950326612a0004280740007003c8400801c400e603003220114120004402035071040302002c00601c114982c110502107401001c0c45070401041c9074802c407800d02d601620710010020707000d052000710150343e10038a03d19880c1303683e403034042c2e1041030060180300290401c816000e090f46000074004240f031540020428451481034158031955000440c481d50b204944210090206403030034082c5c081d05008250090076480c071000c1c840c10750692a002c160300046000751041d0302040107440410b28001c0c96103200d040113154020b41d4018548440c2c0c1038600d2081c032a0160000d41d482915443c1050300400c69482c90900c1d14600c4a42008100b0065030002030a034144d940f0b828561525803224a03080e070103002d414800a5060150b078001280d1140e000a002c045100c007644c46001c440e980c04a02c0f07450f1001c3c2c2c00f0301601034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 841840368 1250 841839118 841839127
    0x90f09150b12010f2c0316060e060106050904060f0b030112020d0506070f0f0206061e0d020307031a07140403032d0c02010f05040f0905090a02030a0b19020f 69
    0x200065004084101001d090109001c0c406400c580c2100e811201c13262440b0781e40c0e030050340d40a0000e1441541850100032008140000c0040c441e501d004031042410912070344a031103000c00c50690003182d058880c410131a511540c407180050805d4104d20b84070740c007861514400280300781e00b608083c400c40e0084c4020030318507400d11920300f0761095030000030380e04550410107000000350100121489103170315548005504040c0c120080041020781e004a04642c00042408000d07911007040c5007550521034114103d49204001094056040e200c029505020301c01000080c0300602c40d41c24400030100c0744608850b070710303900280c814110024140c030b006d00040c4820700001b4028051514903000045140170f4290141c80c48040c0c0b9585885078400084211088608550700500120183c00090400c04c0c14207040a0804582e100140702d4111800d80f034101040a103c82844201c98050f0054141c900300640c5003001c480b001000ea582054108601d8100d80100c0c1c5a482981c030170203268080039242 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 841841618 1250 841840368 841840403
    0x50304020d020109120b1b0306091503010b0a03140d081003060b13090f02040b0405093301060f12140406023103110f0102060c210f01090f09 62
    0x80d205410781c120706000800102141c0d29a44c20022020603106154900c1d01c3e00e00780300904054502140348180020091040c0f00440c1d85941a140d8040c00440c61105e940351502d000034050141c0c0d504090700a602140040140204101c5005107404084200e403141c14940030102d9400c3c0d41240c83c000c1c032034140742c0d0510004507180c010030960700c0000c1481284c0244680c0c1141101c00945040301d140c0b4040203424214100381c00b421180d80000c80d0100942d19041d02e501d9280c07060070036480d060501d1810840b00c140d201c40201011407074444081301c810344c0c44680242020202c80403107808900c0c01034851103045454015511307890400401072809442c0c030f0b500c5030060741020f0781c04500419403400f502503004013410b88a200d03400c0741106c4151903213182000c440c15045410700300d000f02400070480c49981d80000300b10b40c00200c9a00b11580d00d002e511000301c000d49a00780d9042c0c029041c8410321000c0c0080c0342107107050711590f403000c0140b03c000101d8a001c807050701030020422003a5032040010f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 841842868 1250 841841618 841841629
    0x103020f01050c030915040608100b09130204180e070e1e280614041503030e180103050a0314120c0c0a061b090806130b10080d02070503160605030402 66
    0x14103d11090890f030034450303007500103003000495040701500400e0108003005119400030556070008001082c0c0804e190604440c0d900c0c40c2320b80140103000f00307082c80da0f08030f06240030341c1110010050b2000010348505245490006024a609422800d114004d0085403002d040d01c000c0e40298042541148410f0170840303250740d103640003800e401c4030003074080c500a68000004030401d4449503002c0e0003c0c1306030401d001003074610341b1040c20600a500e480322108503c0101d01c101e000340d07030301030034403940d03c410540005d1840c240f9411000300c10300300d950000003003110000e5202905440790700d17081011590340d0a03040c0103000d86059000a4100c0b0b0000c03403150301d8101e00418001042c00c0c2610300100c0907403100b00a90301045007000e10103124202d024a401d9102c0045000390003000050025424090400c0400d590608000f41040d00b43c840410341410391800d21500070041c510568201000055020b5125100ca200b10741c06070103808100c1004004111000c400d480564440f94115203881d020f000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 841844118 1250 841842868 841842877
    0x131202120d15081c0207080106030c0e13020d12170402060a0c02061b150109020901170a02270103050c09012a0c17070605070f03030f0609061d0f0103020f0105 70
    0x200c414400d10b003c55060b105010000d501a000900301d100107844440082c44c1100c0ca911144d40d50745891428000191820160001c51310041c0c240c010030744541d107034954401a07400e00294811403d80c2c4a03000c0140051000c0c4c600c48454591022080082c852082403c0003100c009600010400034203600b64060040c485034140040c0130b01d8104001843d906501196040320b890b03d95004484200300440a40600c50240070401010740c01d00d0001e2002038a60a1405907820180760800001901864240d05503103d50f04a5024040315444c41c17540c00300d1031404144103900090070100050240d501c0501115403864040c0d48403130b04248041005945000503440300d0b48d003c80059824804a890b140c905d03c090185101540c450300c2a08024920b00241540b040040c84000d00081c030100d10a000300e0f45010390981800b107070300000903c8140007031940d50070a416081c81c001d00403a6440141201064102c00605090344680f6450000c21243d60300b440001d500513030f503184240182d4400d0010b00b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 841845368 1250 841844118 841844141
    0x11212140f07050703081b240f070c02130203090105100506030705180406030614010e0403020601050607030e1e0f030307020306010504021c05010b07020a1d07110f06131202120d 78
    0x360309503038681c6d6510b0701507030101d89000148404c1c04070002d6440002d009100f0180b22040749807220b643e11a40801003054010310748484800310600041c6491b002d50790320180c26500030f0102741d441c8851101c020094105650180041d0300e000300090103a281000e058003511f60080410741159540c1c6c104079020b50000001411007814080080d049407154000da40c05103108030000701d00c00e0700030313070401c043c000c4140e01c0f0b08c003040c4c20101400040703600852030074103455090343c00b1036807003086040955403001c0042c2e0b083d41220440d12403030354144884000700300001088580c144104242401c0540c0c078041d002000e0340c160000b60041100345800c0c0c0c01003120b20420f510070a051525424940102c490903400841c1d401000070b00c40c400c500e050488407001d03203505140124840c0c0d11819011000c1d200521040c14003c0d04480004610b03403c0007030160007510903085591600d0540105141880304160032585900345161251000b4000b03d00b1a04d900d6030304121504107018130803000003030a0300d9a0403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 841846618 1250 841845368 841845373
    0x909070e220f0b130f06051e040b0601020610060504091a180115051207080c0d15030204150605030408070c090c02011e0c17190203011212140f0705 65
    0x40c0350140c01c0c1026180d10160140c2e105088075003160810400300f08000f00b11079103540c6180e00d0400020142c65072500e20030b0304100001f6a0307544401550f520000c00c4207801c83c01c0012801004204024076061510070042179094035036540301d410211803040c9a40c0202004070b03000713100921400d4a560300c0916400398440300c05500582c65004a43e40b0b0390001565040d2401e41d60050080020540002c2c994200c030786044c030f203020303540c00d29822240d10281041c0c0402003040301080c40d6041506c103540b913120320004100030260070507200414003022444124000d50402c0043d11100440038900b02c01c580c3c054950781d04e1640d8030382d61610326a2141038115019409020042443c00705481030501250203500000380c04255104004100e5030039000e007650711818070035800035680c1c3c418241904501d00a100c0d03003480d150700760035810100810300e8006000d8030102c0001056a0240700014015000e109911a004007001b804c660b9a5101c40150050100c2000480e911800d50002020060b001b0310a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 841847868 1250 841846618 841846651
    0x5031308120f0d0f1b14040f14031023010b030106080609071101020a091707050609040e03072a1d040314090901170d0318080306220603110909070e 65
    0x40000c110b03945085058505c0854141004681d60031460103241c102545001a00b007a00d414040c1c03060401d24042c141c0308041880e85c01d6040d440411690b1140c44103200c0c28060b01030701d00040404202c0b8883e07950403082580000243c0028410100c0c2c0c1a08c2503903176280c2c1c460b51a80d040c084500b401a0101c03041000d00000b43d4004503083c03020f040c1c50b140a5031074842c101e103032040e025280080e90f030818409802075402004150350350411154820b0090f103001c20300284900030348d07084d0b01415001800c11065500d001c58504420040041441c0a1b44030850995032208aa12203c050300403021403c0605000070801080c054480e012180356044507145c0360030030762401b040140d1001c1e840019651000504814880c0d000d1050a01c080c1c05490100240000da80031161000d4000c0030140c1032140000110704107413501b6241402e49a56020030201144000203850010a000d1105582110002c0384403030701440d000710701c14040c604050046c4440f504100510500f5400500460102d017202d81c1d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 841849118 1250 841847868 841847891
    0x3a0f17070c030b06363601050c0c07270c020c010201180206072d050c0907032307180308040f0b07080f07030909050405031308120f0d 59
    0xa607a5025500c240f000d8080c60404105101108100034107141e01d85580d8050a05005c407140d00c09a0401c190018103055511003c0b49441c000e20981e0540c070011040703841e0314100e000c0402407210004040e50081055550788002c45420b80036090116100e40c005481c104003103031200d0314003145402008401c840e01024a84428100d440c60f49481000da001802d1003940b6607020310030210703016800c1c074484140280550001e05184a4624010866021590103490010300c0c074006003100181ca01040d0980119030904594503441e42100c1d03446401090009980d6a01c2405400c2d9080380340e800c0c00303005100594151501c08001840082000084000303000c68012120f441c1d070003980981042e0703070b846003040b49200c3c1d07070b07000703904450b50000081100c90f0014200070125061802c400c0f88980e1540c0041ca803c6410700d807203503c1203803400e0409003400305000d00440200b6903101d8021100780a159240700040d2609007440f001820700b0030074070111090340222002020f040403103c00c0003d400d1040c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 841850368 1250 841849118 841849133
    0xd0b061201031a070503010b09060d061706010905160c031b021e040609141801092306061206070f1808030c120306061602030c3a0f1707 60
    0x981c01964080043c0d1a038482c030281c609400c5400c22000d203401407456040200c2801c0d02d00c82c25000324010000010320410028942e4040c10241c0100042070508604071104181d465200b805840742c01c0d460140442e81d10314030550460502100e6844801300311f1921786003a903c4440850801d102500704d80708250050341d40130a007014039007401c07840b00d40c507411050a000c101c40c580d4210b403104914180c1d11200640c85070345c100e5480115540e41c800b244000c0354220303026003030110000f01701e0010306040a20314082c400b440b5010882800c1101d606940e22820800c0380414400a204142c00c0031003c40c05a52140c085607012645504048802c454045441817001034641d0012500350000700d10000301c844280030340c01045031412411421428000300242c0607100d030406402e082c46012034400c086460a014040305181e00406040d40c3c00344403000040d04162031156081c0101e5205410030703039003070412034062000360018230b100302d115002d0f680d0f41e0705503070a070a441c65285014000c00c0001480b1303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 841851618 1250 841850368 841850371
    0x210b041104150507210c05010501140f19030201050c03120109090605090f0c040504061b0903020306131a060f060a03060503010506060a021b0105040807030302011406150d0b0612 78
    0x4001050369480c507207100c095114600c40958400c1001c204000c0e004101910080c0d02005071703c20a0361100501e605054030715000040d0021311079401d080c0002a0f080c07281481e440004c1040c1c40345000b00d03038400c0401a080d401a48007003600702c00c0410a00140d44202d002c3c00c56800f02400302c83c035062980004000c1004260f000d20485525060300b842009124003400d40c2140b0880000d204001402c18242e8458135001001405540e5880c001000e210041e00000e40c0d41707080c21812003540100f0a0014554503c5001c141d020303214034400700d5000040c40f4100220f05da0800e03030100340f00e00c0c0c804038a00c8148014005540c40104c00c1900c1d076141d594100100b43c200321036100001c1c000d10b030409140c00d546000301a03620411051000711045a00031800110640740c04040008544408005a5107402907030880680b03481100c41c04800c140d015488050a6179200c080b5422035903a48041020846180716401141b810500251180c0c00c00c0c2d80003181c035100c00601060030600c02c4128030801090 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 841852868 1250 841851618 841851641
    0x71a0402031f090606080a030c030e0102011d03130602062e0f1205061b070b0403170a140a09050c010c06061d1608040c050f0609030708011b020c01210b04 68
    0x58030058a01080307001e2181704014400308000e46102152520b0203092582d2142c1e014041c042e408004a8040e1320170350004402c3c02d0034060900342d0a4000790459a41e07001140d402c500c10313941901c00715141d4000a0345501c51885041c40c004c071402408203a404c05081600a0102c401c00ea04c400310f0700344000500304014155803602212410f0b2241003c40c0340c00800707880361130028a54049020303110304041c102c604491b001446880c8584031450116116801810a0082400c1000a101070010280c0106002c001184200101d80e100c681019044840400c8004c050364400c4410041650241c007021041e14044d0a00084455440613100e100a0a1030a403244007009041008040b04002c0701d80620501342d031415803600e20b410342e00c241602d0310600845228a54100d14045244d55400c00c0b50301809c0c0180a032841e540d40e03905414042d01100301c0e20710244102c4986803c4607840040d207a804460141c3d115002051040c1d2200980d850503120400340c1030f200c003044403e645490085402010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 841854118 1250 841852868 841852871
    0x6080f0105040519020f0915031b03011d070302010807110a030e0a1d01050f040f140a110f0403080f070807051609021c0b1f0c120302071a0402031f 65
    0x5800d2030242c4c100240302240007108001084d2000140c2c83c0e18180504841c030070346245280792141501038071a1415440b0040c2d05208001d012000d10160811007440701800fa002400441c06609000b03020015114603100b980e0b105d5030041000d0361107402a181c0003589418400b4242141c00002401d0001c903500035408074a9408119400e0304119a40a0062652800702035068588001410312540c040c8600d80c4101480c2e01c0c044010369842c0e001e801804041034081040420442c0b0f0310000840c1101d8030a034040c9040d10a01d0701e4440d03c41126402018907002c94500750843d6200081034000320031202c02c02c08207020a0001420000003400c20600520040c0800300e1018201e080b2240d0301c0e0000c5190900611050400b5400080d40d002d4850781e200c00416135100c40000306251b48140310741d4448604184da1004030541d040104500c000f030086001000b890844901035050f8800c02c107004018500c914030b00d03003110040034400e6406c140b000b416220f011440d802292000d102c4100b8000219 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 841855368 1250 841854118 841854121
    0x601030b011805060f01030e01020c03120105090f0c031602010908031314010e2806060b0406090909030804200301020a0314011a091e0a06211415030106080f0105 71
    0x920040904240903609007081c0050314090f400300d0740e078101c40caa0b1031b814943c40d45060a1583d1003034060340c010506d14402caa44840c00b415140304940320a1040f10b00440000020403002c0003400c200c18814212040202d186895102c40403061041e840701c02030455599604210010701042c00444c0109200b6a40c0c080c86034840c01c0c40300801070030611081141c0e24002c81c41640c0000460440070624103580402c40031203c0701c081100c04101c3c50030040000e841d000c00450400704100141c000d45a0a0b80d41c0480c803522a44d02400319150040c2c00340200b080180010001803902e42644850642e640c0c01c0751124034231402080c20b80c0c01c100c40e071102003074030b0b480f494103071880c100002401044295610508105010159a6a449115240c50188407503059603030702d200c80404206d1103160041c0c407590250360b40d84070041001c0c0c01c2c04180e20581c444420380082c0c044c028041d011214151a200e18040d45548408038403452900d03a555805540350a00001e13011301c140107403110b80120b0000030915 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 841856618 1250 841855368 841855379
    0xb07150c030b0f090613110409060308070b150607020f01111b010e0f0a091d0703050a02130504021503062806170106140d09020303071b080a02130b010509030601030b01 74
    0x8014407410f181c01010403c007085040e9641c0040840181303072580001a0310403202d048031010b4410b941004005504040d000002c11040074005d1405a028040044654403403141c5c82c04045440c1650551006003440301001515004201c3c0103203080c141000035101172015070403403d0007041c5440003500e0080804000040d60054034000700003508940e400d40c42c8580500083e0503041c0ba00030042c446a84070200a501441100c003034118280380c0d0100c4c1d40f00e507039a2070300a64034103850104a01804032164132403040702d15401024040c80c3e00605111480300c04100307030242c0b5000200102c0c0d00c034483d41c040c3c41c0b1041d15208070304400c5420390704020099003462800392010b0081b41d541708540c9001001000801d501140300c65002c0504001180e0300d042d9071000d040500350140d00030303500d4000020b0300d1040044032650015281940c2403012142c5075158182034503514005406500041c01c2440c5144402840d801419001d1301410118204841800481e10b041001d8000b15008040c03080148003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 841857868 1250 841856618 841856629
    0x50405040c0f06090803160609210e0409020d02010309030203040b04030b0a0b030c033a0f08250c08130b0c0c0910060809100c050403060e0f070b07150c030b 69
    0x30f80700509040b00c16516000804e5500c1c03088040c04410304c0f4028050b042040440e4102c002085d41207940d50140b00c1c440c441d5004101302000000d4085200420302607210306050184614080e001044480c040040303400540107405005000c40460008005c0031444c0c80e1400041c001545c01b0f01e0440000b0724210314480100c44013120300b17a00c640d00000c6034140301d550002d00c041c00800d20b0120078150b40032182c81c80d1082900d401d036021a08516144041e1045c0e07000203440c00b09890b96803807420b42d8a880d11604012444509070501d0704950b400c1030602e55004100c008517040c4503040641c90178002500c15800303092907401c4403013601c0c80014083e03000b031010400005510070482d81c0303d43d0390800c402170003071101140c4036000c240079040000400445040c000700968625012050000c404801e40050281c0d1284c042203e00601d1b15122901c01da0300055003980f4628400f005180603414180c4039801070300444821102420307000070128600040340074440440c4a00d803404036209500604012 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 841859118 1250 841857868 841857899
    0x2010b03060c070b0c16061d0d0c02060d0e031b07060f111903051b1e01050103201201060602071404051003031202040816080f1b0415050405040c 64
    0x740b04007800380c400480d820001158120401c034000603501da0340041c007650956403007100034003202d02d002d10f100481102c5101105180070b60006070f80c660b8100301015600c07900b140c00007940043e0305101c02d0a280c0504d905c18551840f0709001c80e070910302d41e00b0b200b400e2456144403e09072a08510002c01005c0c0c5c10101c811207004150a1020704240da05003055581c40d1810300240040000c440e100e130030f25006008840040380801d01080790034540400d4940d9854104c00d084003202c01d0300c8416200c00ca418440ca905990380442c007a540c00e048030a120000c0e1700d4060020741e11103a20a8291245102403040400a000d0b0750080c0800d20f16090311615520b41c01c2c020240200d081c0300800805002000301c800981345d040c180741c2c0e5040710100c40b1800034005c642210b480e0b4403449612505260407104c2e200d0072a0654401c4903a00d045e1442d4558444020740700881161135007040c505032501c1c1540008020052a400704038000d590340340020b0070f80300d0584040d95444202001480300451150031030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 841860368 1250 841859118 841859131
    0x6040e10091208010303050a05130905043203030a0e030909041505010906030807021005130b040e070201060e0106050304020411030c0702040605010503092a0901032108010f1205120a02010b0306 85
    0x300078541c9140c86c06000791281144c000200200025001d100c0e040c5015103c010308141c50b810407082c0382c44e20309000e030301c00c0500052001c804075a1400c1c0c100c002a4890503085800300000c0c50940d181c05641d074002d40000c0c0c820014074081404880c0d4140c4444019510550003146c04450014000034180c040b82e2040c1c125118a07406c152051012486440482d01240d40c1a44e03151158406140100c89034012051100740c040c1a02100188041543e0060400e85c0c500020021032a00c80c00320aa00700c4082d4813070f403000e0007408001084164003a401960340640043d02c00309916a9030102255143d204031550395600d00003084200550500c0c0c81164080c00702030801c1440c41c10448061940d40c16280720081f1140c613500c819080d60030100385c02d41a2501c0180602c01696100d01e842c110300d14a00810145002030f40c0420b0028a204000709812160a03180701d022907800d0a801d4020480d030350301c050350540308400d500c2c1c0300d05150320010039040615034000508c8488038030816042c00b070080c210 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 841861618 1250 841860368 841860377
    0x30c1a07080a031d0a02031002040503120a110d260f1803040b070c1a09010c0305030c0c0a0507092f071a0103030302041d150906040e100912 62
    0x4451200602104803000c00ea004038490751102e51202c0110083d00a080b49115490b04002d82c40140707203000220894500d2084055030241d400e0050600d040b402144140c65040d07002c001148100c0385031000800805019242c0304d040340303080040c124680f94180b00c404001034241c0f14550fa003003c03000007802a00c4520342c4042e2031820688011500000050701c03204126100b80f01454040004104450092603000c903c0740e11002c482c00d00c1000384801e8807504109102107169030710048412001c4440801d0140c581c0f1700040350a0310102c2d41600024054122640c08000b46182480c0c00c210004d41540701d040100011400e0503d4002900c010030790300d80703403880f810402e0340e59102c80151124a504080048584401050801c007032000352180c01030a81d41800c00c000b00a050b8950010404c3d2201c0c00d046d075420f0840e2070340c00308a141c000c865012044040c4640703640289400b03074099810000007440417845584898070103040002e6881000262070740c9860039000c1221700c2424883d0030000d0b051 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 841862868 1250 841861618 841861649
    0x801060219140a060e0f0105061c2909060603010c0f0905150f040e01080c01140d0e1608030d0c020a0b040311070905070f021507051605010b041401030c 67
    0x2690400701054402040c040210b005541401e01c1040380303110458101d102031001555110069031102285030144ca41c650a0000144072070401d500c00b10780c4d003a000c021101c0d0000c85915124214182030011b003414602ca0b51100041d80ea00400f594007444049001d4841801d18500301800c503151000050140f01c142c48644110740c1d000005241207500644030758082c0d241c401d143c95030a12a03801c11a49014010501040700800a21030794141c0300164200e135070125020b00152400c2c9401030700d40194043c2040580c00740c00d00b41d0400c00d00420224226040c081155a110021140300c0e044200e01703a00100300301103524174034040c0c00110421400a0025011035440301d980c100300041020342481029120f0004000e401c11548000305000c030350420050030144001412500301c1801c100043c860348441c403101c0c0c4280841d0724020315060321490301e802280e0800301400714182c0b40c203070b49556a03030040d5000f40e250380c01902c100c180d444000b9034403981149044011840b4030742003204a1002c2c1c54 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 841864118 1250 841862868 841862893
    0x30615150d110c030a0e0a050f040f0b120f060a060e0601180302040e0109110901081908040e071220190c0506040308060a061434030305240609040b01092408010602 72
    0x41400c0c81401050f07032b02041030a01c110800015040c032a48203a000009a2907c200e44400400d01d69001e4110200f680c4190300d40d100024142c91080c091b4585c419038500c0421005d40c094030409465002c0380000d074524a640341c001504036200c02980c4480e6945640304182000700100540d59542804c4502103020350424401039034640c1d00400d0b001c04000d1001039070303041c040f40e041a40c004000310361303104100c0d00c2e00000041c41d080c0a01ca09800c168100309680000c0c1400310907d00034071a8001502c0c0c01d0052138030300d417603800314080180810f1054441105e00881c0c820701046200d14000e864801c20741c00c01406000b82510705611100800c202c225480800040700402c0381d5141c400c0601600c0042c0c50404032103002d00b28004a0000c40301c1c0d2944650406425401c030303522a0145640050b0994408004400d4000a502c0580da00c40e0080080541e00c0ca0142c2c84280c07610418980740040503115291a030031007c0d42d00e08071a81d100601c040280c81907000c450240513280c9032020781035505050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 841865368 1250 841864118 841864129
    0x703080301091d010c050a0f03050412200313061e0801030803040c0819050f0a0302030712031107060209130b1305070e0d060209030615150d110c030a0e0a05 69
    0x1801000281a1545555001c140c006070601981c0f4034000d00030405403601180143c500d520025506c004180d01600c01c0c0280ea00900c0b6441c441c0d5006120560b0041000703d0856003240900d06003c482c21009041d0440102c041018040c0300c0c0303010000300b20082c20003102604d411103a9110b014030b1240c801074031103041d40c03213960141140d500000142d01c3e40c48078038005070243c0d01508402034901c5030310310148007103141300540580313a40104255030181b20b000c14601d46607100642e001c0d016070320030081c520000d40034035112284400346260003e04406403004468141c1c1c002c034004e440386038000c1101900f41c0352990800c0c0b4004402e100402144890754080744c3c1d140b049503681c0321011356450010700354a00400d00313140050b4005120000c108600d1601100a40240c2c20320ba0080c8030b02c2000800300708041e5002c0e81849802003180460035004003948130558402c90b0007100d110f0321440780b1596295444007508803030312108055038503420380004c018045104070301842e2090310b940030200401d4031507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 841866618 1250 841865368 841865371
    0x100c0203120c0702060304030810080105011215090506011701050a020a0c020409030e0405010b0c0f06010302030c0d14030f0304060c081b0d1e020304120503060a050f18010b190207030803 82
    0x4100e4040200d6807101049601c5001c0c1480280d00404004204000c25500020251080d4ac4a4500c003500e19241d4810600300c490074000c000114002280c40804101c002003401c8103104106c40106a00039076541d054241038003030744100309059035444002c154400a02800c1e0740a000034600b1030510a09150090150310444000390185560303080b0300c418144140c04034041008050010b0003076584d81e0403410041c0d4003400c3c010060340034200504160402c089041e9049a80080c014071106e91901c0030000c55265020040f80c020f4201084141c9041041c0050415200248003107a200d01d028101201620300180040c400c0023000401c105548007008036520144d0b00f862500754480d08a44040c50081c9444050b050140c0c060380d010000c80c0c00c0b42d030011441a441044800360741c0a50303450950341400141c0354a54001d85010041c00682000341b0501284080205000507154084071203504400007a0040004038000250b9140ca04010a00c1d8009c0d2142d01d20050055920310386881095000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 841867868 1250 841866618 841866637
    0x9010e0603042102030a09080109020a0630090b070f0915052205150310091a0d03020109050105060d0209010e0601022119110a020d0201030f0609090203100c0203 71
    0x80030001c502030140c100f00f0b50020030341e040d8407003807003805a08010350b030794000340f00c8000000d12400022840d03407411300681d00342c3c0740c0c058503004840342482c03002c1d03981e4007020b255a40d1000107040060741a41804040c4003522003004000622640c45050003608154004e01c4034043c0f144001540300040d911204101c11501d449001d0903624135610700c00c464511a90741e90105000300d0140f08561040d46000d807a0854404031280241c0c2c85103107030350210034002101d0000511016100c100100f0050f50000c0001c02c0c4c80c003818580c0c010f0b0030400230303030b9141d110300c0e090b001031390348644280410009100d03150b044a811280d02281845a50020b440c001c4140034203200c916423000400c0059008001b80220a02c4511030070074030201e90040100980c0052900e02c500050100c62031004130700600d044525074001d04c0103881d0129081d0240700300240240b0007213040695410700030310085030f144142005444516808151010700b030040500d0020040c3c01c0c0c1401c6444d014002c154281c00004559490700d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 841869118 1250 841867868 841867879
    0xe071704020904230d1e0806010c110303070b0705031005031209010537020c0402030c0f090d0213060f08010b0307030201080915010e0a0e0f1207150612021509010e 72
    0x40035500c2e150701c50b400a00904c8100c0c031503c020004101d401140c4900c8103000c01c10200703010815402d08a82410054400310b001c17407031115aa001003401d551103410f81c0c0101400f00c2c0c1c0351003816034400c08134002c111440070000d84080103002001e80044c3d01c142c01420114014000400790000c0d40016115000190f41800f6000841502082e035814440c54820340d9008224003e1403000c42c0210100300d0207036005d0050090300e5200302c1b903141510a0781e02134004440220b0421001c0781c2c0c0f1800079804001c00d6036000d001203007502d005995405041696403168200866124500701186800c0c2d07036113801080003a414080991400d46000804070112902440d00c80740c0740d11003840150401c0410000544c104030410000f10b40050500101805504502c508000c650196443c454030340c040400c1207017940d00200070140070349807194080c000700e81c040d80300f0312070020391003d155044580319440340e03074607100042d418015171520460041101c5d5176501c2451074492000c0c0020051580800300b1403040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 841870368 1250 841869118 841869143
    0xd0503090f0a15110d080c0406120e01060312110a020d0219031703100e0915070e180a060f0b0301050103110705030c0604050601080703050c120a0c0e071704020904 72
    0x2076403100d40d05001001c00c00c1240c00f0620140c8801880e4000c0101d4041d120700c1050301384521188100401c0348101c0110340c0850400b42005000c5549400d440b5001000c1a124103180c81c81000c284a00c0c0300440c410700070766600303404c4001c2c050600482d0700d20042d140e030444400c000c05611440f02c03454049604540f0400c04140050500c14407040c1d940001d8080c1c10108030304170b01e40c0181c800460182d50004012580b40d07640711070703403260000c040b22064031a81003546400300c59456150025000704050400c0c80245088030b0118510500c08004580d000100c41c080c000c0d010348502c5640007402c0020f650780c01e1a81441c20b44081da11041c85824101503481c10000e0b40c0440f8a41510f09490b1310105403aa40c04021f41d40a54841043e10103946030b0007440000912118001030f01c204803076101010b060301c50410380c10042d0041500442501c0c074000c0e8425000050707680038802c0090310540d890740c11942484800103040400c2542500107600c0540c0500003d07030343d2140c0303107580309a0000180c14030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 841871618 1250 841870368 841870399
    0xf040b090a08060109140c0412030f0e060d140c09060a0f05071403090109080f1e03070b01080d0f090506090904061409101506080106080a09150b030c0d050309 70
    0x454150341e204070450f0081d5000403425103265002045952000222011161160b5103040007620a510039440f10010310401c1d0750000780214240800d648190034000703000d40d07503070010407540d1b0b022410400c030703c0750340310a91003c1541c40040550400245034007103040100c0c42001c41c007540b20751005a014440d55030000c1100612410850f0405603110405482840e0003410f140d5603a0031081407240410030480b000b2403108400540030546444400083c83c0840c4550f41c14000e01040c0d10342c611f220300040203404003140c100d100d9140241040e1005000000182d44000c004202d581040001c0040e090403c100740d0b906c01083c0c6540f010210f8a1943c0743e100d601e0710300010154001a07503a10400344c020408200004140c60341d180c42c0499040c003a004044401d0540c41e0614052013010408103001403198511035800c05501015560340003550701c070a07440700d400d82a4023203400381409854403254446400c09200e48241002c054413408583c15107130b50752540700e00a401070a4001d20780c0d0302c0c64844 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 841872868 1250 841871618 841871629
    0x3f03041a03161b02150a200d21091a06091513020417032116030f0b1302030105011205090d050c0f0a060603031115010608060d0c1412060f0a0513060c0f140f040b09 72
    0x250301c0c9c9809410003243c1c2c160b150209041b0417400800702903405800008041d401c2c01c4c41d08512a402c2c402c091040403461700c0403c59105100ca1698241c0c1e50300340b00c08141c18030031013502c002e000f400030021502e54803ca103481650100b19054410501c40c068140107a00c165000e07603050b022118240450001041403194004100d0420003990003a40301d2642101d04403260300540c140c40081e40c03034070044c940b401154810360b80f003a80d005041d948440b002000c2640305801400c980211141078549201c1c4440407240b6165000100f81c840c1583c41d0380c10010581c224900d03661034440c10000e03203110b41601c0c0180e10f000c03405104050a000c440c1c400120710b40d0b09c003402c0321001a8424848030200c1d417140d490522108203c07408a01840c06051010006440011418442d440441e1022119038515100070301802d405400700f5000082c600020000032014050b6501c1018195501140c54400c800020200d0200d03c1301c0302c3d00300c001001146e58010803001103406903100050a15031f1841e0b0b1501145 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 841874118 1250 841872868 841872917
    0xa12030b15070b0f06240f041a0d0b090f04030c11060c031903060e071206031a0403031a3f03041a03161b02150a200d 52
    0x301c50240c0001c071407040080c0403c5281c0121804012582640d0b21081400084584502007240b9109207210003076001c1400c20081a0950342d184026051941e5500c1c4040350b15030a014a41c0851004906044c005030544500040480115140a0241400301500e409200060703c00340802101941600620000141502e4903120150801d0355485400040903100d810062405000e5001484540c1c52940309000d0001950403c00500e58070b03450380041503405806042001e0143d907101c0400101103862001c2c848104401e60511003d60724003031900400301c0f4000c2004a810540d0f80704003180f56150b200280c50518018040002c03007024010281021280c024003030700d07082c1003e14041018a8011000e0002c07910804042c40142540c1080c03524a400100d03004000303100402e402d0b818843c4180702488804102c1402984074030500d03008600e203075041000411b21148e0000d841e28a482e802884032100c0172100c01081a8402000c6000d911403102c050310760b0801c4130300340d1681841d0480c552000d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 841875368 1250 841874118 841874149
    0xa0f0506060103090213090224180a050105040e090f0d0f02010b09040b0c0702150406170901050705031323061504020717030402031006060c12030e0c042d0506040b030a12030b 77
    0x2120554030000e109c41040d48404000b42e5011800141c0e44074604000642d8019544140c40d8141001d04006100251410003815010a0301c2004400812224280105446e04039a5664005d0a03940342401900703460310b1981d01030180d2500400c00c4080388048241c66003201c1000300060742d030b265038000151074003110001d4061000c400030f000602d2540202c02520508100006184150380b4481410300b00d4200700c510002051040000580e059044240421013610480e103c103c602c030f01d03840b030319060003190f00314603900c0e404681406100d20b400d160f600c4000c0d10484041d40b0b00178495507501502e4440d040c014544600201c0800c0840d5014400880e00000d414001c103c82d96403440001d02141400360709598480c00c45416619040c420301690b9144240800102222040781007070100800401ca014000e182d41d099104aa0300c401d240c200801d018103070b80c0890242041002c12040750b04110002d4400e07404040e10718001110103103000c60081840c200020000700c1107001c20303503009114642 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 841876618 1250 841875368 841875409
    0xb0c070504110409050f1909030504091b1b0f0f061d1b121905011b050304050d180b0d0f051303081b0d020304060209030a0f05060601030902130902 65
    0x1014045003450b00a001180c0360494203101e1900e420000c1e2480c55015104070001019181d01e43c81e41660581021168501c285406403800c2d545980d20011541e03000700540414503400640d14046034011119070340c66144840e0f0400c00030305a03480c10311030b00d044a801044043c40c040c001c001d00c0704a5000c3d0b41c60200311400d50881c604134141d440d0301d03007030b00454124441502d0130450f8600d0030000921803a01260100a03c41c0c2d50300c040c40c00b034000350b200104441ca0341d203030700c4001c3c16454189254640da48807031f1181074503400c06140c814180045401c1c540c0801c031040d183d000d145d2110703402e000304817185940850f0740d43c240300e410040600b21000f0008407981c140828000f00450085180080d64041e54584d41d4a45514507041404402c03001004141002482100481c181541c01903821510130103005140c840e40c000480d050001d0071038103968840c00700c400c038414010306110003644981d0034130301004015040c0d800501010f9001140c82c010b00ea88203000c4d000c648841c44c6c41119041e01c05030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 841877868 1250 841876618 841876631
    0xc02030901050714010b0d080403030201111603080a0f0f15090c140a0201020d050c04051306080c0f01180609180c08041e2010050f0d02091c0506100509040c0b0c070504 74
    0x4241c007884d1301c42cac442140150710b0a848980d0a424210640300d0b094070505010040c0760003510122240c52001c3c140004540d540d40b2540d6102d04641b2900100701c0708084003240d02541c6006101401c48998000c1c20446e00302403003801503da01648104020240e01081030310742840343c034102d0080c01510b08401a0b0303858103081c884480035030130280c03040b10411075070700e560700800010345401d40d03030706100301d41095001315080001450440340803194002c1c189850350703a4010441c0e031900303005000e034444400304200c010705100020003103480700c0a035808400c0500c608a154a002010769a0040014218a10540c900c0002c203000c00d00261002d600000c1c400d10b116000c00d8207000301007080461507c2808014452001c2ca405903007030b1584985d04001c1c0b1414181040301c2c840180d07104045c2203a02040c1d800f40e0005401c07165403c2400180103070000c041a20741240c5d1584690100d4000903c1540610104030014a10003415001d403244000c0c0551210460b1000d24500f81e4aa00010340c45800c041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 841879118 1250 841877868 841877873
    0x150e0f2d030a09050a060302160209060f18070e090103030c1113050901050106110a0b041502070b0f09060114061b030c0f010b040c0309081210090c02060a0c02030901050714010b0d 79
    0x8443c40640f02d003102c9400a26a849009500301d120b224906600c2d0318180c0580005803418282a585c01a4050481403103110300100182c20901603040100115074100c0500c0440b0f0760103051a981c0c46015103507000b56505584002d415024451b0700105a500b060030445c0325a00c8000f000a103480341c3c06020320050034041c0301c0360b019160034080e80001030081c00f00c0c18910000007030004800c0f034010010109030f0300e40c1e494840520031202d14910815408100341d0001890200000340710300f20340c0002c0402424115103a50401206a120010240e1a517001c0d46a40e55072004403080b01e5014103600720841c0303204440a086000b1041c83c07290720701602503c1c0341c401c81c042d00031420f54a011030741005920310031641030f012140314810103801441d0900071684020f0300b10400e5500190b4035140400b900d9503c03a00402a2204070088600682010091101034401e41c00380e17814000c92130002d9810040c244000078040c0c00b802d90041d16480020158200758035080d030010807060405002c1449038550b60 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 841880368 1250 841879118 841879127
    0x21e0f060c1e030a0e040504060b09010e0a05060406150c060e070816080303070906050d09050709061d090d2a030c030206070503011202010804021c150e0f2d030a 71
    0x1600b0350400c820303000d40024036414010080742e80300861a21842407042902c000c0c440200b0005204450480e690715090010ba51aa00540d0013003401100711382c4e8500d0710a00500680b0701c083c02e00760165042960501c02503503040c0c00d0700281034440c90400034102c01814600e0240c400111401094094000041808880801e0f00700d103a4140c004074031050b550f100e00c8240d9034401100c8a0000480a400a1001500ca0002003050050015010500e142c0c252665820f1100703c0d807011101640d0340000700900c4401c80c41d407a884000055103200c0e01d1400b181c006880d0140340e0390300020401c00d141600413001d000c0088800f00000b0301d090b0000071034103140186c040700c0a035070190094400c020000d92124070890460781619800000f28446070340c694015142000068002c992080e034040c6040d11900340c00401c01800d90050907105a0003244000000444040d1804002c60350018407810911110008402f540c00148160041d441c0c01c40132495240452405c0c000c003480e000c009034070007006600 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 841881618 1250 841880368 841880383
    0x204230901020d1a031203330a05030d1202090d050a0602090306010503070f0315060e1f35120304030221030106020a15061511010612021e0f060c 64
    0x21020100305810419101503100c042d003404440c0d051b03120049281c008100c01003c0c54115090044040340e001c03842c00008451030700e0380092104c12045030a10201450541d070120020601540a00f100303480508009050307502c0407680341d01e25500000c101380e0300d480b0031108101d042c1e0094140c619281c8039181c000069400440c5403031092040c40c0c0081131030703d0080380c40012a4806002000401c0c599600c00c0ca64403a200490160541d90304c0700020401160070700c9034400c810a40202c000325040c9502103a002415410601000d600d481c0c400500300a010b0754200c0c1d00e210315105e01c9010ac83c401665152030b5114089500c203a20100512003010f400140d1003550300080703481d5205042c08260542c60304d0000344110340043e40a0b161f01008030b00301d4840c4480b11400250042402501c2d0070030110401d48484e200701c000b9440389a240d15810007807286e200545240c8985501c0c00c00d0030380005005841780f00c0c4259000c40d0810481c801d80d0764009040e000e9030380c05001a038460440e5100262111038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 841882868 1250 841881618 841881637
    0x6060d021812060609150406050a150f08070507110310020703051c2904110316140a090315020d050c04030b13080d0e07030c08030a0908011404020423090102 69
    0x1090307402d601016070003054280c840c0d0700c01303086a2891b5a44241004e41c51007510801a08580d0b110808a51602c2c1c881d0604c000d40341b00b440d440c01c0302e404200000c0554428030000410000700e5070912480d181d000b81103c0100f0341200011884010b4078001a0400841c2900c2c192070501c00a00c0d0000c064206001d1b10030901264030000303130140108000d4007a41c0103080070341c940001510a03c12001c0715408000303840b80024200140e07a418411418206910640c1e8116002400d44030482c0320a900881c2c0c00022059410054141090130a0281c01d004480c04018050491100114003010b101d60581d075158080da00d041c411030805100c1081ca69000b0f00041d2040c080e0000002d11141840701082c0b00300c0c1d805520581307040e12402d44040201110804004070340180c150002c0841c085c00c000f9406800f03020065030350b8078032803800540010000e03404008a83d0425803450500c0c0c604d41c0140b503100303805880205402140c1401c4a40103141a04035001c030000303000c180070503c0030550240c954080d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 841884118 1250 841882868 841882879
    0xa1814011206080303270a11030c011707050f130f0f0b0a0c0b0901140c0a080601020a0506070e12030a0c0c0501030e07051e0d0f030801090603050606040506060d0218 73
    0xa001e16030242c036401c0c0501c00c42d5a2041011480c0d90450503118650340f02c031001ba4490050001d040b035814482000003d81e05186000003078222885c06006200f2a10300034205401001c10203001d0740001d03a00100002c06102c40031803400c6d04034607a20304440400d02400f8030701e01e010f510f074010300c03019006900841198000880010404d171010b04d0407a484003001d0f0f140c07104105800c1c1d86903201100010003c3c0b455540301c200030704200c030004e001540038401407040d240d10340e0b03098000101718050042c049811544100706601c0484e1003c108203030444a1441c061514081d21008218010924032000e103171403000007842011598000501e91660340b00e41d02400c05140c1d14030045003504d500302812061504120000c00841c0b80401c0d402e43e2000c04003881109a0344501d00081d80140e00c0e05042c1c0b81842c1c6210308404041e80021294098100601b04104940c1161100d60751004010701403801280d40d4004149a507a41505031000000409815955035004003a0f0850514900c8072036070050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 841885368 1250 841884118 841884137
    0x70605070510021c0b1309060501080d08040b150a030213050f0109020f180a030c12030e030d05040302041d070801270515181203180106030308010b0a181401 69
    0x8880e80e008407407103060303100180c40c10301d00c1804c0c0700c000420400c00a01d6000d1350f14040002d00300024003401800d14041d080014144d8944904641403040320002c18040003103000070040001c41c00707100d4a41202c032000e064208446000040341c2d001000790400795000000c0d003180020080a6000184035070380caa02c80301196646d5001e41c40c247c0c0036000c0b503003a0403d414404516900044002e1203d02000141107000056413038445252101054000c003107071048040d01002495000a029441c0b04401d5004105a4480000c01040382c003460000034070407a1039031b425401c80d518005c0000104d1407900c00361201640c1d2107024500802c1181c0c1d01b040c44003140700362110074a001c0c07080400c0b041d4009014095902801c21340c06990380005106101d01c0d040010000c104100410007021508004100d107a620f0030030070550f20108495600d410626810541c041c00000e601644840c11118082c2c00251994101c502c1a1443c0790381148440303103a01000c000285500ba1412030b50607280c001e0302c4041d00e0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 841886618 1250 841885368 841885393
    0x91b0210090b1902040e090703021806010903060b040209190611060618070203070501020703030911060306030a03030c0203212d06010503070c0210021b0406061d010504080706050705 80
    0x15a640381002505003034081000410520300e052115030003c0c00c940005151603215240854201c1099a0103410340d03012103414011410704040956032a201000c440c100c610b0300c880001c060400b6400001c0200e80c076010385210784d8840d501907071140d0303000a00041c0035211006012a4524070b5110340c4001401070990b2568610010510a0258801401c0320820b031a80c5032440e03c16245c00780112045210130880c43d00860001e10107800583d02c240d5000c100e80c01c080c10203500c04c0b0801c001180c0b00d41010400e1014a6900080307505071140d041c10041011440441c0a0b4198010055006038582c2e1605c91001101028a4294815070f003c0c581c0b400d000e5590043c0c1f000c0350312404c8411a09650200100c0c0307184d030040f800b071a400500d40c5400b9074040c00a5010486521500c029080507a020700000c2d46900d0040f107881081060036501009001e141c0000102140098407000001c40b680601c038090300c0e48141e08480140103070f5421100001d41e81c10006009520416003a10341e801402d680200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 841887868 1250 841886618 841886621
    0x61009050618010c140a0308010f060203070209061c050a020a06020a02060a0813020402040e0a0605040b0f1507141b030106051f1101050a09060b03072d091b0210 71
    0x191400588110b06142000e000d48121003031804801d41400524446100007407500c06080d000d404141021b000302075000d14000e400c503c0180c0186044005107170b02480080d50000580d00d8042d0111001c06441c0c9580d004124084410314405a03a00d40b110244420301000040301c0708a41d20a0703c1b1085d15a503550b07804c988401882100070760180c0104180e01c5080d01c90360309290016141c0800080141890340042c0c02c0f80d1041d48020a4180034000304041c007038a130310075000189001d84052102e0713420f800001d14281b070071803209c5101e400447d130301d1031141c1e80c04010b40d55080c1c0d1000d0b4081c042c62626080ca0750f00c07035141c8808108801c0d842600c51141c00c040c0228030803200050303c8401d501da403a9500140b130f00e040010160803c040900c010f40c5030042401a140215000440010303040395605008003900e01307a20100d0300a9105070420007818130b4400c4815000400b070030b55414483c3c0364500055130038a440d070020300e100303051194108042c9444560f83c2b05148154007110350282c0c107030301d8400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 841889118 1250 841887868 841887887
    0x2a080705040209011e0e0310050f0f070203030c0a090801060801051b040506040b28080612120d0519060602010c2a0b07020c04050c040302100519050d0204030b0f0610 73
    0x50000d140008080c003694151750b03d40000644d10308058901c0e6010b0300c0401e10700021803030b6071301c3c43d01d885d801440640c848030703491107400c0041419150003900d406100a5a02e00c002740c9600c00080c00040d00043d0680f03d1052100503140d10b000912851b40c0d1200154060b04050321121140b92040429124000c0810100c07000c1b07400c041e001702d050a00d050a003250351382045080d001c03c6240944114501d64418265100521068564001d24203010091051110703810f407962603d139124842c985460b4084a0584419034005180802daa54074054032003480104084c101d0f01040c100800490035607010340265281c140b4503a200450084070b60420425461140000669030900c0e15540700440c1d01c00038035592100c0680110740035106003802050450380100e618100c42c2901040c01d01c11440e0080c2c020102c0c007050700d032407410521080400c0c10411501c050b90340605c000000c00c0820404542c05032801035070842c0050b00b45141015076a0040c0c20102d42140c40783c1004802c1c0095680500380c1c00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 841890368 1250 841889118 841889137
    0x602030412030f031e050702010b01170109091106030103050304080c0609010c0b04020415270c0906120615050712110d0c0213090807060c09050112092a0807050402 72
    0x5411100d0798800399565200340d246401055180c5109003000c0340d850a07020300318900c0e01c00000b418038010b0002801c407a0110b10747d031304001156400c000b6441c1500807243c1942d0071441d00248009103841d1505052104041583d00034a02200020070b200001c400341c01103d80003000d030741003041c04400f0410188540900030703000c1154101c0d03010104514500043e40144080c00024400207004940420803441c0d5200070710659003100340c141d281c000100e41902d9a9001d0000f0b001c40b20240c0b101410b285040d019600821511a0024071148060780050004000c800780210482c5c01380100105142c0c0402d50680e0f072003010320707800d01035148030f494001c040100c41c0e0302803c00a0b03100035044419040180050f0380c00030b00143c000300c8900d101d22502207050700c40d51a02d543e498952410101740c1c0e051080c00c0e41842000ca400b0011030360440413134262020003030700002d4a0741092900301c0f80703d400c180f04950f01c40c000c0ac0161b9034a0f00400030765425540d4050440e9a066034800c10001a44640c4400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 841891618 1250 841890368 841890389
    0x12010b07030f0e031f020a030612050a150f05040b061f05030c070303090803150a0909020a120f1a01061d0d020f03030d021c0f0212060127180606020304 67
    0xc102c40074802c000020b0031640041c2074410190a800720740c050311200790580580241d00141c0c0390301158140c0b15110061490500c1801c038a5090b4407a02e0300d500305d245007d404800101d4049240420b203900c40710a05124210030402c5007450b06000380d07a800c00300e07070940c0101556143c80680c5010342400015041090f40d406145a031120060b039400d40241e1011018580c07200b03a001d000566020141d48108200d0390925600705032081000b0400030168440c5194518290101c0056151100725406031500a42c40c030390403113568504000d2006a0750710240c6850150301e40d6001203103104030080e0490f840c40c0e850000900b0310344284184041c03401000c070b0348110006040c0300141800b0104003144000101a41e0500080f4100503060360b10139111440700c0784407110000120f4005109400300390040740c10440c2884040310040c412507c004d00f11505000e84402c800c90340c00341110740c111044a0940c0761346180760f6201c0a112081c100e80e00203034a15070404101042c00e910010664041300e24000303c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 841892868 1250 841891618 841891637
    0x20901081f26010501080309091308070f02011e090302040c02010c090509182b09030213050402040b180603010516051b1501060f080601020c010c200301050c12010b0703 74
    0x6540030500b461180540203101e04840b2504980c0702881428000d1004902555481820004000d0b03a018010b04a012850420a0900100c0d165006540c0080d034488030f0710000c103030300e070005a4014400444001d8020305008a950368280e01a141300116032007582c1c180040300f500303038059090f6540c0c0f400c0b020003d01600b60402443c5840f0b1001d03031b000f2171901060710f003203942d0800e401e04003030a0464500031030b0200d4400740d4498688409100c01d40c074080c50140251411580055485125442041e00070360700c50b4081415595a41d12006940c1c400600d04d880c003009542c2001101c2f042200c56522951810000441c01c2d585240860708220031030b81c0b1240340c050351032003251502410301001c0030507100c1c0290035500c0c5040800164080c0400781c071240c110007211240281800d00c006c20045c115048154800d1480e604204201b490fa03510a428401003100308c44071602d48000100210350560900007031180314003000b00140303400051441c080400303a0301d8050b4403c59105100005001891501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 841894118 1250 841892868 841892879
    0x2160b0c090f0402210f090c09040809042307020d0306080f0606100c050a0305090306070314010909050f19050f01020a0203071e050d0306080d08010503070618090f020901081f 77
    0x500400f9294560800140021781c1e411041c1c500c800d0842d510040b0145140138405080c00c1017040151640e011a8118081c0c6402c0da40c1c24901c0c000c2c0c010300d50169840b04250b0765041c0c120701506105824600b00c0300755901d052040250303601c20b504c80150201740b80c4000440c000b1404512100d411a8040081109864a00620100500e41c0c45c40d5000c01180d2010354000620501c4000c43d150300035998036071103907030356401c060803e1b0700608400149440c00c0d8071840f82c006866030f8181102c1c14a900014900300d1400c01900b0201002d0310580d0714002c00101c1c1282030641d0102ca19480e01410407212108142c1454500700d116454074800036a00c1440608001140078401515100340807042420784020f50751a02d260001021014020030b844802c1800041402c10110241c03c0c1030b0715200c40325500d40b81c0485c1c0c9880071401503004200356825440382800000304844028100714200f0001d00c894420400f0007900100c4401c1c0c001000003010460300302c50b1040013061300b201200101c54086c07600c0d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 841895368 1250 841894118 841894121
    0x1a0a03020d120507060f020d050a02190513030b09070911043b0a143d120f03030c080103031e0228020f06210a090602160b0c090f04 58
    0xc006120403c02c1c10081440080c3c10782c003c0c900680c03000e940c05601c5529020704407003071741c0707009007001c055910501013100b0050703404580180f0341c1c0150928a9031446043c00e03200074442c1036040640407554210910040f1140094403904888103502c0070480c880755110380d01031504c0740b8446c08a252400110f0f0042001009441e00d060f9107849130000005040c1c02d1141e0030215003100d500b10707074a0361401d200fa220724051203056807011941c220300100200010052075986403020400e03014a0091802044100c1124641c401405090540b155041c0c014500710003a04110101200024140401504c4aa0094840c03d040e01c1d49130315442003ca11900e102c90000031000c0d080700c00c46c0710b811b02550240c6040d4081900500140101c0c010740c405078018007030310400484100d80034090411651101042c105840e6031401c0008000c3c280d60307210102c030a0080c3c0700a08026019620011320b1121502903200080d580d1440782c0ea50301c0d00350f070f15800e034912a4000c40f042103800981c90b00c10280103240a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 841896618 1250 841895368 841895393
    0x150b01030f0e0114090f070b031f0e04030207080d09050f040b040f2004140108090a151b0207031709030114010902040303021207030207090e0a060e011a0a03020d 71
    0x62400044042801c0100c500781c909010355000a40d5540c2c0c40c035400320929510840c2d20034030200081c45040c084c8001140c2c0c40d040b503c142080e281300480442c60080100ba02003004100c5e98482e0380e6160b407221965040c244069030124058440c03800c001882e1200440c54446443d140c1d140d500411346400284410300c0000c02c2c00e60b43c01645c0b0b20070402140c0d61403150f1170722009440000a0351102c2ca0b404143c80200c00d0114107a0301d801413001704000c01d9950f043c007034103000c286400627468071132900e100c0c9070401040300140b20030340c1c11041c01d01d100b00b998003140380c06100e40c801c408240281c96007039840f4405400041d1030b4004501b018000b980091004200c491006400011400840000ca41c02c40e0004e80040b00041d400060030010306a04022600480207821000380c40c0600680c0c019541e500c4502c20400540e4a500d100309102c441031100ca07101d21382044003403022042201c1058000c00c601c01c1d01041001c03070100c009549050985810b01983c0d03000e1714a85100715140c546141d2045d9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 841897868 1250 841896618 841896641
    0x402010201023711030f07050a08160303050a090f020114220602160e04020d14030c10050114030619150e010e130213090503090d0c030209011215 64
    0x102004401042c0c052684100e02c5580b5001107900400c0e14000f080e2103031102c200f00041004481c00d00a12151004412035000d41501004107030340d03044e2072820a0400000541c050310b500c1000c1091005451542002e140662181e0f074100800d03520042c404c1d04584d20343c0c401400c0b21496084000055009904007504924200b02c2d90741046402c04880006804a039002642001c5219040095680402803004200440d00200c40b0060415840c0c1401d181c004001900c0750091140c010240503004207501c0f0460685401c0c0c0b55282012020320b9900e100f06010700c0d402c5440d04000107401c480301c6141c004d81c0000200500f0140e01c1761226810a4403070f03124030880c1107a80f0010070081c4654401240000c018182c0100c01a40c0b41c0754a910b000b01008000210700c0c2c0030184010300603500e008c40344044607408600002d0b50b0032541013107840e5014001c9182d81201c01e5030505424000360310007041c101e078800c03104200d00317a032103031a01c0d03004560440f0001c102041030f040d0307888048540e0b01716104280 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 841899118 1250 841897868 841897871
    0x150902040f21032703080403120e031c0903060c03090b0a0b030d030b0a050d0b0f0702060103030512090c040e1506040b03150c190905030c0301110406050f04080303101e03020114030402010201 84
    0x2a1311039500c280064041d030089500400000c0c2c100204402d0304812902c021182c01d25201660740c0d800400c0d1260a40344040a4005660101e01c1495014115001c06150008410807955070300000c00f07002800ca440c01601d84100400c0007405010890040e00380500000c1e014090000d60500160080c04a80b401640e0040400c4804103954880079801d508081c002c892840e014108046801320070800a890a01150009001840825000386c200d40440b85500b0311204d640e40c8504aa03402c0000040c0030365031085c1040c4610703000c9100001c14013020a1000c4408405458490401048660b02514203825410485c04030307202d17203c03186400742d000072040101c0d468001d99150f1f50f08203a2241310340308d02245411205100e40c0c102042162892082540204880c00c03030030210410700c0c0264403c202c2001400915a080c0611483c03d8900604d20340e002c03641c6a0604001701c1c181d88030359014124410309551160080d4044026102c02200d80603155007040c6c002c0403482c1c040039803009005a0666 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 841900368 1250 841899118 841899167
    0x38060711040203070519030b0f131404080c070b130506030910050903070b0c0a081f09060b09180f0402010503040206121014060a1b0501150902040f2103 67
    0x140c940b0b000451003500181d59155441e000d1146000c00000529074803000c06140501100303054880381c040c621182c03421202c074080c1c40d4444000101408074000081710000c0329030b05010401400d000602200c00060040d81c02d040e89650200c1c0c001c0c01001c1e051500c010030200200020305054000355040365800c002d039118080700d007804409449080d07412004c04c0d0320002c0c00d1360a02001d260440c0c1c0000c2e204c0c0e403052401d5480c0d00c0c010610a805000c030000b4a907154150141024040010001030010840074800c0b640da441003040141c12801e48079008040d05580d580d0400d820401d41c9200b020145507001a9484540044443d508000c00c1281c00c11002c0011800030b0780c01c01e0b51039108101102c9030002a504204500c1811240b284031070f80148024043d85441c0d40d04514966041c505040c02c44e441c00101d801d01d01d003d000050a104541c0c00038240120f04280e544e00280f0680312800d1003240c807280e6640c0000e0307004a0390008012507040840482c40040d20071103901d0b0442c52860404081e4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 841901618 1250 841900368 841900403
    0x1c020c060d020c0120190306060f030522050304090b0f0a031104020904110a09080105070c06110f0f040e15090a05040c03230114060109061112030a380607 68
    0x80c0d16a6015051085d10041109400c0c48903511401c034035054035141c28420700349441000341510020081c49024192a207001804010003d250440342008001800513140801c2c1099912540f0030300480706002c1c00d08003818401d00700401c00c0070450401400c210720283c40c40d1601904481c1e0011801d80c0550204050070300ea6645000da0a8284401040300e90b4030a1039103030160060040da4400070310f503414a010400c07415048501a0802a007211000c04e003104910b210044078841e81c3c0c0b07042c6d0080804541600c060b403a41000e00103640c1e0104000c0071980303d081c0c1c204c0140b103400315025030014000000540300701072a04041c1e0060320600c10511201c6e02da075102c2c0d512140740340b000d00c160050192038a030040000d026204c1c080e29110010643e50901c9030008002040c240585002e0000c0c0c141c2c900300900c07040000c10304150030310106607224144401d07101c0c0a8a61a007002c41702c01c100c0500c8030a000e8950103441968500d40c02d4407410540207205200e56500121402c1e42d07a2205c0801705003d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 841902868 1250 841901618 841901651
    0x60d2d05062a03093c010b0112020a090b0a0801030309080a050d050a03091718010809030d180f0302071706151905040e03070b09030a0509040203060a15021c020c060d020c01 76
    0x21125401d60300526001180e41190244e50380c1700312201c1140c1c1080c0c5500c402d81d170003080902c03501404280240c1e4400b027a0b081038071800703503030383c08054603040000b01181c2040c3c1c882d6280d8140e81c420707583d0780710039070303843c1303655543c1f140c2082e005071458003d0040005114020710081550152504003c1460601e1303803251400b100b80301d280c0c18145200092502d101028500700c14040c0c020034205901035007403071b0420342d5a0307009101c00c00e00c4055551000c0b0f007812088202c1d10003407c1d030040201c4401520f0b407034020748400183c0700301c200700654041d8183c019080032a00c00d1040c3c4101056601046003e002c0012941c00902100f19080e0071042c0841c441d11030f8000c8101e016403110066554a0075840c03c00600c0303100914107d481d42003880103280380c030341c040304603040d4807002c41d800360f12074850200150500c1496800940200051b00700451707580c1e00803400b1107103d000b4a00d90b1918011120707003642c450604180156108108000c0d90a103684a039002e41460b2540200004400141412640 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 841904118 1250 841902868 841902913
    0x522030b090f0105061e0f010318080a0e090c0a0e060d0c020f062203030203330f030639220815060d2d05062a0309 51
    0x201504402c6003403108034424081d5581108041c2c5c1c1520780c000e104008154044000411584100003000100490303038405c0c0c00104030729034090707041340c1b0301d201d070b03140401041d4030502c003540202340011041100742c0f80120100d44141d80802c18a454544204c00c01c41c3c0c041690031030687c0c000d506001440c0180308074441ca28001c0840c1d0021b1500c5070003844181d1412000501010f840d280b00240d840d42c490980c00c0802c002981410b002d600d90b1500304040d12440300e0104203e40e41003200081b108500c210004803100e0100556000c415803140b03c050644504c400c888418100b14a0b400041c40d40b201e18224140c4100b5203100700070101c841ca07444420380d40c032030750380050b005162500080c0c900ea192404640117140000050005505264982c1c6c400c440c020a2584240c1d052401102800600d58901c00000b040b1000300649800b1050001007400009406941602c00c50300044da43c00004413203a442059114040d50f154203131076040300c50030b5000030403910340c2e8002c410b00412600083c0341ca52 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 841905368 1250 841904118 841904131
    0x6092d0312020304050406051023070f0b160e100f18090506010807082a1209070f0e241206040503120915011a04051917030a0522030b 59
    0x11a44e45242c41c0410060317032550f40001d403103440300ea041e082002c1e40004148850304080107800c0c100348522031105050340070ba0400540f8011028540d101004070202d400752040149210f020001d001100b0210380d481c00d581ca1b12900b00e008501c601403814040d030f4030504428154540503549101d8903c180d29464840d03849145101d8884d03007030000c10340e0040300e000e41c007189910b8481160300d0420111249000e15a403022a22041c82c0a900007014407803040316180c1d039a1450403507c0381403400c025036584400e031047d070255000004d00801c18850700100a4000c110741d1419240d0904044821a03003004200030040c0e012082440c000ca40680601084d03114174082c10185440d980c5480d540d0705041002415610769070894003560b8100c1000c1c035802070554000000c400c60f5000f08620710070b207501c61504000c5c0d100607034000004041c090300000409890b0805504820441c2c40c0001c150382e4000c650342c0d03502150701030142186101c04a050301c0020070660248244440e66038891485828060314031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 841906474 1106 841905368 841905373
    0x3040324230619091401080105060103150e1806010801090201020d090e15040e070b070507060e0a060810090903050c150915100e130b0106092d031202 66
    0x724002d4134008604200d0300c540c4614542d00d1150034850300c3e2266080000241040d440307405207411a0300300321903100c0c0c0507050142080c1c800b040244854041031082202484000c4100511707802050004000111428180002418107120b40348410a110f4603820402001c2200024545d11184540c10705624000000000d4060000c51075252414031031400003289030903044c001044494820b0003125541907540f40e044d502400404901c56005642401c10006180504400340e031040e500e002596005407a01100b200b22554490285d00140001c1b6580818078000c1203039040c1540c00504082443c039000c04555580c4402c841000c00d9681c03c040852126084c03440100702034282110700c100140f808022081d401028100140c3c1c500f1582400003503805e0040440005480d400e800d401000c200c400c9008501c004540b0003d9403200404c60008013103007242e0303960544940b16034007 = true := by decide +kernel

theorem cover : BRFrame.Cov 841726618 841906474 := by
  have h0 := BRFrame.cov_init 841726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 841726618 ≤ n) (h2 : n < 841906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
