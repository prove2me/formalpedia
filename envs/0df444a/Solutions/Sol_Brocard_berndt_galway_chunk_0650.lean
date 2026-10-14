-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0650
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:56:17.651712+00:00
-- url     : https://prove2.me/submissions/6e1aa2b3-9bc0-45b1-b827-084bd1797f01

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 116726618 ≤ n < 116906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 116727868 1250 116726618 116726629
    0xc010207051009030e04050a0608010204081c2d03060f060c050f03090d0615080609070603060506040b27041d16120b09010e010213141503010b0a1206060e 68
    0x1a0441c0a5020880e09211340c40c028034280e542e800b25071140d43c840000c6030340d00314541c010f0b0003c0d10140001710350b501d588060b010f0b6a01403404d208088030701e105a161045a004141c0d244680387c030064a038600142c1088901010101c102c80d4400341a92000c0102d9103612011404010740300310f0300ca8071044051424610700c1c00030000a000010362007085201c000d501c840000c100440c0d4840c1011805603c0c1d0300645190400d00e8104005512840f01001601500011b14034212091910b042003090b444500780705003482a400b981c50707001000c20010344c0076400d41c0319680e11400340d0f00410040c00060000202070714240849290b244600d011207240100e0309021400610b0080c00312003482074600071203609104a2454040e005110080002e14607480a401c95a502071400000b15650310541c20220700054090107a1100710070b00003803070b440a0902c06a1011200500c504d864116842d1004440299104111800800484100303200315590b240c0202000b030801515218420f5002505004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 116729118 1250 116727868 116727883
    0x4050f0d260106022d12090907030c0804031214010f0906050102010209030d1133010e090a061a06040b090f0a0e0a050a02070b0403030509010e031206240c01020705 72
    0xc09202080d0010082c3d035400050030580885a0010105440ca136901010980c4041c00c10040d81c9000355038000d00e02c40821002003a180808417104079540c1c813820400c404803441c103081400495101404100072038021422410010304880740860f060354040e0000b0003c5500780c0c00005110401c0c0010303c0100b1031401180c1c0901820701c02107003085c000c00c3c006a982c43c0f1071100c001c2441105044141a48800d2100701040745d6015115120f20700d54440c0e034500700b403a018060103100d056000218580f8101071109008844650003001d0314031b903940b42c00303000385540a80c0c0c00009150344402412070312040f000d08001c1c500c0380442500c440d4500d05001c4103c0321007141d20701c07881c0000418480740c5001c1c0041904a1340e0640c001806981c0d1006100091240d100050118043e00f402c1104050b8582c000910480d0060000d00c81094010071290792805440080c16444100314001410f50401d0b00c00300700074a00c11a2025802040d11480000070340c0003142400e2032f41d40008150090100420900303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 116730368 1250 116729118 116729177
    0xb04020907020f0703170c0316020109050907051b07050d060527120306010e0d150f020306030307080c01020d090506070f05040e01120303090b0a0b011106010605040b0304050f0d 78
    0x102201d954480f0b0903903c40e242c1e4000203020303c14400101c04184103040503101c50012400481c0d5032450203080300e041c00d01d501c20040740002c49440d00410303d82068002580203441365240c00781000702c81e824180050b400c45030715884500c504d5200140c240d4803410003800b418080d1100040c241400c9000c900c4001071810103090850500551440340200007601041041401180d40e40300c2c0c884800407603411104070005580015001501c109001c1000704501d1041c141100801000483d03080c008240c1c0012205150300d6002070017241d0218241c2e4004103103c480301400149024060007580c4102c404201041e81c2c107031b02030f2042082c003580188030390000c01e099043c618185881c011301008556014050f0301200003c4484003c10180280c02805105078092503028040c40c154440f00000d0000005141c00503e2109464030444004610720381a550707256103030f514003820040801c2c2c0e56400500301300d81c2403003545c54403119540240a0402504040da0342c8a4401d10302c01c0c520406071a80c003125 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 116731618 1250 116730368 116730373
    0x510180e060c030403140d0f18030210090206120108010204030210050309280f03050a03060501050c06070c0c0b0313060b03060603070332061f0806060103110c03070b0402090702 78
    0x68409810000c0c03420b40c480606040260340b07035503520302205c5c1043c00c02140c80c4c80c4400429981324440d420303005580c180301c0c81c1d00c04000c14000f014002408419011026015070050300d501250300d919034109515141c0064403032441c0105100984a005400764041d2a4070b950109003441103240146040d1981441d929005045081c641000d85d200c01450802403208410300d410191380d58070900b0403003041500705103401002c021038103014081340d12804100c2e000a20f0100f0104056009206503040b00450500410447d40c1d015410b07517111039014400d0351210300c00680051802500d0005511509071a241c01c20300d40c40510301a03040c5d44003001c1c03103486500304504220854034002800003c4a41000544241c00c60419800c80c007a107200c20036519a001c01001203401400018185000ea2001245113032040c03001c0c40c0d032980c0300410b4041ca03050381d044100402e82030741c0b00350004030b0042501d520380351030306000100c254510751104078210792400e840000c110a42c5420041d0302e40c4010903001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 116732868 1250 116731618 116731631
    0xa02060108070e060f0d0501090b0412020a0302030316110a080d0b010801121104110a031d0d170c0f03150901080607090e0907030b01060203070606140d1e0204051018 73
    0xe4000040d0010640740c040c03400c481800764603503a03104603501c1b101d130498001c00001c800c50805110700c035011903050310007028000c07200040b5440010b0003a88250568003943c150340710320030141c94540c003035039001042013111110540c0310001403018072800740c401d4070215a6000c00310f00c40c600762680d1186c5181440085001002801702001002d0892a402a824103d160558000900411404088207220000441d854250503050f607c0b1410742c0c6020a150060792400301c1d002e0380c0c3c510b141d02c07038803001503001c01d402048510011200c50300a01d041c414141400c1c607042103132a079908200c401850f000010103101002d400c094444502404000b4040d09481c94406005005a5168411111700160400000c2c41486041c0708200c051907001940d5000e65940701d8001b9943c2e00440002d480b070501d00344000880d08881441c0002551000c2c14002c0074042940307601d03401c000e40b04003045640803c4c0100038010703a254450540318098202c81d811280d410f0981c26600071900c1880481420318018 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 116734118 1250 116732868 116732879
    0x615040603080702010c0303141003050f0318010810080604060f05090f07060f030b1c020319020a06050f120708090d020a1713210209091504031116030501020a0206010807 75
    0x24115180f4a80a0074405011409494114001c000030170441480c0c006074014019402203414814080340c1c0113200b201c481058042180d6200d100e0850b03800180285500100d0881d4052510558454280300c070790287e40342c1d07401c4c229043c000d048504940c001d0303854821164032030262003030039001850480202408000603000719a1071450380919018046c1c5800140a001d01c05e03000a00810b202411210115006400d20b03441d071207070300c00d08034407034080d00720002e1181b08441e002c04180c9400920046c0590700d0108155050b0b84807102e200700c6846e08100000000740842e000c1405003400f40d6810590f40752035189507051001c040303461000c54100000d41d10109000314808032503003143d000e500c1e03541e00325a0041c4015403138942c01015003019828110350b180b003c030481d9031038042c001e0b148090706549840700183c9544031003a000c00c1c0459050f0215011921980304015800260021070751014004402000368400e194421a866074000403818800f680c1480b0840c010100000108807450501 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 116735368 1250 116734118 116734133
    0x130f032604020a090f090203011409210306060711030f0604030807090e010b030a02070b0106020c0a0902031e070203040906081c030e120d0609060e060910151b140615040603 76
    0x2072154440190b112210a04140d45c0c940c0000005540140204030040151041103401e61040740c8000c01d034080e4540161075589041c1114244d10321880038036203940e44080c02c011060300a00c10640756500d861060311042e4504120119455002200030202c5103080d1800809280c4000e1800082007618102000300100000600341910030f407040d80303910713552040c014038000d0050200141c050309911000286036a008680d5404260040d5004a003103a203c3d0040400c0e0b200c180d40303d9550103100c98211585d000d13020440743d0041810b1054a182c81d640e6501d2005a4090b504601c180307401c00e0a16200303101d03900c0c24401903d0141d040500c150010203000f2a2142e441c8101400001d00015824408503401e51001028000a001c204030b880c1e1903810304000030380e0403201e8078000c1e850310000c281e8030188001e00c1c0b403c0721a0380040e0f0880103d020300894008181824101c4a0382c0296825400141a003680060070034508000300844d203040400c60303403d245600c060754001c0d03140000074004180c54 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 116736618 1250 116735368 116735389
    0x120313150e090c0f0a080f061c02040b0f0301020a0e1c0b0705131805010302010314040b1902090607060203100909081911010e010b0126010e130f03260402 68
    0x44403030150380e03030f59403004290701d03c5020700f8040c00383c0000078280c5049810010a41c02000b0ba0380601c10250303911800c2c407010f072509015118024040f52603d80040c5810341044441d25000b9044034a102403032004223003a41c016880c4100403c00d0310f42c0100650520319541c120400c14081e40c00401492074442d00d10301c440c0501040e0802c8000103105007441c507425000001030144811460070620041c0703001000304000c3c0002c0380000e00f8942048040c0c0400002d103800f442c0c0005144034070381c0300c0503004644054055842e1641940a014040c1710b40e8540c1e0103000c0441c090325025a480c80c040540550b0856240c20001d09140351999003808141400280d40502d0a080324004500c48016416240316245442c00d1038250300704045080c1c144c3c819013100f242da135000e807034038070300142c0840b01210040210301200705200900030040041c4a0803205080e0010b9005200d4010aa00c40d1108203000c04080400d501080600e20307221500d03500641d602c8180c189841900d1110704050b40000d207045d04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 116737868 1250 116736618 116736647
    0x51c0c08070204021608040f030b0a05070836010209120a05120d06030b090d021b2815090302100305070806040902150a0c050f0303130b0a0b12031315 66
    0x74081040c40d41c0e000000c64010b00e803074000ca207281d247c41d5200b16607040c000440c041200c0c203c2003038021a802000c03d000c1d19010b8180da441d001810340d56a01c0203000c2040c004403507403a00c04280c01031190803617540c1440b80c111184000150355000179406011515041202014981d8008440c500c04100d000c950344001c2c0760804982039488443d44a0a4007034900c84d00040c10480c926000c2c450200c4000034420315101c541c5c0c0a076a150a10740055551080c480c03031005400c40c3c070390103440d0f141c40d4444030340340c030050340081a07170b032805865070b071000001d40f5603441c40b501060790020b0600c1540f5004070f00fa000c0c2c501b549000e00c220b1510107001400b58078050071941c041c1b034440b03e1100466660b00141c200400b014290182c480250600050500102060035581c5000d51a0740000c60103010003100c0c42400210100c149840480da41c10b03520030001030030450300d25036a000c0300300c0c1c580d40c040d1044004040c40c0010340e11640000300310761281c1c030141d0100e4480e4841075900010560032003101c00c1100e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 116739118 1250 116737868 116737871
    0xd080406050a0f050705030f0601110d0804050f0d050c0106090b011407240c0809010b0a0e040314030106050703110604020a0b0a020f030703020601170c010203030a0b0418051c0c08070204 82
    0xc98102564015005929003141c02e10708140c01c00c0401741e1302c5005107215007001c50410841c2d450344401510b0342403149480e9800e68009500b2001014020308030180c01074850401c560300e148620803180d05291025844900240e0009240c00085100340280c0010f055002030800c00c07828504c001810102c1c00e0304210100d40408140601030051060703d04080c51003081c614a04003400304002002404020130000216a861000c2040d0b0801440f0b40301c24480b0140000c21002e040072541118118010300031020880c4264058030601e40f0078010758028041620380f00e845a4682c5400313040588440045007080d80104204009030380c50401d4001284c3c40c03403404070303650301e40c0702005c0b030410848a0240b85148400900c42d000c255000880c0c604a0300c204c51245020344040144944840d10748840314016030052000c200c1c0102d0580c0f0002000400410001d245410300a81d0790b8840704100c419600c54001d07010030441602d00040c85082d407021440c01c3c100d1404656101101d5006a540103802107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 116740368 1250 116739118 116739121
    0x10b03091b0415090204091a2b060e03130e07080403110c030102041202040c02030301080d0f091701090314040302060f0304050c060c0d09050d05061602120403140c01020d08040605 79
    0x2519980e005201c1c3c240c001d841c510105850f0101c1030083e5009101d01a0600e240400c21124406070071181c0e4002c4e10300034144400640c4510100c07a480c0303170504002c0d90004504280d500050740c14490500301078800d102440c1c444001c020012144103007a88400e003180100d8082140300c5074000c0315590302c83da06007004060081d040101c075141c940c0ca0a05e4640642c0300190100b4104c080c4035108012610031a0700f4081828005c0c4100e840e80421321a000309a4841580c1c08055801018907440780942c614080206907610541d2400f5840000c84140d19031755502144000e15900c5080c5c041c0c5016018071881c40d0919507408501035106600d086041d40c02c020003c28104a401d01c00380040d1540142810b498002091046032200301e005425004901d41c85400101c60034040c4249410702d4010019003401d5580070404404141804441000c50155150070f40110b40640c001d04051401041c0c070000b1000d0341078940386030076808012281075502081c183c0c2881135000ba10280d01c180d01000101c4c85 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 116741618 1250 116740368 116740423
    0xc020108071101140a0605030a0308010b090402130e0906060103051005010804060204090c020f070807050603061c150b0405090601260c0a0e27030409180c060804030206010b0309 78
    0x20140b01d184a6049508008103141480071502c0d0203402012603030700400020f680e500c10140d8580c0018001004144100b004000c05290000a0400084058805407030f014180c4e014030308011242d004203c2c0700c1055014800040c50820000344e1011007824200520f003007644074140f072105203108030b40c1001114800141000b1181d016940144051a801d1002ca02c1d82e58029480d0344080705860030520810100041a010016050b8210340d4007410721032440c0c8441c0c090041180b101c28400c40708183c40c6031368031b0001c0c80107031a1154440c40c041e0001552a1054100015184040c2c03401d0450352080d0014400310841800d81015403070b10646e01c028400760420101d0500c081e0b420560390040102c2d80020780d0100003101584504000168400c41c141808070281c41180074520080469205102c00d02c0b1040841c2d101c0300300181401c0c1091503401e05030391402d80b4000680c002d0800a5080c10a001c101901080304601400003542c03480d055203804a41c09541704002a4005080160b01503003044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 116742868 1250 116741618 116741627
    0xa230405060919030302071706011a0a0507050d0302030105130e0c0d0c030b041a090604030f05090f0d12080f0403021902130f05060f040b010203041a09060406080916060c02010807 79
    0x886401c05002241c1113135980c01c000c1d40b203100c18450312008440000040d2248080411054183c40c00c480c08040401c003c040680595000b5030104810f01c10108029070105104020a12455a503550050f03503a6040805005400c0e1b480e08840c0b40c070504000500c0c0c1400f00c049581c1502c11400c0d910201240c8803820042001c10b09544050180c610b6901448140100d0b500f4074400da14201100b40429181e0900c0e42d60b44001c11640980001c00c00c10741c50445901c110001c2c101d1a00003400b00c0000c0c43c98a000486171128000c2c21100c09403c00210003005410030b450983c8102980e40c524114645910080e44405884d041044041c0c95522554115900d6414406031004004810403100180c1038580c0000e200a4521500c951006984524146410701a1030303402c1c001a40510b060914000501200c4060900c0c003900201c010b03c031450a0f6202e100241000f09034030303560303030415007094540241040307400081d00454000a110a1003041d400103007825000d40e080ca0b00005030783e103100003203a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 116744118 1250 116742868 116742889
    0x13110f0114070602041505131203050a0c0606080102040803070c331b06050403022509110d090c09050708100510110615011716110a06020f0a2304050609 67
    0x1b114026004446078203d9012000d0700a0003d4000e0b582d0b00d032038464000106101100a00800082c1c0410005221520803640c0b03c010078420381000c1105034540c142c2d142aa000742e0488072580d80082620b60600c00914000300c01481382d003091110360040e8803461000f14082c040043e0075144c3e003042000400d44900940e400c208407500c0c900104000c0d1386054400390409540941c0144034128041540c030b81d446d103040d060070f10240c141c02105890200e66101400301000c0e41d01203040144031600001d042e5000b100c034001d10540441c0a114100744900c8221580505000100f20001e020400c02159001c516001e442048a45d100012002c01c400c440006007a12507030444c2c02040107010220000c280be01100d281d00341c8402c41848440b1050009088085401c01d020002c0356055411079409884005c904041d17100070340b11032076550f440b020240d901601c2120740d100c42c000740e0504000c0c0e20030003949500191800d122003c0008030b024204074080c500941d88079200c00900c40c0e42541d15881c0d1207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 116745368 1250 116744118 116744129
    0x607050a050a080903101e0b0f0a030f0308010821070f02131e0b030307020409080d091506050315010306050a060e130203060c190806120613110f011407060204 70
    0x85100c682c8901c0c004449402440c0054040d2190360011205003c1034000e54011300c14000c402c0d414800c008940070081c2c02c00d029080e0300401c8082d1030850540740e203100c2601070341c000c40c0030318111a032918004005420503800f0340c0407a0001c050003d5100b010300141c90108014140b4035407200d65a0815130401c0f4825000207602a400c0d05000d01240501d07005250800c2207203484c91100b105240c0b0450651780e2016000d036040c0c0082152000500e032070b0348419400c0b8011455681032440303529104048603458402900d914400c018403242107c03850250101400e01035001d0701c00c031402c034000b03d1181c402c10300006041c181c4030400180c2c442125440940201003650364580b003801e08401413040071030550b600781c2c064010540000c0c00e080c440401ca03800350011094501c4010190700b000c031610000542040d0348030300d01c0d2800031124030042040c14020303240001a68038800d803514000c5149001007030082d0040b0240800c600d2035a82000c1d2600c100480307481c0c0340d90b40e0005858101c0083c410b58006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 116746618 1250 116745368 116745373
    0x160203030105040504170c0c01030b0402090a0b0a02010e060f0105030c0d03050d0b0f031501030203070506030c04090b0102030f03090c01082a090a0e0103080304150b130207030e04060b0721050301050607050a05 92
    0x7c0d0300402c800a031085102800b0780301008042e8201d001e210603032003030343c001580001010500300141e208010003080d100445100001e440e0b86203c4000c0e0500c030003030300e1440000360340200502403440d007400440c00c00307213003240c59200f00112684c01500c00d0148082442211b691004c2e0080d490316640601c41e02c19200409480c1400e9a04481c4111103000b8001640a442130820103c0d1500b001030440c1c0c0143d0b2154501d50030945801c001d0400303021020f0383c07030381103000034004240c0c054500005140503100e0240a4180e001c0f00c07500040200e032006000507540071030080e61624079003ca40f01ea0081c9072039451a540e47e01551000304c0d81a00e05603001c0311440541c20000002d0090490103140120720505030000f68141c05075411007030301d0741c00c0c030280e90080b03030708420b0f85c00d024880c4d004180c998441c0c20500d05804076a00007500b1941c55030301508031842d00080c040e01300580f141460b40081d214070940030340c858070500c0c0100340740014003409014550010380c1d00d0501400700004988141e00c03104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 116747868 1250 116746618 116746627
    0x20a05060a030f14040203070b031003060207060501061d06190e09040302160f030c0b07030e0924060310050d050a211e080a1503060501081516020303010504050417 72
    0x2006005121054400c9003461400413080c2040c0307480d586180c0180e0f0010700401c41b1030b0501d10007021f142e002600300e0f44042802c4c40c00000245460024017205401240001015072400301c010742840b01c100001e913203000400f12280c240342e80340030940300c009100f030300f055004001d5110300303442000101207143c0e400322880302040201540000c011142c0c0750210404280750f696803034103495400060000901c16510340005003e50007601c40a00b510710701a140490f2140d61b44008a1480c140552f18624400707a443e0082040303a50603842c54281c0d003019124186540b40002140d0000701c0e5a00516124002190740d40c0b05000c020441024445d8018130421816002c0c4061120321803401a0140081504c004040a03070101c0e030401050300582544903544599545070b414002001200401403401040d160040042002803080d00d000c0d0601c0c03001481c1c001203000e00c440c3c071031100600802c0d0744078002d01c04032001a03020040c0ea0440d00f00381c50204482d201d6180010001441301504010143c003c20b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 116749118 1250 116747868 116747887
    0x50303070c080706090b1e070f030e01090506040815060d0506130201080f01060206060409030207170a0b1302100e0f15030709091109060f12010f140303030112030c020a0506 76
    0x306007084410000c12203000d40d42d2120700341d0b043d039a14801e0780d202d940240003962a0106400c070b10070907207404001030361810586540b0320f64000300e0050150002020003c62400c0395811446800285c48112181c07402c0a16040301d80d9600e005001210103040380b004049040c030344410788062090356000007622070700e1500c1c1800e0480d40407072000a82c001400d6201140316410300d5440d1906841c6940e000d8030781d5a40e404188409002e140700101c08600c00c400000412521405003000030945040c050130481074582408448a003000c0c15903480d00f2080d01c510341c010303070780c02800300f007a81905e052440d4001c00f814000743e4001210000e460b0400e84444203625980c190000861003913682c0d07240e8042060f141c9a1440c2281e5118403504a40c8008101000c40c1e803405401600c0718039160100d06240200a00781c024043d4000c0e8400e0f140345610343c9060048540425034050420f030141e00941c1590314010800314221080400913050000c20200d401c19034487c074003d60f000d008090202a17450b10704c034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 116750368 1250 116749118 116749133
    0x30301140d05160b07061a180603160602160f0b041a121e09010c08070c06020705030406051c0c0206060f0f04050103080d060602010603171c051608010608041a0c0405030307 76
    0x841d412511701307103809400e1f8400c0c10119001c05003910301414001d80d54080d490188404c8901a104a03810300c10508000032080c10b5003452006010030750f001d0042440000d00c00c40c100c00050300880c0807074044141c01e0000e10310f070005450440b010005d4442100d06d003241342c16418843e20391160b4800051008000504000c81190400d0000c581e040121903a1a503545600300c42c116503181340050803840100350071900c68400300980a005100051500031f059682d40c2c50f65100c0c2c1d0052000c42d501040142c0030b048020902d9035044001e81052004480c00c51000707403179010040415104800007165540700745c03500381d03112107400c3d4040e00030030a07941c4070304100b900c40c2c106444151455003040404030351240706015890440e540302c00f5122840044001c11015900020600003280d240100740030102d20b0180503250080398100b82215004400c854002d1100e001601700c00c050012a005000000e203006c000003101046009030b0110315200c080d0b008406120b03540c040d44d8144000b103068018000d10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 116751618 1250 116750368 116750377
    0xc12020c070311041808030a110304050a0c080d080a0906060b1815160b0402030c0d08070506010f06022d070303050409050109111803160803030a0c02030301140d05160b 74
    0xf0f06070542d03000905104000c241d80c40c504510f03074205440005d8000288181c009560803503800040407400e000d2800c01d07514550400c96058819900c0b1100060a1150307004070b03040544204005841e000c0c100d00b02c0034041d69000340006110990701c0c0c24440621500e07a201c0c5001e03280d044041c030b5a071180c00d10b12000341001c0707030150762166103a0b098811188184e101142c902540f14018000e041c04552034142007414020404c0e60180940041d402c540d980c5c0040703608400c0d12131119282c90b4030883c140a031600f90141c00c0504640a50700080c0f1656800103410200544905e41260740c1501c443c031a0141c246040c80300700c0c894411410003104054018014100380d464440f01001560781e07406030b050603070781c60300004100e5040410600c4c3c0329040742c920b64580c80002030304a88012203103240018161030a40e20801d0140c2020040c03040607602e5000d00c0030440d46c2440214255410501e2801c07203a8001002a40b00701c64100c0f82d0070410806000c85842c42c40f07044d41d03000016903146072a00141d0310 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 116752868 1250 116751618 116751623
    0x501140108070906171306020328050106080f13050f0c0f03061302010c2d020f041103060103020a1e171e0412120903030e0111040305100c12020c0703 66
    0x560748006041d40c2d01c5440000308851240e0744c0c2d0590b1041c5082605c91444020b02508580c80214264102080031030000714041c0c02003020071807520900c030420703144603c0041e2038070040700d051800403c00c04c1e601c503e550740c00600703071020030075580c9510031151070b03180003500b008145010303481407002c1415000c10250700340007007501e180d259200060105070b10b4550071206401c20717003d2598240f0255108c0c00708603004c3d44c03051800c900d031120702400307078508030308101030010107600405030450441c02c0c038444460100c4020780b4148500a250012080c41e804000c054504266021401e0750819101300044100041001d080640541a41c80b0080c64542044050311802c4054808200c8035000e22101c0485c074070000e800d8911a4031242e84030b0344400190a903910400400400104112105208406070103120b0b40700010402c441b19202400d495854a003040310318024070042021070300100d003500c03080d84080800543c8a88401d01510102a00e07200404d000348089200c0101c80d000040200a490 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 116754118 1250 116752868 116752877
    0x3140f0f011505240a050c100506011103120601030203060a031e0b0108070e010302010e0a0e0a06050306060d0305030606070302070e0c0706110901170402040f0f0209210304140a050405011401 84
    0x940341d2082c802c41d0300e849000b203c0304da6100c819a404078100040a88004040c0c0e240480c81d0010100b8518034041201c00c1690765681c0d40d01c2030010340c2da001180203c2e80039042d4017550400c1e0242c00110741c0c2e40ca005215506150b0000b0019540e565400b1159002d994400c403040c13482150382d5842510303003084000889840000b0000032450640000310101100c5c0c80d10310700d42c020703821b5034011505142807370300d41c075000f075100312001c5171204075107010b140b056076644000504949400201458100043e01c47c41c05a400c00c1c40301070210743d00c081101c0d4002010b031491aa0744a807880c08078503000c460350046104281a038140041c00d40803200034039202d40202400e001da90300c100289140351107034840c603d011600d03080d00d901d810004145a07540c0b140c0000c10010380074801092000c191038043c20044001a40020300c1091450041c603801c12a040c0002c59100041c0c1c0c07101d0307582e03480c417550180e4039480620780c3ea0204150754203903c00024000c081c00078049035a440301c0044000350404009408076 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 116755368 1250 116754118 116754161
    0x1a04090c08090601060e0604030c06020a05010f050618100510080702010506090c030414100c050a080a090206091320030708070f08010b0a020c0319020312120103140f0f01 75
    0x78400c903125806501010090052030340b03002c2c000d0711010108610307075030044014130000001c40c0c4094241e070001c00c034540103440209040e00c0c041e400c42d803118035511041480c01c418804551201445815401d0000c204500245c8450850f85e00781d1030f40e41d106503130041c038186d102603c00b544840c42c076000c0d05641c0c0003070003d03840305070400020320400c894407007000c4010300005000c204044c005504000c03542013a580c2403100246120265030304035a051001c81d100042d0b8448103540080d160b944003411010800c5040900d0b40003600d81d1240301c541500c149887c50b02400c1c480c0d02640401c0161245942103160102c16101e201da051b0000c5611401044e20b55000031142030081d120940309480710381c1c944045a0a05205984e190042111001180f24409201545c0e071010000d400f2185049a910840440148105483c11400c050384240840c2d0612125802001c00300e0741a0549600c00030b400c4c81d165428180900c0c11100d840010300c54841c03900201000783c81940701301e58084840c00c810072070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 116756618 1250 116755368 116755391
    0x903030905070b28050702060a0309050d020309031b03073c030606080c01080601230f040e06120d05090402160606090b01021f0e0a050303070207180603020d12091a0409 74
    0x11514078004d800301d2000c1050a00502e010070050a6500b12401c0c0042c0c190002e403103040ca45101c134903500001d6440050322058501d030170004126400700e5410800c0100108101003a160010761203000181148940036159941061441b00c100e2110a01d502c800c15180e2a99404011550b00c0241c4440e46045000704440101003559418044181c40362001526143c2c01181c1203410320440125410b00c80301d070403920155000c02005807011a031a031907221402d001a101e94060013502251041c021504809a1000c0105480018500318200949c0b1549140003140c081e10407800b5441400b40c944502d0420441d41c0c1d070002d000e41d2244041000f1030100b0000580c0c0e40e20001000a011115001c148218024160445801c071081c8000742e5003207140aa642d94516081510700b00b0250304002030030303c03c0903411900c50749071049160060080c80c0c81c40d00443c9160940c80000707400752400c0400404883c2c082c0801c080100700c8000150003001f10000d409010b500b1034000c01c00e07283d0400c01c00200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 116757868 1250 116756618 116756677
    0x120070c05090f072a060e01140702060a1e1d010f02041a0304021f0c060c0504050a330f020c09280e1b09061807030903030905070b 58
    0xc01d07205903118881d513443e4107a0039103010300b001c4410b1040500c99000480e09601c0700f40c03541d108901c03541010032200704d2400c050703007035444e56200300310180e0260040040c040c0e1f0005109810080d40c290000d0248400c192110040400702c0d0303d201000d040c5000502c030804108141c0d10320130202c5001304500054000600107030722940c400d945404400610540c0c251310a01c00075904280b0061951721030f0284103614001800040014202260003448003006028040c00380c1c0800c01d2942c03514614060078040040e03484200703801000105124000b090030460780c44043e1038180c0244480222003204a0340e4001e10000e0003001d1078005010708402400c04d03040803568940140561074105440c10070300604440150391a0305031514a540343c0e24407501d500b0044c0000041c0c00c00403004420f800215500f40208803001500fa207000307060494a126010041e80c0742240c00c07503011b1a020500034280e040440262414071800b400c0c0b4040c8410000d4580112801400c54840d0700300c0204210f540c03226600d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 116759118 1250 116757868 116757871
    0x12051b0d120b010c020312040503070e0415021b06010305030a020114240a030c03060501050906010206060102100b010c1502030907050a0f0306020717070b010305061501020a0f03020120070c0509 85
    0x4012607940c152901c0400d00c10380102c00421030625100e4504802900024940044107401d00c2621000150030b02c501d04041c08410090442c00100e442182010396031912080d0340c2107101c2c1902903000c5500e25100100b210400b0580c1e204e40308031412961203050582d143e80c0001c083c10050761a00c09215807404012800ca0301ca02d0220071900840650b01e4202c041004003c0c200aa200041a10100000780d003001d83c140910300420700062150304290a0043d907000c0504101e042d503012400300703c8180c0c1d00083e84140005050070101c4c0c01406040142c807410103542000700300003543d008006840141d45c0c0070f18441c40c814022124025650790074404140000e0080906e0030300004030901c0420b80c01d4004116261052080406040c00320003030500540000004541c19400c00004005102c0d00308411a00416800182c0303105102840c0080d540e801515802080c400311040c51105150007036115941c48140850b80c0409840c10000074100d65101c80012078550041800100712400c1680c40309 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 116760368 1250 116759118 116759143
    0x403080d05160e060405060a0302040512072c0411130c1107060503010320012604020f060c07170f0303041a0702070b030604020903070302040f061a03090303130f12051b 74
    0x4514190038441840787c140c1c000c1c0240802d1640800000072252502142254214400d8002d01980f13810000c1c408070000c2241941c2084403103d030b128460003003800343c4154101d60b1100c0100a00001030300407550010640c40ca1404c2a45440c144000040d00002c1c80d143c90075807007013a43c1038107844000640725030200303000c0a00340f03681e010480c500c5a81c2c6d03480350021141050402e504032440000c440c0c2c203007192406510080c0000e0381c081c0800c604001c501c84010074021280c040c1000c40f4200b01e03d81c2c41c07100348681a14005c00311300345c2e03090040921115115102c84015aa0b69103442e00700b05d0a903070010349030350706180300310300000e0382c500e201246103000d540b1080319051468a4203800c00021390800f6403142ea043c05038410001c0146d0381c501c50441c05258070708001c90341510304426180c08280d903803140046642c0400400121560100881c0d42c054201e0002d88101609400c03c4405d41c900751200405455800d02906074642c0c2260140c0301c104d00303208482002c95100d0f004181c50b0704000751074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 116761618 1250 116760368 116760379
    0x3010e06090a02091302061303051b01120906020706090506070f0314070305070e03010e0708120910180315060e0601050703090302010e0301090501060b040f120b0106030207080403080d05160e 84
    0x901d401071501c1d8000c15000300110740d9501416211b50009001c9602c030943c1002d10001e902801c204206041c042580c2484001c03a19071404807419001800110001d44056103050b074442c081c0040240310350554804a8003c4420082c0284500d0050f540701d4040d01c0a5021500801400400310710a00407034401c03110b4290310959540b030b41d0f42c0c282e001d00f4014192506010b8510407804e59910709102c2c404100f0440801002441e203043d10541c286010200c1696420200b0000e80070755885581c00039012052920380025050f810101c550f2481c0101e420080942541c83e03444640c0c111150000801c0d0b403010108821691a403000558140c070501c1001800310740980e104201540c0641e6015080c1240940045a005000d96813182110140d07040b900c03150b24045414880000e84540300005800c00c44040100c200f00c58840c80340d054414487d1404250700002c014040040c82c42c1a503000b140d00900c0c564842d0f07000c042c1341010340400c03500700a0403030700103003900101441090050881d0380c01070034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 116762868 1250 116761618 116761633
    0x40605040b0d020c03160b06310902120d0206180a0209060f33030903040e06030703021309140c0f1504050d0c0906080303070905041a03160503010e0609 67
    0x3000c0300642000c400c02c40040c0d400d01c101000420180000d1001c1207054070880c010034032914080c080b80c1006001c590199109000d9000e15044c440040c0c14940c5d0484406501d040d08040400701401d49058000d400c01411014405190f00001c1d094082040d07907001d542081d901d070b030340750710408841881c00f401d42c5d806002454094241261a25048580544840c0455028401107490140518840c100c407009400344010362030050304064441390445030743c2d1451030401d0741080d0741e24010782c040c00314107141140c0883e0b0381d507404000b0304004640c00b816600320804004420801000710040030b8bd00034201d10700800310401c000c520406e4410000700044071030302c108002d202c2030343d40c0002804a0341d2400c010118181c1d40307242c40750f40001d06c00c2d41c3d041700700f0307042041a00503140154049190b9a0051050080f01d0f17400c02202000c2d0b40040d64001000c2c0300703080300101c0c4079184060042e010702480c0044015035012200ca041074034002d4000703000e03005060071402d50361101250b45412070b8101c2003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 116764118 1250 116762868 116762879
    0xf06090607050c0910031e08030f13050a0b010510030e030f0a030f020723010b0928110406030b0105070c0501050f0706020412060b041406090703110c010b041104060504 74
    0xc003600c4242d00036000c45000410716004214a10001e0f6400d0038041c10f01d0504001300300c44081840d041b4807140454486420442d42e074241e0a01014261030801602e402c002030024480c4400c42c000c0c01e410404036001e1185a08001405d08001e000d090701951700c2d854144c1c40305010340121203130703418800300462400b10b4508050400390803c610304000c054a4031402840301c8900e0000d412041d004d9a6400700600c042510001107110714650715440307904112400c0510703510b0030806030744210305042d080ba1000c0941c0858010215244a07014124030740b00b880040c040c3c4072800b41050314030a172010030200c0d0b031748030044d1603c2c010114020041c8045503420b100d40d501c01d5003c1e00e2400118001213017001060390380d46040c1d03081341c1c000c040d00c00c42207401d1400b88900340c05003003810201034608100b031191208004a84110041141d4003801100020811b40c0c2d220783d02c0f000b150030542050989030540786110038080c1c1079000d105403250f4100500008802c052804540441d000750701e41d90316161805 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 116765368 1250 116764118 116764129
    0x6010c150c020f010e010c1713030e060903011506020c041a0f0d21030506040509100c0e0409051f060501094b0b040b070204022a06090c0f0609 63
    0x110318850460054903642000d4140900910149245d1403001140001100c9030003003000341e010010401c507444140c107002c00e082d20070024a9032030340c151070403081c0c1207004000706118ac41200082c50f0036610f842000b2010021042400c011f803451039096400d43c00c417400821055640214003141e58032000744000059207000144d03282c0c2444082c1811500540303d1302c612f030344c1007a941032a66940d10804e80e10502c180d4503109056114004903000c20180c00c010f08195916032001030f410781c656940e03243d44604c0790b024410180101400900070f00046504d8682543c03030b6110b01d6501103159480400c4240d480800d40145019584103a4a0b4003d20345085040e416150f440200316101414213580b50031070840c5d59034501c03049240c059807070b042401c00c50041210102c507540881000d03107061105000340c00301d1034111420240c048401503100d510102c11000c900c0340701980b4003081406949214020000454036034460342007801540c124070400814032141512402c80183d214170100200c0c540c03031911 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 116766618 1250 116765368 116765381
    0x1050c1204020d0204061805100e04030509010e03060a06080c0402040305190c080318012c04020903120d090506011410121b030b04060b070b0a021b03030f070806010c15 74
    0x105403c14100701c0e9004501112030716044402d11301c4644111040c6400140126034000384486184100a407408009a21007600580004c0c10014006481701c4140c4c801c5649403c8014000c0540350030703043c405c40720030040909128251060254106556017443c2038403d0342c0072290000060145c0d0b1010180d2120031840c1c03003104460141c00c001011916141c100041c0c40843c402004a0690302e04d00740015212024004c003414126104610b0355070409a000d100422261040e98003580f1690f012001034208030840600044c103000c082115040c00c103041d045100003600540540309940d80324a800c600d030480c840900c54100c84c0207800082a94415072030800416040100054650583e406a40e002009244040d000a44034006013500d49090703c689401080b290a18520304601655411a203071801400003d4050b4041440356038440c50f0030401c01c6580b083c0064070355910344181d0485c403420341520b0210005a06400248055024608506c0d030240c0010362052000040040740c0d016200303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 116767868 1250 116766618 116766623
    0x807020f130203041a0901051504050903040b13050411030c07030507030507050d020f06010b0405090415110703050304150b030a0209041e0803090d030225050102040b030f04050f01050c1204 83
    0xa1109100c00701040d44091402140705600c2800c00040070045d001d4203440103003210f69241d2603d01800805a0000b1851824600580d008140e640d520303c480c2d0700b036014542c01b890040c0c10005055a42c1450b4010354000d44000312802c01c04000800710301e801c1c5000803500c60302582c50401124020070300035000741c0400d500c00d00c1e026240007843e551b058105107680206074050b81c8414500b24281c6000d12045002d4488444240e0a0030304e0100000c0d90810090006412220034207100681419503400c503400d1080001d103a540d640031545002030241d4805c130307415520021040c011005d1031400d0f0140d0814400020024210503459408224141c50040c000300d50302203003082d0b200d00709040c00342084002400703941c6164aa19007101030605109007060764100309441080010b00404807415030664282c600e61a00758202c00503c0c040340248241d41101c201c00030301100300681c60a10300000f610480c42501698070500a000d03405085e680c2c16211801156024411050300c195021581a4000e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 116769118 1250 116767868 116767879
    0x2715090a03110604030812060f0906010c0b0a0e03031003060b0901030309090e15010b0a09150912030302130306061502150c07022817060115080a020d06060503010602190807020f 78
    0x80e03886da01d0b0f4184d41c1c403511149201000d000d041108a1030b040b9429465048140c4218426240c0240000c03c82280064005c00001204011640610349980a00800700004085a680e4144404440c8000240d44800c960460906610f69000e007454400d8a040300e80c1619402d428904100892000d0a00405501200d01c03070302c2c64804c030401010400d94003c120401e06c0540c0c030403026100928442440d000307580f40102c10f034641c00e0043d5204e40510b0440b11840340314003018942d403804902a1041510072001c107114000040107001c8281d000d038040390f100080b80d03070511010000c01d83e00c440704410010712140342540029900303017501004050080c4000c0c0030550b4490704048940700046960041060b182440a00b4820b07440c4a6400e070409a401c1d8000b00299031500c9148503000401040c2c40007001205400705607808401d806071915101d0780d40007800750645030403009205400900c50500144200090441441440070a801d1316a810070000c518110094007801201c40c0c0620402e038008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 116770368 1250 116769118 116769127
    0x9020d090209010e010501030f09050a03081906030c0501120509060a1d060a06030b060108041e030e030d020109060f0908070209040309270609020a080703112715090a031106 76
    0x6a40e8546198044d1085040500455041400040448030190b10680e10702d4541080301d00400c0f000200703480490707450f1600843d00d45d14210046188000501e42001c00c43c04d00001004100c040e1100400b540c5080c2d0310100c0609401c42190103543c029108112190032040125600f50816040954890b829503d42a0b0301d0012000e000d1a150b01250b0a4100c1c980d81c1205104106c500c0000540244091030003080a0506071a241d421003080039030048050951051041014010020003d007200f000b130642d1400700c20f00760003078042c1c503078540c04640361351504a02100c856518802e034490390b03420042d042d0a18080c0d41c00c0c040c10010291050301401200703e80061458030399507580b00002e0410003034980180421060209844c4650000c205150061054075134140c0d00054842d4011001e20b00440c0e4030012014103440c0340301d0503001c200000d2010b10300c1c05805c000d02c2080440010207403040c0c80310f105403103003800e50f5005e07400c40140d02140255003080410703000403d03d846550700900c02440d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 116771618 1250 116770368 116770373
    0x303130608011a09030d1b060c0302130f0b04180f050103080c0c01030c0e06030402010c14010b03060f07210e010914010506090606091e030a0302010615090e0109020d09 74
    0x20a00140e200200040140005025805000c03100d540c4200c4030505490500c5140c0000a8135281641000010095006002d00580c41d0f60700e100c004054000c8020000b00c01c04110040c040c1d4000f000980080e152a80c00181004010003c001107884c1c9010050406081003c20102c2d44015005500f10781d451b1203e00360390b14554800d5034001c620890f450b981c3c0340030010300f40f82088840805181414035008503080c15641001c01708035034010880c0c402e60389a44602c016103024981001c09490090b41414240a803001540004000071049040b2030469940b880c100c11903143c126109000150201546000814841c1540118441c1140007207039502044040e903086801d1890181d5010a0308049030303c02440c21300c1219004641940c60100d03070301d030031000700d085881800500350042140540c07201423040f02c140c01c4500100024140d80f000b40e140e050003070187c0711a004014402c00c00320250325005015005400c02c50320036500000581c2c0c41c141e1150000c0d01b007050710000e074680b81c0703211a00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 116772868 1250 116771618 116771647
    0x5090f22060b0a06020d093003030e010504150e060606070206031b0d0906240303050c120f030906060d0f030309031b0606060221190e030f06221109060303 68
    0x181500d035000f080001d01b03a64000b402c0580f10340c011826000c400c03440a40b0519002c0741c40d034020b00c03060708140c8400e000b031404030001d103200780080216500e000e05100070401d40517001000030200c05018000502211000303030310303a0001d8462a0307004604020000c010304007880a540e104100360084851241000a1200380d41c2c410464070450700c1e174803030102042010303510815200182c07110541c85645e000d00e0140502201600001d8240310021405090701c40040004480c2e100f000b1000b82d40310b060b08480c42119030415142242e2500070140011580e052680c0b0700132100743c105401c030a04006135202a4014100e2603070650400001d052901500d40000d110784400310700c00c20001840c80e160040c0242800c1500c040c681c80d20107a80420304c440980311068841761000310580f94160034034064280c1e440c07150741c40d2890f058014561038001c0080040752040c440d803903490880304074804e01c0140e000d02100c42c8100800400c6071400804507410070700f01560344410040c0c2281e290807490030a40c070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 116774118 1250 116772868 116772889
    0x4080307050f01140603030a20070807050a05030a021c0204020d02030c07020411040503070612020d1e0609090803070305060d230c09010b031602010603060c0905090f22060b 76
    0x22071542c04104020760a00302442028041c401611300c0910a04203a000aa140c0c0700c2c285407182000082046609100214851440c68a94040860741095968424247c4900305442614400c100d1041700045508021440c2c0c484e290b4004c07c048030707140494884161075401d410782a60000d6003404402d0152489200460213900d0940c5004c0c1c803810343d441003005882c50310401060102c000c1c44104002d450005080007569924248445000d4051741c20348020300a100b642c07038010b405c209071035040c0c40e00003103102c0340c601d01040c0501c00c03651a000102c06981c1551030080c016601000000c0b100d41c4a5406590003110041100da80c5980a07142c01e1250f130514120300043d0400050000001d07a801c10422854075020303614041c00358035240400300305010061901e081c00c3e003507035160310300c1e40c0c800e42c40880610b900010810040b4149003006110202c1c45c09a90300560410002c01e130300d003542d9684184640440c0038104102e20b6141c035072100180c4020360840348182c4485c070750426a40c0303480c400d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 116775368 1250 116774118 116774123
    0x2121f0504060509210c01150b0406140c030d0b13151401031e0504030215011e0909050a08090f0a0305060601140403030f0806131e0e0c060301091104080307 69
    0x840c140c1001c0c1081c4040310000742500e200c3d94060f4000c0100b00c4c00c4c0405204160366020f1071640c603804001c81c00d5015081151b64129060301507a408100c2e034052034090001e487c001d5544d41d103072038032103032030350410f4418081c84041a600501c0b81078840c5815401042c161000134014030607480c0722405038000c1e1001803500324040003051901740305006a001c01102d00c000240780c14400c68042680540c030040000c0d018041680d16400002c0c01d05000f0001e0f070740c40c46125110b4244c20340c0d4495690030711540114160317540c1501200000303900001800b410f603d0582101c0980311041096840c1c44e80c5070300600340c80e0307081101074100c00755a41c1c4440d407a800660282d400740900b03250000005020701141e40300302403118030600080c40400c2d4021401c090f030001c2410010401e4891400003014500031a5558006d1414a4048c001c0c4141c917006005c502d0b50044020700401615031001e03a10780740a10b50b03160308102c00707000411010010760004100041810341c120314041e100c41216003035a1228000703 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 116776618 1250 116775368 116775371
    0xc01020a0c02011d0108040b040f0b070207090c050309061503070b1204020910031703040303022a060702210d0906020c150c18040c0315060f020609010c0c02121f 71
    0x60000b596013214829500480d1516810800012540041e00c02c1c07801510180060700315000140c10004d403108103051494100045004071325016030000c3d03440703400d0f01800c584641009031041d0020f008070142d900945160000d0310403640c4121011002c2030f111413201d6414480c140001401d4854079005100c01400c0014440142c40d040c014001c140c6000743ca1a4031034803000b1001c00218000e0031000c020080d41c112441e6032510b5600f800ca01900880060f2610104c0c64010741c1c00303100c840d450920300ca0045506655082d41d030404281c1e10741c20654407a01446d1916400914081c20001c010882e240c58510300003200032403171321020100e030004040124158441c078040d140310740200d1000f039807066030712010314030303003daa4502d000740000005e0140340115101c11505000c64003a40102000340d141881c0003200704d40d22080140041951603410f40035010345d0020901010040c005c030541c00249441d40c0407111070550a100c1100552402c8956034002e90021400d0801010407120841411460 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 116777868 1250 116776618 116776637
    0x1090207110316031709180103021806030c101205010b0a0908030a0e0402070f150b040e030325140a020109031202070f110a0302030a061406010801030b060904080c01020a 75
    0x4194401d051414000391003503021034100800040c5210b04101035a600901c03401210400c8580d0100034016071248591081c01007000e0101c0004800302c050483c0e000312215000910062001c0a0030407094900a41540000ea80c0d5415030505820002c04d4081500d011f00c00c02042c50507050440e102030b00046207a050000e004030001d60304c1200407010342940d038040c40c900300c1d40d064040c4c264190f00706054007403500072610300e00340705012403410007060f0011840642080400061001010386d03500c0c02e80f056190210b05d0550010000541307104182030071807040c6d080e040618022502c11844003010070040c0d02c00241003081c41ca44042d004d1420b1035000410301ea4001d14000c1d11034280000d03119102d40c03060010b04003044a08590441464115132220305500816002c11142401c0c0d81002c0e403d4030449002100f0003074140d0240d80c51051341120b00030561580c40044806500a21000e444408240701041c124a021039155402901c1400401c0c0f5041100403880d09903003046e009080410350152 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 116779118 1250 116777868 116777873
    0xc01090302010c08160e010917060115030b13020702030a0c080d0f03020703081501050c0102070317060d02010206070e0103200304020301060e0601021015030b04080c0106080c060a111501090207 85
    0x100807007403002c0d0821303100b2450068a100a44a2842d1606081064002c6083d4459000c2c460310000782c179552507885a0300d582482c000380d541c02d081c4107065030a0004003820342107030302c240702d80c00307010400400d10b8140c031150300f1440b0041c0d04034803000d80c5d060103000418000508080100c40c0201009070180000e0101d2000240072803011030b010a060500410038070000903407003005a603101c00509840742c1e04841d48070041340c00b8001c11114200c0c03076200180702002e02d41c000c9034808042ca400781c141000c03941c5000502c91105c02c14800203000d0f03030004010a9980c0e00490120304c01590601d00002e0002241344240c4d020700e1030527441502e01c0e0700042400b042d0b0400780119409002500f0a81e242e50a0203c0001d5a41da615000d90704440c3e07586a04000540941800780001c2d50031000c140032500b4a4104458180d00880c0c0740c1138150f10b0560001111240410000440304004000ba03007001c1c07101c1c0c8162011074110100a080f40222140041c1c059290701d4000c4c00781503042c1006032030b1101c42c0f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 116780368 1250 116779118 116779121
    0xc04051c03030f02130e1302040204080f010f0e031c180c0302091806061003090c0b0408071a0d05060f1f0f02070509072106120c0b0304031d0a050301020c0109030201 73
    0x41002d1002d0f00d004105000da20b414807a14001100c4131075000d0a42c1e035031241c07501d003d1041e054000a6001d0700008001030003140005040d44601460030080081804008a5002721010140940171a42080c000d85006180400e001d2807010020390340455100e4401d00d824641001400003202c0c4c9101c2c80d070341481582814101c0b2944084c81081c3c4a07104c42580c0146560358100400e014800d52402d0008154140b182e048421a580d1111450f124582c0b0341801e801c050300b1900444034280300d6000000b41d09031134041074030f02d10a40740c002e5528003508104404047d0600804150700001600054022520b450191070180c810b813207103006c1c540340c80f050000c104180f103074850b1045600940040c8001d03501c5401203034000781c0504040c41800380300482201c0c0150041c00034032b161440c003880014103010f191014000c40d0310400c550104d140d00c8021f072031450b00040d100900010710f0182d04240160003203042c0f03440d1139030044c01b05011996860000742643d00c1180d003e00d041c1d444170082004c00d03809 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 116781618 1250 116780368 116780381
    0xe060106031a1503090c0901091a100e100306150210061401050f0a090f03030203031609080d0c020a05062208010902061c091403070314030705070b0c04051c0303 71
    0x15003048000051415000940c50102a83d94001e000c10000109242c0241080400361625003d0000351481d80e40301c01c190010184400168100c100503004004240b8101e4003a030303681c0020b51215a45248504203120400c44003008480c14155a00404105122038811000d0107846941c01040001619407030790b0155031460380140c00003141b4a960403026a00b240c01c1d900002c10030b500f0b643e252075402e841100d1400f01e070b03481a81040c1a95001006042d0302000440c8201c1c1a16116810b1989407070b01107034150f07034900c500f94294210b0141500c031140704121408181d40000c102825007500c800008950380c1c403a0381d41146901143c400c4030720440380d002c6410000c1c00100001c011050554001ca10503220f60800c000c4e04410324030100044a040d50300145c01960010ba81d2400c006140781a05e07131742c0e80841426008100da150078010517811440440b4492801c6943d400c0c1810526542c072041c0810151000403410000d00021031075440303c5a04111020174032440740704040300c6040140890381d2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 116782868 1250 116781618 116781641
    0x8190e0609010e06090d06020a0f17130b0402030f0706020c040b0603060d1b0e07120f0b0307060f020f100b01080f060a03080a030b090a0b1e0a0303080c0d0e06010603 73
    0x4003400101c440383e030040a5140c10800c140c1c0c0440d1348944d02c400180105c040b42500809561002c0ba6080d040c907444102241902110388030960076074076010a400e103443c3c00300c40c240110802c002e06100041c5003001e0240e0090b10140c101d941c1410b010754058180440c1da0800317801a0304c00c004001046c40c00340218080c420096454915504010300070450b105045400030b01000d20070f081c41c18112840301801c03801042010045849801c042600400c602c2e50051804030b20b034103240e100082c506081c840d05000007401401485680e00d044030556881100d0841103095000311700f041e4065490a003c0d0a0403000a46000150200d4080001d000c501000e00f5900344000c1e10401c000b10b81e12056190303001d8036041021b49460705420103046018100d203050060300211050140403018401ea0081610904121100c91190551801083d00d8001e56616240d1142c841281000843e0080800c507402845c18006a843d01c640e0713000c1401699030f904000021644004010010305a040c814258644c1c1d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 116784118 1250 116782868 116782879
    0xb0406060f181412070b0a0206010509010b0c0a151d150f0c1e0c1608010506030109050a020f0301090203120c060f04080901120b1c060e16060c0f08190e 67
    0x1030900b001c1500100c0310075952801850041d950311400c035401c2214170014052140010703550178482000039200d40c001e20895000303032151000810500312090079901180d49080041c0903054680d12001e003007a000b481c00d000090358403101e001c40d008800c8a0800304480b680300505100c000001d0b03031041c50400404c0c0e040030220352401d02c020705500c001207a8810544a00700348645200e8a0054160b10828070081014402d402c1e1440006141040040031106900004c01050351010207241c01d072a200f683c000d02c0ea80100810400600d0102c00d104c000c002d001c0e00004822a03698007007850148103c1c0b020111303206c085030114090808004440d4041c078600c119400f9410907680c0c003070803030042490640c18495115004030780e500d41503011083d207a00040200c1107a103004240d130300710740101c01340c00e4030728505102c4142990080090300e21340901000e011445020314016003101d401001101c12546028400050341c0030a25035405415001180b4150301d40600281c0ba018010404a049240c09070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 116785368 1250 116784118 116784167
    0xc0c030d1715030102130801360b1003020603070503090f1501090207141204081203010501052b0203040b070305060f150d110f0301030201120209030309130b0406060f 73
    0x24045290a9400541c0010408032034050580084c0c003a004e82c00d03819030b035072281050001c1d0b0038405401074003030781000810440040103115090b507007085070556a1231080c00d071000304100040c4184031076035006015042880f0040c4d140d80c0042c045600c107686110004501109108010170240000400018100014080030f8401c00b80d40414100510036690741c1c40d800702e10711041c4a90b06954001104400342584c0000300c8001e1040034603003003406842030900c2011200c0c0e0341e4030b94560480c4d0503079005840349428600019401c0044001c180340400c8a92004864001421014000303103001e240304036558521490040d000501f111002008140300e20a084280340e259102d00080e44901c5d80300703513001e51707403250000d0003503002d810704480480c05c0c002c000070000f1141d904000914180c07031013682c8131301d03041500945079010b902030710365010b0381038204100300c91242c6040403d544403002808004220004164001001c940c00b680c84a0301003034100142c080c0140d03110901301003114011880d2840c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 116786618 1250 116785368 116785397
    0x10f05010206061c020a08030c010e03090f040b03030d0603031d0306040b0411030c090414060f220c05040905070e06011b02150403080301060201020a1e02060a150b0c0c030d 76
    0x115400030305414000c020f0780c203130040300c19003035a1881c52103a0003034110983c0035594442d01c1d42c1d80e4412100300200d5407804945400441000c02152503400d001441e03001041c1001003000001c0034000402030741440b0802013040d05414a0040c000154004d40321840500c402d550f40304200e828280358144260002020480001d440074002074100f5089a07568003038107111400b0031b00d03098254042030740c81601c0030100410009d8241c1c4640c182101e24058500540350f805c0610151101510407401e10044040c40121010b41200f41c2031740207014029081946584401181c1160a65902652590480385080c440300c1080880c2581286007031078031654101c1a16001281949c19400c020302c203132101c2e140010b2100d50742d003e60f0060b5800104540d52542e441d81c004c0d000398030142d002c42c04101c3e42e200d030340b00c890310310b45809900c5400c3da0084c010541d500658040104801130341807800c224852008243c2c40703e480003801001c060341c002800d2485500017054030b0428032031302000c01c000301d24540b100c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 116787868 1250 116786618 116786623
    0x1030207030f11030c010e010f0e01050c040e070504121a0705160f06061505130b0f03041202011509090215090a23030313030201320c031b03040608010f050102 70
    0x2038003942c1c03a000ca1203400c0760004074150704c40d030038942150798207044d5440c0400c8410f5001100c01504031804014ac0e2610500c618265002203d1090310082c05000070010a1b1500c0710b4107600444518081d4a401d803901201c20151044020a441d03d003458045081811140c0b561680c11000d80d09210b814035003820b42d0028070400c41c3d040181003c03241c00b0480100041600600c0140005907000800540742100003030543d00121204003c560410b18005506090b0070f08845895844100c1306286a4454450012580120324103200315907072a0000002910800c0080000d00401c0d50040340c00c41082c01000a641302e14801c0c20514042005100c1c101d6803030744000c0c012501c07224404030b201c51400048484150310908510f800d404005110b03640d50f0004034201040e2031003601d42d510241d0724408851504001ca074450301244035081c40703540d0070400c03c01c05482031080e03010481c0c1ca01a440704082c40182c0504522401a41c4045001c2c080d141e0401e9905000d001400c0e84034003201c0c903280c0001d5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 116789118 1250 116787868 116787887
    0x909010605060406030b03030408060a0b03060109090f0609261908150d0f0c090902010f0503060307051c0f0c05030705150f0d02070602031905180c0907030213080a020f0103020703 79
    0x10325036030708046c0010740c40c03d00651300107102034400e5840a142c2500388001505d40e03d01103c3c42409100000300c0c64200d544100c050040d00070001c00384100e40c0396242e10051a046e14180c41d00e160300d02d00e11403061b03107021103910b40c3c1407100c81c220f03218107400043c80c0044085044000900055404005541d1142850110018000c40b0060342c0500e46041101e4440d80d5044064014030300920089203c2c0f40c2034000d00d40c841d100303070790305140806000d10486039400180c6030750381c4c103030048482000140ba0806864540c40000403030706030701400d1542c3e602e0b00f4010031036086034080290102000030380782c14007480004040c1600c580351030310262100030805114203121401d0b100310105d006051000e090781512541680b1080440d03032400d0803403d00e03640d4144040038500d59820303c00052401e000400402d4048203042c1700500c44800350100704a00007100030002c07400c0603800e0041d11307504030590911100920310080604996401030051142184a1109003414140108191800240d01072a582c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 116790368 1250 116789118 116789129
    0xd11040e07031e17030408040617011d0402060c030c0a061116060e011b11010501050418030503060d0b011d0702030715020c0a061506030f0c17070516080909090106050604 75
    0xd860300d09480c1c01c1c4180c04d8400c000b01000350002c81000f0410021000034019200305448284000d1010140310f0022807090141803503140d02185940600b0410f0b003102d0360000d2004101500380482100f003980b46030031103449003944ae030242c06050280906442640e80903400160980e00d014221003c4090352fa0344d44e1401001c03195108014081c040080d0302039411458101140c2701a90b0407000024000c24100f15080000d510b0100000b469107401d108005001540c840c0b0080c80352503d4034180d40796040184050380005125800c0c90000759900c2d0500d02800c040c2c20711041b403c41c03819105500103001442034095600c10807409011881140080e01565090400980e41c4d0048100d95800c14030f107036400618050800e40d40c00c034400304640c00341064810b01d070b80400682004001c90070954078028240c4020566140034402d501c0c0000342c03016444810781c01e000746020360100c0d200b41e100c843e13400d09850364040400e0000941c82c140300c90680010408009102e00b03824200007404600c154882d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 116791618 1250 116790368 116790413
    0x103030c02060a0e0a0e041203050912090607060f02042c060f030a050a030f0e040b0a030b071116030215130605030a060b03090601030c0e091513020d11040e0703 71
    0x7a02e0f0301d4412910100b2921002d801c15400b02d03030f06ca054901928050b81c0c210b80c2582030145807070013a40301e84141440380440d800103000c40ba0740c903202d40400e81d01548840381c014100f0803c110220f0010301480304031900031000140d03a0b914020410701c4880c00700322075041600b40c009030034800b000071001c54ad8106c035040314002c0242d905100000c1c5420020754000b051405101c000601389a0802d20a0040c82c041d6101c01000c1030850040108640705c0c003844a5001c10511028800308080400f8158041c0c1d071070a2407075006008450481c03400c00350881c00d0301c04001c102410710031424a190b0400481d044d030920715040140307100645a00310842c1c020700040180c0400003036880d10050700228020180c00341c00b82c2c0d907402c0c50748280303403255000d01056078408601c04000501c80d036903000c00307441000301703401400c0c1d0780300303050040c4001800c046c0000c218a00c071261a00c02603a00c0580400902c1d02c0b074800308210110b10301c00d000c159103217040d1703005458100310402c00204060305070400c09000342010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 116792868 1250 116791618 116791627
    0xf14190b250b1014030705061c020c120405040b061c1a0a08010b030d1403070c11120a06050a051302040207060f060b0d0f060f06050c0c06031f050301050103030c0206 73
    0x5850218030325102029194540700c0301440b540c105044500b2080e03408440c84144c41041c404145681d4186074803503240c201d802041540c81817844011090941c1d080c0c40b01c0540381c00c0d080d000706454040d10403203801d4982c0c030016041006103800c0c4140703850041d090710f100e401e000081100103080c00542d40c051508985800100b00031240c0c810b11003030581401082d85502c180c441c1035050081031110241802031041c160311800c1c0c00e019001c10100780003108449441e55036028811920025210411580d20a00f4902d810301907070307048031440d03091040c84d005180060550078610305407407004e07141c1c4520918000a21407401c5c080e004c0c468100b50183d0700943e8a1480d85040e40007002141e04004181e490420040b43c1400c2000007000da51450003020b0202e800456001e0084505511401240c44c6010a04000345400740015003840380a0300e05603007512801c880880c0c102d60003194844117852102d40002010751050012401134082070703000300300560441d41c0251281c0e000c03d4010348103880c0400d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 116794118 1250 116792868 116792917
    0x6050901021f0b01120902030c010c050f0106090203090613030806061c02210903040e19090512030601020d02070e010902031f03080a11160303180f14190b 68
    0x80041e0902c0c42c80006007000c0c5002c4000a40141641101c1d07600240c1031000c54a4200f055000d9070380780c25001000380000c140d10a00540b030800142c4c408484502801e20034403010b40e002e2107000f000300072424000d40d580c98000ba00e10b0904074002e10307002803080081585000700e0ba101844aa00c01d00c15120b480d0348116185e00c0301c03140c2e414140301c00802400007072044d0380c103070388158030b540c54080354445504141c441000113034490186000306400541400d00041d00030481040c1000752030390242d40003601400755240d81c1e0a004c00201074880c018000024801c113543d0421261400c43d1141c070103090404d003000400c820701702c070600c2a1044d054000c00403034204041e81c054181e100b05000c40d4000c103140e4038600741115402207480c220103c0c42e41110f840c10b140b004991010500307806054034556500395070b0103680c000180301120000b03001d0b000c0042003901200540c50080e101d1a4822003c0b02c101340704000d034009212030350503003454001d0400c03c00d2402d114282d864081004428961310b21802 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 116795368 1250 116794118 116794123
    0x308190f18110603010305060703050601030b1e10110316060b030d030903030b040e1c050409090c0f1a03010315020702040c17060603090a031d0306040b0106080a0b0105040605090102 80
    0x50000312560745824891004044a8803400e01d08038864000070030004514410041a80400d2001030911b030400d1000504261285e40b00990121050400182c040c4003400440c00c2c9c2e48060101406e94000200225400c0c50b069140707091410340c0303142040b8a41c0e002038400d030303c90142210448412144240c014100070380c80d0060210001d0141c101c4650b00e8001000501a10302c503601174010030f19003402040e0354185405a82498580c50b00104869680d642c540200c400240c40f1003800c018013404007080e003488502500031800e018080b8400c0701400d01840303e80f0300310141e2215100360000348100607420007080590381101d80007035039401303c2e4600361164000f80c414281e0003944a0710b000030f0742d40d082d80c002d010120000d10380c040d000403c1c0e0755041808010304c170aa6003c0c0c110344c23045000000080c031804c0e504895008092154180744d200c3d0000c685801c00a46040b90300d0729044006000942c0c0c00f00c031841e40540311040611148041900280c45489203009000030454000b0b41c04e0b5069008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 116796618 1250 116795368 116795381
    0x405011e022508090d050615010c030504061808030c030403030e0f10120908030c0c0c0114030c090406030b0a23040c26060109020904061a0f1308010504030206010510020604030819 79
    0x545028140c5e41580ba0142d1107040403141c00c5007038201a0b41e09005c55201e04010b540341e96040e190320b440c107420041c054584803400400f07210803540240c000b1403510010300c0649076041d040c00007951103070700b185000b9040007090001280200d56040c055403060303588204d00040170030b1a0a100d06408000c980d0000600814072010740070000c004203008100c40c150b0000d2100030070315004e42c2d0b40000040b00454041d0760b0706413841d1652005001140b1302020b640024045c6000c000d00c00529507959541354880940300325205441c0555681268802d400340122110229200242c41d015510381551550116440d41c0100e1405061402040c40410000001d440b084c001100c102e80302981d40e109850302a42c82007420500403824180e000400082140c20300e400311801080407400c02c0303150854090300342c22840026052701240c28000a56100a2241a00507806036014082c00e6042c41e0602454007543c400550465211004210109901140e250f420440041404154981d0f0f11900c0d000381c400d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 116797868 1250 116796618 116796637
    0x60f0a3c0b090102250314150c1c060f03061b0203070b180a05060619050102100c021c030209090114130c0e03161701060b0403080708120405011e022508 67
    0x1440241c8840e0f0784800917040e802c4034440d01a90200340310070521992600000214043c000d40c400020454280d281d5018100642c400c03070101503070710702030105c1b2000c0d180e03e60b201c109401d02d544414414024540101400d49895110350107049444520081d6240324007540602420492000305803072038044845588254500821104420424184562989400c2d210a4801e0f540854001010650141d85104640c4160080e0400310a00d5030030a025060380d50300c0c8001c40c0100010611010720b070010901d2204540d540041c1c4601c880d07814401384060603041400004051b4507058070f01ea880e03003071f0025128040440451055500c40040d185040a402c150343c0c1400b0301120a101ca490100f207070710490b5210103500c104006031003011822119a03010760a28050200300c10700104c0e0300107008024451045810a1410000031f107945121a000c1c0c60403105030f511078000390b1108011109030310789480d05003002c52500e01482d040c4014182c00508004200c1d0b40480038070f080c0310350322054442580 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 116799118 1250 116797868 116797903
    0xb0d0204090602031503060105010906080a09170a0f03020306061803070f120201170603030301051905041b11060f01090b0102030408061501110a0f0b060f0a3c0b090102 74
    0x41890b000c000b80d0803c03071700030000c2110310700b018840385400240350307040700c4043e100c500344182044003c40701b0a50080c00c0e041c466845520000000b4080c00080003500011002140c464107540c00c020580041140000101401030044c40360381d59901c0e04070f40800701b40c00210844450a0030101c0d0400000741c0c041d8000651007500010101501500700d000d8600c00da860040e46070a110a0300300d0b1200c1990043c0d05a0310500050203a401c08c07244a40491126482e2200c05a60791800907040e82d0b10340c00ca60246140e860680d812140d0024003501c40214a00c015115a18000b90084d0204405100313081c4020746074066031149034024006c8501a00741c01051311164035101c0205151800740c10729543c0003070b194226500c1104404079a41624950264580c400359945032500b85641402a01082c0d00c084100b20050f03542d034803081c010000b001003a00c0309100e03c146010840c000e0b05206070540001c0b02d01d844008005c07940c0c54508080e143e0454030320b900c5180a400407403400d040200303080c00d9103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 116800368 1250 116799118 116799131
    0x108090c0d0602031f030b07030e070317070b0a0c21060f03061b0207140d0201090e250e010203040b13030b04050105091c050a0804021f03020d0507021207060b0d0204 73
    0x8030b03a8008622034800015180b00c080300f0f400c000084d004042c44003405da0112000441e80c00b5202c3c2e0000c0c0c5140c20074004a440e15600c0f5110800070740101d0081009803080050402e040259503002c840d403000e40c0718000c1101402052011704054050f000401d10314544015244400c0030301c1d4085005840d40512140e942900c0f0324114005003900c1340406000f125180d5854002c510018010041c0c4540700e202e0035030080039400340190301d1001001241446540000441c01186660100e4032400c410010080e1030b400b000f0340120840b00c880c0f0032204100c10b0700c01480890b600082100e0454201d2440750b0340d0f501201c7c6554603110810307000200341d00101030501c0240001508654000d10449058881d40e00d4110000071002c900243e103c0d0200e181400000c00031805401480d0f44a40040d000700d401c00120035410b801c20001c114010007080d404500785190040510689a106100b03000030301c551602500c2c840b40500610a00073701d00c90300c07411105105d48645404082260340500240a00c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 116801618 1250 116800368 116800373
    0x316030c08130b07180807091104060f0e04020906070b06120f070e180106180501080102040609050405060103060b0a0302041a04060c140c0307030c08100b09060f06071202010b2404050108090c0d 85
    0x847c8400d100e20780c0394900b0711003048265030400d4205c40440740d01da180d04442c081403110568101070701d5060540d005070700740025181e54541c500140b0115200d000021558034001c0d08115141103c1c1c114000c280d400058500142840001c820042d1520111350004e550382d81401d090203650004c20b22440c650800e5000a80f0100c0250100198100c8035020701c6141c0c2c90300c80c564201c0c00350748600000500030203010406404c003030b441140c00000600d004030b01151241d007846020360141c03000d100000d03800601004449040c542c0403402589260200d89400c1c94080c004011020405c0301500340c600e8410600d00a9070104090310f1800005400d503410150382c1c2c200741c0740c000c06600c1000440e01410014180c10102d0744680d0861642c000c1845189403201010300002c040107240050f0420380411002c00402c50070f4070301501400203a0300125a1200400c00d1015030035085500c644032103184c0b00042502d400c0c00042d9019103a00b0300e8140b01a940707048000385403102e021402070b04511128200000e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 116802868 1250 116801618 116801623
    0x2060403091d01030f031806091d0f1f03050f0304060314040f03031a060f1305030d0801140d081209011104031e02150316030c08130b071808 62
    0x8914000c1d00ca00c4001640c0d2078110240515280b401c1040c0c0708120300600c0001c44a90194290354001e14001300c0f52414020b12115071400d54200a000c551a40810004070803450f19004420320101c62900483c2442e08903800744031006000601e81a40e00390b040380900850484281c019034206003100c04505200d07600e9034486d4850b001c0c102c00281081030784412000100320f200e00655010880400c04881910104d0003801c0c08441c44140287c10721030102542d50340c0300904051341910301496503a4a508104a6403a18103600042c0a900058102c0032201d81044126044401c28461144002ca221000074204000c02e0002000e8480110309005503c01000d0940e10440c40d0b00000c00560240c0c4a417032456004900c0020300980e5400c004e500c914a032071140c294420310282c94070501452120809119030422945205d04420311104200034a51500070040143c09a0822020300c3c1401c404c41c80c460b501d1a94090a80300100011802c1180303c1c0070380041c1940000e0009043c42d0702e500cc842e8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 116804118 1250 116802868 116802871
    0x9080f0a03051602030304020409050709090302100b0307030c0b0f040302060a0309021002070506221d1504050408030a18060510030b0c031608070201020d090b06040e01110306060d0605030109030206 87
    0x1400645402c0009190f0002140c48032a400e00701d40044d41165603950801028110480d01150940620782c3c002403500b20301e00650640328803039000f404410803010079000c1104d051003800c500ca41d01442c010804543c01003821001c0d5920300110a565500410300c40d0154420350303200a4002a00203580c00c070391a850f501c07005540c0d100304c0d11030310b40c550780c6942241e540d2054000c09600a604000e40c4100901204040d01c007124041c00c1070703103060b0f40d50100c000e0032001d007080d4442c2000358504010301e542e00d44104a0342c124003183e0070032440c00e040c1c50700c2820b070100078080620b41e075840d8002044c420081c4500d8651680c011170a001c14a405c40070088140d0a03840100d4850702180d01241ca071680d00070580344200a900c0306180da03050118011220134030050520019550308001808843d2030750700820b924140100d246150f41c2c180142840100ca020604081080e4503100d00660402c0326082201d400400443e007540d1180d0310015036100604681e404545c1c190300c0c1500c580101600401c089 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 116805368 1250 116804118 116804137
    0xd0809090604200901020f070312180605040b211f060201090b13080c06010b04230a060f05160f021f02070b0a051c0605040e0304050f09040609080f 65
    0x242103a15918140425601d10404083c490520905000f1166600c48040d2900c01070501c121001c500c1c2e103c035080c0c146002c1d9081031303030006000c045481e0600d8010f0549402e400b034140300c2040c21480d0100080c120701890044240c3e2490004402c0002a071251a44212640300354030f443c1c0c5410250b5002010005101c0601c1c1811000c00d400500f080c01841400007803070700040c80951a940d40c00010600882010003200c7d03d00080c8a801e071600300421103580039242203d0815526410080315002d456409200740031820034980d60009a41c03504040c0004a40b5241409405014050b00545580c02451340b00c0c01a94001f0000c03505006c40e02071010000307402510001d0130401d0704d20f411203a40c4a1800807001680c4400820811296440e00524188080d032512a050034000302d440000380b0144500c013040c1540703a0b642840a80342c80e100f5240d05803101c0380118586031500021860300708000b50081d00c610b11210026081c0030720740d0000a10564042032040d41c4401c04001c0c906244c02c0312881 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 116806618 1250 116805368 116805379
    0x1413050306100b03061c051014010b0301060c060b04110a05090418021807020a0605040318080d02120705030c0610030309050d020d020409060f180b100e0402010f030b0d0809 76
    0x81030144002c0514041039a0001019524640d5a070051059411101004410380c0d001c81c441e410224034140032403140002041b2000c1071920710b003450b08501d124182c00203000d54408000402619030018284e10900d94008004074906c00300800003002441e1030207881008040002d0549c48080e03000c002010314050032941003140b0085903821401c08014588002d4002c0340520708c0046040c2c81840044d44400c0c5481117581c010555030b103600903146c0c1901c0072001300c2c0a100f502015041e000c05280040d000c01c20007400c4c04030304c1400007036448403440c00701091403000055100501005004403110b210307070f01e02103e0031810309140e0504080c3c414031054000a80304140410985413010045107102d400501d0000700f201a80c003000300409603600e040f12540d0341c038402e064140c0c0c1e01380034601c008807500680314a84120b40c10000c1c004000184080e00c0701020a005110000c00c140440350015028603000e581c5041c203000c150000c01c40d02e0002c0c0d50118038881d01c2c4c0e0420002070010800e211060f01c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 116807868 1250 116806618 116806621
    0x1302070b1605040e0a02091909050f101412060f010e090718181203050916030b040803060102030403170405010f02010507020a110406030807110a0510050702060304031413050306 78
    0x700386032494024440500016400c200c2002021050b102c00382e001441d0000040c5400404000a00f035054100e50004010b000d14100700411446885081d0788406542c40c414014a418a81c3c6100f21540e401100300320070f501203031500141c4596040328000041e000468a0f28108080c50040000c0244680b1803212600c100041848901081074422203c0000c4004800c11981d0740c22800b4081b041840050072201042e100042450010740802001c1310f901e00040f107007008109141015050301c81100b845402c0541040014080b120300e651090304125610f80300d464000040b410b61007070358030213861000800003e2042d111000b0003801240c0f001d0b203850804800514040e1700f40c5030203c99280268102d81d088234042007003c008814840c2c03009100085164481d90742c100a070301302e03040641e0400c0f995107080916007054541200034010888941154090040e001041c41c0715200c0028068071002c000f040406014804000a10f1400012030f52075110032000c400310940c0320710600b4030a204620 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 116809118 1250 116807868 116807881
    0xf04090509101803090905060f03011803080717040b0c090607050c0109060305160e15040801060f0b03060306070507080702090403050c150c0a0c0212010c050d06142d1302070b 77
    0x41c000f4a01a41c55240c18940900c0c0880490042c500201305a4200100500106283d5000c2c0710b202c2c8200000440ca052030481d50034000c001490041140c400d010302134030000400c00c0e40032a1503a1055005400740074a540707a06015a06014050310355802050109040e4108900410a20b428000c22fa0307481c4034080e0340d050100e00351501540d450704145030204090b05494418442c1c4420754102929050008403001200c1c0f1203580305500c44100c80e5075624050003150308a14030840180081540c490442c10000c001a0701c4002c050700d6071040c000005003010400007a842603030f0a0b242c0040c45210640b03064100946560301c0b6001d4001c850180385413801901c9a5812914001c0684215660900540303c1c0240d68150f14903509a80c441448404544100001d0140c4680c040c036980d11252142400500b62040d55119008648410383c0880c2a03099615200c102100c0300d4540c0400c420b849480303407551940280131000c1241c10101c04000b41c00d44c103403650028103ca40c411569030b2410f58951 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 116810368 1250 116809118 116809151
    0x20402120f340c0c1d0c0702030607081308071211011a06090406080607020d0210020c0c091f0303020303091e030901110312100311010f0806060f0409050910 69
    0x640c409030301c8520b01400318401c1405415a280b41010f0900c10900c08450301d6419403141a80e0008240c410440c03e131038030180300c001203290088515242c030ba080c03901750750000741c48030310040442003041800c0001500d45803081d00d02001050304540141e6a80240d42800e81202c2c464402c8080032802692804407a03820500c00c6140d00d480d9807140c01400d4180b0001c00c03110303a21100704141e001d40c0310440820b03840b5003844002d0003000160010480c036120508081d0601c002d111820300781c14818440802003400c04200170382c042d0b40c221441a4603968001d900f001c0029848080c8880c0c0030110000b00415400100960103041640b04a4000350107100c85020030848001e100001d1b80c0051280c0c9078694003644980e0074010b6010241c0c2c4c00c00c180d241800400b02c400310350004950074040e40410038040240145100d0010038a8407041d1410703030319409440c1c0d010103403c9601a000000700702482c030825005580103070ac0150000c3c8001d0a0409a00c2e907500e00b00307440007005c58034141c25800b45160740f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 116811618 1250 116810368 116810401
    0x605070b06190603020a0302130905040201020c030a080409051803120a05060d03120b010903050f0a0303152303100c0305011806050108150d0b07020a030801060206130f050307020402120f 82
    0x11080b440b0020b003020380071000307508941070200600d6001d1110011980907180103178080c02020400194514241c0002440e001c1e014500c0c0b80a9042990400d01103072806003220151402203c0c0860b03181c41c1c19103090a10040302a400c54140000704001895286800da40d50051102c01c00a0040c0e1301c0313000410075054000e4100802040e100000d0103503140c1c0d15000002ca2040504040d41380fa40e4a448550920344a0074541000350440940340c01016058031403034038450541c0508003901814000c10402100d51100140790f81c0c80d00300e540000c195810030201e500c249100105100480380a60040c01030030f02801804502c0d800e9000702c143d803903030500c258002c440e4169582000c945030710085a084200010040c0c0e00000e0b01c0d615000401d200920031409588035900a085090890800415100040e0000d03011034009000f40700e55040e0900051060301e401100c3d04000c1a00342c6803261035445000d0000790070900200d845009a1b5034040c0d81441540901e0003188a40d44842131070704050300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 116812868 1250 116811618 116811649
    0x60515030f0a030c020a0b030c0c06070203120414100c0c0201030b0904080a110102071707060e0708120c03040e0a09020102060f0402060711030a0204050c03090d090305070e0c040b040605070b06 85
    0x100b6820500400e201d6038468a80c9400074002c2c0d180252115810110383d0f10440e030808a44c0030000c1d00880c8004100007550348128184003550400d0200005503221000180c405090141d8041812030b0328042400286c40e51900c66104000702e8003510130103021840c19100590200f86407901c111480d080445041348660340c41184646407140405090303c0c8900103840041d5250750a200820000e10300018050403c9003100d0507076103c003814a0a0000e0790051074800c110b5400c8401c04006500c000669444222601040c0a444060f403111081c55030041e80e01140d2500302078014401c2c1c00410707502113101c0b14000c0e820390f5043e65500346248150b10040d28001e4111008204a10209481101e0b001d04c0c284000c05944442d03443d0740000c1e05030b6200342c900704140035000050001005040090705800d2200e0b00b0901000c91558031056100c20b2907200714070700994100001030b4540d20f024115005068200c020a46446d1100d000600316000140100c4a400c20030011070801d2070400c51125180c407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 116814118 1250 116812868 116812873
    0x1060b030f070212040609050405011d0c1c050114090106110307020d1e0629030331080105010f090603052a0d050f0c0907170601050403020d060515030f 67
    0x4650350301c140c2044070014821400c42c000c1111038282100301000500040c07699544401c074460030141040119141170b8881085c031080c2044005088000081e4241d108140e03860031500c4603031400c00d1180c4030903840001c0c03481c00c0c07411002240124112481894141007610007007010b0b81c80d004141c64113003896001c2261548180312a1006240001c10716142a119416440c82070000c0341014650000c135050031904291075540c2c240341c09104c1100c0e41800d94290410801700f0309900046900c80c402c900f602254000000710b43d0380740b203e00842c075003507030021160701c1c802159a40c0400f030b000709000e015103254200c825000140f41c6d40700340107542c03e4941141c09400580b00d954800c031200180115290b01305c42c58a035034003486643c0c1c1d1141e58119802040070303201d00c01442e44034a0401c00e6081071988206108410f000300c40d903000900308902c18500a8442d80364442c9001600c8038045c40d40000c0d40681a4040c103c2040034640095001c0c100010760814003c031104101a00c031044850280b003d079 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 116815368 1250 116814118 116814121
    0xc101407030207090609020d0e0607090501030b1906050309070f060e060304170a0c020306131a04030909090807060b03060105032116060605091e190e100506011101060b03 75
    0x400802005103926482401120701c62552000340e50269515548014450390340441c2012003889140030302800d03461140d02420040c80c189001414419660003068100b6542d01045002c9496000136080400003900e11455860307504d40d8010056030040782e90302d9250040c2d4500240081d400a08042078810649404d15a21041018400c15400c014820740311140704018000352100301c0401480c000e00941c1ea04010000300e03006042c50b103680030744034140402d0320200b0300010903040340c908620406485840761854441e4141119800300d0b0382c014140c414a40382c0071600304001d0074001c1040c68030600040c0301400054040680341c607402d01c00d641d095008030002c1040d90407038025000c03105203a802402e08002d103c0001124061580380f00700c40165940c1001c1c02185081c0c2d600c039900110f0007450300761038407144020211002c0c014010b03035100d50b070041c94501d0307010168003c4001c000d00750041f2044102c2140d005405400140c2d00c0e14003141000040c21002c0c401030082800740c8440c0840e8501d0f5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 116816618 1250 116815368 116815397
    0x807030b0102010b090f100e060a05010309030504080625031b0807030e03030907170f0a0b0a0b04090507030204050c0a020319020309030a21030903021507050c01021303050c10 77
    0x50101605114110f540e5011040c0d80c1d40d0710344003401d019201003050004a8a000c200081103224281c0094454025003401c201e6913030f4920440509541d000e1130301007650700c0186810b9940e801541c006d003415004d240e04115004800c01e0035039151001e48642d42e8098610528190110381c148100c03500c0071502a02a00300c0c65000c0e410351394010407039103400200940005402c904681050b80d1620180d000f80400f00684100184452012540d00e0f02901120420207011940d07485241c0c0020aa0854200020b131009955071008032040c1c1c01400c1401141d03414030301941c481826010481c03082d85132502203404801e0100945c0c1c40d148541e0000d40c54410300c03141c3c451920201c4448003045100c1000300d0309507900d040c41903450740d40c4102e4802081d800303804410a0554071151001003094034040021000c60341c0007031848001048040c24802540380c000c8110f4440c4154940a0740540c000503510f1280b040a00d1108107c81c081c405894400000c49c0030040d018a030a07580e4400102c43c034070840311 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 116817868 1250 116816618 116816621
    0x4090803041b170610060f050313080d0c020a022d0603060402070515010f06020a02011d0f030d020c0405010b03060a030b0c0705010c03050916061413030f08130e0403080703 76
    0x35964002e040e4100390641e560300d00001140c6a4403003c0c02c0b50441000e1090003001d848180700078100d1801c1c103003480a64904001c0c40390100403c18000002c0c031004103810b1100c56021035404c0b0340391703240501000270f0b4001d02943d2000d040b40c6c01c078020320a03084030486948644090b00c01103203c400340420340000c17441c100201d42d080a0503581d4495420030450000440c01c00c1103050071200703030707510140c1b940c540440c80301007e0f5164000c006540000d44020010703a0701500324030060814101c5d41d626501c2103004542a41c49440481e034151203881c0900c1005078002440c1400c0d0141100d040c02960780b54150783c011400290380c069007011140f1820f20015544003c00c82d4003a0503800c40c1030402c811602d5260039595091048001701c0e9458060204d40f140038400e0040028000182e68840381c582030008045904142c60040300410204054003c170002081e180700940e0083d02880342a801e5042803030099101429030308902250000006010b281500c409214681607201e03500c1c0e0340e840034010fa0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 116819118 1250 116817868 116817893
    0x108040b0c070b0403351815070305010305070e010b09131404060e011811010804031205101a03060904201302090118030b060603060a0315090201110a0c0311030a0804060513050409080304 82
    0x1007c9010303140706000f10326001d2064500c80d0030076a0b4042000d5155007040d50a02000390072010b13604100e40e0061100c1410030003100c070460000c0d600c8244a0f6846003c40004120b601d909241c1800583c00380400d00c02980c00c0343c022145030304001c01500342c0310301030364007140e0241c03000920802400103500f445602814425501034001c1c20401c001d000302e45842c0b000c41301e0071980350444101c00e4505100c071440c0c0300304c0c40d20392840c241c1c560361540c101900000c40b401c00040000f01510b4000481c060100180780110280b00e0000d050101160802c5045001a4100380740c081c2c00150850004044440568620011281c220000c4c44030780e10703498140f000703c1e03000a00c06600804500c0b0f0020004190b04034000e441450200f0000b1244440c0c40010b0281c0c040050b000c620b036210b0100d10000c030314000c5407501100ea04c1074410700100344c0200402e0402d140d83c2c5001d440b800c0041000180c085d0004001d007011500c4504046906880d40e003044125180d840d0007909210050000500090401d459903 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 116820368 1250 116819118 116819161
    0x618020c1c0207060207060509181b0c010207020f030606090c09030123070e010302034b0108060606041a18100f030e0601050108040b0c070b040335 65
    0xd40341220344030303444076114501142040c01079211010810401e40e040c0310613809410189012407600c0382800004020444c000c1b0a02d020000300c9001c241218041c4180864031080e400410752101052107116000b03420606085c0e0080c080c6150b06001e0703140214015109407801825181140c845070250b42103034001c1600b00c1d40642d6034691210f1807000070b1484101d00d00701032000410a20b081d070350041a60034141081e030b0606005106100301521200049440844032030150f40c61701e689041589070b0346107410680703010312882c46462880c0703032840c0c815036042e5030b51202101d8258642c041444083d01c41d5110364103040704000802062410f2001c010980c04410600219908008e000010100600703400e000021441805070469040e40500482c8030484440010380030540c548000030f407240000070001080c2c00002e00000d10300c4805402a500402d4003c00700300011700e018030b07010780070380c5000318012221300e95544841186c035600822024882c18210030002c2c1522980c003100d40d04110b80641c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 116821618 1250 116820368 116820373
    0x3030f12040f080d050103121e0e0a03060608070501021b011b02062110090209102d170a0903020a02010e03010608060c0a0311030717060d020907120605040618020c 72
    0x3201091a480140556135188800040c4a514510700040f011034010030a00600503000d50000003658400d1020303d0322000c500740580c840040c41d000400e185113540004080350300e002d001040c0130800184c80c80035100c1c00c2c0c00712500e11181240c0340c0440d00030440b1140c00554085484200422400350072010301344090042818a408000760311050f0341e00d441c009a0368a552002c0011500d090751140000f01900070045107401b0345027010480002c04901483c1c103002d003601403100d144050485503801e010007480c205000c40310f40c1e240208011b006c81c1d000c1500141d0040418087c1916200d06004036a040d00101a8440198010b50380000d1000b0219815540c50400080f025410300070113200f0642060f0283e42ca48080c50050121b50414502100a4605004005006404c0304c1105801d4004060f898207958070800001d846107581400250008503203c140841190490103002c03140a984209200c51610340007032004941ca284214002210a50524104940030368014521015240103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 116822868 1250 116821618 116821643
    0x203040b03010b0a11030a020a030206010b0705030304060c1e0504090b010318060506060f070507211208040213140a060503060c0d18020406030c08060f07050316110607030204030b0603030f1204 85
    0x840c5e411604004003000268001a101808040e4180461030140500d0f1019078244041038580941e20700009000802456490030180d248030700852108020314100540e6121103001c0090092480d00288a0705144905106410800d5800b074061044114441601c0c0c1102c1c913441d032180c50141c0400b0300100d400140801500748201e1248004219050040d4001c20f03109107418603104243d0010840d034200041d00481d4040020881c10024039040c0c3c451502080d151106c0c000905250740c800c0070b1008083c038180301c1103403404c0c13400d0b4940d1180181c20700070007441e940c1d03505040e1604001c54086030621f004005170001c0e4841365000c3c0c440c10000c81c8098100c0907059004c00c040f550981c0003588c0003000d001d01007100090030480c0c603a201855806d00403590800400152490101030501c0a030400d40d240c011240354800d0364180c240540100844d281030826200c00b5009501c503010640d040b01c0441c0020315070b8100001212010100301d4841440d00005404102e59200302030b1044580004540c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 116824118 1250 116822868 116822897
    0x80a0f1b08130b0313020102070e0402010530070e03010b03011a010c0809090903030402130c020d1209150507110123040c0e1f060c12080901060e0c190203040b03010b0a 74
    0x4d903115500f40311900d00ca82c0043e0001901c1d000d816403210704050804800c210050341d100d8255110301d00005050303001c00c00c0c3c4d0010843d0302c100c2850b40002c0f0016290400c03040b250f02c00c2110f0201402a0020041d420840042c142600c001011900d800c01078240d800c4429442003c9405001c0d0040707170b4079401c00a1501c0015030f0b0b80030650b80714049074404401e201c15031500e00044c103c0450f10f620100817945811070013035201c2240c070390350f0001e0002820a910034035019403c0300000690100401100503000142d44004010036204032000506007001100d45810501c5000e24119171301c094407048c00d103001c0c004005000010811a08100e503010300103071400c1480003460040d841400f001210442c0084003500c0006141d01200811401650130340229041000c01c000c0c025a0703103807100c112340d9001242ca000d0b040e180e00803000a0706034002c0000b030282c040c0152011001707003d10354004541d25001207980b4001d5006075000704004200401c0305890101c0142205901c0d410020f80740c020b0f1a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 116825368 1250 116824118 116824139
    0xe0f070f02071703040924090902042316021b15040e09010501051c02090f0c040503070305030d200412050c09070314090706020a030507060b0a03080a0f1b0813 70
    0x118040584c40443d050100042500900d00050300307007440040480c046c0601e01d020035900c1c1c810198803d503100c0d0700340b056450365003006c0d001043c04403000c040c1051410300e0f040050411190101191040271107640f17001d10100d00c12807941d0841d031103400b85512138010050b03445841410080c03200010000040c4600710038142500c51268031000040d9580b40405101c03106050500c100b590154084c08400142d0310002e00940080c0034103040c20342c0b40d41d100d84c0201c0c180710301e41146500d8810f9910000802600000901403082215001d200b03104128001031410650100f5200c17500c04140004c1c01024521428240c50901490444a000b0041d0010031750180e070940d00e0f4000240c40384450b07158078100c0850396422a600e0300061000501d0040000c0d111009044001c00b0042e001078400c041c44002d41207105045001003d1004984d41c0313180c20082da610900c954000300d015401c99005050081d00c41d45080c607a0185104e1a21402d56100c6086a0101c81040412a1080790100750f06010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 116826618 1250 116825368 116825399
    0x3060603080c0f01020418050a060f080d02100510060c0503070606090207031b05071403150a090b090c1003020f0c0703060b0f0303070f060b060d0e0102030f010e0f070f0207 76
    0x38000765540c40c140103082c01e05210f51401000c00c16030040004000480781103a100c440c0c0348a085002405e912000d40b1344010b030103640d01c810b030f075115080c02c045941000801c00c00c1004149800301c84414031103148500603240304030780c24100303460044002c200d1140100d115641d201e101f081928500545503643d042103400d15004141015404556030007019000504410309042030700740c155400c042c039602c0a07558440c0b8045c809200100f00b1148685440400124900c210a48401100d0b403070b04101001c002c0100600a030b5a0207800400324540d00c80101c0da1703008040000c0c05400b0180c0d947c40050f4040d501010707601c0c1401004005999031102e0510009000e9486100c0c046203417030500081014400245c030f03280344a030b08100050300c0010769100682d940c10b0350041000c1100c00310710b00000c4040c0621182540c41905102d01c0d1440650107500851051100d6807691107035903224800480800d01c1120003080c8103143c1d5010942d202e00030340725580c00030384900c12507450a44a00b0080300f44840b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 116827868 1250 116826618 116826623
    0x51c0501300c060e1c050727020409150e040c05011d0301150504050c09060315010201110f131409040f110a0602010207120206060109030b09190b090c0603060f01110703060603 77
    0x240c00e640304c8152901200d0010180401089140300710f98980340c0369100d01c1d00c3d20682e0315001220305081074a0300221408441007410040c115240d55880d241c10000d855070b40c0d032000360ba42c4280c50204801d4500128030340034941103180031039010704144c015601d15014080c1042440b560000881c40c2e95000d0007403480c0003100100080c03c1c1c6180005000c00d444c005018020320402c14400b185050706c81d48182ca0380709030040c505450b03203144040142e0041c02d03081d20480c00518002550900c101800700100185103424009407003c581d1150015001401c0050240d401041d5a0109010030742c0135910006590040300d00742c04002c003e00014448003445d5200b080582d4012900005002c1e03006040c41c40d1040a002074001fa20302000024041c2406001c01071010310144046004100200f0000b03e00350384c0c0141c85a41d1080034102489081d1007101c1c01650780c810100b00000740e05050060324010440500765040303507080e21005440c0039500c1980da411622030384c0c1d40040460300d680100d5000b0350 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 116829118 1250 116827868 116827877
    0x60615020a030201110a1b020612010605030415020f1b0c0402030108010c0306090c02060f0a14070e09070e060301050409050316080720060d020306040219051c0501300c06 75
    0x18082c0b0b006400d4035400c0806103154202440790300080e50300704440850b00002d64040092481c43e5100148030360044801480034801040300124030340390058000c40c0124080c102402c0315207004280001a84a04494038441702030901a16040800f2a40a07233001d041c0c8100b503d680b10a0f40c800b10b8120b03042644603c1c0c0a03034403542d800d03c41e15010f00c00c540c050803103110705004003c011b00001c2d503181005800c00b0281815680040e07038140300f80c2e00100440300382c510117504500b0a6040103000403481105288100340040c0412502ca016008164034080040d0085086170b01e0710042000800310075100b40c3d8640002c0000c400c0c207129817842500d600d0711940105131180c2030750401062541d4901070110003480f1051203221565901c3e0181d500d104854503000d40e5135903030040800c001c0d0180612890250030f216000344d00c2640c1200103001070a643d00d442c408444007448401007030350030a10408840480d0070400c582c54007070709803c448004114400c01c03e0401d10380c2c0e07510400b100345540b240c00003d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 116830368 1250 116829118 116829133
    0x5061f050a0e04020301050d08070302030c1603030306090e07090c170f010f0b12060409020a050916141e0306040b0a0305010207020319021c03140c10060801020f030705030406061502 80
    0x40d00034010030002c881c19101141103604010100b2080d41d075280c40034013192000310b005800c0500c03c02c201c60061a4180a860301c0d000e641d201003141003c00d010480100b030405001050070742c0c191040803401030b000703401403107030341d00c2c0640380001003030b052106400f08104021010003c24002038600d00691408414121542c03514140c44120b0849811100f000c4d48200403c500a0788003503070854011004039800102d04549100007a402c4049034000343d0001484002c01802c2840c045200700040c1d690340b5007840545d00210902c0e0381d880f40402c1c0182c5c0341054020281c0c9103145201965000002401c0004c2544070303403000a42d90715950348211001d070740005d9200218101032021542da200301f1107494900c8100f9900003040c0300140c100e07055000201800d9030003418840d54413040340c0305039281003940e00d40303543d25050784070444032400c0b00d401350034184001038414052003124101545820342506684501e101100e02d41e2000e00295641601d0745408030305040302403400070002d0b14940040269 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 116831618 1250 116830368 116830387
    0x40506132112110703170a06032001030b030d0207121a01180605090103080306190512070807080609030703050a02070503030d02090f0916140c06010e07090801090c0905061f05 77
    0x1d6500e603030f9100050311810b10140001a400002c03242d110f103010795901d81c0c82d645001940000b406241d0000e4902420075014400154807002d030540c610000380d900b03000b42d4000000b4555070b05095003a107001030b400b080c401c02900a400c40044c48007485180c1c0d04103920000140d40c0c1c80c9400a8020168035000d50b15207130006c10700340c030643c4014407054921200661468440c0b0810340002803155000308008031002809072031548070600681b100810b1502c0141d103040019136101d0242c0102c0308140b25982001c41c0d402c2c0c0024185200d0040c0384001c0d440e0004581d0b0807105030300803040e4401540724884010403103540038009403080d40c0595030016200d810300e408004060101148060103400311406001a0140e85049800b083d4150f0a0031480d034112000317408140d210b840703203400c1d160040030000b041406c0c40d10b0b049401a285c40c5e9030303202d841c0d803112001d034200c034202c01008000b150074542c06c02146059801403503211000400d098460043d0400d08104200170ba40342000081c40016007009 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 116832868 1250 116831618 116831621
    0x70203040807080d0801050d080d1a03120f070204090318060c060f0b030a0b2a04050420030f06130510050a0602010e1009020f0d0303020c01050c03040506132112 71
    0x10a071050007401303003941d40340029000050600a641c002c2d805610320304284044941114080c80e02c002d402c100710785100d80c2000f0f0300010a4071152290040e2101c080308000314209907261072566147c542e02c0d0040aa0802c801000001012810701401e800c204108032042c0850000a0103244c452880303021840c5042c504031054401012246413920942d88102d8400050001803d0340c01103102c11961944c0516081041890384c400d01c841070842200001486070300301030400c60b001a60288603401c1c3c01d400d0280403c9010914680c41c04003400003a08024101c07000396000707400a02580180745044424205442c0111501140c5020400303080143d401c14a0b100030090100d88000c0000f03030040c00701346031200c140c211101c00c1503031213941c2030301555500e0301d6000010b10010020b880e00140340c038001d00030303420202d079611240d4070b0030000458891a403012203100d20b5100b4060200742d55803543c04003007468107030402e488a5016031045035a01040002040003000c064070741140c8255240691070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 116834118 1250 116832868 116832883
    0x406060603111219020706020c01050105060f07170904091a091207060209040209030f0d0801090b0f060703170a1d010c090510050904061203171506070f0204050702030408 75
    0x104151411110b014001141402ea400048801e402d040d525201d280c000c1c40030b040210345135809940300007040c1c020411154010042403c0b024000d0140b42c0c1c1e1903082205a01072521201501401085504000761100702640a00a00c054085040a00900100781110110101190f8051440f07501d800c45030503803050075600000400c01011203004202d400b5070140540130000b4030450300886c241509986a0b01034070200100503007155130805003141620354800300429200c1c00300355941d0000c95a40c202c1e010f411402080030b003100d061b5001c00410300c601c56200c0e01090b07040250410b42922098089110b82d40078000b900c1020803603603c140c000940800740564484110382c5403941c801e50154104d10f01504455080b65003451900702500291790500c80d803010141c0c85481d2180c0821090000c5840c4905940240d07160005000d0701c41c60705848031020f94007090120f40c922440015843c00ca0000c2c03401910901e00f9554a250560214007901c1d001c0d200f81015030400304060100e81d0b000c00c01321 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 116835368 1250 116834118 116834129
    0xf0303070305010519060f0c050a0b0f0708010b030402150c010f0e0c040f0b0a050d1e030206070e010c0c0b030c0f030c04080105071d1005070812070e0a0e0a180b010905040606 77
    0x30001c0d0b0304d00100907207158006c211981c12310070b245030361600344503090003550b501c03603008088a000d034075040c00201080c3c0012143c3c3c1d40030500404c00420b104d00c00d00140d900c9140e01405241300c100340940582d846401110b0b407044c50b0764807406d807100c4415060003440c50310b810f00c10042141008902c10001a21661900351440c28a40004610981e07540c0652a0807100c0940e40741c6243e00c00c50404400c40c00d070185040390f0300c13884206110101a80000e04034802c0d003d99a40101100605004482540c00101c01408507140709200f0b0084007690350080d604280000e030030074034004810071b02240c140c1040791450001640400c0811447e80280140340d40513041e031030301000125056800d84440748209800364040c80c03200c03200b100705500032070031900b00035003041d0310343d03201e01201440f020380796000c039000c000051070740308500e03200d00b058140c03041604c0c3d02d811107000944c1c8200c5181c00400074a66109a0321003034082c18008540d5502419001e000026400f18003868281002e2040e55103540c8507 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 116836618 1250 116835368 116835409
    0x20030318010212160f020402070203030705060709141008091c03140a020403150b1314191a010e13020a020d080603030f070809030f0105070e030708011503140f03030703050105 77
    0x9500c4c01c070100c1451303d0303001e510000601c1084640e001040c024080c40a0080d014400011460144500020a280f1a5100d81e581c0e6071980d07110300c2100240e4095941e4543c1121000c10f0b8820180e000d04941c5501100207803c60304018a00d5154421540e425034508006c40ea0300c690171404401c1d1041e03040c1e80081003042c25458149180c1c6c1d403000440c0c01080b0000340d16544c684c0b561160340ca08190060305008102c050140003030654420782e41c40c000f920745c0c62a1769a01405070003403241c280141c210300c40b801c100700c807143c00300c0b1801503402140c000c0405a0054030340c8110b4603000c611f4400780c8120102c03175005000500701020064005000608094840d0b4000d2020426045090040b50700c0340d031744034007110307152501400481e1038500810191130855003400100030708580d000b007400070020300c101e0840f80c406946120303003402c85070840782301c08411080782400c1c00451800c50284c440f0003140c0742111800002c4134007540c00d6070810303110701001a4070b81c001080035180448041c0072072a0200309 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 116837868 1250 116836618 116836627
    0xb0a03030504031205042402010e010c09091a12011e0e0303010909082a010b0105090901062609010504060e0c100813020406031103160b0720030318010212 68
    0x10003901c18040d91000a044440d500400c202c0380d41304100303a400502c0d100041000703111020700e84490540aa05114005600e01080c0d0021400c05014030602070345d440c3c9414103170a00b1304901002a2904201c03c6d10881c0304c884001e005521504100034608604000000302001c1080c3c881d002c28282030a00c81c07405040c2215506003041c08400c0b07a045400c600ba0000317a0450030701e8803112030300800500b00d800010783c3e51491107010103049400c1411503d1002040799520060040d5442e000d182805034100085100521200340214a4000c01847ca140600d01e90b03101c084480d5060035003203c1d01220399459000740310401113140075058800d680e410242c4160407068000c50122043c44902801b0042c0140201d880640142d1080444540250060042546038141400c00e161404402c500911600c81d21402064581d12110159a01154042d01d44502522407511007078200800003404a00c00442d04184d1b50100004d090b4410300300003194600300d4007800607040a4840ca213145041c8010030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 116839118 1250 116837868 116837873
    0x16030905010828060305030705010501030c060512010909050c09040501060e011211010807090f060206060f04050f0f07050d0603120f031a04020f070204090f060b03070b0304080313021906030b0a03 86
    0x9600340302803407030b03845885099141103c4100608a6036202a241d40400180c200600106410090680b40a403104424003035494104940b0340c860114004408241c0c00700510120525400c00302c030340c030300500407140103003031800002d100300f03402351000c885503990346c4400c014035000f0300101401040004c1c041c605031011925007030b00741c0302d10416a50400c4240c3c00001e0300b8901a42c04036004d010702d0880803041d552968070296079020142d0307039244510130385064004a8686400346038803030026601400a141c84043c0240b2400b60050072900a00c00c042c416032907161882d11407040118018005c0d01c005681001700a400550294501000c05040c240041003808100707061a0013072200742c5005a80d001a10b006070030b24040c020009520505001505007401481915200640c0c0641001c000555100041580c5c46005100302040300e6804d00c00540031510030800b5581c000c33410500b02c055a10f190b40040c81e07801480444075030000140a041c45465894810328058403015991168850f0458 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 116840368 1250 116839118 116839141
    0xc070b0f04020f1207080d1101180f0f0609120c111e010e010504180e0d0c031407021909050a0e061306050c040b03040c090c02010c1e03060308160309050108 69
    0xc240c090058132002c40d00c0c0c010308030420041c8024003641041d5000400100c43c02401205200601c40c00307903013440000404003500302c21180c68268450b4010351800c01603910481d44d605500b200b510714641d204030180218001301d101680751481542c50400c00e8100c0e142c180305422140da04140943d4210640c40e092000d1091010003204003400c1034100f00c861040100e8551003213804c0310300c4080403002d180411216940041000c4464101034454079030324280300701d441400e02c40000e000140c500b0750394450064090004c1006070b00207001c0110310413210380c8000c00799155900882040380d56000300a12080107208a000301011440581040c0c20520340001040b2008200507285c1e940d2000410341c0110b40004640092a8a4600d1603c82c80c141c241111045903500c2000d0311039041142e440c081c00d2045c418041d000486d0340b900d010854050101d98407145024403441c040c141e0318100800821040801b0b422030703000324591281c400c1c0c4103140c0180f041140d980a48e040c8101c00062283c40c1d02d02c2c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 116841618 1250 116840368 116840389
    0x80f011d04020108060d0f0f1a090d1b081903050a0b0306192d050f0f0403030902041107080912060115110c1f030516091a070602030c070b0f0402 64
    0x24a040c2da055152480001c081c0c1b10b40f0480107103440c0f00044c484c420070080b82c2c4011091350041c4030010030700c0203000391902002c4049407000141d40215400c400a039000c0c0000340e07061507031500075004000d50383e0b0ba400702540c0500c42207000000b8043d01c000d03010354903000d000c6d031201030351b0700a001a00000740030030399a010140041d614444148110504842141e000800e5403800216071302000c81c01e4007804404941c0362a046441605100020300d0702c9903880c0c250760103800c55184201b801d643e240c800710002c0c01540c070104c1e07000c0c0c1c0360b03008909080c00342d00c090400039008031070705581ca1003000c040144403030911100e070b10180c010200401004001e03686001c0c568030103007010b4040d00380b100740e0b141c20709904a10b0194000d640300d18400c0c0340307010524040214840c44d00c0420460303c44040300d03001c1c10014407240300043d1115809021581d0b828094050b0640141e00c2035091061503500c0350b041ea0011955501e000390003250f00c02c244a4a1460f254100c000f000e041c2c1c946040c950007180794100e4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 116842868 1250 116841618 116841623
    0x15060f04030b19110319090b010311040e0106060e0406050f012a080a12050702010504020f210a080903060714040306050402060d0c0f031d032b020703080f011d04 71
    0x101400203d01074414000d80c038000e14846410441244102811480384e00140d6a24188440d0306260080d031800074400c4084164024000d410581e00c3d640d00c24001c1c840800b0080d4105031280b00d6840c101100f401440e001c4d05840e1640703a401640781080c0b1085422550000740715a501004070011a40c2007840018030703082c920500141511154235041004e80e44000041162030b0000d6071b65070082d4008001051483c049400b8082502e6419040342070311000e5402135409419581030000c0c0340390401a00803880e544081813a41c200b107079130350142040c03102d881c01d0328011000274042c601031605108040d07100c0c400e420000c950345800402d01c0e002d8004e034000102115620800f04082d0340c0d460003900c00c1c001c920744061016121403d0001c00300071442c8083e40100b418000500d24101030107900761025154a001103040540314400580d8228102d45604142e6020101c140241c01031030004000c400e000e5100e031112400c014013002c030600c41c143d00000000303a0404081c947c417544503445541054 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 116844118 1250 116842868 116842883
    0x30c11120909060d05031908060d03171005090408030711031303030c150c030906061203050f03060406080d02061f15080c090406120605070509030601030f0c0f090515060f0403 77
    0x550b01d03400700302a0885010b01078175602c40403880b4004603542c01e102c03014071f0040d9a510255515100244658807000c2d00e80100450b551800300e00101c86440c075070302d0b40301c82e050881008580d034910102e1140c290a50381500c08200000800001a811030501582c00b140c2c0702c000c51034400d040201032000300d02400010100441c80200c14107020100901040681c0c109900f081201c183d600068020011402c040b503d50b410a00006030307140d040000003105c05c1e015140c85180811041280c04070364002848994003590b0b480011271803080c204407940314103c864006140d0f5003442e1404009400410000702031070000ca40c4d083c0040300d511038140200901e9410202290b49980c50b8482c030078000c00443d160854541a000207003d40e5942d0f903815690301501c07081000d5114a031044030584288041560190b0000004000013541d000508030700900680b1380100c0a40c403800342c010810402c1d400391003116140c90902c2179a130061814200c680d50300700c40c2c1e14500b4003491143c58440c001c610002d070042c2d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 116845368 1250 116844118 116844121
    0xa02060612062a071e02040c030b130509010e060115091a040b0a030b10020a0b0a020301140909030c060a02040302010e030a0c14010c0c06031514150309030c0a03030c11120909 77
    0x16a84001a603c0071544221000f0718601e058082d1307615005c811100b0b91255080000d100c034054024400c038001118040c1520791810813000c1140041e100242154a4a40da1200092240003052219038003030507625200100d2001503180040c0a0070f22900000b022400365101c40746610f204000b15070441325150845074035040b111200384c1c01060070300c00c22a0401045502070000a40c04251201160f1060401c06850749901c0c4101007240401d000300c1401d10000c445003085440c14000d0316501802403003c503868040501d0740303d030510000751862008660046828030866030461417030300030b00d9000c0e00101142c0000d6101c00028451900c00c42411603003544000c4090f034824a1240d02c1150081c0d000040b85a56031402130050005900307801c2442e1034800d020883c4000c2803d01168410003c0c080001c646940d0081122070f40003404030b04407440704200b185034500c3d05110b000e0324035000343c80c001151190550080c0c0356000e5417580c0202900002e40d4400702c00c00103003d40f207150708251241e0886 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 116846618 1250 116845368 116845441
    0x604150f05010b03100b09030a0615090603030e180f0c03090115030b01080d05030c0d050721140901090209160e060c0c030118081c02040b0a0206061206 67
    0x414110140111581c14500081900801c040066000d14034101130300c0041c82d51901490b501707002c0c0020503641038205818000c081030380e0390040080850000c00c000b40c19507036090058201e5415030b2080300480c020100d481c4903403404011940f01c4030000340e0803c1c4c182ca0000c0c80d07540d030004010700740010020003001240c4400300941c0020030304c940c0d240d20320b6003058803802c2907802d10f202445544070f688603242c0c2154110b0321038415240142d1030503903640d04102e92801d19802400b4000d001008001100c400480380304a0a1594298080b03041c0000485001ca014000e04aa40007014000280e050400560058403050000d0b0382c04405d00e1264841c545160a0464100080320840c40e805100864401c44004010454841d0f94104400070401c500b8801e5905400c1c11410002904e000760601401e100307aa03402d00201ca1441140d02c0051411791110010440f0350014070205c03005034003441c200000e80c00c0c4051040703000c055050042c2154646210f82400c000d01030040b102092807075a180028 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 116847868 1250 116846618 116846621
    0x2031c0c0f11060412050c010309050703030c080f030403170604060f03061508061e0601020601031a060409050706090306060b09150a0507050d031a040c080c160209041118010503060415 81
    0xb08054020040c540d61a034400c2c0740302e011800300b10180c800b4014992040c05960082c40780c820100e600c1006003960500e0358406481c00c1d07a150b4010303074003c01c080041e010000b0b0103d000754400d074801c0d141c901400e05c034110074081d142e0717004110901807442d10034240300c2181c229103c10f007160750000c0046400c0400d140001e1a940c13035030b0302040c068800c0005000e07848000c5940700d1803100c5408608200781d6540e070012a0341e05000c3c48013401605150540409541c9084242627200c803000d040490b02c40403503607076146000070b194400c50000703210007018010040c2900461005059450300310707041c201c0540004190140c41100380c80700c040b000070301c868000e0195069901d219000350944083ca1140354000d405000d0800b07070703002c20039080f0700800c90600c0c191161f1000101c0c140e071070004540d20500e9001c5294002c0526074002580f84c000348005a40c1d841c4007602c61841801c12170300300c0b08d00c9414080b075211711298840e20340c4002c01c010301c00794a001885a41c0680c00c12045091801c66004640 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 116849118 1250 116847868 116847893
    0x30910031808221a0703020a0f03050c0706020703021003051b03010b040501090b0703080a0b0303120a020a230915040b0d05061003020909010b07020103060b031302031c0c0f 76
    0xd0880e0807002480c2880005405800b07002c81842c0c039070384403007808001c0c03a8103558a4050114030540c2c1c600040d5131080424003805420b44240100c41c00402a6290344203917240200c011000158002148003103610144500801055140001d04085e411940040e00000c400d560040070181e80e1f000081d019424000d0b103900e8400401c001c1903813542c40c2d482c0c0300500c5d4058040c0714040340c65018002004200c3c80c0446031340d00c2d095956107003d40c4500301c45001a2110020301c650611040c031103401d542d01400394950040c3c1d0040801640e0380c0c0d00d2074000d0049541d0040111002c860b011201c0d0500c10084201c03480720200321040c0e03012101303120000c6510b006a400c108035101010400b0f0f074a2440c00c0d4807003405003408441041e010b0000035000c03000e0344581a40036410040c1c07000100444200b2802506407548141008113141c0c1d103540c070032485a00110350841092051510803000e5090511915a0038850f01c01002d0360220766007009003030410070a1004000e007086000c0700f010700c40d101d00800d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 116850368 1250 116849118 116849141
    0x13050a0603020a03110304020108130c05060f04050f0a030c060e0105130801020903211606020c0610030c050103111c0f02030106030606080907080a0212070518180f03091003 76
    0x1808515252800140203420075000e900200c0d280000094800840500b0340348202c0c0e050b99400700c941c0d50b189071301080c00e040c1981155050900c0c80045007540e2150083c001880440300815102c03803504080007400311001c40040d010340044441800403840c44030110b000d8078480d00708888290040401202e0600c5540345040060400140100381224107400520181c40203e0896600c11400965403011b01c1d907407070020079440c104100510b101120095000c040502034070005041001c400c5900d81410703c00c840301d684c020702c0c204052003046120442034000c0c04080ca0204031075418000914a94800c0f14480c40e044201e035003c1c00140040c98011310200c07030131901c0540d22540c0d00c0c500a0060181c600036540400c4104e0000b420010000800d00e040702e43c40001409854100d4081c001d0071440480020910f000d451808607240d03d0700404074a1846140300c0229861901c0f8400ca101c803c4201450080c5400c4900c4c0307490754480000660301c60304801c03100d4241e22190440150011f101200a2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 116851618 1250 116850368 116850379
    0xf250b0c0c070b071a25030c0c020a0e04031103090a050f0d020d03050a1b02060703200106080304051005030709030b0711060901051e010308030112080c1b040c020f03040b1305 77
    0x142c405c0141d114410300020714482d110780000c0c1c58400072409556250031300091152074901c40b040b41640704e40c11180a06d882803c040c1c0401040750081000066160401c81c2c03d00500424007041581c416540c440b800d0031040070354140100700740003a82064852180600c20010f00e04402510360b00e50101800c0a80c0c005c2a6110003481da24001c2d280b500400f0301d038030114082c035001101d164041e502455040748d00600d01c0380380540c0c40c0d405035025085003580305d2843d0110702d1061804c840901c02e003009480000b0045459914140c2041070001e80c0141d4042040014801e00140c00c1c0c0280f8940c09580d40904101050b98542004486801ca00300c6481c606100308400d06c8840c45040d800740740100c01c55500c2006481c1e04140e400100c2000384001482d1500402c010044400103441488000c0c2c8555046460486e550410601d041200348000c4001014805800d90501d414821034203601c603103002500740c40c00c11410381a240d0065114180c50f0402c0012180350780c410b5000c1401c06400002e22 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 116852868 1250 116851618 116851627
    0x709050d030c0201020705060a020a0b0a020c0a05100f02040b09010807050906040618080a1e0602090604180501091e0e0304080708030a020d03050105090a0c020703080f250b0c0c070b 80
    0x200100110000070b02070303016005005021580b8144002150008203840e001000614034560b580200705c04014400c5610a40c2403103107402c40d840c144a11041e45010300010201095102c50310300480703614035200448580304000c02c02c60000104180d41c4081000d003402c0c0c0090b034400c0019074441c400c071888a81d101c000081c02181d89504844103080002d4502a004070940d20341c1411543c4403510403003d0144100860801d070f02d5521680341c1302081e84109400b50800c104900031031815000b980251104440c1209034403d03140c060f00c900760060183c02d10903c10b001440480a82d0350400c001c0110710551076082003801c01c0002c208036802030540000716080d15aa40c0a603644a030000980c42c0014000c038450054030034468042e543c10380f01d008000d540d031500c41480074001132146520f030f0020760141c80400400300c0d2000000d0000b40a1072040c65982d41040b11002c0e0040c0001c400c001c009843d404051000720b06065440c96100741012166996000c2c0d6444080c5002c20039441040d08590005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 116854118 1250 116852868 116852873
    0xf020f040e061504120c0509010b090102060a1a0f04021204060b010f0c020a0b16060e060105011214010512030d020c0c040513150c0e1e011e0e090709050d 68
    0x4100300d55058001c44420b8403400e041008400e01c0d2508101c5100060100344010780d0701c0500303014280d20402548840c281c4d0360021078407901c0d09900030b11007031801013600c05141d41c051103501ea1109134010200300031006101164070b0a510205614011002414049c03016107135a41281d201c507401444400061a00d854510050008841a9400698152006041c55000f001c4402581c0e1b8003e0906004a003001c03000c040d41d40011030902240e8407440707080404511a44500000341134001c02401c09903042c04009441a10304003540b0360303664070b0100c1c8000d00815203085581902c201712030003c03002c3ca64100c0c003442d60140e04201c000d00c42c400501448040800106ea140709101541c0070300441d5500d0003501000c01c410305019006001c9000940c040c440c450b84071424200450a1504000303100101080110000001050b02c0528070300c60542e1560308264681554094500803844240090720000c0030703406c4040d105130044401c5c001048445004a000c80d015100182031a260740d6a9030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 116855368 1250 116854118 116854147
    0x30605010503030c2a1e03010c08090a02010c03050d0219020d180b03090309030708100b181501020712030504030606090506030d03020702032e0c0203180904060e0f0f01050a0b1f030f02 81
    0xa46c08600c41c1d82780c801d0f02100540103011841c8180f013020040d200001c081e800544440410040440800008000c19402081c2e5803000d018803207244240403032610f858100113032800400000710400c3c0410b0030318a405e0401080c040c1416288034480711612500c82100540c03450041d400455818043d1000215410000051614146c0f40e80a018003c501124090014184140c4a02c40700c41c401c010000c1c0c21880d800004c210a100d043c412035003440e503074544e20300c9980c00720304085000480000b010014010b20f4000d49001c0e0030050010032603400c20780d000a544403c0c600540050503008542c54095540034800b03171000342c00d094019130780ca030748200d0340190100c218a10031101c18941440700030000d1000007590340c60b0401e88507074544148650100318250320001c00c1160001d131160010304000005216040300241c403100108111006d861265007500c4000b8440760131030740b40800b03c40350740d41c41880100020503e640a42c0d1078551000d800c601078502050482101800014a4043c080c580c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 116856618 1250 116855368 116855419
    0x180201030b1203042d0b0403020d03120f0b040e0309030616050c0706030203011805060303040b071b06080f01140303030f07170c0414031b120a051501030605010503030c2a 75
    0x50548070414580410007014030700c0c043d000d071b040c01210a000510050416001350701d0b00c580a41031294102010b800b00100344c0f001d0002041526440c1d10058049081a0080ca4800381000001d5800c0070381990110b075079000c00414005800c17903000345200c021409078040700c00c024400401c1d1010f050b11138ac8081c010398820300c55038010355807403443c03200c02c14010300c5400d00032400100554035151911504421035005020103403040000388510010f080540c1e1903800060005803036407096440c1c00805596030354070503400700348451f0b1210359001e0195404030441e644415010850442a25014001c03075921101598500c0050b07508011700251617503540291048405030640851244111410b00d600c4070fa080024600d500f0440d0851569854201e0190964010f81c00440d6411070319a25450300c1d21000541410030307051550014010b00210b0f000716409410250011031508040714a115684d446018104062803052200c840e003512503503c0100d03420b1300017030141c0e614520b4800701450285c3d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 116857868 1250 116856618 116856659
    0x708120f011e0603020c010f06090501030c12170a0c0f030905030f030c03040b071b090506030606010c05030a0f021606051201050301050717060d0606080a05070504180201030b120304 80
    0x180400011050035400c0c000c200c0d549542d900290703040c50524240d000c0c0d0090034035900d031552a0b8480c040c400010b44140c40003001c202d00042019495801d15a08403103050f000b1a0341e0550404a07100400d8100800103181d8181d1144203545000b070b10b07001c540ca0034064200a2130700702540030002c181503020b110321050319001c0301912034549030809915924070980340c88000c1c1c1d80007408100300c01d59021000d0504180282e01e03110011056801050001440d500a40440c541d628144261801d0401030181c2c44402030034120350307006854403410390ba40554884002001040004851100c1c803d12600038410201d84c2d94000e4582c0301c00c00900740e500440d010342d4083d9030f080c00016070352a05000325402145c5e1503c034880203441d96942421503800003000359030040c3c80c201d419000500340e4402d00b030040c2104c1d4041e01c41c800403490300c5400c00c1429404544218148030391400034a103120070312074000d6070908001801540710008594005da80c4549000a030102140005440850f003800c00c10041 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 116859118 1250 116857868 116857891
    0xf0e0105070e0a0602150c0c0f0303070e04020f2203080309011a1801031b0f1502150f0a0b01090305031b06090a15050a152309011503020708070812 65
    0x80c2c0c04814400401c0f101d02c1550016400440c81d4441d01c0c0c0d04625440d00312040e64001d5180805d8020324030b1400407040443c6600740c1c4008108140b150788000034200c46041200d0a501c0c20710107900c404c2650040c040c0b09410441031141d100014480c240942d001154070a43c00b035280d18006030114020700d0714103c502c05684002494000c1c900e0f00d1f04020300c6041c07803949194140d03401c607281e0080000e000a070200f5000324544011440718641c3e00031900030584844076510034082654000e00f001c045201074400102040107001034280011813150b4005059403000800c4c501903001283c01e40076a0748080c0c1240000210300342c0206101c4610000400c403141190070a40310708000c1d90b0f0358103420b02c2c040c008080c652129907070b02103507030041c03a040402d600c00450700d402484501c0d0b4007182c0a90009090b024804c604032503040300a004140003600444808510307615088000c803004140800300320030503074001a11010805220241c6010301c1d041482c068560400310030384988035109846030325503107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 116860368 1250 116859118 116859137
    0x405060105180606030a0c0513030c090f0506031c020a060203010b0c060f131e080c010f060602010e070e0c040f030506010504110702010527040921030903050703050d0f0e010507 78
    0x74401c0b01d1a0040401070702c00c80c81c40c0e481e039001100078070b4419800c2080003002c016010900e580c06a060002c2c50142400b80a11803a2020040881e03000c3c001101c411410481004256900440c410384405020424945c90400c00030b412401c1c00720302080204098030200021400007200070140803203811403402c950380ca40301e070301106a40103c2103440e003c0b0004403070359420005a82c07200b8440080314005507418002c0140d90340c0c1c0fa880e00410307414481a951000c02224a001c2c0d4000c2e14010903003800200f001d0f000c0021107940741c41785030080c1e4000c0544c038804198054088001c84004142141020010a403285890790311800c0a120b007a10550401520016000580d000c0310440341d4141c449503d00380b00170300c01901b8940c1c01034201a41c0c48000d080b202d8140c80c2d40c050400000e01c182420b000301c4d240b0b0114840c0c1c5c0411480e180b0100351404004c0070010b44c2040440d010541c0600b01152904052481200680011070020203071500f00090105c1d1200c05410041c010344158950150383d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 116861618 1250 116860368 116860399
    0x210320030f0106051602040207060903180f0e18010204170f1501050f01020a05120703110a030507080d0207020d0f023102091c030c02090901090b0f07170405060105 72
    0x40c00151980c00804030380c0001080301e540100010b000302e010030245200800d08a400040480e00012026501d598440ca04241016400b085500da280211500c4117030907420308050b070300c1010003801616140d0243d03030301040c2c030503d11108444030082c91030000e5640c1d0362110240240c901e443c4010001c6072084013180d0000c00d4000c107a51642e0a8040905822a880c0504004100c4d962841c01410750092411a0010600901007540601240961b169807001c561400800181e081c10001340307580c2010460740e000980c01030858440300c0d040306086403101d90402c0360000920810800030344c42803403941400c00304400d8105032101240202c0308da030b08110065071980b000c000c01810303004401d15a000d0005034010160b01800709440050844903024a050034092042056100c0a40c0491501065402145018000e103030f40401c020000740100b988968910041400103840d003a01980d00300e0000703094038802c40b4040031010385000290b005081c58140346031505400e001d258020203a01461006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 116862868 1250 116861618 116861681
    0x7080111040f140f0f0d12110d030b030d08101229061f031e06170f0d1b0503030412090602030a1b030c0b0403091409040302192103 58
    0x100420f001c2c0c40c103d400d400220400000c421003000642d440011041124041002805440e181002a40f100c604010703070144443e180290b582d004004040c20940d06081c81e032004909001e0812442c14260859218002080c40b5003509400030018208040c6140090102c1c2065048060020803510716030080d543d07440b0708603803604540e42500704601d0b500c240000c006202e03441451100c50719001942003c02c040d64111001030b11600c00015441d060f040c0f01d001c0e04039040604140e2040e009240faa0036140300f0130345070004a10309105100341c0311040c1c510b07110301040303d4061079400b030f007a2030344c2c0c0ca03243c43c12485c0760500104003400500b05c1e84010030124000022250411026140e402d0110b00003181011540c0f48034104800300b0100e1724440b00092581c10146002c0c2d0301c079482d10341d880d60402641d0b0201e10b1607000e49a100d114008180004244c000c03a07a84000580002051080d4180c0d00b004901c81c99610301144001c010304038640290b40d819481030901550780170001003008c4007030203140e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 116864118 1250 116862868 116862899
    0x4032703080306010f020106051507050d030c140a1709030c120c07140301060f0e0925090203060f03031b0c030a0c12030e030307030504030b060d12050c07080111040f 73
    0x3402441c007040410543c0d1700400c1510030520300e506c000326a4645440109a886101c800300140301000411040c0410005015441c901039507441e04004a01d02ca202c005c02d610b0359502d00f241c46503000103550010314410715400c12070740d84030041300d1080c0c1000ba11803652507100f480d04028a000d000303008078105a2030710886441071042c400409115081051540a5000c0e000c204e55141d96646400507180070407020280007044c0d00210800300f03140c43c80107181010360003200300250828580c04003404510000800701a00c1c07114600689a0f61484081f460703a40c00454007a50601c0040b0301c0c140d070798032040c00f502c1000c0440703000d4610084100e81815034079251084000d00754090071405100200364074210011003806441d241c85210392020209066500666060340095400503041c0f090102080d46960418800d131210380290b0440e403034114803a04000300310000c016002a110462010400c607443c060b004420007007010074280ca032907405680c804d208540d2220203a4000041070366446000c807 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 116865368 1250 116864118 116864123
    0x3061501021c0207050307030f1709030d03020901180b0d060b12061207090906060608130b070e0f12030403020f06030420061b06010314010207020f0418050604032703 73
    0x50030122980c1d0450b540320000c1d05440000c40c030a1000c005107943d0104050802903002d4001d450b40c0c165107041100304881800e10800a12104020200c042e40300000e01001c403002034034005840e200c2c0c0d040100c60070a51310703807501c1c2c00d03501722031300072909400800051002d03e00380502004495600c0d4020440c9000340044607030742980c00c00004185080c202c14004d00041000143e030151078655082c40f08940660030241d50080c0d440301c1c140b0179581c0000761260440706000002d400d02c0296505d0310302c0d0010050013101041005ca07103446540e142e038004c01010030401408042c52400d541d010b43c0e070f650003a21003684242c0c000e041c640007d0800c001101c0c015038008001174403400070341c032010245d00d54045240382c11a4082007401d0110f851174500140c546a180c000d0481549141001c0d600c5900306418800030740d104105810040c0e82c1e0602d5144825404c1e1008035070f4a03118124500c1440348128064000c0c000c14081004143e44030f60a000c0501150300101900a008904400c20600c2030100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 116866618 1250 116865368 116865373
    0x51504061a18041d07030605010f0e04060b010306050301021c050f01120609050309042903071809140304080a0312020a120f1d0c03060a0b0108060d080d09110306150102 74
    0x2c940010341d2400d99201540b0300680082049400f0715031080c80c0340c3e54480d1511454001d40410300c00c1141500030b06005108044444400c01e081c120a041c0c0e880001e08003c1040c1d40d80e0026410341d0b4040c0c0c00403c02028000d0007103444803900c0c243c0250803524108030500c0749140c80d0000c1c0e0030b00c10f4080d070f29068584019106a045000341c0d00c900083c5180f1100b9640780c0700c14000e480d01c607a55405031240348004940301100072039801d10840b4814010000051090308002418881704070a410003034401c141e1010003280495190402d10140101c02340c41060034000080c0200c0d032480e0005203000380e01d109564000143c814800b41e84201c2c09000762400005030440300031080c807200c60300920a80202c419002a20640c2c5481816500841c0b452000080c0c20010743c1c040d2600d428000329600240c00082400385083c038400080040100400131481119014202c80a12105105540c0ba8100c1070008200001d4141012030580340b04031081d40c030071f1190000062503c40c14070908848a08103800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 116867868 1250 116866618 116866627
    0x602010b04182406090b010f08070f0e06040509010b1c150302060a030b040509010e100207050a0803130803070513050d02090a050c12010e040309080f030a03051801051504061a 77
    0x45000900c0e12620520080e401c520302000001e4020b4031030030006241d5060006086c10a0500151140708800c10140500c103400c02048030aa4100c0481d46e4040c1c0e0354502008401c0c00c030000076030f56010f26003000b03400010703040010540c0d04010000b081c1c80c3c00814104d108204c6018141020380c0e401c5a008208c02c0e4181c201000181054006131856007581e0502046901143c4c1c042000c0310383c2100c842c96103a444080c11000c0321014040b42c980980b9071a07095282491a8072450380d01c000c2140001c182080000c0040d001c01140380f0601c140e9640240c03201d980307040c1400010702642190400c1c813040c0070340342000101460040701080645a0107040624165644002d800041c0401099618004410400003d8400d0000c0300603001e000c01d0310030170f5418101800c0040020585802030030a645c00781e03c045412007400400d13105080f90750310380880c441d40d039000a25920b00440c00310005a600300800d01c4418401e00a03050031041c41654204a6203550b003c0b00702d6555294170904408800411 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 116869118 1250 116867868 116867873
    0x110c100506040b1c06050606040b0717090d03020109120503010e060409021908012307081303050d0c0e011e050703051b07180c091401030905070b0c0102040602010b0418 74
    0x100900d512500091001411901100101d80d4680504e8640c22159185000020400405108164116206071000d86c10a800e0680d01c040c01e10071184054101d4040b4a91148103e28030800c40d602d01d4030150102e44070064514002c0d02804da540d000701ca403c101c0070388101e28203220b1000e40c1d0403920550100112a102c2c0001d000040403940c00598200d410f68084161041c51040710000420840c00005484184050260f24680442c0300740308080318003905208015070300a49542c0c20281c1000c2041d5941d60310b107000e9a0700c0c4204410740583d2400c24803040805a00481a1003c3c80d0017a00d540c44d10062240c81e041062940c1214180880d100b8840300c00489e2081c400740c08400d00080b0114042c0002d07231811840c2c03004d190300901e505800d901881044600c68001c601c1da04003513050403800701d4148000000702c00046d492032810155100005014841e00f00003040c014450030310447d41e90304011400360b010307500138010f01000d5030801320090f95600b01407080703008000c6e81565182c0f140c0b0159 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 116870368 1250 116869118 116869121
    0xb0105040513080c0d0206010510140a0c0204050a02040e09061b0708040e011502120304110d020319030206090d0c0f030309030909020c0102340605060301060314060a110c10 76
    0x2512000160300c01000080000c0d8440c0018004e8640a41c0249491045044000c0c41c089050300810700504079403180d502601d03004441c40200e082c20402030303602c1c0e5891120880b400b0303a0060000c0d5200e401c180500040700c4540e40100156441d0000c2c0d00344a41d68025032030303a40d050940f000c51100d01e0002c01c9265a14071100540041c030b104000300c1e403500ba521111424040020780008041c840c0103040301c0c1240c0d030100224001c0c07400240095045140903140c05107140c10300100940641202c0140c0021940c0900c6041c0074124a000310b5034940c5590f081c001e5864608031401c3c03505101e042c20744a4824020308070a0766440d0302c1034101201c20242c1e0b5089010b0311280004406210003d030002c00c82c0103090002d45900c0e036000000580340d601c0000002031418544000c2580700855282c290720f101594002049003c2d0001c901040e1500e0304800309004004983c0081d1011018001d0619116408506d541c080c0b00308030428017050004000c0751040788503040801545610203c00c5076080b00c500e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 116871618 1250 116870368 116870371
    0x12051005011215091401061d01030b0105192712110a120305030a0516120905070f09051006090509150a24180501140304020a031406041403070b01050405 67
    0x410602103050012101402d003481516000342c4c00703880e00d0380c5440e0400c484031092075005041d14586500c205010860900c202201070051a04041e01d038040c03051264025021250003041e07948100c203030a000400300921690f900c281101025400103044940542c0180180040e20002805618810241d55a0038480d19190f070f0141d4010184071000202c0c400700c0f0a1903074045000361a252f40c0c9290031100301044400081070602d05a42080c44000e686a114210207a000d002100005000da2141480c5140254035806441d01c858664004950411260005405019619206041c0700d032202c20503500c40d0828001c854201140070b00082103d0100c0340d0101030300001502d01402d460b101c60721912801c1c0c0030f001181c1c0e0004041c896009665201070411300500c1c1d42c260a000c0d0508000000308030a038a0071400340c076a6004030120b415940ca110030803004690082e00400c243d03445075402501d0f00421902520314041c8034011309510301c8003200300d40d0030b194084080072613a802d120800000340030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 116872868 1250 116871618 116871647
    0x50604150305130b0f2d18150a090303060e06010c170c06040614070c0210030c031104030f1401140105060f071202010501050406170d08130c030809011205100501 71
    0xa4012400e0007050780c07802c0381402034810200071102403502c0039403040c004c1001d1a084101c0da454102001c90400071380301b0b842d046200f2880051400c46400e40c040d183c035a1034507404824408110503c41e00505540c06080070601c00c0c0c0b010b00c0010b585003004e041c0c6500881d0543d01150040c1070350800280e03001380d0b1103d80300241003228184000001d0f43d0b45132a0342184e0032618561b4805a004e0035802d0150940ea01022074509166091402c3e80130411074482c0258a0003455202c20045504500070303008918000300021505172683d540742002d4240c5050b5140a035100e075281451810310980600070400b51803082581190140d107030005004180e400301003110003607401803192000040140c001c807250044030750300200355941003004000c100d4400ea8020740040c80c46003904012104003141660081d4494240411150380e0494401203011401500408030b0104640100401440a01400d010f22003030380c034200b105c0c10406240044800a40d1281c0c4079902030b074010080756101d030f0f202c2006103c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 116874118 1250 116872868 116872891
    0x2408030309060a090305071506090b03010b03070905090316050d03150803031303050f12040b09010902090406181a0108070608130f0c0b07060e010c0509060a0c020613060e0901050604150305 83
    0xb223440d80d04071520310f01c00d08481d0985410782000315140500401c1540e9074114002c0000d000713203034002552010760348104a00d464451001820401092080c1c4c0e41c48101039040c0c2541d4519441e00c5519032050780d55007008646421000d07180301c00032410b040180e078112130045180d52a4000c0c0120745aa07030201c1182082000c1102c03400b482070080181481d880e00000404d0380b0b05040c5048000607000510321412689440c03514005a51040c4034107411981001000410071400d042d05900e078000c1034005001e01c41504081860440050300c864104c0300020183d922a5844500480300080b05455034800034a01008210100e00005500040351f4810440280030a58600c0404900e4011420540d002d5a44100c0c2c50710215081c000c01044400742e00d401c80ca050002d100144050041000070310070411400a110115121801244e80e014508410b00b00c500f966828020310100308000d0081c09140200c000041900300784041d103060320084900c820380c504260008400411008103001c4841c0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 116875368 1250 116874118 116874127
    0xf1e03120e0316090b0f010206090a020405090109080a0c0605060d0b0103140f01050702070f140d12030b150304050d090b0a0302130b0a080105012006011401020a062408030309060a090305 82
    0xf40b103294a040041c610940c020814584620400414902030b00895055400c01b0b010445400e801080c0b0360600d85e03040b01c0c0000d00da11000c4c1c8031030042c000c0c440010600c00d40041c44000103038020003180023852092109000c299200700034800d0030320308454000d20f03100d0b0300401440010074400c0702429108801c801c6030f80400d000c1114038251030741a5030000150f00090002e00c00940514140301c05071070410079044000d522040810181d201000000d8460201102800203c91090700f0000040d10002d100e080e40310014968141c1030740c400c4d1001c0740c40d80f045645544c5198020901171044611300d00095082401e840000d0b80170391301ca444c01ea084849003100c04100c001030300c0701800c00680c0c1c99035414850743c1007000250000b040341625820742600450409450b68001582030305440e2021070940340f00c580b800060b468002c43d400001c041c2814481501c00701e0240700c0413800e006a034800201d41d01c0303945503845516440107852404943d006200040c103605118bc0000d5056031091900a00c1c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 116876618 1250 116875368 116875393
    0xf090103020c01020720130b0a060f0c0515060f01020105070c020105031003020303030f0906130c03020409030905060d0504060c1b0605040203030f0c0309131103060d1b0f1e03120e03 80
    0x60030340606800050201c040c80301d921807e20490019501c104800104003200d0303500c0014101d51064865803003001582d0020349600c0e13100d43e080100603a03000c4200c03070250200c281040701c0020101c4006000c1c000d0880d03101d100390b2050040a02501c0c603519000050b80c1c4c01e03001100e0701e0b030009211001d0420403400020041e102003000b14031030307903280580441ca424180c0c3c002d41081405498142c0000d2500c100c040400d514450b003c007101c0d411200002c180d2944d16003503620b030160381c0c00180e0201d000300310a0b0000c0c21070b4114502c510301c83c0c03c04000b283c071351510550399800310012100f9002c02da5802440003459607882141c0050009003101e0500041030f04291140d44100d04403080c541000c641c814490074040907032107000c840f203001070216441c8110030150b01d00005140c50702c10b8a032200241c043c0400001d2588440c1420302c203100407942c6850001e2031141c060700c02c55000c200000c200004010151030032a080c2e130380c0091810400e2130040d1044940880040220764580500038420b00c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 116877868 1250 116876618 116876633
    0x20d23030403050303040b01050a08060109022104060905010c0f2c0d081b03070f1b030204020f040e01051504121514040308280c03090203010903230f090103020c010207 74
    0x107510580041d40e17a0314061034079000840e810380c4080c0c022800403506001c803450204020703064075007070000140c84000503286411810300b410320402ca0ba40c00d007014002032148076040441071501800080c0900c250004044461841d28071035040011b4600e000000c1211004006003030100004102c200ca103c5004002001c040c02404121503545001541c0040e00244c042e01008410400015500308071241d01e410100c0c0c015400000c0268504200001c890004805690f02558014008544a801f00304003954254071a00942d200b9140400001405203809410811401842c40c035403030409181816280b80108840800c8038412207407210350301c650b815482108840040e481c424086410b2130b05000c2c02c01c01002d800c01640c4501c051880c001c1c54a03065800a4070042048001068010160124020316404c14020340c503500b032106500916600c04410150070302003c0e0102480c0c48100b51410580c41007031404007815505008010503503029902030100703040303441d0025240c90344035030b6150b031f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 116879118 1250 116877868 116877877
    0x9020303160b0c070807030318050706030c020c060301080c04051003140c0906040e060411032d0d020a05100216022205160914011403190c0309020d2303 67
    0x540400300c407107040d041c0100360710302d190020b004002041c500710580c3c0b5013500e00e1140390006400d050710fa06002c000f0094040c21400342c0c0d500617041e1000300740c55810040150860002d400010300c1204c504181f94a407900840381200c1001d402441540c3c024000d010107408010445601082c0c2c00c0c130b00002050f150a141060741c25407030042c205208170103007084090f400242070303e40210300e001515800034800107215074006401c00017403111840303090002494006046400400280d400001ea066400381c0e040300c90400b5440015982030011440c800c0b44c1e20121908081c0070b0342d00c0303010301c0a00500160b0042c507400010031a070142050b03c1e034000c11030440c2d0403500107400085085010804000c28030510340c100c1200c0000d000700618410000b00f0075482c0303003e540190480c400c4031000e0750f070103080703c8155882d001008545a140c51048032040114243c1c6260307440341030945d00a94580302c1d200702800d260b0700501407081062280c44412600e5202c100c5d0030109103641d00b01d01c400d14804c00140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 116880368 1250 116879118 116879137
    0x901030b070311030c0a1722140a03050c010b030c100302160c080610050f060a080c070605010f03030801052403070e0306010b040f120302120a0203120414010510050604090209030109020303 83
    0x15507194502c5074000c120268014406807400c41040c140001c8822071b841a051190000340b602c8c10002090800c40680500c003001510a0b200e4116440101500035001d021249204030080013a00c00100a05403030b095454080342d44825007098065880d40a03134081c1005401c1660956130280031a51030a11504107904001c6096001008201b0b540c120104404080c0105852480c01c0c00c22031030108005018055407841880b00202c0000c030407185000070307942401e8100c507040c030142d65038000722041650540020740c00140d10100214050070047c0000d40c80c5400341c104014001c800302d40c04201900054000317030810010701782c1c464240e0740c1081814080c100d42c82000f44d03640c0c9008030303c80307404500380e0145540e014840180c50210381c002c40c1c500d021404001d94a03944049850040303040d881042032210011100405010a200b41b072000301d85001c00510003081591140120888040c4007442215401030081000b480034600c103030054400c04801400200d001c2406900290443c9c122070500d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 116881618 1250 116880368 116880391
    0x170304081207021b010c0204200705060a020307020303040b06120610052409061b0d02030d051e06121e06100506040315020702060c011d06090c0901030b07031103 71
    0x624100304820729070036401540c0c0740010a00f1310303420f071107803d050350110351410305120500f0415025174a440d0419503440b80c480b403d4515505c0480820700480d00452815245489003400041841410f0701c01c070790140c3c06030740007582103603510f640702d1459040080210350401150484003001e04002c00415010741e58201031401001c1c20f2a0511401000e1510100e142c407038412001d0403c034581d4012584078120544c0c105079524000b2030800042c0051980c1c0244500c0f501003070030080b50f030200c05840b4070000c100c424001525801c41c09000310031183d07442c001050a07030f80842c0c07031403504400c614664070040d010750303a06003200030740c020304213801904800241e0420001c0050015001150b100500400c5852505007425601e84015000301c152403100f14642c0064500c0c1555078800c250392100c46c40740c0080c801900c181050071420908400d410000d8840e003004901c3c001c2020446001403c40501401c84c0d40e0301e152a402c820450241c4100149684e40c0c501402d0030392144000d42c80394811000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 116882868 1250 116881618 116881627
    0xd0b04060c020c10140a020c030d080601121a0f12010c0c110607170903010914150901061203050f0c01050103030f1e0503040f021306090902130605010203090d17030408 74
    0x700a801c207040c83d140c03c0e01c240800101103854a420800841c0905103004c500da0f111320300c044040c1d18080300e284003203038980303d03400c03045414980c442c2c030240c455402a40d138810307030020900103d4181d42c00b4034a0041e0125440050f000c0506142c96084001c0034001c00c2d4a402e04400d1034210f0031104071202503000940c02890701400c1c002000320f00e14071004103542c80d51808501d40c8070fa100b040c2040c504c05009600000b04c0d646c841d9000d4201c80034203a003206004500344108408103a603900015091616440c00f10002410300c0b0040c8100d000326442407102c00011011035804442a0780116042d03a0708070403c3c4280c40c1650824851940038510036160403510881c811030246c10142c03c030341040f591158840c1005060341c1d00000740c1c0d80017a4040103400f440c1d03042e81b000484941c1d0001c1410010f9280203400109032107d80c01c4076003418004da030440c2003090030340c601106076603960044601607032080280d01914240031600c070022900840d4900360390109035851410b03035402580c003510045030208 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 116884118 1250 116882868 116882891
    0x13060b030a060f05150301060c0f1203052d060f0d080406050a111903110f06090106051201021303080f04030804060807030c0c030909050702070b030a06031103070f0308090d0b0406 79
    0x3c101000b0b00000c0f1200d4545c0c9814000d400035500c0140240c0080246890030441080110181403172101e42c04800c0040241d240c0f0f50040007010212030b07000420032203800601c10903070403111005110301c40d903c420500356502c0f414081640001c118294004004003090340105111030b0180014020603a0b41940e0b07445140e5001b0701c5101c0403d03108000b90440c1c086440740d40b00c0030041800c51545402d2500642e2807403401d060800340c40018825107401510f042105003107040d072140042e208202c0300c241c0201d136591425400c0303000e0b49500c6008050703017540c01d00124405d0f00240090b90034150703d03640740036100e9680e6030454000d44d0100010488900a02c240c158140c06015420f44641c5030007182a9407039103004112550611a050781595510040f54820744244006400342100d81070312952403c2c290700c01801010346200136220000d9125006000b8913000c14054103d540b1025111800707800d41c0c451071115130086c036810782d0000c0c24510b0500003400c1c0500051140d401a1400a101e48060 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 116885368 1250 116884118 116884139
    0x30706090b0c0c06070e010c1407080d0f021504020d02100e0f040b0105070b07050409060b030417030601021e0a020a0314010e0102040522090812070e01140913060b030a06 75
    0x60b104042030310741030000040381480000c4050f40300015280098801c4034090044c1c075001c800007400ba1903000c101c2c802600c82c5000158140480703a00c41c046800b9112580c1c01111450604002c1c2001604411040180b091700a5150ad0b0064001049100b503051164009a080ca90724941e640124000e2821700b4010310381417420340c01e50364045e9070500039428600e0000b4050703c25248001c0c0740e81d8481e0081091a0700c19000c0d2f402400d5003200800060744c80c0c40c030303980841d0411901200ca00720244034403030100560707405803030103030700c041c0c00a2510741d5443d607246890508500d4102954850140d1242c05603540821400c010f501400c198500000614140c0f4252552006c449075160300400041241da00c4292a008145102d4a8403000302110400c406003e400e0a400261092a000c10b074500d03002401c1003118000d10b0315407038000580c1b40c200019078489004c20000c526200040c0700c82d81d140d041c103400081c01c0d01d50ba4a00040c1d1562a6174204196401c2a5442491a90765500c24420310000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 116886618 1250 116885368 116885371
    0x4020a08300a090e0712050c1c090f020d0501020f0f0903011404030f030207081204030f08090109020603010614090d08040602010608030403380a0b011706010c0b0c0903030706090b 79
    0x280301080d2802c0711060020f42a101c0714460a114113107404c001070f100c58071410314580b088960240512460802c41da41c0060f90b00002c40d010010f007002e00c8100300d074440500c5480141c0364058000109481107400304030b039000c1085015555950204401c0c0604050200206002c00303001404544403000c00d07090608548004500e210601041014040402d400201ea403850070524500903a5512091504152a02640802a0b00d41340240180410940c210300950b0300c4a80c1c43d550241c1c03a0382c82807101030a803003540d000a90803040420051004a00c140150302c0d821144080c00e6151404110101d800c41624007804c1c0c0310000041800c0c03084990a018100061103484011400c0a06584500c480205111180030b14002c013503480c2070001441d0608034503041d41c1103030822100d00d0007540100207081d480205a00007502c160f5807480c2a51801d2000c0c0c00740c04181d49050081b0110755400b60024005400744140000500421007280e40410051078464810740000c1907403065881d10b103221000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 116887868 1250 116886618 116886703
    0xc0f020109170d0b040204082125020406031b03050601170309100201090203030307030e010b01030c1d0f030a031d0603060312030601120f020c0d05090a0303030504020a08 75
    0x14280703000007140410a000c520001c0390b4034826039590005000700000c140740e00310705400900100340040c5100010880c8920301c654058560a0403110310610351042c4254403400d031500c45c2e000b0911720708400c0da51002c524103102400000c0c04d00c1c0c403600d40001c08028039094032000340c0310722004e104010081c410180105505102c801503501058051030b180e0107560b04141c0115a030094000343c09100350030a2603180d070042d0940795070303003481c8034001e014105200c051401e0398201103960b0b285510a200e41c220f07030207a95950044161200c01440441c64442c418a036000c0c41c1d2442c60409035600303200900d800f5200340c662084d1003881c0300c45900448a0011180c4c490701080c0100541c6031030104402c101e4000610526580303a44a400581d8002807103441f00031820321f8603250501c4040f20b50b00078144061000d0484891034650b00c2c0c100c0e958403403c21110341107080c80e2420030010303010781c0206820510051810807a9502e409000d440e2050b50980000080034911008590b0316840c81c020403400e4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 116889118 1250 116887868 116887871
    0x30b0405030a020c0109050f010809030409180c05060a050a050304060912030c02060109050c1c0e010903051209070b04050d0206070f0605061806210c0312130e0f0402040e10020d0c0f0201 82
    0xc1c40d184c00508d038040050382284c1880ba207500094400c00701401118003900018100304080c02c15820769010350510385034122001150405c01040302d01c0c00000343c4d5200c5240c0e81e00c0c81e00d03200700d06000b11420341001d042141e44d50f480e10701e01400034400c40101141404550343c0000c101c14501c3c1c00903e00700381031f4400c040d040e1804050100c1d22100504444a112111811900c052440c1031060028440414011660f52801000704201984180101040d405203032141c651a11503030f0005455007414411000c013000100f10070805030821a10250040e8001414141032035000d45903054441c422060441304540c1c2c03441000710703c1c0745c1301c0c65421601500400d01c07000ea25049000c01d48903160032081d00c0c444104d03c1d0105489001c208800c0081c0d110103400d440e24480d605100b040d1a421918907406c2038554140046401149050b1032072003040114410403142e1901e4090100500d10f600002815008504030002403c60707c0c001412000042032001500900f134180040803c61031b804200300310f9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 116890368 1250 116889118 116889137
    0xb070306120809090402190303050306090c03090c0111150f0a0e03040b03070e0a080a030309050c03010e07150207170604020102010c03020304200f0d0305030108061e010303030b0604030b0405030a020c01 89
    0x20b4012801e031405403000f40e070210810703165070000131f540703212150560150301022003011081580c031402071130090100340c40580a60729103094140d01404120303280c409030350110903001e07007a40c4980980711014030440142d500c5501500000780c1804411188070003030000303d0050043e5840a0711a0103451030249015604007400d24444000a110241c4007100b08100003440815541e10640c00754020241402110160a4646006000f821142200f41d40310700602041801506041c021080c80000203009050040d0420400d00b000501e101040021031003002d1000c00c1101883c503007482d40404e410024240b07071038140700090039100071100d0340d0201401407003440005407071029074040da40300f1490a040c6103200c100c08206d40b040d0040c0d1031644588a074008000b4180c02000a40c1a600f02d01c1c01d80310180d41d8004c01206803501c41e100c03a88044824070040001c24400d40c8110030140b0000d001c14a01036076520745005111003910b040e1240e8100050743c90800e41c04000000e9030400c20708018000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 116891618 1250 116890368 116890373
    0x9080f010c080f0603031b161505070311070b0c0f010c0201060b0306100212300906010b0a020109050a080a02010b01180603020d1103070e091305070b0903030c06040b07030612 77
    0x2501c002030500000b9468040211384c06513810300554026007500c51030080c095100c42c1c4200e680c2e0381403064204140520308404034688aa5011a40c00d04036a902e82e02d142484641d4101e0341a09061640c410701c0c041c1d1240400c20380034030801809900c00c120300404070380c015510061708642104801e031095a2410108206104065042e00e6111800b1204900c00000340c0030161300b89001e143d0f4030010850b0001c0c07007407981c885510600500c4208074151004c015610b5211240004043c4c42c141ca15920140c01001044003072801844034108510010507a0b000c81c1d44c0d8a4905051750703000b181c0c1e81d04003040514400d0340c24850707040e0031042460a03186404403188451f1640c84640581c0081507000110000c0e840c16030703080b07503070581d040c03003d0159649007240f0b00030510b94040c0801071003001c0d00750114135500490f289062081d03410402424542d858024030000d07551100c41415098001803205410261040c840c0341d01c1240104046141c600d400b030b40003021074895800c0448100100c140d060007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 116892868 1250 116891618 116891627
    0x30405010c1a010e091c0e10050c06010e15040915180c030302010609180c0302100c02060c070911070507120f02030f0c0a05041103010b0313020a08070501030b0a0e13060f0c09080f010c 81
    0x1600041d032381c4601c40e242001040720280300b4060309100314460400000b0308001c4010065104d030301c3e200514010b9524140420050302e07002e0b2009014992041108062180c0c9940440e08031078010420080d246000d5903004503038600b607401500540d40d500c00803c40b6403050f0181c4502503980220124040305030f66a409000c1c8824080a4000d041056841c810703240503182c50045607400602d200d48441e20000102d9480440d0f0149094003402c00c1e04183c28001d0714010b65501d10b60200150240606042c550461251095400d640103c07038180f070b000150714140503501c442103100f03000c0c00c038940e170000a0103103605490344142d0186142038869044d100901e0151780c19030b8034400e04c1c42d40d242c03907551055480035403113074010350321007150310000489200c0080d00004030744e02030300c083c4182038014082240b00c170494422b520364021400c000540f501000400005030754030480c4009004400b160348007003101c03150b00f00c110118810450500031102c040100c0c02220300844028010350120030300081 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 116894118 1250 116892868 116892887
    0x30c030905061b040503072904060c0f0c0b0d0203040302060609070f2d091d041509020112020d0905160803040e0c0d050a09060b040b0102030405010c1a010e091c 71
    0x28120031020b043c0d030810a841d03401c95004200040c00c64124544030000300803174942484001d880005013059004d0b07407a03aa842034608075841500c0d042440009500c442c120348100400c2118407202442d00802c17200c800b14040d11448104000042c0c9a04d05403030064a000000f81a0790b1003210340c64100881d1070b80c80b0030faa0f8400342c22840e003440c841102c880462848861a41035109003000820300441241d441040c41e002c54007504c0112000226807540c20050000940340904881c01e200c4e40070b0032030070064106140c1148103142c20904070070035400c6501280c00181a4400060f15180440c05207d010400b00c103070204000c10b4410054684004580e40344240d1041000d2004948001076003a00200c00303441d00d40d0600881800113242c1403040317030700824181c1001c40d0300f6882c0140b48100b5003014410034600c1ca5040c0c0095251074200790064802d41d40d9000700300c0e0460030440c14468440c00b5030410a0080c10684038070502c2c2e05111100d1424508a429207030000e0140b8810300b540c15a2205400303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 116895368 1250 116894118 116894131
    0x504080d0915050d060e0906160302031e07180305010515030f0a0f0503040b0408010203160e0a06030f091b0503121206010c06021b07030212030a02030708090a080708010b01030c03090506 82
    0x1d540e00c00c1c00042d2400580417075841444280c44d03002c10413400103004500688544207181c1c50b038101c001284002d8040b401300780c84100d580e140268840c0b0070b9140700204c50b13800c980d036400c020f40d4080036402c070081d025103642c00454081c3d45030818049000d41c2042d1000300c44c0811800751003045030780000142d8034241450f0140c82e525030013a5540501c9400e10440d006003003180846682c3d00d844501040c00b0798030959403002d400f1780c041c03030507694688541c03101d50303240b02c009081c10101481e01ca001c401400070f1303079600305913960341d8921325000900048454120700b070310081c201c20a0389003104040c101091144403010b0341d0410007041c0f81d00c10620080a501000900b007500003e4034a051010080c021002040310302c0c3d0707180c50001d81403080015088100d034403c4494280690741d0030289507c134044c4502940250b802400040001920003014080750b1744040d00b181081c65440301950310307185a580c004da000d17035544c15490890356854002e61600e840790341428400480d81d03071b5880b50f0341c28008040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 116896618 1250 116895368 116895377
    0x90f04051003150b03160303050d05071b03030b0f0109121401090c120203070618090203060607050102220e06010e0616061d010608150c0f0405040203070504080d0915 73
    0x74111040d1002079202031034100c2010314044511191a00c01440c0014001c0e20030301c9914075510022501a175a4004c0c0c95242e0741c0c140c103200810b58280d0103080c014018070240f1510b03050403859a1002c01c0c0c180304050107540d010810002c4c03003090100220b0160f2010341048511402804103030007620414000540c4686010002c0da00c0c041c1c0300d13004092540004244c2c075007249000841036101074a4400c16030084041c1c4a04030795501064500c602c0400c004100b0b0b8603021010004949107074040d65000d20b024004914007099036840508980c400c0d480d07009100310582020303102070040440e0101500200c03206400604080c00080c0a0805045155205810019070f01c1104004003600d4074009031700c40c40a00c1480c103c17400308107440c6140f00c54005c80d5071820200140d5120001080c13002860390348070a0350a5260302d840f003c400c0c6c1c0700c0b001d0640218400c010019513500c8610056104083c0c036a616074881e801d0807482410300b50b042040008200c006241444084001d05c00c02d490394025051 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 116897868 1250 116896618 116896621
    0x170a03050a09030c0e040b0a09030207090e07050904030807020d05210a1506030c030e0a0b01170a20010e0607030e090a0e0703050d0809070e0c030c221a090f0405 71
    0x411100d10300b0301c1d0401442900348031400101590300d60205800365208015480c0d0325a00d2134500421100c58045c0a8016031000904029031413030303a8400b143c086000300582e51181e854802142c4280380544088000440a01c10044100d07810300a4000043d89490036501d899003142e00c0c6503150703400c927860404111203d00400c901c03041030f40c0148005a01e111520f080550307100000b81c000c10300703404080042030070680300c2c032402c040c042800d505081c2d112000400c1c0d642070000b00c901c450f00484504d00c3c030780f0810403890081040441ca065014030b51540441280089000040403041c020350154007410050000e400069005007003104240130035540e51607140c1d50385840300040c02010903000c1450042c7d0300080240040070910300d0038102c1d075460742e10b02500c070350300c03030315611842d40c03013601c4038102d900f0046880740c00711000440d0042403500c0c0301c9003045424000700e0000d01500c00710540b02c10300c14400f0000d82824150510350383d64510482810485504c0214080c003256400140c030450340d450 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 116899118 1250 116897868 116897887
    0x40f06020313020d050601060906090509010b0d0b0a030f03090b030c03191d0102040e0114010c06020c0a30020303010602070512070305030715050c0301050f0d030c1b0609170a0305 79
    0x7102c9180e500101420390040c800c0c184252a00310071b0160000044c0c2144003c94094050203180007182c030060504031880c5c0c40d00c0240580c50b04443c07007400c98251100c8002a8135a900920b00014602070941e40c00fa071100f41c07601801100307080e404001021828003c1110104040080d681d200c64400c880314000160440031500824204103120a0031091490034034100205602900c180d0f00401e81814244c0d807500542440b02404880450000d082e01400000042e41d6801508030041134200701e0340d0f007100580d118245407503088a002c44003e07070718080c0245001c12580f0303060300700424005542b03103505004001b91a1230141c007403103016440c1c400e105090038404000410040da01b09050f039803604c195107814044590782c01c020310000c908001c0410100c18850313044904070b6800401d03a503086642e82d014011080c40c2031f00c095082c081158105030111704030f40c2540c2c1652080c595480c60344d03420840041d14100154000b030783c00d13131b070310000e41d0070852740015500810780d0305030406d00d03114410350 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 116900368 1250 116899118 116899141
    0xe0909150901020a03050c040e06010516170901120e0606190305010e0703020109060905030a03030f0f051f06090b0906031008030c16080109020a0512010e010e150906040f060203 78
    0x51003200d003110001080720328581980546068a01c0356010311003070311002e40a5005000e203020b640d003070300c000d0320101e2660340c02400204404845e0444840ea64103c41c3c40f01180021200189603050500240c004072a40c0e000d815004030050b03c0f0003c101c1e030040c44403000e41e18040144007070b026030950041c03200c0200081ca00c41c8021940b26000b8401c1004110100740c480c0602d04c8200c0c08290b40c0d620104045d030050303a408040e108003034000d040c1c0614686040b4080d10a044030a181c855903085000303458156030049500c1801c0000064107401c01d4042c4114408510307a11400812406c00000d00c85444900202c40600d10111011500c0751581c0400c00354201c440d42c0b00078900e1100080408d8850340200d0300281590065000071411907840d00414261364030414001d41c0400c490b6000c0c0694a40999014158a500340c00050f00310b403022215400c6800250b0381c441e40342c1c03101c807480402e140f070581d0443d4441c0300f0314090304442c1071a40e10344514403070003d0300030325a5401000242e00018034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 116901618 1250 116900368 116900383
    0x504140906070f110f1615050a050708090d1b080a020a030206210f040b160e120c100302070203010b0102030909040b0a0b06030403080f0603010203070f080604020708040807060f0f0e0909 82
    0x2d400b070311004222825011b80e2001030091034822003460440004039000103060100300c0d04410b8840724504200c5460071205039010715002c484280c000c0c0200e4445450b00c4691008851041c2c0340640260f454142e000405c9450341d0107138103168002840325005880d0740304aa02100d07070660381d00340c442456204180503031001d5041e99004c080d04000b00a40861002009802180100c2c0001441d4031001c414110b051226489140030030011071110050b4244001c240030590b003c2d1003911624082400052640030034021540f000980200d4940d0941c5028861050780081c01d00003185010700810102702c41c0200148050400e0030000d00240c0c8a51181e04020400c49000704001c0d601d1520740780241800a0944010540e245404000390150405200304c80c01041c890301c50304001b090600044686c1400201116002034003404500001109003002d0001340c640309014001240c03e02000a2101164024500810012035071905e151070300281c400d03001003401d0703c1c00002565004505481c0840 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 116902868 1250 116901618 116901647
    0xa0e070f061b062d06050f1306030618030306050405040201080c070c0e0705030708060d021507140f07180515040905010b0907080106090503031c0b120d0201060504140906070f 77
    0x148099040200c44d070500049100d8518013007140c080c4422003103d8212001c90082513000350040d4220724062800240013901340707420800100f21140c9a0740e0fa0001d42e54558050000c01151aa40074101905400f8503405804166410066850315800007000d00340c001c0c003007241a40e03000604009001c1e400e50140041e05030200d003504281046400185550f10071603043c0002000e020105000307107001c104000e80550001d2400303d200c40c0d80d002d14001640a68411190354600401d142e01e50442404001c0c40d50031024040c003d01841c103a9200202c0e0449118545110325140070070941024981d81540d10f0102070b50001079614841c541a80105031042e0010b501040003400c00244c1980080c1d000d05030381248d41c0380d0503500e40d16802e0641c2d82c0600071400403404491800492454500d44c44101d440800a160f01024420042814241250725103820010b0f5111403040c00f480c00c00307010340340c003210b1500203410840c5000c0ca50282c450308003801c4001001030031000303201c080d4132501da4550b0311107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 116904118 1250 116902868 116902871
    0x711010c08130303050703110109050c0103020f0904061805070906050304060f091505060a05030f0606090702120f040305061b0a0311130e0a0b010c0b01030f0515010605030a0e070f061b06 82
    0x940380e08000d085c80e04070034021170000e24200013030381d02268107008028805900c0401031010644110056010303402c03020901e07403070040c01e00049145541d1406040000e01800c0a020710580c040c48012003910700003011581070086109081024580c0041102c0d485900b0003c00a0304250900c04c01e40988400c550241c039600018154166500483d8000c0c0e02440d021501c14842039564001d00d1340701e90b80141128040e80001d8005280c030700707088008035404a158416105080a03000302014246c1000c1130003600350034007040610400c07104200d4075400c0591103091948402442d031111040b442181c105904060301c8029480c03252001c10142d80c0c6502010030000c0c0415202c604140360303000c0440d1640151401c100c0c0001065000b4064264902d0700038900007410f0703082d03444009528101d200100c550744982904c07405400c40c8180301030302074001640c481d43e41c0c2c18203174052010385640c0301c0e00c4001900100810000303030310004200790440c0d1460130030341c00060240001c0d0030b90686944001d40300b503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 116905368 1250 116904118 116904157
    0x170702011b0207050604030f05070e010803070308010504150909060e0607020f1002070201052205030a08270a17010f090305090a06050405030703140f0a0b011a0711010c08 75
    0x25010340010701d0030a6010180c111a02001d40101da581980c1d110f01c1d900300c042080140f002c101c001d48600c203054050022a68001d545048048401c20300760f202d108a0741002c9088010558014500f078010074088038213001001d210200c00072150001c1c42024034107941c41070700340c040180c1344d041040100b403440180d079a14501144041c0d1619000220a0450f000348120100d91868500c03c3e07450154041c1e4516040c001020f4521b0841c08034005c21210303610319100700048a5804000c85c503c41441480c146458281004031301000c0300500358070701c85906200320880b4003901c032440c4010885003c0411000d02061008a02d80140179080c0c400b0122070a00d10008103061304900102100c1c00c00769541821700d0f0381c170141142c0b01d006a000b41c644c15084840e080011540140510f40c0c2280c000c1c05468684450060301403801490540460324409a03200400504c1d4565961019400701c00d54031918100c21580c0f00780c2210300500040341800210003042c024080288250740782e03034154074202c0c07a10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 116906474 1106 116905368 116905381
    0x23040506090a090501031b080606030a0204050601030e0a0b090c01020303070906051804090c2c131106130e0606070f1112010204090f1103040b150117 66
    0x204102800c080351902c818404e10b4000d500c903060f0f040040340c0311111308510600c1d580c000b106e96000041001580c1c0c070003150780c525640d412070300002d5a80d28503006030010555601d0410302c0d4800c2030900820030001d01d0006015003c1c034021580090408001241e03a8402111a600019841c3d0b17006c01005000f034015000f112946a001e4103000c03844804542103a140940548075035021010801146860341004040440710381d840001003800307a000202d506001600107008401f403582c0700e5040c040e03900711000e80740100400700e0355640300054005140320040d0050a8075071072140d02060191500304222041540c1c81040031108040e29124400500440d0600d150440601081140304450a2000340080c00c2213000000d00d40d03480c00e508204903151110740c031a000c00100140710218000c59035195116021480c06250680c2400048807da074180c84910949200078052045 = true := by decide +kernel

theorem cover : BRFrame.Cov 116726618 116906474 := by
  have h0 := BRFrame.cov_init 116726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 116726618 ≤ n) (h2 : n < 116906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
