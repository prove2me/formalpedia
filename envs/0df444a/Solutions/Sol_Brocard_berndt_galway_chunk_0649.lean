-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0649
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:55:55.706698+00:00
-- url     : https://prove2.me/submissions/f850d532-1a9f-4f00-a71b-d9d541e9c1aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 116546762 ≤ n < 116726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 116548012 1250 116546762 116546767
    0x2030706050a0b030303090d0e01020a02010e15040b030705030402030c0109080a02210a03021507090302090a02030712020c1e010204050105070f150c0503100f0e010303050318160e0606030906010b 86
    0x50300340b0076001100040c5014003180d840e401c1511410391900303c660841800185d10a040d46071941c4006421004180c043e1950a107080008040c000c401404140030040200d0800000400401c4980214415029540d6941e100e0034548100b5041142440a02e8100010f4140c244182c2c00301090000c01144e0440c0c503640582d001000203102c4450004402645000f0314640c103052580100e40d00d21882801415550075598450096551440f1400065000301a80c0000341088403240d00440d00a48030b0f05103000c0850801c5459404d03a40300028000340c90300007098905680c900030743d0324420017178000020350070a03062000081c143d01039614007130a10040b0400c004140120083e11034030f86080aa418015603543c104040c0c10383c0e1059405074034451500c80300003041c0401d007c020381075840d0b5484041e5664a580c031304403070a800281400d5004000c2d0111001101c41c2085480c03c60030010f01c43d07000103881c0c1f05c804c400703010004103075901800d001c10030040c40340404075409055550100d1070a4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 116549262 1250 116548012 116548021
    0xd03090804050d140f03040618031a040c08070b0702011205010509060613180501150309080307050c15160e030610290304080d0c031e0c050f04092a0203070605 70
    0x10f02c101300e42c00100494000c000036401140070100040040d03071600c4d20b41c140030140c0c2c07103075000c00d4400714800034081552140399a0707400c41c07807140d0454010f4016490141a25100d0401078140711041e8030807244d02000103096011960005440c11107894402c4003013190f03614103400b254244030001e141a00c075180c00500b0340c0c04940c2c4000b1541c084e040314590b4242c4a98080da640d0000c01080c0298503004000c0401c51010510a001d0220784543c80420b690941c2c455680940700c50b0004031888005d4051040800c80301c004011140e441b03110b82c08880c1010015101e805002d558513407640138040d810010800c00c0303010780010b14001b190b810122601004446c1b0100b900c640c0d0761089000304c1107000000740011b0000300005410044a40402000002e5550390184c041ba811142d1104c1e0300c1586405800f028085680f10780c149021a007070a515260712000794805a0340590001280b07241c1d0341c40c000c8100040070f48500c4a0441011203100d444054100183d0b5074064000c000b440340fa11000003d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 116550512 1250 116549262 116549273
    0x120604050a1410060801020309010e0d020a0204150308120601030501060e0a15050f0d060e100e0f04032105040b0705030105010921020a03051c0302090f010c050a0b0403020f0d03090804050d 83
    0x818020301c3d07980c0308108554540e41214042e40c4203580b592043e60804070500181e02020800005007055900101903005441d0709010190280208940681e95100300010201d25020000c101c0c0d00b0b008181e0303440c00c3c60444005001c648040c6c110000704000c00c98088115100c18052405075000c0c0c2050351700d0b660044104803207d100d0100d003403d1000d004034160145000c5600018151100480c00b05040d40e01c4040d40c03640f03d9198803c02c9172082e680404141d92410401c80c15400c00e0181c036101e0811105c14000441d0341207841c258026499481041105100a50300e407070b50084040d207000c03407030b6524040009200203c0c1340609500f43c0c48401003610f480d00c1200862961507806850603145a50b6810500c0c0c8a04021034448078200e040007064801520900c200d03015a04010301c28000b00c071100004640304044040c00316161303c540100c01d00403a100c028200c0c0709038480d60007005000c00c01c09240c4c0c03c141601c50300d81d040c5030a100304000045c1c194011368056a60940362005000040e0514 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 116551762 1250 116550512 116550523
    0x6030d030b0a03020301240e070503041401060302091005041a151b150a0b090105060d0902010e04060906060207060206060d031b0c0306020901090518010303030903090b0c0606120604050a14 83
    0xd52647c6082c40103036040d02d0325100c0c03151018580007039a0907280d5a000c04401d61034200c0c0c00d02c0000e00208006400a0f400c01c03e03050010000000000e042a1a540881d025010503541c13140301d201c091408101c1468540240c030382d1103044111614800c03180401103542844801e642d01d5043c9404500709a80019031491407801100d41d0f011581c2144c00010140c15005040d12035518550805040c19910309080442d941240c60142440b40783c1071100441000030321441c4403c0b41041045c2d10541616900c03070042e00c000e4560316000003192803030b01c003000e860314019900100c10354201004004c0103039034000424038881e4144c184510200c1064000d100040301204000b01143d404d8880401400100c2e0b019114102007231b00d0721508103840d0800c00c8001840f00d82c41d0702c1d0030b2100302c0041c00060f11940000290901c681014103001c5d0f11a183c010031500800040c0200c1d034014000c01c203840c5480825a800c2090b100050b051600300fa80740c1c00d4882c5541c00d0090816800480102c1d01100200103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 116553012 1250 116551762 116551769
    0x607030804170706050a050105090f060907030e1608160311191d010302030708032811030409090c0b18010e0111011d0d021507110304120303051b0306030d030b0a 71
    0x202c0036911040c51400318002c05054440c2a015840c090010410b4101000301600a0301c0d841d00c068400e40e565010844150b60081102c000c0580b034841519208078104020b03125200511120b000c02800c015030705143c12900c6442099500300b02c07000300080b8074428040d55007828140d80e00c0fa4154401440060741d403203a0381c0040000f134000207030200044041002c203130603284210190395040c1e0340e96650540d240552946c0c2d503081003021983d00d0864601090014500e901400c140c400c0d00130702c074042070568005504c1001d03981d845188034010840860341943c0a40b9041c07c00a08003500c1e28600072070f4800c0013240c24140050301c0c1f01c0100781d03030280c1c40384446064000001d00c11001048502c90700b01d20803a012200764400c1418070f89140340040350080d200c1127804a1004244d448005c111807541120100141038042001b001c5004040260f5900c101ca02075140803819080c8441e084900c00c40b031450960030641c003841402059900412504102910707890f01040d61051500090340d4903440b9030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 116554262 1250 116553012 116553053
    0x20060703030c0c0f030c0b0106020607020309010e0d020d140c010c0335150102010e030f031f030503030103030f08060a030c0b070c08161a18010f12060603050121020607030804 77
    0x2135031108042e400106610940c5c480c9040903200c1e66034134010b0b42d480109450380b02c0560420300c02002d06500c200d541200c00031004000e04044e107501e8010409209500400380c3c0e046542014004800808000011000c802860600c2c0c42c41001e0710300520688110300c2e420990340d04c000c000c610303542e02c4d000c0100341502c0603002040c03d0b0800882103071751941c00c499418095400c101d0310716400344000c0166024842071040d03e92655940e01c00c00906d5020301c003c43c40c2c0f02c10b0707610004404030344c041010754080c500c40c0e21501d286010307600c070140458030001e0400b44107082c042401d20014542d000104125021001c80356200c210b40e01d051907401405400c030b192a44030701050403415004184508085039070019a41c1c2c0001c6003d00030408910810305180544000c0742041401944200306500c00c080b082e103000004c0c3c623540202241a1002d5174070400000e5101c10044c0504c0384c0d428a07000400303100f400800d8440e61b01d80d0214010b802a0708000d02840003007000202405210014a0b81201500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 116555512 1250 116554262 116554283
    0x3030f1b030c030b01090b090d020a0e0408070c21080d0204051e0a05062d0d090b0108060105030d120e030f13210b06040b01120c05040320060703030c0c 67
    0x4000040040000c0400d007800a82402c1c00d008095000d016210b040d0b1f000c2e41c195618014030b80302400728609558100300d800c249111800110f0701110081940103a100e1640b140e0b41d01c02c581403101e8109099001080004002c01c80c100546020800314043e040c1d01c1810b25803540090144c0c0d1000b0b010395441b081d00100001c92040510388a442902100784048800010b15519613013440242d004800035050264a500043d81079608103401100a40d00c0152a03549000c841032240c000351400c1c1d220440303840c2e40210052010103014041c2c1c60140105800910400880002c014602c000303804451005a076901500304241034140210f9102d5200386218540c1d60040b800101099640d522800070016400c2d103181d522068100c09201c171668022806a105403103c0e400c0000800f0066211414401400216151110107000301c045c03009590311104d0311540b46040c0234030f40b41c601c00d030600c225020344841e182c841c0d96440107590301c05405190000708000501001e0760101c610000107003d40022 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 116556762 1250 116555512 116555561
    0xa0b1002010f05010f080d050c0705041107030e1005071b030f030206090c0409030e04180605181527030705061003060b010f02031803120c0f0d021903030f 68
    0x15041030b4011941040100072a030303030b101401c501e101014002c070720303681d0040c103501d8900c90300c00d03c00361020440e0070701500c410640d900300041c102c0e2102a03002452000204001003030582114542d00e0015080d1a030410308010010024481d1240d00e00003030910600c1c00c0000d026411041c6002c000e03551004406100d1107070707814080d544140031a40010b0743c0c031030f0b504101201d080c10b0085032803456040e218640c20300704000402c009000b44501c480d448040e1074aa10000c100140120760051490a0318a04028000c0039050b0a004c280486a10040000000d004900035040c0817035440b08a0440c0854120400418542c00d40c4206840a8054491201072203400c0c1d030707020a0101141c1c801c6200701300503203040c4011341300307504185141740150b0000c2c82401c102a510308000b0251850082c1910103d4600401e01d0559800c900c0340302d540c50b4081d8030340c40d1060000300315003030710582140010405d0408142c54030012500fa101c00404040d03d40084662440c0160040d1030b0700c142145012000000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 116558012 1250 116556762 116556767
    0x20c0c031005041b0605040b0906090a27060b0403060504020117010905071b0b07080606040509040809010327020f01200d1d010e060f070c060908121206090a0b10 71
    0x82507605841380c01c1c440c800d4881c41e0052100c20412a009622010305091500c01110407507044041882d800070383c1007041d280c19668255002e0050f00c40c5044804003ca64810845040c1001c041c2c108203040c0744c200c040c81941c8081d403c0e1070440b0380c0301d900440c40d91b4442c8012600d90f8004450700c02d0345407000c030020403100c910b9000030b88140380c90b90f90400360440e00c4070102c03010b500c11f20016050f440c02a000c502c02c684a41006a417024026048a203040c1c2d942c400301d0f44003c0704407410f8810080200b882d040079030b8903000b140c803046030306d40d281c1c8903450080c642e100b0700a1030804000d100b0450320241001c20b034010805c813001d480d80034410f44000100c0c01001500c2d030176203003003010004d42d00280700444a0903054541c041320034183d403510707080b1a801c0d040c00140d0380282d030440542081808440d000445c648400009885140d561240b96490040000e181081e50005c0040c07840c0c0030b000481880c1052600729501103011201c0580d9074841c10082002808030a1100340c00901901940c0311b4141c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 116559262 1250 116558012 116558021
    0x130b03040b0c03060f12030405030a051c05040f0605071b0311042708090d0c080a11040212070c1505010b250c03020d080c07060909180b0a020c0c0310 66
    0x14007552600300941d0700d82020100c148412a81aa4400100803c0c3c002904040d003504d08100005001c4a02e082d85840000c0d203003d01441045501d544a000c0000603800c4035060050840f08900301a0300702410b01051a241c032209001d904200f00d40416014203025503550700d0036403d16a10303c00320307070700e6101c1c18101c10110003608058010750511815800c4044040311040910650b251200000700b41c4c0c0c0e07207101c1c0079405554881e03800f10311803903c000860700c0b030341e131201c000c0010800030a003842a910302481c9400340c0e94404c85c469807052100210307a240151295620a12170324008800903e20310340303020103060440c082c9a44914100000c2500c16000d4000d090b140743c101d0000d01c10300c2008620342020f0501c08002801070440b00c200704010300f4110103250200b8401c0d055a402c06003541c002d1031034170310158001030005039108810030508159202c2c014040c00c91084145058070302d43ca07180d008420240c0001c0e042e640c00900c407002c900052060100e10200102074a4030200004040c00180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 116560512 1250 116559262 116559271
    0x2010219050904180b18030d020307020105010f08010e031b01090606060e120a02031c1209031e020d091e0f331b060b0d0b10060507050a080a0203130b03 67
    0x100c2c5400c00404650141400300008598040c400000a03031710390801c44046c1c0384c40409020b040c40280100e400c0000c850024611504881c0e000147e07561510213a034208945aa00c41d140e20303490030152090600c4044102c0e001140b50030a40d40705000c5200e602d5004001d9110040c100030b1418801149650307000c803d90700102002c80c2c41c1e8200b0996070285035100c0c600141d001354564412150319110050200c40441c5400e0b181c141040c0d002c0c0810044411346080343c00490000d03036095204c104c0b410811601241144031440103200000031140007911115103800307090074204810001000700c66046903104090801d801e403503010f25a4a0416040c0c901c00e115811000e048500b042d0400c484450301c00e121350306c0407544c071a0801d400300c41c2144d6010080c6030003901c2da1500e503c140389040c1c0703c0703000e200c00481c40740c00c0d64a06841d00d8074144610060035001402044000c01c1406c020410000e080401d183d002401075a91b00180d940503071640c41001e40c0c1c0402201151700000700f4460420245108 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 116561762 1250 116560512 116560519
    0x30806030c06160b0a0902060d0b01121a0f060f0a050d0c03090503031503030d090b1e010f0504020d060f0305030a080106030b090103120c05010e01020414090112080a020102190509 79
    0x70300c9480c01000a40d004143c90400310b86aa640300a010541155403582c125411250000d003040309078021950691008410380d01581e01c400c0c0740b0310b207564480d42030281804801c81c10800307000e20880d070741c1d11110301402403441980c4500c01004580d03a800225103141100312016555184840d501030300d9600311a5200c003a00740307020441580140640103d8035100c0d4401c01541c61603541201244006101d21141c0d1f8041c80140040c0000780003a02c101d00d03003140a8080c542c440e241058201e071030116406c14120003003040000411102d0b0161406106681d02114056240c403603c904040c003d00d4a5441840800c801c45000002d004010000f89203410b80c594800d416030b0b07212001682960400076240d40c00c210300c1401000070a4905400204004c21803600140c0c01480791161400e590583d407244015075030004c2c003002000004490104075803000d480e030018a6140c80707000301d403410f0f000740003401c2c0a01c0001c03c010094400e60440320480c03041407464001003829100280f580d084005010301 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 116563012 1250 116561762 116561773
    0xd1b14090a020304050c10090906091a120304140310090f0203060109020c0303010b0a1b03050408010c0e06030c090117160f0206100513060306050406050709061103121e0403080603 79
    0x10042603a00031240b044e6001001804445030540912510484e54100f01080102130b01c1d000c0b56410700b60240000902c905130001c00c0405030100b03050a201f5200e480f091040d012150b0b13009041401100343c608407070110b07103c074502062100120341072083c14448404882e2030441d01c80b0070070003d240103005041c004c0e0101c0300580e8948102004901c1034810905543d4424001004115030301c0d0020b101c1307010240707025802100c42083d0362281803030060f400c50202d4404102070107100824801d810b0000658075003003090010f11400300d1624400500348004020300000c20003c90b9008582c00312100c0031000d034900040c03a0182c2914505403030041010700060b00d07d0310400c229440041d1050040708440d55840c0d40302c1c5450200182a54007007401440e25890340000408600b5512400d442140100030200c0d9a14050a0040c0f40106c1c5401c00418031401099504080d0000015520390401c2c00825501d245c80700801c1a41c0b03020702d40500300502c0002c0382008109a4400c01d10b5000e60019001c945 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 116564262 1250 116563012 116563021
    0x70b07090303020a0b071101053c010311040b120d022b08070e040207050319080705030a0b0a0308070609020a05060a0f21020c070608060105030f04020d1b1409 70
    0x4540403040e10000d0016404844888081546210600d030001190300b8021440380418004c00d095860842e5032110015034000c03500401c0c40b0800d00807a911518040750101e4245682d002700f6402c006020241951110403016081c503201c2c1c0d440019900b100424402101d45204405640c64440005072001801000d00388070b941b1080d86401d440030740303208000c0d0661001854040b030302114010080e10400042c40b081c81102d40b9980700070003000d40284095656052100000411150482c0c0900d04106000b410492084e602000352078020a461501042c0344110400052a040e03c030340000e4000f05d400203103581004443c0d8015540588203440c802c65841c2d5840c1003100c140918541d0b5004220b2900e048203076580314045100c1d00381c200b80c900c0281c50303502c41090b0040740c00a0702c0d081c600e944100380c2444081d82058100d0790080c42460054038501e000b60050a06400c00381c0002e000385407007c1d000c0c041109400c91450b2041c1100e644c0305011f5a6600380400c00c180ca00712882c06190002d000c03d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 116565512 1250 116564262 116564267
    0x11010203011511100c0210050108030a0e010f031b0504050f0406150c0f1205030108070b030c040b030c0702090a05011719030c0f06060902030a0c1704081e03040503070b07 75
    0x4a040312415203081e0600b0a4260703081d070300035040d205044064014807681395545410382c4140600822241d008080c1e0b0003050359124211101a00901501d40c030a003c409500c50344501c00e141c1c104820b1a02c2071613001c0304c00d03094010780b0800d031080d4a10f000c9924810071a0f40c0c0300001d030003181c004852418490740007100f4042100e849015103a0800300e03421030301d5041c501030764030005043d01c03449265102d160641c40d03c0d0f0810005072856000a080000108440b180c00c00c0704e00080c251820b00b0038034604046240c05200e1041c0c0c8100e180d03441c4080b002400c00385051301a24011500504483c0f40c1e4903001009000511007402800800c5892085850700c10000288062694821031010722800650391806d480d5240c00000842d9400310880815000821602030b0724000c218440d80507849080c690684000c2d100002c5505041104d03c1c480390518805070541e103500070750040d80780b0ba030311981401c2413880310000e88220300c0050b0300001031000300300c2d00000070a0b5840c01101c0c18040c94689031000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 116566762 1250 116565512 116565517
    0x1219030c0f080f0603190b070806090f01090c031407090f06020a150513120203030103030206250e0604091508010518070e1e04060c120203070f0e04090803100303110102 74
    0x1d03000449580008401843e480c18280c1c000070014121480c290b81541c5620100c0304010040f40d0849002e028000129009500d8079040101258020001c1c5800742914015081c1407050710005500c615071030041c14003941c0078513009807201c11400c00501c3c0c9030030050100101807081e10650450080c0014140d440400da907003540394420140e80801d410080802c000d030401030080079420f004014040d00007944d0321443c200d250256005940c5940c51400e020742803220080840000c65130040d16281ea1641029901e80341c8105404c00d01c0b890075a483c0480c441d80100e412404040740f0746044e010500b44a007061508807045c40c4000c3c04266038094594000c501d0203000600f00e81e0200100380004444621005c2c1c2c8415403401404180981a202003054030094405461041d03a400000b488aa80b0240c2c860118100d030a0035440c1d802c2c09140140504035030f41c13100301001840700e02e901150769160414180c3c0750304002c8090301c0307040800d050500e61001c0d10048020134100d50f00307015200c2e018002e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 116568012 1250 116566762 116566787
    0x20d0b06040612050d2a031211071a0f070e0123030a020d0b0a060e130b1905090a09020a050f030f01110a120605030309060a1b05010c0e0303070209181219030c 70
    0x848100e0b1189a540596124941540d074544c19622703000c810740005012406094003a02580315000b0541203910040021034015180b030441c1c056080400603269040b10344080c028400b803a03c4507210269028200d8006200f4040c1e058184000060042111080e00600b4260210500410a01a00d80b00b0072107000070a101e00070204502a50500c10361900300c1c40812480c41e40075020031500c0050000621481d01c1410b00703942801e0b03088040c070042c207006400603071140180300204000c001540000300d076240700f03106051068000f171881c00310f40e40f014410040040050f1009010800121950400b160800d402d02d1000402c00785002c10300d00c10701d018000c112480980554a007182d1079090240c50b60108c1049003e1041c0440301040058048030581209401000001341d41000c9690051503c061641e1080c820b80c400e0090b00090ba441c008100d400500d6101d0b01071382c041244403114100400c14036007400703e88010507203041e1100d021110182d03c0040d658100040c079000c44040d0b03000d40d107669 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 116569262 1250 116568012 116568077
    0x120f030902092a0703050406080603010513021509030307050102040302090f012304020c030a0804030e04060e060607050a0c0909030906031b0c02060c01060308180409020d0b06040612050d 82
    0x5010440e00720031040c403400880f403400041c2c1034400407115061015800260f0440010300f00041c00c119030385e4010f000c2c60f00040124002d2003d81001a203090381062400d6000c0d100d251040d9410308400070744070403121215001f50a490b00d610203400d0990003500548001c0e40240e14100c0014a1408110f084a058622200c07840c144885084900291410103120380c50300300c0d40c00c014000c507001082024000103445943e9082c603d140610380240a031071002080c9001e2828040140402002100b410364009025183c00da140e80701402e0403071905007408000b400e039041e081c4010412076101d070442c55009000341c0b115040d603075032100c0482c11031740b030b4605a400c002d100c689201007480c801c01110117440d000401050400e00c0c005101421103850b58030440d0010350026448a100402001c45640c00d581101d081064a8254012407030401e0701a400030840a0030200042c4c0b41e0b641c640c0011301a10184004070b03820155854401d40d00e100c4605284080350070030304001440317003d524a60036203000d8203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 116570512 1250 116569262 116569279
    0x303030703020c010b06030c07060605100c030503040c030f08030403031b0f0c030905120706030e030702010834050d1a0a1401170705040501120b030a031407020904120f030902 77
    0x4040c1200250000c254a028a540380d0031148420383c0c801c0081c5010340100c009003960340502d0b1030644202c41266001c40d0241d034a0003c5074a5054100745041000c60701420700036503c5c0c2e907a14004c1070552003030b040140000120300d203640038080d1980c06540b10b02d00c6601c041184400d9491450201041140d0250001d03000301105031a0a04c00d0a8108003144681000c0542c9a11400018000245019881d415600c040c204000c4285c2c1405024107078000780028500d002070940008001c00d400400d021502e00000c507050700141c204d2a41c00c1a115000c80c400c545c40c2c0f400e00e0004110742e02103044a0a2681420b44420035941c0b010742c24100c3e0a001031400d98071074070302480c2142100030400e9260502821403081600070400f440064403505083d0369a942d160b0a200c000750a800400d14028881c91501c0000f0030192000194810010742504003c5402000b68079144d0041c828401c0080d04801100c0500007000002e81140720580c00603120701c0d030f07001c50701d81c0c084040301c0500c0006580460701 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 116571762 1250 116570512 116570521
    0xc0a03060f020d0e16061e181a071a1003060b0607050a0c050a0e04030207090b130f0b0108090a030c0b070903020306010b0d060603020a0c24060603020304051506030303 74
    0x180d0140070301090307605015007440240c03000d40003120007034015240c0940214990710759080020303881c040a01ba5a007020765a01ca159500141e650580f120781c0424007841c0030740041c1d0a43c030450980300034078401c0348540c40d84884d40c0c60001c1d07a400c0302c10112450050003d456810801003400c02d44103a400c1c40014903242d10b5900c1e40e1021381051901d2a030413200c1004400c1c04502d0601003000141d01134807010310f50900c3c2800f4042145503030350220441c114841e050000007940480c48004072030b1410804a078100d45000011040c0420219000000d4909202d025101c85190420382c1c54031426280c2307514a40e6140300003038540c1c6031400d00400049024003044001880f0341c0303009800a10500d426080c40d600c9501191500310281c201c5400c4180206500300daa100c0d5016a1000e0200c070b14055092920031200504241024032004001254504040d0310401000190741d9080146a0382071100550350000038009500a80c2e0907100d500414907041c2c1c084280701c08642c0581d40c040c001318910717541c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 116573012 1250 116571762 116571773
    0x3071e0e03100f150305061b032401020c0a060815010905060d050c04152304060e0108090f01060b09040e010606140c0a05030403061406030109051015051201090506090c0a03 76
    0x10034081e10898295207148080c0c42a0001d00d804e000b0710b00c5580101100c1c00e00d0203901003280c4811000c0040c4080c2041044410320101d480d00c1078244000c60900d070b07484103010040c0d08003030f8485501078100881c00400500725601105060054100d101410902903040004451000550044c5900103004000c00c0509c051141d112030361003c021901582469100c400c02d80f00b80c48458911800070380c1582e2011040f141c0300b885a481d0841451300e03a85050301c2c24201070440220340c40214140241040081c50302c40c0c0501c9048904d0703e14200030400c203a11055945029006070521a004601e842200d14584905216182c20703912203488480d00d4982c84121500960b2200007117010501400e210040052802c00c0940040c62180c10702281c20148141303007440c44500100050311a80c10441540d001c20b5020601e041502030811002c228400d007413210501d0b048d1a0341c004e50b04a511420700786110344040d0310803403119104109590080d102d8480842e9140304100720a54802452041000051f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 116574262 1250 116573012 116573021
    0x609071503061206020405100302130504020d0f0603050715050423030f07320a06141201080a0b011a0306040f090227070518131103071e0e0310 63
    0x915071070042074450302e4201c88540310b084501c00320f8126801140c280300a00d00703402c220b00a01d04a160850600b6280f02c680113041a080c03041a00455000071a020400b03003030340040c00040c4045c5c00c00d0241c81d949103084c940e20401e0340309683c040750100c11018407851103881102c080312950807901003001740d08200c041429840c26070180c1d240c42124212040300006000c114010f10342c0030350214145c0311030203603841c5c50403952451151804120050324026507803e150764080e43c285180502d004ca016403d00202c501c605042c142c0844003403800041d0b0500001440e02d0b40d5131081c414048180d07070307038000d907043da00020320456070381d5000380001452401d0513401594070683c5014046400f004d44d40200c5e12050344c60720790000d28064400a0b16003000f4520300c10f5000100c41c5040c619001c00b0400080015908a4000d441251408110001ca8019070440070074080c4145031a0b95905001c800500034030045842c0c00741101e01825909101401a072100560b01d1028024000302d000d420700c41030060 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 116575512 1250 116574262 116574299
    0x30a0c02100e090f060405060607030f12061a0301030210020a05061807091a0f0f0d02010c06020c0316510519050109020a0e120f03030f060103050603060907 69
    0xa40030403802420b0341c90709103480c021904d0b8030300c61402d0304000051000b0780740c1c024901030044104001e95400650702c04400e8269030340314a81415507215454081000d808958402c1400b0071303485072401407100f1080002d5040b00e10841c0d038240310500590050fa1a040c2c0c0705c10152003030304900d00080c00e07140c540085151404145c82600c460715102c0204404441c141c0c0ea80d455480324100c3d00072120b0400f40c1d010449190103c450079841568200010b002c4164440000e0411500480d1102004401d406484190b1540016262604003158401c951422410010fa51400402c0a9004401a50389100c003524000c0ca80e02030058518402280d0281040d640340300f0510b030303002c10303000ca1184203202c1c080c0074504441b005603092140800c814161081a00541d510a10400030080190341101d1000c0001d00250303280c48075045407450481c00d00d840d124000c0c44c00d000010800c2044104081814420102620100210b4a6640078503070b071804200d078001500d900204003404408e8002d2881e0206 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 116576762 1250 116575512 116575517
    0x60703020307021e090f010e13030e0a03060b15030912070201020307021509100528051306030522020306040b06150c0706020601120305040302011d0619020d02030a0c0210 75
    0x3041015070204911013041c9440104008400c5081c004a150003040a03400240d512050f1449505201e01284500005052881c104101e2106403040601a80c00d010300a03070003c1070700340420754904084000d018243d81c1b543c880c1c1c1c5c1c005903040203142d071141a24040c00f0b50b031f0010708428954802c0e0040a52100000ba4103511003400b05c880141d4610b038030588011000c65030f0903100d182c01024010a000c01107442014007400344100d244408034003a0201d0084407805000c0d03c4a0300c024800d43e8180306d591082c1c4d024109508020481c1c03034040e000700d40a920825074a0024044c012030048811281290095254014201040c0030401541c00e0540100c0d00410200041889028021003580850010205a040410200019078052000c680103040c80030341528400d1541d90028146c1c4034900009062011540384255800707007642070401e22620103044566640d101800304250304082c2150b03c40103103c0d0800c00b280740761000c0103030383d520026a1249e0410002690070440075103c1d01110008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 116578012 1250 116576762 116576767
    0x5030f040309173313030c0c0b03040201141c0f1b020606090601210203090c1c0b010603110403060902030c27010609050604150903080d060801051012020607030203 72
    0x4442c5902c00c910120182102c000306404c000001e861011121a00c04444109140c0b013000348100d100c01000a078801d00ea04183c00f4614410f150071b9900c04c560250103072401410807004600c01c0d06420003180114001d0301c0b0108008034800d80030106e44940d90300211482030400844904604a80140403680c203800c0001c00d18086c65514043c522014510343c10041e408481400280d0400c03514903070300804c0c28641810210081500f8031085689000e6000a0560000004070724a00c01d1000d00f400b410024044600c80a890107501d210583e50310b801c0d03c040700d200000117681406486144034283c94003410071f0520345540c43c2c41d401000300c880240c6c0c040c00f681880c8055a5502e1824400f101d900c403502002c240001c0c4882c140246050700b042042c4034030400300348040c0e0f03603550641d0b00320748210602000b42d905003a42140d0b00d003500c3d03000400a00d40498080c02025260f08076009684042c8000c21a50740c0c0c015180e540d55000d40308a030400d54142d80003401504040700106402800b80c01100d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 116579262 1250 116578012 116578019
    0x3042a150903060b0303070803040807030e0a0b03010501020d1106010501030e010f0204120524151c0c1e140114120901090c0504090b0a0b010c02090423070605030f040309 75
    0x50a08450100080c0015442441403041091921a00b00700e20300503402541407000d03641d51010184406400600a041c02290304801c040c4502c0c41c4c10003222000d8000c0180650b21040700c07555410a004144c05030095050b446170840c404d0030f040500000d200d00412140e40b8040064000f4580002403416035500c030b10260040a060780010030040c094802e00f09064446402d04a007000003500c951071100c41d00000000b2140b0450007000d41220502c840003003248013640004d5070b400e2038034a90410766140d241102c1c09001e0300e12422411541c0c031324120301001900343c400900d902c016001c0c00c002c52450701014156548a440c170659080d498000d080e240c800e602c502c014440710225192000360703448481840401a1000b1000020130007640c2c140810034040c0c1e103003418250000c280e01101647c1d0400c4000310380c4224039200140d40c000e8400d8007241858200010a4580d10060458600e0300640001032b140c400500300040303998591b00c450454903041e0542d092040c002d0b0080d02004070480c40030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 116580512 1250 116579262 116579279
    0xe03060f0c0d051611030705030711040609051906060905150d0e061005040f05040201050702040c030209060a050403060608070518090c06040b070c062a14010509070305060a0203042a 80
    0xc07401502444881540c941c02d00c2130040040101009021442e081400004001036001041e40d450239800f5840d840c1240b81030b00424010721581d80200382080c00d040c2840f4003c1d00095022414008603602442a41d850b84801d8420340c1441c8902034100c2d00800108200c0703201e18000d01a03480d19490302144002e25058085e16003542590501c4418900400411403031130a80302d060310880307109105110034a41600084c0250140010190065841d02484100d041c8654116038000e8001002c0c03c0c0c0f1441f810100924a411900003280d00c90b1400401141703078907000036103508440001300700c41c03011980d01c540c0b46844040540410380034820101e1000040d41d54030003400150540d0452300b911200d8a01344407a2900443d0301910a101e004088250702c80c84100040012a8000302320f80c0e104440c9152860b206424201050441c1d40382c081800040d45000c40d03035000300e90051080391020307110035011030100e1100f5a8002c142e10f03002c14210001d03003600c1d00751040100700300c403a0721703000b0703540d05c021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 116581762 1250 116580512 116580521
    0x203040e090106270c020114010605070516060e0f0f030a020d060908030a0c170103020a1205030909091e010506010206160e12060604110412030302072103060e06010e03060f0c0d 78
    0xb00090100c00f42014842180d1038861094401606d200a0044003000080c49801c000180513200404c5000031f8000d09201d0100215010805030742200c806003907a502d002040c000d140c008103403041e12041d02a801c64544000d0b00c82d0792440007005890099041d50802901c102c120b0011078016807901c1e1070380007158010000d1445040c1080000c1020f00d00901e0090205003c00c100440f6410184018809a158004804190303a00d4681c1820324860700d0500385d01d0b5000700d01100380e2040c621030400c00a0310004c03d40305420302144100000d080d031900704a0b0309076001107e44034010382c0440002140741e41d960300c046001e0049800c1a84e06c46281001081c203404800c40440350b9030b402641446001d003450300c504032040c035610250310300741424040c10000d803003046103001e02055000b04598040c0a4800041ea4030005d15203a0810b402d20341690290140501c3c0c0704411804900000007001d55000d401d00c50400c50000300a040350b41e84990943c140084050200a00c11905001210850a06100303 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 116583012 1250 116581762 116581799
    0x60304140f1b040507270801150f0e011a0f070b04050703031d13022a0604031d10081f030506090f010c12020901020307060504110f0609010203040e090106 68
    0x50850366101a80080c0d51a0002d4905809549041d0401c500719500c00035204254200304e005172040300c000300c0d80541c0b82c0d0143d00680380741c0d440c04086801c110f00351204407048482080c02c2d1305103560b44603e0602d45010901c00e65541504c8007030710096185850300104044507080ea20f20741410180d88415041010880c0d003154181c0c0031080500600da0400c11001311240216425444080b010020072010707007810f040e164250340c001c2030640842d480711002e01c4c080760700e401c240310101111003405036941400707840683c0490300705240000880b40f99032084d511000054070b540082d124418085030084002401c1c2d241c0e0300c5240305030920040040e14120019170041000b0846401d00b440c0e05410001d10a8200e0740c90f80c541407001c02d4403900001c442203e400000b1005888554105c0140c0c00c41c410828020655460641000304005407141d455440180a4512a800502200a00ca1940b06040d0354030b016a2040c8002c00808102c0d00310030f80c0c040c410000102e94290344941b503050701c030b01020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 116584262 1250 116583012 116583043
    0x3040b0d0504110f01020a0312090203060403020a1b0b0a05090f12010920010f0c170310171f1503060903030618090c03030507031e050c07080f06010506030414 70
    0x4090005000804182c8403c0c1401114410060985000080d50b038030340c0c0c00d000401b4000405e4a030b0100e0291366210411054014098030103a00e010b00d8000e440d1540341c80100da2201002c4502c0c04030302d0305002003400781d40e65151000e02e820b40c425425100340d0000c406441e4042d81c0103440c14003540364004c4041c040d103116400407841182500d00740740c030b914084000b51410800c0e20b0644e09103a9101c2e4100380d80c031149052098065000d802c01c61344000c10762050408425000003800400b10401540104465040b00541c2003c10020421a240d40000346030001404441c6901007046011340c0c071100201804c0e06480103c0c030396a58030305054445002098012030707914401082803404c0703240e0303442c10610303500802c0140c60000d81d00c4143d008010300002c3c040100c086030b400100760041514040d5603c000302d2254a0400015000303105c1c1d4000c10074a07000740a0404000750840001507060340605490015081707582c00c01d0305200c860f8100800a483c0c81c16503140850b540d0105000030b03510140081e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 116585512 1250 116584262 116584271
    0x30403052d040f1409012105031903050f04030f120e0703110103050c0c10020304110d0c06090504090803010909060b06031e1b12060301060504060b1905040b030c0a0203040b0d 77
    0x20512081000b0181c2c01080d104103490740300c13481a510f8800b92030560702884681c14480c1015070003a19001c1504500a141d0b100001e100d05906a008141c02240d4030a071340c09000b1903642044000301b985040d28001c1c00314201c402075812550003580100d40c5818200000101c15100c9050f880c42d0841607402501e461402ca00c24010700d592600030541e1110074a100c3c0c83c6082c4680c60b45982d140903203417045c0d001a5001c0041010094420b4601a403d00014920040160785003000b002c40f0416100382004100311010004850a00c0d00400208542180485085a2170701504502400b04000115078803a0b07100c03a290120360b99103020314050501d01c01030104101402c040d550042c44058201117003410010607650885140e24100c075110b4031b910000940949490021070701400d0540c101c0303580a0300f40340c5c003c103200007000d018004030000e81c4000b1071120038944090351144180e00071460040d0080000035000030541004100300f0b522441101c0c6800d0f65042654410340048020400882e200c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 116586762 1250 116585512 116585519
    0x303050a0e1e1501080a06091506090506010306090c051e0c030a08070f050f090d020d05060c09041a010c02091906090905010b0a1419080a03080402010f08060105030403052d04 77
    0x4001190181114168060701541005c5006544002c0900d0042032203407031b082002d0030040641c050960b054a20107007408141e8841c03101d0009400300701c80e4640080e20744580080c220501c0e00400d0001d100a403030303043c40c0c6a422030101003039540300c03100000b003023004100c15801810100010821000d041d90340c00c00600301410010440040c00083c503041100600c0740c01140c03044032080710320500f0308640c5e047c1100018804510303410380d1035070040c00302d000f045d0404c40842441d200500341200111000c000442201070040c240042c000d120900040312541c0c01401400c20b2060190000401e0042602032518202880c064030602d4000b0050a41c80d40cad0080d04010007401482901c0000300c6440a11030300b0000b12040d481404c1d032500e44182c0001000c10344003010420814040c110721410346081012a04028001c0d050a40b01280020024054101c003240308503012401410169100351458445031411540e60300500b0b24801c0505502508010078040403110320320310114060030588403440d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 116588012 1250 116586762 116586823
    0xb241e0c07051f050a0e010c02030f030d0c08010806010303030b010c060f0603031715010f09030b04050115270504060e160512010b060904020708040f060503060405160c0303050a0e 79
    0x10001d1112094070f5114540c21800c0c0d4020040d03031003121a900d4484907175540c02c80102c80040c0a1480139415004089200380001c41c00310080000005041051000c074100b2802240c0c204400d00c5014042c0d00401d0040c0000b81c802c0d080607650b8401454070308003c0300a80c95203401c51340e0b454080060281c0e1400704004040d000b240b66081c62000c0300b242d21491904840507103810010102180c10402c04a1012800c640103c6681d4003a5411801c003030305610302850114001c00e6601c106a00b040304032071000070207105c0c002c0c2034601005015040301e61044170b01c00f460040c0c103002d04200c42081c3c8501da248030b12601004140c60385210725015400c0ca611702001d10043c0c2416004142031030b4107004140002d0785800040710102e013801d43d001603961865003040e07a61402680c129201c5400b5580300000d40c01d40c04006180200c508503001c21054640c3c0c0d906000c0205050b00d20408204954034400109009502c1030350f01880a00c80031880c6d00d0301c41d100310304100c882c1608040480011014010900 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 116589262 1250 116588012 116588029
    0xb0d0b030c0f0310110f040603020301090b04020c0d05030c040302061216020106260a05070b070309140108060402160b090307030909050106081b09030d050d0b241e0c0705 75
    0x26015642c090070014918082500c8030a80303064414203980318420240d4a0010104546009150084841e00e031615040001c000c0c0d84281301e1000503905011001105151520840310714074400c40050403038405049041d030380e44d08010107001c02c40c2001d010010144c0c035510020040c02c2c491285403280340ca856404003071102c2c40c3c1e0500c1000c581c5085014001e4420b61a0a48000e81e281c0c02940040c1e08500d144c1803400d00704101c010804d0185c04070029101c00c2c60405400c0b01c6d84241c80722000d142c1c50b0620020320700810921140000d0804010640740e0506a0007482c00c24241c5260404040a54442c04400d1009403004030250b880000d116051650110586000c0d000d6882c1c140316951400c00003c20026024200c1200059840000f01c0b000706c9010031150365881c06030558440504210001c0c0c160b0b0001c1064200140c1000140c0c1282e28001452131310310f420841c5c40420202d01c0081c0803034a500100302d100f101c2c0c1103000d0524005000034000e0080910b0010050800500700b006010302e00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 116590512 1250 116589262 116589283
    0xc010c08070206100312030e0c0604090902090f04050619091703100f030b0103080a2601151806030b060c01090b0402030c0102070b030a05040228060f020703020102030d020309070b0d0b03 82
    0xc5490f8400384005480c000c0106001701b900d18012644031130707209065090590814110b50322101c0010005003001094020a441c28000c4800d0b551030364500c8130701003031144103d40041850308a00b000418921810303443d01e001c0e82e0344410001c0c0b800c90075620392181042c92032055450030b40c04401c220701e42e00c41e806444017030709001c1c02000146103150750704450040107010003001403501080c68090b40c3d00c9085540d0040c1d1004403112061b0204c00080c003845c01080c06510b1036440701d40781f003032400380c01108a903854030545844075080f1460309204a004042c424240d0760301507800c010842050300c09000710716020340a800e80000d0b5040034410186002c01721080300d4155040030320100842101d600680754042c4000e0400b003280e6030350348000b1383c4200b0b100d1410340f6244000303c1300100c000c42c546128800e41c0c56030344900202c400700719410b9036644004c0c131001b401a8400c0040400e2448150042d6401c084802c2c100d50006840301e03107a03031550704095074002040b9601e44100c0c4985c6010040e48000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 116591762 1250 116590512 116590531
    0xc080f0c16050f060906160c0306090219150c050718020c07090c0516050a0807050f0f1b040f02040f06050a02060c1201090e0a02031009060b030f031e0c010c08070206 73
    0x10070f0341281c040340107401a070b4038441c0b0074000491441c6030386c00c0070014051569884103034051615100c0c50040d00415400c00145c0c09a201203080f40c000c8114200360720143c1d2040c6c00a2110100707420411503550104140c11a81d034002c406000950030740c0c1d040c469907400452180507031140c4202c54143d20b80b03a0140d1251000500b0500441c1c0440d030400c00300c8050940c5981c0c000c0e6016035070b0800381c0c0b4241480324000d1802e00e0009188052040103c1c43c8041002900c044e10203071480003443d079513556440381d180032038802081201c00182c03501d0b45c000d074604203c401015040650311810807000c41c2d07265200d40045071001441e240015414400b01d80c1c40041010081d0410004880490201c00b05005e51041155070392444410010200504084280c2c001d040340d80c80014010800301500311507100701c880504001002c2d0280c0f5020030740c00912412b0f20000c50410381e4146105818600302c100056002c01d08010750302c080c401c28040e600c140e080d140c07103440490a2031440245401d400400d010907 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 116593012 1250 116591762 116591779
    0x8030108010921050306122a01080a0504020312070c05040501120b010f0b070204020c01020d09031e08010b07020d030c08040e0f06030105041a060a0513050105030c100509010c080f0c1605 82
    0x305690801c00b038942000041d91f81208070031514840915107901e01c0c80441c58410000901100d103481c0c89422241d00340282e13a001041e0b180d2240400c1a03030425200294980c000581100082d000003000c0d0031054081c420b03c0c1816641e4002082c1115000e802004c0d01e00032070b0f14200c041c060040042801000b8030003003820b4480c54035103614924016480028440c940001e4490000c0100350144c6406206601c0e0412091020749405046120040d080890415448001007840c50003451880d0489501460041c60059540e081101240042c0350031401d10071025428000310f483c00024101810a811048503181081c11114080d118010441ea219070306102c100000612800703204c0c002c1c4d081030300ca9801591100c0340082c3c1e00e042d00b500800c1e00705400100160b0000d20a4000328120ba000b6800d85549071301c29400e00540c1c00030b0f02100400321b202000400b0b915440b40c0c1410901da40103150503410a1860901e09030703140c5c07005c9401c160300e40c861a1103403200c24613004100024881202c0120 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 116594262 1250 116593012 116593073
    0x7060305090d0804110a0905071206090e030d0213080303090a030e10020c01080a020d090510050a02070201080f0402060415180608101e030c060203070302010c03050408180d080301080109 82
    0x3c10b401c2c00107100a03d00c07640e1845041443e2900c1282c0790280001541c240070034608070034010400c0c4045007244000d141840300000c0d54103118401c15504100c0e8001847c03500c41c0034244800654071079141d146400b0a24100080c031030000340055402105118060141041207003401815041e00d1b1405078421050704a0036445141c0014100302e40803020b003011242d82e55603d00c80c1009000b02c44568154038180b152040401c1004207903885042c0e24840100000e403100b01d424800c9005129009001c52514804507005000040b02150b1140c80181050b181a031590b02100558140d0814000860f03445c103d1108021110100580600441e160100041c540014942c040368241e104003410049810303504440d59021407a000080e640003c6400e007040d5403490000d5903940004410381c010352130305142e00364242c405d00456004541101e149420301400340c00706100c9840388100d0a6100048034581800100000050340c02040d6800001412139901e00341b805003500040301070307000d0048690410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 116595512 1250 116594262 116594267
    0x60e01060b0904180b0c0717090d021909110405120a08090d050a12020304060f08010f090b18041103010e030c0d08040503070c030c260601031502040b0c07060305090d 73
    0x110b0824008803004201d44003800c20441c1440c10000001d080356140d1010440745060b80c030020102d25110b034071780389002c0c51184c241c000f0300e000f01882d0702d0b4044401b141c0c80002d450810592403021000c018141160747d501d44c46001142d48140120518041c042410821403800c0c12000402c106a035001d40441c001641e40c00c01ca82c450b14803540c0c407440303600c8102d2003407100410005030030982c0005030900720307030328014080d5890700a03120340c03030004d650b00b0502480d8902c1040002e040301c0d100400400d14504140d500300c0a013900104640c0c00100d011960301140701214800307030186000c1e5110800c1007032000c0905003598049980f04030f440d4400c0240c0e140640c03000036440e441510500d07080c400b40d15549086401e5128064015210450080e00841840785031218142121280e054500c40644058140984408111241c2c041504410010000314050784510031030014000c000501e801d0f100d500e85c00e00d0f600031028000d050340c1700c02c8080c06916010700c90760f508280030600900040d000400700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 116596762 1250 116595512 116595517
    0xc0e0d02030604020402031f08060a0e07080a032102030403090302030f0a110904051e15060913110102100207061e020708030c0d110408010c021501060203090d02060d020a0c060e01060b 81
    0xa000305c0d400400200c1000740312008c052030004117201d81250341d594036040703943d6040548100c1c2902d85031008a178910040012000215001d03403001d411511002e4400741c1c2c200c81c01040902c0c40e210036595110000c80c0340e00c011481036110707844401c0c019096005051030300425000b40e01295202c0d086810205201900d0845521011544821180e80d0b0b0710700702d402c04000c6008421501d15001070701080314000b0603500e18141000003d59140da85000400c6081c0c00250340301440c80107808502c00100b08200000101e841041c01110984046c5078201c0d800c13a444510107440c150359400c1c02c00c1c203461000b1103000f0040c4000a0a604002c4282c031002154800505403070030490300000c0842032405907800520000384501d8049494581d1880050301901110340d83c00d00500030507172500701c5090450030039816106d9550040d400c094450040c414102c0344c150040e81c2c015006c0c00040403070303080b078002444540705594810000101c90325103070040e549010034a20699040003014404059044107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 116598012 1250 116596762 116596771
    0x1060909090f050303010e160536130e010b0409080a1d06030408030108060601080f060f3616120f0e070303050405010e040603050d051315030c0e0d020306 68
    0x1400a006071451602c1110040410b800034028080400002a030f01010200180b03d07000036140380d01c200d00140c404440522914114412460211082c2045900d01c0c2c110b4144542c100754a6094032038100300000c084c68141486c030000c1a442e04241d005000c400e005200b42c5071020341301840382211690320389c0e826000726000c0808000d084106a580b40c0700031038a418100002404607543c0381803034203180101d07520034003a880380c900ca040003142095114101447c4034881e107500d80d801c50b032260001c00c801300c104290742941c046c0c510100d01da50b4400c004200705d0742c2e2480a01078001025215001403464000134103004c1400501940490107a402080c454401c4400d03207000070391341040500881c001d107510001c28156215044000c010540c102e00203106903802600c6142c10f0b080403030100825280030b40401000e50b00306030900b98403e405000139000e0203007001e032a20311290300d41142040390745018603a140002e80320445965007a80082000203030040030f42d5103400141c49600400d503588005407 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 116599262 1250 116598012 116598029
    0x41505030a0b1b03090d090b0a0905041503080c07090e0a15050606160b0106030f1806020901050f0c010c090906060f0f050c0a06050114030a0c0605070201030605120307030207060305010609 83
    0x800100c000540191114403d07640305485500d07404c26542059a401c009103070640442c800c1900840c001000c07605880c6e0818a943c0c5001d1002e080c0014400506030206255041000032140400042c3d006805880d074030032840e00030040580f070022104240d4205420aa40c035400100c50030012480100019514010086000c103a5842d07800216a1501c15218003000c040c40381040e000c10040e201038054103d80720350b6004c1c48030b07030403410001c811208280415048254620700040000301c80d90054481c684050504908100302d0b20810341a9074014046402965550344014041a82044160000d001801c008012950400c44081c180054000b400b0042c0202d10810040c410312038021204040000c1c0280c4100c1c207460301d0007001800081c0a03108182c000b0505500c00740c1800910300c1110780d0066941d511207881c000094a203980240030580c1019110000841d144e15600c03a070700c9414010b60000c41da81d80050800906210903504040c08040c00c0c000104907180d0302441407070680d00000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 116600512 1250 116599262 116599283
    0x12050304030e0a030303020a0809070803041404090c0b030a05070c0f02010e13152309060d03050906030709030b06010f091716080105161103030414010f0509010506041505030a 77
    0x1410290741c035007580c4020a50040d0600001320400d68941c02134012030403140c413012417903100d40c0403941c0c45502c0c0c0d00a0804952051008200c00d260040740d00424880140c000148142140ca9441b50301260383c000001000000003800f91041a500c1001e501c102246041e1151501035a10000100d83c4a10b0190411000c4690754a40f669000208041c6040c049401c0058400c114482d50b02c7e00760300c0c4540c04081c3c10b2100d0305507042d141d00d00d9440181c0c1004020003195504c6400b00440718035500010740c00c00500340544100b40e20344d20002c5004000f41d441d1182d01500d14581401d000c9002010b090400c000c01d0203100b403a07070704000218180c5407102226624210700c0c502861405418010305449042a003030002103e500651105005900300d403842d40c01c0c00440c02080d0380180d64514a81c00301d03030017000001c01142020425400301031201d4000724500b00080d801000344c540540e142c4006035075070014081241b50034030403140c0400a40b144078440515020002e0380324860071130b01502c6000d42 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 116601762 1250 116600512 116600521
    0xb0a020318010c0f170105060316090b07030201140106180504050a14042a030510050c090301050a060f1502070312020c030607020c03070b030c160203010e011107020406050d120503 79
    0x422444000311601c0300002c00004440c40c5000b4502d0380540801000b0440c8a80303030050b80100485000c0c181c03400a0300e11403858503102d1200024010b45030540b0204401c2c60004104d510b03c0e08010300d9440d000e81c1c00864030383c040c0740103441e8401d81a80b1041c2805000040c40815084200103042202d9040340d0004660740d48445c1c0d140940354018408481201ca40c040004201440c0f1072060071200702100340c800c0c000c100000b05540030103404060042e6001107501404540c41d074004036131014601d940542000078150129094401c1960f0b0428820344540040c4111940080036000030f1400c90800c0c841c80165500294440c0c403c1d001c0a440c140b546140c2010460003001440074000019040740c507540340c4840c000b9255801400700d24824050510000b8003426404281ca000b903880650300c1e4078002400c400c41a80e0145804203d80554880e0b628407010a000e04c41c84542028035000c60382d45210340d01c100811903580d50803003480b412882480002043c141c8020ba21540d0180c1849603483d01c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 116603012 1250 116601762 116601781
    0x403020705040608010509011b0c0b060d0b04080d0c02010605011215030c0807031a01061d0103330806070c0312060801020d020706050a0b09061509060c0307020a0902070b0a0203 78
    0x100d600701a07041402c00c0310004071001d0542c00315100e114000001c20010ba003510124900440344a01580003c104058000201d9880001142c020100810303020020159070b458242c000d40c112002c0c0c40c0c01c6402300e001c06652040e40948030180c1a41e1000700304141c18100041d141c103010b2020b01007401d070b0326109502446103070460b610246400c80d10464401d65640920b035907178180c50004072010034a19807044001000c403032165058070740d5911414420500b0360102c100d040c01c500400c0381010b0301c58842c20349410180041c43c803912070503002c5042d03003600382400e002068036aa021519540c0140c08000f0500e6005040170381e20b56142c41c00398900b90b88109604090002c07604803c6040d48002580051400c0607801480d00900c036a03001d1042d0b540daa558041110750803036410307811503041d000040e02c1b40303022180e850b000741c1d902c24902e081032505004a8055080403100030a158000100c1c44194905041480020200c142081d450108141d0f27400600140c00303400a101e003500400840d62240 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 116604262 1250 116603012 116603023
    0x9030703020d0b01031b0311090c0909010306200309060703091713060e060702090f18010509060106020f0607020a061a03190605070e091512030406050d06060305130b040302 76
    0x54000300b14a00b80402400d0000c01d0440a201c01ca0702d82c1003017044800f924000c55031210481e9001803240c1800a515014011800320060400820103000c100c000300030341d90616424040c6009040c00103212511804500d1840010700360b0504003034092082003481e44001407070701d6210b06c440c0b8001ca08409285040071041200481a034415440440e02201d44030750118100b0489800703956010032891140140320081c07050f000080c0d0044090301c001004610651843c0717070001c40603a59a0307580c0b0000f085843c01c68500f40e0b019191504180c1c01004056810800341418258490280466041c8503c0181d9940740d520750007810581c561060307554045884014204109010782541c500c2140900d410716130500b40207045800358502400f080004e4800c5e81d00e180a22005400c0c8886501d540201402c84401c0101065101046807400c0303250040500141005102546856894020510104c02555400d030003071000c141c9002d00700074410342201d1884d409550404080c1c4c10903211400c00300c1c00c09 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 116605512 1250 116604262 116604269
    0x90302030a03020114060409080a0315080f0c030f010c09060e06120f070f03020c03040b030907030812042a031b0e0c04030c080c01200102190e03010509120a05090307 73
    0x500400310900d00b8903406400044001107178181110013951100200b20407140e03212800741c2007400a10040080130302a0303104050f80140d0f9805080110394402026150400300b07944600d8640288549034190304040220303034825507034880284640302160200070310303003c44e5114950400081e0b004100054550804403014140f80d683c494020b450118610716400328240c60705000030700301c0844408a18401d10a441d84035047d01d0156240900c0c10303002d850300741c01c0584041d40e0717805103050001c0040c006070002c150a8451601104c40c0d0702d05800c01d1903a80011001c11000d500c40200c041d40c60040102070342007078030f074003441c03221001025680c050040c011030b411454541e8501020311410204840207041201c1c0300f4141d800e05a0f4549040716240d082c3d4100b8180401c0351000004c0e500380543c10410460340c2240f000505111001d4914607204079054a010080780004007101c4030703410280a4541d00810001c000c18200c0200c0303404081502c10340054030104040803802c400b1950b814050800107 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 116606762 1250 116605512 116605519
    0x303220f031e1a0103210f020d210204060e09010806010b04030f030e0915030d021605010c031106100312030903020604080a1106090d030501080703082502041b08130b0412090302 78
    0x5945e120b00d00142100c400c11201e40241c517502000c040301320b1003401b0100004070700d540070f07041c035603c04c03401900d1001c1801c01aa412880f0010100807161951010380002d160b240c0d12201114100c0d01409050382d01a040320103550022001448580b00c148200c604590f44024080e80440550804950042da00145558004c040009024041d50103070201d0a160700110251905c0702d0140380141d0303a45040c02180801c0780b41d0b030b0314208040d41c041c46642091500030304000013184100c000b0942082c004440602508102101c14018011482490019030800307080400c030312407658901030750310b01d0300802c010b02c2d001c000a01100e401e0301c01d50145500d02030031000c1392810300300004a55261156039002c100040d04d810000200c40000152400807a03400c1602203280102149a40800310b800c0b480034130702205100325400060b1241e01c203034001180c140d110034202c1084808000c009000c081d14025103005a050050041201c0484090304150311045901c03205401c0041914800029030000e0360 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 116608012 1250 116606762 116606813
    0x1e090f03100501080c03010b09010b07051e060901060605040e1305160303050702030d180b130510030b0301050a020a140d0905061305060105011407060f0b0303220f031e 74
    0xc1c01a86504070302d0688000b0001d5607000d0a4401c180b50803500c11404186c5c1c00101d04004205101e42c0130700414001b405071301500c0705030010380064014165030281812042d400b54041010000e420b03c1a03802410261030414074062502003005803117a0045c0c600c18081400c0c041903020884100098801003001851000d203965036401c0c081c2c03854122400c1640640660041e980141c0d2290700381c2c034002002d040000030054100700c00d000350364000030400c6804500c5100040b481d65680b00380980d6094850303401103a0b8a404605140c00c0d540050014028140140012480284c00c07500090500040710200e41e00c0e54501103208019024030701003d00355010785014803510f02151031801840d58003c504480d440c2c0da84000441d0b1801b0240c0b511441c80006111603000500c0d96000b00080041c2d1601c081545004400068115448100915002c0214007010041d000100038150300034403040d040300e1001803a5403503044d610740ea0704144c0040307d6922040c02c010007180300300b4001964044d400456 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 116609262 1250 116608012 116608033
    0x121115070c06050f0103020102030406120e060c07120905130e0106030c0605120c0301150c020d0510050709050f030c090714030c03010e0606160321050a0b040509031e090f03 76
    0x1c01d408050003003500d0040c00c080025100010024041c2d040380d030f040c0d0045213400d2906404a8044141503010440f040d02c0341d144600304201040402d001e15002c100c41965103059107020505642866040402d01c809030808008550391405d075814000080c0b200840c0110400c8040385c01064150030081c05940070070404110700794818040c0c5009052415010078640742c0c200c181c5818042485040d8140c18424003020301c0c40d1140c003108608920140441650341c40e580c0d0303800c6c00c00729070210380500349569001304002e00f42e2000300c0308000d20080d603c42d401900c0a00200b5121088075400e240604008408902042e22030880300c0d10f0150003c26980c0c807402d1161030001590b10a00c03806212000b154007284503450580101d42040d0608a4420a19032140c0e03010b68030402c0c8016250880c0980d003c10300c0d100304a42c000e540c85103150303000004004640d40204411543d000e0925459a8014400c01070307000d1207030318841c0625410051442d1282a08030006854a801c60300c1d05415005104505 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 116610512 1250 116609262 116609267
    0x822050610080c0604031502090a0503060a0b0102190b0f04030e0306040812010e010e0402090408091302030604060602030405012a120203030402010207051c030e04020702030a0506070f03020712111507 88
    0x300030740b60300b2010b64008031040401c015403405140009882c8400000daa002c48a040364002d064008014207032112341e40c2e0310b0f0002820100121884a501503ca020180c041e44e414000950120040d060201102313100c0c0c1c80e20036595200030000b06070a0300c484045002d05014910003072105100400b00d8036546000e1611000e40d4000c0078141300303054a06400814920f5500194030305a4210307440f80709156840e038003041280c1001510940788d42c14108604174041d1105c0840942c500d080b0080580d41c0d04150b07040c002102c0c5d140d0b02440c1150000d20043c022680c2c050740741540d64507a002c4808484014800c0175003140c0c100c4000808020701405003181c096004000346229070300036000d6400d5283d4840a200c85030344a080740c24007448401d8030100c00a401900011007030640a000141008041ea0110b1300d08068a20155110b43c4000200a4041d60180341a1248211031074250b0a05003281d171601805000c001800080c0016079007000034101c1700300315100c1e4288181c40140060308086001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 116611762 1250 116610512 116610541
    0x40308071e080a0f08060f0418060c05090a09021602060717073f052505030909070f0206041106090a0905100506040e010b090a030602070605010e060102010c08220506 73
    0x440403940c81512541c02e03a0062090317502c200401340c032282000c2020b4080000500413080080d0b9083c408600d00008034580e8442c20842c0411911407075520b10840080007100702050b1b1107030a00a004012051050b414242c100d100107505440361910b408040c6000c04240c40c0d144000c403a40540850b04074140f001c58100014070940300c0a59400440f06150002900c41101c40c81d8055a05c0c1d10342d03044540d500c41d000401d00714022130f00301000b070f12501000b02004080100140d540d640701088420503803414034402c5400100e9414044841c40c84880041e4507048001c02c09855001c0e80d14441543d601c49004070f03500004001c0c400702140e07860b038070807034010038084d92503601305115910086002d0414404031015503542d6034005105a10300304038140309074007507045035402c0602c80c000040061010300141031064403400020890390f040c402d241d0242d110040c03105046a041188420705d00d03410050f8627402c61700900d80c003618507400002010201d100d440c0010180d1040030108404105103101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 116613012 1250 116611762 116611777
    0x90807030e10020c130b130603050111030411041109060a030c080108191205220e0a02160b0903091201060311040c120c090902030703050601110303010803040308071e08 74
    0x9500c00c40c120841c06001d4090500c10111015901000c10b40410303140983e03148888500c3c0e000c0c007103243e211020224000c40c041e881d40003620394440d4028020080e082c0614803095084403649421403401c0d848982c1342020304100c581c0501d80d5001440700c021103071350031150502c0c0c0c060000b941e2071050b40b500a0040c11812501e02c0024074010020034412008110340c550f001d03001d04c0d207030318814440d220703100d085c1c01840600060010403c0a62520224000c1d2400c44404080340e480c2d40d24075103c08000700703200c001c041c40c440c28030400c266074003003000e043d100720b5030758004000580c03c0d0b6507922810f00e5880b441c4400d56101c2c500080034503000c1700540100c01664420448031400071542c20910090725002c081c0030003c0f5895a43c0e8504001003035010704901203a6140048545507140301d0801243d000707071078280c0000c1d00c980c01c00110f940c01185485911082c140190300e1580340240e200d8507030013140030040c007000780001c0e04814800d810790301d03558503030711610108441840c03840c00bc005544220b9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 116614262 1250 116613012 116613017
    0x90112060324111206120f060f0705090d260f090111010905030301051207050a14010e0d0305030a020a0c020405010e1b030f010501050c0a0b010b180405010311150d09080703 76
    0x40302c50007081041d0141c0d100c0614020405410000750b8a940601c0c281d004041036084099a490145001020400c003964210f0120190400d410602d003e9002c2d000010118030500c00100040324581c0c6900003008502d0b034000d0b81030124513407100400c56510440399158130b00b0200203d2800c0d103004003480140a011000d8861401e00194000c040d4281c070140b40c00544150414001044181004d0301e08403090498807007601c80042c0c40701d00080312034131240c205240c903e0a5a500710341d2541c0042d5024142030080f10744900e90402a40c2c02801880010702c02903680350049040002c650003154840d041950080c1b0074400c668680301c8960302983c0c1124a1914204400d13440c0c02e0204010007100c2c041c00e540120403110360308000043d9003a42c40701d0100405445041103040105600d9440039020b0044541e105543c0d040f00c180741c4180307a185c62200c0f40709910788001000014901420004549001d403003920301003541003c100340c20b0192941020741942002c0702d42080262080083c407a041c802d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 116615512 1250 116614262 116614313
    0x405040f021c150905061f090902070c0317120c0c030d020403081e03040f1707120206010e0c25020a031a010303140307050711211f0b0907050901120603 67
    0x104052000e03140c050702e91540145600307c800740030109844241040c0041c03403c1c0441c00d541e03100d583c54101c0e405004203840d095000c090034010000c040c0c80018400288a418908110466000220306c4002070311104041100150300042c644003802500c00c10114a501152182d07501d042403440c03940b0514400004415005c030391002300481c1011b84c1d00894121010040c005110750303442d00d100e41c8520354002244000e201020004440f01c08082e244145607024092a500d000c0000d09075500107040064012002e129002401c0d051400d458450300c00c1440381d12000741c0c0390000c20404002d940002d007840c0c01258004900b001c80c1c0412a040704d100e95101c2c0f1510380c0000207107059010684d032150000340c0400030440400c03e03140071488103820042c075104005c0c806200c0f409201980e402c0701d5209401101400d1000d81159100040003403101c603050180e50345a00000f00070a00040070701c014040089000d409030303441010302c045030081c48441040740300d0312801c00c400401d48c00007482000c40e915 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 116616762 1250 116615512 116615519
    0x60108030415030c02030d0e1e0c030307110f06040b0c0d02070b04060c060b0910140405060a03080319020310030213060e0a0e0309060a08090715050405040f021c15 72
    0xc0781c084484150003100744001060040700a40401c186003c11840140111040c1001c1881404010745d1902c000708003c006140030560b03446160042c90301290464a110f500d5524003008964006a116858070f40c580b00341d10004803111100a0400d402081c0440e01283c10031001c0000c0c1000d111110803114800d89401c4203d9590b0500e01504214030002e03c02044200d0041c801e86100a10600e008140a0b201c640450041c10080f1480d82c0180c3c58210104000c004001c5140c0d8407442c1500d0500a51402001140d2011920300c0000c2c049800000007691052528401c0c0c40214103101c070a6561b404c0c01a240440d01c01d460200f81e1060b101c0c00f000c0300c415545480746804a822240a030340da95078414511400401ca1440f400791940000c102d11595540d449008040c840070544403001c241c00d0561405140801d0354204c1070385520001c00040056402100f610111803080f0b90101e040c0c3c8100f01d2000c040d00641c00750703040d116010b220341140c0d94bc15403c484040041100304448084c2d9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 116618012 1250 116616762 116616779
    0x2d010908070812160f081309090503040510022a0f06070b0601030203060103090503031e0115020304050d0204090204091103010c0f08010504090305070203030406030203010914012409081e0601 84
    0x2128410304896600180b4007028800100f00070388003070360070203100c014802010313115030713202699040040b036075010001010720101410001c203802904031071000b0055204031f5a0307815520701ca40d01480788103220700d04032241d06074420014450a8202c040d12000e10103000d038441220704c040021183d116440c03030b040c3c1c207800b0300b003040c20b88fc079441e000500407255854020040d8002d52014005904054840e0411008188100010340c0910b011074580e4849154200118120307000c103030807606542c0c4800c0d900e101c1d81603002082d103041d20000c40c0e104240112a01c0024000c023661600250043c0c10140401e0900660411003242c14000342c0081c0266614240c00705e900b00034968034400801c00305070040c041070a255201c2101a80720b418840d241c000d060b000607241d0b40155001c040000c3e0004014000514140038000038044a2122141c85504088040150342c4260700b00180340f0303103011580c01d01c05200d80d000300010010a01951170040981c4d13420105c4100c0e070a160211441010000240c060 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 116619262 1250 116618012 116618023
    0x31a06031506031902120102040311190807030605060616080a1e09030b0c0f03010e190b090c0705070312020d03060806010b161103100c030b0f0105182d010908 70
    0x1c00038054110400300741000070424001354426a044940300a4032003059030300344000e0007e980107071070044060865a042180701c019512110b03420341c3d020030040007202e074001a0030065035808000412665152030120380700d400380d09405002000001a1102404607000060504902c540c0e9036a81c0503a420021030304c2140418404000941c48410801c04908880c1e41c0742c1c0c0244010104c20b181c01007030404103004d50800e80065070010350382c809202144910f0300054036020015902807181d0284100000c4142000420b40d00d40d0400002d220401c1100030300280c0d001c3c5600c06680c000504030500300070343c0c0c1d024044186002c80d00c0e004000c5000b03c0001100c5049806005505181401060b0100c849212640c1d0403104c00c16696021000344e036091203082d0b44540c4140c0c0001d2440e190390001400d0307844801881d0301440440b40c2c07440190740e11100f16200581c0382680d040d0700703e480e203001c03d0351501c14003030700d22800303051560310815000050b00900000400343d9034803001c98cc99003c840c0c1c484 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 116620512 1250 116619262 116619271
    0x501050603070f02030d060e0601080a0501030305090d03030e0f10060504090c0501030b030f070e1b13141305040615051203090d06090209090a0c2c0907031a060315 72
    0xc5001c1c40001c0445110706100c2e21200703103510540341000701440300c410a66003241c01196000c6102c1c0d04014180d68412506940801d2062051200d54074685002d8514464036818601071004c2d00028010305001e6005940305181d81c404070b0381c0c0d144e003010b00c0f1a20f6601107070031b1f890428285080001c49190a0003216111138001c5910300d0214035000c0150001e0040d4180c49070980280010b82c9116901480707098000c20a28280045d180342403c0c0d4040540340022030f40131042d030103000c036448140446040f50103a480721030130718580c4c402c2c020002c0c1440d40e8481d0a244000e0030001000300300401034108031040300c0701030842840740b9142c00401560302180d06410070180d00a2142d60030f01d161001410050a009400014581001e6000b04000d0315045581e034610b0381c031080d44402004509500c10700103204030300780d4000010690070740521400151140d400e900060401091101c1d001380410700c01994003c19050354251000c01540c010102194968468000c0c01740e00f0010503100500030703116 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 116621762 1250 116620512 116620519
    0x1020a0504210f030e03010f1a12030409020c03090a090c0813060605090103030c0b1f330906080a0b0f060c010b0907050c0f0a0b1b070602040605030601020c0103050105 74
    0x905007081c240461082c1108401041e00020482c69004640d800301c1254815000390744032010904141c0901d402d584902c0801c10015280c5024091403500400d1040000c02003166181c07c1c20780030762584c3c2e103507005a400010000e8400186000403030350010003405c140800344c07002280984d66101d080f0440ea550060a00407500c140b0001c1d20100031038510740e109a115400c002034007501d43c00400c080f490700360411408201011061028480c8044101341e209140f10b07282480c8001010f14022042d45611500d02c84200440000040d4019001c0180081c00c80310240c0604451003c0b000301000114070408003c6a10f00005c10703c07100643c021000380f5040502606d070041800300510403d54004164000203560381c20101d04a542c505410302d02400300b9a84054496440c40a01401c18000b01400d902550044480c840080c0c54001c40d540c2c8034000300c0c00040f4030601da049040c100d1051480083c03045100040c0418169040b0000e5400368000307900301c9001c11008001036044076000c0c00380c1a427 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 116623012 1250 116621762 116621767
    0x50406060816031104140f100e0f0409020405071e0201060b040b0714010504080d0b03190204020c1f2a0e04020d020f07050102030402010f02060f0619030b090d08060301020a05 77
    0x2c0c061841040c0b41c401e111841d00040d04600d0004089140e0095001070140c02852250310005140c020090324107040f04903598941821951000380a02108a00c01c50043d4140500b0510a95650380b02d5035049270003034003e200342c1ca00030000402c107404808049000b41041244038101510500c541c100780c40c00c1400b458501400c161545c8602c0e0050b40c421200b1641c01e10702c116800d1400e001c0d02e03010b00d10031812141c03140400c1d9401e07416200740304415070203a030001c6464103081b500d00c0c402c0031540e50165001a0746d6041e038004903050500c205130111f20398a4108800d104c120300c6500c650384008205110005d040b0f000002040048240e403603a02c002402c078111001181340030790081c010849a40e000518060641801180c107030420803055031140d501001704030035560040104030340384002e84058140351420405179000240003034840360183c00000b0b01d030541d90886081d20130103160880d851422516011000c0ea42c0d4030071900480f4001500390f00444c89a090500036640e401515486050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 116624262 1250 116623012 116623021
    0xe0105060304060618050a0606050705280c0e0f2401080a0b0406030507031407030c090902030312090a06110f0703030510051005030a05010e04020f0607050f0601060c020102070504060608 82
    0x303500050003c0d125540c1c1c43c2e01c0040c001e00003035040c420700c500001010a01c0d18011315040304171442a4025402d000003089220005180031841100049250701c80b81441400340c20034082c81c031044032004002c451500804580c1c0040801c02c1c40c8a0306400b14264500c0d91107000c20146a00c081800041000f02d08070030104c2903001d58201c9620240c1c1c5000028241c45c624001810340d81703142d10503a800d8002c40001e00522580425005450009800810304149181d49481f4008468441c2400b0a03035680140401c55030107008641c1003400441c440c00c4e0324140a020552a40c5002808440b0316140401c01c6000c40303502d03001d80c0d681c14408184a070034040d080e10140d01078000140515105880210f0100d056034a03014507443c07080307480c3c2c1da4584a00c1d00e0320598080b500c0c182c00000c07a00b80d80750704000c01652074803202500d145054034026200c03032030340c42d000d491300d540c80e201c84141c0e000b004008140140e000700e0f0001c14600076422501d000d0f6482007400700b1103c0358000c400004940f000000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 116625512 1250 116624262 116624269
    0x12050c0a0f1d0a060903050f01020a0e15090607150507030902031f0914011d0601050f010f18080c033a05040e010602030a0305181c0e0409050a05010e070e0105 70
    0x165030b0141407100080103040c0040c14880c070329080795002c1206507405000303000e41080081c0307a41400c140210300c0c012140002801d60a5a110302c20301c01c01520034030841e02422a003e640203250041c0815444140d980b0740100d401103d00302c2c12803480e180900007403003188640241c1994503006030203009030680700c83c00040510140203101c1c4880e0740385e018100009518603008407412010000015500c121180c10202881001ca002e2803103500500050040740d42c5d103c03404500c907409080c0342d2200d40d1110416a100380100c100f02103110400b007000508224081039000e0585821025031b48003541391036844038043c51900450f081450401800c3c00340c01c44420200781000580d082042c2025941c42c1c1c40c0c2a940003d82041005810201c3d00300c9415400d80601500721944c0703050103d41c201110a66a60b035008005207100d402d0100c814825860b002c2c44040301020030151040c0240003d5080c4160b032092a9070089440398a8020b41c00380841001c5107e4054442c5443c8203001c81e407900042 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 116626762 1250 116625512 116625527
    0x110109020a051e0a0b0901080105150a05130e090a060e120304020f22090b01060804150c03020c0703050604050d05091806041401090e0705030304151103070501090312050c0a0f 77
    0x15584104100c0b5041c1e2030b0f9241c2103824000c01c46590706a0341d80100c0c3d0b000401c580f4040e880f2b03d0003843c151100f4615440707500c0030351b400e4491601e441074503003660030380311100110380f6489448500009418090015000700b16100010300440c1c0901c051580b841c0e4541d50b9411107200c00468150500c0810300501d00360008158505000304100e168685180405280f10841d1201007140d9503548100010817086c100b189004100500f00b082e060304e420b45509100041d140e000c14040b0741e03228540625103010f5410385400d640500304560b102e41e04da00d025995103c05640c15a00c81c8503850a0000c114401c1c02281d0703c42c0000381c0f041a64100d80b42415041d4580a0714141c1e10540380c1c0200c0c070b5159285070720300e4000c101d00710000c550240140b00580c01e004094000c103020350400c2006000c0440240f0310700d5951010362501d60900482c19440c14114018008024895420f0414072814035034410508209028100c804000c2c036250664843c0b010310032012101c01041c03a10240c21401d0703000780d00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 116628012 1250 116626762 116626789
    0x1c09050f03010605061204050c0105121603060b0313031419050706020d05040f150c0203090f01020c060c06070f110a03050d020c0d050d140103110d050304080f010507110109020a05 79
    0x481c50948420019800740c1090380b808903100c160306e04100c00e10000b00010310b2400028203106141003118560720050490007891444400b845284108031144207a206200414640a089480341440040c0c4421400d00e000e041e00081d41e01c80b000b80c0514040c0084407002d101061250700003440403c42540d498001100c140ca48036400d09c01c154152200380500351146204100864003211549803a00c024060400305107219454851901000d0760004211850044111110344000e400d03040100e180003600c0e20794a03000701022451101b1842d001400a01401e150b48801880c428071001c00c65451121004081450780581c04620200c1d01600082003034103086070303000d494000340742000c0d031030311b82c44021800c0080e4002500380300900503445110346410301c50a09075955403450321401c0080100400c03061084215103140010082c007041110300078020030301520045941c00c1d5229000b09000c0303d0f08008920f41c882c2140910206200d22901503a0040c1310411141c1010203201a550210303d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 116629262 1250 116628012 116628019
    0x7020f0106050d23011506030f0203100306050c0c1002040911120f13140f0c0409150509031207030c0216030302031204061e09020f09010803040b070c030c0e091c09050f 74
    0x782130710a50a005545900044902104069103003541c020202d55561401e05210342c030600910620050002110044942103c0046282e8990008600c954840e00c00ca010003807140610380a42d0181540282084905041c01000781c82da0311200b903009071082d9840c1402c000b10b00c100145000c6200541c954015000c0040c40b6061101562901c0309915000c660140c40d030300080307007a1075212040101c060f00201c25107041c413604025550722282e0030400304140c0c110f140c4a0001071800311003042525948540700e80145a141055103000d002842001015001030150410089014071242860000c403549a801140781c141201c092800313418018100722220b03a00c400c600c0b0303400d082c44480c003400501415000140c41b000c0384100300711018030440007030080401c50010080c1840c0881031710121040108500d544002c00d2401058046c20b03034000500601141d003000c00d01d51140308103544600e40a0b030440790441d41e000c1200d605040945603600004140071400d00003404c0000d100a80303c40b026 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 116630512 1250 116629262 116629313
    0x1905070506070303021e0405030d050702130615090905102322271502090306010e0f070e0307062006090f0d0504140909030d0906020307020f0106050d 66
    0x3403001803040d500c1250140c000980215143c9540a008202d40f00a0054004d60a14041c540f4020035103da03081c0240c1c4040c044003007008019500c1e90b103400e42c0780480c0300c3c80401c2002d032614031040885200041000002d0701040b00492203010303500c2020300030698044c84455051400c5c1c08910340890405070052005a000349440c2e140d101c0120f0000f40008509800751031a462403944012a011800402400d072001c440c48020809507840e25091160441800704c400c10070400e03201c0181c0301d00007c841d054480c0304c00005502140100c09801158280103076a0a600c950408560040d800d103c65581508044410001c4501521008107036031036080d2801824440d00040d0382c140f00049030b10451a03000781d0080c41202c0010b00c2012055816404c1050500c0c1c140b08012a40e1151040303100c1c0281041004100740c0da204000b039610900b11030300c05001844551810324080d4000341d4449000d0f10613150301129411040c0103400a8641c0030f4203481180340c80f07031104820703032446900a032114205c6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 116631762 1250 116630512 116630519
    0xe0d05030c0a03081806040f080307090b0d0903090902090a09020d0b061612050304170a03020c011a01030e03210a0917041a160f08040f090509010f02030405190507 72
    0x180115940e25001e6100e1348050301e0684110440403e03a00544003a540203202040001600c003030345240c940d60092a001c0d2243e540c0302c02034441d55140c0e003084e1a060804038800004c80ca40d504801d143d00c0c400c0d510520800c3c4d44002d94002e0f4015001c10680c4284103400a1000c0c08244c1c3c05040301803440000410880340000104001c0d80c440e20a40300e01c24294400701c000d11440403a00c0340302501c1441c0c4545503203001c0d203030803640d14807814500c0d40c0403c00240300d0340741c40c3c8030350144c58406440400800c00030154043d4220441d079104030311404030b420a5981106600d01009440c144c100080081c1d00c00803510020f01d040c5070b03000305400324099035107505d04085480500e000780c105131404406d95841d030409054403440903182d6601441c000040191086014562010502c0264000e5001c1072140701c514004019000b16000b54504107440d0742d0001e00f100340c0b501702c1802401c408000308201341844070040305910044402500d0303a071002c89110010f54a440100c03000030300030420348594030744 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 116633012 1250 116631762 116631787
    0xf0102100204031112060f0a05071806030213081b09060a08010501080f1603030f0c020310020307050a11012f16030c11030c130c0e03300405010e0d0503 67
    0x5400696114070209518044d6081c07503400c400029020030b004280c1407500c1013000c20320a6009103070741c001e5905d480c04182842d0080441d00040100040c0b0214583e0311180c00400030340107900180080704050000240f034020104402d50081081d80440640301815014448400000b07804142c004c01c18580010713100d6000e00c5840e01a0200c58003529a01d15180c030441d10b002d280c007029042401d40d0000030000203400071100c000d11501400d040b20f640321a0b0000a08201d01c400b64100c025000204101e0390551000c0200b1500005031a50006070541302000c40c200c0c0d6100791032318a0710040f945c49143c02420500c1102c000300049074542c1c6040652041148040d40c041800c8012885101010f402c00c06020301502000310140c0c0206610b0035918000f0700144031020307818000c99580da01c007400c0b161051101d140c0c1d948024084850600c0c0006a0442c0110840c4807541c072001d10000ca090820950400c9900b1500160b60300209503c02000b0040c58a9840004803010310082154803407412 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 116634262 1250 116633012 116633017
    0xc04060e03100204080304080d03050c0412030c15051012080405060702030f07030c0302090a0c090911070b0f060901150504030305130504050703051f061d030c090a0204090b0d020f0f01021002 84
    0x840101543e1a14a0106083d00d4840002741701c1c4281410007040020501c000c0c800d88c0c007158589806058806014102560911000100036000c03007084000c84110500f40d4100900901d04c807000b14a8050790f51012071200103c610008040c1c0004100410061902034050000e1038001420355100c1e01d180e603100c510706a150f900407110080b01d213004006624200e80c015610200b0300505111011111f04018003620440c0181e00c50503aa450a406510382e01100f510b2001e0781c011901d40441c01c1100184090000859000d4401c06c122030000c0740095025240d560030381c5c81034039414106400e40d9010303603540e08000c80702d8050284907040020244c1d9036015041c040d180c40c1c3c070002032504020940ca80020996459015402d2b00362604006040d07010200d44210841901c00420741ca80101c0024207014026000c02d500c45051400e00012541c1a0b00502c00c40d500140100640011541401621680080d020750b2140c0707508404521400e218450012800c2d0500c16141000741146a14007244c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 116635512 1250 116634262 116634269
    0x30316030e0f0f012705041104050310090201090b0306011812020427021c020409030f020d0906090b0304050f010c09050108100b190215040809090f0c04060e03100204 73
    0x240561450035250030b190300c0305003100009580280705141c108001030b060300c448502e880090b04000b0700d21008001102200b6010300402031052152010003000340c08a50000e020304c5110740155a40c032400240a4450741c0401941038649c403000c145005a0051182c00050115040c00a00242c00c014101e040c10a0b034098595158801c09004031801030101711006203072000a0036500e1b40d0142054100c14200e40d1216904a40d81401c0c1038600c00d54040c1390f01d900c48029000ba0400014208050300300d03d180e4065800e40e42100d407002c04501c4211003c041c6803040c00e0101c0c603c45000d0240707510500013180d005002c0c2c0102d801d0a03428581e41401c65010b0b10142d00043ca9002c01403007150b0b4864500c903003000501c14900c152038202041d10300e03603200307040c91410051102c0c0704a044a0707000344100c40b00300c03040d03c0740484145043d0400d01440d50100400301e08c2807a031000000c1480b1b500000b41e5000d500e411b4005030429041000c20764400039045c0b40c05a042c800d50020b101490071038002400134 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 116636762 1250 116635512 116635517
    0xa081509010b1807022e0b040f0c0503011d010e06010c03020a0f110a06021209010f090905010b03010504050906090a03080a1e0f050c0712080a06030b0f0708090d0503130203031603 79
    0xa45031000c8020708113180c031030707054000900006d2440a002101000b070688418613a03000a104844400010f0003440a030440c000481d003011a00c940e181d80080186048403014016004074000e4101281c1340c9401c01d000c1c0c225800286000705c0e07091b510403c103000c3d4441c442c0c01155441d40c1142c07034140801410210031641e04101039101c2080e401c0c003010202c000c1805000802d072001c402003540040d800351038101070400c225070300240c42e0541315446140c000d01d002c040400c11540c680b500c12606600901905000c0d504100100d42c031504c001038014811400000500140340f095039086a0461001e4001c054054980744004254000881d200034404000000090010081c1c4d0b556800d8580c003e00704a1a128288071040104240101d04100640e440c94404c8c91540c40c8154540146400e8002610304211141003250010f407040c0154015505521000e11958602c1451640c4000c400e4a0500198084c03022411640880790b440040620003015281000e0300d602c0324655240c07400806500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 116638012 1250 116636762 116636809
    0xb090f071b0309030f0c03080f18011e030b130e011a0a030b0f09011805010b090f1009050c04050306042003190332040302040b0a081509010b 62
    0x110303039003015030401d8200000360410349100d0705803405052610244400780c0000d010000c9142044100c0041c5009181d11100082d219004010a050342c0c1e085100101d1002c24000d103045402c0d8050503001182c0d1504c0940d042e452480e0b00c07021005030021882d050340003524550307200b0300e01c1190300a0080d40a525000050000199005800b007024003158150141e0030368403080c0081248141d2281e4810040481d04881c0d0300c90f10801d50050135080e503d800700d00503c029160030000190040400780004071007007034998840c0b60392590349aa00780c0701800c414011000401000c00141c20240d4000109950503090940d40c2c40401d05012040b00c00303c640440006240d00c2c0e408d8801c012040c07400c01a0010035988030b113520142000b031a20340014051015052207000c68020405491100320b0b03c43c16060100032009000040e250080c0c0412841a07003085090282c41c14400420012515820020b2201070b1407244045100741c0054928290380d500c84207542e0660b12101c0d000c080d011030b4000d4504 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 116639262 1250 116638012 116638021
    0x1201060e15090105090f161101060303080103051005010509060409260c120a0f1101090f0b16020c0618011b08040603061d1611070308040608060303120a0b040b090f 72
    0x1a20310050300420310845c0020103000001d100390b0340880e030040b4140d0055075102d80300142540c1c00603c1400229041d807d01101204040c0d20003502030490788540c0403a6600030006141100740ca8090181d00e8002e224540028440d14040e0410b0103081d00800d000307000303016021802031322102c81510004800c0400221066402000c1008145403007000d003c0b00d08027041000028007114014034460304010050440d04d2440c0d8003941700f041c82c2e03540324031a444910002d02e003d4204c244210740b07004442c0da90160229056002081c100401040205401d04d000c10303440700a02c8180e1004051410002e448000c15020301202c0e0b00c5c1040385000c1d00d4655110352900200900366a0950444500c1142000c085480d0005e41c000300c1d5000320060903505080a051042124180705450b030782d003d40d1261100000c140720a0390018026280c45542e44172050760342005040d503a210720791044e1400b010000005039010f140b540490340302000100003068400c8141e002444000007030311250700c07462216081c0f0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 116640512 1250 116639262 116639269
    0x4030906020a120503040204020d0507030506030105010623030a1103040501020414100c11010e030a061d03030106080103030f050d06171509070b0d1b09181a1201060e15 74
    0x200052019200901041d00265543d01c08109018504030034001c002c0b0102d002c40d940c58050b00d000c0e44a40c1020001b03484e00d0200200503080940c0c00324040d52a010001c41c1c0c0c00d2180c1441c0a5803200041a032446041a4600c141150710043c1081a883c0d52119640b01c40c0038800011030155005400244e211420b010040f00e14034442c2d03101d540324181140d0f100201c92340040c04414101c0d080402219607521200040c0c407600c44104000d1344c507000d4000701f80100b200ea680a12410002c5145003481030741940c02c055500e201c04e000d407102081e0400700410010341318011807014011145000760400d046c41c0e9210007130351303001d07007240461001d180742c032500a100801c104481405c044100c40d40d242442c0c20002c0d280c02d00e50003201c11124001400d03100d107000303a4001a501420600f5500c440c8a03c20364002d00c401079138042ea40c47e20903104000f1103089064002c820015840c10320420010004c0c00403c0603002c48072424040701c0d506c81e4400209200407445481c03181159020201041c0b0a071405c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 116641762 1250 116640512 116640527
    0x40804120f06151520071206060504060506090d1a070309050c0103060605160c0b070503120a02030c030a0b1906030b010f0306150f090e01030309050f0f030a080901031e050403 77
    0x4800f8100300504003000740e00c4801c605501d0058480c100076104401c941e46044044000700c0702e02c0d60603c280e00e000140f84d01d00d80c0a0344070040c0600c1c0704201e01601d0300100b000b41c82c0741c0c2c400c1c44c1e031001051000d4507152030941045090140728040e400f902400d0484150f01502c4115810340201e03950392180000c2c00380c14813035032054603424602004402d040c200081c04038010960040280c48090040c10100504500800c01901c01091a2622100d9038603040d40d4a51103801ca0a40c051681c06c0030034060703401d5000750303801885401c07402c0c0d0459079034030b00d4000207002400c07a05911020020000e0991580c040c02000a00a581d0307011441ea4010400903102440c12034800302003600d0300c20200440840b0f4100752420594903e0500c0030840d01c54001c42d55552150881c0300303003940031307000003040681041c0808201c0700151805a685007000080004105020020301d0b01900b00d2441c03000056a03003401490010414103000801092002144102146c11000104066a5171090005058000c02c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 116643012 1250 116641762 116641781
    0xb040308100816090c02030d02040b0a1b15020304020105190c050714090408030c0f0406020c03060f13030e031609090b010e19020a03060b0703050d060b090a0e040804120f06 76
    0x700f900d24015200b00401ca80680300302c0585554401c124030701d0314400d004a4900103001c071025510386450304400305003070780402041c1d00418908401103910030655011004142c0d0000c903c2c9108500c0701403c4006948020012810401c0c1040301c9051519407401d01012400265200310340300e441c03403506911300342654019000c1100c04000510703041d03a5041d0101d603c2540000f09503200d4403000d0080b036540c006c0403a140026003000c81c01103505a170006400a203010202d040320300540b1694408018040c0540d8075210006540f070a400c042070007802e0051641501808441d00c9a043c20008004e03041c194204200c010346846000d000c0c00f4500d1031840c0540141c4410f484942000c4820340342c1d0154240d414124150081361411919010754401c81c0246001d214056071941c01d40341c001c01c00d51010080600c1340c0d2400741c2c04510903803500f054406510b0050940f0200d1030500100100060004004807040e40d410040070401800d04128200f4003031250300c1000c035110309403415400380ca03000302 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 116644262 1250 116643012 116643029
    0x150e06041d0309060d06030209250810060302180a0f0504110c15130503040e07030e070e010b090409080f0703022503030503090a050d080a0c030b03030909060d0b04030810 75
    0x214241c2804021181c8400044500550ba05421404000504441d600c06940811002c4c10070030203604981c01250b10079203000703080020400c1403909642c2d40209403444c89610080c403c0510840780a0350042403004158050038030800102130008040400d59001319440c0101c0750000c0060341002c1c02a20040c015031820142003040341000e40e565000340c21420190403100c10040303511010019040c41666800c942a02d0344c4a440e000c6504c0e2402c1c0948006002901c0e25020204580b800702c0c0c030500360303440380b003104080da46801c6864806801c1440c0722940036503103940c80000204844020040e50780949101c0c0d0300d5541a00b0041d0501034a01c88103800c1c0011a94505010821800e8030700c1900d5160419544944510030303140e02d00031400c00300910b06c0c0b003180121442c850300512a984101400c2d4003c0c020304403040022400c0d1801c01d100190158810300070101c561918400080d8050806003032007120391801e8a907112244815642680403806800c1030100c2120b032041325002600c00ca1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 116645512 1250 116644262 116644301
    0x31f060f03060e0103020f190b0309060f0105030c01021203090327180103050604021c02060310031401021206040903030207080708040609090905060601080702010b120c1008070206041104150e0604 86
    0x64000c180da00d410006074501c5291400b00e0080c2c840240c07000c00c0c028000201514ae220714042c0c074007075034030b481c1503030f840068402c1030000045501d400500e001101c04180d000d45640e440030707070015400c0c1e040500f8890460100b4007000300c003400c01320b21401c50901000c3d080003c1c8080304040c0201401c01c00d5000000c0020800107201181c400207003141c0083d415030b00002c661284141102d900041c14400030350003000001400420811899030b00283c0303014200d2030300010941d100e002d08071b11a841503140b00c420004001500c9141650009180601030b0402500e080040c1e90344100640c80321030201c56030400810306000d9190300942150240c003000c0001c11404d4840d490352a600c3c00000c11640c1001410300004920510039081600a010050902d9180c0100f8802183d150241c001c0c1d140c0c0660302241200039075903c00c51a04c1d0080c52660040c104548413038607416045031303111400b9900643c0310f2007410350b100b60200034a00146203e0031544812f080c44020001522040a12000c403205038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 116646762 1250 116645512 116645519
    0xb12040c0510020102040e0a15060809030913050a0506121e0f060c0301081b01080606220603060e150108011505040b0a080105030d0c030801050d0c030503030408070b011a0f031f060f03060e01 84
    0x40d1006003610490702f005c080030b40c1c81e9000e5038603502c1400b445580000c2e803034100d02c0411201e900828061030561900340711668980c1c06201250b0040c1c040c46c8410341c40300c00008402d074400100c5507218004c1205507101c0d1544601c8140c642001582e5080c0003900001c01003000501c18000d8003c0b80740480d582141409030358000070011540179000c0740c440c040001e80201000141e007904c071040c0d000140c1e80b8841d030382c2d6150084e004020a1049a0f030b0740c0c500100040001101c14540000c0b010143c44880c4a03074200192080e0309203c0118020602c00e04100202d02c540410000d46025200c03a6190707100d942c1003000f03050030009513154080c284120076411400003500300505505507001030b00d080c288500c0f00d007441602c4024590020300f00e404000309110512160300010580b207406021031045990380c45032100440c0115002c007280300070061015804620b010001117030042001260740d00da0403100020700010360b4486c1d0116000c248a41078903440e0701d804d070041200070181c507204c1985a615 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 116648012 1250 116646762 116646791
    0x6050c15060105070c0608090d11030304030e12151e070906050a050f070b060a050306010e06091323060c0a050f0c0a050a11031005010b12040c0510020102040e0a 71
    0xd5042480020a68110009060b80d1252003500e2115400c0b894501c146640d420004d004504140d9146038a40140d9191a6100340030782100f9510602000007541307190b0b92034604651204001e45503603030002c407031007408003101010421544600d1854002551608104540c401140668243c110803a41040100103014bc0c12034080c0c0102d034200e0504540d102c0550400b22224441c0b6a181e0028003800306030395080c4034600315018130428080da44200c0081d264002c02d83d890409200d04075a5090040c00a4a58208201c9181e084260440d031040030401d903a440e2a001c0001441040040d41442e400c20249041004950b81159a803010b03140b07402c18911000382103214070003c0c82c03140030001401a070001404c0143c4120a0703000415200415030900c0c08040c8c65881d11410b5100380f1440c1400b461200e164494a0b040f83c40d00e40507203141c07058501d403450030355000400c140c50403a20b8000000703843e181e0b001484901c03805e643c0016601d80c280a03c58640c020007800c0c1000c04c2d0b150054090b001803 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 116649262 1250 116648012 116648023
    0xb0a0608150904110d050705030f030403020319030c021008150f030d081008030c070f090b061b0109020a1e150c17090607030c02040c031116050705030102030c04050a06050c 76
    0x110648080030141d0715401c0500b074203844e007407405400c82e0b400c00c000400e00c2030104501c420341e88102d00399a0b0000c810801d8556a0140c0d02001c1d506800c40301401c519000c2c265060001c3c8e038468141440799211580000e10a540183c0002010469139010048000039800300790200740c2d000c0701c55416000608020075900d45011602800740008507012980c0307105d1403101c00d4000c00d4510304496641e0054021541c440c03030588554401c02146060206400816000f0f1201e40040501480e0600c00c000620907a1290350301e4400045542e542e07070840240e2a0030ba081c0d0090071200d03021241866000301c03a41042201c550211010035044914860169401880700e4106608504c19000201301120b403c04c0612406c1074603030740040002095410903410410741d11701035008641c1080024001e050550a540d03590540050300a001c200260705000781d03446041126001d041201c41903a141c4003c40d0886c1d009480c404c646810100701000b25240c840010400f800d060b28005061803010640d661340d40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 116650512 1250 116649262 116649301
    0xb01150909111206090103081e07020a0f05030f0609060a0b1f020d09080307050a0305090a0801180c150e060c030702090a05061005070506070c1a041202070f030237090b0a0608 77
    0x1107403100c1600390701481c0c806694ac0c07c1c0e002040034801c19650b40c0c0c2c0c0c400c007081502c10b4600078080c118002c144100003107040c921074403021020f80303e0760b550442d1080003000d0038011154480300c4440c1031016a5224003003207056080079002000203841e089009082181c0a070300154079603004010420003c2c0001c21446031260f4181009911058020700061070700c1d04c6904440d0896190900d40b22034038107001c40c800341c154014440015665219042c00903010b551031100e40214298621820140c2401c02c020820740c2039141c140c90900505a000480708001030390034009454070b81050010364a06000410503681c0e141c1422403504d00540c0d505500e41d030b4001c0c000c00901902c890030301b0030300403525410343c0c00892541d5294920320706840d002c00b00941074440c0300e00522032060085012221070042109803600200b810044403450401c81c0d07a00d03291304264011200a4450590300d10a000701018090184c0820100320b5000c48028441d8014050340540c0c100694803060002100c42c65221007000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 116651762 1250 116650512 116650537
    0xa09050c06030406110a0306031704120b07020f0d0e1305130f0215030a090c050111030412080d1814060601080103060209030c060d02120c03040b0115090911120609010308 75
    0x3665074605020000b0003000503103500854001610881b0558180c1c0520140d80c8a055007004560865800030300c58002c3d4010030355150b00c06440280415000d000e541d500c40c0e454030490310200340c3c1100450501c001345000c01b000c61041045c10040303180501e0350020f10900c01e50304100314580300450030440380b21b102e800791071081043d500303c0079501c0e000610a482c450780b6100507030b641424501c000082889001c2a20001041140842d85610134103280d184032a81c2001103040074103000d43d40704010400d20302116460010441a074200c1140c1c041c2c80114000c407841560b00c40300070b080200000401382c002e508284c020b00c0402272070381c2c0c002c880d40341580e400050040e20f4243c0c100c003003403511440e03040555100707601090315041010f5680040440d02c0407891145000d464010300303020302d40010b450040c0020007080061003400074140206001407800e11b001c6880303aa642c00c05800b01c407940d4001c007204c0d03200016040054500007856030380202d0250343c00c441640c0744d91900c010a00901040300f40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 116653012 1250 116651762 116651767
    0xc02061b040e0a090203030304150f0b01120c1e0c03170603060c0c0c0405010e090f0109020f100c081201090b030a0309050f040b04050c1305060a0e040b010903060903020609060a09050c06 82
    0x103d01d0042c1d40031070612a40a4212581d90034075080000c3d00804200140c2101c03030501103011881030181c02014041c40041c1c464422204140000130050b14445d03c0751010004007d08031052a1807200d9403d2103114540c4699902841c50300317000f00a00425090295105400c00601020340c5000810030341c0001c45800b55501d4440340c032181400e02a44140311a8098140000803d05140e10010039003c0c00748042180d4071103d04444031402e80f46444d80107503004035441244641801d102c0f42c2e4032120f03a00c9140031248100c495503401113540011140b500c82c2c0c825880144408500c91150200c42c0c2000c80050802030b13445c1e0380c02003040f0024082c0c1400b44100201c0ca42050300c0701c0e0402c0001c5a4000d00506c003030320304290050060742196107080800c6268040005190406000b11400c0e90303010f55440400400c24003c0c0405401e03030640185c10088601d80010110f15548510828588a580039040508183d401c03d817400902900c2100e680b0f00d41451040040c50009200c03e65080c142c4640340c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 116654262 1250 116653012 116653021
    0x60f010b0d0f140105010201061203050f03041a04030804030f090806070c150603110405060f01121503150213270e010e0106030803010806010e0f010b07110a0602010c02061b040e 78
    0x5040c07000201242c2030b041c5801c4190154400355550305868080e4020000b29035101c0041c11a82c040060240100310b08000a028150052000b90b52050240c2d203901d44400300c040064220404c2150194001801e0405000815900c80f4814881c84414a000c8221905050544d600c58030080c08600c140420340445404110710144281d08446066504014442d92400c5c10f8803594000c8100a2049280800103402458078540510142c5c074181d40fa40024a8042c59190051443d0414a055240f42d1540000000d100861503094085403036000b5031294403411050702409426003041d8040d0840c0da020180096002007500c0b0034841b82100420f042881004040c01001c54116000285d42451750100611240000031412280f800086946d0350380c0e0380d10b03115010402070b901c80450107a02c1004102254844c0e014105440c050000304254500300000034054041c20391203030016075101d140226480c1c0c2c0501c00c06a00c81e110851501400d003400e038028100d48560702441c0c80055606020a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 116655512 1250 116654262 116654287
    0x403031106011d06031c020a02030708060f040210090801020f07050120030703231611010510030605040305090d060f0b0301052203090e101401020c0907050a05090a0b0d0b03060f010b 80
    0xd280700615414241c905450311b14001352100030361903041c4d00a211742c0b0301c0060368160010f040d900c14072602d0450001c5072141da007008a4a40c07480030100400012100c045a000c5082c401000b1040b48800c48542c0c0d00140c0c40d00900f5100b041003a20003034a50030704003a207803200407000c890340010305180006900d0701d101030a0700c0c01daa4500202c0c11882e1808100300003031002c0b444060202c9160b85506a0300035008100380d003654002c13600c010b107140303d0280c1000012010340000742c01034482d0038130301d00f458210004207e0030101c0b80403d451301c039102c2c1403d0206080c80d100ea103183e10800d400034855840c160704103802e13880100018002d46405825200185842400820041d00d94107500420343d09001d040003130248030a000e9240702000da01d11303540d400d41c0001080c8811a001070070b0a009550350740301c04c1d2540d4201030710a005202c01041100129032360403098402901e4403640c060703141c204002400c0d04956501c03c01c640a07034801824400c0e0400507444490444034159074031039885400f003102 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 116656762 1250 116655512 116655523
    0x3050901060e15120601080a0209070306090e0c040501060201090f02090604060b0f04060f050408150a0213030803040510110f0c01091509020907051e070602120c0403031106011d0603 80
    0x820b8640c0c1c8040240203d003608911001003401049034160440280d050f51107071943c4080c42201d1843c0e005c4030000006041500c0c121b0340c080194203000074000d941c0d07008001600c0c800a1b011440d900f0201d180c02d80c40c5454494035004d0800c610003080020010b40c2c41c1090410b00c4e10001c0c0c41008a0000203805545a400c808050300151074202d4aa40186071409030507045809030101251460034200c0c1c0f41032090007964103c0301c1c1d0900400380b4403000c0c07900ca15500c00107014041c64503020499036010306228040d050003184101e80c4c003541c83c075142c10401d08200300c012074100050b00344280381c01d40d91403000955800d10040c1108079035500b00200341500504010350002c01c8030341421a00556862154030420b03000f4000d95840d01c40d503a410400701c0d424401c0c81169035094054803440b01c040d000041c06440001e2141a0043ca00584070007071500c01c03a030846030344104142c00a0300f881010b500c561000017465140000b061303154106890f14021b000e05d084110003081c03030040000c04070740c0c0030010b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 116658012 1250 116656762 116656769
    0x4030f0f0c20061b010528021303141f06030809060a020703061802010f0e06031b0702060403060605100507030504050f060d05010305030405100c120c08070503120402040c08090601060305090106 85
    0x440e40c3d541310340c04480300b140d900e48480942951030324002502c040078070700503200c51080a00442641c0c402c1c070403a110003034000c44011515850301c0e000120000fa10445104082210b001c02880462240f03131141141941d40d5144048a0741422401c0000038009425200d0160b011650300da110041c109080b0300d4a5111380c4050683c1e8201284503400c04032080c143d00d0708900031b0b038490284140c0a5410303100d01c44540e02d1190008001c0000589420812004e55582e01039018070a18041041d0001100e9422079081950500d6403034604205030b00e070080002c10468a44d003440c0c2e0074010142c070050704034021441020700906101e0b511160325034621044417110f800004003004a943c40b0704107a51341c2e4106d80520350151610402007002c1502400b141c90300c0607072109a983c013002054104440015a540d8201c9441e00140701c44400560184041d0018605030032454019142c0340c010041914049042c00d001d00000100341702c510070002c5055419540c09040c0030455031079500606004164503031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 116659262 1250 116658012 116658019
    0x10501050c10290409150b03010f0203090c0306070801080604060b0103090f05010605040506041503230604140d030212070804050f0709021305040203060d030e01020c1002030304030f0f0c20 83
    0x800c5000340710700d025140303030801d0315901160320102c01c1e44051204498002d107002c0c0403070070003d100c0c1b055400f0301d42000441d420b014001041c0e5505850100c81a80c009036031401d084e410010119640382801c000a07940100d0601e07002c2c20365450202d145440f91400707400503144079190b00800820740d001c3d1b0446160b0301e13802440b44649480c5410603500070562070040512450610000c0380d01807610380120701420610200103206245142d8500001a168692403400c5088003034542020160078481c1520607030041c960280f00d10303e043d0400342000104d4808605161040c030030504648004039088e03500188508021003c0c3c1c41e030781001842c0820043d60358003184503000000ca901c0341e5035006451310079910038090f0030300c80d100e404010690004488a64102c003440b20200042803044040b24140380c010300640d181440c1c6540411040e1098400309005640004140010998001e5030b03541031050925207034040c4030f0280030042041d42c0042d0058040020b04070b00118950440604400e8040b005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 116660512 1250 116659262 116659271
    0xb04140a14010504110108010b09061809010f0f060c0b070c140d030e07080304030503070b1005040609050924060d05031207180b0703050915070605040501020316020f0303010501050c10 81
    0x9041103003c0c010480d41140d0104114072480429405140d201e0b040c3c1d14116035840c1885085800e10207160801030081c242032029594070903581e20b404141e20302030840e0203d0541035a08011001119494a074000d004110b880f03030012022503590303042c49410440a1400706050500307400c0c140ca600789981c0c0000858010420480406505a031024040d60291400e13601e082e6680c3e40c015803030380554400685650070412030100040e10590805910048020024400548400216040701c686801122409035030b0001e02c0f46880040040d83c100c0c055030303080039201000604030303224580300240416025901100820b800c1000510035100da1402c4011400c20900e001c0d1801014040f5410702805d175004040700c040380041c40201290601e90301511160315080030300040c800c13080310025001144910502081c0002119400f811380150f00800c00942c9a003072258507018010034015a810035540f2003110003050b4080481500e0440b0002d007052500c890304d502170381c0d0030640d0700544e0b00b08280c80c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 116661762 1250 116660512 116660543
    0x1060e0f061b0f01020d110702130507180602011e180b0613020705060103020a0f0803041a041806090b040204050f151908100b0f0306100201020f07030c050f0a0b04140a 74
    0x540c0608051b044220781403104240da01000c004500c43c4a801a4000c002c9216549400010f90490b503080551443e00700c0281082a009201442017508030f0300042c0d440308080881c0200c5580c50040e00a01542c0403c04203101108000c25424000d0000740603507940c200003049940d443c2d84044281400b01c409550f00c03a03403890403503101c0509000032840380140725804166600d038421400c095030403400046242908050303544079030320000c21401d103d5650820011803d040c02c2c04404884c4031040d4400f01d0044c0c00c1c030f2004e00c242c4001200aa00031881171208005940e20000d03c4051040256400d5071110300003071001c08140b00314000113030b280894000c03680b09258050300d518032031013059104440558481c00700d5140303840783c11031002202c0b0060000c0707802d038680030712000f54070029400014508031941c1c1601303405070010a42600400d022109007014400e09000a01461200d08041c041119043c1e0310310120005c05031000d81a0410001c0ca0301907840100081e29003143c0115071034150201 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 116663012 1250 116661762 116661793
    0x160507030b090a0c17070f090c030501050609181b070807110316030b090a15020c011406061b01020909040f1101020115050118210b01060e0f061b 64
    0x1000c0c40308840010722440010074510001c03500700001503110106070152494000003001c0b03e03210340700700d6010b402903450000e28101c0c3d10304940000c05810314041034504036588054102c690580c01540070300c00c10000010b80360b031401000045807120f4903540d41213441e50082482c501c681c2903c01c2900d0340c00000d01c038081c00728060141c044036108160040c2107101d158103041c1c4481c840c0341030081c1c041c500c24090002400c80400a0f0f03100c00c0b410122007d42e13602d030320f8084a50000b101d22515082e80040c225100708030078001d072100a000c2c142c4041075070618030085810b07132140c0100c48240e4403032034003c03001190081d01191100880100750350f54500303250600c503001c04a440411150401090400c20140d40103005800b041c01c43e4410304400c0500c6c090041d6034030002000d52200540704100040b4000c0f035070400c0e10400110010700c0703111068082c80d005000c0c0d0410b8028400784100b03104c845d40075646190f80e2040d0380505480c0c1d1307900c640c2d00e407603920010f51420000520718024080c80002104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 116664262 1250 116663012 116663023
    0xe030f0c01092a03030503060d0605012405070c0e070909060303030f0f0911010e04090215030a060803030c0706090305040902030f06030106060e010813030c05060903070b010b04180c02031605 84
    0x5019041040f046001d42400d012000d0410224103102c901c811003c1000c81e0080300a907510010140513003410244950380c0200311035098211071901544901c004c002c40c480105602980d480e6810203e00d0003116880700c565a281760b10810070040f40f40c400081090b4802d0301070100400559909008079600c03403502030040c041d10032480300802d01d400d8a1034420544c500554100a82001400e0750685e69040110394840802e40c52070340298031000c2e103a0058a40041840070040c059114540741e0030000020000e8448543c4440c001c1d50040c0180101018038a040342c4040b40e0165000500914030700e410307982400303079134001c110b2203201000b0401549582d41ca4184185401c9008111943e1903131310903510582c0000505001a40e44000a401c0e01040f03460078910902074202048025401e54441d403901400311101d4209400124110082000c1000e01d2800740c18401a91400d103800d000038105109007010b00c1d0680c4a8a4265585840d03000f4821103d80888480000b903400c01c19080bc00d945c1e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 116665512 1250 116664262 116664281
    0x90f1e010f110a080a0e030a020c030f030301230d0602190306230d11030307050d030506040606120504110319030210090c0b03190f0b030d0e0102030d0e030f0c01 71
    0x194207010202140403420311507441d002c0c00721480c41d818107207410300c2101c0c2c50300b005140e15003580e522003441c41c0d02d10f810000f40c090100103900a140d1060030300141030900c0500d82401c3c12660080c00107103d01861070440c00d151144000c00381c2d030480c5a407000904102c440840c0900441c1c80000c400c4090382681440c2a21104a501e0a0004a80e5809a1100d4019a0751007a025400924510b800c3c1d03d0002c0e12403c1d02e9005543d41e00072095480c0000c0c1c19544114001ca581b54840e107880800f40350980200ea83c0403c2c00c56040020500d0550003401c110f40745050303407640036607440000d001c110702c3d0000e03a000203001404491103054114503034190341520020030340141c0700741916a041d020700c90250142059015403080001c1303240003510f42c896007010b0002070014000144040d003042e0075102d2803000812041f0082500d80060040c50300340007005900c41d0401040304004030b60b50b60000b040740d80c00700c55030400042c400d40e039031901403d60080104602ca2214001450340716201d054100e0b2012 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 116666762 1250 116665512 116665573
    0xc03040302121201210302190314120414030301290d05010806070909020301140d050f0111030411010c02031c03090c120c0f080a060c0c08071401050c21090f 69
    0x40001ea08410305c0c50f0f85101004005078400c1203a4560400d103030500c0301d0803510a00f0100d40c0d9049403032664045812004c955203401c4060004c1000380640c100c3c8480340c2c48100e070702451565051403903504061141500f001c07406081d0a400c1500015801c00b112500b030120803041102d03584a45990b51a41010b40d00c200018401c1e6a0100e0207a60b03500c00c99040fa40103c907400700c0c0e5514482840f09003100d219058510307010320482106407890a00480c0d145e03540c506035055483ca064070b410304404101848031410800741c0b402038001600c00003107068900c0075910a0031280c14105100300c0242c1034801c001011100d60781d0b40010404000030203210003070310403020200c00d641c40f40c810f0010424203100f031403541d50043d100301000c540c07260301c40c240c200ca05e880c1c81c1e402c80c42d1a482d4541076038004e171800c40e107007100d040740b28191803001e02c509900803031010040c529000f2800b40c1740034090029000820480c00c02c10110340200410011103280b001d8020945100c0041c0708101d01c40c1c02d6080c070391500c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 116668012 1250 116666762 116666789
    0x50a06080105060f1f050c030a0c1a010602060403030b04060518090d080f0a0203040303021204050f150606270d0302340e07140f0c070b03040503030c03040302121201 73
    0x964501030550080011000d010720300101907034484040c1c2481c07510204018424104000c0720b095a0038001004409683d0300c0d040f40301c41070be2612660b00c603d40f240560155030b080c001407054a0b404507007650420f815180105110104400040050a4940c4a1035104028040d0001c1248801c22000d119132420381c281d40c06484081c50a90301c55100f00d5215105a900400103008445198040c50304240649001030526404000509958000b9142074a40740d00a2031201c50900c0100201d20050040c585140d080b0300300b250114246004644420390043c540d08900e18072100d200780075000d188001014441a500542030103926082950311111a00304400c903034111200305c3c1000c000e07040e000e002e016a1200d02d481201f5070041c1b00984031034100b011881203a107550510320050320001c1c611690386941c9010800c0c00070301c1c1c81c08a40c0041c0c48081c0500400004c10b002000b82c0e80d12400304e6200351390300d94982c54120704010f1070316040c540e420380206070303214190030005070b09059400c040100903 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 116669262 1250 116668012 116668021
    0xf0f080a02010504060507050109061104090507021612020102030f0301060801030219060c060207060e0a2307030807020103091b1203030617100c020a02040515030c0111030304030c0f0204050a06080105 88
    0x9855031039511010307001c02c200b0001003103668890001042e0a0b8040d00c0000b8502201d503071004152440c58880068040e0081403c0c407464400380714194104070785d4001003140c04050f05884605070258411123101880a000d00b00a40e4024401c880e050362580d02e2043d03aa40e12260050b00d103003000c1c081607014030120322006c088610404140340a0341c0e4551640740c0320400b182e0392000079500408040b04d10300d03120076012659040400074016030178441c0c000b07803001c401540036600e42a005514034054980c0120780400204510b102100c81054080c0780204200c246030818000952003400c222001e00a031040002d8880682c0301002c4200f33109070307400e01c401c50f55040384511900d500290510a43c02100c80382c8200c0c1d41981c01020049030b140161006100c2940004040711004c0360300003100502c44080d02c00300e25092042c11a000f1b003d080101c125014011050360b03a0000a07c0101031190b0341000c0780500503081c000c082101c0d401002845189043c91445019002a02c28035559609090106 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 116670512 1250 116669262 116669279
    0x510030c05030a05190f080a110c0307051f05040803030103080414090402091303111608070602160e13080705010b010801050406051005070206072f0a060504140312040f0f 75
    0x143c050130b4000d030041010400070441102c0b6842e9281d402c4900440305101c4000140711140581240800303503e0f1001d21404441030903003803819900a16100c1d1304404014040c075a122500c1c02c40040b9030f614041103211000c002a2142e10464110581c10311000c4000010040000014000d442c40341001d051440d0307031402801401d0100b03440095100c194503000910400791340f580c0000380760103841e002c1c1c1402291070946052a48660b1800040001000103006070502004410010195480241016007040c01e0000c2d03003600318010000c04e803140710302144043c00001002c1040710341041030507640f03450614080d0f0080054481c0b80f0301203009000005044d180c544508811070350060140ca0f030386641c95204a4080c4e020380340403644240140300c3c3e0401b0ad2000b45980700d092200c00d641c00c000c40c1a06003014000050000c1c000d100b0205407009101056000c01900d08580000911aa02840d1309001a082041c0c00c4103200981c0b401140002d074070b44240c400134044911001b071741d41c883c64840c0c044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 116671762 1250 116670512 116670523
    0x31b15020d082a041805060f01050a081e13050c1504060507020310020309060603060a09020f01080601050c060906010f080102070f1b030507030302030d0c02060405120307030204090510030c0503 85
    0x42070102d03041c0c0000454041c0540d2507003001841481e6000003010703c07101142d0f21074205801800070344642c0040100000154415a500100c003100c1d43d0850545803030008040d4401c0149440410000c00c0228171800c43c3e02d1030118042c00d255641c1207092a2402c051a83d42c0140c03c02920700303116a81c0c4100c11404c0880d00200a0b16504a4091816081040a071602d41c00004126014030603c17041681c0c1960300c0c4080e5000d12002800740005003000310406190000180c03034444c40c0e52a1400220050b81e900300500c0c00103c0a0808003055a075410040e070b0399014150720b007845405940304020610b60003148143c1a00d00c241c0d04c101c066a00e07089014203c4c011000010505100d0b5548000840c118260040410190b4000002001d449642e00d03410504640d20487c0135a1000c204401c0c104414020101d42ca075041c4003d217600d10346922619900c50140d0002103040500002007241c151007601104e0180501000501c0141000e26050510340e5591106640c1401302d0350010a040c6000b04a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 116673012 1250 116671762 116671783
    0xf0d0609150e0702150a0603031103030c030420090f010e01060504050a0e310b070e090708060105090d050a0b062d04020d0e031803030307090b0c0304031b1502 70
    0x240c149090b03040018546810300040c16180c00d52081a01d01000d034100f44d6480d6100310a8900081004d80c9146009800003480c03048240d400d400c03d1040100300d9440f1001d599120342c1113420304803581d2421440d00d00b1800c03188816030b0810214420045a4400855414100c42c4600001c030340c281c0e41e07440101c490380a14000c00d60720a0032450104103044c00c02051030b8210030040d600c0800400d00341610764210701d008181c0311038082800c0740181408000001c06900c101d003810b28050b40d50140c0e002503030000c40200441c040c00181d80c046502c90b4402c905442050101402e204000b00d0242420f594070b00408a04540002070300002813824200b20900300c040d42511040b100c81c40c03141d680140500c1c03003e04401c03a0002d6082c445820103088a000788000b01c4c0c0054041c40d624033798648014070701070500d40014002d40c070030800d001d5119408030000084034015080540c4400d00b100a140c11031065a001074108a40d0380c090441c0358030030341c2190046642019031058400e604001c1039880c1c2ca507400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 116674262 1250 116673012 116673041
    0xd030c0c050a170705101b0c170a06060504050c0a0318020618040e3702090a020a030b0409031209021906020d020f01230603010f0f050601090603110301090b03120f0d0609 75
    0x1020114804048012094140305802d2311003002d846a100c0080010032682030540b55000d00070443c1808941e10402d000b50400342c07014440c034600700495940c1761041c41010010550b82d8144d1140d4402201c7c058921079500420155413444c0a804002c088441c410186101341d00e0450703098040d180001c0c480c152000514000c50a8402e03820341308900030f403a8041d03400e100c0e0543e05444d0040c0c0d211500030748224140303a40140c4868a00400404480b840164540128500b04150300807980040240c0d082007590407000c0380032030403031011800308038464610440c1008000000701e801c94020524214803034080e400c0390000100b203c542403d89100c070030134080700b042501045041d0340c80403901a80c0b003e00580081080d811030b405802c1112208441182e03281da82d442481034070b60b400f003449001410245801c2c400500040c4445c2090322041c4600a80c2c1d0342c0c2e805400e0810b45082c0100024680c44800303071038441d4a00d11007070015a0120482c00341d00d618060340412400c400d032140030030403000d07403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 116675512 1250 116674262 116674277
    0xa020918100e1b010921052416020c09010308090f04090b16050f1801200c01120c020606040506010903120905040b040501080604150e01110d0510050d030c0c050a17070510 75
    0x900c11400ca41d40090015202400b903123640000450312003444200b0103403046a001460b1802c0b03031004420011941034003085400c220200c1549958020306241500e03004880c01e50b9503208140050200d900b05a03001d90498200a100740038445103000051049012045070782d015048a0f0301101c051280c800e901106a000307002001d014003106504904401042c10f0031010500e458418210880326100328801320351158813a441e482d64000c551032007091400303030300b0300c401402c00d20702030b48412008242034012907070340d4002803032a80301d030b0400f5008540060b8810840d0b030000308000d00d4203480d800b41d240241c0c00c005c40c038040c500701445183d04030358160b4050016521242d079880c3e080304001c1864221503440d00355005a4240a1040e985540700320400b440c1e82c1c01c0e11109010646000401d11280105d603070a042006880b01451145982c0c0d040c036204100320f1403803911090380a0303142c2000c0e800550302903011407041c05100c0050840c842480c12a01500d40d11300c100109030552540001c00035501 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 116676762 1250 116675512 116675549
    0x3040605030901060513020a030605010e1c0503041e0602011a1c020a050a0b04180501030c050d06020c0d0903111f03020d0b040509010506120a020918100e1b0109 71
    0x1400107542c1022841001240c2d4640c0c0c1c000081d0456039103101ca2214a60005035500c040da0940308010041c8004c3c241050b80303188000015000340004808580e60180c10005d59081000c1170040303a02a2503004038440c1d990600061020b40705143c2c1c00791401641c680003800400983e407412403603140340000e1061a003804001d1821214a94070a401c90304444140404070f00da40d10300c00140050100703072400315103a070b1406680072402c81d041c00c910301d6617510781401400030807003180700c2c1401d0311003d6443c68032008552034894024400c04c001003500b070041b203240500090f13002c1248800c89005d60603044034480010308000c03981c06404101e0003003400ca5103403d0340150081d0082c0960b031450000005044410001140a490044640c4082655500b04200051038514048810700000350b0081000d03980b01c1d80860f4003442c000e0410480454103900d0388480c45801c0005180310300411030b040c4034a2041c003521030303560403403880300f104030b006400c4040c000d65115070300300c0040341e060074640140d0780354 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 116678012 1250 116676762 116676767
    0x10809060606071e02040c030c1403040f0209040f0c12020f010512060108070c0501050f0f100617060f1906080109151a04150c11010507050607080919050303011d0405030406 76
    0xb40c0d40b40c444d800ca0454040c10300560354a104021101c041030b01d000c00e105540c21300050401800090a50745040e0a0080c000450700d10901c0d0b64541c0da0607501e40c0c16588540c2050130482c000b2074802840001d10450100f80743c05503925500c2d25078825900200d80c0c40500300103556034090310055900c02c11301400010041d611031a000d580181c0d180c14404078070403640e2161030075501d0860345c000346a00d0103018070201c0c805080110ba80311911004440046080c07040040011108040c503403102051400410b09a07983c04020342d01a4200604070380c41c0401071500000303c40c0c181d01c60140803034a604000190404103024080c032a00c81c4c1080348001c2810414002074600f621041001d000b5001c1c0030102c3c05040301280c400c01c0108540f1102240161f5242c100c0e0b00d080080c90403410424144903280020b840010425000303651814042e0b000e50742c0c600703014544107038410b0741090095805811001d2180c080021416105031641807007441c0e800c031240c10816002034500400b250f01c2040308100492 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 116679262 1250 116678012 116678033
    0x17070b16110f03030703030b030d050415050703050415020f011b090b030907090c051b03160201050c010905030a0f0801050d0b0403210501030311100c0e0f040204051e01080906060607 80
    0x4000340340b4940c10468601007072642e0072002044001c250384000700940c80ca0208000104076440f4030b40180351a041400b41995140c405111500784100801d0030300405004405a90162483c108901004040101c0017559200101100c048035480c0020380c074251141c0d440e40400c290031a4890710300d010700c0d2807159101e41c0e000800c84041401484000310701900a401345400c0d01c405030783c6d0203131640a4240402c26003d480c1ca009038155008000328901c5195401c021105d440e02401c21030307110611105603501504002da0001c0c56404002180391000360801208503900e887c3e0b0307681c800340d80e0302c900521580d8461040701810241004000600191180d2040444134840c0300804400520b6000c0140070307640280c00072800302e0001010309032460820400d80c0300d50f100340041403000128040024154080d0501c40901810301c4030344d61003442e211501101d00400c400340c00c0e84140c000d0503889880301d038050001a800600541d01050802c1d80c00200700d401035400404184ca0052036544280210 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 116680512 1250 116679262 116679293
    0xe09060924090a060e2401050a021c0201200301080304031101051909030218060d140c0a17061303020d03020d0b100c030206010510020703080901030b0a17070b16 71
    0x71102216002115240e0b140b89500500711540e004c248182012410f1482e14401050f0300b000308400c20040040141c14406141c503001d081c20165543c1060040403401c045090401a00b00c20031258450009a4154065164040518030002c10b6101d6000c00c5d0304035100c288542404c0d45d105110600110381502241800000c1c141051407a0617030f19851118040d2038180200d02182c9440380403c1907080000c0f05015440720265916104c0c500f02d000207000354104000500403001c0c0002c0024081410051a085618000d050000281e5076000c2003000d580341c00c0c1a20501d000303140120742200b818800e0302a510742d040c0c000c1c040c45003c2c58822002500446140a0310366211a0081c4d43ca446100c47c40200071100da80c2d07003140015a0401900d800380c10fa2001d07015038000c04641d20826130110b03510050340d921003143da998124800040340505041c6000a80c42060f18100240b075052289001040300101d1042d1307000103545101607120750180d0b0801d0700b64441c102c020000041c00003800360005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 116681762 1250 116680512 116680561
    0x8160903150f1508031c27060e0f01020318030403020a2d080303040201020f060106050f031008010606050a02010c020606013213050406080705010c030f02120f03070e090609 76
    0x30004030f2070381a251070b8041d44201159000000e000c82003024107110b20300302c1a80c2010500040c5248000803d0015403805010840e54503072260b0750070010542c1040580c5041c4400306c840740308902d282c540c000c1d4016106d072039801e00d0b60344035400f103403401200303690480390000d14a01c2078516003411180046000c081c0c40c401c4c0c081400b80c500c0b107008070068203005010305c90000c64582ca01440064602589142041c01c10783c0302400401413254003500302c1e404407464044050702c03500e440300d008c241100302e81c00083c165404e1400c04034405a000700035118061095009001805021509036100c500036200c2ea80056105000401c00754402d56200194824004140080c074140c66100c039041e030400c558030700d96100d400d04104214a4240920740c082c0082c140030b4150b66180c1400a40002c4503140000e080c45649400818124000c1c0010750190f071351007079029a0340384000d910240590049880a02103210307021800842c0c2080b02d4000c0c4555005005c100303250311f070108030415440318400d14811 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 116683012 1250 116681762 116681771
    0x90f130602070602040b03040308060301090213020d06030215092701030602090d050109060203090f010212070305040c0e09071a1801030b0a0906030b0403090602060c04060e0109030f0308160903150f 87
    0x60f0b0910040c001445424441074580c100b906d801441400007800580c800e07030502c05801c02507a2413603412012070380d4031240107969814001d640d40c003034000d42e440650f00c2008d5191000041c40c2020040618490440f43d91002401550102001ca65010f20b015101c1701c540740107200082103030340104030078003000b4a08400022144d0710f89094900750001103440540110900603400c100b00910b1540401d000029401c24890080c0d030380005000a00c08030806881e040484c080c00108803000c2c000e04458120240b01e4074040c0c2c40d19030303036001d10301c02c0c0b0441035074002004400c0d520f000241c6000508440c860805440d030280110301604a60641940c01031150700d0004191060384110001540b182070900c000d450a4240688441d01d160701403010b5400503000c0000303070b244210445003038401508001040c550000d0040700c1680c040d0300018001d464440c481001c0c542c1000e0385910400011845d0034411700c00250441c1c01250511005000c0800602203003a0811107801c440451111440f0004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 116684262 1250 116683012 116683027
    0x10f0e060a03110c010608010c090806060906060c03030f0603070e0108101d010c09090506030c0a180914100e0319030513021903030e040615050c0f0313050a05090f130602 75
    0xb00b2681c031241c0b40c07130f43c0c1e81e640e12810006040700380503540f044445401c1129410745020703d181c1e12401d00501540c40340e8140c0000540c00d84e0b50070306890070001c2020459032a450582c4001418810a440591280c4900e980015440000302c50312030580e6000b4025084030142103505d04003814070034220071280c201040034000c1c400d00c24030401c0502021961040c540c2c80c58516850708560740038210a0080d08000c52201941e210700044d84110b0700562009002d984480e2a03030402400652002071080b400101c0d90805071000040801150906040c2044400c61000d000ca07a207100b20342070007101c2c0320443d04030542140260700c8668804030784070034801c440d02c00742e00248030352a80c02000c0c4600070001406005140d403100303549010030381c00d0b40c0400007641400a14488412500209030400000007582a15004180811003d80012100b00c9484a6040e1400d41030701446009850050241180000f000e260035060383c0e0040c031410482c0700c003e4644544200c002e04d0b4a400580e200340c0c0820002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 116685512 1250 116684262 116684291
    0x503090f06151e01050a1202040305010207210f08060613080d0f080a02070302031e070b0a02090f010c1115041502070e13050c040c110303011202010e010f0e060a03 72
    0x110321a004801006003409035560800c0907258108021500d80321541580f4002660000100c500080c81810002c40c0c401000c00d03001c0213445550030041141d400400e0480421000388446e0541600740c104848959400c0034007161140030580401c0300013081180410710500300780c8000d1007407600c0703450175154064956050500d0300c2d54800c89c0b50001062640c4000c48a580000701030b8000c2203d041c158600384040d01c00039070b82d0003080c2c0929000524100017180e0010344c0c508070348159500941c000d17484d140074482c200094010103a15401509004803102d5258454504242c040c0d90281d03280130200c0c0325809002d0442c14915200000311000c1002185051400304c20803c894400d50080840038146511440071140151612070100361450a11002035000328180d00c0c1d019050301c0024501006900071104c00301d40d01940c0e1040d000000000c5100320144110182c228000c0c1c850400341d040d003e0044500390715482a110008865800301d456500c2c10800034004900c6502d8007141c0828084141d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 116686762 1250 116685512 116685523
    0x604060f1517010305060c0a0e0d0609050606150403060207140f07080c0a12140c040c03020702040c0c021806040f05160f03020c03312304060f060503090f 68
    0x19000d41c000c0d101c116007841c0d40c0300b10030b071552000d640e041070815451036171080e5440030064942d64041c6404a01c0d943d0f030a1084080d4003800c08024900300e8000c11905140005100e0508207a60781d00070500010020308050700c01c0c071554242050540d00d01803842e103d11000b904495821100724507480702601c5e4480003004000e609500140180c1201d41c6404001440d011091a410b80245240c110400000078840c42d100143c1d90440c0840700c00b00c0040c6859410b20304a004002d070300c10720702502c601d42180d1590182030050700c00d95040240e0400c045040e14910b0400704002e5000e060b1210700c0000b0f90301c0303603001034014001034408121850f00e0203590301a6030003100c100d07102014103ea6000001c1e4480c2000b04540c8440c203045250001080c00107450b4801c0c000800a024100c883c0d10200b600f00351409118142c002c1c2d0002c802a880e201c0507620a2404002000c40100c000c5074480070b4a0f140c8181c4040b1031880030b2940c1e8251510318203540c3d54100401c03054482c01490903a240c00c000030b110 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 116688012 1250 116686762 116686769
    0xf18030e0303070c1d130f060b010c020316030611030408220b030a0905060609040804050103150f032418151e0506031513081e040e0a0608010209010e090604060f 71
    0x8040003040e25400031134070113081c000c1c031030144007000c00b1060300487c0324200712900c155000240400d55460042c0182c5010040c890300940510510001d00603d010f02e014844c1030f039120b003005110b25501284001c1882c04141c5c1c2c041c001c07103803c0000765100482c0d56032200503d00a1101100c05580d94224402c80d074104407140c4400075100c4e00e200e01080010302c03003c2ea1255048848880c40e0400380c40d1848503016a000d490305040c2e45260302c0303600120b0001100010710103a401c01408a0300d81c41d010040d0350b442945a2030b80070441e514040d03c8419801203420310000318284d0030503001d89894260544110713803014100140d880c0e8850390380d405000d064a04404840501245074148a0141482c0ca8203200c0c0e14900d40a049050184090001c9030a110440d0000c1260ba1220201054056000a003020601c00520002400541c8403400c1000ca48205400c5800300714541d681c6000500740c2c4a101c0c1c07514001030903112b4480c0c09281c80c06040b900880041c000182d10f40c1c880700d800d20401d030280c2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 116689262 1250 116688012 116688029
    0xe0606130f0b18030a0f020f0d0206031003050105070c051005070509030a05011b0c2f0904060c0206010b0418050415060b07020a0f0312031a040603150f18030e0303070c 74
    0x503400525624034140d08000c0320040d8000c103103903042500c1b44411100302290003889a00d01101c2c0000507901d120101c1ea5064004007000c0c0e40c1d082145009180d900d0a1108071040e5080a0001d10814019119884050340050180c0248040c4e6a80803006100c0140030905000302441607c1c6a80c60804c21080080d00c590000960103000c051503184030290f0200d01c0c81000458081d4400244c44010415030b545070070b48403214001c800d45100d80c6245040000c281c1c019441c5401c0100344156500001c00c80512a001d60301c084e41c8541d100e100d107110341d0007001c4040c00c040d151081602c4142e03112992140c06108071036150190101c418043c0c8106901c5007c40314004210f90041d4a801c00b628401840d0707001c0c0141c0c1c0c851860b5141403885032082e00b40400d00d0381e100300c00c850341d411a010841c2002c000800c10420700c0d4503447e18112030114403410102c41d601c1c10301660b00d0030030240f0400c10001c82d4096041c0514183d958207c8a5240c4038181b160540000c0c00840700050301030088201900000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 116690512 1250 116689262 116689267
    0x22809180c020105180a061e090b07030e03030f04020f010212041e1e0b0304062304061b080126071511010b01050d09051908090a0f0e0606130f0b 64
    0x7400003425100098283c242d540040440688118070000d103403041d03507030300540c040741c4051004054650b80311030540b80c090050500c7d8103001003281000d001c91003500d6507101000400c000c80a066903d01003141e00481c1001c404001c50054075000c020f04050300700c144110703043c102160324000c0443d0040d900c041003801311183c2d454006d007489503141c0c02030009034110340c480c0c480e040302416000e0800e205032149044000041801d02110360042d08681745058450220411600d10780140010120f8040d280c0383d10780400d522550034110341440ca05121680c2c1d200c0e05900b002c00480036a000465802280c80d61141d401c0a4184107003d5000284560200100990040e15000c0d10842c2458001441c82e49049000c0c3c00c0d0f0b82c0c005042c0c42c0e10030b8441c000020000054a0032038500f401860440e11000c0c0044800010040c07501c2c001c044403035050340c1900040303a503181c0450303901442d4003c001103c03105a00060300c9040c210702504081914102443c1c0842d600c180f0103030001c040e07410006160800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 116691762 1250 116690512 116690531
    0x60d1b0f031a030307031107030f05070e0105010c02030c120102070b0f0907060207180c09050409050a0c090b0906090403090320040c211d03040603060f060302280918 73
    0x94802d45400501c440b441d90301c060342620010343c50340700c0c0080c02828403508002c122075441c400c12900f4080c40c0e10100d60013028a66040103513581d40c6034450a242c82c4d0b04440040703401e510500141c483c1c59030240041c14119054020000180c0300b000e0440c20565003801044085400d0041d05070003443c03440c0d54401c003400c200345d0050070024030350007010541d030040e6400c2029600c103d0410300a00c11070a800140300031400812a603c0394280c0c000f90340a41010401414428003190049025106800038140140d4400000040c0d400380c20086078071051080000700030b404d00c01c5040e5446072080c54600809900c0307036241d0980c82241000200c1c4480031400c0b5846d00d050030702c161030ad41851f6041c03023414441451282003000e06500b19290b0490744441403403201d44000c0d40620a40d98084041c0c035140c0f9140c400c000c0c02043c40b40300d8404100c00f0038000168490080c406c55160241c081c2400520400702d04803064059030301c5032540c0802c500c1a000283c0400405c0040c100902440000b1824800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 116693012 1250 116691762 116691767
    0x80c0d05100f06140102010b0a030b090a0b011d01050a050a03020d0c0b03070c050c010302120103030e03010e0f0d02010f05010303020307200402072103050f280606020319020a030e060d1b0f 83
    0x400f0102e51781568500522038000740c1e20400c403072044a52140085049a4540003002d00f0803008150003000404100004070306140c2c2c011060780c11a28400d40400e0a03a40c0c0d104000440c1041d2160b5504018030700383c1440507040101d0310100072070103104000c90190b580e103440c0f600d0b40c0c230444a400000704070ba005a0b04000c8240001c04c0150803d1130294145400079101007111a0180700050a102009940b14000d8500b9008908844280e8007501c040b1286880304684410700c180f84000154a1700e080400d017244188103040c10ba0f5050b6000b0741c00d050343c980d55407840d00d00458a0b01182824040d0165069840e40000d020461050f4481d51a01d00206403a46c260070020080078140340c180342c10014003c8142400662080404001014000f40c6650018030740410f0544c2410241c1020804595950000001c0901150707210001c0c042e0300c00e241c41261941d1148800400050001503000070034900b140c00341111602900c00052985035410321709400e41d981b6601c1201194902c400500001d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 116694262 1250 116693012 116693039
    0x80a1d0d030504170723010e0615181608040c080106090c200c040f020d0911031225110d0b16170f090c03060708040b0c04080c0d05100f06 61
    0x9003a41007903003840c03c00d95413508001000c500e1030000220003800b04c001c81000350400040e4060b80803e407141c5040118280c6000ac41c1e013803d160085500c040041c0c070540c4100b545500c1040205900000c966520f10111529100076009582c8203080c0c442c00f2800060078400c1000601c00624001100c3d096003030054030907001500d802c0b40c0348007010307a03000d05440085108501000700700c1d40051701c0e080920b00e0000034011a0901e005c03c610346144942003080c4082c08032b064000c11021200039166903110030a0612521800312030310306540c0c1c2c403050700c101011400c1d24018481d030380c0300a0210030000424500c07000d01e6010b0300c50011220610582c000c0f41d200c6281070310b000e40741c050802840e09508261600f000340100000440500001d0511507041c005102d07a4900181516210f052450004089410a840c1510700001d52030100d27410034a507a0484040b602c0d00c5020b04620b000c07040821601541038482502c590203400c580c6140b40e8520311458800c605d2102000070460b0410a55900c0395 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 116695512 1250 116694262 116694293
    0x307091b09031e0c080f060411030102090102190c090e060403170603030a0e06040807061d010806090402040e011b030608010f02090a0510020109120512060f01080a1d0d030504 77
    0x40c04002d0021460b001e40a14081c500c800c2088200078544c6094403184101d5405100c0e240611101404241d0380491000c3c096401103034511408031401d404c0500301e120b04c0740130902681c045811460707004144004601807500540744405125920503e000070340382d0115160320300c3e801030000c00c01003581001c1c0070400d2040f1001d40b0085454004003103552071256410013001d02080c1000e07030303000c0c1d44d440c002c48014050484c00c1d01e06070742d510301c1e01402c0c1883e0094003044902c6501c012038055440303050950310030740c8014200311075915a502404010101c04419180c1e40d5200d00a041c0d080e00b10b5800c40010803010381d80020551301d001200f600711000c886007100c03058010800c05009640b90350341c2009a0744111003995102041c0702c002e83c014212410018501c1020784081c800d5160440060441010940043c84199030b5080c2040140b00f0b2401c0000d01081c1681c002c82d0385e40c0c01580c040038601c410740172700c0080403003110304241c9444060030340e034800240c64404010030441d680a008051 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 116696762 1250 116695512 116695517
    0x5011404021009060806130615020604030912080a0503060301150f081b1e0307030b0a05060f0105031b1e030c031b0a020703020f180406090b063304050307091b 70
    0x81c2404c00c03c000305500405002c89128400c0c0e94002c451054495212500a04411110759104403108a000e512400e0445041d400f007030f15850300080000440002c03d00381a4440c0c03440c1d14001000c203065441e40c00281080f030b019903075511072281d0701107420290405084220002460382d840e11b0101444d205282c20580d0b0500c10312045040c45480d000c21618846001c4c2d0020103520320034102203498981c0700e62028148260b044240300031140c05a00450045a05a030142450601c807801540c1e54402602d0310318800c680c0d080081000e0407860040d000808100207000c0c41050007201160442d001581c9021800c1c00010511154840c44100d00c40216440710915080c540218000380d211076091101a001d80f80300c00c800c03070056451480400e000052644404094101414500c0050112450444d220200d90020510f145018202ca500b0020b503a61840444400500c010165142c42c41c41040b81c4842440042600d5400344406400340c9040000010240c90900300a410010034401d01e00a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 116698012 1250 116696762 116696777
    0x40816050909010b15070305120a060f090905030315120109150f0c020d08092e0b010206131e0f0b1509040b0c03060d061a01090905090604120c050114040210 69
    0x409484526805030b12174100140d0b692552424107050ba10340c82030940750341d03d1080080030001800c01c6641301c0016103200d200c2c00351216843c0d4900400315150804c014182e0ba005000107811462000c9080c010800080c00c0802c00e803000303084082c259185101c1c00c40313203041c5d800c0c0c0c3c1c1c283d100313980c2c8120707502c00039846401c0c40171020b80480a52954482050740301080b0502c000191280400c016460007640c1610b08a40f1001750304030101d110741c00c464221a4043d05082030300c00c4542c400681d0740d00800380880e00020030303500b80c0e40b595a4403190029014051506d042144045004d50f9a100030450041425a40c90300e00700e00c12072403011405010314490034450043c4008964401100d0f98800c1e403801c4201c2e901d40324140022003042c0c4c114001410076003402c0c0804080345421044610441007a200e21100c251500c040f40103581c4105c1e8030049941c0007078002404a0081c41c404500240141045100c181503a00d441e800d40340d000004d044403009200a120440c01c04c400c80c0000360030103180c0500d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 116699262 1250 116698012 116698031
    0x9010e030d030f2306130921021005011802071e08030f1e04020d0203010b121c08150609010c0611070b0603010c080a0c0e04020d0c080c070c06030c0504081605090901 73
    0x180c4c68001e0a0f0a0007142c10080d0150b03d000d440d031006061907041a03009010980350728030342e51520000540380005001e0040ca512200106002e014142c0c0c56180c0908030140d80510140c000703400ca014169004c101c00c0e15100c0c1202d81440070008c10a000c0e0f00050380c0c92401c0c0b080900b0320349025203402ea840040c2c00120100c2c3d5911603101c3c2d00107030b04591103e2500124000640135101900740c00303501082401611a0504c40000c9000130400140088400c1325443d000544e01aa0200c4520b02798840c2440d0301e444d54034211f001060308a005050822a4803069280c0350100c500820b103a0020700400203056052000e801491360380440110b000303000b0840b110380c1c0203009100240840c03800540321b00c4e542d01e4050040103420340b01003024001f152148210802030010300200c140800105910501080050307514804603050907400c48900840701349004021001480e800c070611041000070701010500800a001d21000398000989020102c0c1c101420060b0211000c0c00c10181a032501ca02d07074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 116700512 1250 116699262 116699321
    0x711071e060e01050f03010905060607020909010f0c0e0102030d020d02160804080106050a0311090601020111160b010819030e0102010f0c020c1302031e060303091206090f0303041709010e030d030f 86
    0xc0c0d048d5440c40318041629141d000114100e03014140000358403607a18410031046020540c09400507204180b802c1c00259201a0240c9909601108003070042c0c2007005508404d90032500246092002c80100512304195824000d1042000400441c0c0030400041e003004004024014413000c1d002c110341d00381220b0710f135680c1e140d0700000c80c40c4d00a0007000480002b4201d603000b0350103444c840300c010030030fa40e40d0900c103203401c5441c0240850403240362400c0000071514640c00100c0b54580e26500075188034200e42602d0030343e001c02d0500b19050445d07480301200600c415080c0201c0070905015002009810490b070100100f40010000341c5000078030500802c0f03101440c4400c08244e0f0004488150700b00e1f01d9620119086200c0d0703410040c1c0002030040080d00c507100003d8903034860040319094802d40752071705410750380300d20090302c0181c00c002c4204261208506104000d0490a038141403420340080d2100100781410007c2c1d503914042a61000a01c0070f01c000c0c2d016000159010704507500b00340b420038420 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 116701762 1250 116700512 116700517
    0x8010305150610030f0f02040f090624051312060903080603160b0702030309090112030f0305060307060e0310050103060c0905031f09020105121911120711071e060e01050f 75
    0x140402c040c5c54001c0c04204120503480344406000c100d8041d983c0c5d940f1286200210219031261000042c90301c000000c44031105403404414503031a04094616415450048416800c050030095010007107110000300710350b07a4490b401403207100e0700700411444002d0401802e03803480100070602981091443d07260b15200704004400381c810007036500e41c0b80c00c030343c1c00400d166001d036036200c68000307820074004910504000c180103a214441e40d58200c0110024070110152041510712a8155011a00074010280108600c040400014007218480311a00c119142903c0081e8019188240d981c03410241d029071182000b80504010350041009050701c9829507001d02a91a8000e5219505d980c070904580c410341c21030716484005010303a085800c002c5881d800caa0040241c401c1f2503481c05091210b203c01c0c06094694481d030490521150740c0d101d1806852004811141c2c8405010341d00740425589d041c04100307496040d01d01c0654140604025020b84100d8a00c1c041c507040c03102c1030101c581803041c0c9804 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 116703012 1250 116701762 116701789
    0x7030b0a0302090a15140f0303040315020a0c02040c030b04060605070c1503060f0b041d01050904060c050c031210090203040b0a0b060d05010b030f06040216110d0b0403080103051506 80
    0x850220540c0e40400800c010700b80402c1e44610034440c5c110000d4100b030300400181394808129401c98198062004240d50f038801c612005140202c42a01d1880c0100168090701324840c040c11b210f0340303180103540020200d580310640540420340d0740d807800045082c140700310006013505081c000c0c6001039039129020680e50034440c81040d42d8030401c640c29410301c01c1d00030700010a00d4402c035400c0661110b011419540060040700205c2032560741032a0100503207800217048031800341080000b0340301ca0311440c001c1c03d4140e0034402401401c000700384c04d50004000825103800c1c103000c40722142c1440110171000141035480000c07140e00500c140404101814250b58102e410403000007140c1400c4000b107100c9000e040d5074400c0c414941000000ca07100c21500840c480c0402c64260036403a03503800c00b0030003280030f40011a100084071002c20030000f100c920110440d03060040c5400c00c03100c803d6a524401140480e8120b0000d24600010000c002e410840011681ca8410311a611498583c0128000000455 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 116704262 1250 116703012 116703019
    0x6090501060c08181906080601020102070807020108040c030b01080c04050a0c052b060e0702010e1c050a17040c080f0a0506160c05010609060f0506030108060708091c031407030b0a0302 81
    0x24210804c501013101c02d0070100c0010706003200c04001c8900001e16401240701d02000b003080880080c60a40c0b06108840034158080030f040e0a109454004484081000b030086810000d02c20b0040003184404001a0081040b0b800138a1030000510a200070303940d000c0d024441503800c0641b6120b540f6085019180442305181c030601000ba641002c00c2d44040005e00d580d64ac41c1d1130046d02041d141c9412011512a001d2500248085a48c07420850341e2088100d200e00181ba01c6100080b00c024481c500400c6010090f140c0035481d154940c100003810501640c0445102c100c1000406c0084814026040c203a51110007a0050700c000e0f4540581307404009020584224414501d05250380c007881450840da038214008010141d00c0b000d13180c00a084500900d0a43c00c03050b0300009440c54031604503416620803001030005622120f60a0350a1180030742102818098581d0346150804a8400010103849030f40c2c010464829032603800422480180c08032013014200f413001c07035445d140c1c1e4000f90112076055 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 116705512 1250 116704262 116704267
    0x1d12071112030d0c020105040b1f09020d0b03030c070501020c01090b03071218051605030d0e0f030a020603040606050a0b16020904030201020c0d02101406030a0303021606051906090501060c08 84
    0x4454680c218400c1e0074014018a20745115041340d9a8154005031045204600c0d414107078451411780f41c1b60440b070128121022060003401d000000141d0050541d4010061b4081a219081c8001a0540e00700ca10140d0301035004d8a802c0019680c100245400448c0c00e01f44035a003181454422043da01c001001d4109108085207012000350040e40310140401040380449085081d03850016101c80c090760701c0c107075000d928142c04540c5c0d143c0420780c2d804103012511540b080080002c1030100c422020010640c0c5070280810440141c1c82e203a0080d4490ba1242c10300040c00b0b42071008000358600c15030055444200140224001640a1100110500c0c0c0449489181e40d650346070880c0640b2030443c01c0c2c0054022954202c2016400180a089d40184070005102c0429081c0100b81c800c04100e504c0c0e5450350143c050080420301a6009068030102c1d044125038045442d145c0c0402d80710140d9880042d010009040710725030100344140d8015001c0e0000500541d40b6100e4010704030039003240060f0060400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 116706762 1250 116705512 116705539
    0x1905060f01080a061104030f0506100e15010806030c06030103030f030501060201020a170621031b0105040b1b0d0203010b04080c01030509032b0f02070c1203050f0d0b041d120711 78
    0x740d0161b400070b40e4000c041a801c0c0e9100e107071254a59105442100c1c40c0c41008002168000000d00e08034401c45102c10020400f83e52100116100c4402401e10341d094010800c40340d046803126402540617501076285d816201a101a0003003c032941688082d045900c148200190700780d10a03068000d00c00b084108488a84803030300012031039407040e46c0040c0c0040c408070702424503000c048040c115014425607500603080202142e107080c0d450803100207207240d52103800101c80310a84c05088030b0001d01c0e41320941c1000c5aa036a032004990082e040020422404681040041b0b420401611001420b19081c405801e0400c8820750380d00414560458040545400440012500d10a00c6020712030541c00d00c6540091201c1400950104100751400e408581c00450044c020428452410754140c0d202c500d00500c017107610030030390800d410400a80d900c8860171071540e41c440c0241e40c2805840c9020018100782c0c03c407024606139540c4850404080103009400116003804030600c0301e4a001e03a12440c10020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 116708012 1250 116706762 116706791
    0x70809030c0d120b10090503011515080c1903062103020c040b12060a09030e0604080c040b180f0a0f060501050f0901030608060a0603050709090f02040b01020f1905060f01080a06 78
    0x88100031a0304685d032802502c0c0d05039400020074007280c805030000c1040c4055000c600766029880d001358400c100c24005c880804038450100c03513601c8106855823908100305007c04030400d49542c1100740002c0c0e01c5440900444807800c2d00c0030b076950040e0f00440440e62287e034019440d403c608003003921550380c4020308071a5840d0351070b000d480503032904190394407413612052040050160200550000f030286070310f21542c2c180b503412107040c1d404000061400000d0301c2c0070040507069031080315400c070f00c0e6101d9002002d007540c0002c90241100340500e0f03000c1e1400c094802e0440310081c40044200b41844820080c60340c01c40126021591107550322030385d5040500040c0c000d00010b030f011084a11814041102441c02540400152845039098600066440300c0c40000c0c1c41c40580044c3c40e0700100620000107240c01d80c08000d81c0281130064a00ca00d52038044142029103280d855040c0b0000300d22801c003040000d00c01640e10080342d038140304081d4144209140d039165245401000c19907250103800c080388 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 116709262 1250 116708012 116708021
    0x306050f060603071d0310060b0c120c0a15090605040602120609060f01111204080307060c0504060801090504060b210c0319020907020f0105010b040e06010c08091009120308070809030c0d12 83
    0x4071558001d00605580d0b41c0f0082710355000320343d420401d000d12180141b644004600300c0e00890a400020881035440340c94082803450140c00501c01a95038054040001d5810701400b8401c501035640180c40d1960807000030b039840002450345104500200800015603906518500f4182c801c2c43c1100401d0200c1c00d1803460700c02150710380510824003103000281c41d81e0020007445072900c1280e0911001844440944503805a4001d41010821800051100d081d030755001d158414094032000c6100034045012507400c000f4041206001d00b084101051640700c1000001d03007011041c0d0080404000d41c4071010450006007100a21a00c000d20104080364400c2050703840c0510310704003c0026517950f000a800d03d611601c0b81e1510310984c000081d00560081012180d15600240c1c0f262400e0709290070454613900800c40c1e4021b108180102164100090801c4030413107119031503e0741181400c21002e0580800103040a071150b1042141d07941c0c0030300120b411081d43c0d040341045203003c0f070304034422400f40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 116710512 1250 116709262 116709283
    0xd080103020307140d0203010603061b0305010305150402010e040507080a180b0601051c0e0a15140a020d02071b0f1203050a050a091707060e03070b090f01030204030c0306050f060603071d03 83
    0x66027001d0011090000c0c1d944251020030844001210701c4505c98415000d864003440042d080c0d802050100386818031350000154403d00c1490699090780560001038200d45060f140480006c1c804010403180c0ca015110380802582014030341422800940d4900d0105040202458104100424621a401d50148031502d01082c0c42e542805030140800c9103654a021002090790104212103461076442442d03c02c13017520307150745050f8072a2903585a1004000e58401512411429400c10145010400d02c1c008114007c00342204440918038010309a08110943d070006070014510465100000c0c0e041812079400c04110305041e6255462940103a17000740d65a4000c8100e449064541941d01c2c0c0c012031524199511521350714115280c500a05540d0109801511943c44081040c021185001d11984800d460305150241c41c141c0c0b40d65408045174050b40c400c0b04c00c1c42d140c0301440780d00c45007184a00e500160a407001411403a00c0c620090a00500100120b108141400000195141448101480c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 116711762 1250 116710512 116710519
    0x207030f110f3c0f09180102040b0711101b02060904020403050115060f0504172b020c0f13050a0615090905010503030c070308220e06030d080103020307140d02 70
    0x907650311011042449000140400c020300ca0303d00900000c60303411220003501001500e28400140da000c1841080c003009401d1789003801109111515240e000d000a00c0034140702c0344203644882c02494005601c1e0080e02100b8032585098081541041e13100141e5106842e4441039020420705a001140c40c84c480c4800300e98021f07000117004401d010b01500001109407800d009001090f03070300c10040340c040160168001c0014802c01080042d0741c807a803841040c5511720002d450240d0f20a0f4401000a0501d00c1880c0300d4940351510400030540600401065520907140b1466128100c40018041118460304440b01c664130703c04030701800425444140a0203002c43c0403402c1011000010301180001d200e084859802c20002084030304001c015100980f41e420010140c0c01d007143d035125925000b1040a115464481c111600c120022202c003030028614401e0060140c2490301c140350410000e00001014080b1038001000103850019140c0c1c211400b4100049104c109200041d40c050b8409001035807 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 116713012 1250 116711762 116711779
    0xc060b04020d061d060901050409060b030105011517060d030c03020138030102041a1b0d03140708190209010504180608061b0304030f0504080a0b0105100207030f110f 73
    0xb500d010342c002416202400d40f11a03515040c0c4103440120b0300203d41240e0000c1080004101d541065000107030010b10801c4e01040c030754003400100e400c40e5005da02c01110340c03080d4a049400c981c0c101560b22400b4580c0070001070f0030310304040441c00c0c00701140c0c00142000900095a0f0505100b90301680c0c0c0c00448009000400701c3c1e91040c80110b100f000040d1484803d040c07007252492905108036401c46641103140204e04212a91410113030b0019611000c1c4035802e000c0b07255504105126454224030b068400042c41c1c088a490200d01504c018050f00c2030220076010301485402c00c05808101044541c400b5907214211070040700d06024541c014401a2020f005d44050014070b9040401503c2c1ca0744100d1b800341d81c4002480100524040b040880b4050800c0800c0c04240714458524401c40c545c00d0881c64142e881030702c00d24007940f0000950340c2c1c403d1813005218518000f4200b491080082c401800486d0540e140c0d11091500fa2000501441d14141d03000c0c80703034031400c0012900c510020404c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 116714262 1250 116713012 116713027
    0x303080601112509050702011508070e041104020f040801090515070c02130b04020c030c0f070506070b04030e1c020108011e0e13020a06050705190c0b07050a0209070903030905030609030a0c060b0402 87
    0xc0c049c0600d14800d03070010b801d40d04040344000e000143c0101f2250300800072281030b1100d4459400241c075050072913811640030002c060202030040d008000402401000180c026860f00345181410072592400094a101c2401e1110250344030317a001c0300d1190111024840e842c2001c5800340100811481c10750454004541101d0315000030018040440c000d0041e2404541d2580d80d00351140181e00400d50b0100301807000c98081101c00800c0781d4814131a0501c2541c071030f5800d000501d500050a0781d80d0010803015403040071540c1c0108841e0040100f0588548450841000002c00b41518003840d604058440001101010711072800d41d09203401504240398540c0310320300200281d10281069840c3e10821a81481c4100c0204000382c044d0303000040d0128107400c103a08048540d00c2104252110f1003140c00c80d0025a4415207102d006070742a4403410344c140e01d546009402c4c000240d100c144690003100400c01c0414000c411200004814035000d0039040d40c034940103000b0a420001540c100d44045500d6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 116715512 1250 116714262 116714267
    0x20d09021c060e03040f180605150702040b01020c0f01050d14070f08150a0308070623180a0b0105120703051006060e04150333020403030806011125090507 68
    0x40d2203000b403206100d080880d9a01131303030b00c1c41a803084421403034894408001c0e82c80000798507030310030004500201e0b90704da03500c0005940c104052510101000c0c005260411840c0510850700c1c0303000c0078005000d20b46540300010344044403250703070541400303000103210045548551000140300c11520060443e07080142004040c5041c520981e008180d2800100b82005069003410b448032100070900f40c130147c210380e90302a240e00300381c1003250380700d03210201000741492121810349607214484280040e4170301240c8407003407044100701c201c03030a400c015130303110200e1080d076825815100f09580c42200b204a20b4826854a0070a0740050058000c01803a4034040d241604400204d0755507079606c2004074000710820007181c2195840c0352400e07401d10340c10000604d400b600040005600303000740f0304410852050311503200c00800a02406540010306000709070f001940660810b400b840c245454112a4200954510f05803802c80d0f0014182c0c0c56840c609800d8031501d802414420406115038200b0100c003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 116716762 1250 116715512 116715559
    0x1407060612140f06060103020d0b0303030a0912140d0c020c15030a0b0f060a1404120c0905010e090303010b090f0a0303031407050a02150a0902030a0309170d050904020d0902 76
    0x8407900307201c00d62141c85550002669510490080c800350995440705c0005600a600407041c0d881d55176101e0006980707036903060000d0b41c491440b080d400314801c40b081c0350150080032441c5d407450a00c40b444031051003602503481614525060342c980060f84070150241640703481d5214500e6503200c1c003501c1c506d40001da6200065402450041001e10030170303896200b0402d0300964011020380019090000b030481500c01c0c05040700104121124a10302601c0b1900810403804401c0140c1e2001d200240800502c1400d2080c42e0044c0100c2d0244030413030400c2d0790402d0b260311040c4544008540041802d00003a95171034080354082400a000100303055a902d809000303002c00304843d200070120500050b41d000d01800071581c85d40c0340c07039010300b4001800125403000d0450140920030619503c40507100180c038200a03a080240c043c0d141c0524aa1610015165540100609580540009210320740454110702514880d810172500507072203420301c41c0c3c032400601030341b480603501400042200140e021190038 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 116718012 1250 116716762 116716799
    0x15090a060917010b0105030402060904060e0915090d0c0b07020c040614030606120d0c030207030623090312070e0d02090c0a0f0503100e041a0114040f0e0c0114070606 73
    0x90402c0b221009212800c0b502e14225050201e00d003040007900510b005001028002c0d07000b0400180d040d11a0044031003100202d03443ca42c2e035070002420004103031903000d41e2980041c40d240280010a030881d0001c0c9813410844000741072085c542c0220306910b009210f03040d4900f074003410401a9030750350707644c10070a000890a124040e00400300414010b0070000001d00c0c4201c00e0070018807901c414914219081d10101d54141d0450184d40008000200320f4042c0010306650031840c080d1044108104003140d480240c440c1d08207a01c100605940c0b00c0c10001180d500c0400d50901c0411201c4a030003180501c0e0520348000c0d4007101c260304012024203004060001c031002a95000700003021030200352800c2c0310a6450212a0300300d26010041e1015600ca02a17025204240600c2030030b0100b4016101161b00b82c000c80303520100002c480045040c244a60102c81c02d2542c42071040181c940c1a0707a890320313242c24003d81002a410301c0c0c555518036003030866060a030b010500700680355860b03020900701d441c40c66 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 116719262 1250 116718012 116718029
    0xa03050919031d06030601090b0c0a0209100302010e0105040303020a0602090112090b0702010b01090f09090201020a1505070e0604060807030c05041208070b0108070602060703020310170d02120c03040515090a0609 93
    0x107816020606000d13080e240308400686130104101d081402850680c0c0141450310030354800e00301540f0040e00c591501e58040c0504011510441e030462001400e0f400e05a00d80c14104141403100300302090b0700051000b00560030010040e5145481d90040300d003030408480c00405541841c04100400080c80300e440d01c100401c1d03000300301302130f1004011903070004603104807901c44885a50501644203554000c100c018814012101c0c900a50f917100720445c50a05080341095135240b0410007902e4101c078030f4102000c01114414170b49410002d01038440b18010f40008201903840050f030200d14002d030100d83c00782c14009030388008160f0394a402003142e4004501214400010000010000f80c0062814190347c502d4010b0446580c901400b10020340004214001078004000c0028106a44585001035150050050605102c011602a1070000d07103c07403000402108011800180e200070065030256941150785114101c01c051a0345e1941c00749a41c0d1650080c04100000f4503160445104403c8a031441d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 116720512 1250 116719262 116719307
    0x12030f030c1110050c070605090609070806060d1e02041a0114040f03120c0803070503180601050f010e030111131d0402100c080c0601060201020a0905150a0305091903 73
    0x840c1100d18001d180881d491540c8543c1200e1070400035600419409143c0345002820f05016403100820368070150b0340c542e80e540000090013120107040c440f4402620121000780b100342445404504520401d40000c1c001c3c9200c1140e40490003010840014210780003841805200011030300d1228242c8080300f800c1c049400549420031a268a005a0702128500030320740708651b01c2c6450b0310f100316a030502d2010400002c80c3d121000104481701860046c1299070f942501c2c0c2c40c101c103c05101c250a84510700c5598003400041206545050949038006000e20b8580300102d000c001007805044641001c0303880d00320200d800103003140c2168000080f40c950a0485580b04008040840c00d220241e4000e9040b4451a0300548940d0041982c9030032180300311f440f9850320414200b0036050403403e07003210300140d400152107000b190f4800c903808068101180c042c10003044620940c80300b40b2400303040e80d00345a12000000c040345418460410602d0081c0649203020503580b4004100c07201102d20f503840d401c001e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 116721762 1250 116720512 116720531
    0x50411092d09070b0306060f07150f090b19021605010507091e06030213052701050a0e0402120a051b04110f070311010f0c170105040b1f0912030f03 65
    0xe4200090054401101a00050341040002c44c915400240500d800c00000c000d44188495848003d02d403042c001d01800b2004140c1c160b012080e122102081c608142c10200da001c080303100030001c96005010070008540c10017090101c2401b134000c010403840328203004200d8205000040d08410302c0340350203a80e6100308075247d58a844808504003001d2503d1003440100b404950700960003031a0008041c5d00c480600b50f9140002500c10f04040c034980d22039030740f012581201c40c1855240e2400b4080c11110340300050305246191840c81c50082c00a80310384c908035140701865031300f480385412040d0840113641d8401a01c80800c041000700d030200c1c601880c500b200c0c00c07042d0007010096500d220008410a0300d02404e0340c600f1101c0c01c55900d99a08107541c1e898180d44000954450088017202540751141d2900c0e2078811088010760517400240103e042c1412302c034590391900140b40b240c2c041c205444c441030b540084101d0350440c00390003140078184080034920505801502c0070049100300c0d0f1b018448160f1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 116723012 1250 116721762 116721841
    0x501060f0b0a0203041205070b0309100516021005060402300a18020d0516090b030f03090306010b0714060f09010e0a03051c0e0a120f03020f04030605041109 69
    0x103691400001070b0424007040c07101c06c1204c241c81c10124016030440b40e03d140c541e41c290806500580d8103c065a011815040e00800640141980705080301d0200c044555080c20103510341c0d149c860341c14640d6036a003001072560350700c60b81a200d00ea01043c0301c500000e40b00d211141d124582135080c06200e40408000207642c00c00303a00844800c400c240021403c003180c0e960a0000c0510140012625405401600c01c00c00c0150480c640c0242a400c50214108582c0e0041c1810101180303032021040d00204141c01d01502c0014000f81114006041705a9074103035400d0851090886044500090240c1424440c0a000183c0340700c1c002c49004008228550135400d03400e0780c407800030b14001c1c08184144413040c0001424060785103200f9680b000410030101c409051802c28172140c10840d80050b2500b010008103034040070140c5048080d0404620340311038018600b903640200c0c4001031445858000240820400081800780240090038600b002c0c140492082002203041450030940c200c12103e42c11501d6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 116724262 1250 116723012 116723017
    0xf1107150b220207060906052a091005070f0803010302090c0a0e0108060a0509090703062304061109030d0c050c0a0b090d03021504050607031406030d031509090501060f0b 75
    0x400c2e10403200b03440707600b80106940d40c0b540781e0000c40d400d1003200003290080c00390000d101c0c40f039040080e2030314201c2403002d622070102c8145c0244c14003070204a40012885011585c540c2c508441c000383d24030714484200c98038442c0000c02800f1f103400c91144000c000701074019505032442120052142d40d03544680d058680211048140080d20034803114110754000c1c1307841078118001030400240940c0f154003040c07003240190380c0580782e944440810010701501e403048044130341610240c0e0810540d981081c2910200282010300400d80e122903112002d031280c8101c87c0600c4024003500ca0301e400740d50f006000c40c030441100361030f14010104d20001d02d10380300f9a00402d40c0c030040f081500300158501417041941043e102101503106011440ca034041102940c10b12a911900084c41140381000008040e20541d0b0004001000804148141680d001c039104d1043c680380d160001d031140a00c890014504281c0d03024000c104d1410800c40d0074080c1c10340002003550900f84003036405943d03810040043e403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 116725512 1250 116724262 116724281
    0x906100e1e040603081213020d140a06050a05040203070501050901020706051309020f070507090903090303030e1606020102070611030103020f060c030f120703051509070e01030f110715 81
    0xd00c031488806503440c100c0c140345034041161101d070303840c4010030021500b200c030b041c0c0080d02c40e22004252081400d044c0502a58020600546081103800075400300b4000c0004210040c4514022204041001420083e51500c550055028400e0342003440100008120588003a8060301400b40081000d50003442122050201a4014080309250030001c80d00758201083e40170800303264800014102d9150b0001d41123035500c500c40d2a9942c112441c002d85071520036440000014100001180840e420104a104694043c02c020030a4204240c0c0c01e4249039081c0c41d298525075540c0d1000c10210741c154050601136101d204104280c150001080c05540024440254091142c2c0d007540d0650038020301800c03080c0000350441c0d0806003003080ca400c0b2504204400105280048208404540d060045640001c280d400103003584c2c1980003c114810001850a010300c260b0420080503039100b036000210801000c0410007c0500d200c80c45041548403150a03100d4a05514071519450214030078403c1c1c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 116726618 1106 116725512 116725517
    0xa1206060e1806090411031501060801060306080c060409020a0203040b03072303090d2003070b07030b030d09051003020f031e0901090305070605040206040315020405090610 76
    0x5114514988000c2e4148503061003000d4035411400c94006810241420030001c1650219280c00b003441001002c020401c03000240c420b620401c001d069901300d0f90188225990740d56100c5d6180c021000380c82d4804810001081001c0b07459000307004e11411401940e0a01d6a213108001041c1c2044442001040e50090200f0405108111a4100021003540d1505500304203480e0795881030315800c1181400f89184160a500410704c21807200d04100c041281e076164007610f01901802c00a8a00d58007290500103604000d16001c80c2c2500c0c076078100c1d80e03015481c03032800041100c102015a0fa541c141503003044906003e2003644000c604c5241031100351945889150840399000b040101600c0060349000410400281d2000450f1516a080301000c50075444a00024907648200d0f4001080c84e00a01a9100c041c0c1240c0c000d00f0172500c04480c84a09507076400d00b800f0380c200b240d5404000 = true := by decide +kernel

theorem cover : BRFrame.Cov 116546762 116726618 := by
  have h0 := BRFrame.cov_init 116546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 116546762 ≤ n) (h2 : n < 116726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
