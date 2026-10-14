-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3013
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:24:31.120614+00:00
-- url     : https://prove2.me/submissions/4f8b504e-d10a-4b30-ab13-51dff3f885d1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 541726618 ≤ n < 541906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 541727868 1250 541726618 541726637
    0x90203090109080a0903030e06030405030319090501050c0d0f0c02030a0f09121101021b0f0d03180902040504060f1d09160b1201121a0601021e07050306071e 69
    0x500c00e000d4404050b000385640f00000b02c4032040c84e4044128403d072442a901ea48075075502004100d81c034001913401070b0a90f0000c00200d48030085001d24020411404c143c0070408406a032169421503004a4030b074407000c50001000d12007884544191030721000c800304200882d500d0000002d590703020f40c914520030b000100008107070040c0101007030402001100403034000c070155132500300d21000503ea0500c0c090302c9910400c80e1501c4100e10741d41c50685c0041d004a40d0300c15110100807035211102015403c2c481400b07444004540c00804500c003501c0101d20250b6124588002d001c21070f502d641c070050201410380000e0002070481440481103505040010301c0c1c03030f1204448541080c440080d0701101003004c03240014070a211a018201440c441c0401003110380c0e940d00003019035a2840300082444011030040607400b9032200b0b4070b541080b01031044441d400a0204e2401c4508685880c1240560140500704414902001425031102c0d20745000e000e5181071040144441c41050501c0b41809030b00314 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 541729118 1250 541727868 541727881
    0x13170a0b1b03090307061104140112061508251b02060c060103150501060e0102060a200d021207030b060d0c020109020907050909010503061b090604050d0311061f090203 74
    0x5030040d9103504a01d1074076524100400700b150b4a40c041c1d101150740c1802d00d52a04103401e4900f054070110341d4806140b80c1d04070614401151a425680801c01e0707544c1d1345080c081124800d05c1040310a00c0c8458881800500b8003004482d401001c80d0f22210001c0c1c56904402103260384103521a03990110f00040c0c5441c500c00d031000821501408003600d01074416540008180a00130407094222480d103c02040940d803144d80403244034908a1001e03016a0021000c82d40881382944030a50301d2808000b01c00c016100460001c489600042550550075004100302408804009a06801c04034a05040050b02ba4070000701e40d2601510114010055403009803c0a46000390040e2041960080070509585030071403000d0140e0b0020301c0218020503131070f03002260a00f0000f414901840d40e07600c884601c003040121000f510f51095021540042c0d003404009915160800b88500c5c17240f098071154200d00c2019416480c1c548002e2071143e9948900d01c504803d6242405224241c8100f4035015030780742e40b901d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 541730368 1250 541729118 541729141
    0x91502031e0408040e090a0b130c0608150a060203280903020118090216050d0c030e06091206040821152b110103110c190f0501050c13170a0b 62
    0x3680655040c5c0c44180800800413008107601d03496511959000819480d8041e441c100c400c2c15203002492035600d034809112441c012482aa4087c090203203c0c2c00e02c0c00b0b00c01c042502c8000680c443c0d030140c0c0c40800c880c81c460214000305007910070049000e001d41150fa08005000e40e0b01480040d05001b01e2120145d26280c48010450291420003c03e540d61b148215000c054003040100682d098029440c00b0000c881c0716050201e5200d805135507800c141010401000741c140d10100042d548030f400540e00040014050088070b01c40c0b401554110b48414580801c01490220041544640c42e0918100001581c464005541c66101640c0103c0007030088e40d005000190000c00c4008a841000300b0b07101086485c513048012001d0030b07130303060105c510483e0301c54160340106038005440350005400c012500310032400a49019000f070f04007480c1c00388952030365402c41da810703502c03018170050019401c03d00342c0003a0007500c01420070310045810300006004107034881611420003011508000302180070800d0b103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 541731618 1250 541730368 541730377
    0xb040510020301080a020103060501020f1f0b0d051e1c03150801050a0c0e0a0308070b0603010216050102040518011d060f060a081005040b0d080901120f091502031e0408 74
    0x20340411035070395850f20180c50f40c985103028120300080c01e084003c2903e5201041e5214420145802046a980c1c100d80c07a40d0000d000030400b225003591510003280941e81d40312003401031030050014154040c0c07074001090b800022800d40f004150f00c5000300008040034410040e80b84040ba150002d40d591100c3c81c007070480c0710144d004444079800c3c601031000d0002268080800c62200f5102e5201407001d1505000c1c2c00c1c4400d10014080d09402c0c1300000c0460720343c5800310380c010401400145425116000348602d00c00900c0c042e51030344c1d4089000d00607414042602c0490b07000b00130400f60344c3e44c9803c400264001e40c00c0130f4401941001408190b4a407540e0002e80d92100c0c0080c1841d03142d02001d00300802e503c4040328041403141400c000001c090030984160040c0040c003611b074410307107281e903202c03240c0a603c1440c5050400c0400100400c10b882a4800c0d007419615100010400450303c0c00d1045100009940e02d401891040051000d904280744c0303284d0500840c6007003403a042d51241014807140c000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 541732868 1250 541731618 541731643
    0x8120a02091e030709110d05160e06070204061d09120f09120a020a080a05010510060f1d0a090c080708060105180307050405010b03180111160228051003180b0405 71
    0x41c40403206e800000d040180030401742450007001641d441c0c03480c07070340b6501e821400d480c0420325012000c8160f00b0000002c080c03807800039001203045076507243c00c21414060703061201c10b051446800d100801d801800b040ca01c81c885c2a64003402c00a0102d8100e40d1481410343e01403040004419941e01580240009147c0c5900280b10342802aa1841819180c07a48900c2c129865460500010041c0c160003283c9801c1e03407016540c0c4001040c2c0c0540c283c44004100d00000c1c0d030b5140c0c00d010486d8039a60641450054a000c000100d561250508050281c05014040304280041041000190b99004050741c80d80d503041c0a160002266180100e814030650307400c4143c2084c10702001041c2010440001c60065a02c038640f0300310040b250b002d4608a610040303007410040c404006444e120b5482e0301e0038800890000304550001c2e0b4101d1180c030340481a00703041c3c2200d90a42d00f410466031a0005601380403039813a0030148469043d1f01c2220241e1356140d43c00408030708050001c941400300030401e000c09000d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 541734118 1250 541732868 541732871
    0x30c090409050a060e01060f0e130302071a18010806010c06020918090f0c01020a0b190204081516090515070501091a06150a02030a0e0f040908120a02091e030709 71
    0x710f840c00e00c1c03000340c55004480c6025609020000809540c000c40034000c440050320414015100c007941c035408460030380d109408502c9160004078040584e52484a460750400403055503032805042c10242c01c030801e0100c17a05008840d800c020075660000b90488045501500040c1d8400d05070700003440101311054414604001c4000300048002c0c0050708400100040c0111118000d00f4001260f8510310710b54010300c84001c04011a80d000300349800280301b05251840941001d40310484d0a1800380c0813560f107100c014800003071214000d90250072013684d07410351525441c11402d1001080a002103010303c40c865402c0050040c0901c1402e5000c04151980319240d03041c0c0c44005c821150301c0031000d82c0c24511a401c0e840c40082d03002d244108440002d00380c3d0300950308001c01e407601620700d8001040c609801941d2150b42c2680c07640c0d2031107440b400e54800e4555039101d0181d030349071818066006180c1c0c820584104061003080d070b10120040381c0004000d42100b001a00140070a0a0124a034070025105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 541735368 1250 541734118 541734133
    0xc0d03140f090406080601120b0403030b06030a0f0c0806030a0308091216030f0c0b040f020307030b0c04090608030711130f0203130302010507170c0a200a03140f030c09040905 77
    0x341c000d00904140108603001d211980d11039494a444040a10039100f00100ca508803900040c10050305c0c95003d40242400503814199030301146007644210340c1d41880a40d518003a460400940c403801000d01d00a250a003c6441d0540109a48000340304c000b40a22402c0c0000610561040200324400d5070701d11243e5898000d40001c100d0354040c442c4049003c03030a104400c040740303807040c0c40d03568005400442041300d680351500e80c00901c0da004030301079803d4002d075039010011401d90001d1501a01c0003411403980c880c81d0414403811202a40c01691454200304241d20200e1810030040350f035090101c0d82400602e890740005c400800d19140703003058160020040024031180810f200c55500d009800910060360b03204411101000752000039043c1100000c042880c500c50b00028125458075420468041103050304488880da4600c2400d03030180e03010341d0380c81c410103901414440c2c603410002380e6103080402c035140b540b115000050100c4c04d400c102182d0490700c1e40d52504441141a00002503a508 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 541736618 1250 541735368 541735387
    0xc01060303020708120306090f15040911030c0f090c1b10272105070807141204081902040207060f1401050628180b1306110c0d0314 58
    0x20f849540c410710807540920340f08a80444d001108685c810074000380b01d1030141e914006410320f040b1010301848000f0301051131702410742d1518401c03a55018040c11842400003000400c241c54aa6a20b075058054681d007200c1c40d82e07985403845e15035004031104c48071a0b00c50406085103200b4030001203014109205110680144a000d0f42c481010708040a04503004000c0022880c42105d00b0044005e002c4c0c83c0041c040344404a00864180c03024115182c00c0c1d180c400c40340c413040c0d25070300034050541d91100c40c25220345582d0310400188a502040c01849400c00f4901b100c541d0300e03202103460780c0d91141e1b00d50040104540e210307411540c03999407088081121b0a0846182c900820b80480c580000342102c42c0041038510300350b410396000162800c0085142080b89001d0031444400c1c0b14400103004030017450b20302c008140381545010346225528251180c081084402c11080d10f603000400303000300e01e2008440e601c1d001c2000075603004140d540e045010714619044031004c3d10702c15035803165900070034800c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 541737868 1250 541736618 541736623
    0x70212030f0315060f0712020102220e0906100e0c16230c0a210b0c0307081e01260303070e0a0503010501080601062006072f030405060f0c0106030302 66
    0x641140082400c0450850f01404498843c442003140d090000b070250000140020300410302e034080340d20000d810034190041c03441e012007584103404502440050300b4800001800f40c95035000032000020000e42c203001c2e441107496662800f403a0008115000055030780105042110300d41185040c40304160340050800510501418201ca07602480d2003003d10781503040082c980540020040c0800c0308146001c0300c00c41541d001c81d4a0103031020b4103809440203c0d4148141c58030528072611420390345d00e01401e001348200e40062140c143c00106002a8446040d40000701d41594801080212007051082030401e49a000000c41c45842c4000010441100c1c0c0c429101491724001380d84c1d0f500055101d4080500381c903000d00400d0300c1036000c3c0004002951240341043c40307000c03d81001c140d00e900138606850a0140c11107849010035900d01110000000d9192100c0d54130400d580a103907082e00740c00e80541c980c821441340c20f00c82c1c440807410201000c40d03c070403105600c015034001c110840c1c0da4a00130f034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 541739118 1250 541737868 541737871
    0x203070b0c07052e0c020106120b160309050a0b060303121f08010e030a050a1404030302010b1804020f0f01020c0301060e090106060927061511010b1212070212030f03 73
    0x240c10340569041280109070030110807265003200358090b1146403444c85030710000e140a4881d00119902e03013800081c1c2030340c60710422148501030003a5003000d00d0a041c1c02c0e00060070560502080524144400002c42c502140741d20515074844074040719603c5001c0024950302800d8080d010224218040c0001500010b80140029085c16842074003e40e99001c60340c200c500342d50300100c864008206507184180b1442c018a82410035041284001084140c09203542c0c0280d041140035039510201d802452502c601390300c41500e04841590007d241503400b003105014040c4c0064007a9510091308400c5a0090290718040c88029008100c40d603955402440003003001e42e00c40705d05501e040004075001d40716030203000a9900c05411307515241502c185000301c60f06190130f40102e0540d282d02c04a48c0c8040302a54010b040c505a652210320352484002a02f1550022030484c0300e45211902c0c00c1403100b0100e2071240c019811b1401e107403514650b0021031408a01104040030340e002c0003401a204004000145 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 541740368 1250 541739118 541739123
    0x705040506100203090d0c080a030f020709091110142107090e2a0c03070302071509090e0c040204060c20060d0c03061a21060904120203070b0c07 64
    0x521650310707030074184407070038500c50b0032800160001c000207546400d04070405040035200ea11401e0302e8541e500c0e0030034103088030781004070002010740010703001c80e1703504020803406444224001c0050101554034262680d050011080c0141d40084400004038042c02540b25074000000c2c0465480380312000040550340d00045a10448140402080202d44a088580c0030f5800e40940300d8111748a01c1900040151340104441d1070000c0d15080d107101c5040750303002c1c6c074110481c0e400541d03c8040d5454080d05100701c0742c0151850283d040042c46216902110501c202d80d032260b00001c6541304401001e080100002c8610741150000070001180341d88180c4400c8c017580122040c1c555030318000205014486140381c0306520100900c283c8402c0b2005620441416005040c0041c1580c0e80e03000794440d044181c05115415280032a0801300340b0440c8400341041c95903100d02d15000d16058001409410b00640060710328000d00501d01e10f01402042240d1400380c100341903502c03e19060301c403500700740e01800d000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 541741618 1250 541740368 541740371
    0xc050909010b03132a0f080f0d090b07031103070308010e0c031905090c0307030507170708070b090604181d1c05030a181a090a03020c0108040c0b0c070504 68
    0xb49101014050381c0c0100c544103812849041d0b5900e846030042c0c00d40c0261030388116084a030003a01410301c1c03196001019074050406c01d252030246628100410800703281d1494001414001d042903201c61503c082d90000d02004d51200c6190408407000c03808002201003d220000d81d0505041e017010740c060494030b0030039402815030741c0c029507091180006c1d208030010800307009a103544501e0759000281e2000e440c00481e1491141030700041d150990750340c4142d0f02d50b041104180420364000d02107106241c84a8024020540b8000d80c51f6510102031090401e9094042000701c0259550b90444006100f09102c10741d5603044590500300400b010840424500c4000041c0080000c02140500a10364541902803103600c0c541000e66080c2d0000b01900c500c2e40e81d510380b60050313148881c0720340160703405509101108882c003014112072480140c035030307801680b0104d2200c00180d030004604810720700c20700c1c0500c1d107911103280400c4402c176540c02007401c001c40400c213840c040d40d00103456421220100c80 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 541742868 1250 541741618 541741621
    0x807140409020c011a01050a0519122a0201150302090a1b0305150103050f07080c1b010f0c02210a05090d201507020904020f0306100608010b16030f120c050909 70
    0x646023407085c4000b01010450500c03540e51f481001461011800341c031820400310200d0352172949021104086031240348410401051643c1010201c007400400c509400208941001100c102d0354140701c0303120080c4500007034400188110840e422070780204200300b51213111b0030301164002d0b001c0e0400f100d40b8109a40211000442d66109004040c001c04080c00c0c202c03010f403191035080741c0c5100300402c0705498040400c103402130003050343d206120b00d03920300b0000500e01321a0f14025044d02c00740000c1100b154455040030900700e420041100050003091a8a907a401c2ca007882540c035401448002d5a0001184000509001d08416809110103191214000c500460390400604044604142d040d0b4882440508010f05125100e02d821500041031342d01000c4010300024a01181192441c0940741c0f0300004215040d04003010501411a101c1040c0c24180403090004040403022805810080c4c030300d5030100c03094042e10403851202540342c1d00307100c042c0e0741940151403a4400100d0764050880c030310 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 541744118 1250 541742868 541742921
    0x30f0726070605091207050603130b0a020a0807110a0b071106070815010f030b15070b09060c0d020d14040803011e082e05011508070e010807140409020c01 68
    0xa030080a640c4075403103680c10401040144a50003070207440b2041705204840340803400d90f907440701540c0f0500050107081c0c0c4e100c0705e43c9020221148050310b0b500a0314018411164201e80111155502144500c0e203403442d82501c0051a252070f4420b0000ba241d080104148035541e9401100001d440c01c082003100d80035201c804044a59402c119022070ba0901c0708034206c4455845541a00341705541880c001c81d81290310710000301c1c1042000d81d510301a81000401c0c80400c140c04003002d42c4400d007000500607500c0c4c9940582c506101e0444060703170007035000680e404142160b50111103103441c26019181d151910b460411040c2c0d10a00412054a11003c000304002140d1400c4405a80740400901000c3d400242d011042c581c4150820321802907140c040d51203a4000d09c04d10f8000c000d0411018072700f800406010341400c82c007904450401c14108900788580c0d810107900c0d030308045246085010700d006900014001c0c0669082401c1c424000924000d21500541282c44240000140c0c081c02c020403070b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 541745368 1250 541744118 541744123
    0x219060518120c1908070f030302122515140601090909080f0705071701060e0105090f152206090e03040501080f09160803071211030414030f0726 64
    0x400a4082651241c10310f4045030824803e486100d02c0300d89010074442da15003601c1414030b00c0c02d4020b00304a43c1d045000700181641040004800c0500c80200d81c40c03c101c0c402000381c20f44010400c0070715403035050129000c000002e0785401009100700004c000031100341c0061151005c2c03e0701d500d40003901d2200c0c0421925040d2140c2c0724400c1d0300c04c001ea4030b006203400c90544590000fa00c01c1c0c0d03060040e02170009454150700c4c4041d43c140c0f105000000d85c0b070300b080c05030501c000d8181c20040c0113600420400050590780242a80c0001c1850441490303010101c00050090090f02642030b52101c240300f201d04510002d411102c240d13030f9110014012083c6101089541c6d0080d44103250001e5a080e0110320300d49101c454075600401030400340c6190442c40001d0111102c41c642c001c050744d1b40001014801c0c004044101c0420031902d2806100244080c1700d840d94a001d980581c03840321405000d24a0969005c1201c401c43c1c8403040c0507145043da40d035000303c060707000c21045074526120100201002c404003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 541746618 1250 541745368 541745389
    0x304050d0503130806270304030b09060a0509030f070305070c1a0705070b03060108130302010b100c0516140402090d021923030307061107050610060306060311070f0219060518 77
    0x1100c0d07501a40c01540031a800c900c06c803290131100940000c000210200d00b942d10031030f119104d071000420303060034a40715000807600001c2502c80c141c0c00278408100d2a00c501c20071180d54542514046840700890305040061044550101c6603451742400640c155084440143ca01c035401035003900d5550b592480201c409200c01c49600e0300003110000000c2c0004044e42c0c1140c4124002c3c800021058085004124144000c00c0c401c004142d4400c0c00108102e01002042c00f6015544180c8003410300d0a041541c1d484016003a0b103100f641c011603645920b4070f503800d46001e9581c00800c6c0050644c4e0006148041e0301781800b40003120250080103d48070124400041071625024004525240c0300e5120780004000f801e11441c0f01910411141000c603404014243c050320a9100030b480051074204003030f040300c5035070f80540145818042c5103102c42030036409880641340c101d042c03416111110310004110180c502c00e04e45005a41c0340d000704955078843d0280000495205444803640195070802030403828 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 541747868 1250 541746618 541746631
    0x11040213090b0a06261009020403062c0c240301091406090f0619080a0b16020c0d080a0926010f06030b060d1b03050c1804051e0304050d0503130806 65
    0xc041030410440c07a0949007081c1c3c000311b00521400f09503150290b40013664030981c010355100f40c481a08210001e149859040310079100c2400502c0c0e040c035640b00d03030346410040300c0b6244a050b4068400540780c41d900d1281d030104054060b01a42d03580c4440300c590062002c140a080c03042401070005038142069a038807401100c810010b400350383d5a41c000c010b182c1551800316280d25035628000a162801000101071046c851500d42c0340c5813920b22401071002c98400030000071980040384140c5142c59492503001801e0300805043d650b24070000069450f200e26030301150b0300254903045080003080210460000c0b0840c50000d0003080b107084000c0043d240a400f01501d01c62840c004a4178900e0980300c04440584240180e84030800e1030030402400c1841e51b07205913020f8100418107040d0f454500b82d520b0300c00c50031041c0c140c0071741420f8171015907883c520041000e807101031031a0422400300c10025103001300f000a21080b090400c42c9400c0c0e03105d421100b1035190442c0c061b003011580030b4001c2003041c41800b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 541749118 1250 541747868 541747907
    0xa0b0918012d050702010209060f0c120703030b180115051308070314060c0a09050d06090206040b0430030f0c0615051002010603030e04091b03061d0a0b010311040213090b0a06 77
    0x242045440742c0a684034bd2103441081c07050604000e070f05200503018003032280c0a5180029044050001d2002201d244018541910850801881441500c000390210405145042529150b40c007104038511841074100707119038491803900004000c03520b05a126541c131210182c07405600c0ea1940c40c3e019014210541020036014101400a4102034010100c202e00440b0042000c0b4001d80100c0c1c4203920507042022a028005020f0000c07017450303062950796204400940c81c0003a4030307a141102d070302d00b40c190040810035444c3c00d40198038819034280108a07003280b410000c1c5070034006002035046aa00c02e6034090304c0c2c0300100c007840c540188590030480390140c882c0c1007001e01b11402c00009041d090811921880b0049404002c0515900301502461280e040040ea151042e010000c0c074026903240804c1d140d01c03007214040083d03030403140c450450368440013061145010a000401034002c03111800081024500000303002c100710342003400d01400540c1c10042d01c070b032100e00c1122051440381498509a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 541750368 1250 541749118 541749127
    0x11203110c03060f1f0b0c4c050f040314270312210c03010803040303030b180906160c0b060f040207080a05120a0b0918012d05070201020906 62
    0x75a0310044d41a44440e41110900091040f10403099106000343c00c031004a08010440002c5104100f2a180c00030b04100c070480901001010318911001509009040300034040b00c1d04e4100100390040d0b0700506044260501039031628154019080e0802c030340607400109030480180c007640700075040342e030500c0407041000d0300344900020040308218412841da0b0103100e0304000309020f8010202401c07010513000c40c42034020000780d1010038105405044054000340410040020120000803503003203e0f8907050200e0048003e0002407500d55075409150601e280035010000030f80f02c0810418450381d4002d500260001984504903841c52440200400c40101c4201080032481c0a020060170400000d1026290100a0341c4d04591508520a5440840c00c0450a100755617141a1300c0d03540030343c0019041140303180d01c40006c0e060403000340000700700250700041c601c41000d0a41010361172450040894264200c0000303030086c1e103003903100c0010089103001c020481c410b2041c001c43e00980001407209041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 541751618 1250 541750368 541750381
    0x6060103020306130504020f06040810060506040b04031407031e0c090b061e07081209100b10031a040c020309030609010c0804080a031b0c02030c10050d0f0f05011203110c0306 77
    0x405c4060410390f440b28840c40204501d0340c4c0c940c0200701904455003d070001c0392200710890300345d030003a4002502c01c04040c0400d0022a40b0310301038800700e80c0c01003a4101c00c0c0e1040c20a4a0802800d500041d00c480d88034030b004205d140d00111800b55262080100b550303007583d03074110328048900001c0e020f90f10134010002c29001c2218203011120910219040a00d045425a68100140d010142c24504070000d14200541c440d0180701d0801d0403c4031a9003403005416903000110f0b004103101c041400d0540d102a04116456018603520508201030000c004100c1d803010080c3d9240c02c101d1156110b81f08a80c0001c2c0c00d0041801964044815034841c05104d8440e030341c48c1c80c000d4201403110410103942d0058900d41c00058181030101c050185c40350640d680160050605140e042500ca500440e940b051414545038008121103848542d4840041d10442d002c40b55000f074050480051380c080c2c1050004902e18514040315103110b0701c40d0320f40e0b00700c400e900d02c503489c0c40325020501c8542c96040500094403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 541752868 1250 541751618 541751621
    0x3080a120b06030a0b1f020d020601080d09060807031509150b0c03040308090102030d2a050c0d03021c091208060a0605120a1d0f240a240909050606010302030613 71
    0x101c07507001054003004c0e816240780c00f454110b00300301b9000181c1c0600c1031114642c2c0c05121f40f45c05062408003810074089000c102501400e202d1088000b082816000504180d100758800b240382c0c0d081841110aa0355510b1642c009850002408020b044004c0740010751080c00004840c1c04250440c0074505003850750701e41c40e460743c100b581c0346410f5010800008808600d07521807030508a901d401f900804004101403012099081400c410510008100f05541303288006130f5006621a18500503a80f00030804071545001c0d049525080414144031114042080100600c8500c1c45555a04451540e4032000c10012500e203206200105508101c80c000d01e92007a0788076903010301c0e80a40811410300e441d243d903003411902c001070b2203182c03c508020512f92900340303d000d9086000400c18541069029586000e59401410030b40b50141d80c3d80c0c0d520620003111044112140c0480351400b8850740d90b01030840074254942084880f070050300c0025410350f00900c207503402000301600b00009030011440100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 541754118 1250 541752868 541752881
    0x1d10061803060c090b07050105011d150405090c0303070804080105060d1505130c0e07030f02030702190c17030309010e0109030f080402120319030b040513030815060403080a120b06030a 81
    0x2010813031240c2d008152000207100606529204000018640d071401d00400700d410a0341c80c00c40c414044410901503070881c6651000c1d11200120760000b91034276100c0e00300f8074000c104048207406000119a0340240002500500122414134000303001a590300c004001000500c00001043c0814102425041c80d0095103d10391011010001c464950015150750b81d02c1141d562181130500d000b0001c109483d036240c002c0098802e0800800d5040d41800038020b91102c1000b0400c40e624003542884106100d0552010401451756461071404901203011468403039004075041c50803982801120001c502c814403414400c1505651480c60201c45d2800c115040f0001401c280e91107154902c40c0801c40c6010300041c28a030005502c00b00c00c0c00d11001000d400d1300c5001c7c004c144210314000802c040441c9135140380e40e4140c0e041c903241046654084a061a100310b01d2003c5802510104010040008507801072912500300d89941c0004291004401e05442c01038841c0354000d41300b400454951001a003151 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 541755368 1250 541754118 541754141
    0x8090d0f27180b0103060e0a021c0e0a020a06020a08090f041b0305011d040c0b0906070b1003230c0111070503060a1b02070614131d1006180306 63
    0x2281c0024004500080e015560450540000c0e060380341c0921190910940d180c0310020300301840058500817010b072060000a01d105032198002072014121286030440c024020013502d02000600b0020741c19507541d0000c400228010708400301c0100b0f41600000f042c0724040c0d8410781c103c2c50640558140969036040500a80d04240c5460880449803d0440445045170b80c9980026aa600d03050016030705003907003400d110f949400001408040740c000c0307007040140e48000384003603a520802004603070980324100d4050035024658040c061000e8004114200b140e00a520304480003010401c54440c1c0b16901d2203080c0d00784c0c4022020302030f550141c892000da4003401400d0301d240c0d0380c0c0c807400300e4140b010071203a5031051960780032070b441e0800c00d2807803100740b459480c801800340030704001014120600580850064040220314458011409030390b0101500f07090920407a001d10700c4006400c40d43c000d680e0b5581c04411444080364107031081c10f49801a0070403250301c03602e240c81e50b2504001814042d601 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 541756618 1250 541755368 541755407
    0x3120105012109060b04240308130f03060504021005490b0316122409030302070507050f100305040614160909090206070204050711010c030c08090d0f 66
    0x1c09602ea0a120302154580640703004205491a40c080200b203a4200c030300b0040083d180c003141a04540b004a1190959038409111a65425080c4400c01d070b1031416401401c0c9600300071004010400c1582207240034a01c240c40ca403442941249050354140600f6400000c0d240c204070600dc106005c20301102510f078003020700c41c40c40180f00d0004a018151000c506044580ca9040814490800300800c2110140d103002d800d10841c100281e041602003240d501030808a0f04100500c4901c0040010b003400010000040010503940d0ae8058003a400055050303a240c0603000c80080c0d2820700c0d450403038002800030603810280b5001c51003580101005002a1803841d079a10041c42d150802920050007001e21007038550303600c0081c8000400071a45600040115401c1610710801a103510040c0c2e240280c0c1140c02103801d6641d10000c4031044007a046055082d07080203003540c181034241d846a0320f1a4020340e1458280c2c0d45031808240d407103002022800c0000c0b00d54910340b8405110340003d20f00944c80545 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 541757868 1250 541756618 541756667
    0x130201050306150a030b0a0f1d0718030b0105040b040501030503030a15030c080309030d020d1d01020102090d08090a17030d0905150903121f0314120c07090e0312010501 74
    0x1520095130454000301c00031035524030307401544c1d00d00004031200401d14102078075444d50911410b01480d0302a046070384001900f941c08500381e207000311100060000b141034003400315503407801c01d407200500a00c1042d001e185401c5421641d0305081c01004e040e207806c18015845e584501100e0070041c1010341c0188124241e490021000900c010511070080056000440d211444031f02050708211020000d0425135001da04d190f205540c01c0035011000c148a03261500030b604203000181d0180c420800000d030320200b080011130030000d40c0700140c11400009d8465068a98490903041d044003048180303018594410320400c207081410382c0003485458811804d66030a59200f100089012905440840043c3c1010810b682030982039100d03c0e5000040c0d10040814110b0520416181e8680c3d010240409505007040c12010070100500e40c0301d00c4280c00d540c1c1d0340d0040e50000b03d440305900e0044030780b40d504040520040701000800d885100c070781036400c01c00b16441c10005440b002030403143c540b03044c2a002c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 541759118 1250 541757868 541757899
    0x212f0405150406181208160b270307030203040b070507030c0801050610030902060703110f0d021f1e0216060c1106100b0a0806060409020c030d14130201050306 70
    0x21588401c1c45040c18410b900d5508080001d01488624160080c02140000080009481801444504a8210362032507512070414044241d07140c0c0d041d034003a209034001c0b01841b4410030034000003c2c0c081060b4004a5190049207111502d0b03204621000e00160b02c24401441010201401045454414811680c1003962592078a41021442c5c0c1b0a8150307943d101d04204a03801c0c001e0300324524103ca8502005070b1540d544c0010074a01a03014080c00b009010f1000b0300c031800041000b214244809012550458a10300b030003540c030000050104841c4528800c0b01c0c103195a103018522000f01c0180440b51050b0b03216000c500250005c841c0c020320451011103180110b080d81c400c1000d582e4241c0c0e80e00c075810710701e4110285450741c007401c07111a24901000c10480000b01d1000c0e076001005074503101d0b12680341c41000600d940103d41044a00c14030018102004400000050940c1c2c170441d0070601c002c154104110521000131038112000f610080c902c000150f101760021503020360700401604500c03800300e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 541760368 1250 541759118 541759129
    0x106081b120a0b0a0b0a0509070804020102100e0f011a09010618030b0f090c030a03020303060409060e100c0807020c030703060903020114010b0306150c0d0c031e212f0405 75
    0x20003540d125980f03805104001c0c0180c020302c2090202a28001846450480480e206070030080004013000015404034046a03c288041301d8120341c0103400f0310103a212802e03066101d40700a01850001d61a00c54a841105001e825410050100030854242a8a004000d4a080d03d4a642c0c803080501c8040c0040f0000d101480f20f079000c0d041007140c0d50000d20f00780d0b402a18101030340340143c0c4079611030030308000000d5000045a5001a0550700418900c22500d801e60103050341c51111000d500a1410303001c00d46100358821201e5000b295034065040d101e03800107903100e10103044002d03050f0b0013a00090000c640d0360380069068900c030b032000069190041720131700380840c07086e00072078000f0400000784031031803400404215031a030315036041c02e25010300c2c02c00699030744000c50010400d02000e0800002410300804102c080b503100c00880195110068100401204840b80b007110104c10480003148451740034440c941550f80d04000e04bc102103e054200c0380c5a0b22074000e58004890b04000204180d100d2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 541761618 1250 541760368 541760383
    0x209130605070e0a090b0307031b05120c0a060c170f16030903050f010b06121302060a090608010e01080604151d0616110a030c03030b10020610080106081b12 69
    0xf9914444401004010031400d0501940590390300c50405000c81d5140c1c0d800300e07500d01242da206200d00307054034a0101300c4410150707650025512140ba019400501040411204901e4034201c86451409403910400d807150b02c1056400f40103941c205c081070041d640c0200c02000310801c5234181301c2c00d00302c00311000407e41580b0f42c03045001500106082081003030800c1908180380c0007100a11014241c180840d4090145071003000c820018800815411210401d0140b4200d402609159540108080c0130300705203003d2041c040019512000010b041c080c10f40318605840c0001c000c0c29035130711030781c4032000d18038400760140c04156911103841c42c4c042c0e500154003604900c0350f0040c00c4245403448030840115400701800e8207201403140c50850441d400300700c50030b299901d400d001d8081c0700700b410220014560551501d03084a8450340c1569055000201c50b07105074103c042c41d03c0101e0311143e242c3d00b40d80701d520410340242e000715000641c1134030410078150b015030f014141762494540200c206213030019 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 541762868 1250 541761618 541761631
    0x1f0209100e040e010c0c02011809090b1006050a0c020f0f0306090708151005090c0d020d0603050c010212250803010605040602071d0f04261c0504020d0209130605 71
    0x1015010300c80142080e0007003103407042d490310080040c0c00f8070317480141891880800c0203042003500448550400081081c507005040d000074100b22000951074146c0100c1d100f510250b000c0d031450b00e000140e0603c00c03003c80302d080c3c19568544441004903400c0c800c01c4554a0b190560003001007a45070200c0d00c04001c1c441c40b07010103030010701295107003a2000c2d081204202c03030480303040ca09100300308030b03080c0a0342000100c0ea02955182825a5038096000c124002c000841075010700000e079004110324207400601c1628095400c1d141e410b4848801a80d450403c08541010000203000001c02e1000c071070078800b282000540c10700c0c1d60b9211a81e40b000d00e80d009030018070111f040841d003071000542c100180c0025000d20384200d800342e03110303a26004204a0040010010401030000902080f80003061030f480c54448081d00e4518001214001c0f80320b0300051002959080207144401841c880e170701503a805940c02a1000e0398209154003440441c00f170042524211400e01030056000070020f01c035141c0700c1c91 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 541764118 1250 541762868 541762877
    0x40f050711010603020d0314040b030a1a04021e0c1009050102040303020f030412060507030b1008060f06070b01300b07120515010f120212061906021f020910 69
    0xd0040409048201c16400d00040d9030301d004070500044e1100390000d01e110743c041c241203004441e0a84182000d1246130040031040f54040300744014200c1d20340012002800480406054040c0641840100d0162018540c00340052409408a8180403001854139403142800d40b4843c110709001c0c201542c007a00000c4070942e40c000340030020716905100003d440081c1e040918a0145003030729a01c0840030810b0050038490b900c101151300d0f14080d601210a512002d0424450900c108002402c000c1c011288180901c4031103043d42030600c1c1210850f4500d5612004c501c80d603074282021541c44039141e8440b10469109000d0202e5108100c01d100781d04603200301031a98203481c0080c0c0080ca100765103003030396990740d080106002600c8012210241c05000a1903da02d9044451070b0450389440f0381c80400450501c002803011401039500c190f103104110980c2c184c2815003560070804090748480c86a040180c102ca840014489045007200c00c408404080c0035003045d83da040003841c4980d84c0d0b2000c80101c0e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 541765368 1250 541764118 541764121
    0x721090602130f1508071e0918050703050108010e0d0e0a0b1902010e121813020c0c01020c0f01050313030905090c0406020f0a02011409030709020315130605060406030f0b040f05 78
    0x81002c4081e0381e050f6042417034108000c0c00e200c4005406c41c013000078203084400a01c1c1c9408442445405000001c2c26600744546651469080907002048280e07480300020b8241000450824014050520b03c82001c2000b00f541114907030007151f000104161695000344541000110b07101c0650203031000503d4005031074911422070002030f003112503c0341008880e810108540e440030f4040c50a9800b9540d40c4031000000c540103c0018142c204c80f0010b0251032840452072030703e2500c0010706100404400e03000c07200c04100050030030003500003000b0400e00007542040000c01c014a61a02205c04512a04000004039102c10004462020480d0840081800410100040b40d41045501e40c5a6401405090821003a800013407500940704841c09083c0e03030002d01e440c16502c0801c80342004011a090031500d909102000c2e20414989103175452240e4400760040201c91142c0c4210412205c0c01403030189050302c2d000064018050b5484c1d412030310795490303007841c4940e111401150038801c40340b80001001d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 541766618 1250 541765368 541765379
    0x60e070e09011e0b03130501091103120f04140303070c06030c03050606030f060103020f071a0402101115060d14060f01090c14090a08071502060721090602130f 70
    0x6800142d020103400080c83d0701640905500700200400c0d0b403101032060307aa85e5a1196200d0440310082001401980381c00d024030b060105241c28901c48034012400c0c0c0e003100800224501c01802815124880b0340b000b0442000390002410400540404c00b80589042c002d15465000c04902141d01c05000300e40c460351700c03441290b41445100d42c4503c0c2180c00e80e0441c00c100ca1410b10041008000905055001446d42a0490320009445a043d80403034907008882070f692001d02e01d840e05a4040f070260000803880b1100d58051040010031080300710003030040c00010710b2040c062140251002e0b402450201e80344010401c4a07030039080c0500990000c10f02c40c148030b00c901d030090710305a0160740828a032119003800070b80d001407643c85070400c1c0c0e940d0903182d007240c800003440780b101544100210b21900400141401c400382805401c044c95400795012a540c0a0094a41208800c80602c24401414a40d01d00c1d074282d034040c64455000c0e810050404450085100c25200f454006c1c034a1500f10071010050b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 541767868 1250 541766618 541766629
    0x2090105160c0806280908090f04021b03070c0909020102210d1b0807020c0a0905100e10031713122a05030106080f0c120109020a060c0b0a0603050c01050d060e070e 72
    0xf03524908010406c2040056282c0d024031b400740c440c0451060034144a8145030380e4846e01507441f134692580c001900910340d17442d000d6030f030343c804481241d28411160001610080394456642e0885c0c060b00a0310700700349003243c10781c8407580509101f42039550900402e9440c4a452180a07200602c450403105a501d4041c005484100020601411940400c040c07100b6511150300310002c86641c000045415100e100840340d81902a80003251400d003081d0800290291f003413482c0c41140d004030f81000c1040b1000c80b000314903118865981c40500141c00c42003000c6001a003103821000e0142804a036241c0440f900184080042692149a01980c15052025150038862440144403100040c2940c0a030032105a44484004030310034854060000210141002034004940e15940286094400354452030701900340e5804290954840c0c11901c005094005540308a03015a604040109200da0344403004403640d61180707011918850f124040060780316480c3d08503078050401c40d01c1c1c0078a41c1d1103d009025 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 541769118 1250 541767868 541767931
    0x31b1508091501050a170f030c01140c03010803031501030e060702210309060705090a0f120b0f040b04150204030b13050f1f182301050a02090105160c0806 68
    0x300c94148a1004105603980c8620b81360451b8407400450035580c41202c80581401007006425600b40000203919043e42030650010308490710400c0700390341c162280c0c2c0c5e140000703000074050110207a0003040421215910141a40304021051401290b540d68106001c2d0500380d080c3d6100015034001d080954011071940200e0f8034102849400c28158546105920340d60030015084205110b0b0008885815886040c01c1e40050701800f03c80f0740060740c0d036003062090b084100c1c20603503d44813142c01064005000082a9026541040c43c005258840c1d4a940c458482d80480c442446a420080000024041c600c0280b003110609008944004142007803410100312500010700c5810170400d00498514990200203448480c0c00002852114042c8a10350381c0c42c25580546001504d808507585400701003408034215484ca4024400b5848810120059018020703c16001c40c1e01401a402480c0300038140c815068041c1403103107000f554495050341070407010764865400b200b09a0b40d01d05610035400c4540c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 541770368 1250 541769118 541769143
    0x270510020906091509150c16050904120509182d04151118030705060c03070f050703171801020607080402060c0c06131802040f031b150809 61
    0x15881c0080441c00140d05200340009580f05804440c3c14001440095081d1042004094003401002e00c1c0e007040030580380c00001c40d00c4014821b0189070700d04000e13010302080c00c45c0c001500c080000d03140c60340c0700b0f8a0981c2d00340307407a0100f00d000d00070451aa0360342000c004003800103a840034082d05062803816002c3c5a49c03030b4a030304007080090385205520400888154081d8000c9032507104c0d004501c0c17011004d044110a880c004450124010f0100080507810544002c412011106440d41e41d4041c4803150090704a0038595410905c61031000c101100310380600702d1301c1882614003164483c0d484e4020fa80b0410f010b08041a404505800b000c0c0d888a641d110010090000744123600e07118000404052009000030300541c00460341c80608041000b0340700c00d1690040c5050740790401d0000f221a1400d441c410703000705a1426840030038204661013140d0607034103d294580001421034940c6c403842c50b400410319480d02052400011801010030225801615582d20a40d039400c0c84480d01d4503080004002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 541771618 1250 541770368 541770371
    0xc05090118030807170706021908090105040c050d0302120301090203100b040305100e032107030f050121030c06020f12010503191511040f030c0e090a03030f270510 72
    0xa1003c01c005406842d602a03100c041d08540382081129040f490064520040401e0300100300302c100d61402005ca60300c580083e07600c0c04000d036910130090303081c1c640c240d6002d0105006840140414103060000f500c505000c1d00440e4008181d05400203241c0d8407d80c05525a00c0d404424400d240b0003c194410007452201e42490415081d92103868485599104519281e50398150f4850f21620034816070b00600458403003a41c4260039504404603040c402c5408200281c41c041c0502591a154072440c3e05030f5002013040010f41c040c1461f9030f148456a014190240080d51070500005401c1c0c1c002080000f00d00391440d911500111044028a24183c005034442d03082551364130030110541c1c0385814883e42040e0502c10340302e0044405402014050844900c2d03010004001c6015003051039541c007201d208509080718560346100705040c3e2401907541c1d2009411a801841c00320b8460b40024020103103510703001034901c94501020004c0301c0c5a05145000d0200400c17504d0070300c1030074002280d48400d81d240 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 541772868 1250 541771618 541771667
    0x31404180c0917102703020a11040903080613020c030c0102070c060e1c060e0703050327030706050c19150c080c0403020603041e0b09071d0f0a0f0c050901 68
    0x1180c4e840700c1c55141c80c100361581d5503114440e910704044a00c0f21034034048580d07002001d02402c00035250264210305862411440300c199070982454800c6c0710b2096099910302025465070302c104121201c1c14062400100e07000d00103404802001d02c02004130700348040c001692440d40d45045001608241d011b07409000c0c0301c5060710700940b00c00d0b4500640c1010900100c2c034900291904400404150049280521803050040100100000104442228080907800d03004074141c85025a458062215425030000081008000c1c0160090407001c5c080d901901c80380c000c0545c2d000c4118991803c10b9511543e40e00e0078007145002c5d485450a02038071464458510b1822884c2c00c0756a200b2840001d003d040008009000d1007240d078201c1461040e0000034991500b5a802c3c9400c043d802a50b0b40e8140f40500280016050b4490280d48401c1000e49002c101584d200381e10400340c0f650040c020040d0a85070303412114805624420f000300c0c241e40b91607040c1c0f00e8005500040801a55600005607440201c4c07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 541774118 1250 541772868 541772909
    0xf030c080a0b070e0111010606050a030f0c0203092101050c0403022e0e06070602040e0910090b0f070c210e0303030415050402190e0130031404180c09 66
    0x220280d80300c44642131004141148000480c2d101d580402d02990719440d24030003149003544407006050400c00c1c2d61b8103028640d000010f0360100c0b21104840e0340540e10410401405040001030410301004a81a5482060035180c07000d094600440f0b0046014a000805108518210300416502d140d0400706800e000d040b96021581d00b04091000f40c00d00c05800c0454859964103800c441d1107035440b070000e54440c0e9a4082d083c0c41441c05490700c143c2405408914001e8415a00c02c1810b07854002c159040c264480441c04803e00401826100820000d80501d0021441940c82341c0300144440701040c5d030103c181c05008100040719030a15200360400c00c1400049001013042189034095101e000400d0f494070702c0002c0c3c84e1039600d1390f01c40119038150000140c2c0a0002303c3c242c101c402918009582c0381c03500712904075004240317012004642c1c5080c0224086071003011481c5129040030242482d142d01c6000c10300c0c190101201c0a1161a00c0c0c0010524442d84008400c004280b80b00803c0d90500401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 541775368 1250 541774118 541774133
    0x501270506030619020f0c07030203010605010203031605090f0303120609180c10020717030705121215040f0212010f06050c0a120905120f161503020c01020f040f030c080a 75
    0x40c080038160203820004c00d02000c220b07411200c1c1c41309070310700580ea1030340003160319900c1d041350344800e0340309518199000480b9400031080340d106404c041c603c448000301c0040180c0b059001002c245130800c0081080c1e10094030200010031403052800510910352401c2410400c04540c001e2034021801e8110102c44114030001400301c42543c3c0441e100c103040320413000200e1401a03298400015840d0120489079030f440040f008080c0d0600402c00c0e904030003900c500751f1203030348500e0504070f01141d0000000380d442d03081c2a24a9080c001d0003000854809840402d10060782c00000401740d44405080040103440101e0402c9001800720381041800c00421100f502e4440e804031002402003483c02000540d040d100d141800058000100201010024070303e9246d07a40d041079804408034850800e1001c00301c14034181120480f40414961075040c0960300e0101d029400c40319486072659024880390b05e16000c5900500080c0150307296024100d8a541440100d84486600000342c0360891451100401c0030b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 541776618 1250 541775368 541775371
    0x305100f0e0c1e15030f07050a0507060c030609062d0b09060a030b0d14060a09080a120204050d06020c070b03040503090904150c0513091401050907050c0105012705060306 75
    0x701e40720b0020003140424102542400c5140a071320140c401c0007250440c1605002d94000c424400070040790b9603420005a4a44c420f025581010070414400880004c2032034202202d0905ca03441e01280c00781da00c568407815280310303821244580e103140c0c11445501c000030602c02c120302d40340c519419a152410b8024680d501c240c0c0d02c0301c1d010340720000300f15800c0d0f0b000c0c2c1c01202c01ca800260075100310b86410305006204285175050013103e03008504c040303540c003182401148541780d00141040d19120552005a079400e004241c03403240d6076000d21002880b075440001c451842406440050f03560088a03c4d03081c00d041040d045509101030074000d00020480001c02d640a0323010030b455401d00394503031742001d08840315010307906820f05040001c0c00458940c0000608815a00c0380c220498050b15036800c0003c1c0c9110b8280001807000120040140c2e290607007032550440c10505045241104101c10542940d0090f0070181125519082d00d03980075000c08070402c8100c6c0300d003c00300441d050400000c2e40700d450 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 541777868 1250 541776618 541776643
    0x603020a02160f120203070b0d050402010e04051006050a090e18010501050316030809011b0c140d15020f090a030b040c050f0618032a0a0503030f0301121b0305100f0e 73
    0x1301c0500b0401103403020801207002c1c04a40380c0c1d1946a60080d22240c0141c03104890403400262482c2d03d00c80541494010f9501620f004070700041c185023170000c110b441d600000802c03400c101094000055280384c117424240907140b040e00340310f20500440340142c00d545041e8490343c000c1d03101c61120f02401c0701b03101888042c1c03680402250356035a901c20040f04e410800c01c10849102c0d0312130300500c08202c681400380d01150380b0501c0140e4600300401c108001c442050102810b40b40608080101c03c0200342c1c0181444055060418208080880412400b0350190001c44000450300c2c180818091042041c1000303000c1143c01c14111000c1501040844c0200b5150b4000034440342006942c0385c2d400d06c41c69030301c2da056001c1d003428003140006d02264a15113164060190078042030205603410301101302c441c070100c10107a0383d00d56440c0102c1540b25080d84082900c890040fa001d8100056083d0310100080d80079800410011014105c0841141c51510300070b22158a041c48458400b80b0209141c940c025 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 541779118 1250 541777868 541777889
    0xf06271a0901090918050708010e0c040f1404050a030206061e06030714030c13050f0d0314040b040603240501080a1109030d03020304140a020a151106010603020a02160f 74
    0x740000050b501550a038119418550070020916042030301e00d84405185800752080b180001d6680078070078221050307116071450380e810004076200d0500742500441912095000002002115200256008602512308035100d070480100e103818143e0421031a90403a600f00c078400c0080b025242080044e503e41d1000e103002d0900400041c41c140e0043e10602e480420a0541c1650703403a00b504090025400061020708140b603501021400d818070040240e40640060001c80d419001610706484501500086509140080101081c5281c290010704000c103011341300813804c6803018001c500c0f42c50b501c0c80174541c4c105407104208400ea82c8403800350b4100740b180400251464420101d92001c0c4202151075402d84030707148041500b00e61560056200318000c0b84691502c1030751000c0d50307440f00320604019504c070740e00740014403105407c1e400c0032001d00d035181400845807078441419810048241d1107040032a6011940a00c003e805102908010043c81206002e43d401c1041d04080407845001c0d6a0050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 541780368 1250 541779118 541779127
    0x230903150f071106040f0311060a020405010f18120f120804020907020c010c03080709030602070803090c0d08181c05070503060c04030b160c140106050411030105030c12070f06271a 79
    0xd80540844d00c0c8490310304056600629019030b140cac020b9403081c0703d0b59000560820040814600c00c103180c402e20400c0b14404110340340b500640e080c0103100e40750151b50044031300c0c24440c00076100340c040007150b0050781c6800e122450140108400000010090001e41d040060160030503030b80300010507003031a03245c1000c20498071030b014101c9901e421a00003c1c0213a10010b41f1700c1c02c1c000d40d0800345210341c18107000c8540b80300e480c409000819111110003414444180117480440780008a241004103010741802151365003d5240d1520504d182e10994642d00b0582e400d0000b0b0405024156010200d583c004d0300e01403035076494000f0808002c0c002c01608001d02d00300b9140d0761059113030a07901c0d82c01c148001600701800003224001c046622a00b031166140a02c081d1880c10181c00781e0b4125400140078140100740c1c1c2c41030001c21000c00d40c02103c58010290081690145090004007500d215a82c4000a2409203114415060306401400c2d800440560070401040b03110f03010041d1104070b03030459448 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 541781618 1250 541780368 541780373
    0x1a0304030c060612150516140c12040e06090108031309110405100f080a09020a06030c090b0c01060518060a030201051b0d2d230903150f071106040f 65
    0x1003e042d04941d40f041801001c03901031281689200f00d02c51500c01c070800190711881d040341c40524070070180344045400d203050a054800071501510b4218294001d591a580c1d00302c02c1100c044c4d01c00e0f084060040d00740c8043c400e0508101207414090507800004528140d010003c00413070507118030440800750f445401ca03403514644076003518001d1a01a00c250b11005d030144000e0440c5403684900400680000c0006141042c5802a85e42c50b40c4c000d400c10307807514140314041f40034280380c49200b01030040f90700b00081d4401c0c58400501030301040d60b00020349241003404104030010492983e68114085100344011580c60741101400c0342d41c2400e00547d90361445251481c0c0758580b00607017582e401540d404150143d08503a80320b6520311040801c0b140c1d0302000381c0001c40c4000e01503c2500140c56150309c0305c84541480494441c8401c103614190a080482000034035140403d10b030712861108070320502840100c4d0340030f259000a10390400c540040d9030350031042c0e0344640c01000503014003461810b0405 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 541782868 1250 541781618 541781621
    0xd0c0b18100906020c0d08040c0b161205041505070804260d0c11010f0e01050f04170304090b0a08060c0901030905010507090f06020312060f15030406151a0304030c06 73
    0x81d640d60030406104418542c20054000d4000061041880c0690003590403c588280b4021f071007646d0081014030414206220401103402003507a07118440b85400700c203004a80c2d59500d074000a00d07541d40d590350307903410012214038070b1420024000070710805001103400a0000d41c00d40c0c041e5405566040c140c0c44400300c21149005900078070701460b02500610302c009550202e0480202ca010742c07040da510810714001160700c80c1e260302c0a0b100140c11b80b14100469071080c1c008010120f1700b9690142440e8807801a02c0c0c01100c0702c0685011680b0018040105564501030300c1d1015104840d8115400d24004e6029140c0200619010540c000080c69042c0c0e40e0107a40100041a0001c00801103440c010301e01400b0140e40e4080e4802c8441c03400d50016401d480082141c1c5108440039104200e03071220300511441e6550303039000c0e0361300181806080c031400e001000a50310135801900003141810040c02c0a4801c20041d820aa84010300000d04010440c400da08494000d5407502e0061901c0f940d40c00d01c03a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 541784118 1250 541782868 541782883
    0x92414040603241b08060d14010c020102091c0507180f0501090218100e011101110c030a0908070605040b180a1d010504060509060108040507180606020d0c0b18 70
    0x14040040480f81d0625004640404442181002420004805442250101d02c040001c8207400240c0081c005055405c1642e41080c249104e220148200b13a110703100d203800e40e000d059003403005039404503c405040c64540704039000e040440c0c020303000c1d0204503110349850340c5030341c041c1c0c02165108803604900000c49602190000d420144208525611401844061b40c007407121000d140c0740d401d500448070324005d000002c030808503032201100104c0340e00040d107001c1160040380d022550390f500340354001c0d139280e80185441c600e407501440e51004244000b82c800f01030fa0b040b02103203034445c030014400c10b90000c2c00c4409940482c580a03440c0d40100742d034561074150a072003058000070085400107081f110a50b0f000039100b500040004907a80300d0041c003045581c03903c1126400840c100c0865402c0d40500a01b580050060094550300c6072296a6001c814000d000c00d1040103507a030004103c1198148680900c400403460700c030140b800c01d91a2121007a4010f0000d02d0240700c0c0c28a150400c0c0320421100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 541785368 1250 541784118 541784123
    0x21c0909020711090a1b0c03050702100f0f03060e0a05090a120f0306120c09020a0512040f02040c0f0f0e0112060909050f03070b040f030c081201092414040603 70
    0xa55440700540360200f22250100d00f0140100001e01c003165024120f80900644d00056030411030000304091030880b048805413a06074140007080000c00050b03100c800074540c00301c01e1a11880000191007000030860b07850425500205131803d4001c3c4080d224001100740c1000b0b0240303012a86444e50b07055035041050350030009050600415000c080c0a41005880720400c01d591010001d807681e0720101101c02c02c5c4d611008080d80c50040e0184002691030780035055400c5540b0304a400c24140c03402c440900c400030b03181640d030b220000801d20118030340341c00f41c190030681c281380034906010000d6028100d441803c2802c42805104041e00744e03964401c1c844010003050345c3c601802000c1c0c0d83c02c80c505c01809070002c1a45e19016018010070001c40000845240c6507015840c01c4496445031150700811b403480d50304030204200081074401007003126010701011540304d06a038030036500d070035284003c4030342c20490942c2024105d00009078503128100c00001315840341c503003500040d0380c0c40d000400401c6e568100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 541786618 1250 541785368 541785371
    0x408010c030506030d050a02030f0d1b02010906050a09031e030f14180703020306070c080909010311030709050613050a0b030609070f06030212040f03110f0d0e0a0303021c0909 77
    0x11103260580c1a00418016102a0259040f461680e801198203100b840c03c2c540c0564000c01407040b52088a90080c50143c1840c4400907031140070005581203403402c1e88150740140e441d4040750f02441a648500d981085c0130320f00801540d0116a0050601c20500c040400540c0c2445030241503140a600084415030b894501000451840164034240308070560310140c2499802051900e5080e0010b003150a0380d4004008007903695a40c807040b103080c0c0001c6811a50860140215000ca440e1a100d09018611612070280c604000000340340c0340c0702c5590700c42c03620035081c4001d0001d10348030382c0820416486015404074403a070728010b03290003038000da03a050394040c0716030010800c0180d00814100250307a8609542e0008550700d603400c405038043c1407480c242c40e82c4204081800588580242c020303151090034840060141d4216050038042064400c0c011f5820152010b5074441d480440e2070015403003218001c80050554030000c3d0303103003548480803412a8040c0c03c3c40070f009006400707403002410307a40c40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 541787868 1250 541786618 541786631
    0x50a06020a110f01051509100801061412011406011103090a030803041a0709050607110a0605030108160b190c08130e010e071403060609060720100804030c08040801 72
    0x80106111a00000c0c0350550060b000e4403080e40f01c1c103018107809030300340c04a0908036a0540040211a24010348a28021140c1d0f402c0000c114800303000340c8004000400ca14041d0404803024081110440d6205054a9140900500c0b4500c07828040030780210003803803c28031a01c2084a0300b45107201c1d03c000740d0b9000032948000006c101d581e038000c0d84101d200e40c03940d403590400224900c85d01c0c0700648a0001080391103a040c405801c0c00303006004040c3c000c0f1461500c00c460100450000b54440e04800e0000344000014051a4010080c001d400044032150404e43c074a4145d03c0c0e01140075900303240304041d54041021100c0ea1156161020700f5402241c5503603510422030705c1020300300c0d09120300084904047d000203010b0020320380d01446140c42d911150704a64000c1070007001e503840102520b91205090010756500c0e03d40313001504070944038040203148401c400319048007900040306020700c44c0c140307002c5410207690301419140d0415410300306204003074100d203403c0342c3c50b009680002c041507181c080c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 541789118 1250 541787868 541787887
    0x11a0409021303050f0607091428030c0803070510090204140712200319020408070305100609020913020f040302150702040b0609030d1425050106050901030f02010c050a0602 76
    0x461500700c1c1c0c404c10441d00409030386913846450302c208035030b94400304110301c0c010444607584410100d001d050060842c02c1d03101c54609064110011006910f4950820840034401c004132205000007500c03644e001142401a5981e440da601c90175108541000c90300c8405010440d100c41c3c004840309031050904104030316201d80000c0c8900d02e540e58506101d81401d01d0018912a68040b881003044e15410b180d1840d9a2a4801d192024140540d0040c4a900300000621648140f002e00d0245200e0005407031491101195203090b682c9076044003d942d031040200c100d071542d9282e4500018160042d0245e05c51100b005100070314040d583c03010f9006140b01c09415000c090a80060100b203100711010008112640d050080e035009034080590581e12240098818600481d00075100003003d000c164501a82400c080b0640d031922904200c000c0b88002e030100801034203000b90740292005896081480d0b24544a05180c0d1b88029006418840894801810700c041130204044a54011034117540d01d100741e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 541790368 1250 541789118 541789147
    0x170a0f03121415120f0607020d02011b0c0311120703030e0d09140607020a081926040b0c150123010e0303030f06030f1203060f011106011a040902 64
    0x80d01c0340d4022481c0064010b8a02078070310b9050300580c1c001c11200c81e000d1018051065013103100782401224810281e0413180610100035052280ca031548c0542140c0018880103425a5041c0d0b012a410861710420080031b541c2c05450030420715050728060400c15582d20300141401180018104900070004001c418180c0541043e1682c01818046900724805940221044600c0c0d00540e01500f03960300b600a030514050015003807160004040e488030a07541c1c8000c41c03800100444481480701201c0882040c090070703070a59602d68070000e82d44140080c228076204450301c2540245001d102000c142c0703901844080051400782c4d13917111499034465840d4031001d9010140150304110b031408004001c42554030500031000282c10150046046442d200380d045032826004010315018820041c01d480440810000801600782034041c1aa0700c0c20010b0500c52146aa01c2140d4140154107411001c00350b00040d940307044488800f040c1c17018101c2180004614032455000b9031201c1e0001c1414060900c10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 541791618 1250 541790368 541790387
    0x20109031407050a060b061c0b0906030a030e09071b061b020111091002031e0316080606030a0f0605060c10060f1a1c141915170a0f03 59
    0x7030301c0c0c030810340100c10280e94140c41200401862504410b880030001400b0341c000788030f00400280002c1c00e110345420610f591481d4803620304030031529040c4810b040e041064141d60450070680103004100e8507514041d1404080c880141d0040c0d402500040d00f031403061505400e405941d0607003c0848905060070006000762400441280080d480002e06c0d0900520884004060f000612424010f0240411128104900740c80d42036000c200704081403218240600d9201c00256000706807a41000411408060803000072801031100d00b01c10700045950b40c40030359600c80701e018000f0070342070034107480c40001d82116445203801c0100031520020100c000b1841141150542904100d4035950b0280045503031031501c00c880c504048880160914031920004095400350207510180000d81c114840e0221440d0b0007030340004031041c81c01c1c03040807a02c82180070070501410704240304e484217161586d80d4110083c4115050034034103404550f0000e00c01c2c4051507009400c40d15194480030141000380c4100718 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 541792868 1250 541791618 541791623
    0x21030304020909030a090902070809030105071101050601020c013509010f050c0f0f0d09020904060c030e0c0a091a0a091e020f070f15150501020f010902030c150c0d020109 75
    0x42d80c03000190300040000a84480d41c6150703407403428061401403410003e521000d000d40e401c00c0c0800c26902291000d000300c6028034099950440201c402c402d0050071503e010744501e0454020380301c1c8a405a0b07009400030b902c040c1c00114004d00440c00c0981c5500c440300c0005081e6090390050400c0030300a01035000d000442c0208009124030380e01e080c40c040080c481c4810311104494284042003010071000302516032004603000000f6041140d8000500582c0e080b6011642151660000140709a0501600560201d90001080c1c04207000e03000600824581c041c0c0c0e01710030303520502004413080e490303031070b520501002e04080e203800d0315908988041c00034a441c1144202c2d2200c2180203801541c822192100329441d0004d05200c001c1d505d055080000380d00c00d4491281d01e20388110f048025200e400c0c1d0100001d2524540289020300183c100a00d24841417280e0b450200e5010151314085038194601c4c0044401c0406201c6a10344002d8034000c0080c031184501c26812624200d913015809244000e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 541794118 1250 541792868 541792879
    0x3050c0c0607020d0f020a0221031b01021305040506010c080a140f0307021501061403102304050a021810050708070303060f0e0702100f0f09030801050a080f06040f022103030402 78
    0x4005081642d03507ea080c03c0080d008840294810115400c0b072200000700d00f408015280703415201341619a25100c200c00204142c1d41c0090000703112989450b1420092509541c1032004d46480c4001030705940f81c618003d82a65400030711102d0251007800d6582102030101842034507580811061211900129001405807040c4505038241c02d80c2c00302c0c268100d442a0b620726211039a00c1c0c0c0c1d40082600040c2c41180c001c19018004594801e280702c0e0b482030f0324003081c510030681da01c10042005841000c2c1c05442c5a13441042400800f000c0500a54402082a07038110301c00c103c100d108071428426210040e0084a0100da440100350b40341d0002d004036102e040d4905015900d6501d04a40c02409480030360142c0d0100c180c1c0c181c00741d010303042041100c0003070f0000039000c3caa42c10410151040140300324001140180140f00914200c0c400b84042d050b000024040c1d032502008040e520b03078014002401c002e03080880300e4110b5903004090203078015010b429081c4c4070a001074050342c0f904291000c80c447e5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 541795368 1250 541794118 541794137
    0xf131b0512060a08031606061205030c0c0f0a050609190f0305060609072a140c0a12030804032d080a14060a060e04090b270d0503040303050c0c0607020d 67
    0x103140058030f0009403483c03413000d545046000c1e02210101d01940314211a601d895510010b1040358501081048074010805103641d810340c8150729060403200c0b03840d00c1c0b051284040e01065a10f60103110416180282c070200c3e0343c0c903400303400210310041c1440001d8035000c0404001c603503044007803408800c50b40708030308403003141e00d40d44100900203408886980000c2c545403040801035002c44446500c181d140c0d10908964521134590b920403070340002140b8903540c003c80e5010031030300b0030080701d034000e080b0030400e880e0040365a50300600d0004050005010892400d8400483c0c0019400c240210030740300e20031031040150b0003409020030b641121145400b030728007417600e051003003800c611500c64480140040ca18a0078080151500441d03a803510b50002c0d030b11403803d40064443c44036039000d2100000b1110001410601810318800d040310380c015182c001130f030480200768210050b00e4200da071504002c982c5a0300e40c0301c1c050700c601034203040720740d24071441c010301000d40c3d000b00b2107601d00045c0e0394600351803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 541796618 1250 541795368 541795381
    0xb28020f09010f05031e061305040605070f020729130e0a050a150611010b09090a1403070c0522021614011401120507050306100905070e0f131b0512 65
    0xb9005c100d0f0480d2403002d5441e400b01854840110599104070010204180e14130522628411640c1c12101242e40e00e541d1018820481d07040324541c214103061b440105003060810f440c070154041c40e40c48070341d050311281c0b26004840e0000030944483d102035582c0200150350700c3c81035041d040000e03070300540d450346001302290010915001d4840d09064041c40c440360545040c800300c0e28844002880c1c074172950303503c003002003507a140036029001c0c850703000c0200101900c2c1c0c10040d1860320300100c50691580108101800907c0c2c403c5090122042181c10101c41e040d410210495a1038641c000c0105920004000018a403055819401d217402400425410203150040a080b0307800c0f8401098a0291440104034541038170f4407958525110300d09031184559a140130034035144042c0c131001420400b965003480128540d1040d075a0041c003500c0c101000208600100d40346810342181c00c0d00403070710b200141500015640120b4241c140c051701a24108000807002450364102d1030700c519450f409039011504 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 541797868 1250 541796618 541796627
    0xc050405060a0f12150819030801120203100507120506010504050102030405190302060a090e070810030305210c090102010b03070f2117030402011101090b28020f09010f 74
    0x5903040644140e28000ca0950305072600300014400e241040b40c0c00503100007030a2680150000300f100e03505460806410000010308203600040345d10410200701101d080401d500802d80f82c112402d000d0140d04021003800409d041c040384125000085081c0810b102c602540004e14642001d40d14400300016140c0e4401181c0c14401ca00c0748c140141c0c003d1000f4007041c50101d9846451110444050550343e0790782e408550181c05c8405a01e001c40e0300c0c807400704190454a040a980146286400d85407864040203414800d2014000034003004804032712003400a8bd4082e030800034400c80348200b290340ca0113008102c3c0d136031b200034541401542061124503813801c0c001079103c241c0d001401c148034003505001842248058180420394001e1807800440f011410785200b041070244901030032580d070700d864000540b81920810030890380f40e16029095021500b003001154000f50075102480141508100c4c240000c070b0802442000b1500c0080d928090451380b000034141030b40280c03200d5084090384002980e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 541799118 1250 541797868 541797877
    0x301120311031b0d08192f040f1a0a050705150a050601090527060d08030405150c07150b03030702041409060f09190f1b0e1b0f07020411030a050a0c05 66
    0x1800484186941c0d03422011504070405902280303450000c1c1c25101345066400d420042d0544130420000102805201c2c09c110f9407030050050300d0f0004880c1405440d0000462041503260400c00c100403658000b049414040031380300d803015480b03404907400c01d40c50100040009a9400f4085010400700140c5030401c443c5120181c46020040440c1c0017203071030400c110380300007040c1c00d52010541c01c18000250812000d10300a5001d030004040000791a1600c2202c010f000e0b0460140c00000d01415001440380a614088103c441402080322000722000c81d145000700440254002d081c4404800d050700b2528145200c0d0701e030b8104a8269464051001d040b280040e00d480485800040300e61034a0304400d04540c92551113203007484004d424a40f40c000d2545605480742c070180f207901c00c0030082d01542000c0c00b40c11074203170038160301c60001340c03c0465880d1007954031901403290b0114401080d543e859016020001d6054800c07552880c080d14580010142103c234181044d00d031007401450340b4401c0e01540c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 541800368 1250 541799118 541799131
    0x10f09030221090303040b03010503010606143a0b1327030c0605090307030f030c05070311071205100c020c0d0b040615080109020103200301120311031b0d08 69
    0x2040c80940c5030401102d94201c820b07015204400420a00842c1d0300c080000340000c00354200c02c15260350500d8101802d4a9065020a00704142101c001007829080d05c00c840300c6560b00709180c11034035202e0b642010061a180740c1c1c04800c00440110446074800340d00510303c29041160307841240c04601c3d90b824101c46550340d640c08600510846e141019075847c001248a07030090400210b0081075235030741016181c04480e6403000e030b0000b1690400301354004181c0082950719080510562134100c500804070300499038045e0411040240c11307400c001003408148043c2070306685000012000e400c145a685105503503000080f440c2c4440350f0152880450000c91006d0018068194450b070358580048008000c0e06c1910295580c0e08540c103101d10310f0184e00700402c1d5910011507440344900014045492180ca240503204005c202d059032107690f01c00702da040d50054040240d030f4400c58202151141c881c031840140d14400040e0509280400000c901007c201410803505a58482101212821070560300c5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 541801618 1250 541800368 541800373
    0x90415030803130f06050106200d080a020a0903200a120b01060e030309041416110a06021c02030f0109062301050a14070f03030b0105070c1404020d140108010f090302 73
    0x89148508640f150020180c0159160040083c11392101011504280e1180000c40c103070b100c840003095182c00c00102075160380000b41000c82c40c1c80074045c0c18003034024902d00c031540cad0002d41019064022400c01e8091030704220403402d40348102c1703400c0702c1c10b000d2804000d1190210000c00605100960703030748a10b40d98444000303d040d034a01030055450700810310a9503410301051055046036250f61044071180c0c12600841c07455410030303004143c0090320844100040046d001d80a144403100000e400070700a6003c0001640c80c06d1031040603005a01d0490004c48190000007800b100446107803229059400c0b502c0304003e101c0c0d40700e0720040d00f002a80c801c50445182168441e0580d070080000e00720106290030242103020100048070351030381c44020210742040304c5281140905500d44a19200c43e2000e01301545040e009403200d240580491080003001507074079103e00c0c0d040d183c6030192120b440c681e403010f10419201c03a003058003680c02406440e00380c1d03113448558411402c041c050140c075a07815401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 541802868 1250 541801618 541801621
    0x30f071e170a08030403141303140a0f12050f04060804050c04020403030e19090e0615090910020c01020910120e0c0a0b1b030a0c060c23030603070812090415030803 72
    0x20f80c0401c0d030308020811340034811065100a803051300d200050a5008201e40d1402600342107142c40100ca400010108020740d0003410803100044092181e45201500508026600108040c0440d401e2060300030304c4450010129002a8840d00b0420050140e8403802c2a100041c0080c0e040c4030403400b4a01c4003400003504d070512009241094003881da903e08540c40c15400a684902038901a611103502d4511260300043c01c101c0140e0ac010305240b0f038040215580300c03141c1000d0300c2440d510003203680e50180d241e41c005884d081c08882581140d1100e10301811000110741c0500000d41409144200740c0708450034600c1b2801c50300030104600000042c0140400300c0079042c441c101449411030500414107070352481d098a0301003003c00c081c01c036035001d60b6240f52540506203040003d403004030450205104101449481c00301000304521081180e003610349440b5036542c80041c2c54007810b0343c0400c0442c00341c50440720604103c403000707040d48070041c3c2d0b040c81121404025003250450350711016158160070300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 541804118 1250 541802868 541802873
    0x1b0a051b06120a0504230d0e090402060a050d0f14070f02071503020d090605100513060302100f0e131505010c081228050a060603140f06030f071e170a 66
    0x2800729405c940107400d4103609a212440020070300c0e1a40d041c0103041e40c051100006404e6000210b51800c59098900f810390713080541c01314105006005000c0c003801004281c640403401a50301507140c03080030751020b10545495410001c8000000c2c0c403500000307044240c004880d20300004007981140c10000b409030502501c140c00700c000750843d40036440c2160710341d0941c03400f060306409814081c042d00554003101a29110821402d02c190b10094184d090822504001590390820804150096400d200800c0369000b681103580c0810180880d6000381440c40d000391504540d1f202e281e0585140841d030010341d0301d500040d00c0b148664640100307181e408004800b002801031381615040300d9640103014202c06481c0307904041070b49a00d204401a0f5541c010880c038079681d03000700c50082055060400407150fa5601d92403282c80000d00d002c2200c080c1102090441c0c408000710221143d0b14015912541d848900a01c1d500320711034806504884040170100390044a0b1030110703180c03242000104034640999 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 541805368 1250 541804118 541804121
    0x40b030f1527070504180f021507200306010914010306020a02031218190206031b0c0f030c2404030e010315060807031a03121b0a051b06120a 62
    0x42005a030942c01c040b810402c800301c0080c0d61020305101001c0c0990300e0422082c401118401c510a001a2458040c0100860007880382900d08176019902030f09210b4401505620a110f00341f0020010f00c800e100421a80e80350300151003e21a0440a90300983da0301c0d8460400c3e00d80029100034030000f40c0004000041c450f90081072a08800d0050320700f4071800c040c0103400090300b02c2d01e1035200d01d00a18207801c2c8100510150300c001148007140b91142c031554000c5000c034040180410003110b01c9124104c000ea0446060b41c059401c030700b0882d41760380c1d45051419161740003d1344e2204c05204401a4000e2845502d00b2008100707e208540c0c03405d0341c0d0355282100c0048510415074145540e0f10700d000c111b501b807040080042c0c05140c40d44181d604200d40001c04495089180c00c0d040303010200103007800c2da800700302e040c4130b4003000c8902500c42d00c22118903445a5914038110406102d07440d0242c0800c10081250048524425140000e6191100c11700480d4428000f481d06000e08800c00a4409040f6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 541806618 1250 541805368 541805371
    0x304060f06092d060819152c07030506070c06051e04020d030e130c0e011e050703021f0903112b11060f0a0b0a290c011a040b030f15 58
    0x28442c001c2000d6540380c2105c0d0400c0c035040c1301c4204122203140c80d041401405e200b104802406d41d03200f00300700583c41311100740300841c04590400c9000c00100744c00004008000520145800c0015a0001d04101030003921407100842c00f1240f003414400054a40c580d2107000803821410707000040d0442e40c0c3e039803c020420040080031018800090944000794075100101c8a070700c2e02400d000944508480b40180c941801805041d04000303c4100c00d50701d100900b0500b9020b0b8038076061141d00d41d4210b2a0503410041c1864140c040900c61034541b518400e5290056103c5034044d890b903198004022100b651288030016401e91201100c000007a800600900640c50075000751410044142d0020500c03810030400f612f070084038178609800e10030000c4551040c0000010202c5100c031f1014607000d030690705010b00e143c9016001e54259070008002c1000400c94040b007660a0007017021748488580e0102000140d05500d018a1030034821848038100040c00c40c2a07860794900400390501c4149125006040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 541807868 1250 541806618 541806701
    0x10b0903070305030304060c090e060102072313091202030708091c06020307080a0501050d02031c0e27010e090a15020c0106061106060109150309080f0304060f0609 72
    0x1d006002010070f10038405140290320407070003c03502c902c042070010062040703070f0080c074501e40400003400364581c0c0000d446402c6481d032000b40c15881000c040c1d0001c407005050f18054004490400d82c0720010b40903481201250322031401d03001c00c0000c0f101c0882e640c2c011900c001703080c00810400403c152a0401110714030140d001e0045a10990f07680e50358007640c00595034400811480c07014403030106030078001d081c0548026612400c1c0401c554000941e15444170f03089440310300030701d64550042e81c030460450300007000103010743c0412030000c858032421441111605005213a00030000c00c004082c8800d190103203484400078048405d007078840102c0f10f081e81c18800441c0f80c1c01c2180b0b41986200780101d20040c0320507140c45100c647e82e01403007401c10100408103410812584018060080c11000c042c00c0020145000180031030309140c001d0052241f4001f00002c1030000c01000100155078001c5450842203800500003c1d07a070f41d035203d054030b07446610305c01e1641800c02008119100351403c00131410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 541809118 1250 541807868 541807873
    0x309090608010212010b0d20090307090216060504021908030d0f060f14031f090201090504150e07050f030c0405133e0403080306030d260705270a0608040803010b0903 73
    0x144049023580810100b468458120400420b80c40c1c1c60f86818441c080040c081d40005524017259103803a404454484200146174640d100080f40039519030300350300b1100710120140440c18949410f10b50341c4d00c2e003190082c5419142400030800314600310740119800c5449100c81e41001a080c41c04100445900780480e5405210301d411180344450016200080c4000813080080c91110070700004218400395005075008a08214500402d03c800410f0303c1c044400f501c6d524800b40c1c8030318000302d40340c1c81900c409103440c076008010300c40385007403c0c0c0c0107108030f46003110811110b40309040c0f00d038151120542861803580000107440c002d21180010394140c82a2000009080c00300d00a01c0c62294101d900191a003020120800038941401c2084000031031141c00c0c0002d0380e0309250304500000c0360108400b1035520460000c5034030b0a02a4080d41d0b0084209850050000c2031618031540c4500354040c0544a81d40900c000241d0a010303030b1075140210f400003626032640c1e00380410f076030850307104064403500b52 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 541810368 1250 541809118 541809131
    0x1b01090303300b0f04110d050c070602070507060e031908090604050d0b0105030c01110606010c02150a0f020735150906040b0609091f180309090608010212010b0d 71
    0x6850081080b54200140c0d000502040f070001400103049188840602942c50032404104003480601a036074180c10302013022034a560354008900142c00307055402094940045100303003c100d004200b0900b51500703642ca241440f0000310406035290117942c0014800090307509680c0100f10140020f0030400d1000d0841c80c5007a984e040460024403c01c04190340400c24800180940e2a0901c4688481c1c1024070f0004407881110f04400c1c4c030788001501990621a0618400701103448248010100f8030ba203880c4161600c0c0c54402c040c2100a41c42d03448d900501031100c0c04600c04601c0701e200503014604849004c145d189000244e42d0a1b00c07808001b8003940300d4400b05a00c1c0c0400b14507801d104103032903070240c4114245440d1014090704068500c03841034024800f04000c2000005e40d1000c00c41c0080a0002c45003c0d00148400500c05a0b112450140c40314004500741608005144200c0c0c0502e08200301b143d80c1e92581900301c2c014041c035000201d4110004100c1c8006240241640c1c415490000848 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 541811618 1250 541810368 541810427
    0x1005090f090402040e0a080c0f0f0715140301141206101a132405070b060603040c0504050c090324040807030201020d2901020604170f07020a0b07051b01090303 70
    0x400c034071440b04131361f103010000300810407010074061010010061402006000b03011342d00c0781c0d12522140580749542c10b0003400c5108280c4105000c080354403240b000c65540396101d131010401c02c011515200e00401d0110400c0c40c4074800003030024031401c40c00035541c520798140038841c2004000500c03c00c040e6082480034440c0040340c1d4070410700a024401404410f40c041c69004659140c1152143c03041c00350502c00b02e0081a15500325651040d011254541e8941d100d290500c0c12803041d404c0150014540b030104100c3c403e40d0340003403602600031000c95410007200c1d01c080740200881100108091621404140068268800f0780346280c444e00015050525102d501401c40c3d104140303440380403130140e440b0b400e9800b80c0c1d02c00480004c1c0c20301c00b0700003902d05526a0003400040031900c400014000455440200d41441541d180d10750061522840c0e503900c001e44080e07a04541000e443c24050f10543c0c45900e0b07410f0741c00b200e01e0301041e100c40c13940703a10b141c03020380b4111088014502c2000c4c405104055 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 541812868 1250 541811618 541811623
    0xc020a0b160501022d0405090c0d020c070303030c14071101030908071a0403120203310204090b060a0f03030905010311120f040b012117090d030e1005090f090402040e 73
    0x1500c45c02e0503580d86850804180071044442c9070000c00e0074050800040c04a52076240c402d551100040c019656501d80b00c3c4a184020320618910b00b490303018034100441010383c10742103403103400220307030b0340b03941103601400128118400c0c2c44008005103505841000a54001d800c8024030074000c0989904140b080d4881c0d5034140140c0000040540b410820402007541116079045030340078082c0b0842c11440c01c2144039040c0924032000d0045100c0042e94031001080300c012105000e98054000d001c0c4031540d140c205880041641c900344500503080d0301050480264150f40c040700d4044c0d0742d040241d443d110040d40108131035010316a800604118014501c4a00c400700382c01801c00c0c0241d40101d141a08011240724410307000241d5900740c0d00c080340c40384600b81c80e8000d0070742c0c1c000f10071007129a200c0c2d20041c5544100d0b074810340c000014405010505821400d2510075100503612106190402c8000f02c80c1c521508850780d80c800d038410302e00d07001800c205541c01e9200e80b02401c00198148200e0742c061 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 541814118 1250 541812868 541812877
    0x504050d0c1e210302060402040504240203180c0913020d060e0319050405240c1603050d020604080f0d150b180307031713090617010c0c020a0b16050102 67
    0x81000e881c1020400039201916195442500c181c1e2901421000e80c0e0b130300944641000e17102a2099403110045020300c0b0b0b80003110002802698241d250080703616441d50040e40046030510700307150690302d43c03101031203010418074031905000340710b07152940d6003405243d020f07051514140d03007004000203c00c00003131951240c3c030900c0d000400190307141d01407480b200003400000003507142088001c1c841000b00e0f840c0d4229500351640d200c02c102d0412000c0790b0304401f450047c00100ba0182c852466900500380040a8220580c0c0c019016a140b00366801c00aa940340c00594006011003010040341c0716000300e22010300f54030b0760358003400300b60504112030030114224035801c00428200005911802c82100c2c80d000854a4000e9001c0c2031401d01d036450b031640304101400f03401d080030000545485030901504000d000b814803208204031982c0c54031034041240e28143c615035855840c1145101d4054085c00700072401d42d0740180000c1180342000d0551030141c100c001d203281e5050034100d003180020f00a00282 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 541815368 1250 541814118 541814159
    0x5090405070314240a0b01030e030a050706020702061b160e010e04020103150b03060a050a1206020f1204030509130e120c0106031a090c1002030a0305100302030604150c020d0504050d0c 81
    0x44c030050801540b1081142e060001c014140f510f400700e03c0c0d001c88808810303240040c8141c140603480710018200340c0f01078461400004d60107070002905101307074489410024142074076035049902a01641c0c1f80c10501e100d05002e903156150703400b401040300c002d0122010368440d1040c94041100344c020b948170601244075402c00e00400001104000c26414044075400040c0011181072420500c0c06000b09404940d0300d8028044c1a00002ca10410244c0302c0102c820710445c18104002c0c600d001d0400919070780040c503840d4803418441da881d40912103035000c0d80440300c42440c041e2903540c9000c4900c00c00c0364840e84440c0000e548544000002c034a03448000c90032294440c038041500e2a090240b1802e041410030118415526110b4a1004540c00070994070b00000c50306000500d40c50780320f43c202d20700d03c15500c0254103100d10000c002c10001104200315480440c401c00f031000040111041c3d85546005a001c0001541444100b20b589000b9105541e118003d6600301c8040e030716140440301642109050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 541816618 1250 541815368 541815433
    0x408010f060509090a031202030c16060605011205010e0f040c0815010801060603090830330f0105030a1517122a011b0207050102060105090405070314 66
    0x104210f0a26816840c1d00445a01c060721003e46242c0d80a0851843e00c5a200039007035003c000502c0e5180100200c40c0c002d620500780c854985114070b070010117031656016a60001d002d007028441c101e506070180714143c44200341022003035a82c84406c92104000108140c030300025213400001c640005000103082030110450326030466040c10182c90039175041d5480541054500403080000c88c0a03041510f41000d5550901038540314003509481070800032034042405000b081040c0404031101064002c812460344e408245a03029911300b5000800e0303150070303a41d0130001c102c5c00031125610542c020340e4403081c1e080e0006044c100c810240d004000f03807900045840020303d01c545804000030040300790100c1c42c1015045c034000d1a032180c0b00c11181181001600c01d00092801a01c00d24290444041504105240318821001c600f000390b6840d1640301c0c00340507002c0c1500208980c00e026480030321841d04400144001441c59031076240c00a0b04c5000d0810f01e02440751a0703110507030400091200c0c4144600c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 541817868 1250 541816618 541816631
    0x1112070302180a090902190608071b05100c1706030607030b030f1917040b16140a0804090f050f040b090703150f0b0d03020703060c02030f1306031d0a170408010f 71
    0x612240741f442c4020500107202043c0300300079095002d0129a809020303460315481032440706e403204ea2004404a00144540607495968400d00090303030101103c0000d0740e0701e12200110300c03a0700803192201525076940541043d0300255031140030344c01c107c040d101d0103401c56800e20300d5241c480e400d2496807200e040c11340e00c10720584410322804810724101e0001c22030342907150516013142c0c0302c0144240d004028198070349400c05400d2062811400480d28914030503a40d042c2d4503450800b01940c001d0042c3e4404900d0041040d860b92514414148111103554800c401510703a6215002d950170000d05804140c41048808800154030307042080c05441480404600c00c5c41142500096403400b00c601c0e801100811036100101e03078001800401c0f2504131000203102c1c507ca10041b41180300d0000402c240000004d40fa160610007c4541400c803030950380e04009640000d21700e207882c8201c44403171045550020484002003207000c44100a04034005490314649659620907509480704050003540e196038804 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 541819118 1250 541817868 541817873
    0x130308040f0806061c170403080c01091203060b0702091b0f03060a150206130302010b0301020f070c080307030c06050606070b091b09062d03010204030b0403031112070302180a0909 79
    0x985030080720885030181110080320707050f8110481d0341001b500303168980f00e0206103034141c0411100a03640043d145039840d020710319000d02074140c60301e00300c82811701001c0c0e40c1d213698428440d05c401d0f1a1485502d0b481c14045408101c0e18100c003400d040e0814034000304034041c000e42003000300400c88006072281e0300c900c0e0410800c60069a0b56012000c3c254504071100c2c2a140c1c045442c0307900074010030059540c89120f003000c9004041c46a48a0741547c8000b40341100c8800e01005040040d10800c59550b4040d11000b042e0703140d000b60034009000c10301d070005081c0007c0303d075005140d11200c0038000c1402c1001e161600e200030901918118204d070000b0061031400701c20244911110702e400c0e40c1c591140c2c200b020100381c04948021074101090001c101366442420b402401424214004000b99107403a140c0c24989811941a90100c02185c50181c294000030900400e807403071501034030000e000a40d41c0f0030b82500a940800c000c013121b2035122209070b24a41d2080213000c06812036241c005015a12803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 541820368 1250 541819118 541819123
    0xc010204121401020f0702091801231e071d090403030b0f090106121a1201020406020d08010807051512162019021309080306090a090b010b130308040f08 67
    0x46800b1a80d00401004403040c461004582c4c0465055880d010a0b075194205840e00e449072072803d010650070002401480010190641170030324424507801c160ba150910036052101400d40248100507541000414060080c030440341028038003071040103417000030070010f04015000c413001c4011a550380c88203000d5041c440c194500c24081598034000300c0d418170300041c003440b40c80d041c005e4495440e02c6104103031588810401d00d01c0c040142000c51060401c40405010303400ca40602c00c0103200e060341569501e07101c2c02c00b590403a1701ca80040d2500714240070a006120f0707030700340c0c00b4a1141401c00c102603600d480002d030a4410200b0000003000c81c200004004d2a00702d0480a00c00070040e901d10a66042034040752110740407107420701640c0a07511030700c04190341150b8001c212020301c0c5825041d03800e2000c0c520086100b258101d40c4051142d0b548040c91040f200c030f03003802034a40708888006204d411810b40c002c14450424500d40320996603a9a101000c95125410001040504083c104800e1808 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 541821618 1250 541820368 541820393
    0x60507091a210a020c0f0a021009030b0406150b2107090e011511100903030501060c050d030c090b0706020706140f130204021b010b030c060309120f0c01020412 70
    0x4007104540340524050702c1034200341d0791101d1002406095004924101d085034112001e01203031206642d038086003030300025120b040100741039004005408103001400c1c403650822007076035401340011200f41c5580e11030400800341080100c0340701e101d14601084c4107007801c0192424640f1107049001d01c07010710a41c0d07002104058420018890082e100740803c40c0440c49070b82c15603c42d400489658081d148044803a082c242692420500868118080440c900d400030140341d4000d81301408144d0303a4550850b03031465140b00c090080e801c1030062018441c800d400c1398491035440e04c2c0442c49182c4070b4a0010b001c1e03000c0c2600310b07412030740000d40504100c05402100d50210352021045028540b21448081031900103101421b25246019840210350300e07070b810303116054680043c104510410340902d600911180141d107109105026a6840619180303003142c0c81246000f018040281541d0441d060701d4020b0f00c0b2101010030280301108404000340302800080c04502c102d0420325500341403440c5031151 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 541822868 1250 541821618 541821659
    0xb09060d11132301120f060e22030e010c0c030206030c07050c041506050c0709060f09050a090c12110904030f1107030803010311040b0a080705030f0f0c01051606050709 74
    0x2441c0103900401c0c0c00d0340c6003140800b00f805c5c0441d0090313840c804000101403000010075440d24244012481001003807080f88030305400b00f06903132104041900c0e0110180131000042c0041c00f400842c07040e5500c603041400c1c1080c0300d0014180001d44a41c0052101c3c0c100700c82c694004140400c04600b40a41013001d10640b41050702d08020b411000000c605043d14280622401e00c88001100007403880d00f040141e00a040c00e1004000442d1590f500b45039175089407040070b508600f0300d00801c02c10f0b070680c440ea1140c2644030301541c035190328000364544000b48011041d61510110680801c583e1224009103206521030340d2800074900c0010030103000002040600e603c2e035807103e842400010350203400c40c7c0c1507a420502c91030320b402c0c40000040140c08200c00554001c2108480020103920000d10102136400480c19950b10a0303018810319034070090342003130268542c0722802c001410b5000701d00800403040a11100d00403640c494035004103803402510940e001600c1d40a040150100b01d44a00803482c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 541824118 1250 541822868 541822889
    0x7090b120105010f0b0d0e06180d1707180801050717010816031401020913020a02060f100605030a1d01090309050d0c03061107080c06010e0105150a030e031b01050103140c0a0b09060d1113 82
    0x5000080980e0810b10043c040d100384100000030081c2054a0dc50800c0280340080080c44946886500240810056104000210013080000c5003840012901000701d074034208003403039603c0c6140c640b400a540c910703003802d80956003003085024540f201418900d5a0103182030260f0307100c0380d03087c009140000092a003009000d02000384104800103a2406040310301902c1d10b0b0761251144121400203000b41d0b80081c40707552a1030100003184006400c6a40954046d031140041190782c1c03014444410b00413800280700c10101d200a10000e409544088034407aa401c1c0414209142a9511078040c3c0c40010741e02d10f60781c0640c00412000d0f200c10400d60150100741d03007180d60400c13101d10039030b264002d020210301451f071605800d50542800300141d030002c8445c10410400540d1080c0000d000b0102800309a4000210111000c01c82000250115528602502e14000076241101d481c0c0c3d540c02542c400d6500c0001003045207440e0800703002c1c0740d82161101003055a100503400030b60384940403d501442450 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 541825368 1250 541824118 541824137
    0x204032001030c08130c0b070521210a02070b010b12060409020904030e010c02090a0e120a020a12050412061b0e240c07090b120105010f0b0d0e06180d 66
    0x4a030300201320343c0c1098281e94507590300e008900d840f68900409800061941c50301080700c0042c04000500e01d25020f009581c20001e06040c1c0b184d2006522405001c0c00240c8003540c00c9c82566041c03000d40540c007800d000340040c04d0080580d2900714802c020703446a62312980101c1d08810f90711651021ba5001241114200030159035a408581e4020000b00040c080c884514015002130340034120340c49030951300406080e41407400c4c3c1d0b00c01004100c1c205250600d4820745882500349044002200d004080a400522200d001c039680c250007400c400c2c01400410409000016940d200e9960300450325104144c045503400381000e0400602d00704400d41010886604080061600c8850007202e004405820809000381600000d0840b8410000103480504c102d450020f801046d07540614401982180c2502c00655102559420b992081c082ca40410480c1c503010081e40307a0030401050180c2044001107400650011120b003802000c403559019000104d441800b8035400303004075002c1010340e0030005e010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 541826618 1250 541825368 541825391
    0x3140a1d0d140102030a0e070f0e220b06090a0b0904020f031608061b1c0506120a0303050a150e06100903050a050a0611032503020c01020403200103 65
    0x1000314090303512114140100124005403a00c501c810304071500704044080c507400d00d5000758000e44c0204e68801c0742c1842c01c41c1d07030040030b5004100c1800f181d828120014949003001d164161403980070303102e95500841400c4000d040d45040104006440c0520b40300c0f80c0c1454650140151203400404119083d840c242000c0c03c10360b03583c1d002c0c6030081d4058403048218404040402e140c0105401e14021004080b0000904580006040b40c41006444540390544200940310206409000d580400d642c3c1c5482c150030051040d54003032603100c4002004d1492440d4440c40c140e080029038001a00003039102d00404c8501c010500601c02e4a0251f01d40080720f19240c0204040c014070081e021501c40c000c54400380003014030406050300078503040402d54140d216940740c0707140e84402100040360f040d42407484a24100c3d040314103607840342d60b20001102d50300c0320501d4044030020611108109042e42444001101d100034800360000d1403148002c1800c05c0044082c074440400c9244205041504001c3c44114 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 541827868 1250 541826618 541826627
    0x60f120703060905060604180b1b040801060f0501050304020d032d12060501020304141e0603070c030e10080105012003030703020c0c0603130807050a200f01020607141c0c020a03140a 80
    0x207000e038111038840d482c0d42b41c07000903c0d100903c1f0281d0704c400000104000c50a07000640c04030701114070491601c080d0640d104015240c901007140c0107540010a10007040129000e81c400f800d204601d080581c2240c0304080001c14071910f02030401d00007030016944c0341800c1065200e8100648000d000950070503181450307003484402c1001c6680d00a9001a441c84079241c210300c40360b546131400610f21612450712040c024525405800c081c1d001500c90310504090303082a03000d80213018540c0d6140000c9a00305401943c54151001a54821030702c611042d04a00344d06002450140d003580e500980e4801c50b1588403840c249165811500c102c004000340100032641407803460403a9400b001c026103800305400c0c42401e102d415180a069403100105614582c0c50080005c800b03588201ca440b4608602d10f001240d40e40001c0794000c001c544e41e101044400300c0414090000191a0320760120b40001e030350201001c3d1961f0003121005603110400b10300405d038000107610800305415103d942000322120f0010b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 541829118 1250 541827868 541827911
    0x309260d082512181502040b1902030c1e0705030102041809020a0902030f0402011409090103110a2d170a02010c02011103030f0901110f03060f120703060905060604 72
    0x1001901100842c0c0e0b07441d008072001e06000f100404204038498507900b50131842000b4240072103481d90102030441401c16180700343d40c180c43d480c41010342004000100c0d030110302c0c0e481403e401940b100f80560142003404000c0d52112541c502a60700f8540091440a40b41144641240344a64014031007402020b00c008010001d8540c1c80314040303250aa00c0c0081180380c580b941007400c0d640d00020401408030041819540190702c00c0c0d0b20600600b10f20002003c4034000c41101c03d500064543c0104045405d20080c2d50071038000822841d0b03169521480d0001011001204481043c1094680c101030307064403401e100148401024008060740703008655444401c01c0350000c0c140684c403002e150942e4802c03590a01e00c65801c400f240e03a031781490612203640490465007010b00358280103001c0141ea03200381c1540d20240204004505603100c200c10030080d880b6a900d210741183e000d284108010100f0049840150700400c00040c8194442c202103040210080c20700b40943d0070841810f60600c034050310304 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 541830368 1250 541829118 541829161
    0x1207060b010504080f06091006030807020927010f1802030a1b090c080412020c01021005130b0c0d060e04080a0305041a01062a0c030f0309260d08 64
    0x28440d4011401a1540d00858024000c20320542d5580359a0b4207000910a0040131a201101e03602d001900000c0151816804010400e840034407241005040c0402401c1d00031280792941c1490340098200c8c2100e070a03640c10402c3d43d50b07441e000b201c082c040c00d03481480d031020245541d000749034080c0c3d004a0740d503540f042c4000b410015015960f5000074121807160026149600007403107480000700c80100224015039054070f9408a175506d0081440c0009074202c181001a00605280c4810300114802000e00030035443c8952418106000001da014a80520a401d030503074064031600f005034230104448468006032050102d050900000c14011400d0311182e00d610301d0007149641d528030f40780300513501421002008401c0d1000104044d50064050b007447d04110454a801c2c014000074103014080803c809840b554000000744081440301580a8603203001e0308055611a0761440d510001c029a15000700b5400041d03041c2d40d05540701440140344008442c50040101e050100d004c0a00340c1000000c13 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 541831618 1250 541830368 541830371
    0xf04020d1707020a09060806100807090f11070c0608130c120305070506010308030a0e0102040f0311031f140105221a06040b070317010f060c06090807140609120706 72
    0x1c05600311480c1c2141c2c0100d07805840f029415a40d072072168054410307801165005c1c0501000140e500300b4403c50300040347c0000d4000c003041840d00d40701000900c0b6100f1481d0383d458451003c9010b16641078020096288100d41e41c503c603626241008003002000b81050441004d019400c0d00407402d84007014060f00c0340604449a40401440c00b50b82a20030f80c1c0c0014500d00500b000002400000b9020b54810010b080c42800078940c1c44001600300d104034042d1128040c0c94200038400309070540160701080401030201c60004404481a1582144004110004940f140058502d00da4401c010500605080e0f601c0321035140402e0740344c1003804a4548401001d642c802c0c8041082d00c019080c1808000040c06869580362a40c440c141d05034003000c03059010441303490604004070078809401c0c0c101c07604049840c0310541003840407a0f011420880c01d0752201d4882220101050406000305144e6224401440418044180141c10481c005103150026045840301141100d8150101c46496174004030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 541832868 1250 541831618 541831643
    0x60501030b0f01060c050703500d0c110613080303041509050c130f06030308040c1406030c0c03040509011206050105010f0504050f030a051c030e030301060906030b030f1b01080f04020d 81
    0x55460032414405005501c20727610b00001070041c0c100c1242607404074648007540126142605d0034507500c07104254098000b904011120f00410060111200245401800d562401c9404030602d0640b09094000050320780000091004101c40f1101c2c0c6442c410391034106200880b2551a05500c1b600d0b842903250140510781740100000c80306902c800d0b407245072a68200400e03a06d90400820744101141e085800754045e04005c03841c03018000105803544d00040815245079100c4400c0205604054030003a41448284400304141d0b50790071645020342010000016580000c5c20007406803003040e8070943c1031180f0840f55400d1380d58000f007100e00f6603030300b91641d40300c04001d01c0201e4074048000308060300398000c0505104102002060441c520303580c0e90740901828002c00e044540301c1c0b04c20b10031000031900d140000c1102e50701903080007000040040036962409040c0d8041c0b07043c1100095070b070501d10801d0513000c01e41d40e040b013036458000a080000454514140c1d0204100d01d6440402600e904150300713 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 541834118 1250 541832868 541832903
    0x10e070207030c060f090b0f030412021c0c023307051903030b030715020c0108061c080316020106051e0a0308070b01050f1008070813060501030b0f01060c050703 71
    0x8010030085a0100603c04a65540c400050841011008210001d00c080030002601900c007800e44603403c1c54500224650f44566841c0b1152506c1000041c0560003079614010720140c080044c102c00283e942c45204a10465104000000e070b50501d01c0000d9008403507502203c50b00d030741c9035001208412414941d030751149040c00303440c0c101c04c80040800d0151240c000c01c10540c3c940c1200d8640c00c016012130314000d80f151072180c01013080094a03001a4081903800b125580b18049490300504042c0c08002c14050007498410270b212140c0b002c0c1c940b80800414401480600c1000c4420910350b48000c000250610f000100404610320501c000c0100000c900f40c0706a0b10300c94440011030f402140036580f215245003000c030560092140600c138041910010b02c080c14440407810700c4244560300d0b030540c1c1c0c1c0d45100584038003001400203021a0b0700c1c7c40300600014528030810307000e180615403150443c43c0601c00072000040c16003001c0c0801181601d118005000029280282d0354000f100c480c070013a010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 541835368 1250 541834118 541834123
    0x114180604150f0e012705060c030411130b03060114280503160303080f0403050720130506090c0c120f090a031b051c03031a0306090609150103030503010e0702 70
    0x1072183c480703040d1810504001d1100c0544c0075034100d004a00c400a00e5003171001603800443c00e9902d0181460700a503001424884221004591007407103401c0107484516900c001c2004100c4005000c28001e694251810040c601000fa06004050325200c941c1040c803405c0c0458545081031103a02c8070150381c00071190368043c005003940c5c05450094111400c040d4451000d8825940714482540402c071810049804908580c880d14811609900c541e0315004440d81d50500300380c800302060361032100f210862211680e60040c1c01c1d00315844028017003050304008007080707100d0300081c000d42c5450300c0800c8098801e9001240c01c043e50188070052030f454100c03c00851041f44104c101e902e90001311000040104180e410400c6029444281c0174080507072590103104d144d440c1a801c050300403204c15042e5001900ca90050201d00701465800b40c1c40540c1c10020030300e0710400740c5d0b103015103400001c104214504100034003121030002d0300e06c1c180503514648000e01184010b0240c04601d5079140d000030f981c0e0303008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 541836618 1250 541835368 541835381
    0xf05010e01270204240f0302030714090a05061812010204030b240310020307030f110f07080d090503030412021c0c0f0f120f020a050c06070c0305030c011418060415 72
    0x105c45546090f2007003150343d040c00150005801d404511020119034241d031080c401d0b00e210f06402c0d00e0b2000340240c0081d05074016006004031a0f4020b01c81c5c240407800fa00c1d0070b000341c5508100d100c00121914015010062600764800c4505410fa105110800104811f05095a00900944003421441009516481214241014140d01407144150200155005600440c41803a507581c041211a00d40c4502400340d804400d01c0704a42b0308103101c4a600c0c0da10030002451414452803021b440c011003076000b80103560a000090710b540d08003004000a04ca41c01d451001945201c6c4060f007a020164580400340c15400340c40f4408101d292006141004148400c80c15610b8120400c01e040c80c882d80752120503035042c21a010006401510040400f5000064034584503500602514103031102c042840140d4001007010740744901d8135100080030440c10303c024680345e204680041000c00e1001d00d1010800c0d0b000d02001070000320091080c08030754010901d141c03c164030440e9111802590702101000d400e6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 541837868 1250 541836618 541836629
    0x31c0209060c1b0f090610030c030b030f01060f05061204060b01260103030e0a05012007120c06020706110d1413060c11011103030a0504030516060f05010e01270204 72
    0x41e0b000800c403e001103c1e02c0310890780c1c100d61003980b07260090144004500c00740c9034160001020b0206009050003500705400701c1056280004040c08004002441c000c908101811245d66550051000d40300000e0210050300040e103c071072a1900800f000078000d00c0061019102c03942c0c4030910f000701ea12460b44144510840401d40c192a4070b9014602c0c00d1040a00c8100d020a10111203114581040d1112004880c1d050b1101400d0400d050202c1a40b644110702c2104d075030050b00d60114441c0c00307072044018a00e0242c000054050300f1b00c2c0000e0b10300507440d0000401d015240a032603501c00ca0006100000031102d203003c0b034ac404107092200e401805540038200b944607001c0804a05258404184988903014071545184001c041e401504d01e8984d00c041002103410410005289242503000183c2081c40f03464141d207403244581400600185080c130481d007817900c90ad9424903843c44c80c00303214094201d0a10020555160030148000f64142030302c070054031400e2109840484040d98141c0d401001d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 541839118 1250 541837868 541837873
    0x60a1d130e060a0e03160501060b0a020601060e011409040b0d0204020c0c030c060a0906080c2106030105090d051e07050303011d0a0c0c031202132303031c0209060c 72
    0x903100090800548149000d10621000440e008414001c00c1325003c00000510314000100d01d680051045030b81c1c044d1180d6403604030000c4d8461882e002002c00c0f03115603006c4e0a442d41410001020030751804c0c40c55040040b1401950200701c0701c0c80403207007481e904883c0040c0ca826140013041000c16951800381d4807500c00304109203215008544200a08005c4040e01c4000c14544100000c034014003d5000c005602c3c0201480814050700d41d85400518003020181060740e082d9141e070029100741801d1003082909828412503090900400c0e800100120103006942c205040003015802003900c602401d81c803803038401e01d41c110540704a420454100c42a682d07250b03107481c0500c407007041d0501002d000e0324501001946600043c491800e200e4807a030703101104d0f000c1d0b98404494210840340d41c1600180d080040c0c1d0800340e011503181c40206240122404400d445014450341e00f100b5074034250180d0020018010298417921482015030809140140c4070600c02010400c94020b000d0180d003240b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 541840368 1250 541839118 541839139
    0x6060a1e03020415030908030105040506060c012a051905030604180501230c07080d1407020a021207060e040e0a0f050a0b0a02070f020409030203130308030402120c060a1d 75
    0x19625400074030070b49071131012903c11922011012011207001c1c807030281801100f40014801c515264102641040005190310b0814000c4090f45007181c0d00c2e00c1c1c59540150980c0b80a20869052401200b82070040c0d040090a007001c8548882800c4040e00e2414104000040041c2240d5101d80c03041e0b0025001d0b0208500304101403034558000c0c105070220300380c50742c40c01c8491491760f800030107954490b01720200564203020056585103083d811a15688100540301c2e16011303954154802c010384aa42c19500901703051040e4010312040c1666903000e022070303400050b070034000e894010b0200c270300e0300c003041d140040c8000442005506100140e00c00901a070004000c2006100b000116029030758040d051001080e103450020204900c2204030050181d0f0701c850041000d41b40c290700651005000340190380c036040300d03890503842070320b01c581044a0130f4a01000344001e504100161540c12502e9000a004208403d000208940241108079007000341c100f0008107080c041c040122040340c1d0141030074504 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 541841618 1250 541840368 541840427
    0x61b0618060921021902010c1a0402040506040c051b10020c0f06010602010204030f06150e011814090a08220605180a030b150402040803040b1c05040b06060a 69
    0x1402c1482800d490110030f5658102d41c0f210983d100d110b0300c070000d4008103000080d03100480b4181c038048000342d0502c01c2a000c460082417072000e6440c1503c0e1242004000380c680f520401c000c50340050b140c98000d034600041003c02907000400c03a00c603501000700c003500c6a02ea440d4807518110980d4081c1100e1800800c40c124005d0b03001646c491000402c20a03910917a8076000c0403800c0340101c0c8000380c49206410140740c08582c0650050b20005a00c25800689035218a211305442c14281d1007000b82100d501c044141940c810f01c01d40e00e00040d41c1c0740a59141c241046041d41c0ca9522980c0580b0340c00c1c0000e100c4800b030b071034800900703c051401e80f85880c0c1c283e42c50902411542215820300d00c0603518001e400c1c400d1810300403540130f4071760200180c0c05a45a81e10805c100c0d10850b062190840c0c0d00304004140c0c0401000500014022880b80c1641c0e074804565880d000e5400b011a07102250800f018040064981d101a0358002d400386c1d01b81d92030b0b06400394112003c640452170508000c1d40c440d282d038813 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 541842868 1250 541841618 541841621
    0x207020303280206040b04030f020c0411040609050103060f031e0f05070f060c230f1902041112070f0c023d02060406200a09050f0901061b061806 64
    0x5692400c01007107000c00542d5006a848043c1142c0082220174a0700005000900820841903500710501c1150060784614000c242101c107a00c0d0491a41100440c040141c1c582c40300080c80942801e180600c403162810b01c180035500b41e1400010861440310002c0303258003001210240000b034001402c040780b61018149251900318601850a40c132a05500101c2c420340601c100003030072680013111070201d500020800c1c50342041d58040e070110780650311000b13000030000c200c0941c28070450741d0103107410015441080f080b41d83c4260140700f105000e00c10b01a15040d2625116804412420701c55a8040990002c40e40350004203002503000d1100060100e41d080c5000000c0c90403e8102d1906d040b030a21228800541100006004016440140002c0000e01d035034020705003a0a002207070301d02011542500900a802041e41e860004440000400032843c000c0e51003901c0603003d9420015035414098001c1945e50184015a400003c0713900c040e04110196201c1c4c0d2480c0d0030640221140314007440e2100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 541844118 1250 541842868 541842907
    0x30a090804170c0103110a0f121e0b010c150f06030206040303020102030f0c190c020d051e1519180b160908010b010801061133070305010308090609040207020303 71
    0x8443c450703002d038141d1550083c45011136840644a1980c1000245402202c003006105107010070883d4041c04140198807078010358006411520011840c40010a650401c50340b007840002c7c100004aa1a00301003010149500c0c00d00101c3c03000821201c3c0481290b101030f1100d030744001d4011100060000c02e044c1c2c19070165000c0d6948481c1c0038256141c0961001050049003110300c054000000c0041505000c2c80e032003041d82c0d1000d4038107040b61003a03440386420002d400e18601c988184007030b0141c17038000042c4204950620019903140150130b146000b1110350100ca0088840c003983d036041e1040300751400c1c4200d02c2c2c40780d001003803480924049002001c040250340c0c2040100c0e54048000c601d0441c1802828403945060b95140c0d0503a1900d1022524906014007103056400345001d0a0310208508282c400c0380e01c2181e01c074003541e0311030306c3c60410a41da005041c1400c0518281c014000a03401104465040d0400c0b03403055158944134000500a102e0345600a41c5488002101d90405401c2d40804 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 541845368 1250 541844118 541844159
    0xa03050304200303091216090c0207061d0f03011b030218030105060904060504080d060308040501121a040c300c020a050d0c060b19170c0114030a090804 67
    0x40c80b0054082002000b0500e04540a950503042404540d00ea0b061040007500c0a110030b03400c4443c5803100d06404140c550542c0c112078486d5446000703c885154040100000401d50b515000303000030b071a000010740743c00d002056188205c050071103204142e6001d4010329162150140154110540046c1c0030f40258451061300088440d04d50880d4010310341032290368400c2d10301409014556585503140002050b006100301c800003400c0c442d42c0507170441c510413500690b11800044c1c0e515401c2c50005000030100c0e500c240b0003107041c604503013034441c1d11080e014011007082e240400c4030307009503409890711ba4040c5003021b482407440c41d11040c812a50121100c541103d00320801241c085d5040c102d03159140d010740a481c65004010480c0180e1140c911910040d00a40000031080d40f4180000d00106400c00302c036510400c07405007405a4103001999520741c42040000303001c40c01480740080c049480c81540380c4c00384940031000070781020030741d0880c4103d241d2000400b03590f80d440354900e045904032000d00d03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 541846618 1250 541845368 541845383
    0xf12020607120606050306091e0a0b15030103030e0112020c01020a0206180304080604150207170d06050a0f030b0c0c070609180b060708030717130303050c07031e050403050a03050304 80
    0x4451003204584144025550342d45c0c0c0d100d04d143c1c0d80405101070283c01030240c80ea40c03203c204001003041e5020042e1030045901d01d8000c80c0d403203407039400c1146008030070604124983c001c100400009030800c031442c108003401c0c00c0140201e000014000024064400651415400020401000381d408644030f44996101c501414800c0c162404240d500e0003280140080780c0e210703c000c1800b09140c1c1380360700c0d088010700e0005480c00c1030030355800310a00640d002e84110148c0c04910204441100d016082c05024142c80c0800290701d4044010861001c0b0302c4054004061030f00403490400c1040308a81c0a4840711088440180c0d45500c020620f9003240b05a101280b4000c4034443c20074601c0c020403c01250040105040c040c19850b859816400030b803908060000780290010244025070720180f20741c120420080c10005942006004d0700d01c010800d5020403410400c140000350003403a81100a00c59444a060000500a0596192044d40c201800364410031030310004143d80030004610481c86001b2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 541847868 1250 541846618 541846637
    0x5071701080706230c030a030228091406090306010b07050706030c020705011103090405040809040f11070f14100c0306064e090507050d0b130f12020607 67
    0x11840d85640041c001d8100007401c0c2162030001100850120030280113254005103403550034450145160b100110250110f50042a5004042c21980e410001d01d0507510000c102e480c201ca8004050403180d0264028260854804082e00c1d141c040a80301440000340c1181c00c0c13561118400000c039044050200d5040c441e1007004170781c0324801d0141c0110302103241c0007400740e541440f0040d03d500f51000100c0e041071000340070849056071540582801140180c81c07079a13a400b100c509100546040081141e4001d0030140201d4120098400300c07401d0503080f100c0b054002109180030031001c1d50050340c4c1d6002c0d216503c20041d006006500200c090b605584081001c42e642d400706403069003421151b004c941700408900c114000c4804078114481c0560b11540078030035821070b000a1080d180c0d4207058540c9948001e1403003007050400404000d40703c200d4603803282200d503036180100180c0c01071000840f00301c0c07401400c0412803490000d40005078004504100b00e501003000035903500c811a81700c400681100c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 541849118 1250 541847868 541847879
    0x3150506031902061b060a06030210110322080f01051e060f1203131403100209060d02090f10080708101203050c0307061104081006050604090506030c0405071701 71
    0x8041c102440b026094a009078a15020052a904024183c1015141080e460100814180403c0344207004200e800175480c0c0c1940140000d401c9501100014080f01b03e004030320300d420000949161080c40700481c60f6080c1101301d150205135441d4400c2d0b4142c0f00c0d403021403523442419003065110340c441020051003450315288a0810320019104603420404000e4402694282100c0d102d03a04140310301128600b805030403c2965840b425484075a00c0700c0c054482c0311542c030303003800000784a078080b06055003403010350400035026114444581c6109523000400c902c50f61a2540c1810f0000c10080c90354030700c400c031603d0150030003808944d00b0002a240c0400a21100380323140709601079130380d0b03503c07001000c411607030702aa100e41c809990b50103540b105011460000c3c88038025041071007400700368943c88600e000b00c402d140014031034104041ca41020818081d946502080e241100c103040c40100c0d00792103260101c0d00317103101031400e560801c6c1410308010380c864110501c3e0f1549909041c601140303a0b40e81 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 541850368 1250 541849118 541849123
    0x9061f02031e0f09010513050a081f02090f010f030902031009060b011403130309050310060f060206310209041b0504020304080301120206040f0807150e010210050a090203070315050603 81
    0x40c003403d00302d004244035440035544114003030003003600304403e80c1d0011912600002d11810300366011103260340c84003120240c61004d03050b0b040e204a05049040d82403031000c60028102c0100500341d61704201200680601e541d1180d0481d240d01600a000d4444982c10074030884080d044854054920324101900550154032800410181ea042c1142c02400c5485000e803a84100d048a50150204107481e540440c40380d9050110301424004400c001034518030703005402d0350080540d40040150341011040211070448000158071014652034007040000c0700400d1000c02c807001c9003002e50080341040402040084d8180304002c0348845060800e1040e54420400c8264441190001e100300030900041081440740341d418113805100030001c07400c01382c988182c446c0c43e41843e40f002d2055802048204801c2c0003034480c85041080e40d1501b14a158038400020f955410710702c814589055685d40001c4a400150f445880016402400d44468542d00d041100d00340c11003207031244205142030b02281091400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 541851618 1250 541850368 541850377
    0x40c210240091410050907030c060311190e09090718020304170d0b1504240203090307080309090708130807020d0206040602160602010606090509061f02031e 69
    0xc4003116000c499400555203041852400a007506075110b07140240000c0c0302c02007621068102074020001100d44070850310079108050b001e0551074021140c1480464655051002034900c0c1c7c0c100419440701e80d1517250803500c070b5038040700faa030194001c81a0311660302c1007869203c808210303150303102510b81d070080540b80d203054850714142c11640c900840e07001402e40c004c0c2d0340c07060144264407000c07081000c000f40140d03c001280e6880036a1015050014505048050340c00081c1844d580d05040c14265401e00c4008035204400f0381c0d003454586441000d2003041100c007000800760a80788035a40d26041941e581e000306140c28030071207188000841c518800c2d00d03898800c0000101c9030f1100400340e101d01010340d12520040e038000c80a00d079040b015031100f100410080545900030034100305601607841c03240d00c084d0048011179052120401040e6030188038042511400c5508046036194600040c4000075000c0903858490f0100c00744003080394000c0041e14034500810a00c10420b540c1c003403840202d208 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 541852868 1250 541851618 541851679
    0x4350606011209080903030304150e0c060904200f0c0705030105040c06080415090b0a05070c030905150d090501050601023f161101030c08040f0803040c2102 69
    0x2500c541d8107003280c8541c20000f002d50090040307500d480d802c1004a425540b085409640d0042c03280c1081c025100d451040c4107221a40308041c1c9a1000c01500040140c810551a54805e0780c0b954543ca40000c0145450031009400d24042030f60340d4561009600329420440700e841090089080001d010705060140780d11459000c0d51103070b070841c1010001e80d01024007400603180040e40d0190210417618a12442075000e0080d00c0446030345c03a21905510940e01d00901013420003160030400c5000079003104500040d0b40040382e1210300301d01c682403400402c4c0200000204098204075601082c004190b200c3e0b40101020ba0a031141c1c036500301c0101c2101403458074220f80741c081b240f01110084a00000ca024142c46292080e40340c00d9661100c0c2c842054410303000d036100703020802c1e1500c2940e010303c00d5070510302003400c081c00e45140c00d4461103c0d050818401515980000000030108074210100401414022511080d0020110011100d001281608901030016840440408441008140503001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 541854118 1250 541852868 541852877
    0xc061c0f2a02070305100c120c120c0203340f0f020307060801080604082a150601030605090604090303021201060f0206182505030f030306040501050405010e010b0304080435060601 79
    0x44242c1006c01005c02c2c02814080083c210035407400d9800c113005008101030281e4030008103910446070700c0220b40d800d0304540c066600420500d941c03c851450191003500c2ca01400007903c000041e5000001e400400c00106138040c406034203002c1110941404001d00c3c0203400311182035480310425a6001703000c1c003d9101c01c2d0302182c0000c0010f0040c0000703144290005120322150301014020201d40417034007049941c00c0c0c2280b6410b840710f1004494481d800042442c0c140100c40c50a4040b42d210080a41418045c6459401c82018103000b501207a032000c00c050b0745450300d036966900c0101070200340d2020b1401401804c02144440070f00140440c0201c03d00009031140a814410400158505641c100900d011480c1c0c0094540d4040c044144c401c0703003a002030369032460800200001c543d0b058000c07502c00c924110062058805005040381036886034413826a4986a03420a00d00502456002c090a00d9400202030002c04011031160b031104194012250641d100d00403854031140206c84490010307 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 541855368 1250 541854118 541854133
    0x5030d0203250f050319020606010f05030903070209040c060207081b040509120309010608070f03030c0312060504110424021b0406150509030f0c061c0f2a02070305 72
    0x140890048100300071500b01e4620070854540d984503000c1c00412020f40b0590004126041c41480401a200c010135a9101a03d0240307058400030340300f0b011090b4040d0400c840440003c64801003042120310440d00200700c09100d181c203241c280410940c03806035000500504a0001d05d1401c001840042c540c00ca224981da444081801d203c010301c801070038184c00707119121294460b0700c180d600642c0108800800821400e0908004902d4407480754000c140000109108001080d44411103c850320740c5407502c1107000620001e03d20241005800480d8000d1408500c1c0b0380340c4000900510840d40820701450304480756060240c0d0fa50380418061015030803c150724800070300c500c1d0031154000401040004ca068840711002469207581c40202c5c0031804c000b620324500d1a04222040824a10b04010114803035000d0200b0010301031034a002e095400c0342d11141003240000c5d00706400302001030f0000c1103905007550359070710a00d0303280060107456211000c414002510200d81c54080d43d03000030040510 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 541856618 1250 541855368 541855387
    0x40c030c0f14130b191514030106030b0d1e0209070c0b06060d0e100c0801080a030518010509181f0509160302190804020102060114130e100903120605030d0203 70
    0x280c2d0001c0e44000c0443d6615003d641140d62204484e1000c0d81c11004034110203402c1408100c0c81d0fa0110101d80c0503c0303413140c3d03084c8003d1a6881101d056485a180108140d054000442e1200c0e1034030703e0081160f002c442410f21403400c80c51003c0d103084e0003201d003813400340c82d000c02c203460085080c040540382840303480015410b4104440100650b00700c1200c0000d004a40c0c503a5607082142300310b0858806a2182040d0000039805100b4501600718039020f0504402c150f0f4010704107209182000c001e251080329103c1960303014030181c0d244014050210b140c000303c031181841c1c01e41d00c22614211000c44800f072520300a8000100032050301e01c050150030035a16a0a0100c503105181084174042507000c210164a10450000d00c005019454903074941e281410310002e420302c001600075030801c00e50000c24a03c03641e500003520fa8261111140024010490f203412801c00d0114400100d005003454541002c144d4001d0a8803d418940c54080042d15140c4c41015240c170790555006006034818810542c0d03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 541857868 1250 541856618 541856629
    0x30a17010b09190906090b21060a0c09030b280e0c010302070804030507030b01301515080309010e06160201050c01060503070b0c010509070303022112040c030c0f14 72
    0x1482d400b0740c243c072155039145048401e5900030380120070025112286103065092040c84070840510f03901914402c171070580411650b411006000140c425103e5400d4a00705004803003800140d908a84036840c0e41c94a5502d4444582820340800d181c010080c04030950116644612550a0a02d1000d420101f90040c01140a134001c00c2d01619080410400000041e4041220000561168060f800d456150200c1030359442840b51801e0ba22040d0124612402c03800d402c22801c078640d201c0032610400503c01c6051004001000c40001c00b0744640740c0101e03c01c1000006094202e0099a0303c45040321640c0a100050003502c4440006059491426005602480240022141e0342000184241e600c0c0002844c10b0155806040030386030005040b00700032000e001e8503030304c84014401001841d1031039400941d9002280640442290304044001165003075400300c61110003017000c520340c181014200100061500d11007103866840f0140002102c141c680030741c804507410022441c14405615043c0003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 541859118 1250 541857868 541857889
    0x160c21111501092007110315010305030f0a0203090301050109240e0711030d0906020406111518031b0705091f0510140307030902150f0f1803030c030a17010b09 70
    0x8081104001400007507140e21300c054407185020b0400c0c6035054070074134103040c24158160b0000380c0900481005002007900001240d50043c050b03e03400d5612130f40611304a0445c0a6110826455401c00d400040d48060641180802d454900d41e24011400799220300341100501d84140b90200f004000040d580a02403020001c0401c80403044c0d03407902c0c20302800300c01103d0500c00304641e01503010030305000d00c607071100c4500d040d03400307a100501c102140c1c0c440c20018084014082c0c44410f01c06007401d00594001e00070341380d881c00d103c103000740c0780d1030001c0c0b450740c0f95840e5002e514024140a40000c90902c115640701101c030282c0d0843c0107840c0c3c2000c06100c40054014448400e0100001507007030602c8007400154425103807030360300140d04e007001e104002c5600b03401122094403441c148480f20044a08208036600da45000090a035504244a0301d1102c070400040c01c90f60501000c941d6400c4244040014682c2030380d250794200e08801e00401035040103400b80940171400b501400302c2c000500302000002d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 541860368 1250 541859118 541859141
    0xd050f01061b1707150608010c0309020603040f0303060f0306060e061f1214150f0613050906040e03040b18010305040f140114010b04140a0608160c2111150109 70
    0x254039000c219243c580654408817040340e0400d81c0e0301002c10951170284510040101c9529082c0803007030480c3c0010301c0d0742c003001c0c00140500f80f001a10100301802a48050b000309400822a01415500d00b03150004100300c1c03041219a18154002501c1460425640c1c507500044507404100c10a4103003084800c0803102658800503075483d103144040070707805070040e0321486410582812502803a0706101031004920f104a000f11024070107180d040501d01079600c2620003d035100502542c85400103406400c0304064070003940400240410a480ca01c00280071421011260350f01e0308002000440850b401103d010b00b01c04a4183c90b040040d22948021203141002000270989015125008060a0081c1d0010000c0103001a040160a00d60010302d00328240c00c0b01e10700c081610f0104003401400000b045480000c2040c600059000d0003401004121904402051030f0050705610303007201146070301000da000c5004201c0184049400041c421450071140841810390303440c0200c90000784c41e0b07070b1915 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 541861618 1250 541860368 541860413
    0x106090212040807060905060a0c180f1401090b0304030c1a04050a021309060608030301051302091f020709150e0105100f0e2b0318080304030f170d050f01061b 70
    0x803200450070408c949030040300c005034001650490f42c103014243d540e042c03041364884203100c00c0c01c01105100036000d03030482e4040203000444c00100380040310350f8981d0385c02c42c281c010004000c0c04149588440038030304140c400c4094107201600d03000784a00800c0119001050380e4441c1c0d0040c00103085c08031031150f4080c4448030100b40300803580d44140a88080b50848404c42d0f0003c00100168500481d03001d84010030f00108610304406140801d00e0310901c20401500c09410b107010040c1140308025220060251040c1044800c0024607202c1c0b00303e10502c0340600704001e072400400e040c0f60040c4c90503600078694448203c04500c585058864006027000b1507071007103840f8001d40c6107144c540a01700c071305001c008072041c4c1c0d02010714016040f407940d80030304280740b203441c1010b1200302c01c00411501600d820616103d0f035000e4500d41801c140c4040d031981d0003100030111b04122001c0703140e00124028034100d8618859030b0b172952001c84012a00052a4408229803d03500740415204924002c1c5600030024 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 541862868 1250 541861618 541861631
    0x721020f0c010507020a0b060420091908010f060905090c01082511010e060405030f0f090a030f020f010e011d062808090a02011d0d060e0f010609021204080706 70
    0x11040e00b180c408407584d8016810103400c00040181d4001103640c041d0084030104840801031401c0040090311003190410100000f0700820159609146021042c49008501c2c26044d100c0f04118080c001c208140342c0424100040030640541c240640c0b072143e0242c100404000e0a01001100e42c508060134010455603100c906440381c01141c61000100100e940b164003d41c115100c81300c1c00c44404840b20860ba802050901c000244003208584c0071081c2d40d00d4064541907004d82905140c03003a03009a541c01707026904004204400c1e00400104c55000311601c03c16560140b00540d5240c1c1d640101d240052817070001080d031800201041d4a14060140017241020304081208110300350b110381030b0f030602942591400c0c0455002002d5613002c135512001c0c010581c1c8560000e0311440700b43c0980c882c5231201d0417050344503440d1401140400c503040a0300b4020320b150400c0c41500c0da0041c00028607107500300880400c230460b45008491b455200c03076140c150f5555407a10740c420f2036000001c08031012a280c1c02d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 541864118 1250 541862868 541862887
    0x60d062f030c0f160b0907030308060d02031c0504240f1e030c0504030209010f05030f0d1403090c0d1401060e06031009030c06020304120801060201180611130b030f0721020f 76
    0x200140c410102d41e00141f18480c210f0501422400008002c11b11a0032122207540c016140070480785024003020040d8800c40b9440c10082d6158003c6420004000458003c072403442660310ac07101d104410740e502e031100300850800040700c0c060381a040c1180802181000454440e10961000020b54821302d405420b060b1a5400030300310000070b922031150714805800138810f074507040c0714010343c4805030300c020100d803c1011b01c00b4082c20700c1c1400401100001000042c9c0c03880302070040d901d203007600030810801c0a8517490404410424500d0170070301c40d031806c000401c1c0081001003050142c01e006009102025200c19420050129510210208092105580700080d214000365000e01d10540c1034400700120260700402000050388103204582c10b01c0417151076403d054581c2440c1c181c0003400803402c140c00c81010301c1c09100c1c004408091440039040041d442d029800038500542881c8180035198a4000341100c403040d00240c00d5150400c2c114080d0303010009030340240329903503124482c14100303a200c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 541865368 1250 541864118 541864133
    0x30311010e070807051f090e0a060503030a20010e1e01110a1d0612040609020f06130317070b1f0b0724021e03060d062f030c0f16 57
    0x30f42c401440d0b54041c000500251a01e0710079048802c5280385070000301c07404803030000c244203298414407a070302e040c03480802c0180d43e45e41c000b0009440050704907562007550300030082c50b01c3e000b0942d200303904e00f0700c01c5522003141c01805214800940c0c4c0002300006000b0851002003041d01d0280c9262941d070707a0300804040701c507900c050004404192250f40c554240c2855a03146940c06000051241ea0100f04c070001100c8200b00541d00190016030001e0715400c1c0e480410304400c81c1041c0f160b40700c0004100182c11444c1c0c0200302064130310a440f1080c0c0406034039448021401400c0300104540540000119a094904410400040d13036a4214025940c2c1c2d12001a05500514050724504141e05801e2142403040d00702d0f204a603011942146401c080d041081a04d40001010680c1c2100000c0400c40075034074412420560394100e401081a4401040d164407043c01da40d203800c021144a41c681d04070381e1542d505891040d0341000c02d0364586403184c1f0005040f036105c3c6040f0fa45001d05080a4004038508 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 541866618 1250 541865368 541865383
    0xc270e031b1c081623090102010b0307090603021804030f05280f030c0801080d03090f151b0f050711060d060e0108010608010e03092b03051213020307030311010e 71
    0x20b0340c54070f04403400c0c410228501d00b441010910300b401440288000610894207100c41c0082c0c141540503101c11440004030301621002c03e00a5240c0310750500401c1070340d0340368000002c40b8400c0ba12041020f00046182e1160301d01110041c002c542d610189455160292000b04007044410001179801001e0041801c16403140074814000501880c01d6101c40d25014424130183c81580e0405400944c5040e10f455501d6002d000e9420801d92541d1514080104500740490000d600044a51178801d107120401d0041c8600030070000b01040c00300902c401280182e2035004200603940c0c55614081180e124805043e00001009070004010440309031014514815100030300550580da403510b501d00050343c1e003911402d0304050526490850058040c4400000316280808190b4804a0307188803002204824010704501c5c091810110180c401051303070083c020803804050618a0341103898a02d14005c03250341c076020080d007642c402c101c02c0c4082400b410061028441c11800072624010b00b6100302d003040324 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 541867868 1250 541866618 541866673
    0x7020310142d010911040b030a0c020d05030f0604180210030f23041202030903031c0c030b0d150b0307172b14070c270e031b 55
    0xe42200340221101d401071002d080750709000b840101c150014000220207a01032250f0030700d0640e522001c00c61003c10310180e400514483d00300d1340e12840e06040000c00340c00b070905070030010f00075032480c400380d240607405407401b502003ca0386080603503420f41480020074003061142162180350882a00503a00d0a81801c19204540d502280101c110740b020810754040c00c400300140d00066055070504000b840039640e001d5040040d890102c0600b030b4090b0f0462040d0007600384c16000003c0c4200320b040200d40414461407883c04104000740c101c0000f10700700e815030ba100340e07480705940119601140d81140e18030480d5010810004902900500080c0703840391541c0039064440503204808a400d400303212074007000074810044200c0b00d62028a4104400d1030140030030070300c1642520140c2c4000340c0c10a50740ca007988000300c0b4a809450b843c18201020220031015071940100c40c80c002c0d641d5039805000e070010a040d009504002c410000c0480c00d14058411480030b2080000d082c100c50b000e189009201c85 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 541869118 1250 541867868 541867901
    0xf06020919060c020103020d23011d0c07080901090f08011d0303060a030f051603060506030105070e0a0b0a410c0606100201020c0f1c0e1507020310 65
    0x4040c180a044901c01c0003011008200000801207141c02072406150700d42e09290050b602c00b40f098801c4010a84805591060406001480055400d4242d40c81c103990380d0b0b608148180c0d08881c00010342d101c040321000914031040c000b8000240078003003e407401c0441418500318060300e5600b88810b10b02c41d0f034000c400580d12100c41d624440d0070491760b003501a1003031001e94594601030001c030300442c1c100e100050003070400c42c00b2a030a1010a0142d000c000001c103d8003942d00341e032404c01002910003654118420352070400825401c900404c1e592483d10342c0074240c2d03100c507840c0003000320081d00411943d10921000e4524503e034580316520040700405c41e225071410008001180481e414581a01ca0740c00850400c111107101400242555014004445c0c0424060506204901902510801800038810710b1507815406001048006000c1400d010f00000900702010454032442540762981d0040359603009402001c2c040002002594000340448105a000c0e200e1141202c0d01c209a03441d81c43d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 541870368 1250 541869118 541869127
    0x90804060807450f1e0e040b010303080606090a0603020d0207060204090c23031302040e0114070e04064703150a36090f0510110708090d0f0602 63
    0x4904140c085a10010003c20301090a402c0903101100b40307245010746000100000c0800c0000c0c4890480354014001c4200c01211508045c81d101c04004420300084000c00c07588400a40c44d414842c0503201d500f0b50041441e4201868140705900a6010516528205408003e908041110360009000608440b00d0010301803003400b0006004000d140c0c01800b002041e0000f0b061f94a03100b8042d20380010b0041d049140c4190548000f800a0000d903014110a50070702401356001e08040d40010b206680076221032000c2d80d0500c0401c42150014054200d20a4140560175000b000382050803417011040c1100c81c0d81c4148050714408903406c000d00c0b80c0a20b0000000704078130060710300e1041c40c890703d0540b50100c00a00300030350364500ea2121800b0002d5810400068080d00c1c0881c03000c0c0204155101c0c08001d4080c02d81002541320180c030748203550600c9403021242d1703400c5841c400c002200b80b44134041401c0003459590011158444600760f64844040d40c400c00104d229009111840fa104050041ea035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 541871618 1250 541870368 541870457
    0x30408070e09060613050a02040e0108030910030506030307060b0f3102040302010c0308070c02120318030c0307051005040b0f0a0e030d2015131401090804060807 71
    0x60100104440e0b242d0308088280302040d21481c0c1030b40381d81d9041420101c0c2641c0c420450308028044d55110030010b4920800019000c0b10100092038a50800d8468807181e0309800000d030180c03041a0344040c0c0680c81080b185010501541c400d040b154401416000c440d420240090780d24000c406032484400f00740d001904091030542154480c0e40803811083d403d140c6075400190808080c0030024082c0140c0d04d00040d0700d6480346801042c6154010700d03030400043d4514119030349410050041500d040f40c905d40704400d03d03001503a0f0b98001380050080c107125061806021180082e00402c1042c000c05101c04101d6582180160a5440960540903103468040e80700910030408401c01c0b07402908000c0d0b8012404e6400038298102c0a89510301480c2420105070017860710b000001d00d41900c401000910004440340303041141400c0c0a0b4906101040d804481c4900f22164000300030002e15040204104150148965546c001e0721401e011940300b800003c40750b8581011000e9010300512442c84682 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 541872868 1250 541871618 541871639
    0xa0201081821190f0906030c021e0d12050f010302040903021e061506190513050603040b0f0c040e190609140a0c020d020c0d06090215030901060b030f06040e010e03040807 75
    0x301d6120b5103001305a25284c0400580b101003140110020161545403840520b40200202151640400c1564074106a0404070640703d680541d081c00004540d80d5035404085c4141c00b034a405044400c070764041780d910319800c003c010151b200c82141540200c10b01d2a134041c0c011052411803941d520b001d05440c2c5483c40c0301d0700d0245141c1c0107403072140f4002d100c1641104810b0704200543c072517505140e40d40d00790700324004a810000d6800307039034000000010881005840d145641c0201c40f220016030071503d03501201d007150700490103091041c0401e18002003168500c8408bc11508000507000a01d00380c0790f42030581039812500088e81909058000e201160000348a0307298140c2c400c2c401b5000c110160f6100940304c0c4404a0705034442c03807201c02c030f41e07080c8003850303103ca0010755009191000e032800554000040350400c4412000179407038454009400131aa0044910a4810207504101c070350b100e104010041036104a03c004540d80e5821032081000100b00800c0a804d03240c0007445420b1500c083c925 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 541874118 1250 541872868 541872907
    0x90201020d0c03081f08030417061005030a061a040c050712020601080c12012a030b06160311010906020a0203250503031311040f0b030f0a0201081821 66
    0xc00b00241001d04201107540408041d412950340306181649081810006540140a4114074514000014001140c03030041c5084018144104140c68642e9558410421000503d108031501034001e84591000290244d00c0040c03507030100f19204c5c04000310200402c0403640104484404143c0c000340c0ca0091010a69582c0303034240340c82c8010142c0f507040a143d40d46500c002c0c3c03180c1d07005044001c040025070741c00307401810b10060f102208a1483c02d46695030781c01115202414070100f03151240c000c92038103101c0111041288d28461140600c01166002c03501ca0b6568260b0701d045559414640d40001c0b994002400705c0c2300150f0041d034030303400070524080a40300f0500030202110500ca80c018000b40e0044281c84e8460040104252801914105150401c2295058035441071a0403c1555810420b0788600300021041d0100c400d0004110b0b0807907690508040042d001c21400c40008410a40c058547c510912581c4182c907030382c088000c0512901c0301c5180003800042e0020684000814404070440f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 541875368 1250 541874118 541874143
    0x705010c090302041a0a060f020a0203030a021f05070e01050c03090d0506060a14030c010c020a03050d080109061401200304180b04141510033b030901021b01090f030609020102 77
    0x1e172015008640041c49445051254006010b000c0344411041d50091028401268026095a5498202c050001d444107501642d20603a0b0286100b8040c0740ca106100b15403290702c0c2610703a00e0f1409900d40040d140e0307801103400b20150f48000c004080f078039202d004041800c5403183c0002d00c014148101004a07140e0b040e0041401484502c03481000b582d000941a01405801c0c01c0114410085001041048041c0c0d0405009446444242c0c4030041d48100268100c500d4a01c04203d55030b240d100b46032076148190000c0740001c9168030f40c59603640b40412650307030300501c00c0203e07490203541b03a0303030708180c0c6800190941c20302e5900c0d020b0002504184c09440046d5180701c80701d5459240084662040e6031060050307070b001e0001a41c2c1440700740d00940c8511005110584100c4400100b4000d50007640c0080030000d020a21420468282c032100009880d405481600900042c42d85000d04151000d440429103042000d0708030001035011600407a074000c0d40c014040810301010700e0002929018020707084 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 541876618 1250 541875368 541875401
    0xf010903050f07080405090103030c060b0103020c1c0504080f030408070e01030f03030906090c0e061e0310020c030d09080d050c090f103e0a050619020705010c09030204 74
    0x1000107584036088a81d41036600346290303140d440a0a001d009401aa005140c00600d1800040f0901d5001100b2140c004e11410741840300c1c0c00320100440680c050039410005030390114045000d2401c02c030440d08520300e91171800500300b50b038459880d071501e6040c0d80c2180d007079040006c007480841424490400940081e0741101c202c4e5245540740400002d46490290816070344118100410121750441500346403c030500c1c030101504c0d803401c5120108140c850521421050803203c03400d01d0014001e80c3d684600802800d5400d0030340c1c030b400010358010714401907940010040050048054840c410381c8902604c052910380030070103144400c860300980f91801d404c4d030500100d030480e40d13044241c3c8c00c0c2800503584140312608801e4140c500d40d0004401c00c00620300d1003014862500303c58905e000381c1041d184041c1d502d4085c1d008040e01d440346100b010b04150041c13070000d542c0307038180221462001103440c0700503d442616182d06007140c650080c5100050785012080041d8a00303800b032280d081307441999 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 541877868 1250 541876618 541876631
    0x3060303180f121a1029030a0f1b05070203063412050705180a0315200f030a06090c0c1421030108151009090c170607020f01 55
    0x8040d0071645080c0304100e51005841802c0040180324000542c0380c07403041450060a09081040241e8402d042c000c1070880c01b003546ca4420b41205090700c0704410040c480c1d00900d15280c6042c004080c100c3c071224040c01d151940700f101520f840c1c24800014408840d0b407150348414061041500f0700310090b018240e20f61250b41c1d03c1d14815400004500001d450510104e1051600078003074486151044101108900d044200a28141c015000305040120f1161352000050103c04000303041c5001c1c0009000600140c01c801d9031034459601100b0702a2002894100410381500002580d50040e01c4a81c820b80e408030038000701c200c1a00591010380420b40042c420b858140e00010300c00940c4000213800d41d41d602003400050300d4140680e0302c1c8801407040800c15020581d81d2003034258000e11400c50684100002c04003042d044000a13801803d54014241c070540ca1710342c66070007920b02d01e0015a210004940c000440d9071140c0040e0700100180405000a440e00101c017a00341000c142c20a05984d04206 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 541879118 1250 541877868 541877879
    0x30303040b010b3105030d050c03090402180603070c02010e090103030c0204200c0c090106050304031b17030a090c0f0b0a030e010e15091002070c0504020702120601060306030318 78
    0x1400e054030409204207807150042c2241001c410211413080c1d5440c90032501c1c004036081094010000c0d54400d8084070303d20b90010340100d4480c801d0b50024a8a90010f1090540516040c0c00500c40d1a5103c101c10b4903134042c440000303407290301c1600c0500214441103903480441d40c00c000011514181119100101c0d850b40c0c401030034401800b00c0092082d5904d81b0201801e00744400b50088203000d002c100340e1a5200024034942e10080446d44621400c498130001604520503403c9130b105030380c5030355200c011741d50800e40001c036602c44406c11500c401400d1400381d0000c40940c040c5101e00c21072140440c222a07181402c500c1541a5049102c0300000d01d0b00c1808003a02d000c044842c202c0d41e9140000c3e500103294045801002c03142d40fa40344074000d49102e002d040040704500d41c011103481d81660454104001c2140c203c1c455200000c24040401d84104014a81503020b40300903800a040ca80c1d1494086c1c03222401c00000b42c110b5000309589090501c1455805a0b440b000b541401c00ba540e4030a0820 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 541880368 1250 541879118 541879133
    0x611060c030402040b0a081b030631060f1107110109030b15041d01140a0b010e010f0507061d0706050304020d0b10030807080909090a03080f0a14131103030304 70
    0x144041c4c0156121903034148592a045000b42c01058018261010503414589400c0104091040b40c0d100340301c0e00b408122619004e10701c2e04000c00b20040b140c0f104840070700102c0d05078010710780700743d9110b59100400310b02d12030b2a000b181509400303100407607079840c21442c24003828205580d42d60704101c94550180001010030407219044600030171264041050030300003070054a511030300b08040080645c03407101248415000155411580c000b00c24841e5502d90a01007121614610700b40001c000404a4403a54014403e01161170414a0b155107080c655880b0f817015150a201281c2e048450603c1142d00031500b8012a030250405140c690b286041070340010300000012403015006004000114840006c9400134200442d44104015196000381c108405c8c6500b100c2c041c1d500807000d5000090304413101044281d0010740c151210700d00c42c0c4800344400e100c00001014400c03240d0341c0c3d824030740d040b131518141144111b034240041042c031035071842c00c030f1440d10040e1328080c06980140107000001d003d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 541881618 1250 541880368 541880371
    0x3150605090a030602091201090501020a020d081303180b03040c1401020102090f09090106031b050102010506010e03100b0415290415030509120403030c02150a05040b1e130611060c03 80
    0x4a1350246e00c45034808000b0b140751342411142c810707661030b051950701003080640207009441880e8094500403130740030b50309a42c0244211190f0004003601c01ca0040000d0184c0700d01ca000d03424940c5c1465001d51951060301d41c0c1c0d44155015100000001b40401c40c4081a0101040340c503c288000d60402c030b60003010a0440c100290b400d8402c11b8008009041e50400354008001182c00000c1c6c1d04c4180ca81d40d0404260000070f004a0f4015401c0000282440d4065a43e545041034054020449440a5500307074004ac100b120450750b00c20384905108a081121068103006003034011200850079400880c81111020075002c4606009402e00c0204000301c0402140900c5130300074200440c0c01d0b519050a1070400303c040ea161810608041740200c245944601840710082c8290380c094170300070202c940040140144400040054402c0001340b10704440c46006d000c040038006140513900e03c030a100c0d5003071070f046400c5005d54500c07012010410f196000b0909852110018044c000c2c900f0510365848c1c9500c030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 541882868 1250 541881618 541881623
    0xe0705030705060d270c051c11041103010f080106080703051f14010e0405010f0504080901030b010203070804030b16110606010302091807021c1704030804081903150605090a03 77
    0x1040ca003588860a0f0000300f07440c003000d90302c05803441782080440e500c0d9071781e2001070340c583c0364254020616080140716604460307810382c0078000c002080d503564400e9485d40d20703910b50803a0b220320034800c110140c800610301070803a0846502d01c407820104110b003120038542c4409241e0384060010000f04801142007411030fa900c585e410100044150307488050b042006544c0003c5100c0b100000345444004042c40c0502c1c8035000034010002c40210400540c0c50940f4040e000d17000c10400f00e002580243e02420341d020043c0140c1f410118907888610300c5801950041d2042d030125402c0040840c880e00d85007081d01c4113410700300d020070345094510390f44030700080c1501e05161740000c08a00c982e403140d140c0d0300c125981d00d0080320703036140028000352914581d07801c1000c0d00c00c84403240005180100c00c10080f80001c81c25002d142da440d40c408840000d03020740240d6103604200a50041218409040b1f8820343c96510702094074000b40c40074807000e0056502c4441002828045249259108180d19080300d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 541884118 1250 541882868 541882879
    0xa0e010921051b010603120c0c0e0601121112060108070c240e010603031b0807170c0a0c030b1003050d0e040e03071b050402040602070e09070e0f0a0e0705030705 71
    0xd1041002e803190710502d07841c09205103400400c10900d01d015002042036a2183d0000c00a03540c48050950b01040540002080c80c0b00a003002d0100e8085d42400f141d000c4414074001707002c4400d0042c0e035030031100c072500b584c5880c110002d8114000e44c0c80703ca40d41d42105081c82c02051526101100070300c0343c43c0c111070041c001c040450942c0c40c01c2042c0b071515002400291010005407841c403080c18028400e03484100c0c00702c0c0001c030124504251440d40210391300c1d0030003140c0c1d20b884959610b83c440101c1203100074280600610000d11708020810101074110b00c2843c1000519055080040b510381d002410301c45540c944080900001d00f020506c0407420302d40b410304101c0241c941d0001005400221071004103448045000380a2011044440a24043e82d83c480300b94a42c44030b00f40400d070b101c6d501500300503a0151000f00038044031b400c0c240d5800320044054440030740d00c8402c1d0060f640426503240e1400321148083c441000d45a00c602d2032071490540050550626220103e03845480074464a8400d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 541885368 1250 541884118 541884173
    0x903031205040606150804050606010302040b04030611040f170105010803090a030308070e06030a0c0806040903021c05160b060301050a0507140a02150f04030f0c0f080d0f0e060a0e0109 81
    0x1140c030780c10510145c0a0b0074030350080a65003003001040020111000e543d1849044c002c170b801075000c1c4c070072a010307251f600c0d000c0d500c2e2030304648800d0040c1175004a00c440041042000043d000b03031714040d45000c1c00d0125245c1d80800154082c9609440042c0c1212005400801801c0b4181d91070710804400c50394903040040a66451500581c3c00e22440c102a80d0450000420021900020741c4510025003040d00c8005440d200d42c002c0c441140c405900c0100581e010388442c584984070b60390380c40780514080ca005481d00400c0c1c1540c1850200d90f24040324000c05a00030b1103124602070103820780c882030315001000f06150900008003004021842c03075005c0c10703000803c40314541c4244090a02e49049154507403481c01d265020240321070040b01d05900061034407006040c0c403842070350590081500301d08040c0c0c0140041d29464119400924100784c0f16039a03107210621407410b4001c05140d21004070151a041c40c10844860549005418000c45039152204600015002031a017501d524a0780311422a103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 541886618 1250 541885368 541885373
    0x10207260318030d0e06010501270b16080d15060507020a0e130b040b0403020d0903150f090209040302070e09032a03120907090f060602100b040f11040e010501090303120504 76
    0x6603c43c2404d40b0000500300b00c14030044070000243c3e2412104207036a0804560400c00c44403803280030040c54000002c80e41d9004020b00b207940009090950101c0c2c440f440c0302c1c8903076a90b002d460f9106007445040d4940fa0f0442c015000380f80c00440c8000c0c41d803030800509d8007000d640003070703208413882c000da00524070901c011880c99481003607169141c5500100c288a03c1c10a41802c40542c1c0c4100c404400510815840c2c0040c1c5104200d00c0e030031241d00c189404940760070704550001a006410001c0705142da1400150702603501c800c086801b842c001c0c3c0152100c907007010b02c41034007600c00802b200c845501c200300500354101340c03107150040d21009407140301103d1004060396095204080c5c1128034280b00d18140800c20b0700204d00d40007100e0100400308201c0e42c0c41c903070240954400b4454000503800908010740c44091540020240c820001c20014a00c44840103c1d400c6034100d01507144419800314050080c0500b500c1c800b4054002424040401c03899aa001001507030401c20b210100d60b2104041003c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 541887868 1250 541886618 541886623
    0xf081c1206090e100b130b03030d02040e0601080709062c09090d020c0423040f0c1215110901110a120503060f180a090c090e010207260318 61
    0xc009100e6403040c800c0035500c06100002d440c0404580200e401640710900c82440c040c400c1a450040c0902404150301c050144940100f12540496030075010030450313205131600d144001d1000d000221490f48441c03d05000045c18040f00400300e4043c41415503040c42069001031000020400c00b1010404141e95070401c2d9800098192000390040c1822050081c1c03940c01160001058096908480c00c0d0703000c0b001004250780f11840b205e1803141c50510741420013501000341c10741c41401030400280c26410799591001d20480c1c0d50001c1e0075440714081d00001c00410a0504440794442c9800780580344408015034181d1203003210b400c0c1400250103184941e42e20a010050307020380c1090030031000d4440c5850140480c0e1080391003e1107040340c00c032400001d00e01100760006070044030050884945d00c0380301c1b200090420761003d9640000394000045c8692450003a640f030141108005a00c880082c500768541d000c64407103154101c411400310108034440e010580343e00000b1601040454640e83c1000b60 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 541889118 1250 541887868 541887887
    0x307032018041112011a090a09050c071a0601020c01030905030301061b080703030c03140f190204050901170601080d02030313030507120305160203070305180f0a0306090501060f081c 80
    0x2003d100210304011480c0414100c28101c2c1d00e500010700401c04040065038991103a00f1400e03511510001c4140400c0c84164051940724a4101c9c50300d140001544528690503030203110f060036282403400700102d0b5641031046a000020038201804414542e81d140c43d00c901050103144100501c0540f0f4410072440c034920041107603001004142e41d28900e040080203405d41400007408a17080006400c81050045000d078802c0014444100383d54898110007242c038243c5148052920f078091102045030b40e2041a80341c020040d009070f400b89551403901a9042c01416408013100303070000c105190415402000b16917100181140814044c05249016980d90180b0440600764500e01d110400d0a0303031b0941c0c04140580c1c151944440182e40f200400c90742c920480344020009501800305907142240421070700c0c08030100a0a18100f086c000c0e0204d401c0212a0b8010394056440300002c109010b402c1c402c0e00094103114030402140e40c107210200d0b030368a0309003044400001408404e240160310411803031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 541890368 1250 541889118 541889141
    0xe060f0d0303060e010f03050a02040f110c0c03151b030703140a021305091b0310120510060504060509010b030411060a110709050f0c070c1208030703201804 69
    0x1069400c000c1c00c000300205594002d03410752614031800481c50b5400302e80c043d8112a4040014000c05481342d003403101030812841200c001ca40c60b10f120090301c4201c03601402050b00b1400050070301d9500181011b103010f48003c540c90301e0a003d001030100603945592036062a44850320015036075200c3c890202c0080143c0100c0036a102d0304841404411011600100841c144107443d0b00030301501d41d803c10030380000a6072901081001a00b20122000680700030316413048002998880c015503c0e1481440502c01400480d9a904072200c202d5510459120300c60140174241c408100581c10301000c0b072030a00041c0900f035501d0f000800024100003404018499101c8090071030303034644102807006440200780103000c1e40c01d8000e404001c2500b2491344102403180551000e10542c5844066043c07100703502c100e6042e13481d000041008205800c42420710b240302403107180900d40d2441c00e540c0007002c40e0012500680352841102066500703903904820f58040e40101240742d07551a808200040061103a141c44 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 541891618 1250 541890368 541890379
    0x111030121080f0a2006310503030109060501080f19050c1e03010611060f0604020a0908070e0115020f1e011e0603050708070b0f0306010309081b0c12070e060f 70
    0xc0c9009500c910384403801017200341c1c0c610b1403440280c01c15031200001c907402d4076412542040c82c00c050203031b0326003005050401d45009503c0072071500c070542164826040745503450b40300d190400c030075607201e012554050845c18161400e0f05098a4150300c008840c1461805942c0700e1008c90f1f10042500c0c11140002071000b03132030446030038514040c04507070002d00c10080415800704040740340c00c40c080388061090794014141001507480c2070400c002904447c03149000c00250050100d811402007010301d01800d400d68950722190b00d0a400c0c103214008882150003150007001c6d0034a03800b200001d000d111162050402c034074210310184d4007030051024044034001a50f02213910f80341c0075100e90243c8296130046042d12081030700e80f240700340e41e44450f11a5407014002081050f2541c1c05403400b80d0f801c0b5005143c0800c02050075140d0030303000e4200c0943d05201036810000c01c80c0748142001301c1000e220058601c03603c4000700f840d034140c5030301c0307944036500c03030391540760300207000380d542d841c240e00c00312100404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 541892868 1250 541891618 541891627
    0x4030e041103040f02091503072c13050c0411090f040209040f0207061d120a05040b07050c01180b07080f040e09060103050705031615090807170111030121080f 70
    0x200ba1101a5081c0c0040e80100d95080201d4201001d051f0b41402031b0700c011b0000c080642c90005d03012651091040c2c00b0901003403450002095a4071200490b0280040095071043d10100d07080c45414000381c034280030300c19864401b1a03402c400c519002c0c0c030007280c4111000240140b10707102040291143ca00400c2d0312615140100c0480302241e406000f5080c0078601c04c2049000362500344c0404090000d001e030341540681c082c8032130213035a140103045c1101b1500c0e00e2400c2c181e40300441541a0002581141c89402204250460f0359000314920025003140c644507a5403454100b102001e0300c00c0724005880e514001642d18079024114080358010007401a520b00d40d885e08107241922400c01f80400c507500c0c0552500001d9516000912080c0541d003400c1c2207000d10300e44900d103c1150301392803115061004002000034000414000040200103900b1902c0607070000304526400c540741c0754001d140c000801e0006120030041141032440860400d940c1000480c00e609280c030080c06101c0041a01c0d000024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 541894118 1250 541892868 541892873
    0x602040807031a101509030606060903050114060f100c0f03200606010f0c030c02090a24032018041506120230150105090705040e04030e04110304 64
    0x7541c142203d000307900d01c2c40c20300035040118001d0103068860421010010000b4062610102620b42c60070015040503810645e0300e03035a41080d22072036440704000c540240da0802c1801001e01030317000c900d5140c44401c81c140c0b92540c0010b000c0f09135007015500035410484000002405500720451032a000068404810130500e80100b08007401c5805050303d0004030500300c90070031b000526a0040740141c440c8070f4905094502182c03000060941a010400c40503d03560250b01c54142d400d000c0c40c0c1401010545c8607513100e0740c00c0492a82c030b0312040c10403003600040000c51311301804992042070a50b00d00c19100c40845c0040c2c3c0b01100049410a0840d0200521003004048880c503400320620354403e215450f03450705004840b030340b104806500800306600c1000248070407050106450f60f15010805a294007039a081d1034809616050420f0103c0c0360014007047c40d000641070761117100c51503e6071405040c0101200d4244003d0801000c1c40710700e114440055990790894800000482c0b80aa280d14150 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 541895368 1250 541894118 541894123
    0x60903021534052b05031e04060b10020a060b0d020307170102120a090308011a070b0a1d030408161d070903060905010b0103200912030d020a1805010f0e100c06020408 73
    0x106807040010401c459054086000d903058a01c9801c500440d01d800104840c2d41445500300100704079042581c80c500d003241d03540e4000001c1101748bc3c40d802404d8076002031900d02e0485954070301c0184120124101d50740103903000204036059406031901442c51403000a90103029008200801a58618071400c1011080e40b40d4014084980aa9202c42d210303640c410306000d031031132101e11088000d1000c000c1c18001c0348803c000e0641004038a20000340410503080b1280c40042c650012111641000408005203d8100301c080a0f1840211480b0005494031141c9881600080024050110720b403000814043c0071780360b818000d50300900c081c400c03d040c40c68194001e004404450340400e1403c5009504031b803003020398a19107001080b10501c1c2040d020104a0048030b031070401d0305948000c1103505090342d01030001c5d140304012a103030b0780c0324141c2c6400d01059510742c0c2c1d00300f01e0402141004801e20740364840068808680d041e0741084107050a800c044030022400d07000981480e0001030b0025221200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 541896618 1250 541895368 541895413
    0x319031d010503060103150b030a0b04050105031c12060503030316020610210203010b12010903120b0901090903110d0f02010e0102130308090a0e0106090302153405 72
    0x2951021003040e10561045010160800000c0c001401440010b02d1540203a010558140b00d03a10000f500e9a641c240c040300ba58822100351a8003600c0c3c0b80005150709240c0038840c007420086000c1c1008101c2d8141080c10640340c20b0600040042018580034030300701d290701c0000a06030240a40b90380740781c03c01400e240500781200042c01403059500143d1409207001c100d42c04d03102c01e0500302c003000e0104500200399824540d01a0703455580ca900c00317241c0e0307506e0400500b0310f038403c140042440222414040c20340804020700341006820a61141e101d03655000e109819074101d91000a03880c0818101183d491445039410000d80c0710b8040c41101181d004010b44030312001c180d0080c4822000d50095a00740c0c0580120040c3c82d2210840500000c3d2240c400380c0b00440d8058040c881c81c41c0c0d540f104001c0040213a0007030011412101083c004d500b008024440002c41c2e010035a8a441c103092022401c0e0040400010101070407001c44c400c00c900e443d100001e0554108049171308614060109190301c008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 541897868 1250 541896618 541896623
    0xd09080a09050d0302060a0e100f0b010f021b2218020a0f0609031203090503071b090509060f0613021b15010305120d091502030a060e1b16020319 64
    0x420040000b258a405928410a198507601400f0542c40d804944000b8010000030707204a0702520501200c61011840b130700c02d03805448030010035041610030001d4101170307014400c1c0085400c00302c0341c1c015108800300f0324000b103081680c0078040c124079144096000f106a110035500e180c180140d08850300c0c28100c00c841540d0037160a10a800d94942034040c021900d4412640403ca030800100042800407416590304421401d0210712446159501c50666102e00c03000c03100030407040a40000c1510282c240c1c1c002c0e00411000304114140500e40c0341c0d44880052551707040c11420000203000740c654084034541482418001c2d51039860200502500c00000411b40c80036110701110900c5818400720120b040f43e4000380900001e121506544100b40e001c0c1e01c0c1c111045d80c5600081c1c5c0040d080c440309115180c42000c0040c0c6a041210070030701a41c074160b0201c240c402c521424020640e15280c07103041915210386160340c0d2051710b00141000f4145108002e507040c0504085512140700c8081d50302400361 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 541899118 1250 541897868 541897877
    0xa03140c0a18050105041803110c030604080d0f0209150306030c1302040302040b1f0c030c0f030818011b0509011209030504051507030c0b070c14010609150b07020402030c0d09080a 79
    0x85e00c401c02c2c001144c0905031039404a0644c1c140380b5020034000c88100580d200740c1000c2d24641c039003080200303251403820f443c201d9900b071340054040300c240103e200c0d00c003010342185030942c50b0044003400190f00309070030318065050003000804a09207650421401c51010700c0074102c00300c802c2000c4c0300b0000039040341c0700c180e005174108481200c05103085a032070310402406500481000c0016141115000031280d001c82c240481426041b010454050385048441e1080c2c2e40e000703c0c3c0c40e04480c5480c0b040c54448154045a050075100301851400e42d1044204071864030b0300d41c2c1c8500d401c2d001299550b4200d500024a285007406030020305a205c80100b00390348060316a82a03829480d10640c02c00e204050b009400141d41e804503800150904c0000303a00f1440d28a080f9900b400c41c1c0d2560010310030018440d44890303540e00020070018026010b01d4062418542c0a0b01000346000c41c0d51402d031240070741c000d12856000000070001d440d2501541ca4404410b0001c002c0b440d03a61810000315403020a44e8008074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 541900368 1250 541899118 541899121
    0x1212051b0309010e04021c1107060e0721051005071b12090512060a0f0219021c02030f09040902041e02030f1003051009060e0a0f02040f05060a03140c0a1805 69
    0x241891b000300d415846105140c16228154400301a004084242509190401c200008004a03035075003e001c136003c45140c05440d0144ca40218102d81c2c419482d1039006043c94004404042600411032808038200d01c0c1000c240c03682d54110844000c414a0f08488055100d400740700f040c00300039072514612503590b8940e90f00c3d143e121030070032400300506041044241d00c0140018542141da4101c00181d0a1a45c0c000d414084c4e1510858000c000c070f00c414100607841070200f20a0329004401c84007910456001651400c129002a450305205501459026603119900b0f44110740700c543c8040484d0360685450704411070385009800c06580251031142640c20072402103042d002d20000c10504482d0b00030700400b50244007000040c0078005d14001920b955903507489072803e501003401306c0c10b41c4600c03820031900c2980c3d942c4100402c8401c01c0c0b115001141c6080100009030300c130022020300703580d00099500240300c02c1400340c0f880d100d11884003039000405010005903980d0040c0500d00c1c0d03100110410700c81e5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 541901618 1250 541900368 541900397
    0x6012007170c091014030a061b0305010605090d170f0c030a020d032318010218090f0702070302120106030c0e01170a080a0c052b090e011212051b030901 67
    0x141441958000003004c00250104901500c90152500400c1c014040d141c021142c4c1e03c400c42190504c45040c04062038203d00440826030600ca10341c09024182006030920180e4400708071101900c0000030180c00300d83c0b500c01c80c012700c44800d4480d890341044030300381d0340e00d46030790f00319141c0e04018040e40161080a03880b00f079250080c060300f840e00507135000914043c0c004a06451048c0000343c2400d510f40d0a095403008070040a000802107080c400003c400c0d00442c180c2800340340500200900c01e55000e80041c4089640c1c085402401c498045941084201748011801d004001980c002028400c01c400001414400c0440b480d0489884d2500c4299084211244945a00d0410400ad01481040108205550080640001850042c0708a50031017100c0341d50101c0f40c03201840001c041c1d210aa0056a0303e07903100543c07401804011400629551401022002c000c8031075600505501e00940100740b0988990152502c660a516070700620844c0743c1505a20703a400300d02a10300041400d441d00c800d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 541902868 1250 541901618 541901629
    0x151407050a12170705031510031517030f070302190b010f0b0304030917030904050f040b0903130b0a03090605040f0b15010e0402090103020403121106071706012007170c 74
    0x3c20045000480801da82d04101100c99500c020a004c0101030031085501c0281c5619410060707640039034900142d10301e0141c80300360b403043d0213500c020042e0700d16140402032100088156051400c0d4403030700b162038174070a2500b41c0c2401111100c5068420101c038145080c4000307500102c0c100d4400304501c852030303a1030741540d034501d11040310060f0100d4610b0703404014981c400e0850040b03090300802586e0400078101e0005098480564030101e40300e50f400280020f2240010005421002101c011450031844603200a5188403a200b01c250645c0c0c00702d141c00c01207009804c0084401d81c0980100f00c0d138a00b51402c98040214842c050380c58041140001d4861401400e800903807a4058559511401030310041001039070200c0101070400d5001c1c007002000500c160603891030342316503803141d01503500e074031070040d250000041c04001080307105948262000130302c0da101904a0400e1030210041212601c01a904400603440800203111300000001c10078000c1d1894092442d507c400c3e00c48044a1104101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 541904118 1250 541902868 541902887
    0xa05092d1608041109070e0307030602090f03030c151510020f0d0e01211d0304061413060315080303010b0c010f09080901120e030316111204151407050a12 68
    0xe00d804d040290640040c5807440712980e0142d554039100f40308002c500013107401c0622a80c42260382c180c001c100c00c10203140c444030905545c0e07c01c3e4021030500000c030444556600344030540c205c44c0c1060324040384200140c083d900e01706076405400f454200d11502c8000b541d4940c1e15040480e01e0061048100c1c08030311a4424500c182d01c1692100c00c5030341ca00c1d89008106d00641102400c040e910140c5914910b0303400302d886654000080030356240d615004000d49000101940031040042c10030080280010f0600d1340c0d8207446083c9800135140a101e002031440c40c0c40c070340040e001d40c4008400003495500d10401070940c61041d00080c850007111910140070380d04a107100030851141400700c141a54451102000340d00220080481c05090403101c00b811a407054130245015030503407124036400b0790000c46207164020800003c26800c00103031448c00c81070041d07000b0b0540f010340420071104410300c00d0b1071540701e0030211640e0a603942000c0c0340103a41c54a8064044071195410408111003501944600c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 541905368 1250 541904118 541904123
    0xc0712030f0c0909232719120f090e040f0f05030d0609021c0c050d0c261006030e07081005010f0e01211403070b0703060909020a05092d160804 63
    0x444035110b00c10003686c10715142003062821028140e40650402007044241034010b05844080b45a030001d00305500c51488800a640070b1040c0502d80708903560740200c2c0042100c1d404000c10405840c0d610300205e1003540000d01601420504511006100340030000705000d22400d24204496603441c010740d0148c2c0904032000c818401305094485920043e44c1243c50308a000d803034058a44821000054221500a112000014221781c8a132154030f82d000d43c0d90800030301c50b00410b025417403c120140c10640144c0680780030140c84000d094010502003207024054001001034880955410540a00801c4244549500d5400100000034030312880136085050b60341e07040035990f118440a001151034071212030f01711844822004c5525103128140041d1002034818009009641001c030310003401c2d1400394102c070480b00c0c50188841c0050703603443d4102003161000d075844000d039940c00002d014075592070000c0c803011508440140d00d8410b00049d085205694020f851502d4000c096001c894062044800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 541906474 1106 541905368 541905431
    0x303041b05090925240504180f0f05060a0e0606040510110d03050106091e1208040f140109140409060c090302030f03030c0712030f0c0909 61
    0x901070341c1140b0303039003c070fa100d400c03c0c072042c594202102065007840c2190050a240034001c1c000d1f0f40040c0030102c140e07000e92071500092000f6142c1d0340414841d0038603200b4441005038071442802d0040c28058644442203040c1011654a100007400b15588480c060000255654607890483e040304004d036200c02c02080c59004052030020b40c1c2049405143c00c00c1c0040c4607003603101800b4001c0380d00150100000c4040c040d915900d408440e084058405a006401028402c00c0b82c010000c07201c0100700502003a40d500f400814403003049403000d00251215030200a035030521001403100d031800070400100b841075a0b9403403040ba10010780341c2021409100b000c0043d0b1506008000e4107040311400381d844c40c50b1081c03020170184121030005005d5401c40d10301c1c1c04058440d40c054442d81342400d0007001311440e600d0010b030040d00c1c81c3c40f4a4803028245030340c00b0980224604498481c0c0789001e207 = true := by decide +kernel

theorem cover : BRFrame.Cov 541726618 541906474 := by
  have h0 := BRFrame.cov_init 541726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 541726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 541726618 ≤ n) (h2 : n < 541906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
