-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5515
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:07:21.698264+00:00
-- url     : https://prove2.me/submissions/4db3efe6-3e6f-4ec9-b1c5-087820055e25

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 991726618 ≤ n < 991906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 991727868 1250 991726618 991726621
    0xc05090307080105250311070f020f0906061c021306091505031005042a0906090e09030f0a0c0c03060203010e160e010c0201020c03121908073c120e0312 67
    0x51100c01d142d03c021070f00205625617281c1604031000102408d1254007403011160310071514030401480c90091054540198080302c00c01c00c2c40e54668045e2849540380343c103a28140c0c4200c600000c000d2141c458008a04090305001260b03c583c013009810503a02003042d5008a54100c04064420b40021206801f8608128405200c2030800d0381040701a2485100189100a51112284401c0f61043c81040c00035111840400510750700c035011600514545040484c5803e0940409489200b015280e00708407100140d45c1e0b02c0c1911071b4490f100350b03a802100d2000d11135184d141c140d002c0e520030b04ca80c149a8001c0c0d0003041051002003240203010102d5162a034158000311700640d91809a0038050341076000b0103803070500c0c41d281408558100308420004130f5032010a424503a08221131000b04030b040040040c10051003a400c50000400c11000e0501c03007070000000e98030034404010101c54a103030a0101c07056020182d40108000c90100e5150505122095164545540e2030049110554a1240120 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 991729118 1250 991727868 991727911
    0xf0106120206092d1305040803161803112d040f0f0e03030403180e0f0a060914040212160e0604090b0403020c09060108010e0403080a0b040c05090307080105 69
    0x4000340002003016144181c0a0340854912841c8000c1da400c01c104103055414180542c42c14a907a00403c4440c144100082c0c102030312070349500d00002b05040100c200c440c8480510f58014114006800500040c2c0d06c13401d616490b020400c1081580c60714051082129440c980d0148520103074660401d808204250100800c2000b01405021039a2404207071355119001c06484c1c0ca015400704400920015540e90600b49002004070f003010180701490940da0070241300c200c41c03d030122034102100903020055620703440303519801440658801200c6ea880c20000c13843c0300442d1031407144210300840b80d40d000203590404c281e0302c509401f0035003045800c450318107108402c040030205810900150001515a8641d43c40d2288940207403419005a400074034141002c1c9024100070b17a0020013072801a000b545040c4480b02103a5000e840101800480f100182e00d0000395030200f00b9200340140f0a00038821258005001ca0384243c0f41c0502134012000003080d8681c050048d14040c100b5186600c0d082480729 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 991730368 1250 991729118 991729129
    0x11401120b0a08010207030816180608041106070f050c240708120f0a05010503012307030f1b080114011b050309100504051c120f0c0c170f01061202 65
    0x80402a44180d020802043d141402d2001d0680795200343c50b81343c03031800c00c00134891203201203451140800c00c01a11294200044180000c12500c3c1410182e401e07071101c1c6858040c0e40440030340e0f1a00308da008642d1405002c0004900d500c60790003003003034070000c2c0e1102c000c0c068900501180c250409118100c03a01c91916010010401ca07802008801d003002444013854581940603200c842c44c000e110303414000f4004440c0304071f42c01841c0c120001c000322002e000f485150300d05881e03079941c90402c58500081c21036000b0b03001120404040fa204000741428514407008800e40d00f00d406001801038800422548440c40c40c1c15400780c0161604400c1c01510b25000042c220a400101e0b0140014002c01019454811a1b180300481c0c03a154651100e060030f00340700b1b4050781c20440c902103441080c0b401010498081c00885c840101d1700d4520010740d0080000d503800e400d0034000134240e040b5200d000448501041180b20b001c14440292005540c19120940c01c0e10817a0007414000114980c58030300501c0d20 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 991731618 1250 991730368 991730381
    0xb040b1e0601051603020a0f030201020c0607030e060705090d0203150a0b091e040305040f090207060e0d0801180603020a0803071e050c190503030309070e1e01051005040b160b01140112 81
    0x1902c11582e6041080e0340e1048000d00300398084014bc1c0d000304207801d40c201c05112140d03103c910742c58100622040000050780e00c040c00350014007440400240c0400c0c03501c80c030154185c09a0007504451245d9902d1700741d1100c0e114100d44124031189403081044007894100b0341d8034019103000d081d034142000101001603020002a00c201c042c00400c03c800a403040d841c41c116801002203e0f00180c444581d0700740702003640c001182c0d4120542040d0240c905503034222401a065914030100d50344444080b00301d44009241c2d0360000f951019002400060440002006140b694400c0c04c0710840c00d641c140712200032091180d0024400c0c0c0004022541c10700f407108012040b80a104140700d91135030394601003810b41e48113407582060f64210b0207050110502c000c1e006030700103110080080280180a006030608401030140511034112400c8115071180300d8000c1d180609040d0b03c54a90f43c0103400c0c8030800c01c1c043c100301160310341500c400005480d151044180c03007210041e12007003801a0052113002c0241103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 991732868 1250 991731618 991731623
    0x11011a0901180e0a0b06010206101d1504020f0417030708040e0408120c0306011701050f01030f0f0204060c0512090117090a08030a060f150504050108130b040b1e06010516 75
    0x160368403c42000c0808202500d040b6015820300501410300c80002420800d004042408816145200704502030b4100348110b204011891030540c2030b00d980007001604030120810540c040c0c0007003468560704000d0030080c0121003002803100c0c020303034110340b406880e8040c000c1d0252070702d901803008020410121091a5010703214010785440e0a11029081a0003003080d606207080d81004801c028065070040c0d15454800d002c60b01c2c0d2455580b4040004000c012018082030401d83c031a004040c8500013500210300304801241c055448035200c3c50000c100c50342003503045c1c1c2d0520644c0a045405058101160380035241030751217107800e500811040354115003707005945188108090703c4041407240c07003d03500034505000049000ca00d0021000711401c5e03140c02c07096950020400701c000d000c0d000310407241150001c0c20040348540d525542c0e051040c0c1ea041000d820190785600300000c00c0a6004480e02c52035008040c0e110031a0325110101c4288402c99007a40807803810400301d501c0041c03c000d620580751 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 991734118 1250 991732868 991732871
    0x42d06050315041109010f06121d0a020a1a03010b1b10020903010e010e15040c3807150b0a0504110a0207050303070302030a032a11011a090118 63
    0x65880d00070078036103844140c00460301440c50040c40200305884604140b000812164a150b9506110307890701601d4062144906001512207204458211078000c10f00e818405001c44041c4032074445641d80315401c030300c4200d01c42c40ba41000459201c0300340c07030f040380070380c0342d614401e411a82080211841c650088030b1608a0401000e1041c42040e030070000c0d40594a00c2a202684501580040c942540c10541826103140d04149041c601d1500000d6000c1e02519001000b1001e51100c0c00e0926240c2c0141c0c106078605800790b4080b0101c0e0007004035440c441750342020004c820180c85001030303116009004001740501d46a0004000c0d40c00b107504420b52961f000ac12800d411980c5000140c02c544034264740000304c91000c11006280c4c1e07014800c4ca8020070701580076500c1c10010f5070340252a4450f000c88042490780d07442c02c07034001c0589550404158506502c1100e5007140840340074055090980c0c251025608101802e1440034201700c0041c100400a42110a940d007005209010600c4c3c002c054880345 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 991735368 1250 991734118 991734131
    0xd0b0a0801020a031509060e0402090a0603210221031303030609090b24031f1506020a11040b060f030a140115110d050a20060903090a05042d 62
    0x6001c0c4010f1041c480980c0b000a0092071200c007500745061150f000d03131481e6203080c200704485400e1181c642c5c2d10640c1155050411b540d040803100c01800103800261645500a07180e041040e407007000c041d1400e501e0303000c41f00b000d007141c2091311411000c800200b00c041c030b01b0b0000c1682c600d205101e21404a1003810003007200c94682420700300b2110355400541c0c02020340028403090121915403003101260607003280035803001132404242d60f208040d0304001d4406441900003041030b03559010046180d203140f02c0c0180079542e00002035561000020503900030214440c0100e880c9000e2107071000c0400094259424028688a08003060304014031000c0350700c0e1900580d4000c0c2e05401c1c40b4901070110031601204081c0c00318030007000c42c5010220000d081c1c3c444180d0030005504101074801b14034462a1240c040c40301c0c40d04044081d0b00d92160314210740b01d02c1060002c198008000303009024803d50307690102c10343d107004100980703903030007202225491102e21162110381c1891400c5440305c1030040c0410b04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 991736618 1250 991735368 991735379
    0x70201060902132c011a0d0606030906050a090309090905192636040e0d020d020a1a1b0403060c0f03021206011b0b10060e0111030d0b0a 60
    0x280d80c04111032141200305079006204185100608280a1070b100030307002086024092561340c600f43c180200050007088102c03003170810208000711515582c80410600486980e00c40240c05000b440b1070031901c01c0c1c20b0100040a449842c440c2d2020380360141c2c6d40030041c42c034210b1541c0007803240c05c82c1a90342c3d00400001300c1c01820789058140b02d003845186180b04910600c520300a00c6100b6000003584804100a150781c0d0807401c0c400755041074074031200104401a141352910000a2801c070f060b40040c01d14040420a00001c1010f20407076000c0e800380c1c1d10f03a02669108907219040c0000080c401061207100e4000d00030903a19451340803c1030900e04038140700394080d46505420a9104840b10b9480ea01e81c241c10300e81c4210140c905940605080d0300780f010090540309030b0480201803a04002c80c00d00c0542d40c0320703102c04002030b266410141c0c80c142418160a0500c2d81d907864040e41e400305c1c04000702c02035a94442c4050121048000028604042c485550000079184020301d803540440650b102250 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 991737868 1250 991736618 991736621
    0x711040e1515041d2d011508060106050424020a17031501030204240522050a1401020607030e030417060a1b020309040207060e0a0305120c19080702010609 68
    0x2c00390741c00b0110642c4000c000700801da8000390b0081403c00c68510b04070a240c80c000640400302030380440007101d01140c122001e54171612496441045608007038000d540101c0007503e00007580c5d07402d010348500e0303a03c44005980520843c03103140003c000c082d00b880055050168040c500300c04910542c0c00d481c40540707591078191036580340c04003035450000078007c4401144040c2e80f42d44101307090540c14a45401e9581410818007400b440240d003055165841c4241b2030000c5a2104030101720024030a05c03200640a856015405014001c5204c29070115420007a5600740c0d407042c80507030007410300c0e660310041200506850b201c074040a1000740404143e10b510f404a07076000c401c0103001005c240c81d100156000395402080701091514030f100408070403a42c04401c94001c040c0c26071340540e455195240c404010300900300d03119042d004030025142010380c058020715003600442442c10290325280c1c00111584100c6003400c0e22000701c8035040d181076004445140d40200c06000014850b65207216000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 991739118 1250 991737868 991737871
    0x10120914060711070b0702010c0312020406090302190302060f0d020f180108102d03020a0806070933031d1608030f0f070f050a0506040303110711040e15 67
    0xd1180c0001c0e0401c101554404400c005410390301d0020040341c1d1420002c0c0400d40b00341040681005092080341081c9805540d0180c110b44403e00219902c590b0b440f40185040d046000817231051480c410f02c42240c00c98410444140c94000301014a000e209003c96030055020700065840e050302800f03034210700c030300242c0902030a40b9080030210a0b402c204000510410000f448001c0e024245201489141c0c8442e942184280406907030780d60350725141d600841c014800742c0c8029070201d440e0300e0200d42c0110106803503002d4062900c5101c05181c032009041c0611010030300c0303403400d6103d01810400d088074000b10300b01e10716010700b80000c3d0041e0110360b07900030114140407280e140c1d000b000f810001714000c008220050411030701460130101d10400503d11440b514441000e000d030080b40da0024404040201808503501100300d60410a45d4070301646c690400311002c0d00800c4c074203220001001c1095007180c0207242e11a4803003034940c049804000003450341010040d002d10420007a204140c2ca003100c000e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 991740368 1250 991739118 991739153
    0xc030f0317161710050a12050d1d0402090609130e06092d03091002060709090207050a0f2405040605060303041a09310c020c101209 58
    0x8034240c1c042080ca0500288015240207000580e1059007980c41e64040f06800c50b28030641c4000280d501c0f914201242a80c10790440c40c0d0080c101c100010f250484900d02d84c0415103d442550032032415441c080d11501c1d0314028004400785041081d18a40c60291300a1000700d40c020a041d040041c0080480e01d241d400309038402c8440c1c1e8441c45601d00f80020004954010321b40b2b4002c0000781c0025403d4005c1c1140d004003d0f076400c0c810f11005032400c500b401a55000040030b424540d101d0442d0070002e5542e102650f9990100359010004989466a8021503d4040c1c000b00100884405540d51512a5508407801d45001c0740c04130000c054603003803011031090404071407000b18090406060100440d0b1001d0716091081d4000c000c10424540302040101c16080c110a803951610030810111741ca1404c0c00e103d0314014400880d141020709007060702d4002170341c00c08004000c030b880b1422041c0d07a601c002d91040c560001d480511460924070074003d44030310070860f0a0106480c801a50b1f16031907540c1c1d02c0f218 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 991741618 1250 991740368 991740377
    0x21905030d1506120b040608030f072001090b13051c1704050f0d030e030a0605040b09010515060a0504090207052413080307020c091501140c030301050d0c030f03 71
    0x415401c88003805258168982c030303104180c1d828601400540709103c881248003480303803600030085959a8a901101c0148013a9060342c0e0345890350480781009a01c00e003800c5070301d450754001500c00f2907400303c82e5648005044e100c40010340c0c140700c0000382c0c0342c00176080c1e0040714230304107c0800e260701c0d0b44854000103d1040e450f59400070b440e152800c46c404031845902640d020030300c0108140d643d01d031002d0070b100380207856011554045040494980c0c000001031505841703107080160800000d0350000d4496401500e020b02e254032501e040070700340d65094407048905052000c12403954030300ac1008018a00007800d01034a03055484007800c050360010003050311250000f425180e01d0307200c036800200c28400b15000211903451b00d4002c00800302c1d010000075000480120000d4500c40c000c1010590021008024041c0f13440d00c086840c0340301e901484903500044a90000542810004c0300f92498001044003035829a801c00d028400403452110f41960780d02080d02001001c41c04c65008071198038080c1d0369 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 991742868 1250 991741618 991741627
    0xc020d14073b0c040b0c060f070e0123070501050108070f050d05060103030e0f0301140106181d04050718020d0b010f02030304020f150406080405010605040603031e02190503 76
    0x49480800030645011000403802612403010314502142d1016048548000c2455151004042ca15000d2a084000f0350740b07000522000f140c40000b0301c0c80c802c25020240c0300040d62040c0c3c0445180c41036105d220301043d07492881988440b4240c05200100c8000f5480e141491030782d844a5003500d40a030303c240300070742060b03409205080324914000003400c0c0648580c0058151960384640d0741e00144030190810104c0c950340621542d5a50024040c0c04000f0000d1065850446603850030307540030300c0b840002c12145a4240f10a10360300340900b0803511007490b80740d00c514000c10498480704005108071814000c004000c10f06000400c0341041c2070125290050b01c0d40344c0c06442c242165900c89009d030600c0040760301e05501d1907001080369481941510740d28040340e82c05001c111032042c83c51072110403120100d8007281c600e5008505500c10340c0180700a00c88a95100148011107080b80000381c005498181008034419007142030904804491040719503040b03a0007900d06096142c1c0a044803150400074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 991744118 1250 991742868 991742879
    0x501021c060510050a0503040813180209040f05060307050f130501030c1a040e06040c0c0b070c03080f06060f03090705033309280c0905040b0907030b04030c020d1407 73
    0x400f00100340145003040d600c0d1200e543c01c040d01500004200518003000095945074140840080000038001c5515082a0003901c079080b4000e50060550b83d40540c2c58902c4444003111280526406500f000e40507201c46824041031092142007070120302e400103421004403241c04150305c113380c000c40c000c291225080382000790000b02e030401c0040101c9410b2044c4800d2100d1090450749581040003207800240c0d00d4183c200580707125291100143c450b000c9001000740607a0811100204180301c6d513645800c50f51035008403521402c00740c030a00c0e00b00c0020300c82706441d5a0207100664101c9036840444040603a2100005e01d4034030390b80380043c410b41ca0081d0841c81514062103e0044e100a0f0039001c601c0e140228580d0b0340c0ba9a080c030000308152110051a542d20f11140c50002c03900c1c0c00001c000480743d11601204094070044d101141c46503c2d030340004600b80e00200f00c09050302c2c1e0000c000301d015111a18120740304140c044080c0e9000c41c583c115000056080328804c9a40a80c2102130540310b890071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 991745368 1250 991744118 991744129
    0x40510020a0305040e150306040302031b0f0309040c120e0d08060d05060c0d09060e0706090812030105130605060c010b120c03070504050a020909150a06030b090f040501021c0605 78
    0x5800400540d88046540c0340025041000c1e101914000d48000c0890345c0d0b9440020502aa00c15605805003d01001c0c0b109041c2d0100080c5102c00e0340341d24070342c110081c0380d100d140e8840d106107071080700d50014405030340d45243c9078002003d407215526002022003120744881d0101c0c0c604580c543e00319804070900703400032604100d0b03c03a40044116503035080080f080d203469466840003001b61101c01400581c01c0042201544035011298003c0307020002d4a0303140354400c4d994080d80c040c2d440400c518a90000e80048001198440400207040090031a460700d800e00401943c5c034a84401a50707100e01300441c1d503403178010292614410720000030521400345800c1c0000a54001004001034004003480f4407a600c001841b17004a4109480024042c2e880248640007405810f403065804400304040c0101d01c00b1006c060783c8a074108859042400755965002c0e02155403445803240c0000b043c60008003d031158040d8160b009000ba030015180c1400c01200d640008151040c0442e0b03a0780c0c0d00000e000a0500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 991746618 1250 991745368 991745389
    0x180d0806040b01050c100e1c0c050f030a0914010309150c0e04050c04061b0f05031306031401150c290108010204050616030e0607060519051b0d0908030a020405 70
    0x2800d04a25112080403174a407100315400d41000f842c1d40f104c00c1082c5039401002444150020500b149245400342c0c00014081200c2c900c0a490600c6007036140c034580f00011085400c20780b82c589030b03880c000d45009030581c02c400240703002e50305150350ba403011800b103507c8064a461141003060002488860000064071000c140c0c4200790040349000204180c0342e090303204032019101a400e0040b641c0307c1100c5448503c00b0803040c010003240c04021010200301001000e041c0b462002c1c02c050a82075141c00342102242c00e00113a101900064100404c80401460500341c52403440d89080c0b96000000d44505504140c201800c1e04c00c4070750101d1401f01030441d0669a8050013900000394a058540800958a40122105d040d075611500000c03508250103881041d224610160801e07440e009135051100040000b00c40e015000b01c501c0d4118024100c00d03100781031040c8140b00000c00000c011545c8503510340c0041ca05540e01540e510421400314146c680034512032401c80c2000360399203080c0f40074403441945 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 991747868 1250 991746618 991746641
    0x219020c18041b0f0f0e1005101215031a0906040201020c09090f07230d02060a0302210a14090c1f0302161506050904030c110f04020a12110f12180d080604 68
    0x301f0346000e0205540d6601400c002802c00d1410307501c091091554280105409003138140640304030f4000004000c213051a00100f0690300015a056503a61941c4584801049400a005030000b4040e460f252408190305500b1043d24021204d46c800b001281500d05240c0d504020880b18041402012031342c10b220002044900940b038005c01303407805902268080c00313030031104000c3c183c012520070885c0e000e48264850320943c1c10030b091214101002c01c7c00042c9500c409441d6401660000a069420001110300e9801f5000d04000c203241c1c45003400d12105103140b44054101602041400c001400f400310907690b090042102400c03c00c2091591000c83d42943d11141c09081c0140c200003303e0f400249034810340350000000d0410203000d0000a400700c011441c1b16602510120354503d0741c0343d103e1011903002c44040c204004894809030100c0050107941d2111025120800210023402628200340344c2080045a0341d2511200b0360750390500305084c1c40c40000c002410074003042042d14150048041c0e404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 991749118 1250 991747868 991747891
    0x1324051015020304050d26030709090b011e09120b060a0603050c0d02070c0b070807060b01020f0d030b0f0a06050309101b110a060219020c18041b0f0f0e 67
    0x403001d0074082e440e401a4400e05100320f69001d100d8040c84418181c0f0340f200581144581c3c10900984110b11181c0c1090390444006404ca420100d000038003403286c0340385000140c4500b410545500038215020142d01070501c1001090340e4005101c00c40301140604403881f41007444501e14108051004210507603011000709801c000502041081800444d0059076860401503543c001c0f0342030a003c941e080f0742c4801c1080750001480c400748181107004e030a00910418050114200d08001265a0010b80344403069640000d9021401e80d400f907880b61050540280680300007a025900056012220340c0c05240404c1000082155600050140b464000d02030f540c1082520b44440340e440c42c000903c3c81c040300340203c4a40c49040c902c0c04101c5000034503031000d003c1d540c9091a00034016900480c1001c0005442130481104051070f00c05411012003200100650381543c8684a88220010b8a61900101a0013000204020441e85003c0c006030034030001502180b0324182800c4e04a01004050700d819a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 991750368 1250 991749118 991749149
    0x30911060721050c070603050601120c081302030c150306090a090320011b020715081e0711031215060307022d070f1e080613240510 58
    0x42d00644800401024800c24440c414680c40802d0710a88a2030300d043c030303032841103500006d145503154012520583d0280e1b101c5400d80106001c8800f0f851004d0514804541c8034400511004130550000b1140c034001012a0743c600a500e0200e160440d60031203080341e20000200700105410030555a83e000700b801e05041152100d10340b401041c4141580010791052441d00034001150425048110520304000713411082c80c8001a029507a406140300d0591030020514041a150740203010840c4100d000070a5040082c46040c0036480c5904000d0182c8203002c5c0400540002c900d041000e0b04d17400642c90740000d000d00b441c1d18122200c1092517002d51017214100104541c0540c0464003802c01e1184100341c51252442007210891000031000641192040007000210801c0c0b00c20103504503042560281c4501c45a0348103c10036200318061013410740d06c0400820036a201802203c068030307003d03015280000c0302c010342d90400442030142d10740c021615041441401400100c3c64002001c031081469240e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 991751618 1250 991750368 991750373
    0xc0d1808030f070314070909060602121e07051e1009030509010c06060b0d0f05070315060507020a0e19050906161b050312090f03040308040b030a110a0309110607 71
    0xa480028035101441c24002d01080c0300500039002100d0502c048202d038406894400c20081ca001603521903c89514100f03a00041e4050020a0400c03104007003c50044c0f500c44081c007202d61801c198900e40421580401c0b120700811400d100e1082a80d8102c0d0118000c00c511a114a2800703404401c80b0100c5850f003082400020340050480d100c3c228203081c040000d002ea414032070f00600c0641e020303283c1d810000a4054058115521940600141e034504000c00d4035490800c800b01c42c00e40d81141d540051041060002d603004034060404103100515005256443d040d20301c10303401065852049018035074503c00d150507044d0281e02d0b4004004401000240742042c820200000d0b4848064284668241d42c0501ca00c81100d00392503d90304402101d944480240c2100b400243c00c540007410350041400c1342c1c41003a404000c4908582d04281c1311802d081c1443c0c1d41880c80c0d8800360580001542d101c01c05503071700703000328058445941c1c10385002a1050035070521259685041c40f103a8130515007040072400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 991752868 1250 991751618 991751633
    0x1b100c05040302010c0c031202010902180705040e040c0b07380c13030605091c0203070201050a030c02100608160506030402060f2b0603150203070e09060d02090c0d18 73
    0x100c9030246825100d45d076860402d21072800082d00090100140d84050340d41d129015080b01129030320035a007130481281091000250303941d0564000c80003e10400003000460312044540b500280101141c4030541d64884091103150b00400f011107203031541aa00700c084212140c04103801030908001401000000b508850441d5401040b0900100c4040354010300310480400c11806160311200c20400c85c101035100e40d036608074103031100d515418a01c0a000c4414070200a650b9280d5060312034a08015000c8419400303441e0b0454950300718490105a081c0901660050100424100b406031541c4c0d801d1004000d40341249070049030040381d08005120058503504100c1c0d0360000702006031911100320025414003000c00104400c8079905480100506000380c0d8001d000f1640305080102c852500040c100045c5d01080742c040020400080e0341050a0401c0d900444c3c0c455001007030408251040d0b0300007002c075030040d6100d6802150100b1a096080b0540c030800c6d407058000070004640080d80d554a44 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 991754118 1250 991752868 991752877
    0xc08010f080c210a020414060301060f03080d0c2d0e120307020d0206090a150206160807230d060e13020a0311060d02040e15060405010903080f0f1b100c05 68
    0x196003d1542a010003030070f003c610b103080d034018014071449038100c416219031407040d00c0c058030951810000049005c4001070010850341c1c0041e142e4142600c203407002c1d000b0184e81219206100700710342030074002c0c41e2a0081a20707400300722641145281d0f045000514241d044e0020500a400200300040000000415104a16070450b030f03d04480e6410310100e4418000e642116800012540000c20b0300c10025151600c002d5003903089030a2596551044110060072403503840208121070042040340c0c5c450101c0c0040341d00c0060005070300307a4500b03c000341103a0060118101c100c0c0c1d0340c3e00602418004a413174541100d008200c0c000d4498081e000140406035900c0014181c50f4008100115611a00c09480c0035004160085446590301d403000d00c0300220840f082000c524909414074407501d003500640d015150107030f446605c0181543e82d1102182c1c400750280c404400144030320102001040e0080c5504943c10001171a003148402d00c09190448401000003078a00b045019000c2560000944 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 991755368 1250 991754118 991754149
    0x80a060e070e10090c02010b060d02070c1509060801150504060f0c080a0c050c09090c01030b060c010501140111010e12030403171614091e130c08010f080c 68
    0x158034804100e42900c0c00c0c11a034801e0094590000c00c0040360004051104102c842a050a000c00c540300e2500307c0c01c0300c0301c1c04201e80c0d000070300340829130088000b940a042e550740301e1580c003242d02d501c500a0940c0b84011910040008000075000c1c02001e5110804900600c10401130400e1183c1001015225002d203001c0c0c00c04000c000508482d00500c6441f8501e0301c5604500078683e81c01803050000d2000d03102c0e15095a00d80b0a0f5401e0891034240790b03017514071031000640a02440a0300c07500440160403c0920341d0b81c068014051018131560030b1007402c5c000d1500e0803050880c484400c1c00900043d8001c070b00841076900d03000c0183c4d82c0c0540421a405200303080700c1c0e0790385d89964625080e20742501c1011001d5080030f4000401c100805011151280b00240b0b40707415803561a000e511900c1803044c4500d25420030046540300448020145014100301001000d10b282243c080100b07108860b080c148000004003480e0042180000c0e0b190700f803001e001c04071701506004803810045030345984c000d0f440b07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 991756618 1250 991755368 991755371
    0x6050a022a10020a1b050303070f0f020d1107050a080604060b0108152103131e0617040c0305061311010e0906010809120d1d030a020703080c070506220503010501080a06 74
    0x1c1044543c40f0381c0b8107000c800c80310840790810b1246811b02603a40d4104980041c04a000420640b8907540a2050240c04000c3c582c02090342c4c0a01c01d40c2152001d980750409580ca200350040451640d644101032809840400d00038201850981840420b0340c40600c4501d040c0940c540a201080c1542082901c030f4500a58680c4186003504d50308031684205140d240f02d080c00081403100b072541d045410801103800c120b03c40c5002c01c00f041031502001c80548102c5021a6940c00101c004000548a042d03005003d100c120300002d0352501c4440c1028411111841d030303406604820400c01071191003102c6104003e103001000d21100ba400b0481c0080003134012414451034500044042008008101034100350350121500c90500041d00300c0580807100700300803802e03034019000c55050b100100392428580c85034001c1080f10b145d51075600c0300350300c5004102214028174a001c02c09803901d20051880307510904445405508040c050681011107030440380c0b281c0d0402004100c414000a401400d45406c00c40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 991757868 1250 991756618 991756627
    0x50d0b06010c060903080912041d09030c120a02100615030902030a060f0c0e06070b0c07151806051806180102130e0403080f060310110706050a022a1002 67
    0x1030b14201e014541c0181a1810503c0c404101940301c60454000c1c0c0e410002c85100c182060002e00880c0114020131840f1043d10028002c0342e4203500b0400d41202059099914081040035000c3c10240501711180c40c0e83c50008800c0c401c0792703040058100580504a0030000309041464107030040c1c4903500d9100415403190b4140d0107540d002e01156007600d5000c02c0800401e25031089000c003802802c11b20714040b504040305041c85080100031684001d500c600588500e40d9409106001c03900460420364441d420240c582c01d6541071442154002e107061129031510703440030300d00701c42a60001046a151000801009504404002881c1e900011002c0c403403d90703200110a1240240a403180c40102c401101100041d049004110039001d10f00a40e0340c83c0d0555504180c00102038001e40301c881e01540700d030078011000c2c101d50f0b200d07a00144001c0710705880e10714162242010b807103082d141800642e9000940e440c4c80c2003103454a100400400c180800106201e035038043d10346081d0481004101c1c2c0018 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 991759118 1250 991757868 991757881
    0x60a140d091b03030509010c05032a120c06010e100308070507090623040506010309050601090e010c020610062d02010f0c020a0b010e1506030a090323090d050c030a03021506010801050d0b 82
    0x402d550000700c2d0032f6405100300007840076010503081422030356000c0d401113010911128904104613580314605000600c2c0d180d180c080403c0105000070003a400e01c00600300040f000400c2c0c00000d010940c042d0700205940f50030120f04000b2240d80d0b0b0b0010045005c070a011406013003031001380c00800d50040b5000641c41d0b4880c401640908030007000280140519400811a2405580503804952562000b0001500d40d564113aa95080a8505002203003d106003000241e101d05c186000c10500b00040b0200e422041800c500503a510041c0350000d41d4440741c001001640b944204007400f0690f2000703214901240c0c80d000311514040c066018201d200200244031060a8400c140a10002409071992864000c1003030008150160703089000a03800c0d51140703e041030400600000d180440074041c0b52036405410004000440e1504a50900407491084401e90f0b0610192447c1c5000f0380190885940b0781030350b50001000106250f0600220700014011902c80140141701c5545c020004000c944414 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 991760368 1250 991759118 991759123
    0xe12071b26031e13050108010308120c0906030f06120304061b050705060a0c11180105090a0f050115090911032419181406060a140d091b03030509010c05 67
    0x3c550341c4440510501c8020400212040141842d1607a0081200556180c500441e01b40f4000e1001a0241d0f1090241a00807880f02a07050340000c4418147d901d010340307034004034040340c10031916200907841c60030410084d07081c200d81540355451008080d524103828681c019001d4403500503140c480b5406424400204441000080d024100c001c2c882d43d15000c40040040018601c2c82007125041c002d403040b652241468500281d40c1e50125222098507170811b801d200c01d94000030516006103484154032211000703e84502070191402c4141c002c54142000f10150a0428540c013484d10180b80c42c10a00740942e400040d42e41062030071068104003200c10400f48076800d8200d100d1a4401411078903c400101110700c050100d8031a8100d045851200964400440d00c40d0814440f0301d142c2d032000500300d446d258004002c51030960030000700505030902e0414840d00f0500070b1028813541c03080a8000e2080c025448405e01d0501010560882e013182e400030454010401c40506001602d1030171700400070107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 991761618 1250 991760368 991760377
    0x206041403030d0f1521020105030c07020a030606170a020d030c020607050d02100b19050609130513051519020f04050907020a03080901060321030e12071b2603 70
    0x20000f03000384d44036400440700800c2041d03013548004103540c0000818080e0003a562003036140710b80004010100342e800655403584001d1506455880c1040484016525420a1000781d07010b41e03400100a800c1003503049200d801ea84064038507074040030741100160707148500c40d00c685c0e42c1850b10308112509880400e089000d07034400100f49004402d81400c980b98006100b41c5644450035092200100d0103050181d0304440b5402e0700704800711038030240454180071006004099001e4404104610701162000031a441914002c0a0086201194003401001c121071a1301c80569000000c103070400000c081000d003907443c01e8070003854000c211100005945401e60300104030180c01d160441c43c01c0c1d240252103c881000840207c0c0d004004103294200521444003529480856200e041c505c0042c0346403008103010040d420036407102c0c140d180070b90f0148180c11440c0004120b0710740310701ca00c2c03400703c001080d9085107101301c1c4641c460030846501350400902d075048186420082480219540e6401d500c503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 991762868 1250 991761618 991761637
    0x160302030c0f061006030e0c040b0a090204091d07050612040501180308072d030917070f050d022b020f030c0a1505090a0332030403020d0c020604140303 67
    0x70390b0580c000c0603003002c10000d02c50944d90700416482d1340c40300c10580031503103013600d6080c0b607a00010814041d41810740c801150130038001c04a80085580d4804141aa4030a40ac103a001070344811210541451940e2480c00503c44840500300080c1050f004c104c807801151031000d501e4480101140c1802002c0d03100f154950742c00884445062900d0901424203001580d20600007500c0c01d40420404d0f2028020b5003a44500000500c46140c0fa19006c40c090141510b06440c44c5c256040e02c000352407140c1c001000c2161249030310502d022240c3c02c0250501c024295900255000071079a140c10018800c48940d11943c2c400d00302200c05d80c492003c0b840c1104000300c18110b440005003801040d81c4c00500c078110b07144111180c0c944903007403048003802e8860a4449170055440309081d0000680500e9500e500138403034a000381d240c45101d695441c4400b807c60300003507071100000103006c00d25a05000c2240c84200c2418031110b0071005901003501e03807185100c0e80070000580035943c12180d030180100c0d6890107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 991764118 1250 991762868 991762873
    0x2040501231c020318010905120904060b0406031e0203041e06090c08030919030b060d2607021e131107050f0105071b030203033c09071a160302030c 65
    0xb40c810108200070360003581c03104400350b0121103c10301c440d014024007001591003c06010240720b14880c12040c2d420100d191544140c58040c041100804400500020007140e0b81c0803610049400c1c80d90f114030000e55104582600402c2004082124001c038040d03110400d03582e41d05902150700740b47c0020001c1010052503a03003c104005000d8100201810214404441e0800d0056640032204040c0000d40b100500035221600000e5003440c101c0441128140682842040700c1c1801e030110180e516100c414018100004c0703280c40c00d500345a001034140c0780000540c04c80f14000d60340040c0d06012580e401003407494a60f54152101c2648105070350b5059440030480f4108030500d0720850280a08841110009149061104c0d0080f01507001c0c0e100140c040d0051455501c0b0f40402560443e0b019141803180c1e108590300c0d1041c140c1c1e01c074200d03102c801c40031120301e50350034880012400c1803403e91000e11015140b46001e50210140022104000c0c40c90320700c80904141d0f0300d400e03030030b600802014540c9030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 991765368 1250 991764118 991764157
    0x1170726030a1701080313030609020102031e0a0201060b030919170d02030105121504060c0c020d15050a0e030f18120d2706032309011505040204050123 67
    0x307801007410243c1c0c654050b03041e03c107030f80c94a4071942d0324080c40d0900c214600d00e145042000c5080c40d804210304c40e00601c156840d2506051144001d001c406a500c08000c0002032404a82039080c0700d03500151980381d80741ca01e54148182140d51310038844d002d8500e0041c001e80110100002c01541e03012100c400780304103440300700710f01e8914025002445801e01840d2206a11005c612012905074080f400c000b0000d29291256250300000300020100c0205014014030980d0240e1703100418091500d101300841840c40c81840c1d09141030340e40180c450301d10a420900300a81141000c400d64181d0030203100c1181c3c548800005845112925580313240c0c0040503602103041004001c1000258404251103061403075015000e16488001c404c0309211525803100014400d09121f80c0003885541d200208401c2c10b00b2181d50009a241c07815140e2140c0c1d03a40d60401d080010401c01c2d1544000c05080704c0840c1464940400a089189030901c0800300e60f006888881245c40c1d094151070401920300c4025060 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 991766618 1250 991765368 991765387
    0x60906080a050c0904051e0a0606151d01020c101707020703050f0d0509101e09050406051525050106061706040b0d0605060d140c090117072603 63
    0x64105048058982d0702801450071003904181403a41e00a40d40302004000710384d00c01a500d400e01c0501242c262085c021800d0280100e2014060b001c082c2c003000c0f02d0b00b8696544108050500814404d036054a4661a03085240300d03130b004506c00300351400698002043d805521001ca541c6084040e01c00b190b0212107060000e07086e4001446e000342c9100307404441c0c07078205018450781c0e10b95007421007400081c020800070403035080801680071500640c0c01c218500d50854071030701c1c03804034440300d1000c0010503102d0b0401c0700c0d151500486004190541c4c100c001e00101d100c1c010341903c100c02054421000144522184400300104640c007540c0060007044400d454090040c003908407812000030703030b4905a0100d5501d08d480d10910b0901d41c0002c004240e003180d190384980240400800040d0721902c0c0440210106560b4458400b040d2003000140145a440030208010031106030000047c0e4124080b089161450014a410658050301c20040c8441c0d804500d90041a91092042c0041c2c0000f143e046078 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 991767868 1250 991766618 991766623
    0xf0a231002070803071e05030703080609010512060a0c140307030609050c030112240e03090909010504080a0c1b080d0e100203070f060609151404021801050d06090608 73
    0x5000040340d040c4038011800030304aa54221602032000d054104000030070004080d2100f0782221035424040300e0400940b61961400c3d900b000100340e0101c1c0c0142c0c10400380d86040200240905030850f2406ca246c006410340790b40d1420020a84452165110070318200705005074145c0c40815003281806a0340d281c00303030f0014050002881521440c070304040210315074420003030640f0305880048121100041031394441710b5203d401d43e00320b81804d1400014140481d100d500605110781c045c81c00943d41d80303070040c00307000349040c00805c6504c280e4588400c2c4030000e80f1410854030380d4401d5140505e2580c42d10b0030a10034203810480c81500c03a090380b00d80010800c2001c036540c00d0b11080c1d61030b088141c8540d002803208100402c809500141c00800515000680da0005c644101d4007070100010320a450707140e02c60446000c08070600d030f0861401402c01c802c0241c0d10b05080100c400341c40540c2042c003500c100408030b1810b449124180240400e0208051081c1d6100c20f00402c000d0400303104c504c2da5620b6068 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 991769118 1250 991767868 991767929
    0xa050310030f031205090a0f020d06140a0e070504020901090e150418020118060212161b081009020618030f0709150801051005040c1e02030a080a0c08060f0a 69
    0xc1e0131904104c0054100080400c0311005150040d0294115041c0c60b0308104c04003400080807502240c1d5001c51440b01c11201d12403074451201c0d0b880c00580c03000b2880010385400d0072540424030031030040060b808180d901c0a140401c503001c2c01000d17400c50725540c510303503d0802ca88041e030b0f810900e0400d00c5110350526107482031446001f80c0790384101c0280f650642030428614041c01d0003507488140300100c0803043d07100a00e03e06501c8505a4090075096079010704e229848000c95694222081050006240521904444c1a6a01d0f01009805d1240d07010807903600400500005800c030320324a02d48161818040810b809181d03100b554001602e8213803600c0100501d48460500c03901d4001d021924403014410076000792030300211081030350314280800001e400302820b01000c20200b0202d0310b4400d0901070301910480c0440d009962503682c8100020014440100031021807824528100e5946030001045030300600141e07a600100100c1d100403401c004250791043c02580d01040c05410b85100308041107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 991770368 1250 991769118 991769147
    0x150f0111011e1107020306190902030703050a03030605010813110103090f0b150418060c05071712070c021e041b02010b100207030b0c03071707120c140a050310030f03 73
    0x1c0103d80c220940f540380710701510400940591100010542d510100c039841e070503038415030b040443e49030100e901190500d0202d500407200c40c2d100000301c004140c0c260080c507002d81800e20303040029140812410002d143d4048000c4e0404550745c144400c1c99100b40c2140d8600f50308000388120840c2540b4107120f2443d000c03194482c02d600400f4015000b4070300707405100558009880380f040a1012501c03403000419149034180240841081001d0010300c0403601040c0d4407194045580d02e48181c05400900c0090060441081011200744000140d461400e500c00780140780c0310300b8400010f03100100f401801039018034136180041010440314603a05411400c0c10110564407000703100c1c3c021209a0b510f03522070100070311007920a4000303540c41c54a5005164022050b161640305290300704994203081105a440400123044003006840384041801400d0001c1d403145403c006040c0c04600700c100c2402440c101c001002030010204500611a43e2804060754006406124440d010b01e00070304800d0000025 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 991771618 1250 991770368 991770371
    0x40803070f122f090145080706090f0b0c07030c08032523010902060703030603110a0608010b0705010906020c0705090a0e0a0803060111070e07110105150f0111011e 72
    0xd800d0340208810a4039001070041c0c50300103e101b054013498a800d00c0300c010a84a030b0101c4805e803901c820f80e1080c0751800b2020100740c0c00c2c95600f40090742e81024440c0c0c100364148021018200588441c2d000c02c1c001720341050812039146c88904880c0e60030f040c0c2680c0302800504000c5000300b02004044014507a443d140c0d49003035900710558500d40356283d08e8010103080c018144a401c501050107991305902e050f02c0600024000c006540080c0c0309400940041c0d00082c3c0d20101441046900206039580c0d039011222461850700c1c240008149a0381401583c0f0981e80104a034001c200702500f185d46c4540d030004003035407566100c500f840e50302c601620442c1d1080c003080000c644070461034810202c200071f041e4060240d41101703860360f0120f80d0020b86814100410001d40c04031a80041c03000e000549404007055500c8c2c10150402440b03041b000105071426403500d011700511b070b1500e401c0c92030816016940341e0b07010484100140e0340d8502465039500c4075404c0001c40d64022490361891402141c0c2d0034030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 991772868 1250 991771618 991771691
    0xb1518010305060a030b040201090e0f040c0e060a140a050607060e0606100215270607020607090e04020d08120f0105030721020112020c0a051b010206040803070f12 72
    0x44040d110250796803608035013034040c02e0000c20104a9003641c058011705118025035a28aa0400403c80448003d007041d406001400b040105e04000c5e00c008000d00c4e81c210007107051410001d240f241d80341c488c104040c0c0b0380076211610b42d1900704800703005040c01401d82d41c03508194100500074000e022919119809403000041c06443c00344200200b0741040c0d4002c01d0300e801a1050003607400000b40c0100a04103800b1400c0c4445098000407002074a18100a40128205010b000e4503104010f460b540a0103c440c8050082c240c1c400000c940c015011201c04044220a0402003034504c180000d82c409803500700200010000ca8103001030403940e0903811611104d81d54030482c084071502c0b140c1381340e80c00c06c0028044099803003070140d0580c5030011a00140f9118154104a01c3c054032050103ca41c0e4000742e603a01401803c09010943d1040700f8006440745152a942d03c44c0c9a1000030800c20502101c865601800344c418001c20080c1a028002003001d41c075800d0703030201060b51005c1c524004c42c01504 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 991774118 1250 991772868 991772917
    0x503040501060e1308161e030311030c0a0309080f0403120908010606140a0e1e010e0f010903080c03040305060f0414150a110903060a1d210d0b15 64
    0x216038400d801a040e8044078035101d40da1082c50303921038501c43c0103006070456400081001d4405080001144042c07034045070060b2314000d01520b0308680141d10440e020310030800401e26101c00c51720381030703214039000509244a1404080a029a0f01039200701030000c18003104100302c0c203292580405160f11180c403201d503601515800d945581c0109030000c0c510340880100c2e040d2410103411110510f0400c0400c2d00034002c04243d4030725407280f00b0782c0301180482480100d96041001d200201d00c0690318241c4119140001900c242e955100080103207000042800c60707810f0500558020b10340c060259441c5007040010800300400607202545c1c1d00920801110381000006039008089139003a4003100195120700c0420020000300e0b84002400b10300308041110b41e5024001541301d10f480403c00504100020140920225540c1e8020400c0e8450440c05840c0106090303010034451710480800d0f40d030500c503d2407002404007a0281034004115a11604480240c40c000d050303c001d500b0050560f190301d00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 991775368 1250 991774118 991774139
    0x21003180f050105011d090a0b19050a0506120f03160804031401021b0118030e031501090518192603042d0c09110405092d06090f0402041b050304050106 67
    0x87e24500d031a940306252850014a54480095001d01e080c0510170081300e06403841010345030b04881401c3c0e904e030360300c1c1008060701d400e0304149500c0319900020100c215009080c0c2d903892194400ca54003881c070301c00c00d40c4100308100d411900555841040012880e20401e00b548c082d400101141c0354181129040c03421480052040e550300d10800708000940305101d49060315241403140d81d56415004a00702d00f08061748180800d4000e101c50f01002403503190003030b45d0740b807800c4a010280649410046242e400e40604c4040300003808c1e00a281070101d680c0310020080110f00d241100b0080c110040100300a110f0082010a10800341440215003008007550024405560f041e000b0011413101506000910301c640c415100d851445201900d400d490300005040000111210044c102503058810340d0b02c1c004080d00d407005e402c48401707603000303080a0300006d8801100500f6000000e0300c141c0001c096596641010f4034220106000300350a0282aa0051050340200d80070380e00f941c20100006840c0030070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 991776618 1250 991775368 991775371
    0x120421081210060c02180601050c03210a230901090c08101a0109030b06040207020a0e0415020906040b0903161712040e13210302180d021003180f050105011d 69
    0x1c002d0341b1240070322505540748001c040d1196040200070700030306100b01c000300000c080140021f0130030a080992a03d202c601c03030000400c00780402d4102180905405242100c0302014685108d07550760550310040e1742401042680000740045d195440005011040032a01040e0403401c5401813111603172864060101003504502c0a0000c1e43c0c483c004c0020414a6030050341100c8010005450407106400107901c1d01065004401200a110244400c120103100791801c2c10718405030960400d201000040e94902444c86490160b5500140c406000d50b02409400d54000e8090b070500d020507150000401c40d410455a034945c20303c14031075064005c1d030407030342a901200c01c065075880da03503076032030365903920120b40240b0840c1c01c81032a0100d0801030b0401d102c1c1100c180000d035070043e103425580c081000a07034050914030f13015050511400000d41c6600f00c024819074082d0a01041c440405401c103041080c0340352002d010b1105c2a0300e038404010041d00458100e070360aa05d4803c5411401e010000344860 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 991777868 1250 991776618 991776623
    0x7080f16080c130b18101d1011120901031104080706231602090f04030807200a050c01142d09030d0201060801050108120421081210060c 60
    0x35050001407026440c10018414103078000e50703890f0b0840d50340c042521160000d0192414250f0001000119414110a55118010545401d0f4461281c000e8045030201035100258000d0700c1550074141917600840001118007030950803940705101d5070350542c0320303a00078002c81c5001034100074002c503c1c3c10840c410303601075502e520064002c0c2c1c0e140590903581c040c0e14400d0b001c0ca0866103841403441210520142100b207802241203043c1e64020300c10050300704801000c81002d151450180004039510203c881d6001c22541040c425086c5c55450641c5035019200e01c00c0f040c0c0c45251550010010f0100c2e00c00c403000000e032103a0414426140c882e0a007409232841d00000b040d48070000ca504540400000f0740543c108060291500070f00c14042414807441d6510a001350791a16020000100d00340325460040000350007600c0514880f50040ca503511561240d1114a801614075108000014102c07040a40c2c1c8200340716952045200a50308107041180c808074170b200c0c941f0300007503414003407000c8581459 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 991779118 1250 991777868 991777877
    0x31e020714030a08090d051204080d1e0e09150d1113020f180d06050406200406020d0305060411130e070915030903200304080705040209030c09070c050607080f16 71
    0x140d4503001c1c000071b4910000141c0d801c1c483c6603105001060400001c5c405040080080c1c810381c0c0108501611903d541030003440a080311840e1011855401415601c15490403920144e140d00c8198100200d0141000c40d0742c0d000450399220000c0159001c48030410f800d06461803132844120b109240101d0040d065400a03003131003000b6008007010f802042c0f04601c40d00070040341e102d00c0c0c642c0342e8000b00d920465044422680e03424038080d80200d440580c0f00e2003134246c0a000c0c0780900b031190094803185910030300402e0549940100d0483d036599005195000c401c03050181e25051036001003c8025030903c5081c10103481140441c1c0b00303501c0303240a4025254180060700c03012054070b404a0040420304405d60800200e000c00b845040072013414a0507035036501000350340b224142503140342003c10590055218a02c100060109900d01040785401d101c030840f5000d50b40c0d9500c2c2002d8a0301403560000070260b004d1075041021082e000030003540580c0440c0c0e00ca03a20b550f10a09000b0300c2c00c455101c0704003c00c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 991780368 1250 991779118 991779127
    0x91e0201080609040c0e0c070201020f0c0f010e13050a1d07050a12051f0c022503020409080c060406050103111909050a060b0f0c010b010c1e031e020714030a08 70
    0xa00b0f040aa06401610501003124020b40e40e004217610b545d0199070b09080d541c40096000c0030b560781006100d85107a4800d0280140594030030018001000c01c032107281c1402280e9910045544d14003080d00c4c0f10501110b011310062424400e804010006140701c0c08604402d4681e0602407407001940a06448002d001d01d00c8050512500820904030382c04222290b102c2c0602400d0384c8581040e03101e03040c513050345011072440d41d0140040d08006400b2b175605070f14074000400141100c5540000b804583d01504d00240d08903007070a140c1494400d04512624520400c8103020800000c0d0703000c14102c0380a20958104c41083c507041080340c5034040400744420b440e0760400e202c43e2280303030b000d030340c10014807440066259030302c1100002d5038214030120038040308003290f080e60895080c003400c1e00d10030003440c08400b041310664940550140301d680328407010400300782d1441014010340c0710600340e82c6500302d4002100380f203207002543c96000c0d010b481115046102460168200019040d0f40154840c9605080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 991781618 1250 991780368 991780381
    0x9081b21030906090604090e060a0c05130314011104030b040b0a02031320034c022a03090a1a0a0305150d1a090c090105041d0709091e020108 62
    0x482c1c101d030f1181175000904201c0000e10b90100d00c54140b031003078a0401750045142c505000c00c00c9620f5221a84180b000c00c020340c1141309100786640042e2544a42c405c007111502481e082e00408029120b0204c440d0001804000e006615646a10035803041d200c40a8075a92030f10501c09900041d121389418200200003c8001003030460760b216062181e8106500c0d4506503c00249800c1c01c102201d0180c0041c00f9442c80380c0e9032281100581301c0c5810070401021000d07017800d01c604401d155142c10440d5404a551030000da01d40c102c2102e00243c0c0c94030b080103255884459500c135400b002c81284030b40030b001000200155160703003019051965180003410300e41c01203c1503001e410b0007080ccc50000b030b005075a000207540e01e6801405d500b5014209a00c4000841d0080d510641d001a081903044c0c1d20584100071107030307510803c503819035100b40c1d404941d030030541901c9248424503100f400454012000080f4100000d9800502d03001d018010312610021800c0740710a03280303007040001c1d0000d0001070000b1f40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 991782868 1250 991781618 991781629
    0x705220f0608060d021509040e071a0c0c1f0206103f060509060f1320100f02210a03180515070906080f010e060109081b210309 56
    0x2d01c0318029003c4d98405035154005076030060915081e41d0380710008150701c007550515200f896a2000008001c00005007011800342004440e10b110104440000680b036401e0b060600c010610540090011103031079041e00341c2c803421008166603007401485181c0014540c07501c00410302d13040b104030b1a00c0d800b0b001074505c2107203001424200c81540021250401004610000c01c0c513052580c025200001d06040c00d90f58030381801000350810500141c003005001e00e80b05020603075041154080340c4640760014690103041d4100d41e100200f50b000f240200859170b0280c00003020b400d4820243d080d03c00c0c0c02207c08500d4400d40c41e118ae900308a49090001e0904180a40e01c030700349013001c03010115020501e076900c05185c00e0310342600c0e8410020180a2000c0303143c111091070040d201c1e505001019141001c841c900380039051040700c0102200344080381e40c81c1d001c0c9885201900180c0c0c06e032001c004804450f645a0004803c21900031244401203060710300724404150429400c0304085c51800441c2c104002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 991784118 1250 991782868 991782871
    0xb0919060b03250e0105010503070e09060d0b09010615180504091b08030901080a05060108040f23421906090f0516021207050111030705220f0608 64
    0xd81510074980701c0615804240ba200c0c160b400c039441a5107000741000c613130784000350060340000c4c1444800d20a01010f030f50814800e140482c0145c6207d042035644100050205004210142511345030300284240200706420503c2a1044403040783c0c500840c2c480111604480c0841c3e6912048007034000b0f1007070380340c1500402a01e078000d400d4800851004080138181a416901491155200160300c0c111560404d0704143d000300b09010400441c505100042c1058200500c028504420504260b0070070440c10b0955903003984000841c80d15030711244802e80c0d142d03903074004081440b800c003003100460250002c094540d2800b580da5400c0640708008152a40b40024181140301c20f04441442d50000462081c0c0000f012141d00104403140300c1c00700d4030f00300e1740050088541c1c40c2100c00c080e4440d50300007e1503030880800c25469236444000d420554010013203803c5c0b94003150000001d0100c0c1c19030200c05042494014642003180c8003041d16900c00285041c8078000b07a401c440301c0100300f168092030049 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 991785368 1250 991784118 991784141
    0x18050409060b091807060309020604140102120a05042d181b12050f093d0504140304030c090e01020d05392b050103050a0b091906 57
    0x802c00380c0d0100c0c00211490021110035000b00d41c002e4a021040c1d10402020008100307904081005c5201c0d600441d40900c0f031801451100e14299200300e5603a4420011119011180014107896410030103008100d40d202d031140091078141e0440790804401c9200000c2c0011080b0384a2010300c40c64516040000c840b03080011051607176403180e40660662500c4030351801c015561382d4000491045030709204032000505680d04414092003040f200310800501720703042100107001a0b081111b5241074110b590740c4102c84802d4489038400306400176516401030b502442c40f81540010030488824110703902c0c010b500c0b0240c4040820b100070016442e803940003140c02140d00002526040c03c411018050300c40680d04030101070204800c800ca020040351000c004030740348120b0404502450350000c021401030074242e050154040300050141c0e041ca2070340f011007405a4506000560356401c1c00c0341c80e5030801c407045d64410801c4000031648c0c84003090030480c1500a1322003d20b0740c0455100c00c0010910002035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 991786618 1250 991785368 991785371
    0x120705030c011119060c1106040201094407051804060b06040504020703091503060f0509060d05060c030601021e1e16180614060d05060a030807030518011805040906 72
    0xc814949202404800303078a409405d02003220058a80d0040c045604011080703134039002a424400140e9000c070060086503011001c0f0451080c1d03080c08421844681001d00a101014410210b0040f0000c00d0001e0f1200044c4240c50003280c0d43d0042c03001072007589282e511001061000100000c06a9100c0ca1039504003500d01820182c9980c0464100c2e070000b80c0030b802061100340304004c2c0541c0f500c008000642e40d4501806076a1906940300541201c50142e6817003103105c00f0004005848140c07038403240c20f41050803100e42e07080803111060264030a40d2183d00600800144a83c812980c044d00702149040d94000c0c4034900f5000070766012103440407961a6540a800d281800c24a001080c42019020700400c00050800b80e1301150101d401550001c403c11110440443c155514002641d00541d0034980110350307a56110001040007105400080c0000f4020413220145a4400090040303040950364055071070b111000191038108410f0041500800110020301c45820590010000355214880 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 991787868 1250 991786618 991786633
    0xf06110c0a031e0507210c0b0f0403030e060c1906151d0702120d1e06030809010c050106030203070902040e0a0b030d03020a02150f100902120c070213090c05120705030c0111 76
    0x281400304d04040d40450300202c5440c51024000c0d80300c580001400e16241c1a03242c044140c01ea02725034003441c4800b9013070151840b4000c120740c8070801120500c191140944000c0101d05039121450182c1010a684c11854810710309441c0c0f009003c00400e0f1041e012404203948a000034501a4640091100c41140142840700304048041805030402d03148002010070110a080110f5440341407400c0052070030741c01c00c2d804001140802c01120508030081c40c0001407503045041180c0500b103140c0c402034151203880c030300140f059456070280056a8580d60030101580314508980b080d200090b101c1340d0306403c007050a6032518020b500030220221140180c07040c2849a003841078400b5401c6602031000000e0804009030100c0e54102038019000045085007806200b130044001d026004004043d41d84d40024100250f40c1d4007510108200f0190906111582880c6040f8001c00c286201d03281c040c0004000214100380c01203601801d445024008210000410004550112a08a44400c180900348 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 991789118 1250 991787868 991787879
    0x80c0408070b0a0c233702030f03030703060f090b10053f0f0f070c0218090d02071205210c060115120c05030f0703060f06110c0a031e0507 61
    0x240410a040040070044917040348580b10039040010f100a180b525002942e040046440900c0688420800003072021480c2c403078902c01b0a1924040e401682aa88808000c00002c6941608003609440c00403a40b01c0c100c1e550703040850141c83c0c1402c6c0c04d9034441c0f008503c52180511942c041d1103100001000d40c2c070078100307013800030301c545c2883e45011040c072000340f8503c42100300754112150001c02c414400c00451600a006d00440c032406414141000704190700c4006550b5109403101d00710304032581e140400c1c05e00078005541c440f4a03079100740243c00341f69800591800384400102d401c40e000320291441032484596084d200380004041c60484d1380070300401c5808131040050901070001181c40c030100c54040d50300504424040408032003021308000800000550000136130303402034100b0410b81440e40b61078400b94003070844c0350031403103060444a00014190b648017030b03001d12620891041e03918500641c4140b000703012031070001818242c0122046030382c101e800d2018188007401042900c075030381c0c0c581 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 991790368 1250 991789118 991789133
    0x1a090904260d09060506010806060403060509010f0c080610050316050c0a080c070f0b03040804120507241106011a0a1b060605100c0308060402130509070906080c0408070b0a0c 77
    0x8602488980c3c0d68249804c001c194491241c0119090804200605c0d200000032076501c86c40c040206071545034004a8949007094201d020098020401480031b008812001003149104440580c41049151481e481c0c3d580603008480c01762604085040700c0f4100c1d00c409503041c0c0e11041c1c0006581c40303020a00008511520080c1c441c1400200103400b80741d28101e0b14208500d0a9000569112000c20500002440c0b4804840c1101c410540303071010742245060490030308070190f100d510710552805400c048103072100405104640c5c5522031165002d151483c2c0d81c0d03240424010301c5841e140c50b90706019014902e4002c0d18400075540b031300482c0c40844030103141c0e030070000c075004440d1192143e90074081440c14442840d0540010301d0f100038081e2464500506100d409071180b401541c0c00242001da10000906a802515014101d0300d15400d01c10700082031040507209260016511a004c01c021114403030840f0308031610b03040209034030b5043c90356007103042d03000026080900c10416806000545103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 991791618 1250 991790368 991790377
    0xf05070803090a0605090f0d1a04230f0606150d020a030c0923090604020706020c0604060c1d0112021c140108030f0f030c09030f071a09090426 63
    0x301014540310341c440418460024126041309081c0201030184840b0780d1210b82e640000742004640c0800c0d0742180e42409034120f14150006110400c26000f0402440b403501740c064007203004410950b41c0740ca58003441a45441c483c4c1404500b0f5044880414841d2400c41103c00c4070a4030b0031902d5141c580111100301c12a0f208000000c08a42c0301d02c0a03403038040d0007010710001402d28886a81da00c5e0f01007021401070001001c0031070f01c40c5543c0c00101742030762141e505072000c1e02e0340900c0841d40d0303c4541c4a940e650b00c4040320116600350505524402c0c140c0304910b28200d840f030b00752100026200090064407401d0a442c00001c10f40d0f030922940c1c0030340c85501d5014450303180a181c0001e02d42001015418140d00580100c0c100d640100002689454000c4c119281d0380b4042203590b441e92190034511296103d181000c0d03905200720350103a00301c01008640c10342118002d2a100b480c4401d000c0349074540340996140d15902011040005020806010111422101d0752988801703000418114248a801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 991792868 1250 991791618 991791629
    0x1e0d03020601051f3204060c0b0907080a060b03031201120204050115200f0106170105070e0105070b04050c030322080a020a121b14100c020303030a090f0507 69
    0x41e0004000c24101021014003c44902000e1303904400d030040040d222072100d8017020003c8034101320000700003407904401c8011803407222245540301d0740c444005225110071501030f920003503000042642000001018000c84a60354080c09050041d629000000c00e1a8213021384c06010400c064840c80c94500881030282c60904000e08003001c0303900600c81240c2c41604045820301c0d00760021440c241d00a04201290300700701c620031040e6503160f025582803400748419150f49600b820ba0100311015000b001e00b0704881420700801182d030b50714070222920f2001114203408200200a840045449036030300c4c030f900c01c0c040c400f214042d0090b240800d15580c04181c00e407024901842240704954869040d06004210000090864580640018904030351314403400c01e4589803150f1190401c500c60582082d4030000100d000540c5584000034114560381029052003800e100021aa00b90b0007001003141c0660090021400c55684414400c0144182c4c9000d4800742204000f10000443c2045100b0203001c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 991794118 1250 991792868 991792873
    0xc090a0303110c03160b070203070902030a091b061b081612020c0102212a03090406120b0a020c0705060d0209031203010605180d2009130b04021e0d0302 67
    0x440d02c440302d82040c43e540103061282c0c104541e4026840344a42c0c040e0242c072611010142d580070302d0b10000b881d24519030300c4246000c0c00070040080c1007400390722035080706014219580790321210441c1007072481d00d01d02940c0d01103050050542d0056400340b8440e480c8a1244e2545880c029080b11407101d102c01d1500201e540c40d8020f01c2c1e01090550501c00d40c030481e0828002080c064904060342103c00c0c0c100204041402d101180d040c0d25405080856607044940440000d050201100305940302d038041c0c81e02c00e0083d401e00300c002510880b02c14a5040c010380140701c13034104e0744a505449000e584540000c0d8100d00c52124040780d81c1eaa500c002300f26180c2c20103401617a846508040c141000000c030f51402054800b800100071f0640c200d0112203000c0080c0e521090180ca90400090b10101080005400701c00d40c2854100d075186080c150f100b546004407075200c89951800003280081005040003040743c01c10502003801410918042d070541c03504030004000d60240705001c00c4503030070b80300d2040e00182d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 991795368 1250 991794118 991794137
    0x209090109060b060f0d0203070306031217010f0b0901030f06091e0b011e0f03091401090507050301021321021903110612161e181401080c030c090a0303 67
    0x800348500c81030f81c1d0050703854600341000c22910b01c0c124010018600c480e01e40001c001001c891095010030040c5500144981c010019044004e01411404680841404000002103201c51445c9800400c441c018020300e13103480c9030040110050100440041c10a07a280d4101281e0040b8900500c1c080400461303140405c94260400101030314950786145050201c030313180310b50b0040c00c5607100c0441841d543c24145000c3c4801c900c12001014090400343c45520483d80344c011400064000f03600c1079003d4800c55069503203c804040c203d204e0010504401200d0311002c20442c0700f450b180300f160544e40340d1658001c0d111900810100d001c5032401203000f0014032030900400040da20810500d080075281e1600380038440e9151000c0311750180c441010034841010030b5500300e206000c6a036070712042d00b0a08402c040714860203000311240158641e66020b9400f8081040301202d880180044030580d2080300903200c0c19030f90b960070752000e0508a00403200f081540c8460300c51200060045200341d8030721102 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 991796618 1250 991795368 991795373
    0x1f050f0d06110a021b090403080c161208160905010f05040e01081e070501080a0e0c19050a0e0f0c0906040f0305150114090114010c06091a090303070210180209090109 73
    0xc1081074044003140307500124040145e03407500031910b5406030707042c106285503455440908060380615008060010101004c02041200d0803200c42da29266175116007165444042d20707000da0144501d066000144010420000c540c403c1040442c18200384c105176140503101c00d0f01c021075403001d0b000707001c0c24dd012050100318a0381000400481440e030300d0184c202c00c0e003480002000b854029100c6009907446010a9180c00e10034411400403100081c406550306104803909003020f000380c400c01384108480f800000b10080b02c054002e100c2c880c013181e42a07160381c6041802c0c4613500010402034104505020119551000b00c3d081005540110000d0a00c0384086c887d0500e4050141c01210140010070840009601c40d048524152900340c611010402982c40040307907031050000014000504002e8004103110105c0c05640704c1034000d64810201d5592258195aa807109a61100040e48685171120010750b1030340c04211411030602035502c5940721074000600b41c030700942d002290707650f403201003404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 991797868 1250 991796618 991796623
    0x8070b1b0406030b12240702011e0507030b03150114010f0e01031a04020d090605010605130e19020a080f060a0f0501050f0c0a0f0302061f050f0d06110a02 68
    0xe028405962800c491448030342000d01502491180009144c0c50b0b200e0b00d01c4540d50076039040c034240c4c030748011034854261a81c0d25030395494040c88000803980001021030700742032060252010200001a0002200680c0f280c40700042030001c244108160781c404030312044e55000d1003909a40b00c1d182c208140da42d41800010760038510031740c01d80c50500019140066940d5005030324002c0842c0242000604d1032094507855165030382c14801d242d4018400112004e01421540c00f0700c0c900c5020360300400c02603032604004c2e20b076417082c5180403a10440c0782d0010400f41029140e40d6501109106040200d0108012800140e070004803c56000c901035201f006020034402000a40c014030481d036002c407513403070105901b6801c4d40a0040300e04001d00000ea00c2c40340d260311310480d60298054801c0b150711007a24100050741c9081800120b00600510b004a14801041d0344250308195814100203030180c90001003002c800002410b854020200d190804045222442442442c008030ba815564903281e11000a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 991799118 1250 991797868 991797871
    0xc0f0e0102012003190e0d02010f09031425150507020606130b010302070f05010c1202120c07050a0c06021b15041406160309090b0913060b010c0b0408070b 68
    0x30304580c54664050756000400c0074540400b40781c5002d0340ea4030b0b150010030814090450224003c11420401002d65014000a541804943c250300820040200c16582000d44541100190009a01a0303802c40c801d51520028110117540b8068914000040c02c0c240c25004d9140da020385a64012001103c00000b103801090f43c051042d2014210b246031903c0040d0120f82c040e400c07030700c0250307a62105000300d9000380c4c12103100c0c0390001100c3c1070b1421185030003400782192460070000600d0080f51108400d0440c004d0f641c0240190841451710b68801c00d1240e0300c1c0e0861502a00d20340b01d040d1040b400701d004040b100d00030306495400382c0032400903000c851901c001050030941c010038220180704512100302064405071002c040300408544101c40003e55a8064040800504000807041000701600b0142030b80031038140150070b00803030680c202040840340e0b088420880032051600304030005a0795a1286121450504140f80c040b41c0c40c0e22a9072007160119800c132444100004c0301c40034441030150a5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 991800368 1250 991799118 991799147
    0x150902040f0207030210020315090c030702151308090d15060314030703090302120328080601030b06070f021306030804030215030402101407080a0203090a140d030e040b03010c0f 78
    0x42d80f0303100051350003e54131a41c074501030384596070200c042914440144920050b844000b0602c440b14142000c140400354003d8403040094407404141c1c20601c3c8445076014407480a421315a03030140078540701c1d00140d621039091303981d20010420741900019580c0404000c62198408009101740c150b251406c031143c42010301007101da2051102c170000aa0000440c4c1c15282e050301d225560050407403841c1d1460080002c108440400e40c50100301c00119102e800c040e04d0050340d1000e07129100e40c001036088600307a24410790045000c01001011804000140541900c05004039002c0241d03d000c80080362101e810845022000040802c258504041402c40704148015680d14504160f80052400e4146555030b9041c4103001100307506e40c803190f00584880540204006a85a2581c54020b407264400c5190070322a603060030010480200c045142c03282c0c41001b411010741d492641d2401e403441e000c8083d8556005845480d07040c04c5da00e080c068400c19250301e4584540c0300049010107802501c119011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 991801618 1250 991800368 991800371
    0x300e0a05090c1605010608300406080a0c0207050a06030b210a030c0f050334170c03190c02090916090c0c05010e0601061101060f05040b0607150902040f 67
    0x1408000441c0c00c1c11a140164101030b020f020071558981140900401c0e030007041540524442e1501034005a402d4200d00660000c4004030002551b299030618095800741e080003a90030800030310f402026502031002440940100e44c0103603074030b50002d00c468045802810000b42c0300c00070030300e460400c8174034405500410010030703081d1178114071030940c3d400c1c10120180800160020640c00d00000010001035182c2203407c1d29610f002d0a61250754008401041c002c2e200e8200c00c40088018810303550040e05644100002c03125112403100c0549a044008040200e0004120248010000010340910b4035070a460705c1818440714010410580300c0180f104aa075003003103142420003403214a640301915114000000d1100304850100c032101200f00c401000c030340c83c000f15094403900c0020458101c0d170380ba9036003445d14290914000d0907201c1600c9401000781c0003c206012620b000d8010742c22042019141508001684e16914405089401c41e50031680c1d6403001c90003035040c207005080040240510 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 991802868 1250 991801618 991801621
    0xd0302160b0717030717041a0604050601020a121808010e1e06010e040606050d1a0c0901081314160303090e0105100c02030708030d0221040c03300e0a0509 68
    0x16024800b20043c00c103080f15600010015030a0740c0600090304003107000780100710070362520785071021031540712031102e0b24605800c170300007600c619003409070341e201d4001a0b014002c0720b20960f860021180001c0c40e064140001c80002048980c140b0f2031840043c01c002d00081440c80c05148118180303496001e20741c21680c01452405010100050078a0440e40085420882d90b80e903824648014000c81d0441c40d80800c9103210201400600d1815114440380250f000e1004d86801060b1000d611450607110f012614030700c00140640c01c0140038040050003184940030704081581c0050400003c0d6410701190090381d9810b01c00c1c5580499200050002030030001140e5041c03100091065941c96414020080100703400b40c1103460502681004183e000212034032568042d00300300103504600c401400d10303c2d003000000d04900381c12500900564100c4040040242141c86c1d450f003484112203002542e03440002068003039603800011410b03030300041c0d85642c00c64004404001c020102a40300c144a203440b0b00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 991804118 1250 991802868 991802873
    0x30215090a0804030b13080a03020310050603090d080c0904090f1502041413110d0209040f0b01050a050d0608061008100e100209040906150e0f010305120703020a020d0302160b07 78
    0xb0100c0781520340240e04c21401da590141107420042c10510010107422000c29801103442d0103030051400303142544000e044854486051040350301044880345504c1d4012030301801480e00a00000c1e0308514064169840e00c0e0b00b100100d0150b4400e20700c1240c003403507010782c1c4105020300603a00c01ca0000502034154945441c003031000c034160a400781410311a0700f950b907540f124008180c1c045594010001c240d1a242d440c44213200c4025084441c416025a0520742c0d083d01d010f480f8480c18401c074005031110341c113011156000700c4241c1c2000400b03d11540da10f04012825607010003400b4810b1010001300c03440e403410a11404d09000000710940350b62820802c0c100520000810980300c2490070010040c0c8030300303110f000170b0050f0a504001811080c17804407075540300407013540e80e130702036800f440d503004070176100c0d42c1030600e00306801d10016000340c001565482004a6a50060010600a02c1203a00781401a00090741c1424108021800b5900ca020144013104000c50210f00a00d202c0100f9801c1a8864 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 991805368 1250 991804118 991804133
    0x6020607080f01050906061c051504110a030c0512011202010e040c1d0105040e0a051b0a0207030803040206210a050a2f040e010f03033005090c030109030215090a 71
    0x6015551007505c4800c001811500c0d2081914081c078010680c01429240c034160b03d80c014138096901126440400a00c040f0701d003424080c0a900c070340910174852610b2440c800860043c00044180410400c04002c4016840d00700c0c001540688a0450785014040d52440058010000700011500440c200015114401c1c3c01c50708902c0084290310350b200f0a84039110040303949119640050002451034014410602c2055001c2032003984441c000c0d40c0a4580d40301c08607818050041403500591100d0400d0000911500c0590780051002e00654104000d68120321030401c861145034454200c0702042004180e040c1c00b0303076604814400e904100c8000c01e521401b40200c0540e0104107016940c6070514a84040b4008403002001358685600595841328880c043e45246440140c00107550701404110060300720815450706540e00f0481c0d9444400419242c000e040000c00b1070866016141410010740c800b0300408003400d1080d8050120b41034852030000c0ca24502404c6129190b002103d6400020840c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 991806618 1250 991805368 991805371
    0x6030d09140112020c01060e01080f0304030b070e0118030305030f010f050f0415031b080d03020901120e0c031e120306010c080c071e090b220e0a1b06020607080f 71
    0xa2801c15080840e0000c1c81c1c01030b1049030301e40c6070b540d07187c640d0000c2c0d8a2a02c105a0b41070f691440e09803515409941e00a90b524040d40c0005412070100a0220702280e000b03a0b00c520000c007040c1001d071141c030f41a54014410107502c1d881038020400000c100034800440c00501805400f01b00d04204029040c00d000c0791806d044d20901d140280d950383c2c6515034800450411000540d40220700035801d194094075002e04403e00d02c1408094410400020700c1d29019000707880e806c03007069554401800740d80840d000a4032030190b241c0042d010700680000c2588043c013242050f10b001039480c8000e0340c184034603039241c103c00010348402d9040038010b00030030360303800f210605141c0e03080009140c039418816482801c241340c2707911074041d040f445125100c2c2d600c528071400003112195070080144000c0f00042c0010314403c3c500e0102800550300d11400c0b01a0150f0001c01c0c01c1c0d4440040f0f585c1000e26a0b0f0310803950206050942c044204002c08100441e810021207a001c1501e180034603043c100381060040c280700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 991807868 1250 991806618 991806659
    0x50c090f03150a0b120304030302150a1a1309150b01090608040c090905030c100506042a1107170307020910061706011704110102070602210a090f08010506030d09 71
    0x1c8851300039580e6640c2d211914031003030015082c0d0381c0d11940d07031030003940e03a40800c00c424101c002e1000002d40100c0c41c521515841207941410005003100620402c51108940c425017182c80f0740d54040750011a441e8644202c8611500ca00001e280040c01d00151040c0e00315400042041046010003001036402e010600c02c54000d40000f01e8121400e1600c43d04501503100c0a00c2c8501c5010720b88401181107400071070242205407810005001c00c030111340c1c1e040c29800c1900d00c055030300701d44007020944035030001ea9100c4100b1050354407182d1244903402c40c50b800d64040704140e81c0042150750951600404060304802c4442c0b658150914040001d049880d40103100e41085e400d0100091680c0d0140c00007446c5041c580007081918a06850482855203240988a0043c820500042a5280001072114070400b0b404080d004070640c0c0d0301e02500390f60010607400100200d2040003e030b0700a500007202d01500c041000030801c2e18118042c103143c205690000010404410b00402540e9103141d610880c400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 991809118 1250 991807868 991807871
    0x30503221b09060812092101061a07030e01140c0a050a120201180f0204060906180c030506130902180f01030b070224060301061a120f0709060f090801050c090f03150a 73
    0x43d446c5c0003c0c03141f00d00940450002d04050001108004042d8419000c0d120030b544a00b00c142e0f20050245024001e1140080100320720841d028003e6000e61071300603e510078100c0380c42c0b0b88158a030380b96040a104202c01c0f90590300c05242002000340c1c0f4015607400510038402000640c00600f01500204191140038100b42c0600d501c0300c0544d1560342040d0050080e00b00c003403051356980d480255205031031000d003000041c60145203558692290181e2809008010100640f0200c911a01d4000388422042245e00c00740040001c07141c14006420030340704991070101010710f0743c50341c2070003d40350000601040464100d00040c000c1880b0880751607003415a0b52800e40064bc0d01d03d000b184c01410980c1080080460b40c10459031001d03030700703c000c0c02d0300c0080c5800c10060b52a0b4031000203c4040030b0300d403440810160642445014881c0c0c2008801d15910700e44a40f801e940c4000250841c0c0040e0b814540c01c0d000020001098140041c0d0750a02e80015401403a405010910300020f600c80a130600358082e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 991810368 1250 991809118 991809127
    0x2802150a022107050d0c020901210b040b0624070b0a1e1e0203010b030105060721080402041802150d11181008010e04030503221b09060812 61
    0x140708011404000b50a50309110780101c1e800a2902e594100781c20440e04c0303108017a40804d5561044000d1500c440d806016160141d080183d00750807201120b0b4040c10b07410810103900c01150f210300140d80600d000c1c4921a02c90b09002091044445401c00e5620301c4000017440524900a20022114101d4005440507c60f44034845005e0240c88610143c00c08600711100301a51409181e002f4026018103852023401420301800040c140e000910a100c040030003440104842d0400f40001e0803aa0300c244200154441c1048448500355200b071165400104c0003400c21003181058400d400208000000c0d030007616640d0713800101c00b6281c414145250180224024482d5461504404a21005103144c0c9869007100d04500a9181d100f080d990306c40c2c0d5182400340c0c865400345500b141030300c0009024000c560740319203098a0710382c000790141c0115201e10344079201e013003413699901c0400c0344038002c820a540d01c1c00c4c2080d025117070300c0e03000b0304821403501d002000301d0000020030003011020440001c0d01c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 991811618 1250 991810368 991810387
    0x10b040f080615041a040534020c12030702060307080604050112150b03120a080a06090e19030504030218040209070f0509190b040611060a02041a16080c280215 70
    0x210a401c412180c00c51f04040901001410b00c0c1c01d080720090003582003040c1d9031810907180304802030404824000d60450b41418006007490f0301621250705009003181d207808030581c0455035a0740100c502c50f00050480061110b5403415028003401070103804145003051405d600c8000140fa50042a07008141e640c1d03040c1003464a0500803001645104a0300c2c3c1d071101c8080c1c40c050101c9408454000416281101c00300340001c00d44940f44100f07c0300002030481d044205178030240040100300035024020207100c0000140e9907400c0c0e000c44465041d1260710541400c0c414070105020203050842803000c0310043d1b0607880d9000042d40c0321a00c00700c0e80d07612842440c14940c0c0300103007d50004540f0316800070700841e06640103000c200708581040216040c644e14664090120301460044a800344d56100c00085100b066038007402c460041104000900c042c10399866501d5802000076003010b4000506410b681d030180c031455585c000c4940a2444560390a0380042da07446138003040080381a0001c500f040c0c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 991812868 1250 991811618 991811651
    0x507020301141e0603010504030509130b090a060305060906071e0306030516051e06190302090d060b01020d090b0421050d091a0a0206070e030c0405010b040f08061504 73
    0x3440c0070700c0a02c580302801e0104801c40b5400c1120158240700c07128a0119141d800c05101e564403031034140d0b03a40b40c01d2002200800c624150b2040f90034150b10f480d0724070032400d41c0d1451203203406148000030025403207240d45405418024020502481a00404200700100d070304950007031041c241c10841a20300d00c2c4080e10680c002c0030380341c202901902c610129040d54001e00202234007a40c000311055080f0203a86403000f06800c0700e80c000b0503040307042405061100310700e5192120080f43c16007805401c20907400c002c11000b141c1c211064548580b2210340920550b01840912180201d600e004c194150a0001602c844c2c030a03445a0950880c01440e1410303040243c860100c0003070313032000546007040c50842d002410102a405100e4071480340500d0700581d218041c04071000034480c3c0d0083d0030030b5595600185d4070741410b020107d4140c000c1351000c2d06155102e204141c06480300c40700305901c0b581000303444500b41d00150480f40d00d41d8001010b00c0102410402d444001403002c0b03030040380b00307150a80700c1c61 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 991814118 1250 991812868 991812881
    0x60703020a03111626160201200109110604120807030215101508070e0d02010234050402070f150902060f0a1706330c071d070f0507020301 61
    0x104503000429510f22240c0c91130940c02e40c460281d440540c5001c11104c48000071215803101541ca40b004104902a000f500d00d071070120f440c01410b29035800d290a00c00503c83c2010454044116556025800200303d0000009031500d03c050b200141494180b05c25640e00050040000e06402c00200720b03d01007600c20001414040c1078688441000d081070080301d00c050005000301c440010101c00801641407241ca40140f245c5c840f5600c2e01c4800a030754080c02030703c6143700c406034110b000c0e0038400e141c1c0e111580f00340c9405010402c056450040302d840049100900c9803c140ccc44dd0340100810b00110342c0b140020001c00307400285620071540300064000040881c07400094203c8004110817081d550420007800762140c241d182d40d200c400400c200c00790240400c4a9803680036544c00b00340d008020401200141d607080c9000300c00811449243d2080c80c07604416484145c980c1301c0300707051050502c4c001107500105401c0311034078a41c6c02d008401601341d507100416502001000719081c019590309401c0413 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 991815368 1250 991814118 991814141
    0x10e0c0402220308040608010915090515030118031b0209190f060e09101119020c04330f06081e01061d0306040209010e06031018061b02060703020a03 66
    0x20b45002d40d0f2880c1450068209114813030221f20741c400002131705400390203807555040c050031525441c1d42c1042050b10041c0005003510380641840b044040300c2d6203091041d6921000845a0450140080e02e030041200d0961141304201c9150081c010b001a251030720a10340048403022403010f03102001d40a500108400c0ca001000141800d00008940340140150f60040040381c3c141e07496102014101000d0790130f0b03c2a030103544401003225110511000c81d41c1c00c3c1c800d5051041d11100d0b00c541300020281d8650b0003400c4004203000203411710b07490101c40440480d60181c140d54400a00d010300b44031005c0054454a07060046020000320150200000d03501c0b140182d0041d1a4903507101c00008060311026030721b40100a8607090091001d280000e0000e2045074001d10301d0720303580c4c01c1201c007848900003c1d02490305071041c0c0d82028005c40d0180152500803400e24050b001c1403035141846070546d50350100780d00c002020300c2401c20001d640414a1a44450582000359455007406401c80c02002504100c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 991816618 1250 991815368 991815427
    0x41a030c091e161b0f0213090f0b010e090a030203181f021b150403020f180405010c0e01110d0c0c080102040b09041109010f0309060b090103150608010e0c0402 70
    0x100010f07440156010780f60180700d80d80d551142881d13110b0462080520700c602411610050300180700600d40004001040c11146c0c6d0301084280c02e6036600803101c3c502d110300301e41280e030200050188540311404240d1001000f0010441f946640e1006504c078414001214003500c00210242440d4440394891050300b403d45a50a5a513061807100075140c44c40c481d4020541c14003c0d500800920304040c08080c80c0c2c0794916840d1400303140d9402c200700b25000500f295000012a03c0c080201480d8603011171190740a1070000c110943c120500902c501601e15001d0306103c4040f84601b0081c000040782d01010400e800d002c1e1001440d42041070301d0f405a075008242c00e600008010480d142d881000d040407840a41e010320140b4100c0d00081038a010b080001030000e44080748881d05980710307802802d60f450103504e00260b0200290b0206400300300c260801d0780c80540ca0384940c0040d210b28801d0a00821000c40200101e1000d040303019141c0962107030075841a500032030312000070803e01c40000d048926a201 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 991817868 1250 991816618 991816621
    0x1180f0c0b07060f050711070b25030203071a0f0f071101020c0c0901170d0c0303140f010608150a0b0a021603030c02031002030606070624060e041a030c091e 69
    0xd180c00603000695404c0a614180301c0841c01b41b5016a07420b0345610030b500041c08116090030304815440d00102070300301060012a01e070030105180c0c00b52280d0410300035805141c0d104140c0c200110b21007180321000e80d454801204000e004800f25090701c1e0001d050092550301c44c5c8a07040110750719012040342c103013030354400035000087c440c001880c8000c2d048152400501a82d0300c1c03266000d85150034805041c10b4200e80d560302c0e156842740c41d845006a01c6414002a482c0e080302c00522800000c46400144079802c10060152981241069a220b00300d081030f82c403182c45110100344025950b00c42d90100000104000c03202134000d00901262503a19001308405990707030300700101950705101c0144e01a010300c1041c030101c1e01d850b0007140d00c00c4102806842c9000d2160760313401d000b440440e004d112032005080e0300401e0514000521002001c20b540da102d0b070081154200300880d18a04c10309003805035280204203450700c01041000140400700c42c011200e543d4883e61501c40006080481040900c180 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 991819118 1250 991817868 991817873
    0x4150309150c120b0603070c0213051f05030a170a050405040207081b0307030228080d0b0102010b06040e0f0a0b0d03120615050304120912110f0301180f0c0b07 70
    0x20b2000780e01c4401642da040d002e5805000841c1241c6040c0d840310b030040020000241000d0240030b00031582440a041d56820030050035401c0c040b19001d83c1c1c0180401003003282280003000108041028113400c80250440007200d5031226587c1d40003c2c2401c0605401148203200d140c000ca098900410000d40255075400390342ca00f004080d40100d66a007507210079000070780c031030000000036148140e6050b002031170b031351344d00200c58600c1c422030f01c18510313020340407524170030000340103002500301e80c0d855030760100301c0100f00400a429503c10580345401680107100820a0004c00310044da0004c0380c03404200d000c0e485040c07a200c06008002252074011424031400d504041d84032004000c0c5500030301e070401c005500c6100c00380411140180d410001501840400c0210703440d1000f480403243c031410403240035503131440415111300d070070b902c2070f9a0180a10401e600300e082810043d8920401103008011042411032814208ac120311030107000c401006105a0402244000900c0540390041e04240c4502c143d2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 991820368 1250 991819118 991819121
    0x6130b0f0a381605030910020d020c0121050405010207020303070b0106110a0305090609030c03060108032a1c0201021c0621050c04020705070e100f17030415030915 72
    0x100e000c801440750b100c21107803100040c41d030060760030820510b102d2070011070540a440540c3c10b80c206681c0c60104000a00142c1c0e1008140900100560080c1c03040d001548000381c1001000c018442c10f0011000032039101e00803506c00c0b4800380d032015000140c80d0321a81403060081c01001c5000390144400107581041c82408005c21341264096a11900801d004003050744d124030095000901040e018404010580351920213011120409000c0310200023035100001e24259081e80304000c1a000010703641c841140f0400107400d01c107011407141e00300f40903008942d0b540f816510150340d111a0008010b049052007901200c3c51482c04001c50307081035400c18031180042c81c1611581203d030000700d2407220340e42c00c01c141101c42260000080d054450241d01444042d501c06582180c95001d040d501090b26841c41c840d103030103908140b03c100181da04103503050402043e2500701c4001c1c0e41d005070038404440400000c903010340f190aa00d214843c3c1e0a640e00381d001e0682420300400200342240d41941e0322007507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 991821618 1250 991820368 991820399
    0x301062007031109070203071a040816030801210f030f0c0c1e05030c0102060705160b010b0903012307031a030d1812110d0f05030c0a030807050306130b0f0a 69
    0x4803503800b0151617803c0141d03502d204401c1700405408503444c4815a00e40381c543d40903031060148003da4038101c408002a00151212501203001c2100c12005000c0d83c00d590829500d218000ca42c9180021041e803a0090307290300310040201001039464161440d1445518648680b69001c00381c424401c4d2036a00c6100945441da218140403198224002401e00c0c1c00a4a07000405041c5c02a24682d1a1102c00f01c486600c14200001040101c009107000200300700602d900a000c1701c243d080e10b6522440806007958008640e64854400d010300d007010b00380f4002c500680241540c103002403210010303c80210403484d441b174881e525018503614004850b0300580c07511800034154425044d000d4035040041c00a101c00075000e000340d030780700040c88400e0908511a05e0b61724041e400c0c24516905590300e1500e151710440160b107032a00324246041c10076803c00c4242e600120141801421460040080b902d81e0002c2d145070321129880d040d400b00c1944070040351020a0f18050000c4a089480740100b4549424 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 991822868 1250 991821618 991821653
    0xe030318061201091b080106231309060306050a09020a090f230901050702010507050412170301121403030613021e0301081e0106060e061e130303030c0c08030106200703 74
    0x616104104e05e25119070802c03810b840b0103071a0303500c42100e0136050b9604451001c1c015000800204034003501c54401d9020b1400800303007141c01041140c10741c0b421100761a8041e002498441c140882c080041e540d4000003000e590040900161148900c40880042d11308402c91b11070610000000c08090850003941c01d03c2581d00c2c0e8000d003c59156490b00701d0807034a040f280341000500500052186800090300001040c0c015040403651859285140f841c3d0361080c0d004904001d0f0041a1400b04070305c3c840720006595245d0080c0d401c502d001004070300c2c0402044107040c0e91543c000b0309044108511580e10400c214081e10789a00d80d80c4461607107550b0301c10114122006880401303c181410303414005c160982c0c1c0140d5030905c4d486500f0041c001c2d6038005001e041301440e0b0310401410f00c00340c040081c0260205082e100c0903481c0c40d600f40a02141d26000c50341c2c04100440403500040f80c1040112811583c540c50111001080030001d215012200c1c0051101e0b0302444400105220980034088090034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 991824118 1250 991822868 991822901
    0x10611010510050a0b0d09140319030605090613090f121112090d031407050307170a08181509070303020d0203131a3006010e03031806120109 62
    0x22039501d0242c2c4040020700c1141e078000350a107402c0c86010117070030281003589145100424040c11668400490f841c6159a800c803644c004034001c00000d844881c074158528441c00c0c03c002260818000c11a1024010139079070003880d140c082c11010142550090a00c80c1e0011011340100b0038034036008050340f800841d1680004e00500382e002c00340030081201c40700596003070140c0380350080d80c030184109014055002c1e42484014600c50094001b01da0060174014820000b950782d40c810340c50441c1d4140c4286103008000344003030014905462700040020b81041c84900201c82c840d14009496107001c4810b098800700c41c41603000d00154000005d80b84041e04d200ea02a1040d55540510803a80e0b03006590f40c1034959140c000c81005800394031104c00f00074401c0d10071070501e0500310741d8500480f10040e0014041010045149520901c40c0307a01c03094008100b460801820889070000035a68000c404804400d0b601c442040c0c41c1550b0f4840c100c0e0010200064540001c0da514200c0e103004181d141c3d003962900 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 991825368 1250 991824118 991824121
    0x9060c100b01090b0c07050d050309031902150313061a0a1d18060435130509070c03141308030418053105010e0c0a080304030308220b0106110105 64
    0x21394868065070720904a9100810200d49040c0030800c2c001c6031410142c0c3c01d400100207680a6403028000000034500d450040b0007000b0041c414000c15101070440c40c0140700007801405a04040c052201c0c032583d40160740410640319034140c405021654007000c0340e02000450f000900c034140300e00d5641ca0350ba1500d1440c0003555403401a07566160000000c054940c0001c40081e00003455801c1d007084101801d00385040001422000e2141d2401041c2054014140401c040c1d149621252403040070302401d80320100c003820000c4010700600c007194002010b11210000016a8240081c00c1d00c901c446010740074405503640f0385807075489a0040c001c043c9081429039804070242d51500883d405400c00c01c4030301c00c2d0450f100aa005070201e040c184007a003085014031050124200b40161003000d020300000c0d200304602482042030300a03240e44552101d0b0001d000c1000407940207440303da44041401071079924442c40c54004c00d4090030031040141703004980c40000c241c0c0c580c813040700d60700000c500d030080006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 991826618 1250 991825368 991825379
    0x16031109010f0302060c0c030601030f29180f07031a010e071209151407090e06150319150609060c05060a0209041409060f0c03010f0b09060c100b0109 66
    0x4a6409000b21040600035074002c1005050580051040308080c100780e078800311103940040c0c18034100b0707072060f1040c0342c005611a00340250640c41030b00d10344803007030219190b002c01ca43c8200d612034028906106022075003040354501c0d03414060846100600c00a0b280c40300d03144e192041054030402001c3c1c04400320300e400481c5482e5068401030040c0501d84a5400300a00d1800c000007400085c281254101400400310180400030b010700704029820507982002403070118802400c02c44141e00c00034a801c0d10006029031503d4480c04203040d90240742e6030b66602c2e650340440c10440d034186072120702411310307004207001c0d044065907850041e5401c640c2ca400e20706030396407800c9070000d0701d865008d0003d8002201160180156a0082401010103032001c02c4003501c1d00103513600903d0880758840560010030800205050300c2d9051035100041e1101c00d402d550400540d002061014044c1d01608840010042aa9600d8005884840300c40f00308980c0745401444039100a0291207c049010910b00e034404644c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 991827868 1250 991826618 991826629
    0xc0f060405060702061b0f0d0b030d2d0c0b0a0902150403030f090303050a030c090b2b0e0a110a0504060b0a030c020d021902150307080f06040203040f020f0a08160311 73
    0x3401d282050b40542040005d0440174101d074000307101005116a9080301d030300340c1c3e1400d000101040340507444254000080d0cc441c00446070412000401a403030046000c2110b03500116682012500060140070395035400805070300501c0f980304045e5104401c010080c004407031100003082a41d10035a0b8541c41d400c1d07030701c01c151240c54140c00010080b582c244810040700740710760b014100e11001c1d881e00e400328942c1c4006082a550085a030068490906001310f000e41d228808c110f0f0b54900d00103030070403d0b4400d00351a503440b032046d20300061542c002294a221aa91200802d901410004104100c00c03940c900c40c0b141e42d030f406100e030320f00800d040803407032141340d8000701d0201c45101041d00039110241c4407228015150140a40803a40412075840c001d100c00ea02b00081c5100e41c0e003e8549030300a0070720100f01c50f40c8a078010081e40c0300c3c034010810080060092243c0094095043c3c5001000d0080b54001400c0d0711059000b005043c400c4001404180c081c0701080812a4003800d4a1202144900c0a011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 991829118 1250 991827868 991827901
    0x3070506031321050a1e090320190905090c0a06050d020403080a02010903091e06081e040c0f0603060f06141603080406050a1506050c0f06040506070206 67
    0x354415800d20004803001421503010001c1c0c0e1040000310720001c403407002d101180c900040c1101c0050408140b82c0c103100d800c441400b00061111070100f810000710b40b0000c01da50203074080100022026810482c0d10b524003402c40c0c0441800528070504100304640003c3d0703102e142c1c423900b10410f043c880880c5040c01c0106d005954468041c009030660b0742400415607060f4060400d080c0c03516400c1100102003a00300028109444480d0300114280340107007401040c0c51669080900300c01c1401e070300081140c605584039421547c090810720015555035080c0307da944902445008403a44c0b840c1044104114503001e4800d48041896400f4903a480b110114210b41140c090524440600a010b2040314020900480103941c0410801d1130b041012100d200d00c6402c00e00100d001c19021405d0008100060066640c04207070b26400b00308036542010807020f40c41440c41040180f06000441000e040400c2c03100c91385080d509001c40308542400d29282c3d55800382250640014080c49020940d4040b805000c1e2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 991830368 1250 991829118 991829129
    0x30203090d143c0306010c030e030f030c070806011e211e0201021e071e0b070b01151409040c0302040807030f110a06090e0603100c02010c020106050a080a0803220f110307 75
    0x101007820040c5c1c1e05580d8502c8658880ba49486815004042f0080c01c10007420000c5002c0040c3c400329190092123840e0a6041e00030081117811515010b808d0f4680042c007004a4045500b0005548140c0240030454900c400001e41821200c00d101c1e40058410b289001c8154400c1e030841e0300344000c01c242500c0c1c1484944080c1000c1d000f42c0c20405c1403648900c41a5040c0d00d03462090036806903141208001036001d410112b4810507a60010045207a4001380c0e040c035452503091000c200503038510813120300c0c841c00c150948550754690002c60703c035210380e0565001d001e07220206c88001c1d03100e0800c00380c03001022100326074290300010b511035142090120b1500701e5810f40c8803590000e05019068400000c010580c0b6058070803410341c41e0200c00c1c0d0303001e212095017aa4000003040301103030b0310003401d5030340342d0b005a0301440b1060300402c1090400120f29130040d8009403125100c0d1264030340135580e02381d001610980f0741103443c012000d120440c80c07074900c45d500c02c0344080543c141c454103040d01c3d9003051050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 991831618 1250 991830368 991830377
    0x9090f07050904050606090405070f090e04020612070c0c0623181e0a060c0201111b10030605040608060708010e010605160204020c2506030203090d143c030601 70
    0x150703818160130107504050000c0001d4140b48050740405c04550041b40c51000060b40c080c860001c0c1a00a210100607000764501d0744850719040d00401c42130703c0758903840c403403021110001446c2d00388140c4601d80c4084d400075581d401141d4a410040007c400c8460254100007101504c3e54420080402c4803031403c03104140128040c0d080c401c11440010b0070024009804042001494030350390070760303540003412540d207400d10b2522490000400118186110f664982d0000302800c0000d981c0290181207054210341c2c1207010008017100b10050105070384051380043c100440071071030350008034544c2d02c514066610b0b0f159980e44da040240d2052020302c9900d012840800a6491650310000420071260028001614080204c8010703444d145214aa6441680c10505c1402ca0f0482454040e8010822450294150704089428035294164903000405100032a203420141009100076540d9012902140e2031003105845074003211a0740340c2c0001c0b10120243d1001c80d00044c3c0c0ca0f0182d0740a0941a901c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 991832868 1250 991831618 991831627
    0x61c12030627090218041a0108032113060617061b090105031e1005130b01021207060914100615081f081b0307171015090603030509090f0705 62
    0x50314004103c0d021050303804c080741d841203074500c009034002a40243c1c480c410713510414800036010600c101068200787c02e250800c120300b03203007002c0c600120760484003440c9a8400c1d5865000310080c09003642c05000b07001d035081c03240000300b1204000c240c00c2003030320020584601c1c0d030f915800344500c40c07003101403907958003000d210013503a65100b4800b441e4407180d41b150380381540608003050550b00008450035050b51404030002e00c028100545000c03010314543c5814440c00715900b0020b51108a1341004005100b408151141800701c15080048280d0708900407181c081c2c41c2c024415199502035140b03030701c400d040c5034001a11002c0c101d42c600c1800c84603520104c0540300c04400d140d20b000180346140b50400c0d4000c0203d0115400c0c000d4074100401e01c2d4409900c030b4a400280341c2400c45a0f0320505030849201c0c4120310001000c0f0f41d29400981c4101d0014410903040116800c0003d103410001c180d601d400008410903030010010a03044000312640300199441c4079a40c82c1382c031030444010340050400e01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 991834118 1250 991832868 991832939
    0xd1e060e01030c0b0a09050411130501050306030304030f11180f06011e08040302120c030403111203120405071d0702011a0a17070b0708030117010603030203070b061c120306 76
    0x301520615840386001b076020340e500c00005003525900c590200c41000009421004141c8444450b4010a001e00b029402d41ca80680040d440f4002c0307201c0544440d5515a40d1030810041050740420184c00405036a020171040c0f441c1d0ba514078080b114040c210b4208000704100e98018440555084003520020f0601442088100c3d520400a0700c2202540720340107400416210200150000212841c011501c80340ba40c100000c055410003d224040e60f081c0b07860481814010003101c40b008038502c6a0603054840b45001490a4107503400307070580c0a041d0a0007030b070780c0c810580024040c00c540d50003445020380010020030603601440c5102d40c44004c0b070740d00300000400035580b81c90f0845100142c600690352030801c0c1101d0360094000b01d803450700010040c04030038032000842c0e95002c0c129008002103815981d01a40c0c9109d00500a80f034111480d000032681c0c1d50f407038102c01d4004820b200c1c081310071000c6c1c5404105503a0b01941d80f00400c0c140781d4082140c001e1001c04002000030360b40d60200f848401c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 991835368 1250 991834118 991834139
    0x60e0a0302040e0a170d0609020c030403060207080f0a050316030e06042604080a1e0f0f02061c09060605010c0201090e09070506071a07031802040e030d1e060e01030c 73
    0x6040a26a401890302510205e049010801000400301c1c141035500d190510004c000c803071203500b00c40125407050110002107400041524103683e0320103001603489840b818040341da40104400b04084850001d801007400742c0c08806180140107842e444c8800004c003290550075524010f1686901c0d40c0160002800f10780700c2d92010302d0980e400c02c11000c411551034174204003603000f904484400c0e40144083c83c1040742c03801b03207090310142080000d40c2040240d520703164501420fa01c0640040c400c0300c6c5990556031f0b6082280c1048240840c4203652404004148016003441041a540070f4500100000d40d5402120740191003a416960b01c40700d5400c015282061002c00f407c1c0090313a00c5103000201d959203541004048180c0581d048202c103c0507410340119480300202120201410b00c2134030652002c6c042003182509904075404228100b03580001c500e98002d050100002504006108007800e002c000301422107076102c0d00a00c03c150301c1301500f40359600c0030b100041652840b01000c00071054103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 991836618 1250 991835368 991835381
    0x40f0609060b0d050a05070806011512021b010f0e011109090a0902100503043f0c02040c030629070b130c06030e010c030c0504090b0301020d06080c0a060e0a030204 72
    0x41d400090b41e41d60001c080b4a11140c00c103811101940400c1140e805d1000400480340180003090081c2000e40c140f6514141e010b546124031400d1200c220305072a044d4040350140c503d211412031103250352208ac1c0741100d000e003203040190a00c2d90b2400e035040205e0041030184e000d8561488810310318100300c10007032002a84009040c8444a540c498945c40181c1c2c6842c2c0c0c48504404075916191203040504050042c030000d05480d45110441110038001105201001c1c150840c210011081c25048010140d807615180140254010315000301800f0141c1c255111900351000701da40c820388401185000444401c8141540c0320030720007400900009520343d07003a6a482030400c50b04103002c0745075035241c0c6000401c075001400826156060300c0102402482130b4040200189806d01c020100101c01805a01c0ba0f07002c3c203428140c841d50020300e55103007501200c940f20074400080004030780d0340c03c0c2d16440d886130312906482800340100000707646110b80c0003269055401040005200d24643c01c21008150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 991837868 1250 991836618 991836623
    0x8042306030705090d0f0f02130606141c05010609090c031404020f0607060c1d04050417030c120a0b0a0b0f03010e041a07020d0e030a05071e08101a09040f0609 70
    0x3038292003800003000c080c001b1140d180f284209201d000c0e032510401414910006628403100c1c50842d04100640d40400e2010301d804901c4041c1d6070ba40c0c2c80705515803c145007105000219801d040001542e41d07070040000003100c40b152010819064850411010b580c8605000348151036402d0218003d40b0300810038880f09080201078500c2c10b466941d4034010b0751144081c3d0404241c000c80703100c0c00403802140b298a000f0f0308480c00c0015103070644d20411114100041902c41c441c020002949000d4004100c07403c031905010039030460b01d81410110702800c0042c502da801740c80c50180004075088400c040c0d807004001c20071101d0840c0c1c28081080640c000080c0107590f8454960007080030302001310215400703038a071a40902101c0501c0c1c200a8051090184241d020358050024040800c4010400c10160782e08485040310482d01e035952815407410070381090440c3d005510f40d044107400150701490314519034480e003a9640e4900f40c100904544200ca01800317506400e04002e0000e01e09510582c40b151 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 991839118 1250 991837868 991837879
    0x8030f0313051501030b060916030905011512022b080702010207030606090f0e06070c152d0f0b06070b041b0f03032c1207030803040804230603070509 66
    0x9960b114545018101d0744060446203250005105120703a680185501c075005545020789030410001095101d14201e0b80c040405503205000c0c01000800e40210041821240c40046020b0301c0b009580c6581c0502e0038200d00c90900600101c48004521000b84480650300340c003402184150381340c040481e400008100c0c11406440c00100005182d071040c01c0c050506110006154520307404084101c4210181b9500c00c0d5000c401044940e0381e009029200355541703c803440890301d1911940700003501004507809003440d541c0c01e501d255010200c0c0803a203c850124401d01201c4246481442102c50081909801120400034100800c0d141540c10750024400c3c40b200e81034804416152282810135000464628012071013001410380c0100721403145101d0b201c0c1e008200004030070030070741d1400100c1c507130780201041360201649100c24002c01380150340040ba43e6913a450f007450031005036401400341101555120401d00d66400f22000110405c0c0700c081c11142c80e50700c60113000c1c0c0d51a00407400903035105 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 991840368 1250 991839118 991839151
    0x3020105130f090b1009051e030312010e04300507110a09061802121b040308071104050f090604030e0f0415031a04110402030a0b1801081608030f03 65
    0x240c00d401c0804000c2c03443c07a00c0050000f9107001001106010380110004110b0210001e02090395081212488034402501113801280040d02103803c6001e00030b015119266440000221240d07030f260558481c503c9002c58a1500012086030f01c00450314040302064248402c18480403940140000c01550b0b01500711001d160302404005260070800da0130500030140c50f140300f00142d21206048814002c2d00d10340641c10112030b143d04180700b0100401500d40218160306a941a203840801c4402640e000f00c401942d400d014100051008655221680141d2078000003030903600d0b00307038601405030f00440301602c26038072180ca0403192800e4a05000b0791005030005001031a80c0c030f510880d060314658880c010f060a00c0c500300306954506144600f520021610204000078150703004500d01401c1c219001600e81c5c4410390090f000340748030702d01240c000400d540f0940030b01e50403003c0641258601011108103405843d60302d07032042c01611074500154003e200800005146d00051648000d001e400c002c6071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 991841618 1250 991840368 991840379
    0x1805030409090f14070801060b04210c0503070905010f09091e02030111120f0a020c031b030d110d050603010b060d1d030a0512060f06070807020406051909240302010513 74
    0x1320940802440c0558011001040110400e0084100820703182c0710b00c50400e40307042c0d4100107818207861410022507600100c1c4080241c0716044a010300005000c03100803a84500007840184030038010780c000403218000c001202102d0380a1052880c0d44484d25045c80e070381044040d80c4034181c3d000304aa140d5211304482503954007580251216403050001440642400300ca9102e21700400340c140100980100704030001e003140002241c4d0304c04042003640d1407030704030550300074114051300d01c0ca03080d42d0381410f0103c580402d01002503c8030b00d6100d41c0400c115201c0c40c0415080311b41d10f10b08035810150038401c500b08510039a1081c0d0525241c0c456250b882407054440505540c890a03440000c2180851086020290084807550112050b01c2c8a603103a0388010000b50b481c016114004c040490016021003152030b41d400005c010840038203100c5954600c0c51580c1d00790007150080d014424a400314121000c0313083c81e00e54072151150a90010707d24250340045a255009840501d44280c2241c1700184 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 991842868 1250 991841618 991841633
    0x20903010f05070210050a0e120a020f010207030e2d10030209190e0708060603040b07051603030606170103020f121203040b15030d08013b06041805030409090f 70
    0x100d404107134050f2a00d80c0b80480c0d800101d4102610300040a4944402e1410082000890a01722480a80c407540c4410655400300c2c90004043c08a08683d400402d190f01016040241500c140c030b0100e50032400c0c2204500301c0ac50104240911a4007845030040d00801402c0c08601c03204642c0b040d29015103444170540109008e00250103005015180f100005c00101c030050b4540c9070040c22526094141c1e0900800240c041d0001070000f03410301401e40041002e203406081103400d28450a0b0fa0700700d08010500f009001031465102c1c400c00706444128112084041c10003a82c1aa44e000f012070645440040c10700181440e061480100c91168200b840e0065194001642c070503445000c880045150450f402140401c60b446154042e500418100b03d1503034200d103101341580ca00d000b1115659103244003100c5030818080030300445000300e100407280d02040400e424441c0c8001d03907080c0f00006945c20b80c480032152959000e0156041440705202d560031540054501c1c60140782c4142c041c10f925120200e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 991844118 1250 991842868 991842871
    0x312090415120c0e040f230d0314070306030c0b03101a210403020c010c021302071104060f030b0403030c0e1201020702030d02030412030818070602030406020f01060612020903010f05 80
    0xa502c1c000c8104200c040000c00001c4801030000d40016030b0080c149a5240c0d50214020000213200143c290285848051045000d44040b101c4000710350710b003031800101400425100301500d052202c40c00028851034000d006140c1183c0c0c2c0104900169890611646090b41002d8501c04070444040e50000c0c02d000302c00c01900c00e4640841c00d66a9582c02116201c940755040407002036015500310402c03002c03a801080c45d1545420030300300400b51917100c0c8000b400180c0440c410412003032021500205015994180c020069400da0342040300fa40c455880104000d050710000308030304084400600081d200343c12030300da5030314942000c411004140001848040d01d01c004010136079400b0810609510f42001452840c281900223589010b092407210301800156502c0030302840035480100b100c0306c0701051052444130410742651070035502c450009480b035202e4402c1d0001440744103c2a0000c0034103104240440d42141c0b241b07600c0300c2e5990894000384d00a9690316070701d5503076803c0500c4000305c64002d1a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 991845368 1250 991844118 991844129
    0x3070e1f060518010305060906040203090f1903080c121605071523010509060607140f0d0f021506090402041b0302030601140705070e040503070f080406080705090312090415 76
    0x15243e03410000c0b4211844200c210450416040c1000e0005a4849648a40c0c10650a40f809a0369a440305181d42c035104407400d445589200c2c003c0381d02100d840305003540c1c000c0d902c41d80c1c03071240039114072035000024010007050b400d40100c5e4034046000c5141207418500300146509010342403100c0c540f192140e906501000b40752864a8001c2c5c00c0c061b000c1416104642817511482003082d50500c00407130507054004003114040c0d01c0011700c46c1c042c410640c20f0104809540c0d0102c03441c0c00175081c030864603000b40600420204040081e00590280003142ca550b02d075a480030500b0155a83e41c007040540c10002e0030a0307800c603559140002c034003206c2810101e803502007034a002d13980b4245040010014074082041c14011402031140e840000d074085004011100c4d0082011450303201ca0a00728258071510390000c1c540814104580d0800100c81c010700104c07244d0361213220720303651052000c0c1c55030300c1a00300b415450f800170120080c2211048018000c894405000012203588ca19000c030540d58058111 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 991846618 1250 991845368 991845377
    0x50108010b0a2712060c0206130611090901080f011b05180d06142a030411060c060702070503010b04060501021509071707090c0f08072a0f030e0306010503070e1f06 72
    0x1a181171100c40d0150351117044c85440105450700d03000c004818480003444000340760740d17210401120002e070440d0075034185000003046000d0342d503035520341c0b00e81e1543d10303079030115407035090441c05c42c4004100b0a005110080f9912481e240100305440130070103180e0800340540c0304914000d0003000c5007580c4038160545000d04031420b514107124203803400d00d40c860b122074000f09408240025000070203005994100341c0c0705640b80080d071203000018816016400300e6208600c9440c081140055000400c0300882d80700b50000c1150414003070030f1100790786a500a0b10b016a010310120000700034018171203644140b030b03070003500c0e85151034054a00c4100d8010100e02c849030300007002400460b131640324181c401c45650421040e00811824050403010000702500c080c4003807001c0b9052103c238842c00071100f181196240031420a40c902e0a524006042207050740001c01e1a02d0000f8541400514281030782c1c2c00400078026103141540a0b00107400003014401c06400050300000c066116103040b4018062a458 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 991847868 1250 991846618 991846649
    0x2401091802090f0f01021b03030f160c0905040206190c0b0703091505010f0e181f050f060915060c070b0a11120d0902011b1506050108010b0a27 63
    0x1080780407201034850b141300b00f00031101450f05a80016111602e0720303600c000310f60242c49450001c0e0641c0030352602da601d01000090184520407800b6209900c0074450524181c915032100450340440e241103600a410550030408450a90750980e0300b020075224610f480500e107640342d555440c80003011303200c0e9004a034641056500700b00040841800000c01010204455032409060060503212441441d920002050104000d00d0410005c0f002d043d640000311041103080340300e00740764090404000010b242c601000f19101240c3c6d41246805400014880700c071903200c621300c1c12065020710000c0340c1d0040040113802a542018840203008161110065803600803a243c0501800c0f400b580d40081904000001101040034400b0380b485140c4880c0c0010700814584010707240d00914040340c650b16030828005404010b03c004159809084c082c10a02c0361a9940d001522034107800c0c0240a0a290180b01c030b1609184211000b0180c0d10100d40501240c00c2280d501000c000c006800c64030b076503861880c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 991849118 1250 991847868 991847887
    0x1507021506241b0c13110403080703120f0903021c0e030f0303060f03030703082206140106091a0306120106240e121906060510020f070801052401091802 67
    0x303040021400d45003000c4e200740d14401000a07a00c0c1e11300100c045a20f9925070744003218606d010b06880107194040c00860781c5007800d04028040700308000070300c5403550800c42c00c203030005401d006d81c07110141d00d9001042c00d000c1c10004095240c42008180b41004406210035079155010801e01112040d000d000e540c0d82d0030300c2c0c0c06122903510158880d0703019a00c10401d02001940c8520f1155000c0c01a2500d28000c034071040880645a540b00c0d07002d002d090818148049030307400090024103e542c0b50f2a58018607550b0030392400135445000007001541340034400901d030360402016008040714050000070b446a26540400031036400301c8500c061061040c15030746041e07a0819020b80381210200d500403100042d008003680e841030b42e051808891180700d8440301c10480f040d00030a014080080501000c42c0700c3c4d405c029509c2d615014518a07030310030000001130045040c420b25000b8003480f0440b03110010005025001010402c04090410407241da0010b141840d819003031868240215015a0b20080803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 991850368 1250 991849118 991849147
    0x3010b040c0e03061f060e01020a0f140f062a04031703010924090c0c0b28050903070320060403091d06090a18050708030c150702150624 60
    0x14039201c1c0c04185c00c034420081c240c4100d000400c8510780c1c07038155901611140104d0500322800c90040540c022146428100504c07125500d82d03001442c01156200841007964669620045e141c522540346903196109030681d0403140c02c50f00d4410a0001860f00d992a9a0707045955104409040c404401000500c110000c0c0d0059051580b1140c1c5501a01030030b941c0102d2001c0183c2c86030a00075942c0355101440d9500a454241c02d441e040350300c0380c0c0c2c2031405509014202980c1d0168505205401b4403c1076000300d107100d06070148410341c000b1400c1038015603003910700c015a0400300b180c00c1041c840529400f00e0400405114611a40e02c1800103031511074001e04002a540a071415015030104015450b22034442d001d91200c5403081c0803d4040c00000303503c441c54101100505240181031011803254000401044501540011a61f0070400f0828010700220b00741c641a00580020140c0020750360700c50ba071681c2210000b130115800b01f100c0c051840c0b249071a0a80034118400110300000c40d040032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 991851618 1250 991850368 991850371
    0x111150a02042d092a03020901030f1b050c0304080607020a030f050c0c150409050c0309070f140d0c1809030305070c0f0b15030d181202011d03010b040c0e0306 70
    0x680003101e1407507801e0408070201c5005014048406a60344145c00000711390b0b0b81085180080b03111040c0d0345421010b00100030f5131040c42c905000c41c0c203081c402c180b9281d642c407a19541b401e08800180e04552010400c4400d1740c4043c0c69504544001d010110302d1290520907107001701d5458000f0090b480c218070700a406480ca560080d010310009000300c03030300c1e1000881c01d03c2c1c070038500b20b410700d040040c1c1401e5651280030720f40003085d803185084101b00d0300070302000c02540509883c10031070301c004d55101101074950000303000e02410702521210f101841d04082e11140d280358410f00c03200b02c500b0345800b9051501024001803045507a2120040000d054140c46155013003101882c021400c914a500d47d0060107090070710052000c00c0040000b486c10751003520b4821b00420003000d03a00000c144420080900203e10f10307800c59848170320300000310600090075003940e6940c1a100e40c06000c2c1c0100c900120280c06003443e54040d501c81c28040d5580d0740d40d128103003556000e62100c0b80310003030510605150050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 991852868 1250 991851618 991851659
    0x11100b18070815120d0e13050601021908040504050c1314101b020415090509030a080c090121090b0121080c0a02060f03160e0109050111150a0204 64
    0x1000300500c050203600c000ca50307500030180360741c414001d20103030082034042c070f8000c004240a000301034070442d036568008920180740d501102c140140aa4007402e01c001c03070707400344c460a0160740964107031410210a02d49140c0f000b402040c0d22130802c1e66900c00308058903812540e40944101c0001c0c4155004401d400103c050184032481a080281c0000402c1d05d000b41c3d400041e0600040341800c0004458179040c1441243d800342c014030110b01800910f203224003540c01441031450034007002842c1000000240c0c0c0d641d00711955071030f1403511031481c10b0aa55025004040c100b02c000c4070940440161090103140c06450410009210340050902c0c1c0b80000341a084814940008081c0c117035030b40c8141c12048492600f200202d5a204420400c19181401c00c0d240250030610214440b800f1400060146125003080c0081200d400540c2c00c08441e0030003038400c010b0109d161903505100e1035100308424104000c0c10000c0301c280181a600200440070102d9600b02c00580000d003c2c00741c80c84101e0343e40c0d019035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 991854118 1250 991852868 991852909
    0x6060305151006120f020d020a090911070204091a0f061c020306010533090109080a2103020d1103091513060b062209051308180111100b 60
    0x8010940c000b028070140700d0401000070950500200f400740d9481030741e1026950b40c00310365500030800c6002c083d4100303000000c0442c0d10a00000390084540c028100a40300404401d03250241d50360800004008440090302c0004003011110540701507141c2013402201507010503030452505004005900c40254405580400014540030041e1400551603054038422a11035104505500035802400081180c481e0850b000c00418141015818002d04000c0400c2ea101c02c130058403241e078aaa1042c0b009401003208485461110b070624500c0044406855580b80243c03412040e01111001c5d10039140d00c40711211800820f00c600c0f8001081000b144e07030241c1c6207a40c0d079807030a000341c00a00000304101508075500c5610790300e8565a460120b0358904242c1c00c05a000c90600b0300c40c030b051002d0b0340c000c0180607490a40420110046140b0501855908c0207600d480c0802e081100c541c0d00c60000036503418044c0e1450312a80c035510a1141c800d20111545001423030354501400c00202c002d003541007a1512 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 991855368 1250 991854118 991854121
    0x80a0f020c060a050c1603051e0313060b01050d0606050d050f0712021e0c1b04020c07031b0f030b160f0903030f0e0604170f0c0307050d17070606030515 67
    0x29070000c02c0250344160071072000107440e40c4da50071040d9107101359814440743d1922040303c40c00705504030703010301806070761400781750540c009010842081d40f01c25607007000e071003c1201c21030002480f00c0e04041080c480615090382824010007445080e140140c000c0c3d0701084000c40c2c60120140144550f9502600e1043c0030303051800c10560142a1408160401000540000b11061710030b10b4482000c00c580105050980d40340d0044130f00ba52a8050f4082c40903a000d541c1c03140503401c1c60719009441d04802c841c4042c0c02468039603a0740100500300740b0b44050300381c4804100000d103000b040150600550085060b110301d032400d0103491118034440d50560052001382685142c609520100d21000c0e6070b41400c18440710400b054098070114100c0e10b0720b9911003030008002c03c8028030341c0c00c00c16488100780d0456610705a200074958071120341c2d5100700d03010783c40408100002c3c54018440c920701809142407001443c807550b0795000a920242e419640d142d2144802c00800008005210740011149508c0400703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 991856618 1250 991855368 991855387
    0x120304020d150b0a0308030a0e01050103030504060f021005090a03020d050a12020702010c0b04051b090c0f1e0a0e130203040f0b15120a020a0f06121e0c080a0f02 71
    0x2040c070408028014034140300b000c602e11440c1c0d922851040301c006040026065803440e1a41722035000322000c01103681480003100300c59805004041c146d90341038076007600702401c1c00b908440e0244a4034401c0300310710510345641500c41140c0315103401070700d850300074014440e21400c001c0e10304401c8143c103000700f001c1000702e0403000d0340c40f80d080001d032000d4950244c3e0751100c900040f1084c00407904050070742c401d0f40d802c2c030041043c00258103001061400b44201c2003c000810495000402c03038070447d81c01c90030440002c00354882c000401904200d00448200141e02058005c0c0f96040140c0398008522902c00c4a8000d25107030000800088a01d9400d41c81c40c5420354600862269141e0011305101c4c0210100d4208200f041048440840103002c60243e0381e0026400e581c0da100450069000e10200c140125010100603a084184e40258035030140c54607401b00c0b680014800d001164441410351700f43c40410f4000d6015000c440003003580d0343e04403410043c80940458403000d500d03ca0441c03040115008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 991857868 1250 991856618 991856629
    0x608010e07030b01030b220f110d180c0b0301030510022104031b0818010e0d030c1113020c07081c2105090304030b0928030909020d06050312030402 65
    0x10700c8580c1d8a03000c10a2401500141d001c1c0100146695000422500c6514561464491504d0075550304005004a00a10010300d003120300041da2044c1a0300b040100380081601500080075404e01004400c1800301151034860b03e901041d04820802ca40c0040100284070042004007030039141c40c0d0382145051400103040d03200c85000144004080d51510005051500580b00180c000c600c03049040c00c904094908448507601004401c1c031200c0004041200c254841d4940003e000006010045140040c0c1c5041d21141540c05046230010b11840ca4a1400c1d2140e80d403001410700811005620b6004002c8000c0c20105030350046045540036140c14174241445401c004070041c91420008000c2400c500221b0a00d107501c100d20304d2090504052101010002000b0811039000711400c480548425000d85c1d202c182c5140101c1c880c000030b0081034404201e02001d0245144282400080503580381c1d0000185e13041004268100380c0d0310340c0108018201404800106c070f0704d0f40001481e500d0b00d64000344 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 991859118 1250 991857868 991857871
    0x20303031e0a1503031107050405091006140d021302190903140f1f02090d050a02030601170d05160f0302010c2706180801050109020301032307052b1b0608010e 70
    0x17030802c0488201407504603000d102d503030050710f0054400c0c0114071b0066183c40d9120018a8585251480c207900040ca442400341502c9250381d0040400c0060b00c402e4081006030006e0300341c5444115400c018440c0920040e181c841d002c8940c0f42c6404a03202e15504010b10151080d190710500780d00301c0c664061600802003803030503e2030002d400e541501c0064401c928001d001c0c41c1040c1e038024901150000c207010001844651051084046802d0344e030321660031001559090303003038080681c03058001da8200d5004d9000360034045d1700074200420844007502c03107100194410f141540941d5440181c2c045c41980b12040794500d001503c64070311940d0340c0384094080c1c040503100360010014079403441c2203944001580d82006201d001300a000d1941c5681c0e041c4025031007840200c9131200a0740070340307140a280365504003005d8044005403405500d00000d000e5208201100c040c40840241c0c0d145602441c981c403030f07040c0c6a00404840d466440000c2588400300a140c01c218140668240100b251401c41d05009 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 991860368 1250 991859118 991859123
    0x90b01090525030605130f1b0509060901050d1e0608011107141c0203190903081e0d0f091b0e130503070803070804020a1a25020303031e0a1503 63
    0x15041d40c00300c49040340203020b280c101c0740d0300c038954000840300c4403107a41148000030a4075000304107e4148101d90401c21140c00348e0103020039001d1010b51490300d00000540010711042c1449072425070540442c1c030840d98420b40041c0c0c002d68203903a10103402514840c04c409031107420000c01c203100c0402c00d00b010390b0048060007880301c0001885a001410180101c070500048292209082c00850b100a5101c0e00b0560035002090001c0710440c02c031600c0341c0359030703812a504120f0705403401d032134a150080e074203000c41104542005c00300103541c007152152003900d1148520f03a50001d41c0c4169494600304071075070310f043c0801003001c07402c2c20f011039818401c0d042d0f0080c500c94104510240f052804900b58011807074041c02140f0080300300a5155000114984036a20854005d10006e454000121200f295081d00d842000c4c018060303a03c01d0f0703581442094196126035481c416000159000078510b9000300c5000c2e40c20f0008140402040c0c541c100d4190b040300020000f03103c0d20851981d40400703a035142c40007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 991861618 1250 991860368 991860421
    0x20c120a0905130e16140102030a080a0515120f0705090105151b0706080702060f0f150a030605040501020717040608070324030b160e031b060d0906090b010905 70
    0xf00d00b0a40b20b03580f0501038083d03068141c82d158409000d00315400d400d14407130840b1340c03440008500c810790b20100494880008545603003106880e221072490040800820020302626204400b40c2c40b41da40340002c040c051780c41c1006260303951004910905001d215403016000700841001804a582d4040707031b40224440140c14242c85810300b0b41c00070207294060300c82502d1801810f00218060398070206071407191000e07400326400307038640c1010500710640c126642c501c1305c00c0c141c0c00325100104001c10405000030041c10b20003050b4507621010215801582c003200c0c070b41c1d4001648402c02c454582c9802c60101d40800541c102440c00b5005015100c0041101d001c2595a0fa0704000080a441004184c5000500300d20a642c0d142e1500703401089082c0c54a01c2a8901440b010360030341d1292440400780d000107400781130071100d030030500b10711030f0800c00010741d00403400d0108642e28811440380141060158201140000042c00c0c01c50003d101078210540c01e03403c0400304002003000040701c85401c0030500d01c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 991862868 1250 991861618 991861639
    0x1204020a0b04031101031409210d0609020c01050c160320030c0a060e0712120221130f0b070f080c0d0e130b09130302010b060d020c120a0905 62
    0x1410380c8a10307040a0688003010502005012040750907040c0b40d0400e880400c19450103164007504654111040c14156000040c08010001d0000000306d440d0400705500c0e041190392014041a03d0041c5c004922490380403c841d041c0382d00c240219900407002200c00c80c5011408208881409255200602440200101c450704400764030b2180f510180d04000fa603480b403204014442e110801c1d06003d0f20194104080035025800c0814648211410002d000414408a03903500c00e103090b11040020540c0140303440e06800c0e10002c01480c0d040404090107903911310003124007001804082d049001200b0000c001840440c40100850f0509130b08841020380182ca02d02e4010541d02c42c11503103140c50b001c0e611107400065003028525048520071200c2c6840d083c880d04031802102c2c0c00c11060350b482600003021401d2800c1980c1c04005840c00382c800800c85004240108500d603003e202810038096000a02c241030300c906102d254920000000d103949800000e4000921012480c01035500c10400c101d03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 991864118 1250 991862868 991862873
    0x80d0510081e160e040506011a120604020c0d170c030708060118050a330507030c03030f05041a0a050702102f0903070b250303091403041701111204 65
    0x320503d41c011003240d401d42d00326141c681e2810030001c00d80781118a40700d0348001007181c03a21340c010601041c0448010500301002c3d002541e0842d600174088540103a4204441301c2c0c440428400d4915290054031199010030108000141d83d40004050001810007882886990340c0e1000392640c01071000d10f0a0700018101444201410010740e004c0f07648084c190b28001514550810030700040107004c0000445000c80e02010514a01c0f50f101003000100100060b10001e400b5005a030391041c0280340010b410118041c203001110310a8405031190760381f22165140281400e201c295021034408002d12a6080246c00a50303070300b03071560000d0740700c075296681d50182c214541c0c0c2c900b00107603045642c484412489880145254045401c140c080e000d00c003c007043c83c07100c890880350400081c1141380500d0188405205645a203500c048040581b500008400b15403540a8081414000e0001e0b583e40d6142c03039542c00d418994501c000350036904081d07030440640c49443c02c2c0c41c0b5400c1c012155440903648c44c0b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 991865368 1250 991864118 991864123
    0x110102162003011d100b0f0103050408040905010f210c0608060315010b0301060e06030c030a09020a05120c010906180b07081606020904050a18240207080d0510081e 72
    0x2030150340d059032030714010100c540141d501090881c2c00d04d0003940e208a5000300e11100750340c0f10207400e40d04000d0106240005510a50066038042d0054083c00e08141d00c0d4003409081d00c80a900c400c1000713544040034812159008a04920084096043c1d8510441507544911041c8248a0f032401d004405001822036107051120824000c0b1601c0b0061081da1200c509840750b40080c00b51400040c0c0302c0d0303401403036420310f141160f0152554240c46421591240342c2d5002500e42d02604a8000043c0540080c158036950241e41180c60401c0282c61009003100004041c115a688101c04102c1e02c4d110040c83c00301201000010346414120403030356009581403150481c45003003160440c50048030340702d000b4801c50780d018148581b0111001d00c4240c450f40b01e0602598400d0900c3c40c4402525040200066840d001e0600f540f148229802034071803245454008a822442041e00d031083e0004140528038028030070306920049240606085a0070100319540c1c8420130410024003064607000d180120b8400c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 991866618 1250 991865368 991865423
    0x7050d06120b2a0d0f060806060415140f0a0e1305010509070608070f030e061f05150f0a1403070c110f150a270611010216 54
    0x2285018410155601485001c0415281007907480114a07000b01d680c1196100d5010342c00a0505088806002d001480c1c01d0702c2e5201d40d5207010380503560588004030b10054054a00282100c20280400d03203028002d01058030014558840400340c1c9000602c01c842c000840580045030680700c201d4440700e03c00211300a0111a08980711a100c2401041040c4c03055107800401203121300000d00c40c07515941c290a540359250300610f40031406040c0024440e034442d1040d01c035541c5442c60049000b20316514005e003480c0c000d981d07141c000380c1013040705141100c0c40200c6500400d02038443c4501c0f0a1400c0504101f801215019600c2c4140042e041c0362040c032900e01061003004401170290b80e8100f120016110071203a4200704c174130095508110001d0f142c50880a1030100c2c014220700c103c0341e00e001443c09035a01202418007030004008003140c641c3c107130b0b12083da0000c2c0d01d0500203c4150500030007400f60140c4000400079a801040041ea40160a000358520700b0f030b10a0540c0f482c80e10710380c80c60084440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 991867868 1250 991866618 991866637
    0x2090402031305240712021b010c090e01050a03030e0d052e0b0901030312020c1b0114040f0e070309050303240a0308121b040612060f080607080705 65
    0x31050110700301c1050303501440903104204035006a100709185403e10303003044000c0101c010101c4d0004040ca13018070f0600301201092100140b40242c1506211460b404401140ca00e070703075545000c4206650005c0d94030015000581c0d42c8080d0350324000c000303580054103001c01003c0101c00304e28006d01da140c0a0000051542c024192401d141d041a41003840c2c04000382041d44500010749668410882c0e07201e8409200d0000d0711704c0c86582e0868030306030303010011100404003c0d80e0801c1002c150000c1409502e010040c260101c043c0c0400c0c02c0300050803024039403501f065014040004000c11080801000304481c09211140f14a5843d61010303070081c555000e01501d02d00001081100442c03c214040340e40341d500d0700c41c2c2580007a8140c140721030316019000003000490f040242c0c421900001101a51100c83c84054440440790040452402d400940c000350128110b406403050958030f600032032000c0c20200020301310b0790346401210360361341d0310207840803040c850560003064000703209000710380c0c2061 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 991869118 1250 991867868 991867871
    0xc0307062c18041104050c0c0a0b0c090307121a060a090b130908070b091b0103020d0e0d09030b1b070f0201020109061e050606072604030c09051f0f18020904 69
    0x40c140c1840c91360703070000c4000075228a1030200061900110481640d600350800402042d08590719030b60030005000140a1008890060040500a5604200420150119541040540c003080c501090034108411981660602120800c55241c50705681c56048400d2104041401c440c16404200d80d0114041c0164507903007051035013002e00c6000d8001f800b5440c070820352611190fa44051032503e904080c410245440010301d0b039082d2640c030980240405080200c00002d46020101c00985000f41e00c150300300c04900341d500c080003440307402c1c5040c40c2d108140b03401e06586810707240c0812055100d2030070024801002c480e0341c5000e59100350702c944203103039110300200f0401e024020b40718910300c40c05100c900b6260400b0009000740c00c048068600c8158090703280070745140c0300600f0100c0780c10501e0f0900400c80c03041c00004081891400040018800683e00082a00303140403100b06a603074003048405031101e054001c0180035090107104040354044841e04004115504005002c0e1242e21040c580c0607 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 991870368 1250 991869118 991869121
    0x60305010213150801050a092a021c080c16080c070b1306051314010c080a0804060b010e01022d03190216120209040807140c0307062c18 60
    0x10120b00e51a8016203801e0b030b0000c1c0c0c040c106200121982c01090041d00e40104004604000c0f5441940141215002c1000c4000d10894a885424619501811400c2c0168400c651070900780011406a203e840c40340e28002026203409945d003107040c030601000440c0b540d00078800105000d2138005443d1040a071106031130300c05030f0714031246148d074000910200402c2d00100000078020f01510489046065100148030400d203446146030f00d50000e004114184942009804006081c410092840440e0707511040031608080c10070030102d5500c17144007810b02086c07030740c10036190b070300060f8806214142030351079030503078064404c41089010045a02c441511001c20a20320f92100903c014882100c640e080761144c108a401d01000c040c1141f00d01000614104204009824500361940e4024010403043d881c00d4515510520740d078200c44100d4401e9000b041c241c410901e014070001004007214a80165484441c021300380050444140881000e680c50441c1004d544506080540c5181803014003c1e05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 991871618 1250 991870368 991870387
    0x120a020609061213021f020c0d063210050f0405070201061d01032d0303091106030903070614061305060307050603070f020d0f081f05090106030f2702060d0603050102 73
    0xb004c83c0044124032070381c15200e04038001c201c1c0000400803000b0039402001020005410300c07034201038201046c4c9000c1c2c2c481c441c06004984500c0d080100169004c1030003200c1080d02d240b40c2c0ba4000141c004032104000103020005c1d59100050284c40040c1101d0004032512010b030f00307900400d015402000039400e1190027001085d881e01c0c080e41202d011b0300e40c000d001594134004040800c2c41450920030800d51390900408a0b203e40d00c1007405078812418030080c0d849110008100b40c0003260b51621075400011080704200080c01440440014108503440d0b604100d4000b03804505150f8005192036501c0001580c555810400f03640186405044540e80c0d04205c0d4004200c600d4a284c4200544144040040c1c6a0310070403c41c1c0c15041e150f554104103884410b452110b005202c90f90f4820800003031000701c2d207541c940b08102d000700100e0710b00040000c04094807801b9110074006040b0792220a2601e281d0075941c01c0c0c0454051a41142c0043c1e5a090712408003008003a9a04041c00300e6101144001c0c0c5d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 991872868 1250 991871618 991871641
    0x70b1314010903030b09220615380f18060f04060809030a0507030806060d0609020306030c0a03120f0c050a030806181509060105090301090b06010e120a0206090612 72
    0xc054003a136804d00040d20900c042c0540103105580c2c0c01c030152249554084d000207290601c07142c847c460440030451050903200c2114405050b0070074201c0c00144001446a44c0034490300c0c0c850035410700703821446200c803682200d84078001c40380000b810040c00a0042c1e00031064045211484000034101b60b201c442c02044901030350024001e850106001e480403c8202200009903081803065689040c6840a50355086942c40c03c0a0704450300407000780003108609190f40900c0d07001d040d10000042c0c0303914014081510f004240c140c914000e60250f082800405c1d81c1c0780f0340c20f48000860a00070303411483d0700c00440d400306031058040c000e4040d0b8102c2c4410194001c9070540201c0c0101c402088401d0f0000394062a44001e0300c281641590a4850040e00c0c00c080065581c4004d05040c4141007002c50b0380801e0a603040ba03201240c41031001410082a5a0806400040360800395925480007400d81c500c80d9480b450b1040291082d9408654015075035100021140380744442141801d4500b092542c460 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 991874118 1250 991872868 991872881
    0xe0c13200903160e090c01020a051002090d0b16020c0406180203040507170609010605010e010509041d0321010902042108040302040c050327430303030b010311070b131401 75
    0x3041703806202580005e80d13100003200044660004042d00485448070030b0030009610115005401c01c00404881e80402d41203541d051240780905001030440301c940703038020f0514a0715981c140c803e5250200a1001800c2d001081120188903a00103980b0784480c1000c0d031070440d03507034001c80388840d43c402144e04285002c030780140541b0b491b4000b80000c1c1c0e1504010750701d41d0300004248d400103005203c03100583c58984c009041c205c8a074040900b605018144580c00c50380f103048060300d2074280c120301c111080c81800303145005140c0c07100c00f141483e091258001000e203c001c040c603901d0b41803041423000c0c0803141e0112002150300500c1080f1034800e0b060082c25507082254608028101001c40c5c6118050f540442d020408060024181581c0c2c00519507224010b812030b50010590b6901c1c1c803d640c252001e0413002c000046181c403006191030341c50000c09503009030603030354100f40c24405d24006281002d001e445069600c40600c2c0402c1e9119101040f800b5082070000e801245e4032001241c40090660020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 991875368 1250 991874118 991874131
    0xf040b04030317040b04290907032d170d060f03060b0406030506070f020307060e0c120d0207050f1315050a1211060309100e0c13200903160e 62
    0x100480e40c0704015411543e6040b04c000d88107001c008001000180d4500c0c00503442c8403607d01d1145040c20540300c0710480b000440320b414040c0d220072018400e0201810f03000400c6607160088013041403001c001042d2410604100905001141c1428502401312030144d03600c10014440401c1650760351011944c0410317081c8010341c0d0045c41d140103440c940c03c3c540100c1c0240e980000042450703032541c001c112542008908103408500051000100080d028066261280c20342030052518009020410001000014140d0180d5104d22008a842500483e900d030445504403007046200f01d014001c5030201c03602c01d4251200034175144000340c4020030a892103050310f030280c8a0458090300d4904440e444480c40703002420740b00400385034401031300d4518000d5038000800b0b0141c90000007414030041c162130300b581543c03d1a40003c490392042d420703d2901c1c0000d484072500180040c030000307448104000420454441c0c5807100007105840398a08110008000b001c82c2015030100784d036a17400440e0444140e800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 991876618 1250 991875368 991875377
    0x150e0a080303070216120c18060504090602040512060708222405070f051801030209100c0302150402282105070f05100503090a0b0c09030705030d0c0212030f040b040303 74
    0x72400110a224512007107900404402d182c7d4104940c50302c45222040507450f000c0d0319000041069120707400789030071592142c140036844a00300010456007507540403440c0c0b038590003030042000f51070384440b405400c1100c1c0203541d609440b1502c0100181806124060041075051070402456100ca00c040c15038001b49a10400c102c1d21071000440d140300c502c0012400064043c8201210040000d040781d800f8001410010b1074500700402042003401c480d42c61001180d8a1400c02d4207140c0c06002c0540152624544c904151906070b00180c445003c1000440503a00c51408140c8510302107500076000c0d08410103038054003108225035582c8004406401c0700e25000c0c0101c00196260000110020350300010501026529665000c40c6c0f2600001e042403103920502c1e24207000309040311916070017410180a166503030079140050501d0000d00d540558080d5000708000c582040e03010748070809040d411964900074504107070226240d40100c0c0952410014006000a00002031300000c2040700d100781c95 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 991877868 1250 991876618 991876663
    0x20010503013021050a140c01090618050c042a110105131104090305040b0a09050a2c160e06040509010b03010320030601030809030f120c010b060301150e0a0803030702 73
    0x1021542da010b06045c032000704420348414164a0070180142c01092030038000024008801c0d1520019194800c1015030440360045141003484001d20800405020a4034284201840c40c20b40c80704040f800540051483d0599041c3c3e43e00034814440c040d070300b4070810000d102c60b00b0b0008481c0744560390403000b01c480e0040c1c80e120140c1403d0a0041000c0d141d01501e0741814145005696200d6510020701c540c10040b410300081002d5460f625890040c01c2041c44140c0c07072003c0d20000c09070b005528026800c7e52030a402c10001d44031440340148070320ba0032600d003a1500304501404611240211340042e5807200406c0000306102c0c5408002e10304983c041d196043c00b81840c0c0e050140b6003526010000d405800150052005c514203000a180ca9240a400c90b40e9000b0309c1e0200d203040c00b465007d81e8059190010f21104000c0090040030901c0d10304481c0f01d8695450402da401c94503111618000601c16819042101a590001e12200504007001a25524941503400940300c038900f8850b041002e501c42da = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 991879118 1250 991877868 991877933
    0x12060117060c0301090506010c061a090a141501091a03160801080622060510050310180212010207080408010507080a0618110d0905010207200105030130 67
    0x15607107014815440800303145900b00100324026240081415040c0495034030500c002400394403486441421000c0326078842d20f02041000121100903001c1c86070503082c006050280c025441c00907030404400000141c41c0700d05080180c1310b00b241584001c66040410030080c0764060900d0007035110766900b03e0020300302d4030340101c296000c00f020702408941d940302c2b00015000310f80c4028010004054040142da9498031552200b0030b440007201c0089100c1c08a100c20000c6050400c0526040b006407103050020388070100003400c2d9280c00300300c0648945184550241d5564080d4102d400342c0e034101041903501c82e26011282d000c3c1c0015520700b00010840c000040328800e051281c9001e803841e0f40d107103101c0c01010107003d101501212141c4c0c0c5030b0741400c0080d5144410a44940441c0340c0c030402c00540c89110b00d007070200800000d003140b1030301c61034100c51042c2036030307801012241075510f4605107400c0b40e2420840d611100810007442840c8441d10001441400344400703000c2c140c14441071803070314501401b2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 991880368 1250 991879118 991879123
    0xf030b18010806010b070b040f050114091606020319030b1f1d0405010b030a020a0e1903031403060307050105130510030e010b0a050105161e0b0711030301060c0b041112060117 77
    0x446d0017500ca1411000440c0c00207501c04080007043c0e000c0c80000c20900710325040011418405d480880403075024080c0c5a50f42c441d44480307000201454000786081a5110f441442c035200e400b9100b10404d582c0c0d03881c9803a40d0303841e403480c01c001c0002c0990f10810303040c1e2410082c1082c214500701045540e4001c0c0c030311916141c240503987c10b039585400e14a042d51940014100a5017005882000f0710034440c104c1e002c162165160342c4482c6001c00c1c4000c400a03d1030901070005d080c005031083d5140c8003001080b559480c006481c03821a5020b00e806561500c0314142d0507410b101641000d0b6202140c1d8040c0101e084d0f250300299042151a002000b031100d40f10100030041d1102d2040ca030100b00d05020240d000c1c55090a201d008500907010315804558117081440c0c0328440d03007812542d520b010418490080d82c0003007034842710010100154a194100180580703021b08400004010302c060301e00050400007803941c030396004000500a5800c0d50403030400d040d280c290900507803045841010807101d039203c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 991881618 1250 991880368 991880377
    0x905090a0e07090504140604031e0203072001180b090112020a0806040506040f0f02130509090319110a0f031107260c09090318010c050d0f030b18010806010b 69
    0x26070700500045141224032006014001d009450300040449000d610007803c1c0a002d100364400e41e81c080400c04900d40c11444045010000002c42d0710038010b00c1c0000f01101d8050301918240074401d0401c6a055004803802ca000c108640e80b003408406002500c10400f0300580300c203030800d80718403e05500550910089005040303440000410841c04a200c41c101940b006030846009040419000d042200070070076243c0d019084512540e0000c0c003280c0d288101e00612000c0c0ca02203420b541320b0304182c0c1e074281daa809907a1b50f54201045840401c51814040c0c07502d40140c480c090280c80b000c4d0001d0800784050300c00d14070f065005c0b400c06802041c85510104198003a202040d00c80e5021071008901c890b4080340150001070144144c0340c84401075500d82036254804c01c03203000210f40e03030b0351100c40484041003060704090520041d9040c0d040080c40218911302200d1151030190b03060707100300c6412000751100136150f980044020200c0e8003038801c0307058554140c61843d01210402c2e6a100c403405124400c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 991882868 1250 991881618 991881641
    0x109120c290a0201060f12120e01021011030105090a110406120207020d050a050d0503070c140f01090b1509010302060f030a09080f070c0f05030331090507110609100c02120a0905090a 80
    0x81104a81c011b5409274000481c080010310446400c81c4800d22141b0440350402c211440d100e50100041000d480c140464a500c040c003038a061240b85040e10030300b0003030f0040d4000c6506000070421600c04d0506640c3c107540d002c98005190007900300b141d082c40c0b51640001c0b0415501d6000305003441010500030008c6900503089655082d100c81c6241d100c0d103210300d41100749200b10f801481f004c010801024015816403078060b15120085040034428001ba40c3d910b0100540101c10700401000943e8501080d201181d40c0c0100d401d07030340e91b00d501d15807000303201d40e142c020300c1c810010951a8203081c0300e0003d40700c0360b0f00c1100112081c0e51181c41c442c0340c070202031045540c55441045003480d01c0d00d80d02c170400b244945003200c204001e000002821580d504542203556000e5032a410082030b19800005003015580910150001d800d001814649031184032011854290704d503032042c070040d8030820540416410420649403100e0004a0040502000384602c40c803030202000840d914204a1103003036070b07151 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 991884118 1250 991882868 991882883
    0x41e0614250f05040e0a0e0f0111070204110d110306030c011b020402071704080109021f092108130e061804171c09020109120c290a0201060f12 63
    0x103200780320440302c140c90a4003580820405020002e440790400600328056040d0b60310215106003100c901624104c0036160701c0d01d241c0e040001050b03c01807210120f41ea46501038030301180e40300508540b054036200d216628800e40e40b80502c00411000304030051030054104900f0380e051629207100446002c890056a143d01038420800c80c001407610342e0003010090321600024110319080c00c140340d000d81144d030090110307035110340c42d0305c04501c0c2c003900c894003421019945012400849900030002c510703070301881c000301030b015004201c944008206600e87ca0b51006d5240d41e0b4000110381d03080074100c4c41c40342a1400551401050b1301e4545040d50000511452418804c0c41c0d41300c1d11041045005446500008030b010000019829861401c07030821000e0341c0c4002c21000c9180c400102009565400007011402c8402120000358400c9151004c603000141c03600455100020405002100060b0b0280c0034a40001c03030f28080c98040d0003000440e10b541d00c01d0805207580b8007d5101000c1c0005004101c235 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 991885368 1250 991884118 991884181
    0xa080d17060a03240606110a03030c0e0d140d0e0319110a0803130e0907030f1b15020c040903050a080709030803011409010f030f0803041e0614 63
    0x1114491140764000e2005001c0d1014654a8880c1100d120020140a1329002c04184060036080c281c0684070052100345801081d1410301500b094803684206c40003400c044d1a0000e584a680c8030303101c048040030b03005003c65a0001545460783c0b2404808540500b10700a2024005e0843e026102844461001602405e00032048441100000c40181c00c04c503505500719046009507250800700c0f901a11040000f9582d440015020f440c4081c0300c0c0c0d000d000c210b01002c04114000f035000c00c0340021030358064641d0740c004010345004c036840071640b0741e2001c0002d136a5100061070a084142450210b400e6029030360410800c4080c40181d5812107000741c003242e420441e4011082c0703d003500f568480e0395450451051912031795065040d92003a4811456148810955a201e00d4001c08050040c1000c0075280c1f555469562210212140c203c006440c095000c800501480a00b61401b02c8109c14509040c00c482d05618003800200190409400c40005041c0040c134074044160142c080c40030800c4da24481c9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 991886618 1250 991885368 991885397
    0x306050d1a190c030e01180c1a120a0b1e1e010c05120a0e01090f1403031c0c030c18030204051b0c070501140f0a1214150a080d 56
    0x200e01c005041d903801680c6540d00010045020b100d0118080d1881c2e501060800040c441642580e044040210074644072012650010b50311010142c00c1f5403041c02d445001301d051a0300c1051a006c0c68040c0e010700161001040080e0f4040d600010806408440303052403019055002a41d0491440045400c100c04c1840c1e618035407807081245e10b010005142403a0b40043d0f81d1348080c2007007040158050740c1e003c04204443d406400c6190844003080c00e2070603076001403404401503510103d903c14103111201c80001b810194400f4401c90300d140d4040d02041c50460240c1e41e9030310050603100303070b05070000c0d03d0414100d8030140700d000c040c641050000360321402c29065030204002420b0241c07905500600c0c0c0b5082d1080032090a020b000301d80d401c0c8014003078540c40c100002d4200300084c0f5021544c0d850821480030100400016290b5110b50380ca02a030210310106444001005801484004800400d08200d1000f101ca5089645070406541411200c0d40c0c4d003005640d02d90b5186581e0340814096402181b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 991887868 1250 991886618 991886663
    0xf021902150702191802070209190b030d0f14090f04050a0f090b0a0e1501030609030216090e07050f030a0b101e090b030a0209060d150f06060306050d 66
    0x7424040140300745440c0c41603001aa03002080340d15483d501c40107610400040810000403000200c03140d80661038510342c2d41c001910404000c241ca441407840c01030300303403021419034002c0b603a105003c1d049480b0200766200c00b60a02000c002054002605050303a181101c0200095900d07001d400340c14100740200610420018000c0104a181c18a603079640c1ca030407490300350241d14504c03409880c01c0d04450415090040545035103003030a08042d804020341e0840201e54440c4103045039085903000508001500c0c00304e041c90303a51a40c0c6004903034003110124224000d584188001a40481202d110035602e4017840f24145101c88081e80c135401c0b90b0122004580401d0300e190784208a6101408115107900c404050214906500b40d0642c06000c410f00030307040c052090203040b40302200103242c0c6a48030342c0010101c0c0801814140121a568144030400c81000d42030140000e039000188401690740b801c2c1c800416440c0305400c0001d041c0800005d850a000100c0302da2240c221100721740c00c882d000e58141 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 991889118 1250 991887868 991887889
    0x1c020a0f060f110a05041d1e070504030b070306080c0d030906050d0e0a05060906070804111e1f090e100b0715110301170c0a051e0d11010f021902 64
    0x1011243c6800040e0544024076006200d81c14140e01e0f19500d41c0c2c10201043e411a546e50328000c012040d02c0180184109203031000c203045101c890301502c0e03550f290b01c0f08075118080c0d03520040501c44c00c3c2c4180b00d41c242c1c040c2c20450070354001408903460701282504208100c40c00e82c01c043d01007059036100344070743c0744500e001386656203a100010075403041e016902481d04180c050246c4440e007200042c411078103002c0c404d485e001401403408803907078103040c0c448003140d560480d6400c0c820040c0d21030f030182215101d01c441c0c0501c80c0c002c000181c11484d14104011440c10205040c001031001c01c4046160f120700c129090042403c18640201c0e00c1c2861b02c2e60700507904c0503806513503100486454820341001802035404403094810a182c481d490030010751905602c000140240e5005200405415125080c010007100e008840b20051030441809550085520b00c0001c0d40201041d520403060140c1080c04500128080e0b031a11502c03640800100e858054100b100c1c609109001021000340c5041400c01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 991890368 1250 991889118 991889141
    0x21090d0f031a0303070b0f07020307110108040c0506070605040c05100e0d0305120a0606030b0a181d1605180709120305040f0e0603010e07050f04020705030412051c020a0f06 76
    0x281c180d4203a40006480d6070030001d400c4030182c8246040008003148201d405408c01c20300c2c001103082507255907601c0041c0c0c10030005541003000c0c00e40002c040c802e0300c01d0458020400900042c1d541c100034149103002d0b0208031010307620b92b07014410004450922454105a080072943d5104078165130408122180301e041105408004060143c0004089042d241500030340c180907000a00a2074810301800351921500c85030311910b803018080ac010142200c80d00c9801259200001d2140c0050301c040c0900800421600f5103881041240100f4a640132150030540303904a5409804000d20000801941d00c101c0320344d00092018107003085414401d0302551442072281c1001030425448504d48812524a80e018110748060348090044900f400e01c03a04040a40d90300103884540c0c10300c2c010a050444444401c3d02840d4005040c0c0300f8401e0a1082e0340c003905080c140c0b0a49803240e401c041d50368403901004580200d034040e901c0380026000282845801d07910906a02100142d615500028982c26614 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 991891618 1250 991890368 991890401
    0xc030c061605030c010510090614060a080603121c0b060306100f020a1a194809031a06090412030b090c0c0f03040803030c160821090d0f03 61
    0x102c2041351000c0c01924803c40c0304a6502d03045515142e20602503646c00d40c840e9030b8500c1c0041034524135032601c0003215403003049420107030350740e494000100c2e20388034541192059140020846407000ca00802000e1020801240140000001d10080041a11090340c03215405148000740c0540c884c083c010000b044c0d260b40c0152a11070b803c50300d80c21103451f00000500b418040701e0b010400301c1804107100480d000c081003401c10060f034070002d0781545c0c0b440480c5082e20510b160400641c00d285a62004d03030310b170388290300d00f60f214107145030340607200600c0d0340022903005012003481c05400b4140e40f061485035030010b040d030280b500c0301d80b19554200d036983c4502d0b08158441804200780d480300030001f03010b16909903005681d041015a12400d05444180882032904100070420100364008180d0b82c002513101c90460751164400006c40c1040c0700c3d0040100200c4000c2605a40380c2969100e80100c0480321040c1d91440d07445654840d00d44182141001c0881d07582e03031043c90071600c6507101d5a80c440b40c46c500c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 991892868 1250 991891618 991891627
    0x301051c020316141c051015091d0618030f03130204050f040203012f0a05070c14030106170d08042303090307080a08040306050c04150509030c030c06160503 69
    0x50200b140311075034001c050b07050400040403196080c40e10003101c0c001050034100003034409541d01c4507220000a10103110403030b01d51040311080e0f10302d01980001010aa1020080f0828100c400d02b94904403020f031416900441000039142d400d04608651450031090103140f616507021000c200350340019110702e0000c010b0306000001621144501e0b4020043c55800c07000a14042c4105425078540b5292140b032000f000451201801c0b00103039400c54800001c0c50316840c1c400c10b41c02118107000358640580b0348007850000083c00c2c6036008030702000140990090280c0c0780c580603102904045c80810404690103204044ea01d9071060b00306a401c184a1600f03807501c20203c150360703908145c1c113100242da90b800000f2851300038030f010401c4100400c2d410340035140801c05a1105a00c500551101418623512080090030030b400160488015081c89540804901a22a03005003960001401c66020f44141c3c00410201c2ca0b000900c2180f0f0b64005249925006072505c030714100035120b202c202d445100920 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 991894118 1250 991892868 991892893
    0x50c070e0a020415120c1b0b0a090614010312020d0e01030b040b1002010204051e0927070f05090907051509060d020f0c060f071209110a0306050a0b060301051c0203 72
    0x80360a02151081d40e40b444c981704014075880c201c81c4246100400d10001042d0084080d0000180110158002e80c01843c141d49039400c0802614401c00010400ca19114030010702c00481507445040c0c0c1d0140046060520090380c0580e583d40d00000040040b80714007122a20315032094100320b40b5002d001e8008500d0102001c04030701d1214004003c079025075000319061106040c03004100418020446d40d49280003141004500082c0b07001d4000c480d02108060a91b0719480c42d900d01c00c4e0402c40c030703004542e0180d0ba125240c901441090017298880c0303000d80040340e2a040000380d038509803000180002c0000d14000102c1c00581d00000990f5004141403008594040300d61014000309620002607035580d48620b004981066030051040550240c0041072101c00c0d588442c03410400c0181010010700b00c08141441018081c010303900702c1d03020401340c1c400310810141d9040b603805924150800c2c000c8603906020091180000d006494000031070740090070b0782c1d002c4845442c000348d001905681549030b008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 991895368 1250 991894118 991894139
    0xf02030a0302010f0f020f0405040203220809040c0302091813050330071b0602280f09030506130804080303070215010b1c0b01110d02010e0d050c070e0a0204 69
    0x5405034050f0750340780e010700340a400034003507400d145901042c214030b0060720800a450500660007440d0003258040001b40c046d1840703100610303000e944403100444000d140d251034082e6034081c0320100d00840c103044501a64501a009451340d40e030f801804c00007010300801a0035070186005040384509002da40241c00403803000d0004000b1401440030040300484c00455440c01101030308001e04806041000b00401d0940c03000e00d49100741c00c406100104804a401c201010b8010742c0142d03d650035520a10340711614030000310900300c42181d107a20380c008074909800d56280515100150040d040300c00000c0c204032a010106164070b114800c400c0c242038660210901c2c0d90001c680c1d000c0540d201400c0c070802e04544201030703401082c07800301107032410702040003040080c18072094261415485440d4200036031b010f01c1c021000d240fa44d00071200d0041d0301000081c0a407041c010003190b1805071040c0e280300503101c0d400300d602980d060030061040910f040515003a4400041c000080c071a400d110108121114 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 991896618 1250 991895368 991895383
    0x1507200d030c05060c12010612090b010e0f0c0406051b1501031a091209040c170c09090c030c030c0a0c0f03081608041106070c21120c0803060d0f0203 66
    0x81c2d8645100754080d01d407081c030b0681e024141199500007400100c3e556082c2c103110a0540c0c05178a404601c0343e0b80700c65100050148600c00801e0070100c10004540d400078401080c0c441c0c444138600860301d803920344071400710b031107075001350000200200312014540c051400c650241d07d80c1202100c0c0060803c4c810406a00c0017030300103e17507890340056408a5000c1d4100c540d600850070b00042d103a2900740305080a43c9104081e08940202c1d00c0d1a81d4844060050000c0541480341604e40203951a048560150720b9200101e860300c5804c5030307000f24000c1142441500d00c10400100030902d99158107048a515070088500041080440c1d00c199002604003a1002803252103515010680c0c1410f030781e10105416446100300030130441d00100404100903a481c0480e4240985d252561402a401c0c0001c0202148d00011540c18801c0640960f5285a0441400030b9000e80000000880c24440c01c8509860019000e014030000f80f000c105e05150201c2800f5049110784120390070305d40b195000ca400c1141 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 991897868 1250 991896618 991896623
    0x171605070606030c0302031507020706111c020601180b030c09040c0909030f09060c0f06020a0207080307050f0601060518130b1009030201020f070e0c1b0f0105010503010b1507200d 79
    0xc520800f0170442c10200407001403142c4140101c2c200b80b0f00058000e41e25000b0744982420084120892008400c00380700d00303c0c04c44035090041421240e000006036885ea42840b841d012007051341180f8070a002c1030303c504085504000d01074003000c0c1e003500c02c004441001400aa45400d01000005010040e0740300e81ca144038841d44500003000c8040340c014200041d2070380b0000500c803070110100005517450282c84502030b8410401600c80500b484101d1410015401c80d0001e403000250447c1805400034181c10001c5d10300b4203d8a480c1e80304c01080384c0c030303000b0f440c42c4846142d044415400c081c60105011402200c5a2070000307208000b040004250400030f40805001c210803410520541d64180407080990810364014200d02e458240180c5448500401000000101140020009000c1130f5000c1c0f9030301d0054111040e48000b800c415008101c28400d50344a586882c00c00c1c8442d0400a8101440c0703103031048018141901034031041502d000044509600416408058501d40c1c0c40034000d4178501d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 991899118 1250 991897868 991897883
    0x90506070516030f0c050604051c0623060a06021507050a030209040612020310110a08040203250e0601020606060403060c02120d06062d0c0f150f0c17160507060603 72
    0x34005d0400080d428801c0d00300a000310300c00c01060045449003040041503200200703094412042d1801d1140041c501e42540c1c809800300c80d0b501c880f28003400c9801c0790145038116110344550380e0f50340d400da07960b655015008442c005520006010980540041c0c144087c403410b0261a00300110001002c03100250811703403901039a121b10b58207604040120304940800380c83d0420038401900750f0084c3c0b90003458a807404200e0b49a00060071510b0500c000007951043d92824821803641042201c990b201900424101c105030303800250040d8800580300e4010400a0030b018078050560700d4000c00b403c0303101800400c0d07100340e000400e41c008500005050781003c0d00e000085031403c003200103024200d0341156000401d04081080d4080c8e40c1d4107032021a170364040c105511001401d1908005d5810309090180040c164107508210b4120030341c01216035800b00384410005910a0703107060301e40c07884184031801503026400000d148041085402022600b140c20200e0500240795100c0e0103507030070b41c2c100f1203591 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 991900368 1250 991899118 991899143
    0x60b0d09050f0a2f0306040f15090b0c0315100302090103180c1509211e12030e0717370201140918060a0f0609050607051603 55
    0x20809019101c05a0095000341103910066107650038100e841d15144c803183e1036403164803031110050980e1140350b81c2c00501922441d00d41810800b0302001529001d40d801801c14007240310800300340c030a00c030301554407844a85440d10b0310540c1d02d100d900010118240c86110101070006540c688a9000b90300c1801c2c1c5d000360b03843c0010b10004007500c4000c240100c20441c0f4081007000202c3c02ca80724415903e102d00c528100d5803034017100b00d40e690308582c000510015410310480243d1984086001140d0055011024928a59150b0745020089d040090404500340440c040030078481d400c903c03219031000c0121307400e1070344030703070350046919586c95090b4072560240e483c8191080b18042c5e41088005141d1b08002c00324650760083c1680032481070300a040041b130000148405543c0c0d001e0781c10700c40c0c0c044c0c10910b0b02c0454225a410685040d14102d110b11404075001600003081903038a4160341d0259154621107282c0320500c41d2540000c40120380394000c800340800c0c0b00300c0c0c0c1d43c4c480c8000c500644241214 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 991901618 1250 991900368 991900373
    0x12090222061d0a0e03120c04030b011502190c050a06081005040902130b13050412021b01230c011401090b0604030b01030f0311011509140609070c06060b0d09 69
    0x44500c0399101111090207070302982603455510032210b61103101d240e00030942c0c03a03104c1031040c1584140d41d0501585000802480003503803444000d0002e480c402c94144681da42c9907039000360741681c110484401a81b0001c050654820900c0c1403004281c812200f01c41590f0301c803400290f80c261241c01110008900400300318003401d61200c103400802003a20100301902003a0003081c20350600034401d4541a85a000042042d160210841c00308a200c410411140c1418582403205814080003200180f10321421500c25401403000e200104005840e400d2408000c1c000502c251029140e45140b5004144508444400c080c01070328441415140d2408003581010f0280040700e07030500c181809507406210038400901c190316aa130560b5004901d484081d02107150032660800d80e20402d82565080001260010b0000080c29041d10030060090144c1c420000c80845100401c46107554440c0c0440003088a4900a061090807903000c6d803030109460780c036488410781c42e0340401715021143d0ba5a051a50030b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 991902868 1250 991901618 991901621
    0x190b0c0c04060e0408030412021207030f02010506010329011707020105011d06030304330914010305190b060f1201060e010f121a031002030414070609030312090222 72
    0x3070038000b20390003e2420a40c4070000c040c040108010002c200800075240c04a0003086000b03000d401c1c0454103942e802030f40ca402015910031841d0704002d076080c600820308560083c010001d41c80440c014031500c2c0b41c02200800144107850881c1c0341031004040380d00c17000c440b000c0c14092042040707070000306295241481a102c880986240c0140002d6210300380840c076900402203c0899018010740d5039460020303101d0761400060360200e5441d070100d6a6036181d5140c0c001d408081210544190005400084401035050b21030844040f0120a500f40c1469440941030307110350344030b44d0064883c50030250074004044580e40f298240840407014000100000740d0b0080c1c088000350000c1ca86941c00c0c02d03031071001900441c0356022100d8510b48541000d0700c1c1508038040150070752802012034000301540000f50300298002e64081e9412104041a5004030300d0002c0ca14084480680c1c801141d1740c0380d5201201c50ba410801c201a106841e0100440542d65200c00e01d02c2c1c000b603c50b05d80c014400030446600 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 991904118 1250 991902868 991902881
    0x40807050c150a08150d0b0f09030412080a021905010e1002070206071103120a0315090605030a060b0616050d0f0f020d050c0a0c0b0c0111070c05190b0c0c04 69
    0x91184008070444603108568006031014004242404c550b00c0d15030f0703580ea001280001c1e9981c0c1c0c01c25426030f8860706010306d0407551030003000d000600b04140d4a0b00e840883c0c07a4429030103050304051303000d0b40c5100041c200d00014241080d80d88107940e00740a0200d180407640c521042c00752150b070744a1721807113120981441010344a00b0008011881c1603030035408603420380508403000e42040401420703040b1030f88060141a4144008000c100d50f600c1210f00040c0003403056074040500e001c10b4038030106a0304031500c6036a00f66200140140803210b0256103020141c80b0b1042820b0301301c0018041014a585c11201e401841c0c0e110342d000e0800840071580c000c06040c2303e1801c54082040365440441c4003500800c1c0d09011005528000340e84409003128a481c001107418024140c0c0d120300e0001034032400060103080a240454001e2103842ca940c00030f411140031301000948001d07070800c0100580d10f000c088201d4070001c4019107806041d80e6000020b9260064a000308150b0450100b0700c800785003e00c2900c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 991905368 1250 991904118 991904143
    0x42601060302090a0905010624201507210b030105060a05130b0f03030301170f1209040f0e0706050301060905060c0a030509060d1b170601080402040b060702040504080705 75
    0x3000300910310780008a2240001c2c121000c5940c2d915000310034403000390070020140c00080444a071104030b070444003441d40003d181c440c0014010b820203130882030700b02000102c510304440040c8141500603010100984000e001503052003030300004012151200754040380030f01801c00000a61611204c185404c0d03a0009140d203205501c948010300280e0f840710032a14040c01281800522841130801003000340c8001409241c0c144408030002820400c8000303181600098002a5143d02540703043ea50b9507408200409241c20760188054102810640c1c00b1019665410f140441d0158a4854040c104529608504000340000006100807504080c20303400030036094640c1c41c03910707120116854590001800040c10014006043c8043d03640c0c1c0425200d1030749880c0f008004055010500031565003c40041e0f10126148810b2800400d03d001c0110b480b402068682001c5651030f5401c0000400c1c040f00c030076610100902c04c02d0056111440358034403441c45000c4982e9220308600741545040c00d2803180c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 991906474 1106 991905368 991905371
    0x2117030606041e090c14040608060a051f020606100e10030902060309030301060e120c12010609020a080618010b0a05090310113426042601 61
    0x3c801c942a210003084040d030400e0f0700740e45100d540030b1800400c24061000704440c07802029039030346c00f2500510264482c1e07110b0001943e08240c560300400b01551940c9080c91140c1c04000e501d800100c12150004055503030040103150160604040703004009504408900302d009820155136107078010091a2645007a403070f03a0b50f0700e40003481380000048204419a542d0f0070054408042203911001134130b41c4140c1841404801003400e800100b10750b503902d80000d500042480904600c40d00780e40c03000640c2c101882041503034410709080c01c0c403101000c00100300508c000c004503480c05425013802d03a11079187e60006414504400d0500054506150144c0300800d04100140004c0384d0014160025071402c00260b20085142c00c1408603c1c60706500781004102d1510b1490441008101c40001121600d034002d81c10340c00550204c0152007403d003000080d100341c80400d0320445180da00 = true := by decide +kernel

theorem cover : BRFrame.Cov 991726618 991906474 := by
  have h0 := BRFrame.cov_init 991726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 991726618 ≤ n) (h2 : n < 991906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
