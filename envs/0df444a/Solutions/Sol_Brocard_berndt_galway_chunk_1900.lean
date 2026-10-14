-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1900
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:05:10.169054+00:00
-- url     : https://prove2.me/submissions/6eee1fe1-87df-4bc6-a39f-3be857aec973

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 341546762 ≤ n < 341726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 341548012 1250 341546762 341546767
    0x7050304090b0f0604230909071703030106020601260a080715050c031902070b090a15020309070b0c01021306030e0c090f0c031e0a050106030e0303061e0123 69
    0x7404020b00a01071984400c6400c045100b0f4440f01068003801a032142e848280d811401340059880040382c42070304650007a00030542450640a416500c80d840c0c8a05032990700c5166044907200d2001c01074a068680c65409000c40e80d00c0d0001c4890084a040c030a480140741c42072000c0c030605400c02ca00c0745801d01c650161921035500303091150010403800031a00c04e890601007080781e81e01c3c04408590b406030200e840c250f4050003400361075009004901004144080300420b009020100068000c0a00d20841411698902080c1d01006a00081d03d2904255000b40c40500183c1140c00c0503100700442c2e040014100206011029004402c1e0b9005c01c020030340d54180325102100601140c00001e0059404046504001912000f00c0d88020810301181e680400450b152a542e550fa1a020400a4585e451113003082540d1030000d1400707100300404a443d0148011201c1000f005a901c5140001c1c0303010151061110480d0b08088081c070046c0c1041549042c00700c9201841d9400585502c05034801034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 341549262 1250 341548012 341548019
    0xc0d09050105010f050103090209010614130308030115092301110312060301151202091012030201021201051e0d0602040b040f170604150c0219050a0210110a11060405040207050304 79
    0x4113001c0d04043d04250030020750388056264622001c1c1115031524021128184a10100101c0d01a1030b06406140589010000a0040400c00786040c0c031462404080c0007116064195004907082c41a054070600911040040410690085228800c181000d0305880300c2d0800d664115407011005c400842c40703a0041c01081e090900c209803001c00d6181d04202d600e0b08003000c07489141e1041c04002e00c284040c10024001030f1811410320001c110094041d1340c114020b1601901030f41025145070304030180b0340d00003d0145040cc2c2c0c41d0741440d80410034008058181414460750b8108407a09542e8141c00f0440010b1100d01d41c0c00610040c210220301c01d800c24188040350820541c1071501c0111544100e0911011038034030710b42d490307c1244030400001c403041110804d9040c40c02e4200c51424080c03005400f203082c01030100b652090380e1b1080301c402010781070984043c4c03030155020250184c66800800b01000090071010740d1444410002c1099040039903410020301039074009401168a07400108041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 341550512 1250 341549262 341549279
    0x1031503031d040510090203060f090705030717040b15030114010807030209010b0a09060c0606050301060303052104110d0f02030d020d020f06040f03082a0a09051806090c0d0905010501 81
    0x206040c1d01c211014050341c05c0100f48281400d40e207000b032242d140e40c00000314000355904803881d210207078003412440c200c0ca425580688650411101b080120312401680e1200465113996035110f503621001c00051511584510150080324131542c0790950758546a41201e00300002000e03008110003002456080e003144180040280103a10038804040b040c06503440707035500201004195106440e085440d04120300300803000e406a0341c001b5416519040c000320903d41e201e402440004000802c1d540305c00c402d89041e000d82e43d0101c0740540b00c40c41860741d420107480e005090025540c003c050048880310700c0d400003420918090306600241c3d22550117401001c0c0c040c0404032121468101a046a15250311182495002c00c01c00404001c01600059503444100a07040d065010300d40e100305141401101601241e44401c0030301010402c50003000441c2c3c68000c0c0b00d400c100c00c60096551003900c480051044d030303020282c2043c01076841441455030010082c41a00700c5240680c001240315407501020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 341551762 1250 341550512 341550557
    0x6040905070e150406020d030513030516150b1f08010501140705060112030e0108010303050304121e17060f0f0607020a0e0a090209060609010203070b060604050307062f0d0302090103150303 83
    0x8002c00c1c5400c044c01c005c00962500362400e0252f0705402c0c0780340d035504405442c0004010308600281032005034402440c0058903075010b500c14001c19916440b03041500700c1c061010045018800e400113121270018401c552007103400b13220554040c81003600b0641c0c075986003805c22030240c10501005100d840301c2c509040d40844207102010702800c0a0744d1950458a004046100081c009013a070049449500d1a1078803031901984484010002010720040b80750307000300300c0808440f501070503a5185021031150302d4000050300f1125001131501a03601e46550903c5055013007010180d85c0440c00d0400020b06440c1c260005100761050b401c0024854030900c104070020001030f01c603074022013082c04212007a0340c000007241c09003500000c02e43c0e007641c0e660001411900c100c0c2c000c1d54050181d000c00140c07264000710f501244c404c40d1101c1641200700e44018032990500c4070380c0b03481503921040c2041407441c0071781e008015046061401150214500b4902030024110b60b0080700000d100780b071450036610158030f1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 341553012 1250 341551762 341551783
    0x90602040510020c1e1f120606020f07080606010c03141e041e031106130b0c030c0f030c1c0905091302090601081014061204050105011a070206040905070e15040602 72
    0x1000c031210300511020881c04086c00340d070313840c01800260300c440903140076140b181d60040c0c00b482c2c00e02c840b5480d5003000b5191b031681c01000c102845645000f10b0038100102c1c600d44509410b9450b5807403982980c80c2120784031880c1e0038900844104003c1107848121191041601c03041c00b0003447e503030340e28064040100008140412502c181d941b682400061412140000c41c180c2c03c03140c040c1c484075512240c0305001c0c00d40d8400c03e54040006030301c400b1044040301910141d03a041040d201350710a200c44085c1c40e0b2107400c810b2181a00024171f0202000d952070240d000544085c80c1c01142e6070340b1180441d404404c140c07a1480c4002c1c03101c00c1482146080711809034041c00a107440c2c0c0c058182310b074a02804800710f029403070606400704003100b07082c0c542c9403c0c1d655003207c400c19860203003054140346000341020f000c0c850301444120350002000c040c0038103c544066018003010f1030300e460b000d40b0100510002d042e08003000441c1219083c9580c03554005d9408046c4840d000396283d280504c003900d03201400340d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 341554262 1250 341553012 341553049
    0x1060510050319091e0605060102100b0315180105040305190f0905040e0312150909030a05220510090503190b01050907110703200405010b03060103090602040510020c 73
    0x2c10844842e04074500e0700880503100b42c01051030744407403420f00003007800c40f0607200402c10111262028005a0f130850790044030281c00392040d2040310308001081d1002040059015400003c5902100c5051085168441c1130441c2c0c400c1c41d4001c48021500f035130425942903001400100c0d40311002401801d010039050700505150100070b680c3c04020304148079501c5074502c195910743c19001000000c0c070466541e41d0f5542d090290518005e5104d09520791b1074140f00e07001d4402500081c812003000011107845003040c0d00c0303545c203084220b02c010801c042d941d000c15442010007440000c054503074880c102035000d003a8a0700182a03050000385072900c5076448240215207000e0310400d01040f80c0368102c50541d5015100013125940d42403080d106820321035100b502c1c5100d6050700200740144141da0112801700d841c4030104103030010040000b560310078092803150303c50800100c6c07080e40c0a40d1000c081c851040d5005405c16a480d00012101c00414002030056005001070601ea8a4080340b100403514164 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 341555512 1250 341554262 341554267
    0x3090a060806031009030207091404060506060301050904110418050114060a050f060f0f0f030709050612070e030a080f09010905041505060a090b03130b07080601021903030219020106051005 83
    0x200190743c4d10405601c901140d651a000c0d1418540b0070710800c4040c00c9440024422103160b40c0c071044030550119810b0f10060326000104450385040390840c0d0413908000d00410040d141d9803106071919500c08241a846580d800c84a80c0411001900c140307082e00500001496882101c45c4551303440000308811f1003081d404c0c005000303950352400c403c12408815210301d6100c11003003040d4501031180000304094003101003100b100e01d504040c0194401c102a039548400c81d0743d42c606000d00d50007031561910301c00d240f4034000341c07500f44240d4541e1a140c00090886403405026160342610b940220303201881c40d00001008102035820596a1008140c155020031005d12000850031483c1c01d10300450303209400010399008001c5c841d51802020f0010b0030300495032404c1940245400c0f051080c000c40700c1760f42c1d101c00100c4080c040c2101d40d22803401a0060705c424170510202d183c078504d11200460034194240300081204103a500d15000303c5143e5000080c2d2a0b00342401c203c0354042c03ca040b0800c000b000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 341556762 1250 341555512 341555521
    0x609060105011b061805030903071d0606030a1803051902070506040603050619080616051201060f02100905010501081c0e060a0908060a0518010612080a0309020d030203090a0608 78
    0x28803140b0501103c0c1843e82e00f4400b03103103030110261500c0801581080e001044d18418402c000c4000c201c0584100c08841c0d25650707031412940301c010381618142905003074038009543e50419400071a840145000005041307148040880b21816101000390b00007030000c03d18101c0301c0c004c0c03641e0180d42c808900081c0f8085162400240f0148241d02801040507151000b00d0600d46403404074454038040c0c1d80b640c0b5200358541071210b41d1000211280d15a10702d01d0034407150f925000d0000c841558001c40c00c40200c5a00303064083d180001d010400c3d41c11441071500c10011002c061185116030703481100045101c0d490305004510f02070040081c06003808420f4251400d03150441c04c2002030403003c1c2d03211512a42041019110b880040d07200e012a40641c4d4100107245000341e009030300c43e6000d010180a4100c0c60a406403c0b80c819000e031140607003009038000c0115086d0000b070706061000e03103808100c452540d4081503004103030410840c09a480171602c0c00d514a014a08040a4107080c174000700113103070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 341558012 1250 341556762 341556767
    0x60906050a480e031507030c0c02010c06090813090509070602030a021005041a0a02090406060e1806060904090b070824060d0615020307060f06080c1203120c0c060906010501 76
    0x59103907141001040e910200d944580c018002c1d940d00f082c009040c2c42002203003003007015000745c0494041d40020300e420010a0302d00e004040c2d07181c1035501a543c0b50401e10b61590750000410000006840002051000c404d004e180010042c1c064030710750102040c82d081c83c038071181c504003040c0c00c80ca013590410b000110030a036001600c1d54405080401c003080760b45480c1882c05042d0b529241c0d0f1524101003200b002030719841031300204a541e00c1a02d040003810781d192801c41e0407514603904554803140c042c078106085ea103d001c8480e08200000c1c9814138000e080340010301100d030058401c841c506268410800440c0d001381550381c0c81850ba1100c400741c030003102c20340d62026089003d2984034a07004142045a406280e0200000c0e01d0031260841c511400240d02944c1e0342c02c0b5020488455041c007400b4040d0b06050300906044a200d10014003911103444200440d036503a80310403000600c001e01600010117168071400e8044d00380c0b040309a65a0398111900c2d814200003c110020759403007800108060f0340d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 341559262 1250 341558012 341558111
    0x80f01050c18152a150105010f051305040c1809050903070803130218060a051203041217030a05010f050405040b06040b0406170c042412060906050a 65
    0x42c0442e404004046845801c603100d01070301810f02081c40c40c000d40300b8010340d4507021010310440544215040188250340c00780396610240690307800900c3d003680e00000d180c011009041d00c0400d00004040c50f41d1101c02281c100c404410f40040060f503401e04607a030110320300301e603d80a806a507109010514113035200c199a8418504021b0544000000280c21030802004e11040158024990b17000c441505040449448060350718902c640c000720000150b904d003261400c410401c51402039401d00c1d1429541032f0303070590103401c10340e450501c050305030380610440c1c001948030782c030202d000041c01c1d414404040e084031a6a0811801103240405001c003040d600400c9a610190454000c40d56841401c0403178080c04066100311200101445200314903803000c510500301c1c050a440400241d0109642001c0382c0a480150100554400b4000c1c000403109419484c0940e0040e80c01244084190b956142200d20459240f40200d503101c1c0820240105040440703200d03551900d64201000302405c030b13000340e41c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 341560512 1250 341559262 341559307
    0x60608090307030c08090405040507080c100c11030a0813060e04090302030d1e060e0f1f060503060303120705130618060c021f08090601060306210615080f01050c 71
    0x2c91031040000c10440c02174210741e141030006d0300030700c603d05040c54030580e030311050f009480c0d086c001d01c1c2c169060360420020a100c40030180d56030700c0001559464803000c0004840c820f5406009418140002c5615400102584101507022801251a00754000e258016400e255031266042c2810741000c40e6000054a48103001d640c030004d550003183c9c19035002c8802c25007083c035585003801c0c070009166000c1c00c00030348508620300f0030600301d0361a80440001d0204250141c010701c8100e50b4184039040c80b40c0040d540c80080a411a8604a94102808203a1104580c1d01001500005181c0070710b64401862200070446805c11403413125801c4160052044a40528001c00c1202c0e949003046d942e40c0003030500d0f070b0040e842d1a5006100c41603001450982e0484240d11580310322000014450311034807500c42201c8046c4540d2400f12241c00784620310349480d80056445685440141910255010401e0018150000201296224980e00c0390950b24001e1820707044031810b02c1000040d0020a4900303651 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 341561762 1250 341560512 341560517
    0x15050c16030e0f0301180309050411040e090115123f0c0b01030b0601090f0b0f070302011d06061504050306130203030d0c050301170d1d04060b0c01060906060809030703 74
    0xb050600c402140c1c055102103101c1d54190308208010300a0070f10103400c00c51183c002c1e0359180c0b1103034a44040c0825103440da00b03902010070f070401c8204610b184071640c1c03c0e080800703480041883d640030882107078000312640285040302e4400134501d0401c0300710f10b03440703040000d007002103a452001e240710700c0820b403191600da45000c85c5070801c07008002e100d2003443c0c0307425038060030813811941c580c05c050381300c0181291140c0c04600940f00202e0807201c140051402c803006181c80c40d140c1545186a0706258000c010300702c05564075032470345180030f0418504024000c1da014004090926005040250400d10507544501403002040300f401940c80105d8455070003c1607440444510741c180c4040703841c1d44103000079050034a10300496510301680c088000d41c103c480c0610800c681c00140c0454588489900340c0500200f50344940d102c000036030b42c200710f00c00e10342c00800028035181e440c402c3c100340f0340c81204a03c820f40d645000c10700c14041035120320005001549030081051030910301c4580c2e030f48034041000c2c05 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 341563012 1250 341561762 341561777
    0x5070206060f01170c0a0228060c0e04020c0109150605011b0c081209040c0f05030f040c09090503090909070302030303010603090c05060d0c12020a120b03100915050c1603 75
    0x54a900550704c1d031070b000d02e410120781580d190180300e080c2e4030b4020700c0300140140150705c0402841e0f2485040c1300001c41c440070081218203c2596800f0041c10892409024480f0301040d0000d103a0303c5102600a03d04039000205072001285000e00c05021508040c0385018a090018440390743e105107909075014100c10354544229032424003020b5090300f50321a1102d44581c100b43c0042a4801d0054128600c0a40b42409001c0c4501d1043d1040d005400041c0c0005400384001102d0b144e050070140e40041c020000d001764503403500004030950b0301c050010703140380d03200086141d5103040c4015525840b050b03030b0000c0d03d401403d5600190b1a4070040c0300d81700806d40c860800c18140122650380320000d01340140040e9807103181d94003041c0a03090303203c0d5010110f0f0b1441c04980b5960f071303540215480003e0f01c3e40c4101500b280000304200a1481d8007e150b010b100d1240383c12b08a4106201e400000c030301074101499a5400000890b056610040030b69000450a016030181e0020f100c0310200c201380d041c1050f51 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 341564262 1250 341563012 341563039
    0x5150619051608040807030311070e0604180506100e060d050d1103040e0f0405100606020606010f02070801050a27050d05070326150105030405070506030c0d0f0606120507020606 78
    0x4408480441010300b42c0f03c0d0000c3c001480600010780c03e01182d100f51125004038075030211841c6c035010503108101481d81e801000420516140c0e001c00810703150315032009a882550f480e644e1412504854443d14814010b0b0184907260300300a42c7e43d402003044500c10901c401030b40c0c55a4443c03550121140030f204510340203400615080c01603402070b100030b4060622a2030075009a02c1c1d08041900c0589041c001e1101e00c01e0303400c2240c000d00c0240c031440c0d00104055120030004545400b1100d0300801180102c01010442400a00445000344440b05020400e4222401c1c40b0012000d0a01074442c4060005207080000c0c801003014241d40c00e040c03c15a8440c03240d820281d500000c001c4044078040c00c884001c110502188503040d0081c00740d4048441c52840b07140055510348820340d005002036000100030070581c50106c1c021a07010041d41200c0d42482c0302d0403400c205036401c1400090b4410b0b145e500600042c0d51200c400c0400c2901c00109201e542040ca101940303402c030281c0520b001b599802c00c1e89 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 341565512 1250 341564262 341564287
    0xa020103110f030a0204090f180b07020f1002040f05030303090604060207081c090302010f11030a0203040302071a0d05132109051201051e07020601060503070216090515061905 77
    0x44204240031075503030f6503c0c98042d035800000d5211f8080d044480e0b28200a260290915210b100c402d1000f200104005550740d4590003507010000b0710803001c43c0306101001d51848411b000b001580410210050380b40d5050400311255240a13410850282e4000d01c1000010350001810641198001d94016a15012030a04915504c81c00f03034a0514290294140c0d1000e07441c50f80b20002c1d0600071760007003210780b02004001e01910401100020551f00500104240a946038011070f00680700b401200e508070382d01d102030101e4a610640c00ca000b101c010400c40a510518044c41e0f07441104a092401f05040e1592545c2014103c52028010303590503d090501442c0240c0c441400b9110003403000781d81813240069203000c2c040c100d0700b40303592289104031070038800f1006a80900038041a0041d00c5a41c6c2894011580b90304024030001c03c51150745190444441183c1081014007640321010500d481c142d0301c00d0003000764800e88030380603903001c110a40100e009518103035403a10040c54242d5940d00d00303048a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 341566762 1250 341565512 341565517
    0x70201020a0b01080c01120b1005090a24020105090c0604031112120903010f2d060f0e04051b1c0201020a1505060a0602030f09120f011514060c0a02010311 68
    0x6045001c50350000c00c00030000a0700b0328200009a07600c04d442c6e540c01104001342c0d00003c00700c5030401c06031002c41d083d4034058804bd1480700009017582048aa440d11041c9031304000998610004000340007101540b0b60a01600d640080080e00034504000c4010104a0b2031007a4800645100351100454010b5519031410110150448003114400080c071008603170b07990b1148841a20961801411880d00305050007942920003051003041608a501c081e122000c0809140911086903101008120048840a0720015020034900440b0368030303152410030b152060265444004032006071401c41c495981300d00c0c0c41c0340544c3d40d0300303a4144020b881c40180d01c0c10054000082185076030f0824040c4680c0705074412071240000b00d45202e2402d580e000300f0f903100e1169004401d001b0408020b00703200ca080540d440c00702d0380d100c54110b8074424007075251103003143c012244a15140c00c01c52420404107101c03110703040710301004603040d500e40140c140780d542d41c030341d0841c034000d05040d01d41104110009100e001d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 341568012 1250 341566762 341566783
    0x4080c010f0608030301080c030601030f03050309160803130501031e0c0e0423060603070e0603060a0e0403020a02090105031515041b030605091503060601110c031b090606030c03070507020102 84
    0x41804050f071207a000c84e8aa070401d0282040c54841c48154018928000480f98100e1390825640442e02100352011182c0794070042c0b15514510492494102c41d0340c054901c0030007000c940001e55215003c0041da01e1600d000b5074040c41c1014100301c1d20080d00f42211100c9520f60510001c00a2a000288003c0c0da404110310070039a07200c2d250a070034040085040300250360080281185040365a074000c1005202d01003a07c1c0b940000300d02440c40c4c031041c18200c00440d00031000910000920b503440c0384903074803484129022001a000005a1000c505002078880d0142000f24040c3c5100d50b19102440204500102181c40740c08407415421001e0b2526071082110031041130040380e800416180c050050009485000d020703811440004400310043e00382ca1700701410042c050505902d503100116a50381080e0403880603809189082e444a6404202da0241c403c4003c010420004c184400c000b0100e40c020162401134004004026541003001c2c1100c3e482501400d20940755403507800101d103480704001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 341569262 1250 341568012 341568041
    0x1e0a021009210c0605070201020a09061202040b030c07050c0a050d020409020a0305120712020105010b0708071704090b13140f0c0906070305220807180b18042001020604080c01 77
    0x242c800403402d07804652242c03050f001e1801807201791220398040b401c074464881400002201d01a0600449100b400c1840300346409a0000d41056250f8aa540841e8415100c001110b80000390050400c001807120f00030340041120140d10312803410022424019401400038401e07a910401c40c2e00710b60360742d0440000381d5085401c0b130300c182c502941c0f984035a0344119003c4e141456444140748602d031050040c6410703035014880309810b004444d5114411600701c2070b000c9902c54420500c011000ca011005440103200c100400724007805840700b4043e9114060115500083c00c014030307079100b540060300702600300014100d80380c956a204620660907004445030154031500004a24080c154010090104822205030340f0500c65122030b8020b070600341512485190390802c000810450040710b0005c41130400304074010407048250b100040000311710b400308000b181860000d000a02c203035082020786081111942e02c03680c41176640045c0d0748180003403000b40301c181d001500501c1d45000390400c004194240b03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 341570512 1250 341569262 341569313
    0xc2505310f110309010e190302030906071115090111010b0a050d03020a06050405010510050f0a0e100f0e0a200d1109041b080a0614120705060f1e0a021009 68
    0x102018086c2441c0c6041c40c01d11b2181c079080c15041c400c16104100940d6243d0001c614007e188414080c82c0d400072241070f185102c0c00c1c00c6a4205880d090340802c0f140842d401c805549052040c00509415603030300c030042041c0e01d0108101d6043e103429044406844080b5141520070403a03280c22454002c044000400c141d0908040c00100141500064080c0054480c095070309031311907041c451241c0500c2010f991114980808011241160112907000000310107074400c06038580c070060001c0c0240c1c0d40b1440700c0d14207640c104401d104403403180002e4001c031000c0385c0c030040c500c4841d240164050092000d403070590754050740b0050a074040840c0d0003000040c1060040350600342d01a500b9125040c1e0b800c002c2072030f0300e000400d015200d2003042c0c1524400f41c0c1c2c04501c41d8125050000840340e0705403806040c40f50207000300705070b50383d003000d0801e040601c802c85980c0c0490f501480800b01c0c4614124903808001d0012048031074000c5052011304401c3c0c00300080b2059039080040c0320240160003248070700040b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 341571762 1250 341570512 341570521
    0x101a040b07021323042f2b14010f020a09030308071b050c090a0e071e030c03200f090c07060f020f0a021e120c2505310f1103 55
    0x200c2c80c0c03103104030b003d4400b0441c40d01c0100491100e41a24072100c02c3c10110503c810b0241f441d000781c80c1e5580ca104100000e6400c02221051b080c0b91807180300a5560340c080020080c41d0440900603007a00c0c03006142d0960030000c180c0030160020701c0d18080182031000c16800559100d22a003821003000120760315007401081207080c2540c403040510003444c0a140080700042d40c01c01c0d80e00500c0b280c3c00760f04d401031040ca0301c1d140c000307500313640d0307009003080060001c48000000c500355545910146004801d04404002102c60b10756072410640e030380d140200642105014655243c02c9a1a40003059000b030b25501c0c0c440e03241900040412042c1120100d20110703100d4210b0715180050121b1a0032a004c840100880407207030442007200380b10030401917112448291420125070050840d031000c0c4c1c012035015110070380c03c007107026021101701c00100345461400c10061074000180d110266030b0320b41d40d04000d1303074001c215054521002e1540038101e440308504035140c42154058000c83c40c0300b92506840f800d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 341573012 1250 341571762 341571821
    0xd140c060103061d0109020f1203040803130f0e0105060307030c050d14010501090f080615060d0905011406091e06030f0712110909030306040f0212101a040b070213 72
    0x90361810b41c8132000b00f00460801403101449841300e02034009001030301c0b405000b4108038072510004005011808140b0000035690340c00c00c0a41039064003001070f1030400d401d008561003200c290740e1180201e141a000100300584404084a070005250724011401d03100e90302042e1618401d4a014032007032881c00d44420303400503841880e14142e07007091340e03445c2c4c1040d0740b0403a10300041c0007400b8980054010401061301d443c0800382c010410007014003001c0c104841400035008680803c2c0c01603406945900341045596610604e81c4c1d03100d14201ca1020690500346040c18a0482044040c02455039030710215045560800100c003921203240c04590425444068100408103601811551401e40642d00f192030314110b80d013a486040340900035411a41c400b02048043d285a051921409508010b40c8c140708600801943c818846010b401031294074040c10780f1090582d00e4411a400001400188402000b48040b40c070034a80445009a20b00069590b00c070003040c0e48502c81d08404000704041d0069034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 341574262 1250 341573012 341573021
    0xd1d040f14040b271c030605060c060406050604230403050c010c1e14032409010806090610121b0906080706020c0102030403031709010905030f1c090201020d140c06010306 75
    0x14038554510000c01841e0070400131411900c075185094102c412038885069450200e1419104140740115529548201140c580e80c801d11416515030001001c10061082d513014007901b0500a40d02003000148500c00c921040300c1000794421021564004030301498072410a132075401c410f51008100d40305c0f00c0308024040c004001d1001450741218903a00f41124092081440d28040080f403481c82c650350680b0400c12001da034125120842c071070b403407000c0540e22041401806400301d0f00041160f1303780300b540d89144c1030b0f0040c240310000ba094602804030315440214081c81030791002005404400a4290058405440e0081040c0d645000d00010f50040e0014819049a031550213451000094400480e282e21645c01302070040340c034582860009400000710164840c2804c0c000003081e01d02562a6400d65004030000040d0300c4011401100700e101d28013100b00d07a8507400c0d108201021841e80041d4071091000c01080502c2070300c0040700701000c5250101c0e003d8000341030540d01c0c55070f104d10b4610010b1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 341575512 1250 341574262 341574271
    0x13030e0405070c060b0d030c1211011406030c0a14060706020706090c17010c140c03092d0405221b0806010e160c021201180b0402030d1d040f14040b 65
    0x2d50401540098a003001b440303068082c0d030141d0780c40500088548036404514101d14222081041c0d15140c600f1001c02840340f40c000c080780746101d050a0406004051070000f00a040701d10400c40c50204000c42c3c192665550386c030000990380d054a0b06254180800240103150000d080f150800316404100007400300500150385034000c00c940800c2c0c00754101401c90f0150200c5402144400000707900c010422800342c04102c08140417240340412032000700c0c1c880301c200301c2c05010f2084002d150980030b81c0044280141c088081c2c408005520b001238070312560385035003d403690110103c115140309002c14891004480d801c0c0b405c0d000030244c2c1e1040070503512282445201040301d40000892401650300c5800308600540c0e03501e001c241249502082061404400c68200c50f41d071340c1d5000100042e10204090390180140750482c111314180c01450f0800c8400c0e041d10041010144c03e005000c150301d10050003856040d0b40010b004c1c041c03210010000c20380c42c0161444100380340300700404c02a8005035644103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 341576762 1250 341575512 341575523
    0x15091e12060c0313020a120506161715060702060412050d0504050d14010e01140103140c060315030304030602030405160501140703230a0c030e0f060313030e0405070c 73
    0x42a400034203441c1c80721810394902a10020030004962000e00300c0e002404814001007102ca44569244010401c4001c008402c56044d04900200544001c0c0d0a0a03c09035108070304051070341c0d00b05002c001c041c00b8001803540303540c0c0e6090014118a0345413807043d94142e0368040c05e450b46d100d44034504014100c204013011103892140c4400891990b02c01e4095400301e400140a80c241d0244998440040c00712100f64140e10703640e29809680070070401d009141594448410301e44165055040035003040010001c141000da008a41c484e6640d29503800f2207620070801d1303d2025200c20f514000a003144666800a03084500100503c0107001011070b840551846904080c41c1459540c801507404400e050f02d1542b403064207006460100e405402913444143c1c07401480840f10984e40d918850300d40040d0280d00004403884d100758201a0848d6409070006001ca0701202110707c494009a920f200c0204040d80ca903084249680805000d04861440140001c106000d0b91400c0e0400910000384014203454 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 341578012 1250 341576762 341576779
    0x40e0907050103021804050901091e02032b0c0501020d0507030618090305161e05070f0f0f061b0209010308031b03130b040314040303030609060b1815091e 68
    0x81ca50302038400c9030f54415030000da0054504542c0200001440020400d1740c00f035403a20420720005501402211510045440a41c41c0b80480d0060500c2e00e80e8402460707c40243d00c46072601120240c880d03a00c442c403074620708100700b80ba41c0e00d041c60282c01a1003101400320309041c1032014141e0590004015282c41d03041c7c5070750310b030001c021b500f050701c41000024003c18010480098001100c3c070307540500d03e01964100c202070340e4022082d4240341000c40c0546c0c240d080443c06003d09180e001011000f04065182200e0681c146800c00500740042d102c1e400c00d01180c04049125880d0109600744160340040407181d1340d42c3c0d603080142d0107078811203520b070a000c584040885034503005015207003d210381564004909405a6031860380240c090070079810302000c400c440200000b407d0040c800740d842542c000c19014a410500ca00f502c10540100da0610001d006810444d2240601c2d441100380464170f0710b500c0a2110914151845001d40c00c503003102c40703c0c02880c030b030700b024444400512009558030340 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 341579262 1250 341578012 341578019
    0x40509030a09090f02210711030a090e072a050d110a11060c0d0509040609060b0703031e020403260a050301271a010311030613050901060902040e0907 66
    0xd40341d00c16201060007040c100c10060220803000d50040c444181507850040c680b150700c1c0101e44a554150001001e0840200c04001810307070300c0240d8003082c40a1000441c00d1020440028013800d00301d01a0550714425440083c0405210f2032408082c20803c0300004511107240716001c00c2c60fa00c07010f0a8541c2d2240707084281c642d503c190b440004d914402005401c610500341c1c1c52102854a11801036407104043c031100910003070910068101745401c3d1101c0e40d83d40700c864180820303a24103500c503c0b176103840d0040c01c029001c42c00e0308880f00c85034907103400901c00c20f603042d58100c801d507541c99550392a40301040200801c601100c2c0c1500500e5141000a01464640103050007031007a071120701c000034024401041941c480003920424514489868888441210750003011120130025407180e000c80c140d420f08440d41c040c403540c0704c00049504150715520f00340d40842c200c5500b01101c412011b0f44c4100064411a00794404030141c800e205d020356640d0b0361554003e40c0b4040a0b940c20040e40244603001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 341580512 1250 341579262 341579281
    0x8070f02030c0c060d020903032a01050712150e09070513051501050a0e180114090c19030608030c031c1803050c100504060204060e0117040f030c0b0f01050405 70
    0x81d4400c01d0b80000415410384040c09000301c5400c84c0d03090061068003481500c515580602c0981030024900c4568000f6682c1003030382e0401e50401c1039241009903d490180020300e0340c420441310b049540308001143d03207114608402e8050307126a100e1200550480140001c508001c02d03040f003104c4007240d80720b40d0048070b558240d0850300e09840c007603440c0c002d0f09452501c550107000544402101c60030440e14003403034840130640300c4041101c1890304640360340050080185041c15840d542c441654001e41524005108a03298480c000c1c090000a40002d0031043d0075120741c0081e4094983c40c000ea9844070400e0244654a8015803540080042090f11003883c2003060300c5442c0907001084400300300000d50341c4090b54150b01c00018503105005561001004041d503006031406107110b41c00042e600c03494020001c2a00c02c16100090422002c82d080155028240091036001070300304e0780d0403448402030301d001d48101d50004d500800c400251400c1094100010042d541242c03015103040c085540c680100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 341581762 1250 341580512 341580517
    0x90105092406010c1a1614091806041503080702010e01081504410c0f07080f0715020408190f0308100b04080c0a05010305040203030d02070206071208070f0203 70
    0x35420000d0040000c040d58400c2c91001e084c00d0092180b10705402c0030040d0b51501e22800c651140403402c11018040d0602ea01c0102e009500c84c1c041806070404040c1c80c0014038661903007900d0314184920704041110790340c8590010310003124001448a4580e50f034505104c0c6a0445a0241e010900f00d032001160783d4010320f0350a11076280f90102c5101d0b000b035002040003c0501c2542d00f180783c42000c83c0c010310343c4d5243e81c00e074040b1b05048081c90a01e464100780b880140784005e11204401c1400d1100c4012441200240c49a0b2680f040070991982041040d4411501420b003010f00507100001a280c9220020b5008200340c0710341105444400300d102c00d00c0c900042505100138440c01a4880110101c0e00c140c140235084891a01100d023a2665410040d15540294000b041550031010030b140651514600e00001001d0a08040c4810300e0280c000948900600010000c219000200303041155240340840303808aa01c1501451200602c0100034441502114418046403031a01c003150400c1c000800e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 341583012 1250 341581762 341581813
    0x90905100f03080c07051e1216090e0c0d0b0405010609020301060e0111160602010e060112051c120612200603011202130204031a0a020708090402091809010509 70
    0x4807181e42840d540d108a09940640c1480d04031340110100490666162403541840020700e51012a07049164800c0155161751100340f4101c0390b00c071091002055034080c1c03080007110170340c09002a0380c0700801901400c114100c1d00d540d500c2800c5070b04c0c02042169235410140198000e100800c5850340340c86201040b40310070300031300703012459501c11402590320560182e44100002c0c82928100e401c0c0c0100c01100c0c00c0d0940281c07015075156408200094400c1120900421011320740341c0c6100344a44441d03480b40e203580ca0111880e0b00404041d44858064080300d01c403a202100300b004484e5540e424120041d000035411150403911210303000b99040000c004001844000b04030324030f5a482e1a0100c038182d005014101d811284089801016900031302c06030004500130300050380c040e01072040d1550b100e00c0040502600501c144240701c007248010050300c9140405035401680d601072400040d400e100b14807507400f0000d1022007003080e10081904001e004520a02c01c486401084243e42e1410044070034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 341584262 1250 341583012 341583029
    0x2031609080a0602180901030605060315040c090c020f12041d19020307020a05031305011808060114040e010c03090506010603020c0307022b03260c0d0509190309090510 74
    0x35800004101c0e82e0b4003c011000001c0d141e142c2c03607400c20001c06d0f44c1d980240e2040d10080c4c5d81e1000c20055040a001c0800d94501101e482641450559540d03001c0e84018050703210a1780c1d903101c404a03494000c10200c5c0700d40802000b01c4020074800320001c03066610500a03140c0b00341c5480c140110040304091628042e8868081c00071050400401f80002500014403d100f140b01b07440401011420600041190f801d000d42e66010316802c14001526041103410410b4050485190400400f10301050950558a20745001c41080b040c15001401410b00302c80070400c00d500c3c0880c2041b0741e5403d640401049442101070340c103540e070707106816002c0303000d08440a1001e82080003803c0c01450000c0b982e18414581140500c2401d80c0c851030b07641101002c0c1c1e000c5010a403560081f030350784982e60528803580c10346161055154540304c18150403900992001407510354940001c20640581440780060294450012b201113110f1804e0040c603070b000754410b4008061905011500e1203143e948540262202c20 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 341585512 1250 341584262 341584273
    0x902031605210c0f0a09060b07060e030306060a0c0609020a0603200405010c03030f1103011d0112080d0b030f0d0306240807050310050a14040507020a0c150306080d030203160908 78
    0xf0144200640550310341c95018903a03100104450096114000c0608260482e43e51110054941003048820341040702c00030303500500420820f51381e220221102086a2b10309018074401510302032000e026400c400039170103201342e4000701c1c50304da0540c0123424400c1d10002d032300c50303070034035078141102d41c4c403690164074000b41c41c0c608080042402034001c0302c00c100e03c401000503030203803505215015401c00c0e0440711003008001046940c01590461040c0501564003070710201101c6a038588405101c0d084180c90030b039890710340a402070342c0c05102d42481d0400c503a00350350024488040040090045000302c05070000419551000c0220515115643d20f00e0380c0c45507034032500da000c0d090f00d142d0030091a81d04080114600882e842c0ca4060f40c1100a25090488603003e031100e4040100350764004054030119400100342e80007041c8950752a004480149401480d042a1140210041c2805801c01400703807050800707440c01d007039041d402036101e600c103080800080c45220504460543c00ba00c919000359005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 341586762 1250 341585512 341585533
    0x5060109030c290408070f090203060108150103020c0609010c0215060d1106160c090c030203060a030303020a030b0402030108070501021608100f1805011d010c091503090203160521 79
    0xc40c40d005100c91042030400b03c02d843c90203003c0c80c1d03680c429004000075801001041100c1c06214100348058801c42c40c6c2541186860380000b45404802840341c0d0603042000c180c41c1507640030307038101c0c2c0230740b80c03c04140c40962034400b0340396021b0040748010300b0041c03160748443d200e1141117981349030192400038901c0b000b0440c282c0f60043d441080c002000c2d07104504100c0c03e00311285103020103105900c90480303d5656440c18a4540c204c41c03a1a4054051600420070059550f90300021042074035450306005850342200c0070100c0080802c44c865541141c400000490940d00000305101290401d85c201c44040030800440c10569203240720300c1010754414080d0300301000f0141c01c20003801009400018078a581208202c00340c04480300160341613552445500d42040829142c072200a249200134000c680c41d849005244901e02e11030090b0a0044166000e41e00d882500403610560b001011203020211041d01805815882d2045510441a42c40c00c5504103d50f4055442482900c90140401c2c501 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 341588012 1250 341586762 341586779
    0x2215110f0c03030f071106190201050c0a0203120c0f07060f0f0c02070e0403021c08100603020a0f08060a080609151f050f0a0323010b090108061b19080a05060109030c 73
    0x3200106d42030b103041c158145135901e48102038101800843e101c1c0c140072860b408003a085030000741110400160401840299540001c101c3e03844903208251511290b0345c000060b000ca00801e101700101c2600000c2480901883c1d41081a0941c80040204407041d1244500d004540c00d026003900035030000c184c10404124006c04280d4400d020340182c0f04080c0c00d13503804140305500300d9000404a0400740034013458549146100010300703c6e030b043c01c52500380031034006000c28a01c48907c601f042079000025400c0d0300c4d4440100010301104080316480e04007d29500d03120075030f50a840c4a004030713500010b070480d54a95144c02103000f001500b1951075040c0000c1c000c11204100300c840d0041000074000001031007519540808010444030704445001c0c0302c901c030b803d5910120348141319440480044c00034401c042346650308011000b19402481182040000b064010001e08960712411040807140c05c0790014070382403040b01a00d5003044150740d40401501c1003207481c0006004400144401d000c80f52 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 341589262 1250 341588012 341588017
    0x8030a091503021920060405120f0c0a0803070f08011a030627060a051203191b05072c010303050c07030507180606080702032215110f0c03030f 63
    0x485464007515041c0f42c200d09030709044e0402142800200365208208400340ca59016031413440a0710007606944c00d00e51240c0d66030700c440717a103903108030040001d103031151000c2403080b584501c500000741d410500090070210700b160401ca44603000700b00b51120700e1840038404d00e100e50680e00350b00707500001da000f41e9500d424a82c0000742225006a5099085007061070601042202c503c08107040f40f030301e45400000e001042a066120302d0041503000c51440d14041c0120585600d880480703580381c80b8001e2041d0480720b440020101658421072100300b40c09115000c140c2005903043d078690b241000d000f404070440b2150090342c24500c62103020300180002403145c0014024050201c040b640f4072504d81c1c071018284071142d4011310700343e03160038041010084503001e081c0061115081510316443d207103d01940301e120707007a5120308140c0c41d29019214602d141c1400400740940c45072140300e407601020050480b03170619405011520800003045085040002d404800c4840500518100f02c0200340100503074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 341590512 1250 341589262 341589299
    0x905060a0c030c030909020c010c03110c031e040e091005160c0b0a02130f0509090a02010221070b16090b1801050c0708010e03180d11130f06060306050a08030a09 71
    0x8001c040000a10b0f25140c0082c048e030750550b200020b150440504003808490903c1170200c040b070f1050020403200140842a0b03900d803d1440d60716000003418444c05001407048d600080e00d01e030700000034060001000102c00c80d4140c0c51101c200606e45582c504c0c109803501c00750102d00000d1442e0440e00002e801449060340112403200090b0506905e500c00540354246134100210050340380302d0402403882c03d01a034640046508000e003044042d107400007511414005001c0e907080c42242c0021141030a0203044480194006005001c641044c50281219100c03400700700b000260070301c00c040340d805080701c2242d481c08a407020301703c21000c080c0015120f9410100701804140075141c03000a00031002e010344040001c951002c0c50f600ca810b014a41d50720460814039a010300c030721131707155400a40e04542002c04a80704550319070300501514142400380003c1c080c103041050a1840008600790903130004020b0301c104a403910201070300d0340d0300c4d01c1c0e0320301810310100c00041300c2885c1040210405003107940d21 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 341591762 1250 341590512 341590517
    0x50a17031014040f0f0b0114030112031b0f030e010f1d0f011101020f070311030918130f0c05010306061d0609060d02040b18030303331306060905060a0c030c03 70
    0x1013840c82e80c0520201c5079880342c036003445515408034030725170340e808002031521010016403a811365041808200b50038010800042c144410040c02c03002e04905161702089455001801500c00d40103440d004282c0d0600c80c40f401d0100d01c21549200046008088407019412030300c06100141004e10104202c0d03e60658044e414007200003000d014400e000c0c00101300d00d4261100442c0e032613000e482c0003003400c90100c1c0c0503c81d54106000c803005c036030b50300c1d5007003940407044054860854640c90041d51000b0030991004201c52190102d580802510122540c101e130382c2601c0c00c0103030598a03801903e142000360040d0400e003a08010009451604001500300c00b84041e0055051605200f81c0d44101c1c0e006401440d5034403000300361419140c400701c0d0001c0d09140d050300514190305041c6081881110140c0c11200040021030581c6e251030b00408800850050080013940c080c0d412940007401440e10340242400160200404611402e040c0d0885400c88019500d4010440040c1c03002c981c00703020601e08404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 341593012 1250 341591762 341591771
    0x5060412140706021b0a080405060904060b0c07050f0103200a170f0105040b1002030306151e09120a020a0308030a0f0504210f17060d02030604050a1703101404 70
    0x2420503054050036009100c1d01006903145145c03480d51a48003100280900c4c80c0d403001070b8070000681d00006541c11a40107440c841e880ea01400d0028018003000d40002c08207aa001c01c100458400000d8104210b40f000c0d594212603100400c011801e8070050110b0b89520441200c0504403665020014060700381a8a0510105254408942407842059030f600e8003180f044001404240743c00e20440c40032180481d820f440ca004a034502a4986c000107000e24480c007029200508401c80030011580019628001c0401030281c80c003ca87e2990800c001a500500003441a0a400321001540120702c03034004045420492440d40c4124590380020305150059846001c540c0b4040c005001c2c00340030324400c0b810300c0320f14403c07840e01c0d00314449649a40b4003000350500a03008046e400c001010003065183c800d00001e0340e1040045605907880344002034140c03150700104410f1240200d02006c189220309050303003594940c204001d4070b034003081d6211038102ca042801045005e2072400040d0172407002400100d07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 341594262 1250 341593012 341593037
    0x7030f110306090a0506090d0f0c02040f151707080c10020f01090f06050f0601080c0a0201091506081b031e010b090a0c0e0103060f0501030506031e101805060412 71
    0x2401c0160948000e5020740c01898044c04010050100075405010030700101608800241e004100c205046a1141400b110218140640d1507580140c0d8403030080c00001d018048000c02d010420011610941171640070011403803207041404202030003114640c20081c01002e907181308210404c90074001080c190701c9400c0601e44a07013000c1c029280380384d0107906521110255410543c068070802886028400c003070b901004030a03130300b080500b0f400036040c0d000320f5250741160b84140e0041a0301203020b41180c04180c00021440b00541299081d10001c03015644507402c1440028040c0480702589941600006101441080075940d1801e004100600106d1001111070118480035000d9510121084c0c0f54140b51a00c035030420403500105000f0321702000850302c1c107207810301501c2c45802014105501c86001c5001590100981418046032010301d041442551510075501e03c81c40c861f80d818941041100300ea0051128003001c60560072401030802540c0f19680c0d10030342e00d902d407500070a0209020124 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 341595512 1250 341594262 341594269
    0x8071704080304060f0b09070f032901090605160b150414070201230c071103100e0d090302240d02070c050f0a08030f0a0201020405060c16061107030f11 67
    0x880c000c5004210180d030781d00309400d01a0586540d64130481c1107900342840390a40d40c951030440366005086180138003400e041940128040c0060800004611078003e2811403030744209104604440001d03210740860f96034a05050350680640710901e0b03080203101e5081c1c00480d4803c1c1910758070080c01090396401d02e10150016040700c0501d042d0b011015494801c00130030715024852500c400003c40540860071000358052a04c205005008240880703010484400f04200e131005091008001000c0d00c2c0e0040c500c01c0d805005050704401040c151080c10b50044203070b80911181420380f5005004218125100b0720002d8511803920301440300107c08000800c40c1d019588090200780344162001032015150104201c030400c20030b00c0091141c0e84e041d008001e5984000200d442e4400340500705921042401001c0c1d00900881c0d00c0140c019600245030b03000743c40e003c100318854003209004004201d8490000300c0e80005915001042903102441c00c0c0041138680d46a4995075200c0c518038180c91440c540407 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 341596762 1250 341595512 341595557
    0xf07051212041a1314150106180b0a0503070509010e03070603140a060828020307150f030603050706030b240c0d02030903030306010f17010e1501020c03060105010807 73
    0x300800542944103100400c01c051882e2855440c039040103034107500b80901461200546113030010a809401d90088030500350512a241807801c50401c440382139a500c1c4000703407804c00f44203043e034070401d90090040b49004040d0203843d900e211684d94982180d17500681510540c2c0401d0b94241804420b0360802e00d182d40421036100039164942c0c010642c03009218805868201c080d1903601210b042120278040d00710009040c00240a0343c50300311240c01c0000c68050100d070190400a50103028a0340089050311040e079452003114a9540e500e85843c03001d079407ca007220142c1c04007d206d03400c694010840c00d442074002c1281c10350000c1a119007504010b83c0da0754040441c5074880a400c00105192440f01800e021008000c8018009145004074200c0040e4a80c8401030140d410f206071101e043c141540703d8121f52107922101c90742e91a40c1d5071103051a52120b0002c56018030042c0b200d440d843c880b54800303c0d1425902402070b00409403a42020015584841c00602100810104140791a0b401310545030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 341598012 1250 341596762 341596777
    0x15071a0c120f1311010302070b0c0d0c020a0206030c1303060c050a09090c0e10030e0a060b010f0207120219090c1d012111070c151706210f070f05090a110f070512 71
    0x10b82a81c4041c0d0bc40006c00750340295400303c0c10354010904000141c2c030b50728112544130100c50308107903442d1812801c803405503030a13400151100d4642422400129000001846440c0f01500d920b111541e484031100259a014111000012050400b4400c9814881351244041e0102c0c1030104003143d041084074540300001e003003038401d80d865041c01002560025074445000e8403a1002c0c10515091031094084140740c0a4000e01800c603042e650300c032207030f03407448440c010303040c1d0134010710980242e800000c05880010b01e0400d84a4803202001c4550740c00380c81d0401101800488110070080214030b40401460306001c181001c00040050304005000f165030708000d455019000c00d000700c0c00da4402080b00060b524801024020b4800740a800d41e030704000111b00410a041b034000da00e00c080c40c0b02d402c002c0d109020010620924074007280509503c2e070b201c0c084c0d56041d240a56a5643c80448105580003810240d058000400c1140d5500c0242c00c01400614098022540104020700d071400d03142c5d0040d034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 341599262 1250 341598012 341598031
    0x1614031603021f0b090103120509060a031407110a020405060a0e2502061e060d0c1202010806030a030504050d0809060d1a0f15071a0c120f1311010302070b 68
    0x1c0e5001c8000c90003e880b240488218207041040c110032074041a40007a041c080a04510f440c1b15550031414840c80844003549005000c403500c0e109181000380c09440045154200f4080400004105c03610440081e0140522030005080884c456001c0c0401010094040c0d40c01038035040020500f103004081240c007032014030307200300751403900c00c4800a04040007900f94411034004500b84200003060610307031151501b001010500c1da07221240011450f08502100410104440d10b00080c1c0340c3c03016000015050007030701c502241c0c1d5586c804040c0c1340c503407110340180491410300c410b00c4141400c4502d60605442141c90500d8901001c0c00141d59420044000910940b01c0c12584004400c0249088401a040d601d0b0b1024281440004a0190090036200b50b48000070401c0c0b014401c3c5110400c1e403101d01c5510641c2c00d030038203038064102540701000091020300803c0100d501140d00aa00a210b0b2100103048051216a9540c16004054180c0600d041603001d20140c5e02048030368400074020660348 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 341600512 1250 341599262 341599273
    0x30712090b0f040b0106020601030c052101060602100e070513021b030705010504060b10090608100f12120908060604090f05100624051204020d0f0303020304020114161403160302 78
    0x20314040104c080c050300490700319001000104000346214584005a9408440d440e20540701c9080ac01e20b94142e6080c5c080441d8240000050380310780114034006d02000e0b101080c00400815024142c0d00da003a0322a280d04100b4a4581a565000071340c080d02001032184241c0301c0f000c29210307540c1c1c43e54001000a8945035035440c1840100a01c40c407030214080300c1904e100711010007109024000100d07a105507014480e40d0070000f50f00300d00c0d000301f45010300b00f2804444c4403184c0740c803482010000d0041045803030700d58407009403800700e005880060488601c4801000f04d0f50381d04003403001a1118100c101c4680c1101012800021000e03c080d100034000b420380028041c2c5058140310044040d240b01c0c056800c01e4840408100364002e048034080d880daa41612a0f40d141c51010a95104400e82c0c040c109040c00c07500d840c1050b50680045006e54000d03030301e020320341c901303008040f0061081401000201c11454081d10025082d00b150310308459444040e0b9041c0034041c00e05420000450300202d0041c1c011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 341601762 1250 341600512 341600521
    0xf05060c0a05061e100b070303090606051305010e0109060b04210602030a0e0106060806030a0b0603120304030504170102252a030b0a1815020f18011211030712090b0f 73
    0x20a4129417260807100d105802038580150310b0030038440c1400240415489504403414495281c10850042c030303018241c0344602400000301c0c402403400380150301c80700c46443d000080c00c80160040b00c1c00e941404500038540b500c1d00c00702302d1220481800c8404203094822110001c034807507201843c42208070040120702801c0c0d00c2d021500311122134000809000320f079010301c041d980b40002e0019000d544000419951740394440081e02c1d000c850b40d1180508031000007044201136100014200321000308500c034015103200c0036030341d090740548001b101154060510a1105400400b0083c02d00c600600858a0924402078980d911607022050006030440707082c0100204142c88240550040984100f080240c45c800c203840010100108013030702d10400001d0000035101e40350304850b040c40e80f461546940faa0080400400c06101f03030001804203542850100100201c0d0150f00460441c40d41c0304c601d10b076105501610f1384040b0350400c0d601e183e51a6591130009010017021401280f26180c00c4400745030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 341603012 1250 341601762 341601811
    0x1b02070e101e050f011718030706090c030b330d0501090302010e0c0d021003110c01090620120105010503150909010f1104030b1303030b041b030f02040f05060c0a0506 73
    0x40c20020503041004c41b01c42c460340c140801d00915041040700310300d09412009080134524500a80d040074114034545496007042100260b03541d404ca9100789410302d041c0c1d13a800c4664900300030140f54104407c0c003d80906442100070840d0f9040500028000b1001400c281c03141821525400411000740c0c5d5958041d20407920100200302c0071100446800c1745100ba01e5000c1100c0764107010840c0180350711034a01c160071007840b0003552100340d14440200030240107400c1402c0941010b076841240d20007610011400d9030080c000700d98011000785811481c0c2d07441e2000468182e4002880241281e6000814908507524042c03150700820000001144020000b511803049840303400300507106a40811003000001d558410321507111100c146c42410003455402c041e0003034501920b9050744a441c1902800004403180e0302040c1d4140c580d03034100b05040482401208030710850088a2414100e04001c001ea40360200090403c5484182960f80f011006e558131440d003601690b503610b030710180784d600040317114 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 341604262 1250 341603012 341603029
    0x20d08160c051c02060a02070b0316030513020d031103160501020d0c1b030302090402120103052103072001200c100501030f0b0916080309041b02070e101e05 69
    0x1004840d4400002a01600f26003220a45000203019000108084200324001d0110700001c3c918503e809980e850f0034140e907421310000c98041c00210f8600070106499520364410355a0f00780c0c0c090010000209151001d03104000c059041c2c0d103c1d807200300310612503e4005c8244040c981d209030005600c03000749200d040180c1e00700b41c070f00383d04200c1400c0d952104407008240060b031140d098200140e8500500b0040b80182c820014410740080c00138000204100c0e00140701c03050305243c00c21141108a11300c618962500c804e813a00c00004403000308810340002c0011460003c5c071600000000c4500304003100d46ca07030724041426600740000114290300c2d42c50042c481d006403040841e41c100a00d604586c1c1c2c401e413140400c9006007040c40301400040c4003c908022280f81c0501803c106c1d0496551080d02c0c56482c4d015400a40c01181442e9800e03807640f1407003055030070300d4000d44c014001c02c50400c0d648a4581c40020710702c080d0091140b00c00217206a03845142a44070554a44a01c00c8506200500c0394a6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 341605512 1250 341604262 341604269
    0x603040c0302030f241018090507060c05100905030d1a0316030b01080105070504091d060c040f05060403080a030b0d06050f06120c0d02060a030906050a0e060702031213020d08160c 79
    0xb002e810704010f003080300340e4001402c7d1030802010501000d00c80400c02c0c01000c40700390040141c4a814008503869420030221142103102310704588464420321880700a072449132000404650003401401035800c40b9820048100c102b0100c6101040c0c560307000280b501c03030b21040b04c00054602000502c00d001012092a0140c18580d00030f21441c05c024000802501c1944940d90070640c0d1001d01c1c01c1e880c00101c8030800e100007040d0454519041040c102c0d4003a6000703201c0c0285200d1701c2c00000074030303050850940e000c503a003092000e800c00d040340380d080c0d0143c10014100c5610910080d4004e0000c0c0c402d100b254094040c848111101e41b40c0401800500c04081500387c502e13900103a644002d40d0307110290036914942c1078800030b1315200000e00640180c141c40d07500508550400e01003144281950f40030b5003081c150311088030260b885d042c0080c0e0300d0b84113940c4a4101503a203e000a034401265000c0c201001d4030203020000038074116120210250400800308461000c102c044900340264644040c018 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 341606762 1250 341605512 341605573
    0x3032105041203050c120112170d0e010506030d0c120512070507121b020f210a150c0203030103140c040218090a0c020c12210a021005060f0603040c0302030f 69
    0xd000c1c1b00c1b80703c207249680c144030b6460a4102d0b45015420864a01100e422000082100c1502d51200f02c00e40400b50089001d800c0e4a981b03820009000c03480c0000301d030405003103d42c4981c0900b010030b49500700342130082c207040702c127111080080100700d80c1d0b80000f00e403140450b60350b40c039192801403034035515440a0b51004400c01c0743c1c444c800d182d080741030f50440f4030280c0e0403100f0708280b00901010036602840040c0110542000c89100540a0008600c0145e61442075100c40e010003070182180c0b0840c0c0c0b00030901c80041c0d00074001803000801651040881100320b60444200109150015050364003502d00684007648880300c80b50281840030081e0b030030400c203505c140510300310042d001f9a601c003140e100f140308100603000004581c4003885610303080140058008200810381d6103120b02a070002c0c0ca84001881448003040132100e0520841e80100002810704a008018200f0000035400c094130a0b111050701c0340c1d0000060307504102020b00c41c2880c0d00034041031480a82d040b1180804000080350 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 341608012 1250 341606762 341606767
    0x60c0503190527010903081b04050d080906040306060914010b0d15080d0509030d080105150703051204030909060909020603130309030c0303031a1903032105041203050c 74
    0x128a034400740c1d140114208440c0019040d81c43d940e05841d07184024000003c208a4544802402c1c2019003080c110317540284c07a40701c0180c030381c10b2030740b086003210b061a01d40c1da000a000a00c81c5181c1300c1145507000780078140c11801e00b0034101c005003603940185d2044405c140c0c0e0703010800c8030511034043c540d26001500701c0305413a0761401d03100c125144582d60a1200ca241c1d00d025441100e1032042588010f40040c904503070303c1c1c031b4003120054503960120543d14428440c1c0c80403281840e103d503140c80c3c1a2540900107804a80c0d03c4206680d5075080220201c040c00005c0c004050708010a50a1500c100d000f641d401d0318451400c0e006e58112151030708000407083c01c19071040007603107603a0200c0740c0001074095244008002810201c801403501d8000074030b0743e01032050000906a264218030410b0f580340b001006c0e9500740302c0802201c0d168600211035032000340030042002c04c0c020907080004142e2925954000710003429060211981100d00700d41ca0f440166078001070591500c17800b503100c000e5000313441c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 341609262 1250 341608012 341608021
    0xf031201090b131d0f0303071407110904060207080a180b091c0501230708060f010c1202030421140d090e090a02130b030609210f0702100c060c0503 65
    0x410400c00500703011005a1184203007100024813032481419002c5004c261820402098425502e03079009403440c1c000500403003c620041092882110142c5600000c00340d00031000d8000e200091100902c02e0700c2e2550b081c81a5004648000c006103c40112990795800e02c807400c201a20302502150050840041c05010540003034440e83d0189a40500491140c0c44062003850070343e001d49a04407003400c0008a6a41c05d914103070045112a000d8002503c0f070310f5035655a001404100c80360420070500103000c0ac03041b00041411406844400c101c00c0c0f050f04d140c107484218071b200d0701030191021010810528070600a229070442060300328617022014240003034842e80e00420080d600d0248000210701000491440c080400c51b100c0544c2d40640402c180d0002c144d03003100108850390045005e8001c160000d01c1d00e541c04030b19181588964103440000c0c2d0706e540000c13241030304001e000c00c1032940100000e43c0540e40d00c680c2e6842c3c0244554901003120300c0352a1840c15114880400c00521009000b4031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 341610512 1250 341609262 341609269
    0x203012d050a0605040303030b04020307270504050115030e070b030402010f02031303060501080c01020c0303030a0c02010605090405160e15040b0d1505090f030f0702010813050f031201090b 83
    0x3600c10001001032805803440c11414010412125800554804015070380001d074650803002800881e406a101000071062a20900c800da120440f04000050f050030040654110304000f48050f070034598500c815038607101c0c404202247e10a0700320949030300c00302200580c0580d160045410074600780003c0d014162410703003140700354080500020f040c4910a0b15440501d031080040d10b01076021010358078440f80c0c0da1704041008000a00665009000796021580c80354000a115140c0c2d078006401035140d03668030300046004024000d00282195202c040004903030350b8003848070340250700880242182095a400501142183d9030050540801500820240280564140325402026a000302e1028803140016440300240c2c0c10062a02070007041c541841c2d0250760015106403012030481e0a10604084910350700e0046044110502404010f5140107500c55100c450304010044511442210650303142c0d814019031640510460380301244407129a4642c001060040c65003407020080b20140c600070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 341611762 1250 341610512 341610539
    0xc0504050d020904030507080a23090112050603240a0c080403021207060e0303040c03020108070207050d140f0a030503060a060c05100c020c0a060306030b010915060e060f0d05040213020301 83
    0xb03440350b0203250000d0f0034107014404884c07000b540651000c0d0385400d091000b0300394010ba201144a01e402603400048581071a00844508480585951802100c07000b5034201600009241a415000d0030315111210100004d804d03c07480c0740c0900241062804005003811100304142c050308000170f147c24040825004a28810004450408aa500c0d145424000701500720500916000d200c000200b10a2000200000e810b0f68402d0781d860116458422040741c0d03904d400d00625500c00750341c00f103410000d44014484150340e80c096041c0c0e43c002e07032994481400c00040c00320590101e0b000004004648c40d00d1800741000c3d00c1d50781000108445140c481030340e074642082c0c841c40c84503902d40310441980d008010a540b0390b04001c0440d1005511303070340010003a0603607120864101801c8000460031351158080c81c00a442d18044000c1114a8040200c0711038170b007400c00a401400c1002900304201d03003035006060070400c1c5480410035003410b10503c1101c050715480341290714070500050241c1c4070390800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 341613012 1250 341611762 341611789
    0x1e210b1018051c17041a07330b0109030b061003060e090a0605090304060507020d060f0f06140f010f110c03010c110f1902040507051204050708010c050405 68
    0x145000180704018446128841580003540c1c00300c44000091081e88003040900c0030588500ca800310000c3d4068807a1010780628012101101c5502440e1070079140341d4070181c1070740360141c4c01e07200c2c941511144000c203290100b02c070355203100031703803500030914440c1401000100070003803038403809043c44c64454000861019100c075108809104c0707025086803007904100c0240820152426a90904d03101241c0d50ba00290307411070b180d40c1042e0009084036008070596040312172644a461800d0307801d03800c1007107925039030384100d0f00c903640c1e4081000065054402c14107849210a8009955806c09034030b2440f4000c0382150a1003012603420702d030001c0e40c0c81429154011a1800d0440801e6420140e00f414480102e141d150192301c1c2513071140a20b40d0011000c0020a1044207031101c03c041d1119640e194442c0d80002400302210403034250040c109a880310368440b2092603c1c500309988490402080001507400781c540b9440f1800601c440a028462002d07440720314107185140a1510001c110403030710020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 341614262 1250 341613012 341613017
    0x803010509131202010e0f01060b0f0703020712080d0e160e0a0b041103040b060307061d130e070501080711070e0402040902030303130c060c031209031e210b10 70
    0x40114402028200b000c0002c80d42c01403100700d40c1148040e00a009101840020320340c0e118211f1402d902c000306208513001d070790016a003940351090803403021444e03600190003101140304182001840c025001d01a0103560300c915483c40d0f880340810003040580d80880c54010b0a6045100f01e06951000e21b12010100e4a103000c0000c0c56944410130003009003112140e150b00103080515400d07070620010001c5210b68810155158136440301400d0580c1c60840740900800f00b05240d9120705d40c45600500405901c000030280540c3c041c205104809a8500c0c031a15480d6602040c018415903800c0700c04140d000103d89041070030526121481d41d6079400354403070340b5501030040001c20150344403500070b01c0f010364002d030450782c3e00d0a0000b120000110112400d50707000d101c400002c03d0b050720618106c0e44264042d981c0d20460090494048020050114120184100004210350007000304004258501c0340703841d8410440c040314103562000d50400e9070340d0662490b00d850328090b9961860261000712661 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 341615512 1250 341614262 341614279
    0x1081002090607060c020c0409060207021005030c0711190b0a020f0303070203160804030212150c070209041b0e07050a020105100b0f1c0501032010140702060f12041a0408030105 78
    0x10301741079041050201c010b507002420030910a09009c890340007080c015209940f180d12988800700b0494580c0030946442841c0d41003040101d0120f41d50846400c000e110090050507201000c0e01c401c1021400e07a441210b0b04600401c0202c110b94050011800c41048031002e18514901310000035102e1107440304882806000252000910100d4829078003d1a03001c1c1c03172585110007443d10940c5e40c042e10105407800a8003500020009002d20040d641116400b8080b0603464440360b5800d8900819031011000310070161a00240c1c40c2045c10310203000b504107490303055550540c554002e00703551005100e49090042c6a208001c0078541d1411100c05e4070a032200c0540368800300b00c070010403455040c00c92000509050000c411302605c140207900441c0300030011081e441c90403060100d014612076004020844401000300341b50f0b00c010040801c1e6200614070b9140681e03804010440d81c0103040400d880a040303904101c20050901d128605080002040480902d029076820b0b6140c072050041070b000e08000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 341616762 1250 341615512 341615531
    0x3040303080f07030b1f020c10050c28120c06141609030503070b0c040b1c0b04051504050903070b010e070806030703170702060c01020705060406150605030105040c09080708060108100209060706 85
    0x1d1000c900d41d6031000380a09c0203540e65020040154000c0e200191850041c0c40d0081004140007642c12250000c421310340c0d181d07030312540b16094110014151a0b080c01078580c041d00020314688a1a040e85440c2c0440c1051404e142d10740d083c821001c245e54409000961105101003403001042c0c07441543e00c806e59580320f5aa446502c034180c000c2e0b034815226460042007a14510a82d114082c46040c0d03d00001c100e65001c2c01c00b00016500180c035404101100c92141403010b0400e80c1289500c099981d0481e0707e0040c0725942e1105000c401d0380070159421000e0180800c15504c6854032340c000d1402ca005010240c00c541741c1600c690141c00c0700c45a0410001960811511090207440b0054124002107450b40d0145c10019216002100d04944841c60f000c48009004004226001958400d13510a03045a0038542488014a00c1d500c8107424810000000101880b080020101074980b04024100651420410070b1034000001c100b20309943c01030141b031420b034031000195541207421040100d1114034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 341618012 1250 341616762 341616767
    0x12150e03090d06091e050109060506041e050a0b121c02011506030519050c0a1101180204090804050a15140a08041e2018011d09010e03040303080f07030b1f 68
    0xd0000c000c0d5020707600d00043c806e0100651000d9042400f03004140101c0c2c1e104400c000441d840a8a1907607440d01d06603049104030b01e694444da900035220000010060000000200c4280604000c0c4181c1d50100a500d0411000301d50740c0d407203c40841c0003c3c8031506502c0701c2e40c1103010341c60240508055aa000003072000c29086014408034410350700c00c1205081c080c1020015910042c041c0d00460f011181403a51520140b08401c40540603800c41042c40d03040e5801c200c00b41c02091025280b540701070002241d5641c030f2041c1c0302c000785840310f405a41c80700c910714081c04031a20580702e0750444e101030103480d4545400040442e4800c0e840322056001c1d103400451b03d0720b0302012071000f800700c01d5040a00c0401c041c19000c03840c214081207540840e6400c29004d880c29107202402461418002d0303203082080301903280c2846402250351030001c940b03400c12403c5146540c0055000390b00088441082c03080d142280485240c001400342350510440c200749000c140310f0501200c2e190302001d0089540c60100740b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 341619262 1250 341618012 341618033
    0x10b070602210f06090423120c0d0f0c05150a0e06011502070504150b03061c0506060405090c150d0f060314151b1312150e03090d0609 59
    0x282d000c8940342854681c405501c10941e411905000036980600c0825000e18001030102c0c412940310004140700c400c102d035104070381049140d20900600c84c401f048520318040a000e040240344003001000c10381841e84000380110840e41d60b030301c00d00c80302c400300c4004a4004550042001c0e1125104000f40d180d40050303030000c1c058017540017418000c1400214483c03404c07510800104029500300d41140351280208001c8402c641c3d400b03d40c8000e0003400301301142c00071000e55403014004000b00c94114280108801d132119940c81115581c20440c04c1220b280707081c1c0319258011164100800c0340815042c0456a00748019550620401c400b0810300000c402c7c17500031428000380440d041c41130a50328a0103510001034010741104902800107642840303121712840900c00c3c1d0304102001601c204420445465030b02440441c1d004001c019808206241444070709580f1a1181c002c401a0108030700d451801c50b91000c03109100d603001000340360529030b9505c44401c5500d800c2000020040502d1900301000c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 341620512 1250 341619262 341619277
    0xc0607020d0813031203020a050301030215130306020c10180b100504090b0f0601170103260307080709080c0102030a050d090b0405030c0106060206010510050a020106090e030d0609050708010b070602 87
    0x1e10340028040c0d209900703c080b1108680c032034048904c00e00036034132007501039024a080d0600000c80a00042000d49440082030b44260448030382a0b280005101d03d9130340e4100c0c0c42d0010f642d1107800050060212408009102659040c0b8030104003040da11009004901c11103c00900f4001c0c4c001c010030011881205254006c080040003002081410300e480f141c19502240e4180e10b0702e10450000e640365005a01010700a4807461500a86d0381c02d6640fa07003c00c1480e1805000c80b6031202c418440c660400c0390095024190980312001a403500480007001450542c2001c140d50700480220440c81e60000243d41d561406420420340b14044215088010b10040c8006003034840c902c0e0a20080c084048001c14590b100c1d8802801083d4580f40142d0ba101020310070181c01007081d80907028010f110f6000360a542d1140d03c00801c030150380b808039405440c420f84c00040c0d6a000012003201e0b9801c40d10540b801030814800078042071418240c040c011103014854070001000000e104d400300042070b4101e5a14 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 341621762 1250 341620512 341620523
    0x20109180f06140a0509040b040803090a0606260a030504120503190c031710060c02030c10020606101803020103180c03031701081f0c180b13170c0607020d 68
    0x2096030b10f04074424508220b0412500542d80000003160314103141d041070780f003150894412440c50305d0f20350390403501307510013404480507014492924000501c030b0b00070100107154003420f405528031064a40304003422482c80201d2182c2c860000d0200082d00241a1400c80d400ba00003001008000c0c01e04505501c284003003c000c3c03043c1011454091030308502d035480218065030381c2c440d10302002100345003c000291400302c0c440c605100c00300290341c40354800501141c8081d09031010808503002181a1010300794000015800142c100501401c000544030398460746d40c640140b01d90150140b040780e1741914040a41016220303080d4603030050040c807a4150041e030000c0180104d65503801c3c018048000c103410301103c00b9404000084a203000a0000443c0c0c0c40c0c0817650f4035a0310021554002050035079450000e00122130203020300e101440c01c03100d0080010b514100c0e80d821003d6104600c3d1509a0009046c0210314510301c0c03003e1000044601d0a2441a900f050340c50040d800020854011365000030203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 341623012 1250 341621762 341621771
    0x906061c0c1101150f0819021011160303081005090f0405030c0f06010302010e0433080a1410050c03010b0a1407150609050c09040f0e0118051603020109180f 69
    0x39000c13003c55039a4111808100d046403015221041162124002d541d41460b00880441c40000340c60f08610040514201e41407281c0c0c11003500038100c0c18124924140701101c0c251082c10400d041d0410308560f8090f0364080e01c1803060b82800c00040d03c8503000352141640480707440c000f5040240420860744488074080480718600080c5085a50743c0200b404204c0c00038a540d4291a42ca0a250050005501406914010500681c076030400105009035040301d41008450700002d5100092168501c068014007050b400c0701e000e110890310706010000741e00c248602d070104108404c0103020640e415115001285a0340c0d401e40d0b00210342c403480305082c1403280034001481b082008049650500d46010038101488134503a00e18512080703400c00c85180c0890241045007441d40c1c6040d070301100d0081084003002454446500d04503007112070088002c2e9a00301f42024076001d024081109281e6441c510a14024550556000900381c1b10b003072045000d264443c0d60040445141a007184c980101007500410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 341624262 1250 341623012 341623031
    0xd0906091a1c060e012111040209040f06120b0c04060c0b040302070e0f011d0106020d0f02122a0f120901030b0310020315010804081210030c0f050906061c0c1101 71
    0x31440d0000e100e50740496403000030b1011740348401c50740c14450b47c1d00030192680b400c8040040c40081d40c003c28040d54410360355440200f010280f44a110058001041280000307452494a000d683d103002d0300443c0c4410040c4410403180394403910060f15541e0080003c03401d41c40d1480e003a440d0000c9500030400700502101000301c00c020001840d0f0481c1c4061000910801d1384044a0045a00038025480181c0058481c0c0c0107860141144d101c2e03020f46481141c07490a070091095599422645110614400140c001c1103c0b001d0b81b04480180000b0b000505142c600c22000d140c1d503040804c140000c121408601403400e40e000b58072010b2000c2d00a016900d5105500459000a60040321001006030f55a42c001c0c1d03480d4850000544201d9000400034907000c4105005c070310405008005090310041500040300180e4600190b100130003441c40741c0b1103201d08040810002800081c101c82c010b030702c140721042250b01c524007408207140d55030300d0024035556421b81c02c075408280200311126941c280300208 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 341625512 1250 341624262 341624279
    0xe0a03120504080303040f0215130b2109010b210604031d0d12090807030816050f03070f020a05090f04060506130c080906060f0907030e010b0409050d0906091a1c06 72
    0x10840d4900c03c072507000c1c03009c900988405107400b91503030411a04101d81b000303108903031450000b40308107520008182c3e8a80c1c0540002d43d00b680088403c40410703511003900006030f003030401c2d0424007801584411042055811000c40d510680204050100001210940304510302c9058120400c02c02500c607041160b03403070500c41a05805030750303100f001802040000541c400301080100036298043d201c1480c04079243d00f03480c0d0306219076a064a050081c5034034001300c0075003000280b00c6d50f4851940c0520751b03140ea0040000b080c44035072100e0300030346180040002c1010a18071150740300380c0c0300c2c2000900e80c40702004250880030131841c00c8010383c0740030000605260441100c51141d1040c104a91056031401d0074020740c0701c14145941d800001040c0070418460094110301208103003400001000c0080340001410703541a01420307500c50308103858a41c1e0450340300b80d0381d0028100e01d00b04072142d0751801c07a11041551442c00e01c9140c144012584290300c40e035159045040d041e0344481440380d903850b007104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 341626762 1250 341625512 341625533
    0x30306030606030b0f0606041d0603070e0f240d0f030e091f0b0f03061e0d1a0f01030c290318100c020d11030c0703120905010e0a0312050408030304 65
    0x24020304085ca00000741342c0d85850030031101501d600d8140032001710340c4001c25205500002d4022581070141c200c01045142240c02e080b44600702c491074900d07140c02c5c04100e00c0e503211401140661265080b4100c0d10082e200c1400382001c1c103074400c10714039003020b642c10125150385034000010b40c0822000188008055400b00021543c54088425492150703510302030b41161080c10383c000c1070044e084c000200d043ca0018500c1c0c040921007a810035100b031541002410b00804000222080501968030000d002411400c866015110480320300007541561100148001c10f0711900c01100e02c0440c030f2020500c0c0704407a0200355120800407544a00b094800c1a070f440381e0320700520403140304008008540c151107009091501042d03401915102c0200c10003290f183e00d42c000304a866101c100007202442e0010400900114081e12a003400400325450003010705101d9403106042045402c4400050b03641c003417901c0308482e800036842907107400c0b80030140e030306000d141d0114401d03000c003008202c14086010070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 341628012 1250 341626762 341626771
    0x3210515040f02090306010303031808030108010c0f1704060c0201020408120405032104120c0b0304062405090f1305070305031c1107020f150d0608070510080c07030306030606030b 79
    0x80a2144081c261400b40890040300110380e8994800c030010000300b40254072030a800c24402c01c502001c2e515a8450180c1d650085c1e1140310785a5444c0920442c15501200c090040c0d0072500c1e121041c03640c1d8140b05400b5140240001c1e06160b0348029002031a4004d60441c0c0040000b0010f840c41c0d81c0f05124958219007103441018000d028508010900071008200e5a91465110301d030f10b070816003441c110701b40d40e1071070403422107200d601414007040100c480c0c400f8501c2280306d02d8001c618004060402001d1b541c40703448002c680001560280a00c0d40c8031010141d11843d018089d8003140c0e43c24107196043c11440c03502a000b07004031a000b0091040110060161107441c6001c01e60200a144204044944d89200030340141d005201080040c60004c10800ca081c00051040350b07520b80d4085286940d031b100c080ca42c68980d07913a0301c00700090039081c0000700c010401200d0340b899010a0749c00140110320010082c0c001003100203003110425000e0b90001025681100040204540703e11307104188040946 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 341629262 1250 341628012 341628019
    0x903101a030a0c090e0102030f01060e010509310b060d020d140108030403140a021003020a1202040b0a09090b1c03051309050a0b030f1c09080a0308011a0403030c03210515 75
    0x18117822200c805008581c0a0201103050003200d80c6407140455a030788501c04800d0401c8000c0081d0015030b0b0b24810400908512200c1c509840c55022020792000f200080017881d200e414800084001c2d6a0300703003074580311009104013503916004046048014031000784260700e1707000c003003001040144d030000242c03080d603100398000b0002380f0306502042e0392440c5195000b58054143c440031100a40b00350098404c103280da0500d43d0b43c0c10112040c010590308a42c0102c0403010380819074004003035200c0300381c90090000c0d9004000c031028a03c04241421103170543c020700203805802d03000030580300b0400c0301d14048840307061000c465101e0042d240509402e0b24018005030608202810743d150224210a45140310002402401512002c0b5200c80281800b44810701000313840004211005000c1c445501e40300f55079440311581006051a07204441680d002803034602484203000117031b08001103c0c0c0c06a003604011410528800440800b1282c1180e010030700390615051202c02402003108480240045 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 341630512 1250 341629262 341629271
    0x130302180709120809120c030703080d0605090c0304061104080105040506040314090904060e0a0501020d240b090108060409021002010c023003100302060c0706080a020903101a030a0c09 81
    0x5580028145010340f0011301035510400485c4d5503440c0010414050740c0c020420b541e414260f00300080c1c20240740382d0003543d105c2400a050f003000c1c0442e10400d4043c09044034640900d0070541d044a80034000200001c007419514818264079440000c20f95008140380702c002c0c4114030f40342c58000c1d1035142c180d4086002c0386000345025280d0044805444008501038082d40035641c039501c40201410f608501107440340501d05c1083c02158080c0000c150500c66054003081c0110b41e0980d1401c806e030704035040c04402018001c107000d01d0301c07010202c2d802c041092801c000b00e600e89000050040c0380f88240250701462005201450399019004151072034900d40a40c0c0e0360700c881c00c7c03c05414a051603c4110095200e8908400708807041c8050740d000300480c40001a00350303d070307804500c065201d40c3d0110881da204a004001c91503200350030660104615a003541891000404030350755a424400f04e080c40c1d519800303120b000342c0001c0e07555407804500030103c44c01040d40342040358924030701c3d00850b030030385040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 341631762 1250 341630512 341630519
    0x1110d090804080d231804050621071a04150302090411030a140601030b0f0d08040f180501050604320406151403070c030804060f02030c0306040b03070b030c130302180709 75
    0x4a80a603411040c1480c0c00c0329072011b110742008002e00004241c541d01c841d00c42c144204500c00c60031501f2064030700c0002804018104030440141c07504401c080703000c50100f08010700c03000f5240c03080e41c0784014090601685482407030700010090300e0141b81d04840310b4004820402100c00c0384e040760302041501401c0b031006d625502c0044083d80d006000341c542164248095243d11b0034071a2450482d54002d226032424551100b0a140e07a820703465025880c5080001803013610f040780c0f48501801001e0840e4003e01d0b00340b80c0b01407030303400241c01000224290711600c40440f00e000d884550f000740d10401002080070540360084001c61850192580740003030701130302005203100504402c480c0a166540c0354000c02d00c010ba60119041c03000144111f5401ea1542c90200310701c035017400030f1030081100d140e045440c0c0c07400000784011501e10b440010f2083c3d012403000c010482c0d4000c1181e4000030b000c4c0307c40d0759401070490000d5000803035600094016500b000180441c0c034030008524000c410b035a6442c40c50035507 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 341633012 1250 341631762 341631827
    0x1a01090506031306090506040f0b011205060433050108010b0909121e13050114030403090b03060f03070e010f0b0316080604091a0f0901110d090804080d 67
    0x864000d0315004241040801c1e495404600100a5288500008100e00c0c1141d85c031581003407010f54084409030f0049181d9001c000d44408228050139210048004401d015200c1c680c1e944400341010f00000090040f601c00c41c08000010042d00d0005c03003094091101003242180105424450b044255207041d10a4030940b030021841c6028042d210300500620300e510402c09500e40c00084041320310611110b0200c0039040d86405030201da12000007100c081e5150a0000d48400c000341403900404101308104030000341c00c034040c1e50644000c115403a89a40e10030700401c0c886403000510980c103114400e0001000244008054165040009510650341d9501c20041c3e613030109480141100440747c1800038594130508440707611110060011544041c540c03500380e1000391140303800714801c404400308803071000c0e880d0040350881e140200822143c00000d403107110500a8000c0c015844d512003809105005108080c2ca0181c03030080181c4440f40115500540703d284051b040b032807440a061018082d204 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 341634262 1250 341633012 341633027
    0x60103020a052709011205010606050703171b070b160903030807030b0a0f080604061401062f03030115140f0301030b0a110d0207030305090109050c100210020703031a01 74
    0x1070300e6103509041ca0000400903512141d0159100684074025203e000140d56003444e043c002c4c400c02284075650512810b01c0c500b5100c494100a0620108112903400203500408503184184016100201c0741c5800da201440501124100302410402150a405000ca845511070140742440e0802c4a400c480020a6480d0b006611000d03011802071400076140900031742003500000c0c0020080c90701541c59401c0109100443c1d0810b0080b41d0210f800c00080003034030b110340c58020301140507109643d032410704001c1c04800303d035031929001c4031422034001041201d41541611b05c1c2c42e003400c0e691290785482c03004e450700c4103010041c00024101440103805880e48400c0310520541012000e1031a821030b103d480001c440034103031030391340356407609400200110080039010040701d151015a942e500e0782801000e070742000d02001480d0340f5000002000950006009214110590340b41c4041c070b06d850000d9051210740c2c0104102c0500001d4007908047c3e050b8050607014488550aa10b020b07103202c011590035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 341635512 1250 341634262 341634277
    0x20a110d0206070503091f0501030201081302090601050c280506010603020f03060f060c070605132309042d0c09020a09091a0607080c011413110a0e1e06010302 70
    0x6800070000708900511460040d0ba0006d140421511400120600480710f481210641c800c4a6511170040c011581c0c4044202c0e003000e03102d545500c00711542d40015405200180c1071506000001a03900754841092060028000100200002c5440c03d424100301d4183c107030b44c00f16aa40035010011900c117010b80700703599901c032507062040c2c2942d80d0501849a0710344a5000698004818801030017100c0f810002d10000d081103070741d515200c2d080c0041107582c14034642c0103007074104984101081401e990b8140b02d21021400c5a0050700d41e1203d051954142200c0f40780075500441045071480e100c1c00c1c080220a0b441d120318607001e48256550381d5103003207000e00580c0383c000a45e040f2003085902c0d2710783c00691840c440b001501d00901012400241d065010400407100d50601182c0c0d1044000284142c140e0b1455030b04441200d8906070412402c01075030420001c1c4103550300c01840c07000d52a808028405090840c0d01a0f00500308a07050710b80c440244010b807101800c2000000d540c9501c2030082e00d014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 341636762 1250 341635512 341635517
    0x3210f110607031505040507021b0a180b1c03080f06010302180d05030d02120603160f06050c0102040e180d020c01090e09161206051f030816050d0201020a110d 70
    0x41c0d440710340e030890260100c1845440802d00305407000c54035039501d1145500407100c0c0d8008001d00004903104155855600c0d5006200e40b600304002c1118001d00d140d11008001400300015601c0c0600e0000f0745025401c02c3d1945600c0c03503401c1c2d11810180c210141e00e01071813414011000540d60000110140d2040f107141101e80c080c55808020582010326108441c9880b541c01d803030901c9190884541207801072180c0a0f50000392500340083d5040a0025080900c0429842650141044590f4011046502c07500e0100440001c004d2402402035054030003030f0a6640000600e8203050201250b038071105120054603000e00084440e090f8000105c49a003081d040e11900c2160b454070040301d4240320000e100c501140120030b010f500c00d9000300c440b070000c1d1400c1c0c01d100034100840d0a040d0100c41d002040307030308032000c8030582101040c9085c035414202ea030711400240d0307101e203030321491429100c030a03400401c14465a900c0c0551182c064014000d940050740e13500d000d0b1418400f00680e10102048040003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 341638012 1250 341636762 341636773
    0x201050a0b150c0f01050a1509020c030909070e031506120606011b1a16020d050313140102070f0602090411031620070b1306021b100903210f11 63
    0x50807440b080252192003584420740b022901c0c80c650890030b42d4811100b1040310366844010902c905002c0f1803c0003d020072041c210b041142040d080e990300d200311307a10284588070705000a9811032003445d8554088a0241c155904406800981d00382c082c07007592018400c4001c00510744100c0000103006219980507500d00c4290011204a800001e4848c2000d4402a5881e1801140c07943c047c0300207806510010000c041f813201940c0000d0400c440a20341000300403042040c441e6046a04194102c25034000103445018502c183e81c0c1402031140e510010551f0303c200d8000828890b003076001d010348d004203940034040c6550410100381c43c0d01c8110352481d1a01440b0f41586086403150465160960322075150041050a880001e0f00d06110f95004014030390700081c107511005828010341c00104502d000521244c0c0b50b0b68001024182c0000c9131310f0096040c110364440c4c1a2181d4000b40055802170303010408111800d1098410114207614038000c1038010078030002a500c40c01d54420720004075005031a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 341639262 1250 341638012 341638039
    0x30e01030614090a0b131506140c0c06090a1d0604181a0406060b042d0608040314221409010b070f05010212090309030106060e0604030b060a150f0201050a0b 69
    0xd008080004449401000f0400151501c106c0c510802c00c0c1551407034072100030300c0c0c40d201008152034400d07085168504c405015070405500d0000e10170207000360485102d6202c81010300071400b1099554056020308442903140410700c0d07004a6824041c4001399001e1102c4001584c840d104100303080c000518200800e00c000302c11850b452100da81151040c80301064031560f401740c01c90305030015040500c0002820141580d180504d82004000300c0c01181040036242c6880400303401444010405024081c55082c881c02443c40707042245d6030729040b00541d10f903014250038508001e1609001c1c0301e800c1030003061100308620306072105c7c40c1242d925207545407801e01c083e544e000e61768090a00c00c9481d503400740301c1d000c240710042c010700303106120b000021610340048001f01420364000b03a01c0203007881a1441120215103a840445082c3c81d00030703080d20740c43d40700c6a010950340c0d2242c4d4002d000780c4030300d1425560300c1584002c00c0030340031002e035000b40180e48851900400712003481100300d034003460010404 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 341640512 1250 341639262 341639281
    0x601021c030e1e160503061605070501060905010b0d060e13200303070609050606010806150c120f071407050303190201021606020c0f03090d0b090a05010207030e0103061409 76
    0x14000ca0a414054615140584000080c0807400f01d9032a0b4180d045a840c030180c1c02c0c511444000208400c0700104518240078500420f14902e8041d011300300000000c0f22000e000007500b04400410384031008000c55030b56003903583c8040d0080300d8212a203d0030080700251604040d1a454000c01c01c0380c00c0d81c960b0042941c0e455152052240d007282d1005942c0c20b548555a90078409452b005025100124180e4000e00d041130130b0000c010030032418881d40c0300600c8170b0703901c03095100300304030155048032641d03036800503c00b514205801c0c0d1041102e145c0090701d00c1c001e549010107420384602c18495428003100d8032900c40d4a82035280112500f6030b000b40000b4281e100d200200903078010301400010b01e407203000b1014041e005e0a2070020703208150001040d400200c4c007040750001100341100998181810b02000a2418502d40c81c00740c00c01c6103c10221746901000d12000c500a64003000071592500740349005042150900b4400707001c2840c1210004409200102d121281d420007018042c0d56a10705e0341c1c9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 341641762 1250 341640512 341640521
    0xa0302100e12071e0e043203190206070206041e2d0201020705010c020603060d0809060a0e0109240f03020915030f060607050a060b270403080601021c03 67
    0x981d64080c0c1c00a6000b0301410092226401070500d10070f21080350041884c5541120030703c2e900114a0140607402c01010406a000243c00302c49401c550012008601c0c2405e00786d8002c0924100d580e000000c0c10f580c40f45541030b0558a092403580a60341282d0316604181e031075000c111000f8000a0344005400350000e4400c5a0f40500c82c070642080d41c440c1d50000743ea85050ba8010412300d29951040789401c1990b03010801200200307030034030386080d542d000c070740c0818007900000c1c0040e03004000c1100b503001001416420350300c021001a0180d901c174058920020040340b103148442c2c0c0440c01500010079114940200012840001c41c2000c80c40011070004071031407442c08a00904141d03091014a002d9941ca02044102c811030402c0c9644a0815410701e0100c0316000d000c03503104000401c04000011000310316005400d0700010000340c50300100c0041070410702c0d100807881005650b0312041c2030b4444508441d60140e40a41d0b1040d04a503602001a071341d4242800440c03001e803130540d55002089109821 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 341643012 1250 341641762 341641787
    0x303090307030b062e02010e0304180b030f01020f19031119110613061401030224042c0a0b091b0706020c010605030622080a030b030f010f0b0a030210 66
    0x940b00005c03039500b11320880710000c8144100e0a24010301c0c01078040c0d424091907410303681c040c01443c41c20b0702d400404031303880031010b8916109030344440f44040030740d405010000c41d00c400d81e0002d654488000d460300c805540803e007040886880e109212440394403a116a400000628030304520b85985089d5a18840e20400d01600402000d480c16424480381480140d004000e0302100b0340104c21540750510030303248509540d4104464000c0104056a6041c504000412002e440c01c80050501c0c40080800e02c00c5030006007030014682c00b41d02403214400c0b44002c2d0048100030740710294590000d80020b540f030501c1900c1d8010304000c00f140c600d901c0340310b0a118a00b2050300e09444c141107503440100340d800c8010765041c20f940d120000c1141d0308040c450194484010300c520580300b07448180150030035035007880151034058003048507a880f50181d804084251401000c460200400d421074a0107002058104050542844440c0701c0504141c421b0b0016030394000d01c4001950011601141d0080b00d03080c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 341644262 1250 341643012 341643019
    0x50c07050d0f02151c0506210717100b09060a05060f12040510110f0708030a06031e020321090603060d0b041101080f0411010c06060815010905060303090307030b06 72
    0x4141d10059840710048054405070181e215119440507090305400d810445c4400091402c0c03008110b056034035080940e00f01107000000255440400c0c0701c403032510350310340c000c0c0709854603a1240da40d0549000401072045071502d5030600148102d101800b0210340107484540c2c2002600030140300354500480504605801d1140d082e080110752050440c018200755802c2c0e0b0a41c12418610007011100c3c0547d0500000e07118115141540e00e01a0480030310815002600c840404404520b1440300c075040480215004034a100c90b0401001100c0d101c0805400c0892091044c01d0007003010700b0158081c4181d540811484604000c1000309000c4075a000030401d50780314152010321070001e0180101140030b1401444910040f034510000900131450280005002d440302d601000001a02956804c3c0300074020310340205104041e14159000e8101904030b5a0a030040c8120365010300018074040c0d04071202d011044c03041d502c40348181078691003802c0803582c0541284009101081c404901f40d40c1240c0040c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 341645512 1250 341644262 341644283
    0x2f1201061b120e04090f1505010e240d030f0206010f0602030a230708180d0b1f0509090c010201110c03270301050709050315091e1501081c050c07050d 66
    0x1400084c100c3d01c01220480704404000903038028410f010007a01c11200102d0320030000d55041544402465400410302c084010250140100150342d1003400c41c807014001d000c00d0070460a034900506a00000c0c2038a07401032040c0d000000d040281003500008541e0f80340c002c0c51400030f040705c0407501c45240611590341c0e5401c41c48100b0108040c040100b06450082d411651209101c078009a0410f091070901b9120364034035140300001c5620001259003000d04d4009a0700b80c81c1c516815510200c80c640e11003940038405400b003180743c01000c80ca01c0e0f10407400340d008000489140d407102c0858040c3c009100c1e460b0303100f80440c486c0c08141640004410841800b2643c80c400340310b0010342034400441e0320030002224000100701c2801c08112030400b5414482d0003120b00c0c5005114036940d00b40130020410012600030701880507020a02030f0149501200c10b60f05900d41e141d90510703035240710255085140c0034004200800491207141070700d54032a0410054950185070404000c4010500c01c0e0a6030401c042 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 341646762 1250 341645512 341645537
    0xd1817011826120a0c11010509031305060301120602091908031e031e0c1605010c170f07030207060b0616060515132f1201061b12 57
    0x40703000c4003201d00d00c901c451844841c103a81d0079081c001e800c410004904402441407038003030904101100e0b80104e0000340019000040c2204484d0101c3c01007580c0055440c0405100c080c1c00088004c2240d0349944e140d0b104040d9690301404921701c030074811301c21513229180002002030032a4004000010008101d045942c2a02c00000498130f02540581c00503800044d03004202e061090022411100d005910b90640c070702501d071040307502c5103a102d52940c08000000655486199400d40c0c0c01401040d003000d203581030900e001d48c000e000c1c2e118810045026114071300c4000115404892143d801c24580b0503440e160b00c20b041e4003a4001d0042203c0d0b5070f858502100c015155800030b003540c12902c2028140500301c5081040032180060040c0c022070440ca10726a4854440c0c401500074221000f40000d880890304847c00e10055031f8185a408004180302d042402d050344402400000d2130850302c1643c40d9984040c103030f900032004d00c0ca040c01517602c1c1c0c2900010031454040280703001c8660030540700c80881c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 341648012 1250 341646762 341646791
    0x11100c0c0b161704020d0210021f0614060a0912050309060a02010f1104050f01080a0603120203040303020114060d030c030201060b13030c0b120103020603100b0712020d181701 77
    0x88403448903014007035640442c00b50744030a114034611943c020716185400c1903000b0441d59641040040c0c0a404420101c091203031007044030410410208612055400000042070f001d04198816140606080020b600340352500300d045441074042c3c2d0f1902e64440e407a12840080e108804a0140d549000500c40c544031915440003c0400202c540c1c00042ca102540c3c11310002c6401d191010f40001800303200500c1592036504200944803000d0800c603120b507640c00500b4001d4605034000800186003000c0020f50f0ba0b400002074020f4a02c41d4000b40f0181ca4001111900c50310212110b9034003180c1c80b54403d002c039000b080c24910f0280244004149240c13504c44150007580070b070011860130361181400f0411300000860030400740400181451501c0380055020341e4085043c00064460000000800e5002c504110b10800812003803002d69201c540f1424a80c016440303110031070303002d4059810b480e480684205038401030018032240e05801c3c2400d100714039401c1c1650030489031256680317000c0c0c5070f00c111 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 341649262 1250 341648012 341648033
    0x1701060305030a0525260f0d020327070302040f18110a0914010b0c1005070309060e0d140d021201031101090e09031c020f070308011511100c0c 63
    0xb00d050710f0f03590340c40350802000d003404441c050310b00749017020306a011800980c0d414107071040c03044019091016000c2ca0603002003a40f2031024608500740340001d034101c801180350041d61060442d08080c10140074045040500e401440420544641054000780b0041c0b88c680d222a005035806200064207089804803101e0002c1d05880681d09140f400c10713034030083e18001c40710402900041005000065a80c00d08214040d418003032920130385004501380304c80300800c10030142902c03050b030418042070803d0b20000d8000d0200c10390640350319040201d0012015000206580d0401a81d92001c98480d9844400800703900149003040920ba001c10980b0030a030103040a05e40654010b40c44400700c10300c20b0380050440e5070542c3c400c02014100e1020841c0f001d5000c4150740494030f140c440c503081d409003a44444001e21400e28060041440801c0c84018994084050390580c0d00e1311241d440d4034529008240c94019140070212196440000700b011800d801e42c01803d082852410803521108044d40ca035075801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 341650512 1250 341649262 341649277
    0x60d0f0605070905210f010b1c1103060403120b1f0e040b03070b090306151e01120e01050a061a040b0906040906080d020c04330b0c070608060a0f170106030503 70
    0x486082c0180545c600d020700c0640410204a0001c1212038003030408500d114900d44241180010070805400c1440404c0404508602005060316001d141900e40504006010140648014a8100c0c40c0e0558102250003080c1811000c3d00c00c03241c0d807201d00d022a104020280c216401c0358842034011804d88040200e0005403076401d0a542d107a0356900241850310400801c51084c4550940322403800d48c070b46400d042c41c6400900c00400450070207500603903c04100050008003280340c100c0b80c451010044d800103008400301c4000303016556440d1400070780e5003100c140c0900000c0701003104000c60200c01d0300400139a0000751403903041640c1c0b4103066080b1612640311818941103601c00304422a03051211602c5107030111001c00162050342881805c144407010001c1d44c1e03440030380302d603541380740c60307010400c024000245125035610494800c0d070384440782d07446400302059031000030078041d182100b100030503a1340440762044481d15204507040195410840080706544e20000400409d0381400201482c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 341651762 1250 341650512 341650549
    0x305040b1c020a090815130201110a05030435070510170705070314030403120c031407050c010e070b0919030c091d0d020a030e1c0c0806060d0f0605070905 68
    0x9240c1450f45040100011b080c10641001c0003c0080001103681c0708200c098080c038101c5094030246030168500101c07a80003611620003c140001c48000c00880050200c04e107900075141c40340d41d0321180d90440c030380d80401402600120001d0101f420300c031740c4803101e940440c03801030144407100d4030a100b0320805489420000e440094004145038000c010404410b0b03200d861035103103280903100204802c042041800078581c45007494880c25100e034001e07030ba00140e190003039401030500040280465002001e5102c00d5401c1c80c00c202651403003c02c1c0a0704903101a2090352904441504000c2e646504a07500c00b0302000318070b8044042124048224043d04040c0000602002c45040380d8428100d82d03013541c50f150f8003922144501d0b650105e130300c94005c0e40c1800c0c0b0641c24005400010080c00c0740e100d5880d12140441c40c400e050103480044081101c07c4201074906640f00da0007400b212148290340a000d0700042d0642c00d000941c035600041c0c0c0301a20b49842d01441c0c1d2201c0018040c0c1c0b0801550300c00c4d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 341653012 1250 341651762 341651777
    0x1107020405010b121b09061615050103031d0a0b031b0c0102030402030c040b0f0d060b041a0907030507020601031b0b0c0f070608011413060e091e07030305040b1c020a 73
    0x313800030210001500205035645004c06074408081143c3c13240701c0e00c10700b00d000d003030042100c02181c0034911410492a621030221000004806c1c543c500170700c000d12003a800980800400185500c0100824181c41006032110740d15500b030600201c0c1c07642c0040c2038004401032614609894640c510b001d0143d45004400159032428a4010036152103a00c1150300d100340e140000c41c10251f5151802019802000d49052921044a007000c600420b0200e42c90781e04181082c510000d01e071405080300c0d98900003100d4100c02516201c004900700e031411508440560301490050002c01c52020341c9610001d40c0304804040942c580c1001c1009400080c0c1401c1c86074440101e6990300f003418021900986401e01c3d1050007903240c442c0f656020118211640d00441e00c501c0da811900d4040d40011010301012182400e840c00e0202036180d8030300f5203001c02c82c0c40c503514045c005426500859038508482d019981c10703080c0381c24001d0100d0568414500381e108040d0740003000380b103016075001400b80400c05480e00c01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 341654262 1250 341653012 341653027
    0x315010608070f0f0806010c0c060f0306090b0102120f09031b0915010207060e060c060103031709070b0a0509010c122006090d140d110423010c061107020405010b 71
    0x50480700050300090501c51214008001aa0700c034601030745080a80c43c0c42c0300a51210030068502d200320b210054003805500e00045801900004012021600769500300403195403000100e08695610000500582040d80785400e80d602c002c01405449901c03a44842c940340d905000030780f030008101004034448031030460640c2c5610b0b1507070f502130f0300010700c0003012003444d11840000d40303c00907401000103010004110034a00e455840a031140710316444120303010703540c4038240a450796140c0b020300c94140c64044001440312001050800489410304e202d182072414880c401d5a054009181440c10080d0719400440864484035038160030020381d45541400ca400c40300038000700302d4541c90015195000c2c1040c0401d02200040d0040b8056452900345550312030008080190310030203101250440c20407035609199003240c1c00a2048a1802035020340001020002454a510b00d0344802d010070650440e030400704070b04d03401511f44180080030040c680841d941c006401c441d4280c0050310b20400100c0d001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 341655512 1250 341654262 341654267
    0xa1b0501050105131a19032015040e040312020c030712030e01060e0a0c020f0709020a082d28060e0105030705030303040602090105040f03150506060f0a0e060903150106 74
    0x82d0f1a607030302083c244404540102088440302800c0340c098006d4094000004003d64a588114040c0d58480c44148954443d0132080120f03540b5050710306e10440116280e20011003040701160100d80700040d030704000382e890ba103094840e1400d0b48244100f6940810480d29071400c248001c01e02d15124148031444119506002000c0381c0b5080c081f402aa8500a020f1000121211185130300c41c01900c0c02188003400c0010807802c100700d103c00329010307116421000c6a003010a40291041d0700d025a0b42000d00e503900703160a840c24154548910403200d050242a0b0300403001c82d5a5903101a11801040895400d11b100061041c030401c01010166903401090140170a20f1440d1801410220700524a6a052000194585c440500010724140d40040e01508a0740503030117840c000c0650462018004e540c0c0d00302a408044404108200f5500e40341c0016807074640a030941e070410451f80800d03410162401e0055940741d01041d01da95120401b84507086581c1c0c0c0402c40c90042d640500311100b038552404501 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 341656762 1250 341655512 341655529
    0x51501030f11030c030c1203190503011e05060f0d060b0f07020f0a061e170f0a05060a0311010f0c02041a15090105031618061d03120f0a1b0501050105 66
    0x201c0d8404d8100c80b1076110581e80005680c51000011110b840782028860903075451842035040f280c04142d0403080340007005800c80007850407a44080801910214040924000c040160007659403026050000841c0d0101007005499062100c06001801c60384900220f03a45420036011080c810000241c040214100030b200070075000700603107043d01000d08000c0040c02c0421101102c1c005801c9000c4904d845d14403a21182c00c01204a0385407000a043c2000c0700302420504039003101c051401c01021550718104030340000c0840342c1151034541da008040004554020009200808100d0048142c0300540e03a903100b010702042c210102c409000b0815020b100c034104981c0d21005c40c20000b4800704540381d8204081780d43c050104c1003100e582c90309415054070144034004180b103204410060200310140c001000b0034291044103003000002c2c0c407080406984071501d03000000f8800050041c001458450000703001c05140740d050403080080c560303d82215240844030140c0b43d580d1200010007036424400309 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 341658012 1250 341656762 341656793
    0x40c020303090303070c051203090a0209070e152b0c0305131505040312050a0b0a1203020a0b130503072d0803060d020312120613020304030f030504051501030f 70
    0x69401c600c0c000d1442500c80c000100200c0c184124500c007041000b9081c442011075410403040243c4905140d00c0c815070341d00b80408102e000346581c10118203c18000c00501811042c001d1600f011454090f418040c550082c502000030100c0802402842503042f04207110500c01c940c900150207000c04170014203070340c2c01070003442e000036400201c800400c0780d001c1c001a0328213060501242a4030740340b40440e544641c41078003010451800c0103008460105401c500501001150b40c0c0e840d058842000d0080145c0440b00200035034820340d1300c8000101454040350380070310f500c0070441081da0507884944c10f503031060004075040d400904610300d81d2000100c109106ca140d0724040c0c83c80070031a07500d8074102c0c80050a21480740c0240d031401003c42d030307017080226180b00030003901c0b644524003c407030400c91140907150248213541d008031200c0b05c540c0741e02c25170348101c1c3c15035160008004c452006400910002d44161041d008690045c5004449105030900951084482440d25007060800b9041e0618030304 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 341659262 1250 341658012 341658017
    0x3102d05060310020a121a0a06050c101d0a0b0108060106020a030e19180209040b060304021018050a060f2006011a120406020c1b0a06050a03020c0f010605040c 70
    0x2000d0000a40340015011503c40d05200b0060b90740b410001c0560f0f46c00601ea08181d900c07030911710281c2a01810f00203000d0710b401c3c15901e500b10652030303401c01d9038280202c5c6036202d41030707100d403000c41d00c03580340e40c6c0190300d1004e40102050903014860340450b0a0860815055030b5280200d401040014130422080f401401103201a00d0311542070350340241400d40806203617108480814000c107030480c2d03076140b22009010909400d04031540700303600e610182d04203255017803040345484001c5426043c1001100d1285a004190040304900c0c15030030784410800b00002c01c2c00034517120021855441c2c0d14910300c05000152103a02c03510514840047c0303828000f101074034074035001d910350303420104c40014480d0641c1d480f02201801c614900500320038901821102c1c2c1c104090300400c0c0424440e1070340c014010040882c00b6036440d019244100c401001407249440c1d04440d900104120203407085000d8140302c243c52802510b40800410032624014049120b1035040c0d544030002c2081c0d18007840b41401c00d44590 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 341660512 1250 341659262 341659271
    0x20c0c1207060c0b192c0105040c0e090703150504020f0123161e022d060702060706051f1d150a05090901060f09050f041103102d 57
    0x1000c020162801100001d110300b6456000c51060403506030540d44a0300381d107004202410400d40c500d0044502682045003a1107002246e13040d0b160306010b0640310343d0f000019001018501044007a21400c002e016484500a484000c400583c0030911110400c107020804509030610f801041460448059090305009058a4820140b040c0c00701c40c061000c00346141c2512000e0b00230007003054a4a40703800820360210000f401425190750b0702d40488a07802510115502520000c0d44c0210a0030004480c0c412541000112424500400205081440a0201c0d0300f800019503646003910401c0d07445400201840a170302002c110402e07998002801c080304110004c00150808502d4450054510211030100305048182500c0d10b02c0c180d402050041c1845c20b5504e8604884c2c0e000300801e0050355200001003800262038102806880d000f0412007400c402d160700c4940d40e50848190040c8025094098400b540e07000d81c545116416030401c0d14403440010140c410381e002c0d1403100080401c01214640b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 341661762 1250 341660512 341660519
    0x605060c06060d021c0602190318060515060c060402180601050405041109060703110c030318010e13060902040306050603030a09030305070503130f05030f0a11061b01020c0c1207 78
    0x500c03541054043d540000c00080c075001040c0114880c441c1035040b00030544092041010380e5008007201c042d48003400d1204c6012000032410748041c00b102c62909100310700a01c010038250303480325070002070340e81e10780200340b03e49404a034154000c22415100c982003401004294149002c840300700c88031015450280d8605000040c040703001d14003c15004568910008002e4641c5104540b4825001403210b80c403803a19260050020511040c502d0860080401c4000c3c2420000155040c034449124010b83d681c510000441d02e64150500f01c5a00c40c601c84003040c626502c1b413241101802d44c0042c0542d503a030031414042c050303600240685029034020880c020a20364884861020b60341d00d490120354a90170703030a1840c510b00804000485220007140000740780c495000c854400c5540c10350542e00000061411251105103900c00500f0255540d424030070103280c224014107900c2c82008482c5165081c80c002d00c0e00326007101c01e1005640d032000b111648117181c8940701d41242a120401003140d80d05 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 341663012 1250 341661762 341661787
    0x5040c0207050a0b0901030b0301240803040303080a0c27050103230106270609060e10120f1401080106090e030a02070603020f070b090604061104061b02030307150e01060506 76
    0x7024410302c91300e080702086400b801c0e8801c1c2c01844000c01c00070001d10042e0380f10005030011200c1610340000c0e0030703082c240001c1d081c0d00110a50341282d80580301c0001c1c95580b209171101520107000c1c41400c000d02a5104403911b04201ea0890009d099290801c0f507071410100054215015150f05c440b030480350a4000714990580403100f03042d50014900415207003d10a1070a0481841992514a0240c0d100c004038485600910404c21900b45a882d80d503003040010900c00c050301c0815425001030819080c117182108550032003007840388010b800044048508070200301e0b80070203800046c4982d4507607604110b40d0078140034a8605042440243d0314040ca080800782d0740e440c840c4102c030203042e0003069080d40b54589c1400e403a04590001900d0700d107071400c032042980790002200d0850b000d6241c1000844107940000c00d950030756045031114442508404859517822540c0002268144070401540b0002007011003602030344003090001040c0d80416400241c25581283c018500501c0c0c24030552414a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 341664262 1250 341663012 341663029
    0xe060f07110303090612060a0e090a06110c010905011a03011503060f06090606050316020c0120012c0c010e0609040902040902060c03070c05040e06010312020114070905040c020705 79
    0x952008090312003801c040042401c41c001c1d0b00d030039a40000040303088510040f08819031842188102c410a1000e43c60f148400c0044800343c81624041d48041c0102d000074550fa4803039078003600d8943d50703035051205441c0713114203690032418119000d0351a4501036280b107448584440d500c1c1c1040f4001d01518103407855454410000d4400a0840d1b612014000c0f41c0f03283d10782c049809044070982c140043d5498110240140d482031f58240c03920200c1441d44502244003040007100340b50b0580d2000c080e107440d401d60b400a0805c003242d2030007e568507044405403010440001c820440002d01e5041074074112801c207824082100340450620010500e001055681d1108032075441c10110f900040c011580c2c004140203101c820402900000b00003a04003040c0800006803503000d01c101c80070643d80c0e807a2010b003c03d4030750060f040d202d0380d40002d00510010700d403510002e8840071740344000510008000702d80000002c080e21102c0100d80c3e5a50180708134201801003401132032050004203c42c0c1d00e88004900d520 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 341665512 1250 341664262 341664277
    0x20c06060d02091f031203020702010806010801030b07031d01091a010614120405011508010519020c030a03020f21043e01110111040504060e011503180807050109030e060f 75
    0x40b84412130340a00c2e40140002d04004d160000b041d42c0034000b8119000c0e0080d84403c105902041b02da600046040d0f12549459040c2d950000c60400c40f5156900160080e00c1e10409590341c42b00078401c040101c007024442c0805481c05108081c00e080c811858840f00c000d8107800840801c001d42c0144402e031800001104e084c081000e5001c0400d9440d07040050040004841343c400100e11428009803884054201c1c3d8040d4940760701d41180000b5150b5014200c0c03003541c1102486400900041000d64065030103000c2c60b1140c074072481c3c540006005421241c210840b501034051107090288800e00c08620100f82e910f00510a80e00c942c921146204014a82d60ba01a031700741520381901905507920803a824854030700088028002410301d0100301e4104e4015001c1d40740603602d00000060000b501c544203074100c50030301500d04000044039604502402c03440c0420386042807124070f80310000b91020003c0038410300400000031600054a0014030090301041c405100d40010307c04010003146841c210741c00d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 341666762 1250 341665512 341665531
    0x2042f0a0c170706020d06050111030901090b1e030c1c180f080d0c0e030f010b060f030a1d0307210f11010b04020403080a0e04150b090a0306050901020c06060d0209 72
    0x540e02c0c0000740714030348986040140b0150021580b030700c0800a40e0094400e03070b40c0988840c80c0e00f0480b03a00b0113030f8078040d008216000544c5c0681c10400030070820020880c001008a007200080c0004055110550082d15512880d03440080c840c040500c42d1029040811801c181c2481200c040408029022500b0f0002410020141600364108034044045031540346000d50305010b41d41e448100a0f000c02200515140240266a101c41d15020188940d8039005030040c5418288130320352003c22740507080145008201c039034511031940304603208140d03030042c60ba8610080d40c0d1017655240c401c442c200d02c0f00f083c254840032130300103002082e0010950016215140f800304090100300c17181c1405400d480b614650401d10001e000300c00c0c048190014581115039490b200c44400c050000d0104580c1024a1b060500c04080010b10070121000002c0040001c005c1c001c1000d9500c0c2e448810448500b5a1000c0e001e030350024000040043c1404000c1c4e1006044940c001140055000309441301801040f030034a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 341668012 1250 341666762 341666783
    0x50711040c0215090d02061b03070f02071d04060e150718031a06010f0e010207050d050a02040c052a0c040b01020f070618050f030a080903030702042f0a0c 68
    0x807540d1007005508100c000d9900665844d08041000b0f585610640001c03200502506000840808640035a0075002d10055007140c1b86603200d0744203d40006282542c03104501030303144000362010816076142010326182c506040142020724141d01191b20400200c401d940205495000010010000da64402080d00b0b0154030840685960f4181d40c0d02a000108090341c40000c0b03180300300103a000c00348100020b0322401c03c0c1844165003503580841e9143d41c240160f00c814000c4c886d50426403103492055100c0d070101d4400322074960001b42618169600c0500180000c0789400710820f4241c00c1c000d10301c1c950480081070080d102603070f98a48416001142c040c3e5118580107249902c204226100d820001c4151143d040e190b0100074513103601000c000241c00f071004004111031920782000c0a403044018020410340304d41d41e462103000c0d0005244039625000034000324025071100e00920002501e50890744502110204a40b544001c2c100002c0b814204280a411232040d0010302140516422084044 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 341669262 1250 341668012 341668031
    0x40605062d1905090a0603060c1e0f030207050d021b0103090b040f05031201061d18040303050c0c1906050f040206071e080a030c030e210f040503030708071205071104 73
    0x4844185034003991300300c00d559040002078100780d803003802030381e1051100744410000100112a03246d21040c000e05001541580c001e4000c1c014801010030f9800b900b005800c1401e107455550030404245000c00c09a0890b9070898412001c58101601e056400d08081040105948072450622401000188010b0110f402403003480401c00a4807105681c85c415043c003980c652038001c11754194100341e0025803210040d00e88091034162035000c030b00702c40180c100103213980d0798404601a100140c0241c41c292000c00c20540304d1041441882c452030064141002019028a044003c40b60b0040103c14240c501d00c040c80016500c0c1c904540505030403004280901082c400350055100000c44010082d000000312400b0b0700780c040c0c202c1200b006c11034400f00000c181c00c04400782c950052036083c41014560041c61101c505807240074045c40d2100c3c9604038145600c030703404646183e008003c191040c075000b0800c0d804004080002c1209480713a86000c4d130910600784d503003013214403107080c01901c61501d411880 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 341670512 1250 341669262 341669299
    0x609101d060c070b1509040f150e0c0109080309031903110106030b06031c0e0d23011523011d0d0b09010e0c0603040605090a0b040605062d 61
    0x440580035404260760840c141546080b85640c82001c044421101c0d950000e403854054207a50000c14801610140140d034403a0340d031400250f0211400c480307020f907202000804101b14800c0e600407c03450002040c420790325800140c0641c1055000c6a0140d00c01c00c8102c4050710301060440c4190788507090942c4501051a0580e1070900d00741101d140780d0719080d0000144080000021b00591041d025030700d5090443c0100008418400c0019000c40c00f000c800819600300311250302081e80c05202c0040101242052904024031140034507903187e9102d82400841038010b400280c003c0c03040704803001c602d244c3c880401a2501c10305450905105500ea00c07801560800b8003140714141c0000c0040a19015a262403009924155001500356180905519081900040d0418500802020f8505640e640d5580d900506401804206075000f810502400100150260780c0240d1080001148900e0403805000c1c000045401c0c40042501c184d0070641e462907110840710031082c0646022030307031000741000c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 341671762 1250 341670512 341670551
    0x10051503010552110a02030a03120f090605090c0a060c02090411030f150c1305060f070b04140606060f1206060f040801020d0c0507020315070c0c0e040203060108060910 74
    0x4494000c1c002e00c2d121030200801c42080301019125210f04039075600da00f484d240d80f4205c10100a415500840f400000300c2d01410b8210a035802d03a003000701e0f000e005180e03c0b5050705c41094080f0f6040c2c0e211014080e03251000d101c1140850010340d1a141001e03d09070000305040c00e009400703400303009010041418044110402e4203c1080070b000c90700383d00d200d64009542c6100100120b6200a408008101000d18080445007403404501c0701203941c504200800c11254489160191201e400b0001d02c0b002840311202c0328881c5004210710070a10300d100c00401e0401d40b00604062242c002040301071402d584050607191008100c08401900f0381d0f030071010800700e11920580c80340f1200041400a03451005400a080111000c1024002d0300c0a280040d00c441c0a0200d00039815001041004500c1c00c00c1000c2681c414254500b01d141c1c0c08060301d48003000d24042e08070201064100003000305500b4108107550050801100810007407504c00c03072040c0c0320100400c004085c2501d62603000401c8540c0704c2c9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 341673012 1250 341671762 341671861
    0x9041a0d17070f0b0604050a0b0a0902160b190608240403030e03030a0905010f0501080c010807020106260c10050a0c02030304030b01081c1107060818100515030105 72
    0x5065000803506290b042001c2c2205ca4074450f505002c00900c0c0b00b200d6015210f40389901810b400b55043c01c01001e10702942103e0032503070f8803e8040914001080c4440142405001100c134014124400704420030243c0f000c44c1c11003403440c0d114000303022943c900d1140d07040c6c0390340b00342801c0c2c4503948407441d003280075088a2103660007500c800710912808401c40d6211001c0c45210700020880c00c110700b812082901e41c00d108004041d000208000c9495001d443c3c1140d000c1094400010f190380c44055030402c050b1040b1611000700007501490b600c4603c200150841c0d48421542300c004d46118038001002c610401040c02c0401800174000e40441d2020002d4402441d4800c00c00300103584c640b280103a403031111186110001d50101d0407505014040c00e0441c0d44c0741d00d6880038058484c1041016512000080e011260100c0ca119032007959500601401e259440440c9012415040c480322000030b9000c010407183c0700b0f0740740409100d100601e0076900d414900640ca103582e812039802a1090b054540c550 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 341674262 1250 341673012 341673023
    0x30703050307140c0a2001030504020f01050a090803030103030306030218060915060702090f1617011509051807140f032d070806030d0f21020c030c0309041a0d1707 72
    0x92810100100c20181515000400c41c5003000180110011800d2742c0b800d07100030750081c0c09000c4a24640d407160303005061a1007181410144603030350700f541c5491507000340e01c154000795a0305410700451402c405007581300032441512080d103003400340000d00300c1400038010340d042c0061019204400d443c2c4e1302c265940b50f81c00070442110741c0b40c4a010042441c8040718007200d5800c0d0944131385c100301c1c00340c01042c094101801030f040543c0c1c201103c82080c80303c502910001d02c501c40000140f02c0d940c0c2005a01035680302042042d01d8104010081c1c03c80489040c4507000890520624030034075460000d0303d81c00f40003240b000c0e01480c4160302084400818840030900030222404001d040354200d0340c1c043c02010700f41c2c221a590610340108490480c850750000700011045a0a074084c4461a000c1025040d03011100524100c104602d80e85154020200b101043d00701048609407450144101007840e18422a050300307440500300000d03c0c4840e100070007000020781c071714410844100700c016210801d9024 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 341675512 1250 341674262 341674273
    0x909060f0423180102190c06110307050a03050114100302250c0807080a08070605061908010e100606021c090302040507030203190e0712020d12030501050111030703050307140c 77
    0x840c200028408903100043c081a4441560711440c0c14422103000c0f011a0700da00780e0309046024125a01900c8000c26190551261020307110030841500035401078940b43c0300c965a80c0e409800180a4400580c84401d22989410149000d912480c074280c899040394a001a611204014070201c950326184c0c09441024014100c041000101003005007a40c0054084400701540d506141d5500e044140e0b0050042c4821b2040320000384158010941101c8001e11020828980d00f29410041c039281e80410000d81d1034101200040e00140407107042260600c20601415040c0000a5615031900110720810000d02001c10b4450784900034003c0510b50082080c072003400c116400030065001691580d02400b00e43c00c4941c03640c8258480c50085045440241200c07918040455030385c40d0b03081400b0390b008059404010006070b0b4101d000707600754126403000101941840001002d000c4500041c16603a402003180c2c1c80402e4001c0181c1c0e50205580c501420b849207080e000c1c003040d0044020380700151152 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 341676762 1250 341675512 341675561
    0x70302420a12050411040902030a1b0f06080c0a140f0d02190c050d0f020c04022107091a161b170106050604090c0c140a0c06050909060f04 61
    0x804a2078510364459044112074003490b8101c03401035800030103107503d10016500d6400c050f080b058025000074103036a6242016180c82c07176400400d044070203000c482000c06000c0b881e07200342ca48000d00160303c8c02207130074540740410000b20b118802c040c1040c000044180c400c164442000c603060305c504207403c80d0300e6034a003540e002d01039046180040c440041c051106440b02e0700c102a811101074105008020b840d40152060b1000c00c80c2480c50002c600814150940d1912280001c0141c00e1202004481154000c44103280c002e601078144400c000454104105544034140e0244030310005440e640e60b213410a2104a000d6107020b8401003051410341000200782c80b2000f030000440381401c881500e04144520031500301e0307000d40a06030b40300300c0600090010091a81c0503a020302070608004440b0340e82e50b106c000203441f28940e1065142d11140e502820000c1c0050344800404241c140380c0c1c10421000700089000d1001031142d0701554a0b08444040343d56190031202d01802020000b280f440751 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 341678012 1250 341676762 341676889
    0x408071b08060f0106030c20030d020c0a0b010519140303040e0c09130209010c030c0c0323120a0c020904170406031d070b03010302090a0e0d0507060b03070302 70
    0x1403c85800700d9803c4624000940d460080c020815001340713076075500c1042c522054800f81540c0401c5800d42407444140001c0b01d400c1c101e88010701d00040c1d040000e1030b414130140307403030640040160001801911078045800c03241e504810810195a4400c0c4103a803200e0802d001b01e86140995801234014000001c01c0c04604400740c3c00400910b1070503203040b81c0000401c1c90306000e0b032140220650010300c1000900000c203125540c4030741c00e07034440c52031164029580e48402a451448856003c84030b0790341f01c5240c0b410001006044400080a06104e042c0320a556020b0592110540040d0103485800d000a003003115012500c03040300020840300351a1511640010010302492a182d0b0f005220a54140512000002e81c441268441010949541e007141d0a10001d1000980f442c140140c82e1013036103c080c80c0510080320301c041c039543d600341c8841c480c3c01c001095880e0710552078000d4100d10320503c00341c0c5a00201e140b20b400c05000201d41001032400c2041e000e498140081d00311084950031021b0b03000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 341679262 1250 341678012 341678023
    0x8071109040b06030c0d030f0516050a0305040e0a1e0e2401060e03030316030b152106090601090605030916030803010e090f0304090b1f0915020f060408071b08 70
    0xd40a6045503030310020801440681b49000c00040c0104880c0b200030280c05104000070b2900184c01181a52041c1866507140d240a95000046000c00c0380414144002c21050100b80c3d03214580303442c02e01001d60061000c0440d45604038036550070b85d89401c0c080c900048100554170b668002072840100301011910340c80d6000000303011714030001e45000d0064900c0c0c607000081d00d000e4642c03d180b20410200c6030300181c3c001c0181c023000642003005d5032481c518854002025040711081c1001486900650702c4014250705e0000b00b2083c422000d00c0280b10850340e00c4008441501c4550030030640e261039298116140240a40800c943e58041040c04020841e0503030185040300d50740d015085154494501960310b540030314180d014650300611040200fa1461707044132070a030401919114603081c2c07800d0021505a81c0055602c0400c1100301c08001d000c40c09107107005101c44501c090604a410380d140c0c15110350b8081c0c405000340307001003019024441210003100e1010318020184500341d41da05001c94841 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 341680512 1250 341679262 341679271
    0x2070218060a080d12090c0e0f01060311040305060f0a06050303040305011a040203061e0a0f170c0301020319110903010e1612080301030303020a090902030c180f09010308071109040b 80
    0xa0b1000e007000107010000040800880c800c40d1602021802075200b440f009002c0003a041d11482101c0b0390000758111641c10b01c9019441d880740703080256040013406400e480c0203101c0845583c1c01000204041000030844036008100004c03881c20715100ea680200c040e10a07030b000b07198036020024000003000300550002c50000407003818001c45625034001c20040740000c81c1c850783c00040700311241d040e5801480c06407192003401400112159210060842042610b40115102c0f0002c07615109404500b0812100034900440080d851898828120200101810074a484041c0c0306c0200c40900e40c44401561409900980200303d51605000301c15070383d001c141c00f08081059038444c04140f42c000e074801e41007043e4000031010714592071940c0031802548107140c11410441d4140010402c20403900085000c0e20a2180c61611210401003010800c11080305451003020901d0740c0440e1500e400c840141101d4100c12100c0d254089810b0181c02c00d0707410f20400e40d006044100304402c000015080038010f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 341681762 1250 341680512 341680519
    0x100519050312040b120408070c0e0405060603070f06050f1903050708011403070e0901020d09030e2b02220609022125140d0c020105100f090f0207021806 67
    0xb06006603550541c52155008011060008018941a41912803800703500548a82076991a010349070b105d0b560381e0724490b0480c91072400501c061100340b0038204111b40d0401e070114041c1c000c4500e0201d000b100101284144010300501141c20203008881d1029034540b40040d900ea50400c004540000340100000c455850205003032100114071030103a0314030240e4000001d4000c00c181c0b410050907500007040288400036564080001d8200a1100e00036008014403070b460f8030101d50608410490030641030008060b0710605410040414102a40580415a010348510105c2d20410310001c81c044075505240360040c0c241280010150303100d6004000002007031500350714211076042682404102921400041c3c00d44080308564450181c0a40080e4505070034142c140c180000c0041d0480e030041036a40358880e58030000501c640c1c5d0203000310340d8894160720180031105d0410307845800084c0311f40141204103541d5174003080c0082070340c1d040700e030343c190000d10040801400031024208080211080c81c003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 341683012 1250 341681762 341681773
    0x5061801140a17030f072901080d0e0108060f030708120306030d0c033f050a05010f0e180c0406091a030c06070204150302060703110118030f05031005190503 69
    0x768a491003a45111400e04000614035122010b220174019401c14501510b038014400b0110101000011058203468a00480512690b1412034250b0038480120800e1050001c0700140801c181e034007500607503000208a0300b403101c0c00c0d2441d01103490721560707030012600c0c1e1146155024501d40460040d611854085003190b0100511101c1192005240d02008010031420800c400d9a15842e0340c900800900030340401d070603880003500030090501240c1d03440d50803540c0d030347c00c0c00481807150080c03502402c9141b811040442c07030152040d4900000619003004081030032201089a03005114012801c0070003001032245070f86900b00800204071640c400005c0c1c201c030803a5000c0600340400e20711030f4910700803c402d042018907000e110140501d440e4801100c0d01c2c116000c001681c454001c0c100c5180aa075600c25201819150182100c41260052a0001c2031001c148002548a510005840310514099031a03488060b4440207030015504526031040c1c1c460000318403244007a00d101c080711803c408440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 341684262 1250 341683012 341683019
    0xc0a03050a21050313140105010b0403060b030a0201170c04030506070906030c030507050d020a0302070b0f100e0f1305010e0d081b04080c01180b070b070305010e060f0405061801140a 80
    0x1c040c1d2070b81100c40410b40c20b000044c0444d0210b00030703030810380c014000140400c0400c001d942c2165000d8020392004140883d040c000d116140c4500d2620728415001800c0b14035503038002034004d00d400030400c22019481000102d0b0380450209840040d07a0040840e00700d401c15190103030045115004030000240751407d0180c49920030b00505009209544580d4030340403192100001940c4201d1341441030640811001d000034881074000340c81580c521801e103001d030901c0c49110440d15800d500030281c0100300303001d21a0b002400100c0b240c00060900d42415844404d01d0150f0240c251000d0b0507103a4001c8180720000b954012100c5d40c860840e6599102101c4c800221015650207180103000c40c6034840e02c42c0c25600d5018078481040340d001403a00c500c3d110780e03440c4920a45c1e4000b14040381d40030a01020310032038035014040d50f40980720711140301d039591034840b011449118801810030300c52520740c40030030201d80303900d00c42c40c02580b0f074a80101c4c06036031206480d4450710544440340d40107201c480c4000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 341685512 1250 341684262 341684303
    0x209040b061602010809070e09010614060307050901030203102102011214040b090f0a0303090201170105011b0c080d020c18090703030e030c040e0105090706110a0201110c0a03050a 79
    0xc4103800040500960050b026800440c0c03e604014009115441100e1001c5a02040604020b10030707548500045041d6043c83d0300002034402420705103004d4042801408402d940000030390703140700300138030380161295202c0308004550101580204084200e00ea5500c688081510804103041d0013a2610325005140041c07010440b4800e0761a50041d000300004640002c0980d0002c51300495154100c0d2001c100c408501c600305641441c0440109503240c004404558100008550412119040450662411001030f012080c2c0380036220b001000200814100039038214034001400120007101e082c02c0e41e050000c0d40c0d82c840108850f1144268440202080c6007401c0c0c40e9100d5a40c0d0800307002d01514603501070303590014580c0d01642c1409440445481611148510640c406003940045814142528928140041c075048030303040150036904a501c818000170a482510f0303084c60140b99551006200b1400d0400181c1d9030b592001255071b0000c24094002400401140201e100ea036012600d00201c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 341686762 1250 341685512 341685517
    0xf101206020a0905030313090b040603170a12020f0a030b03070b0a030e100507210b0d030305010e0f04080a0c02010e040501090c020601080c09040201141b01060f09062319090209040b06 81
    0xf287e03010425441c02d11034542c1a80040b2140d90000e040031603040d459946031000b4928845410025031030200380707052043e0340102103405220710364104520f0140720b4200d800c02841228660010306803282d001c0b101a0318104124401840078802e26038030380314038140040181008402c40794251103079103491100e4000d18450240221320b686c031441d14060020380d13801c804000c1e520800c144103507511070040c0750340c458520510002e846a540020550f052120001040c070002c0c0c50f00160748001c004000c006107024048440d0103032141801c1d40500c007588012100302d01c19804503134000f81450000a1032400307581000000603100e0f000c0d507890703a80320003900d0b40d141a006070459129440401050140d401003440c44990318654600c14500103152070310f40340301240c10240b03000d242e40d248020440c41042143d004042c0c603011005200300c9203042d13101000f400041e000200010a010b162900c19075030700302c101c1910001e2140c3c0202560303680e0510700c0290041e4031a140141c0c100003003282130303203481e208 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 341688012 1250 341686762 341686777
    0x90203090c0909121801030c020d02071a0f0c0a0606060f0801051005040e07020609010b060a02060a0209030c030f0703110405040506070c03030f142d0f101206020a09050303 76
    0x41c100040d66500b00080184054042030060113510720084c00e0580d14001881ca10042d403d40c0e200000c2060001400c640250100104540001540300740541e800b2030b4034000c5540500c0c0140300303540d0a06c075012441c4207070f1034500198038000644408907100441c42c071410754080e010030070056039183c0051300c0c0c02c245041d506000480c09001072006103401480b1917086526403900d10304107a12861401c0500314107944a0340960b10a0307007082132248003400b4184429400b958194200b01100360042d580340405000c01d111150081107d40e03894034104000c140541000341120f804ac400c0c0604641c582d443c50005645441210b030301755500742868001c00d40165030001c000e0140f6600e0881c00c03a04000240c02c02c40c1003507106c2d002d0722800307410790041101d0a24400c145107054100a040071884004a01c41c4c6500380e119035904030714803107404055541c4401da0300b42d5840c0d41d5031985070102200d0004c0d00041c0c5161009419241070041d15402381484003090344070b051409440754109556801481c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 341689262 1250 341688012 341688031
    0xd02130515180f0a1b03110f0703110f030c030d0b120d08010e0f010302010c1506030b01080c0f040b090708090a051002090907031407120605060a030b13050708070c0f0516050406090203 81
    0x10a480b8180744660b07c4024060b04000ca001c1c10100f9800e601c032001c0d1300040040d00010541060206220740620000326031104149c0190702c0c3c1412003079580c0d02ca000780c080f04041c7c4c40c0d680750040100d40b10029014010070014003503500b000200280a40071031400e004001607021588002001c0c07003200d04605041e2901615503003910085591070303425501401c1c0034400115202c0c0f0300000000d000e0700106007c0c141c0e100c003401100100106109000c820003c00c0391245003800174024030380d1108001c60390045001d1038000420768a4540c190f00e44058498000d200b84074240c41042801801d60160400d150200c2d000d218075100d01e0b50403000d03920f0001c80da1000002c0d01c1d001c0344042c0d00500d01b00c80f02c440d501e0030100c0d40e40d80c0d4000013211900041140000300b81c44a90f10701c2c0c14a0210308c608881c0a08002c01c210074146000010b0412500900520510803001010014031800b0805040070a60050894454681c001d1501d10f240b5403a1040c070f40200d0400c000400c840c8054000d403840b0b80000f8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 341690512 1250 341689262 341689301
    0x30106050c061006051902150c04171609020c1c02160605090306070302160c1805010605130501050a0c02061303030206060102030720011b110109050d02130515180f0a 73
    0x486c40c518072901800d804040d40306801000e080c2c806174480040c81003069254103510303240f81810f01100c4d1046903200d60542d4000c1040f5072a0680740b450b00509440210700300588400c91036080c9407400601c0382c800c90034103d11a250790200c9a000070100001c00050364214513072555201c0607a801d0003003807103090f03041d040742c0c0014000a2090b4040e04209119000b8800707821460348441e01c3d00d0903180c0201c5010310310310300100d6085000c0d000d842d00520700c920b441440c11508800c1900f051030280200c904000001a0206000c2e12541c5540b0800350000c000c40c0c1d5070210300d291400b4013907051104901602030f0304005440e545c00071040d548559045000000216499400380707440f50321541c001418440d444005030440109013a030703464510712500c2c0100030504018000741a081681d0b00040c07080005c2901c440050321001c0e420300c0c4c0401c503448007140ca9201c2e5110403032900d0001d901160400300d0350400704e034420100030800e406031220b40041c00d400d803a03421314401500c01c003d1800109081d031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 341691762 1250 341690512 341690527
    0x507020c04050901110a030e0706020a0818180a0e010f02090a050d0f06021306090b040b0405060703030f0c020a06050603010212130807170901030b1e010e0301020906030106050c06100605 82
    0xa0b042035038014407030000003c02600810b98407055411a00c600b0340020b6130b448652003203034020460003000c0c0c00b990000340301036002503031900300901c00c0c1d0240c0f100718002c50340361203000e44401e62600741d0703094140b80c050000d2615502890040c4000285030b0170941c01e00904c0c00040109208540c01948040c01044e002400c102c2444a4506220012584525042098804599148054900142d02900c5101050304d040002045c140c4039400c440032007a010407007000301101e91412541261740944100381c8821090030294001c4c02c41e080292100c50621908144031680891607989281c481c03081007210783ca602c07040c1801c0340a007160102400c0000c02c0822003009180c000192000e20801600e0300e4020680d550100199016010040429001c035502c2520341e058000c45e01521800d9402c64264a80c0300c010314440c07106500641d040c48481410b001103520203404940708004040c20b600c3e5a540d5030100284030743d02c52000e441d414040c640114041320901d10085044801d03a03a12282000403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 341693012 1250 341691762 341691769
    0xe011d04090f050303070504031a01260f0a03020304051003060e01050103020c1f1b0c150b0f0402030f070908070303020606060a122c010b0607140c031005010302040b040507020c 78
    0x84241070328000d0a021010b40064801c000039840756045503516034680f4914646442d000c4074403000a01100b8803030006001d4440540e40800b61101022460340740c0b440d000518a080c031460451031101c500a00104a044c180c0000c010300440c0d40071365070101c2d0340c7d0841c04e049044501c00e02580001e08220001003000d98443e0b000741110041100c166400051000d102100188a448501030b451340c41e071040860315074800340003c845003ea8241940d8520592342c03405000755981031030380c07805030b034840408010340ca440380d583c0113442010f0000c640d00e00b004000702005000c00c81d0b00c0302c0060105117010036603000201e02c0404807545500102000d40b1180100103d5801c000115001c2010818044080280724014020418540e0991600c000b13a596080714441a070520070700e50a03030501c45200c896480b168111410305400c0b4440041c8001c41c4403a9074140b07450074200b2941803040641584809800b6400306040703900c00c60b0104680c41500d01407100b07554084603a1009604402e1a0b43c2072801c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 341694262 1250 341693012 341693021
    0x150b13031203151502010f0c05090d110303070b180c2b0c0b0d050703150e06030f0d1e18030201110c0a06051b01090809150d110a0e011d04 61
    0x340c5505011410040c2002c00c4810403d02d030348681203010740c0380f4400c200c1c15028490110b00c4440310314103011690034240050080d114801d107190103007400030804400c2c4009030ba44c02c00384520003000d40703665000e10700701088003044c1078510f9060604034000c2e0000300e03600002c044010350405024244500403104040c80c110650382c000c4030074070554058070320000b8203003010b42c005402c0640005890304c1040c40c1d501c00311040144080c00f45403030200d5010500041c10358010440312005541c11031952600c000c03d040c0b0420441480311449010240d4203015048600d0304d20781c0c200d42e80c0c180030f15200c50100700c0d40c488411a400205e052184c4091003d0752003000c004004d003074641d003102c4e0441d9104c000b061034464654008000201c020580611248400148441510f108002030091070700588400f09684a00c0556a11403004c0840c100c0d10154101c003079030001c4400c1c2900704500c0d600410100002d5004031107042c0000c420f5104c1d800558050f48403280c2c000c44180c071349014000782d07905000042 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 341695512 1250 341694262 341694293
    0x10206010e090a05030403030503270705040c03090218060312040e13050109050f060a0f0501030209220f030e011e081f0b0403150507080903070303090c0e0901150b1303 74
    0x40c0681c9030000f01050b4204000c10003140720341d403115504e20305680e00200100801e143d444d120200518030030785c440000111001501d500b140d0016051900c40d40c2600180852080250411081c0d07041048900b50071003028401d840a4007a10404c844601488c9454031840c002c04a045030108040780515220300225803207503104200004e40e1070304a480f001e1a205900394000c100d503100204002d10400b0502840401806c3c0f11000d2043e5415039000920700c00c4000d02460501e1408003030004111001c0b030005011a402071070300c28440049040040070780f01e0141c1201c1c003044d026038142e500036061800741c040b01002070350b54124540f035440e981e441d422103e0010000d4541c200d800407a04d0200c0c2d07002003000350310500309100075800075060041a1200245050f060007000020031080608c0482280c244640c1441c1c0000d03c50194603041c0020b2140707400c444042c1d1012803c000382e000d415400701030740f40c2e0980d401119803645d50b01c2c0050540309804030406106c20098040001506078400207400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 341696762 1250 341695512 341695531
    0x6020d050619230d05010608070f0f050d02040219020604061b0804030c020402250c15080f100e0f090f0d090303210203100311010207030b010e06030f010e030703020615010206010e 79
    0x2030000b50005030f031045611009851031b942d07a40040001d203000300b1480000340b51050040c030303100c1d141003a0380058000f9481014007814a42d4580411507580b030b81102c03507081c840c6000224410486d84000d42c0c52000700e604030b500d070703251048024a4044115020002030a0b176034405400740d40d10780d400c480c00002030708100e0304646c003449507015042c0460102501701441036403d404030354880c00c20042565980e4045000c215000d00d080300c0c0c00758010f40142c2d11400c50014076140380c035000ca030049060700c941e2149050038910b02c28010080c0705100c119008a02c0d510448010301007034010682c588a54403c1c10002c0350a0740420000640200d44051401414606070032501101d4001082603034401c880b4000d4415005406100b004902d2545250201c4207100a00446065949034241110180500241e03503003c44000b41603960304100018a40f6641d400034001ea407144800140c2da40c11146045001d400780c400019115107500329400c410700f070141e0003400c2e1646001004070240713001424507040c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 341698012 1250 341696762 341696819
    0x20d030c0f0b1f0b040f050d030908060c0315031c0c0203030409050705070507091505150c070308090f0f1c050f1c030608060709030201080c09090406020d050619 71
    0x810340e0444150b200c2c00c001c03524401c0500b4102c0080c200b120b1583c010703c14101c0140820b01201b9085014503050750f01c150759040302202d2600701520300c925554440c0d407091141070100600080c12307801a60042400c12120445604040704143e210340900070078416007051143c8031504c5612404503001000c0c005001d80e032400307807141e1045060780c1d4120381e032802180000526100f0480d0801041d00180148141001071088203e05412603522a2003914451070f00300742c070a0031806814003140e410f0082a81141c4a680c0c0d280341030300310b1303230041c02c0003922405094994808a050058080082003001018114110140b02c0202c5410004d00010740d50b500c03410701c4040328014100031070303442e0240d1404070209041c00359600406a45040d04141120780280e814000401d0b04007d5240c03e8a43c2400d29891550768412080c100e406110b25560303000b6810382c2803005100c525030081c6440410325005000c81d076511028442404c40050443c1e00d4817501110801600712174962012158010441d01c18 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 341699262 1250 341698012 341698043
    0x1104060317090f0913110a0e15031605032805030a02062d040b0411061b1203071202030c0403080703180e090717030d0216030f0804020d030c 62
    0x1068003100e07603064890190005500509251100101e40e0824003101c0c80d41591a10101344540b10791600c2d0014002036215002d203209036641c04140d03000d081d0802180c4414600b50800c1b0740643c800e01c0c0c12500034040c142c80c2034a884404103802d0706407070b000340c002d0204045c08680881c05c00038a80003842e14400e40001c1c4000039030240010003854820b60700500f042e0a00552111454040703501030516000060146519a00303201e00d82c6a0154000000c62010ba846080c80165001004c0003694050320010307150700321032000c41c1e44a22500080f000c89a0b41380c83c400a2241070300c41501c1d650040350034a20b1148041045400542e03004100f685078509155072075681e020359410400040b80410b503002c2c2400c0b80304040c00d588100a00903100c0c1d8020900b81001415190a40b03401b420080d4048210350100c514420021518100d0120104554a241003142d2a1081e039010704220000340c04080c03c1c08641d48501906070180da0014401103083c0c03410785e030a07a5081c5511800311400854440b112 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 341700512 1250 341699262 341699273
    0xf180b0705070f06120e06070e0f2e200a12021216020405090d120b0102160909050607050406090b0c0a150c020c03030c0309090c1209030405270411040603 68
    0x310300404c43d41d12a10070070100801100296a540070320340704aa0702c0f034401c0040640d80512440710101d0103441d404000c168800108050340c0144040e05e0044640d442400503000b64441406803c11701a62442403415520250045441c1c291f002c40034291b200100d007902140c01c04003503122030500c90040700c072030142c50f1141c411690401241940a0302c041108942035050074066280c0c49111a4080c0002e088800703000790181c800c0c0071003d041107a4a40070580c490340204104908828101c0100d00700c0c0f5524071805c005400402d000315005e0050b403000c03960b01c9001e141900c06548443e00c40c0208070b400c00c030040c081500915000e1096103d91314468001c41d10240702c1d101210011800800c440c82c070248040d19240708103030302c2ca0182e441002224404000841130340c6a40104072246401d64403000383d160028000c501c2c980043c0403c00007804030b640c00000090003202d40c25521702d5801240c012207041c0310b0810304441540320000100150010b20803141e402c0140100501c0001c80c00d8803510ba0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 341701762 1250 341700512 341700539
    0x40305070f03110d02091803130b03041109040c031b05090a06080c0105090f04090f080d0207231b0102030c0d0e0a0504051b160f060c0f180b070507 65
    0x200c8a0407014031410310500040d0710a040f24401c0070380c0c0700400055142d0100c0c0c0344410003015125004500400403040150610890f80c0c42d0000d02e00888246440c3c46c45826594011381c0e0031200784490517400d500320305010f540c05100c0c5401480c5400b804e451360f00d032512480d0070084225840117242c40c0208030341d9586d00c01d80380104200b5100203207003401d00307c81501d4800207000c00c1d414014117101600b0f15a84041614a43c11000e84010650200515144640141c9138000038040398000c1060f25001919074007804205000b40540b808110020740d071518884030140004009401c035480342c00341000f1109a1140880061046900e4203400c01a00740c14959416140c000041640076480b106180c52800c42c00a46400c42c3e0400103418805e802d44110580d0928002c01d0800c08038007050281e030345803c0e89489a80084000402409030b203000d030f000304400f0300e044020504201e0212270580c46102c2040342414002c40b001619410100300141e08c0d0401e01044441d4403c0300004142c8500401c1e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 341703012 1250 341701762 341701769
    0x30d020304020607320c03030403110411070b0f0604091208091609140c03010506042705010b0c100509032a011d06010b07030206010302100e0411041e0f0b0c0304030507 74
    0x410b80010121401c00705d51820743c08007400c1d03010114025095038040100c030200c942c8504c0040c9030704013000c0400d01401c8011103004000700003151510501c048a41d01038481d0612044d404115a40d103000c100440d55000000307400c1000224015414034024541d154029126000700c4401074030100c54410411400c0d00311403070343c5da00c0e01c2a03214541e1a40007807941000d0281c010509540c188004200c00340510303c01c81e5501c25140d822100d40d80b20404003038852a0361401c042c030440d0784400940006911524406605114079150b894000b440c5224040c01554064040d61a0034a413802c1079402d50071681c04400c20840441803400113075803d1040c86501050416542c6e81c1082c0c81c18440d04180059001608140e010000000060f0340440d00a042d80d60440720a82c40c0302c1040d0040318032101c40085607030007918025050315010002006001291096146c8025948030f2071941e103001d401c036110351901d0581004040c03004100c060060b014004a02c0201d90034242c2e69250145060516030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 341704262 1250 341703012 341703053
    0x7020418060c0e0d080909041a01030305041401020a1112010b1c05012f0a050702030f1005060609131a0d0606080c0103140a0903110a0b0f1503030d020304020607 71
    0x1240c1c26185403c440e6060700350700b04a8070308281d0149501c03204414850480e01d18030440076003000a081011004001d0400d0074181101c440369a100d1070003a103a5405405240020500380071803418542c80000e020820b264084c40c0e540d40b508041c02803000884044561a255540707031000403074140c6440d8a0030000b042d07000e42400344050b0310308101d401c40700180b440c0114200200c1e401000901d2901907041a02d002c000c400366500c40c10003088441d4058040025414016040e0461840c280050040141030844a082049440c0c01c3d04201c4144500640250030001c40c840d020034103282a40701d0400c60749140c2d52514040060800240c0e44000303d84111003880c1d03507000500280c4000c20174080150800e08040000000340758640c200c0721801071030b840030b90392504a00d400f014410006450498600e02c100d40b028605072811103000b8404884000c9120503100001e400c1031044010100000707405005146088280006107000c0d40c0020026078000c02d0030013036100090241d8174030704030300305006 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 341705512 1250 341704262 341704271
    0xe0f0609150d0e060601050a05070302010b1f2d050d1104032306100312110709140903070305070314040510090501120e120c01061503090c0801200702041806 69
    0x5008100c1c3c900581c5900c0c0395006108010081c0d070460304035213030050182842c644400140c5012030242c458060b44a40080c071251104060f00120503401d4503a00743c40c0c85140c04002d02703c03007540080000185842980440c4c440344402180914010400c21050240c040303030288000000f1a40b0398400c3e0310881e081c400c100400c20f1185003400501d1000302050340603001d142010403d40e9094a01804080d01111055150a0038940542240c0000520031000d07150125078507a0040c1c000e10b22065008230441aa0340045e00541012007210081d55044c1c41d403500b0034030750792030440d2024048542440312807001c020200ba03030b03501d400e041c105d8074400e81d490360b136402e0801c000101041c500d100c0031407101e4100300d0b8028011074007080300515070744551005c9440f00c0070040c1c41409020a60700c0141c51500d0841a00d000d254150420743c44a80034100110b0718682c0d80c09014220f4440340782c0242019411030341d0140b0003141c0801002070500061010a00c100020407440a005001c50101e40c200d41e103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 341706762 1250 341705512 341705527
    0x12030c0d02010612080c012309011d030403030f051b010203041a0402100518090a05150d031202070201050c0105100e010b0a140a0306030b16090f05010e0f060915 71
    0x80152400d142a00d00c000c0c01502d103003541e01c0040150a00b002041c000020440300340b5528250f01c60010030303400e0307040c1d00d520701f45c0c1c0310b02c08069103015518841d1075400c0080c44101c007240b214038803a2a1494600851815140d030302d0440c0c40141c0100d03200200003040100c8500b00c048003582007407400c00040016030302d04240c64001910804128a9110117506a0800c005644c4031205400c14400300e0901c03c0e40d86400c1050603c05812882c01e1503441801201401080d0b5541d90001f4480d40c041c100342e18000c2148000c100d11030070320860080010f0b00d4461035058200d5950081d02c00240b06040031410000e545000030f0070340d442152090400c4a255004200c0210454000d50040005c1683c0074030740100e898000f0180b0f40d4031000a180c614000940200c003070700ca0362001005680040c4014894104180d44201780d8090f1002c1400050740000e0120700301120561a0003250030503181c07240d9241d00c10382485801040c5071900783d8041317828850980703941c941d8801e800070240041005540c1c1c112 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 341708012 1250 341706762 341706787
    0x80106082b1404050a03051b09130f0807020405011d10052d060f1b19030e03120310030302100b1011070b04030308040201021c09120c051203 62
    0x2009614548840000c014400c0769419980505402940c01d2070020816500000c080e04144601d920641d00042858800070502502150ba15428510282000752040c4014208007640c034050703c0b460a91800c0000d00300004031000c001d1218648100c50403410300003da00010110750090b4040021148840384400c44514020f001c503612400705501d02c0f222500b00300c049a0303045030000d02404001038090302200b81c02001c1d8802138a00000500459039881580381d15425034100c54490a22030710910041d0744050070104540c40c1144814204003201401c40c1c808564130070760183c0a03501070003004941e050f040303600002580700f14081202c802c0601e140d8a8001c1c50401a0700b5010300c40744c03400e04035401c0c0d41c0c2ea05001e199040342601c0d00e0400c500e081c49101e8103080c8158094100004000f40c00020540c101e0170141c4164000d030280c3d8000c50380300c0480d20024240e042404001403550344203100700701c03040215241d100c3c09031141d082003540702c101051100c210800345c40c406600108440e0f04505 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 341709262 1250 341708012 341708023
    0x10b0703031107080a020f070b1c0204030804080a02011d100c0f0f0507051206010308090411120910231902070506010b0706061719020f190302090a111c09080408010608 74
    0x82410000c00c8e03914605042c1c1d0036035003c1c1e603c110007103204018011100a100b034045d1409140c010010640e680da5903410035568a41c401c81c01c0b40400d10f4503540c0d1841d050030500c021250f0034007038180407280c50b403d0b40c00c6a80c202007040450b0950071b04502c910208450f10641c00e24940314500030914130382400200000c10807082c500c200e103980014014400240d00c3da00391018460705403800700e103200c06040001400d00482c1c0030100180c3e001800c0100b00c50001514aa0300365040d0380410825140d00815042600a400810a181d514202203148840140e01140d00342c0c0600340014103050155807601d00b0071001380e210056403500807410105004183c450300e40149000c400000c816005d07940401e8480d14884a42c14203481064100703419912640034400c500c4c2001002942680d0140390100c1040720180000c6e0300030041d040004040301d401d8403c0458103a2042112428158000c1b9401000c0c20301d100050911529440001c1c00900c4407000b81015100382c80012408034100944145800d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 341710512 1250 341709262 341709283
    0x20d090605010611030705210702090403031a0402040302091f05040c03020301050f0103090515100e0108030a021b0112020d0f052404090b0a050403022d1014010b0703031107080a02 79
    0x2078100300314940002e41d001a00903c031070854090029050700b0600ca88c03415000341c40c80690440c0c0540100010154103038860b5480008507141042c2103000300040c80200c3c004d60100131340100161001c100c02c032400d0148850350f0320310b1030901d0700c0181d1110086401e4544031104030b07000c20780101c0144200d140400c64031440036020b290070404103003203886590340daa0140e50343c4009800c208000c1210804900d140b8070191210034034801c1c43c2e596540e4116541d0b441404400d0060042c1d05040001d03201c80c150321101042c1c1603481c40c10b01c801d40d200c1c240003544450341c8204010f03a1036000b4100d844440c041c01e03200d9440d8942e41c201300c000380100006084000c031f00c20fa11651602e080e500020b02d07840c64050300440d032044001050f540700d2805928105101c928106018030700b1450110f505140b80c00e6414005403607044d5540a1010100c12040d9846100080408440e1500501c001d002d0342000d051904e000b442e002c070790742c061400740790150f50001c2000e07640250009240102c0c1a0100100d1081 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 341711762 1250 341710512 341710547
    0x1e020a120b040e0d0c0809060403030903050d090e01090f06120308010f080102030f070e01121d0709020906070f0302190c0e070f0e0f0f130225030e010c0204020d0906050106 76
    0x16640210140c030340340c11100c02c0120501205c1e1a034841404009000c4c0e8a65003030141c8050364868490030094600c11039031008540d60300c20f036140a010030344100c0c0f2242c1201c0094034107003150f03420900c1c00d50150608030346405c5225501d150010300302840c0040e04551500907100c0408550624030135000180c0d140d08a074003182c6c010818842c924150314945c3d50f000700c952501440400913540122030b001d03485406881c0d420308007400031030407840344490300b11810341c0502250040ba640d02c03400000d9028000c0e4865000200b441584049866500e56298040c8079106545030810f00e541d006402503003462060f510038401400600c8240040d07500e068200c81103003000c9040c1f2041c82c000500e0101e8903455039000b42c45801c000e825036101e0396132000700c8641c010100c20500b06100c580000070342004051240e044030004c00b406440840a4505440d80d4040e03882c2405406048010f403507034668440126001076013044400c508483c14070816080b503118040201c2e10317500d030040050442c40d5200300c5159 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 341713012 1250 341711762 341711771
    0x1203070c0e0c12060907110a05010b010f02010608070e1806090d02012a1101060b1206031902011205090c0402040311040509030a0914030f060708040b0f0103030507061e020a120b04 79
    0x1807411150782c3c101e5005500301c414040d107540e50f5000300d130050000000340c200d074440c3c1c542000801406400c4400c410200381da0b500c50032902c20004a091790780e50b00c500c1e00c01d0381114030203010182c1011012a4032442d1480c0703055031b501d0b80b51074051030400100c07949800303a0002c201e8000034a07421700806c401019080411180d01c050300d111030544151440b0130300c050000d070149007040f4160a41144008050310a01181c0361100c81c0b5050708202c904540d0039209015070080c02c010310008040106c41c2d50f80680d01c440c42e14640c4c04030720006080c050803000700c41c0304140c4000d0096450b0f000600145101d40d81e00f00f800b00c1c1440034070041d0341c405811074400f9002800f22080c0c5a52017005c003001c580c950240c0c2c00070205041e02103428105240001d607498003814081008060304400c9050055124230219002c81d560f003540184907030020b01004002400030480d010210340d140c3c1042d454110111004802c488044803008120f0344404030560100c0d020100d81d0480210a200e4980d052005850610 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 341714262 1250 341713012 341713027
    0x15010902030c03061905030106080d09171c090302030604030c0b0a061503180602030f010f06031b08071107060206071b1205160b0c04032d03030b1203070c0e0c 70
    0xc071a400002d200701d029880117081541d000030240c0c0d0b0745004000240c003c01800e601c4520098460303003104000004203220f240001582c800c405150150703280100c014203074052442c03d500740ca0207046449681040340c10140440581d4042c40200e0040b84a0789581c030101c606840c1220140700700500118a007442e11008000305e071454184800350441920b8001090640401066800d041104d0060046c40c404020400300c1c5044806150580d0343c103888000074196035110490503070f150b00754611490107812040c03000f068020049180c210400c0e080c4101f000146000d02843c0501681c80341e40180d02110502841c2500040c0c801c0707401e002c0100c60320304c2a00c0d43e02c1c0c02c00707000e07981c500803005c1000000d4408086642404040c26035913000c01e40c42890b0900c0103c0030700d1504580406d40c0c100e40034000c0f070000001250011250704c4205140c0026024141e2800c0e00240002100a6000300040c6c18100f201c841c28030081c176446200d115a8101c01e81019166090454020980c042c2c0711010050003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 341715512 1250 341714262 341714281
    0x3040203070e06061e03070e06030115080a1e090605180703120302041502070f060813060b01030b032d030901021f060b0a050a032f0315030a051501090203 68
    0x41a141c910b41204010340300c00002c0751942c031030148000e003659501103d107080780ca03041c2c00450181450360346280001c1c11400070007660b80300a1041400041c042e0070035a24042c0150f4850781c1c01403a603480010300f40c0c403130010400c0c40701c40007a100e04c0780c0782d403001040308100481c0304941d08004030003c00010b03c00708542280d40c50b005404060010355100f440401c5140c03007501290701414004070362041220200d40080d40da4080d90040d204002d03024440403401c0d511811049214841c10306020040880a440d10380041c0780543c03802d8101a200e4108100d9071300c00700800c03680d021180400c0082c610000da400e03003001051600c02d0003a41c03c01c1007104601da82c00074901036840150700c0c3e2031000c0c50082c2e03088030080034154410b1030540804608100d0142c1c000740a03080118054a0a00001d00960b40c01c03608840078900100c0510b0350903401c104803d08510280da40018200c03808980d01c107e03030000928020a0b20b0040302e155000580304e50007090486429401045001c02c29821420007850741c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 341716762 1250 341715512 341715523
    0x302101401051507083702190f02010e0a0b09040515030309090709050d03030c030b0328030203070b011412030a020a060b0609092e03050703030e0111062a03040203 72
    0x10710f40000c8041250302c1844911000c0343d04460581d01c1d086030110800034425503802140380b458014450562412024038000700b42c0207016080c68407100b500f17900c55603031800030350341741c54050341000304840c2c0c4c1905a8407980900400b03000c40a2095486481c114108411340d0001485504100c510054108007074400001340c0303450820868000d04207a8030070504443d95441540702c80c1d07000c02e059400200380368040e4043c030400400ea0f9801e0201101e440141075960810b40d078440c0031404a0f5140c8038004145680c00004e262091060701e140446e81d490f5410700c441d007a08030011420218240456030320300010140c01510142d4007079801d0003400000030b9110790740000042c165540341c58001c42903035030b00003c03500c516000420040071420052070701d625865009044459511881001c07000010030344040da005c030ba52080090156070300b5580d04841c2c184610601c5170520000e200b10082944082c8801e51003039010001d121a41402c6e220075900302c401c1d141d039441210004105210240c0c801040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 341718012 1250 341716762 341716789
    0x345010e0c030f1519360201090303030e2b08090d050f160f0b040624030809040204031401090302100b10140c0106091b0f0503010909020d02040504030210140105 71
    0x458009070f5500c203c01403c41c0350034a03c0800304c900e00b10f07a10115144141a08503945840328280c107404645245031649088070120223804200151342c100f00084c425009004200d5914080d00c0381e00002408081c1c000c1240e0200756145015440d080c0807981c2d003c42120343c4549104d0050010308031920001d0458494213100702d1040500007440b040c00070745113000d08001a800210a50310507850f00700840c40710400c2d10122041c508060010060346900310304526003000b200480b078642c034a966207a1105503c0f286000b500f1503001d2100001040034141c540002800700400450000d005240003810300c0c0500600240191504203000710319164800600c0017010541464a214641c16074401c1c05400f4054000140b9828540d0105640000ea0840117101981401140ba9008620810b50b40c11a0380c0341d41000081082c8010004c00040b900042d0b54540041c0031246203100e5900030400703071102110281c0140e0b10115800401140d61311910080c0903020400c3c5205506040000d48240e12246 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 341719262 1250 341718012 341718043
    0x40f051303030c0c0b0c0712090501120f11131d010f0b03060a0f0b0417060f0f0705090d1a0702120d09020a0e011401140345010e0c030f 60
    0x2c98420500380a8004050803175082002c855652030203544054095100d01021150284130f002d000c2200b500610940c8140c0714140c48010310810030000a0000b0300d08030395100c00241e200d01c407480381003080d5001003e0915168030503030034181c00c0021840d4203003513000040b603200f96218010050030846602070410340fa101d11107642e480d1220400a400d1043c03540001901c2d0400190000e500000c680090045034a49542c40b1405065000416214082101c5255020140400190341c90007072004041c0c2c40356141c1080e80c241074015000c14060b11514008403100c9403400c558000503000c1000e00c82e80900070384000c6c050302c00c2c003e20290031809070010441c11142c84040410855480c941a0400b0b441906188181c40da5034055000014104203001404102c010b042401040380c858112449003410850b034041c090450303281d09600060103103811003a280c0c0c105003000c01000c40b0184a1041440c07100100e09150425031503424101c404600c80e21030f511190190a0390b490115100b00b00340c0d00315 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 341720512 1250 341719262 341719271
    0x40501030908090316090c031e0905030409020a0f0801080d140307020a05012901050c031206130504060c0f090305060105130b0604030803040c0b0702090a0902060405030f0606040f05130303 83
    0x2841c051003140250003c1e1603041c000d40c144255030400c0100700038110b8080e0101802074908a44050302111481d4407118101e544a915200380c09045d604601e2003580703d8003c41785040d0f541c6140d1812030700301414510000e0010f840040310951f0040c1418090240c0d0001303000403000c040c601612866030030714961248007002c000906414000d1211080182e0800020311180000100070407401403444560180001294558006540310b4815240c048a0301001103151821001110400c150005c00ca1a404605580911a4640c0310700600c2c0c040d80c401c03000400c45015800000c0c00241c020f1101e141004005a000c0022441c0011180c0c1110410355500c102039141d0481d803c01703440449100d0380c06c880b00003000010444c14400640c4204d003d410300200c40c0b43c546406d034005101c0c800000c3d41c0079000c40d01007405501030b984035150051000703104a29050b80c0740007003424024039104c2100b90b50040010002c60703080600440c09a2403110030704200c1c610340a072014a00d044000005020160364 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 341721762 1250 341720512 341720531
    0xc040507090f090e010501080c011407150911120316171b06070f03020a0c031d120a020111060702281b090e210f07080403060902180c04050103 63
    0x7605040000c1c040c4400d0008640c1d44411101c00605140074000741c0c99880c01d400000e0442c004111a83d15000503545d000002d5000c0c45080305070780100c041a21840c00c1e1820015081d125403107030f044032030b00ca04121550483d411081021141d070084070315003075810404c0b103058425000c883c1e08481e6648004801c41c504402d4102183d2401064062440c1030801454107a00940000360ba0b889000150354038062110b840394105c003680500c401640c045204020b40c0d0740002d0040c8505980c9007041880c524040c10b28000145a41314201802d41076900f2041201c0259603004200040800980000b40001d09200400941c0d400303c404010f20349075030600140540e40300d0500000415500960383d120362400c2c1812400c5c1c000040e2285491252170a1a0502a0080415507070b2039102031200c0c04103c850400c51081d45540108a040c4417180200201800206844003620146004050008a4520340d01c18800c0c0f031108406484030703094000c4200b005202ea600100c8096070300a280c0880c20010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 341723012 1250 341721762 341721767
    0x50d09030507062a0c0203071404021315020c04060305300a170105040905061614031e060a121506170a030206070f0903020409170a08042001020c040507 67
    0x24805000704500d0a00c8100b100c80003c11440104c1e1040c80304a01560442011040d80d00082e442d8000350540c0150710104130052480444241c96240071348050300c1c16180a070b40400b02000303500520301544610300e0a60400b90704000d1000025000d80d001c000840c1152600e03903403526001145107446640c0c0c4042000d079100d60088600c0d19904420013500e80010820103400340c41ea545070792640d04100c100003e0203103020700500501c0c0e40c110020705103036290341110892140d03080b41c0080c14086440181680c6070411001103110b00403030a401140744072803000d000d824120142c4064030482d1030401c240040c40300814018402548104441007601d400710b003600140c4015848500881a800c5001141c01c3c004a82d80941ca4825070a450380d50340d0b0b524080d91050341c3d01e103003d80000c1c252102800142450b90008038058092014040c07100040002818554018004a400103034110140020881031521103203811030b10080048100c800307000000e40e12884008094800c0c2c4d1260041500380c1d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 341724262 1250 341723012 341723017
    0x6160c0f03110907090e10031203090305160201020f0304141005040f230409060e0d03020c0c09062e0207050901060804080310030b0a02070302100c0512071b030e090f0403050d090305 80
    0x581446e1614980700c035000241000c0c500c0290780c0c1d07110f55030301d07101c1d0148a40f0030208203580c1500d0340c608042820750700d1302644802c0074049065210790700900010400400181c402032068075050389060620381d0a02003507801d843c2111040c0300043c0014407a07418420704000c00c0c2c0d0340c140e10903d0410003070a641c846d8010591a0650801d2600c00d80e0000c0c40304c0740d004061a010000d0403642c540e064210210202d1082e503901c0342c06500f16014802861138100d82064004000070300910102a101e40c0c100085003140001900441240f030a900d40c4a0301405014014881190150311561403d5400f610800000741700521041c000000120042c0340241100c02458004294103100c3c64030010040095007d0030042d0051711030600400b12041880c0660040030307016039541803d1403014005070710f070315102400d16000c9c021422804101458080007008290707000307507105045507400205002d651303103018100000440b410310800000c40c0c4c200381240d102c4607880100080805860904a41a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 341725512 1250 341724262 341724269
    0x16090815070518040c0f0f0801051e130608010b190609060e220b0406080c0d0303110c0f030310060809060601050f1303140d08090d05130506160c0f0311090709 70
    0x1840d003030945040d1540b0043c02001040c0940740c4007864454a40d098460023400d1045a078019040030b03a5540c849d00d11550b0b1074011101800090606011201c0c00003030320120f40084034030769500c00e841c0c151494555801981c8000090307403440710701c0c1090401030640c3e105000b4030082c84a8005014015200c07501002600b00c042088103030184040c070000f5014081e60720050784524200400070468003408a40d6502d031000c0182424514500f030399081d4064261b0484036125400706111520314060701344130311110700c2c0e002c1002d941d807031509580240080d201a040350080100210030800b0f602c00010b4015004542401d0841c0c13181490921440300b849519001801080c1c61040001004801843c44598082c0c04085d219000b00183c070489a108003251100d03503c1d4001d40100c807010f4082c40007042c04841c8410418001b03515100402c4643d40503000762070750460060964000c0c00080001c42c1d01602070200407070b90a5185842e10046200d10032040b9208044d0079000c2400c0c1c0b8043c0b0042c1c0c008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 341726618 1106 341725512 341725519
    0x5040c02150403031103041113020c1b0604080d020105040c0902030405210904050c07020a05090c09041d0706020703030f0302030118051003080316090815070518 71
    0x3a01e026205509050b60b501003c42c0c0c0404039001580f16600580800a00c13524040502c018100040c880d040510f1041c807109002d002c010910444200c282c0e43d0118803202508002007140c46280c1c4050154490007005181090b01904414840c0303001cdc82e54010303010380d03c1d071144059101c1202c0091940d003103a450b108120043c00c0e01d12010b01081d16240f410b000c4583c02103000c0354000c2d0f41800500c0d0002c5503140031890305410b2007000c8d080035683c0c4207031401c2550110181d401041e050340d1286440306252003001c403a184074241d1005c0010100c5007150b82d0b944001e51558036038041900051601864103419500900031241210303000b481505216461a05400c000c2c5400750001862030742c000340020100e0300d01ca002d140502c1a00100800c0c910b103890024020154551180501c1e0300212017000250700040307410b540c07005940c107103555034010700d420050f405800c00840513070 = true := by decide +kernel

theorem cover : BRFrame.Cov 341546762 341726618 := by
  have h0 := BRFrame.cov_init 341546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 341546762 ≤ n) (h2 : n < 341726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
