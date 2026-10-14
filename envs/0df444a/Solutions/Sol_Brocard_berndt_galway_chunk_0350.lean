-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0350
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:21:36.104003+00:00
-- url     : https://prove2.me/submissions/cece0206-28a4-4973-a392-7b4ea5106176

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 62769787 ≤ n < 62949643 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 62771037 1250 62769787 62769799
    0x1e0e0d02160e070c02060403032a020102061501050d06030302031902060708180a0605070503060a0506030108030901050d0b0d0f0b010b030105010c0f170324090c03011707090f060501030c0c02 84
    0x1c0340419202840b81d00501001c14000b100b0303981001683d880000f08091842911410200d0031200a02d0b00c48203104407240f003010031003061507009030703800040150f440107441000d1300d541001600101c545002d12000321045904000001c410980c0200c0a0310124180c4422941040d810340c40480e582d00c819550b0101080070400130600d2050b00d1824070405401e82800c072003400000355210000c0350421507111380001e8010081c4131031890314415450003490211000707030a650622403184e40f2071041c0c503c507a05001d40056003800000007500010b665940c018502194041181000503007200c02440c101c0d20198560004240c0c600e003001940d0503984103940d0070074516030a5a881c4010b0170240415980e006c034020700e140304055040000d51160750341000302009441102c220700d80c540300c0040f150b4414040798040050004801d42500d044501d0440d502d464a17201c07424542c2001425005010b03102d06000312581408255002501280ea081e84d00f0002001c00440c2100d00407002078000798450 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 62772287 1250 62771037 62771039
    0x3060108030901110d0f0c060e07060e100c080406030914070b030f1308040b0304080909040305090f03071410050403050105070306030210020604030c0311120c0c04060609080d050d1e0e0d0216 84
    0x507c14142034182030f2003030300001121501c0c0d070310180c5051340541c403020028070f512451ba40c080c10001144500c00c1c1d02e03400c0506c0070361ba46e40d90383d0740320780294002d203020150382c3d288202c00c1c418040444202c1c4010a400d81305155203a0030126a6680101e803070302d40368040500801e1180d1080c052218016800030300d50381c02e003030a011803a000d503070001d801500c06690034090b0018503a1a0885071303010b107100303072600b41e03690440805001d141421880401c0c441d40100004101e4242052000c803c55081212404061141c891058819014540000c0d0140d807801c020400441d0b0154060b01c10703203000715aa9203480622400881e40c0d95011100200000d14003c03040000038080e800311a00d8210201c10369200808500091500e60040100300b01c16500034a180d520718141445120043c1c8140d140c00504c5608011701195a001c081c0c2442c01080000619541611450750080009410424001000002840480b00500000c0a03041a90300035a075034140c0c064000508440d0024254444540345 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 62773537 1250 62772287 62772317
    0x3070f0305040201090305241024050c100b1329010e1306031203020306010203040e0402010201060302040f0930081008060f090706020d0c0204020702010e03060108030901110d 77
    0xc1c01e00900100d043c41000b190110003d0401c0c080e80803041407110031481d510742d0083c0b00004005000d00641c00c1601d003000b0503c160001c01280480d075292801c0d0452140010120440d000e02c11403805407007a0007005254001c0281542015015880c11500743c852035a41d0361400301158141c819010419048108200c2c100d201407070311800005050400c5140303a400c80c030206044841050041c400d00b2340d80d000034010418003501200007801d8916085003035160520010303550788200e018024400c0301850000341103a1003504448091580a48144030689a042c0700d803000c3c2c1100e0800302c40314030004440004004c1c0d49641e20580241d11213510840c000e0900c000d6880d0240503180007000c0440032008180311404100c258003e1000c00360940c0c00d407030080030440c1421180d800c0034003190400e120042440b82e200c04420422030301103400581e900d101b4801a115080c441d040315405015207000000da0100210141c041c0210a8a51441285111040d00d841c3c100030040c05000c50500c046c102c0700 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 62774787 1250 62773537 62773541
    0x1050d0509070306110a090f05030a0f0c0b040311040e01050f220503070c030519020306011a07210e150708070203102f1c0e010906050c070c0b03070f03 67
    0x1d04504241c030400c9440c0d0b150142a40d2aa00001a071410002060303a01140d00a0b201c100a0419441d04589541002e0010743c40b1801c0540150901d64a8220b440c24020324011440c000c102d0b0480c411756407990781c60005845194204200d100b10716000c02d280c442c401c18051030307104e1084084421810f96038002012403401341186c0d8540442c1d0700709030020006200304000c1c00c3d09401100310754020b518504d051490190400c1105c1c014200c0404440d00584000520034107443d0070341500703e44850740290503543c3c4c0c040e0102c041d01c00f26520701258000c0003003503403c80c41f0f0403e540e107856000704e0761401d00c146407508080c02d18888030100a802c001c100d4640207000003c6c40102a1001c1300341c081014015958085241c002045801c4120011711038080c50380001410310904240c1400e03007081103050041d030b04145039000d142e2140030340700e210802940500252070b0b0140082200e410008040456900006001c0314002c480180104401500e4000e480c400e0b10b0310b40c0d4044603040c00001c2200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 62776037 1250 62774787 62774791
    0xf11060402120111070807020a080d05030c030a09050a0308070e0102070f0e040203071707090b0909030304030c2a09050a06030c180915090510050907050105031b0a020601140f01050d05 81
    0xa4a95070f031300c0138108801c1c2c4c4030f0020000280a510010384030300d080c1c010802600620b510810484d44001c02840e41560048240d80c0d000b0f000007411505e80d501c030b4940102600e09008000c060380101ca509a0826400c040000d00410050382ca0f240e00c0440d150059031707280310b28050022a424089010013403800b0340c880c15544148050180d0300b141741c1e110004e00d4400c2c0b00c0407400d0a1600526401d00c0f50300042d1250400c000c108079050145420721581164032484041c00240401c0a407a510106000d81e003a140e074000c45040443c44100d03190107074075600b074105500130450b4a50402007c603da15005008403015a90000425015141741c08030600344600074440c50078105480320b00b2500402c18030f00c0c110f0810181c09402144210207494a0742c18010150a0034410070316050503c508040d000483c0803da80b000e00b0120307940e03290104a5190860821650500b5000000b4501011030b8041900c41c12034001d05450111940c1e003c1c1005035661621446a001403001c1c8410100c40d08160081a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 62777287 1250 62776037 62776069
    0x120c010f0b0a0b0d0e03040e0108030a020c2209020d0203030d02040e010f03080f0d060503030f0c062a09010201020c0a0f0312140601050304020f0a06030b01170411060906040906030f030f11060402 86
    0x680307815035560103042c82c440b090b48003108580003c074112002c3307a0140a150070010040342c0007203c4258040542c0d1030b03000340141c4005225503034401c50085441d605c1603254400d4004003101d4403800002c46940181d8484d028401c0b086500788000140e8500c201c3c4440c0a80313902c0500301d81000080304821b400c2e50040000a0a5035464100c00115a2410310041c14004c40103000b0079038520309800802d00c0e201c8040c1499109881c50101c02c0b00892000c0c000344400403a0300b1020b6036480c01440101c0c00fa00507802607460074002c0000b8007040040f02c4503440c1400d0b00c05e4540e60007581117650030318115852001e41c502d83c0f509030301c001101303584242c004680c00b0340b00901c9a418010f00314042110565140c0000001c01c0d03860001e81000d40e00003801603d811008183c2c209145060b640d1500304850f8046414000c1c40f011036000040d40d250400d98000d0300300c10404000907a9203051500316002940800d501103038441c551019040e200310300503075981d50420010030705600c0d19428044800c2001e600c0d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 62778537 1250 62777287 62777293
    0x8040201090b28050a020a0602090a090e0102040801061e05100908010504050f06090703020619091a0306130903021c021002180301060e010e070809120c010f0b0a0b0d0e 74
    0x1160040d010005800d6001c48074500f8078034900f001d00440520402050a0400c0c068103001d014840380d8001071441c07001d58030203000f58541500070302250000d007181d000a84158240034826060703000c1580030b4012900040c009109199803180420350b01502900d111007801407100080c03049090506403400905401e1803d05091070781c6071421400c44e8001d40c1c0496070358001c008402034109040204903044490070018003411031941e80020464455007115640300d0140030081940a4000c0e00742070010320780d8050607608015070700d80700301c0250700481d500da210314001d18400031b2010b598071464124a52540090440d045000d040c8840c150b4910004821445102d40e003071005103c81c00940701c0d04508007142402440d068080500390f880761341001c2042c03400344004106445c1c00c0e05585402c003945042049031512a00f03c0749040c0b000351014089c0100000030b422031350b17020551001e0b00c910741a00c0c0802035207008500304240c40600c2d10030b440004105010300402201144d02080b0390145a90403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 62779787 1250 62778537 62778539
    0xb0112020309031908070201050c1615021917011a120604091407080c060f030622060b030103061a010504060e0607020405010608090d0e0105030403050d0e0a140d0c0b0402010804020109 81
    0x30102c1c9070b02504d00b000980b114080c4407803035409000e22500003c6010b06941084a042580da00d480f0140da00502540886e080b0240c400a10360304032134101d0740c00408041240d2100001505030340d540c0c0030b8034a456150100004420800c4c0012030201c0603110386062a0015814024041c101c000c0d00096009d5511403450001501c0800b140c0c02404898024014143c9841d60305800c007000c20403100e024800070070065840c1c1c0e0805003160790024003105c0d03240d462101507281e0083e0f40f00c0f2031000301400740360000204141c83c500d801f440c101d920801060021609842e040501d14003000d03400390100d0001d100500086025281c1e01d400004068069801c15541e03400140540c0e03020b038807040204000f00184011000184821030f5036081c581090000c43d074000d00024010300c4010800341c00c0003400700d6100c000b84216004070300c03481c03546801c44040c00104d040040c1a0504900480e680e4071807039202c0300300540914520150541c2111265400d80c1e9103800554260100900c202d0400c100140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 62781037 1250 62779787 62779807
    0xc020d02180108010c030c05072303120109050a0e0a0b0109050c0702030a0b04060c020703110f040e010e0106060207050f03071a090d0501090201031a0609010c050102090303161101030b011202030903 87
    0x106660080514100100e0b16410b0b03a04098101c0d40b500040d01c041003802c22000340424060781c0401c0031501d903050707002b500c8040348010314218011312a03000088070140d00000f8501c8401e400141c01030302c18500400602d807044840c0c540c1c40b040000c0003000b20720414010401c520071a1701181e4820803040c10340e0300d4000711340e0001b82000a0040300300c921040103018802440b41c0c520036081c04142c540005d04105003151103440c00c0341c18400c0682e204c1c0c02d00c862034641d00d860300d40105102616540c02403101e4240c1d101604e010b482c1500403a40184241c4800007010300e030100d00c4404403071000d806444403500f000c1126150408000a40100c841e0800a140b0207071540e1842c1903499004000004540d0348610005003610180c2150f0000b208450742500d00f6036680e402214040c003c24280180f1248441c50014064098405290760501010482110703e2a26210b000ca03000d100703503002c021381d81600b00150300f01d66034007440078001201d05001c4425250700ea030041d908000404210b07410000d98074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 62782287 1250 62781037 62781079
    0xe03010f0c051c060509040b09011b0e03121c050a0902030706050a090801020405010f081305010501060c15020c032502060307031e050103020f04150f030813060f0c020d02 75
    0x46007000542c00145403000c008081c2e400040d0a0295581803140d14035090000d40c200802800151444000303c1c00300d401581c003507010b04000f0200c081d0b0325041d40407205000d09014180b5900c13500900801803107540140c200c804551859200300c50700070720002c14085010040030020156140541e60308141070241c0d40804c402d10050449640d035568a0128000080c51030240d44c0c07040010b03a00500c4103020980e00b005011080d41824a41603072142c0c1c0300e200c100b10340d441484001d000d40d4605000481c1a0364030030170744140c240c00740325075829240e207065448040b48038054400741960020312139464040c1007130601007005440c20043c41c030b95120070740001d4215481941c50300c01080d650514101d43c0009840c0c20030000118074003c00696141d41c010840192030301d03907090322032595070206102e403455103031b0507402130202079080540547c0c581c50500007540c000980c40303546045440000610b40d220b107410540c0d120007961801d0742c4922640c2880940811113408a902448040c0c180e59440030391 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 62783537 1250 62782287 62782301
    0x503030a0b030d0207050310020702060d09060b031603120c140f0c0f0402030415050a0e07090b01180602032205040e1c020a02060f0c0a0b04050a03020c010e01020d0e03010f 76
    0x28000201d41074010101441c11842034003400a541010400300160307600032a4840740740c1c0c041400544e44440d548000b4625200c0d03080040c6d5218a4a00e0305010f00909600c880001681603080383e0b00800c600e800c22081d0b011034480140a0107280b4440d409152040c03085007255131144d054142da110350f03d16000d00345191440b0071102030b44a0b240e5083e151a00422402ca00081a0f80443c0303582042d84070508a108140c00000d603440c0c4403008600c2c2008140d00c00000c00052505946529849528480143c02040c85d92400524076440040b80070040a0b600c0342181c800390011840c00402c1d10380300b240881e00507144507500d800c6000c00116034445010b0301c207080c0c00001c060a1003c00c400740a01400081000400c00c40d44403125000058541d5800c0721aa002498065a02c1d80415521103140c507003041802816414001c01340300400c01c00180c543c040345c4c401d17025600c80070030034001110175002603212540141d000500003004c040c0030b0040c0f000f406130050008500c01c0b03010b400308000d403000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 62784787 1250 62783537 62783551
    0xb011407230312090d090f030b15010207050301180209100e040f150e030a1107050127030204020703050c01050702060f070c030c0506090a0b0609070c0b0702070509160e0118140d050303 81
    0xc40d10344405a19489810000500200d0015003c41e43c08d6440b1110500001400c10348007003100b030210a2260700803c409002400018000c1c044600700c030744c641c0080d103140e0004a010761031001c0400d81c8400420303041000e4501d02504ca0085644545420390041d102c282c05483c01c801c03002072928001d81c24002c09900141000041d5524000058000d0001e81e0201ca192802d401501050203144c1e0322081c00d0074880e050103c1004015000007800513401800c3d80004d50081c400145ea20030140c000000d40300c1c4400b4000200a03d68900398142d07100d0b003045501c00751145140d00001c4402d40520481c440ca5806454403412200e466560185041c5003076030b060409501c584801c01c00c1114060b900390303000c0d01c29205218542000701028102a40400004004149030400180914820400f4400406000349060a603003486044d05c2d9481c0400c0850701d000030701c1010b410056500801006008900718030700d003580384c2c0c94804401400546c4100070707a884801c1e0741c400000314104002075030103800c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 62786037 1250 62784787 62784793
    0x160c1509030b0a060602070b090102071e0609060c050703080c01020c010f0e07050d05030a03110d0501090c12050f041202010e0109050127030206010e060105091002010b01140723031209 81
    0x200314280441c016070010f0400b18064100081031160503804580d06048484041a09488507a40340040c0d0612407650418140c0f10050614440007002c541d610200310380f6107445a0b0280c544030760048076081c41c00300f17000d0300780d5203d40b800b00b000481c004010151060680001424050075165441c25101d151042d0540c1e2526000c0e805014141488013200030002280c2000aa225030b40e0f846403240291003400c002d0540d110600c0005520200031100084070f1600200499a1a041c008004017030a9045178001030590980d100d041505228043c043c4018140b402a030b80e03620799a0020b041041030500045540ba680d00a4062100f4091005203620500001ca0542440c1000d0340c4030702e041380b01c3c80c110141e071041e0300c2e400b00d1d40201d40300f0b040d19820316005a00d40d889400594040c8905d402e46500454410580202e5a5065021f104026000d0340c0d808075410540e1010710007030240d40b4015101084608089505480642d501001c0e080710301c099a04043d00b0030f01001012204445900440d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 62787287 1250 62786037 62786039
    0x7030507140c0a0f0201020f070e0103051002090d021005040506070c1e240c0803090d03060b090f060d06051c1103010510060e01090e07030605031002070503160c1509 73
    0x39400004120404545031002070800d9184014141ea0704840302d00a00020388009824040d64428803990083d12a01000ca80038180d4075450864484000d100544040c01346400b04541c1d41c1c694000c4813000d1300024140d8141e0941e035001c01940e140b08030001700c02d1100030080050306803104406000c140e03000f08120a069441c0c03d03100813480a1041c1007140b0403040308002e00034402c0d425203000d19401c90229001c13580c5004201991106203444020b40a03060110030030141c3c0030000b5060f1150b030800d56052012aa81d0104c4441501804420b00d0340410514001043c0c1c1c1400409418000c0c0c01100102d0f425954201051050364202c002016084441840c0c02c2840b80f407815102001000f0f82c002c0126180003043c442000308103014507030400551880002d110ba04c2025080f0103000207103a012824245480c0240c000c2c0742500c90302d8028000c20042a6041d803141c420b071005c41e40c00c2400f851510320b130401402251040c080307045850500d100004a41c507a006602e038822110686c944219103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 62788537 1250 62787287 62787301
    0xe0607020115080601061b080906040e060f030109080a1409040203040602070c12030903020d0807021302030709050d0c030611190c0204050123150c030d0b010e0114120a020f03070305 80
    0x21200d0b0820f101540c01140100b0615074402c1c17640c2101ca003000f244c98007484031450045400d101e40f4069a80c40310002c6400310f0800c0c1ca507104140521401c4030004a11541201454240c441c94000500406402c1c010840c81d41d0003611034007079840a0805d22803820410200090890300191015176086a001c1490000c010341075103100d028001c0c050004414120981d03000b4100423140c00000d010300e12031302c2e21030204131b8081c05070b500781540200300c0d40c0101c401070403e400a40007140c03207034009a105040042d440c00c020340c0d840c0350030750001114007542e420342c4c13501400b502c3c404003c2e00400100b0007440030700105030b06482c90700030421f070386003459401e00380104000d480c0182c101217600e103a03403400780b03600140420240c558044192241001204035011010803030081200160750b0340400103407841452150344c0003800c803040c2601c40340d024003d110011190210a42802805070808001c50b80c00060308000c407075840a00b050001d450522a01d0400382c0c25002070f50184003003502e500034002c035 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 62789787 1250 62788537 62788571
    0x100905040e030901021e0727020a030b0f040e0334050601060206060a05030d120209040f02040302041103060306040b060f060403030e010801060e01141c0203130611041a0306040e06070201 82
    0x2000c81035039200b4001b400d8803a03140d180c030b070644180000800305219103095809091305441e090401880300715192245020082c01a049421a4500c101a0350940c8180c1d8030b0710740714080322419040029810041c0140c0e80520054800840310003500032685000748030428007007410f026034824409000154502100a807030103202a048602c5500540001d00007501c0020382c00d0301442e21071800107488009503190704001d00c1764490460304942072400c81c0304143c10310b8009104491003580c00f00465901c0426550180c00140da85692580218010901003940b0710046038110030010101c84900e1405c82c0000c545902591040b00494034040c1d10321403070368200140354018541410200410303818000000c0c0701800189200000000c0403032000309225911081180720317802c8040440d6241045103650ba58040020400c680307040c18018004d403000f04083c19201141c960800030002c95180380044c0304039810080c01540c006075150079180030303403408121031805480d00380c00002e0f82e02c3c51820a804 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 62791037 1250 62789787 62789803
    0x4080c0c010e01051c1e0e1014040215160b01030302060f070203220504020703020f070f0e06100210140907120b0109020304151401090b04090c05100905040e03090102 73
    0x70500600c42007400c07032070360840221420400e4007001c1c0e60241c3d48403140b40c1c1c0100b40c1c40050704140341803040444018905607002d00882041c52044488501ca0040b800090300c10a1200c140302d62a030501040041c20b0800f44890036038101d4a04600345102c503000c19004000040041da411440600100140360301480304640040708030803405124640010301a40d28456114041e5202054808460050b600d03a0484800381070006e20540d6079107042d007002540c42400103042d5006008200e000100c1c0d5504440110446031100c10704000d95542c00304015003129803c1c010000e6010b9403032403010019946c400c00400450f180c9140a50b07040496902e485c1c54415001800170f00c10520401020600003e40c2d1411208031075000350b0ba03035803103203048962a040c80444a8440b41040000762142034241b4440d4142ca04240d402c22130304400350100070a845904070080d2204082043c20f10141c2800440180b1580c1581442c8004541c0e031000304045900d520111100380c1c201051442c429039052044038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 62792287 1250 62791037 62791039
    0xd1b030207020306150d05070b0c0d0c051513060e06010905070507030e040905030403080705060f06010c020f041d10020712030603051e01110a0804030306060302040b180a050301020304080c0c 84
    0x5040454581c0484c0da64803001d05403407480c02000c10840703026a901024121995400426100415514a41500c0b9904506011036050081c0e0484684541c40398001c1c0c01410780010003402d108034800d100c0c0184100107030100d40184051004400441c481c1c0c0a03110842d428000101590361400408900b11600a0110010000304000d19400309602180e04d0301c18100444000540e010310785401403a5128580c0b00420055011405009000c0f0201d61288140608852900746685144c01107a1842c13000070700950080380780504a0301030510394003035030b202c0c100b82901010f82d00c04042c2c990300c1d15161210b4081080c3c0c0019601c1d0030040c0030464540001500e0800303100d814219a102034540c41d0300616050304203c1c3c04411006041c00350410648004441095a560a12218003c1410504480c19408203040c490001401c500c00d20845040b9612030380e80508107407000c00110285801c401407240c1c401910342020940d80d60a100450041c3e1061850b659645003102c5602d05100c01c0c2d251613 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 62793537 1250 62792287 62792291
    0x709120f020f09071205090f121803030901050301091e0e010903030f091a0a020f040306090302060708010f060e060f0414091305060f040f05010903050d060e160f02070801020d1b03 79
    0xc040c00640000d980c0150345c044800110780d940d15030702c43c01d00c0e028030038003888414451b0300c84101507446000b00a02c801c02103800c01c902058151020f00d5620710988425a0010318100010490003803560f100310324140c070940c010340b02000307070f4242c0070150b901c900030445080e50340311400303420160035219003040c00d001080144000c60054445c0c815502026011418460701d480c00600c100356641c4c1203c42542d900e0300d050740c5454590070440010b2005100480140c818100896101c0f4003402d85a03040761500006541030301d00300281100e5680c0c0940d40e0503000b40080c403c00898481880c00b42000d42003c4a80195601074030302005212600640089403490010740e445022900220783d081e07010f402c5030304c2126244c540c0e01e0585043c1024000242082d46882032440802d0343c0b04008040740454400c050001e01d13280c1c0081c02200300c06442c07180d034801c1c3c44a0944052070107030000c01c8426040d80183d50490360765224003402c0e030b8800c009041601c1d51304e610b4001d10080303102c0409a080c94030319007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 62794787 1250 62793537 62793541
    0xa0213092301151202090702030d180303060602032805090904060b03010b061e0a09120c051003060602071202120304060507020a060c0b131b1404060806040b0106080709120f020f09 79
    0xe101440205003c1d005106c0000000c9140e4000c0080b0341e50300c51030b080700700070901c0586000b81c80fa2a41e042c0450001c0e003407180001740c0501c00010340f82035101d92020300c02070074100d01081c0700344040701c045035007405030a1102c011150f070340401c2588680e00a903400f0880c046c0000c201030840300c0c008003440c807034541445003a24040c500d202070f040f0301e02e9402c10700340c1c0c407060700c0f6094500400681c0498140080100c6590406c800501c40d00210b540907101c1c12980160810180c05840640c024000181d000c1c1e079007000044a9105e40111650004d0070000f41090740303500c01411540039400441c08610005200011402d2a80c014070041c64549001c3c0010115035903080c09042c4058411038002809010aa05000b03142c0ea03001c1491480c10300d440721142d540c1d16140c0903410065081032065150500008103000b012400c1881641d001c0074194840c2c1c00c0000558200a0251499040145508001c41d0501c104c0c008120b03a60300852221320602c5040c410400318082c45501c541c01810302a003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 62796037 1250 62794787 62794799
    0x903050c0105160f0e0409080a020a02010e09090a0209150a0609060e030109080d050405010b030f07170c010f0804030c0611040302120706080106051b060703200c0a021309230115 78
    0x203a1a850b1506181c40b04c502c800c075400181c040d02090340060208d1800060701019540c001460010a034400e80707407030a80036a52010802441d5003115161340c1901300524020062600c442441c0d030004071040382d401601c040c08042602c81515030043c102244a1039000c0c45000e810003020301e9003400480c001d0080300607903941d4900b00d02581001ca000d06845a020074100442034000c510b1035007000c0c0441c0d00d02d02c800e076501740d651a420b21456200c3d041080840741128008541071034032040685640c0d96568480c88202d4400761b0050040d800c02252035a4140000d07a9400391040d0404110703071035901c590a500411480c007105120481c0580e1100a0401c0755580041c6028116401403d10341c2d240d207843c513450401c082c40c059020720140211010804402d80560281b07611241c00c4c8403d03050510650070109003441160710207074aa520100c0e00c5001441c101c4000702e07922000c8c1601240c0541309a9074000313200034000c0d24040d04211031040f070101d14400d00c558080040c9116446100704d01d80302c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 62797287 1250 62796037 62796047
    0xa14030a0c02010c0201050c0a0507050a06170c07020d0b090c01030f02072004020d0e0102070c0f0605030c030604090609030f020f01060e010302040905011b03020705071203120e0106090903050c010516 88
    0x1c802418419070300980c000b96805501078449402075001511031500f101d10300144c4880d030364042c3d58400c1020b4540490064401c211340d00c01243c5001c0c2c1a41e640c2c84000c0043e800b900b00a03000ca0340080c5d48040c40002440c01c8000d82e000785042001099141c5c0c4250026040e03542c00061034194034814808007000c84c9602c8004021031803202c0c02a00c400e4004800b0502070311644800f0031000f4100380541000000550082000074003401c0c914011f07076120300c0200c00b046480c1c4113031030000d001800815144003079a0015a0000301c010b0001480c1407403984d41205841c0518029804107200c8058549926018440aa00d0b103000a00800c0400c0c204510140101c50602029024642d940300c22010000c2c2548001c1c1e803194410b4017001041c20704000180654040074040701d09019034440000e0403030945100742d440907455190011401c2c00400820000c2844500002e00d940d200c900c00500c896052048119690103a41c0c1c0310340d5102a103280b24292680035001c8071014240740309600019600c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 62798537 1250 62797287 62797307
    0x90405060601030e010e150612030310090b01030f0c02030904050a06050d03030b03071706071d0a14040b0415080f0a030e0108090c0a1502010b09010302011407050a0b090a14030a 78
    0x900f4006030001074407489a004114041c00c11440348102803103070002d66803000b2242e109034011104511040c84000b901612070109440c20703a10030044000c00d00900302c0c950004d160700704040c500002c0c2400c02d0070104054600324074003040542c00000d0070340100d003400d000701c60f40010501000e210701454680800c0c00c101072041c0c00303002c150343c40c0d43d4819290b40601252006141d0100c402e00c1304464848610344600040c0e0700c0c180403034404200c07806400e200d070400c1c0e40014002480c2a03200e6180c080201614904d201b42c603584160340754490704082d07981d48203c6480068180c840c00c500b90804140d5803910716246100c1c4541d1740042000e00000f640292030f0984440e0a203032805036902c81850f401e250030015143c42c0c0e071050300800d000c0341e8484034a0a03501d1800307043c0d000b40a0311040d0024082404002e000103800544150301c02c050101c018801403000522640456005800589402c1d00a007800d55119400ba00068900d40c103100c01d5088801101061a000d1444d01d003160001a000c8940707 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 62799787 1250 62798537 62798539
    0xf10050a0b0f0c03030a060602100501030b0612010905070602030901030e0106120807080d060b0307320c030405150409050726130819080c0c03070602181801030b01050904050606 78
    0x700050501003060000c040d01c81a02109007200d4403414400d1903080541083e007da10014400c41800c40d0565082d070207407a0483c0d420690800e00c2d900c0b660305015070b450074103011042642d05c510301070001503420410900104055805903448182c2400010252101d40ca100c8042c3da0612600380000c07502c00c00d950308540d074044141c41d5101405d103000c040710302580800522451030058002081c50714100118410b00980e07a8113903a5262440b0b0f0040030344102042c20411180242e0711040040e00c40b0020038801801408a0381000e80e42c43c005050050300f0132100c180c5210202c0d041299a046009698104015061800c10050800342d821400e0301c98400386140c0407000301c082148115110f0184610755081140299908182c440802c89900070b003101b4030001d401c090011301280c02c407005440c016a03000c4059841d041c130903142c1c24040e400038902003000032450525045035a4a2031010484054480000800d0391315504003080c1301c04059000d9030088054404003c0090004074803c0e6000034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 62801037 1250 62799787 62799809
    0xb06030d0f020721020607050a060f11030403080a0e0a1a0106050a05030c0a26060f04061406030a0605090106080403230703081003080d02270f090405030f0708030f10050a 75
    0x71320013000240c20040d5450294201c14006100001d000000c55541e900b60300440092041d09420001c030b004a0f80101c12002500e4001d00c00319000900c00c090700360308030240e10f60100e0601603c00c4414184a21031f481150380c030b4841016903007140c40b0171038030764010702c0a81010b90030700e009154003501c42e1000800c18400ca10000a524100d503004405005004980e0a04010001100411340d01000c0081c0c078501d01c14081560b28042c580f425000d05070039140903810a4112400c031105104150300090000000700d600d581e80031603151100d504103802030040c0d540b036071480c0c20182001b070003900359100002c0d5060407003541e804114100c04211031103140c3c180b402802c59034a0b10740084c0c05050a400080c14804002809121300c20680c000d00100380808080b4003000001c120400300340c0b03182c3c65219802259180000d482481e00001c610f0707002d8094415a4603008080300180d002c3d50040504803220b0101205020940b4685214140d2000c451007004a0007802c00340010700450192295444040b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 62802287 1250 62801037 62801069
    0x90604150e03030c0c100504050c040e0a0b130c09090b0103021203130605040503010b03010b1c030207030b0a050f0606031009051504090f020103051f03031412040b06030d0f0207 78
    0x585035901c800a840c0c01e0009582e140d040282001c0b00c1a80958820801c0784580c00000040f030280c1d10945009a0380140181010101c400a002c040c100c90724460000b0b02840031040c0100b80342000e814400c2410100b0300300c44900b9498801c10001c600c0e089210315524003030302d06002402108a03181581d404448542c103440e40903110518610800c40400c010142085000800a40040c054800d41d0811002807000420071001d040c00c03500441030041e80265071021a4000030021054800300c03e0091040c4da8540b5141e486402044000f51303015a48540d03036404100a41c900b013540c076034011404444540c42e5080000c3c0c0c42c000c3e038810740a4401500c0c1c1d140085007280c045010200074034440500248031380015820a070310400e1082e10700344d000c07d04000008608500c00010081c0c01402c0d0078250040070704640f402c480e903441040031040200c00800a51710000c1c5801946c0748500e1145411000614080050504044e000042d28041c046800d0860418540120f02c02c1d01b9540c403d81c82e1a824 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 62803537 1250 62802287 62802323
    0x17090a150501031a190b0619020606040501140906120123090709091101111603060203041401020408030f0f0d0203090c030d02010c09050d0c150807080615160c05040612020f09090604 80
    0x520640314201c011017202c24008d440c2c9600419101d01c01c03c000c581c1041242e903290725121030f070402d0120490740090510005021460644400344c24420154000130303034103102000940d9500307107030b1030b41200b8420400104152a101049100e01405010318240303d207550076503c114080202e81360360350501400e03c0b00480c542508102c818448190080341e054525902c1c00c105009503c162000c2d2400c08150030388260305003050003120119030050b401145007008820400282c0e4015862100082800300061300c1e4001e0140061401400b00d200038101c1c0b440300004162410200c00100419a41061140c0c541a90440c1c203030390468005031740204007a00b0303d03d40000849015040260b404d690101c2c0315040d00c0d1701039015440703841c40f80c4507403038146c80e450b0400c041806c68410821040f9000c10403042c074510000f08610b0028440d01040800715140c800060a44016801c1480d18245550040c07056203007001209101107001e072113280882c1031030070109489440050000d400c50911880c2e100c40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 62804787 1250 62803537 62803549
    0x192c060405090604140a0c1808120703020102281706090a020a0504090c030c090f0e041e0c06020309030d0c020307030308090a0c08011a030d17090a150501031a190b 72
    0x15014030a04a941d051a00c06c807024001d100c401d0141c000038000210442d4803040b90306240c8151500e04000301072089885105038429800480f0413411550240417400c0c40c040c00c00c80c0d0b0030300010129844000e28900d060003d09204038400302100c04a22441400f0fa580c070346800d0290011150480540d8410131641c003503c0f00d01c901c0e4001d402c10b52820310880801c650543c40841d00c200c09544010800769100d400cdc59140080b4010041c0f024020008030b00080c0c50080d040109105c1109090002c020b20f0301c0b0301000b210300d5400700025030000100044030340340501129042a5080c00c118000121540119a80343d5180c04014103108803a004034031041030420864802691210701220740d5602e540701c440c045c001c2c0021212005126080d000c0041c40c1c04a540ca482c41a51b5886203900508400075001440010b8042c0c0524001c0c140c801000c1011000300c04c10740505100c01103420351541c5042190000c41e20204909580c9030814000400ba4000c1020641c0001c520045081051400010f41b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 62806037 1250 62804787 62804801
    0x7030b0f01050c190c1a18040903090302060d0501081009031e021203040804060e0405091504170406091e0b0f070c0f09140f1e0c192c060405090604 65
    0x41443c0c45003000c5003003210b8142544240d9070a22a0200b0180707406d40b901c00a4040d0036007014407008080401d03980c906140d440014060f000703241480007140c1d0b0b9000b05005078090110f0400c0d00d51151b00612034598100409112010ba43c04100005042618000d11003621011088580f400d40000d0b07600580c070810114a000c0e119165150392402e00b4500703060f4660040c07143c180840c104a0500703140303251501c20140310720302d0386018184c01d0f03005102d00303180c49100038421544880b00c810740903281c401e808060405070019846440c0310300c0c242a040c0034510004482c404040c00502000d02c1118860070507282c00e50b10311200d09440302202e01c1c05100740b002c0d64006044400c002da100066521540d00094441d40810710400c1f1540c80300c1a20405100c42104c20780c44681c2a1a45011010088140c85030321031000c006a03410640c2004088031040126645040003840101d0f42e18000d094440785056078100070a4280101d15010000c00ca49000c0d0b481424820402d2500042c071766119a04012 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 62807287 1250 62806037 62806063
    0x6030d050d2c0718060303080c0702010201060b0a03290d0b0a09020303070605010e07140a0f0c02061b0d02060103050c060708070204050a0f0b04020c0304050904033507030b0f01050c 80
    0x161400454806950f92003215109020440950320b50309907000b0418421102a61380545d14000c20b665000c1003245e142c1e10000e4102d045640e64540090fa03066104090583c40c02030399008111420040c1a11408040440c01100d03a144008800d0003281e5030f12100001c4140d000300c0344196591000c0421004107010a03019405010024038401040242d0b40005e05848070030fa442030040c0c88038101100c9440c806485213614517010082c0000c0316000f2003400f12120b082d031810300581d0440342e02141c4181c11031030606a024512140d5030080c9403040c4040d0b03500014031b10060242d580340d5102c5a5503a007034012182e0150b200012040c0601500408483e881e5070046d2040c0003504041d400c10000380b250042250000345440301c1c0d095103103800c3c000c0344c1e102d18041d40114105420f0400b00108070001800c201d0900a0960032440d80c0b0414258843c0b511115a078094008801102d000b808040020034100030945060004900307640c403070320503182e400400c0c0b80454841501c92030f1103240a007615410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 62808537 1250 62807287 62807351
    0x31c0c0c060c0b0114010e0112021605010902030607050307080a1107121d0a0e06090703150602030403021011152d0103140109080403060b2704060506030d050d 70
    0x100300550002e800320101c910410b4241002da030f0315001c0d8080c100140380d01900082c0510340c110025840f8440c4c00d00b441d1005130f0700502d80b50802d41a071440e14a48501154a0b1351a6101c00d810f5140a0024a0f40413880e82045465490149001000c80350010070300440c0c199612641e0900b054003200b0381b00c80710784c81030080300c28280001e8098060b80c842d984154050592045221003820861038910444000c031051803115115103003000070b80c04005214030304150740d4145540b13011a440d02e10340d0080055801840d035950540c0140318030004000c400205020990405041580001a0085500100e114030340045d4860340009140c11403000700e00d4180e00e03498515031418940c8c012240d0304884c852a02d1941c0342140c15081070903160000e002030100a000d00c01003011410340e42042d200c0400041954401034a002040b24a0700d4004611004100904040004000703c0380324043d00008110300925501c010988001d200d4132900c450340003169103407840c0c010300701c040c14030b160044001c0d40d0071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 62809787 1250 62808537 62808539
    0x204090c0206060f0f01020a0b0603010e0304030b070e0d0f03030c020a0b07030614040507050412050f03120109200a05090f1c03020615060f070201052208010f0209031c0c0c 76
    0x8002c1d5a8801903400511941c081c10b821840e900c0c09100a2a1424040c0c01070000321800f6203558103611802032445d034065480e00d80c0305070301c0001400100041d45c8208603000b170b03904004600034070149102c0c0d40540100c4000c002d1001050307101c0980d001e550340c036150103e503100241c4c60032410401200e400421407400300b0180031051390980c200c2d00940303821030400700a070300b8008200000c1c1c68081e0b61b80f2003c500100418040e2600304010700075418080c10884450128005286185901c07404801c61001c16120040c0144a070500030020003c2100c020918100030f00101d040b4207204160303085091220000e40c180e1039032a080d04005e03003054002c101c2030203840c0040c10701002e0701d440e4004030f005008000000308650745050744944800c1d405800304d410840031001c5489168482d18081e1305110742400301ca2a40500c1e90000b0a42c0c81c08018105002e61510340031a0944410200c114820350040c0724070740702030300c00040004c01c518404000001b194401d5034152160840c100300a05034070b0310050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 62811037 1250 62809787 62809811
    0x81b01021e030a0e01020f0703140c030a0824011d011101060909122c0607080315030d0905030a020607060612030e0315010b070204050c040b0a020a110303040308040e0a020409 77
    0x42c1d07220381c100c50000d0001010640301c4a080744a02c16010040140c14007125003c20b110754046c01d160308080c2c41c3c0741d14101002140328955009074080350300044441e820090125404009001c40002c0300c4180e0b0300f1b9034003a000180100e400b02d0300030000d00117030f4a00c18a05a10a080842494140c3d0f0000c01a981d142c0c2d41e100003800c3e101d1b4003511181c00d030f4017850101910078020780380703511910284015a5020f1200c0c160200c00000c50060348120144030030804030700c0d6240118000e081d491840660306907032009040c18070f070b00c00262509200502c1d40c10810394502113880004180d04640d9140c0d61551403400344003d03c0350780c20000025001c42c6441c4105038002c1a1503080342002c4044402140030f001d003560070305c002402000020602400540011300b842d80010b070b0404d600601440c242620381145d01400d8020803ca040181d00522840d8140074900c0000b60b030020040d000f4500d4141191501c0a01d413045206d040111306060300010b040c1e03102c170381c1980c3c09044005c03000d0090302c050340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 62812287 1250 62811037 62811097
    0x3040b04080120070b18030f0a030e0c010801060905040504140115090e0304030c030803092503031715060a02010609060b0403020909060702190c03140114070903081b0102 75
    0x841c0740c0704401c80e030401403440741124206032140302c5da01901d201c901d41d50303d031600c94140c0f402d07401c0b10a0501c814042582240307405005002c2c5503000307940024a0302c01c21408145010201102e56040c461900018072205520548210940d1402c1d980031507980c40c0ca14124020707105142034820f16501e8800c034803683c1000c02c2903000858001c07034401c0c41614003400d070054903442144001010800d40705d00c2040020107030409507901808290554101c102c051010041102c00f1a0b000700c02d204040340280b0030036403c81021490324089400040c0107107410400c6c1d10a00281c51740c114881d541c08201421358602c01d400c4600a000c0540050203403990398102c7e40c40342c1e00280002c91180060700005050b1002c001100c0703204205c0d60307008210a25030f03031400c002e90a000103001c0d140c55400000200c080b80001c0040221116448000201241c8121565142600140181e41003000c14981000800e04c03040640f0500d0b4105004400406003e0404070b0091190244480c1c040c44c29038100c550f03881e010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 62813537 1250 62812287 62812301
    0x1503050106090f0b12150d030801051503060904081e0c010c1101020c0a030e04021b060906090a050309010f1b0f05060a060b0301090c020f0a05010c020106060819050903040b040801 79
    0x16201e0a40b0b80e41c842c1a0862801920b014840c9040f44c01d214208800c0481ca107003941003410b0301c0c1c04802d00480ca80100e03503000300448003034011a044c0320040010b810046c420b5082d110703a04e0362050650504e0030009903522000b5001424003a004640c07010910f0140c800c820500300410600c0382d403030301940074150103000c05c5559100802e41c1c2480d02c840002042c001c80350049030f41e40140c12039903801c0d0343c159a95190180c0041c0c00c954244154040640b010300c0d0200e62117140c0c8001c2a0b1460b00c0c1c2541c600d020401060103546402c1f003041500000d1000081da0410744003424042500302902c03200302c403400d440718404084003284190ba107081c0010b883c0300c01c00f4140a9020b6901a039540714507070302600c865200d0b25241030700400040200c4101c0e507102011900003441511110000c950034140b41402422094900d0303550740c0f00c0700c0d5060b902403003100010001c1d810030003540d182110f80041084c48104103003043c952a2000508500418001c80b0b02802c8210340c2c80f611a03858001030340c024030603 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 62814787 1250 62813537 62813549
    0x30c03030f03020301080309010810150201061a04080607030f0f0c0e030f07080a02041a04110409060f03020607030305071403090708060903030105030a12020c041a0306070c03081f15030501 83
    0x5520300607110b4801d00807030341611726510081d4505011500111682c00b002844007144c1c038442d120100345408031a0200c41d01c1c6015500200d0300c9414140c0c8164002c2d1460207068482204000c100305108001c50001d6000c11039080000d03403d2030303981e0201c0150400860004038146061404104075400040001d0480c0c01030b021a14140c016845541e03450805010b42d40715030344912801d00052820380c0080b208604110940b1034610344c002d000c41c0990f0808135103000318100105040c0030728140d510440008000706400d0055141c6140c003ca200f80c07041d0800034080684510000c1c4845028211a80300c491110000d1940da162610f041e80d100d4030316008500301c3c0c1c011400410b804450000690b416604000d000d450900703655903551200302503511403030003503005426581c40030744c1d030720310074030f40b0416520328050310230302402d0101418030b074004200c00144100d811295000c01c2d0300159103984103003504414140502686a00800c045280c0d201100e81010031510131940741e8546c204504841d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 62816037 1250 62814787 62814797
    0xb0d0603030e010e03280b0703050714070b04080c010b03100b03010605010305090709090507081009020109060c030e060f0906030405030d23070f0504050301020a0908060a090f120216030c0303 84
    0x302d860011035600e4199128598940e010b520100c582c803081403078070020075000e090441401c80d2503942e03d0f00e01110842d401e0700840e66401c01c01070100d03040740c0300c43d100c105090b210502c2d00031580ea8001c030112010700f010700012404030b06904408000d43c000038a00c87c00500301c0d4464200da41d140000340c80e801482602030b500b003450018055000340a8180140201c83c0503024990814504400405580310117460a1083d10800203010100b4400e42d420240707104404141c00050b400050489a01580200100800b004800000c6a48966481691034003250107950b01c4c03100b032207580d0540c0110711410354812000000d000810400000403c02a04040018804034400d4406210031450307030000c500560f490540000c400903c035034a0600714035640c0c1402e46c1020f0300ca501090032604400944004100300010520000ea000c0000c982d100401c031100707104d2800350340c1c2d5924030382d0322585004004039101884500c0107802132144c000d940d000b03c0024280d00d03a42c0d003090707500020708d0311069010074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 62817287 1250 62816037 62816057
    0x109020a080a0206070f02060909160306060e011b060b0402040b031b0903030d05040c0e1303081501021b041d030a03050a02120609040302070b0309070602060606040f0b130b0d060303 80
    0x31408268041c019400901380d030305214403078031003150903100b540080b6030003a03040000c2a00355685034082c9026142d41c0b8100c003440c1a6144000c5d040b26610713040601840b60b4041c000354103030b902c52104252a11420483c0349005014604000640961030701c156200f40080707800b10f1082200c00c051340c0314046202030055514500a0b0700010352280002c99501a082084854500c07400c42d00503d030014400d03511141210354544840c0c651460903240e009482c50220780c02002c0c90350000c200307500503001101c0592489044030010b9030324040c0c07458040070140340492464455545030301824032615084022031003066095101500c80d409402d907080403e181401051903030605100b41c03465468001610300898072008100203048000400840c11440b801c10042001c1d910030b006103028090100092150a0400303401a0800030f000f41ba80740600e000b070004020080e42c0c401d0b40d80c11900c10b200050780d41c480b800c1c6401030b488580d8012030248100090030b00003581c042d40c07009003241d0084d5200103403a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 62818537 1250 62817287 62817299
    0xc0c03090b0309030f0c0a0203120304050f01110307030f06090203070507020a12020105040b090d050114010f060c0b0c090a0b0406210203090a060b0409020301060e09120304080a0810030f050109020a 87
    0x6400190f6101450394828415050aa400354008094088211040755450206640040c0c64480e1a2043e08040c1ca0003000b0710040000803c024000c015075540203004101c0c1d200101d09080c040140828101601c0e102c0242c1020040d6020301c01901904c1e805654074a4094400740203035000b2101240140c902c0346000503041078150703180c41c00c50340c16541d151405190050f541890b800802e24244c0c05000300100c10000744092041c01506810481c2c0200c1a614015490034160b205a01150500040181c0b10002550080809a00030511034099880700030240100380101500d8100c041010800540814100d0b003000f1000642d9100001c0440006041e80e0a01c0c140d0000356400d01c5903a00400720400014010f82000e00c0c4908080c20001e64640c40d5000242560225441079a8008a410078400c00034001d01c04210035038043d00b03500f840c42c1000ea803442003911401812004102c20400032440500031001c110004680009091880e100103081290091060100413840340304c3c805000a14 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 62819787 1250 62818537 62818559
    0x90921030c03010b0a0912030c061508101a060d06090605010e01021e2104050a0501110d08060303040b03010303110606010f0903110612090604050c030106140111100c0c0309 76
    0x20400746a0303503450640e481c16500070701d40e1708450005000d21465040114400f0110002d20041e5401b070340d2000040041030500344202c071060f003221403040740b940c00d0a00042d900010b03240500d100c109030000348100c08454140a01080040c00303988003000103142d071280541504400e00f900d0140e003080ac0b00d1656540152240301801c803109002d03801000c4580b14a00c0e26107149007443c00e544040d20512700c41c41c000e43e1284001c05d0070301d104402001c01e09000034100a129440500710070b080801e0105004d002c000c4e47e1f0f01c8094501820080d41c0c200045040d1130034019a8004d06c0d40c000000d0f00c80d40c4902c0c020302024a600e0211940c1d02c902000190190310642c5402500e00e62525803800707c2e4250b0719241d8070b80300d1390900f950704507070100890345c2e00c0c864801c0014810958003000d8040340c182460500d041c81082910745200741c0c14175005005868496420505481007400d0040b03e500000c03c1050030900140042c03140f1a1404c803140140981003010070a5080c403d5a078504041d48460b04259 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 62821037 1250 62819787 62819791
    0x1412120a05030f130c0b0a0908010e160f050105070f030c06090807050d09050a0b0d020c07060e10091a030711011b0f03020408060c07020d06110a03050a020702010c02010806040b09092103 82
    0x3601585e114204100c0c843e40c80202008505417518511250300c40101c10309544c00c4585c08190350384480248521400800e01440c041c1c400d190089a00c0b03407518000800c00d01401001130003549110041104060082031b54030444ca45c0a5003d01080c1481d0401d612590820801511140a4548007809081c030841042054070070041040699a0900c601089035401c10203160600c940e0030080b2954108007005484020000c980e21410302d4071801c824803031114070106004013488001002848032954040340e0300d07c61018406896240c2e0740303004044407490403041d5031900a52801e500c0381301c10f43c2d00c1030451102400f191500c12030f440c44007000720128400ca1080301855004000841d00f017840d044028003101d80020100a000200e0f074071680d080300c0f100c0c282c0c9181800c0c001401d80f01160076005544e0300c410070000444c1059a9900081c1170100c000c01c00a04001001c0c0029043c0e90b580d60142c2c1682c00d024062407101d2070000c2555a48036035080c070700082000a0910245500c1014044038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 62822287 1250 62821037 62821043
    0x1f050609011d0406170109170703020a06020f12040c031106070201020c1c1a010609050619030b12010c11100b010c08070c030830011412120a05030f13 66
    0x41484200c004001a814103039412040e8060340b20b580c006500844050352950b0310440e103000147d0400c0324544407120a011415440240d10103000314000f003074000c6034144031260049009684c40451009400b07072881075880340030081e0403101c01c1c401440303040d0350b80e1000e80380315070955000c40011804100d0341d030185180084c01030380400d82800d403a0901c0f80b0780f41d420042c800704000b40b1410756030742c2c07000d11402d00c805800400c4803000100302c03555118101400500c01034907018540140c5a82d040800300031850307404241500c0315050b040c0390310b41d1280c01d0301601c02c08000b004548044c21009009984030380549069105800f00700103150744038403400c5070f1490143c480344500720716640e5090352604440026500ea0402c4940000414140310081c1402c41024148151400b4880d203601c008042d0384910141e1141c102c001800740300824840982070410840b01210603003034183c5170500e06a055003a4201030000420083e440a030010041c0d0b0045100c0802048559603803000c0801280e01c1c00009 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 62823537 1250 62822287 62822297
    0x1020a23160c08010c021006050d0b0c1303080a090501082220090a06030212060705180d02040204030b0615071509050c03060c030907081615171f05060901 68
    0x103559801c45840c1c0214240700300c0744820352a40d1020143d08560103412210b0250b0400449645100000e20505020b464100c0344680b82c2203041d11540708011f0000d1a1083c0d0031000100448240300061001c0300171940680059603071004000020442502071054074080360b510720100f90462220381c0308c5441000c141034a41015221a2240600e90200980741000805000f2079100103445041d000c2e481241c200d0404600f45107148180704003400d07000c002c0c20f1142c120409010090741e110085030803032002c540b0000075151016001404031068858000d501910000300041084171a1525034420b5200700d511170680702e400c0101b800d680c8210381000b8107e00344003000c10340700c0400b40e218003485402402211903544504011905d01041590740c50030800d008801c1001c40c0720100a0b078000340c81000050000c00b103944414201c81c011f68080d001c2c1c2d1004200626407800e01c5103400c01c1c45203240e00c422400e507041620300640c61950800e19404807080d034803c082014100b42c01114142c0c0b0b810303074030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 62824787 1250 62823537 62823547
    0x402030c090709030602030406021b0a110108090c130506030d05130302090a060b03150f0102030903070506030903070b010605040303120203360703060209040b0102011103010623030901020a23 84
    0x10420074100003020700301440400f030300100120300e00784003641c07003140318070030040e0366040f60881e80280c00642d40c40c030102a4880d050540020340c0207034000c2c41c1603600f03080a040540354030030451b042c181140b00d1541c2211030300069041c0f14000340c100034060345003a41602d5000b1074440c2c1c116004c0c424020041412410064100300502701440900d900070f840e2100007800ea03886228002d031a90081d9204c2e140000c24540c80c0c0340500e407940ca00c0d0301c24002400110302d4a18001c02103525071600d841054170030b40012002500b000810b104440120b5031202c0380d4907082d81c4400000d80903810500058002418000c0055020551707442200d005e084c040002e07413002016681c084a200141500e405100003010340100400342040101a01a5108010151302c446412041c002202d034071242c02411681001c004020701100c440449066070b51500e03102e444407003a402d11000304071241e466005144000400c00c020400194080c103407181c0641d4654408101d04030791410078140040d845544d50a007081 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 62826037 1250 62824787 62824789
    0xb07090806010e0606130b03060102061f0302040f1d0f0c030102031905040f020307090222030309120c0e10091a010e01050903010e011401050307080d0516020117070201060801060b030402030c 84
    0x42944e0707100c0300007041517107804840c84810042c40010303440349a82e10004014001150303014070441e5032107003a0f46220070090604d070320200050002c07444043d00565607442d170400c041402e034201a030030304544281140802c148600169a81401c01d4881d511406082e400c4152403806008582c0989190181d2411091040151000901010f0b00448181c6101c0a030200161000e2100d00c0090090900050f180c0081c0b50007a01101b605007144039840084000910000c0d4000484005880300d0300704c0c4408950140c64803040108180d0404208900d00d142006040d0352101110400d8a920340b00501c45401041d2100d089003280c005c0d5240401d84800c01040107503c280007070914204020004140040c00f60012403c40302100c0c0d207490f0403008030005020b24101000560010070b20840140811411004014403034082d0100078400d0030300100d28030307095a00c640000505418032401181e100c0c00c1004c00603000300301c9c92144102d15404d0134800641103100f4800d0368800e580140280070174801041c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 62827287 1250 62826037 62826059
    0xe07021b0f0105090a060f0207050a0b1207111b040c02010504170a090b030114041b05030109050a1d011401060f0e12010e0d030b0a0b031e041502070f0b0709080601 72
    0x4845241001014002100c4907176891041d04000d20241e140d010107529180c030000e00303100c1d41e070f00034901917891004200000d038800b00c1142c2072600c81c0d180ca0502d54813040c00440d400d0301141e035000700500c45d100b080c03034410070709403e90400018211030030060001e01c10000c1e0700780c2d201141c024000b44041c042c3c3c5c041000190005140c1c1801c03510300402c10507140d01c0a65002c0d003003a006024541000c401071860b41c241446802040a10080514941d4541080c020120303c414001d007603182d41c440c030100d504100184c0140414260f5100111b039030304c03407240105000b403500c0343c0c240342c1070030741c45000180160080c143c1180c401001c0c0e40794028585200c052202103090098074208070340d138a0205980d00c900c14842002210301540d8042150315031007040007030218058000c3c00d1103a200f04203101e0540030903100f40301182c0e0414003444140da600c0c01c11840c000684100c8400050001552004010b4241203d5089511601050601c0d440e8080e00704c84d5080980a5402250301c24001130061030499 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 62828537 1250 62827287 62827309
    0xa03150914010606020a0507052d01020109060509061b0301140618030613050106060e060304120c060c0309021201020301050907180f030309031406040206090d06090204060f0e07021b 80
    0x103400d440d24012070745840c050869800fa484400142c012100a0381007107014020b04e4001d080884200c0009400380e0b038001040c8011850072014a02c6c5583d42c00b90703070390003174002c03030105d580240c002c01031417070400d40e1a500e0716000c0341c49032801c2c4030403121000c2000c02102564103a661003d040e101d6040a18188a065440102005941c4507040d058489680e001c0042e144100500c0d0f00c9031103841813030314125003590310b5030700300c81d003804a0300317504249a8a0361001d07645d001d90041443c1c0103141d000311003079490034080c2074080d04090606a01d0407000d0f0300341e0030905007980f0030340d01312200c564264080c0d0300700d020030b000d459440b4030b030800461a81031089402c641410040c0015107405e41c1e86000c44501210580d0084003c50f41c002020414409c042d0b4405d030b11100004003402041c42c2c20382c0044c06500c036001101e4070070031942070400203001d02c40c0d0040340000d41c0504200000c40e11041081d81c40141e038824100506130b9400000e030224400300b46001821381d9803152000d162141d20030440c581d015 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 62829787 1250 62828537 62828543
    0x9100302090303070524010503150403050d1109010908070f090209150d0b1c0b040303020c0c090901060e1b0301183e07020a03060c03020c0703080a020c0a031509 71
    0x3400301c40520356090000b40b41c818070404c000c02c059203040c9200703411284d0114142078901c011100411076501c000ca190904480b41c2a40c4030460740d00c0c5d03d0300f40e4003801040c2000d066946094003200081001c2030007441e15220980300c100085540d40d581d41e50350304850054811148544900b004048025006032401c0480101500c00b00a142c09880702c880d0080441c0902c07040d00c0e0000040181040f00d04081c8020355249044105461034445108119000d03000904150b4006001c800d2400d05008580d6046802031110001e4240744035118081c0c0018000c11403000c03000000b090078910b003025002a0104942e20040c2136a2070094075018121030408006100c07a20744480c0d10500c0964640040004100a551108680c0000c004800071010000c504031041d410031140700980d560940c801e04070b81d03102d040840c0b614003a00d401c40c0a801540d030800360314030a01d2008810450110701808525255908503103e00014104110540c03016200c0940024a01203441042c2201074004c8000680 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 62831037 1250 62829787 62829791
    0x20309120a0b04081206040e1e01060f1205121303030c0201021002030c0706050907080a080c0f07180e0c0a0e040201141306080109090302030405100c0b0403081911091003 75
    0x14a40b20081d0341e000890302202e88000001c0c0301c40c40200d12006a0b5041030054404005159400c49400d0741c4041c0080300382507000015000c100076220075001a005801c03041100301c821136a40500d100004000c5000b03c64030f02846c0000da46e45200c1c141031301e2500b80550500c15440d4510345098525078014041030f41140607903008507121401d24002140030b0030812a42c3c5648540500348403040381c1e40903010301c7d065044090108140e8800280030252260171941d0580d4031030b00d0341131892030011034a8003030407d4012018005100c14039050312500401000400384101c444040d9440d807600010303a0081da002e6130161048c014083c01c080300540c002d1040c14814408981d81c0002a202c0c2c00041031a81c020700c3c800310602065612041103801800007450030300c400705050764040c3d1030780110b003d202e0040704445091150240f1480e00301c40c945402c041414007901301428000c049100403100e2420b0500c07100c0e03001c104c0e05540c2c403c07181e0440c2040462030522112404200016030104e00c1801003603 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 62832287 1250 62831037 62831053
    0xf020a082202060a03020c030310050f03010b01080105011101150308120a05010e0a05070e0a030602040911090d080a021c120b240f070203011b031d030a050703050d05070c0209130302030912 83
    0x4c8108011402b4207580c0a885500358980300411845051000f0710900990500e05400b4041c1d0f080703500303c1e041d80c0090908079544410552414010a03a0280380f0785031841400c00002030100c01c5004003180c0d00000d031051090342e13411a854059607800c0c8294299030304100c00084c02d44c4510b48c40250814500c0c64403c0e0074040c0d030000142c080c8280d41095801039400101000812200c2c864402c0f01c03030700325400c01d080c0f0103100300142c00d2000d5110040c044140018034030400d544217000d10380700341c0110105148800303080b11005201542800886005514082181c030703191400c01504010070410300f03005a03c0041e68100c40315030b600015801000a442448a003005960a0080800c0788841001d04100068442401000d0b40d40010462140350382c0109814811100407048540440c03060a141d55114910b03d0200e50602c104d4078904426031404c4140001150b2115480e041c0034002c039079981051305d40c240c0d04400383c0311022004015034400c105440c42e5003070404010a0340040f03001959091 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 62833537 1250 62832287 62832307
    0x2060306010c060911030f0106080304090b060c070902070b010b04030b130318060c0606050d080a0503130602040e04060501081903140706060806090d0c0c090b130f020a082202060a0302 81
    0x1d00e50351314040f44e0703107404891084624102002213043d01c0c1c034841c00038403005c2c0ca06072030681caa10590055445240d1104100c000c1da451701000c4032101d09504084450903a030f03403100c0c2d10081d040b02900b00d50080b000000054900141d40a84045c0c0740c00145112542d12240d0102c410010740c1d2000301c1c148050985501440e040300d100190007031031162140a41e034000d07480c2030000c9a0107500038510810b480040100441e003604240d607607a1002d8203099580b5203403504081c44005c80518020b00d46030001030301088040744082542c2c001c0384120014020351f600c41d0380841c0c4075080b018503c070650b4809450b001c040b034402e41251407414507801444e842e0200390749910742036a0090b0061401ca61040c404e000d444101000000c1c2c0ca1031891922800c00681e5036a40c07000444580308540b2403640342c0104411a603200a078a080c4e240181c40100300c206210032191000e908800c4400b00400c046000084a44600320b284c0d001c82c041004c24044190f070740b68208500768204100c00303030800d9070034015034082d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 62834787 1250 62833537 62833541
    0x6160206031e0603010c0e0114040503120a0f080402011e0e0913030f050405300a0311010f090503070303180602070c030b0c2d0918180d0c02060306010c06 68
    0x40c001c8546159841010303210b00c000700ca00c0544035500a80c903002040e0742c83c1e0b07032010504003000c20901c0d012400b078118003500308007801a500311540c54003c86086c40e0303410100d20f0003060840503585424543ca224200b003942c1c454421240a0701043c0000a00c941e08012180b079801448501d040801c0c60300d0302100890103195041710f0352040c0550000c2441c00340341c0c00003102c0c00140f81502e0000d10f01810103012880e640806441203144111001d1900c0080c02d03291155181c3c1c010b01c0307086030a0042c080c03c001f48647c1c00d441c0c075070005500c1c0c400b0301000c20440740180400e06421000451a21110740d034114002c24036209510411403150310f1441c0003507041d00003010440c1c01920345081041c20750030b00d0080f83c40e000e000c040d9445801c20400461410780d580810a10f070f248040c002c0c04411a21030f83c111842030306400c43c0c0c0f02025030301440c045000b51500e80d000c2c0791b400401c3c081007209082c0c039580e039904c500c40e01c0010699105d0b0b2a801441c05c03100031540140b0614008240b88215a607580c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 62836037 1250 62834787 62834791
    0x6030b01030c030606080706120f110a080117010903091503090b0108030720030c040c0509130501170a02030a0b0613020301060309060c0302250206070507080604150b010504050616020603 82
    0xc40c54a031882c00c00600c03a10340984806401d4000242408a18141000c0c04403900b03041c03000011a1a280b0805198649a0100b000c554614085e242d50300c402000003030852900340502481e0f0b45a00303a1144030550140305105034240c0c10f4a41c224100d0605088104861100e403240042548900d001000134005005440c020b01107040255180c0a06141041d10600001c1104403151980d48010000e83d40c005200b800030075098500043d901c071100760445092080440003a08000403034401c02e1010710585c00903040b50a1840b44403410b01c58405071a4440b41c0740036029501d940000803603008a40d07070560890704142d004000c2181a0103041015007030380c2003648200c0110750380300340000600001e8001c0000fa510185011494800e4040307005940801201800e4206186001400300319100c00007116980c9402c40c00310b4400950b00c1c40410755840d8210b80c03c440820300101c030800e1401041c000c14403852016120a0b0501d0b040405121240d0000d4108ea90031515481c0700002603212000214 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 62837287 1250 62836037 62836043
    0x6050717070f030210090308060f0a090c050406020c030a0f0b1005030a060501051801050a0909020d0b0406050712090305090607020409061b0306050603010e0406020c03040806010b19050c12090406030b0103 90
    0x148040c80d45050290410711028004418036003006d8200740020740c000d02441c2c0c01041100d10b29103a604260125503612107941004149515003a8042200c0b42c01601400403955680d0848004920080626884d407580320001080300075040104400521880388003a4808d050303c0754144202c0c0d41303600081c60b141480c0019140079903202e005000d5403c103400030540011206a00088552500b0f0104a20480350b00c01c8640c0c29548140c40c030215a0b842c200003150710703008000382c0064100f0307007460b10040c10155045004100c0541c205400307a8180c0c081c07940031a8040c2c03989424000c0d540c051050f280d100c51000c0b40c1c4150744001d550005001032203021001e41d00c00311401309504441c0000b40031603200b5000b05200700d20a00040144040c40c20000390302581c011000358480082080072440c40c051a0030010440c00380400124001686030054104108002074888108900d02025a824070644884da18980c000c0c4004550844910b402030003000e85c060b00010b0703495031f29125010b01c10390030b820807 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 62838537 1250 62837287 62837303
    0x1090e0a24060302072117070203090a231206040201200a24020c10090201030603080f120f1e0601052a07060504050306180705041109010f02070b040605071707 70
    0x170740c24000c014812201400001400414145c00518003a24840c48511203510021901e800541c1161086c001d23190615805410070801a454140c0c00c001e42d90041c04c0d10428511082d031700c0c495898400c0113100c600c0c1040c2c0140140d03440d6a001100d42d104034074030b18840c5c01d1003003c1b00745119404021581c001d030700480c80c0c807148420392110a0009811016003140d60b60061295508184010a6507140410342c003100280385034552005a0140c03401b5480a01040703c081200c02910701444000d1107200130090902d006136444141d00d001240081c0d0f241050004400a03403209a040d50040030b8201d00141405800c101c0c01c1e0982541441001a40a440a000e11216001c10340c08120f01000761029003092800d250030000880d1341c1c1e0000500c010344813411400011854042841b03031300082c0202034821300040400c0540380f40150b204618a6000641184c2020b40c11032010030544140ca80100d240b514140c5806e004036040e401a10b825180419103503090001030049078010000c8512400f81 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 62839787 1250 62838537 62838547
    0x130b04060902090f010b0f1e0c16060315030809031518061003050d0f05040f0e04110a0620010b03060103031106010605031b160204141501090e0a24060302 68
    0x1031081100300602443c2c0130722110741c0140901400d480c1070f11000c2c2d070b07a011040d464000d0000c42d90750407540b401c0c1c520b18a80c3e0000d603004580101140050b420187c00e0b20017400a9900d00080f0225140d0b42101c01481c06181000e100041c0000f0040a40d041d0040c21a02030041203009101011004e455907401403c4d5100300f49007940e818007200340d0010045a51680c0b1071301e036440b80c41e11071104603100c400f040040703406001c01900880a8902400003120400b02e420307214410140b0310300e400d8805030382140310a903500040b407901e2040581603940c150742d420030030b9540c1800310828048001081540d55200d50300c26245450030441039000754065650702d460880c840c14101c1c14180b06820080030888200b0402088041844d01036444891121400e40c1d01d10302420078211018400340c2c0294400d0404282201c954607140c1301c28090f0281344811510058980700548040005100702c0d100030b480c1e0800100123041d298002c0c000f185114000031404034080381402065031054100c1c0d008658089a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 62841037 1250 62839787 62839789
    0x4021b03090109080c0a030609081c0b0a090903020d050a14030c04090b0a0f0506030403110d020a03030605100914040207080a020f06060d26092d010305071205130b04060902 76
    0x401100401c1320601130504680400003141d100c080c02c2c000949119124017a95080248010840310810b200344102581681030a0280c1d0150100e00495449a0750f010008665110b1a00c29445000d9260b00184500d4810344000d41c1e075038000222841c140030301503d22401500c0f4000066102d0b5080b9000b07196118204450101150a1842c0072409039062090500c0b60b0410001e200081e640110f81c2e40f9140d42c0d461900702c48044002240aa403401038421340820302da00040c074a98a5482600c0c00d200080c0c80718103001501401010b03500018918800802c440a0464604d480388000500098540140358446000a901c0f0110b03100045e440302103416841401030100d0b980001003201c2405050007142c980b210350445400024003401c100c00c451006a1031882c00300c40d103000010340440c980d0340910101c2c0702e200240d038a000d1256810020601400e40c4280300d418410b0b5006d4813074080d00c01c0181400d00c024400100800180c0c03600728518000315181112180c40390340300b6400032401e80c2c00c81c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 62842287 1250 62841037 62841047
    0x110a0906090b03101404060504020d0f061509020c10090807080703080a050603060403050f0a090f080d0306090621060e070e15182d040308071106040507120204021b030901 75
    0x100c1d4180325107401c071710134243d40c0c0300c002c400d41240d044100441c407078603140005205c103000c00034010708070686d0100d0300c010440140c10804c41c816850140740b842956480700402a4480d00d0342031180b48c1c100f19008030074500154045846240a1400c85060800950b10304030740303a004d0507043c0d0214055100700040e10a46000e1994403007030980141c00b041c145136401030070500441c80c1940d5104c00221302003200078132804900c00209910341c124402c241c4d0b10002152940b064800c900006410306001143d015a103000301b40454103210710011040d2040f1401d1104000c200f40115083d039110300e5280c070350b041c04002c803402070a64241100d801d41800c407841e04d80028200c4d1641d00078414500c0d6401e482e140719409076400701c40380c0070b80d400c40c0d40e200003109002000c1b58103042c8100341c400180002d25030b00900107440380302d0300c7e00d03094510344000340459a200d4040b40c00400aa1100605210782c048668581c01c506202038005400c00c003484c00011909d11030080311044560010400540e59a486 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 62843537 1250 62842287 62842303
    0x30504052124040303021804060f06030c02010b090c07020303040e0702010605010f0201090b0c0d02040b03092401032a0b03180c0a0f0302040b030c0607060608060c0412110a0906090b03 81
    0x221005484034441825071000300b4070020806414140d003c18440d10a440d8803282c41034000c4020010840c65448404940c400035090094a0009281c10000c802c42c0780148100303000d5980050090300681d072a015581080e03030115408a070140418003001902003010050140140381a400100c1c4841c2801c00042c9071b0110002c00108583c1001515000304580300c0c82c09400c6040301c14696956460400b64a0191065600c03603620b00c50000104003003510040350600c0900c0c102003020400307000200840700800800e0001602c0c1001602c0311302c8241036007404103001d00d0034031950111441e9441c0c0b8045800e800488040b0516001170a140341ea000c0244007260000600b2903501e0042c5040c8401e28840380900d0000a000c1c40c0e5401044450b5a001c00c5488050340c0020142d9a940c51186004c0003c3c007a648a00e50491160801050341c0b40e82007001d540540b07400c0ba03400b01f03030840c00d40c5500600b288030504140c0c01860b5420003260030b80c0c0c18051500580601000400d00c0c400700c0702418501000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 62844787 1250 62843537 62843563
    0x90506040c18110909060f0307120b010b0f0d0203071806020d02060c0f070f020f030706110601050306010510030902040e0f010204080606100c03080405160315050a0506100c0305040521 81
    0x14008602c0a88a80c10301500ca601c039050341d009405554a8011400703001f00e0b800082d60512407142c00043c6840343c4016660414403070140c9980320b07603a03030343c0e07020351801030700c000341c4e803900e000d020a2090792030301c0d40a903500c072000b80b0700701c844c040601d410800f860105ea000040140c111544100e5030350780410060f90051007013840d00b490140740c002044a540611000189600c01d402124019592058001e98100ca00201516580390b503410700507040c0080915541342d94041d4400024403882c000c14131a0480e400903040300126040004218018484071070200d070f1060341d4408001c48030004101118021100c2000143c0d40c1e428090b98602e07001005200c98890303e880070801220503481421042c62507454140072000ea1502d182035810039118203407201d190750114a000062040480c0406086036030050100202e4032191804001d40380c0441e80160000e0217030198402d0030b440f6500c071441c4240a4030f00542060348840004881c0c51058564204401e406801d0406980061010308003d1030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 62846037 1250 62844787 62844791
    0x301051008011413060b0c0606010f09050105030606071b0305062403070603150801050412030e01020306090c0a090306020d0204030309050a180c0e031c0e0607020a03060b0103090506040c18 83
    0x21401981c00a03140440840e42c0c002c448020703104013108200c3d000311003c2c0820240350313501d90380c4c0b0300382560380e4540403655140024003604010811a001d000c443c000c0d0740040e5a00d03841d656818051040940c0040b20481e040164031100800c04440ea003640b00145101e9005004c10b41031608403ca081d800000c503030350611801601c00009903800090b20700840c0d0b401d083c0440c0a0b1204800c0301a03098035540101140d50902c0208410812241030f04600c07420b083e102044401d6200038814201e010866619412a003e4004116610543c0d0301411581e41d051a00f229401e84039903036101641c00c001030320f601140d0003003014420103410001f20000b40c54162100b02d0001c2ca80150354036041c070f032403e5403040140d0360f00c8480907644c030421015411440117011544200b584084504942a0b601c030020009102d1803001c82d86850000c00312011260000c051040b030604684072640203020390320905050582c2d400d2010000707241800214070480c003403440d5043ca2440c0c18002410b42d104c00360208032081c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 62847287 1250 62846037 62846039
    0x305041b050906040c020102070c06080f0a05090c15160c0302090c031303081b030f090606060415030e150907030c060c03050403030315050307080c0a090e030f180603040602030105100801 82
    0x2c0c44140900d640000204c1d40070400381c03103031242a80284500380001d00085481400802e40301e8100e495540186981ca030410b2590340e60324080343c1150700a0b12901c200d900100300c4030500e868107c2003011040001c401031844c10012400c1c4522101015904442d0031108070070030019403510b801000d612640d9102120319501e481b500c2074242a08005c00141446010004103490803a0354212401601003021b51550b84d04000c104242d0240c0121802c808a10801d800110316041034001c0d201261004d080200381c0040b6568240c020705408a40c200f11403054849107a10100501481406103842c000038190380c50840c189050305c0180e6811200c14020203c0e021000658060f0458040b01e40514000030580c001d145207022001c0c039940070035414803d061011038001ca020501008200003100c00d05a8250348211410030385040f8425028290001e000c0c035074024610728000d158003002554208085107888000401507001604e0550300680e000c001071009040002c1900d02d800301d6400c0c201625 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 62848537 1250 62847287 62847289
    0xf060b07050c010c0804030b0a0207060b0d110d050f1b0a0b120a1d0a050c040c1103120603030c010c05030610030912050a1419090512060a02070809030303070305041b05 74
    0x5182c0501c1483c10081512422024400c01d541607402444e44404003070003c3c00d150390341402a40000e5030075581d00e45448000d030700c2450101c800c2c2c80f2640c1c0c0140c41400d01105c410400040c8071810409817400c0c040d1041143c9040418400713200d01c01b4021200700306d0707060b0103000e0121030600c9030444501072004000c0a410801101121540403174940000710b40d4443d21842c1e804003283d8036075a15807510444c07004100308038010071149413030740c0f00351010056282132003001c451a90781c013500b00180f030708104400540040e41a00203075009402600b2207141802c040000c40c04c548010500000044020040c0803652070202409030034061289010710100e00c1548804000e80780100d81c910500c0000036a03961414060000b070382c1ea072418a11296210208074600c41d00030b000016644000415440d00802c45180500c20b100d440300104000f0a0a43e8440c0b5010f0001c1d840180103649224060082404559007080110302c101c11075980402d00d4203081ca41340907000d12007081d2600400c00500140702c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 62849787 1250 62848537 62848543
    0x16080705090f0109050402070308180109021e011b0f03020c040203041e020a05150c010e1204061d06030412030e0c060702040902040603020619080709031722090f060b0705 75
    0x71200116000840080c60350010703103d03800d960303204907001030020800c4428150020411803013240c480607560000c02c42481c1c4642203c42c1c40c4402944046a0b440807615071401c100c01031490300d410f0400a02c04c810f503542c1c81503001d030a81422204040c89840180c1015414004010303561400d84055045080540c1e5882580001010200a40300094040e400355a10603000d0801407a0150609402040d541001c608542c0504106007056081108801a800000a900010001c1c41c010309007044c0c10050704440c00c40c4594072483d40b0fa00344d2103290990340d903040004d5004500c136094110484011090240c10b9404800d440d0402e0b4002403400e07412070300c4000813211050741c12900002e9221481c070000d030041c00ca64001a40080002c06e1070402201e581180c500c0005107034960042c42e98890404482c400640d010040442240a52203208503c1d10780140030710b81c513040004682060702e0180301c2c69001107548200a00398484000f03005114041c41404081e180c44240145072080319140e45903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 62851037 1250 62849787 62849797
    0x130501020615010804060f020a02030c010b06070c170a0213050105180705041401110a0501060305060f01080a140102090d03210e0309060306010c120e0108010e04020a03110111010501030b16080705 86
    0x414441044001810421b5030360140300c00e00040f000854071050107020003980d94100817800e903520b600c0c04903c00310030b241140945685550041107108094103020034100072040b0170301104480c2c0700e51401c1c0d2005039686940c0444c0b903a03050b90002040c3d0315240402410607010421042c0981141c00ac2c00806d80e0700c10102d0f000c3d140c03901e11007114401d4000040303078000301c05204140e040c003400344628200403040d001203040307a0045c402c131400e644075903030820602442071081020a40c092003080e00081c00b1001c1c001d4402c4240000103050842e4000403c480b6641c61000720001801d2032602500b03080c904040380400c800702c01c000c12a1034030700d0301d08035600c2c81000c1c00507205800210014160341c0c03003801c0e5040280d0707201043d022940c440d000b01074241c9007001d2a1070b002c104010004100d0700661101c003072069400400c00c1440d2891510340040781f1044c0d008043c1001403e9100c0b802c0810309000300e40c000c0d40300d000340c107001d07150142c14407040e19508801c0c202004004c80600600e00c0d8040305540c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 62852287 1250 62851037 62851039
    0xc0c1e0b0705190e030a021801030b0601140a0309020a051201140109090b0604050c0705030705011e0b0d0b070e030304180b0609100e0a0f0608150f011b021311130501020615 76
    0x480200c0c44c1c0002850000f01078002540007280c84100260300004030507450489200345407940700c503200c000040d20a444540da541c11942018800020528072a82003008a6400540b44040040d1a4004241011083c40d00ca000d00e07074603002480c0300d01060b003903600d00401c00024100018192556203152182002e091940300d1034881004c10034050f580b1084481c2340703900070112660f50030a0b03d821406001019807a00440c01170102101c0d26203490302030083e031160000c0c2242c4101da4190703242c4584900291250040010780e640c500746546040000744080c0901700c520b00507501070054400159880002210301407041846034030303283c6d180c50411003003954050816103440c084040c00b00f40f15a82c25407102d010120b8410b8006802c5030050b0440c2c0c0100c007080010001e00119006118080814030b054900190a4845460180e45110503072424030f8402440707400c20703452003185001036404105104109040014104001d14070610100000742000e002070211450300181c18502500c0900040f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 62853537 1250 62852287 62852297
    0x9091515090f19090b060304030504060819020a02100518030a0f03140114010809150a0c090503010203010329060906040509101119020c060d0c0c1e0b070519 69
    0x1107940e80c0c811580c2106a0b901806074030b5107010f449560780701103000e4420194401d00d40540445981401c1c42207074171480e0903486203860240b50290840f0b08050040c040703111201141c2d440034070f401050004000d14a41c507401400103412030364504040315406803c006003c1201901c1d0780d03100c440402074440803e400d061001110300b960406801130094503005e06a4421840c001045840c1c00c51801c090304582039950b01c3e0583d4850001030342e0b81c10700c5010300d080e103441d020002e0324607140c50f040203020759260b00e0626409a511070109003a41c10a801c21034086102411b4420391400d05600c5003085107110010a0701030801101003081820040c0450b4003903525030000481680d41006000d880c9014080c040054180c2c082d81800c0c2c58105d5185650f021b04400310304509140b000803810b10401008040514144d001100354006080c060308034420b008034051200045482c40000e4001c802c00030310868000981481c01155a10005000750b0501000384010212085868030300302c0e00420500345 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 62854787 1250 62853537 62853547
    0xe070e070207090905010c0e060a080103140a05060a020c160605070f14030c07030201020c01111506030a12030902031207030e0103090c09020a0c12020d1202030705130303030209091515 81
    0x4120b0504945030010030401c1e00f0048a03004000701540118a071781402d07651106803100f080200000c2c0c1c407401c50007400141c20b4000600c0845e0031070005020000c1d1201c00c451520b40c0300e55400e07080903021207142e088113a0200310032018030014801383c44a004800b0410b0b403050b09001002e40603004a82c0050000895075541c0b004018016520511050400007203d446401854009aa072105070204900500943d1011101540211400150000c506010b4120144500b05800324250300625a540c1449a824030380302207100802840000c0380c0e1a41c01040301c4045006062038104c04c0705001800c0d1008009080210758030503c0030016080034600403440d1203060411022031100e035001415040d20004000c01c4468000c410b20610b14494800c9040500280e0805d036140e402c9084d141c1c003c40c900c0711400400c1440c560096501030441e0810343d00b4062100a07440320300101d81c2044000c29400034041c071051902150702030384151040c8140c01d9112812000c110791022590305440300744000300e4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 62856037 1250 62854787 62854801
    0x5030d030e0a21030b0a080d0c0f060c020615010f050406110c03030a030605040515210304030b0106091805281103070917010c05030412020109050a0b16030e070e 71
    0x144048041c0c01c084034501801602c04807810201c191085000460314240007401c0a081000190341140c01f494068440c40d84000c0065504000131101103807001038940080001400910500c070b428503042c0d008080f5464080106005205140010f038140400b003050300641e542e010040700c040d00c9440c0390031000c404c00344500502d410650710442c0e5150002046256025515038801021160129070512154980507110040e0360804028180c0280081c1101d4170754001c407004040b000e00d40c01d0222480e103950b03034171013090380740c0c003a080103000a801910410020800351210000810342c4030080200d41000340300c0810400d140f944090048a2502c0d40e20600445e42d070065402a41120313240d0fa592030300c503100504070340071405807038884154030070405143d400500c200400400a80c03606440c50301d60ba191070354920340f490036800840d07403500f44650010382c2c00e00c0141c810350310503009840d040c20500c0440b61044802060b0f0300c00c2600c0c021080c0521100000d2400885080000410060301d0f085 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 62857287 1250 62856037 62856043
    0x90b120706050a02160302030a060c09080706030605130c09030312090501110d14010305030304020904170d14070e0a0b0a03060509010b0903070e0f16051603020f060f0105030d030e 79
    0x1a001100380038000c0001492600007008000d800b03915070079075001d4400e101c0c865502c040b4a010181d056400780d050302001a00319408941d50b4046814418449642e60014038a002000e410480000e034854034108040c0c10282c03111000303c8400601403264103c0e00f41c0040c90080c0602c00502000101455000c85006d5a4000d0042036001002408024100481800d1075849442950b0605203086a958030f42000d030300c00c0505980d03100024500c1d6448036000c000c00340c0c0b409082a00d034800301324000d06014002000620034411050408a1000c401703c00b01070041c000140b070b060070722070180e2100d07070140d60b8402e0b054140d5001010450b2100824003007203000700801c2c0c10458000401c0800800d000c4104005480b8030282103049500054030303111900c11420065604085952058001c100d0700d2a140d2501400c00c806880c080d41422590301e405003420341c0d640c10550150304a0b820b040d200020902c171043d40580c5010940c9069403400006c03e9032802e07040d90500406940f50620400c0c3d01c018 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 62858537 1250 62857287 62857309
    0x90a0b011404030c0f08030a02100f020d0e06041109100e091c0503040c090216081e180a0f0b091e100302120901060503070b180414010609090902030601090b 69
    0x52000d07880b141c80c0d162a8072154201d01a0500800c0c90100c00941810000b003120324840103036019041e101c80040c260000b90031404080d4501075000c0c4032070541840030b031150086040303a01000b0940780c00c040c10700c4e5030f0001c50000c480340642004800c014450034151962812a501c200300381c2203a0340c1e42241e4030300300080784112883c0405a20b10030b041c11980a0042c2d0b0207280246400303030a25985903a048203d1190f15802001c04c192852144003051020b000360000140c04c1c1e18402045407400443d900580c4010486801d06a421281524604110411001400081981681244c00c01c3c2200c0301c0d43c000c410b101c0b441190040c2d40c2c0001c0d20009500300302c503980c001c0c040801480ca0303008042c01940000c1082c0006036101000601c00d0b0505020382421030b200507000d031503042e04010b20301c00f882e80105e1001b00ca614500d110082d268442c2d00c02d100208410041104955040800061107000142c2c06086103909150081c8056a400b15610341102c040b108005521400000070070360190700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 62859787 1250 62858537 62858567
    0x30f0303060d031b05030318031914120f190203010308041707030c1203030e0114041407050d0507060809061e06040b030604050a06060510051210080a0302011b0e090a0b01 75
    0x1302d83d60400308840000598000c110b00c0a450107018011410b1a0340c03030003120750700e0345005c031003404803c01240114904042002a605d00307602c1c01f1042040480080300036141506102d9403c02005141914000311b0045044000c3d819880c652464039007071594001d9008e140c240812541c41d018152070100071032001154002000c041060782c442082d01091f07400c00c419404a414014040c020704c03010b02c16029a084461070400203501c2ea52960100c1c030890b1041c0c90514401c040010035103075218414503d050780304100030040c40c1d041c100300801d103000140c03405030681e000f54103119540d4581c1400c03240e4105020410300865441c40d0005001c3e080c6403a5040d014000c00b000c2c4800d04c503000c9501c2c030109000320340a01c1051b90740d50511561401c070b0403030000050014400c1c801840b10008505401400d00840b1a21041e191210381b41460703a1002c085000d80c0d0b5070b00d100d0007416200c0d9141e0382e03060503606100e07164150308004030b818800020280b0340816034a500100d11a802080ca950100700 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 62861037 1250 62859787 62859827
    0x106050d030203090916020d0e010504080106030f150501080706052b1a1014030402180f0a0501060203030705040308030601030609020408010905060c0a1b08040902030411010e030f0303060d03 84
    0x345906000c0e4407944a6141d41e40034000800029035401980c103a04418110994020b186103aa42c000441e0f01c001800e40d400d0400104110018811409004503806107014030b91021004050340b0f05407a10108c19405030141c5414403004019003040410b0180031904030f030a0246e91103070207482511460000c8505503e00c0b01040f480c92442c644554070080c440b40840c81d00d501540440c4040041114095400500050046d4280b0603c11201409107400ca0300c094010613400300c0c11180d40360204170031900c2c0204400003030100001c8108034040c050060030a0b002441c5141001003005105224500025000080c0000840c0303880e40319500550041c203401800719216511803c0850183c9200c500560b03140c801c00012420241c154811241d1400c2c2c00c0d121400c1b40c291400a907880c3c00c0c615030b400e030360040341444002040000c4d400154801c0b8070a01214003600d070b091001614500c005041039000740d200040d5010f0088000084940040d000c865103003800303002d442c0c112590480140380c010100c17 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 62862287 1250 62861037 62861059
    0xc030503040305250501140f0703020d18060b01020601140109060309051005090c0a050604180b030f010218120303070c1b0b0d090b180a170903060720030703080a0b03010605 76
    0x20402d4052413600b40301c3d800902503025500d00418003035109035058041101200f01080956009034010b2481035100a004522109503a03042d0401103840041501c91644a415084403503034103102e00350140c5075610948150013200400200418407901401040c180c0d1205407030140501040011001e0f41d103000d05224900d04041c0250b20303a07091041c500c1c0601c0003580040b4062409109540c15500c86000b0941e00c0021503040c0006032200550681c1c01d030140340c000000651080c0010071500001051105034121140c050040b0450601c550901642049c0140314403154400d5110189a801003211030401184004105030480658018020312000180340c031000342107500462a400d004040d60480713940c4201102240e21440d1600c080c151304210841000a003d450340410b00a81440c40e82c0e0030300303607020042450720105603112008581540643c1c1c02401c2e280301426820030114018500388016550b000d4880314019122109280d110040c820789a2003d41c004001002c00500343e040035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 62863537 1250 62862287 62862337
    0x3020d050a020102210913200304050706140a0c0c0519090609051303050a0207030602030906040b01080d0c0b180102031608060109180b0a05040516031b0c030503040305 74
    0x805800600700c1c0580103903624174030580b500103e00e0b240203404811483c5450401c0c0100f041980c7c2c1e200040b6801c1c1e079604044000e6403400303058103014030f00320017240d5601d0a080c24528038081003944508200308452080309030003034005050b10348010381350030301c0c070b10b07881e42858254994071058100c7c5030000880d01ba80b0300d561068400540485000303c030204201515000b5a109444084440501e0b508422403c440000d01c51401010300070490720544441580320394400c0300340c0e401510f400050384d001c001031009000a01c0b896500400042000b442d80005194000e040380980c0f080261406c0e11800c001030540c2d4182d102480000b11306402156240303000f4008100603000c0e000321a000440d00400900194020300c1c4845c1510421640e00799800520b452200c040c0c51036000c0030350040030f00350001807580c0300c0340a213030701403e0640c5803032820841c032038001011101d6a020040102c40e10100c680c2c035a54002e00b01c01802501494001c0d6240d5030f50800f948c26106420242040c00f2040f001c038900 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 62864787 1250 62863537 62863543
    0xc0e18060c07030809070501020d1101020405091302100e0906060a09030b0f040506010f0303080a050c09100206011406090901060c1a04050d08010602150f060102010b04050a02120606070308010b0a03020403020d05 93
    0xb10610030780711942c0c5070325040140e559500c1c150003454056407100c02c8c00c03026036001c0d400e024402a000000549425201c0011420050042d44d40a00301074100d0110011803601c0e1740e41d68503610179441c22003070b00d20307281002031851030b40540203a01a50703001400340016489407000c00d01468100040841c10b0520204028029004590540d0070713000340d10001c01c0d00c480b01040305003101e8056507203291700c1d29070f440d0640040c28041c102a040c200b04001050203501c98240d5080310880b0b64014281c04d616090580d0740c0704c0c0031282400d200e10703402c110102156070f5180d136207810347e1140c1c035060200384164a841c0c940041244010781151110030104410407038001600b82400480e42d503080d440340d90310801640e5480400f0805e004140110001900380d1030b168120581c804014400800c1c001803070004541101c1003a10f100c1100364000841d1002c00d40c00c07000d0346801100541300c4074505401610018002d00c01801414806000000c03a0300255100f03405440180d40c0040c54004003410603d051a070b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 62866037 1250 62864787 62864797
    0x60708090f01090605030406020904090f0c0603200d090c03080414010905040b0f0906060f1201260a080702010c060c02030c060901020306011d030102040801060605041409040c0e18060c 81
    0x4800c0680e03101d4615294071400d8540d00301d40301c1e80ca6050468560b035a92801941110786544d4103c1d07640c03961480402c002c9100c03488041d016284043c4510b04000b002425030303942c18103c0310382c0d180d20104110302d4081d400032580c00c0803010000061313a02103440d110011581640c4050301a40001c14042148540111010560082620350300c1840f5603550521007680d4501088076403010421441d9201c508111382c0042e40001d0080a03240b91104e500c540c0003c2d0b40001e41140c08450b240c00042c00f00113940d41c0014501c90981d04800c1000c5942d0103a155203002c000030003410b2a60200d000c07000c690140680000c900d0780b0400c14400040f00344070080d030780d0701300390020091442810007181c0c01c484180700b00c034000c07007040e51441064070403204444020070390518041d41541d420807000810600a1041c80042e00c000d0f81c2d02c0d41e442c0d01e044003008000c2c00407104288580d1520050000154208040208840c211101d040465694260f113441038051114901082d0040c001000b0b90b840300c400041c6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 62867287 1250 62866037 62866039
    0xa080d030516080604050703110a0c0311030f0406050a1101020a11060f0402030309010f110601090516020303010b1603120c02030307031d150c04150203030402010f05090f01050d0b06070809 83
    0x1c0746540c1c40720b0040302440503150800c0031803448008a036103410b140d0015030307105d140c40c140071032000e0415459600075408017044400003034040110008056008a81c3e2000740400740c01541005054030003c8894841e41c4945001e10400080d100ca01600442280103201d000200854947c102948082c14070702c1000a440310070b00403040090f000f164074002250180b6005401581840458801034400c000e800101d0424060065400c40030314038200903844c040d1120700d10102c1c441c10540e00140f09002110841070543d0014001070207108848410b03111004d610003211000e40c80b0f98103007982d0780d244010500e01901d082105410703000d500000154090ba1056600300183c00318800a04013802c010304a50001d070700309205110410060030714a940218000c00c4252505944003c070043c06504a1703076510258101008200656800c0f05030718101a00c9410039030303e0078200f000020820b08400400e40d060100100e00c0b03900c801480e5010f001e4940c0c01400899071013100d410301c5105038120310912 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 62868537 1250 62867287 62867291
    0x20712060f050c0a09061d0a0b070311030f071b0e09060601020f0d02060103260d060303020d03060501201c0c1b0602070b0f07020a0923060307060513050a080d03 71
    0x704009016030800c03a8480c0e601540e0b40ea54031806e000c411242204042e840311000c296001d92050325680302c0106000070003040740a10b5031007000b0b207400b404c4403440c044c20380030302e8000b4000303a0b080c500e008046400a0ba400100106400005442e0b0710800c0b0064000b1441c86c2103500030071001600001e5000e0240b00c098080710851114460502c4c1e54040394410100141c0024004000156007082c00000034018940740081907032400418030b049810900084000f5030300c81c4410070500d0380610512810402610b424440c040c100000a448901c44440764406000e1080002c41c130810300303110f501c54012218600d034800c1c20100000400703040300c03200260703910000700244980a02017003004004031245900900310301403901540c20803030341050500303c242da1030030460305005958900c084d1014010541c0c0002c0d2070005100070111140c00d10843d10303c0c0d83d8a94050182e83c0d1b4002034850300710344051801c1c07130b030710024284c9141320240640d10554020100340008034100c1000316602d0382d07894036030b681 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 62869787 1250 62868537 62868541
    0xd060506090d1b0816090b0613140d02030304090902030f03130e2e14030609070b0c010209150301170c15090d20040609110306040c020712060f05 64
    0xc0002030701ca81001075610040240c080b1000600d6904a4560307155002508005695075840050801408510505003c0301d50b41040c015210540714144d40d501050750302c1400c0504030b20485d4582e0b05035001e20362414000c0d03944400d0598076100e0f503804003680070381503d46440ea94840480a4481241c04920901418903040e8a000001041c1d4102e0205502e0706052030f4600822031170022005044864a8580c119109100782600e0ba815032410944aa401000c00d10700b04013018800300c1c1301c130218400e40251041c80990070002034540103a410540c48140d80b4001c80d0481e60080c8100180d02e9003012803803032709130f440c044560007650403614030a9a41c01c1498108505a407a2001101003a0348005542c071101212510000a001c96603805070001c032640b031450b00c41004040d030703079846407800e1000d02c0c03021911424075025001c01890100014081d14071303a0440c0d0034090000070003890190340e8450603080894403c01c41100202035084400c2c6804500381440b07000340440c603505406403818040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 62871037 1250 62869787 62869789
    0xa02073c05060f070c0605010308180415050f01090e040c031b061403040807052a0609091f03020a0e07170121050c03010f0e0105150603150319080d0605 67
    0x40c01211141d03100001d0b02696a40f581000ca6885020744000c0421040001c64000145c40d031003218046e42c007030308200d40c448400030404e195224000c00081d01850a1000d484000d603c04040107040d01d1b8104c488000a980314001203404c0c40b0390760303c01c40340032040c40144003d100001c4100c106907402a01102d6000344401c840341c040b24907503c182c03400240d500e42000c02c20840c103800740da00544540c007021715000b07035506c46610b0006a680d0040650b9100c09540848a14808088142c40c100b41d031050b0400b4204070018158141c01401c0c1882801814540c540204000450002441d4028910303d1456204d40b500104480c049800e40302107005040301862241c5400d0003103048903410908020305240310510003081c2e001038041101c0d0f5114512003d00c0d280da00b800307110f42c400c0c19090006102c90200c803140d07094502c003070001406d20828454800d00c0743c562008985e17118460030050f405420940300482c2c942002e4842c00d07082000350a0150041080600003810f602c0004038040c001c094641d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 62872287 1250 62871037 62871143
    0x2150301050d06051f0e10060801060905040221131704030b07121d10050c090303030c0c03040807030b0f1b0a030c020a0503030c040305060106080712050a0207 70
    0x30040603446149400d10b0030018030383c4e400c0703d80d201c011403a400b060a003080c1a28200840c0e190401c6c80000004020840700d8041030800200900003460580f209514204014091018078009d541c000c41c1c00007260014054a030426441e00001d860f0003582c0c0b4507150322a481903210758001181c0314800034521002c0047c60300251000e40b900568110f42c151503030305099410402d0320242c001696201d01c00c1b00f02c0320107181c48414000340c3d41e40103040f6a1451030201c80884600030042100314109100d0b1503650f0710004140c07a442810003d0a0340e9903246071840c1451402140d1015115204a0f0000310400401483c128064010801e0051142d00c4030707104000440c003408000840940c0c2404903012081c071980221110961301e00503620152aa522440d04581c41141c103080f0001d0002820010440e080290350b004003498503186005080c0030400800f885500100f4141b8191954003051814800350b04079014907500000003076104104e4014081e040d4070b607108003100076185080d1a1200300170303a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 62873537 1250 62872287 62872289
    0xa0306080d1e0c11031b0102100203040b04031b0501020c03130503030a140d0204050904050a05070806040c06210515030f0d0c0b0a020c1207020406050a081506040f0908030402150301 80
    0x5864240a12030345804841c00090003d084d24003c84241c560000342e2024880c1300303040301084880c1c3c2c542005810000e07142c12070307070000401418410800c02010503203020545402c01d0749868030340d5031140c03509410810600101d10141c40d83d480000c121004ac100040105140100c1100c04141240da03802019101d00a86444001042080320480501100030004010464000b0801420142c0700d0b0b000c031b180680221403c640c46c2d80304200607000c1c0241080303a42e00802450004060303c0c94980e90f180c0c10a550b40c4901c1081c030406000383e40300f4050251078900c40350000001003010b0f1034081c5140c088510103400030740c00b074010204414041000400d0300c0d081c0d11003944583c1b0ac042c83c16610060f000d0402019008419400e20400010002c24400c09000159810446494500720b004010450f0b1b907607881a80f08440c01a0100442c074004182e08928034001107044035641d0714940420050b02942040e014005e2800c1005010014844003031070107503000341ca00c014040c1e128801d140c020310007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 62874787 1250 62873537 62873567
    0x91407030c0e0c091908010903080612010e0703110a09090302030d0e0c031209060d02040b0315030706120906060302060309030421030c08070501020403060213090e06060109050f0303040b0a0306080d 87
    0x10030001308140f4108a011901e11006040d000c03103d1503903e00145003116400b1a040380082c2c10041408214542110306098040c10300d402080200f05100100da9140005c0c4002049820703100892001d0b5500e01e14110014080074038140131070354041c50000e450750301211070079000724a40105002c819a0028110308007540150052814022103103038907259401c810762440d440001041014170071005400684010a2800b004603180d041c04220b0000301c07501011000d000340d2103c841040421350080d115020711204000c0010710a80c1403d00384050305031904040d4000b0000004e00020890000040003203d6a215021007001da004440303010b11400c0d08000b500068180750104d0204224400401c82a0f204078001413400b5503a5991034142e80004d0b46d45c66020410b00020002208130303004141354110000054040c9241c440d0000c0c01d030f21a5801801d000700b1501003114085e441c10811200601200103800341c49550035a030050103400a8010801c1901070b01e548000c0650080858041c80f1074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 62876037 1250 62874787 62874811
    0x6010906050c0f030a03020a09080109120c02060702100206061c05030901030c17010b0714061e060307051909151508070309080c010509060618010302060904091407030c0e 75
    0xc40c0000c11915a000b10226011600544242040c1a00100010840303541251405603c3d0408040c0c050110030b840c0c2c1c0310780040d90400b40c035903001810010301000a907055040c240039445280c00801c0c4a800f807003000a401c62800e4000307000d025000160b5030b11440c4111480302094240c50020080c0d241c14440c0103110340d00510001c82658000c2c1c1150160b42140d14110602c44500b80740c0100500f800c2e030001004080c0015418144030301803944414041840d0018070460421201d842260445003914850110140c3c010802c00e95060100000801004050701c0f402d0b50400369446000034a8417030540d116180c1080641d81b90707981d0801e00d00310b400030b20560038480047c00307065401c160300420070020140c1c3c50500c540000c0d0f500d4081c221408103480000780c24602004c5a41c500b24005c3c3c803041c03040102d440648541000320741007038192b070380c140c03155511442c0c2a40400e001d42602d00000f042549600a502c4000300005801d0084030300407013000002079954070300500204425103500d40220 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 62877287 1250 62876037 62876039
    0x60406030b04062406050301090f0614010c05070503030706050906010602061306051e0403050c070e0112060e03090904050d0201060914070c02010e0a0b1c0b1804150203010b1908060109 81
    0x81d1250b10800e1100d8080070140b0744c1c0d003500c5803109a000c12640100f0b011600110040c40307130030b2031841140c4549403405010002e05050502c1d0350703110240c002040c2d0411041103211020490309000c81d0008040140c126911390045107001d0014007000c54690000c1d10481000081f041c1c030026203203004030300d0140c0a103140c0d200b41c0c4400000d8030000b03115903085248645d0f0501c0b03083c13010052500c1203009548194903040504070f940c0c200f05c5554000225107000c4401070104600250000d601a0351204c1d00248420f032448205085001c0d2080680e40203680104200600c180441c80440c003115541c0200641e54541c20444211034920000703121181c80240080e40c3d10f8010f00c42d0440442c014100225903003050340018840341306c00d80204110700e00100b0162624040200308603031b0300e4a05070083c0f140c040381c1c001081d42450105495540e510141022800b4025901d001c806640c0c90b03480300f91340d40e41e16000811551351010b054100c1c6192648045200d680c40303604124020541603460745015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 62878537 1250 62877287 62877293
    0x6120c07020a09050a0b0f010f120608030c010b100201050705030c0711030d020c0a0e04350f03010f0603020315040e0309031605031903020c04020d0f15050405060406030b04 76
    0x44000800080000004000410269542c0c0314034800520044001142c503251013100102a503c411072418012a26410004210782c0c2011141c840c0626030302e0700710880e07201c0100b41c001070001e239404000d5502002803260744030a410b410081d8401416607404900d40d005c1d4104908868040b100c0c00001070301400418100c0e070340c180081c000075000344900d494031a80800081d05060728060348134056030040b4443d400034140300c0074020051420b50360b201041d1800340c0783d0220f1500e800c00b45124016254140b00c540d007002c01c1c884030703140b002400030f00d031034001e025100078142d4000e015880400c000e5820024070b41e0300c41e000302c92082003900580c228024100090002a1980403070070482030109000d0b6420a8804100c7e400610b40058140c0e400d071440d00c030903d41003944c90003820f2400c60740b0b6004400803907000103d900a44000f640d0050b030b1541d0341e881c01c0b03000345501039800b22441d0410210302c03880e61407542d04a003070307070021038081120b500c40a003040110b460b1484020b10101c045400034000c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 62879787 1250 62878537 62878567
    0x623010f122c0307050a0602071b080604050606040203010b070b191e06050409050d0e0609040504060506031e2a040c0504090e011a060306010c080a020703030e0f06 72
    0x19450550030801404030741050064180e400024911000d02c420801000c20000e0400140354002e542602451810300345456040d224048820040e00b078580004245040000303100c51054a80b00b45004580225210352040e52241019141a10f0703511402c0b012800a00d010f10890f0304a0300f602c80310510f070042a0343c800c1d00c4500000c0800c041d44202004050307120300c1ea4010034000c102840082c40480b401450f889040b620148c0209000c1d41c5450b8040c8001800003646050035442820703c2d2100d280e80200048043c4503001440d0340103803d0000340420880d040e085a40101c10450aa81d40050101d500195003011f80301d90b42d41c542c0c41014802d0345a885402a048904e000002d51141062040042000d488807107540300000780c1c0003e010404a0800d204001172696803d000b804415411000c00700c1c070072225414148142000404280c0603805211010300c0703664002c00240e201c80312000c0294035400c840c402a0080742a5815202e034628150745034101c200001865681002102000004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 62881037 1250 62879787 62879807
    0x509010f030b0909030d0e0a020d02060d020408011d0f1c030f0f0905070602071202060421020a1e0503060f15010203070506090c0f0301020903120d0207061b03062301 73
    0x249076440595411586941c0f60180c0314074900b00056590342c2e9054440c0c0d04850750701820080f1900840c3c02c5030016a54040c0541b00c09404a0f0201d490b05485605480280304541c411105503103040030080400c8042c46031210120203c0c001e8034281c0540003e0703d0745400030140c500603245030070910380e01441d0099109410034050500b00164000c06510b00008480740b00f01c0503030716039101803030410440d58104018400b130b00340500f040100c02e125601181c0a8003e078004c10410201040900380c41c202d90610f10006d4a070010a040d0145030385102c80407204540b400e007042d985c0c40010003c48c5030700740001c3d805c1c02940804034076141655101028689020440046811400100b00c2c80000c03e00400c20a402540590007030300c80301f0403501c100808103492203042402640140111001941c02164200101c1c144616450380e400d046107901e0000c0c8600390300106040c0c43c0880014600c1070a0040d1003c0c0e060f03d4034100442ca44500031006224a4440040c40b00000e40c1c041404951065441030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 62882287 1250 62881037 62881067
    0x13030614060f0d02091b0304061506021b063006030c0607031e0c050f060f070e010e130b0301020403080903010b09060a15030f0203151503100603050907080304060203070501050f0601050901 83
    0xf4146d041146081c025035441078a0070384145845110303059000314200c000384010039443c00200710200000002c0c2c04040d5040704024032803040820800c40040c020306200c4031558401d010b003500019030700a641d44250080c1c070300e40d0007845580c3c1d550b070450412204803042144c154403000742058804100b03901c040c000110030320801a032005c4032400200104a403c1c960340301c5402508603403030420780c4440c524500034408020008446500f01d4542d804c078a806804980c29222106034520203121607001c0e11084028035011340c4001000028003c00f00060031210104034002c0c405000345000700300f0400c8040c0c0c0c05c4d40d1300c002101d801300b00c2c0441c007440c0c6400c0c0c00c03041d09020035040040f00552040342c00c1210461004020700300c0000395840c00c0100e0f800411041440941103060140d01046d4500180c001c035028140d6450201d6106002040640000c0900030126030380c1e240ca45000039101d420030b01d000c4506600f4000440d240c0e41301c11105600c51034043c0e64380c904200c181c0004540804480200d9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 62883537 1250 62882287 62882311
    0x31504020c0f120403170301050a06030507230702090609060306070c0f020d03080118050705040501050903100903180803030c09010509010c02210f03030c03070c0813030614060f0d0209 81
    0x10040031101401508803281c0c10071003458486240d4100380c6110008111b0070900344108100601c5a943c0301c4081805852452500090941e12414259103105144040d5980c12007900b40013a5000014401000858400d80d070403411611801e0070b1281c004010781d0b10741e034950484c1c400540c90b98400c040ca0581c00340a41610051042190007040d400c41c043c1c5001e900050300c03c0700620451f4030650b4107402e1840406020030040c605000018001c2c0124001d050411a000481d0390b11542d08000d00b50b034100c03200204120850541c42c1c094541c820500035107800c01854400010450720210a5a00c12409a540c9925000e410401129160701003101c10f17041c015804100c1c7e025071200c402c0045a0766000624440300c07014145014682000e000034010154402c00801c41c01042d00f074203a94019203030b400e01c00038061592806101c0350003001e1030704001c5000d21100206005e43d035002101e50045500d004000c540305c1c40203200c0700d8010714a03840d4100d00c4034040c1e80c0c0141407e1058a50001c604071341 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 62884787 1250 62883537 62883553
    0x307020a0905042a0510050307020604021932060a020c01050a110f06090c040b010e100201060305060a02031501050403021804050309061b010b01030b03072d06021c0203031504020c 79
    0x16450280c4d00004c082c482c0803200b0140003d090184034403c0809041c2485801c40c685180000c0d40ca07000100001d000b08a0405428103c01d007904036440a445081d41050070403418003410103001d12414007407500002c0e02c1809034411306005044070341d1150b02ea0301500d50120400015201ca62106000318104044d4138090480c00c401405556200350070680641158180441080e14042c035210720544a43c0c500a002d4129030307080f8400220140c4c0541e0303003000034084c442d800e0380180400d90000d082801003204102290345681e004500c0ba011185ca4007220f01c120400448084c001c501000750818405250b40b40c00650101c06c0951042c450805c0fa858184d03900c011401a401c5150b00e04061041400d1301d408810081c001c4981c039034801c0ca000c0000c44100c20009555140368030804041c1c0449000d002181308404044c40d2003a00c20407141040642d90782c0c00291b440350000c2c007450360681094001b45a8900c04400c40e0300800391402040150b000c130104002c000e500c07030f061600451140f564 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 62886037 1250 62884787 62884823
    0xb0301060e0d1e0201080601030614090a0908070c0e071404050d150f06050f06130b22060509010809010c0503150a030f06051801050112200a0f08010c020307020a090504 74
    0x380f81c5008400782400c0c41c080d000180f00150031050301810b150305040c1014801d01003584612080050381c07808413110b00b620344402a204c4010007404601400c09e6030700041147c01e01c100b00080c40c04442c100c6001071a950780d680360445800b846040c034240031300401c00c01000113241040403140d5244c020804841e03110710b070002c1c0c0c01c200d8682d08002c040041d12400c04010505e42480300075000002a2802480c00726007030800c80e08041c160140b4014071a0110304420108142000181405942c1d0909070140f515407038050b000781c01c03080110f40007076644000640086018002c0e00c1c0b011034203071076090450310341591f460340040d042c0b0f00483d002182c0c9940040802d401e4118000355a016490003c1c0368103041c0d80749000015a5034001445a0404004004a81c0c05032003009165421a28020340c003010b801012403459440b580c101d40c09242500c010a4402001d00ca070341c11548080001c014414654000303030b03164080c2c808080d50004e07200c0810020162030750801e6074010300c9400600380381ea81d001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 62887287 1250 62886037 62886053
    0x1090903200106050307091103040803130c0f090b010302070f110112050109020301081c0e0609060904020d0b0906040c0c060911060c01020a02060c070f02151606091b0b0301060e0d 79
    0x1000c0d44a6a440d160300b0081400d0a1190401a121807e024498461000801800f910014200601c1d4070b00020000d00c0000100500c8010154024859850160303504280750f101512030260b40d212924000310140a580a442240e0302d00c0d500c0720134010496125281d030708030503088200403810b20051010341c116001302c1d4400d180c003078042d41074010307102c0d41404480e900c1c20400300841240c100080d1054659650030005510401c00c00704d031910b036034032010004039a0034011601c0098006002080e003031070070090394106800c0321506440300003075640c4000c01c00094071003a8242c0c0380460220780e00c01c00841c0c40c9400c1602c0c0c0900511120020750780f03d4000c150240e00440c06c01a060358041201001140d0500c0354941180060032502e04081c20303a08d03070421204603854024801c841101c00e0300380c560301a50a6030048008101c4081d0401d20b20700300040035100324101100e5841d040200b55900d0a80134140340240e400c7c2400d0f80f070440c0c1c202081030f41c0c0441c02040c1980d00808090804d00025050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 62888537 1250 62887287 62887337
    0xf0b04080c2a03070b0f07030309060504051027030c0809090f04170f09010e04060504061706100303020a02012d12050702070302060f0d1103041410020c0601090903 72
    0x14105030b001d420012003118024040c121014841d401c01a820000f1200104c1030350700401148a0155440e070151409600403c00d40c0e130000d24060600b8100024000003040c1804910840c2d803052001c080d41000715103500d42014110004007080b00d8000c800b1a20821710340c404a4410300440340383c1442c01000407003441007103400309c0e6014820002c0004002c1141032002c02e1a203440c410340d0800c0507074407001e071060180c2c0900904001301c1550762610b65a850300004003c0502030010001c950b162000408000c0d641c444210051189038085031803444038050460840760554050710808000c3c1e401144ca00709500110703051813000e0310340549500c9000019050391050380d101c0455103024410b022090f030300024200700070354000980401c05a1900012520216803803525260754994460520009200190603070051010200030401003105c0c0003200f10203091035900321902c041441000209912510100092540044c1700400c440c2030290412950240310f410081890b044400c032240803aa86 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 62889787 1250 62888537 62888563
    0x150a0f0c06060b0912030a020a020d0203101a0301060b0702030d030e120a1805040c02100e070807080322030c03081309050f01060305010824060114040902030603070f030f0b04080c 79
    0x4000744e8114945401200e4101c80c800d407101460805a01c0c280c0651a147c510f40068010888180303014119074003444502c682c1403030030204108040200c10402c1e0305c0c512040209000e9840c040d000b00d51300709031009458816a004000701704080e8800e404070042c01001c69501080d210300711051136045020307000b07001e10241c20750700c1c605c116500610701002510b0700c2c1e00403401149800b5070b0440456010070040205c9544010215090344040c0000b4a440042d60084000e40110200400d443c0c00201c02056600c88141040d10b002c1029408540c0d041614400180030b08407944007040010000b5015040500241840b0700d0b15551301c40e841d07010b0703850442d5900c3c9410703807803001030003000d405210782d0b4013410080c8020451020704607000400701080e598280034211a52001460313580c800e25002c2041c10b0003410131511595503243e5030019400c1a034101e4440e02070071501151489101d400703002220f07084604d9001071003c5459286d0200d90242c03082d41d48503010002010812030402201e10400c031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 62891037 1250 62889787 62889809
    0xf0d0c030506061216180e010503060f06030a060f020702060301090b0915030a0b0901060506130305010b19060302090429041a0f0111100c09060e150a0f0c0606 70
    0x40040072500e008240e68840d200501041880d03008148155034040071049000d4a0040c00000a54506003a0400e9050012103070001048048810b00114100d480650460f200c540f80c646401c00c00201c00c8812980607803102c815000403c01c2500031a14074100103400524060303564010581c1b5500c00d80103140780a803211004911401c00c6101e00e0b074800a486100c08020314400c0020f034a4041c2d9140203400c602052001c920030480a512140c0100001000940d90382812a4a1005034002d40300555085d441c100c0d071b4041c0d504190100c40c0c0c20041e16070389052414100b02080d4001e42004c00c0386034216a07100d244030360452491444072500b101d8804080c260003a290200700c1034403c1444032200d40c0481c00d82081ca29151080718460b5a902420542e0b404234184007000c0c40c181041100140060610124410154100b10300600f5200c2650b038106034004403070103100040700e09401082e0754800c02c220361042d03688105112141107005192285104c0309903141c1505464040c1c2000003018 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 62892287 1250 62891037 62891051
    0x305161b24020c0c030604020109090b040f020705061909030801050621090f0d0903020f04090302030f070606170604030c03030c09031a07031508061315020a080103030809011a150f0d 80
    0x2020410603400d00c410b00310020940e0741f6080e800280140300c02e22541c5507403500d9901c55240b60317541d0303003100542c01e81c0c000085444101a0400c0395030b03801c0039507021400303003841c0b40703a41d0f10384986000d02926260991a50186646000c0c180202503200031803000c965584040e003101484101c03d0300743d0240302e855004165001507030040c241808407c000d1801072140010303041006866005918981c454111170006003280d04d420240c1c11480341d403900540c00b440c000340400401c0f00f5588003809503482c40c600b050f161510400c00710358036082070b00c02501107083e8011a00000307210741c111641106103850f181c00c0445d86c0e17548a80038160031030700c48090070021074100f1001551500c00d4001c400480c07450600f00910b030450198659030083c00011808030902e44003400e004041118442480c11035004554914039000000c1401d1000e00080700082c1445001c1000040b050003860f0042203403c0744201d0710007151040001c0b14004088043c00c0c04018420210728041a002402c446041960041411 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 62893537 1250 62892287 62892307
    0x609050616030c0206060f0609030d0504140109030203030714120403080c0118021005090a0f080a0201080105010206090712020d12091a12010b03060118150305161b2402 74
    0x5501c0301d07100d0400700b502c2d0109241107554001461074010100307441001014007074601080082c45940180c0d034042c85001490607481e94400d0007042100d0200c2c004122460303800c001100c500c6074510000c0e505500612a203008225a91680140c0d8a400300031240103c86180114006801039401610580e03c003240e26503941c1d20a0050a500703860b40d180340784a8904950006102072a07500b114000c104010400382175984501c0e603208e01421b030751108a101d080c0c0d58004c1c07a64500d100c0704120b0008032544000105540009045e901400c05030019160f9103040c04020080c0d001d401c0340580e8031008401002d00400c0007540003820074805a82d904070790608141b0000c40ca0980140382e9400030310100030000c902c1c00300041203415030f03a03426055a40c0391103080040711510202040134588103c2c0050016400010380f0400d0880e5800e602d00744401c0da81c2d10300c181c03d0703d2031400400d0302103416100c000c0741c0c1e40000e000c14400988603507105000394002000311039801c40c0501c403410005a00007001402 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 62894787 1250 62893537 62893561
    0x2040e010501080a0b150307031202210f09030309061317060403050301090506010e041109041a060904020a02190606060905120726060405031201080d05040e040f06090506 75
    0x2080244100034032041d40340000d0140e4580c0803000103042080d081c008104007803c1d2000d998410007005003200c0103180c580c101403400000302c1007940054456601e85c909428045c4140c0e00d82c98200417440e5003480c1c050349001d03200d5441190f6041e8103000c00c012000c080d80c0d07904007405012000441c14070780e5a05044035003000032210b1000404580c0080104000607074030004036410749812950102d0151222001644c1078115884440d41c050b0500241d603481010001c043c12182d60211001d00c800d05071102255043e40d03c9001d25600702c0001c00950b46903090a400500c0e084805204030f03100340310f201c109420701d0389030004100c41d075648034441007190b01da01019040203040110760074140404a1103129907254101c1c0301e901c0051542981ca00354008017103803120044c00742641034542c20700d00fa00d800e503180d51166641e4a003100c1090004140c0c03020005050020807426200c151500e4201190806001070040c011100c0b00703a241c00501c0010036030701441850911943c020500b41c10902c080303100c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 62896037 1250 62894787 62894801
    0x1090c051008090c010c0f081902060106030e0703060902180c04051f020d0c03140c0606040c09031502090607080c03070b0f071409030102040308030906010f05010206070c020108060406050310090204 87
    0x1c00480b54180b240c008004500b031042442e090828014801103487c4c42c41c841d035403110014004040200383c3e040400694008080880061350a496103aa2600401da0850790001101440c035402003005000040c03190340304626040c00145403080a003e085944580010111a10b20080740041420041d03401c1c1a080488501148020708a406181400c000e40d03070400701508000304030350b07504010241409030210480c0d0150807801280c0d50516030b91480c1c2e4402c01a50100d000324901000394208511131032402c41035907809507600e884074124811060203500030341c91031a80414104481d00005006400504a104558020f15150581d40c2000307007140b8002000d04101010741d1040000d42944403141040341011140d010713444031090008240203004e1a0002401440c0000a00079aa500058040c0c12602e00344240701c4107540340da00498072010700b0b50303190010448183c2c0c001c0040d030058072081e612000140000442c2a92100028907105c1c442514100190355030a44800303500f0a401011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 62897287 1250 62896037 62896069
    0xe0d02100e152802030c0706020a0908120901090e01030b0c220306060501030b042007080904050109050405160f06030b0d0507030813050d05030406030c090317030610080609040809060c01090c05 85
    0x505628040f0000f06c05031244100c000c0c100c40e40000d586446a01940045000c5c2c0b00400403110203c0d81502d200015500040446010600d044000038500711070080081c1620380c0203106111b03a444582e03070207082e604035020788442d11080b0980d100b104810b00c2c40c0d00300118082c880c0424150310340f50001d8100c0f902c206005020f1820840e00580036404120bc030050b84031445140c1c0e59481c894208074440740030728424540d00ca03052000024847e05141c1109006a003d0019540d2286071040080f96130822813241c076a0741011385408200c807034001c1d0b002004080c00a8900905900d06eaa20b2606060751a082251070141c081044807039070a0108120026000649280002c80c082d41c0b9400d80d28000d51007244201034032542401100c0b84100504c100469001013000301c0c140c1044c1c0100050340007103030f6550150b00c1d502009011140b04980503400b80a01170896402038071076031981402903011a031040c2d0020350400a0f1420314509209003e0b14a000c2c1005100b15400c1008011041604e0803240b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 62898537 1250 62897287 62897291
    0x50708090604050c01180b03190608151303050403020409060c030605030c030304290a080708070309020d0f030201150b040306110c030f07020411041502010e0d02100e1528 75
    0x400260000340000d0b1320b04d003d00708141c0e844094140d2200400c500c1c0c011460280020060080c60104e05109250440703030b000c4244450754540b038181e6600d450030001600c2d5040f000d000310f6100101d0050301380c2080d009242091400e5281d40108003074502444c0101c1d100340d5544034403107415a040c810350010340022070180400c0102c050011b550b0340114003c104070440946101c204e944408207030b101203820b4010600d41c844040c2c2c01c0c041c2c07881b1411074a031800718075000e00280030705100e41702d45040326a004040444114140d2100c80c000d801c0c5040880940d96940a03e40c0d01500d01070390707030008003002d03001995642d05520340001910215015031311150b2050040f00038124000c000d94442c0c9401485041d1202c1180c0001005091440c18041c1400070010780482e0b440c1229100004d503961680082c001780400c10803055444051110307000c01a00203581c2c0501050301d036080050a4608481100d010882c4240e8100c003144007540c1c1c050001c3e24008041c0401071449030140440900c540003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 62899787 1250 62898537 62898541
    0xa0f05060a030b060d06031a0f100b0304030c08031501090914010b1e040906090e0606090a09030302040306050702030307020f0706021c170411040b031c110a150507080906 75
    0x2080c0107000d1400080207141d161049041d65886010969221210707041080c070400c0e40e241421041c0c3d0350300f125095440e008510018102e000414031031380c0a4003070078040641d02480c0400c11107540c0c00c0640110100920f40c0600300124420740095805025a00007540414048000240c050710316a0701100a807070503c072000090407032440499044614100026594451001102075112903a64800f141364201241c08104080950701060954001e010100540141e00f0002941c814040b00c0392039001081e100041d000314025000013501520909000d41400d440b07a03142d40941c0c00c01c90b8114010f903c003000b0400034950400885030b500754000083e010060410100a480d50724812071510800d1010ba0107003032081c880c019184111400000c0c1e002a0300b414503120103294962095140f1803424a1220031451401140781c80d0000d80c800c48010110f10400030940d0110000c00100704240a48000c420104d0070b80302800d010740340005c0e0002580d00c0d0080c0041c0000c500504481c10550007030301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 62901037 1250 62899787 62899789
    0x601050f09240105160305040f08010213030201031d010908120705030103030c030c022706130c020c09042103020306010206100b0a080c1b151302011403040c05040203150a0f05 77
    0x502c0a8004603102c10b00602011005803818421300c07040c4004c2e085100625410b16500c0800b41080c0c42e2883c400f0900c207507a0721034490031307401003001d20b000c0c41c40008010401236000f0381c042000310410f50981d8001040c846842821500c03030604c1038035800e00c001480c1030718014034184154440c4c07540c28628155411901d0040c9a0005410024140450091464255a242d19500f0380c91134203250412050b0030f02c69107924901c034040c1c40090181030303c0c88200c040410503004440203101c85900034007084c4103090411606400180c026113483d020001ca07051106000544d04080010742c0d1009656424281c00091400b4001131a403021b07846030490034404840d02e4412079410301c1403841d216886844806843c6420311405d00e0054a48070b004140402c0b42ca0045283c0790035100b2001c0390384255461040c117804204030118000d0024604100d020743d03c070407101c069504507004031104402c8070340b1130000c5000ca900a48005002c00b08858465030680f0301802d005010300303a80c00c005030304589044 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 62902287 1250 62901037 62901061
    0x6010b07050a020a06030c14030717060a0812130e060f012007060215150d0f0f0812150117060607050a080a0804120203030c0a0e0f0405090601050f09 66
    0x20086441510000402005119080000b0b0301015001041c10884030380d100c101a000b0103407000d44102103641400810005407140c0c0c282d9216510684174814000000c0c03e12040b0088010007240e40440c0c400c3c40031404180070841b04942d00360400c191035581d24540c10820300369030154441c42601102408200c40b80d203583c2c40d018540c40b02824400b506003104084582c904444200184480c814a031000801c10340c009842c01c4400c40340c102204c41c50300e60b2001e90400d42c03940e242207a0841d03102c40d41040051f43c810000118180603c800382c407400159680c0507515070008010361142224501030001000c4508800b15000c1002d00f084080124842150f1100b044010900c5100fa140800d0107002c1c414140481c1c040c0503030110412341d07240380503003001d84030503420354080e1180703040c8608000c8018000022207000d02c00780c164060405003188022100d9000c030003d640d80016600e4005895511540101030082060401403c0150f05240512a003000e08460071842506000c05100d040d030041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 62903537 1250 62902287 62902289
    0x5010207030b0a0212072f0c01050f0f120a0c020607080c030a0609020304060504060506030601121203020c060403030608010c05040f0e07030b0306040c0302010f080717090c030f01090c0501050304050601 89
    0x30090b42000365840802c07540082c00313005821000c0c00501e0040002d202d83c0300f245241c0e422054944501e003000c52480504d922a51110402c0302c0b507010780020718480d8040c0380640285025079a4083c034085111304d01e0011900610685103404c5000f030107009650365a07014159025000b48010070083c43d10003030007000d01902800c400902c841c00030205200016a40003103018003603150007556a8200b82c581003000b410101c4040d11150300c2d29000c65107601d03022403064101d5480d9204103918074016107030401c911808500d0ba1044c180e0030402451864070078001184200c1c007941340010140d00c0c0c1185182500c0d80c8040140800900300000d0111300c005103074100a4a012100f050b0071991545000d40003071041b407030b200d0780c984509810801084500c151102c190b9100381da0309040002011000c0e036070343d50140d6100e40401c94508002d0000e545141ca416405135208040707920100400300424280b61000c0001d54581c1d445070701c00f03028805140000e00044c00c1c00c2c41c04030701d1484c054541075107503641 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 62904787 1250 62903537 62903543
    0x90507020312060f030109032007060207030611070609120909020901120902030a0c181103150f0a17031209030c12070602070206040b04030302010b040b03060a0e0f03040b0306090109060501020703 86
    0x60b080c00f00b061030312551101e0401d40d401030020001002241000751141003c1e100c02608155151200d000d01d07100851000212155500207001407400c41d52070760003411301240c000000401c00c1c8501c07004940729004428019024401c500d40d44415000001c2440280c2d07045200700300e00400c0000c800d640d11529200106107c0000001c0c45030582c800242028110003010740b00c40015207000c1002858000104445140d82000300489100b03146c0c42040b80c042228000d50204210200002d207007040d120400d01d941c002030548200c035032986c481c0c19042090464011a0368400700c3c02126010344200000d400c481c088006600b40440c0c00416559601c1d034101c4540a120045444030030002070383c0648568540c0109036580751030312408046030941007444103800644c2019000885030405100e1001c15010242c05068240e40f408102d0000d402d1a0045404600c2203210920100e00d060000d84080c26121382c440307039242406010001d0000e4180c01000095280c0a420406603800050000c200c0b58 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 62906037 1250 62904787 62904817
    0x70c08010f1a06160503030a0506010f08010602030708090301090b01061101060509090303010302150d1109040506040203040b0a0c110a0c030201030b0306090304090c051c090b01091802060d0e03040303030c02070905070203 97
    0x213400380b21002a26109002000c6200c0401402140384007904514464002070ba1170301c204601c1502c044441c4c0b0002e10505001d40c2040102801042e213150051a85440150005c14242c101d6a510141e40c0c900340d000c08001492a000c54520020a010307520040500b00c8000850b8202940303090388922062100070312070390502c0441000c1002080a580d058850401d003002610070030b00d4a00d106600942d403281c421460b050000c1e8152070a0310a40780a80c4c0c00007003c00480d1344030b1a480f030060822082a4003070003810100805c03034480030041a00124422a2800450751440c8005015143c01044940c0301e60400c5040014007000041918201c981d401408199031400110170350f003d00c200301000118403002000c440c03184407560020401c0b5480f0740361488003070307a8031002c03481120517401c1842021248041e40b40d015141c0317900500040300c0008000a00350b20700c218410b24540c45503200714007080c2c031004066070064050010074020042c0c01401e00070340c42d101d60000e45a20410000300100a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 62907287 1250 62906037 62906047
    0x70e06090a06030b070c0203060709060203030601030c1e12060617070f03060506040b130602030a09030311010b0a1205060f0f0103020d150606020f070506090f010c17070c08010f1a06 80
    0x2a0042e000000255082a55004e05041003200208003110000c41603009110309000710316110300c00c070310b41c1c0300300d032000d60165003541c50b1a801100030700700c40500e034410850b1540f020094440c02c00140c00002e803050300c0e40403100040c039107100180c46481d07003e403050010342280a01040c95009100e80d004020740342070a516500b4101c241c0050406402035034004001040100e0104101d900800c0543c2804000c02e00719513540800304d0742c9205a11020f40091248401003000a00401c40e019010750300000100f0780d4101100482c404138000e1380f10202420181c5d141509100050004a400151034200d1000603d000e0a40c0c103000c030300620000b030084001b0030045d4180320861a5143c3c102c58140400d0000664592000b503903241603d428401c24014460001090f2900004449042c00060408040381c0320580040d120310501d10800d81d071400c0307112007940c030f00700858008004080c0b080341c3d00b40c40b4504100d40c5a00b140d0800ca00c10034001c0c40d001c2405044d258031441d40305490300c111440c9075030b2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 62908537 1250 62907287 62907301
    0x31e060403050f12011211040606050a0513080d0e0a06090608061e04050403080612031204110d080403030201020a0306090e0a02090c0705010e0c0108060d1104110715090c08070e0609 80
    0x2500c104900c03600808500e50001c0385000401ba44031900038040d070500c2440c42241000c20044030120b10940c00810010040c13907040381e000d00c0c003502651400c0c03100d60070002c0c0d07582c2d0b06a05103580082c004000070034030000300c0368610f4140d040740d000c3c201354078001c80b6441c20800058004040940000d100c3c5022070540510310b803404580705442d4401500601060800340b5000e07080140a07507c1c544680040c809110000d440001a5a0151000192080b071a00c998403104078020500e107200381c004088020020100e94400e00a000031403081e400140c1e1560003080060454a550f000710580900700442c6507104040040d28841c0c1c180c04507203218154450740c0c580c4806129196009105500340700c1c0e1401c44010105543c0345d031410130788a0890356a00d503003c2000604074044010710301000800342c140705040c10340c030102098010b1140c142c64880c850312007503040020200484101a29020010f08124007104075400400b104001080700034148000500c2910000b025140a0b5191000003a82c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 62909787 1250 62908537 62908567
    0x1e110306042f340203010e0111090906010c0507030803070f03020313020103151802030103060608030a020304140102070e04050d022b05070c0e0c0a0f1e0f090e1005031e06040305 78
    0x2c0182c2072801c0700000301c641c3c034240501d001c0b0001a48179528010940490311418003c0d00c2c401d0131201e6980b440c2078504402c00c80703c00740c0684403e0401c840c410700100002c0e001c00242d0040c50003502c2031a16131801000c000c1141c122408402c04150051040c0001c0e98842000d01312100c0d82400c0100711000c0c8420f2003b09005071398402c000c8402c060000c02102c2e07555a0046050300d000f14002d1003419210701c01e40d40e8900c98541d5140050f4400c0004102e1614214030414101005105a9203c0c40d55900340c800102d4060b1000d41722500211810b42c0c0083d01005050b0711480c003a18032a103004240780c1081364071058a400d020a200d8001104001c20555090440141040110340e15243c1070003140c0228a4201d0707041c040210315410310300c010f000d0041c404208620703039800710309495042075441104d080c80c210000a00307110140c80e001c900042320306052440bc280d85c828031030107503162000301440c0280981d1444038005038a54605040c55000c201039600513050b0030034681e141c61079840750b94 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 62911037 1250 62909787 62909827
    0xa1a04020415020705040c0503040b0709090f02120f0105130e010e0d0905100503040203070b0a020a140616170f0709030b070e040e150a1e110306042f 66
    0x150291000801003440b0005007550300c080c0707505608440c0025165010700048030906001c00001c501e0500020340007503118045241c1c4196103103001c289a81e92511000c2c20380350b181c1340115501c0e40214038001c4041165070081d600c0b03107803090b14600b25494000450030031180180c180318866280c6c44205002d120941294000c1c5808c041110703540c503000750300140b4081c0300307028161040f04076022002035548204192030003650000c02030034500c0d1174000700b00d4055206008190a42c0101030070580400d803d01c2c0c0d24404c0103415006080346150810f812894490a500d5020501c040510f482c40350101040b2a06c3e40b01480c11030040060710f65030825101880a9480100300c8802c540400042c0d642c41040100708000503201800780044009080c0c0d100e01c0307000128481103400000103040c40751144c00110081e260700c500c12001015228031201074810b00b0b4840342200c8c1001040c4071050501d0b2042c0b054041200d2210301c040d03610200d080b880310015072001032200002195120700c200d0b414041c01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 62912287 1250 62911037 62911039
    0x30907030c0e040b070c200f06070f020102061308040302090402030708030406020c191d06040b0303040e0f090601031a070315080a03031103011d0405070806010806160c02090a1a 78
    0x100c01d41d502c02e082000303240d08607401c4403071007045008140b00c0c43c0192441a1030300d900200c500904401e403040b0080740c401c1c6a0286900142e0b26400d04404c0d103c20008100e21030040c490610341c1002c80c000a454524003505580c4050700c841c0c44600410540d40c1681c056a40c102d507010b0160715217000180c0741ca01c1c0d0f0f805c2055180400200021415000580a00041c0341907410710100940d1481c0c0f4800c1d00f44910494000003e84000d00d407445101d282e44562200b4002c0001803403074201c00101f4a19041034101e41c0c44110200d0601118254556005a0180301e000c001d148075815035860000307400c640e40d151845d250070180400c02040c001c1e00200380c03840b441180c0c1142c8030307034501e8550b43c2c0d50001e1000341c0101c2e00d800c0d0103101c0c0a00900440781600c26a42468805412202182500000041c026100c0c0e0042d1207012480d01018420240244480001080f0504254a100c4107118003080c03100c0a220800c1421001a201e1000c05a0f01098404000400d0002c4800603078505149400765 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 62913537 1250 62912287 62912303
    0xe0604050d06020f1902070b040302010f05030910020a0e090a0504080f030c0f07060c1b050c0d020111060901090b090d0c0209130605040c150810090209060f0d060302040c020c01120203090703 84
    0x2204d500f9030917076030386061401943c0c21100c00940e1101c111030742c0d03c80c9000181c0060410307504034441038020380003560440c1c2c41c2411600c104000d882c00304101e8005051100009075030081103502c81c907050f0b140c9a00280300351300030061420580d45500c0702d0311511034401c0182c28040009810394041c9002d5aa01e44604003182d03665600c0362400c02d00410b103101100d800b06081e45102131642000c085a500b00700c1d030280040c4001090b5008101c15a07039902c8049040000c1ca007010401c65a003800400d000301303500320002c00c0032101840c00c3c00c0100030041030340006034000990980155404011480480e070191090b01f240c3e1034006c0e424800300b201c0c004c00341106040001b4001046075072000c0c0e030116131241c0ea03904210801240100c0f100c1d4800c1d12406052014254288882881e030383c0180703500d01008004500d80b0602e040300082c9034200e20384035541a96500401c0040d400d01c0c1c0103842440511384045c0c50341201040010305803c104444080c0c26a60120001d54219410080c3c0409180c1211003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 62914787 1250 62913537 62913547
    0x70f03050309040c0c02030c150423150a050a0305100b162001090e0a0608070b03060a09020a0507200d080306030706090312080901060b04080a060605010e0604050d06020f 75
    0x45940d030307a0302140445025910341350324011110301c03030b091108445a0040140030b41c1d00c12001080103481401000c0118200e04001c0000c01c420184808640161500540c07040c81a904c004c00141106800404810200c100540c0c1c600710703880b2045a001075043d044c0051191100c501c20a0f11017140c0d0003007241d840c030000342100c2c0c8403d12a00d07030303a84621620344101c00b0b09404031091911034a44c90310a001c110410024091548d190202550020141c230000503902c0c0c3d10010240741c04410b9000c101c618400205122981c24240c070520050589010250302d40300750480010103d11401c034001e0704c54240d862080d15a0f481d41000c00c004460002d1201251540a0814031380c075a2099494178401e210700000085c0c2d060151402c0d00840e40c002030f0110200c030b030380641038400c020000c1082005542c1d034400410a1141c00c8064400f17041c9410080407903d02e540760820466815400a50600c80340c4032898400c0c0e51443c00721800d03100281c4488284401a01d0808017a01610540e04001c05010031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 62916037 1250 62914787 62914793
    0x307080406031a040e0a0f06020f0304120906020a0b01051002160f0509060a05010203070305070804050d14010515030709090501140a090b0f010b0a11160602030a02010b03010615080702070f03 84
    0x308a242c142d40b008075001c80d040f04101c200d842c1c500d1500302c5500400d0b90745012620b00030f190707030200d0300542002d440c249040211407000d500407502100d181c0d4400780d032145469400701c1811f000e424240010050300031240c480e000001d40504c109881081290041c02c0da031442800300d248881c0b0482810241e07951201080341d480100c90060301e01070585000010158030b0400381c10030807100181c016501e070407040d071011149a4000700095070441c1d403c1000040b2501c9026a0f1040e603401410303003003001d060046038182950400f900806290041200c42c00259a000ca0a076085820040d40010002a1841e1581c0580b91004042c101e80e010101000f1014255401442c003070f81c441c2420015035aa902c0303000707003a9a82130280c80c500300c000f44180e82e4580e00460b441000789407040110740c1c0010540744400050b000c250018001030300081041803a050b02402a42410b00301140207000240c00d007a200d03007240c091102c40344208900701020600300f9009204e2070f00a014101c07a00b1100783e0710780c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 62917287 1250 62916037 62916041
    0x30c0204060b0d27061503050303010305010501090b03010e0d180801060b0d0c050a08190902030a150612170f1c060807090207080909040503091e0a0b0415030e030708040603 76
    0x8402443c103181051204441100c0e06210407a210b1008101c00d60801c030320307440b0440144555000a41056007102020000c6001003001c0d60003503224000104056040c02040c0040d03e1240b5420382c002ea0418030610414900440e942803640e43d41c2c0341a004014450810384030034410384e8084042540b0b030001c0465031507880e000400300d02c0d00515090000d0220240c0481d014418040c81d600000c0610f000b140c00c0d00403400d015030b624085c11402283c01441a00000d0800c002d9000407992440c43d0342c04210031140c5030240e000101030120403a860312050740c1300c04002c034a081038140c844040c0081d250350241c24140035200a60020045101070f01c015104e43d0000707105a0281034058401c1407400250400680200c0ba140c0c1d0384486910300305a242c5090120000014000f110140070034000d001d2180c8880d032a01011030495600a00000c00070414040701000640240d012170b20304000c00e001c0300100c2c0e140723040c00329124a00011050f80c4800001d083d0300400f40010400c4100050001d0820350503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 62918537 1250 62917287 62917297
    0x60c0606030d081905190e01090308060906030307140109060507020307031409060d020a02010908030726040b0f040303091209030605070e03100902010c0219060207080a1a04030c0204060b 82
    0x96040314460b40c0e901c1c1040c2c951003011a41d2080e50404091182d5003000700b038100c690480040e94401501541c0e03108654142c800704500e00246a40d51010320b018150311913001034002c13600360b035024541d05218000c251207100b14100074280d44000c07055044950000d500c410807079904400c0402c11420001002500d990010f03605a002030740014183c0b451414003422602505c100801b09882d0614801005010b9002101e0600c10b5541c1c2e11000d8021500e484015032045459a070b4030008042d5810510407000d03d0414038400c0c15005c4810040001d84a048041c2c01000c07802510250b40c0c5c0703624040300640480c00d40108500d030a407000462241d00140c0c0c0c071050700e1040c08288107540c1c1c1c06104441c0e0000700461142d16901803a40042140c03c10382c00800c03a68010702d8815041c07030040e0086145035403824150a0514180142004081d505002d200090071b007907006850442d109498440c410300e440044401d08003080300201d020540281541c1c82c0c0d081e4040c0040c0112966070050481c6a08a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 62919787 1250 62918537 62918539
    0x1d060f0c030703080a0204140d020d060c0323010b1e0c0a0302060406050105010e0d0201080702010f02040b0a030507210b01120e3403170c1b031009020f040b0609060c0606 75
    0x2007080842d15005d03850003541c043c0d58010031140105a11201001400e40e64400b090b600a1100c0300614045690340c010851458140c0e10042104520321202083e450340f2100741c040e001e141d200052010031100030031105c000180e19034600550f40c40c942100d12520504106640c03911540701090209034011818910460161004003e02da0b82d840040d189050308509090340907a240b000000190700039404581c000003503100009031003451703190002c100c3c1d1050300540c0c3d010002241c040f290551500a455012007149040c40c1c645003003500540200401081640c1c08644480111110740d00c1001441c03043c69a0350400d008540d00b4039052a00c0e150130180030f901880740d00040d014203200d200c981c0b45662000700a0400e00a01e1a10b4082ca140344003840c1c494120ba04011100261381c040210b86d00381d150340d03101d103158039031624101031a08000d103401c0d480f41414940c828000d655144c0070500102001ea8002c40d0601030800041c0403840340075075541c3d1010001c24400300082d0700288452103900 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 62921037 1250 62919787 62919797
    0x20313030b01180608030a2a0311011b0504090b0402070803010605031e06030c0d05010b1203030106110c010e01050d06030212030d0b0301050c1b1002121501030b011d060f0c030703 79
    0x903800280c0c03c2501c2c0c1d503000e2443d1a82c802c220b410251446150400c50b0003074540e0b901c5030f016045211800201046030b009800081045000c5401400f00788500c1d04450100b44807806a2041202c2c094102e0213103201d40444156580da04035000e0304e454049070421030b80f040d10b0f940e481da12440e01401c940c0044d142c640201200d0030b2031042030100d03051003034005d01c401802864070f01a00340410032280846071007100c0715500c0c5c4000031040d49a0003582c044002480c0c029584a40c101500288514500c0c01c041e0615440171038040305907600010140c12100c000e2030b0542d603455034090803001400c003070380c0025007045901c01400000071020014010042c060641070003150544010035090f503505841c03013403001c2c0c0204101d4950f80000303c2e0081200c505141a01c1840c403a4224140403600042c0001c0707000c01200c2d08216001d80d44912101c1d2281c800d083c1002030b001c8041c0001d000201e9041d010341e04c11512403840049588120584099041500c1510341c1c46c4035680c1110340700c1d0450702045010034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 62922287 1250 62921037 62921069
    0x28020d0207031107030b0a0f09060606020c1807120203071b050c03010b180105091306020f0d0b0d03090b0306060c010615020601061b080703111608070f06050d05040201020313030b01 80
    0x2c000070407188205e82e044040d81d202511070a54840040c5106c0c048104041e40d98000c0b04002406401001c00901240c2c0150080714606018001442103d11079495403403410b03000c100c1c096810000303609030840700480040c0c59907105a0107070f038108120310070031104642c0c107081030042020000f5821401030054000780f00c0341c0b10080901030140f40424080a000c142d410051041e802c0c60140f0715440507036a840c0103d110980d0f21080c00b280e004040e0312210460009002d640e00c10a401040001c01d070a854100000c852510300500d42103450140d2030510300c0000119005940d01c4007668482d914010080110b5a51210030b01e071102109008807000d070148070000280a4000d8074901ea80c8881c180940400b0201130f582c1c9080e96001c01c90440601c40302e4071b41004007620410124040001188540300c0f21070421000e14030340401d60f4400d1400c1200c005050091320350103010f0382e4454a03410030101c1c00f42c071144010703415030003504400e82c3c154124420002c20711641e0701a0728100c40004148021f41 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 62923537 1250 62922287 62922317
    0x3110f091018060b04051306030f0b04050c0603041109060a2d21030f090b030a0b0a08030c070303140c0102070308100909020f1905091e090c030628020d020703 70
    0x2590f03040c4940c03e40e2541c10b100c1008181006402403d003880c6001000452079169900c0e83d000601c031500960300000c600d4108405c02c8010131540f051003104454507419442d19076103003000021107629142c096505030300030815684511540308042c051a071103a0a500b103040e401c0d60a1102c2400110001035206800000c00c8030008282c0007940640003240011381440e520280c2c0e41c0c1c000c0c91120010845000000141c4035500c0001d54003800002c140400c040021804000c1003076141c0e0810b900c1504100002400b55500149480480f44d060900046841001c4842e0035072b40034042050701c00d5400000c220341050341c014559803041e640d811165a6154988042c1c00c125404084000e4000c0d0204070100000e10f4110196120340346103184c0e11403d2510380c400300701a090f0946100040a185001528400310700894407980241140c0040190610a20001c2e50f280d4002c0c0554580d0901046c4000040e425912500700d5401c07010fa080d903a0f25001400701009500000041c0c001400b414140704030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 62924787 1250 62923537 62923541
    0x1020414130c0f05031b04030819020d05030105100c1e02010206130203060f0a0905010906051605071a0903070614013303020f04050301060f0302040b030f0703110f091018 75
    0x2c0882c1654503101c0c0b4400d407078429500317503001400c0c0014428181c2498410840150020005148240c1c0c4043e1900c00a90407030388507504d00c01940080d904200c200904a581c00b00c01d90341106c0b0f0888402d440d901030f00c01c0540700c44141400c050116400c4001c1c6140c200403a0320304441341d901c00c1c0d00f15040356035101c504142020120030300035032603046030300802c40722402c2d0200304d0f82001844100180c1f00020755a014219046008102c901742d445030100b00700700b101030804460380100c6003420751902e41c0654411549000749441c0720169085c00c404107504200400582e805543e2041003048a44028260b40001403024480c0d9250315083c0003c0d10030744041c00300c24591424208020400c554180071042d406500f102c95010340c91441404005183e030b4007401520002c0100b104401c520754110300520041d0303030b09007900601170f03030015085c2000b150000522000b202d070889041a0081e90a500182d080200d1600f461fa00642c95001c0c440c40e1120321a0803000c440d440e980380041c110a4202501c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 62926037 1250 62924787 62924801
    0x10e1b0c0a020d140a0b0702060c0a0e120118080d0605010c03020c0907021f0204090c030b01080c030402060d11190207050a0621050106020f0c04060f05040b0f030102041413 76
    0x10164101c0c901e0140181450032a07036010700e1140c11480380c040c0038402d0741450300041001c265080003445040c0081c040d010300c0340c04d407c101e6170400c4900d44480c00e0300241490000740e07800e83c003070107138803040309600303182036001c034080030702c01d801104485089003410341c440d8211504010496160503c0000c042d8001c01762130b00681c0d0301d5000740c00284056400c125031400c0062140c1d01391b0098520380b181114010070091039808050400580351400c1078201c000f01c41602004406152408190398601d17130f0010310a40d404000d1340328140d526500c0e4408200140540b410514806040940142c92144107401804004d90030b524034682003016030600300c0c2d0350100d501c9940d030443d135129000d07c941340c8900b80c0c1c40d0b1220140a0340b801a0140140040c0c00c980c401d3b032164005800400c01a8050841845081c07100101100c041c0a490b06020001000250520486100309e030364030088006503d40d000c20b1500e04000500031500c860340c403003503046060f07440240329100303550b5a20601d064107464403a0039 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 62927287 1250 62926037 62926057
    0x501050d0f020102010b04050c0403031b0f14100c0503040515040803130203010b030303042102011e0b1c0605150402130603020702010215041a0708070f0509040e010203010e1b 77
    0x1090216440d20141c40c640480141e0465488004221241c1c80b20f01403107004490003a0b90b40c0da100d14508000700f0048402c0320a2004a02d07050110000c0b45950400031000b542040c0e820b188515031182c45c0f45040400400e80045074108001c6103411074100020b544940c0c00744042d90481c0380c90b46080018407400315401402400c050011441201400c0c14a640040c13029000042004600c40020300d5501b044a0031140e6440e0307450300349020700d0700401c5407142c884a40000e21845200c58000016030a039001079014079690388a00c2c50040c4c0c0c2d0410b100301080c1c178500c0038810034036103400c1400141800f120912040c40081242c02524102442180d071203450b1a2400b004e01030501074210060350041d801030b8114401c0003030320400c10010f045154040c51192a0030740005ca02c264030a130b10100000c01d1542402100400c228078507030042404035510005241a681d02c4201e4400a0300500001c107403001c0640c030100010540d002d060100501600111040b00388008401c8040810303403140d0340c2c1603 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 62928537 1250 62927287 62927299
    0x3051006030b0d140109021201020705012412031e080f070c0b041b03081204120302090108060d020604080106080f0705040501030c0e0c070f11010f080702150915010f0f0801050105 79
    0x20f2030210302410b0215044801c050004520580c2c143c00244440741c048442c410f00da50700050600c2041400d1143d19180c031070f1003404010b06038000000f0040c0b02c4c0c1c10300c1501501c04074511400c082500c240001b0460700c05070300110705590303a0070100809503507086907020a8040c94101007034049004080d201109030340400b9550459581342c0e00c2c402e000440d07800c00800050703585408030006002401500f4043c50079008503070940340a051401c50b011841c103601040c03510400c552102139900130350440d030008080c0c500d04105403051001c68118440c0390300c410101d510302440032810500105006000c0300500007104c035002d03110001c100071194280320041c031001d0701c40b50400881d204e840000d0740c09001084000c1c14000c09840c0c0e40010030500b402183c583c3e0825030b01c85095030300141c940c050000e4a1900c11760910704148082c0d42c5201016026400e880703e40005494410308001207840a850108103242a5a541b0080900c16500e40a502c2c1c00522031800442d61010500c5414103c520060003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 62929787 1250 62928537 62928559
    0x4050c0603060a060e040225031404140603040f23070801060f060f0c021306050405090607050d090807120203030915060d060221101a090d02040c090e010603051006030b 74
    0x10a030b401188514029030001c0c4c003400f0038112a140714030071094010090b01e0070003001082c0c9c540141081109000300c04060b50610003441440d05a44191441e12829a10280e4940719424061095010014010b0000003585000310845082408025901c00c51204440305181c0341d0904900340d505a025104008007940410854a4400e0000d4841c1d41924100f4241c1e060346500402e80803082c68602e042e02e40d40302e420030055400c080c802c4030752080c400340144c1440e007000c0c94001d040348248000108120349034400c0c1760078041040b0445004a90001e0160317001425400302a40365001110207000301d010300c0b9412500031f0103481c0c40c0ca2007440014084410900f036a5a850300941195103e0700498018003076000310f02c076840c0b107803038082c0e00300c1c5c9400c1229034074240002130001c0e46031558800702c59090000d04541d40b0b4095a1040031541141c01055042110001300d860540e50340c02800e804004c0d03000081ea41d9015444140503521703400054020b41d803122419002d66140c0403500e6000142004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 62931037 1250 62929787 62929799
    0x206030f0601050f07060b10020f0c21010203010e0103120906170c0403050d020a1101140702040203061903140d08090a03030504030e030313080c0316030807050a021804050c0603060a 80
    0xe0495104805050941c100380900003850159040204100d071000d070303070f8401c45020f858007291742444000d10744010501401c04000c9503844500204049009100c003034a443d082c0c0b007200c040081c107651040021500c0350f96500c210508580284000ea4102a0646481c03800d28414800c04003910340070f88421125a02d6450800d00e221300042c442c42c04c10b901440013000040c1c0c05c0c00380300c21450065004000501a5041c00320700c54402c1e640781414000303502d6001d0300814200341510035942c0c0442c1d0040e182d5031403002103100c0c110018062086101101000b00401405000100f000c8039141c040360042c000000301034407001015505d0801541c45800f04c03030700092103038001641c000e2180c5032889038080003101091850704003500d07865240ca0541030034020501c0030006503080201c21801442c600b100c840c00c41894184c42d0102402c40135000030008113014003001440c620641c0a0110f0407001c91882e06907034640c6090301c04841d28000c1001c0c000c503d180c044c003034a0084100800301000c903842c4c84 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 62932287 1250 62931037 62931061
    0x611030301150201140403020a020a05040510060e0a0503030301080303041104150905040212010e150f07050a0f0e030a150507090303020c240c010204080f0307051c2706020d020604020603 82
    0x40010390456403545e0b00c0c9200c1c20b9003100f440340030740d1180c1c004114010480c4100018506160841d601a2345400b04010200c13162190100031902d0500f0701c504e0380300e400408503030b000c00547c0015405200000001a40f90000402148100c5c090060064040520310820007507640030400607684010300d0006110740f82c941c1d8045034200d03200030309040008240c1940c0368255618442c8045141e04442a401c100c030ba8108007441d4400f240203280015031400d0100508070380560368030f00c41049000902d2580480c09401d240510f040002d00701c0e5106401807070b20030350012010513910341d5181800302007900c4c01c0c00b90407207500b660740c590003902001c0c1c024018000340c1400307a10700c1110703980c8200d400c0b50044120001003038003008640025a032181031451043c54840f0180444010340e20801c41c0b24003103000420f10750406a80000e00c00c0448104c0a412100060704000980210320700c10929000d80078040d030076070111a004e4099810180001c0c03400d980301c0400b154040d40000041001130806241c1e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 62933537 1250 62932287 62932319
    0x2090904080904151725120510050f0a1107021005090f061c0501080a0804050103021e1c0507050a0804061104030b0702030301030203150103030522050423010611030301 74
    0x1a1000404191301d4050348030750b0020744e0003005100c401c0360101a003040103001004450344101815030841400303902d45020301100d4072542d10846501c401d481c0c20070906016200c2403040a03c005d110740d04082c040404803020690710030607954079100d19074244000761800d840071140c000f00310b400000750381e0700d00b40d59a0f0f100c0740007103a20a001d9410300c00141c1d40c0310040c0c45135030307451120101e6a002d0780560700c04655041e041188181e014104100000d6060000c40b002d584082ca00076132500071064030386c91b0894803100701405e4094042070000c182c02912032a0302101e288882c06120702d4641400a5620348112040100015220700c001004500150042c3d0001407841003c10318096503510b540700d4a500941e02d610058000000402c154941000f4030398074458040d041c0041c41d4074594000e03015204000b206250000281035412419040d190094001c04e4050014401110100000d5020046034400c102c4028030a0f4000301d66603210700c0e10f45d045240c60301c008500d10390800010646007001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 62934787 1250 62933537 62933539
    0xc0909030c01060f21050307080a02010204030c121b0f060c0c1a07050f0d051902070e0c1c0e0a08070501110f0a02010b090603060a090201021501060e030f01020909040809 75
    0x8000c440301e52003091041c64001c00c901c0c0b80341c140702414100c44240c842c800c101090403071001946810041100881114600c0d90b000c070280d9038600c12514240c0c0640141c1e0301c00341064440186c0041d80c0c25280f1041801507126504c1241c0300ca031140800c3c42e4070300c6107010380f411034034020740305208172401664036151160040308002040b9940383e0304c22814084000924003410004100d910421404010294402e44144003030240300c0754900c4020200d0081ea400c107101c02c10040992032180f4001e1015001400c010381102d03203249000c500e001c4040e400360110100c81080c61034254000903080c81055a04104100508035100c65074840d11541d410806061700c45540e01c640081c000080d21004000d04000304440d65101c410245001c0d084400c203241a5008002100030002243d03008a4215803014a10300300040c44242800101d240c1000748500a000340395000c000300321b0941040480c03007035550444c01c880f0205007503178140e400d0f8052000c071642c0150b07440b801305000810300c401810400300c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 62936037 1250 62934787 62934793
    0xf050f0a0e10030201110705060724050108030a111c0309080d0e01060315050411100c0209040803010e011a0a0f0e1008060a0501030e1009030302190e0307090e0c0909 73
    0x501c965450402440a9459504180d0a0b0b5010411560040030005107040b401000e8000f032840c15000c030b4003c0c82410001480000130b5503005042c10103102aa100b00c04203544100312540c0c69402955072644a5420703035002c141461140c0c1d209900005142c0840c8843c40210302d070751013075108103030040c081442e4225240e0806000c45604a00c0c50301c588140f604c484400426450319504000e444505030181040788503042004000114841c1ca0ac8001000002e540440406d0300e8414121050311340302400942c00402c00040c030003403103000e0f8013641c1642d0b5443d100301c2c116640d40003c14501c030510340d140c0002403001e00180001500502d5004100a4a4200609010a040006070050204444d070030003248100c428007006081605ea40c002520702800d00300440080406000d951340b0321248400b4800392202e15800c1014403c1e0143c40d12601009480d0b6442c000d400000381101c484001594002d206070b0b8000685034045000345240880718401401401e0303401c80030303c04506802401ca0190344 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 62937287 1250 62936037 62936039
    0x30e010b011d01110d0c0b010918030c1b0e010806010b0903100c031503050102120c03060a0504051b0705060703050a0504030509010c0f020307090f06290a0e1c0614010f050f0a 77
    0x4c00a001c04400d50351266241c9106c030780c491034420016541a08070510780c51030108c10041d005401445507000c0c94040c00c0034541c0311780901e080480000103005140da40c50000b100012074240c1a4803442c10b81c0c9424003592201d81e242d9074005181d0045420003035050f8011030904918000c030340d002d5610790001d4517000c00c8146900400d0101091240d10440742d50790300140001141a00c803201c181c1001604031051300d98205240041d2a07404140100391140369104041001d035001c810900901007161071035952541c4c0c0e83d00309aa00c400f01111028003085c1003200240c0002514403a00c2c0c070441d410303100c032414008160011500d07101c441500b142c51b202c50395003241c0540c0d420480f40c40208850000403845a058050940036158950300800240d810080b0a0b021140d490340041013034515001100e4a0381249141107400d18981c40c0003680000b4441500d20365003440c0701ba8401c0f400d01a100074400c1c40c071004600704000c4824800d00f5034441420b2414402840d14008102a0801c01070107001d4035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 62938537 1250 62937287 62937317
    0x717070519031e0201031406030303061302040909081b0601030b0f13061103010510050f04090c020a15061a0711040509010f020315030d0903170d0f02070302070501030e010b011d01 79
    0x1400e40420140420f4107a41d04a0b4110f40e80750042e00c0000c5402e800c000c0c101e007024400319540e4007002d000c01d48140c106042414148446505560080804c0c5a090110814a003046201c0741d1003125100111303843c00e50190040c004c0090f4290480b68800400d546a0f07443c41c502040c920b0f805084141400300c50046000411520300500040748241100c26560354981b104004a4042010006050020611061403c0185241514110745070b9490215066074030b80003c90070000d0041001700383c6844003807586400701c0d55520082c10b0302e0460300030250550b10460518490701860b0002000c9050030b001c01c6115045c107420564210061000226140d4540300f1020b040c1e0300211000b5991030000e00c0040310340d140804c6440d80042c180e0500205090454982d04030740f21030070401c60203540000a04008490159001c2d1052445c841e000310b4540320341d450300030340381c000c1c41c414540028146407007083c0243d8180301e0b0003504c9005842c3c01003010000c1c4000841421003211641c14440000719030014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 62939787 1250 62938537 62938553
    0x8090a15030b040b01020705010815041128031b11031c020319090f031d09010b090406060908150606160c060f0503070903080306240c071707051903 65
    0x80352299140821400d060350248412140510841030443d0f008150400407130740c0100742d440d041240100c03900410403100011034091f148103106041640c41c0050528000c03000304585004890459a9007131600820220803019201a078813045400d030207001e550741d002e50040d031500798802001f800340c070700305a01c1700d122010422440480c518050340010030000996046403140c40007400460041010701c200f030300d604e1405a40904003e003403100000440c0700100c010803820b07082c1c603001031061000b5a11090340b40c1481d04001d00e2640220f003040d00214080c2c1c020000d45055031017a8009000000711381b10411140c07080601241d0f04010200003105c11101400d0905074998000c002161609142200080201c1000300f0038904200090040c0000b04ae4060040300803241c01402c0107480303440340000649001c03200b150f081c0e41070b010480141c540080307101c00741544031804800e4800295444030030b0302c2452401d041040b065001610f080c4580d152407464944d05403503104500c504181c4968400d10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 62941037 1250 62939787 62939819
    0x80a11122a0607090b0c0f03030a0e0c09040206030705130504060306020406090b280e0a0f08070b040e0106030207030507060e03030a06050612070807030207020d0804050102070e0702060408090a 85
    0x8545550401151150003110054001c40141075004141919202e54020312050080c001c54400351030000d00714011030301c10048070728940175240a40780d490a00a0f00c000041c0100200d650550056101c8140c0394038000000d544295009864a850b43c1e9440c0000c1b5415401020059010021901c001c1803541b034912895010b103101b118016915400c010014006441d19032020b18100b6041001162015442c92800305460340c0d01240b00310600718020a4a080805050868001400020010340c201000550318201e401d0382c815581d0a54131388449026070320079400350480500c100c1c0010440c1900c40d0b402081214040d107000c60070580d0300e0f51808240c90078507006584a61020090001900d280e2207905d0041a007211210701c0d00f090040b040000560091045c018424001c0000b42024040d404030b80c21594001d11120501c0c1c131030300d800d103102e800034064030380144600c500200300042544a0306001d070b034481d001030903180d40e03aa40d00b52059000d980b10f01d821144050f000a00c03460307180581c007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 62942287 1250 62941037 62941057
    0x15060f04110417060f040812070309080c010f0b0f0f09040311030f04080601051c030305040602040f0b0d0e0309010c0f0f0c08100e03130e0c0f030f070809060103080a1112 75
    0x20002e40140c030078614060b8090704411a1801c20406c1c4030006040c41c0c229010120500d919030919036034a80194000d08080201038901d001c006510b05120303a040d0300403050f11042c98010018146d020040c4244031660400b4185c010b19450f200c403c81e850403e004980c031610a00e0304118007000f80201c141540c0240d441101c14040106003845103050034410b10340034150540c0d005080c42c034041580b0b446518000c901800789942c4101203021300025404803406081c03281d00c1c0c10300c015a42d60446045130700064140e03640d41d2138103090342c0c1000004402c9410140e0160346603862004152181100c0c03422100040360400ba4080d055400602c65a442000034080c11015004690340c00216506844409440100b6508200070000041e076030007034402c3c284c4500000c071900c1981c0c1e104002075684204001c1c6081c80d40f02104210103500d03007440c22886074a4603a03c2e0a10ba407214102955a15028000140a00e5050214011203440359400d5141c1c101004101d544018000c0355940d00c0343d01c00c51101d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 62943537 1250 62942287 62942309
    0x2040f0b1903120212030a0c091a0a021006030804030b0901020706050f070809120a050d020d021813090503030106050702030102071a01080d05040f210516051215060f041104 76
    0x8000b03015140341d00c00b07078010b83e60000d81051180744038034128910000b4581c124841e529030317013501a6132080116202800c0a043d071014500304201855601d07410007034182c0010702c07450010000b401101c0c003809040b00e44c807a4130740b0f081c02d0031591684400c100051180c0d03090342d0f082c40120040741e480d005580c021100100b0040a9003005d820080028000510840455011520030007120301040e04407032003240079181c125150748844ac1c95101030b1048400b5400f602d800444d100d60300c440c0c0000010b214503004c41c0d03907824042e400c40b0003005176543e0b018082c0c41d6800500040090600400041c040d07244001c00040c604003042e6900d5882d902002030718017515200c50018003d490080246a40c04030050030040d003031926005280e40d480c0818041c6030404d020014900c40c847c200d0784000468180c1c0041921420a1581d1030001880d8861040510030200c95050868107840450321605100000810a0440c3ea4074001d02001080401c40c4541050313850442c4901c401401d000340000c0c01c43c01c0c4036 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 62944787 1250 62943537 62943539
    0x10050a050609010602150115050c160801061a040909060b06070501050402040509010b150a050c0d080402030114040807020f060d060306020c06010e060306010905090102090901030f060e0c0d02040f0b19 88
    0x500c005610b050304114199030000101d13248203001c80c040e081c1107819a60708480c94030b0303503c0811901c178010702c1c64100c042e2290308145080c50520000050507a18103000070040035075a4115690002c2e20904a140c45807402c000a003c0c19141d5000340c20414001d07440030500740c1c10007021407400d9004a0003030300c0c56550b845c20b200440c60180500c6400c019808021b01500c290540010341c12440c29101c4211542d00040c074003501030164043d41c400d51514030954003000034040340a00104401c0318101c0c441c1d40703041a02d401d41e0b100b8489440c080c0e504071038100d003080066828800740500e606115a40104184040c0c0300c2c6a459000740c9000d1880f482c1c0250721015810102d525102c0c042c3c00c0f00d080030900c1803c100b05a280000c0c15411a580040b001c292622002600f500901c2400700050300070380e482c030020061241010380c2c00d10041c49080d0030848100b4840103180c880c03001d000c01c0380c2e01c42a40b210350400b52500390030400c04110b84203400540d10041c0800150f61301d501902942003220b107080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 62946037 1250 62944787 62944789
    0x506010201140c0a08041a0711070b030f0a0b040e011b120203060105030c0304060605040c05030601120b030c060901091e0f140d03030c020c09010801050114040b030a110310050a0506 80
    0x1c80b440034202a400d01c0c143e0a0001410b0030030f00810402d28104180e6074005018031000c2d104007410420f250802244508081000508102ea9190303110b41500c2400f000003000d00c210307001c60740b05800040c07070b80301c06441d0250143c3c041d1055280780d80d40651110003406400b1001c0c4542d400454108038100032407400070380060100303034011030881a600d105204100040e44c011003100e0b4004d440b4020660f0ba99a6032a003a4014038441d00b000f9005442d102104840a401c00000e500900b401d0b210440e0710840d082170a0259031014400c0354040c0c0241d46c0f074072030078200b40f409400c0000c07050500c1303600b5589941040400c982001032500030440f031540b08001608121895102500d02d061003c0340d107084500114412001207070004081598682400d0b10300ca1081c0090024440c2c018001c07041942c0da40f4003c0d020388401e006000c0c0b0702c00000c41c0c0c08003a01c0c0510070790b40c14030009005011035500716103d12440c072882c003d00c5038040c000c808800c60f508403548100343c1718000d04d03640000e05040001c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 62947287 1250 62946037 62946041
    0x706030b0109080114040303020702010c05011a0f030105070e092d01060e01050408060c030a09080c1b030106030c03021002032203031b0f020d02010201061a030f070c080301090c0201021902010506010201 89
    0x340c0300c1052030345045e1001c10b000c441e4510195220303400d82400743c0e0340c540b00d200407908984002405426940ba148030845410804000c125000408480f506000384802003018202d800640300000801e54130106151241012008182d1020203801c2042a000c3c400b250f08211007010403110002600c044014445660002e0090780f490760700307183c110b00382810580700d82d5489001400d98150b0000100000e03c01c010941c12031481c1c0c41c0d10140700d50b01e54030701c4d423000d580d04e010700c00c4016000340181c0c2040302103080500c03820040340d401030f80042c511440d64091241c804050810a0110f00040100c400211240e9204807071071600c201d428130031145107040080c40035441c40c49e100142c0c508e2001d0800400d00c0502141032554040754228402070742071006070300500c4d456110020642c203050100d07000c541c103040654400d0220000322002035403034100c1194125176881004000d151305100501910401c0e512201c0c3d80703011400010300d04401c902e20000882c440c081c07140d0060303454800700001940d081c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 62948537 1250 62947287 62947289
    0x4020c010905160b031506070213020711060f09010509030c0307060f090608060603070e0429120303070f1b051204081e0712060b0604030b180a0213090f02030706030b0109 75
    0x2214008840d041c1040c22130280310141c00b60802c001d20145031400c40d51102c040380d40c000c0e4020b08413005411103a9400000c0e40242c1001c0e14242c51404c081c4680782001001c0f1507903441c101034a5445c040811005442c90380007000c0031500340c8946144141191001c20545c00505903903154240449444480240118201e80020301003101c484d0620078591281010b0fa90451170b036003000007607003903540301240050000352440076600c008828803400756070340c0b01030141000303d09403a25900724961800440c0c2c2c81c401916484d0020b0380d40c000c9120410700c6445450000c1c11642c0c00340d100030320141c440e58981401c00e10081400300002404002c89042005038080d100c8500025010f589811360525840e212144603400001500c00141005c1010903404000c4a4a00401e0180c41e25100d04280414070411500c0c0d11110307656801c02c10078610300080300e0304a01c0d030081026141c40d080d001c00101030808003e0481c0c0a1300301300c10721401645c0922064001d00b9036940c0018039510803500040c9a0005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 62949643 1106 62948537 62948563
    0x312010e010510090503030304240204030b07090503240a0b0316030302070605250804051e0118060c060b1518040c050c030d0b010e04020c010905 64
    0x503032214906840094075440804208048150782c1a5841d020351603041e4011301c000380c002403000c074ac040088191a040d00e02e078140a10180b0701640c00176081152800e04500c204180e03241e004034501c1c0101011002401d4559461030440d07600b800c2d0301e02d0800b91801c464002042c803101604a907083d100040c0489070b0511048009080020740c5001c00c4005008460000030314900c14000d5800d441c00d0f11003210303c0f96000c1102da0764030f041c881d04100d400d1401031100050325512850000700120350075102000040000d00010007400c840901600050a07043c41808040ea000400e8080705a100310002905818034000401e03107610740c10010146040082c55001c00c010f07070304400300c00000599081c01007850744141a00c45010700c00180d50b02da0300600c4440000e0f103664000145520381070601e8286440e1220109060764000411f0030440c3c7e45444100041003403c210404d21200 = true := by decide +kernel

theorem cover : BRFrame.Cov 62769787 62949643 := by
  have h0 := BRFrame.cov_init 62769787
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62769787 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 62769787 ≤ n) (h2 : n < 62949643) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
