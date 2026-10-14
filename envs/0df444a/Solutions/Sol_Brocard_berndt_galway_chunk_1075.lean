-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1075
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:07:36.445399+00:00
-- url     : https://prove2.me/submissions/63db7822-0d32-4337-988d-a175f169a7b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 193165467 ≤ n < 193345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 193166717 1250 193165467 193165471
    0xe0907060507030e040509330403050a050c0a030c03030c0203030702070b13030203010504300f0c021c050109110109030809040f06030b0903070b0f04080a1d03031206030d0f080a05 79
    0x401c004070036240c03144c1a81d4074020f903400f410801c001011180d00307400c41a50080341039040101600b071000e0b0751030b0511480c0c50106a1154240c18426125010784409039101d10401007002c1e140d000300716607a0100b580042c04501800e00994040000a061900680c0d0380d110560340350000d070740300c01c104000080d00c001c01040001c0070420080c10f01a643e5012034251003041d582113502111030043c0c196011640712080b06008111490b0070b80030390350340314081d04c1e14541c92221000c0022520074001503448403882000395003105032107800186101e09100f07000f030036980c0d03040340c1000245003000701d10744c0304118410599800caa151841c000c1703001d040000505485040c031120036100c2c080007020030740f000c01d03552041d07981c507002d0360b500c84e800c0c588070b03030075120061a0b9200d850190041c0004260594140c1d0750303c075207a00b0722021032a4203844400781e6040044403664984000900c41c482c4141401c03456006580550441e0b004070711960080e11000410100b80000824001c0014058200f58100c1c030f03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 193167967 1250 193166717 193166723
    0x501050d14030c030a1d0105030408070b040606030b070e010e090c04050402031b0c030703031b0c0609020a030b130b0c0309061906050301090303023109020705030c10150e0907060507 80
    0x30703290011550f07a59045402019100c0080f407410110f4045404d504807400b11a0301e42440d0651552030207035540c00312801201005041c0c0040c80300007404000c41d9502030800303075030410030140f40d52404610090459559000c81030000701c00700131149590030705541c1c040c020540c401ca21411309082c10140002504000c01d420340240f503074404008820001801805007000b0fa802850340c643c09410081c0c151010b420300e500c0341d00740441c034000d00c2d690b10034a00a0000d80c40303403020441e036001c0d0001510024407604054200000c060500c002074403201403441d0410300c81c40c030303000644e501e00b0b260b207241d800300300d6003400d030754021000040da50341c0303581c416107206081c2c000d00142040d08e94006c01d08540141904501183e0300050b010010240080d81031510f03001c0823201000410028070f8406104460320030301500c5600819003404121040c01910209052a02143c01203541e49040300c010b40000b0300d0309141043c604c800410b040800c1d5010398451644600207005c0c25150103400c0b00c069200580c00c3d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 193169217 1250 193167967 193167973
    0x10608060f0303091810060e03030405040906020c070902030603010c02010b0d0b071107090c08060429010c0f060b040606051213111905090105060702031c0c14150a0501050d14 77
    0x200d500b699810064400d038004005e4007040c1c0b4540310030500d0904945810010600a2584d190380b030a41c1d0000494090340c4003514041405039003850803001038001c2c2c4403581510300411078041b8005c13460ba07014600c5513500310024009407000210581c203c8030741241305500040048809004150002d2196800c500e031890a4900444d40300700e200e00304034690b045090316544032030311400301030380c0f00481d1500000308407805c02c220300340005603000503440b024071a60310440305116400c2c50303070040c0000005190401380f501c107004190302d4294010005003003070074401d629062000c100036100700280c17040c180000c5003120258495600c010f210743e010308800c07150398081030080302c2c254a40c02c2480e1101038540c02c0301c40881b82800204004800305811241c040e000c144022005a43c000421a1140b1041f4504c40021300812000306c1d00000902d03400b6020954000c0040c0a0003000503a0948020346400490025103500605605030b510a20031540c0c00101c4c40d203014041480c410241084400f08800c03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 193170467 1250 193169217 193169227
    0x21b0a1a0c030a020a0201031a180711010606030b030609030301120b060a0302060c0a03091a0d0203060d0204091a06090f010b0c010f0c030c0e040615050d02040b0d0b010e030105010608060f0303 85
    0x1002d02d1644031a01840050700100e0001c400c42d6014002d8003104425016808a06c106120200e18020a8440000710042c40c000210780302078020301c400c99038a00d081c1d00900640b82c480d400500a00020329400c0d000348100f0300000c00a440200c140d038165070291400011810180d11007280405c4050a0264880320115000005a5545005000c0c0e15040c20103880a0045410007400c8012aa800011313190801c0d0a04080d180800d400c451010200000040c2c8a4036500046580b180406400039003091410b64105e060044031841c090681558003803041c0c80e03507240e02c14807200340c100352800c14601c132071800140501a2030300050480440280d000241a5451007100d500352100741003040c010940c2c030b031038545145922403000d080c444015035051050b00d18080d030346c4004d58a203090800c10058041815200400190111002800040c40c045e880b62402d11451004102c0001c1c0c160124011100220f07950406024150403200c0c0c81c3c480c940c8680d100c000b4040c000801d43c91140e45400304002c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 193171717 1250 193170467 193170487
    0x215012106180b25021c02150a1401060509011e0c0f1103100b061213080c031305030c0306150118170f0f121c021801021b0a1a 56
    0xc80b040030501480504101c1c0c2419900c040c910410134041c50480745400c1c4152041c3c41e00003a00f02c203c07039440005892080d484010132402c0400c1c00255511030b51888050140d9000d0756040b84000780f841c501d48081c035903038600050398688651051913000c100081d100024407041c0c22050b01305140c45082c002803154060355119401c0184502c121030080203e40401c8050400f04903210452800c014100b01240c0e0480000312540180c640940d101003410000038042601e10340460092548100455201d002c0e01c40030545031f4004004c10340c44540081c00001d12454000307080c506000024016001d240c60b91304440c0d42815800070710605001c1420038003840d03544682c00c12001814540c0d090b0541c014003001031801c2040901c107000b1564445000303a030307003103801058900d04040d410340d91650f0b402c002c45154a0510440f001c8034021403000c10811074204200c01ca8141155099081d40c441c01d214101d880c1c441c501c078080305a00700032845c10903c2030011500d031040700c0c2402207540354108400d45e5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 193172967 1250 193171717 193171751
    0x61908030705010c020d0306050d0213021207090519030206073002011b18140f040203180d0306270204090905100b040c0e011224060215012106 63
    0xc8007110984e40d52002200080d81c1440320105900342ca103014401a49004000b407800031186201900c240303032030001c401c0028601e50440d25101d4100351000020301c1c010724081d04041003849018001c5000203c2940079074065820314050f6a40100650708101107a2034001c3c8a41d4482d50542c0002d2038080801c0e10301c0398200c14024640300903400450304500403043c1c0605d02d503003a5850418050070000c1d00240c080c3c59210030b4180c1c2c6424504008000181c0002091404101c0c6030b036130898400018071107105030701e040c0c402200481400303c900c072410061080b02200d5042c4039851501106583c0d143d21000c001c0001002e0198100016040a444800c0038040b1a41d8030b600311050390100c02c0e550384041141c0103000b1216022201084a0884e100c00540811440c108007410412040c0074020765500713960080e003030b20141d91207101907090610300911185909009401c050702c24001074003000041d150300c3e141079480720448604000008035407000041c001640c1110065150780c40036030190321503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 193174217 1250 193172967 193172977
    0x8060a0903031b02070e0a15030b06010305072a050f0105011d0108160603180c0306020307171501050903150702010204030201030b040506030c090606070f051b010c0b06190803 77
    0x10000410904501e40681261103221011001810380d0400c101c1454000c103501040741c088071003180d2940e603982040c10081c07000c296071074101c10500d1004000d029080e040e0908c118400c2c0ca0070009903c0305603096925015000c41c80d038040005001c1510001080c205641110707105104035440524080443c600f99070098016805445070380c4031460b080340300301c0c0a45004040720005081d06240d0751155082c8901ca501034a03080c1502e0700c80658190355010070b4800d1143c0c001c0d07000c40d0115224a0f040021b54000d44030280000c0b500ca82070214041c00303240407802208003049090511003410015180381c4c01c2450700560600410091201010b0442e8003188a60029800140d4603400c510000d07048400405140c0c0c082c91030041080019100001c4000740c80c030040b00c810f01103a44410004000d881080c100501c6900705400900c100880002c0d1044039a5400303014003030321558a001180c0004010001600c44585840031400360304241e44902c89100f40b481422012540b0381d00e000b4916409 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 193175467 1250 193174217 193174231
    0x80102031305010b091308250c0f0b091f0c080a021f09030f0c06060506070f020405060609100c0203031204030c0b09031c0b1f0c05010c0c0209041b0806 67
    0x11501c5118200701c030a100d110204001207806240f03d0400382d2075024084c0a0600c014421080000d034480c0412207401a024001291788034040004035501d00340200001511a0381c0100060040102d9112400029103200c030b00081e1281d0070103400d501c041d5400c50903400c018018020401180750100e0301503402440c500c0d0783c0d60020812010303480e82403403584100c1345500b0302040c5440c1401d400644d1020f1015030101307851400c3c003c60201c0e420003000a102d55800650703c01e00000d2040b0030801b090035581c001d82d000721401c00039640c4500c20301506120780b00034242c1c01001049000d100d107000f800d054a036240040c04890400046207160840c19400b0758058021030400860503041003d101300140d80f00304040c018500384400980039176040b52411050a4505071180100519034a0b002c1303c000100a404510303503018004144c003d80104060034082d5455420714501807840c5020301ca60043d5154060080000c80da219128000580b41d04e4400c13000741141d0304000100210300300115801030803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 193176717 1250 193175467 193175491
    0x20f03090f1011030708091c02010b0901080d0206011e050405010603020301050415050114090d060501060806131506111c081509060a09050414010207051e161502010608010203 77
    0x11006250070b18081100a856003018106600341e46144001e00c243ca0b000411424009025111803c9042c00e1071010840c4511024903040252034056054101821440702a07480c0c841590322600c0c3c1c91f8039407202070305240c050790001004100c103071075102e9455416603603410007207543d80e125400241580c0d000e900510000c2c1c0c012005000d5403800c0c0c414140000e40341048132181c030340b0344000600110180f038810a6991400324000c0d4054480c242c6800c54076a00c00740801043d030711400c2c00f414514090364018010f0b0740c0781c040c11002d000b041c070507110341c900e002d8840c0c0c01c607505e0a5000c584001900f00c3c484070a000d114032076180000b600b000c2c088031100300e844040882c82c186103042c1c0804010003060707124400c031106116141d11403a10080030b0310785203039000ca0f0b01d1307481d81011000398011409005566200040c2c29090140c0072402c1c64250001d9400064400016840590f580900d40e45408401c0c8503048200100604d043e03803c00030040e01d00020846c2036031110740c5d0f07003280c100712030111841c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 193177967 1250 193176717 193176733
    0x7060905040b100f020a050106121a100509060a0b0c010504030e06070201090905060d050a0c0f0f061b15021201050a080d0c06050709030c180f06080a0b0406020f0309 73
    0x66040019980980015a41007054152660000700050802010303002480f065418880b04d05200748101280303036421800900060790341d02072910680e9000321080d204c11455426407403000031400d545a0140d03d204001140c06800c00d000c00110340c102030033f9540d10603040d40700024507580000c00b0703003d001d00901c0000780929003814084e200a0803801035031b1144008102480c0141e03003043c1d9140503a0f0f450440002d20381c1c2d4000107c0d10205504e44040d00700d100c2d41140d4010041c10303c02c00401c0d0303440500040388080e541d03d01c0036015a091f0051201181500c07200e00c40b101c1e034014819862502a01d0700c07400481045e07445204984c41615580d42c858004c10041c0310504195402c44001c100380130061540484150300280303140340c110720081c0708030f807940085521107226110f10303c00707103420044003642070350764114a201c8280c2c0449a280900c0c2098051800340589100704c80890313400c0c0307000e03144c960728558400c4110907005100300c0342640e0a201580704880307901c0c0a18401c1c400036000344540 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 193179217 1250 193177967 193177979
    0x30b010e06040b03030903072319080d020d0e06070f080310050114040503120f0f03070f080a0903020304090e030409020a11150417031312050409060b0c03070b0c040b0c07 75
    0x1481241c00820b01030ba104018030310311501d0000e0088c007200c1102e1086010900d221200264550b20041100d9220030021540c400144c480018241119190000c4403200d2444550584c3c482d48201203d6000c03078180702c00c001c00d83c244a030003440224031400c40700e140c4128a540c0c1c1c1500f600b080c0e441c0041e42d84211401c2c0420b58000500701c403007030341c45625141850300e03040000340d85481d00203000d0000c81020802c9a001c1d044001910071501c1c19040840d200e00d01074000070300300844030740325900145a40003c20185400e03827160000d05505036010310710b02810701c030800001e80300c042c00c4409544810080000c0d658050702c00f80c0f030005103d6880090300741601c004c06141c40301d41d5220042d450b101c607060100094011810f01c45400a03600c6841e1607a803200301d80502100c5200000d0400d0344d02d5054103841d0740d4441c0c000d00030344d43d4461b82045040e450780c0f1102c05e54001e030364018000d40d10407c008030100b849200407690012025014501d442e854004440aa400c00c8a20844582c00f5000510030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 193180467 1250 193179217 193179221
    0x50a0b010e010306030c2106020c100b04020c0a03030e030706051008060f070e0d1703040b0109150501020303060d1103030406020319030b0d110a05040908030a06060302090901150504030b010e0604 86
    0x2007402403800f40003807801c2d921240c16200f1288a02d86030401071104c0007083e110407883c003405140d001740382151503032401e80e805074498003a0103030901180d14100e52181980751601c241c90382c01c9400001000d000d0402e0342e041c4c004100ca000c1083d0507102c24004540002c0c02801000c0c407035020305134103116a51926118500e4510301074460041200c0075010040d4550344600d4900c507841089800c01700703840071030904030442164201c0c40d15401800004000034005020140c504031010141c04100004540c1c003103503440780e441d0007580d005800400c04181d0030b20f0210100c1c4001790140c060803a03181da03808000791842d072042d802000960000315a0442c1403241448650020340d6030b040500c10704041000240c102030425400610351034119050a01c191113445d2464040e01000d03008000c590068141340d801c0d501b040740c01c0741c42141092400300e0868400c1c020345004600c0a800311540e039003003000a1401c4035002c140c500401005010001c040b036030010415000303001084090f5800c0c1000000c0c001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 193181717 1250 193180467 193180487
    0xa0b030d120e0c0d080313120e0a05010e03070303050f190c0606080c0609040f0e0105010803070c0b090a120f050d0305040b091203150a080706030507080a1b0c15050a0b01 75
    0x454008501120720707615184c01401806605c01701e500d035680d64001010403100c55083d40608010319540c0c0b030121903034000520010461003160010700c0d00d03694000440d0032407583c0041d250913404c00c04007080041c2c0184d0141910300c06054031141041e20848400c034080b420b01e01d00c1c5000503c81c05150090001078413510300984a0040034200204800010482500c0341d03050081c09aa91951501c68400003684480403410108000340304d00d580d991141076407038002d040300740d8001414000000c0c01c13030b480b40220b80b0710300c402619146405260505160140d040710f00705a40c0801d5400b2a04000ba805025800301541e164500141d60305250134990340c0440700500e11b190680c0040c0c60301d640088054190395000350b1000040e65040742242c00301d000c0803d0391740900d104d07116101000c6001905504210711903000756031401115941c2c02680410348403800110101d1001c0382d0006451544615104490305010b109a03800c2800e081c020541111070031512480e103da503c548a0310b031580e0140b02d00e9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 193182967 1250 193181717 193181741
    0xb0f0912030406020a02090c0c010501140a0605030603071505161b0509040f06020903070f240804030912020105072a1d01170718020a021219080a0b030d12 68
    0xd828607043c80e02c0655500c101c100044c1c0306801100001d040501440225580c4c41c010a0080c41079503525052041c00c08021a0030794404e0b2540b20011600d64400c40980e840382500600802110f803800070a82c420f03484890150f4100700041161440d1291030010110a992080720944482c400b007960402c00742006400c0680300c2c482100074800030a6440400640c0d098121b80010707a107600c5040045d01d0b0412a41c40b04480e002c0c00400010000049102a0402400c1340f00400440d01091002c039001a01264020003048115105100030700886a2443c2d003d0b00c18101145042140e85802d44940b0135800701e42045604040e055510b9500c40c01500000c0591080c2c044044020041c0082d452205000d654501c6036000100442440200001b000602944407040c1040c10744401b0100a54004513090340036129400504160145000c11505400c4600304092130301e801c091001c4419040c081d001a0805403106580301140c1e8042c080061410b07011340754440c8540701d400c1070310207442a0400d02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 193184217 1250 193182967 193182973
    0x304080d0804050a0b09030918040209070e060403030302030a0f020f0c0d090b0d110d090503220b070308070903060c05040905060603130f3017101401090b0f0912 71
    0x400009600000c800c0144d50b07011040210310740c1c850094502d14050301b081607a000b85401e0200c00c6007507a40710a50701503402034070042c0240d55031000c2074814052901c1c0843d00003900f0881000802c0c800d81c05560002d0207594041010700d050417180c0103a821000e01c035000c40c4000241d03600448030401507074188130594100040d51620708100d0342d0190007481182000141ca59554104500700c4c13104881d520340060004101502003400c11640d030360008d03103001021030103036812210300b8079030490000704070b52100520ba0301c4d1964517039040703c600c0c034003404110610032141400b00008060f80250311401507280c0e5425161842c1402400c1514400742606018402c1003050044d01d00b00c80147e908504e800241783c0050581c1da180556106502141800c1140e07804000c2124465480b11040d0380d448032a51214600051021490162507060707540c020a042442000c0040d030f02c00311540c0c03520040504120620300c0d5203080d0400305a20010001e40d030480001000000340c9070443e06141842040001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 193185467 1250 193184217 193184221
    0x1e06020615060301091802060a05090306010e090604032006071d0909211e0703030609020309070311030717070e010609030f03080a1107030914031504021302040b0c0304080d08 77
    0x30070b00c14481802043c02d21510341018000300c2d41ca09081054440d40a0140c940c0c8003c0904020b145401242c030f61840703809108000200c8112007030b06117006003554005400c0d50f85807035030b0a881031200e0609105108031034005180046506100c510311a100f00c0e00c6144100b103091301c407100e00107038081c0350a124441c50018445020f038001402c2c0c106103140c0a800e4259000004410030a018000251709410350404101e000000087c02500e0305510a440500c046a11556084164082100c0101e816071003044200b010640e088407540d00c21001a0a0747c502c652100c40c90303610b80e42606840d06030b41d88020010801c000380c0001d80d5004001600c1c2c903070709503400c5a45040814084880103020402040082410a54290700040d80da1040140da80c1d580c1c4c0d000c0c80d014003240680c1c820780c11b034110200c5225415007804140041100421941c3c0b44440d99503a08001140c80b20742d8100244540c24000802c44903840d000800d0080301401c010740d2502d190104951804a040030801d08024080c81 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 193186717 1250 193185467 193185469
    0x906020316030918020d061401230408010f0515031615030f18061103010b0a080a09020a032a060914040e060c071109040209041b1e06020615 62
    0x94070920818002a01d540d0a501d0030102c85104440d04200403548018860f181c000300d41d5030040c035182c0c4e4080028080d155903207488480c50f03074501c0041404a502821204030543c03555080c0868104080c910a04064842c0c2e40745003103403c9540c0309003e0342d69400c10310016425050340d40141d03c0d811802070102848001e10709040c5d4103944924240451504685034000c1d0180c0c10510581e19208020440e08003103807110801c1001c91101582e00d1450f0099220f00e40b118002181c0c103a0f4000d42e0f40c1840c105403031030700312542c0d04010003511500e5034411400d801650350300340d010005d502a03141442c3c118028117200c88113080030f034110141c40c417090200308001500b010391141120070645030940c3d11b0720341102040140c41d085108423100e005c0c1004100f20790700b141000c0c1c018a4010240c0e03505032030b0f201050000f14001a10b011b54403e02d46000600054450b15221310010658518019042d540d502c80955040485024041411036403405001d0540d0412030240e0120024064900c0d08900300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 193187967 1250 193186717 193186723
    0x4090305070201120e0a0f03031410060c03120f050915150d02030c0d0c140d0209010b0a2d0806090601090302060d021b010b040b0d0506060918150603010c090602 71
    0xc4000f4180420841d2142001070280d0200245040200a13504004101d141060b50b50041a0040703011901e07011007400603c00307040403031780308a0307562a41303400142c00e00c0826118007001e41401c0342002248001c0c4040160a80508400c40d00094404101400e2100405003416521f046002240c014802000669081548600360a0700181c8203c0c1020700c1a00100e0306003c04a40071a403c900c3c545031b51010010b41d0b8007105c00322850082125440c080003800c00110850548003e5441007070440144001480030006100b402050708004135000c41103401e44088000043c11344e040101019144400e2603003040050b684018200c454180303500e030000c0060000c898501001c6c1c0189000f00c1c0c1d140351041c10ba8111550700d0000c6d2080c2c0c81d485190201036020f000f003072078500d02171420300364494410f041a0340201c40141c0d025028061303550b6004140603644000a00e890381c00c20381c50305c043c011507800b8064802d8100c00d10015504518101e014035003034445001d4060700304840400c0804c0602d03404 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 193189217 1250 193187967 193187977
    0x150b071a151c08030f010306240e090307050709020a0206060405010b0a030c0e060c0f0c030d02190804030605010315110a050f0d06050a0b0310150f03180510140604090305 75
    0x446200001060a203003540800c2c81d62500140381d003400009101c040c080c111800d504a0307124800610074440d01c9641d500421102c007c7c02c10340e61025600c01d106141e503804031960b02410000c21241002410f0b120340e0701d041302982c44608599800178030660190750500c08140e00101c1914181f005524205080c0114880d450501c02056620250f092200d4410703010000d001000610458036035038810106902c070401c006080d0005e116032002c0c00b0060030081151401c030000754001c0e040d046514500079050f18070450741142c051804200c00300c000333100ca12455010318011003084d848000200101011500c170f071483c00762111018494011113650100403610f40b003610403c880d8680d20203a000300090601a001503600071a00340c80410040d0050002c0c511584000d48041c040075940c0c000a80440c2840c42440c0000b03503d02d49564025000340c000400145010049408402d1652100e80c1002000c2014004190b2070314800340700f1010035405141c001d070003240c0800080744c1c9594058a54820 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 193190467 1250 193189217 193189219
    0x406060b030402011b0213020c030405130902030c09190501060e100e09130303090b09030304050d09050a0501050307020f0601060206060f0a0b07020114040801140612010c09090f150b071a15 83
    0x1420f00c00000c5413682d80e41c0d107064800e07c0e8425500d444502c188640c507508103004040c051420040c1c41d00a54256000d40c0342156000740280142820480c10300c514044010b010128090200f0700f00c442100d010721450b4020107176540d600b0301a100840802150311003a03491401042812144203d05030f80e04603185411401c82030766139400c0c6c13100d8070341600a40318066020b400071281c5410810b641c01d021009501c240d01c203006680d644400400c6c141c8081c0041d000301a00140c41c0c4030b0034041035009170000c507000310880c0125911000c114248502c0c14070240c00100050b08100c05004443c04d100c01c060078140c10448603800b802c0d040c141000e0082c0034041000c3d0410140821882c40c2081031350848001d0001c0707100910100908000c0103803207031000d4400c80e001d00e08110141c90510410312413103040d401c99a075034154051414000001601143c40d03c205a80c5d903c00c4000e08880c08140800c00901021001c15280c2d040c84c10401400c941e8007240342048503503181080501c1d01e00014005403510 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 193191717 1250 193190467 193190507
    0x8010b0c01091403070501062403021e0705010b030606040c2f0a050a0b0a050106020a0b091e060108010f020a08010603110d060611061503121e0a080406060b03040201 73
    0x2169404035805040320000103070903d50240d00518071a9808001040d40030302541c024000070b40d4a1001c0d107407507241c2201c0312540390800d0191918651190300202401e096500034250340d521840d0340c1c00c5260707119000c1140d081c6c0d545c4881002504050040c60fa010b4421507082017210b20850380a8500071000307941030700410f0000031821510340502058158805140201d41c45400c0b9417034919510080c0610030740c3c850030248005806a89140500c40c186d42d002d40c06003a0f101900d80e40c0d1184a00081c200780700b03070b00690303450307121340c403108030700345400201c0c590007007105501d06807410b400c440e00014165006801002105002500039089604654140c600000e00081038850100940110001d01c0e2030642410340018641c0e45c4420740d42c0c14680342400761607640c0c85035201d001d0f14007220008150107420810042003070b40081c4d80540002c00030b004450018904d00111280c2036800303981e071600450712060600062045a101c1c1502800409905602d5401c241e00007a03c841e083d00c060300d540308 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 193192967 1250 193191717 193191727
    0x15140901090603090c080d081503190b0601123209060f0a020706050703091209060207140f0d140f06150402030705120403030b0118030f080a0207080a06050703061508010b 75
    0x143c5e558a00000d142c60420358642c0306000f1001051070704155610303010300b510f80f180c00c41e143c600810304071440260201098081c082c1660b54062004000303000707034103002c00c075502041c15a8090045e03c48094030310f072180600c0440a1140c01c40d01c0041c9c00340d4142030071548200203031804002109600001e10042c540d0f4290381d56254000a0710880e100200b006040105000100d50581c002841d01440382c55508446071f1200c4d000c5600f0340d820320540c001030348245420032174035242c113030a000d84081c090001031201d80d4400100e119001c2e2420100e410220200c14644411001e001340306c032a0440350003912041c1488002d01d56180c18450b82c00740b01b940d000020800703890140c0c044903044e6040b40c0c505a828a018140a40100b83c0255068042820076a00c0e00c801090a110070050f254043c1d40c081002c3c403a81c45040080e0045040c40040d80700721180481c2e444410040403181030710400c40880c80d4604020014199800b40d44003c00740940c181c4000c0b82e1942000a1906480034105103507121 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 193194217 1250 193192967 193192973
    0x603050c0c010f140a0911040b040240061e030e0a11030708070501050f07060b0612090c06250501110a020f0c01020705180402010e040203011514090109060309 70
    0x54807030011058181e40c40e02d401c60000d0001c0340c0003901d1040d80d5200c44003c42c0c0c2d540007108140c94080000811058034091250701d545856409814140b074098001400e004d03041d64540b040c0490890070316100b1043c626041d00d510200c2c00d155a4401d10030242000d90307031510305c0250010328085e6101c517100d01c0ca40d0745201602c2c440d034044600c1c034402c2c0040710070050b05401c085071007600380800c0c1802806840004a02c1d0180050004100d8806a4a4900d802d51504a00350142c01c900b404403241500c0764a03001482d0b0310070015169200b265a4a02250b05001d0111840c0c098048030050040c04203100d809108142c5440602d428040c502140000410610300b00c1d00410f0500d04250000101040c0c0d0f81100e0750014240c02c8094440d0111007210b4842d00c01a0ba1303845407031040d140d008403091603402084a14034203090b00036106050282000400720300103416608260041c2d1494418100b0103075149900481c0b00741a11f070403580701d41c500340c10500000c040000c80e02400044c15214400d40d420 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 193195467 1250 193194217 193194241
    0x30609030e040207060b03010c1e080402030a0b090f07050405040b01090e0109140f0709050405060c0c151e130209010b07081905070308010f050d03030c030e0706091d060a060305 78
    0x7440c60001e0045640d0101c92504000501100c541e003030203586025244071125005840114614103884203100c1d00c1c41c8201c90441c2e03040c100174401c81c1c15010340740b00700000400c4d0001e014010f0300c01c0301c0a88140255801117914103c8035a100034400e41c02c0c00300784000310742d000c403409043d02c4610302e01180d02030004c1000d5001d800340110040081c40c3c006050005460081740c2c03082c0c83e114200640b150640e89202c80f005544054034050200d130042400b280c14000440020103030b408200044d504070703070400048010040340841c3c1d00c00441284000c0c0c510000d00100a45a00c1180d00c501c064455030550040340149605001d8200c400400003181340501401c5c40a403102202c0081507140f508804000050998102c000c00b1004984100004a14103500b0300c02031054400c0500024245030b680d4504030301804409541400345980d0742c1280003c45000d10104000e0100ba4403000d5625140c400248584507000131044e43d050100e00500503540c2c0d502560108481292901050b562a6a41c0140c9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 193196717 1250 193195467 193195487
    0x1312030c03140f071706090a093807030513021c0219030b0705160308070306030f06060602161214120403120806060c030a080c0408010f1b02010e0703060903 69
    0x884505001d080200c6140c420849504c10401655205582c900e00101d80038025400e0316600d81c000442070000e0040b141e030380d00101c645401043d13030280c3e50810300302d81780d0300c0000f00303055021540000103114611010741c100f0540040c03840c5420082443d005010b001c09491860300244520094500800003903090314042200d150002c12010b20000c5401002c16051110f2000300d99940c1e039100006e44a900500c16501000c101b00d01c0140c0140c142c0d50304540700000100414141a0307620b80c0170020800c1d0780c040728861031040000040d03a6003042c002030320381030010781503841903d0a84018410400414907038010700e94030000304141100d460030034504141e10040704546031007012a0020900c003c00504040451054841c10107a864003070510109110b4400380e11003a40c01040180030031480388050b01d5001900c0c00916040039100d114190130342d2131001d0310781003c07900c810140309001c45460000b0b007403806e00d0008100c0d01880301e9440b0b403610304d40e10024159030f86d00c1003408149409108644 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 193197967 1250 193196717 193196741
    0x30c020f2103131505030c070203030d0c03020d0f050106050909090c09070f090608040b0408070213020a03090309051002071802091c03030b0d020901090f02070803040b040b1312030c03 81
    0x2001404003800340d142e69030040d40248251550741200040d00700031044100282e0401070f0784951655a40e4038086101c0e81c04140100d0b050320040203208030300f4049104440e000c5041e5a009656145c604080700103650b9000030f4078810303038a00001040020740190480702c101400b0740340e8420650398020b010307092038003c183c1140c110301079a0400c00200c4d48400c040107000031644900c18071a840c1c0301e049a848000f194003c0491545a0209000c00c54050240c682140b0052804240700e002207984400d9030412404840442c0e100c0320b0402c20107070402c10100c054101a01c80300ca4000640c40020342e00c0216109002c00014441c030701d030020411a40458401000240001001040083c030380400001d1000064000914240c8800c03841d1500c074611622070364004098852036400c0800d1074005142071100895a60b50811004000413810b002035840366000b4a5443c41c2484c10342082105c070314000706502c0c2041e1142c3d00e20b40005100f1040f02003961f942d440c00182e19025440300740e0040c01014a05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 193199217 1250 193197967 193198009
    0x30c05060403050a0f02010b0102120d0b10030b031b0d0b06120d0503011d04031d0118030b01061403090601060e0f0916020d030903090317041e081603030c020f 70
    0x1009143d0448010005004650b941c20400740d4400012822100740102c021b005811911409102d1a134483c00b40a003901c40d000002850141003000a030322002400c0c642c404640c843c0c151420b5480d0901000343ca207207200e60800c2d0f48070021130028240e034002c110001c006251003000710b200f945860440000030800002118004004c540c0042c029802c240b081066524441c059000054040603c1c035004503030540311100c291342c201da4503640101030402c120b8100060705e41b00344211a002080d0300001d50080e40350110715410300000400190020b545008140307400c01c28407420f0040002c0440c1161070500c0c00e401d13091034020000e001c00c01c98207e0f16910045601c00d000c2c0e05030014803001c100080c650201d65440c105e044080c2c0a603011481e0141c04a20340e010100046101e12038880104012a020703585800e85076481844405104c0014600c8100c1c460070500c094402041340345c684001001e083c03061589165401401c200d50401c00030301680300409030540d00e80b10010200f640c0403c0c0c003c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 193200467 1250 193199217 193199221
    0x70c0f0b0904180b0f0c090316150e010504031502040302040c120c020c01020312060604050612040b06060708070f2f010210060f06050304170a08041a060604050d030c0506 75
    0x103005141e00003810a9102c0e91030084410030f071a003282c001c0c407200c552109404072113660b46841c050480e24001e20102e06210200200b1140d980e040c04041030140880324000c0c0301500300040b40203400494030405090019140d4054681e03070300a4251070459910001201c5950617075031801020340601c1e40001d40003820409525001901b20790441c5c3c05280c094010090722100500481e80c1305401803015025800810150004a903111070055200708050320030341c64a0303a0b0f80041059980074400d0342d59907101380303024003041000014610741c0128003140c11508044091b01c0c0e104603889821001028584902c02000c104400c01d40c0ea110070318031015480000c08100c0c804003a000100a6155005010f81c5010031404580c40c49158162514041d484200500300f18054515902c003410990740b408020700c04c4050f207000140180512115661890440d043c28070302101101143d180d40b000c109030100400255854180075101100c00c215581c030401b1441e410241e172003401c03018000e403041c016241 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 193201717 1250 193200467 193200479
    0x50c0a030b18070e071101061d0103140a030906050c0114090f0d05030f0115120c021e0f060f15090901020a020c0307080613020a1d040c050102071a070c0f 68
    0x400c45200e00302d0a2181101c00d03112a003456124683c600854080c02281e60108402d544588008000507521800003d00d0759224141c1a528986840c1110007034846c0f1401401000389401d0f200318614009002040400c01c1507501034001d1403075000b080204040401c800700d031660250406c4140c0d01542c0c0b01141d041c204006440d84440d9143c04014051142d10600c14106110310704880c881c1c5424500300126908048200ca100c000a103500300401100d400e06584004892013900010b030250380090100c00500411241c00e070100302c001c10683d4000304c076401c4503541c010842c154440d404288003070056452604506603800c03816941c43e00001d114003000019031055009080c054400d8088410000703e070400c1540d54403446c01071221300c0d003000012820381d0102410005d46144003c009000880c1ca03100c000030701598442c21900c20780094801e0100f400761307070043c0c840903160a20107095540c0c20301e034039a01707070480d00041005404070005d42041030090403041ba4001e002442078021440d50707540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 193202967 1250 193201717 193201733
    0xa061a1914010c0c0e07020109080a0c030e060405030a1103030c01060b040504111303060906020906030f04020f06030705040e2706011707060f05030403181d0a0605030712050c0a03 79
    0x10041c0c515403810300d00d6044166010b0b59245001c0d5601c000a8640b150800800050405018080c103080d0364940c1c3e903040000b030408015240c03007407d940e500d010b01d420f142001444820324801150280d01d0811050006480100703140b10002c0d0042606514200c100c800300745140710303071107811105519103000440c60501100c02401250b0703044074184075145400c2c03070f02c0d20280704440140001c0e80c08044104006141600900420340c007440b401400c01040402184241e44100c80b206d215031140e0b0100003c5181c5010700341110003059074064114500068064240c1c400c43c02000c01029814001030940ca0404070312001410301e0000041032024800403140c3e036100c080c0241c403441001c0629824a12800140c2401260281e81d5404c4482c0003042060303859a00c007400590030002169190702e15070800c5054000200701c45503104003003840b5a008014520b034041c010180315800c0000420030703941c0c0040c907401036864504600001080c0d500c0d00a01c1c3c90007250031a604100785910000c1030000003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 193204217 1250 193202967 193202969
    0x141b030f07380a0209090f06090f190b030a14010c091712070809090106120c0203031003240f021806160b3111010906020a061a19 57
    0x500200c8445a010101c516030076550400781d2026440b41d0800c420140a01410054008842803001481c0045140100f000054220b07146800070401b6400d01c50389051036031003194003240e0107a0425550800300d0300401c60140d003842ea48c40c000c0d111030b14144141e400380000301d16281d01441000075248404800e901806e582d544541c04210500c8001480d510001c100c0400030f003804026190140e00c055105941d03030000344050b10350000500540c910f9444000140d40682443e0310f030320701c10b0412062940107a42400e9254001c54200344244103044207240074180aaa5104210040c074042c1321142c10840402660f020b46c0041c00c080c0e01044110742540149045108000140c0401144500f44a05441010310a0300c0552090500c2004100c0100229402034440d00036a40d04040e2250240c140c2191420803a0032022805043c0081020030601c1d40380550083c01c0c5450200c0c580322001e903d48040c804040c000a4444208440c1421111212450841c2c020050640051101e084ea8460049 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 193205467 1250 193204217 193204223
    0x20c090915070503071218140c030601120b18010207080301030615240c051221100803180301020435010501080a150f09150b04060303141b030f07 64
    0xd03007000b0601c0503200e01c04a9104031819142c1c02014a800c0710000001c0c0481008074000760141c0d03500100040c01820790058541b94000102011000d04c0100b504008040e4080301070b400400805900040d900302090781c0c4903004900c0e0a8080d0130a0034520302901c10040020078800c000000802040501ea00c407456000691005811094440014500003061600200c100004010745803d001e445001501c001512920560b4940385401c0c024203201e4000803500409030011312240b9020b00301d51004c0030b0b44041200700342e075a42e5181c402031544a1044000035100ca07600035016010b552002d4048400610264500e414004150020024000420700081c0b80000003002628002c010502505042e200440054911000b99580349011100b00322019645151109800d40210405104120400e80034455844086010040382c00031120694902803103507203481018004030740d0101510800c40162001c0030740d100b010108000c400703c0950344a0080d4031001a694003261a01c5000d0106a44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 193206717 1250 193205467 193205503
    0xb0706050627060109030c06030c0e10050a050d02090603190b010e0a0b0a170a020c0f03040f060503130f060e010e120928081b04200a020c0909 63
    0x40718810030200c2c0032a41140e00401040300100c801020300c0c210200d03000041418500680e6949540e6403044494551042010950751824594410b80042c0303100281e80e0704583c030030300060904c2c00c003a0041c000c42c22103100308840070a00b100440c02c60390484611040c010036094880ca04040c03286101800300c04404030040c10580404000d500032240c0000c2d140004003460200f074203141500c1d201e5040a11003104001c840c0c10400c0d500b40000003680e014107103d020242e95003100c06121482d18140f10140030203540f04010030480c0c6040d0141986c15151140b8269640b071b100c82e1461306000320940d078040c1401340c14000400400065074850200c0c0031103400280548154003264503101c4409105902a8580800c460209032038400c04601301d5032080c02b5641c602501d401c00340c041303a1010360404034440d0722200402c580850030700b05403d0300034411182403200040021101045c1409003a10300700300c82000c00c0f075109060007402034031400c05025001c4505403928196803a0b94800210514840c20 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 193207967 1250 193206717 193206721
    0x207121104140609040206031b13032108190b060c07090b1509270915010906060e0d0201270e13020616055805031f0b070605 55
    0x4400c030700034820030004000398038985c1c0369024001141e00050980002d81200080f078a80101e480c0c000d03145280c444020402d1071425403406001b40c000d04942210002401d80c20210a5503024801c10380c403121481c00780311458506a00103024000241e07003158008404038906400c400e00188510488805117014000c005040b0140300311150300c1c841c0401780c40e000b00041c03800760505c0780d00051a5003801100040c1041d5408400c04031b81d0083ea90034070310b0381284c0c50200b21404d2058506c3e0140002c55002c12845280510240410030700340152409501c2e501001002e40e0b01400c011a40301c883c480c513002e039150f8a413410001c6110180190350003842d20b080410f22450321503a00382401a400f410b00c606e458038103840c1c030046600e0b00e403040301e061184030300f880500301e9072030510200c2c900c4480011006003040c070060468252252207092103282c500c0024a0980300384100031a0070780540c280941c0d251600e281c802000040806001c5003034010075070014229940c1401001824002c02080100d9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 193209217 1250 193207967 193207991
    0x60d0915050606040602030a0e12010504030c03030c180e091e0709060801060503031213050304170c01020a0201080a0903090b04030f021305070e090a1808030603010c0c0203030403120207121104 85
    0x3134010342c055040160f00030b1107403220050107000040408600141159000c03030000c6801c60035681c0840341103000444841d00d002c105a0140620fa05600050800b001c289c00c03030003040d4410384410300c40c40d1010b04850010030a080014071810342d8040491440540001c00303030f908076a48031220b10a0500c0030f454044001045031040c81000190746005001c0c6181c10b550015698039080e02424004010201008100008104200820081c402c510001d040d114211a00504010f40000124190b4004265440050703074400790b0f955000b24959030009200b0f5180c20304882204003034001a9080c800040c020040c007440c40b06c1607905030b100712200c81d6203041c520074160a494065441c407000c80c0c0b00250323101c0945802110305620854005000503a0700300888043c649800f90030341950030780000010b01445060a002d500b0b2a980103086c0740b010740000c1d5001c20b960380b14620015145010035107000021a2080c84241d0040c00103035a0500d000740281492120200c404460381d1165107016404102 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 193210467 1250 193209217 193209229
    0x90b06190f050409030215040501140a0e060f070905030a050703210c06090f05030706050a0506030304050102120d0b030a1a01060e010f030e1207050109021c0f03030b060d09150506 79
    0x390741120166005180c0b402080c4405000d19190850941c0510303c0b200c69189003a00c002c5124500420010035642240c495400218070094100500315040c602414010400010001d4218001c15218002c0380c2c0d544108940030a0355800c0654580207100c90a402d0040014005040d24005c6403880d5490100510074081c081c094014100442c081c14100b2002c15030326407204030468011000040100101d607162419a401a001161030507036403014054450403e108a0781d0020042d4015803500e0306020001c4c0d9104103200c8120701d010000520a9104d41240d040740c003030780201408030b626828581c54240010072824419180c800140b4000140c124442c8103032103800304040e15440c00801000754100c010341516241490740340309200030142d017081e03600e00900359140181d000250800a42c4100152400f2074a0346072410b41400c5440c001007511160100119507160800190b282d0b00100401c119006e0752101d151024506051207050142d000b03d140b85218041c50100043e954030020021 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 193211717 1250 193210467 193210469
    0xf0e0d1a0c04081c02120301080102180102010e0307060b0d0203011b02100c0905040e01110f0903010b0303180603100b21070c05070b0c0f030d0c0f05040b030f041104090b0619 77
    0x203ca0788105030002c000304001c401072804080c944143c030008108807110071400e0340282e02c0840b00341e40c00101d2403682581103480150782c1d0001d00c001d00507c005003001661b240110140a010b1a03039070000d01c2005d81d03408900684182d4007a0090240100313200300342d10662140c1240704090b0140c01c04041d54107200d40310729800b41c541511307209041d501f0300e021310000b0002941030a0641d9a10611104041e00c110b026002c1c00c48050611542da08809081c5401c0d10580461140203610074400780101a8030b104220301d1110b4150743c8036840e0f6036052800e404078100345d0300c41d074100c0d8000512804140020291400050b41249205c4200e0316000002c031a0040e4185000d482900300400511520b4200e01c0184190b410715011500c04401c0c4406a50035540120300789240c0d250394440c1680f40329000108680b0403201820078074140b900c0c14403818400d12004241c0713800c0b451510009401c00204028400d61150060020811038146240c494464007083d90070790310a00020114100314103803401108 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 193212967 1250 193211717 193211729
    0x30201050a0309050f1b0a1a0304030302070c151706091e060f0a0b0a0206060a380c16050f03100e0a05030d050105040c030b03030a0f0e0d1a0c04 64
    0x64507004000350114000c05881c0c40850725030140c5409861a100c1c20000149204001e24040101030200010480310440951120201d64000004410451071000030740c0d5020f9054100542e0301c84d510301e072070007000c04079802610310001004000500c2a0f4800852900000b81460745541c9494440400488210403128143c003801c40b00c68518030220b40c82030a6406c9200a05040d4440001800080024039240c00260f0305020100d0074800302641040490340210b01a500a04802d04000c541c5c0850f94000341801071201c01c84524942c0400081203c5502c2d128503020680c4400040382c1054031007030903080c21601c080c4196000300c0e452516106441c043c84004004002545290b50000e0181082403802c18144c0110b00e10310700820410b03c01005003843d1084002450341c10501000120396814110030201032620044110030f41b000021180702000c42d003010b038144c401d0f0b448219681c014044c3c600760005540d2109800700b215000e009104a540340c0c200002507642c000b80d042d07890103540304103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 193214217 1250 193212967 193212977
    0x203060403211103060301050a090f0803040c050a0b0901020d0e0112090f1a310b06030106031506081504080403030503190612030e09010806150d1205120c04030201 72
    0x1140010380100e002070007940d41c0b54440300401541d411808110384a060303200d1801c100010400c00946020f103c2c083c3e101c02644000c100c0350103603407204c041032808040300911441f800000b00702449911810000205001021840c0194503003004da0304030f800140c0310501601c6500d20414510780142262220080180e6604108d051400a0000030703003000e2005a03810f010803481341c000b00e0101d0242e80c503800050400d2179078a06044000341802c52981d600001a030003504503480c8498451944854115000f001c0003545440b103000207401010b107580014620b5440c0580314804030b419810200c22154100c3c140c0c0c41c503408912888004000444d0000c3c1219020802400024001d0020707582281c0d07580c403000b083d000c0000c4004119806a0410104002d180c02440101540800c0c1e1320005402680c0c440c55a5141902031070750766002a000c651264041e10100000351a400c1e108151540c2000c0c42c0b82440d0301160005e0003640c011604480201a818005141400c03100221400c036907040e990 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 193215467 1250 193214217 193214221
    0x5070510140a0b15130513020403030206070807261501050301050607080f0d0204030602030115031e0c0c02030102040b0301090e030a05030f19092004060302011b03090b0301120618020306 82
    0x4800300502005001035400401030b030003d04c3c1d1540e444041e222502072108101002da042a080043c502d1066448612072401004140002580415400c2d0040c041c2c1c10304a5503500c0b54042503880b50107149010b002d42c00000040f0b0500d420010310306001c0c03119a86085482d00003400111110310090044a8000c0d40811402c0e0002d50400d0042026074101d0500c6824100f0740c0700c01e4004c0e43d1241d4429a8401d07004801408480009841c15010b10401d003070030840f104290380c014080d40c03102c805aa50030740d03840000740461401054401d2029030300038001c540d0b0703d840c0c00d0031206d581c000380540c410b0503251940c6400509000012601840a251600c0f030655032150350780707100310100408480641400e214504c000240c58007070398903080d102e0300340050811185642c10040d80c00034140c0c540315605240040016036003040d143c02c1e54010500038241040201d060640f0035030690741c81501320f205c00000000d1041d0703a050b0b41d003070304c144550303414401e81d503003080c501c0040582a8006036041d040040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 193216717 1250 193215467 193215481
    0x20f0a0b0403030b0306150f040b130f061802030906010e0f0c0a050403200f0609180a0207020603011214031e0d1506050a11060c0a210c0507051014 65
    0x100c0103900a1092801081c0b240c510303c0480d0900c60309403980c41c8510b05180f48801d0924100b01e080b21141c0b020f8504000000496000402c00201e0a0482108607610b49401146282e40c0d004900500050f001144a4a14114030f1000030b600c102c806180d82c0c014600045495883c00c41001d004a156041c101d2107500c0300480c9814070f5110201910502178200700000003d000d00c0421034482e20a04103074002e4018100c1401030340038180d1501442221704000002181d642c0d99000078010400300095007041d500c420b040741c003d1040001c0a58400c00100000407084103504e0070030710240c801c0c0d03c3c0e8181e001c0708021840ea20b010b1107201a120360155050540115208000b5080c04415084040f50f0f850b424001c0d102802072a810440c006600011a40c41130764024140f40c22003000c6d10002c1c80e440c6800310f1320306024065100301100300100c200d80070703082902101e64000904420b820030131421100300005401d41d4001001100c7c140107d80305a20341c0301d524408d07603002107074601071590103640d640 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 193217967 1250 193216717 193216733
    0xb0304080d0b150315010905100c0606030f080318012a05191e050f070f1a01060903020906010302070b01050f01110114060117070207030f14030d0b010807020f0a 71
    0x748455803080400311940c0c881c0d070303611205003058400e0340e43c0e8102242d032104130700c0300d20300c415050101084041040f9220151012aa440503261030602e1034903610b41007000e08106d51000d0040010300c00900f080c003804000035800342101c0d000c000740d0030381c002826070700369450541d501a50701d01500301c66208159281800c00c0784407080c0303401392400c128103001e80b94206034002400c0015221134200a0b44002601c206907000041d41011410205c518011403818401d014000300301b40c00429502c010881125400021001c03029200312aa42c1c564000a115000e00c4c481a84920303c00004540694024400c0742c0f10a034000d6943e0b0466801c0130240302115000040460411180c0021144413240c02c3c4500c03058030034a04410041820142c0004202e050ba0300360003030101640c00c0500c181c485d000070f0780e10112a40984406561101c80c00d00c0c020648409440c00010300000070307180b06890b072503401448900c0f001d0304c900c070880e01d0f14501240e84400d54580c00c01c0540c840c00703180340407078512 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 193219217 1250 193217967 193217977
    0x31703060607060c11010501060c0c090b0102031603030e06070801030506130201110a0b040510020a05030a05060607021f030e07140409080d0905060117030a0f050a030f061d100b030408 81
    0x80c01e2107203072070020381d10030044800d2220158001440d4448404110900780200c5004007102e280a480c031040ca516103064030a140c0c400e0100071039480202c01c01e031ba402401580c2c64668600d4155401030864140078001d440c200b84102c01c14019800020f220600a610280c10303030342c101c0f0003800103944014051064542c0f00b07a043c2d050100320982040f00f500e0810040d60411721540c00c0032203e003031900c5c04510304030740c050040079014014007594a4603548042030b43e500030b0384002e0101d916140c20000c85d0301e03845110030213504003095289815807074901c41c1420702c6030039140e5010060100740442c400c0d15003003103009603c11410b82c10701c0800a07207003c0e040b00c0c007111702880c10f051a22000c0c2d440d1404407400044201c0d8103801620041150309501104081e815289078051440c09050103001000000252050f40522001040c4401998440d5001d52000c1c101c41000b00300e060385a0044841251500c00c0d00001ea03030035038001403a010300c2c50706180100c40000360081c2c1943c94690340d550311a046 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 193220467 1250 193219217 193219219
    0x11220b010905060f090102011112060904110303040605030910060b09151903091b03030f0807020a0c0602010e0d0c020603040201080402190308072a15090b030a0c02061003170306 78
    0x18004a030b030340c1e1040e0003814440e4070b4140140d0344091420000e420340b030586001110407a01401081d010242d0708503099030201e800c0340d2a02003903640d8945041c1d0460f04040154240c480840c0100b02c0076080001180660b000700301b00c44004010a000c04192891030060b01c501c2e0109100400280c1030086180d440c81303041c030b01428101800005c035a000c1136500843c04001a071203c0c00002402018640061162505008101d5160130f5880181142c008007482004121120780000c540340d1090003c80d05e241d03800107035040d010703990b130310024003901030441400d40c3c1e40108403860300c4450140303018102203a4050000750466071203070019038200c0c0004000343d030442c0907200d0300f8100580110001010391310409a4a0b180c3c042c0b030400c4480c1005410710301880e103c07000c05800e220006c21111100b1244c441c01181c81c6030011040442e10307840b45038490200582d011040c402180e000b07070428642c08100380d08030707505507550b00382d00392280ca110310000d40300e2001d4240308440e030341c1440002c44d48884 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 193221717 1250 193220467 193220477
    0xf01090b06340f05010c08060a0f12030c020418050c12070e04020402070b0a142206050c090409050c040509120304030c1a010e060909030c0c0108090f06070c11220b01 73
    0x282ea5200c220040100701c2040360244d5581e0205c41d0b0b042c2c0c000d000c40707401000c10340740050036501f0110344040440080c010000300600c034440c403404241c407074124140320b10760140040c84100710302001071100745d17200c0b0000ca07a82d0080a500301d6441c141503408200c00c2510354010003800e072800d182d9400780100504185d030026000c029017004030f0540c0745020b006451601001801c2c0002c141c0e140a40c0740050448030b1805004c405184150740c2940004e0546504244001040d4071002c00c2c0d40e03044d111302512a0b4102d81803605840900a0100d032040c040c1c2c3d410344080c0899070b1649109920b980140201e03070091401840800e01080c41400c03080344403482402c0c1900080803848030310041c410268861850700341241c1c1005100d0405040950300050160010740c00c0c280011520341d2140820040b180c10010508005081d00300100650000d0035280010754515080200005211501000050320105c0003400e807500c140c1400b0a5000440038107040401c103058010190b00301511b154074078a41005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 193222967 1250 193221717 193221817
    0x71505220305030703170106030b0a030b1302310b010c0b10030515091c0f110c09090102030402010815030703240507090f08010605060f0a14030f01090b06 68
    0x81c42000113041083c06912000e82080010007640d8100c0b5050700180c0402d1301b00f42c19514180c5544c120340d41900c0d8080c8100a031035072200340007801c907031072441d02950202d0f03410f240003802d1201c8114240e1500b0100001c14034501c80708490030030364503044a224002400f08a01c17002261440c2c80c0c0d0381c0c02c003801d0a820060980d40c0d0700c402e8940080d440c40c109080314003030140190090100b10342c880704100c01c0030b180d840d066042e6000e04603010240e554000d1141d5064449014002070242103002d1000900d01442401e0a00c0c0e04c5000b50800c0350101d000c200c0e420042868000034002060301108001c0c02091114116034540012000c030501400762641c4040d51000f80c000c003030060500c22441d96562004171880d14107001320340081680551601d914100d030500440d01c0f400100e460346054002d503c0c0da03542c260401110000c1403986c0f144510a40403007401914104000303642e0403603505030014440c00ea802010000103200300046070f10740100252030710000010f1120541c14110031031811126072 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 193224217 1250 193222967 193222973
    0x90a0f0305220e07081005011101021c05010501110f0607031d011b0323060d020607050a060504170a0e1e0d141009030203040e0924090715052203 64
    0x15a0140d01090070010314440b06202038140c45182550207103035840d10031981d041c41405110b900c035030340c0038460420440000f001110042501210348010075a60690f44030403024040b40300903e42801400d0024a4128070381d00c6015000804860030540c080103842e1a8940200642c028110005007111458801c0800e00c6079690a1040c0c8030381d01c1118103000042c3d141c41800504a40c0e03110740030529410750020100004100700c801a45c4110160350310700600510b40001740186c0900c3c9401041441110f00c07034010003c1d20f8000310f00031071060108030001240c03220000c2c020300407514054009184030040000a1500180b02421366920610300345a42c103071031011a81155984a050312505844080c1c140542c000f0000111540440300b403c208001166400035124855846042031040350302c00420b070749000901c01400b43d17403443c138800d46d403000b80c2945286109200310390140b09401103500001d41c91070220030041800d406541c07024a001c1c0301d84c41640c41c0a034000c40404400484034004400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 193225467 1250 193224217 193224247
    0xc0a06140f21010b03070e1c030503040501020f04080a030e040506010e010c02040b09010801140609060f010c080903030a090501080a090209010909050a0b1e090c01050f181011070608090a0f0305 85
    0x203003904c2d0301c49680ea0b140c407010191001080b0b1907424014081c1e42d00791741812882000b0a00f1207070b030514246940c0d84540c285140603004504038204a20b07000a000203007070100280710074542d8442d4540c0085007020310200406c031201202c1d03903408100d200a406000d98031468140c254188020070009100441c1c0c0081703400b44000741c11056081c0e40d20f60012404a4262001652005084a00e54082d02c4e1400c08202641d1b41000780c6414440d00e0310904c0200720a403415108281e401804413601c580701c2d54802820ba0354035200d2503010039491001311b0410903003401000300301900030703010170382691a044480004144504068407140154000c090000e500f0540c201d015a000441540d80c10881403030081d90710074058607a122503482462003405a0341c024068445d61a00d4000f01e5894011500d0001b48a0803070040440d40100e6214a07048000d40249a60305808440c10071a600c01e03464000c00e0f100c40000790740408040d80030800c040c0c000781c1703503185240d89280701e0702e4120300703100f14402d800003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 193226717 1250 193225467 193225469
    0x15140304150e1c0f090506040f09020a1101090b01030b0f24121605090705070512031314010e070b040506070f0203011d01141303050d05070e0307080c0a06140f2101 72
    0x40015200040c1c40d1340b01d80e011904001500c0103e550324038151402850044c0810700d4407401c2201c40d004580800b8440c00399140380b0072504048004c0c441c4c0b0990303117050300700c0784000d000846401c00c0110214901c1d1260f002003e1082d2010080008840b034040b600710781201410060543c4214120200f010360706007401002403c00c0c04c40640c2c443c45041404111100b0401400d0004000c028881e400202c0c0000540004400b44403403030554944030444504680300c04118007a20740c00c0040c200c0c4002d850150f10801030105214192001503845807400842486940304059014000784810301c080f9801e1218000100d2000f000000c1c07060041060100d640301a00804a0695403020200302e40314140c01c1d541e60043c03d446003040c03041d44581d0046d10b203004003000e4030300d85551107001603c03090045011624000700181120007241c5d8600075240c1d02d18014408a0140c00003000008481d40240010003000c1442c600795810811a00c9038014181c00400c1c0c50940d08000c2d42c01c050944c600200058 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 193227967 1250 193226717 193226773
    0x22020c0f06090c030c010801170109060204150e121002030919050a0512040509010b07021206090a0309051c0b0a02160f02030610030809120a060615140304150e 70
    0x101c0e2900d041841103090503003400545000e83c2110001c0300d00d80e0ba10103501e50550784007142c052180b51b00ca403031030750040c40310510040c8540e10000703020178085030000f070700d50403000c4503503905a0b142044400e00c50f603409032102154080e400b40d424429644c0258025503803140749001252900501280d01c40f29903108070101303907001c0e0000d02850007445000e102c0d10031200505c40000e0302d024034110104140e00740510942c6034102c400301d448011961f40c001c031030308608600003c451803410080c50700c0d5201d54804100300c000c0758089500094500b0450701520b210151800c3c4400c02d40c85540341c54500840c020b01c1d0103a450313400c000c0c5c0c50b119000044401c2e005401600c03000a0031015105051078084c1c0604030070161442010104001038114080303440b820300980f1050030740e4044590070f61070000340d010b0061006080400c0411904030401000c6003003600d5a40d060202c82c406402c000340d61005850103001c00b0201d0505960702c00c1c4a400002c48010020101d4a001e19445400180401042659 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 193229217 1250 193227967 193227973
    0x1c020603060f24042c180115030309050a080c030a021002190f0b060402031005010e040b090a09061b0507020904020604031b090506040e0606090406060f030f020405100522020c0f 78
    0xc3c000c5903540ca58042111088180300c8004041c4541109a849401410341c03209041b40383d100450382c41d00b034000c8000c0000d1203001041030741d16481d01501454081c003d1074021000c46200003510040010400c0da07141000c1c02500c000ca100340c00313214150025404000542c4200407803c0854039280351600c0c0798a005084810031580c05140c8661140c13405090396110b40c0c0148248500c1007104426081200c4090820150515000012a0240840442d059440001401004120031882e04000340382c5118a00401c0400b080d4034050f07001000c100141000600140a204018201245001e400c54001400e850170a6600d03134624201c0000c80700c800d103960501e10800c0050440d1030059035002081258140021001c1e280b0031640da010051980d442008000041014031400d80d1200b0702800c088900300f9043c58980c18078400440925030124010b924100003c0ca201004240d1901580d2004190320f00410703080302d82030705442c242404d91031401c0d42040070110780441003020490089003007000e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 193230467 1250 193229217 193229219
    0x3060b03240d12030b122505040f060e0106031514042007020901080708100f09020a0b0408061b0a080603010b03010617071a220e01030605061c020603060f2404 70
    0x100070161010050818000d699115600d503106c0b80c0803c00307003503016810340441803010b181c80c020100300c0410791150780c0061800040c1500702c03010342c004000380e8480500040380ca0744d2310303041241110342402a030540040004018003241c50710750105010b10b02c1c010700c0896440c6490081c02c006c40350400703803480c6103800011103d0450070040880b030b005002640c00341c0f04a5280503005500c40c030700c4543d801003107581d44049400103602d9600000b12950003401e001e0195860300e8409003070f90300a001d001c0a9100380d10000c0c8100340300020f52190040d5000082c0e040074005201074130140340282c503640c0c0c503540312083c070790040c1c07801d01c500c100501e4001c001001341c0c0c4000c4101130070201680c0040b0ba40702c00070f102240300c403081c01d0211850b035070200003180460660040803001a2100d41c00000000705040c1c000000c0c01420b803c004c2c01203c00321140400c0340600610801410807424000b9084001800050b00c2031900c0c5158240205001c0c200340d02c2010301b40e81e000c96610001841c07012540010030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 193231717 1250 193230467 193230503
    0x30106030942060305030a0f1d01090905150d060c120b0a03030f05040909031e0c050c10120f06080622080702060712030f0c03060b03240d 61
    0xe64040001007002002c00c10301c041ca25064052110a02c03040b20785124500c070241c514002d0340311200550b049426280c83c0d0300c1e01200100125131201e02000081c00d032520500b1000a02c0221b00c4590030142c5400312014601410700300900320041c0b604031740070440c010801e6183c031081c078180c0841d4441d0340c000401d442d0144014002a84101348890700d945010398038101502c070410010b050720380604100000d2100103004032404c1c4281d80105945a0404041e0010541c02c60413554900014400400c000611000121103010242c14080c0c4039510288454049003041c20304040a14000e140c0380003164000000a025190f02c20003194440e039580b0780030800c80809000d81a04510b81003180300389141746001103460380c0801c48014004500c00501001155118001c498900303601019942c0030070941c10024004124082c03002c0c01290409080d611024460b1007058140d4401030135190444d10f03000d41d84540c0703140e00c0301c2c8141c0f494032485111496944401c10881c5a41c07081ca0602880400d540c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 193232967 1250 193231717 193231733
    0x303030a0b1005180d1e05060402030c0108041a31020910030b04060b03010209090a0504150e0d0c05010603051f24050f01020a02120f1509060c0a0e04020301060309 72
    0x1040304003c02c84107110914800300e405a0344a245502203c04941c0142c0c0c5040201c01d03015111031700e54540d10b10341416030070090701007406403043e03000300c003582c402010460040d503041000b2a401441095089200c210350038078558050303000030f2141c0000c0088072061048403a590300c80c82c0e034030300010305100c4130204516282c004503911541c0c0c0c80c140d000883c60b5580d401d0861a018000900864a401e0410416242541500c8000e032000301916201d081c240500402850b048d07401340c607011032502e40b04410042900400d40c03020001d4004101e02030016a0899141d081d000007250195241d04000001c140f0822141580e020b0135500c085205032502c2c0780e40c08861400071402c40c80350801c0310b605000c508891041013107401c04d85407029403540050040f03061446150000754001c2022800c402201e400003120303034034040400100da401074501c10440c0b41204040b5010701b000d52040c00010184181c0c0f5000d00808006401c144509044810000701a038100743c002000007581c400019082c40100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 193234217 1250 193232967 193232989
    0x6050a06020f010e030f04060521040803010806090a0b06011803021314011211040b0d0c030b06010f180b0c0a050304081c0804020310021c0908221508150303030a0b 72
    0x130004503c0d0600c0703c1c100b801c1c2e40c041e520545050003804505002d02910200002c4240c0980103810789d02403400380b03001000c0d0b8000780940c640c2440345800007041000000b8442100340d8100703142106940d554030045410000d40e8003845c40c140d0103c640040161a903102e49045504480d0740424102e2a102800c011424140c1c02503008003d2400001c000c104c00120489a401c81a100400d6840c603000100e499a8001c1c6001080000900303030000070321940b824294010314003681c980a1401072000d00f107a0307660300c5207030b847e410322500807041040c030050340c0c010f28400ca1148160761000c8040e4070f800342940c0003a031202c0c400380c01079604510108820090b060225225041c184502d00740350300400e540309508440e0b0b80141d0380c002054460f4180039900c03141c40950380042881000010310303083c1040d4010300705440071f000e0707802101c880f40b503043ca010b041540ca44000241c00314141c141d0440320007102400d508000807003102c00340a561411300096104201c12040801c1c90a144024003000707110b9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 193235467 1250 193234217 193234241
    0x402041104183c020306010c05030a0e030615090c0901030e0f0a0b0a1103060f0102030903070b0405040b0301060317090415060f020706082712070c03110405061003020d06050a06020f01 81
    0x50103003d0300c002d001c001e07030700803d0900700d100503180c0c0d840200503211090100c6000d070040c4070100302d0048550b441041c2c820340280580a480707003521010941031440d150008020b92000c400d0000030b40100070040584110241450003040c1d62041070001030030304444600001c0140c2040e640700090120024400360002800c0e03000300032a0300c0b400c0d44074034280409080284a1364004080794080d85c820420b44010030b5009043c0e03240150b482e80d034020b1990103403007094003903410816031004a03d4184100c1c0102c030f420400030f030146a82e9403002d4140368003c07020303039a0060b41c075000f40c00c1048040801801900040e2507140ca41010f61601a241082d540d016800304052842000300600b030126182030001041000004800d02629401e810020740c101940342c3c090020408100307010100601004513401404100d000c5070903001400241c2d101240ca03070347c0002110110b51000340c407070703402800c13942c00700c1c0390014050b0b440d64006181c01c285076100c10016401980d11102d450020320a103404454 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 193236717 1250 193235467 193235531
    0x503040308130f0b070b0103030f0e0306150102010b03010905060c07060213060306091404030e010c06020f220801110a11100509011d07080703030c0c09020301150e030a0308040204110418 82
    0x5c10b942c2d4401d0005e030140070041c104002841c811034103c0c003800860840c810002c05550091070912258850103240c0700c0d035240158240140c082c01c40c2018801e081026401501801c081d589440c0ca42070b00390f0042c00c00700d6415600700711000d081074110500002404140d5030110310b03d0701d8510180d0aa94480c56480307004003500701480002030b041410595818003e0038201c9401c3c40c80d0074190024000d2503000c1c2c0b1001c0307000070280e1034480d00912500c0004510003501c84803030303222403607682200da11001002e00d0f52010082c0350301d00c0e8000e02d01c02d005803e564040798040000c1c00100c0c0b041c0c407819501440c290791030351540f040007201904900320f9848a02d0043c484245040d0126640710305510000e400d0291515140d424000c000e1982001b6103804082999a541d480c0c0c03186004481140813440050101c04e01c0b04020304c5c7c04204551515015915440e8503110f940030800204440740345820940020000011240c2c043c461045d600c8100000c001000d82403880441c41402414060b520906 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 193237967 1250 193236717 193236727
    0x5090d0510140c1611010c080412021c0b0609060a15030c110a03080604051f060c0c0b040e150a1a07020a080c010f0c060b060408010504151112040503040308130f0b 72
    0x11184544d51807280d5003040070300c9920181040140d82601100302e02910000000070045075044203410a03a00e001e1003511841c0048a048043d1010f241140100170f080d01e41c440d002c60958607103148201d0300b002000704284d0b20a42d9959051002030070498901c40031070340340d0703e4002280341c00c000c94000480c840c002501800b84aa0b5000b08101d5004000c207100f02da82d0b40101c0c180c10b9580b04059001c00c108400c04902e6034131417002400c8040900412035030048100f801045244e50817050764121403010080b100d040e00c801c001039035048600031805d80c00480309440002c0b607070610304c511031072611040620343c1e0714401401840082c60700340d00300c44100c2d800275060480c182d0340308a0240340e403459031501c1b8800c0d001c0d520b40500580080904182c0c0040046804581440107600060082d80f2030071098000c607040d4134a040940346040c1d645451100103100c00e02c8482c60b0300945550052245060303914050700e0380c0d0b0b1004d45030843d8a9850b0456070070701c014000b00c4d40d040c03410030207080c4003031815040ca = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 193239217 1250 193237967 193237987
    0x70e0702011505011103120a1b0804150213120203010915061409270c03150a0c0305160f0203090d0c0807090b060f0a02011b050c07120f0305090d0510140c 68
    0x41e106840e20247c07208181000100c041044e079100880b52100503001d5100414840d43c02000200705480a6551450341c221151803403034984210f894000029144495151900114078625500d00000b6605075481c2d00140001541908504c045807504000009985052611010316030b600c158900d4007600c03070b4205011080d050200c040340404600d59261404003101040c4a04002421860680600c00e48410160581c2403281080c8540c08900b4100540000b50400300d0503aa001d540405661481c0303d130340000c3ca07204008400c02d8441c00e0044071301d4000e20f08081089104a014191850f8000c1c4030309124078141481302100920200d00d00340b00300d0011780000b649034407074020b60103034800c00010790140580c000e410440025044051a411a5001000c098000d91056114503000d0003007074004251000c0e8003042144a03900084450703070b40e074001c0c0c1e010f032000c6e4003030a1220b51002a001ea1280002c00070401c0341e160101103032011614520701c4611040c040c5020705544900c0b50180115400f03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 193240467 1250 193239217 193239223
    0x4060b090402070516030302030418020a0f080601260a06060513091d0109060e100218060d06030b1609050105030105060706150914040c050f1011070e07020115050111 73
    0x1010300403240140d40340e100d4a001441c021070800081010010108000180341e004006401104c2c4d4201402c840b90a002d403c42c0224882c0134844000f14024007d41c1c000c0c0c62042541552200060400d4a1182c03201c1004107014068404990000c0c4040d1b4200310012106000d414020803d078140603003406001d140343c105000003801810359142d0707641c00d02e4481c0b009004903003c5803007400d0000c00401a007410214050300c0854001e0b00d552003030600d9008030030914400caaa07281103001c107a600c3c1c40c08a0313040100c60340c420001030080300d80b0f804000c0045610007010900034940340300d1070b015002101c0030180c0301c134240740e01142c1400002d00040009441c6c8004507217285601c140001600c200012050081110540054000501e010030300034401c02c10001c204e020302e0080c4402408682d0b10000c2003041c1e001e14100e1a0045445020390398a14094102c4405603000c0c80d05480310180c0f14240b02d072208904036450300042c2c0d15000071003010400743c1d000c1c2010700428604130034401c1602656941d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 193241717 1250 193240467 193240477
    0xe07050102071502031c0902121b0f0a030c0b0a090614041e090606031e0507090e040f021e011805010203041503020c0703080a0f0e03060406050403031e1a04060b 71
    0x1000700e0302c01c0c0d00034510381c0c8248121038000d002038048000c0406c50010b090018030075000124011250619072203206940000d01b14042c0c0c2a065109010300e006105014540640a1051b500070100c01d001100081841c2c03200c9026044051000d5182d0311114ac00410302c6001e540107105202c0003840d190301001405080310180c4010030040002c40c0c2ca4681854900c2c01c040d80701011040c900308010030000d0b4135400c42041040404c05c2c0b803e80c803545001e030310111007040d9100300c003041ca01442003102e00c000f008003035403007801031100011940903600807038900c0410070080744018841240032a440e41e040601461803c080283c00c101d01030501d00080e40e02e20030342c011441c600c030b0715080710207030f00e4403a40488110140c04410b84481d180c0d03030b2406040540000c01000003045405d0b603403900c3c00d84502da42c1e621000c0d0050081005403030303540341c12000f4000900181c04040d15803500000c445020551300380750201c900e0001481c0d44c02400700c0444041500a20313803207141080000c101d50055070007980c1c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 193242967 1250 193241717 193241729
    0x601090f05030a11300706030e10090213020703050310080c0d062412050c030d02031611120a03020706020a0b0f10050d03030c0206011202030d03050408160f02040e0705010207 77
    0x1183d289074241c00584030b12483c0e02c05e0b001094108103100c0034068142d4198445014034011075100d0350300d41c0002d8081d2450300f01020074540c003100308403940b20303003581000d450113002510204c09114004421016a4083c11007070340070403000002c3c0401001c4026014000b00300c400c000e09003042d0600700148007581e498001070002915107100c1c00640d0f02c080030400d280d070303000b04200407030640d10a1308003401d9044c00010f484c1400384001a40183c10b000c1400b01002c5651383c051483d1808501040c42250704a030000d51f00c03001c0e658400001512070340d08000c000c035040401880b952006140c02803070107106401c03820454104501590002e401000780540082c0540d606940d60380e2401a0320304100d0881d44002e41c8207034804409010306400d64410001000a607080d161160f0702d80000d1403c480010348005d405900101055a16920907813140c0e400c244038a05041c81c1035000e070a28030440d8041030003511484d031882181e10461400348107a00c032445030701014084541c600000030b5155010340c4580 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 193244217 1250 193242967 193242983
    0xc080609091603050a051504080f1c0c110105070f090b09040f020a110f0a0206030a0b040e010608100f05010b03010501051c05040c0302010810080d0c02040207050102030c030601090f05030a 83
    0x89a240c0c507060044103000c0c12a010690803030340c0d880c213000341d440c0d4625000b0b0b50240240c1500c0e000c94024000b99500c519007081420b850000141032140103588040c00a100d183e00803081400850114080c0a0000b400d03951030300441e090325200751b801c55102410a03001e11602d020340d840c11a41090b941011141c0c03004206031a414902d010a01401c44054040c0c4103500c00a040c001250b00401219980814501198900b0344004520340da28071202502075402501400082c064002d207410a500b10080030f400030508002d6041d255082d103110360400c0780c20b500a6411281000d08a2141c1c0070408800601801154501300895455104c10f00a0381c0c100600050f400d219040404444610704446410800884c903142c10700302c0000286002c100e0029006070040740d80f070720318a8881003d45001101611a24030b910805a4050794241d030102d0f0025002d02080010a00a101441c1b24035402c5121603582e01e000c20004007800143d8200c05150040e095081c4840d0700c001815a134103640c0010780d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 193245467 1250 193244217 193244221
    0x1a07050138030c0414090607020c150304060b03060103030908100b0d02040c051608070b060301090309091505090a0501080f150403121415031b011403072304050109090c080609 77
    0x860300b001d40240c0f1207070b0400d017000072141c05424807400b0070740f081038050280ea025441c0c20600300d0300e458850500a80c444100c54081640c414920001c50300a03109050000e0031080000c007081c14400b0036441500450200041046540414840810101120001040810f91030700c0010080b0108070b501034002d40d5196502c208042c014802c48002c07480e001400c2c00c50440701e15002d0920751005004035100341100021901c942814043c0248640e81034a07491201c0b4240a8404000c01042c07150110f02462054002119255034407124090b07800d0081c04aa92340c1003e08052425074000c1805a0311760004030780a0386418403607522900b043c1d0614040e00c000c1040710704200a00b8001c4078030a00454045d0034032842506036442540040e000f5800d541d405942c0c1802040c0c604482c5102c43e000c6280300502c600358103001c0c4000c60b031002240c01c002c3d1281c00400c40c1c0c0955403210075030b030f00101c1a001034103002542e08295840c0081c142e920062008003103030b8100501c1424090041070244085c180 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 193246717 1250 193245467 193245469
    0x70303021f020913060906050f0d060b061e041403070303052218021206150403300c03090806190203100302120d0e100816091a07050138 60
    0x110b40c0720520041013404e034400d049401308018003c1c0e228501001340780c10310008490078004000d1010400042c01c499940c00c46480d030b940981070418101d944901c04011030442520a41e1244040b503d401b070065480d541010700e4507080210480c9141d100340d02c800003c0000030f9100c1c0032160259004802c18222042e20341520007081040c0e004080040281c8074400304158907035020f031a18040c140360080041d00c4240c140102081d50b00c810791600101007100b8808541d05102c038220144100742008007003050a054090300366149010080054441040e40c02455441801d00014200326800340805080c02c00002c035140c0c0010005030502c580100c001030100300410000f030011500545084514541883c2540d00c442014050fa0042410740602140d04e040105c112011100b041c1c0b01c00c1410b468156025090b02200240c1c401040003c3c000410301e41c2503080394801607100140d0180e1039030507500d0714501303494140f25002c401c46001441402c1c00701091010b001200c499030400003000310110 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 193247967 1250 193246717 193246721
    0x30307080d090b0403030c08070903020a0b0703020312090105090d05030903030402100e03070e16020c0f0f0a03080a050910172a03010b03010510020303010602070515040302030f150108070303021f 86
    0x8090a04003050b010013080c0764143e0042082070001d5565070960b40e8400320142e13900c401c140800b03900040c0d10001408100c545d400100350160007070045074100902d01c5506000e5400c110b50940043c1d440b038003840800413040000b8541d00b001800e0150031803914960841da0b83c0002003003e0320403441d0000e4040d0701030252541102d06d450150540b03544680301d03c0f4100c030620055071401c610440e101240e40c4050b00c0480d0394400c0d000001c191060600102c400c00c0900b100c842c1000303030301c0100980008005080707580105428002d585030b15131155405000c000407040040201820300600414460600104000c880e510140000c20b40310a5610a1031101141d0808841c41d280c001c0004004113070002e0383d1014504a071012a403c0d51400e04c8064220780b28002841030001591103060f00f8003080c90300d59241c20465251400c01820b2070b0350381d000a841d0500c8420307005102d8100310303914440c02c0e805c070001501500e903d01c01003101601d10354000755614440e03c030301385918034851040d1099074496 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 193249217 1250 193247967 193247981
    0x20411040504051806010512101d070e0a0c091401081b0a113c1c0315090e1902030307021203030a0c02150c0d110a09030b100302030307080d 62
    0x340c010480c61801c926005441052134051030340c40c0c4604000010305280044640c0c0e00381c014000a0840482a0300039500940789021001c2031a48807001149a2090f04000540040404803509000c0e42440300c24101190445024001000203241003880000f081055030301940f032080ca02180c1564814111602c0540f40d180c3c6c01c00000e8002881404150344125800302d002c2c0d007181074402d416044140799521480072003e214404410080c442d11580804240d082014070305420344615900520350608030942c202c078000c2c0440c2c0c0e100d110404500d492080c40b4064010000c0030420320104c003804640e40c0c03840c1503a0948110140441c07030110349050040e1020360781d01401c0c2a85000030060040c0e12508110b40c1c100b00c4071315011070305a003d4400540c0700c0303c400c10b02c0b106941c25103440c100c03401c856200c40f000491070b40c1c541c500b28a00e599500020200d660b1a55248032416086203006001c601001c1d1400c8940000d560091016036000301c21100740551100750b80f682c9502c2e25591501400c45 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 193250467 1250 193249217 193249219
    0x315121115070b0108030a081f0e0a0c08090a03080109020a23040e0a1503140f0610060315050315041b030f020a0801050709030b0a14240d08070204110405 68
    0x81c116110410081140151080c944142644a6140c0e2103c0d40d156480c0103241c0e440e000149901c005c41c0303204000c200018880d200354800c0350b200e40c0d203803603006001080075526030a8166984101c401c0032544001d00030b410843c036101500c0d1a000d03584009140c3c10040c05000710361a40050241d6840d03008a00c103120011000c00d40070100b2442c3e50010091350424031940b0b501807402000611082d00c24414070710b0360141a41300c041c0081c2542c80d1200c004800c0c0d028101035108980d07210707d0f641d41c00c10601c0e100c0c1200010064000b03007404e900138180c501c1c580c0024090012140b00740200e41e400702d9128003055a91404100a54031030800d0070000100144020340204541e10101c10b1240c000382d0000c0d074600a03200400c034207603121826400c0f100c00329403010029003654814000908440301040d044004000041598400c440b50201e02240070786078040e1000890300e00c0c122070120080c481040c50000c42e203140c01202184c41c0c1d4030861003005402031080e503558180700340c5d0781c1400058030050b000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 193251717 1250 193250467 193250479
    0xf090a02031302040f0218060708120606070b15010f020708030313050a020d0c091a030d030b0a08011401050306010603052724090708010203011406091f0801030309050103151211 78
    0x141d0704004070700950201040305001e480d00391f40c803240d900b0584101d4071030681c401d03441c40c07074041e0100b40d44418036009007007036602074420000b00010034107800c5150b0145e00a03003d8100103041d03090001d0003003491040f0440940d00b15030400c00101c4804402e032640503450303c0c4085424407941c80c1ca03a00b014840d410095100c0305002544090203242c680c0c801c2034414407101001011251060352061400080c5016456031100511240003807181c0c204030019903021380804902e503145d0000500751402c424001201d013000000410080c6001c004250040c01c0c5c500302002a4107005512040107041500d14002080e00078155003141c00c810450f00d040b0090040c42aa40084da0752030158a500c4117a0741c80625214480f0007080e014030600c00c6a0483c2c03000942249000406402d00400c0c0e000308001d560b0200c0044001107a0124544c4045404846d0fa40d5540e00356042d854040c00c59226500658101440e02d0080d030581c00c2d10140c048243d819028030380410484078503000600c0d4018006040d0044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 193252967 1250 193251717 193251731
    0xc180e04080c061e01120c050120030406170a02130b0f0c0111040302030c030d0806150d05040809011209030c021216080c030709090f02100215090a03030b0f090a0203130204 76
    0x1303082d80b80564803400d01c0c01000c902a40d0703840b041417070100d4504029103c0d241104040140d50701410b40c5200e102c1032806407151040c11080742d10f045401507440440441c00d81c0960b243d2541c3d10380282540002c113100114203010802c10402c05e445010b010362050940000380001c111116542610400e542c490003d100055541c05120304d25040303031204038000d00c00c1201c00381c468900841e00e441003250981c2e41481ca5910360080141c0e01c400d4071801c032040c0c0010068129070510382e01442e4400c502840d40e450381d400c240000146030000b030003600a0407900d4103003003c0002c0d9010041c260304980441320360352401c1858030000d04107140300b600349400601081001a000c0c4010618100300702089055440f483e030744550f02403e4404801c002040c6801e040d111600503c1d05142c000c04a4a052046624001280140380d5400c6000c0c1c604200550019004030105a810b02818441b04000c2d80d03442005007a54012074809407029004401843c1c000c400100d6140410002c10006900140706100e00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 193254217 1250 193252967 193252981
    0xd020403030c021f02060a0c0507080c03121003110103090303020c0105040b010905070207080709150e0c03090106140904062a03060f06020f1b130f0f0c180e04080c06 73
    0xb008610108a001d60001e500b000942600405800c0e0039400e950043d210a0b91032840c800c00510304054640140314050141401049040c005080001059030041d90390b042c898201a1803520010030340c10014502e0700c81400060001c060140b00c120007824046800b050514080d00a40078035175180c0700561034181000103003c48041201d0403600741040070000c07615009022030303ca81c40350041440540c00031130100103828a6034000810055403070309070b4805035100c8540c084d1a80040d161200001808414400071039000c1c803c1400510040b030740360b244000100c0205101c640004c1c0301800c0240e49010344003a8000082c0c00800c840100308400d1114010b1005c098010710140c040c02000c10001c0c1d001288080c00010300b1102900c803507004003010070b0604600c5085004001070701d0b82251f01c4000313101c00a8014000e0711801d4001c5040401c030f0701d041c9060074089071a207810b402c0030400d400240c0640741c1e800246010a58083c0301d40c00050b50f0315800d00100320700c550b0b0b211000c00e100d070388200000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 193255467 1250 193254217 193254227
    0x31206010918050406110c0705061c180c0506070b01060809010f020307021509070302180415020f210f06040b040b090a050106020609070303080c09010c12030f1503050c04110d02040303 81
    0x100d030740700d1a01041300c101c08064180e061f001c0c7d126281805d5001d40c000744068030788400a4540c0081c182c021030344c45420300c43ca100580e0320316180c4d1110318015a80d078804208540203d4000f604040d1950350030243c1070b0b2109460030700188943c4017408420300c0403c01e105001e42110842481d035410942d928180800001e60b248108440c0c04403a000460104002c42070210300c850441c1d40003013184203003a0b011011600b078440b0213002100c040112541e0b2026000441c00a0b058480c407512040b911010310a0000560038070070030501e505690f5510801002c08d031004041034100c4401d032000144440341e04003250081c2414079282e54400349003020801c3c1c44480342c0203d03058070403030760a035107c68543c00e825660b1744c1300074003005011500d10302c0040c1035a046040604000d840515040344804c495454402d1400a6072414400280d00c0c2c0c408000300d00c1c014020404440010684881e5071450760f15150744400542d4a41b40c42640c44c0e0001c0c201626240301a42d1000d000480119941e07075407449d010700 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 193256717 1250 193255467 193255471
    0x1b06070f0909060e0103390504061706040311010f0f0207020a06050315100306271d0c060f270420121f0605040801110c03120601091805 60
    0x29240c10380840c005205008410071250180c035403c07402d0342141d0352107034414882d520810360040d0b2074040702c91445480c2c0740c9140c0105031f0039904244030304010502058170200e41242e905c001b0b0308031010034498800642168015054034217582d00781d1034003092501502860098414081c2800310a40f0b401301281c1c0184611442181c01a080c0c55443d201511701d40002c450056100c03510b804441602d0428802d600b00300d50b920b140020b1015165109011204004154060080d880c62501145007a03144104440143d447c4501c80402080855240d5200c140401a901411000c12254880e00c449415241280b0340c6136548130703002c1c2c0d400000c3c2e11120680e8128510450818105079880c20781d13a40c120300b541818000140c80c0c00c41d01c0b401d042c060703000502841c0404520001d00381c01c5e140c104203413101609256031017039034031860200e0302d81c00e40b26002241da100c0740003003004402c4650000121003001122182180050b42c80c40b0058681c903000f9400701140d1613044499614900c0706501c868 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 193257967 1250 193256717 193256747
    0x30c0c1305010806010b180a081f06050f220504050a051002030f040f0507240806060910110307060f290f21010e0a030809060c030601051b0607 63
    0x1100c94614040001900c000384240b43e40c6400450040c0f140c80040002005890080d035100c10483c070480e008101016a20340c402c000c0d40c2c128107002d502c07146202c0d90204090301d100c00705104281c2008001036041494092003445050100300e520800c0468a2651004404c0c80908101e01d20b00b600b441a1140c0707085104032094040c60841c000c48405c1b0b4401d607030041514400c1e8403850380c0c072076480100200015206640d00d115106c0009a1108002d541c4603c3c0000022112100d040d154006000040701a1003607204040c2808114515280c8070b0311381c90b42c44564685100b6003484030300b501e41184104000600a181844650542d40b825038212003d8080c0a1445140c0d0340340d049441c40d903c101d00847c0c1c99011408549565a91510403522440c02d0340034404541e203061002142801c580b0710107040305160304405110781c00d064108440030380c0004086c2c003a01880ca001145401980f20003801c040c180000407466003620841030b10841410030100e003c80c0c1c085c2c1003c136800f500b07456040c03001d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 193259217 1250 193257967 193257979
    0x3020a0f080408120412140a06060308040815010302030c0603101701021213020109050603060301020d09060504121425080c010e12070b0a09030318080309010522030c020a08030c0c 79
    0x144c01c955441400c031021500d02500c000f0004803943e48690464001543d028038900c10121b00c600810070900c00c2000171071254003041c1e40c480c540b80340c0301e00780314460155064a070242001040561404501200c40c030703400b00c903107a80e281d0701e892011401510603003050a4a0511404103080e8240550041c0b85040c40071070303180c0044d92810301c59000c40c498880020300003880c05004000c076040007805145c01c400018005030030036100c00004400c4900d2820140c400503100d1041c4014443c0c80d01c2403400d1440e0903c3c003411110903480307400016102d10340742410364503540a9442501d840b0411b44c42101e5500c0340d010b668411154480a010b0010080c041e40e46000b080801c294503c01d820448019a611a070707502000c0e40d8440e4460010300c4000c0b01038040c951205189038a082d0301a1216641034480c0d20071645a007071208901c3c2c00c48500600600020202d0401d07954680c61102060741c0850340740c9008080070f600c600c04602d5450032070344584814030012420302007030b0364040390a48a0010980f46 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 193260467 1250 193259217 193259233
    0xc03070209060a0305031902070b180a0503010203101208070b0414010c110703140102070c0e07030f06030c050f01020f01060f031707030905100201090503030a02090f031204090903020a0f080408 85
    0x4000c10308a9130b100041c02940304011952090301e68410205260403a030064414190795002c248400b5803000300580f941300c2070760000c00481c2c0f40c8407a600c1c010b031001f0380003141180742800008a80c80028000c0b00401c02d40300200100f000b104070100c0b84080e40c00b11f4031082500740f40c45c041c030381450f60110300c454039420050300100300c6110720781c0900d05001c82030041000614540311841480495500d968095400b00441d10105582e03008560080c1500c82c6040094a411000103007225400c5180030003484c100320b0104041000c100442090313410440b901c060a80803900140d141c240c60070040003965003000301c009120f80c0400e581c0b0045902521002d41a581a1240558248250312009000c50315945c410300490400002c0741116000d2800001039135045034484a103180c000700c49c218480713500003e151410381040786a0410400c4190002c12511611024031030690145002e4540d0b26551020030200b41031013082244035031604580c41c0c0d591b001141c14055410f41c01401102001d11403030703c1c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 193261717 1250 193260467 193260469
    0x4030c090c030911010c0302190b0405100b010c0809040f050f01060212090a0621050103081b030901170a0f020d0914072d17060106020106050102010207081206150c0307020906 77
    0x941103ea80d030003624440420a0040151000410088207504501c2500701750046d200050344d444542a014050a0b8201e20b0b007072070a01d140000040501c541141040c0d8060801d1342c21995000005a01c01c12254403414014007181c020141140f140300e449041a0901c40503040c000d6605050740e19075802d40311407104080d648601c42c440c0300304542e0401c7d42080104210352181c203072005140f007105058960f80341003520b50030940c0c000b81c0040da80d0403030002d521082c0c41201d0010b81c0d400c1e0a0913000c0c60410300101e001904030b043c00310200302000349502c00209030604e2640001882d0303008000c11501c401c0690108001000c11047c1210030310580348480c2d1646400040440c02c90f825401885030b05580341220a05c62881066204a98460002e0105416015114a040300c01e50b8034010041985400c0c3c0007800d48802d540603c1c1903901c10003034400410904400c844010045030000d00351611544003042050103549141621181c2c0410307c0f845080e008002000c205008031414005511107078 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 193262967 1250 193261717 193261721
    0x1a01090b0a0e0d0503091302121003120f09050d08030402031519090f060e01090c270b060d021210050316060e0a03051906051b0406050f0f04030c090c03 67
    0x206000c900c005480e00d800c0e14103103c2580605106209407030600c0158000f15459520700c04a83d0400ca07008214400400d140344800c99005e6002803580e02c1d950318540f2000f40305800148103034100300301c3d10034001502e4040c0505200408000c1d10401c1800d03414113018503680c0080d2802c0b40300f405000f00141c800c45040c030b441401004100d1510440c8034008020300000e26409804450000c14003911038085030b454443c514024070014008104900c2c14608a0542001030700030195100018140f11064513101074003ca12880d104000103131903214200041050040e494100300c3c00d400090319820359131042c00610300039811107001e8020540c55100b01611070000341c0f8400c40f51a1455030800500b44110800e4104c2c41010307060442580c5c5079202c003410007500071072108041c500d00031040200540d070320516511042801300c50100c4400c000c8a09003511840c071843c0200b00000c251503020401070011100400c185100c1300d903440d0b64070f240c502c4030103405201d81100c075440c3c1041240014080c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 193264217 1250 193262967 193262977
    0x70504020414010c060f090803090c040e030406030e0c040603050f0f010204121106130e0919050a0201050702032410060201020a020706030e0c06030f101e0306020d0e011a01090b 78
    0x2600380b2a80500450044401221064003503880d10380300c0d006083d403801c0302c0c81000c110a025104a03070780e03460406009840c0100a014450080b441e01984000c903a5010040e1416500c0504c1c01080004050031b44c1440c0c0036188604075845494010300000700000003c410501c441c440082d11f00304822040014201e02491050002081141403842c0008000030080c5100c0f090050505003882c004500044003080d454100d0518a10880c2c144101c0441c1008001030a0032185c1c03004801c0181d581d90551910703203401c0001d0500c0004188902103660034425a2041c0c0108020108500b41d402144c0c3c600c0704003034400140300704440c4404a075480c4180215a514000c6030000e00d5040d18200dc21802032204540c060042d0040041e0541682c1d981070003140995400401c174144d0782002905405003651940c0318801c002658031542c85109840300c10795040765040ba00058580c1413412280c4040c02048040040c03d51810620800242e00d110050384108401e80e0382c00007158071000c0a446038810 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 193265467 1250 193264217 193264229
    0x100515040615121104150806090a060b040b070203010e030304030c030f0f2f0d0e040e060f011a1608030709140f0607080c010212010311030a120e010e060a0f020705040204 75
    0x143c0b03900c04880840f1900146650143c15007060301e03069642c502d0705c5600700409000400903c40d2014404185000030030340340c214403241d00c10004245042c018030b070706100340d100d600300e0b08902080820030f669080d03018082c41075000c41038903544d10f07161900511200c214001140400c8100350300344803540c812131600360704001d10340312001004090051090011030140c01010300d6100344503c00c2081006020f01d0b034040300c40752190108000000c0801c02944d0a40c44c08024543c09901000804e5001c111144d044402d410070800d401c42e1540c41090240c82404039003092015103100c20820810780100235031180030315640f001e45180d141c8103540700412002c030015a01424056400f5040d2400c0002040010302c98051945800c1b4001d05035400d80e0800301c10f42800c10072070300040050042980e46060000401c4020b0b01c404622541d5600403080d00342010010444510010a100e0f4026002e04c00c640a00408c030030b0f00c3c1c00000e4070041c06191942103890050061100010311402c003402958140d40c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 193266717 1250 193265467 193265477
    0x408070e1f062102130504051b03010b0f0705190201110a23100c0c1203020901120504060b040603050c03070f0e01052403010306090309081501051002100515040615 72
    0x101d454021503d81d10f0904003404045031480c0b00f00c0b80010188000c203000008100304a4245180408100494100420005409140c2400c1c00d6624169504403030550314604641610340708c2c01c110a0400d4042d2420013450707031240c8072960034082e0109024510062007640d502c050b090b55090615150002444000c1c41d008000111480c1c1007180d4080220f006c0d44c440440304501d10503140a026280441d280c1008100d40d0102d00007408035000420030722100c0e5040642c50070b02d50740c00013040001c01e050f03104c07900307903854010a00b0441230b80c20081503000002c006008080e184d0a245440b5804540d440c0c2c0304c6e100340e90b0001451343e49481d0650881d900301c0c0300360001c0d0303103002c0a200c1c10410000107840080050b550b009440c2800c0c8014601950260740002045151458050800e03c4c0d03542024889510035803084000d405280c5030035043d15801d945d03401c9840f005243c00e915004038001004c4060b400c003070400107940c0303c407500000402e20488090095551f9140c4600102d0071000100000413 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 193267967 1250 193266717 193266719
    0x18070501030209060705100c0e010207080c130b030d0305010905090c060d020306010c390503061f081e010501141005070f0f080a020f070b121b0408070e1f 68
    0x3602079800f0307100e90180a010107240c0303041940e5090401c4101d42409004903030307446003108142c0d401007202080110a000404a1509141140c0e41d600f01c0203a90602c900d88400300748a290701c0b1500302461111020b003c0740c820310745041014026007000d0007034100360f40c82c6c8000161001d00020307007610800d4024211740c0c0350011802d0030350041d40c402016241030011800e24840000e10031480c5041c01d03190400c030120300700ba00c010000001102070001800002c6811828400e40d40d000c07911940100503150a4a86d0004a10412070700a50583c06401b5601034640700345003d080c9103030a030300a81c5082c4020030181c0c2c0c0382e0110344a0240e0101d4515000b80105003590110f6010700024031301c0502030505142049415510100c4401071042d040350100e20220740c91504039010440f4a01c1e049844003c0d28002d0f050000000481c0950040c8900c1c07240500301240c00c005482c03e2541f104a00460480e66954940034180d5458a192040d006803103050000516944103400c41c00d09640b80c4031200c05a00c1b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 193269217 1250 193267967 193267969
    0x6050c0316031829010b040e0c03040b13020310020a0302042607030308130203120705060609010315020a03060e0c13060e060d1e0e0616080408250501180209180705 72
    0xf04c008910007807007051448402926070340c0f094034014000c110790344015a64500300004004d480c10007800c0048004014014040000d14000a00d980b15403103c10703c040c0300c82c0b2400040d14002c0c6910280720103038400544502d409038983c008000340c9048245901d5185902c200f244840c0400720a1f0001d117402040c403e00000f031154035050b402c0200c8825410340c0c00020307000a400d0240e1520401403003500000c1c02e50801c203003440a954808012222500190724645403408545121050400260343c00504480b000340030743d01c180082e100c0419a580146048500980158094100c0c203500885200000440c4d5200700c0c0007014008020f05140d0500c800c0d82d140d0300180107604a480c5201d0340400480c801041c851080407501c042d004004c040509004000aa121103583d14550421100004100c041410882144c16013022a81990000c104282ca203006401d41054020041c0d400c04881581d00c0344900c84000743c1174000c881c4942c05494201030703041e41c002c0381100507110ba00440010012 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 193270467 1250 193269217 193269233
    0x201090f0c141203180303210a0b090f0412230405181302010302070606031208040c120b0c09010c02030a1208070903031d2101050a0c0302160605090a06050c03160318 73
    0xe030b4201a0032242088d081c0007581140807011641c05508400c1d1000b08000c54480b0300a1801141c1e00b40c0b422000790034039500d6940c8034140180042c04504003010900740491040c40040c070080c0c40f42d200703c0038105020b040544980d2040c0702e010300c2074101c074141c0e0403100b09000481c1d0080d01c800c80305d10300101859005401940190000755206c85d90b0b11400000b01d40c15038540f9a800a00d80e891b00c1042c5440d142098040c1203540207014491520100140044c84014541d500100c405070a55290200107004031000780c102c2ca8001d4250217080c1101d020002c8202d0a040b215426441d2401a45d41d8000215421007591101900007142901c0c61101210180702c1c128808201900d100041d00400c4032100c0138048034201c142441c0e55030005c0040100c4503105409620070286015858100d03001b82445d40720680c0c090107005143c2c0c4030003103021000c0800480701c401d603208105014a150010078907245410443d1841d020000303004814a002d4030038480c6011410070066030080c043e29503240d0840b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 193271717 1250 193270467 193270507
    0x200303091e010903080d0518030f09040905160605032a04030f050f06070f02071d010b0307020f0604030e0423011406040b0d0c0f050c0d0509010201090f0c141203 71
    0x8103001403d0808004650007034010014480c92142c04203890402d6101205070074020811039265410038054086503090b1301c4105d880f14501114040340c2c481444c2402070a240202441e05000980e0a00008000d50440d000c0c51103034950301c1d00c20241c49020131040d00c1102d0502042000000c0401051001030b0303046c118124650300510481300c10031003403400589845010780c0d0034070114034000d1041e0a4144c6c10000e050103000790031038410b848216006079171005981800b40e0050000d012000402c0c1610030441207192840385011503450b4109414081d083c120759028940c059410065843e41e204030142031080d8001c25015020307020f80ca047c490140b9104940e84495010008100008040340c400d0701402c9400d24469000880d100000d00140280308001c449a040c000c040c010b5820507640800d02c20350000c02c84c184103a0710194075004034011700c00103200a0038110307105042400d1026000080064a091590350000e0700f400f40b003045550914000d0030f0019070b0003000b41001201500c10008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 193272967 1250 193271717 193271719
    0x10c0303050a0905070e1801180305070302030f0703050904050a0b0f060a0e0603100e0108071a07061404120206180a110114030a0b030d050901020c041a0a03200303091e 74
    0x290003e0103580751420843c880e40b04000b90804032044c8141d413071f8505041c0691521400080000302c0040c0301c201808241060040c051020102c0c1000030305000707004981100e44484040d558a444518018085400810b2082d010b20701c0d12001407081900e51041281000c070003400320b522003c6006c20003480b684480c2400d0308001d138030100010a5203522000d58050b54118400480c81030602200b80f10030340c0c0503841000355501000d41001662016401e52111901802e0495924802401c0141c0607140912502071482101c800300000e0268500382801000f40710b50a48209864180800b250740500381c00480d01c1e038200071030680010702c004034098071220b410b0518148454407404c0042c86034001300c81c84403a203916100d200781c45103818400d000070300b251414000d08168144000039603c1c01c083c241c01d80030315919200c40e514440c034141e8280c01400000d20200003203490b4540001c0040321090031280d4601c2c041c1b142c03640780c540032054900c0780300c000d80a82c0d04a0120405550000d020b55052 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 193274217 1250 193272967 193272971
    0x72003010b030102280e010504030f1a01030614010b180402030603010e06041202010b03030a091e150f030b090f0705220609170114011701060509040c0501110a02010c0303050a 77
    0x81c08440d102800900703000b020b0301a45c070494040503600d03c0c0543d400300e140003041040c0034060030090b03a044801c0d203007603d801c0340d0b070547c1d2540301c1d207001d44441d1040f440100b1904144030001040015981100315200c03030141303040400740da032082868258020b0300d0120509140f40040d810403801c0550207143c0c08040200081003d09141c1c800e58180281070b107050308c240301c2d4250f0020750507409019068031351000343c005519050300341c0001000908603000d441c0124403003180c0900003002c1c100480c4054122a20940718118507031303401401101624400101007414402d020016141162400e445080034100000c461341c2d0b6800111116070101000b03000a0840000400800c3c8141c003140001c1d0415481e2400d11078102a031940014001d240d681d80503a06002c00c1c801d034840b000d01c5150440e1307400175040070042035a1121a01420154202d9030b048440035042009020710209a401114400c0c0c07280c01c6046240c980041e2034008050b0042c1c0403036103804c28035000900c254809a404807000c440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 193275467 1250 193274217 193274231
    0x806041e06060c020315061e01020a050f012003010b0f130e01260307020307050915040213150215070815040903030f0b0a06020a11030307080301121707200301 70
    0x48500701c40c120b400100010700c1c0307081c518046080c00c100384050f003100900610310500c0d06070b0010b04070340c0c0c17071341084040b0440385652507103203900030880700e220380c1c3c0c5c002c098940c0307401c04405d098028100049401e1003e58298031481409580808490590f5000c2c440d0038a42441c81801c000603602c800010140c2052000c000a4400c14941001d03028003c0340d600102d6140700000300021500d03246140408130b4204001100059130001080c2c0100c490542c2c03003c04079650120102d0404581413103450b041400040c0001440102c000004180c502106400d0310001100500302da4420000070b10040400c01c100c04a85500e006120705c0350300101c020740811111407401c000c141501c0c54a80202c0119442e0100061041c0c41c07401000c5075203206480c0c109200f898600001e40c0e9520744d03040a404643c0321142840903850034000c645905401020035940c0b07503501d08000c910030000781002d880315040700644040089440040701c04c0c030351300100c0c0302060039070302840307407815000440919038950b5031411 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 193276717 1250 193275467 193275521
    0x201120b010813051203040f0506010b0f03370902100804020108070e040b040c080402181006080c0f031f06020307230106030507080a021e060304080703110106030f1208010501080604 80
    0xc5d0322451180b00c800758540249e02c2c01d64644981a00121a6041c05104110110040e8000e80380d00c80020000f050210309043e150808450043c032140b206514488582c0480c42ca80d604404500da209440d600007111b00c1313103005c4030071040a4038000d001034107010206000510640340c0181071100180005044400c68001a040743c00825010012402d030720208015031810000034049000b24004c401c1c2c26240c6101d210703a400c0e41c00e0042c0b409100360304010071440c500d813200303842840069051316aa0f90614a240400c0b6400c001640300e40e0031440741c0d0105020b4404815110840c0d03110902c80d2840c00c0032100341c2c4a400144aa1040d191740e1009d001001c20400c024080007001003001411001003140180301c03c41e14140010901c810b0b083c980407143e502c441044030350003600302c1082d503194001d51800b21150150310030042070365801c0860200c2480070522500c540c4911501d030020500b86101c0058800100920a00d4041044500003503170300d043c203030414286c000d404600e007410005844 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 193277967 1250 193276717 193276753
    0x221101508041406040203030d02130b0414031b011d030f061519030c0e07050c070605040501110a230a1b05040c0809030409090812070c0201120b01081305 68
    0x94160002810001c1440140300c1c44150f011a80200c52018043c00d103003580100765240300d21000e141001c0e5001816401e244890600310000d020090420b82e5500c1d5600880305450381d11416292090040d1560b50044191705058203001071010307103e6104e42c00650003154900c080030002c0710f405014421000000600a01043d03126086032005840c0c850b02d500c0501c4034911052000242000f0b08082c00d00c007040314100000304541203a0842142c980c2c1c5e00e04101d5440c0241e40504646206542c004940903070070034098810b440302a80c804619040440210380c1d2a640c3c0fa0002d4106400040450202001b6402d001d40e407607041c008607450810160b80d48058540c004013004004801110284800d04e054010301001c041540360218031403c00300d105030b48a11a074400c043c00d0390750326004c2c0c0081102a0040ea400b1001d148050040d910b8052000390030f094410804a001440205202d4a8140c0f144600702403e03d041c1e4400c011503441e009822920b60000da82a52684112001c0c440786080035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 193279217 1250 193277967 193277999
    0x4020a0201050108070f03080d0c02030f070b01090c1706090705090604030605151f051608120403090b04151103040512100e03091005090a09060605090310022110 71
    0xa90000030590b140c044e85a0401c0c86581006491100014080001c545040301b40c446450204000282403c04100203a286200d034009404498030007140312400d000314040518121100340006120342000766030100d82008590246580810700f44000c11203030b00380340603a16030142813420310310f1808000d88000b0721240c025600c1121820344910400900b42002c01000d01562002c3e10100300c034000d4890030002411607018a0010803e02044485d442c03c0b040e140d64400c1e07074002107644e6607120b000f0112480c0001c1200c0030b0b804910070301d1000513005480c3c0b080303500f101d400d003454002800d0030710342c106d4135446064104989440203000100309982c0f4071146069544800d0000d2994089030b0081400f83c6201d689c0d009400e810034040300405403241c01c40d465151724207143c243e40e1400414005280382109410242806140420202d003141d046001800c40c40001c078111208801100c420340c00341c0c804d000703e04032030230b02d01450540ca0510455006030440c0c2d0a0384c810713442c1743d00c48036440118030f14 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 193280467 1250 193279217 193279237
    0x804030f030e0405151c0503030402120a0b01180b01021203010b0d0207081b0f07030f08030601170a06051903020303040909140a05012702090106050d060f03150e06070e09060f0402 79
    0x3c01d90301036580e28041d00443e03c00c2500524003010b11911f40c940e540c40e408014000b90080c001c19160516a036001d11600308115030000c0d4002465071102e245400072155411340c03c03549803070700c1d0198a042d0300019650142d00400b0300001d182d42c0c00d0052200312508480c0305c1d0141d15400f03000030000680c04402522402e5080010700e00b4001d6800b1005140c42035010142c1e0154100c21818030118605a5400b014142c12680c0315590761074410040b03a20340000d03079030015131908810a0103905042a040780d0200d540841d0a240c2034140151504000040c520000754140e104120802c100c61094200502081c05400380401c0b03020b010100505240203004112100d035500d400340103102c902e5660010003602c10001c0f815200c01c070740c1d012030345040b0103000b1102841004030700d4a042c031403507805c14409000d0440440240c2039880c500b1510480004011030300c61800d240e0b502c2e032290f00006641d40b24802698500303801028020500c0141d80e00900183d4110a41e86501e24044e00c40340000d18540c0c031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 193281717 1250 193280467 193280491
    0x1b110307210326220b0f062d0405151e150c03070b10050a0b0717090d03030b031006060806090a06060c0308150a03030c0c0e040804030f030e0405 64
    0x31142c580200480b903210340307000344240107914001c07104258000c9240d12003410401e11080e007403041c0e4800b0141c4001c640050003822414100002a241e45040500424043d569010300c500701648003e4031034000d03410102140c0905009040c43d280c55040b8981240c100004907159101141c04603e041c1446440000d022007882060026420328820b08100420700b0700b07141d0301301403043c0441d5460340700e6a6000f0700351400840103c1c40742d04500441d0310091100a001c170039001c1d66400d000c9050340141d50217907003c003126030302c1c1c0d104201e1400856840c3c49005011001c00101170f903080c0d0040c10307502202c5405100d90200740341c0101083c807824003d030039181c441d6000f44c13070303d1803c00c5001c61000303265024460500c0d400708039840d0000203140c1e000da41801e0282907035448080c180b02291040c0d640d40c1d40543c0c0100c001082c55000301103101c030140a24009020107440d8401c000304c00c801546e005100c18401c000070004a800b98a140700c8083c468070340f68044c200700b07500103001d0300d20a50307020a0710a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 193282967 1250 193281717 193281779
    0x90415050c19020a021302090a090f061d0402150c3d0603051009020303090406271a0d05030d060603020406090603050411040b01050d020c010b0901061b110307 70
    0x199004850b20300c10b84540c402021120455404075080c0250340303102ea90340980100f820a41c5540301620314014200c1c04204002d54910001207030003600d600e2041c501c2000700020180e1071741d520300c40740da48183d401816100784030300d10b403000303041035484004c00380a280100004110819000300c1c4141114052030b40043e5a0701060a103400740c051440e04200a4a141c0b000800000d070000c11949090640350b50700154881031800403030305501c10413250a50052500c0c0010070705041ea49201d5041c58400c0c50b1050100c8811140329085a00c0c41d03100900d103810a1001622514000c91400001845a820b40782461401401942900d00c80d40080000c08e401160911240c1d41c8103550800521090be001e01c254103294a81408002e400411580500c3d111002c421860340903204a802c585000340e800c541d2800407100c598000d1510104840c402d907100c10002500324411596404c154410000c20741c845162640c441c0000002240c079a60540904e00c03001601c80744d0488000305046036050101186 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 193284217 1250 193282967 193282987
    0x130504060e0f07020a080c01090b0a0203070801050f030a1a180d02030d0b0402070b09060414010209010e1201061503020c0c010801051c03140c030301030501240603020c0712260a02030702090415050c 87
    0x4ad40c009250122241c03051041001c41d550040b041811030740107540c107100001c08100403a0508034020f034060076509044d41c0d07500d8920745901c0c070b19100f14002e004200c4115030400b100342d1107000c2a13941c500183c0c010b10044919480d681d015013144036008000616101843e40d0380c5084050403580c0300e10a4000030204400d102c0001e2601da08c0b28402d4000710300d80380345a8001781c01c010a81281d1405140200da2610020340254040000b42c4111109440c0c038511010000340654859140142140038120091505501031580c45040e44c000401461007404070418440b094002c4560035401c204103281a5039891600400174880c0c05400c0700599980d40c1035040481c02d6400c0c00d80180c0c101e40c1c40007918401050061602c00603200c041ca00541d417107407c60300c450b291401c613402104011482544140070003000c0380044005540b030101030689040c0c0c5904800c1140a105140000741c0c00c2000000014a010003032603602c44c0c8600414605a514415100c0840c0e208644000c0003c00c00166030000e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 193285467 1250 193284217 193284233
    0x100e1f02010b01171e130813060e1807030b19090e0f060c0301050114120a090201030506030a0804120507080303040303091b05030d08060d0203010c020102130504060e0f07020a080c0109 81
    0x7500c03913220300e10241d0800100381071540c6000408604010084404600200d5260085455003600700020944030103004440c40d0401c02c4520031440031400125600c0d02505040c000d406040c1c9008500300350617541c2c050305901500c03000d080181c1c804001410380d40900081550306011303201c0741c0340029110450141c0145003940288071000580d000b24108007014103214201c9054400038078200c0140b141340d50703800d242d60054034409040720b0500420010a26205e038014034070b650003660203201075102c1c8000c3c542c69220385400070700f4411702084140000c08084996200182c8103008840e03405680303030000c500716002540c085001989030a000024406801e01149c1a0903071481040c80d1a071602e00000c0c3d450206032200c500384090740b030008043d6a100c1000c0644660060b0090054100210009000b0350060100e41040c1400a0011542e41468891003082d5500d50540b22025241d200340145002c500038015421481084681c400244010700508205202c20f4000300f0509494070306044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 193286717 1250 193285467 193285487
    0x26010903032c0a030507030207080d0c0b1602071e030512090a080d080601120b03190303050a020a050d050a02041205060601030c031a0d03050f1b060c0405100e1f02010b01 75
    0x41c81014103031070700e41048011800822113549030504550702c601030b01d0140e0500e1099070000704240079010b0b59002d0560441c40d4a10700a2044a50004956402e51109001d030101d49100c0c2c0140e00c4a0300c1801900c04680c045103d008403200d01d034050070782e82d5440c28942005101102d109100c0482d994500b414603c030120098404800036000c110b60f840c41c01072140900904d01410000303100f1031600d040140340e009100580000d42911000811001d0103107800440c070b882100040d20f0640000c01036055842518280012541c4151404012031404400340034041c041c419050f03402c03c03002850510b00b130365880310380c1c1c8078101800091504070009400c0703540f081606400c0c142080089190b000c450781800c240c2c0541103480a4025410782000c40780360284481c8001c04400000b8400e0030200ca881035139020003569412100155a410340f068510300841c0b0034960004020002c001206000d040c06540bc0d41001c1e000306500503416202c42190703103000c980000580d5484254200c10359100d2040c030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 193287967 1250 193286717 193286771
    0xd1e0e06061005130906080604150507020706110705210c01080709030f0f0206030a0603170a02060403081b0a080103021e130e030705030a080f0f040b012601090303 72
    0x3200380c1c6001808038101000e0900c0301c400300180000d4802001c0409032651000d020903800412400c2e881302c00066030b603141982d00b5100325450900c0b0251903001707801801e00c9080c150b4040c0240e540b52a07030595401c036803d2244042c5011b1404041b4032500d07002901802500307190305001c40c00e90498466800c001d0941421810002c40800f003142607608070400104030303039001c620021a80c0d001e00745981d20058681000394058000000c3c00b52004482e00048107490080b100b107154040761101803107241c42030540e03007009030b0000710008011038000c02c0b4007588100c90441c000e084d81203203025440e655014048400210780f1050050040d401c00c42c030303c19030500c40280080c00c500e10720800038041140c00b09150a0150f150722000e503041000b030040c1c1c0c00c055404401c8984442c4105409808244215004860318058500044c1c0c50444014140d00460700300c0ac4000301e9900307120f4028000718008610210070724089103004402c000074411081c1490080e07900192521061808080c83d0300041515 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 193289217 1250 193287967 193287973
    0x1a040f0906050306010302010c1e0804140108010e060906311a030a1217012318070c020d020621060d08091e0603040501020c1903080402010f03020d1e0e 67
    0x502c401d480020340305040d290242030a00c10344046160102c692200350460703c61003e0810010420001610042c4c0242c40f02401c0c2c841c0001c601400450310b00741c0910440b042a4842d4021454904202c3c0b60300350000d00180406a407000341003500164000d44c4032507140030125442c00c8517000e043c03d204010007602100d29400384450800002030b69001e04030740281182140ea21050310301c501441d0541040103d000c800307241503030343d4140383c40015408103040c2d0030303101a010100c616103480340503400204482240032045440303c0070120b80354401d04200300c0e00003030380078000c0026a89200251003156021400810708001e628821030318401c000d01388034012494203900500184c006070681c1d0f0034010035100340c40b8005140408480a40c5440004e40d0070000c0082407006108040d001044034036656401c407440203101c94079110485d90359020150011f201c16021900643c0309070700b140008a0a89405414020050b007000100d0380b0300c0384d55000317010b5401361140241081d4010a401d003072188010f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 193290467 1250 193289217 193289219
    0x702030703032a210210090302011d0a0206031501120207062307170604020d020a050d060b03061804150203090c130e0d050313050106090b0906090c09060705071a040f0906 75
    0x16a4807004d0320b81c01a04000b59400d04500b031254401c104031661403550680c20f016000c01400c010b4020480301c1c8a10340403c000341480d80440f00006182420198003915091640c0d80f0454420311003651034100904000c8102c00d06140c088071400a000c2541c0103030030005206440702c010f000c440d141e0002c80d0080104000400036070715040800000100d22030002c0c1c2009039907100010703000b441100c6028080500c0402c50003812076010014014419550a082002c1a100d080003800c90108403030a40c1e003e00c039094071030540e00350b94031415000781c8601d03c8100c92103544080c0400b40e800031241c1c07408560103262a0501803034110002416504410b07020000306c3c00c104840c0c1e41700c07901c942c43d17002400400404142d0f03298a40e81040c0c0d442e83c11500070000c0c1a1159001d00140c07205040e0f50340301c0c030507440200b021450484840385c0a02c6803d07038454645414113080c0001604030f80410348550003413000020f21000c02051480c0350240c101c402541e6141800d1403040b01c1e01494000c080c1492402c08 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 193291717 1250 193290467 193290473
    0x8011401080607030902010309020a0b1213120c0201030b040e01021812030403030c0302071706070806040e150a150b07050124180204170601080c030a0201080c0f0702030703032a 78
    0x101c854018003c1d2901085402d01800168090700708010001d42000c001c000010f50702400c900944410000258214026103401000c80a403126060001d41540d00200004d0082070181c180800c0329407040c10701156290000c40010100c03580f0141c184826500018171661000e010124101c00b40b8040314403003281c900494820ba901d000b0790100405000b03000b032441c0306042c003c00040c801440e101d100604107408201209480e40d80940b200b5001c91310b140003150451425000780c11710f11400c00000c200101c071418000404c003801800d5201581c2d51a803440800d1040d04602030054504030311119542c041e02c1c0303019070840c0d688881d0407460003550500c035004041c61018040484090010076902c12055004000080c4100c0d40452a140c6d844201540108400311b80941260540c0c0180c904d80345d0000c2c14592101c1d00800001d0014508000169001e2051030142c440400e41c8007003e420200241d000c00c0c0f03031241641045e0040303510b59148200215601888110000c1c00d0101450030241c966 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 193292967 1250 193291717 193291723
    0x201140a121a060307021506060f030a0f020f0d0b150f1603020c100f020601050a06120e010207020904030c0c0515030103030f120501062c031c05090306010f0801140108 74
    0x14a4441d003548851046a541140380c40c484480000142520f03560b007000ca001135541c11801d2202c541a04500000810501c1c3c000241c8008449040c0306510310390b1141c515000401055006005903582800956000c96000c1e018002c100c00054002440040e01c0f0100020304103030203541d0440540c1089203150440410040c0c4a4814145190002d115090302d0286d040a00c20f0f900c450b0490055141581850b9000b81004441c51880d026201c43d030340ca40c418401c40d0100d50107503d006c592580589038010590303520649030b10412500041c100b4090f940002d10200c001c0c0c4050f000640d01c0d050b039005001c03d141c1a10004e140458803207514201400041109000520028052203040c184803210180a03886d410045801000700700100d45e1949005007802c40d4150031150840c0140703051030310380c07003044000072400c2c1c50080040ca41c110720760b041103051903003040d0382200b0072105004020854500b006598040e00c19121080401da0500580c107003162208040300f200d10781c0180040000c40004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 193294217 1250 193292967 193292987
    0xa0507050f0f1311030408191e0f0c02090103050102040501080109090201020c010e0123251a0c0c01060e0a14070f0302030a0b06070b07110706021213050303070c030201140a 76
    0x985800b095a540c5243d0031009000c00c1c0c40101002c0341c000204410828088003c0c071136a5080f0903030980741d00004104403102050072140302c003409011a101c5c02154010303601d842c0c44032242c0c5080d030301050596005c280494420b9200319580d0b034011800340100c0d070b0412a0a80900701c900001c00110f51a80c0000399610130b06207559040c0310119014080e182d00c01c14a014982080c0d840144403608041c07412001039000400c4121810701c9204c4403a00e180354505042c0071544c014001924141a0303050002000d00701920311002c00204000004c5c542c44280641d000400030b40c0c800102600c2d118081e001558151980c0702d0340368404504001505400c00d80b0f40c9039022052070011380ba40da031400544000e080c0d00501d16881203000c20b0b082c04020052841601c00c7c0111307030f90013003508180c5400b0b075a10100d40c00f0710000750300701c41d1240a0048008000c0d200e43c1c408404030016407580c50300468110b9015080c1502c5411440c2811b100359600060140b02035560810f00a16188625000034520380c4130b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 193295467 1250 193294217 193294219
    0x50105030619150815060f01051215040e0d0201061802040303050d0b0102120c0309041404030903060b010c0c08030a14090307030201030e12040f0e0106030204230a080f0a0507050f0f 80
    0x283e400d00e03103003102c40b070701150020302108030458200d800328038491100001d04440c054419501441941e0303036075104409940d01d00c90a601c4500c41c0d610b601011200461030340642c1904681d5440e80c495200c6000c00ca042c48198158000281c51410040c601120031400500545200c0c01048200000383c0e112080f2440c02244030300000f882d04030040100d050110076504042030010125a620003150044010800c40c002141c0400c646142e0604151546004a07030180c04601c100b031042000c1910340d000b101b410700052400d6a016941603170341e9800c81032981c020601c15031000c80c5012120b600442c1200300b4050914602e0308014051001a64a00c2d0a0000031304240c1c1340d05c090f0300184820400c4191524450100c55166038803800c1e082127520040c4900600140280b0000610500134800c680030358241e580484545407207260714048075051228040e0b001000e250f80010185070a200c3c40301800d0f489000790400c80c1d510f06040d0f1501e407a80e00f00300d201c0c1c07807500540c034259620060003100c8054 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 193296717 1250 193295467 193295471
    0x7030e03030c030f0405070e010b090405060301060f1203030b1801080105252d030209010f03090b040b060d0b04110307050301052e0b070507030b070c0f171c06060201050105030619 79
    0x5e96440e0490030300e1180d92000217424111000455035038580c402a180c80c0da8140d40400040e9141010142601e5540c4071f400a02041a0340900c4806c3d12000c070f5a01e0940a8180416026030b9000814008202e06003000071600202006104100b001e020341904a0507924014005003289181c600700e1130b41180003001480b03200544400c034001c58402d14410301c2c10b640d00c880381e44004580e000d0042e50001980500152000702c401c0d104500130700c100320f00c00c0d41268400a081e0740316aa141d41320784026060341c0c0d11610302c2101d070000440128645100c0d070b01c540d01c440e1354462404149480c15590750071151107a41810b00308228600300c0c0f8203002004000082e0307480d90010700ca410f40c0700301d5035179006525802c4001407440c00340f105c00034030601140d00c02c004030b80081d50b680d01c0407a00e404403000020702201e0303c0e0120b000030540c0408100b025080020b0030602d0b114035003102c01504140c40b460030910ba501c82e8010003690f1317028440d840c010582a0040c4ca01440d00040a80c4125000844481c02507 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 193297967 1250 193296717 193296721
    0xc050705221401030c0e040b0a0209010e03010e0c04051803090d061d0c130b0619020c0d030305060316030803040803100f0605070606060e061b0a060203040b07030e03030c030f 77
    0x840101080071009003044100b081c50099040001002001d0100351100034000c00001041480c01020510a503006608020a41c5980314020040d5006050290400c01c448803101041d0b5030030b01c999107090b05401d00818a50141d07101340001c2d44c00080801d80a0800c400701c0b50908040401198a4020212190748295520740303042c500400c50011001010302d5030300c01a00340e49000065410004400f110001c13030341c500101102090b1148414515000305092185424440104d402620207042c2801a513560100c140045100801c100c072003a80080d1b00c400070b0004500b0140400d2561003010900f69501031300b10388031602c05200150005000d50310010000b80c0d1155414161000f400705184480104c5a40340001040754005040c1030f50140d140c800b002903030a0007120a503200a0000e0103031414582c08a04624411000400b03040890042c8284800000d40c64030056104500c00d040c0a0018203001c6802400c440400400301500c0d4403c1060020a9100c2c0703090329401880c2032031040d106c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 193299217 1250 193297967 193297999
    0x30c0302160336031e0c0302010507021203220e010303020a170c01290d033609060812030c040905090309100306080111030610050906160809100c050705 67
    0x481040c1c900940600c81d44403c1c4525001c2582c00c07001201c1c001c0540d0300c200455105100003c20150100070120400301108100550282010740501c2d030004080c50040584480201e00f582d200001c44642c441c020303441d4482c40d002241420b0043c04003050040b50715819560040e56506400740098001c0d4642851140d6100c901d02c110b40a258082e030081c0300c569000d11340c02401c80340601d601d6000801445d00074a071b50400e030401c440019003650b1242c2025010401c094000e0010370b44210a518800107650341d406102d01861009010008002603001d144c80c26041c205a10600103412440007003040c055800200016242560b140d18000203064482c0b031050b03451841216007458001d04491941d201c040e425500a00440d00c52000030301004a80386c01080381c0d840202c0c0d06550214254804d80da0491149000d0294000080c11092625260710110040103600800458245000084030617550400c5c0c1642e031045402400e0481c00710401d40c0e509500d130111070081501440070b9000403100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 193300467 1250 193299217 193299257
    0x5130212060739151e0b041e02030a0204030204060b12070219080a0314130c0906030201020a110d140f0d0c020d020111010f1e05090625210b01030c03021603 69
    0x10220036441005084917111021074414480825512118501440c0f9441804c25001d130038200304900300740204031154802c80c84002c0d04040e14902d4210340c207001c0840180c48034858940604030480c42e068694200e0225203083c0300005200c41e0840d04001c0615424030040151a40c08031361007900c0c2621003e100c04224000d0606010b0206440003580c10300880250212185500a010700030019a03540c54860001c25101c042c480240141d01c203080c01000706903030408034465250018801112601c664943c0c120311103500248002a42219030099103400342003007c2142a0000c3c208406114002d4000540303542c094240030703050010206e003a8003500801e50018080000e950410050004180a0136a11007016021006840c0c076100200f00c0c04d900004403188295149171203940d1158005620048200b002002c0c0e0b010f101079054041c130412064140003502d100446000154a0034000004040c0c4001da110742c1c0606204003c886010140c441903525180c0c0c00d03061036100c207203918481e041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 193301717 1250 193300467 193300493
    0x804150203010e100603060b09040b0a030f080a110105060a0e0426120114062203060903050c060f040b012106090506040309060e03060a05130212060739 67
    0x200040c400000072a440c042030800c14000c0e14050300307510103692110800c1c1d0840b0f0040c000c1141100c014002041a8a4150003d443c003450203003507290141c0e07403a0f40310080c0403024101156220400306442210070b40c850490000c0442d00d01c000d00007404c0642c0800c0218a0600a203c1814140d50000c5c040c400c541c03c5c401c850842a549299003441120402c0c2c591750495440c40344540d204c2d0000084030603040a24800c0c26400411107481e100107641e400c400070f0a0041040d28003507441c0307800808100948203014409000e0384800369a541c0c3c100205051a000404054510003d074080c000850914603209040da00079045000c003c0c05042401a4591480d80000741a207083c04001030810101041c20703809a40b103611a58841521440b00340c5404a070149100d8141e44864001088070429820194004107525450800c07581036070042141c0503e264000000c40d88807406011445038800c0e01ca100050040552800c402d0202c8141003424200c40d003031442d84419810b0358414400c1d0603800c2d41c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 193302967 1250 193301717 193301753
    0x120516180f12050319090f0b0928030f08090f010c03020a060f06050604030807030810031e080706020706060602060901021305190b120907052b08130e1b040501020703030804 76
    0x10100e08480000801e039511b940501034400c1404c6600007181d40c40c0c98251b4907030000040044071030f5a0800701030021900c1c44d8440d000060005074000011480107040040c003140554901c5560302000e6081c00004034050411904205030f0304003800c0802d60200b440102c0c0c1c2c0d8481c03404118002c842c0600c0e80544141d80215500050005d000020405100014001e4504c65250241e0300c2d079400d40c01150306034403407101904001c04c60a02e4080304407045c1300751074041d04c20300e0460308110b01a181e00040740c02003407044680d01d550f02c80601016804001107544080004c000350720303210103003011800c2c891440c41072902aa09407107074820448082c8280c20041e05034107a00a45456034100f100500303640680ba10000340c001d0800228007803c05c107001d820b2032542c03005e03c0500602450744261840d03495910944042c0f0f018040c1822070008401c445c0300401000a09580381d05240c0d01480c018050b080004021520401003000166004070b001d02c1103c3e01420030141c0d42d0341d039007419060071405048903 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 193304217 1250 193302967 193302997
    0x31205040231060504050115050a0302040e0c070b0105030706050d020309070305370305030103080c0f16090b120c010f02100203040308090d020f060c0703120516180f120503 76
    0x1c03982c1d0048814104078040c01a050a000e240e684206100032281c0078080e840021541f17041005401e401000100340051062900501d001d42e40d1103a00c5c001d00080e42d003c2c8128500240311401d000000d14200d0240c4006c030090260245051400323000d0303205050946d1100c5401000048121344180040300003140c100d8203954140d0007803514029003103169404424034190315072a144042400403a588501941921107514503421030f140e07a07065400503464201075100d460741c1c85444460034800700205807600084505000e0030310400d0710541d41e0320340c4207d0254000c0d15502420040000d80038070005800e00341141c018200340000ca041c81003030710403a1541400002400200740d40f01000d284074810f824107803050b007000c0f14800c07601c40152610980c41a8469800315a80301e22035801003141c0c520a05204480d41e950240080540d801200c50514410030850b5906100d600301c1d41c2c403d41a891b90014840d40d50030142400d100141a01a111003410400ca8200410800b00111070520000d1126 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 193305467 1250 193304217 193304269
    0x4050901030f0203160509060405040f020a170705010201150e06030709050411010f0c1101030c0e040f051006050c0706030f0e0313060f09080604081615022101030312050402 76
    0x340110300c2c18150200d02a03c15003460b146036401c210400419240c0c020880e14440c5c60304010400a008040c0066600100c0740c80d00030010780d210000140140064030b07150b500c0c894401d84041c105070035503020034107590600c41c02c02031182030915607105592001200d201c0544403280403902d0300300c0740d8100c1741d00e9915050038401401010740700c0310720109091b07031340d56800040700100300c40180e10503078014030100c40d14560218a6004e500b00603001c2c41c0034504046107140101c009826501c000d00810020b642d01e0003801103400c070300c05494001c2c1190b030403d0b624012a05e5201907603418248245070825a5034a0350a4100000d0782002402d801c0b5041101e441e00004000f18664144501c64000410702d690044141c40f401440d44608455041d0060401981e481d01c0e6000d075907200d80002d40e03c500501000303c0001c0c414110003040000c4440300180c4555440071201310640c00c1d080101c07503020103240100b0000340e0210441030b50a424020105a945503031001c034050070454402c2d60341c0199980c003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 193306717 1250 193305467 193305473
    0x90a0c050426010609020a1b021c1a01050319030509010c150b0103060509010810110910080403080601021506100c0503042d030f080a0507051e010e07060801090c050405090103 77
    0xc2c034180440c29a00820100da5246101c02c2240b09139910030001c40c800001c001c50155150580341e82c800d0001e030145003d812050441c00703201540c40e038211641d1000641102a1840170b00481d400740c002034004203403000401e0340c4480d40078040d12000b41003200014644076107900c120b80c98030f50a9403140d1070001c0c205c0c03040c0e9164050005800d81c5030001c0e107007410011f014a0450701d514101e614100141032070000e4160a41c010b40344c464454110f001d0104650207194950301441c10240c0c41d103660320821400c003803070b0040441c2d4024009074119400802220000d44102c50b04542000c000c440b5a1b00042d140541561451822000501036010114000805145845e0700400e4502101450541c08291090082c4141a280005800500c0c41c2c0700c002d0004d2420700c010007c08401d42441c5041c12940d03918545004107803103807071000325600940080d0382d075024096400f040c0c00b0200507000b4941030000c020b0141d2030520030f80700d89a444082c822542402082120702400000e0031b000c03030541c0c5a007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 193307967 1250 193306717 193306769
    0x2070e0103031d01030b0105041517010306091e02010801060f201e1903050918040804090b030c010e010e04060803121b0a050403030c0212031206040605030c090a0c0504 74
    0x1c060300700d2403c108011101e0b0b58820711032101400f005844442c1058100700b009481e410314004047d060142d4804c81d00707003611465503014000e510800c3d000c62840d82c02e2401c21160410492918110481c214a207801030703070058001819111149413001c18992882011586003081540c3c0100028000011001555010410108a03882140c2405034107035240c50883e85d5103101004115041007100c50040001d210340000d000c401790017441641d403810640026840103600355001c95a054000800304042000ea002d002c0c44800200c01030043c0c9420700d0006401d0020801649041281c105240003e9564a43c080c1d40988560402c03207850311400745125554403015600c3d98040301004010240c144086800c4030100c1c240c55442d1400d161840c0e401303452001481904903444403502e80c9c020b4003042e0400103424001c3d410000c4c1020790400c441070204545281d08254040d03000b5000c14034468607291000c80d04a03140c550000b03403000c41c060b004c076018002c0d03070404081d2003051120310003070502c45 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 193309217 1250 193307967 193307987
    0x20d0218010f0f030503030406021b10020409050708190b060d09030c140d021507020312090c1206150d050c090705030a05071715010201150603020408070b0a0212030702070e010303 79
    0x151020041e81e03c0d02411205640a8030009205a00c100300007400270381190082d04200459a6100000c3d0469080780340c1090f05c0100c850100300e80c04641000f055506000f401d0b04289141014252070510b2900f0666281841d00d50415040e120504c000c6030b5101e1030102d5041c010102d108001e9282e1a2400401619243e2003d90b0a244558106100c600012074030480d65552a0000c0c640d0074914607006160000c000d08003010760005110840c4140c00d00e050003032080c070003400503040020000081010001d042d0260345200d500550030000003403c1c95591980c0120220380e884011801b42c50410700d4800b0181f0076079002540c0c0014040c52541140c00b440c010034034041c0c144180e030b44048003100d280302800010307507045001102240030440e5224800000c0a01032001152801602c06006440076407544040c000941c0042c3c10840c0102c2400002d001d0b19804e60501d140901c0048020b507103078450071103e50401000008104002d00802800300140751542020310f8035a503d0070060034407044 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 193310467 1250 193309217 193309229
    0xe010f0e210f03030c0412030e03070b0904050a0c09060302071b030f03120b100f030213170106080601050f040b03030c1009060605180c0d0e010f090c080a0f0b04020d021801 76
    0x2c0c859101080780c001100390b0780b08a40103c1d4242c1007500e081e0f000304200c40d0280041d010b200d020100c08006403070a01c03134035018080e4842c206590301203d206100440c0d500809542d883c0d45000d55015a0561042d50682122818503003da280d1000d03060a60161013142d10b46482280205070000c1000b0080b07098241c95030094070f801e80b00100311103800c4140d4001541c1e040d40845100806103110b0300600703d214400045107401401c01040324002030368100d050b0040d00c07138001c850840b03984080b402d000760405031200342c0141107035500d464080b407011038100310310a210b142c8580c81c0b040561810001c2e104008202d0b02101d1040704801101c000034102420107850700d900700407000c920b90800d10440d0719a80c40e803050080c000d42e10490b200c10141c01c810900c40803d6220360505141d60000d00a80000038510340340020149141c0c0b400c0c1c5180115544954a2a0050103104001c65141c00e8607074000e50b0420003000899855100080100a245030300035401000310a13034810309040d140c15681078a00d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 193311717 1250 193310467 193310473
    0x807080706080c0f030705180402070b090f0f190609170d0b060c100c0306050d11091812090a0f0e0f0a2702030a120503070f0e010e010f0e21 62
    0xf60709070070001a11441c903034900a10810004210720f140f2135801061110002c503002c44440c49420b00040036a800000103644d51080c420500c41c1e21345040c8003002c031081c0c00c40c0003000b00c5600031a1458852110401c40c0c0c224071042441130050010903008200425840240c40c00c900e1064503140c2d00f05c0e0031900c440c0c4442c1d4600242c80100381021812903000781c05400062074a9103041c19580b020f405202841420940c0f03588000078581c85102041400320b110b240c0718003a5114003414411030410080821140f142c10f510403000b21000820341d5841861500c0c001d5686080c0341c1d020071003082540d0701035030701c0d02c0c0004000500380d690380048501400070345127903656a0302d400c14a141a0b4140541100c41c1000031030b01c1d04807803455168503266480c03001d8261403007250981c0b14240208001041100070490010070800c00aa011808080d944e0740c1e41000100b0414900000f012500340310001814013400600c404050b030b02a490619091400a05024002d43c204100030380040700c90800d61403601c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 193312967 1250 193311717 193311721
    0x605040e0a02070c0311040f020a020705010806090f040f0f1a0103140a200a0f06050909100605030a020a17010b0a0e010201180b0601050f0a030227100305090106080708070608 77
    0x1001c1c90086488094021011034031160443d2100700c3c000c000c0c601082e82c0190389400d440107c0c5568005440410b905401502501d0314240016183c0e4a00070222446100b4160820001c41e10907a4140c1c0c0050704000c50108446407854420f13044200c216000c1c010391040e183c00e01c3c20b1007601821034180c900c2006464270712108006803541d10750f070001d401406541d440d012070310462031821824000c400000c0040c91496980d1811040c244d00b15048180040e0b070024001c40715041008074590040e81c04801c0003840b07072800000a149001c09072401e030140d6000079181111500c1060000d4008160103a82c8000c0d5035601c00c1110309a01c050000e40108402c081500301e59030040c440d2110010283e660400c401c081680c4114991310b0007002181404418032042003901301d040054940c00320309450040e961103400102002c42450b002c082201001d25a920f01ca00b07855556140d290070b01a4140031400d6194044064090041500b1510180c0306040c0b0005041500080746801c0711100e440b80d00d120317 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 193314217 1250 193312967 193312981
    0xc16050105010f170312070f02031605010621050304140105270111010b010c12050408160f0b070221011b050d0b0f0a0b03060109090f020c0f16260105010605040e 71
    0x20303006c0c0c2e418548645011500003914240980d18101a4070038034810380c0d2915180104826007400c1c01c680c140d0b081ea6643d2800d025002944009442141c21818500d84104440e0b4078107540e4410350064040340b0052180120091340100295040885d41d8845c0080e4696413030003038019030419005050010342d4103000003d8404040c0f18031a44600c040e0348004051000381c0382c0c007665246100c01340742009001c00c00043d001d0002c1c00080f202142150440c0c03403152500ca104140110190001c43c21400308010368801030f500e007041c410030580040c08000703645a1189041e40102524030030182c0e1500d10504401c0403503400320041c102102d220ba42000002c400708180001c2100d5205680e8100340d02900c24440d00807594007540c0d1101e01450140c29041e100c03c1104180e621810300348044540100b0114440340301400b1241c15241780070010520075003a6103540420034075902c03e0b8540440c007826103440c60b1031200f25240e00e40106900070300855941e04030040407580688070700c403210542c00c404a114 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 193315467 1250 193314217 193314223
    0x2030403021b060405100c0c0e07020f0708030f16060e010203070c0213090804030f1401020f071e03081801060803280f080a0c0c060609022703060c16050105010f17 72
    0x30340e403025248000000d40d2007070a03900340c07d000307200b96000403164000003104200c00c9000c62040040754041e160108100250501c0c006032500146016042840400c4605000102313803180034920000c03007130b010702d0682440c0008069a40b003080d05540000100010f20307030030480f08181d0302c0c4280c1d40021405001c1c29000100c5548200060502d0410402040032404001000c0f00b0940211501418003511281041c04c9034002d00d005200454041741c8030040c03040d00024010300308515062502040c1103a40e0040102038000d0400313420110507480d055120a0035407008018011090032641c0d1407007030000d0710400d52a071008101c25201188040036085100b032420901211071503c0e0107406441c0e480c020400340c14021301640400a203901120080390840c05000c00818400c0d00040c3e0b24078903003009100011211109209508511916034070544001490981c071031103040d0025140d84500080c03203071502c01400050540c0d8207110000c1003039601009200120741c031141c4684d01480c3c83c10f0322a80c1b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 193316717 1250 193315467 193315469
    0x102091801050906060703051201120b1f0b0c070305070f050406120809010f1e080403020606030d0c14120409020904290f030709021314040612110d020402030403021b0604 75
    0x900520200701103504d500705440a01203203482030424600344400104c0301c00072202c090b8450300e080c00414072010103000194120340d03041851503e45c165890210344035000c1070b40e124860344000031800969014030300b406202c001c0c091a480b400f51103203903654000c59403a0030320901803d4803641c50040000360842d018542c01906692089000b8281f61110006586103124000e0b4035090203142598456100419080914540381c940c541e251181010b04009140402c000c02550003640500f400307d6020f078008640d803440a5000d418032940d40900e01e051403d10a00040e40001d079140400d01160540300c50b0080d0400b0035085d2010001160429280702d801d50740c00103011443c100724a81c50040b410002c00e00180c3e00f201a045820700c0d5a80d94101049a10078040800c059884c40f1090141220443d142848400222014480a414415490040481480028080484c1002c555540c3d29960300d0410300b00e8004008644914150030042c1d01c66640494a074903032114880503608070300e88501510 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 193317967 1250 193316717 193316719
    0x6150405040b070507110a080109060509010513140c04090c03060b0a14040c0c050d03090204050108031315020106030507031220030a0e0d0219030510230705090909010209180105 78
    0x2140f40c440800c19101030348441010307126080902134552060301c40040c0301009260000000404645d541400c1c412190060440540c0b42d04120500441c84429485000440c0d001140b225078a034110148a1410301407442a94005003070070703c21824407500e0101201101e024001c28002c100020302007004042c55400340781003001030074000f0409801c29070b01036844104281080da280b0302150300c40300d150840807140100080e031145d511808600f058081c040c01480000300071400c00580ca0310000706505103014009481f06035041c60414207100350000303c001c58110b415569429120b0030024055100c00940c40c000ca001100040d115610803ca581c0a004543e0040d40c1040c0c010300003154200c2240410a6101211110181c056034400c090f1101e072042c0c40001c403014919514041e420402c040800301192450460115158809036054600781c4500d2001500036541d0510142d50303e0148070941034001c010035041190800c0154010311040a040f9030301e60030413010b407403007045c0403900740515 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 193319217 1250 193317967 193317983
    0x6020607050a050a020a0f0809040f180b041a0906010e0106081308030712021216051305040510030b07030b0102070b040513020a05070f030f0e0d0506060d0201110106080615040504 79
    0x2100401c0c0f08a015103030340c040d144141c1c0c40c0245240c80f40a8100768100003550700341c0d00000c03200030a1034103100d01041000001820b009100e02c004807440951305644000e440001c010001408000401203511840c20004441c00e480e8184006c1e1300c2e075107100c00d002e0f00f190085607200106002c0d00030b06c4000d1107114401306154000655a54019040c1c2000c2c080c00d0a200f0f00b0940007411404600240090302e403108001c6070940351004809008999043d066018844104090a40208600d50b030342e003500c0040d50701140303d0720750401a40809450b54400f5010309001e90521482c503605070400c40e400701c8264202d482064545448420610551207520740c00401c8190301c5045c0451034014205000c40303414680e003482807075111070441c40e800100c01c030002001d415007500c4090b008680c09442540c16a2680c0d440c014560351645d50340d40280c100b03845110303001840811a841020403000348603d180084c000581e88030716580d41c4540a803001e0a064201362a1070031141058030074984119040030384 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 193320467 1250 193319217 193319227
    0x62304090c09020a02030909100e04061e050c070201080603060c04060e0301090507030503040e07030510051216080c210303010b0c010603120801030b13080405010e0d0f030206060a0602060705 84
    0x1040010403205400301e50381c14901030300054189440c4040d002c0c0c644181c001d141c1d141209070821229060040c5401c042c3c54510344144000000805526072080e40700350000758a2060610000c2c1d160a04440c40500764100020001c80700f2590300684001da100b13884a00e241c1e10b4500401d40c45d240c046230014000c0101340020003002d071140807540c460400c081c00000740c0c0b00399615000e003890103e40041e20300b6440003a04018a01c5c4140d962640a140f924042009080500000c00103603194031641c0d200e14583c0300184480281440386541a0720f04030300c5990b249540700c11964994152a107038030720a9640c4c00e000160201c00300102c150744210280618510780c280807007207007260405002c1d6030031503594480101c0000d040d0310001110141a0301d512101e5855460710b41c3c0d8003030300180001e210340988001e480025841c0c00c00d54003035031424203100589009900c0410120b0089000207007280c05130640074400d264010a98034011401a00c200000b1621101c1c11391765080103884042c0090300400c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 193321717 1250 193320467 193320469
    0xf0c010309140304091407020a0c140609040518070b0708040302150f0d1505040e0a200301110a0201050601050c0d0f050f130f0603090f020d0503070506010303030b040623 75
    0x2121110a03880ba11907142114010034400d0724641044c0c001e4049103075103900d8240070f58035000469501c004580300400411402d6912aa02400381d44155106140389003160316007607075004156064150003030020002031404036510028428142e01b00c1030540600030000ca460000c03031003120000382d00a1300561404d4659828002d04091040e4803180002050001558000e240320080011240340e100200d14400b03003010021000348183c0c001440f403880c10504480d0000e010a409016542050f9151a21001c1e01060a0396000168840780d0651801071042c2500040201038503e041c6281d00800080d030382c2c0b40065502d0b10803402c2d07142c640e50050101e40d0030144948036400c01c2400720b1402d90f0921217102d240d03001d150003d4403480c5010304011400e00a140070101860002d08003071400f40041e0395691a04040ca00c1003100103802580d03911003220511004004035518140e1000803a40f06607075908005006041500c0850702c55401c1400000d003003400d6207180d451b20403600c5101020214560 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 193322967 1250 193321717 193321721
    0x80c030703090506070207030c060c03020604060f020c0703060e0c0f090109050901090c060305061203310b070b0f1308042d151e020721020913060e0f0c0103 69
    0x5105a00709501e4160a00000710140700300c9005400640061699a044d442c160602c21441e80098040004000b00480420b6002a840390400e4000000040c0d4070030300c0001364040d1040c280c00409900c00c1000000c100101607111144510290003501c100c442c0050401604540e000d00003a8050340e07240041c0580100da501194100c081c0100004d4065030759039030303141510700650005010950b00c5c420494142490034882d0700d0030005001542c60264040305180d243c00244841c1c59042109040d401c58001d00142d00002914203c5002500d64030145400c0d5022030086610041d85004a004608000002180f0030109a032100d9428282420408000c0301c44601105240024800c00d02c0080c1201105c0030081c061309400300c0c2000040d07580f01c00540b003001540c00340b42551641c070b15003100746503020480000340d40035410801210440741c1b040d000200800306010390300455107424004150389608041078010f01c103030420302004105a40842d105c506800c858140c40d003200d00403100e40c5d0305c26 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 193324217 1250 193322967 193322971
    0x61003061d0c100c0c030602030403020607080c041e080a2f010906030f0f050f1f030f03080403020f0304061d010f020706180807090504050f070f06180e07030f0c0f080c03 75
    0xb6140542c2500c15a440f60b4103405c3c072641c825035000d9400010300c8103141c0c0c1407050561042050400603810b083c0486071305100c0c4140c0c40303244091049011010701d4405400307103443c02065600304070303100c00ca0b1500b44192800480c41c1002250083d00b605460400031070510520110016141c0b0f0381540e00e41001a000303025445030889409569000c47c4400509904c00c050150100f191084c3d07841c5001d42c80c0c03911220880da4142403802c030700482000042c410142d40304402d0b5043c036280d2655201d03840c040e8502803010500c1500d5020204010400c0c580c80a8882014801c00d02d103c11400900801035800202c01d84070070005802805c014000c15000d07103c00d1505006080210b4522a40d0301410f42c244000c0e5006001a95210010301046c40000c101001c200c1610101a04c40240b4000302da445c401603a1181e00140000d0924001c200b11580110400a1180d0038000020303103030000d40100100f04846200c19400c0c60300b51072041a5214044c010000e02040d1254101501c4124101c4134503040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 193325467 1250 193324217 193324249
    0xb090c0d0b013b090607050f0313030203090a03050c0a09022511100504140a0e04060b030102070605040318082d1c1112030c0d0509010e061003061d0c 66
    0x24544021249424a03400c0e00c0b00f4546080c0068041c00c0c002c080b18102500506080200a0240701c9419403502d4042240e0b040360412010304401c0b20389180c168154080e115107598031800c0d2003000000e110010a040180c0391046a086a400783c0795543e00e8200d02440701801da81903690034507100f090410011111002d40901c4a400c1c7d0640c4510000e5070000140c000d0000064020500300030403050120a8202d91100b1602c2c03c4c0058184400343c41146001480541850b88907a240c07807041d2000c0d41200c2009400c8079080c021f80c5844e05000d02500085d20160b0f09040e141200040d0440d40880e200b1040c5580c02062204505a0540f0090380003ca1a03011998064802090319051400003854020455500c40000500205c5401801c1500e41e2145810424041081281220741c0300c00315440c502d1408000101d54403403a00b0140142210a01907a991090500b400046280c80c07001e10100d030320a43c070a01c0300d5102d41c0d1041142c2c04208804a5003607100480f8003401c2e217441c4101900d0255 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 193326717 1250 193325467 193325519
    0x40e0703060219081006300203040c060f02010c02070605090a0803040807030203100204050a0b1c140a0f0917031b160b01080102120c1309090b090c0d0b01 68
    0x2440362114801c81c0c1c8104111a01464008101d4090541200c0201d50013501e40001074013032031400c1c1028002c160840d95032008100605c04c90409080b040d8503502e1f1164014034215103d280c180b8160320103510398002c910200706c1e0a04c2407a6030500c140034103008001503902908081e841c2c104166080d0700300800b6540e20581c68017011035840780c00c10240c402481c0034402030183d10710314010305003480b4552040d02c01490041005010b641c0700c0303010103400c445d0b5484450b0750f185840001014100001c2420784001030600301041c0b40200c7c0728004034010725060310104407504841401c5011100400301c02049586201d0081449200e1040555405201c51500440c09030500c1d140c00c0255000b03502e02010211900460000d00282900c4140075140c498021490070381400d0000307000400081c8a1070320301d00700091010303540302440310403002006003c4007845110103902d80250020b03030895890a491140110940305441e00c81c1e281640c00303801c024405a176908001100e00081c10305812801e0840b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 193327967 1250 193326717 193326719
    0x1d0a031409030f071d101503110d0f0509010209010207050607030512091614210f100f0e07050d0303050406090f0605040501050a36060509060415050f0402040e07 71
    0x1e2814805084034042c00320182c01e40c0c60409099880741c2c80f051740f85904103600f070b03403c000d14038001050850507260003415074540030a1444045001c0c0c0383c4070f80354010310a0b0100e01c9180e092030541214200123501c69041c405662030b80c03801401c030700401503a18010780c00000b04100b54180b1800030050a8001e2815514019408144281e071440554500794158031988014030700a0f80740854030054095120700e059114400c80000301c4007008040301d040d0b000d003542a800b107002002c01c41080f000e00303402d0540d07031440d5019150038020000d811b40345052a0031f002c0c40c002d400d54080752020030388100500480d4078080c1520304500030100208201c500b1a0f40302031601c042101080c009035054407400020800d481c091800e0f90a4400c050004801e250074105071002e218408070b040d10f0000c0f1000c01a420403582c0d00c20640c40c0e00706221014042901c1d100070320420240120b00d4a2103180200796003c6110707401551501118012200240d2010100c004100186011f03004070600c07060038021518a5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 193329217 1250 193327967 193327969
    0x402070c08010c020f10050115080a060306060b0d1506050a110c0402030c1b0a03050a030207050c150a080906060609130902100504060219080a030b01140406121d0a031409 75
    0x641d0000e0364031004d40d01c050085003046404000c2d00e00401c40c103040600c810b503d8201160300d0000d03141650400d120b03051001400722801c41d84507400454100b003090000d666589526501039010381c0c1a9010355003480701c2da07007400468540c0340b000c407442d60740d0781031400d008e0398400c4072080300d07500e0602c5483c010030007004e001c1c1d511303400514051440400c1050356036002c00700b4041440f42d40d02e280e0009410510490002c240c00c030040c0c40d6030079213a041c0075a90381d40500e071550030003205280c07150341302e64070340b000300c201d210b40f00301400c2040311a484204041e290303106402d81d200e6085a079070f984445e04000d101080e00304214107114640703400e00d010510707090550000c0c81c0c41c2d00c1401d400000400c080b6040204540c108401801a1140744000511080c1610b884045104d0003041005142d183d8031501d00c281d208050001c04a403910740402d0300c07561540d00c000c181d022002c000c4004e0385c4c200703001a05e8000c40038a8a04004082400400502c0290b40e01511020340701403200b400c0c800300348102c1c406 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 193330467 1250 193329217 193329221
    0xd08070b010b0d0e06090a2d05160b0f03070302090414131e0203031917040b09100b060703030e0c0a08010509010515060a0813170c070501050f090402070c0801 70
    0x70b040e02160030741d00c840c0040c81c510201d0b81000c01c40d0210340c1c08038090281a20300882e00c03200b019045104a503a80085040502070010004010418120020070400902001103114401043e80e20100c5040a40c1d234203120000380640d061142280500700007080199020343d0041070a000050b00105100d5100880d440303014408484660790f900484000300100103075400611201c104004c02da1a15000d41e8000c070340d0302d010719000c0e09284208891190340242c01000002d18250041001c0b0304a440c181c504400c41050a40700700c0401e01c03c3c1c04210007100c403503000e161244030029000504003c204e85085001d044000d42031142d07405010100a503644403800d0010142007081d0000c00d032401d10800c06802c40d4402412000c4070f2004611507001c41ea16403049800191043c544040c49442c0d8121808503c503552b40000c00c041071a2114180b040b026102800c1038443c150f05841c8071039a10300040d11203202d00003100310754600030401540c461415074003800041303000701e4014000356152050a03003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 193331717 1250 193330467 193330469
    0x90c0e1f17010b10230c0703200904021c030e1504060e040c1715041a0907171909061508060c090d0605070e0d030e01020d0504080c0d08070b01 63
    0x520300e06a06801c1d402100b40940381c810141610402c14186008000030044807400141c8180d445a501581810240d40301c2a14914034415065442c07560f66894400c0410105138600c180102c0780450380c141d10b05c3c01061052003290081d2001003020500c42c0c41426001c80703180c0803000e002da1008010ba068444031011560042078400c442c1d5510b0a0010140443c0107984c00b00c2d10076410088016030113580722106490a43c544000d920145c0c4034552201c0003180d4400115402c03d1a100c0b6003912100f00c030034200d11003d016101103040b5110000e003103602e0340350040c0c001c0a691800000c00c1710f81d0302e01102c41e02d894180740e50010b4105503680e1002d050710901010a00888440e00084c420300105000303141d0466032101c400e6242050b080003103081c809008602030165642c80e000100624001c004116000f440104840d208044926000e4802c200100820f4012311901c24050081030194003202c0c2035807400c10040c41c1c1444064200050190600d03001c441034034052200e03900081081c0b8034a4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 193332967 1250 193331717 193331729
    0x91507050a1103040f210b070c0c06030e1c0908060f040606060203210402040b060d0504031d0d02040b030c060a030203220f030827010605040b0103090c0e1f 69
    0x1650786080140041a00c2c03102d51045902c0d420400040220300c42c900100c01c1141d021002c883d20b0149881d1070040b2004404030003a18903842c0d142000050359020f8201400d0310300c2120125500c98031054100d0440c0c0350317000c0c2043c490f44005200705252000d812841440c55552034103400701e41c1ca85401c00c2c14103009550712880a0068420b04c410800d15006041c06051984021804d1080c040d009026040141240b5407a090f8080041815915943c11072000200050300d500e41d80d038100c00700c05008040440d07096001401d51900301c89480e207600d00c0b05c10304140007408a40403030b03125000c000c024280500d900740c0c184240541e0000e00d4940c42c000c1d086507011307910010303103030b10344601080e2081d80e42e0407000c1c0071031500340b01c52400544290480d0616681620301200980c4c0c0d42418841b005060f0a030600381809000520346003030005400650076101c00b902c05002c115881c00040d0b00b0303204207142c002d03d0350703a00700d03014802c4144c00ba10741c3d9401880750071188145150800c0c1c03214000d5041d0007013 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 193334217 1250 193332967 193332977
    0x51b07051003020c01051e07031505040e0321060a050f0406030605040309060f0504060504030803060424180908040e1302210613030e100504030204020c0607090f05030c09091507 78
    0x1100c003400a1003690303400a20155894180c0d44c0c0c80b15404a20b41c070082101041c10369440d4020ad1003002120070304040d0101030300410006010300c0349913540c4d07042a49446500351119108000002050400e035025800281c140004207007443c0401c05103402c402c40598000383d5800340003022a40d180100d6000c2c50007a02d40b407241c00d0800500030841e0030041d134110306214040000700000c070344c803400700d40840e034000b00c05039281e4a5550000d40500314080ca00380b851542e001207020a80714007620a02240e40071b6100c1c070150f06000f21410141c4216078009800002c09010400150701d0000080341d20000c200002001c2e9000dd5001803100d0030043c558840169100d80c86000700101040380d2a00400074040381e04031040b0703555000b4685501c120100d4011110011000c411501032010740e005554020015910b0703885d03a02019503500707800c0303850200240350480300103600f01d40c5049607015901c0160240520304550800d001e001240034040000130700c610b100705108076008401d51030080043d40e2319 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 193335467 1250 193334217 193334227
    0x180118060501030c0e090c0609040b0d0501020415110d0503060d0b0906100902090f010e010c0602031806070f0207030204020f1605010c02250302132403020301110406051b0705100302 80
    0x3c139038030f182e00341d800180c0c082d0480014000e4500300054500115141141c0312503507001d80c280030902510401e03181c40c1c0c03c4071105201c2c40c100038064001d001034544040041c40d5103032410800f00c1d040c0141100d050900e820503014001c2c918401d00003035520500c0036103100b00c40c0c80241d0340c0514840040b11144007d03040381081c048040d402624281c01468880350950411182c0000a0315000310600518188201d6403100e0001da4026030905003103e400c00f00454403460000c2c443c00c20801000c00d42d40302800b43d9400983d000b805080290002189031740244507682c250703400e000003540701d030040580840062040004c03407a208054126581c0c4a00004642c402d08000007070f00e0000130b4042a004118051020090301440d51888000c980d01200c203100c00c2a24904180003e04a04510031080b5016410380c9407581050a0700388101d034802c1e802042054190702503001c660045014000005034108000074404400802075018810f0401c15100300542e40d40000700c440c511400c40030040707500458 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 193336717 1250 193335467 193335473
    0x5070e1002010f0c08150d11060a030e07080f07150903020a1203020d091a03130204050f100f1409040c1e17030712110106091401090509120318011806050103 69
    0x1041d001d1340c05070800c1911424800c10311000ea041640c0110b000f6140d503c194402d02141509030304800002a2149a540707075002c400501618040c0740907005441000d50015801c0c60000d0103508503081000a030003410f0074042a052125940c45100f070030441071400c080013503651001480002d1403c501450410306041c640682051641c2e0000d0b400c0c8000840200a400300002c0b42c450105003848880b40d0f43c0c0d82c0c42c0209483e610084001941141c0307084100100421000d620700d014402c140d80194140340c0c0d81440703182451450082c2d03652001481c02804080c02d200d080290040d1040e41e100b032029031141c0300ca000a0010a00305540d12034075a40821040f410503500d03015840d000b102852400c813040d141c2d620781501540e005000c1210701c16038040744140a5100d00c002c4e00c425a4140184044030b060042c4040d428000d0581e0b05281101164110400040c1c8040c0b1010300e402030f50031a540c19280729480d420299031000d4035500c1e500e01c90718014014021110051003410b0000c1c4a5042d41 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 193337967 1250 193336717 193336721
    0x1002160b12090105061003021303060204080109051c020706030b060c01151505180f0621070305060d0215090409050316120813022b060e01051003020603060405070e1002010f 76
    0x1400b000c00703692402c0700b4407101d503c8071210586000c0d0242130141e541c00b02c040d810104c1006aa1025202c58030100340468105010340140c80c016024508440f0321806102801c10310101500e028030144e442007104000c0301d07010382c0121510385d03402403105082400c00d81e00e407425644004036410449990801c28400103c10450b1155a50803d10f40b0314100b0403a055541c00d801c002c014640d220700806030209107140d41d180c0031680c50048041c0000c42c030221000c1901540681038030f01e440880d0a00000960038200889480c01e9250000e10040015410400290b165884508080e4010f238031840394801003141040240a10035034010000b01658003420604601350940109104000d04201800154409900b9040c500e58044440c4a840480040300c1e00a031500c2d2003418098a0f200034401060090b254402480f48041070000e11003560f581c920040c4100c400d00009502c104c003440071600038240b075480a030344030302e40c1d05050402c83c00b140001b038140b089003083c40f030060b0745500758007003480340394 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 193339217 1250 193337967 193337971
    0x70804050d020304050315060d0203030f180103090b04060b03191b0e09030d05060303040f081509010b0a18020403060908281b03090e0c0702120703030c021002160b12 73
    0x342c4061030038a81404002500d840305402910b10f4844444c020a403030b86e54001c1b40010041d4010b0807613075101036114cc80c800a400514404e00241984e183d90007444d4000e015905c02c407503011541c04410340d030301e03540c80c001440c1c0d01d0aa07582500c524007c0030405020039138101c9455014902c00e00004001d00848204408160170803c074003c160341c28418204400030aa0306000e110381d034042810390301c01000c2481c501455024080f4050a5280040c0a070408200c03c01400d51030214480d6036510880c20714240d8520312001e42e04440551005c1181580d0201c2500300d8110b19030001d03240650b2a107610050380c00350038060fa1300100006003481804980d4a12503901080312514550009800c0c3d805445805020035000700031080b07404a0080612903121000074201a91995040f0704003588251860380242c00c04a020b81c652040040c2c4560002802800f12640340c1d82e84403207070402d5030920154185004184e41544240b41484c0310803210a010390010b4054541703a5034843c001c104107103400e2100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 193340467 1250 193339217 193339243
    0x18120c0a091814030706020d0b1002010e120a0c080d0b120703030206010e13060507020c180c04052701031203050a05060d060c052506050702061315020c030307080405 73
    0x40c018504074502c580b00c003075491140c0c2114500603440001040c0c1c07811441001340c010041071000403520048103207a809203d58110a4480070048102ca100681c00c0300c40b4100c034450301c0d521100811030002c0189000b0040083d03d890312440d0311319140e841d072003150402041c42400c56150510700800b801d1500070568550300803001040780e07901c1d60b10003a44600040c001d0b1801810000e001801e0401c090706040486d6500c40c1c0100818070b0040c400946460354078120074070840549038054091402999018003e03c1d084c05050b1400b481d0008000304000c03060071940b061600c12409803203000310b038024a40258010116054200341c0c403c0002e0031914000d1107030619510701010b100d803644421722210222603001d40300142d1401441c0c0184e03482e00559480c400e000d03074442c0d21a408090044621400da07445080240440d403240315069803502c00444202580c504c84034a0b200100b412005e4140d00362200100040c50311060200d41402e6500c12104400401c594000b07000411400300034810751020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 193341717 1250 193340467 193340471
    0x4020d0e0610030c03060207020103140406060509090d05030112020109030f03050702090604060e040605060a0f0f080d050301151407060906090506060f1e1207031a06010801180218120c0a09 83
    0x109580d5520804c80780c601014041c558042108411a4082e91026204000d15061080c0a280524018016200750f01806d0300901140b00801e030000000101000c0c0000580c8809086a08004030310609951000c400c2e070400203481000000f04612041c264442406681c400d030340c915050040c0410600060100e60040d460200d0801002c140000c032184c01030b612490215103500c03204002142c540c182c0d000f1020100d400780740042c00603003100480040b140b101065400880e0400400c2d28180401d204000340700c0000740d9040300c0e4500c03c070b010484050144003d40d08107900c948459049842840341100c0040e500c0620300244001002104c0c1e005038200c400b121840100380c08940d603030f0084e407289500c030800803440c1702c002d075100d005880740f815400080799510b551b80c0c20301113010311680042c00b030b00707400f002c001ca4001e52103a2140c0381a108030b107180c01080e10300040301030b00a511180c26500071031420340e40f481d001d0f540c01780d081d104815850011b0900006a00c100901581c0c42c1e4003141c0d0a80c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 193342967 1250 193341717 193341719
    0x160804024605090c1b030c0f01050c09090609092104081603240f1107031d09070c03020c12010c26061210090b0109060512070306020a0e04020d0e0610 66
    0x2070b50f1015481d900a421621064540408042d80d05202030440200359041c04007061026101c003001480f1411205c40030001d010507119201c00d45083e00c0f83c10401500804000002800390070a4807040e600020004201c1e40d058004a00006041d9088520302c0030b120b02c000f40400011808101150300414030300000d0715050702c0c60703440c02011851800034042144042c030b204140c1100540c01030400710140035040c80700880941c0c5800703080c3d002040840c089450040440c108610180c103c446080c009050854203072209107041e60b600300c0500d81102184914030b0310500135203030440128000385034400003107820f804010016210003400e541010015118081c50504090b00d10181d0f0f0300a8000d50345469100340d8030303200030b040c1036101c07101700e01c85c0741032610700300400010110950494000e0b28082024540300c204010401c9180c07401c030030b0158440182800490800c3c2c0c010032000020b81000901c0c40503440100b410b9070000c0303510782c00003507a45200020844013480059440080410840078403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 193344217 1250 193342967 193342969
    0xa15091101020d120c02030417160f031e020d020301090308010e01060e0303041707030506040b040b07050a121a0a09150509040309061d0402030108060601020d08160804024605 77
    0x4c034680c0e208484101e92103081070120b2a000780f084030040d2100c0c00300d00d140781902d10203036513462034110f012802401c1c0b4041c002070502408501d10081e00d612081507941031301400420100010503420586e407050b480c4480b200103030350034450451200e105c1c1d00c0d1038071958508401c40d0280181648007809102038030f04408100d68001c4103c0d4155800c000000414103021201d481c9040f445030402480c911806050009000e4101c003264410392180c903802c59903036984507040300c4034003c841846002c101903454040c10000c0304d4100f440030060b034840c98498040c40600013441a0314540c40384074480d0307075080c0448503c805400f81002900d002e0710000d01e241060b40d8002c10080303c610450040000811482c07040d05051221001d03078841c010429520b07961944002a00c0340303420f41d91240076100e4141000f08144c05110011b00c03c242a1000c14050818801e0694158400600481c0e10036290040c81c1110709001c0390070100c400c4810481101d005280c101203c82d0802040c101a1288103801c5c01c10003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 193345323 1106 193344217 193344227
    0x1203040507080706020f0f03130302040e010b210f0c01050702010c0c05060d0209120604080415050705010f06052b06020d02090a29091008090a15091101020d 69
    0x168142c001005a035270f100c1c219044509100000c0208094a0b00c2d42c49424100d80020012603207400340341c00101c1c40140303106100e40c1d14213a100e403810384240400116180e406144010480d11002c0c0002070020b019180f4000e0400a010190100301b0602000140c020314000e8804c6807212454003510700a504504249130103803031040d803805c0c0d03044800640c0034061a009182c280c5028140814642c1c0000002c0c9a03e0601208000b801d000403003d2084c01c1d15024503210002d28941002d013003021840c1d4030001a4940c1d02c00303034900007240040f010301a00031541f21341c00690720302d4078504041c0607000340d0303030701c035a2100102c1c82c00180c1c01141081c80b01d00030400d511081c80d101021907031035428028049880d0f0480d20783c43c20209028050740501c1d81280360202115280000c41e60f80e0361589186441420a207601c1d8500502000032400c1c00520215090000c0c2031560305080e40104 = true := by decide +kernel

theorem cover : BRFrame.Cov 193165467 193345323 := by
  have h0 := BRFrame.cov_init 193165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 193165467 ≤ n) (h2 : n < 193345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
