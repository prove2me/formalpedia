-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3438
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:40:04.806901+00:00
-- url     : https://prove2.me/submissions/3ad1fdc9-439c-4673-9c7d-c72a25515418

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 618165467 ≤ n < 618345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 618166717 1250 618165467 618165469
    0xf120a0f050a141b03040b06031e0c01140901020604020d0606090e100f020c0d0809010615111506061e070606180f1506030c1e030f140c070b0709051e 66
    0x29969442a4040c0c11300c1c00429031030700f00c842e00340701c05800504009800000709071a6030f001d01006500820050040002e030000c0c099440c3c5903410115698041148400c1e40101c0e54154821030b030642405134040c2603550385a50030807942d403400c1c0e0030542e0460754802d40410010344a01c151800703070050a00801d013074108141d20b1410345100d070754194041d0340140030038114118000303074041104280742270545450352100504e85c0104101c0c0e211000e100110404c0108054110003510b20008a41c815201d03d050303030411880e42c3c00029103480340c00007002c2103c803d40302030101e50029807082012480c1c0c90800309459040a48480350800c1126816403409601885194421100c04485a080034130030206d161081d111500483e125403014141c9072030480000302c2c0b107002e076210802c0510a60349099030801c00c008009240c400406d0b004a440d01060950385401c81b9101403084494086030b616000e01580c52104858020f0000c409000081c0008205a601c41c4071f00180304030f0006102d43e040704048 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 618167967 1250 618166717 618166751
    0x80f13020402210a1a21240f09030d0b0a0302030d02031b06010602060601050f0d1b091e060e010c06020301320102100c09030b040606030b07050f120a0f050a 69
    0x18081c50708a6250100ca030441420901c00502084411034400c85015500110044030007541c2d44000e125018002481e101010340c3c0302d041f41a030048207101029603030f0391040d2540c03900b0305680c800c01070b134000d00a01d140004242c2110300b00340d00c0640b080e42e01a984c0d13030201e4a80007846c04018050703080881c007160a230310068400250038045030000c04a0707500d4400c019442e8078025041c1410008009032030305c0c50100000c21502e40d100700b410104400518402e000551400b090742c07450014420000005009000052401460000c10441c400301445c0030301c15526034002450a038140300880e8140000b150a91000e98000d003403142c40f503d80e4a09481402c00501c108502d503110030301540904e1200d030390340003501c0d04000484080c005582c4e100188151108407596200805548100007040100620340e0030500849102ea445420540c5800d1005c1d40c450158110400351002e007400080c0c10001c0c0303515525048000c1c7d040c0002e420802044030001c1c0d5408480c60f0000303a48805141d440c84a00c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 618169217 1250 618167967 618167971
    0xc07092f030f0903160b06060c0a050a060c022a04060b03130611040e130c0f03050109020f0123180916021b06071103010209041e0e060106080f1302040221 68
    0x4601a500c0c0040c00d40b2020741074024000043c0036810b03201b0029400f512840116010710055400700d5108000f54505076965116664044038800d0605003100681800003650b003001041d90980c0c12255852408880c0304001c0103656198410340780c0900003124402c020003540665031400c020440150641030000c207a541a24414214031000c0108000e4105221031480c1c001550607840714050505003041c0c0304601513500038140000d030364000002046015032100302c905200355511b40150001d82c005594085070050b40c1211120300509075800005101c0051400e81d080c0030104070403c11000124590410403583c8881c001d100b040d04810641e010404109100446024551a6945900401e186001c0d62400801a041007005000140d5084d01034950f03052024000b080030485044610614504440b18071311280c0c50803100324415079011501e01c0c180c07012911040031a89480c480017140110081454004645403448000140c0c0d6500052982c418813500300000c800010711001020880 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 618170467 1250 618169217 618169231
    0x20f04080f0d090e07122405040f0203010f03020d050106030506340e060d0f020a2607020c210618010c031e150e040503070605010b0c07092f030f 64
    0x1a03020070400081c0d40131200d03611980a252000303144501003502c60150000701101c2c41e5640c5400107280310711210382c2d6040c0403250f0840301480a601502408000c0707210038040c204c1d10a11145060003d070800303035080205288540000a46103581346c0396139080c450195010b40c49075484080b1507912800590f07405040c01a014810566015406e80280100c1d10640009001d0380000c6589440b04d040c0da8440a0444001c10080d50744401c0b201c80148118000030070031004030748580a1048050006c0e0301c0900c00c40b060f03001008514a0602080303190000c0000d0b07290020082142d50401c048144500d50103008030030b140d61001c2c41d0507a101425984402e40710400c0600d450780e40304035440005a41800482c1e0640006a40c00020f000c241145003190820090040304005000410800100922115000da4801c001998880041d00302c00d1140340c543c0b1590b540554000d01410030300798040c9914503a400c1c1040d0944e00449480c0d0520380050b01c64800103d800320030069600d4440e809598031840c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 618171717 1250 618170467 618170477
    0x1206120f170d0204140108090d0e040e03040806040c0f0e19061809030206061801050d1412040e060405010506090f1f020a050111090105030c0a230712180302090604020f04080f0d 78
    0x2500c00030490749e68042407103400400820662608084e00c40d44e00101c10135180006072507469441e40c40c030603950031080c0d9040700c080010000004582e112040081c1c15109180305020707241e1103c4e05680c9600c00f602207280f09a0b41e44d0a00010701581d542203000c043c40509002040c825490305000e0704180740200100c0c050f06c410f21103001c0f1500741c460b2550540e1021100000407038228148140100b00700d0510710034600c43c001da40f10388a41c0c0080a0021109064081039450b03451609120036101c00f845070b40d402c02010b1110705128641a1621004108043d0214100d02d6902c41e55003180d1800b00d0400c000340c1c009184900030301100b80500000406031406140c0740400c06e2000030800d20000302444090b08001c01c54032a010b02c41d01e1146841046c414002d01440c6444107a0340c05984180002c440450801c040340442900070304e2003203020350007515400c0945146030280442e10000804099015a080000301c500c002003802800c080c2004100030083c410140c1e41440c80c0c02c038424090380c180300c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 618172967 1250 618171717 618171721
    0x9050a0311060601050717040e0f091c2114180609030f03070f02010b10031a0a05060d1104030c150906080f28050a05071206120f170d0204140108 64
    0x2907004401c0700d40f240d50041f820701542c50f001411180901a03a0800c500d00c46140042c01459080105d03c0d0f4007030a19041540c0c81d03442c0c511010030010610744800c0d00442c140c000c0201e51036134004940d10b0030200c480008500c040c10155111211401280c181d102c0d041600c031519080c901c01c01c111036000d201c4200031031412a1864600800b40001010502041103089405c0e150900c00c1d0491021400043c0c440561495800320160140a140c11800409511524002114901504d201040711805003115140c04945030000b0003901340c00d0420b5004200402002000508486019000b0002131071742d903030012185100140100c410350f200c803040280b00c200b4001f41c0720001c003049070828642c004c6040039040400540400040800104000c6031409040000030f00d190340140303100e000190341d128410448481070804644403406070300c801c120b50604180c0058003e0640e0b41c52680158001c08a2440b0500014915070011910300100f40c3c002c10b00b00800b880041805582a0090810780d07030714 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 618174217 1250 618172967 618172969
    0x1d0601140108090c090c19021b0409033905030c070b180d03030f0504060506040c020a0b16090302060408010c140408031603030b0613030203060c03070206070e040f09050a03110606 79
    0xa1a0b0b0604d506104103005404030721900c520314100e40340b410030080b0004600b1350032000607458034210f083c80b141002c4500311103101c500e040e104c3c50b4030565160310707110110301942c82c01c0c4030950a242c540401c6041d8055440e034099000c007400760681442100195919882410014102072003540482d03c000c03014085484040ca01c0003010440000984070703030112540c00d04003240030740495200003410a152030103000a004064118500ca80400d0350184030f8600602022079071044103a40242c5250881e2001c42e04a140c03240b25100c2050365854829a03140c0c43e9000601168000c0c0d0004107680c2d5110460340300e99800005290303440080d00009810286030003107280e01e80c03066038a9038807021905101841058040e9001040c0c080003d044d00d81c131010548587d400d50b24660001364464882c030400500b07140d2040080f28854059a07000d00103030b4450a00c1919202e10344031600c3da0058a801501d03040051500c1121880c2e030280c0010440c240003810091300080e200200e15000b60003000400003a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 618175467 1250 618174217 618174223
    0x114010503124e150f03010b03030c030301030c12021f031104091d0f0307020108040c0302040908180d0201051c060b030103080a0f020d09181d060114010809 69
    0x110a81210710240c1d550040e200a603c080d2911000b07102a2084481166100104042114284624082520b00051900c950005031141190303000e4400304921020b0066082540b0710208100029001054840c561400281145c0040e0b01e2510303a544013100420512044001480040101d06403514004c400b6401050250000b500440e0b00c0072541d03104080060f1107540600303425035072200701c0c50712aa203519200000e800d4000d22151030109041c00d50004500c045190702d0006c3c5007000a40c5414640d500540b60940010070984a40006020000168403a07001301c44d00c103445005140c1d515800c01e9000051408214910f500440d400910700c170060740c00800301c80c6241112140c4d000c607039080e0720704078014000790b0f00001c07000c51001c000003040203108400390850050310b489140c50018041412651003103120a110001040460200700b19909008c4598040031381c1c10b4049160001141321754200700e9003451080e029032025004101c0e000101d0218901d079107003440e002c205400c01c103203115030b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 618176717 1250 618175467 618175483
    0x30503071e1205030414010504060c090e060603060f03150a02130e0610030b03070b130812071101030b0f04020304050d1e0504090e01021c0b0108250e1914030114010503 74
    0x3c0c8640000841c0600200c012075030640610807000340003d1910789000d8004d0008c4104820100b01c00400c00300d07810714003044040c4501d40190030702d8119aa01c1d001c12010310780a803003464040c01041c1007925510709440c00c0d503100308500840569682112814400c85080e140c0c082c1d0505080602441900d40e0364615034009604145804910a617441c40000d0034000340d5403210489100000700810440300e4003080501300d900b544151a0381c0b5000e042c00e0196072189000081048a114005004941c000e43c420a6070741000f51050400d641e06c4000300f0100e80c015103040c2c60951000300341c071007603c0d8401088400b0302c0e0032035410050b0702d4500d40c0c0075006006502448a13101d8031032007080300c003203002d5054441c011100340795103020354001000c0f14024003a8014490000e21004009040b40041e581030304030074901c55a8113511200f507004100c6544566010541d4040c151480410800c03401da01d40c407000d07250412240d10703846805002c00d0f0850301180c50102c00744c8001e100400840e5404220b8079 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 618177967 1250 618176717 618176753
    0x10b070206072d2306250306054612080c03030c0c070801090803240a0b0a27120c09050106080915010503120c0102040302040204030503071e 62
    0x107500803e40607443c0b0300c43c070502045142e01103d44906800c3c45101011030110070814201e0001e507002a095140c3c50f08801c0714081c1d104d01c12444c1d08a007580a0002500e80c54915250006809455a00140607460345200308c211180340d0000c84030b501c1910ba91b500c0b103005280140511600e0f00c224401e03c40d48101e200c0d00c8407141001c8102009d000b07034042140c40b10401e003000d607596171070081c00001241e0450600c1c00040d2068520100d000e200510400c1e0440f0381203c1c505080d40d441c0d030842140055018070320640d1001214101e449500c03014070000161945000d00ea488424000c4001c09640400c88071081c031242e8849004901d07010783c001c00f030a5070807840303200e0001811801c180a0b11525544420101c41c50711000290b03075603120000034000e405d81e80030740340c089100e50708448010900380235051740740d00241c6480301903215802c000c0114855250000d42803542d641c0000b0b080b0707000b82d44160b5064100240040400610320080409148030f40b982c1051203c1c0ca031100d400c0c03034440038048 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 618179217 1250 618177967 618177983
    0x118110f0d03080112080426060f090304090b0622081203131101050f03010f170a0c0b1606020d020918070507021c02030d210b0603040f061104060c0506010b07020607 73
    0x4144a0641b04480c054a4032000080ea500780e0002c00c95002946002c41d490305008081c00b044854400b03842d0140070b902503070f006600b0325052140c20700c000c00c030000c141c9510080c1004107200c9520081011552211013403042e15000307180c50700c0d0b0340c1415001c0304132201c9040c0420030026203041c03000400840c5a00034880b0b069041d2000016540d500ca00b052101900f400480002100f56a0f21003d40960788440c641d400c071010010062039450202d280010300806c801d503400e100d81171410014122025400181c012040f07030946911089900050711041c015400003a0f24000c1e040800714100d84100ca803070180c002d03141c420801091801a078100900c1450480602a14507200c5400303260340c02e4005003510314900002801420b450180902020030200e401c580781000b214502c512208190050700e010714554840d41d4464452400d603a00700c440304c0d6500f80b103010310711207503029102030001502d48810780402810054078000f0b0503807006410040810181005881344001e4030401039002c011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 618180467 1250 618179217 618179249
    0x210f04060606020307210e09090c03070b09010219050709020d060f1401020601090f0f020c0a060b01020c0a06081e07080901060506130b030402030a0b150103060e0c0a0804050118110f0d030801 84
    0x31107a10402002d043d601c000908d003403024518000c80c1d2509842d4089003195199561000350341500c0c06042c00781800740c0c002040c8503070030501669607072030381a1140c000d44120503124400507040b83c01140540e46920343da500c00384070540c4c50a90f000040e00030008860074a207030010000b99122014010182c0f441d4a810b400450f6548542101c2110448034806548400c2d003054125070b41c514221066030040d040000200c001d5002161034061100040c00b800340c180c0c104007042d2201d030406400c06065000c040840c40400c0002843e0500800302d99a03070400e50b06114220500390745558014520035030b020004036446010703003000c01d8125030f6100e045540702d942c0d500000c0d0400300180e01c05001022040300b081140740c0183d0050107900403d0301d040200f01e0b1950403200d40c1c001d04481c0310006803010028444034600034104958454800c40004c521100b2610200c5440c42008100b211203584280c440c0c0240d01e00314101c034110150940e181d104458081d01d00501007401032242081d0395600c900 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 618181717 1250 618180467 618180533
    0xf0708250302060a0e130917090303120f0405100606020d03270c05040f0e060c030c040f0303050d1a0f10090e041109010b120c210f04060606020307 65
    0x1110400031a00107000c1d50311382e1990720707025160f101541c2d085172240041d01c242d4100351000384031f864107060f04001d03d80e0030310750040c2001110742e100c00501d0794140300602c802c5139011100020144295001c1005c011301c0c1c102450154500702082620340d000704c3c00c2110510200e6800109529001c41c03e24022030481800c80440d4a00b4640c803d110303144400d0f111040d01844481882e000840d202620b0030440c412106401c078040b030300d030800c1d0350a00790051400300c0c0044c0d0f01a405160004058007004c0e14003561101c07040000710207940110003107030000c203041400c00841d00c1046040b1612030440c504009200001070031600c88510050303ca02d040316084001c0a00c24010f48028100c3c4105010480c200390800c05620b00c5240e043c54840c43e04200041412003011058400b0202004a0080d0382c1c2c42d4400c422032346802900b420700e000301b00b0440202d4626046009180204001c80c295111420982001c00c10349415401c0364095500c20050140024030390740b02803c0d9050809004c48030100030203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 618182967 1250 618181717 618181783
    0x10219060c0e090f010501020607030c020c0402070201050c1509062512021b07140307050d0b06040b090c0909010504110f07081b0708060a0903050f09030c150a020f0708 74
    0xa072069030083d0703011040001c040e8640c1c80840c16644240c08403071013561510801c0f002e072120a0b041d00d00503006102d10200368240340d0007074140188141450b9080503da01c844602d06000d040f850400c44210100b84160300c0420b101172034100ca004082c1c05c000504407244009100c4a1103100740030003507240d0500000002c26810744000c00143c0340103841e000070b1810041c1d920505070041c010340d220308040d07481070740c0380008550741103810180c0000380c0000a40c442040500c1c00a010310b812070741316906100543d031481d0700d861040841d08207060712258940d0034045042d00580005001e1803829080217011590700c820746040c1c41071304040c60f64540c02481c2070070181c02560507030b0211f2413480b066121014404030316101681c8070402152040e0740c4400c1f200c403e440100f040940410780410017071114049540040502d030a016044800708004500420301d840113080e481c078050741c408211043c840d9418000403200340c1004005000c410b0a1250640e110040c01043c0440c9211994603001305290070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 618184217 1250 618182967 618182987
    0xb071b05044b0606170f01051201020c060c1b01140a020c030c070803090111030f04092409020d0b014803090608060913140a0807050307060506010219060c 68
    0x4800800c01d20521142c00e018090902404020529424681c10742120f00498180302d4140210343c00e16036481d080500076003400071282ea01d0155000c00c180c03424020704200313280c011182107107840d503241c00d000b150700d160804030b01d00c0300426410401c004104028000405800400c04400180c0c4c94103030450b2203240d0f100e07410a1082c14000c0d010b00080001020003c1c054001d003c0c0c23615814007140c0c031a016100d126400400da60003506000c1809241c009038011800d0154040703070505c107070032191a407004100041d8071400d0500c0e000500b5080c8082540039441c0c60703070f10a007030995003680720101500e03002e800c0b03101d04c10101c901ca06a204000741212009181d0b6444164400a12017003411b00030080075060041c070010600131401705500b424103082c401e00c1420f40c149900c11034801070b903800005270401d110031401e07032140100d8a0082009800200307034041c8581e0065070b40d070511f890702c981a9440140854159040f40e4002e504140b0340f124a81c0000d40e110600080e41c103488642a40e0714801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 618185467 1250 618184217 618184331
    0x60a110c010f020909160c11060d0f0c0f020a0201080a050c0712052a0d030507020102092715090a0903020307060905010507022518060b071b0504 64
    0x300b80c8251000e200c998000d008145041e104503d41d583c940001001c2c020806180c5000540540080700108640d64054040800d0003032819180008403548101a9600303d1500014680d8a0390385580303040e00600405a0000540003501d504140c540002c0d04001004002440285c5c44000141403030103c0c90882d5409582315846000601d04800c00904940080074041d100240320071125a4030100103040080c80c40d244001803407807800840007180030301400341101041d5902400b0702040c0b03a0b01c0d85515014004001c541142100c1006024035801704050410904442c4e000010850307a01c035410b8190340080e0740e102c040389a0707035940b404900c2e500c40e217603015010310700e030100100c00c10006400c81806000b0960848181d4411050002a070402c03c000c1100500607400d0100080b1840034203040003910303203020000e003242d07943d10000601e0740700c0c6104840922951055012101c03043c240c100140c070080e1410084130188880380c0207141058511500c581c03039100e0b9280c010030f007001c00d55000004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 618186717 1250 618185467 618185471
    0x3030705061603111e0c07170a150212060607110409060b0414190f1b0206040b0903040302030712020d14030306040f1b080705220905060d05060a110c01 67
    0x1078200302c1060380d601e400300c1c08400203041c2000303103100494100995180d92031050b00060380c00c0700624640c80c80c0d4010642610325028a0b0b00008400441014070440c05c1c8a0700e0207030641d02454904010f5104082c040a17143d00e106202000ca410300300c140030707540414240c810650702c5509007402045c981074200d0896000e400c1184800030405190401d401c503e809407010300405071240d80c80d444103002280c00c0306008404c40662030417410341e03811403461a001c4100014085c1c600300c0202000c50103010241000d640b0400c10311081120a142e0750394840d0071600a5070910303095600090b01c07207000e0b22480810214158660055690711040340d407150342c1c4a03c030a040c90b2214400a82c42ea0800c64409100e2850500e183c2c80c007111500895504410000e455a4860107003841903a01100251440003002401d00440300c10b082c1e44c0408446074042c40b0b000c0c0030300b40d09d04030302002540d0b00101218040c203080c000004c0040c50000d0b1194212140250206024130f240541100341d014040411000f98 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 618187967 1250 618186717 618186721
    0x20d030c0c0602010f0c08041106030a020702030a050a030f0903120f050d0213080c0a05180a0b120304030c060f021b010e0a0f0f0e0907150210021207022a0f0303070506 74
    0x7601580f1405c416420401c0901c0000003200064403811000c54016017410b40c01da034aa40e140c03920400540e0b025100031001070030103082e0740229251005c402d200325007d5003c405010141b581020540381a0552403400307500c0182140e581e0a254070782c0302e0b04481401100143d02c170703a1502841c00c0d2540069940011034855030400110701402c5818480c5a00901901103881041d007010034503030381500c401a0260340000803181d00c0c2d000c01c40004062a581c2c0c0e0b070340c0511004c01d07920b02040c8030b400300083d8000c40d115820342c18507000b41111940098140309a194603003a501340c0104e450b2000030000c580801d00070f41ca000042e50241c080300140c2c1d41c82034903a980880c8465138080c01d41d0a03a1409607100380c000d521550b907504140c1050740c440c180c81e4000481000083d128280e041e10310f805074410380f6a040302e003e01c04da050b6000144884a0740f0750190812603044d038104140812500003481d0345910010038207410400c45c0c0b0f08000f40740580049882e4a1082d10100215044903a01c0411a0624 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 618189217 1250 618187967 618187979
    0x3010f0b0726070c08061b0711190312021f0e07180906060f0303050906030a021c050411041122031401060503120f0301050d060b0907030f111303020d030c0c 69
    0x2c1e0344200c008494041d5800303008100d2242c0020710b04d114942c01310780d4800540707900110044d240c0041c54112290148074000811a860303008048401081586248012038118606409031191b1100c200045501050a14145801c00498036a6441040b0300c001410b0601c080560708000340354100325140040c20b81194103081069014899090080008001260300c864000d110701e00e41e4400075001840500c000c14040c81c12500941d00310300004001443c100345910460903c0c25100e5074110750a94690410062080c0b90502c49100d4004890400001c19200002d68a6000703086406010320782c030148481c0e03c00c0c0c44507180405113400045140510100d80803e601078030003406068042d0003403007140c1c942082d258054520300c1c5072114003e401c6a091130103100000d0401c0784140c5a158a81e03031604c80c3e6840e420105800340b140c594021401480902d15103050b101003d0f00d52200b0102003144d0504281d40100a10541740c1c11902c000f5211454202181c20410154028260501c180b02c0007880d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 618190467 1250 618189217 618189293
    0x70f140a0b0603150906010303180e070203090a052202160b1006030605010507030503041709040207031e09080c0f0402090a090c020d0503071d031903050304020a05030303010f0b07 79
    0x8910421812107109113400050140913020982c0e0214850b8020390044c00081e000f01503100706245d04044489000c3d03600d00c0d0444a801d01030320180f01503040001e4018603818070b004d00c00064a8123850030008905180008c2400d906c0c420407a283c429404910110810522051810030f00d0b04a00c0c0d80e1078504040b09040c1040d03080f485010b02207032801e040000c0d40d50085c1c7c150740407290141c0310350342180c0c0c2c0c1d900c03004035001d1498500c5104000c1001000041e9036140701415a4038000d81c2c510326000c0710b840814480d0300820b00340c0e20510000c0b42e0100816100000d080d0300c80c00381628402544036425020401074058543d980d0b0f840b144200011403043c0740c0d07500c440c22005080c1e00325100045c25480a60300c1c1c2c802900ca09000a0400100c00c41d6144480030640b22084050126034170131018500d07040303030001d030702c241180020000028030065182020040b03010348401c902446c51949444025082c0c0344641c81191010381c408181c4a0900000034114007810880040c000140707404c003980518 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 618191717 1250 618190467 618190471
    0x2160b0d051302030a140c2d0922020402040504060314010c0305070906230414120106060f140936060109050607051c090303020708060c070f140a0b 65
    0x11503580361000040650b081110000e107020b070040c0c00b42480b00c0442e150500c980c41c14046100c02c0c2d228550280c40c840e200d0741402e002e1740c0c0c2c0321010712806001e1800d20302d801412139040c0900c100001c80034802403c100f42a0f062480b00700c0402007118503500d10226020b0f0050764011503000c0d2030704c0d00020030f00207030094404201445000801601500c40070590444100b40c940030f000803040c0c0014000280540420b5000b9080c0300c01c241401180c90010ba120703030b44560800300404100d668074803c5d5040000070041c4417054a0000d10040c2e0520400403c400c1d807202c41082001105a07154140c8190242291303604600a0405042a031020000b07510000001111404600c10020520449a0600d00c4c007400344905a40d42d0046030f240404001c2d00707810a490035030b081e00600007030194a60440020b14030302580d544822070803a1035402c02034100f2000398001c80c12031700010200275080954500300c54040380d2008818000d4241030411003901d0030b2060342e060040c414281d000c018001003028042c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 618192967 1250 618191717 618191737
    0xf1209081c020f070b04260c0f120a050a110d0f080a020304020a091e0e0f06010803040311061b1b09150612040f050a03090302150406050a030c02160b 66
    0x10003046848401d008030710444151001c603280522070200002c16075070b0406c0c1c2043c01900c4440e01840324440d525111f1118041c42511520300144204440200703000c403540303007521b40380500f0800100144040c41449010a903a00f004400038082e041a4055018141a1580303481118103018500c4400703000810601000c1001c5591200010005542c500880b4030179a8040c21170032540e0b103840040c5024181c1128580030249182d0036228032010745118000d5900c5c0110024114240840b90326402e140c01a04141c503a40c00400050006c5940105000b000c550140c403019540c40e42c440c011074401142c010b000f41c15000e0941301c0d0710342003884025003580b00c5080b1400380080d1107039200c14590b022118100e44d041301080c4034020745400400180c0b58043c0c0642e000a0031555241d44040c20800031403c101c0205c5e65411052066080440c080c900105030111001c0c40e103410f220000e032150184913802d000705501c60030302c800c031361b44280030504241c01c281900c0101c442d1108400e0440c0d0704000c1807a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 618194217 1250 618192967 618192997
    0xa080f040602100c0f030902060d1a0f0414180a020d1a070306050a2c011502010506010203030402180702070906090603020f03071505070602040806070302090f030a02100f120908 78
    0xc2006405842404484d25a6440d1090b03c280641d405602502456406aa22400a01c040313001440b00d4000d01003240180d40769070310300d442c41c4c03000c0250103462440c005004a01c0e00b0040d1098000e102e000075000319040c44082103090300c04c94010324180904c0d800035000103588030f40408000c01c6207040e002491003213001c1205942c0710817084045417014810254006a6054200001c0800000f0403401d6250f460356400c0001ca14800c024038440203a2102c070a0112000d05090180d40c20304c909078100000f4805103282d810603400242c0051006044140c41902e168080750055000b00044001411070440610920ba40d41190f140200f00510003030340190a84840c3c110b0515000c0b65201c01c1d9015801d001c807040c0c424080403900da4100c040d0807940c0c16800c200100e51100304000c55031203a070a0395405a901c0e407059003030110340250703161014000d1780208982001a07440c0c16080c1001002803503c00741c00745400d0b800711245191094120880c91603d0040018071440f00300400b0b107940c98141d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 618195467 1250 618194217 618194233
    0xf0304050c010c03050d20040b0a02061f06050904150311030c0a0810020a0c0c03121b26120405100c090e040204110d240602030408030f09030a080f040602 68
    0x545000f000144001c0c0002c104024000c040800fa502800d122613241c40d55221606c6c481e0381060807584640c2001d40c000038041800c41c2080d034100324007075100c45400e44c07071110410790310514013014009000d007034240000818000c1d06500c640e13010702e10200c045c0411105255690800e103d02905159085000340247d60000146082801a000448900c4030060a900442d89480070094200000100c10026001c244902103013219072108080e60060781d803070010100700d82e800340c107420b80403001c1c448032002070b0700c2c500c00f151001e421140302d00c2054070500400e4000d07030510b8000d407150602d125082c41003002408140803001a1559035a0645c08041196014809044e00ea11401c2c1c071881e4401000d440005006040c503410180f03408a00c4000103062840041240013034034003e91003440c1001e00d00071107030360607c03070100355500800240c00034500d418182581282c0300d1080200040032824001002c116507101003100c0b280e09500b2051854940c44501c11003407055000348950790040c451000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 618196717 1250 618195467 618195469
    0x1401030221180f1e0c0d030806030705040b060711060d090f0b07090e040f0507090606030209010f1803021c0b0720010b060910200a021212041a0c030f0304050c 70
    0x21801e0085003d20000d0210664400380341e240c882080d0903219160007642202d8025444844d01194928800e0b1220b82c214a4050300741441d01001e540024452804c100102089403039580031102c44a802c5841c82c182d41001c000403c0301882007075846541d2070f03d041e4803001407004101e45114250302c142e100036444c1d10788136801c42d0304203000e0054003256800031001c0780010f4600c0940340c101f40d10400075220015942c14145c411a00e0139805040420340000c0d0300f9001c0e683c42315414213814083e050404402d03402e010384004151050000a0042801850520710050080040c0400c1c035805040400b040c03501c404010002d403804913140034040d0f1035500813205268180a4a940500090042070505c0e041808205601001e01c1782c0f00184100900c08022880079003003c9171200c1180401000182c3d410710500644091480d108880b82d00018080040320305074104480851745048a4401c00c0f220b039585543d110301c211b1b401c00e0074034400021800c1d1403a0b14a40a1881180204103440165403560 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 618197967 1250 618196717 618196723
    0x706060b0708030c0c0a12080108061006080610020c04020d0603020a210f110907050406230f22090510080d0f120b030a1401110a09140103022118 64
    0x40042c01400c05100089014100c00060641c0940d4403040b90009070f11904d13604098030250341c140001501d114018045480c2c10002c6d91b42010350a90003240c180d141080013041080044c1141e071040e01e1040401c40304d103100308800224120020021566818441540001407c40e48002c034090710241e04005210006000c825908401708500b00320a270302a950345855450406400711144010400844d00b5a1114030906104007901e445060395103041000c080e2030107124000300a00c440c4044488071341e0350021402d995074034a4100796a9101c0a19044004000d00d46940da04200341c050340c8001103d19064002a0150001c594200d441c00d8841241e16140c046540101000c40d005d0401403404c07034481e00743d22101100c441000600c040303a0800003401d10581034000e60b6030310b4002d098400c2c0075400f8440c02c0c0c51078014040d01849d003242540e02401c020000e00c145003950040c00c00c07406450340203804803200504009003000c5404c000b0944540300170016501520599100e00180140716000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 618199217 1250 618197967 618197977
    0xf030a0b0f030d020d08060d050a050606090a0c0e100908151e0105030309010c02120d02010e010b03060601080a02131a18060f0d090c0b03040b040b0609010303050307080a060f0b0706060b 82
    0x6a40501040360861000b0313030701081c011f88201d8010548025820101e4014000420034070701c41d07000360070f40d4240003040020a900150050749000d1a0010344100c0641124401220700c5050b00e0313441040b50048400c0c0c1e80420a42e001c50342602540010600045e0030741aa2881a01a4010301102c0d00b41d0a071034000d0000e00b4055103170994802c0081c608290700a13103580450500c010050201025024015420900182d800d20301507034643c055008050000c0c000c0d04402141980200084d01e4800002040c03200041c1070b0f00c003080d6000800240c11083d0707005680141807480c09030741e01319007a01e020361003e6000550603091050b16000844551a161040b200703403016465000c1d0618030f48000d1a001003000303070350031a00c5a41c0c0100001c0c482e030110020b5441036000d61601c4d4520f1409080c40c99052400424680c0f00301c80030001800000c0e080020790f84c210342d40e407802d0403481c0c2e2074042c00e1000f041103810490038007668480000d000100807005011081c8201e600740003203551848510354078015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 618200467 1250 618199217 618199243
    0x3101b08101d0a0605031207030912021005070807020d030f03050a0606080a0b0d02040903080613111b15040b01080d03020403020a0b0f0d0204180507110a14030f030a0b0f03 76
    0xc451210124903400b20349880d04481e100d1400500d0035a05c0c40006c2c54142510303803d440107c0042030800501d0b40104004006001209810880c004907a0005074240307000f4034010300780f04000c03a8030400d00240100ba0b50480380c1c0a004104200800d0030f000d00300d02e004560000000e4140f038001246000360340200f104070380182d00c6e103d9264440c2c0070694068081c000200f0b030407844880b6401c016079a907001d8010041e01a4070740c1425800e00200740003006000010141d01c0600741030705c180701d0640050444103c6045080f8100c0c500403211354460800340c00c00442005a8103400600081c0703c01c10b18058101c1d04048121a03121018500c19000c0e0f009501c03002e0b47c81940d5030b0341000001c40b0701c00101055052041428a82283c043c841c1040380c000317030414001e4041981c100d015a80442c4a4140c1102990501c0c00301c02c0c0c8218a49952114030380b500824600102440b401c81c010100140c64800010442482d12494810344801c020b003c050181c1c0d01c10489028055800c0c00c0200d613800d01160 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 618201717 1250 618200467 618200489
    0x1b040f0e0a1e06020d020301050a0605130918052d010b010e0409060b1203040e060d020d0f06060506160c060e0105030714040b2107260603101b0810 65
    0x9581c2d02c45002d005106914038150440100e004000100144002c2c41d0707507443d400005071a541042e00340940782085810000c1804001c021103010341d2522180310b002c4903143c130740118040d20310b0007100400000300400240140700b003d10080310125915084050740700b90350a00c3c00c04004051000d426607422010a5001c1182d4202d06190380c00e042d04078800c82400340744042085258040410b410700644044a901d9400c08034041c4407641c0081d035807a80285044078a403581c0e54083c1c00080120701c0710500104850070340c00b455401c202c3e86030010b10040c40018003440d01c900c042e008541000d401d45400b1140402080000700d8405e020b000b1105004206a541b941590707520141520190440203001c6203590b401d00000500000b07070801007018500814146039843c0400c031101e800c0f8000504804140401c5242c2201c1c0000312760040d448000e4240310341d000984809010900300398401042c0640f050074040001c0f60150b4001c1c18498031100e075503a90f4503556680402c200703562014010605114 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 618202967 1250 618201717 618201733
    0x50a06060507080d02070f03090602150105060f07060b090109091703040b0408181f0f110c0d0c0b030a1401090507020c15190f090807030b0105211b040f0e 68
    0x82d0b0f07200182c50b0a0510010051514400d91240889015409000c400040101005120082e8140140c681030305030340300c801049504040000e001070245005400000c3c6010692034240000d90301700540d11000600918500e50b110002d1f40302800c04503400303449184913842042c1440238001c0803a807242c0e81101000e5070075281c5664842d8164010320150b00074400f12885c071001c07503442c56000003003a400c001f481103107002c44510140542090092032400d00c5070318082603410b400086007000390401e04942c0d0b00c070701c2c00d035510305039079081a16001641c03c0d24002c0300b01706612000780e204002030001c0c003c803c90b030f0381c4c3c5e901c02c1d42040c0c40d402c0740c0150042c0c21070361780418641403ea056070820142c04000e1402d1100c404d000010303d0040c500d0450020b5204039510b02e650780c000248402070300201c0f01400e8118110384410060641c10321605c0e008903412049240d1940358181d0106444501c18192201c085200b0582840380d06402c070020310a038a010302122019041d8810301c512445418040c000072 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 618204217 1250 618202967 618202973
    0x709141509060306030a0c0b0d050a05190c0201151419030f080d14130309120b010b090123040504060603090f062a03091401050f01120c050919050a06060507 69
    0x1a80026150a03014400e01b9040f000003040c0d00380c5070000c1c0c601000c40503107510200ca4041c00341c402c0039013445859480c020034060542d050303002e89040401e0882c07001c66001c4501000303d00411010710200307410518100d01040132a1501160400180200d82030142c50360710304188104a10344e8800241641c411901103000a0201c0c8054080420b4101c0000b038002181102800452002c651103da48000a03800d01e08154010340d072800946101103041c8800344c5c45646070b05d0511010f006040c41913501060a803030b182e1242d05080220356604d0081070001d403607111486540d4000d030043c144940d040807804500c280c801e109400060ba000301d00c10344c2400e0103445071002003004042e0031401d02c0104000c00d0400b40003240355018100c20b983d000540e10241e00b454946141e0005004400740d0410050245021180c0101030550b05464443d41c442ca0083c80c0819002c00980e00071900141d005013004000b6012024a200c003003d10b0b0b03c1403255030341d924035107411550580501c40c00f0038070500002001c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 618205467 1250 618204217 618204229
    0x91104060e220314030423122d0c07061202030c0a03020901140c03120a050402010906110309091014010306180207020103020412050c1008010e220b0709141509 70
    0xc41d8000c4c184010512107003030615400342c0c41102c0c02c3e11f4061001c00c54015082801d041d00404218110150461140740600006207100c2d80030701a0f103900c039075101c01038080f007800308510b4001514407025560386008802941c442e81a0f02c21030001c9030500382c1c2d00c0c100364402d00849100380b8800b0308103450310992071401d400075017000035181d0400171091100107001c00140e0040203024441c2004544614030350301350707043c42600101240492400c213000d020050360800c41a0050320902e00f001c91115000b544581d1841c010840180e502c40007c2042c40b00c00c1c02407803042d00c1070380d54125085d500d4503070840040d000d0f81c22500c590f017090041c0f00101c0321005030550250924a20500d405881c2c035a0f18006c42004001c1a1001c0e903150700a0002441c07245490803484146100d9414001c0c625890000b142c1d0001d40028841c4000703440801c8601407840c1909141c8403840c0c2d11042d50000c509100d1801043d151450050031200d00369074140305183e1030b20380404860060b03d108414a05240b1400b8482 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 618206717 1250 618205467 618205531
    0x303090501150f170a11060903150708071e0206041b170601140118061b05060f070807090e011502010902130203100f1224091104060e 59
    0x80d503556a01140c09100c2c080480110041c4000100300c40c0c00b9082001040750070301ca0b50b0002c405584103135080f6001440b2552030201c0300c0c8040310075540b50b610718008a0b04100041a540c0781c00d0441d8003c214620303401c02d102501681555071849030503551030042c0201c01851108901c0540c1c000750018001807285054585011403480c0b40d425000c1e51000403030100752000780d03030400540003600140070030b4a9040b44082115802d01c0c1090104041090502030f80600d03000350310800c14800c201c4006005904072800095602600312441803800b10f0380b130401d88805490700340001f4134810220304480e21640203807064481a68007209945d20701101051006400c180c01c10642d52240c410740050790740c032155802003000207003026950745055080c01600c80c105410520300545c0402040c0644050b4461090010360b100e001e0b0040c1c000c401131a00590b0f10081e107022070300c904000c1c001007040b204500205032140305407828041d298460185052b040b07030440d2021001d0142c0300a01d030020b1400e924040e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 618207967 1250 618206717 618206723
    0x1080406051b04061e03110d020c07030213050f0601050c250e0108420601030b0a080304060e100f080a0e07060e0f1203090126270105090604030309 65
    0x90003070600b11281000e41c0c0c02c982c0c0b005004c41c00c1140342508464217001e91100030041440d040100340940000d040044c020001c500c0025a0f02240280001904110150165400400104980c0724030300c0020080c0008542444030300e000540813802c554003540030b480134101305101030f040c04600010131511002000c0f040c1c845a40402d6800100e502d511010140608900c0020741600a06052a2011514001d041c5400c1c10401000e25851903100500c0c0f107101d425842c941c60380e984503040128050040740051690000d9508000515880004010b008403052134079030a544020034800c100c2c030300001e49143e0000c42d07120304041c1c4041c0d101d032000c6a40148424000520b1000154180e803a124031071300302d9808602c0410889500b441c2c0341e40142c0e075000c4100c1d2100034039072705059400d0b00ca001d42d41100e03040c40f1003920f800880c800542c88400c117040380545140311902e011b014140120b00c0f9801c03061000d8000f0014690080c4043c040c1c42e104a2501008000303a0722584e50031801041015401d07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 618209217 1250 618207967 618207991
    0x60b13292101270b07050f07050d08070909060503060403030b150423030a12050d0902222405010c0c0905090c121906021821060c090108040605 63
    0x782400d500c6249499124040381c0c0d00004843d003c1c0403003440c0180b95a40305000d00860080c40a0000e01e0031021140e02900500d00182c40d01000888541d99001d00300c001030071400b402e80307451000c950020445203d901e540d134440c000300d030f07850074106c2c112441030090b603402d500034000050100e8002d0304220701c182005031009c5040140341c451407083e500950003503a030b11401c0503800440c1c01194403207030034064411805000d270701c20955155a4200b40104807070003400000f051086560080780d0008015076000b0b024050400c845a5410184071440c455414185141c280640035168046035201c490103400c1101d211050700b043d0065403007a055202c11103072001a000c010800e601d403802054043d00004000303280054404007044910100000e0134080c1d0fa02c8100044140ea8001d0381e081042500003000507912040c0511229003d420b14a41d50707000450062600c21441c0b80d0001010921038481c180c40041d02e23a40894042c5101d02c48855000454480102e03010801c95400706421028031130751 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 618210467 1250 618209217 618209239
    0x803060a05090109020702030c09070203070b0613020a030b040f09050a030e1302180907020d0903020904080d1d15040c0b0d0603060c0e040617060c070309050301020304060b1329 78
    0x5882e110b00b6040384101d07a4011480e001181410000840441c004407a07080c29803a141400a50360b0148800142072526264081030040d103030a1080c540e2065212015551619844c4000d07000c0c0c690220701c0782c029403a0281204d44255188903658505a012025114013800e0340c80848140b1303007a01000d50703c05d1681e041351000525520042c51050b0340004228461410034041080e54800240b0352000e541054a000c00c407180d000c40540700366903040703601c81001d85560801c00f00702e0143e04400c4032000d03d4072069a940301d4100e402d0300e044182d09422101d0740941c031800d1840285066400030b1445640890038403c6140e9800a0a04400011400681c01d070350398840e1420348921050020104002948803c020706003801800c0203090042000d520301e040202707440c2d554441c010b00150305244045809010188039007146402044010000c0d9124240303070500300000c10f03200303449520031030946075035800c04030840c000e11042e44000c40282c0012000081041008901c01c0c8034594400381c105a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 618211717 1250 618210467 618210469
    0x2180901060503100f0f060b160302030f0c0a1509030e010f05090a0f0501090e040c060f02210316081b0a050c070f08060f1303030c0e06070b04230a0803060a05 70
    0x30000d51001038030004140c140010908504031b41c6800e10380b07000b0508188080c0210f6002c80100c806828004a04000445407814101c1c2907001d0803051050b40720b400540081c0c02d0300002503055620b4026143c103030132440d0501580742161450f240081c042440948803841541c01021000259030050925030303e450b6800d0000340360013515801080c04e00b4003c031000d102030b590140701c400c05056030402a415034201911594103841580c0704190400268402c0c26031880e200307100180800101c0c60f058075480360865501403d031b8100325a0517501210b00d62400c81414841c04007540205141d90b000c041c84009082200c0041e48450025424844200603c150020003000f05a00a00102243c1c0307113241d080901032403e0100207030911040300580c40034052030402030b0000ba4081c65150a0006141058500a0b2400f1310054801544030341b01144200c10b204242d80c415218034400c0194503140140d9401c00640e802652071101281e61110b1941000103c580d401550000401030045c42442d0b0303150 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 618212967 1250 618211717 618211723
    0x20114121801020a0c0204051008101a040902090f101d0a0f1418010b04140f160251010501050304020f040c1101020d090c05030303010302180901060503 67
    0xe4580120046080c04005410360752040006940715040025894101c01010080c2506010400a44a184c1d03910201d60181405180c0742c3c001d0510700d0544000802e0000300342c3c02400b084100001001d800c0e0b0007e4034514140c8101070345a64002c1c00010301e9102d1001904014000900710135412480c0030300820701045103554240720207003001441e07040d4a000d4581d442034a00d8603044059480c1001d007031584a0700c500c01026400350780e8080500c03c403a41038095601600c00302480b075070071030305e0400c08080c0045140d1b41a88103626800c40c00d001625440085150399040404d1440182c102ca0300c403003030103205601c1c0410240d6001d20450800e06044195010740180c0a0700610306000c44d1202510001009100c0c5004240c00d0030500d06600e0a0740209000c542142781c030500c00c03a540e0b2030341c01040d0b018000d2400c0d40347d00000210744032640c0000940c0200310000e400e40b48401600780000ba28900002282c0c1030700d40c041c0a920000ca6008103080c841000908401d10039500c43e8004130f50307a2010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 618214217 1250 618212967 618212977
    0x8010f021c0509120d090c0b180118031a01050910050a0b0c071a040812161203020c010903051809010b0d0e0f0609061b0910051e0403050c09090d0c0b04020114 70
    0x81d000010094900e21f010100d41c080f50303018905d07030300050040c021012203480c100c0c08035203005c0c2400080603031040303c9801c4414854000500c8c80c2c0c0300700032607000c51441080d00d6050329800d84d0710340c0c02c0303484002400c0d43d020302ca8859994810021041806980c0030310700036011000402c401c8560254948160000d59440845890110030b00231508022141c410004280342e0580302031810b1800c0c1c5070790710a02c1d0703104400001518002c00c550050780b050b0311950488900d061040020080580140380041255000301c0c40d164000c502c1c0c01900080f0300e0140c18240c100ca10450303000d8580328014486c0c1c2c0c09448000070000150007410158440400c0500c0302c0c40c403171040000640318601e80b01120503d01951b000441c90404c40502040c8596201c4050702c214002040c10015102c078850b801d00e5000703034001102d100342c07900040b60010800c000010382c58080d1800f20b940c1052540d030700c100345030381c3c40c28072030a54006004009401c0c0443c20360700740740b0b80040c010324080380d0006400c0f9002c6816401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 618215467 1250 618214217 618214237
    0x1020f030f100e0c0304020d140f07050604061d06090d0f0203010c030c050a1107260607030203100b0304030201110304120305071818230108010f021c050912 69
    0x10010411960259a45000d41e100b1603400d41c010b0510309086140c44045002404455a2400040807509640c0d515001c4461150b0215400312020340c0d40d281e0688030016114140c00c14404c200e0003055074903254056030f042c0d0300203130345000d00c0208411049810710020804250029403c000001054540c03068200c07015020794401c0100f40301501c10f01d801c490036100c04134101403a00d01d2428256070b003e03003200c1d1060b82a2610a104041c540c1074103046c4a002d0b40100c40314803036103030403001d050481503428440c0124082640c20b640d403401c43c01e030244d1100300c5041d144007500b10424070000302c1e01c60165070814000e200003e900f003102520310405a0003540c080c0d404103034907818280510341c980140b81d404405071600344403041410f02030610a00107130240c40711840c4103003a074100f04102e55009505030200300300c0c940301100300042c0300b0142000038055000c03203508100c60002000e0140c02222052603403007800d04400030302e03110103000074000034081405c1e60045408103562071944602070601c03070007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 618216717 1250 618215467 618215497
    0x3091a1603240825030816060e190302060f010f0308180307030b0103050c01030c02030d1808040b04180905031608090405010b0406030b010201050609040212030c12040e150f010318050102 82
    0x203544c421511a0900d0094101074a0043e80c1e8140b00041721503090701c0010340302c00c10407010001945040700c050300400f141c100c03003071280220800f01581c41005c1c1011050090302035444c1c5032541910103200c210240070b1400c00e4031001d030003000028001002004002c1114a0b4407c0a0201000090403da03140e401610174001c600014001e1144c18002c080c40e204003400d00b040402000340002e500e900907450101c50740755454640420b52101301784200d600da03502580c0541d64644920307006400b81c005004000c80c2c64004401032207400356600c504c4101d5500031700214104600c081c9a00c5482c840b00c0000c643d005c0d020301c4614580d813218020b060192100342a51a180da05108001b012950242041c0d8116030511f41480416203a0b0045241c109070143c0381d55a6034180f1074520b615510070828010454400c02e14500720030014440504141d9120220007042c0b62a83c05502000e03901c5040720b2584100c444080c0800c96010f07600810400031501c00e428190421038583d242244c00c5500002c043e45 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 618217967 1250 618216717 618216733
    0x3030d0e07170309010903021c02032d06070c2910181e11120c070201020c0f1e03010608030409060e0f1909060f060603091a16032408 59
    0x1030802c60412415a41c400843c108809440000e1210303000d44000381c0074140311010105000c124012034041d898014040750080300e59292800c0c501046501e00c00086102d41410540514001c40d02e14094032031070381c034a80ca0110307544030108400548008080b00c2410301c2590f4441307500c203040c0240b0828181d982010001d1528100e42c1c40580c0d1200c0d03030004140b50101401c080d020060080800e402406000140720f0303000c80203000c02d841a5000c40d6440ea0035001000940b544d00f0300207140280c03007a400d94000c0001e00e014000400b0340e07002c6090780b090000e60582680d50708224504030304040100042401607031889100d00315070203a045841c00503100c2105205800b540f176221900205003621b0703401c083c54004103480008601ca4105911181c50b8030014060000540100f070600140f140c0400c0710545d2114050014a91405c04450b0103881c140019240d04034658224440c2002c0900120103a0761400c0032001030010700091100c10420240a541c00c6941195000113001da000040540c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 618219217 1250 618217967 618217979
    0xa151d0d080a06061b081204080304060b0904082508161a100b032806150f050301050d0807050d05090109140a2601110301060e010c0c0b070203030d0e07 67
    0x2001004082c840d985003000d10820010b548210045c200b003001c04140028a01c503850102c0040c0302e004071486071a16083c040c001441034020085000e50302c181810051011183e00703101d03082e901103c1c00742000f0740c00d000b00d0140c01d802202014003d1080c040f9a8511802d550f1100c803281c01c5a60301844600704004203804014507809004030501109400c1c031741030724080c51918880f0440c0d0189482543e000b00108440c08042d400800c0c8050381d24050603c10542545640d008010a114081c00e042e40c2e4100103806034046c00140464028a5440600c0c41c1c1c2040b0030b100d051000c080e012208000d04105500110300c0602c80151f800712507580da00d99030300c41038000600310a030580080d42030b9089040306505994841901d10200c50840f690040ea00c0c01300c0140740b0784800202402d043c15402c04c41031001d4403a108000f141030700c44549070203032450b4110004683c0c4c0c0b40d07040e00c002c2030a8404203080c4140c10341341000d070407403610040440b0300d49003242100900b074881c822001e442c03d0307205405c14011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 618220467 1250 618219217 618219227
    0x1030e0a23010b090f0105060a0216060f080703020702090420040207110102010b06040f03200607060605010311070b010b0d090f05070e01050915090403050d0e101802030a151d0d 78
    0x14801c04513030742c0c074050905944010f0041818455a4410b940000b402281c040c000c1c000443c0c4400f03010003809a442e44c46e40043c08101080d1540f800041100740040d160398060b00c02d072000203030050700b40c0c00a980c1d950b40e81014140c0e90040031f00070001c1d0703141c5410f8a80d02e5000600502c1d20031000c40120408100c0060b0940f41d40c0000340d441140b00380700c14802d00c40d00740000012a0341200d4443c210847c4061299034068011000740d03080035000481e01300380a0b2541281c02225030030390307003009418a503680c1309995000303044004000000d0303c00100b1a450b8100080c00c1000803400001030142c65640c0e507000d1800a600d4204c4503500402020000803200e078610798010241a1003481d41c1d80b81034101b244040c0d01d420281403080c000c1d10086820306105205840c80300c1e03000581000004501e0a60b2591202e485081080d164107180b41181c0581c1c0c0302007542c5120381e02030f00600320a54583e440b034002004200707502c2d131660360720484281e82540c8a511604c0e0824800c0140220104d50800101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 618221717 1250 618220467 618220481
    0x2001020601030302062208030f090c0a060906080417121b1306031a030d051c0e032d0406030903020607110c150f04080c13061401030e0a2301 62
    0x10540d00810010008680c000c00d00c9584000103d407001c0214400302c409070343c03000001002801500c4d0220030403400b00035001660380200c265074200c0708ca0100040420110004034054400000c100000801c0014022a070f03054125226000d110021540c1003108900ca800840c14215454008024000c503088114848840718541c10285440c041141180743c00400039481840200b641d1441c80e00c4a203c0c04420742030807038a00a00b640c007040d41200d0300610a0f00640070002800885601c004910b0030a44a080c3c031240d16040030354240300d04100d84100e0050013503142c00c0c0340400d520707400780c4560710400200082c14032614000b5900e0282e05000b03140c00b07030041485040c0701c003010380c1444406000512940d0481c04558140c1344e8617404070343c20061301404a0548080501040100f07402e80c001c241c4d1441040140d500250f41025094114182e42c0503120b000388001604822a100b544250045003110445800306c680341c22440d684c003e0030005804120b108841c6140f00c56038110000e000d108 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 618222967 1250 618221717 618221719
    0x3040f0902030105060f0c0c2d01170a0506030f0a080a080c2a030c030304050109021207061e090b210c09010806040506010201090f0c091d0309120304090920 69
    0x14210360420020176218450300e07011000265012942058912081100a03d080300103060340589004803000b0780030401100c20240c80e0380b824104400c203e548200d00000d00c84d0300c00d454a5107140ca40030f071160001d000180c00c45425018894403001241010040e02544074418005140c0c1c03001c0382a030080603084098545840701404004108a0a80c0c4040b0040c1c505101070f20326800540140207280b6603c1156003806440c003000c400c0205100040d4841407840f03000752040510080e4007580030351945500c0c0a8040494004000d2101c0c031a50380d2002170300200c00303041c000180c0b1b0321540b00f001c1075040050501070100c03498031866090001103031990f801c07100d0725051504001d0150000303050604001c0140707000d169600000b62442e8401d4118030641e0f50018104400d18120f03040c43d42d58806103020f0050601c0c101b034043c41d01408591071200c081e107029009036003406034500801c0900d0403504114a514402030102040791a41407043c4401d00780b16400211842840c072489001000451307080c0303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 618224217 1250 618222967 618222971
    0x120308070c1a150a03080403050715050304030f05070803150a0f080a0b040c0506040b03090f1501030b060d06060605070c080c0108130f08070f1a0405030a0f030b04090503040f09 78
    0x9140056030700080d110104192540a024030340d200340141c01c000c030741c40040d5a4400110413000080c4895071008101b40d80c060001d40b9042030b110008804116241c0500d003002900410000300400d200b41080c202d907200070300d0030030710b170a940ba00c800350a50015541040011900c841d00448c80c5096404000100f0a00200903c2d09103000302e85500e85901c544040e220010182c001010040407006210161100802c0c8548454a40c0c1c4514503e40040340e008000e8822443c2e88080b94070000356014014143d070b0b0b4103070038030303821030384c41c03c1c007030b40c1c02416054120460381d000000240707486c00360382d026200ea999059110790786410111b102a045a000300a1900a41942c50a03039a0260217154007002d80301d8a0242c207072940c9441013150340c2110001c0e05006000c9401803c01081c140405d40d4240a020f03400c10390010010070400e84002a50018810340c0100503804400b805460905402c50540c2000241c540170340c00030406403a40c00d101103506810000d002d0183c0e00c000c1400c00040e0041040c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 618225467 1250 618224217 618224237
    0x910030c0e0a0503030d020f041d07022b050901110607020105060a120b01290c0606090a0c1205060117090d020607050c031c0209041e180b0a0c02070e0112030807 71
    0x10070b44a00c5a041d10106c0560001444090111500308840041180d1860000c4580da400303509081c020040e9a88401805941083d12410740c008100074203100d10b007548003166a44070942502d0b141c2c0295070983c10701c80350b051104420718040c0f102c2c03841080c2e607400206c0c9920302a0100f02d0981d500e50024141c100c100b8081d0b9003c02c05240c0b0341070645400d070400b0320343c100419a0a021951190890240070360300024140a030010104005014010540d103880c41602d82050f10016601c0007508100011800160b441c0e0a030000d403c09a0402c0c810305140110f00401482280e510390111400c411990104006c0c0510311760400603640c1c400c180b8a0880d0500c0d200c0840f41ea00d0f485451000c4002040c12110303100200b8143e412035052440003007040000c04060a101900f400d4098440e6038198503000862000211095200404541c4a441110b1555175044000000d02d01d501224045104402002c00c1c507604103040203018000c3c80302260701070026450000d1151100401c480108008082 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 618226717 1250 618225467 618225469
    0x20c0411030f0c2b110a020c040c0908011404050f241b030f0601020709021806071b03140105090c090109020d11041517070e150910030c0e0a05 63
    0x1540d41104078210720800985482c0d81c1c201440c0107013515407544401061011240c603003241105011007180160922102d02c2d0000c1c1d43d480c9000c0c0034072150160b00700e0f0000004d1443e00e0b07440461079009608159481c00c0e142c0404d5070845118041400100180000344000d22800300690703441400e07524001c2c031040000c03589442080418402d0112012402070108000400441440200c050344640e26500c81c54000c42098003520103a030041d0160107255400f2130004802e008564840c080a540803007c1c440f21814403001c0d07400130fa0b0aa80d5003012180300f6848559181c0540000e500407040390b11a501c914001d1421140302404541065003c0b4540242e00d403600c403401030440b84407000041c2c6503020b0884902c050000c80317143c015501c1c030001e00415000415104525002010342d1100413064928503106050b207002c0d25640089050081d00c42014a0200c481d446440000c84196003040700c0800416441580c518401021946031180c2a00d0160b2100782c1610310b00d42181c0702d2809a107814 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 618227967 1250 618226717 618226751
    0x51305031b0109060f0902180106020c01050d111305090c030f01060e040e01050f0a15080307110a0306050a0f0b01051602270a0f06060809070b181c0201020c04 70
    0x401d01c00407100d0020404550400e0a60107520820340000c070034883d01d161800400700078480b443d0220f10841030991110035a0341c100341080d060343c60ba80c0003403200c074082034015520340d001110300c44442c42e1a5886001d4030308081c3c000c0c1241c015020310790080c0504100412464050083c18120702e144107008114031540c00b4060581180c0150803c44880490400850054020181c5002c6250b08210a00861140e450a20752140d4180a020010300c5040c4d400c0306000c2c1040e221351f81040c2d0003800080041036600f04455215400201400503ca5882e501d074000c1d0f440442d1482000d0350307030b042404250200d9000d1240c10240910304545410b4000c05103080030782344580041c0c000c1c140703234041c0c80c41d800e4031402001c5441801c000d46500c81c81c0c03009809024182114070880c466080c02000200c0e18010b0490a000c2d00c12034018010080c20050141d01079000f0685100c5266070a00401511351903c001140700d08a18040891111042c3c0c000a842c003601d600100d40101c0c81d200506c40002c49503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 618229217 1250 618227967 618227977
    0x618010801120c1e090203040c052b02060d061701020901090b030402010f0e19030f11030c130906060f14040b010807050906030402031c0207030b13080409180c0605090405130503 78
    0xc4d021075800c581115441000c00f6180c0c00102c5680d00c00814030060254040428049603000c56000408150101e44980700ca4003113244a482400180b0705034006291110240c402c0014030340c000100140e0780d011018101d00b400c1035215182c0d6000540ca03a603540c2c0304020a014005200d180d03840c501301903000801d4886aa80504100560308002c01c200d50f55039002d0b07101c500d25010b070010f01c59841e418181030140c10340030210303a015401058981c2e80c1c20081042da680e148001c2070402690782d41d04548000d454012001c03503203603683c1e99000c41d641c02707141d02403070103070108000300c12102103414248000c94030040c80b2241842003c00420210325408811280120016148592691500d10200703190050341d4107014504d0049031200020907a00241060460b13010b907c400000e80c0b65000c1d80b504d900f40c03001026003a07a4007088180210380d46034105248a0105500a0205585544030710f407201003180c12000c00108001a00c103281d01c0c2a00659400030030b0789401d07454a803825a0389036940c5c459 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 618230467 1250 618229217 618229229
    0xb01320c060103030c3008090a020604060203090420030408070309081f050a0509060a0b0105040b0307050705060a0204050d02040506212a0a03030c03020a0b1608010605360618010801120c 82
    0x1891001423200c0c0b4040c030402c092035074060300c119100d80c0c459401035207035001241d51500072464000c0140a4150b0305101200d005807800d0707076500d1350b03d95441708407c50384641020342c28003040c9280010703c400100303c00400c19500e242e0105090074099104401d41c0c40140c100d410b65800c0101384940c03198040350b1039400242444000884074414401070310302c0c0c0102c0e40b081060781c0340401000710030740c0c00000500c2d07502c6c412810703a45243c0d11944a80102e025134010160000f200b180c04000600705035201a810a5000b4440c00d5008919104102880c424940b81860341e007100d48004910311404c04c81c08092020014940b04659030500030548894040c44060100460130030008103043c000d02034100c11941101500a9a241154203401139003030b65282c03840001c82e80800014201d02c00c0003920a400e000c201c0405441400000c120f0050054007241d0700e10554004050744c142c0c0e2030b80001c1403220701202a110905070514000340030340c64140e2003405904c0403005400c00140041c900d40c415162 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 618231717 1250 618230467 618230477
    0x3030504030e240c160b0403060e1c050d06080607021606030c0806061809010803070b1e130221060a1503033006060e040b01320c060103030c30 63
    0x2980304c07241c3e141400120701c43c0e201618403032012400101201c010020b8074003550301409451219202e1581e04c0c8400c207203500c10459500d0383c0704046803107203000380f00042d12a040400d005403212180d5050441c00d85440c000359000c01c4400e21000d49840011000f003041d07050410400005000103084200000d2607184a50ba0000741050390140c0e0342c80c01d501041014080540d590b0310f84a200769260b2100b18166100f040c00800216030b4200c04088200300d40742440081025106d50054115204120340101d0340102104040348001e00403000520384031040400a1540341840c0710800100c803401d0001c0004141000c5040c00440d030000c00a00071454605510f0300c940e500901147c00d4544200300b00101c0d03e09103100010110307800442c040f968a03080b6001c01803409403800640e143c1d604075548880b0065480110700f221424100c940080d41a407210b03461403d030082503540e003031660903001140410440f0f0340e02c0090081c03d0f550230309007544403042c64030100d1609486048d0401d0b03030058602000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 618232967 1250 618231717 618231727
    0x203090a0b0a0204032406080c0d08071403030a06030618030e0105030a06080d050c0118111e0901080114090a0201050d27030f021212061c0f03030504030e24 69
    0x101881d0b04aa00179034100080c036001c081c8600c0070f5146201030f283c000000d00d0401c88040b034440c41c0800d090f1081c0500a20811021400d84d45100440e00440720a54240c218030090220a14061008501c182c1124a00003101811440e0840c1200d000e0803000b01d292581c1c0340301d030002035041444060400300c2400c01e1a22a9558900403016011a41107002c0c00e00913a601c0004141d0010040d002c0784000b84028428801d00480c4402060035400019080c124140305075521030400d0364002180340304044d821030b400001000801c8903e0021fa000701140d80d074903d42c64154060380040f0a400455035009021062860b400081c45402600c10340d00301a035888210b00c0c40003003180404000c0b41d10707800d050406000d0500b0090214952008000c1c050b020710703030480852007440c0701102c0ca8041ca040300719040d502c59034103125200d0b14050103d0000000d8603110004512005901070105100c1e9034041658501858002c2210691141c10b40c003540740d84008405121582502030ac4490128040a80350 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 618234217 1250 618232967 618232981
    0xe1f020f010f05100b1c09050109030e010c03121d010e030a030e06070c061508010905012405010206151203120718030818280302030c2b020301020904060618090203090a0b 75
    0x25180b0803406c109892600d10101d00700401904071800c1c96000c4c5d1203116400d440e07840192501c4c2400c1100400003132610302c00c41a0200300d54880c405000c400d00c520650300100110003400c4904a9a80c02c2d2203500c0400d20000543d4503024415821501d00090100c40c24049000381c100034180707800411a036120064030408c3c3c0008540310004100e41002404030a04e1810b2450080040b00d440492200020151801e2080104680341c115001a03000300701c00d940700441c9100303090041d003803268400e4110000e401d1000080019081c41d01e0b0a1040d0309240c141a84060a0000300d00c10819aa0754030540c100085042e580941e401c900100c801c0400c00ea107d180040c2500c030380d169030842030b41010040036011038007440344034090700e200707030f00b103a07142440d02c41040350698140c9080c0c0c07001e0340c1c00d25040c08103059000018540a102800250510040031300180580708a03800c0f98000808141e0148807400d0306203144401030401c1c420851843c100004126100c010040003c3c0219401c000480d8032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 618235467 1250 618234217 618234247
    0x1061803080c0307020901170f0706020a08090a05060301083a0806010c0c0f0807051c1b090c030e011a0a0504020a05040906060512180a02010e1f020f010f05100b 71
    0x8010360040009506d0740c3c4980f5204000711551003446410310074080d01c1c4500520004001081e500e40360000e15606040b683c0d00aa00c0c0c0c07100700c0283c1c01441c000000030386511010042c41c080d00500000e0885200048100104600000c1d20b0102450004020f00e4828a007885915503400c01032500050994480e00142c0f01c0f441000b45c0100b40c401030410000da03000300d02c61030406481413881520b800796034170002c10110001a0a0109041d911007080000040c0b10300e005030044482c0308007150100c0c0d035600300d600440c0c9080001c000800d44500030403803142c0d802c3c40703032000080c28090ba030300c03070440c03110701042120905000e142d00880d07001039900c1c81c4600070025034000300b0310041c092024549489000b030260b0058040064450500c40c08a03d031131424101d00101034204800030075142105400450704020305100d006e0304002c1c045003840440f0315590300f03200104d886070000e010060034864002e00312011400c800b40c0f014600800c0c08450f00226905604903001d084400743c03108001c07a41100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 618236717 1250 618235467 618235477
    0xa020c030a12030e0304050a090221090610050612010b09030703170c0c0916200307050a031115060405042a0501080606030408090d050c0307031a01061803080c03 71
    0xd8984209444481046405800719006100595090050603801410340d50780b80138a001d0b0640c00401e0990074807400c06141c0c00b402c540401500c00103008080c00301c018541c0038003030b100031800b9005a020054050149451800208010385c1d0452915040c84014071440c0741c1800707404250840002d040e09e1907a0104200d001450300b00100d00406809070744203a0a690003440388050600461035a0041c601d4810051889020440414194038009500407241d0b0809030403500c009100016150000c03010801c041c1208074030601c0188501a19070402401d401c00b040d0080b0415400f120b20030016101030b041280d0000400d81d0f0109443c1c84914100040c0000080e96000e800e00c0d1580c100761042d0b002c042c00e4202d03002070721610040e45440c000e010040c030048034094000c0c0ca08100380407036820202d48500d5a41d004205aa0101e000d03400081d050040c1d03640159200440c28130180303aa101c00c02481801050542400d465034152001c0d0351b11450518070010b00424400326000350340d8002031003210 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 618237967 1250 618236717 618236719
    0x19030c020f1906050712020601061e090f0806070e090603071211031609051302010c030c030c20090609010311011808160311030c061c090602030f0403080708100306020a020c 76
    0x102c00325842e4580284142c00082041c0c0d07006407510002041a070001c074405045c0d540076584c603080010004040c0c40000700b004040d00420003210000100b0b40f00c0c50030004080e00b4044082d01740ca04100e10020456070840c40442c2c400e0300c41c4400d010895800064200480340201f11484810002d424010400417142010b59058016554985003101d91030f13000d80d040e603074140c80820560f16000e103c2c030000264503400a011516172a12140864052130403110500c1c0729142c01500c0441540d42c02c1c0c0c003035078891120900721100070103110141ca0844001d551000050380d4150f1950300d103846a030007031601100e200d814000c482d2a5240030958003c03617180030340364400c229500b400109540d200b8503010b6220640f842c5000b503510007898640802e45091100004040d0b0341407904400752044032054015400c079030b19a80e10000c1001412900246105854600444249107090f00740a401010010b040c04200550207080044404145083d40c5c02d41ea00075500603101e0380d610a042c0c0c54446076000075 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 618239217 1250 618237967 618238009
    0x4081519090602074106011a070609030306080c0105070503040e0c0d0c09050907020318060c030c0105040506310b0406060e040c030204110414060c15070e0319030c020f 74
    0x10b01c80507058403030900c0310a030311013450002184010321800e8004400b07945ca0041500b11500401c40420003240c00d01415900c0c3c0c41040c506059662218226003010108501183e12118104080170090080b164101c4003030a00701d241801c41d070b503602e03200d12840c010b01c02e2101140001c0f4020b12000306c01c0d19480c04c1c10a0b4100b00ca04090310300039011021324071686116075109400a031440e440170040c1c402c4041032260014100c0107030020880a60040c44400b00c11b40f0080c482e0550602017401101d015074051805860903080540c00390100441c602e0305101400d42408000943c20459010041416081820340742d26031245c0ca006006001340b64030a285800c0d021007800284990f0240c0300d01140e100301c8082000359090364881d01d55000da4070808550099402083d1883d041200081c414240702c4000c2e04c000b820f05040b81131100c1015a0701030005481805540600d0a0800040c88a103090038158142440c95540c010190280d200c0001d0040d500c14120f090305880d000c032250010f031681014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 618240467 1250 618239217 618239243
    0x30724090b09030702091b0909040203100204031109061008070302030402041b0e1002010c1b14070b030703240303051803061807050f0d032102030c0408151909060207 73
    0x1003030303407500f0244051b07215092500121b9140c810400082804000143c402410080d41d4810403034030000041c01170340c0501803110807044515280c801400954411201400300e11200010b0001e00b20300184210f00820b48000e9a200f031541080c3c2c03050344501c9914015a0301d80d070340e00c0490064a141070f216001c281440c0d00c0c0204003a000340003484551400d41e401003c0d562855022401c0c0c904003050748010603200c821b4026407400941121202900921480801c01c0e0703000c040c117141120715800541c3c0ca01c03000c010700c0207203941030103158218481d03698a00c0e04200c200c003d0030406041e43c44010180000050b50b0480312881c002c2c3c0d84c001c0140281613442610b000e4031071000d20715000b0724001150040250101d640e00d001c45440d441c00d800544505417070366031a6403e582c414465240c1c0403500b500040205602d100c0d50000350b1054500c0c9050031b44551814402601d0603911001002c0307d00100c50821200324640d0b003c0c80040c01c004040861700b140b540c20020020303c95902c0c007a00030180000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 618241717 1250 618240467 618240481
    0x2a0f060c14032701170411010f032c10090503030a020304031205040507090b0d050705280b070201080c160312060305010501030803180604030f0c032105040b060102030724090b 77
    0x480d000b0824003030f01c405200f0740790a00e01c0c0000100466004044040b0703030b8134100303581d481618140030703009d1103080000f4203002c2580000d58560000308201c142d443c01d5410710b4010a030600400a13103410b84002070010203080e0755401d48a007c0208140102a8080300007824584200c0d110540d0410001c0304102c60b050900300f0f1078583d0076500911317008909100b0020141d080080c00220f0554005d0040c001180c01e14081200b08862000700440c803040004402c1c0c445900016400b0040c00800030050303641c40c40b4170015120f408020400d01e51070106112110b00100042c1e04022000e9040c0b43c0342d001221126000030003811260030280c00c640c6840004020032107001e0040d40100c178203000300411090381140196030b80c60110740c01800504c1401c8072103c620f000d00451080c06200741090200c8400c5071640c50107400a01a03031107400b42e00c2d80c1c2400300740304000c0c048a400c91420b1003d189070011580ba05448040c83c80a081e402c180d03e007100c2c014414036a03018840c02e95106d1204031050034140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 618242967 1250 618241717 618241777
    0x705061306081306140f090a0f08090103060b12010302040f06061b02010203041a071e0c0303050903011107050105040c090606020729031008060703290d2a0f060c1403 73
    0x1111061b0090a01000c909800e5000940c1030340030b98001c011a80c1040d15542d44040364108d0010541855152a000720741c0408144c050200e407410703120380413241d42c5140100425942494080e82ca400d190110500c1055400183e9101d000003c1d030180d030401c0280d1004070f00e1441036600280319624031800810300050350000a042c442c3c014058545110001b0200d440c0680500c02c000f05103002804080001a005602520346001e008000044481440c400c2d5519a440840c040380c61b070355241d00300700801003c41d60f07140160a0410301001103508048029544065900844021004240151800d0031101c0500810103403000400c40e12400d1405480009030301a0041143e280903010000c4e41e0305221344144514000702c40705d001c0411b0711404c3d10700401e00b140100705411040c01c1d8030b10b0001c50055060140140003034410107044044114002c0b0714044e89804c810007100e2840000c014866100264140150b0401d1501e500c107901c4803211440c41c4200c846002d131a00c000174041e041d01881d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 618244217 1250 618242967 618242971
    0x3030a03060f0503150f0405071a041e0b0d0905030d09050307021e01050d0207050102070b0403120b030619020a211a030120030c120a0b03070506130608130614 70
    0x2048000b030070903150410583c54480301100c2c80d02c0302610400090f1100c800110541e0000c0c000c4050350701003034654802500030f44450311499000003001500f0415001c2c0078004c04804108c220340c401c489410100e0200c842c0c424055900b8002d0740b1281c020741480001d0040340c840c500782020401c02d4403042d150181c3c03a5000340c90b00340c0c400d85402c01c40c600c8065559072514165001603481502e01a1103c410400075007041c6000d9600359030030f121407000031b420240032b1401a0700a0320380c03107050004503400d102607880d000f00090003500948140413070341e6409c00c0105022800b0000143e00c170100088103c50103441d00c146010080031038030b901e2411071707443e41c003514000c10f42c003503006c0304501900141401da4104c81052142c10940086030036444d621a0055038010000301e04507851300f6508680144200c900b07039042800c20307944040c40082d500c2c0c1002000c00520b03040e40c0440c207000014642521200d450310a100a00c150740d070014410100c0b03140701546155000408100c041d04001540d4412842 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 618245467 1250 618244217 618244229
    0x6040b070c15110d050f070503120108120a050906071707030507061a0303071b090f0605030706080712020304030504090e0c010201060f05030d11010f111806040e010303051803030a0306 81
    0xc610b50b6010458400c1d950100e10a902c8001000022290401251140d02c51500d544010405000700e000042d028002007a40400c503d00d400c6080d41002484c07400c00050002c0e905001c5402c1200001c0709400900b0740b00024022142a0780390325a502305641000384bc0542c0d000074040019a202c1015006005480c0ca14004c103c20040900f1004d14495400c002998056241e0300a005000c001a0040c00c400008900c603a860380810756240690781c141c94103009040052902c03031101b4095410100241c030001c061074600000d4a084c00140900b8a80e0607140c5450034a4001000905043c0a0000c540051020324000c100050038005880d881d1a001a42e050065090441c000790070340380072100005a0340020060815025a41c0042d03844411a2603c01d10340d54a6a04000021006100e10714600c40024001c0b96608105405407508140741d0301d440e44244c4052206001110166512a05403507050600c00c1c0da0340c00038200314444a0388654066414480042c0124169906411920840f14 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 618246717 1250 618245467 618245489
    0x4050402042606150402160204050709060323040228030303240e07030b0319050304180603050a0f060207200103231f03052e0b0a0504020906040b070c 66
    0x1103051590321140155045003d90f104d10071140c20a04c4c180c1d000301003c00c1d0481403540301801d1913011405480085940c40082410050b04008003901401090082c9401084411303144030720380c146066246006d00b0190107500c442034100700e10700d00300341410030b03144000028000c0c140c0d413842e004001d098a004224041002c844a20345410200301b8950280c801e84482c40f2007558895100300d008010040c541c81e0300d031091080103690300c04140a84240743e8051009903540358113083c428940224440c00210145140200070000300340040b4201805035800141d142da03d01d01800c082d03010340201600601803890001b491040c02006c03900c00218200e081c0c03802d00198107807000c65088280030300c91000000426200141e200361000f03800030003440e10140710340e40f92610b03500e0300f92901d5106a014100024a01c03074003800024100030000c5819071840301481092844c80c0400c281b221544603040c0101e801095010460361804140c0700644000f908098640300b0078288603803450f80c1440f901d02005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 618247967 1250 618246717 618246779
    0x16090b030a051b1305090303100e0106081f170c03010e03121503280218070c03030c020c1918110301140f1314010b03190b060405040204 60
    0x400d0106410441540000c00b6003000c100a800c10711100c180a0141d6901458070180c4c00c441c00d0f210b2107154003591004005545034600a02c240c41d0000564115031940d01e404c10040168582c06054264403c00c150ba0301c03041c01c00c0d080500c140f28600c6402c600305c04c09001480580c81c0034006042560010102c1c0244000b5440d019415143d02c184001d54519401c86400510f00f02c1c5d40443c0c041030321301c01801b01c1e1545480110800551090009962040c400c0724201a0a5180c0548001280100c0e08000d504a05280a0203881c140b01e500c00102070507241c1500240e402c0c000e0110404100021f80405aa0300302104550900e280c1801a01a2400b03003090a800040861094400711100702c41c3c500d00e180d00700702201c080c8407041e05030158440144100c51549444030300c1c16000d140d1040c0004190041141154100d41205800420500f071092040002d1210308000c04003003c03420403800201403551002041451145410080e082800050002100503480c50310014034030a0b1400300d20a2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 618249217 1250 618247967 618247969
    0xc070b28050307022b031e020a05030a050601031a310c02150403021216061404020f040b031c1e020303091603151a0307030804150203070209040807080c16090b 70
    0x400d6030310485407072080c04200005d030341901a50006031040c10011202e2034143e2600103583c00d0742d101548000000340b0200510080d02c030640607007070300700c2002d09044c04071038a009940f501c0c404203007410038440e100510300989020074409024002c182c040005900c5c10090310510310140c0805802c01d00140b00d14141c403502070200c4244940102e81c59809440400048a101d0703015070003100b0000d148500c48081400026118804c0c641c00c0195030000010340e15082c01000003104540200a0040d8148150440309a8002c06da0540c1c40c501484a1485500010000c032041c0700c0d404142107281141040e04803081b43c0000185d8440d035040030403074a00041004511f024252540f1000b080080c1c07254010301030343c04a801022005c00c40310441154500c40c1c000003032a0400551080d00c024600240c00c1c03000035001c060002c2401d2542c00203520301000769000c69161500200050b080410206804040000b000300b142c1c020f0394418200d13540c542030b0303440d086001d080d00e1080e11009454001c1c4800f003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 618250467 1250 618249217 618249253
    0x3030e070609180518071418060901090e19050304030203011512080306010c050a03120b04021305060a0e030a0b011814070e1504030b040b0108030c070b2805030702 72
    0x80c0c8802080c074080008009588002134180980b045640312091044850200d0742005980020f00c1380500b18000001903405011203082400c130b00491040d00f0301d0800086850704541541168070381d40001848941c64030085040c014008080e240310b1100a1100c414000000080d0054038000c40c000c01001e0100720301400c442c0042d00c60255802a211a500080382c00103000d941c2c0900706052400513903000355107050404004803012800301c0d1032180c1c00c00f2071603040e04c01c42e5189803080d00c003107241c90800081060b05d1112407103110311880c1c0c00140c0700c030010b2144008040881000c0c0459411003494503001d141e140c424090011002c024403400c40240140d0b00929229284a0090b10030a45440b0350440d14600600216070b00702d8020a05401e4500103280100002c1d4026505401e4074141031038040c98000c01030f4001907070f9600612071540006d0001c01c80a0403a45174585040d80c46000540d101d00300d1030801c071016080078001e14207558107500700000b144605c0c030b1a03003903c444085005000903 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 618251717 1250 618250467 618250469
    0x4020f04051906083c1509060d0609080405061c0e0a0b0402010f02070e0a06180608070b03190f02090f030607020d0e061b010c20030a030b0d0f03030e070609 69
    0x68448408181400c0303190242d134006065200800c0ca85506840c81d01070881c1c0c508808040d1036005c2402c01c1702d110389804c210720641204a822560a081420000361340003c4910003030415981ca040340000c002c070201c00c680092401a0850b030312165880c1d1403882890101080040490410707019411101c0c0105a41e103450b540100c400209071603903001110740000340d078580c00c150320422101066009041080c103126407143c01d40132404a00301500d18884900f045000660343d41409030a1001c0a00410180203170303100c481c03903030341c980c0c1e100090303039079805191540051841d203000651013802c1e0186e0010100d00800b41c0d29541000a40802d26a503020b0132035001c0011f270000400d115515224080e50345202000900440c00c080c0d06026184041c0d00c00044001c180e99a04169203859030089040880c5078840d078207000c2101250031001e905c9100c0d848541d010140c0d121103141655a50b00411441640c0144042044014514010b40207018204000d200b078442c81e00b0009103584a298484 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 618252967 1250 618251717 618251729
    0x206150109091e0929090703060213091a0406061701090c030e010f1b09030b0f181b0a0f08070519080a050d1d01051b010b04020f040519 60
    0x602900d0320000c0c81c0100003c0ca40854080c00c40341441400030403c0c0191040a0f01400b0204031080e820002c2d0f40b50070000c0e07403610381c0d815404800c1140101c008650070701101c2e082403016a4607000642c240040302050b0b00440d522510308555108640621710408105038801c1d94204142612900c080d611440e4000f21a4030502056006000d90040e0b0b8000c02c00d0040c5505001c185800301c18401070a45071082c04050b4420303602e0f0348003001d10305000301c1040246400e05044150506549425038015002000300c40d1440300480415402e01c030000c40391001c0c0c0c4404040d83c00c00c400008880040d0324510315090711802425001251a000c03041003802250a410000d1580b14030b030809205202c140d0b40780000380e502c43c02c40b000071007513001d2004150309803007903000d000300c4041030130050101e240c104c00320300c10501045c90f081310360b9800c04207ca01d02c3c50602d0000321200540c1c2101409860a003800316080781c004140e410341d40841e40003400c103540007210119542440780e2103200f00b00500744911 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 618254217 1250 618252967 618252977
    0x1005060f090d03030609022106010c08071209090212060109140a030209061c08030106020f01020414010503090718020a14161b1a07031101050103121214040609020102061501 76
    0x281c80c440c50301c10382c41d4074140c0c4241000f09065aa508004c4100d0f08201c019144801c01c142107a0001c0d1000c1c41c4240c3d01500c00d0900c000c200c2055103843d8918040c803038000f0302c851403214132420700c14020300344040109950401075603140c903030001c80301850105540d80b602184070301001258503d0f40d882c0106424002038a085da10314550f4080040c008809401250010540380c4401ca1650420002d40d4400c3d000c0c1103925969450400000e1511002e2110b5400076481404240034030b202d403140e245204d01c000d18016403652550740c0c500d81000b0250340904d10b402c081407445100e41c0c956801600e042c1c003958070780350210214035510041600c2007411110300035a03000005c400049400007010f0341c51080f410040b50360368903030004240411914401d51840800030858400301075010901e0030321046d8040003030005504d03582e01c9004030702001060708140810b103403100003103d1640d40700461032401c0c82507580301ca06150418000034032510909a00500030b07000003030380c60150540d98550401042e551 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 618255467 1250 618254217 618254227
    0x3120903080d11190503040c060914090901150e1b0705030a0c1703070c060b120a02010305070203071b060818030f070c0803070309080705123a02061005060f 69
    0x1214020602c2000f80983c002c030500010f0000f0801c2d01c5886903400041d1a0240c0d40d0601d8101050742035540d90189003080311000d024807407036503601601d2141110542d6a50f01c1500d40c100500d0251040141122200c1d80c0c00d00d000030300c00200d250b83d03806549480880070341354268110000302885016405041d50b0b00401003a0f080134400c04400b04c04034021007a500880d138180c4c03621241a413043c0d807103a0008600804110610650388503184900c01c0440d503540034107007918196a01c4941e54000a41450b54480c00a03400c03034020f2040340d11190b4045441201048114044180010607010707003030000d41c00c0000142201d000c4501e0095031014280214144420006891869440350f80121420b444410b4001806a070400c0906241ea2294440740401800c000d5601d15202c11a88074034410442a0081d00c40f4810200c1d4803a9980210704a5604a0411242040b101000324410840004a040040500581c041101c81c090181c619580780c445652f01c00708800341c0982803e00c40c2e0307480d0800c2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 618256717 1250 618255467 618255487
    0xb13020d110609090a0204051c021e0a0807121a0106080c0d020403060c02030315040203060612040809150c150709260105090a03111204180b0310060312090308 70
    0x62a00726001c010012842d00a40d00c0209200107070a075170400d405c1e40c0101c2e00303120030303d41003c015103541b824140d0718061140310303000500103154104004101c41041109880b1350b8490190b60000750050a0844940320394a4403a01c641066011081e80c25001e41011805081450380025049501c04e030f40e6452207480d014015402d59001c040c0b45964142d013044000005001ca001d61204a42c403031b0080c640b28603111141c10030184502c00300c144501d01c1081000b0003640e540054401035001c050b02e0f54115522843c1844071481490440c60780014290349030b0720001c2002000305500a40c413400d40f0440030030b40125201c1404117895200205408410a100c0d12a0080024441c6590540c441e09030b18583c00b03c40c0e08450054521110070b41043e01c958052542251a0b0900c001110000740040d10081e00d4101c100c2c0038501807090412002404800c207506660084000010000c06869034140140300c42c10040529200c22640c0e9070400c451240954005c80c00d000860780c000c5a200d01d0084400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 618257967 1250 618256717 618256733
    0x81e06070f0c0c0320030d02060a020903100f0203010f0e09071a0d061e060203120c0702150f1c020921070b04030b0702060108160306020306010c0b090105040b13020d 73
    0x2404001c000384209840d000c100a80c03401001103002d0802440c0c0984400801d0300b0b10304d405c0142501a034000808a0303141a4005a07140e48401500d50040c4c917a020180040e003030002c400001080c10341424140c00444125500840c12549040300c807643c02980c405002038610403c40742d00210ba0822001041141c0d050000c01070780c00c03070302c0700000d01d0030502c0c0c09508204c1e8801d030410b0312000200403048026800b400d181002800450000b1820022140f5a03202140001003045025444c0480da900454076030081580c1040b454150340707511101030310705940c4103800c0060264001c241801c68868540341510031034400e4000505400c441d4402c0c58aa00c050f000c5941e2540000d00c11180d0024480c7c0340e80014001640c800c013040c0340d081c01c048200034586441070700b0861140e004900c2200c19024898881d100322940600091313143e03a5920300507990f0b41054180905403104403030400241c414194461846071b485403c041c5040c4d203c5156040e60301210000080d004a00405407002049800c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 618259217 1250 618257967 618257987
    0x6030d0813020a03121e021b120102130e06040c0521060f0616060506010e0a171e1005070e0d17071e0623010e0a060b0c07081e0607 58
    0x6442c020b2031513542d558600d82c000c1c2410428002610900c00400401220650301c030600e880c4d84028000c1c035141d1100400f064800c40201c5204e180241e8104a014400b0f40545000b50006110f030713059255142101c0040300b0b800c82e40144100d140c54900380034180103405440c0740104c980b6041e00e230342080c010388165950f80a000150f100304400a0100c003959520010480500310703903040117400a0515190007030702c2c0041d0446060001e01c10050000d0340700c001100040f14401c0000710411050b40300203a0078100d81c1a00855103200040c09207034041d00019454805499606007002281c0d0b40790380498090011001ca01d5000300d014100101040c40e141154030f101e001c06001c0351500c1c0c6036590b81d0308448030f80e44c103440040c50700c2c480302c0e401d00180d8030070085451252072640e80402207152500801a105000d2440c0e003000c1940881c00c801030701e900802c003400007800e2646c0e54004c2000e44554501040c2f040200501c2907042c202015142c413240c012084a5050003401291074402041c0d0b007104203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 618260467 1250 618259217 618259219
    0x90e011e03150903030b03030301030f031b0b100312020708060a0f1401270504020d1202010b030601030503040f0902090604030602030c0f0d0506100c21020f030d0e0606030d081302 79
    0x300310008404900685051070b240c0c1800c0800244400a901c2d01078103403020110601e00c250014401000481c84151038108601d61510380950104201c0d000b031076000031820340140c120081030b410414800c811850480c02c0d03d00440d40c420342030762140012a51a407007030040c140560071540106030f81c421580c02c04007032511200001302e400c1c01d4407840765103460310036800084a0f9501c4520f1032506094442c0062038506074900c1848140740640210300c1c000200c0e0341c000d02c11444544000715082c030130350000da036012000381a903030385595038200199640c0050080461202c44d400c1c0000d03461a4610803200e920300c000d04154200303031075901e90a0080d00007d00c0082032160410402102d40c003500010003207040b070f5050000e02420120280070300c2040341c00e240014000407100d520003003035402110b4034401c4200c00800c0c07080f403544c100490400c030043c07200d1b2903e8800440e5241d98094990000145504044211170711a034403142015901e08002c42c2c00320118001c5804206040c0e461074180320003c1c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 618261717 1250 618260467 618260519
    0x50c0f03031e04140a0806010e060d0506041202060901200a0e0604060903050c1c020f030106090e010204080d0c020109292d040f0623210601090e01 65
    0x42d0b200418001d2580102108002000080601180d0840320004400b10b0080d0740810841d07091110181c1e5408041c0101500c10b61440006900350792016181e440c0300d41d00405440850030540b07421150a0602c1000c2400340c09000002001c003901440b43e010107d0211185c01840790107102c1d191000e900010784881040640c040d141310a0f155140204010410790750781c20846842d50070114101401200d00700c0c030524486600000407400d0381c0b40c40c000e01e601240c42100003100c440002f801800568000c008403418095244000c05065015000305c41e4a0025103c01e019540002c484003500c03488024040348440034107010740c0c1401c00c2c00036610040c803406240d21000c0400f003511a0380103051007580700140140100c01c01c00d15a6802c40b4001c01089483c1d042c142420a01e0034070700710714000d0004000c401c8070b00070a030344e09001c002c00148260310441651a074074102150510700323031041d040240000100110708107500c00c0d5180c07411101d565056001c01d9090141010043c1500004902081 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 618262967 1250 618261717 618261727
    0x71715030a0b18010c050706021c050a0b1311120429090d0c0201140702040603150c09080309011b0f1b061206050a03030c0212120a0813050c0f0303 65
    0x40c4040160115540c0140e0000c1d0b81c0e071a00d01c841024071040001e00d2040343c2d0500f404809101d41103401d48003029030202002d070b110410118484040c900c0b003144c410506007000b060140002080e40726440451043d10030119000400c0e045c01c040e1012905510003200042008402a06104d240d1a802902c18003412140110b15598402c0c0300360903c2060841d10700e18014007805034003c110000707812a55003840e40351422682c0001c0c0425555581d020b25141c0b0010303503801155525840f62000e035038064a00704800c400381c6c00c42c00080c91034002040204008440200340780c58000166031a15205035202c48100e42ea0802e0304844200040b0100c4202e444004100002141c010031300700c3c2005c110030011000d51410380e0007080c245030040e064500f1464100140944d485000c4660180c0e60581000d0800240c00d10100d138200c44144541d12040c081d0701c100503105480a0000c00c00c20056550303404450303c030318000240100b6a210014840d5200e030b803900c80300d030030700c4403880f140c01c0d500600780c90600c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 618264217 1250 618262967 618262969
    0x206160503090108060907080a050c0c0106032a030b0109090206360a03020607060c20010e070603050609130819030e0d03060b0a120609020c010b0414071715 69
    0x411119000c8856410218140946590101c441580f0080803640c2001c0c40c209040080e06d50322001e050b00d2101c0b40c80e440010401c0c1040000c0b0b07400030025074000c004040e507a007401254681c3c60500e01d803c86540c03020020702e41d821510081c05407904143300e5001646041d42140082c003082c1c0040360070003014014505850702d523003101c046020100d54904407584254900178006240600c4403441001203031010701c0584c40c1c405c1034607111a8881c07000511721240c0a002d0350111455440c16418030030b04212040803036019000030840d103a0780c1c0215201151100c1003030301580d030105d4125400019200009000c1d0035528110201140241d41003860140c000043c6041055010304160100742c654217240100d110812100704000c4092a04000150030b040f10403c061242c07828410070441000c0c001e149030348103540013038011301c002101150f0ba5041903129a01034407520601c14070030361500c00e03191080301000403501e1040350780d40c0e60b4484c0e5241440d922a444003016102d0b2140b2003c0b40404442 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 618265467 1250 618264217 618264247
    0x606021606230d0504020f06161e02031c1805100c03200a0b0105060c03090d08040801020307090501081b0412061103010825290d0507181d01030308040206 68
    0x4003d05820104141c903150050003170f88107003c04007500503001040820040040303191014081c83d409203059840810385d490b03450030b940d581e0b800a0b40c540101d1b241c0440d0b05070b180d0340070024881346440d00d8444042c0800f100704000aa88a299042200000440384591155241c46c3d4800c0c07003030801c40e400c403401c01400500300b0494102c41c403e6510200a880522200c1d6142c11300600c1b049444603d0080c485401c19128021094158058000b0b50000d204100c80d290035100039010690086440b40ba010f0401026010b10f441400c0c04036200b48042001d06000320728000100003280005841d0608c2c01550041040301540700b030311860741c1c8503000307010400c20b14001d500900d0b1401c000c100d245040009103030f00b01080003c04440b0249030408202c4902400c0b0141049907681d00c010040e0360f5502800c04040c403494880c08002440d01d8100043c613500566110006c078008111fa01d5059100d000c65048116040340b1040b040b0411001040024443c012841d1320600c05000303d03043c00280595001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 618266717 1250 618265467 618265477
    0x608010305030415300e03090a360c090806041a0a0905010908090411030115120908070f152c210406080a020a0c1502090a0e0a060602160623 62
    0x80b071800c0d05225414012100d0086d207107001c0c50000a9407416240d440040c1d90f55086201e81101c22140c050307450f4030302c4802841d002e1505004030348081d03000c0286501c0c3d030090055404010210301c0802012602d80e030005005482964821000d6100d0000103d00c03084242d0020a84081c59803608098000100c0a014003801e071403142084c40c2d02c40d0400300410050328180c01c10350081c076800b030004200b1010700d031001240790740c0141001d0720b0341e135054400000901202c100103800d40400081d480304000d415400000c810340609104030142d54141ca0280c01e549802c4880d05400c000740b1900003150440f0320600d4072905440007183c80948054002c001441070044601015250102d0100b00e03041e00a01d0303180c0c1c80342281e01c0451070301001c141d000d004100711003400b03001c513080d24891080314800307681103809420740184a8018550f443c0c2c84484107000446618000c10309102e000030b00703203000150300b42400f1038482140d2a00c0c0e0524804aa1032440082c2f288030303140b00903668000e80016080101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 618267967 1250 618266717 618266777
    0x22b0f061509020705010f0c0f080a18230f25030210050c0c010212030f0a09080c032503080c0a0c061b17010806071808010203010611070608010305030415 68
    0xf50300d501a6040c2142144e9040d1060b0f001e0303d0611518826103588101c0240707101815040c543c5e800e440b11104103000f004071020b0180a25901601c0304240842050704a09041543c0d054100f501e2406001d5a02c0b00410b01c012001c0d548076401c603050030b008006400050510454000403150f650350000f0b4081c000e440c0c0c515002c07910014507589030850034041c1e03883c011003e0000b00209510000081120701c80201000c0311440b5400c080f80d0724190a4102c0e403650341d0030034203980e21490088142516540030303906070b02080075103c2e241e4688204a00102401c1034058607031002c40d6454030032210b110750083c00b99808020300c102d10710001a416210b1003005400c00da011820302e01d84581e018004140507021102182c0f0313400010003450030f000a45991100c464a403080c4027003940c80c0300301025071540c2c011b010039500100020681c2540040c1003081d041104045409103541c815050b20342603002c1c00b000d841034104000c02d01c5041440c03083c14203071011a02d0f00c80400a0306030121004800e5241070b03c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 618269217 1250 618267967 618267971
    0x30c0c100221010b04150f2309100e0a03030503071101090501060501090602210a0504081b0a0b0c101d01140a061a04050d0203070e0c07022b0f061509 66
    0x511031044442c12090140c100380250320300e4a41841e4a026101051907151400c0000c50520450060320904500414130302c1e424014501c14102045411650410142e25000314a214032406540d845030030803c5030040090030000c0104d0454600300c45907070008000c8000d000d61030382c01c0c03074410400b40f05240c00710b405400000fa104c1d040c07070001064400e10703900002c219400042d060a1860b280200301c4010001a604281da0f800390780802d5400b40556840000140510000b0b002c03181e102641c60740c6030890882c4c10b0314185443d154910054002c442c01d02c000c6600224100c00f0020070359029140002000300c409943c00c9440c1c2100f400c1d0b4456428400c0b40035022030510a40390305502501c7c0c058403401900350008200340382d4028031406188070b154461243c24804000317645043c0402000380510442c029a146000120300e0203a62103000c0882c0160001c941c103148042da40048034240c9200b110554205079030f292911400e01442c0b40042d43c1103a42c0300d09a401002d99070250100410a460780 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 618270467 1250 618269217 618269257
    0x604030c09020c010c050304020603150a080304060504090e150c03070c02060c0c03060601030b0f06030414030313030f02070b0306120f01020a02420903090402070c090c090b030c0c1002 81
    0x1c0f05003900d4014450209004c07060080c000140d8585c015280e11142c50550010081e5000c40002d50b0170090368421801800000f40c08210b07598860010000ea0710000c00a1040c0c0440860140d0b81e1480d0341e5000f45091020f60100c0c2d03002d03180310f0042d500640c05140c4007c0300a05074000641c198801c98034044207901080403020320b42001e0050640c40002424100089403012000c641e180005454030340c0729040c00000a070401c41440004504200c041040360344901e4410b0080390403464000007680031544605110510601c00203200e01a00c239643c0c6024110348542080c481685410142611540240800204211001d2001d8102541d81d58000e140340c4035080201c200c0700d0b605400543c0c00381207081b82204032020480e96000001100c01c003400305076a9003030b041811030007650f840ca90305ca40000341303410500010740d5400b03007a90742103213040110754901d00c810f44000c00a4801d0030a400c1040c0009600080c880002c0c03c111300d00e9600b50354488007108803150490384503680c0c1c1d8100c2c50301c4902d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 618271717 1250 618270467 618270487
    0x90a0b0a0323010909051f053301120e010e0102040f0509040b060d0804090903021509190321180c0f121203140a0e0f0a1106090604030c0902 62
    0x18005000c09102c0c101c030544000d20001c2e000a1405014031004180ca0300b0001040080421441c01c0b201c03000d414070b81002800b200f108003e400c0a4038036031020907601c00041c2800c3e400051070b1800407919a020320700d003545c4500650b5502d100c9a8102d900703603074402c81c0c0040d090f400c1c0114000c11140100040e03a4504020f1038006060315034000301e0255920004010000b556011000c1e04828100c900f0000e540c260320b0464100e21964000c1070000d0704203505101003540001d6840724401c8548440c82103550740942031503658103c07070f120b01e60381545040481e001c2800765416070b1950700510b00301c150500800c0d0030326041d20301c10043c1a0015108003400c0040c0b2264580c89000380203071003001d500701868414890041d08203c0c0029102d003111044074880300e4000e62100036210120b11040711719103811008280241100ca4003003146005151400000c81000b00f84460100d500c01100014003e9007000d2102d02d80008001a4001e42d08100203c01300d41806586c00003480c6607c005681c400300c0318 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 618272967 1250 618271717 618271721
    0xf06190f270612020a0c11040b0a0801020d0c0516020f0126040c060507021503090c12100506030706050406031a19060905010309080423060f0703090e04051f02090a0b0a03 75
    0x3a2444011901c140000c5e00c0407070740140882c8602d40c21003100300e14461920009130081c80c00510f003c6d4481010400000d02c060190041d0410300000708041040560688082e80ca070320580140020348000c034002400145015041310840c001c061401d003001c0c861460804440f0001408020724510405003044108000a010180a80720f685070031805d1401e940d0209560390002c10030544a0600400001c283d44404c02ca00140c00100810040e200390303920008503101e8124a0012000a09000c0095504e00740024900100c035038a50354a1300d0315242c010100c005005507000c043d80603120610350381d00d95903505110b60b002540000b4201c00380d8900a0f010340340c9a1194401818107040200541c040760070341042c3c40480d440454665030082c0c50b0842c1c02455007412800300d5110f0008200e403c0882c48007406405801d01c40c0e01c5540b5540d48075031000e02c08901c100c8008000360310a1259400d043c2400784810507400080502505100072440015040a42d41e04818000e01021441c1d000c81d59140c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 618274217 1250 618272967 618272987
    0xa12031d280f05030d0911180606091206010e011706060d1509020d080d0f050609130f080307080a0612020a0918200f06190f2706 57
    0x1840041103601e88540c100416a0300c041048031000e800d42040700c09002c511000d091010f640102a00e9403803015541207801410300b094180c0d4241c1040e1030002c22810002c000b039506007542c541104240d9141c07020051303e688202480d541203e4011280000900d00304900b0740038000b403400343d030700035810f04000040c00282084031404035480b80080c4015611540e8141132842d410043ca4010041d00c40310b0340780034284401e8000d400001030303030301c0342c0034001c40d06c001e00320903041000d0900c5481c1c5030729040070a560f810394030b4643c8185644042000d10308000040d40d801440723140038041c4450b4a841c0c1c0c3c0070b0b5400498500f8003140c100d904110381c3d1041442054040e018211100351559010780210703540c13a5403400350851b03065682c0c000301815a988500846a582e11200381100722000c900712400b0314034001003039400754458a040066900d404000e4858400c99060560061850480211800d0004120030801d01c01c0640e03c44120740202c030500781d01c1400c81c844400899141010041c0040c0403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 618275467 1250 618274217 618274271
    0x6010806091b0703140a02060103020307230d050c090403031a1e090403031107050304030203010b060f0d151508040b060f15090a0b040e01031205120402060307020a1203 74
    0x101d00401042c80d1051a1001d260351540800d01e454400510b001e84110104c0032040550315404240ea41c205540000c80710b050724402c0c1c083c0c0720015510948503032100d842c510341c00c010b0b080000c040d1180e41029203201c950607004000700d036517419811021401c2d440381900c05800003621481d03480d081059010381c130ba610010030b86000c100071940c0c024428510411203c61071081018001041c149032094110400c0b580907420781d240c0e184241e10f440d40daa5070192000728040c2d42014550b5806180090503074881e041c0840d0028a0f0508105111000323103d522a0b40703085147d258000f0079440d911100019a5070401c0d1101c1d80ca608260605046000c0e0082400d449010704c903031540c40544804901141d0f0a00d8a030f007240d2141c5c0c0c1000091034012550300800040000410300103241800b05070424120303401110340303460b00001c0e03850486030b82c81400c990a4640c10680045001424420029a070240c158170640703040010385d5488000c000e0007070140400103910780400b00388002010076802100c860f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 618276717 1250 618275467 618275479
    0x2d05040e010b190c1a0c070201031b08070f05120a05040b09010902060a0f11060718171209041d0f1b130507020307080319060504020702030a20150306010806 69
    0x1191100003103c0104544941009040c140400401c1128044840141491280072205103800740070900650070561040c0e00081c244000c5031020913000840220440303040c0c0d15801a030707a4980c820307110181c560342e00c1e02c1000310811207442d10156900400d4025440694041000d0800e410300d00010140648042080e03490440040c3c010f035a00411035a860000c0c1c102265005000e20068400d030300b448132440d05901454080005450340902e01c400e980c031a1804080c1a81d40b5401c5180c2e0110102044a120394048a5040c12604601c0084c00300184000c2000c00c00c20140c1001d50324528000c0c50030b04c0e041d0711503070523031400c10400c0c40540340d07081d07290521840210401000810030340d1040d0003000042d40d24004500500d209004403440380d50004901962401c02c0c00d0502d091f65011051a1121440d10350049004d142a000300e415140d001801001e10a10700e4031001401210380240090b04240c101500c002c0e901d81801c4601100c0c03204d0242522031410000152624a005004500c01d80c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 618277967 1250 618276717 618276727
    0x306030a211d0112150e040b06010206100b04090906061502010e0106061704021009150e010807110d1d0a08030c07120b24040f0504050f0f0c012d05040e010b 69
    0xc2d83c440054182071444e4000411036903034003c482e081c5030366150000302402403190f003000103010031001c555004410030303400c07250b95a0b503c407060340e44001c1c42d0052020112041008103d01c66464110a8131076000c3d01700010056500d10080030000510f04846000d03035150002c500e0341800a02c03d0500800c194200030aa0481c0c030b050f021501800100003d2003148050000d000d5184030b280f001c40034000c0d00e031520302101d80515024190240d00781c2c583d400030312050006104c0520070071031200c05428403002000b4069040b40113840303905141040114041c00050748100030303603848c8040c1c0300905044c000783d99201c6241181c503042c0315207908605040e0021915030b0700012486072141707510030b00c0c0c10b56044034000718200441040d501400210350160034019801d1904005500c458015031046084840c403078104ca04584d11100d481079004015004002007802950040100303c500d5440c0c080c0f20004000410384c0c020132200c84405100003d48046800d01c074035448905483c1c098540300118a08003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 618279217 1250 618277967 618277969
    0xb090f0c010302160c180507090605090d061e02040e0606040503070501052203140f0607081b09030328050f07030f0507150e1005010509010b0306030a211d 68
    0x240c1848a00d6504040c2d001801c442c1c50300010342e006081650080f5a07105040e51403c09010860302c60704d00004c41c0d450400410869401383d18128101d0782c2c10f031903160900303c0c1c000070408161071508081c2e5000d41c50700c00c0c2c00c0f0290118400869100e01e400801616181440d400c41c1c4c548038004c10741801034008000034041e44e5030003d8603004445091a0160f0340324071170001001040209203000c3c06041080f0008402c204034043c400c041c9c401120101c0d5980e8400d00241a69404213503024008a035402000c540300d00082c240d00c0c141c210090443d0f600d80030401c000310345150700420301b408541d00a41c0c202a04004c010700040c00f56550340c41c0c418188001440b95010620070070380010240216590008100c50084041d10841034204008030284a481c13516040900706e1001c812566018181c011944ca040c1445034605889014103c1c91070b6030f007442c500080070361001e4001c950510030f5607410340000302c94169110070001002413030b01d07114240356400344c51240462540e181a940c0080281c1407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 618280467 1250 618279217 618279223
    0x60c0f0d021e190312050c180609011409010c08070516050102060f011404060b0c010c030510031109060303070f03020c09060108091507053c03090714031c0c0b090f 72
    0x6052681c140d216076030450720f425a602c2414440910f20142481c2c104411900d82101070314240003101c207810b2130340a0323400c2004a1031148105072804241010f00c03941d42c0364102d0001c0c00301160181000347c5181580e85a010644c1c01015044038107500032603200c05440c8643d940b020081a00380020030003810425407612207503505008091000c4403040d6469000c0c0c0c3d487c0c2101c002018070003102641d031048482c02a000e0207519913100c004c80d040c80c010401c05418540d02800b220b03042440b401030102d4410400c10900000342c03140341d052005118207400f086800c401c80c40494801c4c1c0050a50b00a1001441007280d401084141403100034001c00105000124001c070450108005120b015074804506940301e001d10f070220b0b545c030842007580c140782c00c59030302000003003001081410300103000101c0d070750805d484121052681c03074001d18003c205902004020754003281c80242074403d00c09909012180365800d042c0324500040c2d440c0700c10007d11203540b444e2a08124140007902c0c01c040c0c21a05255 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 618281717 1250 618280467 618280483
    0x120210020d020316020a1518140d06020f0f12040b070f050706150905150301050a0603111017070305010e07030b0307060c0f0c0605090a0b090d060b060c0f0d021e 71
    0xc0100c04d0740000508554501043c24040d1400b080d0300d000071503043c0c0e4010700c01a00c02c24184109050300401250b41d2036a001507002d60040180007503155039841d17548402940214107a44610441800007281e0048500003624640902c0304921525180604145081e0180603198406000740c00c0303000d51607036501608541e0003d0700714a01042000302542e80017603214241c0d018041052805060144000d003205050b16401012002841540c46035100c0600b1181240703c0103061002c2440c0c400041e00301064214001c03501410580c2c2000c1c041c20400000c00000c0343c0380e50010343c0d11001484010029180e030358100708580750410480c84607002181d903581d1070340600801d0040d28003481c2c0401c80510000b02a140d40f212040400540d03030303c809416900003d10310b522030504040082440342c0c0740c01c00d0369006c490040c02c0c010070700c055440309030061000c49280750b0403800030003500e0604901003200c2200ca4000c04008c00296501e800c000f810070510351592026a030b40001d8107400c000e000940d02d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 618282967 1250 618281717 618281737
    0x30a0f080c16020319050715210c0c0c0e06150304020d080322060e1e0d031d25090b010e0405060d0f11011806020a060c18120210020d0203 61
    0x11000b00b05000003032030180c0c080700c0c0d0000d107090481c04108003c00803800c081180c08d84224078483c9001c080c4251030b03800d101d03200781014a0b141d1206480d9002d95801c51000e807040d9040444605d98503441c4c0350403001d01c60304081c0c49403c120040c8105070500c0400c24050302e40c80e02d100e5045041c035500061094223020300240c0441c4020000c5600c1c80440c19000324010f14010052410415520b0711802038032444d0341d00c2c03105006003181152804440c10b02c410751404543d02600030303c00c0e0150b0039070091880c1300c0ca04d50b00c0701e2190503840c480d110411588401e543d00054184a40d0b000c0c07100c2c84505e0500390400304084d402d1283c4400c1d40d903040030f49081040b501300c078041030a942e04c0021403105461130130060491031035201a042841201604c10754141403c0c0e84106c4011111011450150024494440140d000304000804076940381d1064900c05641d143c48100400b001410098217080758010b00300031051035840508502c1d00c4005049a41258005006040d0720000e0103500c03170240700404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 618284217 1250 618282967 618282997
    0x907050901050f101b0b01080d02010203040503030f0c1603050c0622020f060706090b010611030306090610020a21030b0a0b040e1015120c1e111c02030a0f080c 70
    0x40d800c0117000e1010000b18440c00160000e900d00300d41440e407000d10080c8660301d9140110070320035640038418006c0380c1c4561341100c011803468854042d2085800401041803c40e12000e000000c80d100380c1e414600741d41400380d60791685034058584058100003000c1e1100d4200001d20100740300004284e12148492074040310340c400a032008101144403441001d0004041d541f9042c00b020400c010044d04c076050328641c1e6102600c1030300107541207541c0d210a84503030f5889400c003400541c251800c05401000c9003498410f0710800c81031562565540c00004038180b5030b14015a141180240d072620034250940303070440361100202e182440014151140d409802c0b080005d4034005401d841d11001080b0060240709001103102000c0d0b80020701070b20300c203801ca620490820a0030440c40f0700c6411648041c003c01a02c1300060542905e0a0300d0b043e0134000502284d00854414a24003448068900519072480d0003440e92070b9002e00d0300901c5810011024001c0c40407100a00c9240060502a00d0a544000144c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 618285467 1250 618284217 618284239
    0xf0d03021c0606030204180506150313020a060f0e06041401180f080a140109050d0302031003021207091103070c06020d02040b130513060503061501031b02060907050901050f 76
    0x409418158800e4600342e041400c0000d1140d0f0560043c41120800c0c4241c002d441c05101a002c1521019500785500c01c1000b09266000b942032001190020700e5002c201c025043d445c0e000c80d2180101d40c1c0044c3c007003075881310484102c68000800fa44006000c948452a103070400b151a2500c84d40500820b04100c1c210301002100344038030616201900e20110088045c41e0785140c61603407100711900480c0c1d0b5041081510f00407040500504010543c010003402c0311140a0304200c0007074100400759401c0c181c03171080000140e00c1b0520746014a0441401500d800c17400c2080750f03c1507545000031124510410810484e0484c0d100514103600c170341c480405681c0d100c21322030f500701901a580044010402c0001c0071070070090818890411030f401a581400356102e81d643c01412a820303481116016000500041c61044081c1d00d50740030860141000540c40301c4e086203ca9240701000b40500c0580e003e0341c14002d41d248208070b8000217003001c5600fa5600c0d0304040c0843e00499000110b00e00410714114 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 618286717 1250 618285467 618285487
    0x22061a1507110a080708100c05090306130305160501140f1b0c031c0b010e010206060a030308061c0f1e0c0308030a0f020f07060605030a0c17010204080a0b060306090f0d0302 76
    0x40c02030f00078110281112441d0303072112080c1d9107075450302d408100094641404080003034010025240014001009015942e030b13000c9104001d243d0b003135821410848208050b403140400c12469845040c0180000034128038040301e12954210050880703031031071309441d04004c10a07070041603003400c0750f1000b210a900e800b4031601c5a441c40c0100f800b07100c030008590052120312451503200161011090341d41c0394140d00c41100581e183d0f5016141c0d03a400820050041c004203019920454000e00b01030400c0200e984070a054041001e00150304071158145002d1442c01e10003040f0b01c00d500d035201e400441c15545526652a000c0218034440107090740381c0400015014200e5502c03111143ca561081503544e940c103030703070707503200303a9025070340858145140210220381824001007910707019a00030b0900148904045001c143c0050060414a07a0b640821000c65032143c240640ca50f0944281c92403c0380b410310104050034408018047d000652103815000309064001501c0b007003501c2c440c240140d8891740a8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 618287967 1250 618286717 618286729
    0x120204030b01032d060903120908031518012702090f0d050307050d0e01030f050903030402060915040915060201090b0601120603080c030408010501080304080309010822061a150711 79
    0x4912130803d01d003c507101c00113000d895002103c0b00d900c03a60b10b00c8042001007000208603440c1c0d10000c0c15080e8103000080e0b0140698a110710711400091910031440010250144840d800f45c10558040c101e040c2c2c0742c50102c0741c1420b030a12004043c0700540c00c1010505c08509200d80d0741c0301d918490b07002c115025050000038804c9800f5183c01c87c058a25242c1c81145c040c000480c0c1d5044240040e02c0d28060b8800a140d0b44103d90058001300c01a61654455800300581c42e00a1076410f40d00102030010004880d003020000d0009212540022803061940b50300100e0300805a445402964104401200007551001c2405d0740603909007072806446c2150450b5500401c000c0e00020400040020185100c0000102030401c07140f2060090044d41c0c0c031403500503200d000e00d00c10500381e03501c280001a89980128001079200c054620442242144070050b4179084400c8101038643e01c5d0381c0c080e03801451a070280710740b0044000352040409074a210001c00414403c0d804050900000d10503440b4181d47c6907 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 618289217 1250 618287967 618288023
    0xd02070f150e0f03070b06060901050c07090b1f050306013504020a0f18200f0a0806030c0105180301090501050403121b0c03120b120d120204030b0103 66
    0x203020079a4882819034400000c000b030001c031603010b118048111250b4040001100d02c3c869000c020f2180e0340e15210244406c0307800c20100a41842028000301341c0c034040410040008080b644004150042a6010b0054900d9064901054a1004003041c0d80094001e400c40e41c20210a18100f0715020308204400005007210000e1a03c001c01c10300c1e102007529481e0362141c0503a0007210406101642d4044c10054403040303103c2c0c65081e0701c400c220007482500b603601002d0f4a2003c40c0940ca140380300606100400d0348141d0642d5603000c000701c0c0b004001c40d8843c0201c0e0340520300f0744c003c08101d0320341350018046000320300c01d245407180e00c0040884a62800e400c401c4110354808000c0c8100c0c1041e1801030041d008010361108050b16006003400864028515500005059101d107803c0c0140c0b80c404403002205260401940c0e070321070151848944034480e502007401c940b40007428010300e811400401059540160007a481c0c0184420300204100c0150181100d5002c00440c014181810695218480e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 618290467 1250 618289217 618289223
    0x50f0f0a0e0322140d0206070302030702191502010b0a0b090a0b210c0307050304020103020c1c0810050316090504330c050a080610020a0203010504060218150d02070f 73
    0x210b4070700f081030401086801a000c0d0803400700c0c0040d80304e100d812110350401c821242c2c070001c42400c05000d0700300b46005041440c00f074419039150540507008206040c01c40312010601c044181410003682c6072403100c94402030300600c0280415610140014010011070041d0306080d02d002802d60301e00c0e51092401c0004114030000243c41e605180c0c00301090fa014100260030191400002941420860040744d00c11023b94580500b55111078004400035008072520303403280c6c070514104581c60400c190504446458542d00c00b40f0500d05017082d0402360b101580141d02941c00480700303a8008020070800010b54a1030500010303aaa190708000e200580801100303080081c6001001901d02a00440807480030401079043c010f07800310280403600b83c170400141c00e0005881002013000f51801070a0410b42103114411541084082d400003821110241d50031a00d40d60b00060307840e040122a60b48046400b41182c81c1c402c01d4034910041e004500c54101c001e44400d600040900800191007034060456070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 618291717 1250 618290467 618290473
    0x4180c18020c0f01050604060b0c060c18030303090c010318050a0f0303020f03070c110906011e23190207080303070e0105040306020705010b0a14030309130b0405070207060e04050f0f0a0e 82
    0x8580702c0b0f4540202020784146014a0a003000868001d9880040701c02420055000b40402d03030b103a003120803441c2c204d110009d000714280341d200e211554041002c1c3d4020074082000e4451003d0380c03030024044a000c0b40074400484400140100810320215021801e40d80003007003103c0402440c50101c000340b15821a0398014036010050000c029030080200c1501d45c4035400003e10203204c20108601c000088944900185405800c0360b524510915240103844450408110345031585000c4811280c00c1700341c000100d080450322004009040300380d944400c1050010b000010700f0000d04e6522840010308074000c0c4081040480342a034814811503001b943c00c0f4004645070000da140083c06411688203c52007148003007004600729810101e50700d01030500800442ca450b4400c0d007484202d8802100e900c2c0541c0c1c0d680d0b50101140c5441c01060722410035980a0701055040500107045002d02c1484580140d241ca420403041c860108041e0341c0044080380660011740c0c4020071603011340034a08105200740 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 618292967 1250 618291717 618291733
    0x15080c211f142226130902160206160c1805100f170a0b010b030610030b09010608062106060a080f15060a08030f0904180c18020c 57
    0x2040004407801514510380d41448900030b0001d2140d038801c1c081c0c0d02d00b007052401e2940c030301c1075959480c2c0b4008424072031000c0d030440415001a840d600103e0464582c010320700011711040d0303803a00b94502c1d00584440750045080180703040c074292401544c128000d0041400182105155407501c2025103195071084c0e0070964140c441c1c207810340e5454403178240e05415040c400030a00c0c4040c1240c0100c180d500200a0b0849585031481c410704040001045d18102c2c002c01c848800418880e94509000c1d00c5d00402d055540e0420074144803000080910303503802c05242800304111640e540e0050343c11251a0300e0a87d155841c1e8000140007180c00d00009400c0d008000e03a40d0a01c2d00021a03080d201c0c0f1001c5481000440c4d8a40049866404800441072140c000702e00040b604540303001e20a400c84c0b40640340071546078941046919540c42621003034041c41e03004c590010149400e026590b1802644201311004820985c1c8810040860b80200006442c0d02c0c81d4040c0a01c0710384d41550b034083c1006044800e29 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 618294217 1250 618292967 618292993
    0x1030201030e0307060203190605180f19051509061903080721020c21070b16020a1d06010c0506040605091014040c05030102070305040e190911010315080c21 69
    0x10340039210400350232420f15900049616000e003200103000001c152001e910360ba40020740e150340e20000c113054200e42d550a1001500c045d548110b40c4034940704c0f02c10500e030301607103402c100002c40014131481c4988900e0340440380400c1c0000d031042c104c95000d101150ad407500c80c540000c098007074042e24182e0f80030075801d444510b40e00052111110005849541100315440000304d0449900300301c0191960140008021039100300004000f420740808102109103250f80c00030302d01c04801d0b800354001b40c2628182207034696040403495040b00090900710320101c8070b07684003030712030500403c09088241d864001559200e420f00807113416641200c0204003e0140d0900204605829903040d034107084803035008101800c0c14801c480180e074040d100e01e0304292401c000c04000044c0180720040b200e40c012a100803010baa4010a0040351284000484601d180300004048642a51003200107203002d40c41040703010300105059030400c0059408080ca010010b01c0000d2004d0018000e9106100384260300c504 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 618295467 1250 618294217 618294241
    0x4030218040b0105040203130209091507050307080f1303050a030902060301091d192d060209100e0a0501052505060603060a020a140901271d0f01030201030e0307060203 74
    0x800c51040001c462666244c800780b0049000c00c88039000480d40820048003d031038004601c9a00003a070108480720594400001d20303076000180c9491011442c080180318400b50004c0780341d42d1103685454110658980b255120700c10501078603000c0c06003d400500d08900074400c0c1c110b0078800d600545000c1da0b950b941e418810040040300c1c400002121255051300803a9408640d0003814141c22001981e560015103c3d2181031452401201c0b00c1003000150011020b004400034501c00d0180d00016183c0001c10b06220303520b0022140d500c104404100003070001d5491840c0311050f01e0080c68501e4981c070309550310071b290115101941e803102c41c0c510304000820200080d00ea1140000741c3c140d03000d40d1034070b103440f00590141c0c0b01d49101081c25a600404c4100f010005458003560515018002c10001004403010030303441d2505000c800d2000740e05010448240908640700500d0390031145591138890300d000c03150b03070040c00003c0c1010746078038031204246810019100800c0c3c01c035101310741c0c0e804e07c0c2c1b00c0450 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 618296717 1250 618295467 618295471
    0x90501110a020d02040b0102030714010c110c1302090604090608010c02070f030b0a33050f031605040504051f0c030501050a0305030703030c1107060824010507030c0804030218 77
    0x2000850000340c0030490580422541040c81d405040a482c0410550801c0098410031036814110302c000d01003030020454000200741e41000035030000509000b8950010301c1c582cad03a807105140781d500000144400f42c84655030605142c281b50001621a0403500000d50a171041d680a00c0c03000b402c0400c080303a03c1406621820245a294085408480c0ea400d05010305202c14440030f000311050784005012035243e038210356003a4540c03584c440c51014091102e813850710880424444450f0420b42d052007a400c110b0502503885c0c0c012002010781e501ca40e4580a122541c03806440c0c0215180c4001c1000c200041200c030021280484502c550781c0c00a5214000410360b041021000905041c0001042d003451202c410540f90401d000d18a08415500d0a40180040384455030820800e50515540640c0078099500a04403d681c2d42d09103041c99247c13142c004003020002c00594054082c1c0d110b20713030303040421207414640c141010440c03140182802c2c00e1f98042c65202035085202002c040303880c0302010040c94 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 618297967 1250 618296717 618296719
    0x10f1818021804050405030f090102031216021203060a120f0f0b091b2d0a0b0406081005030d0c0302071e06030e0105040c091e020409020a1e020a02090a15060905 71
    0x1e4611900e80b402c1109a03071041d60b02030080d03002000412100a2882d004058405040c0102c13403801042c0804084070030805c0b12007480f4a8150403100800541c14003080c101405401c0ca80742c158201388002030411243c0344104002c50200c02c41c5902000941140c1c0d03d1519000303003100a0789449420100305211003190302d1f03030f601d015018030300400c8440c009a82c2d412500190010306004451803824620895040c843c1c8801c5514010381c1e12203036038112951000e4240b500c0c0c1141c940d403811001800d50034020b030001c941000140d505120031340f0001940303920b0851500d010520755609080982c01d000d034a4010402503041c62a1400200303011403030103012030341199000c10150501d080000d00b01d44095800802d4018400780030894508141c2000e00701d42c2120038581c0f00d414a6449040403a4000ea01100641d80c01190b1070882c0c0e600002c4445104050b0540b90740341d0b8025080082d20760303003a070400031311600f41c01000c20319041051740840798042d0b0040003400c0c600e0f2150317401b800c1c0d08618842c407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 618299217 1250 618297967 618297997
    0x90b0c19020d0507122304053d0c0c0801060e010b21060102010608191a010807120609060c0c141506150c0313090f02030105010f181802 60
    0xa400d04900c00a11140c0700b20041e51001d0a12401e0740d591248001e00c14503c0003004050040b04407118001340e100344103e102100c41d01e81d40d42c5800c0c140b09200140b1014005040c09501c4085030039851180702500e10340040070b600c814140243c03020394008800c04400b6014010f031120105052005502c40b42c1991020294500580c1c2d03100d004e01801d02c9070041d131601c80481c00111244c00030958949a40040301400007103243d40d160900030b460074034010b016007846002641800c0078046036031015004142440b014545541c10510400d540c0d46461080302503040c2d040c50200207011080e03103c008030070f03408007007440040034201c4000c00c804a1100181c2e0000b28480c0c1d0040ba010002a00c1c06054600e10440300310760341c80741c08018a2129645074502014010041d400001d5414802070400c24040310714110b440e41002e210000721550101038442e200e10400060020347e802c024407950700d030054500b01c00c07141825034100410000540c00080c40f20b00300c10074130591160030340141148909a240d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 618300467 1250 618299217 618299257
    0xf070c0f060914060d11040801090503090a05100f0e01050708030f09120301060e06032512060b07080301030f0f0512090117040b0112050118060e0f070f051201090b0c 73
    0x100d0f504199002c051258443e07410080074242e000c05801032a004081c2a10b40350500d940d0700311079400d40c0c0b0a04400c96281d00001a1140d840c038140751102d0182100327941d000d090514006000c1d00a03d905100340003400920000740c91541e20503000c0341da400c0d600030f000d1500e03030400490642c50004150340000c0140904182c1400580c040c02c10742e41241e002da900d0351421a00c01c1c0603c44158006800f101f1300c07030004002044075072075106200c940c0f50310b1582d40d10300c0300b10f8081e0f80d00300719880e0ba0030510604a0420001021524040940b811740350020044c03802e401e0a454402880640200001c10a0040440381c9440e60480700107401240c50031b0f201d45a0f5106160600b20120004580042c0b5550240303005001d035400c026100c0f04090b1180700001000001c800420340002200f040c11100300d5101c402800c1402d20900a1180c00141d4000509106041801e25007103c441c500529018000d20300751281204800d402820b40b198001c1211101030820350904981540030a030300207580744202c04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 618301717 1250 618300467 618300479
    0x140306061806120a020a08071505070b071d0a060f030e0a050d0309020d140c0a090203190b01051204080403021503090a0803040606051210050a090206040b0f070c0f0609 74
    0x32614001c000075010514556980104000a6030328042c5021080c0c8600300d59500103844d4802e401e0098009500140000352904040040501b49403074814100a0148607480019407400aa1070b01300a480c20140840c0d840d08681850aa04041c2e855074044001c0e4000a8400d40003103640003800881e6405101d14071107103540710398500c0c5505004119620500100c01100d01c29800580220700c020840e10704680f040d01d40d4000380c000280d001c18030717801c01b1010801da4601122208000c00d0f21550039800c521f0141004000c28180d2900380c0c5000b03480303c5040b02960b2040080356841d11400b240484a0305040c02c04030500d40050000b01c0c000d404002d141c1806056150507244181c410400a0882503603564500c400d41c2c0019000310b0b01c4948848010034103944843e590034608005d800144910490501c548003900c101420401941e46004c01d40300242e201c4100702c40c01c0e0385040c4202c503501d01102c4c1c2e02812503c2402c0000e1b00c0b068829102092043d020070710001203504560b2800d1200362191b03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 618302967 1250 618301717 618301729
    0x40b030703050604080901090b03011d060108010302210f010e1c05030112060207020303040e0901050a0606090803040b1b010612030f0305060936210901021f0f020414030606 76
    0x100000c2d02c0d82e480740c40004d000075800c0c001000962018944451b40c41da0b5103034612615002138020001518028400104d4241500125030b4032200c2440e010086500d1600880c2c1e0341512203030140b8003005074450424085404000605050819034001c000128118100980300c2844282c810711120014011184092041054a042c0c440c44a0305080001e12643c4100096000410480c1c0500060000088020f0a4135050703220300044000400c452130044030803002c40d034480c0c0143c01401203060007440081000019603050b9408000c00c0d954441100001800003807802d0b42c400000e41c2003040c007054122040c02c032200320398482e440d0f420444050700e1083e0195107003151456000202d10001070540942c803070045015007070b807003a901c0203240c90902c6e0596144a2f484001a1039000b44169400c2e6081e200da002142210f0151181c2002c06001c0001c0d04d800ea040413602140400380b8180c10510150380c00030303007000f2140c201155615502d00841c400e410000300c0091080c0600e80010320281448 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 618304217 1250 618302967 618302969
    0x10b03071e0801201c1415030714040b06090301050c09031209131a04090318050904021f09120b0109060506070c0501030e03040302131a22050c09040c0e040b0307 71
    0x20071011082a0044c0207400c026030440018601d00c0c51550044405222041c400d590b651814006510303014540f030740c100f18440060f049180d000740d0040341c003041176041da046180070369002110082000c010850024134031740502c00002e81e043d4070300014081180c84801c01054030130380590540700a01c420030009042401200c4680e900400c1c80c6400c610402c8140e401843c00000794160309180c0e50208001c9012520b55260480200d203205107012030400c4a18124001070108450301a00c2c2d1601d0b0b80804c0440c000320b0b000c0e850f1141c0341c4401804c1240540a024082c14a69201c041c4211250a107600c100d00d003840fa0901103481c2901c0407a26080c503c0498038206c1d0400e00361000301e46010011402403601e61039005043c04180004401640c4403450000c4070501c40c48080340c0b100f030703080d40d5814110502d00701501c110381c01c1c0c10021081c100c8015404082804d014000b40320350720b1822202481c40b85499081d481b03480d01d4118800c01da04600d11006c8108203940403c00340407420140755840310a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 618305467 1250 618304217 618304241
    0x100c05041a03041406070e3c0d050307060506090109050702031605031e0403060e03030f0a0504060b04021c05070206130b0910021603080601030b0604090c02010b03071e0801 76
    0xa0804180240301a00116000361040703000801312041c00b036540f400c210702079813280002200d4003407400c06031134041c404103c4030100088918601c2102100c20b00394183d411000b0701805440c0e03410000c0d43e84c4400a1000ca290000c051f03a0388c4a90b0381c50000000d0208448843c410400e010021942c0e4505118036481405a600290306e0144c4001d0011201c0c200010100d805100030000c511148498100940c6080e6030511540c5d110703811841c00d50113071500d0702030304a40703a0b0080c801c001d4a400c04840c4a500107220040008050300e481c200100545452040310360814000030300c2112a418144020f4116090f841d4100310340c1c0c560714002c030380750282960f0031040d07410100340741808504031911003500030710680304503440d286003c41d0183c1a80c00c40da41600d0000e4204441500303054101071140d611003804d207810080da0441500240d11402075009010000303540e10111450203000b54884142068020103c0b4900c0d580c0d400700e103490038542c0b403021000b9030b1038410008005805000c6d030000c03042 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 618306717 1250 618305467 618305489
    0x1303050409020c07030c06020d200607050f04030f082502030d12091b080d181401020a020409060605180915093306030c01090509060120100c0504 64
    0x200d080d1038100650040c2e40300b06070138051018000005880c0066810041c00290090031082e03c44c0e40b40030704901d0f40100d0603401803044035541440c03100c001c2205a13204002d0704006d510f0384003030219502c440c001ca4100610a91885500d4814000d03040c015202190f200390f1f00c0d000d4074084c04c008601003040300310000e4050344215500c41d0351601802807908803181d1100005520f80c0c058441448000c1c3c02d13458140340c40d080d01c40600c4110307421301c40611450900d0038405004448441c10b001c240c650340c420840c3c0444454460b00441e8801d00c010742072160001c000f07200f80901800d00e000100f08511a0b60700c034500d04690041015058001a03124040b0301c030140503d20111059090f80480c0102107115502554080402c540d48205d060b0402d16441504604248010003c0045d01d0201801103031280c1d0003042400764980e4000707985025640213503200c03000c544a8000588803031404a405a29003200c00c1c000211844001440404c50380b40b020080c0706240740d81c4030645103481603025591b8400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 618307967 1250 618306717 618306719
    0x406022b1d03010e060a09051e0604060f1103100f050d0c090908120703020415090e04140c040216020f0f060a0507050307020a080a140f0706140403020a06020a0b13030504 75
    0x180c01c4520258000d2000d000441d0301c82001c0010750401504136840c1e10b400e0342d01c099100034084100501070f400c02456080d2a410f00850100c2640c44400070802403015494180002101d206600880121024882d0058076414010021000c0700710a02814452071481b0318006a01c0c41c018601d001260b40021484061030701305482507014200380f41040d101c040d070400c0f80c940c0500343d00c9030700e521405041c3c0c1c0058540e42403d088201241c5454411010171802403001d001c251002c02180c0d4103c1d82c001804000300100f5000c1c542440d0b1401112031740b01e80702081c807940f004958510844580e1080301d10a021411f4181080511035048401d160800c80c2400215915030054004004007809003040b00d040098650000b0100c0700e141c1c025031300341d800003c41c007800c007c0c0d064039181c21414014040e1864617004c40801c1d40e24020341c883c0388108040c145149189001c071904030b43c0a940c024160581480d10340b04060354030034101504580845040340000d00135202c00080c49030051b41079070703100d10341 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 618309217 1250 618307967 618307997
    0x702012f0408031c0605090402131a0306010b070605012c04031b0609031b110d020a050a09050f010b0f0a08040303021204030e1e090105010809120406022b 68
    0x990510406032940314003044041a1024208044c1881030b074007424065044801081480503a0105d500c410b005e2100030007840f0041c0c2d507144010361402485480003032005a280c075803c00e2403036440606505405560000b01c0d824030480020f101340ca0045200344030305d903a129280e0284410150b600480a6441d40002144d240c108104640250092030940d4118252402c4c0b111134815a0b401110f104d0b90354000c1c90109070f081280da074002d11b0300c00f490018900c60b9031a069840016104502e124504818520085545000341c0710094a0041c240c080703203c1d122059400140810380e0341d100200c0d444800043d40c480307140226a6007410301e40669041020500d820388007100301030070807020b1640920031400c000321b0b07040c1c03000d1041d80265122000c90788070b407045c07040300b0000700c2c001c54030007030400410bc42648070710780c9040c1100c40a29013101155107104259080c8030a00b990500e8600d400180001c40340d03800180b020561f06d04d0041e4451003000400031054082a030341041003c40d4084200d0020 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 618310467 1250 618309217 618309281
    0x20f03040306051017070e070e2211120405072909010c0f0f0c120804050f0102011d0615010822020102191a0112051b0d12050c06070201 60
    0x44014201300103003050300c8607061039900c20912002042c592080004012036170031090f1840e0000310038109a04007a00550201d52004803980c010081d074002c0d403a01030804203695020000c0c01c003018051580b42c8031241102c414800055a080d580c0b03104100780840c200c003007242e4410508101c0003259a102c9600717040c1c40c180784c03c1a408181884074818003600801c0004001c0c120185c03280c041e0000700d41c048e00c0c0071080303154690050791070450100911400140e59004440c1a2030741207601c90041552000100e02428171558000000c9043e800186038107a400101280200c0c01d0604403134026038400d00440d0710303030340440c1c001c804492108800c40a0444010320446d0141c0180305640c09240c0c00c00850716030500070281155030b80c014101d038907840f0080007445405041800b00042455000f500c4580e41c400701604202050742c0c0d804500c150550350428148a1990310501860103401e203000c0240640c0c1100310742c004503000d00d1000401d20f62040c0f08182860450106840307400300241d0181c09 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 618311717 1250 618310467 618310471
    0x506061b0c12010903090f060f08040602070813080c030c09150102070803040609080f01090203031c2301080f0610151103031003050f031c0225140d020f0304030605 72
    0x849402000c03501d0031541c0700c5490100c490000c10b000410711049030702d401003e04946602060b1400c41d001c1003800482e6012608590b100803a20b80100942c0352410540000c3c8200c0500a2903560006039140344403200c3c049190440c6c01c00c0d0142c3d11020764203024980c4424030f811040d80c2c0325400000040b0542c0c10b194107a4071081e010710490340801c2e2140d800e0383c03440c0e2003038200300f01160a0903401c11011004005c00580c20074000000d011807541540829a41e014602c000c102e4890700c454921130041d025482a004803021300d640d050301a00c1c110401110050070701852020b40104072049a4480700000d4481c0604240300056400c40d00d0710f55511480009201160100b1205030b100c440c0481c800c0020f50700a01031301240310350701441e40c07901b03602d02610340c50010015002444038049030070042c444904203100c1e1000142e81d0308490802d08100316000b0075140baa480741c0d600c0c404244003d91030310f0002020000111034144400e58030903a03860303100b90500c50088d0310801003400080e0098000c55 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 618312967 1250 618311717 618311767
    0x150c0a030f0509010f0b0f13270b062115070e091006020f0a0512070809030a0516050a05091503160e19180f0c050402070c09050604050606 61
    0x704603520780d07009030541d0702c140c40c1034505a45078039144c140c407101407150511075601211000003c003101404690103107810501c0d000c03000c5e902c01c0300b400301c80f226050100300c02034403402d07001d02c000035490490780c05c40d005d4800d14000c203501108080e00d4130304038807201e08080d00003000b0b1546001d212030000f044071000b4030020422a100411084070780715108a64080d0004290a42c4a10304200d0000d2a00e0031721202c4140c264032403249200822004038200b112401c080421035900da04a05010b9101d10a03d90100e4040c810343c100d1320180500850840f0107079114404c2e2444460b40c4600708006409036019a43d40000304030301140240024556501d01800e014054910300f81c000c104d0081014500d41c030058103081580c04001c815031240400b80c01c20f641100007008001000c0d51025082d03600c00500604c1c4600c1c6a0520043c442030b40484401040c0007403081d51b0b00c524500e003820001d01d0b00d120b40382085c0d00380004510207240a01a8500c03851000e49007904246007440d503020b03071101c00d0b0806 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 618314217 1250 618312967 618312971
    0xd0c0306090905010e0f01050c070f020102071203080f1b090d0c090c17160c110102070b04060201021b0109030f05030c07050d030912030b10050705100905010e0609150c0a03 76
    0x590003064000c901c4100c3c001c0c8000500d44500021041c24814078036000c90080c1d242c502000702100c011000e550001d40c00c000c62143d540c10761b10050b0b24119494000800e0741845034600d004042e409000e07944142c02105c0b010b01c0c2d68450f6103c0a034054401000703001d80c02000c0c08141c0540c14200130f8100c1040c01011109400c6a03a01c0f00700c070440c2c003e0303252000000c0e0f0701215402002007502d181500f1040040c17001c95011240c080040c0074441c1014000c0100b8600e0000d00c080d68402c21500d0b0180c06901c03046030f40c170743d03407010060b00079030040b078041841c50070050302c0045070300b0103100d039100198058841400c0f80290100881e59035000402da4800c007201404800c2c0464005c01c4801500c0540f038034001000c01441c2030203455006006c240008250500c42c5203040d640f01c50f03202c08003440c1d01d824030a4581e0b000d4904070f0708082d40c01d0160b007a001d14107681c4100340a015040b003980b4032500c0e0103480e813030b031580c02e046500c500d200040304a580d0041000300c0c00c074200701402480000340510f40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 618315467 1250 618314217 618314219
    0x50112150512030301061803150c0512010f0609050301061805041e0605060406050319020111150f061801060c150609020d05010e09030406020c040b04111b15010303050d0c0306 77
    0x14030b18510004111000d40d01c084010300c50075400007180c080320f40044400030343c15403540d524400c071031a501c03000d00340b01c5032502e01084045028505595160410340d0040080c1d40c0c5405c121499a01203118400004080000000d801d0906100e0138042d10355899003c084017012040100c0038140140041350305002c080c0d83d81c04144d010780c5402c44034a1098001140314182501000305844842e0021442a00402e40c0f807001e40b109802502006642800c000c44001d0784489443d0601800501c0c0e0076414030190100015071881c0010284208011a060041b54000c0900e8401f0341c0400d0180c0c0000c541541c184c200801e9201e90645080254040003043c0e007a1648401416600002ca94610345d50302c5e800103105140885008560280900700190306203890031800a40d00d200c01400140100e42d075464050032501d5a8200032012000f00c0c0d901580c07400465000740ca02d12041004030300501451480811050400c451281201e8150703451900304a01160500b001b44408945502815035581d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 618316717 1250 618315467 618315469
    0x140a03050d0201390f030618021e04050a0b090a0f120201030f0b1003020f0403230c0301090201080606130906080c01031410231c060c090501121505 65
    0x8404402030010703070700106101c0c01c5070320f0115003500c5030042c6031388005102024900300e01c0284030b40c44408586150032085c6030030442060380100f2040d0802c48080c0d426800300141028190002c0ca000b0760030241c81807030890a5400c024250081d80149580030301131034030030400d81420b44090042c901005000e03800e02641d030b0305007401c0b4a00f281d101410541c07402158600399a01403080924111040800b48041a1840001244d04806d050808140b56001c204005030900241c180e0700690741c4140d81c00141058080070030540355400403000918031580c1010103950038103018107400c2c0769068642c44003035101d03003040004541095000560130010700c5000581e091050040030011315001002c6e00000d03ca82c0001410745504460308107820200c04280710541020140700801c036103a0090390203940a0342c10f50311100c281d54401040d400b00e000180310385881d1190068000303141c0709500030031510480311419218894548581d07404100c541014039140c2107039420142d44000401081e180b0252924 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 618317967 1250 618316717 618316723
    0x7050f030705060304031b0c0305190c05013b090a140117031e09010329010e0607080a03050109050a0c120209031e030403260403110103020f120f07050a0207140a0305 73
    0x44020354235054900020800d000060049030491107841c441c4021107146500c82041c4141c80b4803c0c2810003c1c0c1104d074660085052881000002c044014803484002d0400303050016500e000001c1c0c0300300005000f0540d883c03140e205200700321644001e49400b03686840b00000112064000c0b03103926000c20000d00c0810700448000b001e0340030b103031800551580f24110005044800150f0840c00f990a1980403100c00f146c48242d40c0400c10003440d060001c030b80e900005c5600b0340034402000f00300c0350010903494180c0e50190002410b80d14a80000c1015590701011030081e00e003404001004240c00d04910701d0a0040c5800512101d40081c0032154001002c00d034402d40c95400520240300758002003802d004101e0000100410201c1d50803a401d2030310071113941c1c0c181920880c130004215042424585880c1d9000343c0507680d910040c110055115045c0c900c4450550350b08407440c4240c42080000a91441d000780c0c01c2c0c2d410203c440d402008158200f4007000c0c9045100890103a02400c05800040051010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 618319217 1250 618317967 618318017
    0x5040503150106030f06051f03090b10090f0626010213091406010201050702032706031602010c03110409050c042103090b071205030a061e050307050f03070506030403 73
    0x9444010860b40c0741442c002c0469507503100012a02e07040a10030030843d070f14188010014030f6803030544019404032010035801804403410044c1184800b004000190546035410421102c4081042c080b251034070807084103c80c2d0601610b81502680380c9240482e1804c0b0000c0c8042c114402c00040c0307029421058959490502d51000422544404081001c0540140c00c1c64000c52b00b80021700c400d0825090207074590103000c8180c0220144a03d00031100c02d070311441c2c0844201c01810035956410846000700c81030b03420000ca600590708003a02000740c14030900c81c400b4200c0314103076a5400c00b42061200c0c0c01621014040160304c01e020300001c2403044065100000901d43e801c000000c0d5040f52401809181759a4450024a9400e21261011a0042c201008051054034000f0307500d80d00d031f1b01c0240003001310340c00c1011030704500310018400b1485180e91109031001101222006913590301000340101d12450750b00d8254000c84010080c600b405009140c020388a810700d560006036114100122542c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 618320467 1250 618319217 618319243
    0x240603010807050a0b0c0c0d0503090a0308092403060609010306030206030f091501060e040b0d05060103050708121903090807080f0d050f06090402012003070c0e0112110409020105040503 82
    0xc00070401c43c40c079142c0b04c1c0310000d04d081744000d0700304440c0c01c101075107030006c1d00b141c24000c40320361006400700202403041390407140006001003070550f01c1b410802e025400090b05113003c0c61104c91052806044110704980842c5116559440c540d60a4144542608225011410706844810101c016620341c4042c5205080c18229003080303180511075289400a00c071382120790700c0c0901c00103001440d4000b0401043d00802d40d03010035011400e0004c25031503020300e0707009440c9005a400120400c0b0020031120100c8080104032100003800140480441c0320348109a851104541d090200482c042e800404046003d08006400c2182c6a180c1aa480e440920000c041c8200012003217048072851190b00d030801026071074081d00c5e1601344045480880b010304040e0502c4910340560b0112442d0030300500c4101c51a509981d00c1c0c60091904002c400c01c20301400811056020000c03440705200140220b500f500100386e080c400c10b5000070311004058000050341000410400072030b1030b480c1001803071a4281 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 618321717 1250 618320467 618320473
    0x15040e041b0602060f06130c0215060a050d06051506040f0504050109140a0915090c03020306150307032d03020303040c090b130f0f0e0d110a0b2406030108 68
    0x1500d868480d01800700e03a07603034622904074094140701d82a80010142d0f800b0f0720b030312061906a2074030740c00642c0911300e40d051130800b03504100541c0601c0380d021034050303407d411a044841442e1503c2041000e019490f006568103c175071100c3c46404140a030b0049030b0800084030100d05200c1c00380c000300b0308039070141e0040a41025116010400d5081c14401c9900411090b20304006a0708100c074041c04c0001c001e004000625201c81495081c04160081d0b1070b081c4880b11000c1003100c401e4500f4240030842880280e210340140b100040c1900d208032400c213207184008019005107402c59490400302041c42092211081124854001f01d0581c1c0750092803003402a0000c0d6140c1c6801c0c9418503104c80c0d0740c1c000c3e00070705041040c4d800154075860000c44410120410224201401a410390010a9140002e11ba424100000e000a0480110300e15040c00000d903103041c45880d0400300560703a460031280052040c554080000d0408085070f01c00850206844080d5080e690404002003ca410030703000400700b90 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 618322967 1250 618321717 618321721
    0x5040f0218041214041e050405071808011a010f0c0206030f0a05390d050c0c061e01060e01210b0a05041439030103150b100e15040e 58
    0x2015199102000207501d2500310321403443c0c240c0d100c10030b005d04d115960701d01c001017061003015840494020081c2101410800c0300d4a00140010194981170801c0043c0816900c0040b8007414107014000400d9183d4181c05d6141d14008011a010411388020004110070000c2190051f0340b1003000b503004401f02030072400a41010000b0705e0486102030014840781c0030144a000700c001c201c203048450465040d86440a0040070b18448400307204411012800c4d500d02001c000c100c034001c5c3c02810040800300200e564070781c1d900051001140018041036181d108034001000590300c611022861028189003191030014a00d903409062442ca002240070340e511050322190a0a00c550a0790007408121028400200c158a00c0d007802ea00142802c003001c0a2448005411144a03e00202050f8400c43c40105080340e4118040700d5002800100c0c1c07030607000144a070540d0301c035000742c070128030000303042110004c40c042c0282e078081820710b007698210311501c0640c041d115401e0050002804810303000d02842c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 618324217 1250 618322967 618322973
    0x2010506090106180501050d0b2707050a050412020604170d02060c161e020a09050a050a11030609041103030403030819020408120c15090a0b15030309010305040f021804 74
    0x244143c10082c2005000104201100813481220040751400c1c280156036200d8a8180c402801210004941103206c00114102c0f924114829a40c2c0c00c0c80544194059210351404482502c104015080081c05c20701c41403010342c46140c2c0c2c04401c0d84c40284428a019502d01408055015812883c0c40e02d80041440b08081c0340c05001c0c6a51040c25902940c0ca04041a45034040c0348030410b401034005034461303031034052280d0f040c60003501d21a0010509a000c603507403210400505011141c52070080d08083c045400e9048901680f41c0b0380041700d8840d400c1d69a032030280401c01000800a03654071010303c1c022032164809000600c09940260340b00d901c503140481c1c007140317440c01031000c80b01031038810001080502c0010850380c0313180c030401c69502c0d5501102d4100614001c1801c250032a50364005085c003c08050009903501540d01c20000018660f441601c5440820742007991690150401c01c540c3c40958481c0d404564464400c07a5810342082d00b9402040e043c150a00900b025401044240001c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 618325467 1250 618324217 618324229
    0x90b031603060b0f0405072c0a030b010602011512030f0e041a0109080d080112030210060609060f0c05190f350301080705010809031c05070f03090822120302010506 72
    0xa08401d860a01c640e00b4147d03c01804c1061428905120b204e20740f811301524281039041103441500148001410743d200d04041c168594203106100241d844c00b007102d1000c210580b190b5040f00c3c0c1a104540361120300d618147c40110301f240c2c04030100500c440c54810703156202c2c07048890b400d1211900f080701450030400941125500d030402001039104c26005040c4d039074041c1d01c0350f05441f95050a10504000d40c03800380d00d42501c20b041044501d0401c180464259405800c035000c4990302d03500c40b040d04207102c6007030714100c058150280098100545581c480400801d07070400752445040030002c1102aa210b0215000c2190409122218201c034040d8407200c8200d401c00400c007001c00c0c032600c0c40d454003801d20350341d02d02c500c1403d050092650008000c1b481c18001d43ea4001c0f10301e40381200d1940700000020081c54100d031100046660100501c400f24481d104901c0460344c04440f2a2500200701600c0070584000085080405031a140108200f240c441c00026000d11a4002148900b0300c0c2c400c0080f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 618326717 1250 618325467 618325489
    0xb030111090315150f031515010e0f01091e0b1903050c03090a03031d01020a0c02012007050f0a030503130306050c0f120705040f0e090106080610090b031603060b 71
    0x9607040126040c844200e1300c91a0283e00315a048410700c1c040505140481d0800c801c10328000d40002554041081c9030f00c190100300460074090360ba100000040ca8100141d01082001c06400038210310028040015086006529094030b0320725140d405d03688504515547d440028201080c41c403583c0e8280c182c58040c022243c12030b0760f0300d100034114a004c0c40f9859560040c0a400b4003019260b03881c802e0305002d00c40f44e2403145138010000b0340da54240244040c280003824a0f089002601d200824010380d002d01c492a074040c882c581c06000154a420200001c200d880c801060303028084050001c0007400400c01031400c5107840d900a038590346541051012a0300040c240e800f50360040044803190701301c24044884100580d1003c820b6502c2e48981164130b4003a541001e50700c070300d400c3c00218140c148041840d10865850000303201194440592507110300068a0b0001e01c4800208140f000000d02e03003144a4a407000703011211014002860300341d54680c680e0050b40c20b01d82e20110080396040c440f0400b4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 618327967 1250 618326717 618326743
    0x305070f09020a0c150612201504032009071e0906050307081f060215150f061e0a050304060f0911150d0906020a122309010b0301110903 60
    0x40c10070032143d00c081c01c0310203e280c008180c03032003070300e054001200c0e02d500c400040c00001080309003480140c601900e050040318042983c0340b14608214076a13140030b08001e1620550141c88504051542d542e91880d00400c200e808015009160514901c2c0c880c0c51040b03205460796a0382a510b07802d20284003d021024401280c2008170000302804095008402c076900130a4910f07040700203031348440903020400048005078a8000080600080d02c5600003502440c920503402c80b5241ca4442840b50b11003140550101034010b40360110240540c90040f02504002c6a2180d00c11702c0890b440c0940d03041980b0410106c0e012800c04014002272082c0e034480d0080f070440d2510200b10300d58164a50446250080300c1c543d20030302200341c000c15441c0c01c4500765105818110418080b040c041d192081c00303904010341043c0019907420b0040350440b160300940136154000d803070035201c00910001c1440040030003066500e4640d00d41540c86100e48003407081c41814602d1100326a1a014803004041c1004440a101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 618329217 1250 618327967 618327971
    0x10e060307150203130e0a11030103050a0f020102100203070201050114010f02060a0c0c150606030e060f01120c05030f150115080a0c0207081203092406040f150305070f09 75
    0x424a0384000800c00c00b501c1c40040b0050180303000d820300300e1840c4a40c0f1541c1e5004e142501c400580d240038031282c2d50189004080500400050b03440d40b60190000b440080d11603403010b00d004e400318510f04449100341d401071040c0c0f100c80c000f220340c4c0000d03a8000d0790042d0040c0c0d52a030040020198a1103040300190003440c000039840d00c41c031002503803003902604449055556405514845008001d0605c036554000c2100401c1111303102140b008018510820300803904200110890103008074809124000e49500e2065a90802076116100c080c42c5e0f004a410000c4110041815a010010001a6444071004201c0c1401101c80344000ba001030b40001d84000405810f090400d810810041e848030303d807040002d614213215000c0740741c040168829000c500645403041d40300e0740354134015841203000e60211b800b20300300720b401d0441d440b411280001c1d05829003008560309240a40088000c41d032050300215810b000a1075511000c0256801110564001002001581002c032048801089006c1003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 618330467 1250 618329217 618329221
    0x7111309210521090106170d0f05090402120402040b1002071e0b0f0d0605010903030504061110020c03070c2c1902040312030b032a040615080609010e 66
    0xe40300d003152001d6101903104164103040195184070341c0c103070b40c0d0340050550782c1880788190b4520b101003480140c070005515401c000b00880d00c524000202d0100203a00f2005007001c50326040d04645030440011920f08020041010300311554403400540002036401c4900d210606180c8100320842d044442201d0090801998255982e60082515821204800a919400780b2102000e0701c08400a4110340e030380070804520107680c0360300c0304086c0805000810080000d5030f100e5005550311001444001c00050b0100401c6c00031a00c0f480170440a5941d9004031900300d0440c01d4110240c1c2c001007202c107419800829500107110b104d4403102e0041c82003581c04d0700c03401400140925482180e03481074042c600d00c00c01180d5060095409002440c44840c01107441e29103034505005624041c42681002a08010310080246404141c40c4070030f100c01079849480940c081074094811842c04003090380140e41c1c41d00001c0041a800090754010303034a41c0d603150280b4200003041201881a000381c590040c860301 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 618331717 1250 618330467 618330473
    0x50115090b0411040504200307030b0a0611030912010e2e11072301181505091b04111209010c0f0507020105131203021e0a03050909070e0607111309 65
    0x13290183c810650700880c0e10b807411510340410040c4030b08404d07540da000004222405074140d024511b070074000c681051f02a40d0301d01c8201d0341140442003601d03954108120311103041c58100500da26982070300f0004500d0300c620020301420a041c04142030500301c0485201ca4020307485d108560080010031204014581003998011040d010340e400041c4180d09980c1984070360003440c0d603c20340030900c5000900000260401100103040046c01c100c400000008618a01450070b016940c858464400103054038203038941c0300c0c01c207000d0180d41e003504103541f9600c11301c9607804140207001014040401131031604003400400d0843d006124090204201000c0301e5240f01d910604403a01b9a0302440e01c5a02c85111500801c3c04507059880107640b0b0002450f020201500412464403051200841100390481c2c0030305107455050045005000580411075080369180110041c1e0b0006885d1500341c1e2014180720104540e0b81c005803054a060886e0b621242480c80c04080101c1100c1e402c4500b4403100344155 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 618332967 1250 618331717 618331751
    0x1021305032e091a01181a0d150e0304060c050f0601050a060509040f06090e07061e2706022107031e0c050d030204170601060228050115090b04 63
    0x3000c91519000c150381480603046215901c90300713007001e0108030b5941d80c0301b0410180350250b00600355810880d01a5812010030f5146002406c080d1030102078004036600d08440c40c0300d200440f0525551068034141c5088100701070000b17489140c40f104001100703814494908518105682060f500c50401070040340c03201003100e021100c803810310603100c031068000940900b0a003400405c00c58a440c0f00080c190429420040842c5809010342e041580c82e02001ca03403804004240501c0840c8c1c025820f00400c0c0320320410300a12101c10501c0d01038604000004152482580c003000041c2c0c802c201900008400d0804407080b04101c2c4500303441c203070841d900a40342c440c4016604000103445003948071401d000380c5400c003c07254000251142c40c04807a10280003504203014001501d04800d0365030540440004085046c0d600c40d4000300627101c0144048480802c02c2c10319040e110600c942442d000070824000c5070000801d0408400d0188e003003003205000c4591125405101d18101150001d1610010b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 618334217 1250 618332967 618333043
    0x123010e0c0f0d060e070507031106013002090f06010f0f0806100302120c04090c020604051c09080312010e06010f0f0e0d0b130b011a03160c02030102130503 69
    0x820340c280d15158640315803c000d0401d540322a01d50030b488002c0155980d4080c000b006c070340b40300303403030710380c16200081103055492400340a05107221051200030070007000790080000ca5030204404c071070044403240c1e011170b40341207041e5090000401c080c001d1001d25038002c02d111180d11664030340a0300c52000c81e68018007142d0003508a500485000c000c14058610980440d0b8a01c01800c0b0402c1c210705142107400107640c0640316042d0118580f000d801e12581c4041061400f41c0e40000081504095407054074a0009640d543c034814001503840c001140315007030010380441d04148a5400032585494001d0445810040c00230303040281c002e0701401801d4004004441109251424008446072103010600d11008403101030811010a410440c408400f50ba907032001e2807180000c2d0160366650403284200400c0c466091420302d0040c40025015000394214042000051030310618011181d000709089030f20540c0c20700c2c1d006d00009400c0c00241000c00041c1d4080c0d03c401410403034a0100340c1c91300c0d07041c032003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 618335467 1250 618334217 618334237
    0xe0a05060103290f060114090303040e09070e0702011a010c080a030e030d0905070f0801061d0402030a0b0921030702030d02030c1b1f0506060a0e030f0123010e0c 71
    0x100030300703e031100d00c2840b80b1003101920560742c0c400c40c10b100034132192020301150310383e00084070034502e84901060001600d042d088050004c50a041c100f4580d01031140d0014206d048500c0b074558001407001c2205075050007419103400010304009054208040b041c1030002c000c1c1030240c440c0e03000b00001d52100031950250100d00c0c0008201140f00041130039881084d000c480c201e410050789009012010440c01d0444840c40015070600c4e5a91701041d09030342d01441a01c00b005030740a203003001c00800d42c1085501500c000d003034540103c02980c0d110f803072003015603a40d84aa442004041d11100c69501500b00c0688500002c60071072519801c02560b91141a130740078441a000702c0450389420110065407144c1d0010f103120602c50360302040240d682c0118910300e581d00322913501003082941c550f204881c082c40000d05424a000941300c800d84000c04803403c42a010b20600026540081d4203101e0000038107038456004207599124001c40c0812201078000344414080d0900b07100a801c0000c04880440503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 618336717 1250 618335467 618335483
    0x1606270b09040902040501080f010621030c0c0e0f0103050c012313030512190503012909090408190e0d020409081308030d0f0c2c0616060e0a05060103 66
    0x207050700410040d0185aa00940090070700c8008964042c010400704824456540200010b560364170240c41e4242100f412444a556400026004207228100c0c0d403403801d0141c0f082340c4020307a449214182640b01140c606450141440040c002c0141c203001c01c0c14146000d01c0d00101040900051905007a414540318800c1c2d18001521501d8103024001c10006542201c192842c00d00341840780035113580403081403600060480d0700c1c80301070b03405001680e0507103e0340d011203c1d4880d1071440c4419840002030700703000e1442003400800329955510070414407952044a0f4903407aa24000030170002d00442018401c107206a0300400d01c1a41c544000540040703804035808602102c6608086007248922042c0314584520000080f481071030004c010030440c81c140c0c10400c40c512400051404890205201d440010b03144e0108800c0440c600c11115003801a210281c0e401900340c8001460310340c000e400f142d01c1000c1600443c01440214400ea01c6540c0701000905a0804103986840e101d480c1404002c002507 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 618337967 1250 618336717 618336727
    0x18050a0f0c020705130623041401030b0f0703110310050a060f050906070809100203031608240f0a030b0a0f06120303090f0c1e080f030412141606270b 66
    0x80c640c6d04020010400ca08031003141e01146031124040d01c40207208140240e08182c050885180c02c0d0a000303040720340003800c01d1155101c08031045a05007000e0301c24401c044d00c603072780312501e641e1070001036000f2403201410405040ca08800d020600c550399101c1c10610101c4010400e085d60041c007110b01c0d0321811141565030b48041c0c03509903868020051a10341082c020000302292580000003980900850b0213550290704880c2000c07202000226940c400c01040100768800c01c3d206180041c0c110f01005203901c044645840110b04d042805d540144c89440c4d0400034410010481e11410010b140500c0d41400403d04281000030106c8020f4801401c160b600e425010a010000894401c1c0c3d03a808140d02011680d907180148483c0e2040740c0045010040701400034200d103000481d001e0710500e240c065030910386001c44d1900407140d0000c055030785c8011010600c100030010301408118204900c15000000c0c10240020b04001e41c0550702c0c81186003141c0c3c000441802550190100c46540d40100c0c0d4803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 618339217 1250 618337967 618337999
    0xf022a01020403080a0c14060112020d0201170c0d0e030316120f060b030105100309150e03070c06200f0a06050402010c02040c05042c07051318050a0f0c020705 70
    0x9102d03d83c00a0500e11021440903211548040e014040d240910144044410190080c546400d020710882d00080070245201300141080b5030ae40c0340b9140141000d0004c02001c10010401482c00c03540f01d075001c81300080e001c0c0241100d104500301028504011810b51802003a400c80c0c2a0002c0c165a052100c2c440d00c5821900458009444101580c1c40c02c0c004640e51f041c0c80ba072160002e0141c1c512400250403d05031882c07103407040c90785060b00100700c580b01d01900c62a03400144100300310200e5038001007114001144031031007404000c0140365603842e80c11400465150391190343c3e404007101c80d0008100c10750300030800034480c00c515400c003400103003a0b15988010b0300c40d4005203c0081d0494242001c031103400d0b030410046d10403200f070480561320000080c201599082ca100300c5559500b01c011011840b85885407022300b42008007019405000c03520b4540104101000320351214842d92658100020708015005804854a00100a0004901da83e1019440c3c2005000d00c40c0110350b54054880e01d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 618340467 1250 618339217 618339221
    0x3060d1502160b1317090301060e13032706030507030b031606021213210f1407091b0e03010b060a05030a0630030201021b0c040f022a01 60
    0x34035a8120011582e6a440d9a200e81c50b282c1c2c645000d0b50b40d010740b10002002406851039200415601c1004090901200860110f44c0d82008040d80d030159603032000410f40c0c24807240102c0c0503413604801801403c1441c40c3c01805c001c0580c3d02540c1c5a2901079410102440000d10300301520440c1c2808101c44c1d6561800320014421130107210390503c42c0510070b888140e925070000040e41d103244d00f540c0d01c0d001065183c0180d07118070780c21812150f900344020014907403c20110b04400e408050850b038901800d8075150340d6481c401d4015681011250740c0300d8040c410812650004ac00c2000013800301070102081030f290500b9074001101480303040e0301c80f14410780d0290722080c3d00c84401000a500d500314408020040e40040300c1040d0564600308000c600d0310014003451209c1e80c1c11190070042500704950440c081400c6074001c50a564080c0000280000400c007103035070311183d450003811010914410082603902c180003040d0140c1c4100710011070ba400d1078a5000c000015040380903101b9160710400c80c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 618341717 1250 618340467 618340493
    0x3070c0f03080723090d05070f0e0a060e060d110109080d05040603150305032b1b081e16110f03032502031602060d0606050a020f011103060d 62
    0x260103021000e400700741c1c00c0b080142c0a41042d56a84840105007011041d65400c000701c0a0a003040c00e202c0a03015180071221520040e01c603109907529265104031403c80240103402145000d8011410055400c00c00c0c40382900400c26110003528a040540c0410101004402c0c0908410301d031504039401d50340180301c400e0041c6403204c01c80c0d0410205c12001440c641050050000007820030740d80c0d40040120720054000d407a0810302840c40c2c46c00d0342e114240c5445c6281404000d9190410a00c0d26083d1280b1807401c0940c090241d050742e0030030041000300001401231440408400c034038501c1c6802d80d9100c11455001d105445841000383c0030020582300081c0b01d03a11103006119200000e007a180c0c011020318010445001041c2c000e00c0d040880807010202ca5410030b0040c1c0c410b100c0c00214003481d101050086001a044c01d00d002460884801030302c80d01c0d0000380c017041c0000340c00d80085034100096113001c140307130008100300c0d40c5228150006100c00b800c82886000c1076407400707044c0304c140300c5080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 618342967 1250 618341717 618341723
    0xf0807050c0d060203010801060b040308040e1f0612050a050405070e06010c0c030606060216270605100f080903070302060103060c020f07120203070f05010804120905041103040506100302010f0503070c 88
    0xc800b024541c42e00b0300283d8001d000700c403025401c207003001070b001d4103000584040d203a0064900e0704180c288890b400e09203000034250106d5001c020f21801d5518040c6140c800544200e584255510340341144d8a400e44038094401c0100030302e05001c2201080340894400160307103102d1907030100ca8642000488040080d22005851401c1d400c00000420545a00c00812142d0310f4090b280350102841000b0102c46680c402e0103001008881d2541114102c0000e41c070303c00039244c070001401d0303885e8004600d466854204110204443d0741c00b840f0b5403500b003290a42d11003003a400851504046650081d00c404040c48000c2200b84c0380c0e035012403c50300070312250b021906041d00310b91f01c0e680e40303039000a007600000205034040e0140d514003295454880040c00183c03401a151201c0307940710b6a4401c662003210210030740411a01e404041043e9503140141c00078488103100580e22808d0604260f410090040c1000441c424038440c03c10050b600140407803e0101135041580d1255912002550481c455803001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 618344217 1250 618342967 618342979
    0x5070306060f141e121b0105120f06060f0a02010c110309030c060306040b06070507090c052803090c0f030201090e07080f15090c0304030806030601032102030f03010b0c190f0807050c 80
    0x3d82c07220728000804511b001d03141040601d50340d040d81c00648152294004048150b1100e000198440b0305008500d6080136001d003000e443d1440301c242902294002c10640c80060351510000700c21198401032044002d20040061454880004002542c07503000103101c50250201000045141d6180d50040c2c0300d00380060640e42e42c8a206141c1641c0711411809040b09051800400c0c541d00d80c41942601d209640310303405d4841c8034038000b03c1c614200d05180b00100806840b007111100042030303001200010030150b8041c00206d420b500c0090845119604000301640000c4204480c242d80000030a800c0000303840c0b034440c29103400c0600d03100340e10903035000d5070070080e14801d001071b46600400841c4968001c1c2c0d101c14030758487d03604243e141e01c02848040c20200b100e00340e50381094a6034041420840740c81c01207030f02c0c0c00002d28140446403c00d92210049443c042010340410201340000d12220544148220030305101d60395000c4000000c1c60090300d04c1d039000ca07080e82004010000c42134001001014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 618345323 1106 618344217 618344239
    0x420a11060703090f24090b01050a060311121e010b12220809010302220305070b0c25050d110a06030e030d0903020106050d05070306060f141e 62
    0xd031003007031032190750484c0d4070546446046c0d4124801d804500245d8034020400c0070b1052507500134803c2c0350500b0f140b0317114415818103c0b0b5040300032503040146070301c44c03102c0310340b15681c12007200d4404030072200007080400c03031540174100079900c05005481580c0c500811402c10707528400c13910280b00f1f01c00200340025564030301912552406140050030700317145810308824582e44420311240d000e4104024030601406201c044c014052818800d03103030100c01c850b00c542d00c444003505040380741e01c60440380d0580302140513088020000142407144062050914840c1c0c04e4218401c02e114000c00b440019034503000e802503100d8842040090360402042581c024042d044082d0b0840c03c5540e6503102003401d03071351740c0114070203503000310018040c49040d454000704071026600507904c501907440003004112005910340c2c2400e00107643c81205078085103061400c2d084054a290340c48406504 = true := by decide +kernel

theorem cover : BRFrame.Cov 618165467 618345323 := by
  have h0 := BRFrame.cov_init 618165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 618165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 618165467 ≤ n) (h2 : n < 618345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
