-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0142
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:04:47.561653+00:00
-- url     : https://prove2.me/submissions/c443e2e4-ff18-4e1a-8dd1-7b21c5bad8ec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 25359718 ≤ n < 25539574 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 25360968 1250 25359718 25359757
    0x30a0c02030a090612060302040906021305010c08220512010608010e0c01021011070804030302070e130b04020f03031c06181407030f110d02070b01050f0303161703070906030f05040206 81
    0x5c100a6001c1801150020300a006110b000c0c1031400c020341c800d03030080750280ea9154000c40c182d40a00701b181e00d0300c0d030701400d101d2800300c9032070f9103003506220f1049600d840805078200280341c0d0784000c0400440700051000242c200d00c0c01d10041d0840d218820384001e00d80141404950307903a008604904050744500c03001c2000c03103801006c04600c0c071035120010513034a0042004002e00d50b0000d012400d40e21608513200090701e0700c40c6c480e08070000860740103081c1d88141c000140107092400340340d4003180e17000e0100c9007012014405049401d8a614600c00f900ea500c15007040740f084003e2035401c1441c8814410010202c5500f2065a15800145480c00f4542c491092180304005a801503140446801040c0d84525038003c140c0c0196008070400e03145001d880b000480c0714070340800c0707600c1018402001140752012121001c0707020502640103503540e08100002003001d0780581300031407280019030f460715281401e0560140c01c40300400507803c0b40605c0d000c01c100058440341c2c11100001c50380400c09014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 25362218 1250 25360968 25360997
    0x60a11010603020d030203030f0a05040f020d0218011202010e061911122a070b0306040e07150203070b01060201060e0103020105070807021305090c01030506030303040803060a0b070503030a0c02030a0906 89
    0x9041c950788000d411034540742520050560200146004080d11012040c171901c07800a0101520020380d80038000780e042c4c114020042c608280070440c042e201810b070484a6030003030705511003c0c4090b80010400600c91074080115030784010400240c400403074030241802600c01c658040a101c282d8042d003841098803018500c1d20080090083c051380340d60f41c866640d40d071110080007400041d0f0002c240d01c0203010500e15500b0010500d201503a80c03810130a41950354580c1000041e100001c0c0382c1155002d03100300858281555100c459004015800035960707250246050349414505038001000c41e45884800d201040e180c016280c11240c0920302551030b081c85091010036441030010095000955032080041c011550300041e1042d84e0406c1a1880503061200540546000300c0e5034641c9071308100000f500184a00c00a0350b041361004e484800300075294032030406c6542c401102940c96506c00300030051103a42c280143d81c1140c007244040d41c01c043c001d40b00a0140318090141c04144a00b100300d1910 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 25363468 1250 25362218 25362221
    0x6010c021c1a07030912080c07050f030408060f09060408090103060b0d0606020c03011a0d0602040509010308030a0f0614041d01020d06080705010216180f1109030714060a1101 77
    0x100410075901c5110781e0121890042072a08024a0340304214225500060f0101d01902c2099100c942040d0425907032400450704446005008200307201c7c1c02800e0100001150041000c0d2444c4545c05004507561800c0c2a0a10302d051401810710181e0044541003000c6800c002c01c240c0c4d023280d48034110319203450660005070054071081d00b014076011004600030558200580000c0101c0345550203441408034140d040c03602742c3c0c0a1035042c8610071464072011980781044e9040481081c0210360050a040d19800081c2045230203a2040d40c8440c400b1040c440340300310390b1241d417880d2074506404010306458000000707800b03200b214040d84115691081440d11588a0b080540d100c0c41e0507000f15501e40e14031160200400c1715000710401482810400310725540005100d462454140440900c000d14044088085030301c08100100368071386842c07421083c000d650003480382503c4010303520381d203804104041c58500f00c460343c482c140340d084800007001e05803074080459a84a80c2440e25142d00b441d09810f150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 25364718 1250 25363468 25363489
    0x80705070209090d080c032205070902030103031808060103030e0d020109091d12040501020c060c0f01050408040e0703270c030515010f15021c0e0a08070609050102031206010c02 78
    0x2e402ca05030504002d0240c5011585002d640404e481d1903400d80c440749001c004600044170252040e10f200c040c00554003034040c4900b10120f00c180b040700c95064a901c8004103070b80080e0720880c0482d24900b0b404103841c2e41841c2072005060440c004141d55031454500074440c0450410705070060018095110969208040c001d010305400e00050198010240c020030b54021100d1119815008005100d209a011202260304039031059004180c04070f040402c000c480d0b1303c40c54800c8403070b21540010060b5800c0070701501e88141c1c0100d6030b191700c0f1880d24001901d43c40d00201010100f40c60000800d82c200b02201d20055a003841042a550b4244140352448144403e0380001d0000e202d40282c1c2844280845181c40c10303114000c800100041c5c0c0e6004038000210007003608005030700442e02e40304c1950018281604114818030b081c000b214141c80226858020700d8018aa850700120005d002c10b40c0c03c840326900a007401c0c40107614191450000c1c090300100a0042d5041101c042c090100355a511110b00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 25365968 1250 25364718 25364723
    0x1150219020607141f02190e030a05011109040b01180b0f0702091305210406050d0605040c09060206070c0209060603090a08030c19110607140c01060303020303091b0d0308070507 78
    0x1a00300c04c201082c00d541c0b00d0358101040e0314100029200d40d00035045000307aa08182401c280c150403680c011a0960351801c0b2148501d8141c4104450540892800d019800c458052140060741c1d03103003a00305102c19a01f00104140c144012a1a04112b859124001310b0031a14010101a1071b0303000d0ba11740b41c1d0244500b1401030f40c03015511342400032050000c200c0302c6295108604540c8011039419440d0030942e54916443c500b094240400c2140c140500020400000c01800000b003c5460b0400101200c28034054000010075070b010078850a601080881e4000400d8200404c5221043c2d0009500800041c9402c1c001c66001c8007040c4100070410100c06038540c42400c071034903803402e100d8071849030f0406001c0403001c104081314110301d50700413054405840d1104010740250340d1403d00580d0182e1003000d1580c00e0700300420641501220a1140074060741c03180c0d01a40d80e84c00c0800702c1c90300d410046000c5d104100c10700080c0c3c00042e0340d0010409001503240c24110500e540b01e01d401c0e2414054070502 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 25367218 1250 25365968 25365983
    0x20319090f0806010905090a15092111120c0a02010311090907050c0111120a09020f09090d0306170d080403030605040f0203160206061018090207080306030601150219020607 76
    0x2044200b408110503040e0b915211341080305594000420b6580c807940c5034082d03c620b01104102d80e00040701d4200d0110031b0701440ca04150700178540509903004c165100081300141380300c026406402c200b8030440c1c1158000004150418506505060302d88601d50303c02418542ea030f80d000244020703102c040e01d40c00704000300400014a0304890240469004600b4410a5468024102d000f800c80c841070b11a206118491460150741c3c5c3c1c800b90004216508d01071307900c03010740081100076641d001b034502d21a1010202820040d202500050306032019508510f9100c020010400b064200015280d140c1140a00e008150760310740d03080581c01050240c00803900701d414590211b15642050300210f0043d42d003000d030b000c40b00d10a900d00b01d8a48809030fa220381e002c5858a41902100e124901103048a42e4210080e0070117070b82c1c1c5c9824002c07a406440210340c580d40220810269140500c0b88034010180207001031008551004025110b07560314030303410b05c500729091240c000d544400d410303035034903c0d4400c60 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 25368468 1250 25367218 25367249
    0x4150605030405160803030415020c070306020a031a0f210f011401050409030801050906120105040c150c0302031e0405100e030c0105070f0b0a1503060c0e04020a02031909 75
    0x2008026a1089400b0b69a0744140c40c107040d00c801d41ca001c1002150780c00409907007540c80350390f40c442450390206601c48501d40c0074032800800080906c903c1008508c194030042c3d03911008840901903e006055059a4181c0c0a02e607041c580c55011000c2c88000c800c40d001c140a000c804421004048545400005842210301820300c1c0c9005510000f440044441480c074540e0b83c0300100010f4401400e00100042c0c0a040100021300b001e805ca9074101c2d0f00140300e90843c06890107140d00310f07541210f081c1c8448181c42c03020000ca00118102c0a42c0140c03034a441c070107044980d103001c0c2d03480c4609145101c01110403030714940004814410781d005884001c04032500203481c0a0024500109100032a1007401080080b641560040701212615031f031101d10807099000640b9804d0254000802c801174080e120070110140040703000030f01d40903500c070712000243c56038a81e600a0019003c60101d070300a9104010101da10b6070000141d034600c1180c0c29070b005c08007101403421121616550310810a80e0810403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 25369718 1250 25368468 25368479
    0x212040302240601120905030903100605040f0b10080403020c06040801150608070210020c031201080f100c08011e0306020301080c04112b090b07030903170103120e0415 74
    0x340030072011500c1d1007402c084006030700d0306a8240b0050314024041030503009829803000264100041c118024002d490030400e8040100b4100300c2c1d01221a00d0b00f83e45c400c4d0500c060701d800e1042040d6001001d104100d0120441d0104103507400c20705030350043c465010005001c040c4204000d0403001d0001e401d09071115941c10005001c0c1c400014081c002e0307440c4a0010441c2807003403200d40e208a159a009081600090307000740c00035030001403c03001e80d000401804d51400b901801c818000c2503010020321341104440328050524101c0343c0007004145c10500c03243c0025502040260555004040603241c0040b407030050030319001554401060f40d40040000120800085a00601d41d13000383c0b0107002083c03512601c04d100340300e0f0520040001c81c0c40e420201000c0e854901c44008a04c0c1220000351017007040d01c0300c06a4100403290000004e89a01c445010076600140700d410348101c282c1c40c4220355045a44800c03c00010072040010010400d9498400b0750761500440180540d5a9034880c8017030b00c48 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 25370968 1250 25369718 25369723
    0x60b07080d0209060403060506130b06030106120209060a020d021005010f140d02090a020901020c03030405060d020a0903050109050a020427030806030c090906071b05030f03060a030b070906091703090f040212040302 94
    0x441d88a841001d10f040c8008010810303004109100d0383c000ccc034586c9580c2c2008819100d40f59000d0a14401c15428042c81501c0d403640c00040001c0c0c100340c3c0007403081051045000b803810712140c001031030260900300100102c803004650350b400e41c0e44407911046e070807401101084610f1441d000c00f940c811a00f030b091000b002e002c1d6004159401d000e07403c4e1400302d4200024103542c1c3c4900e1050a400c0402004009030b6001150b0213008000315629103485900da480d2502404c2d2804114180c1d4160451a00070303045140501c515036000c0100f40c5034035541ea00c00700105100807400f813005014800d000c40001c0c2c0769981486200402d0400070300e8542c242c1000c140c1e0b030342e44607000c0325000003143e010784012a440203c200e10a0009038400010351030601e04aa1240c01a040604503680050b070106000c00015003605003184181c1403640e6034140075180140041680303500d6401401b0300c00d9060540c06414a0200459081010590310f0704002121800814000e02c2442808400c9511260a01081541c003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 25372218 1250 25370968 25370971
    0xa030305040213180f0309030b0903040e060108090a030c0203010f1d0d0e0603180a020a0305060603010605010f090506090a090c080108010e1c080403140a051c060b07080d02090604030605 82
    0xa46883d40c0560b030494980c030072112200080d40301660301d164070200041482c00f0032078217288685051880c1ca5034981e20701010320380036034503242c840d0408142400000c4080045603403102c024a0640f00341d0400c004856250203034818050104101c000d103043c00d540b025008014602c18621040001c41c3c032107104401905200064800b040c0585401113208030b105412808103000c00505c01032554890100c2e0b0b2440070300f030356001d00c0d050050308440d00c056591210040000c5026038007403e100d16003002007608403900ca410003414400104074031400c090748080e810003580d00580e403007903071100d1800c009090000d0b182d21984486080100d1042080e900c51580e80c101d80f05a0001d0000c10104142c050f220704540c1c510089491215540072034032485207c1d00b64009009040c01e291072035045811204581c00004a1408980b0005401c0041c4100f050300000c1517012120402c0f07064140b1441041070303ca8881c000d0035a60005c5064041d152595040321503c00c0300a00441e036403682d0b407500c00040c110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 25373468 1250 25372218 25372223
    0x7090608011415090a110a080a0b010c0b070e031207030302091c20010e040c02071401020303010305030406030506031603061d03070b01030318030f0507080601060f050a03020a110a03030504 83
    0x34400d00c0325101a5081140e80201000603004510710f2060081c0001604000c01c1d0341c86968480e000c644c040c51514008120145540d51920744519003203a00e00d003501e11000c007a03410800350302182c1c404190806180341d0080c100349404207100081100081c500000b1182c4c080903194002551020140c1550091110303080980d10510312820540f00c000e048480c5103c043c0580000143c00c0429100c0c4071511040c852050510b041e00740c070b4080c040740844010310140c1000da0308c0400248035841d0711040722011000e0910040d0302d59030443d601d640d12409984600010305131a000421003950302480f08030001d008251031401c1349996802d06034041c10f60000300043c10f0081e003400d1112a1400701c100c500d01c0e50004e50a0283e0792035550112905140d07510906000d900c407543c040005002803041980d0b460140300286400c9042402650a000040e40540180069801c084803581d0f044030a0741d0307480e1403c9c01d0058450890340b034242c400da1103188d22b10140340030380a41d032800c043d09a40f0180c091070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 25374718 1250 25373468 25373471
    0x30f0709110304050a060507050403080c0c01140903280209071809020424050f0a0c11030604170c0106171e0106050112051e0103050a03110d0503071805030709060801 73
    0x80d49404910042c401941c000d07000303401030343c454000300e20035410480d04100b00303142c51841d29603287c40355100ca13000307400740140b00c1c0c002d0a00b9981c2582e12081240314079500b00e018a14224030b1400196940300034042d0410f100081148030849107101c20b42c00400680c02401510075803800c1c08005204000d0305550711500c4c4030448020a00003024800e41b0300780d82c81480a4002085032001e480c0d089080e4550703420820004005942450034000b0240c002040c06484207072462860b4907000d402c000c8465219400fa9108200b000081541c1e01d061000308a080d202c003e64a03205c140c10680074041c0340c3c01007001c10002d40e240c014601c800150b5030342d842000d04140f000d01d03000e00c107616007640c0c034611400b400a01400c0b00c1080b10295640015000303a2071048030b090724000e880034074042102c268000c2d00c042c0c007c0390b81c5030305040e0800710700010b540e00c4201600d40c0480d040405480c0d400054000c108000f19507540c0011912221010307400740c0b000404541c10141e85203048009040e03180100703180c95 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 25375968 1250 25374718 25374731
    0x1903020915040908040e070c0803010303030e010603080f07020906040504020a03140109060c0e090604060e0c1804050408030711030304030816020f0105010e091612170d0203010b0304020a050105030403080703020a0905030f0709 99
    0xc8c403610401080a03800808203103540d103107450840c040d0180c031865400655982c10000001144c0c54018041500c0599100d070300c3e0010781c010440f120301c00401060189040000f003000681ea0000d61070280e0b5031011104010070b12071500c050040100800082165140c20700c401440c2d5002070500086010032209440e140e9640d000740400d4034100e115880c0c0400c40d09020510baa003152002c0c0000c0100c1c011410102c070200350010b8252b400580d42030398401c00c00000d02c4030316a80000160b501c6000e800055240d400e20b40d60007018114010402c00c0400b003000d10603801c06100340f1410300d54080c4400203000c9561551400380c0c0c0c1410950340940144544002100d4448508a442d03041701e00119000250420681302e4110910651030b02e01c10501080010301c8020000d4800385028082040989803207251510520043c00140d03048241844414400c10000030780c011500e80e40075036135280c096140c001c03200d0103443d10390b0b25030451545400340c800034540c40000000e0360300882c1c00c0c11000b484032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 25377218 1250 25375968 25375981
    0x807030b0105040b0f040c0c02060d05070905010c080405060915030702010b09090c03120f27040f02070b13020402040b0a020a060506091e10050409030f02010b1903020915040908040e 80
    0x1241c88000b191070300305003c5c0c2d10813170f010315150344099400d181a040000c050400d580c0003540c940d1101100d81e410704d0f9150248051550b0241c07419000c0c1c031080c02c00c00b0710f682550b266100140074030300c51144180d0001070f20300020749900c0750305646010300760095520b0b8101014040e01070022005594019420340d00041d00c0250001080f030b00391034015019010440c102014040107500008110441100411141407140380c03240e444800c51103080c800720ba1400e00c050030401504c0781410001142401408110013082e1030f82c1500e0781003c0c0001c0d0701214404248041800b900a0391b201c0c483d20100440c0c60a555600070075000c1d1004e1207011308001e141e90742c10030410350200c02ea420251248910244051008402e68503a400c0b0341d05144500c5000e95030b000080a85000c96002c50015078510140f140b0a50240101c01d07d0a40c11107aa000d0ba405070420304440c1b034183d01c000b900c00c6880700046580c1c013101c4a1600c0b403c07600504140803521084c1003d89255000f0b03c280240507082c80c000490303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 25378468 1250 25377218 25377221
    0x207060f0c0f050418090602090a08060403091212030c020c060c0106050112050106020607110c0301110c0f0105010b09010f030b031006051305010803070803070219030306080f060606310807030b010504 88
    0x1910036030000b2100d0640d00844800082140c003400311403650b409c004062080da19516103d0003803007420003d1603903140138900101902c0e850ba11281c140d0f0748088481c0005409480c0c094190a032a00d40040e070200c2c440d800701c3c5081d1400040720707080040040d51134289001174000c14180c840a0700c404400c04060415035040b1102440740f2401a000980030450441c49485c0d1800300303160900c121418404800300103400c64206043c100d922940010b40790b40e03a181c5c01d12100c0300b480c03040c00c002c000541c50001c103601c40c0c0c441d01056078104102003d4540e6198060741c04001d10040240850784074401002d85800180b00a0081d00e116035150713100324860451900405050320700400c00707942044080d64450704185c0020380031109500965218030540d08092281e400b00c107000303580105d0300303074a08166107003004011901d02135550450740800109444800c110707142c0d501a60440b09814110703a000503600c10301c4101005006004240014095000040590649008180b41c10307240c0d90380c904200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 25379718 1250 25378468 25378477
    0x80c06040e01090902061309050106030b010315050609030a050105180f06100b030606040305060f0402040b0a030308010b0711090c0915070f020907140c03070c0b03070203040b09040207060f0c0f05 86
    0x80e80d201c6540c0050103038240399000b8074000d0b480505001c0c10901541504104458190040c107c41c503943c00040081640c036000741c544600084c241045146405480c2c5440400309001d914000c4000050001070780d10b0402c112004641c0000007001582020010302501c143d910340341c20900e10440010030002e102c04903116000742220001981c480d4070382841013a05420081005a0114050000001140c3c0038012584180240c0009903814513103441004100c4142049250080c908100c041c4000ba40008056040d60b0445c040d40b07858964030320b007040030001480c42407908442104140041d03440c004001d0711035264100d03000d00d401c0c560b10080d00c089004061014200480309150240941012440316030003504501e0614114100b1b01408440381d030022400b240c0d2039000088403002c0c8004800c0a00103889410750a80c80e504051100a40e41e0140c1d0042105121002403010f00e1a074a590446940541c4036105000312210340100c94010580002c01d074002c5464216041151031060088a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 25380968 1250 25379718 25379729
    0x32609030417010204120b0406050a0209010c0303020c070305010c11060c0315010c0c0905071101060e06030c10022103091020070c18060312050313121205010b0301080c0604 76
    0x4500306460206022542c8190628000055600f00008501c41d081018681c0809028403090075a81c205880d0030821910020244600d903407044c0f11283c100d80c0d00411f2400180d80510f00541c03505c0bc1e03034403103500b420320310b500c0140103601c0e1607440140c0c1500f00c0c00d06040704c0080c1c4142d50280e9034220308413003184000c803054900300c041038050060079070151003040c0440d4007a41c20010b0007522503500004a41043c1d4460012404107228a80078890074040c0d000600140981d0b409582010b0020955600320110928802c80a50300450780300d41c0301f00711804400200c98030082c0703030800901517800142e0043d500b46813680a000030108503e0410f02400b800d298591000510001c101e28600c1010f4000b000200c468450820000030301c040c2d451000c089904844000003070092451400034000e08101c0090070502c00c081c41001202c103000c00c6805419a0000c0042e214904000760840c0d60000c2d0790800d060f107034030b030400101d407607041031001e14142c602c10012520110340003810085140a98400e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 25382218 1250 25380968 25380973
    0x206090f010204031a04060906060602030301050a080f03030a090f0b0103080a0f030e0c04051f0f0905060a0303050d090f080a09030605090a05070311060417010c020105010905040203061501020c0a03032609 90
    0x50fa0321101407545c103a2007405a140060188225600d11050b640c0541c001801a0700c080014801450a2100d40b0300900684004100c000310001003c0e0720b902004004190541da507940312000d004403402c0d200e840d43d0b03008011080e11740c1c4074070f404216500301c98441340c0082c82d03001d0060036031400ba1103921840383d154070050044c4200c0b0020403001d440c00a2044c100c01c08a203d141e144601b4a01c030102c054a9a0305200b9003280c10480181d0894030010007144c861804001d0400200e9001001c5500d044010f047c0071a82100a052035002144203000082c812940000c0000509074010a080c0650b40304070070601560702c0700c561640e0b50702c40c002e501030020382101800b040010041c84400e10f0312440644094140741d5034004201c10180c80114100c8240d45980a28280075820300c60341c2d0142c00140020405401d29030040382d82ca19000b84000c4000c0c0c0e001c2254070842c2c2c001c0050000112000f81078428198403441c009141040d907000c44907948598552025006000041480c4520b00c44c3c1b00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 25383468 1250 25382218 25382243
    0x20307120e06180f01090c0509090105010b030103030e0a050607060e0f01021c0209031507050304150504110f0a211502090108130804030602040306061502010c02030307120b030d0206090f01020403 86
    0x20007030f120201154a58010b108107010b050a4a07070a0040304038030780c051100b01c101d035850300082c0018070000500900099241070010710014503081c0a490650760075141815058200300003284d122102c0d6009a41d10400205040c41007200b160055034044400381c0507070b19420b918011540c02d0b03009240c54070384201c0b41e0001c0160760b0301c0683d0180010020040840b17151001880003019007400658100000038000810441407100581c8040100f42c82503208111a02d4123417121200051400074241c0314240301e29a10307440d540c0b0301e6103180107840d1130714541c400d100302045050b2400d0b40f524401c42e1a80e601007180300d061284c9100303940401c034040c3c6515415649004143c00c0f020404c4100320740c1d9010501020002c21a188080d2000c0c1d80700d4040083c95a003408040c002d000d040c034400500f168108048865200d6002c81641d4020130315003040409028202d4051000d400d0120040780c01d8460035440e178118a43c000340d0382e4050100342c003c1e190401d9143d50814203074861808054941d42a100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 25384718 1250 25383468 25383481
    0x705010b030a0c06110304030f060e06150303040b071a090f010b2706030708030d0605010e09070215090705030a0c06140403050714061b160801140105060903120d020307120e06 77
    0x801d642405c210842941d2900707480350388640ca10030540d601a5505980c40f50b400714a00c0c0308004260300051200c00310000610b00c0300001756a0b10640c09035106500b0007040e400100310b000055568200306080002080c0d140180c17015541c0c000c2640e0014440d07003090705d10b182d103062030040340d0164801c05110700c681d12800e4510b00385296000e1f10058151042d00c0f80003803041c0090026000d603441c60031000c03542a16140004100d4005040ca5900c02c6000000b0300c0b00300350b00003482200050112040d000b16544102070760703003002c0145d032015403d40282c103102010000c0081e03410003039401c00d4850400404490754040c916006a00008180f039112a105004080d005c0d245031542d6a001050ba5240070044000c00c613075080c200c00850010341c04100302c21041c0d0300d074400c450050841c0e0b42c02001041d4440001c900800e030306210b05801a000081c0b20851610180000c0e40c88000b00071000c0d5030354100340720100083d4000c03500036000481000d030395170702d000c09401b80c40f440f031069900604c215141c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 25385968 1250 25384718 25384727
    0x4050102070b1b03040914060a0b0315010e0303070605012103050a030e0a020a120201020d05030c090f0604030204020c0312060103061a13090c03090b0603030c0601060c0f06050c0705010b030a0c06 86
    0x140c201c120f168048114031100c00000c0000740003030420400046100901c04d512141c49401c05000e40d80b240700c00040511421320b608054035070250070070a001442040c03d800603680b1a441d00625605800700081c003a007840a01c2e00014101c4420608500e10140d13410441b44c1030000d6a80000c00064041155559952082d040700f040d8080c01c0c0c1c2591590f141e154002600110302da4014003220300704400000a643c0c0500180358000380c10308151745180782401c0302c3d100510400304074502c41c800c40d6200100545454040e60059940036104540c2d0f280c3c5c1c49145a0741e6008107800a60a001100005009501c24003034007045078500c124182d92aa502c0c1e00a0b22513820403031589807082240c080014940015008842000e680760f14001041c0302d0300d091003444000d005044038041d900c100050700d055000060304a04440c807514107080c00e1742d014505440c5c882c8445101034001410034061040c02c0002c04020f00b09284244001c200c610901d105050702e8440a20700a400981c1c800400c0080038040d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 25387218 1250 25385968 25385977
    0x11401080c0c0304050316050310060f1215090c0e180a0b0c1c0b030d03060b03040305090303070b161b03020c040c0201180f021519030c090302120c03060a0204050102070b 75
    0x2c24054909007611800841e103402d00c60440003280440307200c3d041286013000c1c018000c4a500080c010302c500350030100c903006400320f01c0c81016454845902d169090003040c882c12100c5070102c034810f10244030b41c1e00b088004c40240e4014805142e54840204a0040c1000000403030014604090441c94005d074030b44030b04480f4018a5a984170b1380400504441d04042c603005070000c0c80600000030403d80c24000e1601c1c1455400d0707800141407505009202c0d00d54100152035120b0b0707052901a5503950500046400c500480c0303002030400c0105001c0c00b602035503601c01200001048d0340c034040c1e01d40035180501081404080c014000d03801402100301d0031305140e040744013a6a042e000110b22111008441082c3c050541010345e4101d804480b0b070000c51402074282031524660124103420311912805100075004ea004450303050503030f5500f003200b0ba940501007000041d43c001300703c100140714440743c16450300000f000e82032190181c1c00c001056491644255401c3d600180c0c01000e94a09241589540f03030700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 25388468 1250 25387218 25387237
    0xd09060212162a02010924030506010203040302030307060509070b0c010207050c041e0507020c0d1b0605131e09050708041205040602120706060915061b0b04030309061103070c0b011401080c 83
    0xa01c9404a00900c450000c0300d007d40d490b150031001215009801022070344040c15950440d08104005c1015940010986820507048240011261500d0380e44d545841802d80c0a140311a10200b0301104408041d40030f4400c0d40c1c0580151203002da0010200300c00c8031443c9030082c1042c100d40300c1d0310422142503848564011801c0c011100e042c80e0b40c000084152121000407a107134101c3d14200803980e400c00403208001c3c589400d20740d040c0801c11590004015490007040741c0902c3d0740400014a503059281c00c8002c19458208002a00707040c10000c00c0f0080c02c4a06580540e034100352104403d10590488044420340ea003c0c05120340c1d0880010b500da070201c0307001d603517840d10b9003c0400c00001c103108080302ca82180450301945498070300040c05060b40c0303450f1412490751030b034215070100d03030740020403036000340d05203400140004680340c85801401c405100d440e081c07101204100641d0341014805500c0790060500602c1682c1c1c44c88070403000c01d04124800d0000d00b142011030741e41c01e01e140103480a180d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 25389718 1250 25388468 25388477
    0x3040b0402180c090a0b040b0304150605060d02070b0609040206030c0901110303090a031e05090103090602070b0c0d060801051509040302030d1802040c0807090302060d09060212162a0201 82
    0x210300d1070145028800d0b10b400401083c005400301851601140740401010501501820720b40743c040b03407000038000100050001c58030300b050441c004101350301a20260400900300c1d6210200541c441d0025040245c04490460440d80490340a00d0302d05a140d204a41c0207202c54503554400703006d42000d03009203a0603418041c11007052815014240044c520948407100185902d0a590800070301c2403c8451190ba05644d010014142c202d9101c4100c51a0010a00380410300810700e00d005030003403062100103011460306506210741c814120000300352a0340d0310b003070500c480c64489914500301c0d44152100724400508407036201d49400d14580345940503020b401642d00b00a0741c0c03401031040c0c0c2c54190b1101400720340a440403046140c580301e00c801c1d40c41d2600c1c004850703142011002e00401c641e400301034495000803444034428a075541050380710301c0d0709c00300c1035480302d05508855a8085003510041d030303040b4602d41c03c0300206209031240864000099000e170030b56031020500d62000914294141d0402 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 25390968 1250 25389718 25389739
    0xa06020a0e04090f030201180b06041a040c020606010f02010606050d090305070209010b07020913120e040f0c02010209030c0d0305030f0907090e0c01020d02010e070302040f020405100903050c01050a0503040b0402 93
    0x1503950744958440d0074040c2420644138000d07450000d00316103446404001c10104c2d010030b040800c180c1a0f01a60090301594001000b03255442036111110315000320030392050a02c0c490901c880e030b011982c1401880281c1b00c680c0601c0c4880c0c81a0b00361201401002d000074000e01c102da1941089410445629000707040c603d08e0718035140c02080600d0801d811140422000081070411801c0564000360711011544501f414494513582c1c0003200103600c8019000c010540170407810301e580342c4d4082610341d2039100c002c00c330240c1043c401a02035004111402d20034011607443e0441400c0072050b8500b4940d0641c2da003440d50751210310882e01060040c0492804e80325603400850542083d21661031143c0352040280301022160000a01d800801250b680440e4140501c1c912141e00c006148015254100c801040d0892440b2120000303006550069610800c088000e0340207940214006003607901500940f6020203030040195a24030652807080000fa20400014001c40c588280d0039070490320040805108 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 25392218 1250 25390968 25390997
    0x50d1509050114070f050405060301150324031b03050d0c0602070f03120b030705150706150608091b01020d050c0307020d030302040807061b060203061203030106030203040c0e06030a06020a 83
    0xc49080315840c0724014003e900b480005a000315000308070624a142481c0340c281010007190560106200e00b0500b19881c16400f4441c5d03010b03030000303240002c0803c200d1520b0103070000651694070441c84103031942d20016403152241e0b80d005031b9100603280c1050041c1440301c07100c041203445205c0e0351010b803052a421b0001600103408504140380c0b0301d029076601c20b2240710a01c260811a403400c040c00e4800d40c810307141000552240e584500281e94204c1402da150025810034038050501d218190300c812039071460124406401009250194140c6021261302d00707102c1c090400c5528001082e1809030748040b50040f10030380300d0002407640391180801d0313078208400c0e940030500b00891940b040300440d402140c1409004400c0021000038a854500103116846510440d07002002e80c06e006020780c1d40010001d04191038400b410201c503820751003141e55969544200800039042907401322088500340c200002c500c0301120141e03004080c01000780c04640040c1e07030341c08001d6200200b600c0902c114400c00545 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 25393468 1250 25392218 25392221
    0x1809090a02012006040501050615070209040b10080102030906011e03030e091b03070309030315030b010b0d060302120604060b0f060a030507020c040903120b010201020a170402010203040b0706200301050d15090501 93
    0x5d40c032400000c42d0606110081185019900e403808811031018030075180566106200f03250010b4200305201c03200c0d100e00d010598185115044400740707600000500c02040c03400a8502c2c101c03442c210b90601d095509115501c64131a9910000e0300007105d04c1c206004038548031464942180c0350304800c2060070340703c0000c5685504211800d4001c40e945942140506800d80136003840c0d0882808503014150456481145070070042c0903c1041c44000b054900c1c03410407070fa0200d009107800034180e01d007028600100c280d4400049034100c840a003001d1022a003802e03d00c80d00348250500421050400003034440c02c4004200050030342d002c500c03880f202c590481e12980300d207080701c80c0259200c8550407140c0c0700380407d50300840926411a80b041003944113003070f4408180058050603030036140080d02e0303500040780395009035040070b605800c000803118100030890f07011550030550480c0c68407200814a4064030940424859503420030b030500c0d000030020303800000ea40950518120000780c51800390322000d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 25394718 1250 25393468 25393471
    0xb01030f0905061602030a1b02060c0313060e041a09060307150e0111061012050f0607050301030b070306080c010e190f060207080706020705090a020d090501021809090a02012006 78
    0xc0c2c41d5084041030150096152040c00d0841c3c0041c0000d61804020500c0102a001040c0c0c0542e050b1981c04801d000310740c1c0e1402100c580060720310860ba2904010010301c1c1e06150184950f00208034803042d42e054504107800342d01c0c0e0302010700902c002040b21032814401e65040c020001c030344c076002d04080411912090050884141c00c2c640c0e91003182410100098180b14802c0b003602d0080d4412410020407600ca910150160f500d030f50b00d0303005403514601d840d91034561001c130908042d02803141001070b21030b0302070051812079000300750544003511050b1041c0c0407502c280c0070f81760700c0303402072440c003c80f55000c4c0142000100c800341c40400210fa00032110240c860868010140403d00007004001d013a904000800241c043c503000f502c2d05a00d130a10113952503d40d03200b942d00518101b000204c680000e035050700c014240082090145d00c00511700607000b54000f244482900d00b146054680e941809400c5500c06d0803e00001c00c1d642656800555440308001501c07100140e02c1c0b2821041100c00348800c0c0d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 25395968 1250 25394718 25394723
    0x40e01050a0f0f021303020d02060f0a020d0f0e0906044206170103030f0306050303030a09120e0105040308070c0b0d06090501120206071106040f030305120109020310090b01030f09 79
    0x5000c410b10341c0c00b0415201c10914001a00d401071104100401e28185180126503048881180410240c400b14040c6d0041180d4550040070100f10700d2003c98010135041c114140c103690341040150041c0c1e081e9078000005148a810026180001c0c4440c101680300c000da840f00d0082c54021928606151010340c020860042c2c494884130071011000240c0e600c00401800d4581400c03020100c0045042038004014030015081040503100150020300992240e00a03280250980b903480c0751020300c3c10013520511108a078480084121528024428542ca01013000142e4949280c9459038981c0509900116025200301c460600005400001c00c0d0091a00744482503012841034604030580c81242c00503840818a000118a100d0040c0d40308811252602e40c8034801084803c5044041407550248d600a90001d0205510100501d41c03c40040d00e41e04150901c00001390381c854644505a0000b40c0701d560710880d2408061118083c2c0d03801107080618103140020f4816124030107002a00c2850609 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 25397218 1250 25395968 25395971
    0x40801020d1406090105010516081204030c0b010f0b0f070204181407060305010302060f180306010914090a03020a0f080702040f020c0f0d0207050d03020c040504050c01020d020f03030c09040e01050a 87
    0x3581103038403031030600d02c3d40400e0840c0c81c00302c43d625190000c0c00500c03a00b10590b0000c1401030b1004104030149050751040705400b0300780140d40c0340501c1c01400c90780740786905840d08a5404000100114040703000c0741a2601d0f4030206007000d010070001c0003141c0040c2012603016840d0b00008080d00c401c215100d040074040d10242d001d8a40201c103c0c4d0410344660009400c01d0b040c50014409a02c0d0300040390000080d00c070070103030741e05c0b040851080b101560006495041c05000000940c41841e03070801c85d08103400c04481100e5448900b500d03603641d0514207006000d84c220042c10004a40d40d01c00c0e0041c00c9001d11031007864208194009000c54840602d01c4205544c0481c15155809003008060400984940141181e61200001035582c1c191403241503c02c451901149040610034803c44110f03580c042c009000c46e080520f4000c0d1a21a082c44903401842007800042469200140c078440c000340c1100270314950b44400702c0c80d81c000d82c4200c0070729400584680c1c0d107100040003441540c2c420401d0000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 25398468 1250 25397218 25397231
    0x7061107020118030206040b07060e06010e07110601030b0c031806010902040e0108030901120e010603050f0c01021203040b040605250801050f0f09010e040f12021f0e0303060405070203040801020d 86
    0x50900010740d28500d0980d84548014130050302d404007100d09940d11901e040d51580001c2c50038001415112000b11100d0194900004041c450f02101a00403034250700d4090342c0301c4003043c03082d50701c1c6800d200c050003840b0b05002141c07403c160306006540103280c04040c14101c2e01d58401c0300d498400c00f079001c2c8000c00d50018040295110b201d04103405041500003039444c010929000a098064042c0c4480d21303a42d03580740c01e5000000960143c0015603100041c0e800340390b10400d449440f04071040302e0b540940110344038621a6140b41c1c04803881281c0c401d21034011500c45072546801420010f01c00d250f24a0010a1007410f0003800c6e0700e094100d52103981b0100f40d076041c0424440c0403040c0d9400640200c4d02c110301002c15a41c0c0d244501c2c19070b40d003020181c0c0d150781c07079040c2203041000411303014000580540e40c554a2540c0495003009400d04400d0f4420540c25004089046510b11062200c01d41c0040c000300c2c1c0d20f8500344e0440798000009104803402e02d42c03200800d600720b074081000c003140c5030b55454 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 25399718 1250 25398468 25398473
    0xb040303120b0609040f020405150405040b030607020a060b030a081603140f0412020a030803040f050609060f0114030708030f040602010506180c1e04060f2705010c02040207061107 79
    0x103420105075190180030300c0340381c1c003040100722507006036a0000e104985682d00b000700300402d0b60680f00141300041a14141d80040c500a418070352181c007445000314100701140341d140c00c0000f040c5e4091100c6500070007109215485990060541c200d8031981805204035610200d40c00102a000da4900c11079001c001130160303d4040c1645040400380d210b008002c0c841149007a00704800d440455044480300b484015951001030300000d01030700000d00c8110044140014030241c004011440e038407600445075562611280b66540365400c59114039070710f5070f290051085a010088406400c0406070444030819140c1e1001402c5070851104e40382e03841408a01000f595609000d0142c0043d0280c0c1c0481e0034000c50140c2205d0240000c1c90918805c80000e880c180140c0300313408400c5050090780e0165141ca032900f0009007518000035105000801c0c0c2c1c1e0030b980c000c600100820071038141550401d0485450000103641d400030304c507001e90b031096090100002003240388c0940014001d000991395541d03807452 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 25400968 1250 25399718 25399727
    0x606090506090901140c130f0902070506090105060604031502091210110403080403060209130603030807080f0603060609091f0c20060604020d0603080a0e1c0809040507020102130b040303 82
    0x1410003540d030781450300903102c200380540051b822001c03046206544403001c4600c0174400d030342c99000c01d10008551100191030503440e03000d4200580f00b034066484503150405868207859042d100b040c0e00c1180ac0104000050b400003041c0c6045a5110b409070800001e84002990003a035841051040d800407880c2c20300c0010180f00d44c9100c084881d030464101821178480c1758540c001d50000038038980d40040e0310642c6594440c400040c1c1c56040c07006004654981c07400511240090b500a00400e500e100070400d00c100c2491402d100e444040c0040900c0d039038210420450510162014075280294440c103000131500060800843c040c5c590003050104c000302c0e00820302c841100c44c40d1806508017480c05501074000c00d18070f411082c1140c01685459100d04a10004d20f0240e00090840400042c0c80d171001c0e82019044000d01c404954100640703000c40014030010100e080b00a0070f03010204868002441d02c0e92000360091070510006003401d07000740410b44004006c0d08850400c4001090402c10198032 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 25402218 1250 25400968 25400971
    0x30106060c03050304120e030a14060106080402010f0c0c0504150503060f040b13150501030b0a0b031603020402030a15031a061c020907110d03020405040b0301060b0f0313060609050609 81
    0x11480c04090071106034400400350301000d000100b85402000149080d00d00ca448025000c0394000c0513036803840041d02d010b008114205940b120640200d100004519000305462403240350103855880d10b0180d0f410381201d031403801c48070441d0000e8525202094640b036034030030ba40580101480c102c40007420001010f01d0800000c01807100c654030401000001500310703102a8000981d01051400025645009100030700804015042185040000000e1040c10728100b40282c0750241c040003c1c00607003040c180c6441407400d074440006201d480801c0181860780c0216444410814009031041004000081000b00d40d4419201c031031440342d1550035602c0b500100c5412030400c840020031a5106000805925000b0b48040c4c0300d500c084000510f840d0203009a40702514482c0300782c1c1c100c8842c095001d0001e4109000d514021890310100700c5960030148100c03800e036090035480c0b50901e10303004030241c000e0344010040c0012030021034503000050700c0c0c4d000e4000a000304403070216491502c0400d00020600 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 25403468 1250 25402218 25402229
    0x15030c08360f0f0f061b03100306050705030105010809070608150102160801020702180402100c0201022d070b071a0c0d0203040302070302040f14010303030f151403070b190e0a18050402030106 84
    0xa81c01d2086d000350a07800c840700f864140d5444c1ea2696604108500d03428015070000c0c1c8400c2c10081000708041d81302c001503069520036207840c40d064880d080c02c141c1da4210b80c00b0b00703030208244801280ca0031505030191300364844140304035080c6454552102410340c80551003040b03169000300e000811440e00b45505090092103c0700c060941c03609400188035400c20194407000d01058000040569100f0300034a400070800c01011490101180f140302254098804000c4d01400340900c0881d2030b81080d070844400c44c1c3c010342d8000c180c0307265030f07400c01510b11701800c04035502d5401c000402012060f40082c500c1133010390054906503255005000036980d609500b096003a14111280f240404003203000c0341520340601c0d002130809236000d0540002c082c0150701d10310030312050100140c415a0704242c03813220a02501a10202c99032404016294000c00f0842014645940c4d001d840f40ca10441c405002018000d0403101d107580e17240c20301d4070f00703402c5c3d84400c0d001281c0314020001941000d0081100516 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 25404718 1250 25403468 25403473
    0xe010c050c0c010305130b0f0412020307020109030b1003140106080d0e0d0308040c05060f04051e181306020c160614070f0203070306050115030c08360f0f0f 69
    0x115030003a010340310603400d00c2d407905055460b008903203107126200c80012420b46c4001c000300c0303a040c114460039840b482210100c846030f0300961040c3d81c65102100ba10700b4254180c444182c0c460031980e801038801d000070001c1d003003032020050020101d4000c0803500300449440000186171400c0252090402e074000d2608018082e03940c00820058984080000701ca603050314104141d0740301d1340341071550110aa4421540a0008100714040600c0d6800520403503030103e0300c000c034031a0420115450503000580e500d42c03089918516400500c10203107040c0d03002e19a9020041d03645541ea80e10012a00702c1e50f001c6000364040820384811000c02d0300c480c0c1c0502031904000c81c00a04205094074244201c0f04002c0c6280c00560140c81152005c001c6440a941e2182e0240482e603152003180e080b206144c54240002402c041e084c800707007801a2182c9014103035421150002d1440000d0340204c2100e07503d0642403403105245c01c130007549020f020903c40f10440d4001b034402c005085031894a2304d000b8072000d24094 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 25405968 1250 25404718 25404727
    0xb1009030b0c3105061c0506040e06011502100c03060e0a1a01030c0302040e0f0f0f01050a0302010309030c0b011701140f0402040b0109030c03080301090e0d020a03180f090e010c05 79
    0x19044048110041c01c149000009a8800d50f9018000c880340c0e078403c0350007120225802e03069442000455a02d44000d400402c801d07503d600410040c2c68514228000c1d03034104000521a07400d00c0d00c01c07016400e4150040301e41d1170a45480d404210391001141c0c00000340c2c0e0f170368107002d0341d0709500300590800c013054070900c40c0010328049602e080081500481c14035641e802d024038618002e80546006140054030b002c890b2074810400311114100b01e401088880803540010400f10302d1440703440c10307a900a813181c1c880c1403e507801034006081010080c2c3c244084030b18400e0006240680c0d65001e42043c10540024810300c03c1e0302d600f035a48410b030740c0240b01c900804010900d40d413884500d0303201d82c0480740805c081000e0001a5100c0481e071f013014181713400f100340100601110b440194103d80d540182041804804d50003e621460b030540c075840160005030450000c40c5c801e0040d1809003110300d9400540954544040032040345c0d40d4801194035440712402090700c64203210742c030546645030070210302c0d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 25407218 1250 25405968 25405987
    0xb1201050906010e06130212010519060503010506070305040e070f030f0e060402090606040f09020405010f0503040305070f02060c0717060a090201050301063f060f0f0b0903010b1009030b0c 83
    0x489105011310070340f0401e000c00054060340d40010749640d00003100400c545ea500c442c5030004140e1801d005807406404c13605e1059030314140a0360702504487d02c1d561401c0c11a401c200800c10707268411507090307080020500c07000c510307001d0000c5024040c201680f0b41401c82c0482540c082d050f0350440c0710980410307160010744201100007007500350344181d04445c44940c13565040001140c80c00745e41c111000c2030307035600340c0842c500603240e0040007034501c01d8a036500320780781d10f240c1110580b01c00c0724010001041031150701300003003d0105020382540300500f0380e070a00044072205071420400e07030b2102000000f02200b00c8210308080c07111a800205c480b405001142981c1c00103441440107100e04010421307100c031200075490884d0001440305c03006c00e002d9a81316501c40083c40300d100c624000080344a2400000007aa0038400c074503d0116203450f500b188803c0c0c6004030540264200f2034103250507540340d01c0340159641e9440071010451465884078000d1500f1401c00030010310000b8281c1001c1071007041030a03213 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 25408468 1250 25407218 25407223
    0x20d020607110a0201030513050a0506090c0303040f0e040203010603060213050a0b0406020304060516060507080105010f110601090e0f0303010b030f07050702030307060c1b030201020a030e01061409070903080403060b12010509 99
    0x10f0007602030070003250640f100c4241040440421101420300d000d0025000c3c10081e010903803c0c0941e1000c000c451b840042503040603280c0c072903031081c0545000414001c210000d19030001c00c0e030250005000080c1c0d10f0703403038a61500340d90055035010341241d2010001e010b00c0c40c1c01c0f448503001d40121404941414240400a0343d00d00c02e5010316400c1c000b000c03501270045507a05480c11741499005a050000742000840a000014203009090200c0c5080528202451007118125901542c840042c000f0364640b41c6054000d0003200d03c0c2c2c09440c0140700e0188401e503c00c0000718001c200035080c03980e481c40d004605030b01c1540e02905041c2000b1041080001581d0000192800c59800c03440004d5076200e02030058a4401c5043d4403031072010311990441084c0f54065000e0155002e16407401c0c4007500ca0741ea4054200c4406000f0114201407103614080d07282042100d56500c15841c0c02c101410a072241c80302083ea8220760b10850384681c44005c0707100e02c2d0404094450502c2c1000e0020b200d281011002d81c0d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 25409718 1250 25408468 25408483
    0xf0e0901030618140705040b041407050a020703080c06040512030f0a0f0b091905060301202208030c1204031a0408160602040f0519030b060103020904020a020d02060711 74
    0x3401207803601540c00f080340060251031000b07a4402c609800e0484005903058680b500e0b480782d144030b185400030404c10350800d8001c3c481c0040c85074039181000e03aa500002c0d103141d00128520000c42c8220400071001030f07540c0e0000c00e406c01004004110520300f80c0b418030702e403290482d03012105443c18014803903094101346030260419101000807480c1205080c80c08004c1c4403085505500111072824400c010000000e01d03109000031113070a10007590344a081c10309a4002025520b003d0074440c0c1d600003048c503d1400742000805040f6402c40500703070005c901c3c6462402e500003c900d50000141c0340800c04041000c91840c1d80d0441c4d005060a2954036949490b0001e00c241307842518100002034200180401100d519841e0b05042c4101c006850422034020f40050150303d00b0220504400301d43c43c40c043d0300c3c42151004408004c401a420f40d6298200102c010741550305160302845000810795940c0054a5903c41e01e0b401802254007505000b880e05e800a403144051060030040111070103008980385 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 25410968 1250 25409718 25409723
    0x509090f030a0e030c0a12020a1a070f080c010c02070f06021c120b0411070507090603120c0507050a09020a080a0b0a05040e071706180d0206151f0905010f0e090103 72
    0x141500c40041c0f0100381448008109158024441c1001089040da0050181c640600035958002e0064603030715004484941d0028003000031405002941c0040e80a03c0c0c0c000045208804007414a80740d14401403d644284801101582215406000d40e90400d00108000e020f544010607a4a41e03041c0c6071000c0300d0b0660340000800039461080c00d5011400d80100c81184405082000a003e83d003050b40382d41c2d00700d01d000311414040d1000c0000c9002d01e1340030b0041540d070040c1010f4950300d40c42000340c1e0322074034140c01181c041c003071018001100e41d15000714100505d8404400f50340c8407900c50f4018951040105484425031400084600385c0c0c44100c00c0c8000d0725001e580024510f011410224540a03c80d80098004c42d8042c0f12145540800329280b40034200413041d06139890850345040e80c4450b0004090310040e40b0000010f0a022a40842c1c40e210150281c0342e444500c4045400e21701c0700c0175580c080401700308030b80c0d010400303544d000540c0c803c82021850041c5440407590005540040188000b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 25412218 1250 25410968 25410977
    0x1401050306041e0f0b1e040b0d12080f070c051e031e04061b0f0204050c0d090b07020705010f0210020a030b030a030c05010501060c150e0c06130509090f030a 69
    0x154090720b643d800312500080254520030403500480810002e041c0015610b8460341c10b10811345400e09100c0c5800309010b2002c80c80120700341005091000410400240d2a4015142501c0e1000b14083c03140200000b0392a94a4000c03e00e04a541841c4119011300391004000c580c08100000c01d001154201440308607603c0880c0004910000b0740c90f41c01000d079600010007400c4451551810b007480200111003160703c0380c0c00e2050b1046400081f618581202900000c8031008440041c40c040d8001d6512030351400c102d50811305820801c1c0d04a85c1039000c01c0340c408a0120601003002d030100b10820040000346812081d01c060144020346680c2282c0720a2066600803441021090094010405110000e0202c440c0c0e00c40310b08000b00107040d1a2000d4899518050003c01c003288122240c03111660800b070341031000418488004014070040084190602407403030441d8413030703459070014088041346480541c6818100000c000007444050b0060b5400d6001c0010441c6240021080c0c0d0b0469103207052 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 25413468 1250 25412218 25412221
    0x1b0b07060f020405100801030203010c090b04090207051002271203180a0e0702150901050c0418060e010902070b06060304020a0510020304180c031d0601140f090705030f09030414010503 81
    0x7080800b81c0500d4001d03070f82c0030b20304010101e6000c2e070000d100c50490340201c0080c4003444212200b52440807650281c20304140003003001b80007070902038000f06401031240c3c0850700c4084d900c84140b0101c1e0040e40012200d0034502000c1010b00c007c107180c141c080780341102e01d40020700741d0700040c41d81d038405d04c21078408110b481c51000c00705035240d54002004004036034044035a1f00e04448020f440300d407a03030782140103140b80b44d01140c21003405202e41c9120782ea00c0d048240c80c080c1000170300000c080e41c0011401d00c9940f03604006c030359021305084849c028030210318056221802d03454507d54600000344802d015840078010000580d0300c04001101f01d481c10b440c54505080c0388401242140704581104001d606850310400c0340b40f1301035104106054040d9800c000034140708000c07400712070140c085032410361700510041c881c62880340c590703c0341050000c044502d40ea5180010520b81001100c006010500c040108500041e01c01b6a0319403107001e050107107141904100d68860760403d40310b4072a040110120 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 25414718 1250 25413468 25413491
    0x601060e040603060903050c07090b010504030b190e030904060b1305150c010905100c0c02012016030803040b06060309030a05030c0d09050109020109090903120b04090b010603091b0b0706 82
    0x10b000d8406550410028424100c0600b000b5001343d11401c40720303003140f091060005414842c2e01c9881b14044050b900d082c41c0c00c0c55900c50960344071340949408a200001c803802882c0015030300c116043d21034460f0295803510b02840030041116040d0b4041a8842030820102020001d032000b401c0541320100ca5441305000302c1260004280521083d07031040b9864444094203100000440045c2030841b200180007c2c8484d01c411548003400a500a001c54562100c205400040038510079504a03004101d88519040b2910b200c001140c070380c0241c42c501d40004c2400244555500d141c3c3c2d0001d400e80d159803460506115042d9030f0f10034404c0b031030100f001c0030010850024007081203c01c1c10519031001e12036005181040350003003454180881c04036441c0303040001d0305030450052040e0507405494941126114200402c0648050b9441e5640907965426080001d0b45540b078103406004a0740d00040c03111040d261120580e01c01400701445900680d0307040180000320300450303154a038451004610113075403d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 25415968 1250 25414718 25414721
    0x5060703020a05100501030507050a1202010c05010e0304030f150c14090a0f080606100e0109030f020d020d1a06010905060304060b0a090608030901020c0f0102060610050f030a0203190e0601060e04 86
    0x10b0600038414080c4d803141045205198000318180c0c3e0003201612204d540d07070300801045202a115841440c0c5080c401c40300598002d0781580c204a0080d00040742c40394480074914290b50150700304441a20201c030344003083c0069440b8450300001d941c401045030111050001e400c03074500041207144240b001842c8107464440c030404c40000c040c03400da250091a10b80c10300f90740b02c0340102c850350f01a000d10b03016241c109204020f4032000802c1a1a8080000d00315200c41502c462201c00a0b0380115032158170000503185c01c040000074501451000200082d0103c044041c84ca006e08020304005921100740104e5494030210b8ad0482e80c080300000391002c100020606000560740010603251030072000140b0140040f0083c94414000d07420b8898405150040104000b60641150300580c0103400103403150070403000c206201585400c0090900d44803109004180d0301c00c41d03031f083c1510740110a01030001c2c0e200501d0440d01000ca0000e10070104c10b8052142d03034500503c1010104132a00c004a041c54075039 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 25417218 1250 25415968 25415983
    0xc0b0a051c06080114060609040c03060b0304050313170d110109020a060509150325052811010e06060906010e040501090c110d0203070b18010c020a030915090506070302 74
    0x28051100e00003007010441070060a082c803c50f5015400c00d1a204080781c2c40006651081900500150600c1d00c1402800003d102019002c0d051503070340d12f00413a130001c226003e0340c0b03e02d00c0b41008555074003e00070115154200c0b40e216041d4188142c1030020718040104074512615203031300c0d0403480c03028036403007050140030820006500803840201c040703802b0394490000c00149005540014000b05071214010b280c0c4811a000c010881101074602d03003a8520b0a18034100c10600d2402e141170a80320300440e40e241048007401503480e1440040103044c03542054a0801410700340303000b0081c40d0201c0145a44911004250360f00c6828031030000b5116030b0092403400c119403400740081140303684512101c00205001c1000c00003285640a40c132a104030300040e000b1200784240d000d90704140240c4d403180031520002c0c02064680d07a4403172032865902000d200b031900721075095009020001d55400c02414078140d54010703485409400800a85203a04011800304070781d0259102c03a6104100d04080782410318 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 25418468 1250 25417218 25417237
    0x2100506010e060d09060b010c080f07020402040509010b03070305010605070305091002070906031407090c14091305040302030d0f0b01090e0c07050d02060403030b0d020d03030203100810021309090c0b0a05 90
    0x842c441041380c0e9594024041244202810000a9021b4005485250038943e004103c09030410604501c0d00741a03020380160752014001504058803030001500100c400d8010440e40800401000240c0b503060241c2e60041015040c15441c017103080e10014050300c190b458a0740101c03018016002458402c01555000b400410020800b50783c90b403030400e60030700f4098401403651082e41c001007082d45d0144a0170300d9035500b64981c00c0b0804a1071445c203d80350418134565900c18a05a5040500e880310b001d10380c40745d442303580919510702c40f003c000700895815401c00c3c01c11500c0c212122419903001070a66041d1010208000c0342d0303942c0d07000960007510450740d006000e4040c92075039410043d00054400d00942c403130f840a100802c100c10600c00710700e15407030020750f001c001c84607100c010034003941c0115003106502480d103045a84400c105032611100690001c25590b0024860b503000760000d0b1004082c103403d01c418001c44142c1d403504107000e8024001c034461001c001034941d0004d4018800c0b183c10a5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 25419718 1250 25418468 25418479
    0xa12020f0a02010b032e090804031118041e080d020409060f08030708030a09050f0604080406030b03030309060106141201030503030601080a200d02040308030a0e0d0f02100506010e 79
    0x500300c01081016003007840500095820014040b40c2d030320300442c0c401c080c00c80d0408103603442501c01c0c00c211000030b10425a080344507500c04190010542c0c50b0001d001650241c2d8032050000a40c00a2024841d20055502003078000141070100141c60000049140310036242c0b44041081c45080041d014480c00c56041c003820720014001443e0801500050100c40c074940e40d49404640d00c0c00c3d002d03144d120788500100072410400000d4000510780d072102c2091405001212040d134098904245421410355054952080c04039040202e16458007581c5100b5606a020b14154100107000c00c2d80c440307060140c0c2c400d001da8120340c1c0030700a506205540706c200e2034003112030700d5580d2401e025407a075000b6a400e5000401050020b02d01c040c0070300540001c0b0340c40b00000c1c0c181c0c0d1f61003a400c03505500302520107120990200400408201020040d43c0103002e00c001c0065030803811000e40d40b030702d011154010180300700403c10300c00190700400e00b40d01980e80300c41c01044030b07903899004803462082d5024859001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 25420968 1250 25419718 25419727
    0x315080601091b0c030c11060309010e010f060803070b0a090218040611070506040308060406090e010615140414060403020a14120c030d120e010216030306060903030e060a1202 77
    0x80012018101c40c0d608100300202e0402c0d030300ba03a1290032000b20340b20110341e80b034100c2c500280c803d00581c004940540d4941142580b0040018801e52054407030003080d079121903150b00038000a10034460707034145100f0104801490000d105031a4000c226000d0100189840020701610311074009104165004100b00741083c41400c051760a600705a5081c0c81140c6480200d0041c40d15500445814a802030b004100590b41d9a40c12a100400104030a410a40350700001580c03450b180998844980ca0f80000300c1c0803403c20382007441c1078418410f09810000382844800240c82041700302d40a8440807101c91b134a08840030f0100382d440c81035902c001e400010005d00020440188102d042418808841040c4034481e03841c8035950303d218004803c5e0341341e001400300812850141402950a07a03181e00045400030000d00e2107400ca13001000c800c113041910b046c140c0c04042d40351061002911090409410850958034010800307200e0200d0a4021800040c01c1c000e603c0c041c50980c40709045100096589 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 25422218 1250 25420968 25420979
    0x90b0319140607030612021c0606080705031204141e03030403080904050a05160e010c0209130209010608130f0f050a030905131103070305072610050409050a02100315 73
    0x164181a010078980a008080341000c0d110303000313030b07400c0f00c00718031850a0b02e0031a50200070f0340d00948211442035200301080040015042c0c001c1d040208094070107450b0300c52a12050500380b01141d4403030041c1000c2000b0901110020788640386403040d050302c180684000100362049003a070701c0b4158075414400032070000b0400440c0001441d0090b02600d082c80b8549a503c1840190381d005c0e100b5520343c1b4950418522903c0c86880d0002c4060790502d811242c40c107880c2c0200700180750503525050000250f0380300900354141039100c1801806c2500d0400450314010200031030010840303100801610782c40c8c4078941030100880311201926004011758100751003505d4050442c0209200e8a4054002c00003a40b90418a0b441812140071080d48054513680e0f43e00000c80007048000d02030824040002e42e507403101400c84240d110308095582803446503040070803a2441c0c84005a020500c203a040000381300c005440401d400d8030303da0b4185d400c0400c0050400d002d80c00b07042c0112a0100c2111880f00c0000c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 25423468 1250 25422218 25422233
    0x611040b1207030c0e030a02042004030606030302120a0813030c06020307020106031103010605062d0a030e0709180f150f020702041a0108041106160602180316090b0319 74
    0x342c045840401c242a0400b0302a02ea4800c2e9014040d031542198100d070025003450381000e6000172890741c03a00350b2030000c1001c20802e5003080e013096842179600d120138410590100300c40e105414150300c119082150142004004a600401950101c070348828440d04040c0584020094140d009a05645920b05450024002c02c800d20060b160f01421808034089401c06100790816030720050401880e10100a410040e10101e1862402c580e140c10302c45822100c10103000740c0007000d0380d0354005c0b415080068142d8a0008907070000f0740b54502c0c0070031070041d503100c6030314881080382d020101c50740d04090b50802d0403050041004d8001d0150074404440c0c1170242c954014400144200c804004040444544800d035011040c607060200700281c0200b00458540c200a0f2441c000050403070f49041c07100010099042c0450604890013a0040360a100c0041a244180d6802500b80c00038002441c0807444400110194450070b03911640c2e4510115071520140b00c143c01c0034400317003020a8950047d103410345 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 25424718 1250 25423468 25423471
    0x11040b07150501060c0507060906050d0e1e0601061404060905040b0301060e13140d0f0c0501020405130203010302100e1c060e030f120c031b0f070c030b0105010e0d0c030611040b12 79
    0x11418090004042002c270301840345242500d1469890600704401c00301c0b810024200200c661001c0c3c850140c0c0740c8545003081800c0c141a60303000b070182c07246503d417050140040c4940300c0c1500418006200600c070041d4045103031402c4a00440c0c002c900f02044a001c6030040c80301d80c11415100c260714042040203c0000c008141c0e0f5032050100301141c980c0e0716038a1343c031208102103010005121180c2150824491508010302501400005142a50340d1002450300800ea01d4041c1003140c0100040055141c550007518540146080043c04441c0da00c1c009076421168400311000003a040e0b840780e062107026885880c0d070030104411240e543c0c0f81040402d1458100008003490581d040001803e05621030042c0e07406514403a11542000c50701c07500d46007a0390072000311903540c60130501001c008a60704050420003940180c0340d41e001541000c0006010600c103001250040b140c440c1c0780000913200460301012030342c0141c0001110138071040618480d10071540600040c8001080d800704d458810742015 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 25425968 1250 25424718 25424723
    0x9090a0605010e06120105090903040801051302011b02030706032d020d060510090501030518060414070906030803011707030b09060601020106050a050105030a0f020906040e0405010f11040b07150501060c 89
    0x304183c460708001c00459125054400403600540401040141020001a908000c201c025641025102c80c0c18900b141e404550300502001c002001708113650700b0209118803403c903414558022403032078010958030845407164804165940c201400070003048071850b4058103010780804080e020300f6480b034019405c640c031562002407030074038001058034010003d0a440780701620f0300c818880c680801075000303010085c003004d0103080a00e860300c4044c10602c0b009204521402c6a0522050000146031170300e043d640001130964035100b030034004203e080095904452008440403203007203240e0000b900b808110b52001300b1005c003c1f02031140340440880e003544201002e9008205491752141004811185441200e0106804002080c00307000b26400c0342e541642d404001510740003241c00030403419030281d0b0000c121580c124007844100202806144c038001002082030201045c2a15482003078419485948080c99000400d882084802d0354024407414040408106541c2d4400b4080c01c9ca1112480c01c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 25427218 1250 25425968 25425977
    0x9010503030c191a0127050108030d020f09150301090e0a020f04200309070f080601030206040e07030f0615020606010c08090d02010e10030b010807020705060d1109090a060501 77
    0x1149a04000050701e110190210003000340d80c01200307010701c50665092058036048440c0301507110b80c181e13446000d4001c0058481002000840300c411718404558040784402607401d101c01000602e90000544640b400884001a0b43d281c110a10f15413034403c001c400c2e5000580c10101c13140b481d4a4002450490760549018071444080f04403072a108c00c50040025440030300980c4061040c24140d00c68000600d41807114024003c0100810b2100d800c115190069944518000e00003d800d8503500740040c05680010411541142d00084490040340200401d8010000001d005c0314032982064041c00c5001d0010000607840d00d48004a0800f100d40001c054441d40c00880c246502c51212030340c4403a0081d69043c20000394004214015100c824140d04002c410500300307095170f545000041213111140c5000909000c548000340107440020610020754000340001c200c030707444000171150100c95034040040c41e103022100040503802034030382440e005010034042000e4401135030b00c01416200241c07a0b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 25428468 1250 25427218 25427221
    0xf0b0d0e070611150105060f0c010209152214060703230702040b030309090103060c02012003040c050a08100f0906230c040815060409021017010e071707030204121109 73
    0x6130903c03100c07003889825040a4104894000c0154600c05090070001702c6002504d05401c5d0780c0054015120030111040c1000001114103032900c88500390b0400c02030298140c000c0c03501c2d000c040c0c280301078100c20f101c2c016100000c0d050100761166600e01c504c5280d0007140134154480071400411900007142c102c7c0070300c4c07900804c1c0745940f4000041c0c1d0b02d1a00024070034400f9a007545d4412000c0c6ca0f10301010004d540d250b002210280c185154589c3c42c40c91200301d901d481c0d14190600000c1c465440c2c2c04a40603da5554090005090100b8101008284480007007266541c0540b42c00c000c1001d03c030050320382c40c6850707620690307a1015221821602a03c001c0100b86417619032101c2c1c07051041c0e202d0b651160303200003d00e003030f0180c2d2084816070082004000081c0940c03070386c011981c10760070b0301c15000006284011490902c101c03d50748034017400c5200084a050703c0d00110180a0000181c0610030040c0000005011140300340c04580c05003001411803d16072071249880078030450700044481c494440340e0f0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 25429718 1250 25428468 25428493
    0x71101150506090103090809040c080a0f0204030f06051015050711120318030a0209181506010516050a060c0906120c17100503070b09030d0305010f0b0d0e070611 71
    0x200380c4420340d079000704018500811040150f00400303d000040310122010301c104099a501c0b031207002c0c0055042e440d50403140c80c00e01c00300300444c0c07219011185103920510040c40802c01e0400d07881e0005a100900040c9522042d9440090200c0d940c00540341043c0720311440311883d03025002d0400385108401100c182050b40c01001900180340c4040720301c581c000c1c0031603006540407203590203410002900f83e600c41082d50700429800b20088918809106010f143c66005a9041082044441d140c0300408940d05004000800d07921460044415069020008006000b0b0a2010080e100d0740154200440e40402c4c41c054003000d0103115103030100d0808400d10a00180303501581c0d5410781c040d951955030000707a540701000d030600a0f018a112140d00710020a00743c400308030600c082c04210354803d0300d4043c1e9008161610621009110070507040800400c5100e541c2c10817401521b9140c07010b2900c0c2e03070340105044c00600c0e01e007489082c244940700d80080d03000e421414440410b51000d00381c880340b03200300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 25430968 1250 25429718 25429751
    0x1406090607021207080c030406020a020a06020604020105030402060a0509090a0501050a08030301030c0b03100803040305060f0c13060807050c0a0b0f0f0403080a15030203030d050709050a06020604060506030a0209071101 96
    0x201d40d504096000f403200f10006101640c0180340492160300c0050a00000400c8285141c0040d004580540d0100d0184419071034264203640040640380b0040c4501d26181e0300081440c0070140000b0701410000c208106200c1c010f10545140f040c02800201d038900e011803841c405481c080c49058001c1582c40d2011688510100c2164142c07134101d031104030900e241450689650f8001000301d004405600404210a00107000800007540904001e1119003440111440d00c1c650241a1880104d0100f006440c1000c00e1200703901101c6203414601480e5841003030954807840359020030070403400b80c001170504120040c7c03500d03405180e0003110a0400d6882533414017580100340d41c080d01040b40300000400b00701c5160402d0240d21101581016466520380c0480d01d1a080205d00810301d40d00c0e1001c2100c2c25a125400b20000c02040b5114070044e840c0c0a0301031740f07512016001403e40340c0c840000640940f13080040040c0258083c00348400d500d4107501c02440303074400400c1031b0499404e04001d051a150603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 25432218 1250 25430968 25430971
    0x601020309031906090b0702031c05010810050405010f180501110a050d0b0303040306060305150a0c05041a04030203120a02010c030207020f0d020102070e160201060512030327010914060906 83
    0x42d004001c420000c3c61408401000100201c0b2865140c0103a90001000e000321030303000340e0a5800941e1034070700e05804010114600c0000348825854040100001030000402d242c103003006200c002041e44860900c2c50161400d000300c00c50b501d0070181e10103003194180c0f1200300200e004200820a142001c6088106880303240403200000b4004d0044039141c2d58075a201b82d81d4403a000341264540b541e40d42e40d11080d101e5550042c0d50540101c0e16003400e40c558403582d02e0b031120804008010003410918050003d0046000700c255907055405c1180d060340c441130454000e1a0028100c3c3c95901c00e9041c0d01202d907010034230060040d400c0a10404140d03010340292215075038018114080140e5000038000c802c6c4013140c0503811031042840014404501c1e10300320380200c203039201e00303242c1c00a109070290954071b540d4040c0d402881c0130000e2010116020080c0d070740115050413403c488441e28602014404c812124010a9500c2e0100c0e600070400d00721020b07080320a84030182c99141c0e440c1c0c01507a459100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 25433468 1250 25432218 25432237
    0x108060409030806090702070e040605060103050f33130501050a1d0403030e1e061611030306060702030f031828051504030b0103050d021501060903120c0209040b0f06010203 76
    0x1903443c04a451407402e41100e990100b050300c11124266a0703540305800d089800d642c00d0720f1450366803040c040156454016540d000c03040c1a80c21005081681091300d10900c8100c900d0b0420200d5103007030321014111480300c3e0a0f18801404180410b100380d2038240180028804e06200701420703e00010718821003050700300c0960103140d9402d051b42d6640c4043d0042c0100e1851045a0700031100110381e4542038001c0c5034100900b0301c008015074944940f512036030900d41c091010520203041000003003240c00204a84e40104142c0708161034a440d4030110f49480b0240001e600340340408a9880740d00c103202030b041011031904076044003241c5516800c24401c1500e8203500c0d0858429000c05026908009144451000a00541c2d904d000d07504e803550495041c5c281c2044800c0d40104655191940d410404a01e80e902110700c030f1401035140c0b105c0a4844d01c0c3c00e1000418130003042042100150203a09524070454010704210003a24180c40d11100d82e01040751100803203144200490444c0d4800001d40701c0c2c0343c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 25434718 1250 25433468 25433477
    0x106020616050307050d0e0109020405010801020c030d0b030f0307050f060601030207020616031b030c0611030601091802120112050f1605010806060d0606110f120d05270309010806040903 82
    0x60248000c40300c99000510000174044108091000320740c0703912070803c00520145c0001f58800300d5204000664a06038048411a80103000a00b082c500100c22541900707d0f07010002050560701d80820b00b003041d040e0614030039004c00b00e1240306000c0007040c124460310540c400d50745195a080c00660482c0641507001e500070505100b40f010301c6034003a42e034000c1d0070b00a0070400310b038240340318044043c5460914210005025898100208403041c02815500051314907020b04501c0c22100080840f901ca102e04920030a42c20b00040c00b80100c8e5040740c0c000d1150008038405581c4600c07011080711400f00b0112410b2117a520100b104480105284403652800d10001c5045c0b481c1c000111490303100034111f00d0380800104240c513500101071059100402654031100c0307054902c188814100703014002c070302c41c0540110803102d8407410381004440950b01201000182c81c2c0340c01d000c40064644070050020f50703805645401100da41c000010308907400090780c130031080d079079004207000586815407801800704 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 25435968 1250 25434718 25434751
    0x409140115081b0c0a0c0504020c0613140105040b010815010806160908010e060601091202010e040203070210110417010e030a110a05060a02070b010e0610121e020301060801060206 79
    0xa200301c96041c2c00c0354001c9405050f51038840c595500e0381d40f10385440c0d02c15a001d80d03519001c00c80607404200041804039070842c204109000660b40b101801000c100c0380508000f00e40341000204021260b208605400800c110f2815241c2004019030a000d100c20071310482c00c809004285528040d810b940340c1d00050308507910b454403174120300000e04d4000018403a513100d001c02c8100091203150019400f4500a1000c0e080403800545042d002e900f01e200c2132080c080511015036000003040c18030102c1554010f03981e95500004900b0b00450f9250b0452060800401c01d02c0c03440140003610590350090745c42040c895030320103124200c452614030522036400c00e20045100340c1c02064205000081c00003514180b8001d81e4405c2d013040411034400d0046503010950000740b001010300c040c05400061060161350621400198044000c02c203101c041214801184880031416044800250320b91322140440050803020080a07400900071803001039520703000007910501c0024070034011032040741400c020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 25437218 1250 25435968 25436009
    0x60e030310031e05030f0901030b0d030f0c030e180702010506010207140909070e07020303190b030a020f040204080a030206061e1320070303020711091030050304091401 74
    0x501a9001d480b01140c0d141e0700d0040041401400100140300c01610502e541f00c1a40001501321014504030381d02a94030031000c0c00002e50002c0034100350780c42e103003880c40400c4054038080b201c0c0392413009001d03001118481010310403031004070494090345980d0000d00c555610303803004980d500355a1080000d806408420355884cc18800886500030b080482076445403601c40500d00000001510f410f00103074000001c0180c0500005000080404031072002e0201d00141d60029a55001020f406840b41c00460320016095581c0e81c1198000d00302c0005954200100d41006900c809003103d140e401007441c070003586160311044180104a407001888152091802100e03c002007403d03031054040b46a190902200e8042e5841c0989412032280d500907039a02400d00d08450f04126a640182c054005c3c802401080e0070b00c2c201d00005c0d9017101c800c90b1034a1000074181c1181c0e01a002c1e1142041c24138400500c18014044010070540e482c100c3c0a129041549404070001c8c0300074810300028110002c03041c582c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 25438468 1250 25437218 25437233
    0x3090d081b030907030302070609030b0a0e0f0d02010c030e01051b07053d0e100f020708040303030b120303070e010806120709020301090c020c1f051309020304060e03031003 76
    0xc12a8661030850038448401d04290065803003501d800000d6444442d04200b0942d040209002400051805c620314902d5a500d03003805800260070818415141c2419940d0341c1c0d401c0080c201612000e078110b420340e00320004042e000301040d500b00d2001030304011070900c15440501503c0e000f41502c0003404400400801e00c2030080e0403400c000c8860340640c0841d4030100b003941e5803804c00e10f01c00910f041805101d400d8407040c0441202c03100052541494007521580d83d002c9045a00074030302e50030100b81041c909101c1c60081c407038080018241e2501080110515038150301c4103030140b1060303402d0b080322071007017003216600e000031900341c00094241821380c3c06952042c60040d4005402400c00c0c40150740903a20281022002c1c0c004940455001c00101321604a6028502c21a5628000b501c00100c4003004102500d03008aa00d8044030000044120320034858811505407038214440c206019448800d1000654000d890507548207003022819900b0003004802c07a0f005025205014481600d141d40b10351 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 25439718 1250 25438468 25438471
    0x60f2d01090c120204080d1205060d02090601020a0606170c0315040609060204081009110a051309050c030307050c0406050402040605090d0302010f09050105010518060a0603180c060305040b070503090d08 89
    0x104021a040c400354010083d40060300280640c2e4016140a1100c40740c01092448000e954201a604010030300c655034607280b01011160740c054403040d001d40c0d10080143d24107918510001c210b103240c0540002d20400802d0712a400c20900000e640c02825100c041666490281015a242c0f10f880070105001420310351110785028441c44016060690350f051260034140c2401d50034500c9915076030000c08004041c017419007202e400311000c9800c0e83c1070101181000b2440702c18013452a9503440d008043c8a810444806000d41c0101103035540c3c0581c0c41d20a841e0b50b08000c6460041d0304013403010641d460f107070007504e0540d2000e9603042c1c02c104092080184061540201380c09655840d244851410401c0c01600402d500840000c40e25501d464140103a580381c58402c1900380d440e00080c840140d0302c07842c1d10790803a0b00c289404524030322400b0b001d015842c04804000c1039061a4000082c440e50180c011904c0b8501481b07000b58555104c2c2c0040d152440211074005481d001405214000e50049103c103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 25440968 1250 25439718 25439741
    0x31504200316080c01080906010f05010c020a090905030d050106210c090302041505030606030106060203090d05010b06040e040b060f030304062604060203090f01150302040b010c05060f2d0109 84
    0x442d4451484000314010003082d0b004075220741c1190700203010340c0d40c000060f030750401111b030000d00c5d0542c981491070741c22001070b01450741000810207201e015944e40c2031088015080200c010000140c0c0c520f0410341da0b6002d09064608241080b000203005409013800c14039068148207510990619001075500820700607001c442804030081010000d6116407188240b24441c0313008600f80350b420b000405103050070081106109a040402c203000c203da01100303031007d044d0143c9010800d0700c4d0307626026000d002003d203225042800410000350812128410b240220301403a041003140e00d0b07141c1804045030301500e00c03c0e01a40101700801440d4401d10083e440d801440b4400b62018201c0c4c0d1360103056801c01d4070140c880903000700511030180d60601211044a042200822000151307020081040c1e001c0d00c03004e07210310f03a00c483c2d5808903402404016074450344130081d92000d1800011100c041201a80c001c02940c0e010160b4690404094a000001a0111b40c03002c103d03a00e0300d101740000d800f000411 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 25442218 1250 25440968 25440973
    0x12020a0b0612010f0606050315090411120a0609030f09090e061819050703030e180121050d080a0b010507030c0b1b070c03060c0306051e0102030c100b0315042003 71
    0x13501403001e040c41180042c0c5120340e241c81d501d0801c1c0d8625035040d800703080c0c124461f824100c207010001c0c4034001c1000c1c03e96003e4451400f1008061617240c01d180c15244003030a501e0900000c3c0c41023550100c0740312409810b0362141403015444450234002c4940c00c3c501d82511380e00400100700c0280e0682078681c000303010b50b01194410100303d200d40411184c403131012103080c0e1041105004044d003103800c42c1d6041406650841013000050002c00b84404184203401143c1179001d10007403050b9140a403612150f4015046030442801c89000608507507040320383c5e6280920f0680346441e258441d0045030070182d05980c5803c1c181015441d4100e05050141003403101441a60070b00c650180c28402070111240121150074041d4990708001b0103840411005e40201450008140030a5480528000f0311500303207006800c42441040041c3c0c90b6104020b003000040c490380482100480c041d41168030f01001c02c0c2c00340d41c0f0100c4685040180101d0039540281300349451038000c9641c80c0d420709450a004c60040c06c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 25443468 1250 25442218 25442231
    0x81b040608010903022424010509100509040c080105010212090a0f03030507030306080c011202090a0e09030403030306050906060307180906030b01082109011202070204050903030412020a0b061201 86
    0x501a00f1500c000504801680040002081110900302c08824041c5050102c2e5150700d401c05c4c50301156901080941c0c001c189420151076070340d200700140c03242900080c100b101c03950510a00900a908189210361180c0e007441c1100d543c90744900c00c668103c58041c1c009100250703940c0c58464051300705042c1c803030700b10a01d000001102d040d00c01f0b82d14001c6000e520342c2540e420044c01d005003690042c0d01704003440e902c50034280000382d900030841058108210801078407070600030b0008a201c0d03a01c1c1e01c410005000c80c404d010081202000800071244aa1010404155103c00b40803043c0012a0100e81c08203082c0000380d007840c015807903007194102d1b000d1700c0f00c21a91121003100442d0200d82091310304814940050080000800c0711800c0840d0720708908940c0044c46004010b0351240402032810016000300380c200a0f14240c05072001c480d8010000d00003482c0c8450041d82c3c03a0000c5905a034001f06084c60143e03035034004100740701e426821a22005040d40c0301001d220150260304c106807655941c401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 25444718 1250 25443468 25443479
    0xf1b021305130209070905010207050907170106030c030b030106030f080a02030c030a05071103060f0106030b0607020409050a03020c06040f0506180402072114030a0506030f0303070c0b010906081b0406 88
    0x120740c500c103aa40074059038281500f401440381014006000606100181605104036a0000341c000110740c1c0031903082c040da0303480b41e2003110320710704980300745c082281d841002146558154000c403054210139541007007e400241c2c00c142c02c2e1040da11014084016280f0000081090080280b01c48031950048030701d000814a641403540e0300540520b4002500851080b08014000741d04e0000702e44200e0080506041503110002d80d0303031041c803e00c42410f980d448602400c1e01c6117001c1d00c00164006004210300d600ea424101c0c1c03a4501c1d00390440050040c641203050034a44101600c09031100240b0381c0c1c0c04e0350309203c140704a0382d204c2c002c110715441c44062418090340e02ca00003080180d01c41c920005554141101030002d01c107102c1c50003400d11260781c1e00d4070080c02c21001a01c0c1d000d211504080707126241c810200742400c0507034190100c41d000000070000210f0b0000b07400070400c0d11800780c540d0140e030380e45844800c490b5140115a500c1d00000c030841414184101c2000c81c0b140001c4c00040e072a43d485 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 25445968 1250 25444718 25444721
    0xa08060d050109080d0b0a060503010501081305010b0a0801020c0105100803071203090213020d05010b0c030a081e040503120606040e010308030a0b0307140306130317040303021c0203010311010f1b0213 88
    0xb00803003103e49484103000c52040c100440810008e000c242400e60855050000103403032041c0003001c401042e540b2400e40ba003402000d420000c0d03002405858000740c01d480e99590750203940310320200d43e2150300f824082103442c180d4074604d20031511448040c608004c2c1031342e41c0c1c1d044001944441001c0544440702040540c0c0c0700402d89500185050005a5400405003240c0c1690b005900803210110240098420f43c0313008000c4400c451403a14040710309589100c00000441221948200e410840388208410040d00000902c1d241d81014040d12541d940ea10420209104a000e224068050400100b000a012601840c2c0050040310042418603282001c2450301d0301039802401000c10918040c5503500302448035a42104080001014404443d280580081d130307814400341012031200005030925109a040d41d5100c4201d550307186111907040040c40188d0001e0006980c4861351034100c200d158054411081280602d849001842c20760240c0d03c08a24920342090ba0415006c2d8825140d44a09 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 25447218 1250 25445968 25445977
    0x80705040f060c0218010509160c0506090601031b050102032a0f0607030c110307030804020d080d05040309090e060105061804050a0c1808150403091203080402150a08060d05010908 79
    0x10b0740e9a060700c2080d18010000003040c0705040b0351320030201c48010f2150751036020790907a014140408002e00c4400c0080d084844410514000d031080c0100b0303050103061600455080d040700e02555200c014000140c40010941001c0d1260f14003690042082440e00f03901b20120404080d540402c0402d2407880074500c0e800c001065003460030580040e4204003280341c040c820603400c4041b501e8003d10020032804042c0e80c034459000084d042c0021440002d00319696003402d01290f5900504180d121000c401c044000303848143c2e403c602042a2403c04607241880b4071400070000144001003c4076460501800f40d15407000b130f4441400000b490260f040c545681c0140341c040c0ba407552000600d5000c512000300490844072107030480224410342080702c0000002c0540b05041210320602650b1603600d02560f502c04d280e44040c0c0000030812182d400c2c940c004255521590082e280e010f090703500c40c21015030512580014001150308007012602c10300b007400d0071300300c0300307124100024845180303449129980c0c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 25448468 1250 25447218 25447229
    0x303070305070305180307020402070203070513020703020613030c141e100b0604050105030c1c0f020307030b0604120b1305060133080606031902040602010b03010e150106080705040f 80
    0x2220750500c6001541486020b90140702d0038418807140804900c040e44a200350075001c2d21840d00444e10205640d000e202c1c0b41c00070040102100c0b4a800c003611004007942203514203a001d801100001641c0341c800e01040c400c0d550317041d0385040c001d01165465281c000c1046820017000c0c0309100c2c6c0d1181240b0f105a21485415541c001001d03001603d0402c0c00940e240d480080307004400c14401004a03981000640744c011040f01c0100c1c1e1a500309101882004610240400889081c8a14142c102a0560003107002e040303246d0702070200346140800c1c806d5038070841c8244d400d9100e411119001003149001c00c0d0b5000100c0e03611801d04000c543d2901071510100b81c01080100c444090541c1d685428800c00718200a4040b40b201174102246001411303800000b412107001c1c00740000084c100c400d155180085280c00c040007191119140c0000074000d01c0200404c40c085c0d881c00d00d040d9034003000090300d14160300a0510340600c031b81c00d1580449080c074028001c03005101c8113020200b180060110020007401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 25449718 1250 25448468 25448471
    0x909040c0e101e0308120a020706060b0403030e0109080309040e0312010602060117010509030904110c010e16050d02030c121c0c030906030216030513030807060e0d021209011209020303030703 84
    0x3414452180e0300c41420b480300310320f201480b00d41040014001d0040d43c00c4115026191501d50b035400c01e203007010b03104d82c2e00010b28a40c500a80441c450720107102800507a80a50390700a0301080702e030010740b41c41004d40910034256009221000d1586010380040014032100010742c0d0504e0164460085248420b030800e00150f04148018010b103000c000060b02c000e07101d80024400d03424040e00a82e103e210316881a8003031500c8a000050640d040d8007151620b0101900800440300d1307151f062074641e20049c00255040112410000780c030301c1c040815051250f0000c024105c0481e00b0000c001162201c1550020315000d403103440c01101800c899554601c02c01e589030701c0f0000296140090030000c154009209151062018641300715042c030b10455016410704200d65070341c2507040170301c007030311120762006182203c0010600c0810241da00030501141ca5201101c1083c654004142d0b101da48402000030154414000000c1940c0300c0c001d0f40241c4800400001001c04c8150082425540100d442c42d0209 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 25450968 1250 25449718 25449751
    0x6031504050f0f15060f060c031b07080a050601050d06061701020c060a02040e06012304080f07060203040501170402040912020618010b1302070602040f06020a05070b09060909040c0e 80
    0x1c0301c080c460003034800e12007406041345981e4802542c803001d20113000e05010703070a424103000c06515500110f4900020500c100c83c1c68540f00e4090441041c5944101100c90050000000b90701c6030001e15028010b0303111018040d9a820a800d00c50b40810300041070f504152611400038040d070303020900e10204c010b07038400560741d000001d03101858160090725501200744104801c0112000c80ca01c2181c01460034600321542c10700c0740060f2100d52420344000009044002000590070a0000b64405030701d50001c240c03064941e54880c117030703101c3c011440f5003404554600d200401c00c0460200281c1d0041c4018030000c0d8010007920f0701c8100305044168400544d2060303041c00141d00b0030115a007440d84401000380484600d81c00070400c0410140501c81e0f1007500801c0000400540d41c05460141284000d107680103555000000d645646000e02a105e500442d0008244100c0780ea040350340301440a080f0034034091400041c4003d10350001c0082d20001d0624402290014640609074024010030600500b02c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 25452218 1250 25450968 25450993
    0x30c06040611060f0c04030206070f0501060f050102070b0f0f0307120519050609040c0501030c0c0b0403020309130203010609180e0709020309010b030304030f0b0601020708070e01061b030909050603150405 90
    0x402101510148139082c00600b04580050160100c0d401c0c3c0b5410380d2090388480c102e181000ca0030802c07600040295080c54004a2500414100c2c0b50842d0005da0885d002c00741d85138012800c500c101c25070400715020400424007440070010085030081c145207001100c01c084c030340d20001101c2d8140c2e2540303901c3c0c802d80782c0603506a02d54020303150030100c04c403141a001c0c01c05980d10300410f8020b06c90316060544880d04544494040c0c0e49801c4d0903a00311080b03100618003454000e481c2d5010503c1f20740300355501002c40c080c0000d580700740c1e41601c1c0d80d502c070030301240c0c00e10007441a403c1e624104030541d207403144103804070074030284642c4004100050001d6142c0c10003050403800d4864402c41e05020758000c3c80b08002251004e4580c454403500201000302c0c0d9101d610040b810040076411407041da1180b0701c0d0014800d914001c0c0700703040794270070b54801010400ea952141c01c0e984400ca009000990354100611a22480364041904032400074112408000100490f10303042100f203a050341c06420415035035a1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 25453468 1250 25452218 25452223
    0x302070510021c03050c04030803100501172202120312040201030c0e150c01021b06070f030614150d0f090204050105060304020a151209060902011107060c03030506030c06040611 78
    0x6200c2420b0010381144400080c4083c1c05502c4440d03038808040d21140441e031000001000c030707170103503411000b09039030783c6401110300e51001418800e0700e0011302660341c5030449552001c2c11038002c100d29100403200350f039180c0e100c2c040c001c2c4030761050341d01c90081c0c4030401446104000030591030310315001003402482d2600014003140d1529401c3d20a00003254021400c907614810b001039608080344000da1928081c44850340240509a00b004000b481200241c1d1507180c0090003912640441d5144c0101d4419550200d0684000b44030b03030302d14080c41c14074048103440c0c1480341c2c1070900d052034410b43c10041c2105080040e11056000003502d20350340d840b5542903007403d000f103c1c05071106607a030354a503060035400310300e50841c148240480003d4021000b0083d51248030104204452800140140f06035410410024202044c0480c049003031803029168841001c501d05007100c1146d101c04508001d01d031000d0300a0207004180b0b50380340c0140c02a1a049584410151000d00a1a983c401c2240141d81c1e5203413 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 25454718 1250 25453468 25453489
    0x1080c03060a1a010309080708041206050a1107031209050105010b040302010908160b0d020712050d05070c02011202070203010b03070303021c0201050907170a0605090c100516020d030c0f03020705 86
    0x40c2a50070404461060f6003581c504000454007032900064448440c20700c0911806005401821380c07400190000340403039052080c07001e941c0204030800c2a501c4080204040f100032603101c00806005000c0d11004c24010300e0b14000b6000020360201f48080355aa0305421600240c11164144d4404038080c425540d2024000c1e010f01041c0f00107007081d482c901c0c02054103200728440d6142d103500000d1180c8600c1310741e4060b0744000e648150b40074070300390303818101408541140011507156031600001400c01c0d44030300302c0030341c07500c3c0c040e10340002e15811502c0304c0002c0e43c8051400e0340c01d507488003450061620704000200040d0b0103035003d4001a1088411580301020680c1d209045a040c0010b0040d00c20b0301081c20f00031100e8a03040400c107440c02d5201d0754144001010090703c550b01d020700304080d4007400b00b542000018115111160286000000e503030b2402891034032295000c00304130102c0141482044d03569424000c0c1808091446540c4c4c035624000031156080300181c21169007005642044c0d008071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 25455968 1250 25454718 25454731
    0x13022409191a030f0f04050a050d0306030201030c03150302060904090b0f060103051b160303060504020c01060510020a0c0504090201020c060a09050102060f01030b04060b0a0b0a02030301050a0b030103080d09051501080c0306 98
    0x42c0c50f60411261a0032500c1d4080c2075101c00c00514400b007820803a04010f84035a00d035008081c2c401018050f50098001c225038441640424100700c1624010780c400d00c14802c1c01d800501070954801e0850302800501d400c5250300c0ca40080d52400d0160105250a001d240304003441c01c1c2524051508400041c00d0361f80c0580240f91440c9541c1c400b04401c1281e038141d42c102c1180e030040e440c501390a0b040c00c4001e0103d9602140e0481d20005040f0f905030700640091081c0c400c1600c915003078411001c0300b21307541c1c90081c40141c4152400c102c01d21080c9015001a9091401481201d558410a0740050750301c0d441800c001c000318110702c03810006e40d6010700c40254403100030040c00c1c0d055891925841c6c040f62004200621140da680140713001a81c17494a454050610034034140d46514240c200650b980c0e04c02e0040710321500102c0d600082041c00030044906803507010940600f40104402064041e040e000d10845807400391020021001144042d441d009141e610001c0850751110310134141045400b81c150f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 25457218 1250 25455968 25456019
    0x30f180a0605180a170904020d0509031909080c01050705070e01120c09022104020103060b0d06090b04050c0a18030218070e010314060f060c0d0201050f1302240919 72
    0x51340040340100921050450004141c140e584440743c0000b0028403a45030354940051034501031005101c4008050200e85d8a14040c03048094001e900a031748125051080011540c401c0b0f5005007194428005800ca4074840d00840c0d22164031100f00d1040b0303040c244c010251400e84c40c80d014003032140e2501044020300da1408118500b8210078007007002880c00c0c0350f24031029810b8401180440e4400d130f110780c0c024400c80c0c19142d120001150510701409240c07207031074015070506440c03480c180340a00c5080e0103503d03201c90451514a0307a20068a4400036070030303000d0a04209040020250310740900c00502c4106014090321945011540035001201c0012880d04141c500080080300000b50454150002d2080729034084825041e400200b00d80b140d03042e100002e0060350f1200c110140c05400a90003488117115210207aa90007000c80481410b41d84047d500c4102607400503903941072502408080d850a10070540f4040c1c40d00013080100030741c50307078440b4011040c040400007450100308a00c09103501c20744 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 25458468 1250 25457218 25457233
    0x1090b070302030d0207110a03140f0111090103051e090102190f08040b0903070f060b01020c011806050306040905010903090801150b0405090a0b030706080f0a060308030f180a060518 80
    0x400966078010f8142413115150300291001c1800680c100385050710b1402042074050544034501003400e2154007940003080c0c4510700d0901c0e203281e01800f8000c01c04a02e5000242046022070044000d4440905207000b0342c10745144100b4056102e540c0c6501c149030100015035101d940c0d090303200b182401400c5050070041080041060785600442c07054100c0d81111043c2001e449000c1018254452200020071885940d41d0100400400340c11101b08540c5c01d03001c0d160144040401951514010040031034030040c000340a000e414007904c00341d90804805480054254600e0b9107190031580304e00740641c041029000b041108840901400811301d801c481072002e11490203542240701d000e14011244160310030030000303260884660000070b01940040898913010b5440a0240842c0020744034180f40641d0040090a0802d085c01000300300c0e035010102c5880c594580d01100d083d1400034041c0490b0541c041c0d4102000d21080004c0c0c02e040d0b0280c04001040c3c186040b02050f800100c2e52140255041503c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 25459718 1250 25458468 25458473
    0x3060703022517070f0c06030b010503180a080706050f0901022a0a1b0306050f040201050a030507020705030d09050102010501150801030321060306020703020609061006050d110a030b01090b07 84
    0xa02c401d410081100380c01000040c1d2a0541540942400c00d20514030041050310510194110706400c4070302490358546480e84424017201034400e401e80c13850101d881000030841c40011910a001044445800e4610402d5203a0f190f0405510500c4c00303507602c1d0b4890041c8420910111407145e0007008e600f008529007000012000030b46c0c0312040c01d0541107a2030030306518004800340494100b80b54001c070707806072086485806007429151030200345c031610300e0000090508241c498006000769016100c40e03043c5006440301b10060540180843c00314000c0f40c50000c0c0b1a00c0812101074000020340721140c103c0d05200c00242100d4050388044075032094120101300042d08071040a041d82d4061a140e80e24000000204103030040440303c0c0c0303081c589071003000000d20034158080c100751440f0383e00b40d0300c1079200c11104e2a9074140640b0110040250420304100480c0aa801440c01481c10600400c5800f03c8800807034944d0040c29108001ca0b0f10b036540d14a0f590380c811100c030090542c8169103824220b164 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 25460968 1250 25459718 25459747
    0x209100306150c1a09010903090602030301030b010e06060d09060e010b0d1203020a020a0507080c150316030203070315081c080103030819060503010c02071a04061e0908060c0304020306070302 84
    0xc02060902010451610a12550f010352544480038099412110305224685500801f02c8407820b60010b014400041090f41c80403007200d0407070b07400c03072800c400a03401c00c2e0941034929005091164080810055180603111074015154506d00445001a81d42105000c450950320b00242080c0304101c26611000015110869244d102c59146001a1030310f02c4424240d24000d901030003d080c5225000c1e00240c43c0740c001444d00200c1c801680c6410800c802154003c951f030005454940032100030801d880c0740745100340e015640c083c241d490003007240350148100e0403001040303400100c0c40303070001c060061900c0d14079808441034040034585490550b15548008202c540064603420441000590480c0f406005400100c05450000d000300110b22040304040d43e01c160910450512007030361007480324025085002d4404852150300c60011480315071010410701c022040c2240140894080b0101d1307415802c0050500c45d01807001e1300b554a0800c1c1c01018a0254010451801c05004100071010b4000c034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 25462218 1250 25460968 25460999
    0x10509040515040605060406082707030501051005060301060509040504020a0f0f031101020a08070f020a09020d0b040b0102070b0702130f02030408040303120510030201050a210f0b04050c0304080d0209130209100306 94
    0xc0112181401232500c02204621008c5610380c524bc801c07070340c4c040180841075101c2409407000c1e00070001519507074014410640400d10601d801b041003403200359018141904000e6105100400880790381d40c0311107050701c000c181c5400602410b980d0000510400c148101e8104012609000404400c0d500703944240c414482c0301d000415010303e40130303940219160301103032002900c4048001d6460742400c0300032000600c17041802e00e10072410038072f01d40a90350000c42c2c0300c0b080e6105108403d01d48109902840320540140346441c07015036841106100404140c400b4500461095106a90781d40c0781d402c0040a4100000484415074900000e000d410240c454030329080301d80c20b082460b110101c1c09000d807000c51458140101d070702c00025040312010000e0b030150303640b0901e0140c10840750079030300248012100100c0b50030070700200810202e00400c40e0b06000c0c0882142c02e000152918814030f011a5181160101404c0c0c0103401103821686840d0400300040d10485c0c40c80e00f046090b10b040c2211100e0200e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 25463468 1250 25462218 25462231
    0x120906070f03030603061b08060108011a0c07031506030c060509060d0504080702180702100908180307090c0815030f0c0910170601030c060206070807030b01050904051504060506040608 81
    0xc11406080c10035001c0d804c42c800843d009030080014251902206101210140c2401c0014402000140c0998000c2c019141070780c102641900088104c11030414255224091640003442010000800202c000051081c40101c0401c00302e407083c0341d0300e13000d0700543d0b503600400203025040c42085000c1d221081620b5520143e4003011134103881d1820440028070582070081d402080214500149002504189003e183e86e5400c44d05000c03a107224100440b46880002412100b04016841440134000384056800c44020705071171003203030381d001c01108440c8204201004100d0400070412031502c0788400189041059024204100b090a05c460311800481c481c6445074020201040354140860b8000c00540390055541c1905000c01d6062a07a0301030034030045070800000800465401e1000c00c0c40c5010f8038a41c2c5540700c0c1a11000380a6014140021390241001814010215a5903540c0280c50203080b40098070b45a0319441380610060b6115900001d00485041004020403544988041d80c40714 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 25464718 1250 25463468 25463483
    0x50a020c01050304030c0807060b0a080c1e030708060f060f060412021005040b1c0b01020a0b0708070201020f0307050c010b010503151201090204092901120206070c1502070812090607 80
    0x3d42da46001e1b10803c5580301d01800d60040808c0d070304100034480d0301485420004807440100da5540d10b111942d1a0040700120742c0007030040c500ea0400421024544050607001400e1b10540c684499416242520440d8501d40581b110400d119007400e040481146c030075000d9450616250034100041700320411200024003070580654102c1c3c2e10b40c4a413081da406003101801d0700707580714024810309491342c000e1030403507541d04e00d0445034000f20360001440e0003001f03a2016400d007a550310144165520132006181e0000c2d0754080000f50b425020b000d0086104841546034207490799000c10100e401c50300214a8203040c441c0c1041801001ca03035484001c0640207044a000000403a01c0400740d014200c2d07410025002801e01001c50200070021000340074410103000c41a000c105409000303200083c0a20079030380051400b50320800903080403001450107e000b40c1c292480540c0d40d000315608004407c10400040c2c01040061085440c14011550a143e52900072420110148000b030780501c200c410003440c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 25465968 1250 25464718 25464721
    0x1030803060d020604060302040303122d09050703060903080a05010803090d020102030c1b130c0c0209090c1e04110f0301060e010909060e0f01050d050a0204020c01060f03050307060b01050a020c010503 88
    0x40e80e424901c01c4040d580034144c10b80300d5a0b2030034090065080742c00100c001c030751828100108200e642c401e00d1a0518101da0a07038201241c810208040f00141800c1c80c40b041d12440079402013041081aa070003944260030004540c5518180144483d0000d07000b4880182854010444200000309940b1900c000311001d0084120728030041c2e25611a4a04c0c61400c1c1c060220742e00e198885007000c01d54040341c10342c2c2e101c007002c085400945c21202e1840c50fa60103d12035200c40000342c1030020015503c217110508544486442400140b04111100d080c241c42d03032124250703820a030406000d804989407520380c10300d003464050480d42e89640014020802008150182020b682c0c0c42403840f031004091610082149588800f02c0300005034045a1182d641119000001a40d0524280c52070056801c40081c200c030003659403c21010f0340c800300341c1c800d85d07640783c40c40403889034014081a0021440307a00116985c180d0391030924240ca0301c004c4114180320040c0801c1c1c1c1c0480e0041031034444070b4400d00c2c0280d074a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 25467218 1250 25465968 25465981
    0x10f0504050a18060b0a0f03110c01140403030b0301090b010b130e0702030405030c122104050303120405060108060f0103060906061208070203060c091507060b0907020a060501050603040b01030803 86
    0x5030180d9802940d210844000025800510a4004110702e24500d001d000e4181c0782c603100e004e0303071094180110020b54845118025a8070a42c411400c0f80312035182c00d4a4403501080b40c900b982e00341405201d500001100f400201601362050005000c800c0d40280940c01e80ba890300014100c3c1440350340c04242001a400860444583c400340103007d13040840c441505101000a503641c2041c06000d02034414001c1100701490f2109221401000318401041510040b00d0310317081d080030050340307000c800005100200d8540d4040c800340254941c00c04281859250608140c0d25020041e03004860703d81144061002c0c03c00c2e001182c90640c0d8204130041010803007481e0180003410b0903071080440072007094a030342c1004084402003503400d000f01d04072411500d88070640580380c03140c1003009901020b52204038650711042c1c0c025010f16401000000750b90b00309203010034000c010890754400181c121100070400c2200c030b842071601404040d1000303030071441e00b03644840314040c041c0000781c418100400020038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 25468468 1250 25467218 25467227
    0xa03021203120405060f07030603120f0306030503030118110301060801121110080601030e0c01050315040e030f03011a03091e0a0f03120b040506030a0803040c030804030b06010801080a02010c02010f 87
    0xc1241c0b03400c080d403440e45054106161985002c2e5041d40c01d0065000209010512a002e86015603400002c03045803d490030b007040d00c00c00880b211880c2815258100000814401d00255008058004130a40240f0b180c0404c00e0495052407050703041000300340300510401303a00c43c2040d41519200c0441c9061000d2904186a8000b0b9003403403d40c2c820206075800e00102c0e40100600d020f1403082e00d09203c8001c1e8402c1080d00da54107c911130740052024800111400428102c0a025000c05080040c1c0d03400a10203040c155805401d82c0d1005034400001004a00c0341001c5444105141869003070035820400103ca4584120160680d21020245084001c084041c000c00740c0d080d5100c00303090303603031420351801800011105814082031498120742d40f00c20300b81805004d104034401400750040c94195a58961a07401c05401501c0c01c2d00c04040102c001901c1c480188040c60185c4008116071414900050216030141c01100d204c1d00040c55400061760050740c04500154242010780000c01da01000b00c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 25469718 1250 25468468 25468477
    0x40b0d02031902030106020724020a03140c0105010e1005090c040e150d05010504060c17040611040e0a060305011505010806090a0b040c0507020405060109080304031b0f09050906060a050a03021203 86
    0xb08858400000000d049800151140c1110ba0041c050400c45000d039050750310b003090003c1d0100140c2c00c8034599400192090000356120301c0c06540c0a4203151124082c0e50840d9001d030016405400c91788144070b040072070300e1001c0008100442c0c1c02401c514001019846e1030041c0d12030400c0e03000d8400042a507034080200c1004500101410340c0c02c158581d0700b0305a003e8801594161541c600c1d04000a851500c54000c80c84074960020050845840d165103420060003103c4040c41080024003003c120010710802c01c90048100d02404201a4150b0070305600f110032a42e00748111240e04401004140d82240030703903170321480c12113841041d0340d1165541009050034202d40d541c0107103003440510480f50008050320b1601d000761010801a61200c00540b904a82070141c9440c5500c09d02003000011400c5022038045a000300350000d80741c2d52000e126071242186d0b000b140126856504101d40b4000802c8441c3c1d02c541c0441d019680d052600e004118014035a010280c00340451200280c0340410410488 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 25470968 1250 25469718 25469761
    0x1a0c09040207080306010e060903030403032607090602010c05030f061c02060a03061d090c060c0109050328020705130b0418060c090e060609010804031b0b06031002040b0d0203 77
    0x10342d81e4441500d0490400d40c02103540720b001c43c1035028010407504044058516000020340154600703400e54505513080c80d100d00140402c0c98080780ca5004400e09140d009028040035101c894009040032006420b69503142074101c02c02c00c0c14000c0004401c0302148841e00120281d641c1c0c180a000c501d03124064240c0c01c0c40194114600042000700075174142e002504989011102c3ca6008100b04010000d900081c0d0b0014019402401c0e07001d070b944bc180d0010210412843e0000820f080c82c0c0d5580c50454000b24001c15280c0800401710005030350079009004110030a10207081498103240010f078050354080b88002c0c40a0369003104021648966120300c000b48260400e01444542030718045010b0700c42601b9001c0043d80001340020046940741804e8000c0400400c07142c00e0003cbc01004441d071074030090050b4108100e489000c4504480e1503940303c0461b0064454241c0c3c0e01e030803000d01d071501031a4804c1181031031040201704000390f51801a603950003800d40700035a41c0d4a4004000e20740d00c4051401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 25472218 1250 25470968 25470971
    0x6030c0d0509070609061e050306060c1902040b040c0f120605041104050102011107080313030309060207050c0a0501020c010926030d020405010f030e0c0409050f0d210501031a0c0904 80
    0x140301d858140000c03d0380403141d09070359024105454180c11104969080f14a503000d010408480c0070306c0b80507401466000d080646a00d080840202c00303140760000300810081844103560900c025810f041c0107841c07050308169030a00811012103030050580c810b061180c0100000c185e01004461101d421660003810000c005026500c4c40100007903083c2d210b4420a030141d0301c0c00f844080c403010041c040c1d0769040e80060605013142d403240d52049a44a040104404041d03a40e09004005180c03840075000c81070186001b0640d404050090041c3ca0080e500054150b510030718843c03c1607a07016039031800b80e1307202c001d200400960310781080242541600c031005043c0400300e00700328070f802c0740e44c06003048500c2660360500104a0b8241503080f0b680601d1409c1490308400815640703810690481401c41d0b11403402c03a2010607180302680c2c1059013802c0400000f4420032071039100e9103140360800044100c111020440d0b54034507a2080c64080d040303003114103d4410302c4002954071000300c0c00e03102c0c00b0901500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 25473468 1250 25472218 25472221
    0xb030316110406090b03071203090e040b040605010806011203121506020a0312050402100309050c04020d0b030601080f07062001060303090e0a060f05060f040b0408070302011d0a030206030c0d05 85
    0x14410000c03580c100e0180c1c060b40ca81040007070845803d004000c181d640142c060701da02420000550041c0e00c035081c0070707020300400c148002142c45906451b1840f071400f070140e8890784e0800e0310f05881550b40c10782c0444195400b10f40140498019401e00101c0d00b5413504008050703010030841800038080c1c0d100c444900890302c54002810980200e10144590b10075a0b880c2c0095106480c250110f490564010750005400c0c1d0b85950210301aa2010440700e0090085400c468001000642640d0200392040d1600e1f89400c020780b614102008202c0c0508440703000303070408900800e01c60703a44050700e204480400c5440903445038090200c807142201060400000d1044545900b005020ba5600d03200d0344081c4c0045400040c400c03040c030b1245400361000d08041440c003030314000420100ba0054150102200000c20002030a0340d10180140020b180700d0024040709440c0d0b000150081040741000002d4461040004280b952a802032000f0340e0350480c1d4180d166120740c44c0401c03441c0184200750300d241c0e29020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 25474718 1250 25473468 25473473
    0x603131502030403080702150c07080714010e0d030609060302060f09060c1002070c05010f080106030506063007080f0105060f0c0604030201150f081207050c06040303090303030b0402090f040b030316 87
    0xb031500d44200386076021a401054031103180402104111029481c0e0400ad105000005012350010840c0302d010790041c0380b1a040304405103084403241c0400d40a03036401081c0c0d50130354030b070580640c1c0000c100307008003001958a5a004601d0a11512070082015240060f9803130080d9202e500b910b558441031802c41b902c134901482101e00952008030140c0d21070009003400503040d0710403404038104590982c0c0e070700101e03403030a20142c010b0100908890360000051002c1840c0c150322810103d01000040002c1d5516100c4c0e0111110088010f002481000050070070001c01514900c40c080c1100d0055030090360b1401e2001c0d0343c00c2030b4001d901c0380075454041e803010700c0103250341500045111640c0081c4502030540c0da800351146000c0320702c2000301e241c200c41c940f54038468241000d400854020810342d548400d03280001036443d4880e4004502007483c040090051541c507209086201c001a18114070b440e0180000803851503c50210354400c503100c1c0c08180a6490620607905840442180300e11b8030103151 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 25475968 1250 25474718 25474727
    0x30102160615090b1e12030703020a0b151804020301020f04140a211704090c020303090f070e06130e01050106030b040b06130e070c080406030501080c0904020603131502030403 77
    0x209546540c048480c900400c0603041841014946000103001d01c05005c82c1c81001040e43c00c0811803907510013200300303288414a000340b004000b51031196001d0304080301c1070f28129528920280c03582d0010340580803000e01030389902d40c2c41041c40c50303030510f500c1c243c0d612480043c0c00382c8158854401d072500301050003d011080e0f0684c441d0003420440700da20300992180841d400e1611a03800320301c42c00e4101c03908035000c0340c0315284200300040066034162605458020410035200b0481484005900000420010200c103211202c5120344150290800520304090280700715000381010f03100722000e803803601c0c0103011079102440345100b59000788980c0d030752640c01400034038030f40120901841c20000d48002c82c0c0f50040c1203495031103c01c402d00083c80c0c1084d160506055004110000b0b002d50080e111003c18112006800188030a43c1c01003807541c10440c01600380320300c0c00e51060141031010103010044c5c1e01c20703040d654406802d01c1650442c3d945802c0c0b0010709580d010f28040118400418041850b501 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 25477218 1250 25475968 25475981
    0x4051003090302010c020a020a05060a09241818050702100c0e010201180c06050307021f06170607170615040e0f0f0403080105010507030509210d02070605040308090301021606 77
    0x60f8000b085035180152090b40c640405c040000c1d4010754803034060000e0b181c0103000d41400c40c0c0030301d462807406817035200513450904285a00120840014132000048c1d80c0400300000340c07440c900c0311041d018580b9100442014800c911098255103501c0001d01d071510802100640a0b02c04030306118140b4a2000a80003d1a010b210350040d401c00300d110000340101d1514940e1720303900c80782c101000341c600082102c990f0005041c510450240b0a42d031401c80040501c1c2d6095041d801400142d6640f920488000901000201e500250050020454103d4200146400e402103140c5186074a5495100050170000054141a0359040200d03022074000d407820034181c42890410305d88070036074031056405010108112070040002d0b9002c0c00510103948101d001d811414424103100707003001caa0500007031802c001009003c0c000c151540c00c90701c041c4001c1207a05051021070014021048c00e15100610318030442c00701801c0e1040000344030030f241d1030940c100e95010040c4021615403488910341040070340003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 25478468 1250 25477218 25477223
    0x2090f0406110406020316030207050d0503030906062205060a09060801020d150302090a090804050619020607031a010c050304080d0906020c030105270a06060909020901090b01050f0f0405100309 85
    0x6030400107110360b0350060444095401a80003141484401c0340b032a540d000203102e08030114020b40000240c142c89085a06600900c200055503d80c5000c182052078400e0040035540318404015081005500601051705060040500402c8030340c2c81402103600c100260340700d40c020900c0d00000041024040d405002ca00700405018800c04118448107440c0740160b02000e54040b14a1300031a54904007039102c503078007503c00c0c88143e0130b250b075610028106410080b1050083c0500c1c038024842e242d8180300c0340c0e51014281c10104011354401c0114148007241c02c00c25418440c0000440040c84801c0080e0b60081a401d0f00300e5010b0800017070010001e29807482643c0140c416100cc0b40c48518044c05164441d9075403896980d965141603c5850000c0041c000f9190140503842c55900820b83c0c40c00303101c000c0c100c05040030940294a105000c0d182c201603200781c00c1c807840d00c5000c401076a0311104443c000714507050720b6502c1d04121246a4160311403907200b240d1201111100a00498058110004060 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 25479718 1250 25478468 25478471
    0x1020f0d0e1e0109060513091104050102160f21080408070f080601081005130f03090f05040209060307031508060103030801050103060801021206060a030b090109051605070302060402060304020d02090f0406 90
    0x1c6440b21500030000c2020744850201d80311202c02d1003054490001380111070003904648a000303a0f65100d0300c1c220f60841450a0404030001011302036940c0410842505c490000909101136290403101c40d80140d06008401a044140000041074058010018450b503041811340ea62181c0d1101f03510350b526400d1290303010306181c508000942c3c03900072036403504880490014040a142c0e000102006000003006c0c828001e85019a001c0455010400322500c54425201d6079403041c10b082e400300c1c50304042c0e072040703101d40c0c0108400080c030b80b41c0b4015a60020700605022660b8107034465001903185080c3c00455031480341d0000001490740c4110313454102c8600b80c03008c1043e01d4503000b0007402e03882501140c2c4102c0c1100c001041c01da0a004000745940e40301c43c900044e80087d49400100c005100b0b0303201d603090548503010320060940c501c0741d040450348681409443c0c0416540c000e521210020f00c081d202e5140807000500b50740f10890070400c4158014540e080e640303882144415140b209403401e84115 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 25480968 1250 25479718 25479739
    0x904110c01061d0903070f1e050d0305060607080f0d0207050a0b061504050f0f131505030c01080103030215190606120b0906010c06050c1e07030210020f03010504090201020f0d0e 78
    0x2504195a0f650090701c040010754602040b54941c01502c24180e07030101c0d01c0c0c0b0f00601c10146e5058000d800c1601c880c0c0b180c1c015104081821070010250b82005e01000d106400c1001b2401c000f41c02e00e821902c03042e55108039107444140d510103001c028000c088002d856409443c5c5c03d4000c00c03014142103807141d04100e821300490290b960448415001d54002c254108035591160045440e051151b0014007030024035001065205a802c0001e603510200311b010890440c01c004d02540c94288203601c00c001080c80c089501c0d61450300c009540f0300708180103212502410300451031a60b400c10041003a00c0c0000c42c18056030707a0b220307001050640c0c0c00105d003008625150007080f4614003103418030300a18050b501c0030340544035074490a004003405840c850109008104c12640000f01c00981240d42d54800c3d13040d40c40e11f10608000e07090001d5000541c2403240b04010a9010421003000d5030305550080e600010030308441d01c0140e1614080d10141c022601c00c0a451080300c0360f004081415101051361841100c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 25482218 1250 25480968 25481009
    0xa050d03091a041b0909022409060711030304031a0f060102030d020906040801110405090c0f0403060b0303220f0f1805071b03020106060e060c0706050904110c0106 72
    0x480316540c0e40184000039030707021680d0a052620b41d03190041e02994054600302e01c4014003190b041d04562219840c6a260002802503240881c03100a03400c0e43c640140c0721407665814000c0d40c07441a1030a172407140e103011618100b80111124800890400941140c1d40c543d2a8186040b080354485004034003d448000051040040e1445490252406800450404000543e45030294000700d04040c1c102c0303c18080003c108a090154010520714a42503d80d25802c000a001c00c0c0c0d4801401010740c1103041240d02100c1401c2c00807902140d821400000da040140d1001034114412801200d0030109915402c40c0410650b04d0707484100c501c403e038400300042d40c900119043c0c0b286840b07101d0603800351949100002560343c02007548426903281c02c42002c0007680380004501044141500140e5482800380503090300300c5084e50754030302e00f1900c0a0030300110800081c0d4400040c0074200c10800c1c0030030b00c01d88645498000c00c1c034804000e1156030326821034114407070003001213108010720580d1400c0710313084 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 25483468 1250 25482218 25482221
    0x121f0b1201061b170903120405030609060405060103080304020d0614070906020111030c090d0f030503040201090e040807060f021903140606160b04030c060f0b030105010e1303110f0703050a050d03 86
    0x411034007211402c02114a461340826000070500075038140004002c1d00880d640c081c480c8440642c4e48413105503e1340d00301424185040001810740d0115032010041c0000b0442c0022201c0c112039029030990390300c3da5203101240402c00d08900c020600ca09200d02034845114044449119030010b55481100301d50b252000c9090350403083d940700300900c04001048040000b0300040c031b0907200241100d4084030407641c4080040718450700950000c0c2000c0144000c42d030703010134070b00c2c0100101c00362502d0908103902c1f80c142d40c0c40359100060845541c0c0340003410b04070898054032000b04211a0404800c1e54809028000d8012240c040c43d0041c2d103040001e4151410605440108180314a4009550b05a548814005101030300c1039041c4002c4001140c001246030062546e5101c69100108000c060380052601307503041a0400307a00d004450003001458050040310300718041d0145042c54841c2221082c4a08280500a01c0c0350315005400b0b011090020000344080f10078400e40844500c800d05410450 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 25484718 1250 25483468 25483487
    0x109020607061b030203100e06030102070b070203040f1a0406030c02010e0f10051b040501110a020907110129240304030207081209130b031e010c140906121f0b120106 73
    0x184847c1050740d0511100e4901140103a01080c050b000519210403500c503200000006c854004c0160702c00501400b0341d005d008840d00040400c1e51022800320301e142c1d44003000f8001c40c050f030810190381d8100305407000d200350041c0741c000d44000e0540b00f0100314400600d031030f20910660100d07c0c41c14007001ca040e80c115040c0013400964413170050383c1000c0c01c3c5001154520551042035859220343c06290015946020780f46028481545606901c41148920b03e8250b0f00c5080020824010040203003040000b4081499a40d82045407407a900e0322101501071901c041114000c4814440401044200750300014108166007503601201c2e00346e119500d84e27019030b202d02000c00d60004480412108920704681103200c80582c01020740302408000c50440c200400007484d501d405a444a5496503966049010740b59814007580708135180007040000704446200301e85012844d01c0c41d40c00003802400312a0703200c084030582050711003526907440c80e01490780e8022468000070003100800000c1e8070b50060a140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 25485968 1250 25484718 25484731
    0x301111201050d0c0801050109020a120507020a0809040e0316060b0901080c1003020909100504050a0603080304020904060603080c0105100506190e01020705030706020105040507050d02031b01020109020607061b030203 95
    0x15205a090100340100c6440c0d890089076000b02c13008020968003c28010709000c2d00e159100142c8404100fa80105801d4042614400040c5080144545d043d4041410f03900f00e50002e0302246c1e14a807102c0454005c0c042c070003580c80c0901001c11200510072281e42c1310a03a01e4058801448110030880030898890000c0c0300f94446603202003003403541c500300a03082c92481c0c0c0b280e060040c2004418030200d1141141210030103904a0142802d0215250500c25180c1001da0500100a80d5083d51741c9c030b4031584000391001c1d1050b020340000804000241c1c1112001c0c41c0e00000094486050314082ea011300b000f914007820038042c4020109490074003c0c00da0311500c0c580800200034143c504c078183c442c0401101c2c06811401000008101da03102000980e0080c44142d0000805103041d080c101c3c14a401908442c2c03044403942c0c6950096070300019000d8010303c00708a11811030708014010b07030051079001402508040c002c01d03507c090140303651020038462001d0118a0003080528801c40892000f181c58 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 25487218 1250 25485968 25485997
    0x1091103070818030d09080703080714040b0f040503010c1106130201050706020904060509190f0b032e050c0406170402010503070e06120f0613020702030705060a03020d1a030111 78
    0x3401c42c40e0700d0308400f080c0354076030041c0ca18142d0121130103001c1d034410100a0b180c2a8000403000308066015040725030107105440c080306544200c45041000f442031740b048984541000c1500081142920126402001c008008100c2149428000307403040e5000301c0309c00814011100040ca46010403140e41e044150705179605840c0112a40c0c5a40094000803140d940065650801180ea6198002c485002e01c2d155206406800300c010180c0080d02c0000700c0740140e4500b800c0c0c040c0300c0c82d10300140d1640c0351010720f0200e20380c078989036002401c0c14041c000729103001800c0000384008078054070000c1094841036500d1400a0401014140005406440003070004074100001051240f040310490841103009050318613050320a021884454401d803020540344441d20184052840c02441c003c1c0768003d481ca0039810410103400103074851900348140740c0038990004c1c0b40da103030724440e604440c910820000100b041c4400c085044c14119a42d1030b0781c602035881d085c00d0f11440403070034003521040d502e10902e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 25488468 1250 25487218 25487221
    0xb0105090111010b090a1a0301060509011703120a0c0e06211b0309011a100f051315030605031015030204090201030e1515011106060409081908010911030708 69
    0x44402000b00603540d401d81d5070310402c0141e030755640c0e15441d0040304411008195148040d4030020503040d100000c520983c5000c20170049034440c4802141102c038000c03281c55861000c07140041c1903200c1e08000b000041c00000c104036200341e90380d0124681c2c03031143c1e540b0001050b4050078052640701e0480c24999100014504644020309070b042141e0040c10121642e013400c10085840109403c140ca1110450f5110346640302c803510340c4054031651050850300d00510106840e40940305080004185040040008002017408940140c0a0040500820140301d400321000d00400424440c0559803117409081e03c40340c500c8442d4020008600140803946410501e075031300308001040b105004a06150715400314080182051242020744c03021000012094901440400400d0b0b0b01025070038144110000c0d2401d0010001500e540c4c407180540d4005015641810a41424050b000d40ca038124403001c001880c41580c000c81c201e0403115845010300c080312600d0441e500ca40001c56008000a0b00f250 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 25489718 1250 25488468 25488487
    0x50403022128020f030708070b0904050901020f0316030b090106020d0305010807050a05092d010f05061306030510051504050406080a08030609040f0f0b0f060102060906130309090606031e0b0105 85
    0x2c0c1300041803200a0403940a540c0c0e8090160400c5040d60004009610204510700142040e0241c2075200b88000001c52030f2000d80f4054000c140800790551120307070b84240c82000b0341c500035400030061490007400c0c801e5560359400000d5032208044206c0000038105400055002030000310101651001020007a00700e00700030502c60030b203000030f080d002031400048c1e03850411031388114031011500d05c079000c2c0b4040e581032003102d00710340d1107603400b40d0300545007000344600e040201d1800b0740c140c500c07a180108540d140c0f050300e0080c00f070b003642180f40d009407034601c00c1c00c0505000307004004807441590140720065941540c4c0c1e4462542030405400420200009491440e00c0058564014030031700d4040451800c90311410610140e640041781c1b80c10f051010300a0440603420050340c4004244000c000628041c00402d80f00d81000d03140f030320490864426170080500440104024100c11365080148982d1084020b010f130011071000ca80d00d00b110284000410414014000c0410040c0c4030b60b4601405d11 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 25490968 1250 25489718 25489729
    0x10603090503090901080d11060103020a03171908070905010c0506040305090604030c0f03061805070b0309010f050906010e16050306220905010504110f0f040b0105040302212802 78
    0x821003203480b400304100d80c1119580d2003e03050b020700030940c0200312192500e100079180305500c0c4212051980004010001039494900d420103881e40440b6651202807240444071050041100c8001903400001c0500e2084e9804604cac179118446035036070140d50355a12401512414420708003c0c00640090000602090090005010b048030107403550745003e0ba00c1d03c0743e031030300045904054150f4403140c908106005a0b40690000e50310b0105d07040c41d4400055450342d03615040362080025004d408000220091004c0d4804110204946402d20141c0751103070180383c444009002d00341c0280c0940c2d0100380804051007a04420071003036118180b8644894040003c0c0c03080408441d4200c60101841d480341c0390482c094418124482c0e0700100351410646002151080c001912602030342503c1d655040d00e6590900c55201c4030340580e0002945508040101c42d50b03c5190800794001c00808030503488071b0080707600e0352030740b03804501590380401c1340019042410b480c0c1e02055171074500d0003c0d62009403808 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 25492218 1250 25490968 25490981
    0x150d020c0a0803010801020705071703070605100b0c0109050f010203270a06020d150915030602030c070507081c050702150d1506031a0306010303170405030903070902091e0306010603 80
    0x4000440c1c0020300c56a441e40101e900076049a9040c0e50040b0f428400c01c0350410210001e0500703a04070b0310442c503c2080c03a41d668020f00303c0240c021034843d40800d00c41602a200e01e405054660100c60756003400001c414080d00c1d00200c122a40d11079442402d000100601c00c0e01e002d02810700842c1986032040410600520300c44179240458001c1c20302910024070742c2c0c8003c00c0095140e900206448210814034200d00400740d100301e491508000e40c0e00d00a0b10120241c005681d8000030058030780d194400c00c1c8516004541d1300034460305c07680c80041911a0700042940990890700c00c10ba1405400c40c0c0c04481c18000c3c1d03a0001d4000c00ca40ba02801421121009400d140b861140001101c1072995880ca00008460784643c000c05c1d030303c1e9050591010b4903017104e20044130640c010081c65140d0b54006081a182c04201a040305d01100814100f0506000f1200c203400d000f0101e9074070030344809410b402540a0580f807031003036040c81408051030701c03620031580e82410001c000c2d200c01d82c82d1000c141d029119 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 25493468 1250 25492218 25492237
    0x301050d060b0409030806040c0806030607050c0111070305121305060105010516150b120106080c06130e0103050303060f040c0e100c0209091005180c040c17040b0402040506150d02 79
    0x85800c42e4144a8a40748500e00d0310030700076565204942040d40038481147d4951488500b00700818003000550307140000c15079000400c500d000c40d0345a480c0750b00d450040c10010402401a00d0014806003031542c444060900c031030440c408440c0306c0e110424104003501c020100117000350024001086158010005814075500c02030300505843c800713540302c41c0541449030081c8003031a07a40801c4145814101d00400c040c8500d0002040801d003030810f00c070f0341c0d05460600248207000024a550007090444010001040ca13070f0054211540c40c0c2c60044c0c0c0320b4204944c07550192125201c2d106c0146042d000d50f14420034161034440e0349a03005001d010304e400c2c42901020a1000e101115001600d0300d0308214441c000c0100074040800800c1c0504041c0c60015080e801c0051070840480020940403600707003190f04040f60000380c0201c01e0182078500301c0110380c2788952020810104010701c05413090180c41140700304e40c00c0015076140400c000c1c80703000084032154204070612414000d80c49950041c0101c15 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 25494718 1250 25493468 25493471
    0x702070b0d0b04020313030915020a0b04031701080705090c07020607020d0c120b010302090604061a161707020f040c0504030602030408090402040305030a021903080c1c02031006020c04050c0301050d06 88
    0x2d400340041000d90f441619480244204001d14206050b4002d15400c0074043c0b82110404194812800956031084181c015003040c0441000c2005c04d409141480d2044200201e442c14543e5146801d83c0c441d40d05225107801645a130000503440f01c0901c0458203816802480241030030442d0302400b0700c1c0c85001381c00300ea403c800070201142c00030790790804000071403080d000b15001c0c3d030652051241240016100b940500e003800b00500611294038811000c00400c036805030b4441200070303154410440d003848041c1c03c2c04440f0480ba00032908100040a402d0700941d200ca40c480d84c02010322003201d5898130300000040003407106200060a54000719081800b031507110b81020b500800050490307000780d008907211760001030180c15058060200fa25048604401c0d26080301483e2406014028003c120340ea120784000740100c000342c0740c0c010710304440c1c402c44021901d80c80e00c0481c02c5203040480c0901c1007d441018043d003072902d000d0280d548034044042849045034648018018400d40380642100c206 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 25495968 1250 25494718 25494731
    0x9051008060f03030c01090c1e030f03120234050706120f020c0606090a0501120b04020d050a03020d020f0c0307090b180a051006020d0c0305090a0806010b0c06010b030702070b0d 78
    0x554007000506085100c4000008421287d0715000000800540c86504d07070340e1300744403100100541c086141c02103d4215049811182292608488904403a441e48007540d2000c920305401360f03918441e070f1101c0714100106468407051650260701c4503280340802440b0368800382041c490288982c59409000c1f01c0454045424281c3c0b000740020f0303810180888405a1100341040034510340340e22034540005107100204019410984070380c1059001c1ca40140c03001401d00d011404640343c1c641c05007550742d000707000d0b140040305034070340251109051990318005100307a81d8000c00c480c0c00468400800d1100030b004001d02854495180068030701c182041d03620150101c5038181c807042d000e504034030a035081d0341c000450780750001b8503d1200045402c0201154000c0411480c9150045950002c140d0541025034403841400700042c088441c40d080b129850180800004d0700034003800113030800c514240306982c108e03a29403a44071440e000454501c001a80100410440d426054000305030790301411002160a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 25497218 1250 25495968 25495999
    0x603150b0309010c1b05060a021c02030f0a0f0b0d0b06030703080a050306010930140304030501020c0f0a0515070e0a03030c0302160501052709040507030b070905100806 74
    0x10350300126407101d49651240401c0d040540c0c4080882100c82010442d036220500ca5140c1c0c9076205002405140d04a41c0000d201c0700503004801110300a00805200350759a06d0200c0c11580f0085060310b0756031401e8140701d40b80170103462a005803100400082d02c030300d09001c10344e00d9419903440b0107000d076900b5006400c4040081802c4000800c4041c1503901c5d4140d89080c03c07400149212090b03485614440c040c203200810809641c03940c000d010100c9010413000c4809070400140441c0c80d80114466848006000010440190040c1010210240c15180c10300050a203079034840c82b007100000e2440d00540d403144950b0303102c0300d00503410202d41d25181030031004000105540000741d0300140c0104140d0090307101090f070704210707400317440207a05030140d15107103802c0001c1c06078020002c07450f00350443d40440846984240280c1040b50b20b006243c2d024a0400d030402c985c41c0c5002c3d0100f40c64900705e10b800a10342c07500600302601110400f906001c21482e00c810100c404030000341c0419030003108118140380 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 25498468 1250 25497218 25497239
    0x3140c010203011e06080106050415120204140a05060c070b0c010207200405090c060d090303090f03030506030610060c060b030a051615080907090e0307080301030803040308071701060315 82
    0x3805001c07400700e010510582e500704c004210390344030008001c14000180503455004096a0407500c1d00100c03c1c40365104041d00f62076480c2c2d040c0030441d07024404a0001404400803c1e01402c0340310540d40080d4040d101d1040c013000e84240d040030a02540014020001d10b9100340003460f00710030740d0300018200b503c10766a41000072240d46440c6520042c1d00900c02039454a8480c1d2a080607000c070051949803403000100d4050b0003401e038000401951204480240f50007900840c05544d0f2041ca1401c1c1c80e040c52501400034082902c1089c0039210761000100440c00c80d8139404181c400a41703506002c540a56202c82c0238045031070069405010f210704107400030720108030702d202103103e4484400d40d640c1403038881c112005c0c4042c05482000740301010302c5080b00e40410700000381e518845007c583d5a0500b1003403880c520500c2002043d6010000c000001e1041d03440165002d03910a56070031034a42c50701c0f0307821900c0d81c2103450030a031003410603001000803038001d038030184500301c00d02818040c05503140c41c19103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 25499718 1250 25498468 25498471
    0x5100908030a020d0e0904020d021011010e1006050102070b0702060702130f0f0e0a0209040b0a11030408090108010603090209150a0b0a020a1103031e0d1d10050105150703140c010203 80
    0x20b0250b4007250b40c44c009540c0100000b08a9101518000080d1800740c0010301c08450744400a405170034400f600b5a28207124480480f07159030b4140c001e021201840300c5c060350b9490710095034000b544c80d02c040400d06610204c0d81c0320488080c0d54202d8280f007100e030208040b0ba03000000480e4001381111400c0d4a4900900030350342c0904142c18001101c0c40b0303014918013903c00c0e5035200c2c8040d40000c44600010384c1c0b48507040743c1013504150200d61503512403403114020700803191a142c004201100300002c00c9049070081041860a90321003201c1d90b603a89003503050740d05d1450000d51090840c40000e01d012021403510041d0302c03008011080c0700d640e606880b04598060110b00b001600003107001801d1050401c040001c5100a030000d5142c100c07842041401c04664090b80114880001102212488190403242d0002c548101c0300b8000091003901603034441501200200341410a00001010300e0011150801c0304002e050280c0380401c240d80c03c0303074030500582160225003028450034881d03071424170145 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 25500968 1250 25499718 25499737
    0x5090102130503010c020a06052e150201060e041202010b060a090f0b0406020a02090702070e270a0507052701090207030206010e0403020a0b070c050607210b09010510090803 76
    0x1a80c450300300115014009090b080140079a05001c1c60b10b01d556070000f5041903042c3c201100054903110040c3c004041c51281c6015000e04224444190100100078402e030b04461041c4250b5030114000a02a800d03186030b841115101c3c403020b00000c0201e81d4000c140e28050249100018504c142000003a0403034101096000c0052080c01c001e00c111610f10050b04d01516203c502d050034103103030400c029910440803900a0282114801244100d4003c000210240182d915120746c1490542203c0301441e500e0031110104020508114020a40104030b81074260b820002030b088107401c00741440315a141c84000341c0300801d011100258030b115100c05040c0a001206009030361001c0c142002481d051060300b088800d003540009200c00a6000a82c400165a0060f400c803403a50340d0352003c1c3c1c4c0015811401400078000c400c200481c032a480300641d184605200c41540b02c904045248504a41813608103030b401142c4500180814500a0802c224041385031034442e00103616500c04170708682249000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 25502218 1250 25500968 25500971
    0x203150a0510060302120a27030f1b020a0501180506030103060204050102160e0f0a020f0714010e0a020612060609031005060405071e080718170c12031209030409050901 74
    0x2d1014020070004508014909440c0940c141125408105000382c4064440d000d040d90351040540c01c441c240d6054a0848004181d01c2d200d00703801e0401508054110b02481d0019410848003410301000d0088400000d40140817a1481c6041100540c1c040000104800144000d000c1c0002c4541d00c581c01540618890030000d03032038615240c0060703d0140d01421100000c06040001e2001140d0b03590541c0c0d10410807002100079403034200418001784a105150b89849400140340b006010300c0b0164600d240c403e0340001c00c1650b19890a031a12100b02d000d0003075002600704487c1030b000e18000d80703168100e00c00409080c0313011000da000a103030445440070f510440d501c0f40c00300185464144580d030f50194940c284100554008480088010180d015034024080e0040c04540d40c58030030201203092200d45c0b034000203165140e500070441400030030444050ba12400d1340041c07040c1000c102d03442c00c1e20a450021800c0150202e405440c00c5001440b08150f8030060100149104c0759008190203449150300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 25503468 1250 25502218 25502221
    0xb1816090606030e10020a090504090809090106031b050d06080303010f0303030b04091218052218030203040302120c04050a140601030e0606100e040204080d0f0e1c0203150a05 77
    0x6016a40a54000e500f41450041115002240843e610166011584005950349020310003a1240c0300030343c010540041c9403aa21104020307402005140c003041c2190405210783c2e80f03200c201c081e105058803014003a0481c1190f4518140180043c00169010013030100e610b644445415217190001d81c09480c82100c518010400d158240c071901d00304d0b100c10342c1e090140780c07a40c0d221200049540c4048000b004440001c42c62841d034022040c03405000014801d050048005992003525101b00c07000103c180e103011030071404060410108250244c0c190051820145140c0801901c10030203005412240071f44414a08540d0311441600c1c031800c0311040011b0305101c01008031205682c010005418503160088120209000090595201104540c04c80d042c40e00e0300b00843d00c8071410a6010b0b086400807031b010074500000300c0e1341402e40c012507071900110031b55030344111001d14580260300d4010f002030001c078014150b40c103c16440540080d0443c0d1510740461013025460008845940016a0300c0c030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 25504718 1250 25503468 25503479
    0x9051216060905012421240b0406060302040518060303040308120f06010206060904080306010c062a0c08160809030f06060a060f08012606070305040204050c160b1816 73
    0x240d10705c400d030030a05803100f581095201e03c2d0b92880c008450801c100c20403c04020000c2e460341c074000c0c00d000c2c100445044004000510042c19005001c03501c110305140c40858034510034400e580446400801c070314001112314503480c0c0c0710341004e401c3c20b4050004020110104a0000080440c0c6031402d6072903405140c02c60a032644440050425070440d0000070900015584d02c02d1104d8206401950b031540e070707448881c011b031402c1401035002420b80341031800d4503004090400b0024112081c1d407600e240e52a5880c0012135001c1502c0d2002021298144a1b181d41a00116601c1403100d00c621056440c20310604000ba140c000c07440c030f028007140d10210170800035060903611280101200d04194141460b415000f81202c0c505000e138004901c100d014014440011480c0115807000c0c40080d20316078146690014041d20b01204c080c0d00a50500d808605c6042009c3c04981c40780760741660020240c1113690f43c0c101c8005000c1d00c814800c50b01040c412504600900003111049084c000511640d031808 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 25505968 1250 25504718 25504751
    0x140303091e090601030b0105071b150306031e02030703080f04030209011e050f06090d020f040e030301090606020307020a03060f090209010b04180504110108070201020706061202040e010905121606090501 89
    0x10f04150405003082602c0d410399820000383c85071658040785e1454022200390220f0040304140d130141190219044038000d00b142c150b80110300340e90260b15174010500c840a0900368404440f0802509644504401c101240581e8003420507404201407092900c0d5a940009406800a8106402c0010340e107000d501c0040d001d081d41402000c0c25152620b0500c0001c002a025010702030700c440c001e0358040708100c11550f44a8091894120082040155007c500d140550340d40007401030340b080303901d40100411a240008183e43c000365006002c1000203086988810151480c03040e600c003925202c1d024200160340d0514101d01811080c0b604c643c65614260f008000700120040c2854038070710700300034400400c03000b0704410340448083c28a50340300d481c0c0302000c074028071500701c020b00103e2034102c000c5010002c04c103107900c5c00c038022901485000c0002c0d007201c2c00c032260818010720a501c078000c1c040000c041c170005880300341c081e2007007001f40302903a8170f940003550940c450444580e59501c01c0856880c442 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 25507218 1250 25505968 25505971
    0xa030b0306060907090513020408010507080105030706090305120f0d11030915010b0306012001020301080a021003020a1e03020c010501080a14030f04030f0f020d0f05010609021201140303091e09 85
    0x103e95045241c182040c0190102e400340c01110b004960040e036504144c0d6103034040328001c220310002000a4070b0000c100030841c410030b0007003e100b40a441c6001030301c2e074451600e4a0070760340c000c409000801c1c07220068034a258014032002c0c2e9011014444400072304850301c190f4a1941805840035524500f4a2506061944000d088030012445c1c2c0c006101d18000388040d280c0c00b61081c207081c0b044240300991014042c0070f22804191644c00000045000d940201e000b2031914403d07515040803c011035419410380c020b507000d41c00010100507810303c8024030210340c4621034242c1e0a0052500498440490945900742c00c2510343d9405081924200701d070b0002440070b110305036800b440c01d0120000c008501407003544005800c0d41c441100034000e00c020b2400d4880082d42c02000003002c200146056644805803190030b55444d480e04000042006a0b03000b11988135030039504194240e03084c03d1402550034180c103000754051109100d03c1803561910f81c42c90070031145110342582503070320210411484500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 25508468 1250 25507218 25507231
    0x3160e03150f07030c1205130c030609020102010b01110604111c0506090706050f0703180905010e071707020c061b010203181002070f060248010b0a0b03071101020a030b0306 76
    0xb9045c0369503400c40c0d20152140754509a0180400c1a480b02100b800c4102919180542580e8640c5400810011b495003c42140e610070f030000c1c0310882080005482c9c181e5000f24042260b0000070004000600301003072511020001061b10515004030a507544010701c400e8002c13541640104140041e5100c03c21240d4002c0070301340750440c0f503c4400ca552600074011000000d044c403442190f00111890008511400303020520410801503945100d09602845c0540d01f400100703210301c0b103200e00701c0c60b0500404d200b01e8058009099440e220400d000b07083d44034503040d000400c09107624180c881400c1c00114098002c0c01c0140140e40500e0042500b080080c40b500c40440384100641030010b00b141c03251040b500d4100b0380060f103400407001d030004515a401460f885603c00341641802060210800103100d01148600003000224103501d03d0880c0c08080956a0002e101501000a6800040110741c00007292800500e017005605555080e6086150454046030700c64201c00340b40c0c00d08000c0107505c0035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 25509718 1250 25508468 25508471
    0x506030f0d03022101030221010605060706020a120501080d0c02030109020303070b0105120604031e03180308010f080106121202030c07061e0f08070f0c081201030615030803160e03150f0703 83
    0x52647e40010002000c801c80341d0b46c035102484200c80a80401c1d03108000404026003c140d03904c0301860294029444413041d24042103419420500c1802607100d40390682e0441c0000340107104014030305407001c5444081c100e9140d034848031101c0050300c1c144041d00340148103450740041035042c80c0400908100460f00041c1079400303c010000480d40c030000d07220504030800d244507040259840100c02800340c07840c92180004032444d0300c1040503806039500781202e15400d540d80c074054480441509840080c401d20740034103000c0160601140c20714441220300d46040c0100c03441e06103081e04541c20901c05500909c085030740d42801051052403500980070004051500341025017005030080d28003070b00901490b0400060340d440800f01805480d500c2c1460f0f800400c07494807607020450102021b5030034001100c0e03090420800012101c80c480c5080d058039444043c01d4210b41d64655060742c41c45403603114404025004200c0801a1000d00c00103650044540788103119160000300560350250143c074072010107 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 25510968 1250 25509718 25509721
    0xc020105130f0b040c0b0c06090f07030305030c0a0905030a030e0f010804260c0f060103061401120b0405071a090108070e030c010c05150108030d050702150103060506030f0d030221 79
    0xba1410348041c1200b548601484802c2c2c8443c01c1102d25030f4040e81003807000c80c10000e0520401000050902e200c0c245c514101d8484551002c0b001c0d07103c812906c00280407c1c0184041000100040013500b03030319240b403401540b295980c80000e49403070765894050300170482401c400d00c841e0a1808440f0003141017801c1401c03140c1480d0f0b84016016160120000b0b4101c01406e03058003566040c0c0803a0b004000007c11214a860785a9100d074842c1e20a2100300c0c0c81e189803582038025000301010b401c0c101c402507001000c0081407a2946d031250240140102c5c0c45024400021401d911218441200c40b070440401c0c0340c650040900141526001034241d400740050000c6003107075035a0020340c20715002000e20700361011021914059143c02c029000811a884400c00007062100c000005050104014407040c030440c0c030b03503500980c0c44030002541ca4255551540041c000b10380680c00c12504240702508407442c1c4483e00e012113051480982c0b524002030303000212103006054000501c203d4035100144108035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 25512218 1250 25510968 25510973
    0x9010f0203160e04090210020d1e0f0f020f1f0b04060506090d020d0204090302160906060206010302010e061204030509030708070e04060c1e050301090c031a1203090607060c02010513 80
    0x12001d500d0b8002003045410071a580d02c60712580c000300460b5902400340e07480a21659806034440040100c01d0001070007800690740c000d82500103103000601140c5039600704100d00c00040310403404400d0801c05600c03510000b0103520717404004104041c08846a11710464161004150035184282e4590b132003281048428043c40e61410126802e5400c110f03800c103a00081e520102c0c81c003084014000c2d603c581f6100003a0141900403031800501a10b80d15071045881c0c40300b0140003140d0607030042c0e80050303000c100140015406402482e920070070003000c0c2c504150348c0c03040f10132442c2402c4a084002540204180c030076420304200764800380c20120017a001c4c0504081042e11285401400506816200c600d0200d80c036014000c213201c1805140c4059818050541c4068101d6000303109059141c0d181200b114110741c401c1c4070b0f8070b92b443d80c80c500e0042011001000c02c41043d215440214082c002006280199581c03a8000e160071341c49810302180c41180540040d00b1604020701404c0740d0445802400700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 25513468 1250 25512218 25512241
    0x501020f0d030518060a0606030b060301030b07182d061b0f060b09010e0702060106030506010203190516030903020f040207081605010b12010213060f020a03120908070b09010f0203 79
    0x40421a02d0001110741e00c070680100018140388041100307000303600500104c0c440c103800000035101c86071400c0c400f1000303120034002284800d1101402065801c004149128811211035403e0326510001c542120340314505211200c08500010600c00750381c05604504220782d01e03140c40203040305c1c2414410b002008001c1006803008000c01001c1c025a07840b12000c1000030343c0310005024014200e14a2581c43e030103c1c541030802030f5411303005403160000000381765101e80a000c0c481d0f42d06038083c5040110000e51380598030700b0098000203000007401009a0b15490003450241c140c003c0d541c848001d8994018440c41c40e80241c080c0c2e01540c01080b09002242d60102124462480c0c1156028219100d00b8030500403d580a24103500c048003207010990395605402400144401401465103180c0d6024207440c020044a1802d015801410541c1e0105c1e0107090300160f030142c010404680701e90f0036603900741540e00a58080700c110403008144854401c01748a00a00e040401c0710440c40c508004100c44c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 25514718 1250 25513468 25513483
    0x5190605090316030302030d060b090607020d0f05010e0c0915030c0d030306050405010e041103011a01030c0306050a0b0304050706051c0507030b2d010c081b03071b0f0501020f 77
    0x1020301400141000710340d1010420860054014000120960b0316841d00940740ea00038060b0100e0300d03041c8003004c02c44183c11801c03501380000040181d840e007101a801e112039407504040a40d51f0b0f030605292140803a50030b01440c1d070000c4581d0040c1ca1b01c0002c036010003d40200c040d2a1310f806030341c240414403164030002014005070340220703041814150103240440180c4000e801203908182843c00000311880b500d4903050185101d61500ea02c1d880100b0b09143c00c0300c039024903140490701c2c20680d009482d40a03503c2100984c81525000c2402d90311180070034004c0c941903100f0304045400004000c00c1c40800d2007001c0242c800b5203006440c000c07902d4000a0a01007507000c014040d562500400c4000d0700a502c91485000050982611038054038840742250791002c02112000d010f01e19000c40a602c955161b80c10140d0010f0803034100300510070101900c0c03507540404107151004102800c00308072031388102c88503507805050484d00d50341410140004d0f40603643c001c42c10b55000c44840c110071200030400382e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 25515968 1250 25514718 25514729
    0xc02030604080f07120801031416050402162f0d12031508010911090c0901080103080f040302120601060201060b070317060102030d06030c1401090f0b1c020a0c0506010519 75
    0x1944032507101d4071500241c81015001024210103507a10032485c0e400c45201c4c0c1c1204c5c000e4295402c800e18a010440c5c44113004040c02408000b110000c0c4014034241d4086c14021201c019030104c1001d150f0745022a200050155140b561070100d22105da822588a042203c172506070b8181c10906015559169011003000c00c200926854000e0403180400c1d00c201000102824002802860310504210010044061205024081d88030000b0703d0860f800e41104d4802c001130f510303440160300e103445182060304690310308821800f040000201580d02e45141c4180c501d02d200140815515010b03000e82100e0940d403244407120b4082c040100400c4c3c200139041c42411105a005c12a42c0d1400e004031f045125100701d00c1e07015460034101000340b000c1100403109407100c8aa0070840d0343c01d00001919201c903036120301c0041450301e24040c0302030064440940203103040c5401440c0486480e41c0001c080e0f030031500901c40000c000d034082405000c000c02004c1d00410307040c1c2e0070351960303401460803e1110506020b00c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 25517218 1250 25515968 25515983
    0x11040e030316030207020a06050c0f1b040f060902030c12010501030501030f0f03140d0603050f0609120d09080d0b091501021c020703020303070303050610050f16080c0a050607030c0c02030604 84
    0x39940c024026011600090740c001c07c41da500b5074541101400c83c0d00039200d4000d1910508031080d13014039000440721021030300c1c1015407160243e40000c01000c1c012048207090000d44880d8009400b910310f001031402080d194160070385500c2e417030030301d08c1000f18141d200300c0c105420003004101188500c08070000e04c90b003100c60600c800046041c20303901c43d0f1442800f981704000001c2c8071406100680e21400590344948103540d03100362000402c580d5510203444404494010800ca030340c0031482d4078010031405000410201c1c102006d41c4a4074420f810820b200b103030050320340e40008410702e82919019807000c0c0200c101c1c0d42d040324000c0001c0d600c0c80501c0350440700c0700c00301c2c01910003d80208400402154000d04895aa51807860000d024090070f50741240608081000100d00501500a541c2000f02d20210141010015000903e01e8500c01c1070544a518003000301810b180024004800702600400080c2224188520001d04642c151102003003040186921080183c0d404100c150704690401c0301e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 25518468 1250 25517218 25517251
    0x6040201050306010c06090f0501020903010f05010f171501030c06080703020a080c0c01090f110117012304060504020a030c0e010e0306011703090d12080c03091903050f0c0a11040e0303 81
    0x40440080c8513207076014054445101410080010540080c582d8338801d400030b202214111009a05031341d0b0a0203040c80d40d0b26510340c00d002000d00040c200744069800c4084034048108030380700d60000142a041656504000f0605000341c2d40c00403100c3e90060520b1800710310b8034000d00002402e202024003820b4160000040640c1c264500b50880058290003041c0c02075441107a162000f04007100c11846408500800600c4c41c8001c12243d40d03d040710303107164210803000100c0c1c100040280d840c00540742e00994900011a080d1914405855118032a85000507140c541030b44c00351201c81503954060406c00303040034401c0240c0b40451003504442c01700c80040c4000c4040780d0901d0840c080d215070103400025800c0200c05015407205080d0311030f11103071122401602d441030700422a10044a01d81c140f903010040b51812140c1c900c907041e0a05019240075400c009000078400800e500c0020310300c80c1a8440f850001c2071141c030680000c00300b04101c5040101c2c01c960302034103480c0c0c000281000340344840d600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 25519718 1250 25518468 25518473
    0xc120c0301020a030203010302040b09060319020114030112050705060f0f090607141f0c0824031006060206130302150c1201060c0b1e01052e08090f06040201050306010c 74
    0x80819604140200255120340b80f01030010b0094209210070391195040c00e1030221142007040360b40380240800b4000d0301010383c200c0c9070414403a1030300030100e04004010304090910b1001a01450190100c1040100b503000e250800d540790031a80d03000b50344244800c00910107083c03407507011180d03440c98101c0c185844101c1400040e8850007144806410000341c162908942d11000c112502180d0130100840c0c0034a50505140080f03410041900380446e11038001304240c0c130644405080c104520249510000c244c180c080ba0908840c08200d2900e00e8865605100301034050080d20360082c0319405c0e40e99040d01d146c500950750003407610040a054030620104110100090403070300154520161410a543e460000030200c03103200006451005e090340104a50008030030888008921401e0502051390901d020081c00c0565548044004070200054050688000340348082d8900127071240d03030b25450948805800d000e8140415091030f0840d2081000503a080301c2501c1d00540280b81900103003c451 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 25520968 1250 25519718 25519723
    0x50603100908090a09020406080708010b180f100908010608030c0303070e03030f1305150702130e0a02040608010c170f0a020d0204031a040611070506060409020102010b09010b0403031e020c12 84
    0xc920b03640003004e4240101d02c48015400800894100d035940d24000d40e101c8074102e038202000c0c02070310710032070b010000d110446800c00070210080000038400010f0b004c102000699407441104100e020034030030316081040308000c1c4111002040c400c0c1c069850b00071841411030b00e03448014611400d01004084144140e102082030340c80642500c41015501d005200c4081e031003010074800c00c0e200385c21030641d01c00c00e02c2c01b400c2591841c40c1c0c043e020b10854440e41c0821009408204038425051090000950159490f405610010842070f4000140b10031103403001401c480c071842c00d40b442c0c0d80558051084001e200a48664055080c00c3c0041e241c040704003420700a48070715071018080e8051145580c0d603820460382581c0c010b034440c240412404110700d0034020107002c3d44c40d01030101e1b002000050102e003000d400500c6c3d05071051000040f0f8044c3c80340025440e402c2a003145614031008079050041580200d002aa03448429000343d103040400800203540788203002882d07014201a0013030306000f00b0704 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 25522218 1250 25520968 25520977
    0x4021c0312150e01080106080c0d0206090f0102190f12030b010f0e06041802030601020f010b01050a050306120a05100c02010207021c020112020309031c0501050307060804050a020a0b07021003050603100908 90
    0x1a82070110f815603691100341c0c06001180295409030040e012400ca2031b00e000c840303070303510154041c1c20f01c2c1c1044500010040c0c2025012551415400344480700e03124403620101c10290f1610800c80c00c600c00c0460300380f0140e207040401c00481814541035501180b6a0030000110144e0054648a0032140d07401020070f4a0340691761044c4085114050000d405600380e40142d0f2241200307070708903640551804862400d890051031240e0200e0350800a5985407441031000315400480540100203040410b21854903065880380c0a441e1600500e030340c00512480c60040350400031141c030095003003200d15000140402c241700414084d8a03000301a203021a4010001c1c40700404003d0b40440d100c3c904080f003144c803036000910940c0c01720b1321020341700a5400d2070f208550580c0d4014008014060030243c2c151003406000c2c0c4150b4003403081030345000c01a41c4074242c4401900381600c055850303000d02d205002c1e01414520500d800c1c58105001c02c003c54a0000312a00142d1841b44046249680c0381070140c0244107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 25523468 1250 25522218 25522229
    0x20f1c0605040c05091302011d06160501050702060705040509060105030402012610050613060302070201180306020d0605030303150402090a091506080c030f04030302070c050d0b04021c031215 84
    0x14441000b0900a8000d948411a0020f40c1c0840c0d10b41e6440542d456099010000240820046488140d00034611068000400c0d000360002c2d01e404481c40380c0481040a0b10b4085609a4481e01005401981070200981110550034050f0609040c00d00140d25180c2c0107044604209012002405580c07103144030800072005020704914502c010740c407800c220202212042d000d220584000566410050201d500c0022451103c1203e00d003000340c210061360010314140e041000280020154181d0b45017108000d5114840050381d0354406410303d002d031a455070000c0e200f90401c1c020000504820410f03405152000c07940165213500600020b441c208594000113101c070b240180e058440e10050841405880d0b1603103c0712200e945880e115941c0e44400c03901c021840410b035004c200000d001e600580416845011b224120703544440104541e0b020b0048166000c02d110b400340402e5060043d1400407256140501e1881303810140c5018160b18925440081c80656420b00f142c040940e040300c1102900703 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 25524718 1250 25523468 25523471
    0x3031410050f01020307030206150105040b030f0109060f1215060b0408250807030f02010201020f0d0f060509010b090d0204020c010e0a03030b010807080103080705011e0c02010f09020f1c06 83
    0x4000104445044050180074042c805600722800c42d58000002d8600856040c0e004020603174404d4030039800689400000c41c140714040c080400e158801c2d0f00658843c02c240100030003503603d800982c00c1500c8440d444400f00c5e00031a00184108071420803060641e0b41c00000200b44c0407003500c04103005004a6101030300b5208040f40208220070301080d0850f084406c1c0000f03178808407541808841c0c8103040e02c90881640e000f05010400103402d10071050400d80140001410000403a189a940d584514100c1450507611a000e032510700e01485180007908003a54802029814a1300c000207601c10b01c41901c0c80790218000c09000c641d80c0e0f03011a581d03c12210002d200300c402c0c01307100903034456503030100f01d01080c10114003102035485041507c0c42882e00e41d540d91541c1e46103840ea00c000d9401000d05032015500d0703990482705030200c81e18940d8042000350740041c61503940c820080c2100c2820780c0201813141011000005a603818410403000501296080e110100c04074644c6e405100603080102030b40e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 25525968 1250 25524718 25524721
    0x120a050318070f0b0d050a02090a060f0309060207030c050f060405070b07020a120303061a030c030a0903020a050a05030301260307300c0204050702060402180703110c01090309050a03030e040207030314 88
    0x3040f20015115685c030303080d001d104603103803100000240d000303c504036904989803080c1000348610400c446c4654a00c241070005410045841c2c0301c0c142e9016140036008604040c20050800904121910040641101034011070030260b0300d0b81d85600c01841003403200c0202081d15815035a07601c40440040c41080003098260007645009009007030207124020502c64030402026807241d16004a910849601c0e030382d18615a0b030308241d100200241802a0110310814841d00f0024004208051915025030015030705e80d031406100c0760315103409000ca0007000d801c00703042564050002040d264507941c81444901034001c92260a1502040700c1c150346103e0001d01d024480644e0072000070301216000b99070a105680d555a02030fa0340300020b58000390403440c03140740307003200481081e4015005102864080b0f14401c000c03296413156000140c1082d03540e55150900400c164000c03001e20b008001c1130350313010021807454401400a01e4402400d0340580d800058640030107109502c180460440b04161102130b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 25527218 1250 25525968 25525979
    0x1020f070305070806160e0904060b0405041a0709060207170f031303030e0f0f0409140d03050f060904020603040b0a0b0d110306010f0b0405040b0d050109080c120a050318070f 77
    0x50fa0050f1007410301e14080e0401007100e0000503440300304031054644640b55400340306401c1c4904c05074010400c1c0c51840d41d6444010b001d690303030702840f070056001e40414002144150310f20103212001071b00c254140180b4150070400c1e5500801d414040380d02d01a0140c146842400145043c010180b1244801e4080028002840e0b1103180c500d00070307203010b69145021041c4241c240481341103100e0341994090111141c0ca441407a254216404c183c2c8500032450342076001d2212680703465440c07180100469210402c205544c159074401c01d9011500326a0010517062a0700404c90500c400751010304144150000104100320300d4000c03c18042c80508031405861081c00c05d10182c911401209110b4001c14000080c10303030b00902d1b20780544081003402440c0900c1e00003007100903c81c245881f50400000c804150100d003080c490804035a000e984804d5031a04144070190810f0b010402088030108284000c0040b03503442130a0341e62100400c06403024098401c10030300d00e0614a0b5020321101041c0110210f031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 25528468 1250 25527218 25527223
    0x706050112110102060c0d0e0109061505010809060f070503041a010e0106031b0806010302070c08070e100602010608061503010e060403020102040603060e0c09060f1209030901080106030212040b0601020f070305 92
    0x96180240002c4980145001c01283c4441d820780d01d1900103a4180183e4039111802c2d4003121040d0642400000c50303a10036039500e002d5030122143d44240100740e404c10800c950700540e12680c4040000c0140219240080505081c0440a840c407810040c000c8002810410144c0400070342d0904106110107a41e5942032074a1100002d0181e00000b078240219290000c2c9040802810b840007903e610074035907a1800110004e4001540560b0600414640040c89000622940740a0240040003000c9841d040c0c241c1c100314041236119004681c0342010030004902c01003001500241c0c41860420303043c44080000e0f016010520040010f800344606000805805500801c00c83d034850300c06104a03a5035004180d61408111440b0004190800144d0340614150f0000d0031044140c11805044c001d074000e400d150031004440b0400703682e2000400c3c2c913a540e0030980c4903005218914080d85001178401407030f01e2400000d07000a15100f802000b05000780c2c024010a152080408102c40d83c1d1660fa040095 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 25529718 1250 25528468 25528499
    0x30503030411010c0b01061202040b0d0e010e070303020619020705010c0305040b01090e060c032e08010f060b071101050c011e150503120c0703120206040c0f080c0f0607060501 77
    0x1110162100c40b10302165004402903220943c100f40120000da2034a5015104185a00c45081070540c1c20400452500031031800340207008495031002a03040d00b10545103084030003040c1d24a480d03a00c50001040080e50000701280c0c04001d601404048400b00e180301c030302a02884500030f11035401e100f0a5001540d06512851199002e22480d0482d642d88080f03440c11503880d55403000041d0444d400081340e03084504020358001c9104c80e9103003661000e80d29070044252042055807008690000200b004180900034420002c040290820101c1d1070109030648074030440c100148010f402944040450303009500760307402194000c000f800000d00c900c1c20455050645200c90408910341082d100c402080301120384280d80d4090000d00650390101401d0b080340c0c00c48005810f01d4461884044000340d00140354500c0300030b26400030b21990034146000b401031512794120140c02c1c041c508003041100300004503006070394000c1d00d20910b6400c4041c040b40c854403441d080503106600305000050700001c0c071f0f235644 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 25530968 1250 25529718 25529723
    0x50103080a120e070b03060607020904030804030306080c0109090b13020406030605031203092d0a0606080f0a030f051c020f030603190b18030702120c030c0103090b0403050a0512010305030304 84
    0x2a804002d88590440072207080390075001082e8840b070014442c80410b54021138100304028a81030030003810b6030001d00e201c40100e4040300003900304400d201c101505802104c000e04806c0000d0260641e01900080c106001c5224120750300d6141d60041c0c0d01519800070419500800c24029951691a860040c000d000b9034441c01d0302921070010718100c030052800699008244020140a0301c085030306d040c000c1da0510131040010903180202c1c20034020303400c100900000e403082c040840d4043c07400c09183d00b0b01c0051010403003581c00002c41140042d5102e41d0043e00d0002e1801c00c0ca8450101c1030300101515140701007078845620000301c824101a40300c01862003000100c0c100c0f00540440c070846401d21580304401000c0064480205009401010309000009004403c0300d04222454000a0003050b82092415954000e0030780040941008d00c50401c500e00207080503c8080d115580e140301c2100010300150800c9030210b40150704d0b91240c01258540400001010346650312814807a45980c4180d804 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 25532218 1250 25530968 25530977
    0x201080604143c060409140118030e01020a0302120c010e030705070510021506060d0e03030f01060905010507020d23030a02071805010b0d090201030b040c08060901050102070e180a0204050103080a 86
    0x1e581c0403030441c003d01c9160214461001000340c88a0341400301611200c48103c2c1c800d504c910485c0706840c0c0c2440b8a5003083c4040105000d062000d0801802040c2c60030080c604642084010b031010a0300040c4000b110741b01078018641c1c800c55440c8050040c00c04a010070402d000000c1d0103c00c0c0080000d041e4103890045403102d4500c0310405050365a510f045103240070390501c41c0b000840c90300e03099024000f180302c900d00c0030884001d04e126050440d40120740100c0c111054a0040c02900e0b8044c0f200000f52000b03080c0513283c81d0140e0005407920070180070041842284c2050342103032540c22009440c0d0300712100212034413680d40080c041d403600c2c41401460300c0b039030440080721500340c01805058102d42c2c142c0070b5a490603540301000d2000d000080c400741c0c103141d100c48100b44281c48500c0703180c2d004005ca0381c0d4600c07541000ca040044080301030740a541154000d290600001c0d11000d8010b8002e01e2111031480c0f4503001e1094142003102d007001c042c0d842450071000000b0701010b40010000d40700036989 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 25533468 1250 25532218 25532281
    0x302070806070503010807090c1b03120b01030501260c1f021908040302010302030a060e090c030f0615090907030210030b040b041406100309021306080609060103020d020108060414 79
    0x10407507144c00300744a51001540441e40c05c01c030b8200c20303a11815150385245020750721190010311840f84041c0c1c510080b400155607041c080c464850503c21402040024039061002c2c1d4904083e07008002c04013a003031016418291001c452001003007040346000003004d41440f5091002280c0c08144011130078420000d401501544002502c00e0704111076555400080941003600310740045000b5080106104212940d403c000328141c3e80d9051150312911504008040802220041c1401d003000e41420282a92100041c402c0380c0e01e06140e41d143d400c1045d254503100b540c407011540d180ca4201e0307201940048215901c64410341d0b05401038010400240c0302802141d881800b8041201d400d100a120300c4d43c00100814000d180c1f8149c58904048103140200b00c1c10b9250300090080c01c8400f20190344c42d90340328002c0046040501166a10001c103030090140c1e5031564010802c400301c1403034000c0c1003015070340000d07520b50745030343c4000c40c03c84078506c060798580340040da004200708141b00c4045c0282c61451 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 25534718 1250 25533468 25533481
    0x1b0206010906081f0e070803040602010b09100308030717090105060108010608070804030e0a0b1201090605060705030f0f0c010f050601090f0f090c02010905121206090411011d04090302070806 84
    0x1410b03044805020050042411680790b1100d002c107844080d040e80d58403541c18007241c100401c40800500041c0f006180d0361894040c001c0c0c211105a00c1d0380d0f000703921034820055010f80c2c128242e0200c5e6000208075980e652031010441d034158151020707410407400c8100380141082e05510441c41003100303880b1400280d0700c80000b40c60401003201c202c1c0010f280c8100083c00240319603000019090080c06410703549032a01603510190b08000c40307c0078201e42c1400108140007030b50281900411058400c0e9150400548400f0b89910503400401001500080c0c07460350b60b15640200c609450b40c105c001c00012400304070402c05080f06460890004441441c041980e4a00000c02e034100c8034a4181c3d80c00e0140390230301d0540900030030881507082d03540c0e4141200228900b4000040c0d98521042c0c0c5c681c3c0c50f81c070240f010591100249c40d96010b42c016400700800101c070040452928042400c207008182c0d070700e040080c14031208031609034205052805260405400060b95000d480c03c000c04c1d80c0300c1e80e0b241c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 25535968 1250 25534718 25534721
    0x905030712110601120b0403120b060c0102030417250c030204050405010507140c19080d1e050106020c06070809040e07090204060305150306011203050d0c050a0e040c02031803070305011b02060109 86
    0x681010f42000c6c00722010800007805004601d1421104c0b00000c81c114100c200000c0181d04a49049005a5000000c003c20850100046001d8280c40d1070250306202e1741e110088980340c002242a0304440c000700101c024406068011401558004c00030300481c90149040c50213801c3c29142200030030754410502680000c035405a07200e20350391400402d1110300741d130b100884201607080c0540700c0340d6081001c801d000f102c42c0a00403510344071350342d0000c0303001026500f20102d420580c030403811504511404800c1d6500c00d41222561504444095107588c0d80e400001d00400391401549814840d48a00048140050f0080c1044400c25182009243d491506074035080000c11482c40d0f150b00000c1c011310030110741090410780540289089802d00d0004400d1204540d824a052000f2800106000b01080d0384100208e00e007540585040c48904401400070f540ca009081521501000703210203c45a0b441c1042014000c0d5003200013070200d2240c141001c24001c13070304c1c0195001401060000b250141c00d5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 25537218 1250 25535968 25535999
    0x301020f0a0e0405010605090d03030902030a1a0f0108030414011e030e0d030504110405040f06050108060105090c0703080c03090313030602120f04120302030c07050a030905210a02040905030712110601 88
    0x8071f4550501e415046402c00008921600c01102416525410103000d030700c0c2048240c044510075080d4480919000e00b01c001c200c000242526250000100180070a41000c801e0700c0440382c10304e1031840c203100448010396600c5c0c2c038042d80108190f400c0080c601d0099041c0c00218030f00c1003142c19140b9590b07140104a0583c1d40441c0c0c083c2c00310300e40c5400c00c461070070154005a030145c050000c4817441111640d500040d80d800b81e124480c26480000140720610308a070107190013000c0811030518114103683d0182c0441401004240c80c0000440000c1207400c05004a81c00c4880095580d824952030340703840b100a400400c2001003500d01d01c2c0009040300314004282c0d001d00d4110801119451074007104a0113580000d20318200b0050a00080000550410500000728841d8841d6112030313051038184940c0300345000c10190600720706251900310800200715600c41a40684011885107940e003400c070b2443c403d00f0307001050510442d8020140aa004649032144802c80d41502c0702640d0f54516081c014a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 25538468 1250 25537218 25537229
    0x303080604090c12030311030f04021003020c0d030504030e0402220f051c0204021303060905010f0506010c030809010905070f060215060f06180303030108030c150702070e070e0301020f0a0e040501 86
    0xc48505000f010b41552004da1980e10038500403c54000040303952020303030005c0c2c03031168040e1040400d220842c030740160b2460075001146030071401d0003410301d45c81d40c0e111954418441403564030000329060510a14407202c645001410955540341544c0c1d20386440b4079403010410040d0031140011980503200700b0b940040b500020807581402c0145551441100301c00c3c00201c2e445503003000309621100e5032130400c40056014150009006240d400c0c218207450300c40c050788045134541f5007000116030704003001d407041a07014074000889a84981140d40140b489039030107407043c415603400181540c1c070546808207482c40b603400c0d580f00e20b45000c1e00880c40502a00c0866218000d041c81c0c1d450303800e0240240500491514007841c4c0415142c0100e81140d1080c1c122540b2034200113001d0542c0c0c1d504029a080504500501e0449481c19100094946445010b1342031008607500c007050800b4810420880d002078018021980d40c90300c8442c080b81988603109e124042030070f00c2c90301c034460725151146a0481d071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 25539574 1106 25538468 25538483
    0x40c030203190e0613031202070f0c0b0c07120f0c030501050106091205060601110304081603021002150c0f0c030412060e0303090a0201030c0e031006030308060409 72
    0x550900a0188050600c8001d6040f90b400142c4140e01107851000444044074030320b401c07941ca07041c02e4140390440b4004030340780f01485044403170140601e104501c4e1400041e6551803240c07250054211840302c58000d034104200781001c4da004005014810080e1016040a0366039842900c000c940069860f69901c034014407030281c00040c0c02000e000d9114192920301000d41d0703620798038040200490704125a040c00c00407070803010415030303025111000660b10221501f61074500045002e01c000da110300d408915105109002056041c92403a031141d42816980d56580e0f24502c943c000c40400700e0b14281007000910f0840c051001e072010702680300002000413000e04001d001da882e54001b1442e241c01c200700340320349c001001800540003607080c2000306948164480640702c12810301c24a130781600484c03804a001c895194400c50940f88a84c0750b040850706c1d55424482201c2d02458000c1001c2c = true := by decide +kernel

theorem cover : BRFrame.Cov 25359718 25539574 := by
  have h0 := BRFrame.cov_init 25359718
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25359718 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 25359718 ≤ n) (h2 : n < 25539574) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
