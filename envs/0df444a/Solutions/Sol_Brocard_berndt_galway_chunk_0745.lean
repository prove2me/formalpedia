-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0745
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:32:56.390015+00:00
-- url     : https://prove2.me/submissions/1f29b7a1-016c-48d0-8303-a974aea999f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 133812949 ≤ n < 133992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 133814199 1250 133812949 133812977
    0xa0206040c0b040501090e090f010606020d14092b050d2a030e041a030a03020309011202031006110a05070b090307140904020607030212040308121305120903070b1308210703 76
    0x4000d8034150002d275402000210354541d0003031b441c0c603480020100883d8240513055081d50b50038045075035050004050070082e500c0319040340302d15442110a071044030200641040050070400041c2e220190303d440310394440503500c601d40c960b0510b4100f20340300c441900003030800107500450301246821044078042034400502c010801001401143d0315458450400b07154141600880204807a000a9030b40307802d10241007007000c060344000e488010300d0856051040044511540c81108104031590039a50350200c2c031340f98030f8548400e54000000010000032a0b0718145010000d540090810601c0103d4111980700003800511000300041d00511000541c0c804041c1b091013401c0070302c10043d070706d192100c0e140d083c4003000d0742010880f40000450303034003c100c00180d40070002030301c1c1c1d501000601c080d110304843c1c850301c0d800402c000c03078248c4100300000c00d9100b4044081c061b040d0941c40140b440c1413400b042e01385040d542000110020b000702496503c4803c20740110b641058040c18030703000868260f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 133815449 1250 133814199 133814203
    0xc0601140d08040b040906080d0c02060a110312070e030a0f02060a05070c0611010c05090d030c08090a030b0a0c0e03211c021c0b0609120a080a0206040c0b040501090e09 74
    0x84074005144520024000c075032086458090000d441d0109001c02401d501c0350071003943e41041c0704844002c14101c0049030010b20340000100398680c12480c00e811803420b0710f9000c61464110709103824200c0e00150420140e81d41c0045480b64505045008228030510754407032180011400d00d02078096400000c0c0c806140d4018000c907044075500034405100b0907503603500200903015074010060b8035401e103008641d410b4030640649640d40310040c404040c0e132401ea6400e0f520700c90381000803515003c060107420031075942c01041400646c0140b201642d0f03441c11801410403180d54050305410300485840c40d4503281c07000a105140603c48149a16240b0481c7c4113050300342c003459110300c5031a460011591209821500900740740c4a1401034070841d052404000003e0324800314101e0741108040c008402280340c215442c03030b003802141042c0c4039100c0050f2584c07032207a131088441c400943e10002c103000400c210680b49000a18000c074465080905180008040d40300600c00c1510304001312011a0100c401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 133816699 1250 133815449 133815469
    0x7111203030f07020f03030114010f03060503010216300c0507090c09150e03120d06030b0708061008061c030e10030e0c030303040c060503100905010e0f0c0c060114 72
    0x1201d8030781c50049000c1640e40b60480318800180a4240d8203600701000100303481c140c42c00310405180a44148004507144c400c041d00c1c40c070800d52682c20026041d1000c1c8002d0030500d8a851600145551030300340b05013005130000c01101080c0080001c48903140703003010543c0541c159481e200d00c28000034141a441c001581d081480f4051820042c0ca46503604205060200d50344019250025030500f902911000c0c00703041a260507030000403110100074800b4004143c202d40c1d2520008105480f41c48003540c1d4041203904402240c60282400f20078905004030111001e07091900d10b40501c0c15030701280f0009040c03681d8999103141c103a919420140070340c0c500710800c0000343c1083c125162107d030080c0a0061704001c05d030140180c001c51842da00303010045a2065400c990148103480c9001c20446440c0c1c0001c040405e061102e03040414140d5046c010303180280120324151000341481a090a4000710140012890031010030000c42c20b140003042e02e50444130b40741c401d6852f4801603000710f50900300b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 133817949 1250 133816699 133816729
    0x5010c21030506150a080f0703061a0903010e0304080c09130b090c0108011a400302040b01080f160201020910050c01060b07051f06030f05060703050c0405060711 71
    0x121003a11000607410361100340b04040450741c02075040066505202c0d90301c114003403038000820007000140513250701200a5003005140ca00001c0c5207030354200c1c0590321440140c10501c4c1c4500020241c41074034003406041c0d00148450041c510381303864018816904d4040b510305a0048011000185000c0d46909001c84495000144009646800064031743c840fa400d2894a0100d080c50001140d10070252a00030707000d2420340344161038000c681e0180c0000c403c03c040000b01c01807404610100c4041c0507200c1c516020400340d203901c5581d003540b04010955450004460412540303004000e02c0c0418040001c4d000450300024402000e0640022406442084280303600440720b040100b281540c00300c01000b0010f00c0c803000f00049a12951244803610680e08040c219511620500404548084040c101000440000540907940340c1d64200300c0954801d042e01c81e608040100031589816000e016481040e00890919060030b00d000038003103003c0c3d00ea0240c421020a850f854131a00c680049414001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 133819199 1250 133817949 133817993
    0xc030a210c080618090d0c0609051501060305010e060604030303090201030906060f0f080109210c02130905060a09330608061009020c07141c05010204210203030405010c 74
    0x2200c001c005020228243d6480e0300a000d200902d072032030746140080d540034a2480f40580460b00c0460001c80d01c510440005403602d941d108050400a0810000e1002e00d0f500112417010030740c50206c0140c21124168030105041290790b04110302c5039260300444042d40d52500300000d0020791800100c00401c12040700400251820344040340c161005400982201d201c0b400c0c00c0072079078850b8021030030380e80100300090902d0a0501300c921264074900380c000601401d454680d60786802c80d00014007504424544030380e85607451001c0340500c9418812164070100790703113041c4901066540c410b400004000b2001801510a01151700a500380083e0341b14600000b03d82400141d0b04c80d041d1544039601510501c05050340040c0c00070b900e1281d07009542c003040c00000909003251400304203401026134524080d40c4102c00b0a03a806111903680308244210303001d140016107960616400420140020f40014041000020254010307600002110b041e0f80080c1b0b00040400c0303c0d482e00d10710000600300403031194 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 133820449 1250 133819199 133819211
    0x3020a1e1a0a0c02030f2a01180b0610020705090a060b030c12010614030126010905010e01060b0c0709150807060c020f0105210403020c031005010f0503030c030a21 72
    0x408440039003401409101c908110384207052101382c0c0d82e0702c07603070b010140b0010040c008020340302c0810000e82200d41d1401d540f42c2c02e0014081d001400c43e100c0d401101c003481d18003c542002d0107180140c1e036502000944040c1007460b580f04002e0368a0020b44200f603c100a20b80020b01d607803006402c610300400f42c4c031a1072a181e041c1a4581d09103504058000302d11132a440703000007402c43c481c040341200822010950b030325690a102542e01c07082000055000180444501c440190409115a407030090041d000000c1c402c440c961040c1c02e440c2076510004043d00c3c28842181c9800c004074a00c0d0854481810004240415005000c82400d959008000e28011003070001550794014010f60819842111040d8402202400544081c0a6070030100d216200741040c010300c5e948a0031850750894001e0040340c07144480d04002a1078040240c502c0d400342511240104400641c6140c444090312003180a18108032641100a6907802404014030801031040810070b012041c0f1200e0b441c6803251f0103007d00c02c6d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 133821699 1250 133820449 133820483
    0x907080d0809250303050c07231003050105060f13030b0421020303070905090402010c0b0c090a05091312050f0406030605100309080d020d0b03070323060403020a1e 72
    0x1940d1046034205820f01400e004040c4501c07070300c4143c0a01100071880501110b0458904640d10b40150015003514412048081840e00d8140810700a007a8400b03490810b01c0803981c213010982d483e00205c141494205401030080e991007100360740398601424400d0b0744034000154040408006540003500c04c0c0611004d1000303024540910a81600c20010036594005030014101d0366407108030759040010305a0803050050740703000301e035050f0858014548013082c0078054a90800300801aa10340340d0000000500000c54182040803000038032080b110005e42c3e140c101d00d040042001810f004000220305003281c0c28090080b02510700420740c08401c20303129910340e40054001e14403030007420711611103020107a1042c1c0c824040c100102e42c0c00b11009017003030b245141a0b8042c4d0020b940a28009440e445915141d440420600d001035004400c0351248081c0501c07184452202158402d84d980c10071010000820740000d8101401c3e60300c02071819407216082003140c0c98a0740d0200040c1100d80050000b00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 133822949 1250 133821699 133821707
    0x15040b04020f0307170108100504080c2505010e0f060901120e0c1e011409030304030807060b0a0e01030b040308040206090405100302011202121b070209010306090303230a050907080d 80
    0x11081044e0b80b15442c01c0640050158030303a1100b4454078a082d880000ea1815030950798011755003051080300f540d0705181400324170600b060a840e00c841d03e1840101c41c09240c0c100d1910300300f80204070a08010102c00d40317942c08038135102c4400000c14007031040011000d5180e4410102c08010f40080c034000c02c1301c5407201d981c054485140c91100c074442e06690f27000e2894510101254400030405844010402c4003402c5503644e2500310704601031341800107000020204d0a260014001148590070000300342001d0010004150031680040c0c00c003a60480c011300001b20b07445141034105406040901541d902d91000a1044c8a0104050340050810040c081400d00800301c1105a80c800d880b01c5a8107030411180c0d50480c021842c1046043c4500d00c0030503600101e061082e034548103281c3e0400c0c58a8951380109041080a07882124a10783e5104602c040c1940b41c40340b040c4075100c81e008050a030891516007106a207000d090407d0103940d80000c542d11410421540703000340282c2c400c0c0c48404112040283c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 133824199 1250 133822949 133822951
    0x12030105031002040e0403030905070b040321020703050304090e07051203030901050105010203030709050d210504170a0f03081509010f030b1005150d020418052d15040b04020f03 78
    0x307402880307850340800040b0007034000e5078203540d42003903011105d5485c2d8900314054840803000713581078081c040012403020144001080610f000e2000700305200741009121514548500150086400040080c0001400442110101c403200031000c02c104d010000601d003042d040398059984200403604040c46d0940100140d0700c0b40c1420710007046140e0ba0760005981341e1008954600005003050418011441c01c50020b00f440303406400c01c060203160405c06202019403e2401d000401c0003c141040700c850301e905034002d01c562040107010052500d560f10005440143d000400380000c21002071003e40070341d00f82c03a000c9100101001c03150350b03441503043c02c106503900041d145042e440001444031510000e45d03200722100a4105480c00702960305030032045d080a40f0010029400b000b00041c0000040d9180b0f04c8820102c00c002424289050202000c240c00300f44a00382100c00740c5401881038540044690000c035613031000c0030034110380e80080c2c020805030960540c007900c00f0a180d402012140061 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 133825449 1250 133824199 133824209
    0x3090105071109010f06030e070e06150409110301030203060106020a0f0803090c04141504021c0b060f030103030f12090309050603060a120b0f0c03010f050d03090909050c0a090605012f120301 84
    0x10480320411080b03080d100c04003406030445c000c588ad00030504c2030602c401c01c85814007210303610034107243c2c85a06170402c1d254642c00c2c0480c07030b40c0040300510540c0b03018008180100007900040c03500ba40161340d030700d80a54a2000c05040568080006480031405104103100e415000b80b082060020103080e0a0120354103803241c1040d94980c000440d4141440e100b1168038610960442660030300081103100a022810411600810140045002101c0c00000786010714400d840b0602d42405003540100034034103c81d03440b40d1050524201c0d502183d0042038401c25a241500c00c0c2c0d58a540315130100704100026030018181210700f480c0c9200b1f000d48100154010000d4102000d00e98942c40c1c10415180001c0c01403d00f01c20808408000c6031402c0c02440144900c01c0c100080c1590307490100c1c0040f564040f409443d240c0184413031108500c0c00d0440440079202911040040c1410003000921614980004c1001040c2000f0602010b0313a4485991800c400300508851212039100e0110505410a11036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 133826699 1250 133825449 133825451
    0xa111509060105010f090e0a0b15190c2003070b0403030207080f0307050607030f090602160204050a02031513021b101404030c1b080607020a200303090105071109010f0603 75
    0x403a01c2c4d031050410a404407403640e2440000c0b41410180100d105000e404843d11a80da02c5182d813842c0c440366901c80f1904615100c9a4032140d124000c141f00d00301c0b54950030104201c010103400092003840c413003120300c5c0a0148050a21118402091078049143c00101c4508404a4004105640001c2d29400d613032800040d04e01e04180a03401554038002c90600078115046100003500043c07281d0302c50116130942200102e0300c0171654072003034100d90040d88030341c43c0b10300301800c0402541028081c4540020007000f0440c40d40c40d154098012007140d240d0403030b02c140c81000040780c03100e6840d0159000c500705140d00e210705002803514241c0d528108001c80304050b041401c00c0c1401030089061300d204030b4064407501d568000c2aa00c0d42042c0c0194401c0c01c198484030781006c907001d113003001039500c54805070700240020b000504000b200d00401c44005d901120301d060072030700d00d81c9000c41581d05070036080c2030180c1c4034040b03490011040b40c41c030321a4a030089221000000c900d00109001070445c0d4050710 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 133827949 1250 133826699 133826701
    0x8010216020a082b1b14060709050906061804050a0504021201090302100902030a0b0c040611070308073801090e010218010509040f0504060b1f0c06020a11150906 71
    0xc686480b05841c041c030b600702c4d0340da16441d00400b4607501291810014076061088240e4103000e2180e850780c2c41c4055500b04c0c1038030a10812120100b1841d50000c0c55030a010007a1850040000c0310003000a1000780258004210915003030500440f00400420003007040c40341d8a011030821b002031608a4050303128060101404140d00818419410010b03015806402001e11008100b0003420198000301d0b05445080401c00106201140340d6008503d8419542d03501c07450f00e800184442c070035502e1000260060300c4200000745040f000c032100980c0c8428071101c124540502071140c080d2442c80b2070320030b40320303c0c52480151480740607180c16288569420440d0286801e1150308038040d590004658080780003500e11158050300191040c5a0000d00104500c0c102e00c03c80001d0315400e9070111000b03903c90a40b002c0d40d10f0020f540e82d950340040d50600d031040413014802400300900365009040d42d43d0000b001c00a5600c590010440519010201d914640f0002d007007100c01c0200319206000c0c1d0003a00c2c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 133829199 1250 133827949 133827959
    0x15060a05041809051207050601030209040c050d050709050603012307051b060601081005030c13020d1107050706080402180c12090c03010c090f05221b08071403010e04030908010216020a 81
    0x1c001d0701d21b61038010f0001d103c140c1c255030070f00c04071050190042c0c40024030700e040000d40355604110303102c42a2242c2d01170072001e450710401d4002e40e4000f400348c6100340d0414410380350014202075801b191000072075809409894425040e1010310500b41e800c40282d1400400442c00d040001b0703800e00811082c1d9610345141c1d2440b00303c0c8410050b50217043c3d459040240300d1100752904803450880c00d1f17909400185400b00b01c09840d001c903030348119154134580c0701040c090184102409058024001c40c14172241901e4107600103580600c4014401001441c00da0224242604139804d882c43d601c44500041da290600708030040d55180d611000364829800c0c000c001e20020300c240d100604603840d55007280e011604000c108433108402c01081c003283d6801000700000c941060250545211809a00050a00904000821403100180890180320001505d049240c0b1104200e038111035014039540265100c6248c211264101580020001c0d07001050b0516404250700018a00d0381c0700325150307a0f03040d50300c07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 133830449 1250 133829199 133829233
    0x9040605031c02160e04230708010e06061017100509070914030a11010c1a070801051009060e060c010209090c0309160302090606032701020a08010501020615060a0504180905 76
    0x4e4050f01d85091029404900061400142400307401000c0200520080d0107c003c60f180400c20f0384014890303034580c0300114800d481400441d4202e0029540c110740e101e034082015180c5017280b08038640d4500e0a80018501822102164002d41402000314004d070404000083c080d0405000315114840740c0701c0c140c8040e1038000352030503a407940402010301c440550401075804a0110b8001e0740d4100c0c0d14a4203041242a42141e5803181c100398407403410650400c02803000841d0030003404824000170581c01d020321030308403002d0040c0350000c44e101940e4449500006000e400350701180d51700320204005200a900200d0041c5114030040c1e0211211800c080aa40c41c5e41c10740c502c006500711050b078000c5055804c008006541c061400000c0030340464182d080c06d0602d020109811900342d5020440f403542c2903001c2540c03401410300740700601403810400514000286005513551080c040000d0900b14103000f241035600038030180702c00c13500701d440d01c401b050301030070008004072018010f00710221052412 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 133831699 1250 133830449 133830493
    0x5040b030c04020d090b0a05090d050c210705030a0906021204030305070f0c05120102090f010c050d030f0b06161a010f14220207030f0905030d0509040605031c02 71
    0x801001440801e0031041848029030041880304c007a140c031004460301050170542458019000914001004d240c21070b00a42040e10b03e000150400402700115006420000740d01c030b0084044a050410141c40710401e0181c038464600014050b020100f85000c1c11604540c200044914030340950b4007004280c4404641482103010080105c0d030140240c40c0455448020307180c2c201e01c240c1084003229203610000e40c01216030104003002d07a400082c0d14115050412085114007000e080401000046940320b58440314130303140301010503546001460300e036240c82e004403842c0d4030041c00c1207640f107ea506031101c910381c40d418141c0d946040d04e840448500f0b80e00c0e0b9501d040320110300c850070050b424410200c3d000d04210035282c0d4000300c0003980789880c00f000c119030705801c04062001a40c9507032910300584117050344103214060080b060720812482c1c40100fa8008403107a10715002c0d6a4040d060000b4002301000e030010b64244c41b4a10300701050080301c0c00441c5203180d85808440340c85420700441c80ca003500f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 133832949 1250 133831699 133831721
    0x1b161a06011e08090f0105090601090b0901030f112115090c0306010315060e070e190b03150307030b0403020102030915070903030309031b21050309190f05030a0806010305010504 78
    0x26411502d9103001d00c29011107030461203500945030300c009004501c1b0b082d2142078030102220341203003004100d060340e2072107002c0c01030000390b070041728561440d11404d4220a00e044003410841e01584101026a58500c04040300068180c1082c2e05070505010305680e0271554042c1482d11038400045a09400b001030400c0700c155000b0000c00580e070850b0703210018030203c0749400d43c0945d103a1001046101030303d005607103d40440c2ea1400d9055401108102c24030340075001c2910455641402408140c210301c04986c0c0c82242e10602c40c00c0c1124500100b440c10450740e202415070200c00f402d1004240d819001107010741d050703100300c48003510107881c40c000303495096841c6e03800b042c01c0200c1000020700030340003440d072940a4101001a42c0c034060290309210300c51038048a00d6400c640703190342e482e00805000814188a49441030031807500086003a0b0311024500c5000c1101c40d0300500740108820444800d41e0b880d44081900c0e110452204090300301c070340503900107001c6420503002140700d051510507454602 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 133834199 1250 133832949 133832987
    0xf09010e07050c0304030606080a150b0306040b1518070f02160e100503060403030b0301050a09021e060c100603120e031e1c020601030506060402121b161a0601 70
    0xd1589082611554010551a0f125020038030002010500622a110003481400045c4c10420110b1038507548000384c03d0b61001c0b410340340600b070100d5500c001440070350051307108241e03844589440c03c209407a005040445540251043c203040821800d2100550142a07141c644050010030300c40203a889101d400446c0342c1c503058101c400c05c050401040b5441e001102543e28400441d280c05c0070074140001160103501007030320340602900d81d0030300344201e56114102c40d008001e101859030000d428000c21109654900d058441c0d1501295101e10407102041c0e00c82c0c00715405032500c2c0c0a0743d00a0071280c071050b1210441140a4151903015266501016000030b01170001c64401c60166881007107800c00340795003403042c080c0d0074040701036080922090981640007004950b15604d8041c0c640300c03000301014021030050081b14840120444002e3b000100d04044041b401c0f0820413106090251507400903034441c5101e140300034401100324a00092110318683c4a45030303603001c0103507074100c120b085030005a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 133835449 1250 133834199 133834201
    0x105011d07090509010b070b010902091315150801140301020a0f030c180f0e0903090d020121020706020a030c0c02060a18080601061e14030411011b030203090f09010e 73
    0x500c5600154690140182c180b101c01540c0b15001300d80000e0b8260021048500001107480a0000504046004042280081d40750100c0325011071404a02e8500d540403458039444e41c407546625107103944019140380307031554880e0703850808001c00681d000e01c1131000c0a04600d040d44038908040c002c50f200210b40f9200c0e210f08403040780d4100d009021847d40f8034104254888180020484089412700605021481c1ca1590303040801007075001c80090301503035a039841004010070343c0d03d0342900c1804032602401d00d660488c500e1145040f03100703230403010102d0ba80e10005d5010704100441c1d000d03001a64031550200404e9528081c1682c40300c0cbc01600c00780d488802031098045044c40b828090b0b2070b4020866541c0083ca90b1100f62030724000080c0c00c0440800c2c0400301868460305032070600c080d00303001854035604100d003000380c00b0f402c1c1c0310190001d0030010345080c1c00b800c542d00460740f1a0020001e04c2161040700110304000b03490741c00c0144207034401c00c800948000740b4a001803106050742c4040e5628985 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 133836699 1250 133835449 133835489
    0x1110109020f310e01060f080c01050703050d0c050409110a0c1b03140303010305010b060a120506010c0821072303094306080f040305090a03060b0a08010501 69
    0x682c0c10050741140c603580350780c800b0310500e00c02c072129208507491283c00807804143c0030345003c0c01d49006401510510010300000c001031040024406900103007801e00300d550f0030260400f11001e1281d800c43d51006401c12103d00320b007a610600520407280d00d154200200c0d0000310741c3c1c8105114016518001450304041800800c83c4914008908505012880191940d0b40c0c5c0b00010805407403075024071070f00302000400038000280a84d001c1500c4c100d90786850314022038006492401c8810b9030500040d40d82000884503406010640c000c550011381c466100d0b10301540d82e582c0f06154941c2d00708900070140102e14154041ca01c03041d0120004081c3c00c0c400c0c60012040440358100802c000c0d458410803101c04404170b1000300c25400c111607900050500c1ca0200100c40b14145030b403692013581c0810308070400501d540070b11480e800c0004c20201da51543c03141d0a007207484d800303946007080d0f1200e925140002007007210380c07004900c051b081d1181d000c150f07903e031201402c90303009100b02c0d01a00a5a54400f603 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 133837949 1250 133836699 133836709
    0x90501060801150f031b0504290d02070c03020d2001030b03071403160f030303050108060708060405060321040512070b0a0f030f020301170c09040c0b0c0a08030a0501030201110109020f 81
    0x203421910700083c0c0740c110103080c0810b003160f02020202290002809000010411000202d8400e0600000c0c0c2c020600c801e16271018403c29180e62140e6034049142d6041114500380b003401140c004002c0342c032400650810322405a5260303c01111807950001c0c1041c254000c1c06551270000005000e040e005160418400c1d40b266419186035050003458150180070715165000000b5022424100c080070703085103800303412079406800c01046640202704000307210b80d003c0b10340340c0d200a0545000c182070f107076107000c2403900b40c0700340c03004114104c002c0c9200f050481c482d02410841d40100d80c194011000303024550b454001c5802032594200c000c0000e10046800f401d45d081060b4550300e000110501d40b0342d010003c03070300280c00c8088d250418119200040ba0204640741611004481081550900d80d45d4010108940c1c46200e01030740012075110b40d000411f0000c1081550000400707a1740c0c1c540a10040700626003400224080f510102c00d0000032407051054044196026010b06006500302c41008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 133839199 1250 133837949 133837967
    0x4050115050a141306021005041707021c11030d0806240403080705030702041a03060f0c2808130809091017010c0908160909020301090506010b0409050106080115 71
    0x3083c84880c840ca1001c1000181c010018201c109001500c1d140c00c0078402400c103030410003601116818501840b0100d5030001081194015141d8641d03512101840455104960340c40c0b00055400e040031001d05001d0a5400010b6011040341550042d4600f1882078a01c000140c0703446030498072483c00c3d0300e01410104a40c80f640c0850078501401c2c07550720b82c1c40500340e9000c080c08a030150030116404046040c6801000c40200d43c145281114403a0400440c0d40c4050051025424004482c0490b520044210484103c203039480c0c3c00300d003109040c08100c104203040d4450100001c5100d0006501880c014030708a003451f522107907840c80c21f0242020080b00c0140900b000c0d001c0482d81a000484418190035181c07000300440008c00c418120b064003520080066000050540015049600d0007120004aa00380c0e444003400103900441d034004a030042c5500c2100a000d44100700021410605800140003101c1c02843e00b0f002c240c4e01c2d8841180c401030b00703214810044c0d460f1141d5060340303401500f0031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 133840449 1250 133839199 133839217
    0x14180415110307030207032c19120c080d03050720100516021b030a0f080427050601030c080402010503130803070e01021005010f1e03200306060405011505 68
    0x705082a9505441505500035640c0c500880d500040e0107042503002001030150b07000e68605401e000c2c0900e640300034221008514107100b5201460a130046842410810000d0a031aa0420b01c95005034504a01c203204a802110003d200e100d1110b25098480d0161500c142c2041c0ea8120316190b0700134441ea103203c1d22800007a514055000c06680342c4260f441060700c140303441030b101004583d41c0a0080d05055a0080d001c000c56811705000609850004521496560040000c9040141c82c10207090b180140c0d0421441e02c0988a00c118650f8249551582c400303280100421a90729182d0040d030071507400002d0030717004c90743d10350008000d980a103001d598031003600d01044401d01403655071540240d204644150100784090b80108055a0420501d048040c410070304020b294140f80000c0c1c80b9544920030a0085c40001a200138a4812803070804c009580c09030242c078242c070040d00d600490901d0300030110302030703c14440000d625152030b00032039040764001c8843c02601c0c0711308003041780d07160301903810 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 133841699 1250 133840449 133840451
    0x1b010209030d0302040303030e060103080a0e040b12070f0e0f041205070c0611070e27030c0709050613020711120102040509130311070807050d0614040c14180415 71
    0xe40c0c029450074002e0011100d4030780d0300165164203502c1d0103400c0364100803401c0c00640c881e80060001030003110860ba2040800e0800c0c50400034243c002801900c1810116600040302087e06a80361000158000c00d545224190740c4080d1303203a0604e40780c0181c0c211440000fa9100b0800301e408900c12402081881401d80303000c500d8002c0a407030344000f0310482d501c4100050880500c16034101c0d400d102220151001203142d1900d400d000b1031984a1500111050f02c541c58850711641d40c8150800440d9959481c100c00e50f01c0ba182c0d00c8600c0d0000780022607005000340e42d4048050756214982c070880c2d80b01640700402034a10403025050207058900c0501c04495503500f040f02040640da0400200d1180b20000c180032a0900e841c5401814a440c084010300d50f5440194144615003021868405449041e40c41d12020285030800401a10005010101e5262101c0510040c071440c0445442035804045804080b401e41c4030a2010b401c03c401c00592500c0030300b4010a00081c0c00743c9e81c03110b442204442c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 133842949 1250 133841699 133841707
    0xb0f150f180405150a110301090510080601090b030d030902061c060512060a0b03070f0b0a09090f02070309060807020c1e10020f0c180406050403030e01110a0905030c061b0102 77
    0x241c62400060a4500740c0c0c00c1d03440040c50708050b540303400d0605e5000c044007905124950306858103044a00042c090004a15110000200c24050707500f001c0300142140d108036905035940b0b00c400002002201c4a040c042d00800d0007030302e10385019020301429958007402c00c0389040c40038050444610301100008200c0740e150603002409a407101103560322042200080c10702d40c14524041c00844055040050107074001032402c20461090540ba00c08882e06041e4090303694040031022200c0401036001846014130300b000780500800a0303030103010958403a403500c2440503100c0c0302c00d0b40c4501d82118514010781c021001140c00d8100580a90096000c507200d201422003200d0018160503155902d810051348424000e01040c5010010312052050648403040364400103c442c402806004101901054a41001c0703000c0600c00d43c00410b00604120007040401000703107c58106a001d0083e0358000f4402c0e68012810785800719220440f10401041300385040c22188030b07400680d210402d0b41801c2d541c00c0c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 133844199 1250 133842949 133842979
    0x150306090e01240815130605040b0105011b0b1801090501060b03071407051b06070b040305092b031803060504080306130207020904320102070b0f150f 66
    0x8011000d0305507000700040303a4400503400822035001e107841e41c0c1806940561041102034008100c03007600e0607500911084940d2414410344000250840c002c0019151400700001d000c403030b425840c103845003640c0d06850009010b02c4c614a50005910242004803490046081031181242201ca082a028004521020252070b00c03400c480c0b05601c1030004003400020031801540c001003209691803011103507030401802e40c650300d41d43e90350609030030703c01c001e40081722140e56035020a4a00d0a60320012200b564945498000e20b5a000264421b015408600d0080c000090071303043c1d0480c00c080713146035a060107516201100c0c41c140c0e9628001e505501d0070004004906140180c520441c010f00c8082d50380d04114062000d6400c3c18107440020a205020303c00060b07450180403900140c000790200d40d03a0704040203d40e8035041280700c902c01c5203080c1c121440710203410340141461030300441c100c00c0d10342d42d00b813109504000101c07003001e81448402c01d0040545004078100d004c080001e07103d000341142e51 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 133845449 1250 133844199 133844201
    0x3040c0f12230717070906150e0d020d0b0a09060f0221060a170604200d0204110405030d020109110306010503030703050309120301030f06061a0f21040b01060906020c0a15030609 78
    0x41c4441c8007040d0800201440800113502a00d40200310a0210b481011705445000701900b000c50b8001e845a001c02d2b00710400c1d551124201d083c1c054000011200c0c5091541c180c00041840c1035048824900300a5000500081407095964101240035401d06c0c0f00744c1c40c52203007800a001030010354405251200818400441c15840b003502d9a032100502540c00c0504cc800e810b0040c8404c0080c01c82c0d03080c1941030450310381c44210904243d05590100d00c50b9a10915001c440c083c540100b50140b0800c0500404140e054116144582c0200024101000c0300c2c2e081c180c4490f424050710341c140d4400c02c44800002c0c070603030055501010342c1003038076860b00c142008005d06034000c3e40150707001d03856000c1c4a010b000c810300ca80d5004000907040140d94a1420310f42c405a03004180d0000e00800d008261640c0083d8840300c90004004100ca403c80103180529014100c00d03000c0c00340200040a800c6e010590b0b600000b003d11b016038001b801c1c41c00b2545400070843e0058441d114401c105503c4903000a420145 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 133846699 1250 133845449 133845479
    0x6051011160e01060206060409080406050d0603020429060306060a0809100507050a020607020708060112151d1e1902040b0901090203011805060f0103180803040c0f122307 75
    0x102c00841055503d02580240341c80b20240c0041d12a40c81d1090035800076100c0070844003101c845007006501c0d400e6601441c801486c6070382c00a50490b0a00d401ea5a104203000c00d0b40360841e9403450f03540312b440615000e02200e40002c0f0f43c42a003100e801c00002d0f805501603031031580c0c000090340c00c46022800302e09124041e0785c0f059400d100400d602258203c40150140000f540c03161142c0b008144007460031005075603d95040c49662888180e00c43c5400c2440301d0098014142010000280008a0089040b080300c13a482d1000111a00a41c0c8143c00e050600c2002440c4c000c81c444000d2511600600d079200010480f07a10890340700e230340d8125001d06501d800001900800c1c004034016101e6150a22202e4020781115101c08460325280402c0308036541e242491240f0b07002031070b001459003100f8128110720034039003101401000d008030420040000441d41d01068400740c401c0240e0541d81c0d08034260340c0c1c0ca1880c3c03005280c64181580041070450000b03203416804c40c11411185110b5a5083c02003194131 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 133847949 1250 133846699 133846709
    0x30c190804060506040c140c0f011a01030b0d0506071d03010518010e0d0503040b07180b040603060f0e13031b05100b0906060409050606040302060c01051006030605101116 75
    0xd80300003080203001080c41a154040d00650b400d00601000d424020420303004042110424130000c982e06000c5e10080140070900f0682c074000300500d00446403540403e2600400160000e418811508002e05040d820070625540c454024071242c1c40d030240a9400d8010160704416690401029139181e580c24085d40b401002840451602002c2d80c0c00d545081d0b480c641c041880503400280d0380140c141c2d0040c1129402604046480e1068961040c100c0c0c0680e0b81c40011045a420340c50040b8000010703000400844641e903d0030810f45641e00c4a4903a6a21103100c0d060481840900240100c0010118803001d03511a2400311425840349000d0a040501c08000303036055031000c402102c1000e038904c01c01046140441e0011140d00e00000002d940748520301035900529212400301c0c801d40c07280e00c00d48003d10f50040015131100503a45409000344011160100e405401040010300c07103000b441240183c030b0019052460b0010540001d859540890300245060b11811800301d802c0741c1ca5507030000c0604 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 133849199 1250 133847949 133847957
    0xd0c0c0c0e070509090402030109050105010e100f0f0902090411031017030403020f01110c0d0602030718150309031803060209100509031e2a15070c0b030c19 69
    0x24480d003400584980d0580041d5100500101070004054121080da5040902224204c515545510100c3c0c0503201c42907005200b50700b468000b150840d60150301c588560380c0c2296a0760442e950311100080050f01d4820703950103285241c414042c10006030014800b480000c1c0c4040350034944030600055036401225070740e0614020711014800040c845074120f001d50040401107041c9400c0d50001100c181100c01603d041c0f01c800000c03070070941000d001c1104a02001000c0c5651a2a0303414454069801200d43c0800101441c160090360300130740640e20f040d100c01100e958a10000c2c41001d8000b4040f1000c02d07801d000f032010a910001c03181c00000b81c0618841c0e030700940c858110340e043c401807505005046003480014015aa180c1d200003403c3d519144a40509603406000386c140c9504100103a080c000c0e0900044000403600d40c0c00039140c04c00720f5419900d201c0316460815500085003e000001030400004500802030309002d000a103811124103640a03161484500507a04800b10f12503c3d40080707 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 133850449 1250 133849199 133849217
    0x4051f050601030b01021b0f0a0f09020a1b0b0a0e03090301020f0c06130803041203090b1e07050408031b0708031b060606090d0210050c07080106051c0302100c02030d0c 74
    0xc0e59050089203030540c021b0000b0320500b082c06d600602d03181081e81000c1c8c016411061040d5899031013030400d80c010140300714240c01d02900c07000610065800410040d021903035002000032515540000000115004906010b0341c1d120348400c04094582503010044a2005102000311540c00b0b20007805403074804084141c0c3d60445690507410100001c0a044a80a034008024003040b0300c82c0450758055400b0440350044a46008190f00030800d40d50040c0c1104212003c00800d082124240e0000706070300c07074041107a95035944046400380f00301e010f444d4864105010100b02c01e0104001e850104490000340c44070103850701e16551071600008005400c1859020307144142d91814000190450740a5541c6480c101c8407a0200700044a48400240548000e006840d0400d00c90400d44110b80444420345042683e94641140604268002c0700e101d808004100324950b10f460798541007075a41500501015207021403071130002d0222010310300a6000c00c11420100000901c12030080e03d00c961144054 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 133851699 1250 133850449 133850461
    0x40f0f08060a0e060a0f060b16020a05060910110c060304030203070b0f01050d120315080a030305160e0114041a0d0507090b340606050907020a03080f04051f05 70
    0x160a0000d4049201c903460310058001683c004104140e001a1440001c0b41c02d00704210004014000d56101e03164900c404a5000b4001440284110442d4000c03101c000240c1d0f181c3e0200402442103101c015030060480b02c5000707409000d16840020381c0b03003203c1035610614100c004107040e680101e40860058000041034070402101ca10801d40048803003a180c2d140d581010007203442c1c80b80300c0501a01d260032968120fa00a07200781c00006488000c01e142c0c0848659030a010f5650344412181140072a050800103040041240407621200d0910f95541009550300c00054841007041e2590840d4100200400708480d511520030110800b846c20405039203124040400c8111900038004e08200b09011100b003028051b8501951030070404007c6021401c040f00025440c1e014040c40b0569081c00c084111006100603584408200c0c0c40a85100d00159030300e180c12030b16080384c420002c3c0490480c01c0451040d4400c0042c4552080c07240c800c03a0481d0b408140f140ca0f0414500100d41a81501e685c20480 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 133852949 1250 133851699 133851703
    0xe01051c0f0302161205030405040203090f1e010f1802060c030412120e090402090106050c07080f0f0c150a0e12011815020f0906210403050702010e2b08040f0f08 71
    0x2000300484045a030350a0a960350b1b80740c0301e202d1442402d00c00d940120201d00002004e1000098000301c403030441c1d00b4550083d008103c01c09481d480382c0d900d5460071440d4802a00c0d14001c3c4200700c0580405d22007075550690070007016810102445206100c01e000c086694541d44100c04441c0e03006400c05100b03900040300090410406501c2c03039000d0320701d1906102c0161032390354034941500c1090403d90317251880d050381c0c14039006096009001c14803419141c4024240045110b0002038460016604082503480c2804140580740b000107104650400c01459020b11589200c02c5181c030051074140380466034241a030941703042c511030244c09184c99183d142001403504440000f1241c01d030065003010f0340c440705041c16020b11501503000c0c0c2000640007c42c005540000e000c02605149080031710300345410000d00c03d80046004178042070b150b44886c1c0440c60000d110083c21581280c900c00182400000804c0c81501d900040324207031018400464140081c20108024200031000c4e0008245081d83e0a8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 133854199 1250 133852949 133852993
    0x20103110412170715020c210304020f190609080106050303070f03080901110721020105150d0804080601030803011a040b070f1a1e150312070510060905090c09010e01051c0f0302 78
    0x29608c05c61321424840032541303401601d42c000e0301180d080d03401c50704c54000301e031400c402c20b209000b40080c03110002c5001d9070000020f4081e551454001c1000d1920380d01419500d110f020400707030505090001c8000080d129481c0356034400c02443c00880d15914402801d6000c4c0c114034000c9403a10601001c0703070681962000c4046a4103400e200070320103030804010f8281601812050980644808070301d82d018007071010102c400900112045903155a503a00b0000030640086c000e858021000c0941014030a0348101038030f0a43d2806201c46181480d83c0d0f0740e0304c0c00103030900e508407100324440c03440308841d0010003000751241103d42403a424012501e14010441403005000f5806001c21f00070024280e200001d540340e055901c00d11503a940e80982c01c3c02480c0000c015440140caa0030039501103481015904103a015255600458554000300020400c00030000d00a4510140c8980010040d5260102203510f009100901c4001c51192503103440b0400d101c620b8080e005644401590b44101ca1140085 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 133855449 1250 133854199 133854223
    0x7120e0102010b1c0503040b070b0708090604320109060c03060b160201030914010c031b02030a020d050307050c0f0106030c0503030a09090506010e0409030c020103110412170715020c 80
    0x1c1104030f0381407002950001d4001034020345845065249002c001c2c04000301c40181813201661034079014907181109000d0412100c81002940c50342c00b0400c8010005107130303406281e000c000c40c0c098500303c0350804a400d04915201040300e40244403141c034503d0a02c03c0d004250702a4401258a1600e80005026105142e00c1030351104420041525480d024a600701c220b281d091802203204441070920042d81c15580d403250085510b480400e05240e41c0580c010411104c02e020307440d00340c0b1000c0300141e80f40d00440c40820056005a010928a00e20440043d5408692401c1403410913005485151510810b100c5490150707550360000e0090006600081000301400c8008614003542c00c01d005003503102c54460501c03056290f0011407290380c05402e4007035002c0b00203401000701001c1e60400800c0d03200700744002d0380401e1a10f15a400b400f26684222005d44141001d81180e0300c15035601d07100c2a0001862820584106114880c00074882c06481c25020700742420240c3c6a060b1000d02d070382803011030000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 133856699 1250 133855449 133855451
    0x180302061f03020f060a03060e09030d1b05090111030c07030503041a0c0a03050a090302060313031e021e1006080303010602010b03010209090a050a060503030a05130e010518040501020f07120e010201 87
    0x300300b0040c2e4076100340f94980310f400c1d940c490722040c8845003680075003e6030704180315043d230600412509610010290400d1000c0013018416640480e4003d50b80520801e0300d5030000da810008100170754003914264044a84c001e00703c0345840d040a10080c1041c0890300121030a8100107000c1008e60000c2d03022041d403001444000d4905500b0319641680c504030700c0c0006041c000c010407100a490b000c0c5001000035a005020943d4070f02d4003007011421004070702004c8021940c918036000d80f48610b0740d41002418019002814400d44038501c00e8010a00c5032580c00c020b204459004032400b85902482c0c0c0101700541c0110b071a541454000b9080d90883c0e004940030768414014000c20f030303962040050300242d24100005645c0c40c1d80e0480009408503400050301440005680d50006034400020001c080100702003040c11600c42080e08402e100c284100c0b81e000c02c1c0300d0641c45070b19500140d5190001e00c90f17000145800c0690880240701d400006090380e40000e0803840c100855000f00c1c104845070f00c2480 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 133857949 1250 133856699 133856761
    0xe0a0b101203140702030d09030201120e1e01110c0c03060106140405120a05070b0a1d0d020405060a030605010e010f06110d1101090b1918121218030206 67
    0xc4840d801d02440400038080085080e118080300c8201e00440b00c1c450f401030140c0b00507450055014200040920040b03001425060411a44141c81d03c5000c101d50790700c0024116451074450b0592200c0800700150625550b1020b008d0b2003103c07428024501c9000d40b00141200e500074600b00b50034102c059100c4000d11021506100e2a5004403046900755001281c540d0303500303070842e402d09141c0720990500400ca441603600200e152680600500101d0540e99202c860000502c40c86450700f40c5c000c88042c2e001103405130850010300d02504410352000c4040c1944010660700e856207010b48500ba8400710403401c0c418018480702200c04043d402a000300d013032a5030301c0004580e0151f80c903400c03660803504011051810001c500429000700d0440307134100d6401c50740c034141101c3c62100640405103c504152030000e5540711220500c600c1d500c91174100d0014601e2000028040c0d83c480e15010360321034015aa119101c1c50700f030030300d010111111f0003627008180e54a442e000d0b05030001c00187d01a900c13041200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 133859199 1250 133857949 133857959
    0x105011a0301030609170c0c040b0f0a1809120c02040f0504021008060307090f1a01020c0a0b03040618060c0206010f12080706020c12120112020d060504020d02040e0a0b10 75
    0x101202c0c1182e50000c000100c1d02407505098030b05800111036004c82c40300019001819400010f401c100b0b54000300c8040201a00110422142184280c07540350411059002006840c000c0410314011a00c08040032603100e03807a5469950841100c2210404141c85140380c10541c2000e11812501e00b501e0001081a410107400092007501009050010008840e0000c0e029440030b10076000104802402840344000294042016001030041007440346002c0d05200f01e203601c0050b83e10218a030140103001042e003414868072450340000c0040e1540b548650021542240c080d400c44030490045000051407100300c64000e00740001039021030018002c3d07070000e114003500c010701810744903880303da03179540c5045a01d072840c06805003c5180505d4010340340014030b0481c0003002404000f500040380e1384641e88882280308080e403094030103500448a030842d40001991075109130b030001d000a0141c0ca2000690340090301b5190030880c0807030030f60410085001013200f141e000b40e40002030301c1000c803c003034140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 133860449 1250 133859199 133859249
    0x6080103021503070216080109050f070609291303290703020c151815090a02040903020a0204060308180604150302071412030103030e0d15050705040b030f010602010501 74
    0x514403000c80800c000004ca80310328000c100740c001c08203010016041c101d41d41c400c01d80c000c0807a00000d507003900070070b1038103c88050007007010b41c00d54140d078841c2c0814909200c0d100003164881c002c1100191183d0801050407a2543c02402006412490b4045030504500d019180040703200e42507032545041c20b10b0105003400c0c0e88052603020b0032030307d001625980e24510091410b1107501402c03001000c10800e00c841040221042100495400c085034040701c1021560b00c503600003104e59241580021452500614040d00404e5060703000303204940c0300046680010f030031140d40354000c503000900010702480d000f0101e070720300005a0080356158240341c80c5c00445940721225400c1c0ba01015800a034880802c1030030901d21302d0301c120210071140c011150a85200c040d0b0300030300003940441c0c111401e8281c645030601c4100c0046078440e2241543c60b0910701c421000c0c03e800380c0030341c0611a091001152084c4407401440c8940110f0b204104607525050001e421618103800150b004112042c8050f5001e0003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 133861699 1250 133860449 133860469
    0x804051507030e10030209120a02010201050603062406041d040201020c0102072d0b0f070201081b1905160503070c06140f0a09090c08041a09070902090d021210060608010302 76
    0x3050381d003690700c44c04622048000348660f0782c009600c4203184251028650780014100c2da058400e07002040329441c1c9100b019070f540d0040b40c101d02e16944000c42107419241440d03540b055924040c02f45070030a40c81e20726041c03006240c4284548164484403c210643da4108a5800c45440a0000d0032180d81045c03100c6410300307000c46501403541480309019400a20342c0c02c1540c014004d03242c44d1602c503a020090400d855020303150a034002136000002c202c01d044056021384440450142170f078540010004203c42600e004180d030310a03c4024010390b40b00c54400403004009a00c04e0001e9640c0b64554a4064a0072201d034004204001c90310200320481500700702201c4600c07420050458841183c01c0c01203800e64000c0c3c00400c2c070141411050140c40d900490010301a5100724041c01010003207007055001440101c5200c001988400c0d403c21035103203140c1c010070700c01d80003400c58604800c0540100d13200f46200203800c10607a00149550302d01c160148039070b1000d040207180031071480d450341d00011059a1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 133862949 1250 133861699 133861727
    0x40c020c0d110405040503270609010e04090c080309032418010b030a0308092406040c02070b04060c031716080a021309020a090e0603060a0b03150103080405150703 72
    0x2021410715010300031402211016414000d10611080c6401d02e401516a0015201810815030902c2e10407250580907503c5000080d0117040d060810182000440f068a4600740503500941d0301c582e5200440c1700c0c01904e0010308006c1005543d100172401c10f041c42c0032064002005007400f40040c000101d12070602503608241c5010001400c03440c000a030900429892441c41c0d07240c030403200c041d01003682028100b486141d01c070050f070340384106400c2801c083e006200903103403015803801c0000342c25140a51010301c0101851040724030903901d9010817085070b40f01e500540045689180828105607125052441455031400b18990504104194050410701e01140074240403032000003c901a00d103a05941000002c580324803051030b40c4d100071000a5001c1c13503827480021281040403a03211f08444206015800180062585a481e00140c0c4010603110340415454010585403801c0d00341e110407218003130f6001d413134040e13a224540010841075800e000c2158203641001d210302408a5040b07042841059 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 133864199 1250 133862949 133862959
    0x705010e03120307021014040b01060513030b010b0306030708070303090b030a020c01020d0b12160b070303140412081302010203070b0601120207050a02090a05090a08070203011401091505040c020c 86
    0xd8000c400030b4100702520b50031880c4680d021041144050740000e8864003c1c840c081c003003003914017004400801800445000d04040702d26001003050900c95001003140742c0d040c0d84485403c0d82c6aa540618900080e07001001e4600c010007840078a00c4c05000d101c1c01080031000822503a49581c0d00134002c500c0c1403160031384450000c800603042d0780c1d06e0380481d0700b050841d1008540e1081c0202182c3c1c000d00100e20320070300440d140a4150900c44c130006052b400440e4441c02d03031100702e10f404111803641d031141e030b800c400301038540c0c85200d104004c2c0701110380104c0c07162800c140d41c0c0c440e1110081481800812441140900ea20b9000140c0d80101c105c504654019042d00e40c1982c4820060350041c51203500303071309481d200007000d205000000c120254128401c0f201004c5603182c0114950a58000f0f07a00c445281d040318035003074001403404009000041c4007500110701a1441080c00c0c00300fa034242d01204403a62109000b00b11070164811400c0134103c01ca0f020042e19130010b030025914509460070328003078 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 133865449 1250 133864199 133864217
    0x90f010e0a09020901060210050906190f390c03200703140f0105090c0303040b03090703060203010906082a19030501110c0616210207050703081c020903070501 70
    0xa81042c59166006004c502c2d030303542c0d2003c00079503407250424030602c81440e00c00421404100071460034019615140010200b841c41a5100300074080001c070b44038615a1103c400c420b588010326120340407407608000150b02c5480c3d60910600b0102000d0f15401c0208554400002035008030401a4050070304014101d0303901d4000185241956581015003110015420001d030003100144021074455508002d02c9641c0f980000c40e0b1f40d4280c81c50501d50305800070711042c02080300c85405942c3c0b240100c400c6601569580d280c25040780d1080e04003c0045403609001c2c00002d10400800540e44140506c2d081c100b440e40e01c511501c1544040d03000e200305441e07003d030705016410646004c00f554122008011b0504450303480e58042e80300814010040c0224030000e001c9140e00514013540c944c2c15103030101025031080c0141d0017510a0508221415424440c80780410820401c41c0c0145d4801c1c0d503c40e54800d1402c0c00c110081d030b481c80c400802e0300d00401c101000c0b070310007103045403c54000b03080861513 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 133866699 1250 133865449 133865461
    0x1090b0a1d0f04110307020c0f06160c090903030b0a06170408090d05010e030703090602160b092d01020111090f0d210c0b16020309090c04050d1104050105090f010e 72
    0xa0910800b40e426446402c2003d08100300740003100a502a2800b07408460300b08045400740318064038440d00050303025000f030003c410150b611480d80700200d4420382e6400d140ba40c882c000c40c030446115007429400a80d0b00c800100b800e0030312200d12400340c401402c25100301c6200c00350300c4101080040000b4001078000c2150310144d11840000c2d03a1440d4400c00034030210208094a075a0b039002100c050300020300784100007070681d00100d0000f41c009200c24080784000d0503d0f034a8406540403801064114604086800081480c05805d4410148498280d0031480c5440002420345a04400025a081c01040380001c03607510800c100c2c858070825511010207001a0400602c81a07d42002100b03020b40032241c51145640402d10070a010f201e500b500c1055101d010582050021401e24174015030b05c104103c00c1c15141c1001c005a2084070045240d183c40c0e00c503404035418882d006011071790303136141403140d903444d01c3c15000b11800340600780c800090624211118003030700b20043c40361446240c0b420010540f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 133867949 1250 133866699 133866709
    0x306010e060d020a0c120305060d110102121903052d0907030609120807020a020105030f19110405011209020102030301060c0c081b040e0a020906150403050f07030201090b0a1d 77
    0x50a0000210840d214460402c4c0508a0000100d0441c0c0300310345501c501500c81d02911400c2c0c090480580001c0c3c80c4029543c1b071202c41c2881030381440c158840c040c0d020080720061001007071940064a10902c25410b10180a8160303030016021a24400a0030758159804184500c000c411810342c010003c41034541551050418805404c0500510704000c80c66091200c0c628590000700c043d40d07507540140d900d11500300c0c5c032541c1e5040001d000800800c0880e2511681c880311075004041140c444501c10b0400b60f140302100e25080c0c2c0b01c00e403840d000c42c0800803580c12070700c020419408000e003401588402d40c0002d450348014010344c0d0510034110810001d0007030501c26070b40074000580c111100d80c41020706000c08800130f10050351045040440c041c000c200042588403040350b010b81603059a485002c20418900001807045005520034080040851701c20400c101c03082a80d00064504542180001820f504542e00040100c8c102041468178859000300440301c1c00c004a24514112182000060 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 133869199 1250 133867949 133867957
    0x30908040e0403020a14030426010209031501093914040305010603060b011d0f030a0204140f180601050405040204020d02070b10050a0602070302040203070314040308040302210306010e06 82
    0x10300c80705040d07420402015000109601c3c150300900d64540402d02d1017010541d80c0c4910300803008802001040d225248800031652010007070303600c00150502d110400802d24083d034000c91400a0344001c00100008500e034464180700104402032004000804202c44000e40d04d050b10b9080d003400d500d2940e02c0c030940f00c0d50b400d04c0c2c034101440000da9125560b04295000e0b060318001580c3d410f20346001c0500c10f601510030004250080d14000144140f00d03000c019620245540c240e408d070081081d500016a1349101d040c2c1c16040e860110302c1c1d03600b01748950820304d0400034180400044091001510f1441c0002c0e41d5044900c211000b189941d11440810b01900074900c45aa9413800454036108100f01000058401c2c0000151001104c0d566010440700c1c02052144901680080c01d080c405801c00d90020f60b40811a8100411256200b07030350030300703110b004440a600250018092004240d81400142000300c0210441761150060f0600a4154800030308140d042c0600c05400e204581c0b00d130404e41d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 133870449 1250 133869199 133869209
    0x30203060f070c1a190b0d060b0102030f040801090c0501080606031503030d05042015090906040207050a0c03110405060a12030306080706031e0510030807060609061403010c0207060e0103090804 85
    0x4c02215441110142025401e840e440c0a0350420076028824003428814010000402064420007a5080d11400000c00c031721000d107070440c0010054262a460154014401802448000284052141003c0304803031040e4000e58104181107051182a580b084d04cc1c070303003040e810f00740f1400030700c0c00700c0000b85103206031100403c09034101410482400001000246400c01103007030895108003000c10402c1140d9074801a16800c013051103004010b0809034440c039172150000d0720041c94450240c40c3c051600c0c201440403030b444502c070302c800c0c410883c200c650481c6019045d00c0a00c4281072000009000c141c2602640c61070900b1016800241403080e00414010310481054881d000e40300c5000501030441c1130b5041500030080300c25800f60308403074400da030303c1017040008060f4200d00395640c0c200c29500c0848162960340c2c490502241c4c02c0388600c1501b0050141d0151900101841c0c0185400d6400511a68095420082003080f056400048030f407040482441d002508000d40c1c03401200c1d0303009a4200c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 133871699 1250 133870449 133870463
    0xb0f07121d0f0607020714010203090303040b09031e0a141f06170304030b070e01090b03150418030e1003020d050103080c011103191a0306100504050709030203060f070c 74
    0x1500e003608141e121000018001c110a840380c0300e0302d03900840c0d50703050160b0b104d0b40107a2080c10200409918403560140082051055a01c0c285e0300710000780c030f0341c0c001d174200c1c1301e00c00c40000340380b00d00345400c0124960b00659a40090201c035106440c0c180c0764411690086c0003030864100446000500b03004103005c0300c1d180904184a010440c40030300003031a00713005134445d00e0070020403100d8007600002510200c81c5c0c44180c0105542d01c4030412104e81180c004040d060019407080400c801d041c40000e540f041401041c60b00081e00c829080106903402c0c031b10102c000103880b00d403682c007081d4000024421483c099404528150440724100c000b449009050400289003000100400040800411040540b400248a52284042d907540103200541e03180c9109540801d44011040c100d403c010f11550004842121080b00c40c0c01203420441c00710b8001030b0300c80c1c903000c0500480c60540f0905030081000d28003d4849801c650200313550700b01c041c0030715006000c05800614001d22a04c0410800d55020034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 133872949 1250 133871699 133871711
    0x2040f090b10080307051b01020c060307020105090606010e100e060c0109200306131506150e04060905070c03030209030a020d030c030807031a060d14070509040f0204030b0f0712 78
    0x81108111000ba03805440c092002240043c0e80b400000c15600e546410002528410120404291041d001c01c0206070550040e0090004540c0d41d4030003961252455030004030741e51078441c903201d0030108010100c9051003010061681c041d204e4562010450000d410300300c1407500c10342d001a98a0007800c9a591483d030030f01d01c0301c008100c3e104c200f848002c10481140d00035040341c03e04040d1034100840382549c000194510040115044158501c80c03101d01e0100004d20030b8490b8038961076021094914400b285600585c0d08943c186032040000401908500700039074105010010230340040e441015080540104800c02e040c0e40c00c1c000d4008590340100314448950722442c001d8038a923840c500030340c0410071038000503121a009005203c000070041800f00e5400c820f00c410080b468000300c451012003980ca94007160b040e01403107070013806501d083c0c56064580342d03c4020803058075940b07000340070245d0051004000041914030103e82188224041401a0340e480d030086498205100e460030040f82000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 133874199 1250 133872949 133872953
    0x9090606050c0c043c02070614250f02101803120603030c03030905010b030a0c0512031903020a0c051006240c0b090c1207090e0f0a02060702040f09 65
    0x501403514000c003030380d0a0803c084100022284940400140d0f011380b10b20f01203541c9100c4000c03c51240c10031000c00c0c0740701c0d051101030003280c01020b400c40e9201c0d561001c50b01744a07038410b203031a40020602c48054502d24040003445803200703102c0d641010b00406211000c2003500071f019680300c0902d821010002c8410030a40f81d510074450000590104c0c40c1c10030a81da0034803841c0280340a880e00b42d100c04100d01c106903002c60050821003c1614595600c610070580e075501803260340400c0e4026a000301583c0d0602082154250b4003a09201c0c065008100246030018100020b01c02c42d035280c2401a11222007603800e07203402e194060005c215014038108180a486198095030603240e00c104c1912103843c0d10048903442c1088600702c0408900d52605100c002071803012000c0c0c0c00484101a560585c0d1040702207282440c9003c0211900d4202e400280201c200a120b0500e54034401002081003200205610762076016030540039000d42000505030040d91030359007002034040d00100e01040503440c2c0e4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 133875449 1250 133874199 133874207
    0x2011115040b0610090f06081e04051b0d0222110f0d0c03021804090206040f060809011406010503010b0d060f170c10090b03060a2d0b0a05040b0a09090606 68
    0x46a00d584148222144150380303510685d504804c1c1e5400350503026085040110644032500c00178648a401c4282c56068030402070305080441c05248920001d2140d07a04800348109c1c1340e840080d000340070f07100c02c0805030301580d5043d80c1d04042d15110b101000c0c6403000d00448001500d40b4051034424407000042d0880b03034592060003000711854014080014211030f40045061348500f11009854083c0319441d410b0310700c1d0980c0540915440248858601a0742c0e280c220a461102d48c00750000c0ba41810030003080700f00030b003c4c0b0071440e003181b0410384461400701e001070618041130094084041c0082208070820006501042c00780c9119403040c0703c0595107038081249194003a51042150244072000401350030b21210b10034001c5065210048014203105040041c0e420080c05c46600010000001800f07249002249418056003480d8105a0700801e0181c5a66030450740520395499080200d0110103601c40280c806a8000c001819510340c100d03001146c411603541c004840e071034500340300011000c1d04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 133876699 1250 133875449 133875451
    0xe091216050303010e010314010519020a030e0601091a03030702030a1401060504090804150905010212090f1305010816030803221b090e0106080a020904020109030c08070e09031602011115040b 84
    0x10070238010001c2d54800d02140e09844054804800003880050041d41801c8150068030450f030081c940015580341c00c61745603180c1417080e40b180c804640d480d04403c41c4d50750505107450300b10340b0903401146010f501350b000c269074030b80e04280034154180040b030032100b149081d001103004080041003484030020505007040283e1152149005c4016070b07004480b80b241c0500260000c80c1c9058010f4410440b0070704584440f42e100ca030255521800310303071f84010b40d079980c80070403240c4020b4021300040075814210003510303001406030041c1c04a10008020070006000000f221f5001888072845c1c141c0c11414810401e1141200c000240a29040001c12518403200c503100802c9855001e001c0c040040620305140c201c8669028031681c81d001840da032809400c1c5480f16680041c4103144c05840c142d030b6911480e00000b450740100101d0340104408025806c000e40c02c4a800c440750742c001d985000c0f1040c105980078100440001d0600800401061201c04107001966844c0e0016007803000c0385c40c2501d00080a014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 133877949 1250 133876699 133876703
    0x6110d0c1d030c01020d210204080a060e030c0a1b0503150708010f08031b07050310060639170d050402100206010b0301031502130602030c070e091216050303010e0103 73
    0x8800030365141c0500d00021400c1c24150107801412170414860f00845038041d100040c807001d44c0c4c4141c0c1d0b100d0081d04901c001c1c002441c01c400071780507c0c4074900c0c081094548910010859078401d010030303001c00d08041410210681e01560b9074059184070420b20a80364145d0740010781c18003c40100054415281d124030b840703503c05585c7c032055680c07521400c11040080d40110700841c2c2c024010b192102c0024100055500d40c0c0c0c5048400b01c650303402c0001d160070050200015040d031281c104100c07481d001b211021766903090f012002109494211451030580810303c4401501071048006070920840b50140000c845000014650300c40c5810140da001d030001303883c2280030712225020585020701c0803603000d040c2c40b040010b081c075591941d254080091400007140e180c180d030800c462071003c800c070501c4034003d10464002e5516800400006800e1024503800042a00007800c1041070724440407a080701c20714180104952224201c001c8001c4071599180014460f200000001c00c47c5850780201c641203c2c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 133879199 1250 133877949 133877987
    0x20109060b0a06050405040b0616030c0c08010c05090402130e0a0e0f0a080f070c120c15090f1505041802121303080708041103060703020a0207120209010306110d0c 72
    0x1d20210180012000036218100011304280428051b07440d140d004107840d5200101f0f414100300c01451100f02c602c40c0c11350100c010a43c01085401048003c4009200800c8044e0007005480b000490150542c820000100d2050b079000070f03008000740450350b501c6c0150a420058140c04e01e00a11407000900d8100c076103d07030500c1030481d02113070040d0015040c0c905aa212140a05021a01e1520000d5420005c8200c6002c9030507030020842c0c101100e008203c1a024a0f030030350b10149040b2103406500c56400c00c840400c0310300c420500082d401118210200c50b031102817289805080d440485450186402980c2c613172801c0c01103034862070820f0300540001044010b101100d0703151840111622190008000c02007581d0740000340c0b000e8010100183c0c420300480c03880310341c200c508000030b0804104844c000c002c00d5010410001c07440d8104001009060701d00e910004a08180d00060b0000ba0148401860b041c0c5071113210351a81e00c80710594001e402c40080c00c0c0100032103440081e001140015483c4801 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 133880449 1250 133879199 133879211
    0x1306050c120f0f070507030b040615330201140a020c070f060c020910080d02070303031a031509010e0304061106061c0b0402030c060d090506010e07080c030712050702010906 76
    0x4520320100c410025007840403a1505100f010700203c190084241075415000c0e036100000450a021034041c400c0f0700c203010000b9074500c8030440a00c02009600550350100d038042c1c00e241c0030b1400c10041e40c180510400309581e07102070408201d000d007521006e09690005614188138035980150060540b0b000440c080d02c0500e5241c1d08421a40551440b4003800100440740a802500707200640c0c5821004030340a105415840b580910324100c00d001007040181c3c40900c041091581c50304c112001143c501d1440d03656003004d0300000355217186d4003c044113203c0440d00030409809095024a040a4002d001d881e22103984240141009205d214041e806000d1a400203a0501d0000309a00c2c441c102c0e40c01001e0085487d80316480070f5540100100d0301485200c0c003070305c410758a0030040e00300c004d1689000302c1c1c1012686000c0341440c2060f03008200c0025808140070b02d40b03400211196000061880c02d54499039002030445030402015814442c082c60b00c070a0180c8243c2c1034201142543c0125003c6c408 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 133881699 1250 133880449 133880473
    0x40306150914070e0319032303070203040b0a090509070503100602011e0f0e060c030a06060206010b0f0304050a0606090b01110a2307090c051213081c020708030702010606080f091c051306050c 84
    0x21427000303c88100060300304000070710a151000028000c1c001162801000c40307500e07940811320f90081903400c0d401051b400f004000c42c51100526603001b4000d1031009000d041100842c0f4070358480d0f11007900b04d08540703c96a000c4514455840081d040107a102201d0440c14000700c003070310f160700c00d60340750034060b00b8144045007072400010101d040301c0c2c66801083c83c0200c00521a4083d80024000711841c0c0200302041001c40c0540c0126030241c0600701000032603a00c0407002401d004049815100942c0101c58480f000c1200c111704400c1d8050081002e440700d51130900480c2c10110346801c15a51a0315080d100400e05030f01002416410400060188454451041c80c0340d1b4071001c80390040c0b003074100300301d010701d2035040c000303180b41a41d400240503007426070036540c0c51322540085800c0790040c0c5d5140c0041203526800381c0301c160404001c031070f4a01c540c00c001818a440d0703020808000001c42c03c2c02a5807103a84c3c46841120940c40c80c207045000d50544442d0000c010364040d02c40c04800e48138030002c80907 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 133882949 1250 133881699 133881767
    0x40204060f11211c0f1b030b0d0204050402270a0501060203120a020c03041d15010815010c0f081204050d0306140d080f040306150914070e031903 64
    0x103640707004043c0342075402150803035581654004c001c10441c035120f82a503038250040c42d002e40c0f01000018800420004441c0105007080742c0121800c1d010181080b095802940322040070403000340e01602d020a00303940c2c074008583c03103030340241144103127170742d0781503103941004503403902502079000e85a05010796603035404200ea8a01500000f08100038400020031141c4c080c50f03000b081c1d2490b10000f506e050a60f201a10030102e03000d05001003100c0c40a02c200441010542e009801d140000d0034a01c1903401c010342c581f0345014032000c040d4180901880000b007803201c00008103030010341c007080c1a41c0e5202400d1100382e181006643c2141c5900c00d0301541c1e620540a0301401c02900c0c0096035100440d06001c0401800155849c0141e5401c502005203410411b83c0da0000d1000c0c5000d0003010680300103d00c0c5000d90040e06500004c801c5113403542c503420f01da2401c0f20b130582012680c80e00c0c482c03800c541c0f030010307041c85c100c00e6440d02060300082200e001c0503048081e01c2411195910814070085641c03030518 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 133884199 1250 133882949 133882963
    0xf0b03060319030905030d020a05010606030507050406080601050f0c0a05010506150706110906070305030f0105010914010f171305010e0604020a030b04140105013c0b0c0309040204060f11 82
    0x303a168100b080510003a92241180c542854000e140003402c00ba61000420b00301144107484a00580200c10301da010701009024043c02051940f40030070092400d6540117000703001d540106800c0009882c00315646070300c40c00a9920461b104c0d040f00b580c0f428010710060f0366240804044501d5420440000c0350b516082404001c0d04580d1440d2518010507580c0d80d40003807855203e050309400f81841542925160741c1c01403c400c5210391141952410a040701800c0d45005900182c100009400e0a010060b92030140c42034056007030900d18810800d0300025190b030800c2c542c030381aa10758203a0402071129184441d10040c0c0b800b88008003e0101c1c1401120f8492200301c0e000394011644134020000182e80402e0144c0c414000ca02e540748101d41c80e04200c0c256002a4031543c1c40c0501002160210342c584601c21301086204042c00402100a0400c080d50249502c6000d2040501141d1505041401e1088511042c4000c004650366500c40402400841c500b45840c000548519130180903100e0000d120 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 133885449 1250 133884199 133884211
    0x30228081b1902120d020304020102071208070b0a0f090809010f0309050c060a020a080307081006111e010b0a1214030307050706022a0604032c1c051002040f0b03 71
    0x201d00c2e1840326410004003900e4410a802184140403544110030141009011510205400503a89051a000080c0b4100c1207030040c3c008001404c000a00042c140821a8961039000713030084076a41da9030304840010710a6198007226903040c02d002000f00308031440141040c0c1d03801d13201c1380004903a00404404444807181b0081041d407020560b41c040d03140440182008000c10710403182c1d41031985da5000442d8006640e0f030404182508103121640341c0c00098000500032a1822401505000030300d2540c41c84a040c1c0300414500c03084601c110060700f900301d4151540080c1000740003643e2800c003034441414400d41030f5900841038010508041e80841100d00400c15680d5881c2030058940342c940c0290312032031402e2100c02070404034880044801e00748480240444010b0007c0c0c0c641801d025104100ba000f01c10a401d0030701c04083c1441c0d940e10240c40c580841034448007281a155450102d034142e174803d01602ea4422040b120300540301c0390f0000c00c2074800030368a00359940e582d904902218003040d0340c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 133886699 1250 133885449 133885501
    0xe0d0c0305060a0618050a0902150a120908030a0b010509150d05070e0d0303050a0902041a0102060a0b031b03070906151b02010509010318080a020a0b101208070303022808 75
    0xc0e170100002a90030554001030030050000d003100c0580e000444044950700c45140c40c01000c00ca00c81c200c1c0c0c015007000c140390124407050084100f1a968442d140c4030082101d5021950f81e250100307242d20800a8425008029250346801e0700c0340600880c075a000041c0c1b4060042c20a0b0000300c155124501c800014030f0090040e00e40c0e02c840b50b03401ea000d084000c3c181130340306540340b84a2025a80d00d005404c16000148142d22814044e4000242400002086a04c2d40d5041c122002c62548001884e01e98040d0164a00603841c1002c20019080613241e40c07103007510742c1c18003802044087c1d0700e400405d100542c64940780d6440d2800940f90303607080d0703c1c0305c0d01a000c10320074042036516500a4018600d5080d014820800301c2206035103c0c2c5aa401c000c5001005a102d400311408000094035010b8000c05001f20701e098151a04181c086100854003000b8108100841e5000416000e40c0694400c004e89000750444a10b080344413501100600064030006510100401c14891800356480400010420 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 133887949 1250 133886699 133886729
    0xf05011406030103031b08160203150903040504020703021c0906020601060908121b07060305061516110303040e1302150306012c040f020c07050319030c030e0d0c0305060a06 76
    0x405940d200b0018024085201b01d100c0005c0000700001c0003400b2075100c0b518002d400c411540181858400011800c03403040079801c003480981d41c3c0000a407001c440701201c0160343d420385840c0407800c151441240c0c01036848074001031001d881c2c21a01400135030b4501c1d03080303808580c1c0c0c8040c11204021188030700d40140e000b52002da104054030a0040055181c040c04035060502400295490603406601c03070340000b0340d580144400b91401c43c3c00a141081d442450342c0c00c007902103905034181f254200d40104030919621032041d00e034405005807030003801051401e92817440c180c9a8106841e0100008a10030410300e401302051032030007010b4a000309010380d914070703075a4401c0c01c17540109481c04041025000e1400302e082039a0b82c0318058000b21005000001d41c490050b0309030b141c41e051054204034800d400240e051a1140180718540c40c41343d80619010300007803200d042c10340b80d070030a415200781c001440c403038035505100e04084041e049900c140100c1d559030307641507035100880300c90740114040540c48007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 133889199 1250 133887949 133887953
    0xb0108041a060604030803040303060f0f0f050d030e0604090506030111070f0b250e13090b0f1906060206070e01020c0303070305071505240f0f130e030c010f05011406030103 76
    0x1c0d00c0781d00c07040241c0b0350f6140a49a032035620341508100c804030000b036200c00c400c0c00080443e40c0d0840040c10680405c0145604003941c2d42c4491106000341344c0034201907c44182894850481e02c80020300c0600b01c01d13510303038449507a080500002c9030050300039800e0800e03400410710360350100c40003980c0245404041c03613001d5440384007490010f00240310b000c0c2e012020700105402407000d020390311320984804074580b01010603c041415155001c074802c91510480c0380c0070034010b059507680000c0310200c1d240310365104200500e070022110000c1c010b181c40d061003c00d0395900081d01ca802043c0d15242e40700703240040c40c01280c7e14004190340d50f4240c1c01c284003c03000240620081c00e0f04038800c04d46041c000000401090807920103e5079a101440c1e80c1e0040246110080000401040c043c1e540b10350303030700f8104c0216500421405078940141c03846c039a032140301c030b41a50003154081c00340810740340c0d1410300c0c6040c80d01070700307040780d00c2003546103030400000d2007600b1000c050991324005088030741141e18507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 133890449 1250 133889199 133889243
    0xd1104080111070c1412010507020a050f030a090605032d01050f1002030a0e0604080f0a02011206061d06070c181104080a02091806160e04090c0b0d0902040614040b010804 75
    0x170031021380c0c00000104150f0300c00e032000c2c0509845101c3d1907004100010b141d040c80307840d0112029400019030010010500e40a5007d41e100d8182c5a5604141d03a503034072070116003020702c02a50100d003103800882552181501004001504a0340d0844402c0600441e1408000390001ea069024001d6401000300c4808a4080c540303001c100900184505d00b020b6517440c50904041290640c0356041e0400301c0540110740c0c00001444001e104858200020390030318101400b0b040401400c09842080302100321019901c1c0000c990320654000391681d801903071806800804840210072640c41402d010400d40900e22090549088400481c01460140c0ca26000c0c800420782c00350401301c2e0b1130610303140e40395400030400c4400d01070345606a180902c003000c2d131801411070f0001c00815208504200700400418031107641c49090385c500174800d61765403071840d40d024001c00c1e915400a410a05022000650100e0700c00001e005803000d07038003403194024400044030a48011180200850b10805042143e4082 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 133891699 1250 133890449 133890479
    0x124080109110405030f010f0c0f02060105090606041d15040902090112080c07120201080f071e02011d0a0c0b03070909150b030f061503010b0a03050a020d1104080111070c 75
    0x22002c1150b2600780c540d004030303041000d000c40c0c0c3d0b170b420f82d11350103022039603a0240702d8a0340881039460040d40244450500940319007061050750700c20681078011910303030f80e51501224028086594602600b280109440c0d194080c00ca603a80c1d0201058a08074006080c00d00681c240c0a6005100c0d80403a0708040707035041900700d01102070350030603418071841c41c1200e8100b01c40f03005092488141ca4540340319100041012000501340c84442850f80d040c00210f40c0c0148070b52032195840e00041c406083c80400407030041000600c14003921510900600f9840004501440c106029202038403005846165515143c0f0058880e000001c0445000f040884c00c42c1d030010701c3c8134015044000c2c9090396144110940e40003507640100c01560541880030714a4030759800d07814801c004403000d0866141005008250260101042c28540c403600000c52a840650481d0403260303030b402080004400030141511070390040e019901d01503281c1500d900c0c00c611507400703035003806034031030f00e415505424441d000008500c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 133892949 1250 133891699 133891721
    0x40c1b0602070506040c1a09010905010f300510270b040501032d1104150308040608161d060c0c040509030a0306090b060706110c07030b0124080109 65
    0x9400e201c00e90000e6400d04c0024002c601582200100038185107100c2d050185400e1a0440c06e102000b8004060b40c12000daa42261800d0a0400d550411248180c1d02c00000030401a00d6045c0640e94161038414480d80711002b2110550400c91075a0301091070000080c0c900451081d821f51600b000040c400060442405503004000402e0320702240000c103051360801e03003044070007409400310032011164400380c0406071070b00400d02d1a030340300180c1c85d50784081d01504076803405191504085c0c1d66541c8441158002190f020707002545e9266590001420130f0030076909038a011911844520003a48034a005881c400904040100085207a0080001c1035001c980044550b0041342c000750220b0703855200d00d61060128001442e9070f0301440710014125905504500301c1303e4a400d400d030901d911100c01b0307240c485d50f210030000340100da240f4040840e8003a1682580c03141c0f0560350040300700500c2e00d41040c12204482c9013079500f0042e03844010103401454070b02e03c00040d400e02c0104411fa0241d007218103560303 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 133894199 1250 133892949 133892951
    0x50403020a1715010b030103120f080a020f0903060c0901030513110103050711030a030b01091d04140712060903080c0405090a0b190b0702030c01090312050309010f1415040c1b06 78
    0x28103803c10510001c800d80c041820040088010000d0041c1c20303090b00e022580c0e529050b40c01009441c80600104000b070040000d1035030209940e034260000504466100100030101d40c0307030f89030000703100c80039501c903030b001710700103410100866a40104a120140c3c02688110050300c01003d4400460050500500c80d00c2007141d01103041c01541c5051005000c0c250302c590b80411507501680000d0900c2505902981e2411002040d081c01003170300303011064020f98801c1c1c001c00754503081100d44e841c104094000c1405021140014020000b00340c0c070607003000b44641c9034101c081d0b407003550b071030307258002d0f8030625030050320b0000050403040c0c043e804103080b0700004100483c151700c0d83c030300c030242045203401981e00307450300050000544c40d0400c80c400c4130910034682440118107668130410b1000e4441560024003c0100c08218110001c0d000720542804445c01000800040c44490500f0f110a882843c91100b0080284515050a0040c140180980d807181d07080464001e10300100c0c2000190103650503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 133895449 1250 133894199 133894213
    0x8070302072310020d02030a140708040e011707030f0f0624030b090a11090a06360b101b05030316080702160509060d050d050d0c050403020a17 63
    0x180021142da9004541c082d50b40085200c2103002d01c8501410200c4800641d40301c001c2c0452600e600004840850800e841c21202050500c2c0c82080c2c20701407060010b004510200b804126081110900d9040320703000f070a41d050708221680d40a071500c2c000d00028090440241c00040410410030124041c02d101e08000aa044c40f01804000c800d00d00407501000803180d024200144818081481c2c0c11040b058003070900341c0320541d166121510880d0807140560980c00006240908607440003008201c65440041c260540303d403030f002e54545142c02a01040311110f4107076085e90040c450f2008014018141400140c44d1000c1602c201298000e40d100042003a00000f0000e04280051400f40c10060024600b00e00003a0010344282d4005189908540c404040e807855480341911501c112082500c120140d52520300c0424035010520030301030443d2040054040c0402e9101d4010500e103284107d04100c0024030080c12141d900c514400a5841613404505220315511800482034540000c0101d4840d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 133896699 1250 133895449 133895459
    0xf070605010905061011030706110f0c03040911120f06030c12010203010f150c080d1d060a0f0204080601090506041b090612020c03030f0c160507090b040b0d0807030207 74
    0x2a200242c100000c1507403242c007480842d0505840c060307060002401e01c102c1b8605044e210590724022107801800181e29031b69441c1030081c21100302d0b900c20030f2800302c07075035100d100042c00e9a40307903c144140082c05191090f4440c0105000c000d03200c900e07600c052548020b86603403010481040001e4401503142c0034401b115402607907a2541c502910195200241c0c50f5850018007021200c0d81d58404480c07500b401c040b00200c1603101103680e07907041d4041031032500c4074551103142c1d0080c0710024030000c2c52500c4140031140c0c4100000d500d80300751522841030100307030040c0588a0603070260b80304060485d40301c500107211601d11030f0042544580301400c002086600c4000042c1b42c0e0a400c103250020031340008051100c940d2203080e0410301d1b00360406c2903140030300301076070a0341c0c9200003000303803801030f0585020a10b086e50072401c5170092803000c1e11007a9010340324100284c90702c00724810003400a1815007030018a0410340158810840014403104840714030346c84100b9140e0001404900710700bc0c81c0c0340428 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 133897949 1250 133896699 133896701
    0xc020a0909240501060c0f063321060e0312010f0906050603160f021614030601050a152d080103020103050702280609081206100504080d050f0706 64
    0x1440c5004403452640c04440b0308520040c4944031401544280c140340044c005503410070050328020303a202c540284100c2d00b500300000100b100d81c0c403550000c000e01005040810265500c842d4180078515480c19070741c0d0b0794040c03422806040141e801e10200d4011602d01042195001500811030301060301e207400030821842c44148026000306400303188141d400e04c141e080c01d2044e00d019000039074040c1d107507040441c0700c0c0051541c0902c100003042144522175000920920586010700d0b000d50030010020f07150801d20030411030004c51240a4420300000160760310b440101d130340c1280c904003845114110040300c1100c45802d1b4641220700354105421008402425400c0702c1146142d540d510881d0b9411440010b00350703240640304204540c807118030010751510300c022031555100180051101580301e803904034003501710399001401c40e010114000199001401503140300340d400303e81d4103262000880c2d00760351500030380c06042d07480d6109010119006019400803d80b45034a0b00305136081909580c0c2e2381d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 133899199 1250 133897949 133897961
    0x30102030c04080601080c010c0f081611010f0215270d0f1b050d0f0333080a0b0114040e0609010b011e0c06050c09090f01060914010c02010c020a09 65
    0x307030070100020300304052034051000740e01605060000d0442c41c0611070000b0606946801c0c0603210180f050b440c5020401403000700d41d5020f0b04a802c4401c0ea160600b03201a42c1590705a460340850f5000d902003040034404182440c18100c500c441c12400d403111b0040b8039040d202d0100c501d03515810092400c043c1c140400850008200c280c0d280b028144406100a0886541d214824468040a1201e1000481c0840c1342c8001d803140d480c00311251403c541c1c0c110041c08450070700d0a85071544107840c14121080100e40c0505488016401251580c1c411130503a451800d02400341204064400621281e803c2020784043c1d100018804511010101e40e00c60070300c2d201b540c484400343e6684107000d000303580060200100061555241d03a26028058000e090304882d010024502681e503c0050351888008040e0341c0c2c82070300030b40060344600d05100003041000c07027030007841c0c04140810000150b00c0302040e400d406001c1c042c0c1d10400a16016401500c000d2617011003268400328001e00850064020302c038003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 133900449 1250 133899199 133899211
    0x60d080d0c031a031e100204080105090d02060c220308030903030604050a11070204150308040e0a150f03020d06060312030b0411030403140f04030803042a180c05040503010203 77
    0x5407100c48040c05412520340700140f000b401207405030b00c400380e80c0c080b0340c0c1c00344500b2440c9000716014441c1201c4d400e202c0c0401c0c0c02c0600d1403010801160b01c06d01540200c1c0b10f03403002d004071540014800416a5125002c5580c5070f0f06040400c00c003d1040d042d40000c096480346141d0003981c0e42d8a0b030344d07550141d0b081112074a255910200030400186027034080c3c140c118081c00c408200804658035a100c0901c114070b4064029a110500c5a940e0f00000400a0080d90080c5049031100d40355041f484140c070041e209860001d0520581419400f1600c2c5980e00725090a03005107106440e41c0c0c01e20607117280c0d075034007601d01541d59070000001c00d07103014006035150129580001c01c84001e408000895601300111000b5200c20f108002c002500440182150348682580c0c3ea00d0b481884071403032180c4150703000205410707804000d00042144100d088915040c1030f01d40e119081c828204c2074038440f05280303e01103043c0080307024110000c2c4c59030b1014400c6140c1d407920030302e441d8852000ca403d9a00544075 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 133901699 1250 133900449 133900451
    0x1a07020303121e040b010618180e070b0c030405010f120c0306330c1506080105150402070b04110a0801060308070204050c0c03090f010908060a140705070201080a05060d080d 76
    0x4100c040c01c8104201c42c05a00c144111500f50b04003520380c2c1100c440c0500515040c040c5440c0300a508402210200c1d000308100501c00541d8034a06d040340b0f000d0206d0846c100d0480c8680000810481240001c0d510005240c500441c10546803000440b400c0d064070030013000340101e841107800c95401e54016240d83c03200d25100441c480b0300e40b56094501220344280100341d4160702c060240300003038802d900440304401c0c0c54031385500216130501a00e00b02d8850f1001846501d42880003802c81c9040d00709600c104058002c0c02c3c03c0d0310035001030006900c10040010310900b45000000c00182c040e400500384004050b184464240e01c0780350741405c40e101381e0030a41e120340300481d04504510301401016840b030746110030070b410088881c00c802d40d01d01544008601c592000d02840341c0d1030341305100354001410030600702c40403802e00004440c000c020b1140c415503484007070000103003118095400c07504c0365a81039461090076590490030b01d00628026041c1907201d01a9100c0c1008a4822405030000e90190303c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 133902949 1250 133901699 133901701
    0x180209210f0f03070327051905010909020a0f0c080d091a0702010605090c07050a150e010b09100303180504091a090601030c06050d0f06080c040e060f011a0702030312 73
    0x14029203807007203044945560780e20800512001130350084601460b21039205500161820700700c0208170a607007d8001542005881c1c03440c01034901c001e01e001044030000e07210441d1440e1180302c001c09a101300d111400100d00c001c0c0c4802000c07440307200d00306902c81c044c130121f6060910301000d040c1510280c00c0d0680d07006800d0404840d00c036441e2183d40350440140d00007000028a42404107440c0c0341e0051004044880c0860070900b13014007801070420b407551050010306200001004100200050404800360f580380032200305180c20051803036401501001c8402c0000c03132640d64200d506c0031003c015a20200b400c45000100b0b500e07940a2180c80c1c03441003651401c0804168031801c0c0c250710092240d0416400300004101045009048105407001c0d8174020b6940c5d22820074480150001c00b00b6445914503020b000121008041184c44600074200c50900444024040440d6903000980361020115030b00c400410903081c00c00c100482d1030015070142c60034950380d82c0000c2d01b9a000300402e80480d048542c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 133904199 1250 133902949 133902973
    0xc0f0a0c0510021e190c0f0f030c1104140109020c0109060204031a090105060a050607020f0312090406060518011b06060311040501060c030c1e0203060a091b18020921 73
    0x14110b0184100c0076020141010848075a11175103903240c078001d10901200e06505030521085019200105400c40210201c440041c940240762002a450a440d540400e06850b0140d1400c0d02540301c00108400c408611a428a80031400a511400f8201070395942c074404240001c1841c005071006600420000791500410f0b6031421641400030a0041c00380d01d8001006421b1783d40c4c0315210180da0381902d50075140c00c4a440800d101813100f403107641c0d00d4400c0e0b22071204400b221400926000c0c00070380e414440559076003010b03255400340d0040c590607000301084005895101d00d200d150303950480c4d16192000040c1c3e44075030b070444640e07820680703031107004000758252410540182e40c01803421345091211080d070740d1001000c0c41c49030703040201041052140ca11815019450b0100000d4006003511070506020340340a000307101c50402200c1c0d04581031141c4048020b460000003ca9092400e0340c2850f15500140c00300079031001080703560001510a41c5003084030704220b0580a099602c00810740d0b54016 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 133905449 1250 133904199 133904227
    0x210c131d07090e0106120e19060c0c0201020618070e0a1a010503010303230405221503030c030305091005070c030315060c0b09010e030f030711060c0f0a0c051002 71
    0x91104050250b41d0504100311540f581c81641122803a03e490032008504406050203010102a020543e200364a41d410300845040c4000e41010b01c10201013048208149050340c80c040c0e502400b0f80035810190010790403a4036010490845103042055a1041d43c1381c070401d08942000f940e0300e800056403072020032040f01c114404d100b6800300c2400e0450940d0714640e0000c0860b5010380d859071000000c0c1009003e403000c1001901e001c0d050042080c60181c4806000c90f030100c600c9800c40d081c1c1d81c100b1402000c2a5024003460054a40540d150712110307070551026009880098901c030703c42e20455a00c503918240390b10a85000e0402d5568401c811165420300505480d18480409408107040c1c2c030170401180c0280b020119240d209082c200c0030703950303080c2d440c0c0148400b0f04090b045000026107061070318900002540b042d40241c44001c410210340c2c0b855681c41004030385514000d18100880011496a1806003504e0a01850500c10ba0710407030f540c141c1002100c5c002c01040c60740200e001087e004107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 133906699 1250 133905449 133905451
    0x306011203020609011e0c0e031b0103110f04150903050712050d030c050318010209191706010305100f0902031029031b0102031b060a0b06210c131d 65
    0x304e0002c0c0f02030f90800035440c1482c1c5001020310000c030340c3c0c0c903402c0301e0345401190030511100c80141610700f2407480d40d00820501c3c401f40c4003640001e160501e04a294078504041d54207071250821003908003424000c445100003c140e14810910a49440000c000350041000901808203401c00c00305405142c0742407484c01c0d10000548051500b454405080d4a910809680e4020306010600c2d052189084405009100b0501c0080e0032262084200800d424221844812101e901d0001840817160384401038980c442800b0080494000b403d046044407556044841c82040d0003c000640380c007140d001a1408800d00246075031145c8505440082c00c1c2c000e08642c0380911082101022034001400081d110b41c004010b9070901100c040c100e007851b910070025a034041400b0b42100170701001c07080c2c481d59640070882d2200309107401c2000c4100107040200a44001000c1c21411600612601480039140c11006084103440e4006001c000703003904d003a0041d08010120032902c1719481c441d0000e81004044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 133907949 1250 133906699 133906711
    0x1b010207030e0114070f020906010909110a1103070305030609060f12010f0612050705060c010213060302042c040b04050321100e010303022a060c0102190e03030909130203060112030206 81
    0x44107100c00390110b4803080c64401b9081d812120006035544800041c0d90320b04a6800042da401d2615500708208607008004008040e640d07110104003991540300070303940e0b03c078145001b4000b80c0c09102182e03c2e420035205454000707030024810f1521010110200e141000404040b0300315030344480c50928042481d00c10f440103801c2d04a00303060070020684600e595003035640301c1c1034002c40c000180c0e0360a2100c01e50555a100314032542c0c43c0a101d40d22100140030350094051100d1403415940f580317442180401940f8403440c980c0020a040d03564a032a46441114024020384032400100001c0c1580020602140558180142000598100580c00400360032594004000c42041d61006101103a000100310300100000300d4000400c02428054510314007554585503007082011419100404040d0050104041100c494107084a0b10f41e50071149280035101a5800d90400c00203440342c1d042c9203410f554032400c030410900415115a010074a005800d9120700350660303900d030910041560620856400075 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 133909199 1250 133907949 133907987
    0x3050f0609090312130f0f05060108013615061a07030c0206030919140c0d08041a1b01021306021605010c1110080a0b03011806021b010207030e01 64
    0xc80d0040307070b680d500c0c441d4100003c0482404030000354910312491190703184c2e617405116400301030030600d454028401100c0d4203e94030f01640d000401c04140c14400e00f0745c1c200a59012001445c0075282010409042010400a40c0000c001e3780c0040b810306110050000104540003074228a010f001c5148611441411000e1140c10401c00740820751225007040c440b0f8045441c0b80d965107410308060724103010302454442c42d030581030060052003034440c0f01c10003a1700a01c051751084071441e0100403100c00c039942c000380445014030050241d002205146440c20010001591920544120306921016a11400c0596a4000481d0a00001410349900080c2840c2c0020861084040e0003254407030b403170740621030401c090001e409050000c1e60100c2410b0725405020807505c82d42004000b00207100071035141d5007840c02e100c240616802c05100e00701c80b0402007540300034018041e40d0340001a511261591010000100021071031030003e00c010100d491280e290310342c0200100001610740707040221860301503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 133910449 1250 133909199 133909201
    0x6010311090f09061c030c0c06020a0c1514040f030311070b03010e040602040905040f03021606051801111615030603050616032309100e1b0406031203050f0609 70
    0xe500d40c41c6204050300e03421030300303c0d03181d64900c40803400c04890400d64492403914034007040149500000000e41482c090842500295114a0260399490382000000c00780380034076030200200c00c44820500c4250a00c2c3c070348644140a0510886050b410030380041d243c010111804101b0035400c01407022120101c6000340041503d4001c1c5881603000521a41a485030703040b0001f010031034184c0c121409003464800403c12420a8103084801c4030640408a02500c2501029001c81170741c1002d130001c032901c1d99901c13480c0105600020605040c05a68981401003914154000c60002d00054a041d1074460a210b081460a100e00f9860100ca800d41300c24176103090014000308201250315a40020b80c122804000b4940701400c60090240b0a5044000e0b1061707030300d00c4d800f940210b000c1c60044101004940b054824011000101c03000390040c041d00f036001c450b40307401104a1580455031040020000a8580d40d07039210540480000c4004000096498003005100002403a02c1a004035042d0f07034884007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 133911699 1250 133910449 133910467
    0xf080106060c150609020a050c060105062712070303050a0f030203040f0807050703020405090102040501021002090a0302011103040b1b0d030902010806011b02040f091e2004020c011406010311 84
    0x41048102009403a03200004504418010030384c200300018003034034804559940706140020456040410b89003030030f0284d1000040d0918003c000d031030400e544a5800c0c1e41041403150140609108000b8040e00071180340c11040d0600700c00d2004600540c000e4a030160303200d400d150001c0c41c2503040c0d50003e050520510038800807a0301061080e00b482d40c403880441c3c0c0d41000b824460300d0a0340070380c0000d43c001e0400040044250301074003e001103c0b800c0e001c44180b842e1803181c180a80c050143c2154118028103030400141d88148800c0d00b64014000640c0e00d02502c424a0041c01d0b03011107110146170740182160b110021082000395030100d6035141c2089500071683c00200b2020000d0840c41c10400b0b002041c091403010440f00c1d00410398000c000304014200048044080d02c0d440b10b0a0714040303075050500007800310866402c9202e543c0041c281d212207034800440c54640d4902c40076980c0145c3c3c00d2202400c0b0b44401d111305d1010807107001442c142490319130001011f44007112503d03c0d90030028442910 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 133912949 1250 133911699 133911707
    0x9251403060d032001020d0c02060402130c12090c061d01080f10080709050406050106050c0604021302070803070917010c1b02030c09040303020403020f0a050f04050619060203040f08010606 83
    0x50850400c80341200a59001d060445082068106131140d40c4003150381da5500c07010541c000c00a5014040042c0200c040046041e40c44010840c0c020f1340020f09800f0b241c0d000407481e40001d04003c541d00f070602040b645810710340c040302c241003803c035100001b08005118141d045040c07170409141c2180301410440302031000130030141c009800091001115804503980d494100500005066054207e451a565a241903400307000242c4c0e066400034503140011607158420310807140308941c480010001c64585a090003105108400900640d41c0d00780070420016503010025405440c4650b158682d550601c0e00034842c20700f0b540220440d40c0c0c5000c0022010350303005401e429800310000e0700e001c2e9003465400400d007081c0d600100b1691101010041004043d0154064009d490003a034100c800c0d01658030901801d5100e0380569a4080182040c01401e07180c00d4204a52046010303000c4400c0303405204454020001030b411240143e00082818000c1e031904030404001442d842001744000c2e460008060 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 133914199 1250 133912949 133912951
    0x7151505040b060d0c09150203030117031303110f04090602070203010b06131a07050d082a0405060703090302120309040b06030112030f03140f070e0301090b070c060b09251403 77
    0x42078080e21064213094541c001c6d02900002c0240d44490540301020100c000d44980c0b0901401d40c88580d00100811086070010640e1006142050001001d80c21078480581380580c2c400c0c8254002e00ca8806040e1a845500a17501b01c98822280581c594619204050a40c0c86420342c2c3d50103200180484603c44201400c00c0c3d0459100704030b15214034190081e410458840c00c10080c007140700c0c000706a05100c0d0b00141152050307508002c01150070002485074281ca0390900014001d031401404140501d14005004058841c844d080402c1c2140d504c1d408200540040d507580d00c683d42010440341c0ca103003400d0081c45880300c0c00b02d035a1841c40d0b05101c1120040701c0900000b504001081400d020528040d51109200725614036101e955498001d884008180703003161210b0004a18005080450405001b0550020340c041e03e500b00c6035580f25002c9079030b00d110340710940380b503a00c0f03903450407044d140c0c1c20300c0781d0041d0403000c06000040301000100034012408039100c1c0c01c0000903c180607600000c1800da0f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 133915449 1250 133914199 133914217
    0x10050a30032c041404140304120b06030f01090303020c12030907030602070515010e06120a0507141507080703080c0a1d060d050f040b070e01090b070807151505040b06 73
    0x120203001148012464186007a84100e50094130b01040001642000e010a510542c0724071a501034400c4000c03081d6489000e28410705003646040c0c4000000102036449003075200901404840c0344803500c1e00f0302425240302c080203402103503002034000c2001406010340c144840c0d460001c1869410022132030b079510b1070f0364440909400d40c040f03100020858140a00303009503010080d000c01030358444001117400d400a40d13078684103c01150540701403d0f00428440a01c50300000601280741c6040c0042c0c1101d460900095072080489103c00e01050005014103080c0f80a0380c25652205400d18014041c00702c090130b1014450001c1c010751061079401905202c00012080300d9444041c42e220200c0e5060003040c2000703401c907043c40c04101e00401101e56051045005035002003150302d400c5001e071030018034148401d002a0000d0341c10301c01c100c1103400500e070141c40340000c9458003025891b8a644980b40145203040140c8a402c03403c1d50b002c7c01c48188020b054115400c00aa26040c2c0c001101845101c1c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 133916699 1250 133915449 133915487
    0x30f0c15060e060307061d01170f0a180b060409020604080d1206140d0f0204020d020301140112020405010c03051605250905060906040504060e010c050d0f0504050c0910050a3003 78
    0x1f8125460740700e4600d20340c4488013080c6092071800d01ca250807041880865000403410b01c0d0850040c14100c5070b024500348181c010440c0b003115110481400090500313050240c0e04184204800a07010404000704dc68202060744e481844100c8080d003001a100c01d075001e410282400d0303141e80e290360350360601805910342c0a61000039500c00361021401038014064400c1c8494808400000d45d002d80781c0c400704030308909a88468001d203120f40a07004a028901982d170000f1548817800000038055002891010b0359004030030181c20300342d601d441c079024144201d10220b0f0800300181c134a0f03129000c042c1c009426201e409000900d49180031454a0030020b010340c0c4542c0d15107007c034041c0700b001d41c4071900c0102014024401201072910141030307075104036500300300c1501e8424400446001407040c00d02031684440503001d8140d80c403081229100c0040c0c603101c0d40c0d070701e0060009015501c4060103401420030300740b18190204c846400c0c600780c890f0440324003003980f01e00400a000a50200c800a00121840309d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 133917949 1250 133916699 133916747
    0xd090302061006080f0901060503030a0306030b07030e07180b0d061509020c0d050a0c0b01090213091503020402070804091a040f0506090a020d11040e06090105120a030f0c15060e06030706 82
    0x606e01d80581400d5000a0b0903000c009054041541d060b00440e05413805254043c9240e01d0710310f000ca044800c05c08044150f0303000316605001260b003044e44084843d00310100840c5c5001004005005d1041000045685030713912074522888c11281c8409000401c4403c00843c02c150414a401d48c4910b811130501e4104800000c2c8040c0c041e0180050304549900000641142d6860300c050400030b600021200321121184000020b4001e00d41c041c04900c5500321140700280c0d4616404d2002035084440b0840e03005070188000b061030717011342c800c0340c100c606056002e0404140c42014002104e41328610060f800b03080000704061515450748131034021902040041c0d03504d001c980014020a0020070755240248005000116100301102c9540180011500a051a43c1c0c075410414210f040c041d102141da04032605030030100c4d00888039244404014103005509210a5036034414400c502804c0d031801550303a00c42803102c01600200b01c1d5106100750300808031a818000054044a00003410340000300a0030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 133919199 1250 133917949 133917961
    0x17060718090902012c04061403190204020c06040305030105040f051e101a1c0c021002130905010b03040510110d022a0d02010b03070f05130608030d090302061006080f 73
    0x10702c0c0c0850300144003010325400c455017905460409106401c601c00c0d130030f0030700200d100c0c1c0300308406001d601d000900800f0301558841850b0708800caa031030140d030701a0713080c00841316280003072041510a80c469a0350565070340c140020070040b0365040036294011407030b1500300f1090000d00d015898410402d0364030b0542c607940e0000d40642c0a07905030000040720040d0754203c040c00c1c000304003030129100d100c21211a08002d2400d003a00f00c407108000240164800070f200d075088485940240009842c80e40a01502c44d1516003040c2520401c0c1c0c890a540e17140081040248002030249500c0020054401d03c403041843d461550640680c40701c82c0c2007964009a40e4412600c03480c5c500004104005a22551080c540c000c19200c02e5084000030141d428607140a4040ca070208084054034624122400801c0c10902440925404d103c2d00079601c960b2140c002c00c0901e000c00c0030303041d0001000000304594000b880c00a08100016141c0409422854810301c54107402c0b02c031403039000952646800d00c3d0341d102 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 133920449 1250 133919199 133919207
    0x90b09041a0a091a09070207061b0b010b0307030e07060806010e1309080702010906030e100c0315140f0603010b0708030702070f08060106030c08040f0303050717011706071809090201 80
    0x3034000c003584a03409030030014049115030030044130907802d604000f0f11070520a0034441c85050481c0c4400c0141c12600082c0190750040c2c0c820700848080c030804400d0b200340c030341d1140384904081e0007200b00c0d03400203c10011101c2d81070050400d00001d0303401803c2c103d843c100001d03003080c401600990500c4156a1404007645490f8a0703c9015544040b041c80640c0c0386081a000d19031104034141e00061140707a0100b01c050082c019495910482e40c01000140c140c018150003c260380030424041540344d0500c40d0f03d0003242140000505905000403429400c0c1004009854201d000f01078000d01c814001041944040c005032140c90f90003000665076030b0b440520403800d1900c29081154201c4803a440441d0079603001506034143c0720300d13440400828213145400c1d641f41c0812100140645200080b0000181c40390300429000307121801c04d507c0042603416001089413090b044151011124040003081d1442084542c1d04a001810030341c5c002e0110101000e20f5a0440c020600d0407070b03c1701a88011a441 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 133921699 1250 133920449 133920491
    0xa030807050f04030c140a03030801030f03110f01062c04020d02030c0303040806270a030c030e04020d020c06060a030803040f03140d0e0c060c030d050903160b0103030f090b0904 78
    0x3032001d0b96a550300c030b28010f80ca100c01e5000340d84031004a00385190007400c2034654102030b242c2503210100941e180d035031010602880c410085040000c4206240c600840c00c100d1102008684000032404604040d03070319440c0c2c8540b10748400241000c00d2015000907035404901e8000e0740541e82003c1c0d080c003070f0010916240c5801007142d01480002000505007501080440c00742da04807400b41008002305200d00300d03000d490301a0080507046115003c002034003410f1003001e10340c488d003403001002e085200001c0481e00103040540c442c64002072841451201845078540c402821181c20903a01e043d511400c505010081c0b0051410941006a006050241c6581c810b940f90f0030480301d584100780311043d005852146441e010a01c83e0764840310700e5140c400700380d41d81741221800440c07c0c01c450180003000f41c0806441c0d030b10503000400513503c420f002420403040391070040014603140e51451400501c2a44044060010000b00c440188031100e0b48904484052070f0403580400c00c07510485411145c031071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 133922949 1250 133921699 133921717
    0xd141c090203280c15091404150807050405090607081602011404060608011a01050d09030e030d08040c06090f03060507170907050312070203030702090405031b010b100507050a03080705 81
    0xd141c0c62040030307119160385541052250700380c031051356512142c6498440e1000f0800c4049075441d1418016403c440c0219140e0030401080403900c0c113104500307021034166541084205420414081c0402e00b418019a50000d0502d00180340c0d900d441d0000072b12284000c0e1240280340110149160454800d403c00c510240690745014030134202072800300e000b0480b40c0700d20310141d420043d04411421150442c070304260410303102c0515100310544101e0040c01c4e013450803000d212280d8140c0490740c80400c40291002e28546980c2da841c181414560740010056110400f0009507440501030201e14001c20000c0b20344c00724010980b0b80302c20005503404202004407a200d041020700700581c3c4000000d0b2101110820f400340c0c0c80809800c0e5041e200c500c5942000313505035004029140c018240340300c1c4c16a10900600949080095408207050031200c84124522503030b4545007080c500d880c05c42028500103550303051451900003150394854a07010026005410b002c282000105690700403001c45103000c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 133924199 1250 133922949 133922983
    0x50909120f0307030b09090a140a0503030c03040b01050a030510021309020309070e06010224061c0803100608060d03111903090906050105031b180a080d141c090203 72
    0x850040c0c074101e02d070001c0703030b4443c00603003803020b403a0f06030401c0380c0303001d00031211f0401400705400c01d80c40745110741c51030b00c0c040242442020b83d04001303d002072000d18000e542401c3c00780e56a0a09040010042006810103842110858130400020380001484010ba8000d9100035880d9000031070341d5802ca01655010f00491800002000207039500441d0f200c00341d440303d0020b1199502d610004a1707851022540d42c51b044018003c0700421000381c00c070920380c492001000681070140415001203501c00640f005c40340c409011080c814003d00b410540006880b041c90000e80a141c0140080e46c07068071f50380050140b0600207031858002c0d00c18011003101d1080d5031282c001000041ca0001c0c5200389511480703190a2400901140d103602c24001c490051400c00350b00610040c680e054250560301901c4540210002c0008580d17594540521010060081e0005001c1402c51980040d25100c0d5035452111125801c0101c00a06880001001a00128540c000070500c860380301092902002e44500c100e05 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 133925449 1250 133924199 133924207
    0x6040b031507030e03091c03080a110a03150b16050c031f05040606030209010b0705071203050703050c0a0204050f06120606010203042c09010b10030b09040809010509100203030108010b011805090912 87
    0x5625500e0b040747c0601d12035500c0320015650500108111041d100d402200b0580c01c12581501c1407094000180443d42c05003410b100650f01c001440c500c0d4080380c0382c861a0b203200308004050200a100c4440000410342c06031001f0682e15500d100344c0010032808850b40e680e1900440c050103155803041000c0c6601619078169540c44030148401c80d00092400c80d40e0703100e101000305460043c5005c1d0441c850341034a0f81c1c2d05080d03080c0d400f5071380768014002e080028402c0050090141c0d40b01c0c014107000340c1c0c0743c103026081303030801c002070004980584c1002900e41d48400e0600c201c990340001100e003160b00c00052026503100c100c54160394019a1100c01814800520602042c15810350000d80494812a0b1108404008540aa060741c44540300d0561100f003220000d00440c5e444002801020414540107143c005040005214600185050070050f030002c001031000780c00901c11207000320024202a40742c040b04a07500c03c540c82450117524082d904070008100d903602c04210083e52200c0c151205030316 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 133926699 1250 133925449 133925479
    0x50a0c1a010e090d0e0303120403120204030f020f030d120b0f090a020c1903120c0c021228020904080714100e060f04110f01020c0d050606040b031507030e0309 70
    0x50710100360f520700303214024003849a200314010200710080040c090083c6042c089041ea07001100b01c1c0050069051100c00b030102e001d21003252006201846c81000075145601070740c014450000020a0f030640641d1003001c4400714160480d4405108441d0018089110b1040300082401c41c0c440c4180d00d03810141a0f0709000f440c80c4103401505410303034004100c031021405041240e01c081a00d80014020802031220700305254900d030016030f549079450a0001c00000d860f808100d02d4203034101165442d4000a000c80d24400000030b42d402040d5003002c0091180714075800146a400018cc030003000d10000080000410001071010034542c0010401c4c3c2c2d401a05c2022004041c04441d03400c0d1a141c0640c00015072071740c414602c07444c040c80c0c20058a032001c821030024042c000300c03801300850540c45841006102683e801513800b14003842003010f4049420500c0510040e41c0070003550a210307030040044180c40c102001540e41e8804801c0c80c0100701c00c40080d10480c1540304441499400003050002040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 133927949 1250 133926699 133926719
    0xc09020d0504120804081b01061d040b07020d0e041a060c07060e06180f19062a03080f0c041503090506090a0c0b0c030d02030a0b10020d050a0c1a01 65
    0x48164002d9003191141002c0241c216140201105c0091078860f040c052000c03d00c421030ba42c64a440110b40000450a464104d11084c1442c0110300c28801800c01c02004108030782554034030780049031800244808000c42401030302e104880d596060141d039030381481140100603049440760725100a05150f030359a0b0700b40401511170304240580000324440c10805a00c1d814204100d40c4000035108000000341030547c208401c010b100003030f00307621071030201c0030b04503004081c00001e00400403510b4410910343c44070b000c034900c18220040240803079099641e40020070b403c8000ca90b4440b800d0355841e4025900c0c00b54030840360282c5e0300422001d00c6400501c0690307a41503400400d00301c1c09902110f8455550b400035070b60320000900c1c0107210b02c4400d8420860040321b88080c062021688040d00d042504400c040e030207c0c0c004a03080084940c036810740c001c2501b00211030b0042c0610901c00b81c01843c2002801038106e209010040d01001b90605159041c0020b1559146401004100760b07802c2c0d5a45508501e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 133929199 1250 133927949 133927951
    0xc170106111b01050912101d010e030c030304080a050c07031b050d020f010e030f0f0604110a03050c010e060403050f21040302150307020a1a090d0314130c09020d05 72
    0x5a4648500000c8807200d8022600001103260141d4030303685084813243c14800a101800050b07500341c4110400034844400c9405231000c215800300c00c50003142400e0359007900b510020207d02101d600208a4128800f40c044200da038040d821820507940c5400c1079034200d506200f05043c442c000e01a543c0044108803501c400c0609a010300c000d1400704545400401081555402c0001d6120b4141414800f031540124820045007400400f0b89c5c10b02c0700303220070f03503800c00962500e040803d070071010810040054241100b00c0144050f90000d03009030031650707800d55441040c0030031410b2090242c250825540c404080f0b6004d10b500c217064030302c0c841c41c55201a03079038810800700d85030701e840c1500310f90b0810003c8000d48044030b4000f004032514903241d00c0f142c4582c0d803010302040c045005911031040800d010300030481d485080b07071480000501d4422005030500160a00750310030035007041d006070703000c008181e500f5800c4271440000601c88482c078602100b0101456005182c001e00210f500120400d1581c049 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 133930449 1250 133929199 133929227
    0x18060602010c110d030e03090d050c030714010c0303090503041206020a0801240e040f020403081806040f0e1806010b070204140601080714041802070203010b030604150c170106 77
    0x7486010b03014074007903400d43c9021440d602103510640045043c1d038842d400c0b02c0360400e56041a47e1034195240c020541c0d10508280a45180c5c0c072a241c00c0c0d205e800d04110703560082809641c0c4052880381480000c003240700130507028042540722040007060007001d2044030024000486094a180c0d585d1a00402940004c081c0001142c50000001110b00d441440b030030bc00b0380c00e040d001e000b01d000780b90b0980c0d85124150320a600140e440f182c08200001900c020000703140554211500c1e40449031a0b403562103e80d58143c0d0198100b8041008040c110251400c01d51324103040d04155680c2301c003441e40c22a5412010069a0310400c7d00000714001ea0400038111140240e42c20310820114900851800c00c007030310300c1d600041022000a803842e2140d810780d8050302e010030050389016030f00c82690b441c000c00241c060209560000d112401c6103400d2055800c00b0100741d0107400700780390684560502c1030740300c182c0300340c00740e240e040c0c405c04c0a105010040230700000365881d115550f1144130091144070386441e2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 133931699 1250 133930449 133930451
    0x62909100506030118111209100b0306060402070f020a030b06030c010203040e16050f07080409180210051b0115030c0608090a0f0f0602181302040b070206131806060201 74
    0x109080c020035210400079100042c050074516442c10b050700c124058408842000c8a40c1c62421500c1103144500a00310758009101074061800d02c80345841c1001c100e0402000864a01440c03c52203840c0403076031a074407120444005850f0846030510362911105100c0095101440324404020484211529802032209808550060505a00681e41c3c1d22a5001d018900c038440307000148040000c030702004408109180c04c03820112111079150207604111800c9504076804207083c01404800d01c5107c17a280c40300c5203d0701c940a46500410350721400000e180042010000d580605180d070804905440540c80008221036a11a079902040c034030320740000c90b100a100107001807060b1254403018041e004c1040500410100c03a91820103aa4980320211640403852042c580803074201d05c06407002c400d02c00c1c080340d80c0485c10410860200c8810a883c0740640c8140002d02a14145106441540d0750503130300c040e55001c86144561544a241e40304c01e010721106492942c00c0d41d01074000c20102d85c200c5d00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 133932949 1250 133931699 133931701
    0x40b1c0320030304020913140102030108010b040603020d150b0a030302010e060c04051521010915080d020d08190c110c040b0d150e01020d0e1b010503010e04062909 72
    0x88900720520703140140c1101c42e481400031034098502550080c3e00402c100da120030001550340d460441c20100801c2c0d20340b56940c044010848014203000c0c00881796000c032410860303907003554001003160002100c040c2032503020003060300d0603109a0740440640803000302050318182d07403071030024041d010b40c0074056058007071078000c01c60494207001a40c0075507000514100b100003d50f2707500741c003c2d00902e80c200341030501061303100d00700501d502005010703200701c01000c01d0260480d05800e0199105038408140b50303000e4a54844000d6000c40c21145840040c68000300300d4440041c03510022200103030803100140b5184810040a40107624601b09007060416581242030410421003211912039600d41c000040a0b6100f0010303589a607440303512020b0b803c0000e01c03058118030241c00ca07000301d43c0c0301c0001075450301c04008a00007001202c5030352800050b14040505d0780d60000b09980418464121784034040c0d8040303070801c10141c004640144503501c101101060402d0f68069500c020125980030b125004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 133934199 1250 133932949 133932977
    0x1820070c1e0b0c0c100306150f050a030902060418140a09110405061201090b0717010503030a0c03110d050d06060507050606060a020a0209161106010315020702040b1c03 74
    0x40d4405100020880700c0741e14044460780c0952042c01e400b2a5406080c8298206a4505e80c034099054050340e000115181841c50004c0c01140c00001c150600c00251610100c407075005003119444031b510300c0c2c042581001d80c030200e540390040d5003241014040032140051510320341e9100c401e103490b0680030504140c40b50302c004402c60305c1041000c0e0407500215400b100a0909820444d0000303400f44c140b100c8403458007191030031500a038a0498000b1459028040c64562083c2040c2020341c0034000c6c46000d51501000a44e03e01c01d116444050000100a6401b85805201700c007101302a0360082d10751201803014010003d034482548003106074580700303020400b14420b60507544401d40c4403005104c15105d6401700080350300300b004800c0441c8504085000141c455040180c081c26000c52200c04454044070041d0902c00031030030342c0400c1e61041004101240d1590315105100001040040c1d6501980c008503020f405448a41c6412180384580c40e50103030a0030002150140c025a69014044003031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 133935449 1250 133934199 133934219
    0x5060411120412090b0324060c071e0f06020f070e0402210102090a03050604060b010c03050d0903090b0f130b0405010903140c0306160e010c08041820070c 68
    0x2241c101104035411000100018825510802c583c3c0c040d050074450305940707898080c12544100c2c0d075120341501d40005583c10122a04a09180c104216a19400d24031b003810004d607500c9451091443c05844022030b041c010b04182d41c144041c1c440d03c400e00100b26125000a0f5449100005440c4a8411480c0c00518020080d420b60701450b402010345007503200315424000302c0080c2c902444250b541c05c0040c501e01fa030700c83c000302004522480260141d440d05080c40011500c2494100e41802516080c82c00065807041c112107442509a10001e6000e83d01c0c1811110150f0a8100e1540503000084030182c8007031440103401010b0078001e0700e40701075440e41240b000740e0050740320319800719280a005000103580305112503400c008a030100c07a00c2c0103040c8006460584c4c00c1e101400e59080e109910301899a102401b240b2544d001e08102d044d40350f559980399058840d40c0306050414a01e2101010b0201058016001f8861454400a65a48801e100030380513800104115200c40714510b001a280740a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 133936699 1250 133935449 133935457
    0x14010e0a0c05090c0d0507030e0304060c140304060203040e1801060e0108010e07050102100207061b0c0c060e06030403030b03010e100e0d0903170702180907050f0910050f01090b04030605060411 85
    0x35907180c05d090030b506800c02405400042c3c030321800d260b200d019400c0703018000c001400003042c0e00c1c1c0e5402e4050105081004540900c80301c0000030f9041040280302c40d1380c0020440d81201e280001d4414103688084042501e15a0310240062550a00da0300180c5600c20b20240c90503518a003000300700306501030303050960b10400d81c4545030140c0c02515090124000d80e502070b04080b401140c0225900b0348011441446014603200e400200740e81e050140f0520000e510204058945400c0020042d0001c01c005451760000400042c10582c40d41300740106c83d1020342000415404000848003000702d0308044034007030144402020100e00c035104134507266902c5080c0c0c2904694205150003440c0c203030300c042c2003c01d520a03c0140d820603001001410b4142074024a140704c6c1803044080c222046c14a0104a400840a500c1c0b502c82d035651001d0041e040c541004140031940b0840d06807040e0020314005031400040b59110806846021400105122013a00401d2041d082190308109000c00b140301c614031401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 133937949 1250 133936699 133936711
    0xa09140105040b04031110050901090c060203070f02150706050a09020f01020d051c020405030703030c03030b041112061203180901060c050a0b060303190302070501060506041d0414010e0a0c0509 85
    0x8006000326021901409441e4042c942c1002504e107c5078029101000759a01a03c08040680d03403100c441003406015880f42015120314400f85291070b00c16140d0015891460300c019104048041d1600e2070703401c4403012202c42951201c0c0c180034074a0024a0b03500244030700070060b0b00942d02c1045440c6258400300781d0014091b29601c40c00d007800c1603850828441d202e07402c6901c803a1b5500f0000480c031607030100b0480700218401d03030f60042075404c14540102620039501d0381c03901a82c207006682c031022840f030041e40d1025001d900d034002c1d65629000000c1198850301942d100a02000690311008002800d5445140c01e00b81e6080c41300b13276a01c3d40c1c101d41c1d5411040000e045504403a100f000041d4400101d240c10a030002d0440b4140503065880516030090303a207030768021035800104001003280030301444000740310840703141d41070500e407018807500b02e03071441d07108014600560000360801c91140200001486408002c101c000b000d10403069903410342e070b90706640c0f403c200400010780f80b4000f50f459100310 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 133939199 1250 133937949 133937963
    0x914010915060305040f0204051006030e010507080114010215070c0c0806040f1e020303030109061806081906020d02032a0c0d08041109091e010b09040210090b030a0914010504 77
    0x140c036002c0110003c000240040b9010039a0485400143c2d6490185d540113032020901058468580000078007101d007020a107120a074100810060b920380c00031921411030f50755140042448240d940100e0511002c2c10b02d8407118503a207024091006c1d40005610404c5208805813440c140d1141405603030394100325801000c1419a22035030000a207807003502e10380081a150361015511942d4002070654000340c000c1d070201665010104101c912016241342c1c0903402d00400c000c420308100c4481c1c5c45401030f10340d040348140c000e0100c0701003080a40c100c03401401140f40854032810110b0700c50300c2011078004011000641c22032100712030000d9404540250781b480c3c3c01040b004460403419955418001c00a0f19008030251036a58961501448141b00300b07241030180c1034880b110385c143d02c0d0484a030000c1e190b0aa02d44152400300b40c4426038813a402c690111440000c03541030701412134403c4580e40100d1603a080110030300525004a4005108003440b0386800c40521740c0c00b600c0c642c200d52086030b0140c001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 133940449 1250 133939199 133939241
    0x2a02040b0d050a08030a061d0106030e0f0313060212040b0d05040c03060c0305040209100f030602090a030c06020c0102070b0f09040c11070602060603060612120c01060f09140109 78
    0x1458558028844500301a04140032521662152800d0105400060358000741c00002c000d1001c81c603100b40c601606010340c80b41c500d4807081c0019040542c0500402c0300f4580ea40d00c40841005040041d90804d040d11007c81e0f580b603048030000311414031144201000343c0b291a21000c9130420308020386081e50319000b40a41840d2070001800043c10010300140c844120b10480480818154014a030504032182c0b8040340c1803c082c4180203103003000030080300403200c1d41c02c414001c01d5003848a942c11a60031040150300c40084e80e00286a030b1f003a1368401000b80400f41c80000b4099008240c20082e00c0d0240c00351403409a4400031a600c5119050500e80128010010050185015440201242c140f03241000301449180761081c40c007902034001e0401f6a12031001c00c4001d01d0100407141e440130741039426100c185950042244e4071072101540400040d000300c0c2c2c40580070400d44c0144018040c3d030030f01125055030380000700020034001700005000f41c280c0c0d001140d0441075015000900680026a10340 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 133941699 1250 133940449 133940453
    0x102030f160509280602010501080d0305040c0b0c06010603050f0105062d0d020c0709180b09030f0d050108100c051905070506042d051f1410062a 64
    0x7a84800c1444050240c2406561aa510382c031107071003000c00c0981121240003148000501e03200f5581c0d40540110380c1410014130203090049843c8003890084d00b03011800c0d4441d0300d00b081e0306c0b8110750402019524003040b1040111000580941240d4054408100c9070716441c500b480d541a09001d45a00b01404009810414540315002000c0b40d40e64a80400300340741d038111014207035019440321440c440d00420010024401440040010040c0940400000540e1303050303000342041d950703c060850802c3c500090f8589005000b186c002c1031000500b60703601c141550040380100f40138010003005e03100346000c04402c0c2c4840c3c410900d00500f540c5489080480c0c150461240e15110244001000020702401002480421a40e4003462049a02c030030302d02c801403480700c40c521060030f03020590f0b1141720340300b408550081418055441c2e040361910000c60317a5032111000d081c0718507622000304000001c02280303141c0140d600056880c15a40c511414088840000040d07480e040d04800c0d22900c900c0e5400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 133942949 1250 133941699 133941721
    0x3902060a0201021603020f0d080f0a020a05070501050f0a140403210608030408010b09060d08040e070c050a05060402010e10080c03150d03090302011b081e1e1207020102030f 76
    0x26000440d03100240c5003071020018006800c074642d000f140940c1c0644074860190b1000e2011180c10441860700098618000001480c003c10113001d80220340d03800180282c4c407901c5013085400054000b0024041d43c102404400c148800803640c01c1c07120351812a881c2100c44059445070700958050340c0e200481c0f15030304d080d040d01030345264040b581c0a41d2848001040c20741400500014000d1800010750307c04480c0a01000800c010075003885100840200d50001e0f10020940741652440e400c0162035689051050714034030340ca02c5000d0070b00e1050300d811030204400094043d116610030f9944181c03000190081c00241c0c00b0703030150140419040c00c000381001c29000007071503000010741c52000e004c804410109000e050408000e80c0003400030441441556040020751a5556484803081604401030711084c200380584829582101115810b5102c2c000302d2500b65148003030380000040380907002240318455235001482c403012102c4408001040c850040c4280c0b44509541c6c900c0000e10764802e14509 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 133944199 1250 133942949 133942957
    0x1050d0e010b0d03020604050d08060a0312120e0c010e090c09012a030512060a0e0112030903120509010e030703170c070902030c0a020c0415091e020a390206 69
    0x1040d940c44064140c10382c3c5112002a505000c0c1d0003800003400c01e820b0440c144010814400c0a104c4901c0a12017542c84800003402184d411058410000c64000c000f01d03850a0908644004a410400440c64540000c10303a484c0c4920240c03205000003500109100b450303201114441d1040d81c00f802041c4803540034151032460b010300d0590003121040038440c0d18001c1802c505050b00001d2001c210b41280c030341c4484506030803c00403900002101e180c0780513480410f005000b41031f82242c0e0204044200360284d402000075581c0100c410011200401d40100150481d00300a40011100100c841c544c0c200852914142c0e0340119020394011f1210b050391041c0d0780003240c4c20105208040340080c44400d80c0c800366019611084038240c5d0351100000003444c0011602000d84203502e081c0c41c011980410149000486a0032103000ca8030503001c10030f00c0f10100c002040034a9450000031000140c80e480031880070b00340e13501c601c40400c042110001c64029180518003c44242d148020301001d0300e0454060 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 133945449 1250 133944199 133944221
    0x40809090a1e180206030901090b0106020a080a030c0c050706050a092c0903280807021c08060402070503040b070209091606121b09080d0e010e190b030403080a0c080601050d 76
    0x540005590f680c0410481c1c2c1c011141021a40d5407207405104200200c5843d40c0100b21601c0200520b040c42d0300c88480510411446506044e07403480c0030010240603804081c0d0762038019003a1044107070764920140c043d03032040ba42c91000070442c11000c1070080d142d0340c20002441020503405038120710340f280103800f500d0140607412548024480221300c2c0c01404a01c45a43c6446170b007580c1e00580d8400007916842c4040e04140c01e5400c559420003481c4c000a03000c045d04560b900d4005115251075011800900c00c40750050002d00001070081682d82c540c800400300c0c984241c80c0450140c0d03602c54201d0720b580c22015424a1410301d60000c21269100f150300c402c910603d41c46c000742810039140304040405800f401d22000c1085004208035824090000c0c140d1300113981080d004440c0c030f01c00000c00182c800304070503105504132200c442c00d2220500000300a031007801c00d290303520b007030a003005001c0510450b911040681001c980b4000f061259a8480c001c50044e1100c50800c090181410040d011907450 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 133946699 1250 133945449 133945481
    0x40204030c080102190c080304020f061c061e0815070306180b040c02010b0f0d060603060e0a1509030503010306051306021b15070503011211030303040809090a1e 71
    0xc800305001c01c4041c07004082030b0b000169100e0120450110341d0101000543c10b01c00f006028401007405042100d48c032950485200f144c0d1030026000909a00130301c0508090950b90000ba2907181d64103921003401da4444840b0088041c41c000240342d20104a070081e80010f4000011200706020350050f8503401011a0802041c2d00742c807141c0b44048210030001d5001e0300b503101c803210115801d0034841c10084111a10007842440380020100b15401d1402002900440452000d0818425a0f80c0010051039024400788150708001410700e690b40d40e405019940c1d410283c40da0403080308907104280c00958151a040c2c2545c0c07943d2500b000501c00141401404030600360381e0710000d602440205040d05d08101407000001030400c0c0c40d8a8812180149070300c247c0a5010300040640003426281141e54504c96205039106602e840076141e081e609505e901840b000c414002000900c20107010060070640c5c82c2400383e941c1c0301d14142503400c203464000e807142c7da001b62410601450340114809015503c0c1c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 133947949 1250 133946699 133946707
    0xe031c05030a06031a160305060303040b0904021603080f07050a0212030405010b1203130b07020f0409020105041e0303120c090303030b0a030507030b060f0a081f110304060f05011e140402 82
    0x76117111071070f481c2c086209034641201c02c00000340344041c11040a06290b2900300300a15000c1e001c2981e0b031007140220343d440b01012400c41c1d800d6540350101c0f110311050480983c8800c42c6840d010b0a000c806403264641c02000c070700042c11307181c85a001d540c1c01900682c010202d03071050440e80c400790303403002e04250b925540320385a86106448a00e00d11030116203080c000d541d200d01c2c8110703515400c0016040000030900800001c00903a40d8480c00031420311040300c000550050300c2c03006031818855640609810707008900d504841024091f03060b4100ca00a40710918200c4107180e6510481d1300b400c2101010806224051000ca41302c1d17400f51010000140201c40100e8480d00c4a6241c540658002c564181d018030400110341490b80307540040340002d403120360400d810150525212403840c0318895000700c0c40640d4030070040c0706400000100d540703120708a55a08090402c40b0103811140003446100341003000000d9011480a000d6801c0300d00c4504004189041c980148003145114100b6584590240 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 133949199 1250 133947949 133947953
    0xc01051306031139070305060a0b04021b1005060603071e03021b0304080d210e030f07060b09070e0607020405091c020304030b01140d0803040609050303090c010e031c05030a0603 78
    0x800e0740c107403181d501c0310036141000c0d500302504030915000f20030713801c240c03c409000c00008600054040c1c0000948a01041c55074280000c40e001f0b0068080c80380c154606400001e115440c0800d502089030302c0300e0400d210503500d103070a000580c442a6140e00018007880d840103000f445003271145460352000c0c5005480c104c212030884800c0e0700d07503076458000c54000013810031070480b081190f0007c20801d03003010288000342d080e0740d0f80650307069481400b40546030b0300c10120941e024000c030340618641e0044280c030b4100c2030909900900380d00008600942c040c0d40415840781c01b401d00c485601e80000d0090b86803046650910024060142003440316100c5c585914500406140e82d810122031103030f0056450b1031650034030015946040c0d2040079112a03c4000000c41e80318030b03101050352078010000540d60340f200c0ca0264010400e11101078660700022050082c091404968188449000d80e11000900c1001e810541c540c0405c5159100d07141548a55600490290f030203154044070b02d0304002003071a525 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 133950449 1250 133949199 133949227
    0x9010b130c0905030f03120c07120305150a0b0a050d0b040608031e130303030e0f01060306020405040f02090f0d050f0303070c0605070c030909050a020f070503030105030c010513060311 81
    0x220100c00c44a444041c1014000d500150201c01000110b00400c409050740104035140e00c26a40c03d040354541c102c000821002e0708508403000301e540000302e80000007101d0001001440c0558815115517031001c881e800620700395269100740c48400c00000d02d480c2c0300a02c2902c85501513074a168860b41c43d50542e80055460744102402058603801540d0780b0b010040044d21090740c500b004a5018005011000069281900d82000d69a140c24002221444003602d54a0300e41c001121002035803c0c00c10210070000d00d60086d0088900541c2c05200004611889000364000ca805894100030b19055a038150310388034411a00c10350042064036100d008000d045800d651007100d0342c0d00071070401c4075007204000c42485204d5200045241c040450119664002d104840700c0c03080302e010b50b0300ca5002c500914055811500e81400c0c0c00b030241d030346006914020343c8a82007442018824010314440c01095401042110b1403400410a8017030300504220040e00140f41403610942004014000c081d248940 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 133951699 1250 133950449 133950469
    0x8011418010e0103171e09120d1107060e0312070602090604090c0801050a060804060e03090d03090509090c060d0903030f020a050c0708030c030403080f1603080f0a090210030509010b 80
    0x115a42980c2e1540c110b0070406003481e030442d042155020108400500380419200b0f421200c1c3c1021145a80c8240b034000150000c140400b00c40c50745e0092002810701c2940005a1b94158902c0701d050f110303955030740d070070a07a040d881c68025603405421842c80344001514510003400c006100380801818400c030b800100700f4a801c43d8115101071640c1e030710750300038483c0c00012050051204441c14040b2a041440c0207110402c0580014a086d4803841505012801030059500301700c000780c690044000981801490100c2a02c5410300907000070303002c107880c5440404c000110000103000e40e841d0205c00300d02d00c0300030b14a1900c1607040696608160b560ba000354001420104c0041d950305881e207105450075400c048079548542c0450303000b0005d03400c9007840030040d102100e1300311207140d4482c0655071110392036201d03000e080c0107000700c1d440c0341d10201034001c0c226a019000c203014098290f590040c89404650995001a50205500740e400c01003c3c0310360042030713102c0c9044001003018401ca0300841c2810344 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 133952949 1250 133951699 133951709
    0xb01060804140313060f0e091003021905010e01180f091b080610030207050115060f020f030901021009111201050601020d03140a09050a0b340801141801 67
    0xc2a0390901052003882204186458041005113290000440306460b40307103803501c81c080074041706252415085c0e0051002150498000e040c0701c07402d25004031003010848050008a01c40d4a400c0800e01c40507a140411a0550342c042c1c4811002100300001514200b502c0d40e2090036100780b0384004180c3c1c3e0070360b02022004044400c0040b80300c01010450403030440003880c0700c41c10005079030104150765582e900d91004200060800590710207030343c103001d400b4140316000710241013522100014519802200c07080b00c00455030a40d0381c440221140d068a078412041e4450060740701191150100500e980a04042485007a05101840c2c84c070380800c0704050141078810459550303001704001c95030107121020705040c60f07140801c080030000c070f1281d201c5907003d0f2030741c0121035542c0074007420004200840307519103400400100036440d000031541c4149000e4684c00c61b0480e110040051171111180c0c4420b800c2c94652600b049603802c0c11500b0817800041c168040d41300c4044420064005004080306010704 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 133954199 1250 133952949 133952957
    0x501062403140604050a0207060501140907301814100606081b070807081e040e04060e0c180a060b0909160c0209090a03080708012904030b0106 63
    0x4400c14440311008800909000d0a1500300001500c02d03401a0018603440701046800142c3c2d9201d9070407070300090180b00d00003440f80d0302c0d007070020900718008425201c01d180f046441d681c15a5a00404030768600400c050511480f080c0e109240000030030fa60300b01104040c10308001b4100130306d5011520079491100c0d05881e420309103818181404004e20a544548100c13003428411a86840030051007034800034200c0780400c10b107200f240600ca134800200e07004036400002e80354544070030b4100ae0510b41c2c4641e001d803910307412044010160003074080549080b900e0300c0030b06146c00e0f555610703040d0240c0800c030305120142c05004c1c0310020903903c021040b21008210f002e0071a86141582400c0d048903072940003031050003070620440c2125920010800e41c404041d840b201d040601d104000d54a426501a00a61000b580c40c10031100d0200069040c9515002c0d82e2440016214103d003aa4507000030700503412182d81c110640c0c0320100d4032014014030ba00b010042246025540d03160002d030001c08dc3c00ac00005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 133955449 1250 133954199 133954229
    0x319090609210e10051821100b18090a051002071a1003022205011202011710121a01031a090d05090103051302180105010311040806060906030703050106 67
    0x110003042d011000456550038502d51842c04000000c41140700d00600c1800c001c0e000401c880c3e283c0e4085041240b00201414680180042c00e04009150a0111011249108402060004074007074094a0b0b002100540003654030008100b0f035015119005001100c2c40c45481c10b0040000c100304003508241e01040310060301c41000d850284200c201c1c01060311003014020041c400c229070720b811050107ea504444810000804a103406052882603200c602c0c0030b440d02c800000c42081050030b01c503020303100740c0e00d0006c3e5205080710602d4042c02039a00c0c98660741c24610501150640041e4921294022a2040034902d560064101025000d8000700c4988401e881a02940d80121660503008080300020b07000c045055080101640603201c5058105034582010445c4491307403e001c0c903003854010748070f4452848400c180d641240390070710a141c000f07031070410f80070480040320040d02c080d2121407010b40703050348400e03042080203100030b0441d41d41740c01400c0d000000500c00b449000000c0442d28020804 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 133956699 1250 133955449 133955483
    0xb040302010f1d03040e190f091202010c080105130b03031b07120807080d0b12060402010906050c06010302060a031d01050f070302031501120617210702060319090609 73
    0x540384110751410f0b02c2c00c2c0d62840b0880b6500c02200b0342d000c0d28040c50041c4031568035429000e54805001c803032640c0300c40c58140503005500054201264143c080c0c080c10448100b81d1070201c2c01c941c4a500c0310000a04044018041486c081d845044090203101010a183e034182e00004c1c01c5a000c6441d80500040c035103402202c0000c00d10580303000380740758544074107030701c405071203584c940e100d881002414280006420900350043e98000e0a40b150068a510b1200001030340e131542d515010346d020f80c0400c0c0c4083e80050641e1040701100c0c5210406000740000d6480c6500b405400c0d00080404002e250300c0b259840c81c1c507035402941000e0140d03114004a401e0400d41c0801505407000342c00002094010401c00105140091004035030400c2803821041688030503400c4001804160450b00d18005514107005122100082c503501c0e52002c202e80c1a100280803408026512039210020340104081c8001810402144d4800040040c2d0b880040381c020140d070303108000c5500084080307031000c0750380010142c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 133957949 1250 133956699 133956701
    0xa0e010c021201140103170c030a0c0f0c030317060405011409061809060f010501030b0918120c0c010e030a0f02060a120c03050103050c0406050f060d060e1008120708040b070f0b040302010f 83
    0x80000c1181290301e081c1f00242c40e2340e1a88100308682e024422900041c008002d0b848030181c0415810400e451905e41d1640b030700414a40700d90650039402e001c10303408180b01e841c0c207103d440c1c102c0c0d2864140d90284c422600901c403400380010180340c4e00031a0f040240841c0c11640300083e1182c44c008002d4801417420200c0c50107040c40c180c016030704041c84c2c400c0d400110340b1078411190b00580c00020f01c003200c000c44c41200c0d140903c0780c03401c1c80a0714000b0a105220150001e078a9094010907221480a860103a050503642c1c1d4892501400143c207803080313507025081010043c4410141c601d80081808048000401038a00050300c180000ea501c90040081c00380500282c50700c40e404850a110607403400000805954800f00e059204020010b0010722141103684084010003160420304100d00e041c0c004840a03045521400300a80602c080011502044001300d035881d45d801409603041c1070070041d52b01d42a03005841d00300c850080082030f180114401c003070007030300c01d910035400401d4540d00507030580 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 133959199 1250 133957949 133957973
    0x3020406020609060c0d05060f030a12110f0604140708031201060f0e09010b1b072405031e0601050c160f080f1c0e1008040204110a0e010c021201140103 67
    0x103d9142c100d0300601154045100c200e50080c550b0340c41c0170500e6194200007030500316003400c0d5958148240e0070846d040101850650079800101c1e1a405501556140c1094895070800c100d04259009500041d0006140c440c2031029003182d401202c508030340f614121803a550080c00b500160342e1707080b00100641c5601080d4505540c00c1e9180c2444075141e203d01088130414180596140040c2c08034000584600515075083c0f00c1000104032003019584a000381c01050803241c842c201d00244246190203140110100d030302955813003004000e04034410340780140d4060040c060360b04000c1c0802880d0b480355000c0200c0c880310807120790340d803840900c2d007000c414a1811b69800074802d030300400708012868002098201d072180300d20400c80344610f4116000c46032903460703e0803254015020f4009460265000e00c01c81d11961090760200001d50142c0a80042c5004e062040710000d040d030410580e45500c00c0c141c038203690384007405032490f08400356906825070b42c0d04600c648000340910010024084e00756500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 133960449 1250 133959199 133959211
    0x10e010e130201051804110f07060605090421090504050114040b031b061602090705031906050906010c060906060b0706060902032712040b2a070501180510030204060206 74
    0x941d40071550350018080d07005074100921080b04081135206251203e8001c1d04080919601940e5583c804140004241c5c020801c240e031980e2a014000c9200c1c20040c20050045801c00c0e42c00300e840203c64090035207601000102005c00030800400280b60f02d803070003400d000c1e28050015102e08a81141404100d403031803940c01d03109a21141506510090f6440d08140d10f41c1e00b030b0f60499403012084004c4000700111403000350820004070400c41025880400345008400010381c140b03446070204050000d0b1a00d5000b0780b6880007030b05002ca4070960154001104480c4038910218054501e070b11084201c031460fa00c06c1e00d280701d0000c0c440081100c94070038040038080c162811815401c1c403840c030583c0e02d02c0d9a82d10034a150003030000c0d55403890080041c00c2c2c0d299142012144c4d1251122001ea407141c214007030b43c2c404603120b601c190394000021240015410702540080860300c0c900030046800c8522143d40d500840c1c000080401c1e05e440e0440d00490b100415200981d079140b030a0002840c0000040c01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 133961699 1250 133960449 133960471
    0x405030c0d1218020603070f0c0807051513080405040522031d0301062108130603060302010806040c0c0303020f1611010f090b0403081305041406090a0c02100c090806010e010e 77
    0x3e0900143d84050940741c101031145084025001511001d0322498401705001e041d034000030894400304000020001c000030a020160540c40c0ca8440002011991043c0010726182041c8424492403c3c41e0340090f6004000c803030781403036964907801c2c50140380c100c0ca9002c3d0000703250440b03500700c0c020312a501300d1542041076000300611490034503500040440d1284180c14805001c0d560001d0181c450256414140309072001e5038025543c00c5c010740100380342d1000303d011071090400140540380c103120300c0040e0911071300d502c480d0a2855030202c000750b2150b0b194444d409000c1c0104103007194490b90400b8801d00c00c444642c0d0754952400050b000703030000c0b1150020001410b00500400a105084c2e504482e440b4041544035194500102601c0c0c6454020f40d401070304d40480340240c0c2204100c543e000324001d481e11640d6441d003408482c2a04d040e41c10441c05030707004103650429100741d9403191400040a1605015840d02c452815041c00ca0a030302039200e20b070b4250018040d0032680b54099400c900c038500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 133962949 1250 133961699 133961741
    0x60a05130302100e0705090c040801050601030b090402040b01140705010902120f0a03050a14031302040f020903030a05030a06030606061e0201091e050715090f0e0714030405030c0d12 80
    0x90000e5803141d440801e0a002910f444c0c215110800400c05100580401001c1c110740c0d1814900c03114841d00544680c003603660030900400e58a501900c00c6d03a45c0424003500c011907030780d150340a00002e030000d0240f040c100030161078422041f03503100d0090f00141d0b21a10002c600c05071240104584402411680341c1c4503000405603020b11203001942200156150074805d8031040c0f0400e041d00c50200c0394480346400d031000810400e031051040015038600b44202d908000c0940c42d05031210032805986401d5415034010070085100c1405070014580c001503c90b00854125240c0ea220010b658950b400794010400c0d02070211803090900010410b44c0c0c882d44000c0100b84220f85414004424034142e50202d07a0404260b001400418480d0720301420b80403012580c40080d4120003484032019205007200f516100201003602c14185180c0782c0948059903910105082143c01d5403103075130002d0b204403120b11007004200c0e18120309000e40d8075140c0c407644882d080101050300703810a031841c4d042e0030007814036808 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 133964199 1250 133962949 133962953
    0x5061b0301170a02090411100801060503071809020f0924090f040f14010501030c09081c1e20031c0e0c090406020d0c09060c170714060a0513 62
    0x8029241110303000700c00c5410380c9454284403030524402e910043d400545074010072003802200910140010341c03e5504003900078402e40110751810080c05200300180b420004500d03068404c403212051584510001c007c80b540c0c4691a60880c0c4c4201c4180d241700002191601007031500f0103030560f104001801e94030328802e00f0900c1d801c0d58070544101600c40d54403a0088011511641e00c03038002d021280404109800001c1440d00001d4424460799002038200101f20000b24801c0c0b0050044030320040043c06084080035442d4405c4000340024410081d02c0010807607069250316495101840030b4441c02410464000c904c4200a007840788404154001c1100328040407800f0385441c80d000080742c002402500c1810031908011032120400d60256118080c0814880558020701405049040801c030b640d01c041010f4449103101e1080d140801c0c0101d003010003040c46402c5c1040c0c001c00c451001490202155030f84085500d4000c1d00300c249a01560422611102c03e20036983c10101c80e45140c0e019401300d03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 133965449 1250 133964199 133964251
    0x1b04030308010323030a0c06150509190213060c022b110a091d0f070e010317040f12060c09051e360f06090705090d080a05070506 57
    0x611008004c0d0307010500b00310012088151001c0d0034001402966030320000494005c0c11480d0b2002c0039207980303107084440b070701c00400000f20074200c40010742103501a0b5103200b4074016621104020b081c61903001c001629454000d000f125010340346580314441c1c0e000075401446000030030210710844c00d1141c5440002031803481503405198a900c402c10040e804036000200340e441d4065070100300c285040c005002d20065800c02586200c2d0254011910862200d90400760342e50010f01c9800501c0d551240140041004610712064008000341c00340c0c5065aa4044070070070a025901402701c45403505034090802540d0700440c0003040580c034007100c3c21400d0100103104000c8000c02ea4103588d04000401c0c540b915220121220302000b01a600035445000450b484080607a0100321141c5a00c0b40000b5840743c54125500d00a083c003801c000d00d19a541d8a00b610140e100d010050303401300c10b440825000511240051001c0d8a00755240f980728103841c43c0c110301d8824058404000c02d8003409154501c4002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 133966699 1250 133965449 133965451
    0x1e0510080109091b1805130201050403020d050f120903010e070f140d0b0a02070b07051204060911031c0e0f0f0103020913090804030b0106050a090302090705090301141b04030308 78
    0x140d040002844080d0745130210f1060515007120040410390a00021401d90907800c01c8002c100641040c082c030b9640c0480c030044164440301c0240030030b00510051002d41030440c50740b4441445942202d5542800c0718281d450b00115100c092103080c4005030301d6410b41003e01907800307241c2812008080090503c5c0450840c00d803540070302040581074044529840d0b81c1c003240700c44000e0300840c16152504245007000040d51080c4416250055904042492144682e049901003103010b2803405054486580380d0015141190303060340c0380729a01c1a45240c41d03a007400030b02c0300c4403064001440103543c40030000d000d40c180345400300d10403080500c280d00d064480c409050164a000d00e00142d4070101000055a103a840d00c144480b818905010141040b240030018400c7e01d01a0b1680401a0baa40c0c0d030460b02c0d03118582e500e40000c0c0380381504100504103040361503001189801d0807070402c085074010030f0841e401110700410031030b036000c24041603903100b401d1194949000810b1034030b010705580b806420031070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 133967949 1250 133966699 133966709
    0x12010b1e01020a060509060402040b06040e0109020304062a080106090e010b0a1b03030b03060a090f021005040902071b05010509010512070207210b0f06100c0206090303041e05100801 80
    0x40c0303665040015a10038400440c03000d5000a0400030360520329950741d5160021601207000d035140840a03c800c1c40c1040944040b1100740c0a081016800c01007024040d40001c0c104540c030365101d01480c101003414030780320b015085034000702c41c6400c1480140100440010b070301c15414440050340c148080310b5030300c0810741902c022324080b90342c4864022044400081250702d0507060912110320390105a80b540218613903043c02c40c1124440d2f120f41c1990401c03141c03001c2c0300420900404030035800505045000607203461450a0860910b41c2d01c0d0241010380e80300c01011280d00c2001000030240c2108460240d02400c8280703401d6090400c4071001031302d14400c82d1950319001c0e464000140006100f0085100903212000c0507554009005e03c51010401c00210200c5041b41c22100103101c1c200001d0311170703100c1c280003011240342020017a03054914184e2100140c6c1c02080030031002c103480d1001c0008100134120f01200c0041074040c940f003081d030b17903e854010520402d030f000d00b09102e103580310305c01d5410f6031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 133969199 1250 133967949 133967989
    0x9021012062306090a080106120c0e01050d0f051606090807120f0206070609050307030503190510050411040509010305070503100e280609030809010c050702090f10081b12010b 77
    0x40402c4e0002030780d154040d0b10840f0950700303006000c1184000c4082200c00c080c8100302c001170f0309803240403601c1c2140090084a0b040703003000031104080390042c145000014010301c107130398281c00200049002084540c101b03030f0224039000c00030840c01004100050042490200550007038090740d95a00790a01c1d0b078200a441404081000000c0c04860b5100400980c0d020b000c4030b55801551501410301d0304202e820a001c94840b66100745007100e1402402d01c40d10704800c50350950317801e02c400c110041c005032204d00100c1c401030202080b29181e40880340d018500500091008074603007401c15142244c402002d1064a04242d2036104200d000038030100170f00e042a0349442d940049a903402c089030398110001d80403505050541c3c2c10705400056441c01001010002d0002d011440401e852501c030750b0000941140a04002981c0900641032180d0410415246511042e644000a600d400d04070300309800f40c90040000070040345403001e0028040740b0524024080c103840303440024099990210b0500d0f4007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 133970449 1250 133969199 133969207
    0x60f010302091909140916180b032406011409090601030b0303030f010e0702070b030414070512010204060201060f0506031302040b03032a120301090c0309021012062306 74
    0xa550f9a4802d083c480036a41040400f03070341d44500810180c42a907502c910500c80810100f03442c1100440d103a108084107190041d1f1180c42c284030b2145500070318101e1210315568003103528a641e820b0180c0301407130003001d55200c00b402140c481040201c101a10480c1844514040c444c0d15840d07580640301d180390121042c4003c1d81e54400142d025001d10600381c0c1d414040081040694002d2a103c1810383d14100b00c10700cc242d4070240181e076211001d0065003001c00c010710020300000c01c10917035138040c09584015140e00c556103901107102209510b0b141e500f070340d401180034072005509200301c100922000700d00904492814010600358440913220001a011518815095450f590420800104007504503556141b03110340024000301440301400403200400031004101700000758140808103903025251543c0d1030036502100800715030000700c06160700e4499050150760783d46101007180b0019116500350300300c5d1b600c40c6812140705400010b1110b4088401c40404d1200708408504094183e071a01da031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 133971699 1250 133970449 133970467
    0x10303030f02070b0c130603061a0315030a0c08010f050411060307020718020c070905060612100b07030503090616080a0b040b04020f090114071e1a090c0117060f010302 74
    0x191068502c06800d03520101300f80f14440c080e61004003803460004100000d100c3d103800d011800c0e50914400c4840b04000c00d0200c407481c400034001941c0040c010714070b007500743e10135001007403c002c4074410a460000011108001c2132200f80110a28100749020030881ca03e480c0d40c404210149800c0903c3c001c1c000840003490744c9000700b005401030a03001d40c1c40a02c44010301d6200001c0d40c050b1942c4440c07030062110000c0c0c540c2c014007859009080c020480e50034480d94030300142c00d00000811072000512004000502c4010307286c010040c0d180039680e455520f10303196450300c2c41d180c8060641040741d4040e114010005a000b03e0468004144903008034242c041c0030b0000b005840751401d5568002d01c001030a116900c1c040c8000d142400c001e80b1000d4504007290f1100165005101010701100300f0b61501151704188920f80600081c07184a090540315010106008032820440303000174150f00940c202c0c9555070700b0420550246c8022442488a0310f0500301080007500e05007580c41c185500820b0840b1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 133972949 1250 133971699 133971701
    0x50a020d0501090c09050a0323030f0d09060c0203070c030809060904020d060501080606070b060105030408070f030201050403111209040c020f0a0809040f0e19061d0304050301061409010303030f 85
    0x10444030829091000e561100f20a4004101e1513003001c1c041543d159000440d8200702000b041240c1d0041c40c20110782c00c003081c0070303a07004408880a80c998001017101944e1908040e01800c0340f44000c90f0001850f80342e81c41e11008940c01d42e1841d4095500c24054080014054038080d000d0340d50181201d9203450090003c074009000b18104141e2060000c0703182c0150308481d5000d1811074000342e0f2000555290101400250720a005001d050910440300107100c65005d50b00a50b0081d01ca022801d03d800701684855440c0e00140b40c3c105d00507510354007400203244d4042801d5200c40440d402801c0e440180b0980e0340c42c54856648954051504c0348014001d560003070100b44d216410307050948801d084649018500d9070f200700c443c80d2040b4505040091448001d1103000c01d03201f0580024040b040d8101d03c1c1c01540301c1c21810490b20607850700d54511000d0580c0130f808005007010002151034506090030107094803500c1d001074100944000c04909282c2d0707080c00300ea0440380c250030b000401d1100742e40110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 133974199 1250 133972949 133972957
    0x9010309060e0a150605270408090604030b041203020c0304120c050a180c05090105040608040f05031309050a0218060a020f0d0c05010b040b1e0f0909060906071b0303050a02 76
    0xc42038040c64102006000780941c044c004030350001030070031450f80c1b03600030000c5182051000200e56032070b4488007000745010160302600240a0140d480c00e0080c0b02c000035040b0707440343d00100c070228260424071003008034000465a040c0c81509055040400003c0c2a907501e020f80c0c490030340504a1001e010040c03050078040100640700203070081507141e849005510700c0411044035054070b0b9103843c02a1080358031400a4032960780059541c02d2409280c9401251281c402600030b031554101303600349400250040004001100d001c40007080c0d19844e1120346412918010a20394540e80100301d1200f0342031851086194215045404e80e4481c801c406040b40340c48411481d00d0100d02c0350019013041d030754000040411a92040009002c040c40c1c1c2424070051701e183c400099000402242007a1074030519000341550740c40003031700340000702d01084005824003105603005007654000c10280081d0303440601c4415400081c84c01e04a500358044420504151360420010782010380d294046500e0318450740480b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 133975449 1250 133974199 133974221
    0x60d020d090f050f0615090106030f020c01090b01050f041103010303030c140a031413050c010e030c0301090c0f1502030702010e010c05010509160602070608010b0d09080304060603060c050702060901030906 90
    0x240102c107940c0d19105954503818400c0ca0481d100c0c02d00000d28903007282c48405800400603103211516460200280c010300a50f00c80407a2030b40d002d0060b004c41c082c09200b0080c40500800450203e940f400e020310001c801d201903c90b00807414458100e0302808001c044a0440e40d041c0380009072084c5061084400241d5800100c2c0724110003d40002e0569060300807205440c030148200301c1940760019030100c107020401000b82507800000d000c8203150300800301261814009420303039540b03480000000342107404001f02100c19203c0c1100a0003142140710069011309851b503030401c0c2d0401c00e414040c0d624041c4180c001d04001004060004c2c0d40d100d0002c00d82d0b1198000e000f804030303050108100742c941d03401e50020203032643c5d10040081c1591002881d0002c588060701c40b560039908140030780341947c1c000306103501e00c140c6585522001803420710041d407059008035000265913065141c440c05030b40e40d460340701c020803c0600440e0b02590b101011649030b0102400c0005504801d4a0081c0140c803d013442 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 133976699 1250 133975449 133975463
    0x4031209050d05100b01030515010f0e041508010b1c110f043920010e060907030c240305040203010608030a0f03050109050c040605030903162004050402060d020d09 72
    0xb003004000000544480404400c4070034007007442c210004500301c4504030345581a0f408064200180c550089068042003545032420581607000c440220341511311307401c07240c01900706130344040141600038810366905900484071004801d038200b0082503142044017016181507140700185111f9503034140454240300000c0d105200c410b017944641d070014140e4040040d006402c89100001c040c911074962800b080458036011151443e40c0305101070b0707620107118401c4540d680d81c50040381c0130042190078850102e00000344200c0e8110300e03103031a68920303e070301010640c03110060049500d48100292100c2c0156840c0c00a05585c80b030001030301502e9140d12140250000140d56160035510031503030400009a9103080c040d0b41d0780e036000d080884800301c03080120044188414000e4901c00c10043d504680b54404607814060b80040100c0038440410046640d04401501ca00c2420b4118030040c2d0300340350071a001c02c014541030700429018410400541c50240d03001030341c400410403683c004490b4079001030b2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 133977949 1250 133976699 133976719
    0x1b07020d0804080c01030603020a060302160506010305070317070b071214010b0315090c0f0f04080f1011120615040306140906010f230a0b030405150109060b0403120905 74
    0x145445194080e008007a10ba01501c643c0c4c03100d5500038041d0b84200d90f8090a0310704810702d000d0f0210000c2d00701c4104030b03c50740c126480ca10041501006018040d5020b00080d094492851074210307000d03001d6501441000d0400c0c050b2001041480c51030b0343d4045080d092002010a11940810041a03002104900030001400108a28008501035407080c142c10811a01d466801020413201030011541d0310b82e08070017003280076446a040405042c0030883c0c24203042c2011b465070540c505242031601e2030700302503119440c0f1603081034031b07809000081901c0307004203440d100030f403e060202410010441c5004861490b111042d018000040324001c50704070404110079007a51500e80380c1c104055894a002e8451200003061203044018040200e503280f9200000c601d40c81c2c1c2e0003143d180c88081c80c841e8440100600090442c0d0b0440003584a82d00c910043c20000e1050203180ca01c03510180c1010110610340181031010f000900220b6043daa0400d803040030f110480d04c002c0752188181c0d000140c005144071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 133979199 1250 133977949 133977953
    0xa09020f0316090b030a051002070c2402160303080402121c0201060510030c05070b04111302031e0106120e010e0f031309020a08010b09040b040c0f14040e1b07020d 72
    0xa40000280c3d0008003051100401d65010156200061381c0060043d800281080d03035802e0842e4010080188141c002c0031110790f80d80300b0183c801003ca615403001c170391110485100294103020481481070850a0113400c1419070b10014403000b8018002406400c4036000d8201840040083e03203143c1d5041c00c0154007164466000902038000307803103018080c4d40401d490b422058000d01032090020f44ae076035080c1c28019661a0030410705c10180095034000100320300a4070b15142e00340780c20709048642c03001596a08203071918246a04101048c4400c5030441401402030035413160035400401c0a00001141ba007a4540926004001a03034012111740b090110071801c611000c4007500f400b00860078011002583c58100809078450040c0e0500050407441c010f00104400701d0180058402c007038800601000c84001207003c4515210480001c10f840388045081164090707007101c004030303454141500700391404d009909030780710240602c851004080e0b410709114980310151245c0359001882c0d000400000c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 133980449 1250 133979199 133979233
    0x90c1a03010b09010807023f0c06070f030b0303030403081e090d11031315020d020f030901030207061806060510050903060403030b010c08030c030708061009050907020109060212070306051002060a09020f03 90
    0x641e06400d42350902480c1580c040940081c1c0b00f032245600041e20b03040e41c60300360484058400805e1541850390300d000000d12600c1c1000618416442500d4132080da0034800c80700c084645d8010522800261079000304420008041501c4921280305c2c14120b40d01064420721a00b14080d411210072800c0c1420400500380c019007801d525160380c03903000d699440b400c40d54200d8441c030b000000c14200c3c0d44200b2841030b40d5480703540140429030280c140007801006c200c0026550380c10743c4e582951044e80305c0f6014000343c42e0104030f9504444d03103414060301d800141004203403103110090014041c540e9403100c2c580c580e40142c6901c3d0b0200c0c0d20500c032959910300002030100342d030405e407109400100d4650000705075003400c805081c0e41c0703103940e16044581c61500080103d2841d004001c071045540f40d2080000094544c009030a29164142c0003414501c4d04080090403265164012031003601a80f049082d142d40105d0318581088030b46601007130006036800490b591801d2003684c2501032041021196000d805 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 133981699 1250 133980449 133980523
    0x807051b0102070f0e07051c0b0a0909150504060e07080a03170105031507050903010204081f05060607080705031207050304030306051504140d020301090c1a03010b0901080702 77
    0x8059030340341000200001280d4500c00f0f40180300e503407010742038140180c0c1e0707540941641c403135007600e040d602d00080640b641032611070060300504156110b41d00f00000340b4011002101414204000704005c04260301e800c041d1003845610403040c20b640d0400718050004d04c0d040f42481c0000042243c1059030b8401070203070f54000c01001503002076000d41c11042c050721450403240c101c6200a008140100365040030810701140502890b00b4040100004045a01d082c0045c200030034600300030340211402c2c03111214408250103240e05403582340c032003004243d90303035107080d914080d42040030780303455900e986006032951085c2214249403611030000c014500b0b0f440001103115600c295000e0185941e01c1c030500003140c40f81c10980c1030a440900080c08891072124141030a8500105200701c4c445182c6c02003400c40d40d003007209441c9420100b0081c091035510442c0c000030480c071142d00030f01e158544900c0d84082c3c0a90300f495410404044e0220301414420400f00301c0038038800c40001e066041c20b074952901500d07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 133982949 1250 133981699 133981723
    0x80405040212041a15010315090606020f01050c0f04180906090803240f01030c0306030b010801020c0601080a0312020706022115010302160605070221091201150b090d080705 76
    0x104c082101400c0964032445008900c0d40401251011684e00154051700b0103001c10003040c008204002400c0f801030140800518040e0040d0942c4034001c401c25007540c200030401320001c4803c2002d0009440500c1c00c442c00c0711003824000c011500055126000303456002c401038030150038021400c00f030280e08001980211068000c40e03800c0304001c121034013001d0300d01800661000416046400c594041d4000045800b010324002070343c42d49a030b480c4446060281c00078107107a035000c01c840c0904403040220300d0141074120001d1610030a03d80d4010170203c62400764481d441c1d0042800e6081003e1501550250440e0680340c01201d50384040003404c06172b080303482160a620b001c0720340100c2d502034821035500c001c0c41c2010816600d00d60f100c2d04081d0101805031411889001da555030180d03030b0804000b400c200441401039842a415007007007800005c40c141c5903843c0e40b4000541400e001c44840c0c00701202c4180c5030060301c03908800f0010700e0b00b24607500c010b400041700203001010001c003c00c2c1505494 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 133984199 1250 133982949 133982963
    0x90c1401020a1209141c020f030a0807050f07050a0e0403032712030605100c11030307080a080411090705340b090123011a0d0c1107051012050408040504021204 70
    0x124001c106c0269442050300300502600c1000d000541000d91800c03038402c4d40903084441e0000c0740c1d038603880643d10170082a1200c1d0000740003248100800d011190080c038084640140301810b00400841440000c0d00040900d0b0b900c41c81112081c06030200111591003a0014240b400020f0501c4043d40144a125100291400c00c02203018508585600c0181d5110394075481c00c1d0203680e075903e802e1a05048015410300c02441440d0004201c14020031802c481503403030404505192410310080031420020f13511400c0c4490402c07810395400030644207204035800d03400b03c26807480007910002543c0521421800c2803c45070740424468200c0e0003e0081d804140208040961803040c083c100c000f031862411050360503030040181c0211140700961041c1d2035009280ba0500c0e03038031040d00b20b584003000c610200e0500c40c8200a0000c0034070944006180940d1003042046044800919000150505070720040d540c030042000d0040c0a001d4801411020300219506e07010f1643d030605580d800c503000c903401303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 133985449 1250 133984199 133984229
    0xf050408031602030f07020d050a020a03140c04050c0702060703031d010903021005010605090108040512041404050601020d050318030702121516050901030209120105180d03090c1401020a1209 84
    0x2c0c038800422100b144444c14407080c1054402e508000011003818000d0f0342603c01d0540010243e07447c159000000e622070240303c2040d101d04003000303042c003c901d40c00c540b246140404110307103928400304a4401d2507040701c15a580d41b00a1809600a003d46401228080c8441d1046803601405501c800b507414000c2c0c00311007907001030125034000c0c2d42090103181c0003d8030501c4128019401f512855800a200c0c800780c40c0001c150040c10509030300164001080c00222420004460a01d072007a07981051082c805800c3d605450100506240300140c0240c408001e019051800d240050090741e03c003640c0103021610341c3c5490196103542c1c0614820061081c002072000c19200d107911400441c88048039180d9908004801c0d0054009400500205810002c45d442040baa80020b1007203502c01c598603010b5901502c44803100d11f01d030280c0d084800c400d0515040b0135a0129040c0c0b8194011951011220203141150310300403418401c0c01d0b5401045a4200e1012845d8103411241007030a481c1424905590 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 133986699 1250 133985449 133985491
    0x615010e1c02060310180b090c031e090703050a050106090b03031215040b041e0b011704020402090301020f120609072622060f05010f0e130302010f05040803 69
    0x10850841d00400201540d01c4030400103080c400d010396484643c80d5105c07101980d80e800352500c03d0001845545180344e842e03000c06d00610b0700f2032495811075100c1c03c186040d0f1038211035080c1c2d407651f000c01540ba5803c1c80e20029118600c200000c3c005560711400351a11101a442e2540c040c020718020080a24148100803030707282000410f031526044507604d80b1850f42c0710a501e00d85402024080542c005845441d841c00540300d41c01103242c1210051800004404841e0b20042143c249162403030400040c443d0800b6a0044840b0403a00316404580050f6240c205d2800a0300a00c51407212040241010840d03070818030420304014425036041d18002a2a5103011040b80d40d1074444148241d003042e0b906000380c503456008101903100312320426121800c10a09100f2840c8445c41508807401d90700c513080400c25060902905004041d035a441d064160b04000d070604148000900748040e4915042c1c0c41005d042c0300b50032070010010a0f41040055061074280000c85500841350010405038002034045 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 133987949 1250 133986699 133986709
    0x4031109060102030a03180209160905040e0a0602030a140c07050607181e0503070f051c120804080403060c09060e0307050307120c08010f0507110c010807200615010e 73
    0x71007103005a0203103141c83c4c8041c0040c1d001301100c401007610740c035240d0403010040c0c640b09a424010050029402d0a12050000c02007642c1560f4111601890601054000b11345000400e43c900a80c0184007603120380e1000c0c0000300a00000f220801602e605c075080c04000300441000307280d060f0003441980c450360355007031040d02d030458480509034032082404410090040449070100c0042c01701145000e642d613490000030b141040b586c22920204621480c00c10040c54030414a00703031090044000e9041000d96224008072032001036a10301406468000101041050003c40b00515882a01088140c0c6007410080240c046400b8400114000800311100ca14002800703100700e8030014010038000f414010903002d070f00710502e800c48080c1ca80100c0070032040707402c0c02503900815107403400152925084000500c01c1404c0000061a904588500031281c0da00c0a06564816024100182c4900c103c40401a40032080c41d500c0805010300800d100c0403468050f84001d032800266039140c030b03048030081002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 133989199 1250 133987949 133987951
    0x1b03060703200703022109010201061212180b07030210050f090604080f070c2409060906031e020c10110a050711040905060c070b07080f0a1d010c0504031109 69
    0x6800000b2a01e080c4402d03562080040148a220f44190b41108080c0000300309541440c1200e52481480441e030340784d481d64240324010042840f15170703400c0d200d199a00e50114610403403000300100300b010012618146002403050004001c1d4603200350382d501072400d00948038171000040c80d000c0380c104401f180d12410b1401c00d10380958903910213400280c840f907031252002e50040c1c1001c10120f0084c0301712408200500165401050500310404c3d00c04414071803403407601d00b0f2050400501c08844d60911a041e400788122050b14101d0500040d0400c031005210202240502c40b40c200c1400018900403848000c10911a6804121b0060158031181e2100c0940c0740a14a05135001034401e1000b440403c0b490b030001816510098030009504c0300a481d40760070000c00302c038160112000060040301b00404080103550000031842c111840e414041e05900d048007002c0c100000158940d00d44400b1005441900c1685080f504020001200013043c0506181c01038030096541d0303094004160f010341032014140d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 133990449 1250 133989199 133989221
    0x4060801060f050306030d0f0e0a08030403021203070b01060311041203050a0e010f050703180503010c0504030b060607020904111503090a05100603020d0311030c0106060518010f080117010e1b03060703 88
    0x14050710f119a0104485001c0d0b0323142d0038401c010154080000741c0e140d02c1000c0028103820743c007640d551415401400010342d041c0414244030b41c0200162004145030b00f00035419207a10380740124000317040100200c6103016030740003000d11100485c402410160444000d10948007591502415241e510006691948100c810900441c40400c10710000134824018943c1a085200c0700175203083d2520017080c219050541200b0108000190132f10034001008840b0740d101c8821682a481c0050340c0c3c6c04240c2300c0b4000740005100c102c05980058066440003c9810b6210480107010340707910300304000ca40e4071000e2203019142030040003400c049002007401039070b0a5940140aa8112841d681d808403201d40000c21403d140b804103200a68011000303001f810020480790307444545400e00400f1b10341000e000b00032018180032504200182c42504001090304540c81e080002200d04118440140949261000d85181d405030440c42d495443d8008038104001c54160104c8055079184101501110808502 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 133991699 1250 133990449 133990453
    0x3080301090b0301090c06051c0203010506040e0403020a150b150c150702031909031a070f0f0504050d051005091609090206040b0304060b03010b0f0f04020a031104060801060f05030603 81
    0x144600010394100790b481001c090000200c0d26403945a100078001240c01040008000203043c1d1001c0100503042c1c0003054000c9401c600c0e40d450400041c90512452144035184010340f000039007854020300003210141d400c03049007170852914600c5180100041c03555140305518520300d00301d04808004c1070b218488482d0700109076500c0045103841040034010f0414045200c100800a4001c2d0b5060100d01800a00d440e2142d0071800e5281c40035050f100703031035040100c035a8442046003255014504c2c5030241014209010800f071071400885091040fa0860354100c5140a01d80c4100100068004500500399504002d962202a40c0c140c0300d08110050075568880824103104001c1c02d6030001c00d84078030041c14507280c103a480d03a40c01010b4100315800d80d142e44c0e40c0c0d0140e0000d410203006070b501b6010300303c9a84540a16840004543e0440d58244600071540801c20500c0107001e9440a014461421051512550340d540014400f100074090100081d54902908154030300440a07a4020078000b80 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 133992805 1106 133991699 133991701
    0xc0405010b0a0c02011206050d030816110d0f0309150e0d0302130b0310030b1f05030703151e060b0702030c090114060705070915060305060a030803 65
    0x20011201070301c10840300014039441a0401c4825909080c84040789001c4510000189520b0300426000303214000c110b41490741040c078080c4504800440340c1158a01031100300c60315808401d040034664048004807641601808690340d40d00d00c540340c0020690400c2c1c079000c21220915606807034503541c40c1d810001100040c01040d07040400c5080039481c00710000c8119500324018841d041e0211004404070304901c40c1c2d0002d0100640e00084c0300e0303025007030118444460000e004090304c00c01035030110000b031a0034041707450000c42c0e030000c1500e140d514000c001800600400402d405024082c0d0b0480c681302011031042c01c0244c12035091054507880d40d4818540750100040d002807143d6680e400412130303036074a441009201c600699402c1e8480005203030451070b21881e0342051a003213040c9414100c012140d00610030072140349070f4013031015403258014020326006500025080007802c00c = true := by decide +kernel

theorem cover : BRFrame.Cov 133812949 133992805 := by
  have h0 := BRFrame.cov_init 133812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 133812949 ≤ n) (h2 : n < 133992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
