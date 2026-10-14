-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0322
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:12:15.301356+00:00
-- url     : https://prove2.me/submissions/1e5ea22a-e31d-498a-ac88-0edc46d16afb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 57733816 ≤ n < 57913672 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 57735066 1250 57733816 57733843
    0x50306130c0e120c1504030605061503010308070203071a0a080c041206020f0f0a0801080606040b090114030a05030a030b030f010509030a0c1e030c060b0901030809060901030e06010f0503 82
    0x8001c8028051507006208005401083c3d41a0780e40920089034242410048111180c00021030041e08201040d4140180104c0380100000c00c46a100c00c020000450360070418120100018401440403405240040242c944001c04640b6101d07542c0b41032801c0406183e82c800d804d900041000d02416400903603403648944a60034113807402e030400f044400010b028480c0030b003040d5070203e0f244103659000e0301110003500c003944c000707030301c5510421005100410902030201c0d940242400705005041c507000300a286032005082403056803c00c4c1d607020003019036000035949031040548280110b00140f009246042244e03402040c145000c109141c80d14412600c0c5030941ea00d424104203071044c01000341c2d011303400149040640d00e0494100501c0007a40c0134080c510341807800c040e090401d40c000c200714650750b00c511001e01c500b0b808c0c50100301c8807950074400908046801c1101507480c0c40c10783d005140044050600140d4140e0074560240b0f4400240c0042c00da074000c43d24248002d103010400f00100380d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 57736316 1250 57735066 57735071
    0x90c0705100920010e090c030702070906030203031207030f0e070527040b0405030c070602150901090c030b0601030e01181403070c0506070206040b0a35010e090102090306010605030613 81
    0x2e50341c1d00e59040384030801c1c1c541c000040b20800030825a00c0307807803600071907400140304091031305241850b200c00b60301c141d41ea10094418450000765a007680c2c01000c0031260018040e504103d424040a65058070003000841055915002003481104910500d1640c0012000800c4041c2c00c0030140b041d03503050700c10101f03c0001c00030302c0510f14154030a840b56119034400044680d075116032034000d2442c01614586260780c0100c501c08900700754005044140b203002c0c041c02030361540b60342812500304c0d0301611003d0701c00c000d0343c01e00b030010803141c0a48680001040c9800142891040c950ba1b003161403440b620440d140006010006203c40341004000c4010120051480d02c441591b0b240d94400b6130780710b0b0783d01581010a50600f03540e610b00680b401007581c02c19095841c0da6108006216400200985407020318000f52680c40400391075207400b00ea04503914009240e400e09221403810000145100ca9540d000c07c000b20050300c041c03198500038281038407980e44a0234600700b00300e8001c640c0034000700f07402d2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 57737566 1250 57736316 57736331
    0xe0706030b060301031101020a05030c0303060910240e15091008060607060f0f0204061115091509010603050304031a15060a0309030c0b01120201030f1802120a02090c070510 76
    0x640b21030850b0304690f0b2165040003503101510050b410200341c0040074042e4007002c2581203107040c01100552080401300c407010460741c3d44000b07106044e03440b030059502c8452601c00c50503c84c2018010400403030107a061080c0b02c0c05418000400000c484801d0700c03420b440206503c441d5013084016249442d9080c1016111450498081002d5015000d009004680c6440210f081c11407507034441e80c1c0340c074900001907580b152107503406001c241e981c108690007031143c0e1016440c0101144074460240070100040c00d048414654410750034000501f00210720b558861001000803000c00081000710310490044036402e081d00c1c9007855070100180340ca4582000c004e00003031103030354510403201041600e003800607201d80b9a082c00c0350602d103580780c0141160a24000405c90b00ca00d82e44072140a4802d0f40d061145600742a00082566070398400c184100c070b540c0302d40900520b8152201c091100b415011546000e029400182c0c11003404e079407a4a036007074001081e1042c000d0601509141c0c95030008140241c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 57738816 1250 57737566 57737569
    0x11060703090507050f0f0d0303140112020f040c0813050c060711090702190f030e09010b03160e030a140a0b0a020a120e0607030b0301020c07170705030f0d050d0e0a05010e0706030b 79
    0x4505400825201e07903507c1c03803101c0815004e54807511480381c022040300c05941c0c42da00500c28100d1000c1b001c0c0c2c0b05038100c20000304a4a0103018201c0b0051007a55440c1454554000025808a80f00000c8886008161380070540e078a440001c1d05110380900751008ca841c02c0e840038085001c01c0039055104540103020032002000c5031162001e01c3e47e5111200c1142c40d40b03241001c1b0740404128030403aa100d00b400300006802d080c202c0285000e0042c8118041c61f141c6402c1080d40c0326a143c880399609030700000038803008940b00012031a80c2600072029540485201d540b443c08000d001c440148100d5030101d1340c81c24041e030018510b00c0f12505038900b0407100c0d4904446503603490009024408042d05d44c0a84030450320300790107442e42d8074101800c4590311900c2da0241102c81000400c064254854000300003400d01d000111007501160741c00140c0701d003031604041280e59500c006003010001e600c8000c078031203008040000041850140d400094a103542c040701c5400c0400d140d006400705810a51500010b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 57740066 1250 57738816 57738829
    0x50103060e04030804031d040c1701051c0f060914070e0606070503120a0f06030c030204050a0615031104050d050f07150509010e0a03080a0c06060503060c070b060111060703090507050f 81
    0xc260942030030303010078001c0c1c7e420303000800240034096081420078564030751054204880d07a46121406254025503a200c0050240100031207020851821035004048081006440340415080c0101070200c1c0c90842a220040c84803000080c15005900c210020001d19501018094001d003080341ca01c1d140c03154548030140c2e07d004134505014a42450400300c0c441c090640e012850440314100140320f15a907a051403401d102c1c4070712084c0d008504100010703070328400310f01c512410350b80f052596842441d54a1300407001803c60501e8000e038400d080001088990350344c0389401c0e01754407400040c03611601d090913a07424806280c0c040e4142100454510101c2500003040d0b078902c1c08286071001e0719000c65400a0313200c0305240d002a00030200010045400340e40808500e9450b80240400d01400c4d0b90b0342c06040c1c0c0c0b0301086807103824010091005a000412000c5140d400002c1450007010401000d1a160b043c044150745820100c0e40d074100724030070020140525001803004072480c1c0d14000031800403424 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 57741316 1250 57740066 57740071
    0xb1915090b0f0907020c09060a05010c03080403050c0303161b0506010b090a150f110705060405150c010507021605040603020901290f0405040608061302060a050c01050a0204050103060e040308 84
    0x4260340301d0030301103455120300010000882004051000a08107100d019455102401d071042c0644206070003d242410103403500700803680c040e5034040d811510358604941c8020041e1080f0f0402c40100300e41d6015090030405580103151000240004484020024102d001e00038050f4201130103584c0241c01081c40418031030304440c900c00415644080c1240000c200b62099003250780c502c4098182c04d140c00e9440000390410003210303140d03502c0e40303944100c0b025a5400c1910034503510110402090005081c00404803001c540c0081c2c0e00307030902c90382c0ba040d81d017914030880d9004016488400b5800c903c4a038060b441c4001e20081e01c04018641c1950081844030905004840880e0700d01070b444030002210315106202c14500c1c074800c1c5c1d111280510b1208059000c1c0c41814440d50174140081545140482c441e1301a00408480c100600c915600b404440d8003c07a2035074040c030800b03001c2007404086c01e01846104100030311006a8441c00c100000d000c450040c0c0001114400c0d610402c800650000b5180d074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 57742566 1250 57741316 57741329
    0x9030521190506040f06080708240105040b04090b161404030c0b07082b0f020a02061b090301150305100504030c030302030411060408030d0e0c010e091b0301030b1915 73
    0x440d030f0390b06008038005d4250408280651450b00e80000344a8001198050990340b104c0c2c140c1e50b0386000700851001811441c0c404641a1800c50010011880c1aa000e038151001c0030308003050600c955140e00e409503508480b60308a0103864807000c60119800740341c0070621404a201c103400d050440e01e41207207070f014034001d02c01000400210803050150f51015a0365004800c01d02daa003540c010000340b8001311041007000300136403d1001546410740c0500070b5649a071290303801040c00d0380d00e098001c0f041e00349034000e21b10031700310801c45000141c03420300410440c001602c0c0002000d1740741d403034082d1410a0b001e01141a8510b0541808002988048c4e80140c3c160103140c096200d0300c460819900d40d42c000b8155613400140000d0014003180080b002e000d6221100c8002c1284c031007480a203d445003090300002e80000c840c0c2805c800346181242d072451b0080785801d6040b4140d09810440d180a60080c0c00a131040342801040281e483c40340c00c0300214000c600e500501c00480301001000724000d15000d038a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 57743816 1250 57742566 57742571
    0x714010c0f050f07030b070503041101050a2d0215011419091e0b180601050a05040902030c0408070f0f03120c02100914010e0d081b010903052119 64
    0x24800d00000c0041c619801c003040d41d007a103030a02045651420144030807103000400340001070200f0f0150056920481d040901d0030001340549004640517408449040c003442448421940130808001c444104a1501c0c0e001181c207900140020b8980300c3ca005900ca207184080740140708840d040c42240c102140306880b2081c8410900795070b600c0e0b10010340c00626610f072404002250444803010100040c2424050402020416006101542d04d030312a065045881000110b5000c2d4450401071241907078034039101d4103080c0c5422100c0103076403040d2403544042d5070200d000e0203102c6003401503c1c01044403076140e2281c0352400701e89040211440c400989043c40200c0480d40050045182141c1140e004080880b1001c02000140200c803a07801524507400801031100a43e50180510409a20008040020740d042680d2214000c0c0d01c4200d0202d1009801040341400e14002d00600c10042e2081d00c50702e840faa415440a40410000f541e5925504a044140300803000c408450040d12818003001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 57745066 1250 57743816 57743837
    0x60307080a0c15020a06090c060912020109050f030a050a0f05061608010315021204470702160602061509040f0213111c060501030b2815050a090503071401 68
    0x1a81840700d41704004c1c220b82d050881071410001114481030a48000342c950764016622440d400b22a001644402400310700150401e11040c80e0011482c1c501c0c80d80101201d808080c141d42d000d0802c0c0d10618112002641e00b0121010030405101580d448032881c0f506d031401e40e036583c400a001641c103100c00780220240c400510228501c0d50122030043d050304103812040e05291605100070070388003003010241c1005038034105403032400c0c0504045c0b01155055821001c0e031010300c071800b01c8174054a01400e620400070940600701c070321080b04000388219009000d0510701090005019007060545034862054041004006000d01100c25101501910031503850401c5040301402000c2c000e00c03610640101180c05204140b156056030f0100b4083d031410301842d07540d4001035040e250b284601603480381c2c9140304000000c8441c0d195100441406160107001540c40d802011601d41d8502c0140c002a00080c0701d805054010f01503d0041c60300790001c1c0b4a4501e090440381c90841c9003c211810401c04404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 57746316 1250 57745066 57745109
    0xb040c0206070c1a070e01090603020f070303050903040503060702160e0403090b0c0c04060f1d040b01050d06020d090c061701030503030a0b0105090414040506071d010c051f05060307080a0c 83
    0x800048002428030803984d5400c2c100409071980d101c00610314000391000101080d0180b1a00035a02e805000c0c2c8072403814180c2e035940c02c4e0054800144038005038072060000050643d801c00c076040c01950709402030302c00810501903440c103108540e040a6040c00d01d1303905000002e903000c00c043c4100d07903c1303208103034403080e0400120341441c0c5c0510a0f00c3e0b01a00309a000b04845610012100c129030030790341007100c0803400072811201d00d40300b114041c1641200303200400c40303030400100070700848d442854018a0310b28410490300449905000590b07070039820032018440c00e03030443c0c006803000c1404040441190b03d19034600d0307030340c0c0b00081110400c1034403a07010144907401941668241e0340020010b2002c081009101c05107000204c5094455220300008643c1300d40c042ca256041e46040c95408000d400314000055072000102c0c0c004541c03910a4000520359000440d80800a01d45214008078150800300101850136240790400c84250308801d0952001420000743c110440e684601e020305008070f0502d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 57747566 1250 57746316 57746333
    0x3090e070c02030a0507080f010608030d020c15011d071d01030e0a080c010e011401120209060117040f05010c050f04090c1b050c0103060902040503190204020f0403060506040b040c0206070c 83
    0xd4140c0b182084600c1080300c0401c6d1381e0282c0d04c0300b1040725112a03000002e2400c0c0d41d1a84a0041d09410400844080d00f009800030321508240604444411541242c51084210241c0c441150800a00703140b4180c0c0864003800b0f0b82140700ca00d410051920480403e5606100c200c2c5024103259035002c0e00c804501d01031004100385500510340307a89038051100d01c140031f00b0920040f0308280d460035030341000d10800780a0040c1600c081c03141006e0514450b41c00c2c440c122002030002d9040c08140802603051091040d071083c0b140c0d22500c00603003140d0080c54020b00703441025000d00c0034810180882140c6c03101000071385003203e4507124089401e9540300816181c00242040d49401c40751030394148418090001400310b240131080c0d0307040202556804000b801c9004e14081d00b607140e00040d16920010070b0381442816014002000180340c44070405050400c0c2d8055841100c0c0e150300d074800c00445280503c1b070007400390002d0b02c09111015420794025160040201f5540a11502402e600103001030303070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 57748816 1250 57747566 57747587
    0x2121c08070f031a12160305150105030106080a03140f0412020906030d0c170c0307050a0b070806060301030602090a0f0807060215040206030606030405010b040906050f0a0e0303161103070c051c03090e07 89
    0xb06800541b00c1d8503420656122603601084841001600c000081c0d142030501c126000c4920020190402d02055078085460740030700d00703060000040c280250580038403e240280014170128a442e0308040e02c3d441400702d60340006008520980003250401d420a400031705032005103034407407084080c26080c500c4610a038044e407001b0750310500c070114620007004400140a003610b40641c01d450410742d1189001c58000ca8101c0e000c6410480c14001000090b001c1d8025200d0341c000100151001515030b56913400c290213550007002c00303600c1007904004541c1c051104200700401e5401d5a50b180c174058020030544c0c031014244030f0080e00d00100103014014290311542108400030014000c0c0e60150800801030308041d140c04440c03010a801113160752019208409030a5070071000340d030540d41c0c3c40f0194000c0800783c501d80740a20007006102c0c984040240001d02c9090700c12007000d41e1541c10003060249094146007100d100e01c40d100007500119800ca000075048558030041408140d0368001e084403107010700b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 57750066 1250 57748816 57748843
    0xc080c06010e01030b0903030403020c01050901030e06071214090a08070c090905060406050c09010206060103180804080303100506180906040e0d080403020606011b02121c08070f031a12 81
    0x3480d0000c40c05a5800c08014100d0307025010042d899184c9210b690386911090718003c015034090300000c6460b5020f040507194441e014103001901200704500c4a04019048074840000b4400703010000d41c0000b41d1080380c0074640d2182660b0880c0c03912034840c0e540c1d1002101c0141c0000c0700402c0e00c004001c0c4902c0c82c0c001400c2001e009001e001d805152407030f0b444800340c600319401401d280009090101050946043c07100507070090070243c41c2e00c80190000d0001441101d0603040a50170b0364007146082c001440200b1121004560300d150480280341010a0b607080385104d0902004001010103030303039560b402920350443e0080c055448020025008010351109443c103405814001980f0941103c0110300c2540680c0039240e05139103020044805072241c0c501c0c0b840d0902012020320250908200036844000303148100c45d440b802c60401101c7c0342e1010340c141c80010f4030384010807080c1980701e41d814028104030308003400710881a00f400170072044601052030140e0580c964061016104010488a4900 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 57751316 1250 57750066 57750073
    0x2a12280507032a0906060201060b032203090518040204060506040506030a0c0318060209280b09040e01021207020d03050c0909061f030212150a120503040312120c0f0206070c080c 78
    0xe4a0008601820f41072207280059480c080e270019061003100c04a03803050361140d144480d09501800e00300c0d44282e03c03c1c01a410440c2140c40840c10340c4448001201030303410781c14061080d10f014030420040d107846820141c0103e20070b010070443c6441d40030540c2d0300100c1030390022450b0134000c03808500405100312000d441c0b0714940c150000307100c116401000756080940300030410001140e5040340304440c5604082429041550811044450401078062003100a00c0030a481228940c610300766000007006c0102c04114000f4800340c01d404002c0d541c00f2a060b82420301070b5107843e90150409000c2e030981103020303544243c00903066946a2101d041c0c00e031012300c42401380075911400100250000c45040e0710f004110b0f800b0030345900150040a01c9900010700c000080d604042100c5902181d18000701d9041c0710070f10001c0b0015005003241d1180e002240d8034880c4240049440b01c1c16264414809d90602140d1031303000010543c046401c5a1000c5181402c0c0c0c0aa05103140c444050700c500705081c1d80b40d01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 57752566 1250 57751316 57751319
    0xa0c0303050a030b03060c0a0c0f0f05030310060c050307121106010e010807060905060f0702180f2706010b0f040803030c03090f0607022a12280507032a 67
    0x58011020305621901640c00b001340c030503c84c0505030344880540e1100070314101401a41e0307085114249404c1c030248030380d0080a51485e2a61204440035607030390201c2d8282c0001c01084101203540040c60010b200c00c1c9042903100c400c079110203031a8401e1010103400490003001c20b5004074001d2305540008038980003103071140d43c0e550b554041614801c0c015000103025161000840c0d51040c2068000d841c002052140760240b1a4400301440d40002c0c400c9030041d400d101700800c0304034103010f036500c00c00009180d1807175450300040d4410b944900f500721108540e800e03d2250881c01001410358196825807003a503955040e20104c2c3c4025000b03c1e40686103611000080141000407180a940600c00c1c60080700d08123072503100d110f5290348086030b0400044c3d100e90640c800500c01d90b002c3c043e40b00d6402414003c6c0c1001d0401195168030b0b40d807442101607200d00020241100c250310321410301c00039410381711400c1e4072690300ca84d1038034650711002e0b100103141c04041944540b44501c00121560140b54981c519 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 57753816 1250 57752566 57752573
    0x90303110c07080705010e03060c0306010c0c0f1505070b06010e030f0102041d0601090b0d0209040b040903020a0b1018020306030316050a03090816061b080406030204080601050a06021903020a0c03 86
    0x581c0e003402502894010300c44001150350041c4401f85000b18020090851591401c02c403d030355030801000c20741000411100880416462104040540b56800c1080442810a40308a01460b501001d000400c00d0400001f008244a14800341d00010246042e4542080f5940000e00e4907144220140d03070b5502c0010000340d045001820b84c0303100c0203030500ca003001d5540c6400540d00c3c10410300c82e841032120104021502204c50358001c20300e00c0c100520000b030840081011a04440c01544100c01503403001039608180540359211135400489041c64840302420082030310608181e8441c07218a907038011000c501d85a600f841030710400310f203049840501c101503040030f580c1d400b0301141c00d6000c24228030020801c0000840c182c0301d00c01030381d841000031614001d4200d40010880d0055000100e40f010b00300c1c001030f9684020801001c2d80d0350090b0b2140d0406c007003d0b091601c184c0c0a1841403c00f488100314480d00801c55808000d8000c00c00d401c6c410312410300768100003030b0f00c400070b1014140b19800b2040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 57755066 1250 57753816 57753823
    0x3090106090614040b1512041e120e10020706030903031d060f0c03060d0b0901020c160513021201050409021f030203070e040b090a0e07080f07030215040b030a090303110c 75
    0xf88108076028030291480e08107026000d034000c1b0a060f07600104010071402600072440613a003207171203110b032010440051240211100103128046688a4500320080313941648420300c658040d00c2103504082518040c0e03801b96548595110710400d050701e4614035000d06020ba030000014401c09100d00c01c0f406094003a464880400312010705d0610001e03404510920503800c152071141d84003401040c0125030a8650302d001c001c004007005070941d000c10030308103032420600070400b0825158180c1101d1904180c108030502c1c0f2016100d4240910501418085107d1a030406044a0003500c002915401a00120b504111101c410310a262130311000c0109196050f402181300d100280d5880c0c03030003418202003100365034010380d026074007000c560081041c0e10b4040d03011103540c1580310111441d4942c4d50750002d040240c03201c1d80e10700a809c0a8810800e50600700704c00b0040086082c4594502810308900c48942d010280180d50344954840c3d0031401c15000744e00c8407044a810070001500c511100032084d56 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 57756316 1250 57755066 57755099
    0x100f02011d01020d0c0503100302011b050d090302120a0503090f030a08070c0e0c1614030d060308030610020105090d050a02070e0f06151e0304020d020a03080a2c0105030901060906 79
    0x685c035141e0000c404a202e0760503640a180310380d1121007003910390703001101c0031841d440040318440c941d132a4041c00030740d0810981c854201640c4408000303a26600400c50500300001182c55150050082c000000d42d021089880300364080724403400080f48080401e1910a5401004115010005014082c42030681c00780048980f0070401c02c620740d55100301d50500b070059519114500c4401104140001c45942c002c10001c0a00c1046901701803522041d402500c0c00703070340203940f00700d000020300c1a07900b401e01001c8401031050000748074038105a86602d50724030310416180200071002c10710072240e0384244032182c0105810300303016406080507504443c3d405c0050710124400c8281e0040f100d003404912081d15066000401291004d801c07070064040940c1c8001d1040383d05c0b000344985000182d982110250155009034002c54603184050405000c25902100015001d43ea171104141d0002d410000e1011100080ca0400d450b41c6801c2102ca02500d0143c00c05074815040c19004500040700d4810b088 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 57757566 1250 57756316 57756337
    0x806040b09010f090c06050711040f0204050102010f020c0d0c050321150f0108011a12010605071202010e030d02071401060305013602090403050d0e07030309050f100f02011d0102 78
    0x4546081c00d06010100ca42c1c1d0b4000a15030321248801b0444613001e075000d88011402400b01c3c2180e1504c0301c000508070381d8182c1445605c41d6011406200f00e590902c600380c0b11f08080b02c0c00b14a007044088003907944440c1240740703008012401401c041009802d0058a640305503180d0b000886120344200c0b03001b00395040310036800e01d40070307100f200241d0315088112001020042e11a10b4241e400e080b2581c2d0400c225a40361054481e003000308105044e511034987e8020992940d0701526034125140c603250041481e82e0b0903045a04004890580040200c121800400300e9000140e580c0302c1c6250070b0b410040103a400211951821400205000064200041c40d4000c402039040c400d6402d080c842d1941c150011a6203180c17412181c40780113042c12540250058081c0c18a5410f100509816600b55403228840e502c01d900041000c108240c0c01404010281000f1031790450303d070346400c000c0f03100301c01c401a010003001000d490411400e4000c0d409940c00400700b84450039042d048540e024043d500c02880d44 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 57758816 1250 57757566 57757571
    0xa11060702010b1f14090d050604080315031b061b0d120c11060a0f0b09010617010e0402030d0e1504090203100e09190c0504020c060f0c0c0705190806040b0901 70
    0x214a000c01d004c1500311014519180c03c4520a60f24031000040c2d000f582e2401c1d003020201da0031102180d01001038030300c500d1003440d409940f40380c00d03000c982d0b80240d0042a6070081d4045040f1242038050340c161108440e4003950642d884103102e490490702030010030380d000a24019100f150511903070166840000d80892070041c090300d898000c08807603224418041c003070950005008200e083c402508003e000c20002803020500b400c10b4800034034002020b0b0b2000c40805e105070082d900d07121840e50f12900502841480c0c203c28502900071980b140d00040900c0200101c0f40500d000c00d56410000703003a6a86000b50f44e90b140c80d2200c40900c003c0d8015a40405420b141e844000b50241d01e841c2e60b10b00c20802640549440325803d008414540304000d400c030741c00f80c03001401185039120b901c0508840c000800013004181414a02c0b680180c0c00904646c1c4d4240701004906d2041400252420488506961852100c540703503941c07141c0300702c1c0c50b040000d01d40218024442030001d1401d80300d000705c034180001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 57760066 1250 57758816 57758839
    0x110f0309011515120f060b07061503030503040803060d0501050108030c010b0a0803040302011412160e01020705210a0602280e091b07050106060801090c090f05060a11060702010b 78
    0x2c4400c504442c450307100d44461842020801a00c0344002c070f00c141d0a61540413500390700603007441059070300c3d80e0002a8000c0021130450144040d90141e40d200402d0744480078001c0b4110b8070014864800100060101c40001000c52241c1c3c49200710480e1494015000308100e507143c2100c1030700ca60000352455040d40c200a1010f08038070f860002c41c070446107040021071034203180d41e0041d505c12462410a90b00c0c90070500c0f0300340e40e07924100c078194030a155000c40043c4841c41040c001c1d003180c2124030924115800103034148896220280b00d2040d40d00003030268604035080c003903550324081c1304182c01003425001040e040100c2c50508645012300300390400c5110f07110722040080300c200094803c0150f0206248004c909500d004582040b0b025501c034402d6450040d217911401c0c01d40740f45500440020740c06000400855003980310b8810b41e00140d01e0010552840d0140c600c240c0308480c040c0903c47c400c001000c1c0070b168010284000d6028480d01610b50b103203020034000c1d0081000c2c103480f60241804882 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 57761316 1250 57760066 57760091
    0x28240f020408030414060403050a0b07080702060f07030e01060b180f01080c0304110d05030703020d0e0d0321140c030121050d030507050408030c071e080d030906110f030901 76
    0x81d01e060392400002103061610b800c004180d0444503150300d40e0080d20810020020800c207100c0910014015662007000e400c0c0524000c020300e0006080104540045040c81404440418440c0c5c001d00c80c0c0c80c01041c69500344c844a0300500c01ca920841d50600000368011100c0b26400d50780a601c902101c1c50314488911000550769180b048942e5402504104001400034000d80354000d910300003c0c00801c080b25040c0da07128039550002d0029409a0710503a6800015540b001c686001c0150a075000940044266030141c4000320004103001021802e110105c14004203510841420246140700b900a00340845183e020350b000f802280c65083c0950040c5601162000740b0b480c0f036030392141c000d140b100b9001004900401025002d0b40404c02c0c10800066641000c00c0a08400103859010b080700500d81a4465504002d0302c4101c10040e401c0c4e00c04000301a80810035449080d202d050100f00d0b4030f031a151400c02400211082c048590011450380725444060380654031403d914002000280d00404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 57762566 1250 57761316 57761321
    0xf111e010f0608070e0903090d060f150602151504020a0f090602010501050a23090a02040801061401081f0801020403030f0e01031b0302090409080304050c01090b040828240f 76
    0x700030030f0743d004840402413000c0d0110710a9000f440c00301541d00b082d06a5001072494190141d05580140d1241d0021108004500c5034200304001045c807450f1291414a0103502e03002c0803072400a0070001d01c0c00080030700c4001451905100d030003c00841d0344480c4280c015006e40c441e08001b5000481c03035140861000d005110b0795059407030081450545628044041c0d48811200140d040d41e00b109982c2c114458550031210350003005200d801588075410280e02d1401c42d402a0b0040c5618036807501c4922003a40c110403d2608024403c4807084e11a00340d5030700144100341907010303545a40c40003500105240d4001409446024950341d600b01c8100380070011425160751034102d105d40c00e00d5032840605c650280d0300424038808041c01c040754808682e1200040c5810840741a01c460f0040003284109623442254100509080765216007894140f504403580c40058000c40c07032161101c1882441c285203941c20101ca4a68401d102070512101d542d054102c000c01e103901c0c003802d281088040312010b1031030b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 57763816 1250 57762566 57762569
    0x171c0801140d050f0a0b060f0a03020d080309070b070b0f07080910020a020c09010b041a0a090504110d0c0e01020708030406120b1507030201050405150105010f0f111e010f06 76
    0x51003800108052042000512110b1000c0725940b0489810707107046442406401201c41c05005031280c00d28001c400c0c050460030022015100364a019020310040c0d54004201c15141d0b040581161203a44188450b80303400303c550401d4040707400c0410490304101950060b10b1142c00c00d406810210307111440b065038201000c1e141b440980c1c01c181c0340d0f207032141d1440d0301600c40c4001d5441120001c1c040f080100360480d10a0300400d844040000e4203229140d41130041048000101c92a1481c4c0422100b00800b414042c0c05a80d10a03910341041e0015a18104c1c04e40e15803018006041111480b6148064040c0502c3c511241c0035001c1c0060000d402c440220a660442d0710136281c4442603104661800010050343c18403c1d8800380040070038494061a001502c16607100e5000002d16040a092203403902c844010068a00c40681d4014801030b41d01c501c202c503100c80142000d1001000109040e02d0340d40f2600540301d440d1055180000c0b481900034420b44d0784009040081140c00c241c0380015080c0c1300d29 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 57765066 1250 57763816 57763829
    0x30f0903050715020409060603020714030906030a0e0c040c030b0301050609011d09010207060e0a030e0a15050309010e03030907030b010b0c030306060c0307080f1c091203090507171c0801 82
    0x1070100e0000325034030f40200d00c660600312800610741034550400c0300864074281c02050020713901040b00001c02140e9410b5100300c1d4105001142841c40b040002031603407000030402c0b5000d507290040004403403020401000b0606006100780074a00d803420300100141901d0303c5072031003503090002180c2241001a200c0c2c1c142e40b0340400342e051950f054280b66040143c090040003c66600b0056100401d030280308900080c041140a404001024140200004000340d0081d12504810001304017000005c0d4120f80007200c141002a1a642c80484060041c2031080011145010000400c00b0f4038402080d176400b521b21030b400c808a00c3e6291407040f000c0e40501c001440f2590720400c00f2507014641440036101c3c417620882101c1c9007c4240d6181101a0171070344071848441404540c06c4500502944020088220880100000c2e402c3d925840e01040c00c6a1f9014241a510102141400414071000c4054a5402203403580101d02c41042d550782c0741406500b40030948801f031417404440c4124000c81c100c900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 57766316 1250 57765066 57765077
    0xe100801080c01050a1e0c05100e1b010e0406080d020f060c0a0c150204060203030f06190b09010c061406040e07062f0f0c010f03060302011d0301021b010203040201030f0903 76
    0x30b650043d11240d02c0f10600c0c0041c0808603003000e0303e0040d14a00c02000d001640d94507408211103180492414900b07a1604039803904000080480810000d584298105105a20043e40140b400144d0308002d841d804250440d051840c04180c0d24000a604054000f46901b01c0704c80824038040680c03502001d50303001c1e80d4100200b203115180c5103c1c2d85554104c038001c881084031644030407118000c80e48194403150250704080100100500c1080380c4503403000702500d000e4440300300081c041c0042d0819009855510501250031112a44a4000c1d100704544c40181000b0a12141c1e502c494800d80171240740d0300c5035081011654407004041582400c03180746450300c521002006809044103030701e8200c541d031031301384000c400b000780ca0b000c105c80101003541002902140b415200014405541c0e00c40340003e140c207040e01000182d92002d00c244040c641c41c2803040c000011640064060b11500c0c118403d40e031440e0403036011750302c010b500440c0641d00c00d032400c100d10684490590282c03590502c001d0041079 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 57767566 1250 57766316 57766333
    0x17220603060501090312030e060f0901180302100507140403050105040b0606090d0308040213182616052103150405010308040504020706060e010b120c0903030306131104060e10080108 80
    0x11400c41b548403c0000c0c40c1804148901c62482441c50300d030080310b5412040f4021401d10046a03400c1c840d200c45e40b2142403008140e41c08549001c3d6890100701004085680e4890014600724400c0c3d104071490140016070341d546030303600c0c00d003240a020300740c40646800c400d8602142c0e0314039045c02101c400c002c014081188000d0142ca080e03c129a00400581c5c01c4140c164401d2604c0803544940e1108000604c090790070708085007024081000317044990b88004070b000c0d000d909044061003d0340d0b0480c02c00f20101010080c00c1c50076604040c14250f10f241c00c1030103030142ca88200801f0002d948180c0c1414071560542450230100015160300780700241150380301300720500250509800419840f402108041506030f41c40d4901c0008803000d80c40500003040202d000c550b0014400f040c15040007501c0360090401e40b001001070344078440038000511510480141102e0b01800380c10001c20b0102141ea6203803641e0b611030000c0e0070380340c4041e07415104000c40c2c18500cac41d0300d00401c0c1e0b05059400765401000c102 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 57768816 1250 57767566 57767573
    0x170a0e0a0b09010f02040b0406030518030414010509060a051e070b040605040f0f05071406030105150901020703060204060201060501030e0d0210020c2805060f07020a030804172206030605010903 85
    0x8100a0201020b55495007107a1410390701500041008102e034031501c07644e03646080720040c22510b019003103242405802d00104c9040c10700105075400d86903015424204102034200503140c61081c1e1038020340241010444241d003941040c098040c10380740c20810580c2046450450080388078070440204022414401b1401103081c5a00050f400340c0308400300c036074158403034444e0490340d030a01d40201c41d103600c1441c0601000c01c6105218800d40000e907011401e55041c0b42c0080c0c0700c03007050f50900a40031000306102041d0b0703100b0820301c00115006002195907540310400280a0401c034000d06011030704003494041a04000141000c81000550185c90b0144803200300e00084d5101001100c101c0c812a802082c1c12114880904452821600d030044c0d895545c1c03500300d0030000c0042003d91040804820043c280d600811142c01c025807503d082800c517525840c3c04007940041f0201074500c4200812800c01c41080780109100d214103035003624906036a510011020b4035050701031640011182d00040001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 57770066 1250 57768816 57768833
    0x80606040e010b1c0f050601090512030d0902030c0604140319050607030903030b1302091f02150403121409160b18041808070c090b01080708070c0b07170a0e0a 70
    0x40040850b881300c00e101080321250f00fa12081c1d25141c18040e921401e2150315a000a82017004001c03e0f80c8a20080c00b915084548a001d1401e00e40d000e00d841f00300d10400c543c0c0a00c80210340782c038020503150300c89481d8500007a480c0040c1d40c946000c1d00c00c00100c403000b46400c000c291101a8070000802c4250b480c010114082c0c2903842d411420706494521084d41642d85000303c4290400000340141c680d90090104004100c2440803a1110300400750b45400040d40816490404408400209440c0d120b9150480e45071f000d60140e0090bc41c070304540040702a0301400718600940d80c190840d8005504407100b8840f0354050b103c3c2342d0a010017002204042c2418159140300c00c40001d00c001600e601a00d2619005076107004129481c10740043d0003410400800e039051301810038040b08000d5103000c50000f0345203d05c0034082c070f824003007601c1c00265884c0c800c1d0302401a80d54031840f100f809043c44440a02035070740e000c5c80341e0594540440010a2a00d2901c601010b002d0703480000d251108190322000030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 57771316 1250 57770066 57770077
    0x40506101107080105071205100f030b070e0d030905271602010e030d020307021501060503010603090f0f030807110105090a0605180d0221070f0206090409060504080901080606040e010b 81
    0x4403401103842c0003070343c91800c1c481c140c45094291101801d20b92481340010480e54010203034240700901c1c0400b40907446034810300c0020740f640161b440315503071201c2c502600c4aa02d8145403d50000445102c0310805031302c6060f00702160b905a60481100705041109269032400110280302c000380207001404080701c1320b060009980d01d50000151030184100c03070340c5c1035034490002a5240c0e6000000d00c0740303081d410040300592400d810190340c0c00e5410410700a05600c0188640d82c01c1540700c10031502406032a0321582501684000b8200b07100c0e1251902a0110204540ec040494040b03552944082410b00400d48100c0050024020300031966a402000303010117007841352820405907a1103201c19040083d42c1032017520390000e103401c0000710303500200e031120b0f062044103060303040c0310a1000502c00000c0c087c02c10390448141d41c03a151200042001800e60f01c0c0040e02040c146820702c028046000002d110b206020317640e803145541d420013401201c0c4a58400c2c80c00c00c400da40010884009507101600 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 57772566 1250 57771316 57771347
    0x60605072f0303030405061501020f06070c03031e140901020702030601121109010608160906050304060b03031903050105090901050f190b10120b0109230301090f2004050610 76
    0x101d4800031404645036400444044800d94011401d0021003450b11540660b03c1e07400744000c19043e03d0201d605615801c001e020341c014042d101028208044c000d400101c680c607240355520301c44d000c00e60700501c042e0854000001840c1f601c100401c0110754107008480080b5005801032a8503460071040e018800c840c0311003500c1d80c8003450701224150b901c2d620154000c00d06c41e61460700074105401d03a402440006410032052110a01003003001d5500003007682d41c40f40d04420001009148140400e007544500d510160a844031104490500794060340158103842054032000b000340d40e03802416003214015500d05003900b20f8500005c015580039180000c003151204c1001c10703046c5608000c0394000e101e1034a1000420041284010010710078800e10100c0002480c0500040385048005a504e01c419031800c001c4100d040f070880190b440941258031420f502865168880d92282401c10507407951742d03841c442c001c40818807401913280034025035004d410001c2031042c04a0104a050f6280d070388211142 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 57773816 1250 57772566 57772643
    0x51e090319120212010305030703020118020904020603100906081f0b010801030b09030f0d02030402030c100e12010e0d17070302040b090f01020109170c07050105071a0606040f0b09010306060507 85
    0x281c0c4c0c0c03250200c4002c1c02184184011a03c0703408070f00c2c1c0039003540c0e02900c00b07010312072170b00044101507500d040c20250010340590b0200d0362a200d41e00202110351450304200e101030706000700026030310000251600f551031480740f5a101000c0300a00a825030398090304090005841d04010310119200440c11398003c000d2504407890540d442003400010340142d02400c3c05140d01204200c03c0d424180552007246504841c40c220380005140007401c3e440d8074001e09802803040754030042c5032a80951211000c010b0317010071550486645035009010690003070080300d0141c001d1002c80d59860080c02518103507a114010281407907411740501924002c3ea454040c1190f4031002d081000c20502140e4510400703000c0d10540d5070f0320310601001c0c6003402c030354403082c10480c0400c030b02001300f00080303005102d40744101e0580f80361307441c0c0d1b00001c0d002c0c2c05250401e62021044080c0000c040d2150801000652820307241841495034841080d9401e00a440c1c0243c50500150369400241190750590403c8001c00d00e0507 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 57775066 1250 57773816 57773827
    0x70803040b0a080c1b0606011713060e010b03060c031609060f03020702010504120f0209060a031502031f08070806060f1c08040902070c050301110a050d090312051e0903191202 77
    0x102035032003248642881103030020070901100b540d1107540726480e1201271300a20040d052465000700d583e2010100903008a41da034901c0c8450810a400144120030f00400301c3da03242c01d000ca40d0802603072060341c00400811900e58080d010314061624142119030a440300c000120a040c41a4080c3d4440c1d14100d0400078200804641e50426030014404035009203607201380341c410741c818404189000303041c0c0c1e44506003019080000600e8032601407190114070f42d000d031300c94032003070740703900c0302040701c49058004125500b0049010705001421038201c80c2818111209900d4034002e004240da10075400030340110300000b50019004020622101c058418074210780380907610b810140c200d800c91038080718841201042001185400d02400403070a1110280500e801080d0002608502c203c500b12019540c645101c403080c0f42c0915050303ca142d070741d468240f0251820b600812065051808104601c0504070041000c02100100340d40155400d0460b400745843c00d010240e82e80e02000384a4482580c00f00700 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 57776316 1250 57775066 57775087
    0x200d2a050d170f0a0c02030c09100b0705030d050903030415090812041a010902070204150f180e0607110d08010513150b0a0305040201080a0e0a060504020402070606080d02070803040b0a080c 83
    0x7416413103c0c40e0b4a403d91008548100350030151030400e12480f902502003407120115030301d00300c0401c950100c8921940d038000ca1800d1030450191905400f4010321300f004110b404680400214070072482040005210304201d00040c04451110380c019200784000d00080f034015030210004c0f03800c103000b41c02d0400d03a103000820b400c02c1f525098000c07188498000c0748160031810302d40551181e1040f880c6030f06202d18100705280c03d50a40c103104000040d005414500f0f140c0c1c6240d40000e0182c100181a03e00e28a08000701601d030b801c91580200c01d41c49070841a0841ca44078030981c5060300c00042100139126156102c2202905203504011680d070480900090760fa02044002c118038940350314082180c2c0382c90b0001505174040104500303034107810703d4400044e45c68089043c0d582141d11903c0003520303448a0012a00030f009140c0f00403e018a0140081960b12000840c040b01082c154202d840e45030301c81c82240d840703000b6031255142c06001801950030950061403290b5000812103269070500c0041070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 57777566 1250 57776316 57776347
    0x5040f020907050a17010812092d1f12020a110f0a05151003080f04091505031e03040302040504080c100b10030612200d2a050d17 57
    0x2280b03040030440004c0c0c0794a00b603070891080c101c6030004000504456160142c031946403041c1c502c4030f00001900140c44c802c02c1c1e5a220401100d11014140c0418840031800134299208402081d14031809181c2160008116408507014814449941c1c0400c200d80140d4054065007000d0b03100b20a001e0302c0c0d08080d070400300810489841c0f5a00724010131440e5440d0900c5801c2c18002100d00400d217000404114503241441d44030700480707901114081e0780e0710040d0059a0180121b0700030706205828030400000e09001d4114a00030307500e003101a2080419031034002e40f52410301c0c40c03102c0b00603001071200304003504d03050348100d030700502070316074685030074280055513050015001c6441542d0341d44903030b0890744e0300307140b0049030b2489401c0c18100f0002d070400e483d500d40380301c06100c010003e101d6004c01103000d030076211500c40300400c090b11000c0c4a0050b031400000d03a103c08074800c4000d18801c2c42d4580c403115210041c10031608040c008150b4100162038031051240769182c00c40c2080c00c01c0001001240ca0721 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 57778816 1250 57777566 57777571
    0x204060504110d050a05010f030b040501060f03030c020102250b0903070302040903120e21030601090503013612050a0203090a060806090906070f0309020109080304080d080117060103030305040f0209 87
    0x40c1c4020f035941240c403a41c00212440a052000403518290040c0068180c00c24880b06990300004554090356a07458014050310f40e42e0040d100301400c1050000800d90440d00c3c0c464410310036001c0e116081c08141420500c410000610140c031580d001c010000b0001e1200240380d01c44002d016100103545036000f080c00d0340c04114003200064170b60364982242040c1403140880790b5100b90058501d0329042003181e81c1c14040c1d650751446000c000004501a84e003c0c620075402400080c00070301184c1035440081944121540c09426011b9044122280401c041c50f00d10015990000d00020402d208200407107140d00302d2072040003584010404840c055403403000b0385009000319a5240b40d24500b40092044d9144080c010001c03c1e031100f800c0c4502a9000035016a42002c9481c00180c440a140012240c801e669070004035540000100804c01141c08a045420b0801d10b440d14451666120980c4503a000c00c441903400c607821850060001034840c1d0000c0e0307040f600520400000030095000940d00c10b0cc04d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 57780066 1250 57778816 57778841
    0x105070305101806091a030616080f07031506050307120501080706050a17010305060406061710050709050904060b010e01050a020c01030b0a0815070206070e010e0909011d0619110706090204060504 86
    0x34024a040c4907c0d081050903404400c000c0c04401d1407204240142c1100c00140170f041240742c00c1800030b1050381c130035031028107180c0c403030151011041d80e1107c01070030981c01980d01000103500601030700d80d004520301800b8100c981c2030000300b1442e03141036400c03101c0b9081200244204645416200003180844810724041c501401c081e07c070a040030328050f000c685043c2d01c502d1604015080800c0342020101e402c01d482142c107080840d4607075070140202c80406480e008980d1125840b41408207000d41a404801c80d401c0030303200c6c2070521500308010b5645d405403115120050b03200c44032036030b003a500c2074100840240c0082e011a01090b21366040b02d0410315003032040c55007940350034200014254100301040d00403900b0305007000b4007034500e000200143d81c0d15084600a101850114031001000d40c030194404143c507441c0c1d403581c144807490030380b81c178402d0790f580000c04a580c000c03a4100c50548900c60000038000a11840d2034802c0d6902d1020341a20901640e02035528900003036552564043c40126044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 57781316 1250 57780066 57780101
    0x221040504022b0615031a0405041e03020a02030c01141b030d060303020c1003060506070308061c050d08010510050a120e060c0913020a0819150b04050102010507030510180609 77
    0x2d0a040340505c03010450013070f003014200b403482089440144c0400d100d0b000c054501054590f15810110b0291542340d520490000880180340140356001c49c0c200d6000d4801c40c1a103141c02041e4004640304001038a81100c403800400c412000300e002542d10242100700c1c80203607410030203140310b041d08407022a441034002d038200c607826032400d20700040000c0b108170540c142000300c20b00b0034000c140380d8042c2c00c40041c140322124020442c0c035035510070040c0b2186400441e0b60300c00183c602c1c0003501ca0303a41e800d0203408a01e92000118240ca00011100c0a44069540706420900805801c5914078031040000d0b000030303500d10584039001c90901c0070600c905102154155500911424404030a101000e590200c038070504c5084001ea0b03025200c1da400008080804a540580800d4800103011402403085980008003000030ba11040901a100300c5000340c00030440c88d602d481007513060b03440031146030119079803a960030f001d1881141c40c00800142d2048001a90755101c01124003110001c00320000c00e2007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 57782566 1250 57781316 57781319
    0xc131404030c120305090c060a09030c0305011e18060515030604030e0f010509030601060e06040b120a0515010e060a021002030c030105040b010203070309030605060607050a03030c0221040504022b06 87
    0x30100030082c142c0b042e1131500300041d05d090000c00d6101c184d01106980b2a58001a0061401e4883e809500c09150000e500010315660b9103401402042000740b02481c00c1c0d14501210310000e0b4a12424a0344d1410400b10f5441130910355030b45c001048010480c4000702c611078020100c54030100101d5100e248251181488404000d041000300305010b905941000b001b08602e40b0306450118180341118180d0a02c042085654400191a405240c21420204401050504100e030909180d14040c1850b9641080076480b0010f06103451003528040f28045480441460740a0410360010a1445c40303905c150355a0224590305001603a0040da40c040040d1000b10040c402c6140c00c1c4a000c040b04c00c01d00045217000342c5541c02408480543c0301c081e100b2175860b000a840c58846000300c9542a03440019100d044c2c0f40c6240c0a0002c1860100110051280f000079200d844164800748000e0402a001e95091a250004100c044d5004129911101e860601c60251340320b071182c0c044410a07040d03140030460300d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 57783816 1250 57782566 57782573
    0x203061e0c030601030f1d0601171b030a050318040507080105030a110f041d0d020304030308011208070206030c070b2211040204030c150f050f040b090d0209130c050405090c131404030c 81
    0x84040c4c0102b00500c1020f044c440c0c0344c110001d07495612809003210702d009160f2010019090980c030503c0941280030000b102407001c40080190042c407041101c6c00c01660705d60900841d501e1509003c1c4a40651103201c002c800f080080104100d021070080c4240307244840c4c20040750a40340b00201c200c007154003445203403503004004e2081c520714558520065040510f551402055040103120b0b840621407408480007d201c0004100c0d1a41500070f002c0560fa070a00101c80b1195030f00100c400d54504890078007240500080b1110306110076480340c09103c8040c120344505180010a90b8400e910650801000000410301da10000040160708a09000c203d06010080c014042c800c1c81303030f42000f004105040050440070142c4041d113a13103240c1507864003585400b29030306030305098010754800000d5040028a654002500036503038071813490400f91507a10f0303003800161402511500e82542206103007c5d0a800c191980100d055604103010885040820884002860a540582c0020342a400d0345045c07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 57785066 1250 57783816 57783823
    0x90209090109020a0804030809120403080405120a03020303010504150801050c0415020a03020604030c050a060e0c100e0904060e070b0406051b0606030706050a02070902040b070203061e0c030601030f1d 88
    0x4002c00c407015840c1c041e4465000340692402400241400502c002184003035104005070101140d28146456490b43ca908108286400610503103100d042000c208200d400c50108001c8000c1c0d905030029400c690a040400010b4880a2107400c0d010034003102c0000c54010034011139014030b000790201c5588074100200410030300c0201522506543c03121203500d0000b50b000602c02e6106070140313480d5108050500e03090f81000c417986000b600f090f06044821302440c0c80440d80c000b200400321061101c3d2040040281d58140310450000d5003d02440002000f05405421140040b100340007550042920b50010030f00c0c03130300300781c20032000920003003084018550950035510200d000400203005a18160b40000d9a8800d207004e02400c1000228400c09214020400e8001034010000190b440c1c81d120340c0004034607003207141c00341d20910a000120704408940500410944221090454143e444002c1c015096002404460400d950f81c0c141c1144140030741310340410100b41e26500d401840708100000c0c40c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 57786316 1250 57785066 57785069
    0xa0f02280e010804050712020409020405040303050906090a051209030703020a030c090605060c0307110105090a0e04060609020a09090b010c020d0b0a0501060203030106050d0504050f161a0a0f03050a0906060902090901 95
    0x5103c1c01d4810302010880010309401111460428110040034130f10104015050140000b50003a0510041c0300426400d900524070400510007100e4007590f0701983e41e0740d01c017076014000c1c003503030401c000c83c0d40307007084c07000040958981c06002c88000659a5011030243c1c002071380150384c4045180c90a100030328031800b03a00000c00007105c0b85400d00c41140d15040d201c0c801e104004102009914903031050764040d900303407008004001c22020902d5911040d02c111a070007114110307111031821102144e0001d45109171841130f4200e507950a500c07410f0500c0b0900900c03107040e03120705120910580d90f0040ea180300445084a101e01d019449905004c40103800741c41d0181c0005040d5001440180480c2e035000003a2010340e18803802c0400e40f9103450a00605240f00d00510f000d80b0700403810988c081407a1080c1d60401c441c81c1100d40b107402100c41185030f1003805200200710001d480e8040048a0501c00d41200303821401d40c900007e850640d65031158115261a401500744d250045151520382ca001a001c60 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 57787566 1250 57786316 57786319
    0xc06100e01150504050f0a0f090f050c030106080106050304060603080a030f1a0f04020f0708030a05060a090501140904140a0c05011b0b0c03190e03030a05060d0302060a0f02280e 78
    0xe40c050282c520240150186020b40f50203241a000380d2030b1542d64060b924001811621040d107201510f8400c090003506000180d540c901d81000081882e811044c400c50b4101d401c43c3d40c91200c940d090070b0b41152158000f81c010340326240c44010100c04100308500414000341c0c40d1710000b03241aa5450b9243c2960441700c00740a000504480728040741d00c50306120b01903160200c50040c0d80d64071244c07540d4424080c466015000c8280401000880703805036120743d005802c02ca8141700599911400541590002d010303420100d0046050700c54581030690020390098410101021100c2c02000c1c2c40d0329203021014203a0b00310301c40150400481d600310900d10784032119800d4118070320f00d140c1c54034800c685001d80707031040c841d4001002824003110b82180c5441615119003d00500b228012410364a8005803110b584562400c00804c10615140184203585071749a0042c0c00ea40c2d5403032030000010410002403203003503502088241820017042d100500c042401481c2caa1025224110081c042000440c0e410f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 57788816 1250 57787566 57787589
    0xa0b0307080c09040f090f030806060406050901080a1b02060601030c050f070816020d030c050132060312161407120809030304030c030b070f0315050906060c06100e01 73
    0x8188036074440c00755039001c0c01c0480350303d80c0c0e1100780004c50014104c501410403045e10740741410040281d1032006194a9000303a503584180d0b1606e03820040980319a01c1303604049881088407101550040010550004200100184070b01c1c0700c201c8036411100600700d80c4e005030030040c100310007036030907108001c1c18a0740ca161450030030703642d540a88000c0c403964001030040720000c9425045801c2e45600f804080e9800b401c10b41080c0f2880c0ba01a11499818504903215402d0441c91700100302d5503001800e52040150556254807010b0310001d82d410406880303150180642001d04000c800e00200818000c0141000d109401409082461444011144045881d0080b52081001c0c40361840d801a483e500031080035070300c030350720350005c1d15521850740001d00b4241401400010310408404503482502c0c60345444940903100d003011000c481e61010b403400c11065803a07051082c2c2c24116901075000c180a480c11385000d040e2042035184c07a00c06c03207071300340c0e9840e5901e800d021100c000134009005140d15206c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 57790066 1250 57788816 57788821
    0xe041a09010e070605071b080d03060816030f1719022a06031503120d0c0f0912060e0307060b011b0512090303090d03110d090302060702040504050f1b0a0b03 69
    0xa10340f1801c25108507000c00901017a10310600c000002002d8a9003021000707070320741d00c1d0b8503c3e8280c0c03200280203080c4046403600100007504003002c105103c8800304203520b450710074110364940080d084c81c04815100d407070000190380c0c98a0458401480c01c00c120402e2064041c0000c10000d203421307201f9112604201c15100700750780d80c0703002ca988009030400c100c1c1c85644a64070204070000040100c3c6001e036041c80366400c4409111003c41c000d000380f0780356010030301160100800598050300007410303102c0001c00c2d52000f04020000d41c4070000c4098805c80700411f80c5c9812003600e5140d50480c00040e1480d40d0349520102456800075000401c0d8556900328036841482d0303458098542003003040e21142000000ba020f80ca60f40c0c240b0840d0b0003404002d010038030440e90390030b0040981e4010140c28881d40704800c070440d1310034014506a81101c0d40104004d280642c02e900307110240c040074004031803e21588024001210080c0400542a4503000380084840380e800100807440c0e10395880700c001000b0800c103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 57791316 1250 57790066 57790091
    0x8061212120408120106261303110304030203070b0301080d020f03090105030a0e06040f0c090204180f0207080708070203070b1213050f01090c0e01050a061e090e041a0901 75
    0x1640e00711010005980000c1d925400c000c01144603180803613446070100c000109015030800d28011044109652541b00a54058500d403034010083d5861803c04c114a1003d5000a21580d50200304080d004141d0f8100380d96540131a1803c50103800070880d0240110040c40700c003400f0000308010b25441e20007490b4190281822548034451240a68100b04000001a50400840d0002085220384004035000ca15290a00300414640064212500c600041c000518a0004c0c000e49003604c0c1450800b0009018034000c030002031242e15141490300d0b4092000e003000c17900c0880030b005843c0c001c200342c51b13440900b032040604003100c503080301842110a200e45005a0b11000c0792030340c07028031200240c148004d1814140d142041140a5010b00d40c03d0802d81000c010304d42241c40126810920204031990329481001801c004601642000411009483c40c9442c1d40503841626440f403420007680054030713072812408408088030261104000301c00801028000f45001da0780c0130300180020400c3c1008900d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 57792566 1250 57791316 57791353
    0xc011d0c090103081e0f182d0103020d0e06130501060e0f01090e070b0a052203080a050f090a090c08060a03080f0c010b0604030308060307091b2607080612 68
    0x8802c44400305c50000c1412142c020801214080b00141020740c3d211608203905c2d0300200034038591705026128100080e0502889040f405041040c0500f4810380007c0c0207004500940003844450550380d100e000c1100d11003824805640140d161406100e070f0310216003005400c0d1400369228920344a9100100100c40e94003078903840c19900e2100340480c1000c8400001458114907800480210b100000c400f0900b80c0c00200618000482040c8620b00e03c080a5440202020f24440689040410001309119501ca00002c0183e82c0c0c400c1240c2c1d0a02d10908040b03401e007009900900c0c1c86036034402c40e841c0c805401c039051542c010012908030032642d0440c1e540704210301620059411081c000b041d501801c010a4120a8002c90f01401550711265282401000048192101806405401c1c0040341d4041907014003801e10b000c114000c0220740c000c8008660000d4201c00c40e09170300c28031190f0400c6200c0400c06c558003546481d510764116081c00010800700040811002446034002d1203403050217050764 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 57793816 1250 57792566 57792577
    0x40608040204020903031e03010f05040509060a090314030c03010e0903090f0f030309060c0106031103160e06060c010c0201140a060501230c0a050105040b070f1b080c011d0c09010308 80
    0x42c2e074050f840d03510160101b841c50240e0480c41c81003101020704030030b011010344080c0d030413070300305c3c028031040c003540e800034081159001d0382c01c40300c41d0300a440040c2411429800828401e440381c9400d41c500080204206100c0e0015105404140000001000708001811445400c85809409540b40c020004000360b000c021140206001d000071001215050f5420b0064404a04001d4005555016040c0040e40245484d0004540c91640d5440c4040c541c1800101c2051b00f102e8440c0034030788941440181d0300d40320313002803615610002c00c02c104248040c0a02586d21061029000414801c1c00e020713207140b02a000a0520041da46845403c000c3d070380c1d02c2012440f840441072510320503d01008982e1505110384081d0801c68818406c980080007030540c005072080780500c1402a1a480b0300700d04607602124007a0b090001a5906e0308503281000b0705415000080c45414018a1308140c007440600b580e51404492100f0202034842381c030540018085c03885a11011101810950f045555054050240 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 57795066 1250 57793816 57793819
    0x115020606010f030608010903030618050c04120213090f110108280204030602040314010f0506060f03090f0f1b06030f160309020406030605042102030301151206030f0311030406080402 81
    0x2000080300c3c41030702903800700002c4c01010000384a8503c550501401034800c2e8481d586444070081d1080e4140c614611405000300000009180b400c0e103881884450b40030003c0c1c00380c1c0d002d10300d808241e040106038030030041c20a21405860706401c04a050411700c10800d0400300d414000b503041004900e141440510b0800c0500601c4080c0c518842150b50009006940009104500c0042c0c04001c0c000c88a00300245502288001c0c042c103921000c0d403500780e600070b5810f141c01800074018109446284406198030100360380440e2084121401c1e41ca29241c51740f407035416190440050315860b04041365005040400035101d080c998100307a1880044480000c2031444a15442e00304c00085034400c0c1c00800750190003c0060002035181d08109004250580741101d0032016110300c080010300303240700c1c52001000b9402079801e43e0710b0080042c800c0c14007501e071a02004000c0c80c0041070303020070f481020080e50150984510410741880c0c05068a80c0c0b41459519a80c000c3c04104252684905101d0740b1550 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 57796316 1250 57795066 57795077
    0xa0c060b012a0c0510051905040b07080f091f0207050d020d0605040221010c03050a0c0801050f0a050406090504050111040f03020f01120c0806150403050a0803060607080301060512011502060601 85
    0x80ca070030540f18401e8030350000b581c018117040e00c503081030b82d100c0c020303010681c1c41504036201c030b0071385190503a240e100314418040d80311414000800030840f044082c00c0b1754060180b5061820380c00400003980b040d65203011381e600c4070644004070882541008680c0c0074000a5402c65035031002c2d500002c07580715070070100034511500c1e00001400c41d140c0c0b030303803540d1035200707412030000c00e000703500308060103800d0003100100024a46000280780083c80d01442d01d8040450302c42495603428081813143e0300d91b6942001c1d4002c1c5401c0d200244c9621580308010083c040d2240001309070a05207011800c0d107060000c0c0d994961411b02081c001f154034154240304880d8100c03148a5007529080c0141d44140352015002903203407400c1c206905417a00b00468520603442210b040b81026041c0034048114065800060a1a0710450728000040d400c10001d60700548024042030030051203a80d00141c961098003e10005100480d00321010001100d905026200c07620101c0454050b00900035030f29207004021904108 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 57797566 1250 57796316 57796397
    0xb010e040c050408030c0d0f0801050d0b100503070306021231110a1203080108010515040e070e04050a0b060f060702040902130e030702030f03040f1203020c060a0c060b01 75
    0xb801101181c00600d841015a91103500c8000c03000e8071099101d40d800081840d410300b80004520649009040c0c901c02003406a01c07000a4440c010050070050607102406442400403916030b9003000503000441c480e035070160f030741c04048000300030039100544046450b100d403020500e00c5800c0514403203000d06022040098450b036508100302c00201e841e0020750070072000760001c80c0080c695540d01c041540a61150f030882e903030700c50b2400d080380c004452140f094188541013440d00d18040c0c0045040c1e49103c130849174002c0d228020010084015901118154018003041c004c01c01c1d0b9588003035001034102c4031058401d00c0c09010400d0b5104102009102d42d9076001940e0071540d07030708258046103002d00410411400301c0c0b5906617981e405000268420b01c504d600c040750701d003000801c40301030701c003803074260a00c1a243c00310004403039990308822400e6014901e0381116a071180c2c0041e00c0800902e0383c882000e58214146002107600001d0800d04203c42810304010625100c403a511030a0056040d8a0214 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 57798816 1250 57797566 57797591
    0x4030201120902040f09060c0f0e0f01020304090203010e0712110702040902040905010609020d11030103210207031a0a0c0305040c03032001020f030702060906010305060103060c031404030f0f030b010e04 89
    0x2c160310070b80254090700d484c8544419407120b40c0a506002c0c1f2800c02048a0109484165410030f003501040001540e605c180720420708112001070300c0c81c041070040300d09140d21740a03480b050760026000b0190800c070400820124552000560407048c680b00030421040f04800c041d01c40c076216208000c1d004641b9601420215191507100301d001641081c02000025280c103410f5000c1d50081480d03000c0d1504081c0c09400d0018400100c034120b030352003017580b8005004040602482c0c1007000340202503015804001000c40c3d40f148520345014211341c07520f4100e15140081e10308548030940b0003c2010b00e84020080003400c140a05004d40f90513090240b8140740c6410030031070328101610381940135400840c00800f42c0078104c000d940100801c6d000da412540d2452010b9544510911015140380c0c89400100f001c15050f44c0005044442e0b0700d0046481c600490070301300e04400943c2c0881c0002c100d5150070603841d80c044844050484140b606008415445000a01840003c0030041c411a641c42a240c2c60 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 57800066 1250 57798816 57798821
    0xf070c020303120901061403030306040c0c081306090b03090c0d05100606030203060406080d090b0c01090f1103210a11070909030c0b0609010b0f0c0a240b0909030403020112 76
    0x180d40141102d503152200400001580070a45200580d0360810030041204480840b06898000c1c01030002c40c00c0d50340f003004000240c00660306560038004001d6018002c01d2030f50000341072f01300010078070140061030990b0080c0221550392204804003030510921031034000200e10b003c0010000c07180c00b0303c2124981400c46c10850805003000c061407620400107000c5806801452203030f90101d80402c592540c41600e66115141d200344440042c0000ca4203202c03044020000d07062000c041000040c481d0103d46e200d11f2134a00328031083e29891021500307603002c0c1c03504106030b41c9126801c04051050189003a511140d5000b4030400100340410369480440f045020044040285245541440f01c01d0181c1400303024840b5001c000c1c3d03000351407140042d0b403c0c00c25090f15412604041d04040c50290380303800e0050749811902c44401503005141014000c03403140c041445104540031010090710200c07680e12000c44001e00143e6004109540400c403c0030760110507201100d80a0800c0c48814030641d00705c400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 57801316 1250 57800066 57800087
    0x9050417030a06061808031905070209070c02040e15061017010f030210050301050306040f1109071d03070e06090702030c030c0109030f05031009020c07030206030408090108010b0c060f07 82
    0xc03100200400200000c140c001c0e104594854850541e4540c00141d80342214a15015648540c4d008112030240c144c55400c10350090a81e620f001410406654001080502c1c15124140007410202c0400254501440354502d8044c494000388100d8001c4008480140070003082c4034070544000344202005400351040c070304905008400520345603190005e80b130a0401a0005078040c0941044102403680a00d0869041e03a0340103004081c15070b41c43d034607050450f0303410b030007210380b551010240e40c10f949901301024018919074584000d03281c1d40c005a541c606810800d50f5100307502940c4100140000f6002c020b81052044d07840c5ca003aa079800da0141d15601c128260f02c0b1992000007900d040400f0194828002d03203220707546074500d00b0300b0301d40210b0b40ca000540d51075200000e02003040150401039401486446140402d94803031650300e0300040d000d6001100e081c0c503100400101c468556030f018401e0750162141b400b031a41003041e0403000541c0d40c2c81c024158500061564042071009008042014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 57802566 1250 57801316 57801353
    0x80f06012006041419240615030f05090a03090306050711060c0301081005010806070c210507050c0d03080c0703091203050d1b172a31090504 62
    0x640350708040c5130034984401d0030704403140c580c007400058420b036640030303103c079045190000300b48482d000000c012401c01c1050015090016652441c0c0003e803050130b0950369003121456200041e8143c9042c9203003060f0399008180503a243c1081c4141400203401003c10350949401c0b2400050765921450241e6400c0c103450741e291481d00c00d034401c10848001040040d41603034803480c1601e00100e80102882c1c2502c4082c021803c5c02e030082000202d201d403007520341e0441d09019071980c103e01030030700b51710040c480c170215504070010f1000a0546d042c010700708140030f500202603580c94a026a6918020001800648802200d080000f090070a1501c1500140058244060901d40b010f006282c0036000307501c40000b250200b030034591130a241e0603d031400c0640007100d503110081d20903440340c0f69001e10400103003c05074820340d40e41034005078034505465441a82e20181403503134440c1d40020221a880004440003928100303400f1810040102c01000e004036880c048000c16942c55034a020076554440903501e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 57803816 1250 57802566 57802573
    0x2030108031b010212070e2101091406090a02011d090a0902030606030105060f010302070302100912020f030403030c020f03010e0d02010f0b0a1a0c10090507050103050601080f060120 80
    0x200d1500310120050441c08888800e05038a011695401800e0707008400c3c10404c0c0c50400c0f400551070302c4c00340d00d1119801000803c200104012280480c0d000d034000f0451246980d91031b84210104561007143c0740e248d074480b60050810380b030180f04c1305503504031521000b4100500c1800c0206806981004554140c0000f0f013101d980b072400c265014004c0110700360a912038450134010614904062140900400028210720240916070006502940c894030049003184100850301c03209005600c5940a01c0c0e20581010f0b00e00c00c44e01100070320740428042e01c13a8103a00104000c200090b08940c0075100e2981c1585c800c03040c207403036900003801800405040d005030b02903110f640c184180c0c1075005c080506800002009401c25286c1400403068203401005192404026800c03250000480034009001c5180c2c2140c0c00250030740d0303120b41580e440560031a516070105006114642c1c260003001c0d0f008500380303051b140c2440c00d0301c009174401001411b090305001c1c0303444155000b1814046038034031541c0b0107001c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 57805066 1250 57803816 57803819
    0x1090807091401090504020a0306020f09091003020102120f04121505040311100c0e120f07030507030c1512090606050a1205011a0d1b1a270607031d04020301 69
    0x209000d081e02c0402d2816440c80b06001084040d4140f2840b80910703000346c4800055400e40d40d51800070340c0302c3c40c2c81e1140350720140300458841d80c46024a07482001c8100349071210600e0742c80003a1400c101d80300790b0510a50f06200b200780781e0424800b030340e0442c0d02608600102d5001d50812114055142d00e40702c2c7c016040408001c2030607049201602d200c00307031504540c28406040c0c0d400702103641070160500060b044500c80d04442ca0204000601400702d50306407101d100306c00030301d949012280c0e88212090740040300b04100b8400c0d4009480000c0c40080710061241000c0b020080090804980c032808032541c1c0c1c040c900070701180c0d5020101400010380050101d6449000d0046680a0010121082d6082040710b18201100d410310480da288080c2c5011039038001a03460982c2e542050525501c4000448030000f400310150088404e00345262003000d540c2c42c01d03103411400324450701e0801040f8400030000c0780d28a440d102d040303e45003034240c94440060360030580004180f4031401c450a82c401d001200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 57806316 1250 57805066 57805079
    0x2a0c0806100605040f060c11091608070c02010c030c05070506160203010b03010603020a18020d05040303141b0d0209040612030921021507020d050109060506031e030a0e01090807 78
    0x11068001e0610146965800c1c1c0d88500468403803140d0b000d45c005031185684201300c5c260292120740d030050711407802c050000d200381020a548460403031f99441c086061200e0280c1694000e900c094100c01d80d454a1012a569500082c00500c0f00480090800020507401d0051000501c090405400020025565004240000a01c0b52000c00f001c2e4440d501e00116894140703414800d14048030340c041d12584885183c0345101c0b41040c84800c000e200c068003000741c0f902e1000c0510030184030341c0c46038900041e0881c1248404a050030010401d810210040e941c0c2406880c4001c1507030703504060303441c0250395224504007003405071005500103402d00d0803140d080010160000564402c0d40c0121441900b04910300c1e0460444443c45480a50003000f4181820214002c1d0700041203a6030020b4407001c252007080c0e60b66401c41d1020041038130747c0e0345c0d2403050215a150a0105100241c000d1400c0300c002024190440d0312813050403024802e0118441309200319034003071581c401c001c001030749c103561016940d03a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 57807566 1250 57806316 57806323
    0x90204140118020c120f070602030a14070e0d0b060d080c01060311030610090b040b0616050c06091c0302070b0c01020309060618060d15020c0304051903032a0c08 71
    0x8500b4004010380401d070400c2d01910a0303410050b83e035802071031110100e40151105a004900100340144204242c0700840c0003400158047e0803002800121141424600204504042c1000701040b80d10483e040155407035140c045c5140760494821041510b61500103000d40a0801c3c0041400001080303201103039606500c02c0c0200c9000301c803c0d444144c1d017601016152802210000c21074412070f00144402c4105901c20315040740081e06c0010481c107850000f45040c4c029410251160f440c003c0407100b004810300c00c654041c001510060706010f04400002d00c4444040d951203811100ca50b4140c050601c20060040203151865074142d03034610300d01d80c65000c1d600c100c0d04401d4501ca82000300f0203a0410b0001019425100d090440c008d0f2140c40402424007010b960a5813180e9440e07400c0c0b5100f90b042d10090a5a00010380150358481c54403042c08449501d0403e105051003074004104040394001c5030b801c1c0c0d60b2820304042103820144d00607903510340c2821540034044000940e000708203800d000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 57808816 1250 57807566 57807569
    0xa03023d211107150b04061e0b16020f150708040306060602030f032202210106090207080304140f01150314070b09010c0501020d0c090303120606080f06040902041401 73
    0x100542080c440d03140e15401d0944110301c2d200c4808030420420f44011903840d008030301c50700d000b001e804100611550005025103213990010031032003000803034150300303801490782110040c4602070000d03080c029031030928810420440c0c006401514002c4c041d45156860703c202c51000041c40c011903864102030b091401d0150041d010803545589082d00104503540000159030030070210310b018502d960394003c4100400c2c481c0110200ca0b100010b01c40c00016a1828062a4001ca03454401c0c20781c030300d6140c00c90f03080d9903241d40626101c40c4100311340d0000c134401c042100d40c81500404203802030003108802c103142400275080300c0c2480d440d160780703080ca0005491101d003c50380240c8500074451090080305480d801d140c402c030150b03060100031010582d4000e00206041601540006042040c2c040110702078400003100100044c104580c14030401d904072003081d208460a640c104a001d0611a0250080d0030180444008642c10400941140d42e181c00a030b100340e40c068000d1140b540c0f101c8414002001c05e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 57810066 1250 57808816 57808847
    0x30305040b01120b0a1d0a06022104080a0f050409090f02010806010305070801030605060a0509010e0906160503010915170127020102120a03061d040507050a03023d 72
    0x24040002600940f144401080903004044411140c80e0300d01814010311010403a018a8000c610500c12007050a20451041d207005240240c0d580c10f14202c0c072921209030898510750803160001b4480801c0c100b800361011040700f0704050160020020007a10103003d02d900074128941024001e404103c14407540b103150500c01c0c1ca500c841512900c0054040e960203c90401c0050003002c01000414219005903400c8980070301005071464883d800f01300841002d03040650040280c0d001d0060000c0c041110640c410300040c1c0206014489800c000c02501c01031203610300c92900e0300c40665000c101c441240b0001c21900700081d90600c80824441d002e000142c00c03406d60110340407c120013900e607000e0044011035050b07002c3c0004194860b108a00c581144050400305540d55101055880c0d00030340c010000f05900c0b07900111441d25141c850324140240d00200d004d540c011004200685400084103030345212124520791282100700752001e010b004403801452101c500710301200702074000c1c00038807907140d5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 57811316 1250 57810066 57810083
    0x110313030e041116060204080d1e090509040303050606090406031b05300a050f0a0c05010507080a050903010905011b0e030d0917070504090809091e0c070312060303030504 75
    0x100410042101d4054268043c0104204015440e41185a404422441c8610001414071380c840c020b0b42d2070180b18407504001305124180814600d841d08112004100242c6400810b05051502050305c60401034070045c203054803100416050307a03ca0058030f41001c030190082180c103959043c240380103050300b2031020095407030240c085614182402010207190b0303194160003402c040c40010200c0d01c01503130f01c0b0f05400e000b0085201b0018100340000100c090a106c020442814541032400d00303940b40d0340c001d50504c90108440f000007a16401030340c45116460a000340c407500720b64080780c094984007030020f00039417820600300303442030f902400d141c1200d50b0782d5140400018902c0c2415500c68004189502107090b046080080c02c5225001c94845421201603900c000d6a600100e0207403418014210f50741c040106521009040400c0031a60003495440c030428402c1c840550041041c00140541c40858030000304582418028440d003004c4410030300e41000311507600e080c0140104402e03141240d0b41003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 57812566 1250 57811316 57811337
    0x4030615030c050d020102010209040608010c1b02010813050a0f080a11030903071202060708120105040c0c0b0c0307020102041a0901030b060a0e060d060503010e010506040e0109050c060d11031303 86
    0x680c285908003038a41c040480c2c56201e081104011028680c140c08074110340d020005052542c42c1c0e07004210043c0003000c00443c0400419074050b0071820b24000d010f410030700a180380300160f81e01c2815190040040250b5440555043c2450fa0801030030300c0c03010304154821000401085068401000350b02190703610f52011148010060380c0f203100d4013106a5142d0b11094044c001380c20b0034410841c3c0030344002c05003440c01c2030075aa40c100c6500210840070107a813580f80100103904160040030105134562034000d840c4611a40d40036403086014045402c5400b01100180e2958000d604407409031942c00c25030120aa01c20b040c2c1541a0300ca0b50f803e82c0000e007442e0442015040580507111075070f1158546089907840c003400e00009410011213641c410740c07550030000e15500c080c40b1707551098112500100c2c252524400340b00980b211812803102581c90301030000c0209201284910b036079817040358000da03510300489042d80030380480d00c1d0306100500f00205200315141c041901d230016500c40c0d165400c044 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 57813816 1250 57812566 57812591
    0xd0504291b07020a14120d02010e10020304080307030504020114040305010e1213060f0509122a010f03050a0f06120302010c09050f010e04060b180f09061c06060308030c040306 77
    0xb03004103500207400a02e40c603802e00166007403208450f810b40003d801b41404910402009142c20300d44001900541d5503086007000c0c04000b0301030420101d83c4030701c0039491414203135140001440001e00550401d81c2e61130124003160722a58000c000800c00c0420389442d1510303401c04500810000c0794000180c41504c400426845559050b100f2034000c00940242e01807400d5420f8400b140d0450b10881082006c006004450351171081407244107851400800300002d0040103107007168100c1c2c5c17506501018520590203a6a405170385004082c2c1580340100301a00d03180110b00c040c0c6582454042c9080c1420b5000c0781d01ca5450701010325184c0030342d00a0010018921040e56078240d14045c194004103a44031040d4203501800714010803140150001440640d0703600c01a0f901e80113480c01c60001100184111440c3c60403d414002c2031204035042c200d54240040050b52030513120f90b030300c8001030100030350200f03005541c0d2003d001036410a07507241d5a440e01c184c00746682e51040c00100c44c164913001c064145c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 57815066 1250 57813816 57813871
    0x20a0305090d08180307083108030414011106040809090c07120f0507060c050408010e060108030d0504020607150b0405070314010b030c09030703080405030601080607050d050429 78
    0x11a06a441c3e5021030303216801100c02c0307101550101d0b07100b80f00402072800021042c8004000b00721124103070150030081920a12049845655481c40000c400c50084c442503501008980480d0304031041026149030000058070042c24006210055029110800044c0001c2d6801058010070850f000011030340d8010702014103004000018140d07085003d003003100b0314000c1c400000d4045032810032a00b0300b040c0d940c0303400a407012524910000740c00821308020041702402402003000b03200c40a0015503040c039651503502d02405500041c4240c407080464195154201107565040e005070f44000a04110043c40028151009a83d0b0046282100082002c0c1c8244100d000c04084d2142012940c1d280040500d01c40e0400f4000c1c000c8202c040110907001d5a04100304402140305d04da1386500e0b03601c0c11007014100541603220008a0b00010100500307564050304a03001d00311030441c0098183c640e4149454480c00441e2805181408c0c4110012390909e00c8039858440c2c0e1100d56015112001291030030320 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 57816316 1250 57815066 57815083
    0x606090f1003021005070f050a0c050402070503120604060803040e06011e0203090904020a0504060608060306010e090a120306030b01090b03100b060906031b19030e031903090c0b0409020a030509 85
    0x21100088400b8401403a00300d43c0d8030350802e801d24240c0c0c1021050748458000c100564404c0f280303548442180070401a03000412002804101c8003141402c80b15101d864491054001070918401820001840351303a40354050006402268100c0380c5450302c8007064222010f00f554040d010031106235400d241c0194070803c0d003031030124031340c05142490346590600c000c1e440080d000b00c1e4855818440400c1039184c91084070018103196a5041c50380c02e20303006141c14000183c000740e01c141d0a000800c130500c034002406002d905d5002c8084a020141075004078000e004c240c100802048040000044031b500e0745c1c10852142500b00c0640309d800782001207207000c45086065103500b014043c00510703228030300140a55440407000070704801c043d9142451a0b05903010000303000a201c0074107040c414041e07051260051140a40e0025850244009070250700704031a890013204058031885100c082282e07860b800d0b0000c2228051240d191901e03030a9000c042e4108022520002c0e00c1c103400544001e000203050789 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 57817566 1250 57816316 57816331
    0x3010c0e0904020f03030307020106050108090d021e0111131e031509020604080106030b040c08060c1204050c040603030914090c0f16140129030706030f0e07080606090f 74
    0x96a0311560500600e010000d00c242c0c0d2202950707905a0381a1018001075102d280954000182103083c080090305102000d00710500c07a41c42100310010490700050703118000500305890170041c06400031118054003c030058415061008900343c00c4101d0302c01d503904d050b101c85040c100e0845070484100031030500c9901c4064030351102e00d10040910071440e403003000d06a0001c1e0003586842c1e1030b9440b0a0a44186030300031510b0040342c00400c0306201a40d044407011f0300c0010040c18a6061200c03400310b8501982502a42020f800380c040780420004005018250380c024109200160756810040c01e40049846503400c11440c40c590700e0050b03d4070490301849050058a420305041c08d5a00c08000c0350170105403401c03000c051001c4100482c1e480d91089054031040740000c07600240ca0384100e521912420318101105482100d074443e44c1e9008a4041c080d41c940b454002990402d00400b07601030645030801100c580520407010549080200d41301c2e105050035144454240c462003001d01000c20100c6020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 57818816 1250 57817566 57817577
    0x10206090c01030c110303190b061e0f04031a04030201051005010c150204122d05190c0b041d010b030c0d0507200d03060b09060409150b0319050603010c 67
    0x40c2070035806680b142880c2e0a49142400707580641520513071031984150303075680114090540c4004120400d016404203a03105860543c209809102c01c44908c0301a082c5c2d0b015003520108110180022203010781e4021a00540100c44a4680d403003000b054000c1658143d0065091100040310750800010344400c407034042c1c0d00c2c50050401d40e11401c0160184000000c2500d808200004440c002e0583d4086110b025406c13076a03140c149216038909580410728215107804106043c2004120041141c1d010401c030400400c80c1b9014520307000a800c422500030080d880d40114020a824018002c2c00300364100d82540c0c4d01040c0d88a428180903070004948c8500d4084041003c406046a2900700d82d0f085031150074182d2445003031404007074a8192140310f0303581a901c450300c0c0030350090385405410000d21320303685558a080c441602048841c812405505111610b595148005004217000c440042800c238445c691642800900d980201c1d07003050711070381c0f024144004200285410f10032030403a480641c0302c0303 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 57820066 1250 57818816 57818833
    0x201050a1a011103130806071107030209060603041502030108030d151a071103011a100801061e0c02060d050601021c0207091107021807031503050c060c100c1d01020609 74
    0x454421000d801e40204900080c021520f240c101000045c1c0030740354400c050a400e10709640c0041c80090030480e2422642e01a5004102503100c40340c0f03994001e003045d1911503a0745d640d820140c0542c94403010500321248000000182e2180c0400a0030402c00e22890a0212150110449a20b24141d020306c3d02d807491a010074800c122010f4000740b01c10b45c810300f9148000680407000900711032035074441c01101c0d440f082e204401850038148211044c1c015040c140030550410320010300410301c0c0c0c00c0415010750741540e50200e072402171198001c0c540e030041c072850f6581a20741082014220603100140980b050301c0301d0351a5980d49401c01940910198010800a49007002801c050701d1807060900c0500010400c100142e20f81c90101c6803038948031600040d850402074001400c40342e00340c0507241418400b90301840014400b0035801c00c0301070304480301c0c1d85070343c5000ca0003070030061070781d95800101d807820083c000c860390081d006681e140d40312014250b4543d60f0000680c0c444804540c1d124203074003c1e491 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 57821316 1250 57820066 57820069
    0x31506091116020109080703080301050109060302181011120d15031509030e0607030f0809030901050405041109190807060f020312040809040608010b12010b10080c07020904120201050a1a 82
    0x2c405110310300502d00f110200b1703a14040c0d5418448590020b07100311400100511246d60002c0080c0010450f83c68110b00e85003c42c0d40d00c400240381d000903544280b40b041e41c0d10065174412203a86007440b882005580c80096459240031090780b0482e02500c241d03007401c00e000c10690a501403041200e81260300c2c54050b03645690124010191520120203115500d9083c4115031105c00203004001c3c482d407038011810203410805854507030b0051010083d40e004002c206c00c2640c2c0700003510100d81d010f075800300750100380c00d210340c0e514040c000c1c402d43c124844c0b0f035020b03400400242e0100200c07075811054811054660200701d640080c15402c4e00e0140e032080018242200c207a21035036a010f40686040750515604400060940b4025072001c0150781d1600340303e1102e458180e0110034040002802040215018000b01d40c2c09000c00d04a80e0034007a280c00028500310441c000c0703894092b1300601c403054915162030018111070350307004804015885e244c001504007045114418940806540681c0c10088480 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 57822566 1250 57821316 57821347
    0xf0e0106050f040c2001020d020301030506040203010f05090a06020711030319030c17011502070302030607030c02010501141807020c0d08070b0a09020f0d14010504051507170106030f02130315060911 87
    0x502170041d96508110020b600126480a54065032054000d424142401d0041500750b8404140441e1000c1c9000103202084030b000032543c84140d88248096118010381c00c04502800c8580e64480c3c050000040d141440b00c2c0c4205000f802403001e42302080441c410384030072100710205034443c043e0600104014460319108103610880c444491040341d02072074607a80800c0c102102505c1d80c0c80481e4448400043d455028041d20b0302502c10000e034403281c4c506000000d007104420103188542d40c8225000300b030703881c0c0c070920400c10b43c401c0203882022014141e15045981d64000c0106407550442a0040b400041d0395000d100030880c3c004041c0040114503038208954501d00900803114880301400c600004c680a0107898413071802030024219220315140840c490100042589040024001d50004461091112141540c0701751a0008070611020b9140000f031003012050f0000c10100540007007004000d02c0950200f030304128081c018140c0d507205040a50b0740701440e408c1a11001d010a0103400d4054 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 57823816 1250 57822566 57822617
    0x20c010c02131a100c05030702060c0f06010308040e01140f09090c090901141b0a0e0a030f052104030b160903020904050d030b100e130f0e0106050f040c 67
    0x10080c000e41c2d5404103800c41260040640030f1188005000c0004451600358500500d40703895041105400400307a43d1591a4031852400038840c800201e091108207800f0840c00304084034840c1100c005503183e003000e0310307950401c0c49000c1c204100f02c8008105c1d10030591401d1180100607021803484072001040010301c050091046802d44900c0c420800650b0702e0024407070098a41d00000a5009000c546110f08900c00410705c046920f41510003812460301d00301140c0d201a65850412030b07012102002403183d01c1c05600251082c11103c5044081c04804112403440e81c214400c1300c542801c003000d8030041c6001c1c0b884003070245088040029010005410010506200e915103950200d44a90014011890039103042e0f546601440150440980612131440c00940444401d48401c1626100a107120b03c02c2c5400390040c80d0104910384158025040f801c418070030304e43c0601810100b4030006009003098421035101d81081c412024540c1014811111820300075504c040443d20494402c031000982d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 57825066 1250 57823816 57823819
    0x1d1609061d150a140306150603011205010902041103090715020a0b06030102040510050a020c0a0e04030c030309060c020c18070f0f020f03070803010e100b0d15030606080a0209070f020c010c02 84
    0xe52210a00303e64414030018060002030506082500245060602d020710041c10183c0d5903c20064100c1280d8404050720304482c130361001010803600c145400360262182c000000d4015092040700449481c03181d000e50700ca50850b10403910a00d503182070421020000140310340258000070401307000702d031a8544180d4482c00140000d40380903a500081071001010540305800070700045410351101d41d050116441d500b50887d40c050180d42088000120b0110141008061103200e14a40e010036010340c0040350440d030090350402844110402c007a4450902c4140d1601c200103a0404a00140003085d10500030300320756440030301924150f40d044d6449064001e0f800154400e449140090410030001027420341d10a40600b51a540b41c025100314051001c0d104030354140e050305050000d024008143d03056405031a0002c201c91004040c40841e508036900003a1800d8200759010400450004880c5051031003502c80e950296142101292901803248800d40103802469202d482503108007080e0001500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 57826316 1250 57825066 57825091
    0x90c03130311030712090e100e1306110301080705010203030408070303090c0f15030b030102120a020d0f02030108010614060c0d08040c0e070305010504060b0903070506030a1d1609061d 81
    0x2c88084a8695000481c0c12510f540c003910040000782c0c0e100b040c40004018150a144071810040e42ca6880003205004007010642c80c0d00000d0501d4031840030700000f0b9a0045020030498020500240241d4000d0013610b050784034030000000c0b2035200108892040e500613052900742202c03540c089000d40800c070380990b80c8078007280d00400c040903405100d0340207003d20075001403400001d00d40039040d02c000c00c03040352090b4814003512000f00060407100340d00c035641e04401680c40840107000700082c031044400e901094800700010030052015400002a542601c144c0f00c1c030a028482040114420301d0300c0740110f500001c004191090007010010f8216204030101c006041d2070f01e211103a0180110340b00000240c41d000104418100340c4140e00c050540e000ca45031425030518003083d82c891040c4900d07405090300100051020729a580070501416803103030303140030302c0d580031304015950306500c14008114045410700054030345680c0310740000c5404600019407101090000d90507009030040c10784070940e1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 57827566 1250 57826316 57826337
    0xe1303090e0c03010305010507050403240216030215060d0c09050702010f0c020604120207060905060d090605040b010f05060307080c0a0207090c11060109020a020a02060714120711090c031303 84
    0x101c0c8500001c1c407031260060700d01e4a035071450400a0030343c0c00203800481400720812062000c54001c464214000301c0620280c1001c282c103044210003442480003505a000f900403e40c410141d007c0354416020000c800060340319214041048400492100c2c000c000c0f0b4450f8200700005107007074000c507510080c64000007604590a130b490310b01b560501000e2100507006130040204006510300e05030801c0b085440201000b908045d0094016a40303401254071030b031004250440b0782a001d8020900c03e5500032000d01180c24249030040244000780228803102100e10000f007501c1c24070320281c03486004955038607071f0705840c1c038010454a40e00c80011a4218044d05c0c1e0f0107c0d080403903000d002c1e841d6145688031540d52160480450414a040e002607800c1801040f001d42c05940c000f51550b100c540480d20241e40d560240342581c0d0b10120000110028040d03112528200b0f4403e00c00b030982c0350301502c0d045c16000d942d1002c103c011a4102c41c07401c00c000d000e202185200c401082000c12040c840e0034a4103026 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 57828816 1250 57827566 57827579
    0x1c0201110a0b1302031005060108070e0d3005090609010e040905060103080a0f0201151509081f0605031c0e030a060204090504050f060c12070509040c021606090e130309 74
    0x2c00e048440c1a251a5049010030131820200300030860506440010080c506103c0c00003070040c54081c02c0f03071080041c1c2e1000300900d60b4410000d010f4450380880d441001c0c084041074280761801c000b280107403c189450403800d200740100300720f480e2010010079141c03500700c9400065500181c140a075a4106540d803524100044040001502031800f5800b4180c45138140303000100900140041102164140241500591401c503130000949144a4a1400c2d20380940c500b00c035505060760013054148106240d50020420f04594925800c13a581c40902c403141e1520b0600d9610b16669030707120111040800c100c5006485171480f14034151001741514100000c54490400b603030000c4e00900c100c070396600284800c01c0313010401d8905210000000c2c0c21a40790168208171140126500b90540d2801178000a030745611031000c460b0846402130080100c0c01008000030364600301c0404460880003102c0300400c410340120b000c00f00301c51050383d14032481d07600ea000e1003200f10410784c002c41c00c2c40200e040200ba81e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 57830066 1250 57828816 57828833
    0x30503070605100504020f0d1a06030117100504030e010f03020d020c061005030f060a09110a1401120612020f03010605030613051903080a05041a0c0d06051c0201110a 73
    0xd4050000412039041641c043d4004a10507032155100e01e2042109400b011a40c0082e5104001c0c824000121014610103090a07003050740705c1030f980f18100100100d03441c440b11a10105100600c01112031a0680d900c0f410304464003580c02401081d048409080c16610403400d21341c0a00c180d250150620304183d60900507078108200409150300304800b0440c009101581800007000124010030000c40058621034a944c806011049079a40b901ca100050009003c0002881c0300701405008000340c0e038500d1b4801d14840705651030300081a10481c141c1c8074986000e080e09403a00d0b5040016070030410303404c025407070340f00729a1705d5095501e5013000945540c0500009104004a543c08100125549400b43c246000311181e08041c040b204211030110b40e20818045d844903841400080c0c0d500e450030000300c400682080c0341031528000b000c002c40d003000c03180508014a58075005006040d203640403c4003090305a1002016000102100e0026610800c1c0a0444080349001d59003604c0c1d468442062 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 57831316 1250 57830066 57830077
    0x1406090d120c02130b04111201030209070c170a021e070b13090608010204080d051c0b0d0b040503090a050a050d030c031403010617010608040309050909191511040602061609030503 79
    0x422681e6031a012107242407d010302030240508000c03803481c001e00040002c141e14810700020b40901e00f45000a00201c0c000c5003528105070300300d004890b028840303200790030641e402020140c006009044041c020740d0312480ca40c8442c0151000900841e81c1001d10a6070107800c44800401045400c0c0f034001418a424402c100c09003071442c00250b0b03508d00303003103046103054600c080d400c041040c20000070207810694402515403076018100404c1010032500014101718201c00d02070005a102001d100400c01d001006003030014095643e1460b4030364640421032285154032606420140445c48038001a00c80d00c5003118640c402c1c209051180c03954002c4440d103420981021010a540442c10014144c40041442c0140340516041e001480d09540007440d040c0c482c4aa18060310400e00460181c0c54148030708825040d12080c00289c1c0b03c007604144130312003031562405d00f0581c030b803c640b2403190580030308940c259450781d0000c0c5660744a100d2545449000070200d4070810504400100020754140020304 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 57832566 1250 57831316 57831349
    0x203150d0c061b1b2105030301050409020d02030d030b0a051c0f0303020403050a0b0105040f0b060a030c1103181311120702010b060409020a2c0108040515101406090d120c02 76
    0x1240241880900c01c0504240040c440d00403110301c0305ca8000480000c1140d040d2442510081600e000f01d00c0030421510022074001d500d0302030703c0d081d03c2c0c2030f96159220b402c0900080b1048034140e9921801c1c409402e6860b848900d120518102c411b02240000121180b5a4440d180c010328060b80c0c0e0703c0300d0b0700b400380d0346404a40d00114000100100d2601e40607044203112103240400500c00800b000440500c0780c1c0c56020b041c0b50f260031200322074a0041610002d02d422190580f0b42d031b0f0030070101049505c2e22480059200340003910800c0c1c0c89416612030130031516688401145809404001d034034122000412a004664031000101e01580b12400540300a1070034000c0585c60742d03000ea00c0074107021802e20f10030541003500e0040710301840c1d0480f01c0d60700194081c2010355040c0c0f0380e402e002c1c0c14540e01d0990b0403208010882407001907104071100700c040b44c01684c4416038050080c0b040203054401c1440007540014480d10003008501058040c808072a0070381088000120141c4c082800d1450244000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 57833816 1250 57832566 57832613
    0x50606070f140f011a1002010f0609021c02070506010b0304081e1c05040b01050d030e0303070c060207060504050603192009120a0f060c02070f090203150d0c061b 71
    0xc00614104003d10b00f42d40800d10003d101504180c1c1c03628521144503d0b03500d00c6030403600d0780d0840f128001e50080c085d44040e0305003800000d03100c0d500c001c0a90f128088139280440711048045040c01e40c0e109541510360300c60060201e6900e054050034a5070005002a1031490f000c1040b149045803039a600f00380c2a1081e48100e4640060015804d0400583c05130f4082c0c0ea070400c01080009000e400c00281504d10440e0700919a61440c1821104d800c1c545281c19054400021b1002c14004003140342d00c1100c0c803035800c64030707070075150402191580140e01c5090b80201d03040c004549846402500800030000e200300000d5020100400c000800300d00354440702c1c1401b000a09944241000e41d00c00310110a12402000340f10000e54805010308207141000e8891070345d41c0091001380e842841070724020f12903984d0b05605240c98542c02c0c0020342c01034130340300c040c40c016940c11606410124034000d40d0310340103170410b811245021016210f1860710195a490701070550349040000700c400042200801045151 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 57835066 1250 57833816 57833843
    0x81b0111010903030510050f1f030e1b03010608030c07060c020f1c0b07030e120706090c030c0e0604060305150604020d02180901060816030b180703020c0606010e0102070603050606070f 81
    0x13402c0c6e1125400150007140075001d04100c82c0c94005085c40010403000410b101d52101e0101140100101181c9018a002d58001880500e4104500300c0e0300110031070007001020390380d030402030b0780e41303e401001c54803900651010011075004036404101c050001d80200381c0b9903a10b80025116050b401d25003840d12001b83c4e8402c0502074461271442c0d000e0180d0500b080140d5400d14403e41d103a01520445196003400102403003040141d07000391342e006038071482d20718a40c0d450385090301400f086401242240e0155000048013440d150003150110380c0c106000d0f03c0d0780031804444481490008003c039400540070484020070010600c003c040c0b90070480790b49014504410200300c02d0040c1a44070030204140d40b014850703045100b038802c0c61154414100003a8003011301d808a9200070b0040e020103403100c8800204081d03290181c000b4103001540400b0349a4075a90a001510314001400e601d80c0140d100c0320082c020580651b1003640c02210003002c0c0c50900503280c1d2468050b004000e400c4404003009000c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 57836316 1250 57835066 57835081
    0x1205030f0d1a03070b090d05010603080a1706010201050c03060d03020c06040f030303150b16030309021804050c09040803011401020c0d0c05090a050c1c0f15050f060301081b01110109030305 83
    0xb40400700320400c034060080300b072500040011601942c81c10350322903a54280d0300700802c43c4c00d601c40001507034000903068035184182c0f030185c0f22010724150700c101e1102504c00140c0c3c943c03043c41180d11981446d2034050030360b141e490902543c0c1081c40e000b01d0640c8500c403902c107281d54802c6c1c090b00080180c102c040b00c0ea1410351030300409a0381c10644a4242001c20441840b502c2a4074007502c40004000d8003410b85000306003421006805c89031806034000100d80d00000340c1c04148000b0384d1040c0c1c0904c0072100c18141003030a2109089007105d02034507040040c001401011542c4031400c0e1810b5052040710902d152400001d01c140c0c0c500c64044a0510b0400003c00080c00e1455081d540002c603d40200494270b0000d0803d0403070311a401c0b46288006d041c446c0d4950f038401c20741c0540e4601261079030410000d082c0082c60480d15510740521072145080070700d651802e240840c101c074140c0b80010058842c0441301106a0300840d88503035494180b0580ca054885001024420704074000c0c00ba07500030940f8100b421 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 57837566 1250 57836316 57836351
    0xb091807090b06041505042705010b0306220b06190906022b09090e0c030f0d05120c040b03070f0e0105040341100b01030203010f1205030f0d 62
    0xa1203400e0321410520b4088243d0703903180560302102e000341175540c01030710300701d1080300c8910958201c101c4071501000d039060300e0b80080108480d02c51103070108110503621005060081d010881f072181d404124841d9102d580c1010700c12100d50380340802d00110f41050008009509030308414986035028028041154105030300034060401428240040c003003428106d0300c034801162000301004009801c0c1c4404503100c83c81600000010154030400b00a250101d201240e01c8400c9985503c1c8640301c0c601e1030202460b00800d000c2c0003c1c0560715018901584510b5958611900405200051400303010010b41c241c0180d0003103129010340e0755285032a007241080070702011840000700781041424041400020361107182080058020213003500915a0300d10000d6100c02105001c44000e050420a18441f0b41e00181c203104e45040c0100610441c091240118101d00003403040e0b000c0440c0d4110b00f0414040800c1e040d94034180501c003540d113090304107594041507034408080c40d01d038503507a060580399604111 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 57838816 1250 57837566 57837569
    0x30703080907060f0207030602181002030904060b0405061b19030906031407083706060806061602010507150203010e0624030a0b030a1b06080907030f03120b091807 72
    0x9080000404c40b1203000203544030303000d010040019600003003904001c10036040540000c0001028014001c3c03100340020340325000203c000c4d0045061640210b842181138082d10f0994201400160924284040320344541d500c3e00d001035801d0252050000e4690035a01c46c03004158001d8659202c2d65180c45070003021140e884038280120300240c001d00c0495680020150b07089200e0302076500800001c40002065101007940500040030222008203603102a9085a4101c480343e031034408240d607072242071114078400c42d84c038100c0041d1407144000c010b60058019200260140c4100c9040440010140c4120390003078000d1503901030010100039041c584519035010251040401c0d1303180d82d001c049400294040a17106c141e0035500ca55505141c0d4608008980c286504100f0110f100e01d0804143c0400740c0e518001c5000140510300054805c3e1400241c270011254800010f11640c0c0040c0c80403240406070740c0c17480c220507845410b544480c2d6240c03075265019101c2018011110140215440d20f0b08015 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 57840066 1250 57838816 57838829
    0x4031b06030605030a020409020102011d0706090905151012090501060504050112050604230304090609051602100c0c0516050f1009030f03020708060109020d060e090d1101020903030703080907 84
    0xc02c0380034011074401007103500c0e03060b50540700421400c001c0d1005038090700400300d03a90100d21004c5622002034400041010071500c0e5078503940041d0f0b4460300345105a030400c80c1c4c00649a980e400380f807051402d2016030f04902540c2c614024040119011551003528194a0207440c01d0391580d0041c403440c98103104042c01440081403600740c514030750741c49580710311000b0405869001e22030240c480080c0840c1001440c1400c140aa0b6a10390301c40b040c00d4010615405819441d600c1c0c200003960310b940145461400c1d24441e00100700e070040d2184944080c0c240891302004004040c0c186030005501040907401e280d5507200030340c02a80c01d14085c014985010800c0034407c8001f8400c40d01c0554000c444402542e800c182200501032042c01e0580c0707042700940c0a50ba091003403d0001810041c1c80c0e001c0c01840c1181b00c014843c2d6941c621007806a000d00b81d840d80500e41000c0c12203405c01c1d000e03c3d140851381d10070200140c100084000084c0c1113810002c001d81c08100a0300400021075420304c41140a41076 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 57841316 1250 57840066 57840071
    0x30d0c020108060d030306090e060103060b01050906040918061416030203060a060e040e03040303020f0d050708030112060603020405010f0314010203010b09130209030a03050405010315050102031c09020604031b0603 94
    0x10340009001c0d220142081d80140e40300380d01035040c548030740c10540182c100100d040c8020110600804c0d515a0240300503030b0348030703e80310400401d5885001100c030b0206009040b2400c1c10304180010000b00074007000700038a2105e940ca00c00000304180104d03040b48102038103001c901e18044e503109a080c414040c0d500308040c4100100301107a80c0b440e40f900c065400f1031800100722100c00001c54020300c034807440c2d125035200c0031600001b050390005080c002550b01209494445056030410744850150880c0182000010b000510107100c50540a124030f90154402190096a0f030b0080b8084a10a030084502084091002e10078081c00798080001107102c1720003180345600d41418500d0310b0254400d41d601c11502d1515101501c00e60390140d952240c4010b0070f40f0600c1c1454a400780c8540d0043c0300c1c6901013400e20f054000c1c3c4c52181d0403913a003110b0042c0c000d14074103d10000c120820461520210342500e545042480246c0c40d02000703440614420041c8800e13800800300e4402e103034209a03000d00101030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 57842566 1250 57841316 57841337
    0x1302150408190302121e030c040501021504030c120c1416080705100c02060c03180103050a05040515060a0f0e01030224090d08091305040605010503010e1f14010f0302030d 75
    0x207034000b4554540c2640d503c03015455880c1c0003c0b04185814510b02d000b1610400b0050141308c280d0700b80100200ea8007602203030104021801ca408003070320211006004111200719680100e100000c0009d402886031412100407401d6595130305002c110040c040b400c3d07034040700c500b82c1e585101d01d00e05005000b0802c01082d81c00c0c58200003449481100c0d40e00f13410003601903000404c5480d2031090303494044041c01a40c2c1c0f10814031400005050124014900080c00d04c00450201c018a00c100c03402180c00030003400c0c6801102d414440d0013940902000d80080100384000743e00300d04000d411000c0c10001400090f01c2d45180100440084039190100c41013681c60032480d9030308454001c4036403100e03080c1d810704803400142c10044241e010b41c2c01c0c1c0503045000f00c1010125504640c2c41a40302d070b031080008104030390701c82e8140f500700d950241e0000031f65800040d0f000180c0d10307401c252914210090001060703445103515081c84805007a4441107194000e04070510462030140a40ca070740a4080c68a041e610 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 57843816 1250 57842566 57842573
    0x311030a0e100c150218060d1a04050c09010e030f0f070305151006080601021c0e1206160810030203010c02070e010e070804030f0c02030706181a12130215040819 71
    0x100320300f141c1c903885034002103840b6501d1b0a0310901014690080104d034503008000f01010140c03d1644948000d9401c84000340418505449140c3c000c050340c01c542400c11500c0c50065402410040503e42c1c1841501560300c001c0340200148a944a6120080c10340145103180440c901200072020018800c0640c0030800104d4540075440100da000d890070880c580c4070703500180d0604a040f10500e01c2d600c9500040d00e5000d80001c16000c0c802d80035160421604a0079980d552991300555114900261060354100304600c500700c400d80000c0c1c0c4103100d8450a94943c0020300710740040d07803904050303002a0420414850190451801040c2c0d00002136401e1030040f4005000040080000702406620310b45c2104480c0b10314039400c201d1f980036040711001512000e0203840250104c9110403103141c07941002c941498412081c003108500c4a03101400c00907401c1c054407040000a2070300000c503501d9445135001d6070707400e5240442e050302c40d280c499a69003444029404c002c1800320a14020324240c6504000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 57845066 1250 57843816 57843833
    0xa03020c011b050d1d1503010504020706020d020d06180203040507030b0406090506010605041a040302090609130c03030507152a03021209011a0a0b0d02070311030a0e100c 75
    0x25409290102c8481c8000c0c0d1a40d5550719220006400307842002c4113070510980045402c020320100c0b441450280c0394280030860414410078401a56940134001000f460034070781c01904589110b8400903041980c8405058104e800ca006034280b034648035941040301c41500750100f014104820025455458a910b40b599101414070009146030301d03180000307082c0302d402d0b48405009a8003800360340007540d48150041450700300d0f014007043d01e100710482c000d01c40e410300222400c5130741c060701d2036980e642c881041000d007040c0103011043d400d481c035040c003000803909140343d8040d621170b8503540c2d1a00d102d0b00f44600c80000d81068500410720708070420030401c1904242c01499042c001040c0d0031400002000ca01078022212036140030400c14090045034281900031038010101c0041c42d4100601c08010003010317035124899001c80c01d03000c000c2c2e0f05e140c01b07580e00200700c1a806400c2100389040d540e4a190314642c40003191000041c20b0449440c00c40c82c0c444030403101c1038528946404002c005407101043d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 57846316 1250 57845066 57845083
    0x60c0503160201050705010f0b090702032505031606020304032a120e1905090a0b0a0306020a0201200903071a0904180507060f020d0203042105160b090109080a0302 72
    0x180501140c0720442168440c070116108164001e009100311003499030b0480c0a0314150780707010b210f5801744000035103032407000081d11003110410703c40001142444003401400000c00400fa2280d00041041004603d00b0320510713103034184161401a5a45400e0a0041c030701440b80c002d04800b1310864218040084450510486441e0402200403415030384240aa503614026505240c100810754490041610010b104004864051301d01d08465640c10b0201011101d20900d0564081034040042c404520a540a0b000d03198050000182d048000a201080841c3c010513600301c0c62400122010f030307424103004220081c48c1c0406400140031f58401154a680034056016000710f07070350101e418000c80f440c22100220f135040300036955450744503440204291500c0d02080f000d84641c03459a503c42e8400022a0300b00c4c3e00600016000038901200409400300b01c00e81622184150420349041d24207009642008110302c0320010741c0c80240320005041d103030840e030010f041038000025210100b5004101481e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 57847566 1250 57846316 57846337
    0x180d0806090a0603060c020312060301020301051021060e01031109060f010e06040f170d08040f0b0403020c100f03060b0405090109150305010c0c03090e1b0322050610060c0503 77
    0xa410307a40c002c09140100400c2e4800b51400c0c0c1050702101c07100e80c012000b04510040c03500d0146040c3c3e40c05090500740d100c03c1c030495401c01102000000a140310b00c44041d83c0e000401c032403100c119460803900042d82c0640c1c124201841d02d1500401c00c000f0105c1151440320b2068541c03003407600c4d01c280010030383c40c0c41241040c14001c5080940350240c2d00c6000f150050003100c2c0015060940301c0c0402091140703110b00d140100d11511807036296450258500c4c500c119400442c10b03442d00100c2e50b860281c100058021000c0d44500a02180c00d036850320354810304481240e135244208000f1031002801c0e11203580c044a10030100b080180b100e80ca404107120305540403244003045103000071260a070402d0aa03440940194078002410649960006551901c0f50013035445415041d10348588407000700090311100d000083c40e501e90340420305168040c607072041c4000c203803a450145e030320481109203138190f008482c590010b0040141501014608101801080c68100d48031b1010f65100780d41c81c41042c0703208 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 57848816 1250 57847566 57847579
    0x105090d080601020a0c1413091a060a0b030105041d01090f02030d030e032515050a0c0504050d022404030623010b0403030806040b060c0a0204050a05071d0a050a0806180d0806 77
    0x1055144c01180b0f070b214a07404042013004049c1801e112a090300c3c00d4041030405000140031174168504044050b09440e483c401c0e9a10356417030001000001c290030307031720b10030405140c00304a41442028440c020301d240c01018005807c500350700c101030800c1c0d13550040c0400d05140c05c01c1d054421800000f0385447c100d001c3d000b651001c0c05420801d034020710b80c14005014a1808400c0d07690f40b40b0a410841c020007070a0403c1c01004130303007034080e526030280d8000c88c2d4003c68040503c1c000341c5014800300c441e007034030401c0080d08565015544001a40181c0041c0c0e600703926000b80e204081ba0fa03080100000041c407641603065410510900280d126900c80a002c218400d0089040c642e59940148908000200190fa030f41d4500803245840e4183c1c8001039200703070300e044002425600709010b0340f44118542c3c5d1b1858020110000d948180c060501c4100d904182c2c0390001180d1034803a822001c01802000f4000c009518045019403280ea11420006034180c0101c00303071a04490f00002e84c0d17038100c002100d0360f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 57850066 1250 57848816 57848849
    0x609061014151b010b090730020a050702010e09040201020a082803140610140d09080c0106030203070b0f1902010f060306060602070b040b0a0516050105090d080601020a0c 75
    0x41c2807030b6440220300c8516034001502c03082048603c00404034001000000b0300c030924100040002c813040c1264802d02140b40440110340680c6a520b8403802c0501c610700800c001240c09522038100d8002600440c040f031800140c6000b9036811452105042d80c0807203a072520b41c82c04d90b0000713480d0070081400070290003000c107600b024000d5904107410a58030b40c2c03480c58810303002028000c000d401d0a043c1a0700c040450000709089013440311140754580c0d42500c8441076160309903011101640109072415680340d55500c04000195100024022010440000300d03caa040d801014104415a0f2008402801c104540d030821140b840a0340d100314119450510303000601a0140d001d020f0210303034050040d16018020013001269448000dd50b0069822940d80d29154052010940304600ad0115011024402c5017505440f90008000f032143c101d08204a103452a5a45420344070143d0300c01e1100d4014003203034201c0b00d50042c4e0300741e403080c4240b00030440001141c0301c85417001a94010520400050a01c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 57851316 1250 57850066 57850069
    0x906050612180105040b0a0c05120613020d0203010b0d06050d05060f0a0b1f0e01050901140d0b060309030a02010f14061207080f070906050103060509010b0304110d03110609061014 79
    0xb80c00001e6800800a115601c0c0c185481d106903e0119405441180340041d614025442081a21191001d407806c00b0040c8c3c4402c802c01041c18000d054800405400300f100044640c15800903500810200a84a4846c0c085c003049505640c0542c0005006410a034807180c00720340002440e1340c00000c1c0c5200700304a03031a0301c580720028003050450b0b0354110460800280c21444254108050403a80b69070304480340340c0700d0b00111060704c00da41d000d40c0090364860050710300c2d0445000811141140940c0096450356880100e107a5810485640720150400b090541e40540c080c0030b40303c0404100b050070483c15041140c1c841c450b81010342024021140c50000740382e89601005508068171816088440d6081c403452000d035251614011642624200000040c181d4000d0007440280c88005112015030b80c20501010040d420003007041d1244d90446883c20219110360400e0520344d402a51030320340d41441c04088070710b411005008071740c15501c03d00401ca510700070f004220081e1000c581c5524284102c990 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 57852566 1250 57851316 57851341
    0x4030305190e0f0f06130201030f020d090309060e04020403022b0506130c0807030f03050c010908161a0f0711030d1401080d140418180503090a0906050612 68
    0x12144014604400c0c82c0034018001070300321014504074101c40d46840300c4140381c1d4442600340c44c0044080e030b01c07800140044d8001d4005a481c1d2086c24030043c140f402030610380003a42d200040541c08550009400d0101c15400419086880d1003520300750303e09481c60b40402c0d22000f07491240380e03644c8900410810300800e1020140b032161f030044200d42381070500e130000c048005203003041103400340140a80000c10807004204242101e8024802c000c04000b1514203880c0c1d0742c01003d0780c00003550b1f60b001c6038002580d4130001d0f2a0f000742a82200c03c02e400185071000707006610540c950340d10340c2d04004200044400c4910281e02405a181c402a040c0b079901c075540c42c5000d03c030303500d40380d050402240b1103103466000181070490300600b00300c5d001450007000076034461400411205140e002080b0500070262000c04188904441d04c0000954055008060048070700c404812503154000203100078091400602e400060404070208100304c620340070004110784209400e000103585114001180241d080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 57853816 1250 57852566 57852601
    0x105070203070609090f2c1c0c0b060409051b040f02040b070204050c07080405150d1a0405010f050102070e0c0c0604030225060c0b0408130e1005090c0304030305 71
    0x1400b207a9040352104005045011240211080c0500d04045215600918040c0300700340804606580c50038181c0315080c48040b002d426485000d846082c910903158054a0072400c500b403201d566184025000345801081c461020309594802c1b4140303450800400c0d00031a10340ca4001014041c022064664000704010701041807c8003051840480c0005209900320001e1100b64030841d82008540d480d0341000240303004410010302801420310084c04a81000e420403c2140da001032500c0c24842660508410303100c2003848440801e0241c2c00e45049401c1c540602c03805000f0082104040d6410507000035962500b52043c0110f0100347c4011444c203107000c0d000c817080c0788101020f40d17489251500b00a035450300040001d50080b01d10503482d459402800740c1a90944260b07556085c180305040d140d01e03800d20030140041c0c1c1d10807000c122100801c218081504000c01942860000c1880e080d00f400c0710b600500c2e40420b009a0b065020098004414801c5a5006a0605000804da12400b80259504a20 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 57855066 1250 57853816 57853819
    0x20906010810050d0602131a070807060204030b04030f031103010828080a0807080a050408030406201306080604050c04180603120504090e0a020f010f110105040305090a0e1003060b01050702 83
    0x50114075814420070b074000b0007401c7c55070001c80c21441e5862841c4c10030034a0b9420844002c80c07087c002d080024503d0801800ca09004030070142c1040d450340c40c2c9462101c2c0955084022403001c1403599400c542600415801c80f0b0840c1d031b41415907140ca50215110300c0b0a02c064458106404200305c04070b12808403107492290043d40b6281c507041401000307049114280d03020300202e100c070300004640030501e000e203910803a8800c00d00c5003507845d079680c0d940162003a070224140082c01d842c01e080d5801481e1003d444001d0048402c4400140780440c06420144080c050300e005904060811410311700c420126001c8901000e002801325203002004070013000240c01c0240b92850b074444c4c07a040b81d0b90101c06041aa01010341c00c02a00c010f24101694071181b83c50000e420120004809001d50300501d1040420316880c1000b030140700d45107420f1421924116012008682c001c2100c1000c2c3c20041c0c800300141c03014090b0301c1118144417070898580011440b00410b900d40385d03584c0031000d91040d025507034400da0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 57856316 1250 57855066 57855079
    0x917070303020a09090e0d030c02150a06050f0102011406010c0203030d0e0106061d09070f090b04080a0b0708150607060609050a0b040c0509061c06030506070807120902090601081005 80
    0x4a1400070080d40c80752280d44001144c0410104113601c00348540407881c0c031250001c0c0400000365070150060038400ba40e036025405091103001e140041001207501c10070101d84001f504600f030604225402c5034110325141107a140c00a130320a0b1460450034640c00c6002404c0c0442080001d01c0020720714459580c051607140e06145022605010541244090365400d440313145c1c16903016413200b4600034a00030b09541c0070f680c0c0800301c0c4120f40144103080e0600014585030000035166000c0c10865401980071340010303807100701c00e1014442043c41c80c03138001d0003500c2d110a1900b1b00d0b80c1504400030781d8001ca5403141c000000e00741c04222a82c0d014400605a05000303000d45e1529075204e400400301130403024095403c00b090849541d1040b811261104001014030381005001500740d000351030390300301c105480b0b070b0b4032000030001c40c508000151041c102070391002080e1600001c000c108180b0000403207000d40c04c000b500001a038440f820a1b91080080c82c22440e01e03130f1442c0f221003c401c0142d2006e80c0290 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 57857566 1250 57856316 57856327
    0xf03010b10030902040b0603060306070305070306080a030c05011103060907050d0b09040b0411010201290414190605090c040312020c0405101d07090b07050a1203021804050601050a030917 82
    0x2030b010303080548000d00031601001030401c1c04061014600c421241641c1c55049240090801400f984c00740703401c5031141c42c00040c15a01d4071405450880108419008908640e0b0308104002007401001c44143d001d816450071400d10b400071407000714010705030340140070001c54045407180b00c83e8040c003800702c0001c2c40800c0318201070a002d9000320050b50242d07905203500181104035401401074240c240d07a49140e0715a4144040d50464003039507104012540161180c0d4510401e0304807000541c0624000710030b258242040e5061002109e00991155000d518524200003446400c41c0655040725003001345c0c00c8421241c0c0004a04010884a0341548a0703d02001d03c2699856a040001a500d003180b1400d03490902c84006002850220380c030380001a07000d0400d100610304140070702407a51103001200c122003540d0380c440420f19a403014032400241e021512041421421100d001c4889082c3c804020781d00f40100020054403403011132105042d125005d0404004203444c0d107000120000d9140c64560 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 57858816 1250 57857566 57857599
    0x702150f03010f060f030c0e12072c0114060f07031806080105100503010305060619030c06051309020a0f0302030c0403050a060c18061b0809030f0a06050109090209060f03010b 77
    0x204134054100004c00b01803451819501a04c50421101e0040d16036000784920002040803c80642054410038000d000000409610300300216017484105da04891440481000c0d030005800140c1c005100403030640310603903464840b00101c81005040010440d62004a81001c2d01c1703192040a10072042054071030b000070600d074000402e0741602d074100e44140903203040303003003c8070705000c01c1c000504142c02c59000300710310745007540601e07803854a43c0d034011030116a25142c001310b0bd04150302c04d0340031400000d40c404600485c0d6040501400e0400c10440c02c200c7d1501c03000384442030060601041c16030002c0400c99a581d41000e0328000c5611034211910661240341801c00b411503c420314001c01ca0055640204d4990441200301381c0301c0f140c1d204c10100c44254115100542e8810064407032900401a5664a40b0144403a91500312280000c10a01e441494401c048035030591100349201d14013041c08005a80f80705100c2d4100408031400c801d6039220340006401001030a144a61110b00f506000304003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 57860066 1250 57858816 57858839
    0xc030c010e06010906050609120c13050103020f0a0b0306090c04090903030207170a020615040204030606060503062d010509040e0d090e060102070e06040906060812121b0702150f0301 80
    0x24146a0825100240d84e90503100c8180e488600940354082414080304045003046103910083c04c02e18070031142c80640e020301141220345025080300007581c03640014015030600310050120b016003501c0850290780b6150942140e408040c0109200382581000f1071001c03010b5000750b5020300307400003080103200d005180180081d80540405c460300d11884c0c030010040c00c203082c191340b0b410003250041c2c80c03a03644403214140000110400320b40d01075424080440421002d1140c07d0141030302d0f49645a4034102401041440760b40d6540402d90010114076030659099800d403035140085007824560f40342c0d10288001006460341040000700742c13040103085411a90b0110f0800115030445007090904c0d02c44500498442e0858044c82050004140c08210319090980c41070f005203000e404c0c0007070b5003a140c200980c10685085c0b20f04110380c130301103201c0350800d00c070403101c070b0b0480f001c080b03a541100c4032044440001c1c01900b00117031081024146000410101900319440302c02108200c1d0713a25130f103801d0703078492 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 57861316 1250 57860066 57860081
    0x1020a08010f03030203191103030a0b030c040b0a05010e0112050702010902120102030601051e130e060f0315010b03100905011e0501030209010c060b13022701180306050c0c030c01 79
    0x1410324800041c1d0010301072074450580743c1640c00b0b1403030300c0c081584100940650050640401102004a00c3c40c42414005140078030109400410f51504203003c040c40c0855030501300d44105d141c1212400140c0d0b407002c1d60401c8034420300304007130401304500069030b039031088030840c2c1c081c28201002c01c24070742c1d41036001480751071088420f402d803c00142d10081c00c0740405c86003d03000c11400c203c1c0003140c0100844080e000030340320785220f18050003c100d0401070140760f031000072000e440c442400b0462400c0443d04031700203c2507000308400101c1c5038030700c0e10340c0c2018858002a01c2d40040414004c418550402c4040c01c440c003c2070016507900d0980c80c901c5808266403814801b00c42d0b2010400350321a000721444410165507000c6051115180e00d002810541c2d1500d44c0b00c81603400c150b2281c0c1850003c0e0005200d1464810360924071081c10214804000851904000b00306050061110000c4139003401c1e250403210000705035561000c00401403080300c540080c035100110744190707090301c15000144c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 57862566 1250 57861316 57861337
    0xc0405041407060801140f04020712020c0a0801090b0117011b020c0102100624030605030a06020c010b04020309060c07030207051f0e0a0b09011413120b010506160f1a090102 76
    0x7120302e41c0d00d280840310000d003801100008190725014580f0340c9840da9010620100c0180018503282050341c98800703103a6010462005a00035809a20180c0742c0520340e0001402c5003402804001c800766503081c2d42d420305000c2c0002148407d00ca0044120095010400701a040744a40c0c14080d41110060340d1010342c528418010701c6540b032072900ca61918040d81048401602d1519044401070940f0750801c001c1218040070190b88010001d159942000031141e0385005520041c1e8405800c1c2c0100d0030348d140d0109890243e801081401080741000503c1a0711031400ca060381e40b1842e40e03181c1282403101603402541e0102140e500c81724003010703120001c0c04940060310f400b884015550b081c01110b01c1c1c244104044800c041c05010140e50142807000ba001c04101c00c0e1602e0111041c1c2c4c80c201d2031081d80c00840c4d80c0301c810900c60b0100031042003a1409002c0480d9101d060070312000305910108140c60300240007030742d00208034081040c0c990312a403074031f50240b448400b1886e200158078000e401074600031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 57863816 1250 57862566 57862573
    0x1505190e0c010f0f0c1e050106050301050c0304030503041103030f12060a03030f030c0e030f070302090901140a1e05070201020d0c0c0b04060203060303070c0303030b010f110c040b030c04050414 85
    0x8200400002030301c1d400e20101030b1a02c007201c001d243c0c0300356003255180700c0c0395041c01070b0712180c02c0005c0c91020340380341d038907825281c2aa0201c8150a02d1800c495640d04040c2c083da161400f840001000c050a80c1d6009a1501d4580d0b40c943c0d452500450803587c1701482d54141c4404a01d01510003030141c007500701c0d100e000c0c02103c01a07031007000b001110905444054046400b803541c10208030311a80000c00582c903203007010051802e9200109140c0b408500b404041034020311010700031481c00709034641d040742c0c0c00c000900541200d0f02d10358804031b801400d184816540c9aa6046408003c0645079030b404500c0c201c01c00c400c1c58003e80c06070203036024102700310b4002d2808010701c41c25030241420440840c1c003d603a124443d42c955583c00001d5001a0615038540300c00e00920300000d80d24002d02010390710982d00400c0c00c0300d40000140c03001492103440001d20001c0844803c14540000303400c03102c0c9004840108000d0007220100741008906450703141c00c142404208030511902502100c810b01c5c120085 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 57865066 1250 57863816 57863831
    0x40509060409020f040b010207030b1e0106092706030615030507050411090409061104080f0d0806060a03092a0e010603050402061603050423010f020c030c010c150519 73
    0x10803040b01e04441c0c0081d4810102c8009100703508107544003114406040c0100d03041585c0700d482d814000881140c004205540c080d089408100c0107954150051005040c0794601d00cbc24142da22809859150212140060030707003612001c2401900b002e8020340d004078041007008800040140007541d94082034689100d0004009800d05180c443c40f82e200e841d54209c64285100303901004080d1025500a0303907035513115002c080d00d60915100400c000d00d00d00006103590001c1000e424286584c0211440c03c0c01400000c1007803e441d0b000455803080114a40041e640f1000c2ca803203621a202903c014400c0c1c52002480c080d1110400c2c1e5281c00c2c1e034801c1e03102500582e40d401c0120107451007110000c1d002041070101c5007103140c54000719100b0a200c0e041031401c00c5e40329a145581a0484c0c041c0311400c10b4580002d44003560000003810010b4032601c05001c1c2030f65400c010954031382062295a0412029804100c10b104d400700d034640300306841000500032420150030582d030446001200c061018608030700c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 57866316 1250 57865066 57865069
    0xb0106020a030e09060d080f040302100809280204050703060e01060905010908191407030807030804060b0904050303150604050d030201050702120304020a0501050f0903060f0912031920040b04050906 87
    0x81c4c90b10441c8010b20080d920021035449504540211052001c42c08050101100580e40d085985d1010740c02a501c0d01c3c290300d0114039041c501034407980b105021b6a851540e10311810f05a0194016494043d580850141c4920707804030024801a800004405248000425a81c2c2d1000c030070801c4480990b03e02040b540c482d40c1340da85541c3e41c1500580c0a4014041107000110b204402c0b40c44407141905952446580e600c4940981d0b00c0701030224002145c0070200000c0000c1407060003481101aa0071a08a1a180d40d6007640d0344409001000100d03503002031006242c0e90001290702404000e40f440e410106107240103030107050152400c00250180c110441079400603542943d104ae500204038030501458a00103444662180d446040364800401850760700c2d450402c40036001d01485100000f462800318016410314841c600e9141e281e90f81041030044101c038280d03144801403143c040004403442e40c0075034120300c40c42ca00381c0144040300100c6c00160500c0164054401c958003a81c400d02107075103540 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 57867566 1250 57866316 57866329
    0x30c15020615010f02030f0f1b0309010f03051810090303180314070609080c160501020a0506060f0d0c03080309010b040c02060406090204060b0c010504021011280b0106020a030e 78
    0x32044904002d003600d4440c030541c89100c205a0098990068070320780306020b6006046a0b0089140c1d2a0241c00084e2174001081d150300004d10381500c0c2d20203117041c401d4281c0000d003604001c1902c00d08050702d0700045a040e00c200c1a020040010300401c961410f607101f04984090001c1d0641900860b1400a0004d0760109031100310307582d250702d07a50321b0310a085481d43d85d2149401c041e2082c0c4e0702036550701d08200041c220b000180f4020301064000c02c03240503030100344500300c8840d801c107a04641264190a00092000030007581245003254001c00070890403000c90000344c0400400707040c41030700101c0001441941030003540a500160001c0c03120030107040510041d0380b4010300c264010b82c02600000c020507040e0703000b541c0040c40240301083d0543d4540e03c5100540110404424695550b0140000c520300b44442001c09a4281441c0f62618696410300d41c50f030003107400e0304c0791021100704508441e10350001d040758040c2d4002c003000a6035031140e000a54400e00e0b0003044000c20070740035640c0804d25180 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 57868816 1250 57867566 57867571
    0xc09100501080a1e2306060f0d0b0d020913061107030f030f0902030f01020a0305010509060a060507030e030a200a080709090507030503210a050708060609011701030c150206 76
    0x1a140c00e86151201c440300d0008001c070020003202c4000490000003007113054064a0740d40180100f00741d5142e14015101050a880503021a109032010841907640b242c1c01c105980340c2c98800e840000d2030303400b2140401c0301403109901c0254400b00e90303001c0203043d0500c0011000c45600030b034020001c1010782020880740e0303c82c080028001c01c40d9005c1520f0440c4c0b00f5000704295000490011a01d080c0c01d5000c00d14084059603118401d94010801d0107419905100e40b9004000c110340c01c0c1e415007040400300790a02000c2c019101080b200142c0d040506000741458a0503100c0a0120307594540c15040c0100e00120740d4030304070032559030000c20380d88030325040c40303210243c84204020700807007803034100000000c1c104503004660301d014504000003c80c0090003d058030b42d54102512902d09441c0951b9258540014941009076140205102c50f440c1e01c400f0055202030141c0d04d2542d42d105050060b10703c65184205031488169100000c0204001c00451804031500a004042d484840405c241c1c0c0700c9004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 57870066 1250 57868816 57868819
    0x1309020403050c09091f1b0206010b040611120c010b130506010e0f030c040f02040602071a04030807030e030109050f010f0204080c060306061e0703021c050d09051606020c091005 78
    0x89040c51043c0d00d007084c41c0d40e411050120440d500701480c00c0b0b400450030300e1104034070382c51aa110f4030142c81c00141d180705007868200d44041d04d001c2d0305040841c8030f240504d01a45040098800340d640520104010410320651840140e0b85c54540644101c0d020305405003405d130160910b94180c0540d00001d00450b40601c50586480300036518403020701c4003520a420542d07502d44507110100d4041c5d19244110210190b00241c050303659410722002034501001d07030340001e0f080c52004440d01051521300d001e86050325840720107aa03854100d400c00304d82d25002c102c007241d0300d54a0f2060860402130001420355002c81c294009000c030103e000d181c141203010b05d00c1119400c2e0040070407040c3e40e203015002103070b106030020030050903d041e0b0107a0400d2036a140901d044c5488001501e4803c0c160100280101081140c050106030034900c040140280180f07440b600400c2d89503290302003041400d1000344000b04c2031000c43c2070b03480d03139610000303544030a000075503405030000e071010034046900d141000382602c40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 57871316 1250 57870066 57870073
    0xf0f070801060e060117060a150801030b070903050a03030b0f060a0309030201050f150103050c0d020415120204140603060d0222060e0403020c09070203071209060f0207050919110d02130902040305 86
    0x10040d0f086c07010100c1c002c0c081c0340c4c030080441e000324107058a0f295000c108141c07036907a20015815072810305d98020004c1c1c03488003441924030341040000d6000070031408055041c238000c504d4521500c081006c59007281e100b0742d0300007030125422084e0b0f81e01d03034010301e170302800395000703100d1500ca40310000070542d401d441c100c4081250300c20b0b060040d40039400c4140c1082d8a031034014030b000840c2d00701004a801503006800319059148103800203941c0503180c481d00c6203000300c04500d000d00e080c80146030300743c01e45a12030050f007021000410701d9075120041c0c5c0130180c02a02c081030415a11005800840780b0710403110203189071450110740d13944c0180e0b4940c4900e515800603c031107035504013001007100c0e0041103081184010481c10f000102036103501609a0b0541c0c40300b00d245410540b02812492118040c18110f40c02580e04100503910846229006522400e01d040381800354030210001d0035894040710a46807000405424039a40380d0f00070940c0c10529002118003a840303c002c18103074482e505c00601680c1c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 57872566 1250 57871316 57871337
    0x80316090503071a040504050103081b030a0509100e13051006020a02030a03030914030a0f0305070c020a050f030a060e060709080703050d12140a0b0f01020d0206180f0f070801060e0601 81
    0x60a41100b51110010101013034203042c0d07200b00090540c0d40036001118070b084041624036910200c2c802c43c070070720308000002e10304002112000401c039018852a192060002030460f60500b40140c06040702840083c0a80841001004c1ca107c0a0001070340e1101050203070040014050b4408165825041e0340100503048410940d101100908040340050b11003020582e840c08810004000411002559464840164250000240445200030907207014000941c0d1079000507542c051988040d254101c9800724104a120042445e01c003400800412440c6014006070f44401c00290b201d01c01d203800d81c0c40c201056100d220264640d11303603200080150f80154002800240240900c0f044010f00f444002002d10414401e030103460001d86100b00002d80c0c41160181c14181880c0790013146500f07000a102440910200a6845500034884c0c0c11055007030b1541543e075001030202c4544500300c13108451503411030000c9507031151503d10035010300d0b40c60700600060410b024030b403a5114500507110800400d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 57873816 1250 57872566 57872579
    0x6040809030309060d0605090c091012020d02040303081815010b03071202041e090213050f03030405040608070806150a050f181e010806040f1203060b030408031609050307 75
    0x5800c5200495071600052001c12015103503c0040c060980941c0c4000c114030707151400340400100c010b040740d828000200800342c0540c0345c18031413004c040c2003403415030a00810010540c0c0240114030226036000e000140000c141a84507600320300411400030354200d040c3c0c40e0414030380e564000c1e00107020048404030040101e0300400021b580c0c015503604100c500329280006c600700f20b0340700d500300071098200155100c2d5120f90002c0c0b0600a48114041146050b4003d2000e500c0d09201c2d103c3d042c8a4007040c0d08980c103076281801528001e00c0080d209100707140c0c40b05181d81d1540c0050145420300d110351800900c62180040001072601300c051304241569042c2024010a070f046401c5041e007083c030b400d17449000d109082c08442d2140b850038050010000d000108204058012390000742c09502c10000d000c04900030f01d4190580551150644510640c0d062041e4041c000a5006124811021041200340f00003030b001144103c8203000045445c210704081a1b81141e4075000b0142c0650100d80c1c00d1009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 57875066 1250 57873816 57873833
    0x60903030717041103030703110c03120405060d020403021504181a092508070311123616050d0b0c0309010b0d060204050a050306010e04120e0306100321020604 70
    0x640508111303c000340307154000ca407440d88540c00440000d840301302c3c6441c03908010301c43c095154a0403000f0b80300384190100b1020141c052030103114403d6400162060010100d0b5048900665000d400302c1124444044a180c02d034019125205164020400c40c9055144910034032642c4000e80740b0098444602000780801c41c0e4000303052a48014000743c0035910366800842001300d1a0300d9030ba40034120320306043c000303080c1e41e00d41401d500503100910007a080c000d0740b116840d9010346102500540b0000812485080c016010f10b503950803400100c0104006502050203400715035010244042ea43e564802e2008510f21700e1400740c4000060700106000e810702200842d04504800004514040711344000b41204881401c101c0c2e034503a000404006d182040c7d420080144011006400710f0341c03400301c80403002840144010f00603010444c00c4076100303002d10b024201040001e402c889451801d0b1200e0310141d1890b0105681102c1500c20072913001061048424a03030949901400d5540c50715a66001e1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 57876316 1250 57875066 57875071
    0x2303010e0c0c01020309060103020a0902071106030705040b160614061c03091a0409060806010605030c16080a080a0e030a0f08090a02420403020913080301090b03060903030717 77
    0x900c803003000310b0405040240083c500500400000d040994910701c104942000c4d05e83c0501849801400140c01144030700c081e40003095000d0f2042940c1ea0b50b84141120b0500c180d801920320104045200c440c403182103555003568501c070b85401c101c4001c40d0919109011800c40d842940840319a040c1c078040b028464441002604c281800d4000e00d8640f1102002d251070100c0a104005c40806d0400460381c890007040010580346000e00010350400e100107010307210050484c40781000c000741e10000701c04e401c808140141d40010702203031581a03c47d00107181c0b0f082a42d08403284c90400800d146040c2c0e001c400c0340d075004103d4031807581c940740c0c00c0015a0700010040002e142405600b030b2440240e140c0e981c2d00804807192060380c040d10345200703000ca1140f04210300580400302072540d1109019041001301e8094a804480c0b01e20310750b403100190001c0d50030b160030007012a0008000081c010301c0070341004903d004110306a59190f41c42201041d43c5e40811140b41000421101862030440c40b50b48010343c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 57877566 1250 57876316 57876331
    0x110f0a0905040501060f0e1207060819061502160b03060111010905150f07090302030304091109030d0e03011802090a0216050102070506061c0b070e03010609110a2303010e 75
    0xd00e00d6440001600f01c6509a00c5440422690700140c0c1807564030880c1c2c55130046048aa02180e44210041150743d50384600980e014002a68081190100c0050304180910000a0f0074403080e42c41d40c51b41105c0f51002c16070707600548542d40c0866524180035240509507420005e69a06503640c1c40011260002d000158055955940c0b00142c0460b500f0f01c40c00401c0090f8100984103410310501d10584003500400080800035040401d100507170b00032007220100c131402d03400852141c0d040240c0042e988500560540d0510800600c11100d035040701107861070703a804074001c0013032a03c00090090780c030311103150095010000713400007401128568060328402681d101101d910001580c3e40034226446000b05030340aa011104100a034603100342104404520500c0c00002003440e41d95100c0794a0014280c070060101d4004508215242580000000d007181c00701400101600300c202401c40d80303c1079030240050282c40c41030001314029104034503150140e43c40d043c9168604117551007000c20140c0302c40f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 57878816 1250 57877566 57877577
    0xa020f0c060108070f050a0806010303050702041b0f02010c050a0504050402070804080303042010020307021e0d0b1b090310050a020702130b010206090610170307020a0305031b01110f0a 81
    0x3640308401c0001a01a242ca08014201c013410081c2254560600b81c0c00790744030301003410f401d0000d40e0002c103034541103e606050468030b0b01074910010b8060200d818440b1039400300400c8038020203070302003590590070860340c000304008400500e04403014415000e508000c100104410081400c1507802050118041e031142c40c01c203601e500300181540c6c001d072015150303070034041a06140c1c041624290350641108a800307208000c00b17528080d4890003007180203881507120410b6900c14140901201c101100700420805819900380f030507180041c01030f078400001c212602500706c9030147d01c008880c1d18220060040c5541102c880b2240c0107840300400321100c41d9028000345005071281c80c800d044017071030350101041308040c090009280c20f6000704102000d610103c2071121180d481c4903140c0036a2880001c420780ca03040051001d2452055980080d0090300c2254004180180030020704008010150680304000700c0908240c207894903c207826409103802c0040082e480d110f1001031102000300c0c03c08 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 57880066 1250 57878816 57878827
    0x906080417030106120c09030209010e0a0902040507050d0b0405010b0306090405101811010c033f09021f020714011e02251404050705070506040c1703030f0a020f 71
    0x5800d450b04281c1c410b1000c40c4034101408121110f41c00344d0b250120b15440e1541c2d406195800040d2641018811180c0540c030100c0031600024140d00500e001a4010b40305000e00d04100800814990200609004da2803501e40d102e101842c09024090480d020300c414981540c880204100707001401410480c0c1600c80d49010b50400c059600552010043c10314040344510f0f001d00f0002000b117040c003e01410803800f035a4000000e90440301c440003a51766030300108201c1c2c400e40c00c2040340a408024480f0500c03481a00c420001c04640c104002e02e034401d035149801400d02114801d640f265034003070b41c40580c214010900595440300307244400e81c08140340c4503d01a80304200700342c0002030300603100016005072400c0c141080d4050445055558450409a039052408401d080d10851100c56a4070958441c80441d150b43e07c15400e40300d00c190800309465903802c10f03181c864410002882440300ea641e030403c01000c4a00b0100a680c8103002d860100040380d6070b12001e00c4001c0d8480848400d00050a002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 57881316 1250 57880066 57880103
    0x2181c120203030402090106030203070206070e010e03060a0603020f010c030806040207020a170607020d0903020d02101701080606090105090403051602030708010903111b01120c03020d0203090303180102040609060804 95
    0x34140c010114a0300503540d281464014410400d41c1604290240b50042062102d10380c0c0c00110b06500922a1501c51040c80f0b0b000c00407503900030160411541072081d41d040c8810380721940e0080c411244200c40b1b4a404500d0f090064401004000015009c10150800188181416001484024130003001c161801d0b0300c9045134030802d2068203680045510510402c00c100f0707010814003014200728140302103a94510380c00294800c3d040200240206072440c00640383c0d50040000d8102c1c1c5105c41809000c660710756142c66aa0141111518816440d6400000f0142030140400e0700803905951b40c503107030100103003006d80d003181c8161040340c051098000000b41d00c8020b10401940030300c03a507542d08049007004d45a5240180904d000b00950300c00c1d100d041c5039613801ca50725002ca0706011401080a01814200b900240101000d446085000200300301a021000c402113100328090f0113440e11640314a0300407404c0b07000e13a005410210b0700401c000c0c4401400354012591140c030078403010240003407402 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 57882566 1250 57881316 57881333
    0x51b03040501020c0601050a0f1707080109080a02070605090607140c03031c0506060c1c1803030305010819020319020f0a06020c0109120506060d03020c040501030506060f030102181c 80
    0x200e0075503680c3d502052100c40c0c0401848080d0040000701c0c0c2c61000a403c00842540800c280d1003000031003130083d0700c082212841403210740014201e050003089020883c0c00c01c1d040c5503102d000b0010040c040c40e900400d00d0340c040d40c00d4840c1314070701030310301810b240f00c41d42c81d1000b00d0541a00c0070018450b0410441d240c1d6420402082d90244154005d10074541142407101543c0004d048a441060140014204040300003076080c0c01408090380104502c0d0015415103c0700d019071002140302d407203040088249a0550019812941d40404031425001189141d41007081e1442e4020360581048084c014510742502d1800318090004000b4403461030800c0001b401c1c40a550300c6503015801150506806603048502c01d00240104541c0c8040e001d010344d5826141d110007001d951154a034a10701d0340500d44208032010f0503100c081d01c104019612800d11a03980d02e41141c2e114800d920081200c0e05a08041c000d444100200d40d20b0782c000c0100315070811110b01c0d00b841c801c01c03c0c0d100194440000c506d449 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 57883816 1250 57882566 57882571
    0x601090e07060206091c1b0803040b16140d02041706040515041101031104090c022b14090111120a0e090103030c0f080c0709020408070806070503010306051b03 70
    0x161000604039418410180c01c00405500031030035508001c007049448600800c0d10300c6041c5903412000041c2d00e141a00b40c84220151348a14480b10f14418044100000e141c002c0d8000e80c0910740c0e0040903502c2c48086c1581da10391484860008003905600401c0489040140503074043c03404016003041e884d0b0b8416410489524001d0705a1b03030154007030009100082c081180c40f0340b84210314a0007880e054560083c8829209441810140e0b41c1040c11035004103881964081c10b48034506010181088100950f122452001301c03020045c51101c903622909440001c030803015160b1240c401c0710341c10850b0f214280d0010700034079040c4150044c50416404040c843c00861441a881c2951112800c4100400400400c2038660081c00c040c001840820340002d203100d00300e503003c40501b8010000d4600017046006120f01041241b15040303010070450820780260003030303a860300f0880d1074244d51842080e0b41c0705025111840032410400050010800d02d40169a22107040100c2c5008544201c0e0b82d5002a4400c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 57885066 1250 57883816 57883829
    0x309030e06210a060608150105070609080c0105070519110c1503040506060f060409020304060b09070e010e10091502120a030b0108060a0602071815080313091b03110c0601 75
    0x303101d0b00c2ca41c0051200b841c1500629092020841107090a80c00703400e07940043c0c00c0b0040b40441c1d1480b01303040c0c1c2c400e208031402c00f50b21071400d01c0200706502c2e080b0903a802507038009080394200741c00136030281c0c40340c807d83d00700c4824101c0e000941c04005006907001d001007170309901d0038001c045603500346803595000403803000842c00c080c43e524030340380c10028281070000d0034842c440c074422080e030340556907003000303403016503244000042ea00d484919016000701942036680e40c00c071041ca02000303603040d0404512003000c0d8081e03d070280a00004010003e6010403400d024010800401c8180035140e01d041c1d00000d581075a004507441461442d403c2c0e0f1164001914100000e600d80103400b00c50359001000307940250f4103540c10b040c020306201006e0340318800ca02480282e0342035504030b01180301c07254010840441801d0600b050090301c03441c80640303981c082c0d000c1d40140030315400006128800e5101c0c0035260344040018200032000c0c5402140580b080029500440e81c0501412030004414884140240703003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 57886316 1250 57885066 57885097
    0xa050304030f03060302180603100f0506040605120a0b0402060f03010f170c15030c0909090c030f030a020601050f060f0d09020406060c0309030602090619020604020103060e0106020a030309030e06 86
    0x34a454001d00144030018008100750801504000603102c500c08aa0031002501c40c07402240d8440000c02e24200e0f4280030b48070840d003007440f20201c1903180e0f0705c003500510081e02d0070701180b5100d0040c0b0080f250900101011070b030202692202007211000165000740c4010002840c0030741c140140000d0760002e8002080030300c40090104144c43d42002032404420000c4082e200c004e42e80b40024080d9100c030010225000c0c030020001c0c81e019400070032550315510061601c0c9180c1000340545566580104041e13009100c0c1ca00c04000b0701c1030010a070741e200c0203280d0041200d603017071074280801d4032447e28000750844410f2041069414100c40a481c80b007140040001d03c941840c0100b00039a0400d6016905001e580e024050210b588591184280c1e5000344002d80d4074200c0e907000c00c2c7d40d2721856032004002c00d039107201c50651541c00f02c3d025000d18000d9800344407043e01e500c1c050a1041082c4650805680301194500001f40a50003189445001c0d080008284500c1008070b40154802e6111500104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 57887566 1250 57886316 57886321
    0x51f020414010c0b0415110a03050610050304050a080c0a0b01080a12030c0e0402030c160507140303090604090f0b04050112050f010b0102060c0c0f030d050105040b040c050d09170a0503 81
    0x30a12100788030500400d1800d0b416000d682d40700e50182850283c0301174019481480303411505180c5402c50910fa003049007800340d4400e1000740c02401000152210f500c507429200e41e403451140b281c0192806141c01c20040d02000c7c5055481d02910313030041c0701942c414010781c007012011076080d4003014004c1c03a958000d4070148115140c940030b40769075480c0301c40074140b0386020500c24903849a0008200c074410313900140e4989949841b41d640d0301892262448012101410f50100900441c1c1c0b00b04503820703000d0b4690500c540781c0406440b40540300b45943c001c0e1041c40200190340040d080031704141681c1c0ca000803c0810b1074041426500241c0021000882c10030030a000c10104021005603005c010008020940310800000e4031450007a0819201e50400700340b00175204e000b8040c41c07804884030411a9640d041d010541c03c0609402d103e014420752802c60002d510382494001c507014640755944061410214402c01e00040c190100160355007208a441c03804074540c503030000e100c040031a444254407803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 57888816 1250 57887566 57887579
    0x9060903030b100e0f06130b0405090c12070302030c071b0812030f040201080402031f050105100507050a02061e0f030f010812070201030f110307110d1b060504051f0204 74
    0x880003036800b203010380507294420020a501015042c0b080c50201c0d1140d01e4503800d5400a03445000c1c2c08080e07450b01040b0200000d11002900003401144c1c010b0326944920341d9555210b0340c0c0d0b40a859454400d8000140c0040d40d02ca10a500844e03214291011300350401c0800c5d2076203510181c03010350740a01d0424440051006610401900d0710511111041900d145013018030b1105060018000a050001c43c80c042000c654043c03180c5c0f034030015820038a030048042c40d03803140040e14080c45002d0240d02c1700c40d08107034428071501c212070645402c54010080e40e0156400c3c450782c2d0744540f088502c00c90f0a16800c1420b120010000c1c10400200400141c4038140000d995000c03081c1a440f0001075403140c0e140c2404034007a40c0a5405503502420002405107074140c100e80580310a10108020348000420400103d40000b241903941c048901219020b2201303203c1903071407010504040c011400e0801e200c01c000f4a041c0c00081d403151003201a10380c0000006980541000b200280003116a00414107200c2d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 57890066 1250 57888816 57888821
    0x70806060c120906250c05010302030408031303020c0607060207020405090309030d0c03050909160207090e0a060b1503040c08010c0f0e040218090c130807060e060a030f0906090303 79
    0x818000c035030052510103044101659202c540140da07411900105500000d90341c1c420a492040514228100d10000c000c214000c04c50a005c1d01103455800311400070805521078425030703120315803104410780740da00c5050707010a03410f8603440308801714426124100d1251315540050018540326041c003585400442c8104003e841000b03003594213030340c800c1c400304005580020388251503c2541c1803501c100f10392424115018496500320702c1e000100f038001c2c006544c4102c80114a0601c1d0b41d13003039400c2c0541b203210b21001e48440e0702c81d000d0740ba405800e030031020030410351004000c0c0400514100402d001811101c903260000c48054522100d2039400b000264420b00400c01800b050703113003000044030780a00140103d0b5445408600440d804a0b580084495406501d660420010032410300ca140c400d84030400303a03001c2040054111000741d0000703000800083c40206440d82a12920861031401003070040603004203021400301070302c81016144541c4280b0403003000794003480000c105084075050103004d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 57891316 1250 57890066 57890071
    0x4050f03011112070504030507170c191505070507080715090501020a031b0209190b0109050307091509150510081504020f2b0c02070810050606210708 66
    0x241d0520700941c07000b04400c0e00b11a000d06849109140795211210202c400d4080e54000130100d1042c0e610100341d647e07040c440c1481d4013400400701e070040d0b9401405d1183d5000c005009240340030442c24184401451518210303101410781c40c0207410300890341c4070a4a000b036039034088a5180c0012505101c20382c601c0e4070250f03410b0a203045c50b0b21014035050000b55600503191002e800c101c40074803062000030040150410060700144002c500d810001c1d4800324140b09a041d480a90b480d000c40c040b5039500402c900b0b822588020090b01c0024034140700d0f8405407030f501143d0015141c004001003a8540300388143c049032a2102e01c80c60710310341080c081c030044500002a0001b4042c07610304004500c00070010720344080e07509a40158560b0204002d010103400382a0810b043d440c1c2d241150b80744c90029810544442050102c14000da121944050740c903015035005030650b5405c0700b401c032482180c85400098001170090841440c00c426040c01144d5030b043c0c81810300c0000c420206204c2190f52041c80681c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 57892566 1250 57891316 57891319
    0x20f04260a0c061d09040302013215011e02070603050a18020d0503040b0a0507020f010903080d090302150702060a05160f03090204060909080318010903051b070801020f04050f 77
    0x54401154490721420b210502ca850100035000c02c044a03004000358001d0304004005d485040103042030316029028152510644070011004244418031005201d4400e036203441c1072804955503220f070303040340b00c20440107940355060140340c00d6608600c1c85511703e00441da90943c9d01400f0b005040c00d000500f51040078150301003c45c2015a222000c804080340c20111035812503a00786c00c811149007607400c40c0210b910050100724042802e4007510340050040400134401c0300d80c004050540c60040d0350202e003c0c08050f0046800703011680071100310b540090b60103400390040b108209409030170040044022070340040141c00800c14816600030718010540c00262f09000080c40c0c44560400410b0b00c088051054101078070f0702c09030020b43d121584040c000c6e110b02e48061050b0304480c1803102c040d600584261425002d40408165690418440c2e031400319403541ea250700e0200c0382c8612030544144144445861301480100050f43c60091000307080541104032910b456034945820094505910448203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 57893816 1250 57892566 57892573
    0x515030103120c12050913050907030213021218010b04061701050a1a01120f020705030c060702010915020a0201180501150609050307060513120b150402070f15020f0426 74
    0x3000100344c4c40000782c4c03000706860300075122040140041d81d84c41c9031125000c00f2910380014030610081c00301d85401624020707280d440c0309a0300f0348480d070100d201c1c1e040702211980c003810100d22074000f07002e000c440c0c80c40c1001c004100f00c0c2c101000501116403e41c040001c030001641c642001e010203028490740800e0350038007001110302c504007000d054405000211704010b00c0803030f012100b181300e038402c9070403540c0340608540f034a400380f4002d95254010400f46e8010b03c180c00014240c23910501a01e07a030079a00150000c5210380d20714152001c2d400c0444040155501d07909072034030507003890a40440d03150043c4e0000c122030f08480e82e04081140c581d0440010052034a03c1841343d86c4001481c00200d030910b190561713132012035000740208000150810b50007541001081b400380110681ca090043c1d0405654501004801c0b00b00412886598001805d0203800d81e2484003240c041421001c908148080151a00001c00901d0300c1c203900c0f64000600034040d4046205484000c40700445131900500004e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 57895066 1250 57893816 57893837
    0xe06060c06040605090109060603050a14070b0409090204020405060a0305040c0b0909060d060605090f09011d0a1202012c07050103020901020a060c0e060a02010b040c0915050310051503010312 84
    0xc8980707a040041026000342e07101c0c80465000e01c001d5000c1d110281c0c20903010000640c880c500251101040c4006540c03c0c01c01c3c22203101200c2001c1920360480e0018501240307420714003200000079141f81c0380c003668002e50078080000e4030744401d80180b04001c0260350018051074030f07150042424000f0b411140f0740090a0000302041d854200d00241c000200f200e0600010f1000d1500a01400c513503002107410202e03042c14042066021251a40104d401000034424404541c940341c0348040c1c0a03280c008950311044e1840045440455100003030020340c400821580300901303480514040c01420007415010a00f0108102107051103080040e19003440c0542c40c1c0150000000d5503031692038000380c81150344007601d4030268020110440c0740790028200340c0c0c45001070b01c4060300804815465a001c3d80c00c207800452402e1103041d07400159020805022440c007003e2034100d500744c00c001c047c82c851104034100401c5c3d6a507000d148000d01c20081482c4c41d40e070340c1540703400030000448038211818010551076 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 57896316 1250 57895066 57895087
    0xb150a051204060207050703030c0c0501082e05030f03090913170a03020702040f020703020f07052817070302010909140103030503070216170c0a0b090105030c040e09070e0606 77
    0x300c03510001150503007240c03602c1c0c0381002070013849003a000034464800e0800000426800a041c42c9409000740d0f80c50a60720b0340c400043d115120b007280e9105645000c0784005010480020f000d92000c10060240280b0380e0321000801d18003000c01030f15180d25400814060100c0c41e10042440e03000510700e02c44c0554000503581c080f4225265503000c1c0101c807004c0344400f030f810312a6050f46c468580080080c404803080c4000f480003544140c600744c0041c0100c01c017140b01074030005410700445d100640040342c010742c0c0641c140c0c4110314102e000300c1a41c016450000e0384403c03250702c801c00d200714100585462031452001406040e9244e1110006c20f090280b0303859543c400048450441ea00740c24810f83e01e83c1c40c0710089091400b2440d00080c8a480d114010420000180c2011060401e04048800a60030003017001031a0b0b07803d209080b410801048200d01c15413203100590341010803440c0403401c2984512221405010441d00303000c1ca40e0200c0409c000ca0801c0800c081c1d0068800d0318810b280c08101d62 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 57897566 1250 57896316 57896327
    0x3090f030f0405010302071403220504180318030b0109062904090b01050d150303030f020f03062e02010e010b04091a10050a060e09061008040b09150106030b150a 71
    0xc16241403550110707e00703090140b000c881081da5481202a250341e040b081c1d035842003647c40390f002c02000c0740300c0038000300e0305042ca48144e00e40c802a48551503080030a65030f0449000114a404000e48aa180d000000191913248198042c1103046008a80c02d4103080d07403207080c1301c4a010404481d02d1120b20b281c65958184048400740c9441c5070010607900c83c0c5900598040c403441d10040703409440c080308815001003041b001c00c141c0e03100780d405210030a0305c500800d007a0301400150f06200c40081001c916a840c02513000c0c0d100ac44410f0a4100c140404030844480224861405015075101d0000c50b014110030311901c50308240440e010000341c000340e00c1d4590581d12050050701011824030119001c061030fa031f40140101002029420300b0f94a41d10014050618509180e00031405440400c0061810f2034541010501c91794407160f55547d1526850150000502000c005028480207031030001c0c49000380070b004c1d03c0390742c5000c107c0007815014000fa07001c1289050000b0b4006124102a096209 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 57898816 1250 57897566 57897569
    0xc0115030206030c2208010c090b090105040509060310050403020d0e011809020306010909060609030b01050d05120304080910030b1207080d110708030301030303051e060d06050415060b03090f030f04 87
    0x8510140d00d40f17030303041610b81c000c0819003280b04508001000014504030150080c0c2040d4010741e40c1d0303032880b0381d942c10350401501400140b1408204148020b01c03035401d0810070707070f82c1c0600024100c070b9880440050a408458083e41c058005070400b01e0711080c4540c220303018256401003881c10340403505801c48500b03042c101a0003084101900000880d070542e00c10180d4202a040242e02000038640d02c41025142c0000c80c4000c03100b50810400005052401d0300070360240d941c1010141c074402d012445c0410940e40010000c0302d82203814400c3c00556129501c0e252142800b6031000a4421040e1080095034001d10f188a201355000040920240700041200c1800d41000d0500701c47d59413400301001d007400c0c4d00b9082010b00348808400007080c198590441406a03910807100303440e880c1048044030400104850b4a074021682544070000220a64082603201340103002101919246624000699003150300c8040b11440202c01c0c400c064100341b20381055a1100ca00a5142101e21400080350f400b45 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 57900066 1250 57898816 57898831
    0xf03030c0c0f0601093908040203150109020d0612150c02032b05060118031203020d0c020a020f0f0d0b06040914060103060b0114090d14010e030c011503020603 70
    0xc0303020140311804102082541282c102039038010360312054540010010782860000004a94130306008422a0784148250b04402c1001410306e821000c4007a02c941c0d0019008a800d4442d1417641c2410020300b0902c103020305448000581c0e0382000c100c1d4172094859a0700103603810006a070359200000c3c00503c214080031500704c0c000c1746000807540140d0850203542c4c00c00300d0001d540c000a6101081d905026000c08000030340c04c02581e05c81c030004403032030001100c00c11700c02410766806002080000c8121801c00300985005490074a1900f01c11084d078000e1100400960310040c2081d0852501d0401e8000c0700d00141e0b480b145075000d22000840384c5c500301002801b40181180030800035282d0360810f005403608844d110600d01c800e101382c02d50f02d000904c41541c550b45409074050ba11740c450101440c480e0b80341040241000503041c104421076401d188201e58902400004409854003030166008074204d6501864546002c1c072447c7d42501d948580380f9208002d204003d00c010b0b0348050589800805 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 57901316 1250 57900066 57900091
    0x303020d09050f010e041505060d0209030f06060303250812101a0d0f0209030f060f01080109080405040b0f030f011d060408042304050c07050d0306140d03020a0f03030615020f0303 79
    0x1007581400907d0f0b8481c1c00080d000700d000160084020461f8004013041c80081e01140c1c0c0c00d901e05c03808245c94131029941d0a0345900100189455082d1041c0199010000302d00302800c036008541c0c400703420380c2c40b010004140381d0580003001229168100f1800c020010740001901c8405100d130312004520901c0f04010070140d4600344d040b1881c4496041d2441102e0150031951015921070095654103001c1f640701c200d500e80c4e2400420501d00c10b004074010543c0c489120360801b4246003c01000d4481c4440c0741e5085413060b103038100c00e9603040006c40a400b01060000074000009918103442d84007504901101354820070a00000a5455044604407058401d002c5004240c0311840c06c2900941032030381d036100d030400d0217101a9003039100051111503c9030781240c3c010004001d0a40a80b0303154403848000c0d40d003680c500151800c04007015401c0745e00c684181d4050012175940c104078071303210810a40000b540c0d083d050000b000c28096403034030200e90b0300080120866801d51140c7e20710009140d03213a00c81 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 57902566 1250 57901316 57901331
    0x31b02070b070c1706010e0a1401060804050a0605070504140301020f1801120204031208070305070e1203070602030c040f0b03040b040602090d020405090c0a1d13050c06040303020d09050f010e04 85
    0x49a00c0769103000c3c0141480b44404e18050280050ba102028050800b60b03100303420100d44185070f50311440c100c2e5061a00c1c0c070201030b86080300580340340364014000e0b2118058880b400c40061658401d0714826801c0740c42d00740c1c6660400750f120840c5000e840740b5a00076841005006060000203040d54282103809136001082503545c00101c4190541260008500340041000f0042042d0000d015214419070342c2c0d004000d071b90789541101543c105031441408150500d82815441c181206810840702515048030310301507280d52204100e900483e98002181400b01d020f0209004403c0900010b00f0f10496107420b50501e03407200303800d42c00040c0c0010402a0300003109040354071071034807449503a9002402003140b8501a001281c03203210104181c0c0c440c0400410100303443c3c1031849041c0c40e40040341c00d0013216070b0354800c012000e01401071059400384104e203504006940c900380140061031003580a03006222503032902400c0074025030440b6200d0100d446980c50281d034090040388444030100d4002c19506e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 57903816 1250 57902566 57902573
    0x307030813080f0c0102010b0109120f030e0a170d02030304030207060522030f0c0503160306020d0f05070909110306100509041e060e0c0f12280903031b02070b07 71
    0x100d21641c002403083c020040350361480000410a103041c02d400780c0003400701120000c011074152071103000f94803074100418029004034507003c2910040e184281002086809214000f410300a940c1e03000f100e40c2c1440080040b4602e00910801d81200c45a00096041d4202594040c0d01d03002903011350b40c100100440c0c6140701d0040c2c004012600d1203140c080c010000d49908210a155050301c000f0768031802d0440d4001202e040c00510084800c984100e0843e605e0304580c1c60502944c84408020f40302038a07050303000f040c480c1034803070540103040c10b0315401c6800e407078600c205042d03c4a0307140b2100b60b14014001c02140703440d084295081040c440ca03046941c0d050280000e0b0042c64030203058801050540e60045080c1100c0e40f00c0400e42e0031014003044280d0342c524440c0c0c3c0c3c1d480782c00c0710403100010900407208101405c68441c0d03005080c041010b40100380b450f60701882003607050741d0320002e16120380c03884003415018030620b0007520035403101c6100b0f41c03407414019540b03240781d10070b0b035140e030f040000c144050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 57905066 1250 57903816 57903847
    0x209040c030c090b0f0a03020319021210201801120e011a0102120c0a0b040510020d0c030b0102060403020c0111010f020d0f06050102070e1306020c0604030306060311070203070308 79
    0x14660040c850b10816440302c103008004c025000c03400e4020003d10700b004540e41b814410078400c40b0380c010001d0480740c0d1070174038110a010803c401242c0020003044110703290f5405000740c505511182c400050f40251001100361003040ca00003410700000704011605070500705000c01d02c500e030800c0c02c02c901407000e600d0241008140320300c1c080d5555481c0400f1001013401c3d50f4650110342000f41d003119140650030481c0000d0344036031410581c55600266072400000c0250080c0380c0e01030f01460540f0b5428400ea24143d059920032034a420402d030344d4008030204a50184a441410700080c80242141d00c2d1580c1c000c1c0d034a4001c84c000c0c0d814050f91110450280714250403041e001c00c2ca44800b50349034804200b1303680140004401821000d414a2804039240d48000f60100442d00044402502d03903d4016041c80c501e0b43c21803064469580800c043d08403484100546401079101e42d800060345403400c1d0005044078aa500c1c5180038030801c00001c3c0251f50300003120310a980d00441c01e540e83d070102040c3c40d0031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 57906316 1250 57905066 57905069
    0x50f010501051c060902120102070b01080609030c060105040c0c0c0306230f0601080a020d09030c12110714060708040e15040b010c081b070305071d0601051804091502130801020a0c0209040c 83
    0x21f581d80001000e204111031088141d04030303005041110002d803100b481103501d0b4040e0b0132160222354011f1004200c18501754120300e1030ba003107600303114000405c1511001c0302c0043c150025101242c0741c2e8010590041120905001165081c03484040340c00e112100501045020f08640c0c10042031801040100c2c5669041707550340ca140b410100013000180c81c0180101d1840c20040d02e400c0b401c04800316a2034010340000030000b40b080050803181b402c001004030007208000c4540d030806004c2c07044500007881781c00100040c1100602c8850140703881c40124828610b01060103010b5801e004145400da60800714440150b0340c0202d00f50307110354860317507600b98520601342c820100348924000001031000103d4441e042e60b441d1540182a0501e190411042210a540007400030380304028010031090600c41002600e803000304040b0b4503100a86402d0000c05102c18080303100c43d800620303401d090b10002d100e0030007048164020b50400203c0003004c1c1c11a161600c0290003014008002400c00228604410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 57907566 1250 57906316 57906349
    0xc06081f030206090d0204060b19020c06190f0c1b0302030c030106270e1c020f0f061b09030d2a020a03290c0301030c0806060306240409050f010501051c060902 70
    0x1912b94465007541040000d030baa44000142c05000e0300071030740e410008225445a8810699403000d01c81e41d600880c1c0082c1559015070410110544410003d01c1d00c200d00341c5205c001420040c80c0d141940101814612520f0703581307200f68542681001140f91618401002c42c943c60320800322040294201c40c0030704504480e400190044900018042c540da208200c1031070050390890b09108460402596034103161600e409065014800050120442c500c1d41c6035041e880c802c02d941454916000b0a1910300f00e101d1032808502e04c051915001a44244103032150280480c2141c1490301a4021403c1040c10f07000207417101c1800d14442d4080da5102961000d00e01c200c500c00c15003880c6c16280345400f6042808101d400c551508000a40c454002510901a49000307015242e907444d40351036082c0c04112072080840490a10301e80404554451149070032503400744002d08040c0c3d12045031306084440c140c004510a0064070307044845083e40f84140903089911001c00038120210b170000601102c1c0540081 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 57908816 1250 57907566 57907589
    0x30209010803030711060408090910030b090d0807030b06070204150807060504031101080408090103050403030b060c061e092802090c0706050105030309100c020d0c06081f030206090d020406 83
    0x10311000c1c0040158030503c41d541d00d406882c420007034840d8032801d0030350b030180502e6018031030b4544528000c0c03811034001c002c02e20700248c3c00755250380351110081c08132a0240540c0180c0d01046000d81c020484a52101940c1b404100d011050400175843d805145000b034056544c84030340c0301410552202c4100035110340f8046522003030f0b544000803c981c0c0180001c0b600074015080d54282940105007842c0525400a202400d0008500046000781302c01841942019160300ca525001d455201c000c0c040111141e0103450a40307800807611051071101030780d0031241d00c1042e0030800002c0000c212212524903903c045c8410341e4500c61a0105800e904901075440803207230050203403084034030008241d054030814003402240c0c1d0310001c050700d901030768a03840d4002c07001c0b5002e2080300788142c02c8244005d00c0240441c81a01c41921258010046600203201003031f03003001440b400042548030301c50b450020848641001e41950b0102d0094012021000d0040c410103c84004554490f04144054550580754 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 57910066 1250 57908816 57908819
    0x1203040503071b080c0406050108010603020d06090f0c020c0a0b03070507050f0607050d1a0a1707180204050108013303020c0d08240a0302100c060e060610030c021b0a03020901 77
    0x250f241c0014180310310880383c440e05203074100b03600b1303d8012101200d10503100c1110076807030040103034060351043c440c0202040c2c0d40c03a4040795001035446900340340b8550210010391922840310191900840d0860f1511502d10f444040268246000849034400e0440c5061900e800300703450824036000c1028083c18050140c40c0030001c429501c500541982101c40e8014807906200c030340b0550411b0710703007450315400844003402801140060700c1c070794615983e0312084481c2c0d10341d01e1070019041da48545880410580019041000e50f92210940d0301400e8441c40031200c2400250414098905440444c2c1c6c415402901c0080301c980282e0645034480c0c0e4180c02c0d290b800040c6080140b0b54601100ca00040e4401c2080c801001c0802420384810110041c210010560440e000c02c810a07018000080400401d06440381c0019298050304001c080804014403032400c0850410040b415442064030806192400d110061980024074100110a01c403e0720b6103074802b200450101c11184c1c0001e900301d40e04400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 57911316 1250 57910066 57910103
    0x90a02010e060c0f100f0c02070501180504021206090906160e01030b030604141204080304030f06061205010c021c0807080403090b0a1d0d021005030712110a0809070503120304050307 80
    0x2c85c01180c0344810010011075000c1516281203829041c904c00042c0e10040d410f00255004a0360024002c0f940505000781c0750781d4900190030382e809851101499500442800403d06001481c2a007010f0524003034a01441e246d03900d951580c0040711414100007548c02c00e4403050b4000d03030208000031006019a44107281c0350411840400200d80503941e58468200110a03030203c030002e0703c06035818140690700d03041c03840d15440a0240e101d0382c1500e000d03a451100203114810b503481c4a00c0345200b680081040c080d11000603041250841c04116001c5409000360600c640c041030310f50f4000d6107400c04e072143d52a141802ca0b09030105400c101210900065000e0703000c0c1e040309144e01a0b400321140b10a0b46003400051216100c42c1d808000d403c00d080c1068940c44a0041001c0e590212940c58402c0d03111914014030381c01e40b10310441002d01803170001943c89a455204580030b43c030244000c001c1810340c3c500b0000c60340d14881001c400409600c040086030801800740105d81c04076800c10700303501d1001008603 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 57912566 1250 57911316 57911323
    0x602010b1003060b0d150503030c0f010507030204121202150720070302012c10090302040c0915050a03021207090e01120b06060913050a020d06090203090a02010e060c0f 74
    0x508892181205500d00d24501d4464050380d410f8440d80d40c541410a8050900b0034060043d103c0b140d0400007072071390701146507103042015001c82c1c00c01c00020010110404032250031a00040e040d0b00c2054010030050040c044c0342d441364000e280c1c1c0110a208505139250b0201e080401e031403c4074a096800000b44162540c0c03100301b800c1c640a01c040c24403d81400c041c040d50396800d0600c0f009010509098042514044c2451405401c0c250620403840c0e403160400016140300f404040200464007100040c015420701e413040941004260400041c0c10382001e0324015420791804080003044400210500301034401e806a48000d202e04581e481c2909040c03402804682590003182a1449a100000b61031640d42c0f52034442e850300564900c5171a02c4403014045281e000006c829045500e08440d82c0740400648160f0340700b252503400c0181c586002c0350007101520903541c00015664014414800410b4020845080c5103a090030850110694000032524138010380300248500d000b2112035400441012 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 57913672 1106 57912566 57912581
    0x7030b12030a0302070b0109021303082203051b0d08070f03050c0a0b01050118030309090902150403050714060a0815190801090203070905040209040605040219060201 73
    0x10300c6554550340c004a6001e00107680003030400203004146015901600c0f00c1030003036282c5803900395600d0007170155020140090ba80041c401046900000d443c0905004842a90300c0695503070800039299044000e034034030720441034203080c0141d01d000c40c14401240c1d48002400c3c104101d03134450b03140c2802d2111003102485010011131561f05420000c03018a02c0c42845003260a41c10017000600301c0040244440c0d54448075802030001a8001048006589110700001200030190000854600c3c5c100c12004d06850009004814450042038800640e000d405000d5516405a001c0c0f012510441e403900000440c9980401c4040c0008d15420310107590040c40c0b40100300007103c07030154410a40c3d00281a982d900c99a002c2181401d11140000f45482407081110385403a401191801c2001000101060381c0c0c0d90001c3c046640d03003000307109003940d0740d880546240d4440401030300902c1c45 = true := by decide +kernel

theorem cover : BRFrame.Cov 57733816 57913672 := by
  have h0 := BRFrame.cov_init 57733816
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57733816 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 57733816 ≤ n) (h2 : n < 57913672) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
