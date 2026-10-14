-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0117
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:55:35.914982+00:00
-- url     : https://prove2.me/submissions/95264926-3540-4971-8d8d-5ec1b35e7843

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 20863315 ≤ n < 21043171 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 20864565 1250 20863315 20863321
    0xc030f040b0711030a030c0318150f08090a03081902070b0a050402030c090601141309150302030d0504030f0204050910090501020a0e010216060305040516080318010e010e090603010906050f 83
    0x9640805908154090704696800d1b84e801880824054030082c2800074030701800104800f4821910301406001070110714105111901404e07600f00311034603000003048000001e1445030013054020a00d40c0c90349a070540c0d92500c40030048a2902c03003810354080c590a0017140040360185a4240c01104000000511801c0500505082100d9911070500915112003170040f140d2b88034100710541039204101549504039010020700101d8640e00405040f42084101d42103d1840c03000a81241e01c200d0131500c440016941c107072628041c612001d001d40c01880c0c41000942000d0b0071103588220007100b0b446021801000800481d171491400344d40c182c2d80400c60710f102d59023003582c3d059136207402d000030300d00300c40c40340003a40110b0704a005041c109070315800401e003004000c001c0c5900460500b03444014490712010740c82d960f13402c024403240b01d5401040c8003084650003180150724041d0182d41f54808034503490b051086114010342155099076071400d640d4081003052040c9070080492103d00c2c41581 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 20865815 1250 20864565 20864573
    0x1107080f0322080a0f0c02090601050d0f0905010c08090d0503160c050123010b040f05040e010b03120703020706090b07020d080d0c090306110c1e0703080307020604050708030306030a080c030f040b07 87
    0x2c2e885030b140c0d500744806c2440701d00140c3e90702c6403411342c810424070b402548c44030448103c002600b680c00034650080c0c1484041010024190814841c40685c1daa8030369255032854806070740e4003074800c02c3c0c402061042000c01d1041d55400544a40040c0908110240039440d9031110708581c042140d110380030041c13151072313115070700409816401443c6440405041a0a101a511090f0940d103c0c65126940d14107011074101000e422a68082c070f40142503c020403001c3e10400c501d98880c240840040c0903044010503a6405121800c3c15075400004150801c6402d0b409d101101d90480c200f80c0d64060244015a00d04416009440c1d500c1700170365a000c0d0161861820406a40e150704200d052006c003030003030741c1103417200042d0004040242e02c803507907002d00340804481c1011101d4001511800b4004100b026160300001e12900913840350044a07046036859030381c0e644a01081d1402503041d0042c850b00004100380402410051030400d00366071400d054010342000d15802a404035003941000305282c0140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 20867065 1250 20865815 20865827
    0x515070816030204081b120a03050a080601021504080a020a0501050a060504060509040b0f10030501050424050c030c07030908060106030b0901090203060a0b0d090501050c0d1107080f0322080a 84
    0x807240c0d03090941c101801d00008a403110b00c0c08103107001c0038005040030030f242d40da02810201100c00800036030780160400d09004060380e00c202042d40100310f407000800c0d401c2d4070005d2102003204900c40d044580391956030707540c8031f568046000e070002c41c0300e2008400007050b020300c9610b0150340ca100e00010060f1401c1c0a01003694141e90283e03209003a032030204008105521029a0b20440c0701c120314886907160350401d40100301c1900003801640c07810040008101c0500d0f43e4084205410028400c0d80f2705189940054600803101c00f8500c01051000c24101da0300c1c0006400700074441c1c2441d509603900c0c2d800d2145001000d0340000c0006e0385035003500509007030195400307001d42401070301940780d45000d801262146100c0d100e10305012034005809840c2d800c59034052960b05078400c000784180d00b0410307800300c190b804c0780b4070040c5c0080c5002d0351480403076002c00031200030a50040115040c1529049401d03040d070030043c40080700c024030409558602043c12680e505141c420b81d000ea448409041c030003440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 20868315 1250 20867065 20867101
    0x3160e090c0d0b0106140c060c030109050f06030714040209030105130b10080a0206091203120f10031e06090f0803100501030c0509041512080702090a02030f011205150708 75
    0xba29071114a030042900004040c1c15138400b400c2109000d01c00d9503072590306100d04003d00c2d460f40034100c18005410316060086040700c00500c000d00c50394407624564031460405491143d0b2540c4054400c0020b40b40030303a6514240000108018202404c04c3c3c0860300350f0703508480c0ca4914200c2c03040303240c0030442111040c84d0000c90011101072000e0501040a5540d541c180e0f000e40b040c0c001146410032940c0701c407402049543c544058030744400700c50302002c00c1a10250b3320442c182440c030b03000482c0070030324411800403240c2200c0f080c241240b401e484c0c45107101c440202525019110072491000c1490002d0422945c1e1241d80c6403a62403405403591500c0f1030041d000f00d8109030800b00f070810072a60150603a48211070454002030005100416003184100b1030340000ca0ba050a41810800d0003480d00140043e00e00030344014005a40340c991840880c0310440b4003500503412840103000011101081480b000c0c400d10480d06120400544003007c0c0800320740850026001c03004202030845d5400503900 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 20869565 1250 20868315 20868319
    0x3070212030306011407080f0c0a03021b010e0105030603120712030b010305060105040303032c0102040905090102040b04120302030403051b040b01021f020c0307021302090a0f050d060203040203160e090c 89
    0x4294145580001c00c0c4005240385c03000c4103075001c180802030040305000c075000084c000c41059590502d8280b440d440d10b9181c03c1c00c1d4094001c85804030394201403e090b441d00348805944002004841c4001035807a50070261916816200703041d030044007003903000010311859010301c004c40c42d80a004000101a41c02c0c0d41c02c0c0504040c103000902c141641c004e001c0d41c4c00e40380d240c01c010900c41514000407003003500b42580c1d004003000c6500c1c01d8828000c19801401030f83d40c8810103100e9640c810881c2402d038030070b13071243c0440d03004200b1040084200010070700e50705604c2031060b070785051ba89440301d0f483d22a50102000c0040c01032801c0803e00d140500c10441299001e001034000c0090308410018500748040a065009800240b221207200b000e0045912440d4002c004950751912665113900a40080c4806409107043c0f05001c00e486070101a100e0443e0700040003481828600d07031302e80019400c060812038051041a00841400c0003c00c4000040c0041004cd1030051600c82902c0c1d01d8480c02200c5c0c54 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 20870815 1250 20869565 20869567
    0x3031f0f0b0301051c0b0402010c05190c050307080f0a1e050102040b090a14091602010e0f0709060e10050609010e060304060e120a0503011509030503040b0316031e050c0d0c020307021203 82
    0x2000120301c9612551f005409080030502c0c2001d40c24100d003000040540001c1010400c21132808015203106072030141d0320160304407107030180c80314111541c4d041d1084240a45500000000300016813070421504002d2150180003401c2b03440742e8070b01e801e98006800980c4100e8012075140701500703103c524240148503031000d8400e204000804114844000743c0a40c901608201d0303a84200c41c001d400c01801410550f08540c00d40b0b4581c84406d48440e41800758a84041c04d00500050403140c0c0040d80d80607400c03a50214071000e241204100d1141d000e2a160343c1840400e900c01e403415901c010181d4402c900490004c07880303e603601c02c05400c140c03c60319a1644540140319241074290f11105480c15101407010000d80080704440a48420036150720092a03448001000b1400d41080b20182d0300a0004020f4410040d0325a103040d030580e40c0c0300040701d9003408880000e80004d403040d0401504003d041c1d40303440c0b8042c000c0c0300c182d041c2e4852100c1c000150f8400a86042181031540c0a1120f03250410059 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 20872065 1250 20870815 20870869
    0x1020403060c08070c060e0f1911010201090201022a0607060c08010b040b04030f060e0115060315060c0305090d0203010f060602100b0604060503070201020c010207030f0e0102060903031f0f0b030105 87
    0x40c0c980d24000c1e074040d0142c0c0e87c07001c81d0b051050040000f0060a1840411100480c001c0d0780321160100182d01c04594002454004c4503441d40140911007040c2d90580280030100c4070b0188071000411003c0c11749104d03c5002440302040d840e000003c10200340280d001165034100c015010300300001c1a8001c49c00311404200c2040351012030021354041d240d100c1101505d0054904255000d040c0c0c1c142c804542e54030744440d0420707010484038040c0031a003080c1c0b418800080312a2082101081d82c3c4030307000104540c2c90400703000070b108900603e88554003e01008680d001500440d003168403c850684045542e0427040c01450f80420881c0b0b8000143c0c0d005104171070310718000c180a0b02071442004140100400481c816034000e40585a11202002c0210344959440c10010241c400384070030503010446445c0328020a51000c5031981c42200044001c524680b5289001c0782d0b201050211b40c44084040c8002044a01000346000004c0c003c2c6c1c6103054495050100f00042130769400c62100005405900e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 20873315 1250 20872065 20872067
    0x70e0105160206040b0307180e010b0a080406180803100503030715050417120412051222050106092406020c010c02010302040b0310060f1106060f010201091401020403060c0807 77
    0x44070904854518080c040441c03074030105a440c0940d4014520b440310100401c06c89591150140385c00308581002c8540341540d079403d000c1072050070300800406410800a02e61000d011312a496001072040600054043e03010711008505118440b040f6095800001803101072801820700c00041d00e4114051403400c0c0140e5210b4000c000d2103800a14200c0c7c40d0000107060090348071040d0318010030a04803a544504880e101c0d400020100d900f11940b20f284403030000ca00d403060040d206600f04d4000750214036142e000541c00d41c54800c0d8001d0120308401512800003580c2806641d008012046020036120b40e000da100c00401001e403021005814121010010315600040c3d00010840030309040b0601112400100d01902c181d4210040800000050000380031003e51894200c1e20340d40e031001701c112843d034030848010140058141e41d5a002d440410207528040c1514540308805000009403604030307031b50b440d00341d4815201c46001a540450100144240741c00362060003a250325003c0c042e0724002300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 20874565 1250 20873315 20873317
    0x90f1208040510141f080a050709110906090d0507150503040506130201020a03050a1817060114031b0303090406030b040507050109060504090b0301090507080c120c0109060c060f090f0209070e0105 86
    0x8140c80d04c0c840840450a1170700342c03610708400944506020340d00500c0050400d81d0380c0e00c00901c60120514585211841a000c280f0207071490321800502091806440e0002c0040603001740000341d501e40110b510000e11191144d2a0f405a080ca54450ba0784a14041c02c0640c104200102040e01944a42882c000181c1c1d012898030101945030500a4451808440444115270460300e0b401003680807280200d82c540c68407030f00151800d58002202c0d507e070b8903007820042100c030340081d954169000560f00c2c4602d03040c40324580c0c209a0301030112400c02e0b41d00300016080c0c800301d07072043d44e02c05080002c0c0000e2007070610119004e41402c0c02c009071110300d40700b0001c00920072882030004542d912301e501816564290481140240c100c4202c580440d2141e04403610b800d0b90110080c82500107030b03104900080049884060200305848001c1c88902d1700b1004c0d10100702000c0100c404942c2c4002d803043c014000d109200c15140203240c8410b041c8940d01c1841a0300e00b015182400b448804c820142c41c50b030b0f0100c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 20875815 1250 20874565 20874571
    0x108060403120b03030d06030b070f0504060f0c020904140f0606010903020913050a0b060406050409020a030303150e04050c0405090a020f0f0102030c07080f01060b1309090f120804051014 82
    0x120b07024248408841d911001000c1001145626010004041b1440074640c0c01120682e4003540110907903803100e40003034440032009800100810421703c0308200040c000d0440100756005402d082d10170700110b50010705c654004a4044840c5c1106082002403110208805212002840e004210501705040003030714595030751000a2041050a00080b03404584806590380282c2c0901194954211403409001c83d0604507001360180d4507101c80042d441c54503000d400e4a50b50003070f041c0f554450031a01c3c00c8010703164004034800000c000410006000080c6000d080c42540250050080314800740c003000b0030343e030703010b00f001900307903c02d070b06500160341c444415505e10719080b2040d00d848102c0100603403d500402208ac1d000b40281c1c080084d01500114034411540c0001008000954071040350b624940169036035041c3c042c00609060282c0701650323000250fa980038000b200350946c1240e61702452940c6148403540069440d0041c442081400c004542c1404a0410180310070242000b4800303c00c00c0c01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 20877065 1250 20875815 20875817
    0x50711090712050403080a0b0a051305150d06020a02160302030d0309050f1e06010f03150507050702131401080706020c0613050301110712030606051c06081006030203060a050108060403 81
    0x90000301d4922030140d10218154180341005200d180707441d00303000c1d1105504403185440541420100c3d2a45e141c400908402d64070000c0409101043c1900750704000d00004044200701807243e800d0060654680340812070707607440f0342409a914000444000d007881d0b40780c42030007807640c0140020300c01070b0b4011030503803544551842e00040f00081800c00c0e41c03400e002c0061800e03150085080d01410650300c9002440044144400c5550f41d0342d03102040203140082c0c1c0320180585c0041c04d02689400d40765001103070032104500e00581401c100d070300040c1085d107031500343c1c040469403000161880b131500c840f228010b21f00c0c0b40107041c0d000e2900001946540003c0030f100e02c28240060a003100360700c1c2040ea04042d12014000f005031110704610702e206c40d44031030030607110040340883c10f0090a01c00e00544003520800e5980a0030040507488020704480303100b01d0003240c00d454507000f280e40b00c03041012803a07100f0a0000450301c1881c600505052000280c26440316038140310040c00401c80020b0b200c0e4109600d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 20878315 1250 20877065 20877079
    0x3120c0203120d0e01050f040f02010c080408071503050a0608060c09040204090f0c0210020403020a0b0904020c06070201020a0e030111030403081003061416110601090509030c0105190507050711 85
    0x11610000382400e0715090040114440443c0d0f030302070303005940d02403c01360801e08000c12050311200c00380b05012804580050034140c5c1d08a5103401940f00fa602da80045200e010343c242841c1d2507500380b90030034190390090711003a54101c1c12040601c0d81801195040014007400304034184c00e051f2060340f203c90007400405600d100054901158803668102c9008060307800c03080040c410302510340c03400b40071554440001849040710200001b9107500c22a0b040302e500900321980d080c43c180c02c030600d58101401c4a5440740d401c0c40707208c9450500740b203002c2c0b04a1659000582c0e4141c024001b8046d0540031012034000e80c903050408041d405940200c0b50010f0301820581140c3c0d803100d54103d5000d1440d04010585400c00d00c0802419072909007250003884207100c40c86c5440b030001030072107003d003400245c81c009503c144010098607242d03038270168100c00b50740296458407801a44490a40384250341c182c0689112103905a04c0704001c0c072840d50890040d240161609034a41ca520300f8130349070030804900c01c41e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 20879565 1250 20878315 20878337
    0x25030804060c1209060203040201090605030f06130f02071a0c0408120310080304060801060905040b060306040b040605040603030e031b0109090209010201060905071205060306071202070203120c0303041104060312 93
    0x10168150403c0d01820320b50030302100302246003c402035003040d10105d0219107003400108400c2d002d0300c10303a807003522440c1c0001c0080d0340c1c1801304420301140c481c00200b1542d03114000345004550780000c5c00000d0003480e45c2d20545c1203000b07102d00aa07a00800b0b4048000040c40244108103003c07803c02a0a6240c0c91039a4581d03e0711487c000004926038000c684620000a00041d926000096281259031548a0184003a0754505000a84003443d00035584801c080000645518040e40280403000c8060030005001d80caa80107c3d088900030b0b0402d81c00b0405031243c00040d40b40811181c05901c8507901c1031002d1901c3c10b40040e0034001240540e5200303a8000c204400281d1007503000c80020074900300203104504128070084c10440a03028503c03002402c10000074080e04002030f140d80039810366035503c0020107030802142c0094108540c100d07858006d0285ca9003003a181003001d08103070081c2202566a0b41040d1800812542201c4281400759040c54410070100c0e0050b080c00c040c0038a2800c0601c0c0e101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 20880815 1250 20879565 20879567
    0x3160c0503070315050c0403020a0605071a09030705100c0c12050d0c0c050c03010501062102040509090606030d030e12030c0c060a0614010215010510020307060c030225030804060c 79
    0x94290000c907014891800000103000d44208901c0107049904000c0140c2c3d143c580300c0c01d106201d2804081d4000700070700000c0140134450b10003880c105010b0702010403c40703080b02000114140c2a5003105039030340042000d005000c0280011100e0741001c41040040258501001d00640304140780a02858100c25000712841d00031000c854000118407010805111903c1e400f0b401282d80f03603415105440780055022481c1414492641070b2890303a10b035644030258001d00c454503010f600e144111925020700c400506a00c900b0a01d500400d001d902400380351500c4000d040c6401100c0005804050030841c5000301034070040381d400980c180365400181d0301d903035481a0f02d0151051400382036042c8a1681080140141d55000009a07a40e182e01d14603031550701c400480e5030346448100401c03040080001005a89402c0c0e07001e484850303060058a06080d201d403584011551803840e89004281c00184128908829103503003d50040c0200c00d2080032809a10000d069240c0140b00500950342e91010510030303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 20882065 1250 20880815 20880833
    0x607050606060a1b0c17150109020c03040506040b0d0b03031305010507140a0b090105100e0c070606031a060a090608030d0f0618090b09010501060f140d050108030304150506030316 79
    0x4d40c42c00d0714118203401061801e403142400c00d1007100740480b66904000c1c01c5640c082070b00344520300c5050380303080281d00304a60351000350300c11003540f0303418801004009020349620000e40020b10807011204c0e190720030301950300c00303a034048070409201390002c2088040204102000754191002842c0031a194481460f001c0c886801410f5944c07101d1055402e0075040000c400c1400d0703c540641c074024052070701c0d44185010300070100e0242580b407965180006000172005809001054010000410090754a0307e5410800c1e100c1d541b00111a190041003001504012000c00b00924411100704281c610708807825840c0d01492440c00c2c0415140c02c0c0307940792029030390052000b91000003925210704d207601e0038001c01400580c5040f12240c000c84009014603030b06102d4141255100e0b214400c0102c062102141e50b0038220400c0b00c400001448120140c1e0458440e19018203030358001940d69040c2818007051014030042d83c0007500382044204549501c01005540c20503d60240e16507010f1064900b035544 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 20883315 1250 20882065 20882087
    0xc0309060e060403020c0609030a020d230307050f060c030105130608030f28090e040503040f030f1e03120c05090301050f10080703050307031d03011a030c0607050606060a 75
    0x111410200d10034004080410220f020740d102e6000c4550f03034507010090040718000c44482580c960030091244000d81001003841f03001a01c42c0c020034428240e4124280420704079041d40202990001c1080e0301003040c2004a80c1040380072000030203183c600501030765242d00c0f0501510703000325074414401074102007980020340540a0841034a88a80c2030030b10080780d58100081030302c40e41c280c031081412018030882c4a0001c0d02e105a039a40e1600307082c18054009180041e00480e41303440704010008003641085048070103148030362007101d034101517401e05245021102e0703020f40b42008180180300001e5045658603e6480342c50402248108268206a5103402541420340d019407c0001f005074086410416600c01c07551003c002c00740c41e485000c03842d1303102641c5c04000c00c40e601c00c01090002c24000c1d024114440700035030f007440c1d03500b0030040424251549400703c060383d2020250046481d1030240400348901c0d02c00c5c0d0700366060540c640c8400d66039000241185014200008009030101e02c10610001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 20884565 1250 20883315 20883323
    0x20a05030417012d060e0103080702010e030a0f080a030e030a090510020a0c030f020a0e04050a020f12030703030504060b0609010215090307170d0c0806012708010e03040504060602030a020a03030c0309 88
    0x664068a04a11503105110944c4038031192400c140441c0365400e50240d181600e800c0b20b041800e200150b4015284242e4000f4042d50511411030146e0024020f6003c0c440c50900c00c44005841e140f0715080501a5608010401007681042c0103110300320350301180040c225442100c13902c20403c9404c201f47e0400c0d80c070702d0002e05000980c9102005010400c080540c415109880e01080255244001034044800303440c020850b0f00404c109001601e0041d031940c04011008290710b1103083d0340d5180510396884054220082500e070001c110911560b449009142082a02c07924505803d0100003034940a0040e117080480c000940400d20b504001c00542d1560380d0b002d140002c3c00c0c041c8014000c529040591076907045420700c05a18003007072048804901540041c1c44d5900c400010102510000910240010000b68440c0002030461801d0150f1403e441303210005d0350b40c032420001404141c5100f0707004801594010071903d43c3e4039a0018411003d90b4141c035000684000c010412000740a2500c4050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 20885815 1250 20884565 20884601
    0x60807080601050a06050a0813110406080606030106080c01050706090510020703021509010207080702040203040f060c090504140106050301211a0f07170106050a0201020c030a0305010e07020a0503041701 89
    0x11900c050002452070580da0700300e41c2c0c0110965035200889182c4111062103001980401c08940759501c0e078424a0001880380f6810b0b0817400f00100882c0440b1015400034205074003074401c0c04007a040a101d140c01a080b142c2c080c00d075042c03024001030036611421038001c041030b58401a80b000c0c0300c4103100750794449443d4801955184070504009540d09540310311041074215020110b070203032005100729040c042d8011100c504221058080100a4000034000c2e5958802014007900052162003007117215012034841c45480c03420407003030104503078000808102c00341558005103d2103411200780c2c1d0440b8030080804840c82c01502401d42d00d1805508018400402da45c1c8100403d041c89120503c80e0045122444070717507a80d18421200000728102002c0381865000051120512510080c0048031441c0005407500154000303003071440e4400e0b850ba400280d40d641c01480800544074003036030090348070320040c441d003062510f415440b0701c00d134400d520314805800682140c42c0400e40105025407a04e01141d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 20887065 1250 20885815 20885819
    0xc0906070c0f080d08010905070801031104092f0102010b09060d050a0b0c040608070804020a0902030606040506030c0409050c0310140a051201050105040e01091a04110a0902070201031505011b06060807 88
    0x75036038850700541d41001c05c0c4804c00101d42840603204281c80707001c0941d1001c0d5903910f1611100507422418640380d0708203031650030100100306040300441941030b040358007024504413140a401e0110045980904590400d00c80e0910b50380c03003051642e00080d0495600404990a1414501c1c0c42c9400e01c006003500c007050304000881c50002c0140007200c0c85602d459006694504084448840c100c1e0300039071150300400300f440114216405540d001c400540003900d070070348901c00103030540c008545e2035500d0200090300b441121154000d40350040b004130200c500318184804800b402200d6405080107805040d2400e10b010f036601d56030840100000340031300200c440340e0301d4400e010b010b007400b815000d982401807171720040d1170500c10b5081c501d0f0490804e203a10098000054070500000d40140c542d258021101c1c24079644424a0200901442400598540c03603440050161061002404980c60990004021a90f0801001c20842d00d801c1e5000d505080e080c0381860007081140c004030070342c0c8114031b40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 20888315 1250 20887065 20887079
    0xb01090b09010e0903030412020106080a06230709031209050402030405060601020105090f030403110d1707030206010e04020f060901031d0d09080f0d110a1a0402090f0c0906070c0f 79
    0x1000e400c801054901c100300781c1c2c844030403045801c010b030f60710801580300308001070100d995003441110b005c3c0b1620011600c81d81d212385091400030064416070341d02d40c0d91400c620381c060041000b80200e0703004103114030382c61a1000001d05264228400030348410350109007a0302581c856001c3d10060b1500410440d100d080c40d0801559654007200c091340558030780004600c040e400056241c4031003614034011460241150b86220030840c044540d150001c16048012000506100c0308501c2c44120345d1085442e8080b9040091070100180c1c081c10980d0111414040507840b40340d84041da405040c0d460365a42d00d0a900100c00809100d0402c017034040c1c886070301644800c0d001c11542c042024558070b22080e0b50f210351159482c0d16440500342c0c400e6001804200c0300c6801482e1401e0a184600c0a0781e4040e1843d803268254207040f80b1200fa02c0c42411010402189050708009402070441083c41400d0328000004240600c14002003a02c204c0010030000b00b0007107003148843c0908400342c1d41000003a40e801c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 20889565 1250 20888315 20888321
    0xf0a060905010f060b0a0e01020c060c0d180f12050c0a03050c010e180f1803070506060a060c05211303060903020d050705060c0702130e06060a0501020c0904140304030b0109 76
    0xd0101c8207942007024040c0a03410074011001500c5d040d8980518140120030706560680c0c0c803091403815070054000212a43c0d9691000e0512412554050304000907420300003444000010310064201d0700382901800201d04881450003581d0700c03c1d442d0084e400f95410194a0b200054898580c40345001c50080204200842e080036101c4c020380310035070045da0034402c11480e030128200c60482c012541002a410760a00142d56402a0540007143c0808e44160381090440c1e2107010191802d5002d481800880d00b81070a070000181581d152004500c0c81642c0d6003900c40c00d00c6002d54501400c510103c04112401100b1510380fa5a0007000560356540c1e07142c203d000d0109403201360098002c1a810b50810760040003111101903001c0007a1101303540d440542d00c215080800700f07980000e41d604410b0080c0e0801c0c0b003041070b44102440200301c13628210b0104070303601e1002d4001504642103404106001d8580705103a64209070b04c400165448192034068514500035580701400700300722000000f6600321036034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 20890815 1250 20889565 20889581
    0x60f021b0106050301090312050a0204030203160e0105220b1203130905010509010305030706090312090506092a13020d02042603040e0a050601090e010f0806011401020c120f0a06 78
    0x10000e1040c6583d59003050300b00e500010f405000b20b1081556006100f4141d800258084e904a00c0181003a4907034012920f0314070010a0141000c1003107030f081c050030350064211070040404a8110748a00c5016641c901040c50307100c003079190356403168000c519950300c4d810325101703180c02001101d4407451050007001c0288120b00c0303500401c524150021038035081c41d0710050705807500b0800451900d6032035940c40000b021408800e508026a12041d07241d0240386001d4610854050300007441c09043c0384280504000c402003010308415401003107a60b4101646c909008500c43c100c49821203044e02c192000087d12490424000940c0300080101c0c078030030a0a45a0782620f804282f000306c1c3c084071424a80d5a1040d400b070400340b40820000500740c100240c008a601110604d088421a82d03102a1543e40c44001e0304288043c210b91001401240b10400445005040b031244060b080e910030310010307441d01d0101090038050f40c003400d41190400420040d0601c22507144084915001240c1017041c010080c00c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 20892065 1250 20890815 20890867
    0x30b0a14090102090d02090c071506180b0109060c0c0911040f120305030c09120f060106020f030322141002090f06120609130501050c03040201090f0f050607060f02 72
    0xc80046501da031414804d4034403507030001d00510700814180d000c1003554400145048542c00c0d080240c4000a40e00d8200249000c140c1080400d0745418000c140780b00001c16181c002d8240d01d002001c0300c4680c0d200f070300d2408a5866060543c2040c1041c108042d60380001c0e08420b1040f400c010400340a100800000c108a0385070341d51104565445801c90a0503041b0030502a000074014804070300340c0c90071b0000800c3d03500070007403c4140d4414100a0141080031000e01d4074410b8000c1e900400040707405002a00034051000061417451906000303131000c120401e0740314851541c0080000e010450300b800084e101700c0c184800c8807400c2800f6404400a5480b41080c2400381c01100001801414080c00b51035503000180380c401584c0c5e40311400d00c00c20020080440041540101100b000300388284156030048000d200d07010f41d00d02c0c0c540009448148030f40c0c8000401100e0f5003003000b44059610b02c41098a4040307558a558402c00c0c14010701822190382c15030f030b0042c400144280b1a204801854030744000c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 20893315 1250 20892065 20892101
    0x30f03180a05060a05030c0d06090c0e01090605070f14010b030a0b10050907320403080301050a1e06030b030705041803030e0f030a05090a03060513050c04050c0a0804020307030b0a 79
    0xc50060220f40e0150010203008031740e0600c007069002400c88080c00b06001c0f00f5800240355607641c1012010340300280a15800308200600c03d41072561302425500c09000c00b820300c2444c10406958600b509003284074041c1020062408440d5028029002240600c40003001c58080410b5030600c1c0c40030803001c0d5030369501030307001000028850500c6521184204216101c610284481c4141c64008502d01110807045d101c001a5418110410b00043d002031402840800c1d282d40c1413500388407048401e0b401a40741c0d00c0484d000721008400c2101880700f030b969a480c0200d103030346496000c28903084c442d8105a5009040c4100003003902441c1041c0c0160318040d54003032211502e01c00050f42c950071200d400300d5580c1c008100070300c3c405000300c000b40141c0202900894510340d60f034850340c1c2218802e4540c0d03013005400420000900400f0801351441c41c000302d0b010031060402100c504264405c500029080c044200c000401b99079052220b0340080d60401807034031851400e8035480000b030022100000c0c280403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 20894565 1250 20893315 20893319
    0x804060201060501020619090f050d0905030c0301020702090610030f020301030803040b0609060a05060912070e0403020f0102040f05010806131103070207060e0303040e04140706020a0b0601030b010903060b030f03180a 95
    0xc40005c14038021f400500c02803101066080d0070102034141c1e86010382d06658040e40c1c1e4000610f0400084e003680303280d40d454200ba103042804140c02d0035100c54455210340e005001000160790340d0070a0642002c0b040394490300218100c00f083d00a4103650003141340e420f2000c80000306120540e0000d501ca40d00c00c0c60100016580c000401c580d00b4400e40c0d0840d04851241801d01140c10314000134a032405000b032040790040c0742ca0040c05c2c60034203e6040011100314900030f100c00c15804000081c1030000c103a000350709244c1040369598004e180e52290782c0c10409102f000c00d8040d19600500c44001000c003c090084170650360003144103520a0b00c1d480c0c014400c0917000a5007030b205414090550000a0140d85001d144c00700d10b8404440240c0150303819006148a00e42c001801c200302801401950003034100ca4049052210940c40d000b46444d0505080609a0107280c0c3d0002ca0364090781e5200f0f200040c018174050102c1c0c540345d0614071042d00c51200240ca2400d914017110205050344040b20000740443e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 20895815 1250 20894565 20894567
    0x10807080405060a0203190f0606090f140f0402070f03030504140c030703020f010e1002070e0c0301080a021003020d15080f070617150607240b01090302090406090b040804060201060501 81
    0x1254050b1054120b2008616048600d400564200129084200000080c6075841c401c407149030351700c4143d01d5600c02d000c01450f50015181e1004160107001419001d1402654066008040440c58400e151440c800f0601c2c0c4d407207078180e40d0b41c50307000741109014882c1807074050020001510103440d011078010321800c61b040001040c0b001540d001d0041c00c3d0b0640b0b1582840000243c0d0540e0340c1c10300c5501120401e440d00ca1300840402c21400c1c3c2c1c014983d02d442c0c590585041400035211942001c01000140455980002d2003000343e07505803602d5840c00e07040302c000ca00a0203407000c0900300d10b080c0800780c0c103e0041c101c00c000540391a03a0a85c1d11180c0100321843e581c40c1680304503004203ea2240003200300300b52002c40c40e07000b1808080401d40350407200c00134009a1010718212020303030344126071903540561103a80c001d80d0321826808001e602c0c206030003c5c000c010301d0f1000a202e984c807240040d003044002d8115080099000110000754149843d060949801c1030068400542c41c001001a80b5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 20897065 1250 20895815 20895827
    0xd02120901050406120e0610090e030304030f080901140a0e0f0303041101080a02190c0501050601080906161707090303020f2427010204050f0d2a15020705010807 71
    0x25405860b910b290501d8403c00b80c0740e04480d500e2440421342d0b6801d07203a12044003440358612508000c3c5807414154105007401c0d086a1a0019861040e4000d008000010742c001322841119944d5007001505a41c1c0c0300f0303419025104000113003081541907c14400044866001090000c1702c1d0340070b941104000c40405581c0c0d0008840c080c02c02e2941035503c0c0c101e5405407a62940044c100200545400d140802d140c00034507140e007410300040d0148011320f007030090a206040c0c02500c00d10300f04050f8280013001c291755a10103850707407411810300041d007100d690144210620641100250208a00e0300b020007602e03d403c1840290090301842407900403103c40400c250000401ea01807031600f280c10a61180c0390f000b801400203040315001000e0400074000c542e4020340c0640c0340301c00582d031142081c0c03d204030100c101410600402540b600540004ca030b040345c0544070400b041621400b9908541c4d4030245034200d505c441e0107003219000c0e1034541a4003140410640b0000c1c0c80719241519214021940 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 20898315 1250 20897065 20897077
    0xb0f030a080d0902011103040303020c0103060503010b09160318050717030412030302090604091401030c15081f050a0902030405070506070201170604110c150702010207050a0303050421020d0212 85
    0xc0320040150382ca8041c0382c2d5201d840540d0040c9011005001c80c59461842d560041c1c00aa0240c1d2190400010640c0c1c54028940a044164000e10021817158089460103c01500c039084001240000c560780901ca680501c012800040c4040c14003000c41c203255480e04241e0150b1840080007403446a188980001210100d81c0c03440006005050746441c100c0082d000031058a6001800b004001151180f500074098110f200740c00041f059491403404a090380000d60260a102800c0791403000f64503008000d481e8800e041440c004000300703071380c80103079110001c64001941c0202c03000c4012960311910b07070245100300c0c03086003200c3e5915151001c002c1e280c0200f41c002400141d1604289081c18080140c9540088010700302140d010089510410720f0340101d800001158456070706145c1020500b03400d2900040303103000840c43c0000c0342c1c40301d54031003901040240c2032545404c003040c204000482441d103403160308482c00e900d110b030703400009486244803035807400180300d80c8801d100301003940e1084480c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 20899565 1250 20898315 20898323
    0x5040305070e0903040905010801020307021606140304020307030b0f0a05060409020f040e010f020301062a02090f0702070306020a0905030d0801061e05090a15020601120218130f060b0f030a 83
    0x14040c42e00c200050444002071510100340801d200000b030030b8030540207407806400540005a1039141800000b49401c4032910340c002040d0110b0820007e5035008000c000220440340d5450f0b940345d80c1c0380042407034221180d100414a03440c0b5070800051155131222140107055602d814440342e01d8810030401640d00f0904003075446400341419241a160076400410114040380002c10000040203c0030101d2308260301540c041035000d00c02d030124101440c00f0099003211440300040441882e00428800d00000f8080301e03c1c1203581d00840c8041d4000c000c903800541d07000a00755a20340d40504014944030541c42242c0c0a0301c200c0e001003903142d008102080c10380d00d09540300210360701070387c1d0144c0c1d0310341100d0b41e04414030404001fa95819181c001214016043c10044011039011092000340780940c1640a9981070001d4804080103958103500429403001c005010201e03503e0b0440c044004480880d0024400240b1401180400061380c1141d00361a000315011000c102c010020b054441905003c014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 20900815 1250 20899565 20899573
    0x9090503030c03090a02030604080c0708160b0a0c05031309050108010e06060603100b190e0910060e1c05070503011d07050405090c061b01050a0b100309060b03072405040305 76
    0x502d504040c00007440e0b020003072000300c17122400160042410548140c405a441c904005100a42003d081200d00000e104260007050410322240030803104201d940210038001c08002400e00045101d10004100c25410905988c3e80710010b400c0a4000045442030900301410b140000070100410711440c3d80c203d180c10040c0001d9074a201c01c000c89175100904004102c45055004110007080300040e00c0e01c44004405103000452496002d400300001c656060300c600840c501700001c1c16601300e000c3e030031128542881040d42c008800040d029811b002544195040c0f045486c4051180001d003500c116802a0000c00c5003d00800400b204807030790407052110f41e44041c1040140c5d080607800705900550150994401100f124001000c983c0140d903400d6500c83c529034401102c8900703100d0f003508009180300070030803440e144000c10000c0d070520000105140c2d86804c0310381406020b800c61030741c0002c01000d88140030b0701c8901c2d0083d101c4000d000c260020f041c06014035039040c0644220f81c15a50081c0c020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 20902065 1250 20900815 20900821
    0x3040b040f0204061d0901050a05060d15020d0e0307030e060f0f030c040924050d02100503070201060902130e01050609060304080d0207080313030806040c0912020103180506040201090909050303 85
    0x198601c8103a460304903085a6500343c00030b95079160750b00c0300e407944080c511016424107040e01100d0a4480152070480b40c3c5181005004a070b940304a0f0340110b140e1300070f0b440c403441061200000e0007801340d00130014102e4204070b1740d5001c0c2c2d83c0110082160611949500c901c00c519082882481e0003544214100141d040040100105840015592202850b008a07281caa00d654203002074a203200c0701501c518154200600003099403805c484050102a00c1e0b12000728000d8000480c40000c21446505000c4000085240c3c14401e40080000c4e111000c2d066580d000161800da82e07203601d40c41000304180c402c500126451070300c1012250003280041010b4116103941d100d0300c5c002d62003000c4100341c682c0c0c2045190001080d0001840c821a102250010300301c100e42405801c8000c0201014801d52500c4c1110300c01d140c00240304000e542c86907080358681e014920044e00241000301c1c0b0341c803010789500035407020031500161482c400c52013039a407102c1c0e01ea550306a5405030303aa4204018503540040c800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 20903315 1250 20902065 20902073
    0x1401060509010e0406031712010e091005061f020304080d020703150b031e010507030606030b0d060c11160602160b0712090e07020105220302070513021c0209130203040b04 75
    0x280c3c0c4500350f00810003d0440c1e0f580e80d079402c21000e0030800c01007015010a881008141c201601d500414107100400040d10f0071042c00350f160042c0466614000d03540b1004a0042c0d203030110720034841e19031403c45020018114901a60720f4000340300d40d000a104181c40700d007a141c03022401c0f0080b65440640c0c00310221810504a002d001501c880e15014428407921403030004980201e40304032640c00c000050f050810b03103802015a00d140d0410401d050030148002050b0704c6000007902c5c15034001000003240c0c03168032400c6881040700003400c05140700d0080d050744a10340b850120002ca0390582c0071070b101d107451441141d442040512803100c1046003030000d5800309601003180d51400c1c050740707441450180c46408a61826105881440050390341d18104022420344204074180c0b0f82c43c8001880c1c00c00096a4000d60300c134268080c0c640a0350f2030f0307500000e401d2056010340d01440740702070490109210700c0030081c3c001d40180c03060a200c0d001c50b840030380c9044401c2c42180d006035041072140c03207550f9032511 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 20904565 1250 20903315 20903327
    0x2010b0a052707120b0103050408031803090d0501020d0c11060403180f0611060601030b0a03031202070203030301030b0702061006120504110301110d0e0d08011208130b0d140106050901 81
    0x4020b40d0180c10210701d109101c109040d03014802e02ca03940343c0341c1c60303640c414040710111034007615414103141c6004203020210b400c0e00c00b40c0707a00000c041c00107590030b9524081c3c030f8154051171500c030380c00540c0d580d01da50400030190054400d5400b014010080c105000c02c007190003050901040301513070403403004100424824551076000c01c49070090b100e0b800d03a644490a501241c0f80d0301510000301c3c0c403000b00e08602d0090020642101c0240703401c4c03010f445c070075000a0317560703a191100405210b800001049100140e4040c1d03404260020103494a070740e5282860301c0c02c0c4c0412100c00b0300502400c00052a5015500380c61802d69003155110082801d041d00c2082c010080034000707036460300078204012119034090003540c104808483d103442e01d9825007001c16064507040d10006035682c1011950000d840d81c4030299034110f6200348950242d0b1501420410240d1040c0c52030086080700c030b52400300c0c00d007035441c00602c00303005c01000c00c01441031071040960418000f0b000b5030001035420041010590304c01e02d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 20905815 1250 20904565 20904589
    0x1050a0c080f07170a020a081008030a0509030c0a14010207230d03050d050106030b030c0111030f07140a080702010e0405090d0e0102010f051014010504060503040f14100e0c0102010b0a05 82
    0x8282010204d91501440300440c1046580494a40e000500303a800160710620054229640d080038a02e594108202d007601c900544007440b041110100d05c00c1800e5404100302069541c000e030905029035210194030942001107030b003003409403044030740010b040100030000d46031001c0024040500d41001808100a036940c44005804004080c04143c00810340781c42214000c010030788000070040540001e15081c900000c0c00c0074148860050b013004075040c04001c1b1900007003000880387d500d100e5490b02040501c62510308850034803800000104000b0248000c04806000344c036200d4941c5402c3c0c0411050300e9003101c6400303640e0010320040c40294000d004011200c18140004505003076018203842c11920100c84080741d400351240c0c104aa0f03101e510341d03600106400e10700b02c0e01e080d04001010704244405000200482c1203080c918050089181d861100c20f0a0b000035a080035400b000f40401402c6031046c903104501a605960315558014842c086c41c2c000050a074852003803a10003005845141300d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 20907065 1250 20905815 20905817
    0x10f1707050708120f010f030206071401060f060306080106050619140918010512060906010e040215030705030f06060a090603020903030c0105090a05100c1209140102040609050301050a0c080f07 85
    0x2d004040020711210094a010f000a421400c400c0c60030088a002c1182d060380280c00b0009200001e0008da141c8804072054142c12446d0410400601ca8070b050040c0201c0d0702c20f50000040682c089030595154001c60103c449102c003c1c80000c2e20388040024500c00d610790100c09000381511311801c203015801103643e104e1824046c5040891200100f086216072901c402200c0d00d040005000340e251502e08014a81c5203a030040c08035140034030010703543d050180a500561003010002408545e18240225002c00d0ba04030301ea62241042ca130080d0071078000340c500b01850f031851000542c6074107103e0291107100c0b98030790b00c01981615052007500294060240990980400c01c207068202c0801d0003001e00500340c0320000c2007680c03a207040c514189449038120350203090a0100c0b9070070441d0310030300c0704a00c1c0c400d80030000303540322161400a401c0000c0c4c42c8600d4182d400403900240050304080c2407030454a0a4000b40300d550f40d052111001c9400c81211a404518414040703020141d00300c1e41141c0c04515 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 20908315 1250 20907065 20907067
    0x5011d01030b04020c030406080a0e0604030804080702270a09021003020d0908070c030515070206040809060c070602061e1b1e040e060a06030e070501030507090b0d090201020c010f170705 82
    0x4882c041000e80e804000143c00641c0002010492168000300f0030354031404000d02041002c2c0403511160f19580090030150400c0b0400c0e01080a01800004952105a0007000f6036511403000507901184001c10310706402c00036200e0700064100c0d911780070300c451483d40140b144d10110000d203400c0e0000c0d0450035581c820141ea1311610000a2101d00041c18040e0140c1c810705840303843e501c0c149240079080e0b0726521900503c4801d001d1815000501c868105038000c40060301c554042d0003140c86400b81e0044942d2511501c4d07400246d00340c000c0394a90007404a00904110b840d5030400d500025007082d21482441c48003d460403010513040c9001e00003581031400440c4080280c0140e0000a13001030b08460b140034018021b1100a141102d0b015000b0000750405003d581d4081c4215601d400c40391040e1810b1549510009a42c10301c10140070b4050b00940141a88980c1ea8488017401085261800c030701600c01c50302244941e600441c04520300c90328517a512094004a929540e070080805002c407024490 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 20909565 1250 20908315 20908331
    0xb16121107050f0f0c0d0b060f010309080d050708240d051c0e041506021507050c010c0c17030c1b010212070e09010501030209032d060f0106030c02060105011d0103 72
    0x10040c82260103078600f14000300a03031a131030801a42080c02c4140050320174034440d40c000e00010817410949078000800c4401d080c0030001800103a014283ca0600181200000501d03030000d000e00d940698000c002c19511455107982d481c0600e584101c2d030303001d902a180e0a003644405c10303181105207064081c0c0705005403111a110586017200c0e20700b060305c1000115109000410f02820a03102d079401c4905038030030300418185840c801030348494052001c0c00c1c03c0950f01c00082c0386e81e80035008403100d14000c40000c02050a08100c010442d05152000710b404682401202c1c01400102040d00e0080e40b00d9000d540c40c00982c594030691030321003103015401c1035400788901146541a50780e41392091143e078840f50b110300b80ba14208031b0380002c141c0046060602c144501e1140351000615500d4480c4a0b502180a10103010342141100b420410100b03d41d12440003003048525113a03d03890304990309510b050099100740c1c081661075a07400d00440d40000d003101c040880510b4100b0196039011410305002426403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 20910815 1250 20909565 20909573
    0x60911030a0302030d110403150f110f040305010b04020403030807050703020a060c0c0515010308040501270602030a080901111204060b0406080304080d020c06030f100902070501090b16121107 84
    0x41801003042d0b002d6000400e02e0100301603640600b044444500c1e4403103160904507a200b0021808840030790300103955403004003102a183d80d00400810700d801c0925500c1b5001207491061543c841d00045405500344042c080f010b003000d000340d400340c0b58141c43d41c92095803590000c4940360020b040c00c0e0110311804842401044ca01d210701220255142d564100540c15030030300c17130f2428035900c4a820030380468400420100d0310303c40c284d40c01d0b51001d213800c1000c40c002c245000d2004514510f801c0410300d140c1d40001d0200d03000002440d0a00c1036031909541a540c41d1196400c840e00c031030005030820410040c60640002e030400050f0304c2440784d03000242e180d03c0c080c00310f002c444064004a059501c009014000304408010790a80d40440c0d00c000c1c502d200e00d03032021454070b00001c2c0c00101294005404200300004100c0824050105804c0440d100c0c0094100b0301c1c0a005002026070352a4840c40100b600c2070080180c90465400a8031000c8560840c0341040e0028130410400c06c0245405100303081c001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 20912065 1250 20910815 20910823
    0x5150108060621100b0d020303160b061806010e0d0b0709030b010b1c0903030204031209032001020604030c02120a05010e0606010e01021207030c0819080a0b030a06091103 75
    0x19014040041c100c070b282450910203c5903001d020310349070381072030314801100d05000542c0c24113840c48960003048050014010402c2564500340096241c08003041d00f018114560b1b140d090a00d010741c0f000e40c4a501e860b42405075502203101c0100a100c0c21600040141d400391500401c41e0074003038a000c0b507200040d125920765179000d45c0c10300002034640100700b0601001fa510140500110f11070300749004c01d500d01c0c100f1a0207a99070075078952074580c02110149800390b41520011600051818449160b11781c0003404c03074500d80402c69868421030506030401070081050100c090040e00223248030388403500e082d5902c030309d07443c0e0403684040d1a071214883c001e020300c480e0100900c500008a010305e661504142071100060415040207500c41482929070703030004403210f88614180ea050781d2008a402d04a03554958010702528010002822000302d100c09001c000400d10320b50b84402140d100c1440c000203817201010010303819405a0306030000700300154003404209114035240354940300d50901003410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 20913315 1250 20912065 20912069
    0x3050705040f120209150d0b040c081906060b1821030a02011d010b0307030807050708030f0c01050601030506060d0c030207050d020105010312140d050c07060920010801140d051501 79
    0x483e40030707a148421070034900c515580061003d007064481044910200380140e11849010700001d0000e008103060000704c00f000c0d0b01070310111040e07454502402180c2c11132051101d01c02c903070b0f59140c08000140e2868107810b4445a140074801c05044030102030801c610303030b080f9209042000108105060545108000030408840307079400120301003070b810a0307580081d4542c005105459041c6500314910750b801007000c030140c80d807014005454181c1418114500401500000403d100c0080e00b403040d20311b00340141010400d100000e00c166507400b0011401c1c2c1d035040e22a59008401032002c0440c102e41da40090b60105900d140050925003075071541d514101c9100c0800d000350750350358014801e00200c4411004a1009420402c40c51040010b400d0114450780300540e11285e91140403416060b80002161a0560020428132000c0c46900340b6403142c03641444040f9000700c5001c3d10b510954020140c40d412510004003044642c8145401c1c003c4005000c0303000c6a040c040c00d807444001c020030803071582c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 20914565 1250 20913315 20913329
    0xf0509031006060909020f0a030207080408010e0703020901140a1401050906040306020903010b03060f04080d110d051603060609050904020307031b0501200d18050a0303050309060105060909010603050705040f 91
    0xd10390b0700d0b000c0060804e6089810400c0c02c603004026528a082510341203a000d103540b481c006030381d01c2280c00d00d29028000d5810480d0175500381180f01d03218050028240c8180c83c022540940503981e41c10035035440c00f200c0070400d038001032030380b0302045145094500340c40361020604081d0301c1c10030764400007900c55000e40c0080380d071641e0105015001d03003402d1082550f441000c1d0000c00c070b1030400d03030312004045000810050850740002080300d0381c0c0505030842c3c0001c44241c04025100c4007022914000b41201f12202c05d0148122224040300c0d51107801140d007114100e4a848070b0650518042c026042c900510503030300341c404d411000001a500c0141c90701500c1403916404801400c02000404104908001448280c1c1030148144404008952050b200c4c08604000b07680020740c1c000e084041c803c0d40d1004d40e0081364405c00206140d00200254464814282552180c2e070b01c1c2d804006c0c05010341240c140c1c0051194006000c4180680d10803504281d1034102a401c2682c4c0300c000a40f80401074010391 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 20915815 1250 20914565 20914571
    0xc090a110c1c0e030a08090d02041b0f021c11071502030a030606020601060503010509040203010e030c0102091c05031b070801020a1706040608060c0f1b070501021002120105010f05090310 82
    0x3001810715514001603a072114a0700070b00c80e0f82c0d54000a80c0c0c680c07560300040d240c3c10000640801541e1504400d1510540c06001032040d0b0045411002e070882090030a034000c07800c8014191070091010410803c48034213102e091130b9003610000212080040c07405056802c0c41038100100710000900d036181041185507008607590000d409001301560410392046055500030801808501c0e04842a20305461b000e6400300040da607140002805440a84408401400000b1f09440021010b4008051041081e40c1a44192641002008511000b6100908203030014445003406500400c400300b21940e25500300c9003450f440b00381071400c83e809241400007095050a9500307281d0170896030181e1000307045804100340392614000c6510307500000d00101c1c80210009590303120703c83d0b81054a0548904141d0508060b90203402580d4130046801864098801c9800d10005440ca9008941c460301c0c0c030070251300c0c0991030b010040d281c500f1403050200034400140002c0c0e0307c03500c08220f004155142c0c1d40000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 20917065 1250 20915815 20915833
    0xb030a0204110702130c05090f01020102070f030815030601080303071b0804082a0f010f020106090204140901081b0907090e04030305150117040b040c080a0507051306030201020c090a110c 82
    0x103c17039075048031901d25030181801c103420215030700301c400d6409034842039401082180d90000101e00a01c03500b400101104040312401040c154000011840303140200a03030300140382a2410903603201800d1003070700e00780d0340100001030301c95215061420500c003a4609020b80e65049079910398a58126820140840d40040c011250605e1f02c05850205094400036071641203038120301149030f107034504600324140800302200e800111f100354068001850454011501c4d6900c400408840a1072580314510551142001180781d1300003090f40091090350080c4085100c44210600560381d00c0281440c2c10b100503004009170040034200002e106620076a0001507078a801d000140c01c5000704210981007059032048440146907a00c20316400503084a0200070780d655500d0285100090750b00315814034014081c60604000c0d00207220340540300b0481740341310585850444001120304511000e801a03000c08642906400c240c003070607410510050f0041801c00c803418070508035031b01890410185900c0070f440 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 20918315 1250 20917065 20917069
    0x603040f060f0c020c01110304260708060c04030b060a05090405150108060105010207090e01090c0308030415090c0b1612110c0910150909090b0105011101060312030b030a0204110702 80
    0x920b0802c01e001003020400b9000d400c07802136803607080100a605000042800c040d1815041059500824145443c0d03150000b242b100b00040f05070603410180144a40c41005c20f2807440031038828481c420380722100d070610f17203980c4440d000c050004c2c01064101104400c08201070312800c03845441280200c0060010050410740740b4a000d00c140d00240d0780c2d4011200520440c0e9020901c441107440e120408507110480c2a4158010f01404000404140131018000700700003000000d5845513014110110041c2132400d045c5080c1c641e9032038001c08042d03001e00c1c180700640c564000380c55219407110b1040a060340d582d4820384d009134803050300030102d90310920010355400200607050210609861444840c00d280518581d501120b0289050400e1080000c0500310720031001136004005c01102030205c00c1490a002040c00401c4c000e01e800a6a003007904032030010f05026010480c1d500c43d40005101d0348000e0b0441c0101807440805500d1b009011081026a980b0700803685085070041c0c09590300c0c291881 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 20919565 1250 20918315 20918321
    0x30804120c0809010302070606080303011203020d03020301180504060b090a02090406050105091e060d05010e0106030605062110030f06020405010314012304090506071101060b09060d15050603040f06 87
    0x940d0108000d028600440094070000540e55010b0080c200940c50f940b46103000c0e000f40c8070301e410441643c40040300000d419801c100d8920f80203400f81d0265030801014250450503031000340681603022448540040c0001a142d0100d0b038040d009190002c0d0740d80c2e02e0350016905040c1500c1e080c0005030041180111403609108080c01000b0900b0b0103031610401c0c60106540d8108a00d44a062840040c00241561245012110400007040003003000b980c4444201042c210300b80103500010703152440100d46403c5c00380c1114115a2403c1c0460041e40b0300e0000d08001c00700051223081c80c0d08540c200040020b000c1001a80081c0c0300b14000350716030b420715000400303c0d036040316035400c6500c0340401000307006180843d5090a01c240000030030748204680108001d8494200010840d00c2464100400b080e4400301030125448400001d0060031380d100c4400a0500500400961240e010410324031500c1055020401d1280c0c042c88543c00715659400264440d0401c4800b40e4246446040303420800c08244 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 20920815 1250 20919565 20919593
    0x30b0402070b040b090a020d0503040915180b040e030406080f0a060510030203040615030501140601030c090506030402040f0e071a03010311120a021f0201110306030606060d0b040504030804 83
    0x15808606208850301c66840b08500504040d044441e018082802c5074810300004181580280222107201000c0c03508a50725405031113611840c51a150303a001e54030741120030b1402180c0550301d0242010340800141c20040c00040010780d8407507982c0d0070340c02400710180080c2000704025119034100b40741010002000c3c44c1c000b804070040914210f000c2c03181c1e5884103e54400c00a561a0040e100c0e0f8940c6065001800450103510100160680c00420811f054104001e2588020803c44958030784000560548001114400200d404503400f40320509181014560184c001040131074035030804d101e110120f4041c1f0031800016000903c06110001140160b04900d03d1070f00e420529641c50f648820a00f0b0308903200892280c105205441d1101d5020403400522079002000a12400c2a010256803448114962180036500700080449061724000540b48a02c81c00303009042203694000400250380e01210705014203d0303442d050113441d03448900c03445208500c04e4842841500703003401c00b100720480003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 20922065 1250 20920815 20920819
    0x80609060907060f030b061206010f0804020a05040c02100204030602030610020309033406030b0f090105090c0304080d061415031e1512010b090702070806070c080904050a0c030b 78
    0x41c000305400002e89501203420628200d9000c80e14031004070701809800c41801e52100c00401c004103510300c800c1a0b00e0160100341c807004e10394841e000055500200440303001e5405070440d0000c10090402c0e42141002e141c01b0300c16207401d5102c401008080382c110360000c0c2d603a41e50120070002603041c13405515520500500045060101c80400070f40d48043c2d01c4100d6001c2007000f24140400c410441e00110903960311042d4010003500d07640004e00a080015019210b04407040703403003100d81040b15051b410395901800c603000d82d40e195080c1000b1a070001e0310850720104100300c040407105003880342c0d101500e510703548610464a09801c20860700d0358440b40368401d050810038040746284858840007003142c40000c6001d55655070801c002c0042811003c9a0403011260314001086010b5128400c008400c6aa419094070f42050499564a1134000c102d4158090780c04240102c0c060100320b51503034841c034066071400e560745000c5810f8440c2a240c1c1c00055440b455000704144d05400381c20810841 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 20923315 1250 20922065 20922073
    0x605100611070b0a14160201030f0207230f0609070303080a0515040b0301110c010b0405090606010f0507020406091103040510020c1908070501020a0c14030423030c0306010f080609 79
    0x10803508039807910020f114481c1c0038100055507541c10b5008000162180318040c04a9885002d5240192080c0c020040704a000038a030010503001c8007454400e40315090381000f840b00d000c101d0240b10184245180d01061100d1140384155040844208400c0740300b0310031000541182451807502800d88040a0451200d16051104111070150000149904c502d02110049030001c031610110b4014901250940c082c4100020b0783c0d403403d081504a01d1110b201a20100b00e030395902c1e41d4440e240d010941e00140001c003240100011144104060318280b800140000303812940c5007035480480c1c400d03c2600d03440440110802c814072a00340124031302c07804500c0081d450460070a02e140d407141c8585181516010307000c10004240900072080c1c9020582c014003c65682c030304044050300f40d0b046a5000c8034413001c1c8005045070108040291011103001e0540710062509800711207510f030450010983c2c0520820000c8105643c0400401e4000c04008400780f0f05641032601003401c003440240080e442c4e0384 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 20924565 1250 20923315 20923337
    0x1b0f1a0306010804020d0204050907050306061c0305031504050109090605130b0601050c01020f0d0504020a080703020315061306030b1e010803090103020f040e07090e01150c110f06030406051006 85
    0x8005400c5aa101009291101190307640e880016000c0281c0440607400c20b191004003c01032a0010343e441c160382d030803000c8900b01c0e5603d8007000a42c2010500954841d04409074060000e40910b01641e04040c0f044001600d6040c03034000b00c0e003260401d030b01c5605400e454280d03080610240d0703c181608031414000148032003c50340c543c4041042e0281905d8100100003a246600210030b43c10b503001c4d5122140d41c190f03900c402a400201806d002e0310300368887c102114000408100c00140401101e40c0a0094401031202101d0904c441000901641e000009101140115401031144102552041000b15505c3c113010f008410080c41c0100c424014186070030060100c1d203000402d03180070759024600941d0311024283c84004034003a0754849044800c2c20783c20310182c15000113003181510000f918031140c6d6a41d94070610400f001c001400c0010510512038100491032004044045450103403d00102500000100c7c03815802280c082c4c131129610820f11848081682c1040000c091034030702071013550 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 20925815 1250 20924565 20924609
    0x3040203060606030a090213060e010609080d050313210e03160b0306030304050a0e041b0b07020f0a2105010605100f081302060706050a050c030705251b0f 68
    0x450082c00742c62154001000181c6500500d800030b0624940c0640111142c54004840d03201414030741c000c1c400380b02001e00c0003180e6944904001c8040321b200100501101c89959070544450380060100104000095071100215100c01305100050401e91005885440030001c01080064202c03421071091704a81c05081e01541c1c4010b0620030740d511542000d640c0c2c1c8851000034618400c40e400b031504000c0c4036100059a00c1e55a00701442680502c2d1038045080b00a03c07401143d181600941c0054802485040c0c094144041c20b0100c84a020346100c50131a21030782504689040403c0c29000584141e02031010840e0030b00902000300710580303100c51440e00d110409060403585902180822540600040300700483d11a0301100e150060041c0b40c0c0d642c0039003050301c050007045859510340c50900000c10b801c03d100e20226441000d10390b40c2c0504142c204c942c005203900c1c1e840401e03440c240c10108101d02103107010090303958041c0c03940c0b120080c10f4a130809000d4002e500754005c2510404c0300c403048c0c001c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 20927065 1250 20925815 20925823
    0x50c160201081305070305030706050709030b010e07030e100b030c0f01020c06030c0f030103080309010e0a02030d0f050405190f0806010b071101030e1e010b0303030c040312051605010f1103040203 86
    0x2140e0908004200d507680c4040c00e10403000e61200074180d0320500300700000344100071000b03001c90b90241c2414490f658821100341c0d18090140f0008148400550040082d8220407203002c2e0001214a40071585200041075640741c0460a448402c0b0f032651402080e54510341009000d551640940e815040384410f00000703500c0e6000780e8015802448000006400880c088040707401c12003115081c6030301d07942c490814402c2a00122034101fa95071070080307001c0c0c00d0b107170006603a4101a4002c2c0140100600180d080f5503c61050104e035041c48024040480c80382c1d01d240403c0b90408595451000c0c2e580b0b040180319264035241d024039519040400140300d06010f680c22126442d401c08140d140516621700103d000b4244e4007c10007245c024541c44041e1100c2004560041540c044000d010344c02072107041548074802664000c02000040104000207281c041b420001c5440c00c0c01d141d070500c2404592964201c50001d41144d80b0b0f5505c4440304100080c40c842c1c0064141103566090440c5030a90100b40e071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 20928315 1250 20927065 20927107
    0x6110601032001021002040803040603060b190e01020f07080a060c050a020c01050f070210030504020f030c0607020f01090f0303020303010e0f04110405090c04061701060501050c0304172b0201050c 86
    0x3482029080001059000b041050101170709200e0440d0b4035603076109041d0b26074119004010010f4113203440040d691a480091701c007040c002027584104103080c50001e0b501014446041e03819401603a10403c43c00005020304401822004007402d01030040e071401d8405c50710a00301803424048107200c3c04000c96400101c41034000002e0034002e6a4904242204440e402462070096008031100c2d003509060b681500305a001303520a84100041e03035004070415841c0c8110140c01c54103c02e003400400090302e0400d00d003424100c2c042c1044503c00f515580240b284c86510303002580503a000200402c11084510725140c4d01c00304d0070303c070740c80c540c102659245810841c840d45a8469030f225804144406c9082c000c0080b01403006004204140e80c0302604c00100e62002d2034a6081e500c0c1003800101540541c1c2121080440b80c0c003c1d40c0b415003042864000c03074102c0002d10003144913000709405044032410301a41c001420001c88187c2100e1694001e0079900014084508010240000702c800b48815120040c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 20929565 1250 20928315 20928353
    0xa0b07020d08070c030203120703090203070e011206020904110c0307260307080a060512070807090b060306090901020f030a0203060405090c0619020c1005042c06010305060d050d03060611060103 85
    0x11480a0781001c900d14000c0c40c070341c1600c0303d40d0300041c8091a50907034022f07041d040c406c1e42a07664103036540417521400c500034400c079070080708484000800250f0950060014100c014000501010140000422508440a100c80d0365100050400502c0250311000702d400e48411042c905110002c400b01805000140c2481c003403022140124203104410b40001002d400c000d044100c40c4c1900079001e41d81d0706483c3c40b0f007002d58082c000c00424408c010b401802088540948400d1540d2500c405010f40b02da401011184030795402d0000f40e484114607002140030780c00c1d95001603180d00342182007004540d00a40301105035840460b089200b5190241500e1805180300d0380321409068101c0d040c8d003001c68024a00ba8001000303c071400409401001900544d0040031916404002c00544400d42c6540d0240100141d001140010750b21b620981017181c0c001d50141038410701c41e0311583c0305ccd450010320310313010000309803112824000300740c0c0440151280391003c2c009041c55403541d06c401e00c10707050308100e5039 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 20930815 1250 20929565 20929577
    0xf030602030901200307030608030301140105070302072102040f02030403020a0602030720031809040809040906020417060103120302070b1506090a0b190e010203090f040b120a0b07020d0807 83
    0x380b0140c8084d40500800d0030103200850b64602000c0180415a204680a9001c00d00c0c0c02004203000c40c000042c1c905803902040707030110a01483d4015290340e00f0582d401c4045212700d600204507429450345c04441c400000c078a02c211090188100000e68a01500e8080510301c18420007002c05c1d400102544900c2c1c2007200144c1e82d40b640e06c0c0032180029100070180d44421444120390159500000800c040f2142140d8220b10003240020081c1c5000b0959000d005200700b440510400e103042e07441100b0203031140100500d040c1c0e0707580001b09401104100c1440d80e810505c01001400710310035140d0584030644c60110320b400a15600c101e2001006005a62411000c50b90307030032241c0712242212210f01c801400e2869079a0f85904941c2650302000c0203000c3d100e60803580b1618580112100d0080041c141c0181d410041542c0c144140d14400c41403c0703502c5074682a50800d10f44501c120300c8909003a64000d03100100050400581000024200a08640c48a003078a501107a129000ca40c219409280070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 20932065 1250 20930815 20930821
    0x403020a110f04020c1b03010c0c082206020a1103010501120813031b03060e060c07030302030a060306060602030702011d0d02060309010f021201030302100c0807180f06180902040f03060203 83
    0xb1844110205144035007240c400580d1100008000464140144080000380d4034841120107041c20f070f44d1401c0710040400c40480a010002d14448041d0000049003100032807100c40071884212540f2072944440c000d13070407814000003408120241d51001034000c2e00203014951401d000302078451b0701128080c2c1600404242c088400b200c040140d030046030080301d80b9104d81c0c130b90f003c0e440c9d17a0901480100e0b48280f61003406036000201017038442c42405501c2116051810b15201a000380d40020214060b0580c0c4403c0800011110307c640310143c00c45500568a4288520000d0909880d4500c640c0b2025000341c0c0c0c032182d5a03075183c900004e590b130548030944c40340c41c1d00c2c0d000d501610245502c2080d2078004a0300b490741d503400c4503585040724045d03404c454060203031b0640c0c04100c85490541c0d0740040d2030303000003a0200b40203807042600015420444084140c0d640c03540215081c0581050700001d00d03090710011340219001e040400b50030f020808600e41840c02c07030070103043c000c0340c80b004041d10303004800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 20933315 1250 20932065 20932069
    0x1921050c04021315020606010f12090b040303020d0c02010203090c010e220b0103050c090102250e09010c140c1902120102030a0b011101062d0b1305010207050105030403020a11 77
    0x3401200d00181055440e00352162001082e240f143c081d801c5800310200ca003051183c80020300d41e0040c1c0741038441841042e0048800c96014403901c41700c42400c2d440345001c00006e4000075115100301d000faa001070320303000c4a400381d00c103071a40c568406045a0040c414400044808110050f040109080c0002500c01180200c1c01400c020907812409032501014484034480c01d4002c011080d00036a03081000342c0c1c0d5903003841c18a0181020150040e40030580c0305101d04411403203102503204403204015031507920305104010002c00ca071082c1c0140d444070400403050ba08544008440c46410582a05021810004981d07034058080300f0350442a081d412072040d9103a0889456210f5a1180259540e140010f041c3c0041e248800e0b1035400295203001c41c6032941010700c20242520b4000700d8010303a11407029070a0151600012802502004a8400065900750328005028800c2c00c0034412414925060019040402d00d40c0039505104007001007200095000c100b0408607540072954000c000200c02c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 20934565 1250 20933315 20933323
    0x10807020703150f060e01140906040c120903140715050c0304121d060703050c06060603060303040504020f0903010e0a03020f0102070314030a0b06030903070b0105030a021c060e07030b06192105 85
    0x1000d00c0c91411001d0004c19525034002c048c0081c0d1400b5500c00400c1d40322681444111080c6510020000d250450201f8481e0840c7e001000d500d402450b15004c1c05030341c41c042000c0d40c1e004000c12210f50141d800c420b881c0114a0140542c001d401207502400d62819448086071165100800001c024594004070707101d411007004240552000b03040ba948644407440c029007550302480c0340e68001d21414000170700ca45410000c0340d100d014003401641c1000d00c0e08040c04040e4102024040c924001030014545540b4244503a04a0030800d01c02000d0400c240e00340a82000004003819409900400005020942184015070300c3d08020368810f50705d80e24948044028008411203517032200c400000c0c402e03641d40000207840c045016003040c00240c0da8071010103549200c07024000303400500d0480c1c644a0350301031401940d10517014101c041003404c4603c1400381000c0c180e800403640c5800a500340a05803c141032614001a843d20f000101d1a041403000440e0200440b03029001040c0030295104001c0180 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 20935815 1250 20934565 20934569
    0xf020708070f08010e0f0d0509010c02040e0607081302010e01080408090d080a020d1b030c0f05010e01050a0506010302130302060918010806040201020f0a15151205010b010807020703150f06 83
    0x5040d80c00c150b48070099988400031a1140a00075030900d05100540034021a5100388085c1150052413610890f41c019241c5400c80502a8103000310000c0d684096290341c000d400d40304c042900604250300e0020000781250070094400d0404906d503411420050341c108800c042500824204018269142d1404c0f0b2940e1040014150304455180d0a4404010f07043c0041c04a03800c40350240c41c02c4050080044130151142000d00f50440704085e4a1004240507108404405024581e690f1210a040d114682035540c2842c00311441ea5458003040305d100007920509820030024030b4158900001c2c0084001240e030036000291148400041803d0b09940e145480c40b022840d002d115000da607510781c25a40c884d45d0850b02a40580a086a500084080820041c94080d40000c0044034000c41801c58001007030380341030055040c280a6004118411043c0760031003903a00c62800843c80780413001c0010080380307001d4040029544460b40510005554910a90001c503064400295034108032601d080a03001c0f40e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 20937065 1250 20935815 20935829
    0x7020d060f0c2307060e0319050301060801050a0b09040e03300709150507060603060615030e010506060711040902100c030311030f01060e0a03020301020a09080c0603010303020c010f0207 82
    0x4810810101c89294100b86a81c41a54950441021266502c225004040002c10801042c01c0068030700081640c2c0c42038030100e03803840480b800d0140741d402e0144000c00010410780407900c00700041200907030000400307000d0081075500d10ba11900e8850f2480240c080c1c90b400d188035548a242d06441d1403020400e40340c9030140c01c000445049402e021809080301c042540c2140220718800194955002c1c103d8082100c43c0f000b0320707507113103d2102e0040710160480f0350100c45603520b0305000004074001d8011100a80002c603441c0745004650100601200c182001d00d004a034180303810402d541e5100d03000e039140e1541004002071000c07030b250000350040012280007907000754500300392040f0310344c000c98064030f1078800d803030410495102c002086545d000413204200e0070590000180a207500c660703002c8d0706104020301207000260f260f03400642a600040c450000041d02c1c034008000c012001c01c01e5802c070080c16601e00c3d20319415518020b40b640910040c4505000c004c03255917640a100304443c500400d01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 20938315 1250 20937065 20937071
    0x100507080a23040303090e0903030103260d0b03010b04091e1a0a060501020d030e06040311150f06030c0f0906040b0d0b07020a030e1818010b030703051c08010b030a0207020d06 77
    0x1800e0303040c00d40150106400252418070702003080e07001c47e500c09004500080c011400d41c0e10310b951711301e540320b8040078600407203107441c1d055441a030341c101c00303081072002d600004591007640c1402d140c00c540502e142140f059041160301008150303481e0404600c07a21550145500300000e0030215120ba190640608080103014100200e01034550701410580740268242c40b1084004d0380120300799000e0402041c055007080003c40d0000e4000c04400040394804800d4500c02040c404010031a2001118514901d40340d0b501009040c0c501440009201101100e401e940701c54041c1c04030f403880d003006080c68000d9650301d07212000c540c0d0340c4ac04103071065030160450005141811000b034541c60f0030201103001c0307012241910140d240071007184902400c1400300500540c0c1c2c00417a120ba40001150001c0030b5513807294004903a841c10b01c90303503001d5800342c0010700e10000001c01d06011031101c07014240401c00c00c400103000380c0a04404898000d51070200160b1504404c3c00055500c07a0049001414540703 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 20939565 1250 20938315 20938367
    0x70306030512070c0b070507140f03150402190602060a09030219030c1a0402010c030e01180b0c0f07060203030a090804050406171006060f05070f0803010b030a0b100507080a 76
    0x141c500010210540700b21362034403500ba03907408100c8480c0200c010041442c0c00081051200ea1400302240081d020700900740c856401030040070038200554082c070984070699080402041d810600355120b62031252001c82c103036280c9003da0080d110300f4003130f000060050b00c0d4242002454030070000800d99008081e0040c00040b07041c078014018501c1000c08551411003220074000c4102c0804195200e00d030103071290592804a6501140d480e02080ca4042c14040c04034900719402c0003000032107002d0138002001a9941c1090728005103421040c0410380b2050b800381c10288051680441030f1f03900440404004104010340d4609a403041c02180c00464200340344c2f03000002c80d0075084aa94284d40c0111041e42c91807030078149140180d0740580508404690340c0150405510f02c110000d081e068014032004a0125084c1e841e52550b610030382c040131294074017000307011403000117210340c4500c4c000c00c44d401e00d54480851405421802045d00141141c2c20104100940500a0106041000c035402c0d04441d451 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 20940815 1250 20939565 20939593
    0x402040807060809030406050d050403140d02041802040311010c06060e1003060c0201061412011805010510060315050105030702160305010e0106061803080a020f0a06050a05060907080705030703060305 88
    0x1d0010700c03820001944200c08590b0220002c0100e07401c2d240320340c0d11240b4001d62011031201801014108804000340e5212500d02500d055020f04403450300c0a5025a5962400b40c4480010701d9200300c80541a01c108000c2000820360701c44003180e10020b0904101c0100170341040c8005090031b91111003904d14120401521000840150090300e120704d03001c1003e400248822806c80c2c01c64000c0b51000c3d000100c2d124014901001d0a51000e0141d10000c0340042070200d071001e00c00e00151044440303039100c000f40309005002d001044050070751071408101d5600403440070608070b40280b01c0e4505000c40040071440d128824009140400050303041f103034080c1d03502d10f890350080041515190055280420110f105846480c101030103801c0c00d80b107005481e042d074550f1300305039000090080a5128030010f84012801c244030f02d50324a4021140018640b03070540c5000140c5800406103031268004004024030307260490202c0c1e4000c2014640f040c2c42e55100d1a05400404203a0000707400f6106004042c16070b1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 20942065 1250 20940815 20940823
    0xd111809070e090f061b0715141807061b0f210f020c060d090209071e0c0b0f04110a0806100b0301032402091e010e06210c0904020408 59
    0x3100000c40d2010030f80d0340c01c2d10590712100040c1c41e00780180c01c6200401e0401c5d07807170440340f032584246600c102d160804660783d0009007516048100c03203860711031804003c07074086d2502550b44910501c192103001d400c00d0034590307103902883c082e04046c0060901c0d0b00070520599150b01c940e0981c080710a04140d030039814007418030704000f1000c3c00d0203504d21241c0c0044030300ca1055141e4818081c3c005041c00710040c1b04001c0760b81c000c41078020406a65009040150b610a540280108003c0d150442c00c0c94030002c98043c0020442c0e034a90900040701402c030001507540c511135910280410b01e8400584844c50b00e2001a200400701c540e1010020502080f00c12010036810301600b0560203241b915683c030801c1d402c05000911015124220301c2001e032601d002e40c61112806c50351050030052406514100003916080040c20a219516140c201c040065800081026406400300c0341541041c80e5105400824011080507c8101081c100031440480d80e01064500d5207200510030364491b501d480601f43d031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 20943315 1250 20942065 20942069
    0x90112021002010c02190212030f0705070902090a0302061c1109030c030f0a080706020904090303140f1b0705030f0a0c1e030c0602030718030503180901050d11180907 73
    0x86100030203004040c0c20b005120707000030a642a00a404140300d0012030203880720100105980094001031040810300d018002040c0f0723528108450f9485030900e0030114a0603d00c1d40040655520410048101c7c0d42c400c800b07101100d5046034840c0e900c1c8441c8001965624003065040c07041c40c1440111181d00000c40c0240030b04940c00e40444451282c464101540c448a00201c0d02c5d06030005284000810b424200030a619801030714003611345400340000c00c0c1140c81003901500042c0d0350b01d0300c80c680c4074040c2e000950801e003c6220580c7c0341c10802101c1008902d168982c10001100140cc1c804008051081d02c900180c0f42120680b640e0b21941c2c060183c010300b2500b00c4843d00d00810261401c10711400c0781c001281c051303454082071401503807590002d40c000b800b01810710000e0100e829940d4004a00c01018510071809907844880d594900c0782421940a041d5102d01180c10041c000c2d80c032040c0c6115202d23500007194200584000d00842c0300130700020100404807181e40f0810541d80d40014556003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 20944565 1250 20943315 20943319
    0x9050a0e0706030b01030f1a0607051e0703031d01080601180b0d0506040506060a050906070c0e07020a05060108010b030a0b07030902060c07060813080d0b010207120614090c01050406080406020909011202 89
    0xc041e203903003004142115030132401410406444508000142001d0340608842b501c200b08403514001c0400c15041103c90303407407100315107500141e404d108040c3c2c0002100f55100c0a0649100c0400707006002030040c0400801580c100480d184141d811009000d900d10020400610700d140d454500c00e29080140038206c0302240034500b0100460164149402110040f10490781e800b41030041103401c00107258404502130305c8901d00104003141c200c42001d0918000c0c1410b07002041603d1251602c141400070590040550ba45081c050303031000d480104450000583c800e001c0b12041d81e882d6000c0d0002d249035036010b034014030040b40440c1c4a1000113018019203240d500c3d421a16901d5075002c44404010300c600a02078a0f0502110501c1c0380729410080c072200050060f140b6854850560070b090082064050ba14680c80d0028a8220401c5081300f6400c10342582c0504500303101000082d00511940c8201d00030010a00300140c140700c85581980d0800a000703024103071a595480e825880048078076002e0f4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 20945815 1250 20944565 20944571
    0xc050304050d02070e070804050307150e01060906080d081009051f0f03150207060905010f0209150306100809010e01061d0f0f06010c020114030703090b0108070e0109050a0e0706030b0103 82
    0x102c58000200203017250b2600f04c03102242c0d07440e504110b8a10300090f0088580d484248841c6c40000c5007440b80b001c0142034100300264503248000103500390b8159910002c0f02c186419414040c620011400a01e1026142083c440c2c80d180d9200021404020380d1100300c00300d140c001401507001c0381001e0900d4102c04c0089040b005070305c400c4508218005844003e10a1076208000c2c0440307070b8580c01814000c0e0007007c1c006040c602035200c260030345e441084900c180039400200d002840c0751041a205405520341c405a0a5140207400701b02282c0540784900e09207c1100005000d00609401238115489460024055243c1e40d440100207800c108149452440e12800001c005081420100d032080000c02d18003ea16203504d40155007043e1851000d03810404244209005004640001c50088145560018000d007680c1000301034078606800085607900528001c110100c80341c40000c1c151a8024400a00d41d183c1d248841d006040080100c2e000740200c01c0d00040f0103400d60b0104485d02c0c0207072028 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 20947065 1250 20945815 20945833
    0xc0807090e03030a090f05060f0a14040807020910031203060e060f01090506030601020c040207080301030b090a030804030305070e03010504030905011e090b0d020c0f0703060c2607120c05030405 85
    0x400107986425045404a90061000415140c00358108000341030085140002000c081e480b0503040040480d10700795284090300520072001194400c541c0c0e80441d41c03280b844e860510f41d403070600a114004010344502203800104803203141002045000355442502d100c41c5046546015000d070149201e40d529407240d1200080b1541026810203100100583d542c2c0d400a007450108600b681015000604603c030395030350032229844a02c01008094000c2180a403250b2561400740607041c03008041c11125008100c03000e0000c1d0304103840641003541414086102e07940c0340401c072800007108843c203a0560030282400f013850f1301b02d035001b8299082a46d40c0d003400c080403604c0b0ba000b001c3ca1048480010b460400c20071528410001403c034880558102614020304a4101c1d8540410901c0344401034100071001c0003000210f1040c6007407440c0f20f06240c54440ea01d001403a500d01c616070083c2c10707001d00318400201d1071481898040080407400004000340300c40214020f0458000303c608840d540300d48194 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 20948315 1250 20947065 20947079
    0xa0608060a091e050a020d0608030405030705010212041a07020402030411030d020f031c02040305011401061d0a0501030902120304060906090e0114011101020c01020f1c0b0604090b0a0806040c0807 86
    0x1500100700301c0c00070710f81889203014101c48000c0c5001006104025070034441e07019003031014010708006051100045440754207100425061040d241d10407815540078a107040081021107054038101d0310600c41800c0310140b80b800b90b01070343c440c001000b54014400001c0204000c500c50000c04400c0d0306500302c91654480c12826030b0344000c0208860300c0b640c41485980b00345410542c03001a800341d603030350150512359290f882a0a5a0306a2094100c0b00407410051203907070740c005000300c4100f00c2d941d00e004220102e000850486d030b140d40201410551500f940006645a076009a501c982c040401c4903500c0303039a401d0042022805010f00b90003d40b032048005107c20003c070fa014140c894540041c850312170501c00654804c881502c28010381e54081c00740c9290300000784050720494420845655642d446030034482c511400a0f60703a400d0240c60b01e03480e440d49440d0341d000e4409031440d8890002d4182c507000d0029500051540c00400203200300401c00c03040100c1c0b00741000403907507804100d0f4600c54840e00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 20949565 1250 20948315 20948321
    0x50102120a05130803060f271902070c030308150901090b1002010218040b1c0302030405010905100c0303050717040606051009030f030503070306030813080d11030301031b050a0608060a09 82
    0x80d001d841904c060002c03c03114a4403030042121031500501d1143c00f50080c800a0300c1e800f8071440031a102c0302401c400c1020007481c070300c140310340600c5c05e5008501c1d020050390343c0542201c4030700000d01046000ea00240920701040018000060001e0604c0f401d503a413458600c000e48501c01105000300e801a115840c0c0c280140251201070320140c80c0c0210514101d07040c48001d1403440710950b8003402c42c2810304024500050301c040864020b40c00303590340b01d05010015181f00c8480e0720282c000c5884003a0741d040240d000048012880d41407402050741d0312441d03002c03030b1a22981c01001d000002403609120800005901840856001751781d6041514048001a1002c50712444060003003c4002150750000e40300d00700941d403104046c00c0004a0b66103035140c14480b0341042c0001c2c0c11413540e00005010641d01041800c034451030600d044c20340d614021032810388230300040c8001410b024120241e14001d08100d412b000141c000071300203101c0c140d1341b0301000b0104142075a4182c010304100c100800ea0400b180 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 20950815 1250 20949565 20949601
    0xf05010b06120f0601050f0706020c070512060403030f0222030c060804050d050a180303030b03070e07090b18040509070603060506031302060a1106070c020307150903030c06020403050102120a05 85
    0x85001420795440020100305400004c1190b07040080070400903049a04660240c644240a04001070319400366070070a52a04c02603420103885424541c1140348000c40004005601c598989070114002038156001c0e0045d00072000c00b0096844540c9004608020a12003541102c1c050f90444e0f119607034407001910b40001c15240076007e604002604100316018a008042014007880e02601441c1526000841855940c0086001070b0b2142840c0006260400c0098080d000440b4260524106450b02400e48080d5114500c80c2d0031010030011103020849520410340f03c009003080c001031a000640b10f480d100180592008a490b0200202d01424903a055030b2041c4404607900e42071051301c3d0200085500441c40c0c01007044607140303080c112400c040c00014058601d41d107d1204250b0107104240c14203c0039000000107107104010049510740c0850304504032505400c0403003800181e400c040010b44502c0d08007038010360000a507000c01e0006800e00e0303403090620170310801003a25501c0d0503201c2c1c44000c0e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 20952065 1250 20950815 20950837
    0x2012307020a021c0602030c0c010b09070e04110f0310080f120f030a09120503070f02031603050a0210020c070303030608010506030c04020c0106030b0c0a021c02030304032a0f05010b06 81
    0x208203841c010705240c2c0c41c14613000420000c00f110034140d55204000e0380c0c000c85030310030039040104602380d8910090240c1c01002408a030003050718501002c1c010462910101c202d845207481e001510150b5544100711904010010040b559070701d0034510f80d81c0b05204610a0450328850011080128500401c0701c00c03000d00310040040c50510182401c0340d50b500041e020040040c0d44515070700c000f840b0043d400b100c400b41da84075151039160044000d03200039848154607044d900b04100c85202203a600801c0b030501c0394581402030b200c50842c041246008000c50306205e0140c4000f80b110604c00d800600303a03003101d12070341d400d000480c0c0b10105a82650801c1e1400e6405a2001ca000c1029180540107040240d2102000243c1a0b035030f038a0b213800c485810f40c1c440b20400d00c00515003203680e9050004030369545030620115460845c0c00002562444000c1000d4100154000600e481e2610b1544808000c441c144400d1440d01490511b078104030003241d0112101e40c6804480c411034188030f000d6031068200c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 20953315 1250 20952065 20952073
    0xf09060f04060213080a0c05031002070512031f060309021302071208040510020403030302070b0a060b03010603020f04030f0503120109150603020c0f010c0801080c0d02060904020901030b0a060201230702 89
    0x129981d1101079040402c4050100c041d042c8040340300c45d020415440240d0245066441144c545014541020180103a00c4500c1780104400c03008141c0001d0700c0c505600b40c020080303603a541c3c0c0c030a0a109010108040d030700d025203036510004125a054106444c19802200e540b41e40308008090402284100d44c40101142c00318004540103500821405034480c0c0601e0030f5401800043e40071030126442030300200c01080e4041200d8040c441340c03000865009403544800c100c941d040c03030b0b031607405070205110301400c06400240b40c4980103048019a0300a41c2c4c8003d045403501c0092400036101c4d080a550701c40e6403a01034000041c00c1c1500d005a02c0e842d907080482d50700140c20035104401950001201d12114401d21409500307418003481907020301405555554115414841c203e0300f00100c4140503849200c421000102581e10141224002c2004030350041c0d941c02d080307005a01038240790008543c400c03425407001820740c1c6c064200d031400344950401200c81c0305018900e2011500c0603a610001a40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 20954565 1250 20953315 20953321
    0x6170103020f0f060f0a030e070b030c03040f1205071109070f050c030c030408060907060c020609130902030109060506042f0c0304080a050d0e0105070b190902040f050f09060f 77
    0x20000c400420185010309042e020380f5000010a031940c3c480500c90301c06000010f090030405516115010580711000050840285400510642d41c000a001c401d40b070440000070604100e4290303180c0d581580d01c40c900341c1d908601c508015241d1742148a081d02e000c0c504445c803211600d0700764151841961180c807602030b915007621040b1890303005440c1c0d06640c0d01c02042038903c140340c02c001070801810808010010340c541402e2050501c15103912200074008a204220f00503a00c000c01d49039038540070307203520403104401c50012000d89000440a5010351803c4503030028085035401c0980b0505080d10144154100349041821603500340c082140466a08070100402c110386500520042030a102140c4c03c154403180080c1c240241000c2c111005d500070400001c0a91300900100300070000ad003401d0b81091242e0312011241d10000b041c0c0b8032602c1e039000009031000001ea0290b0034254028108100000490a1040040c041a03450201c8110907030b0000c3c50352a00001e10354414188080b030314001d03031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 20955815 1250 20954565 20954569
    0x70303050903100504060c140a1704030c021c03090b0903030301030204020f0c06131505070e0d03110a03050705010b090105011d0406030b0f07031104060e0d0204020d0204080f070617010302 83
    0x140000892035494050a0950043c8020318081c0381e004602508001800e4440c03440054100c250b482030040818005201340718020340c10100c9289014100801d02d407242d9254601140c4407201d443d0003d510041c2c0d80400c03018107042280546841c0d04caa100c14030155101e016904107070103503103030140d0701d50b1040006200600b080e40260040f0401200b40074103194603600c007141008811905c5541e000381c3c0040c1d0400f0704c00070410480c626176825000b00300508280c080100001d41089529024110600071041010700c0f50750100c00004480d400d03500c20b640146002002130340030321015500303982001c42c40b00051802c5500b40c0e0484405845803080c107102009849134034861710705100d6106e5030300d85000000c20f4a0085507482014080701d070745c1c1203203022407010303080f606400c4900070180d038140020301541ea00032407040d0000744200c0780014043c004d840014040d1240c608104070040c000700700010b50302400a41f00650040c4507080d18030700c030b880f40d10031580428090a150010240703240108054 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 20957065 1250 20955815 20955817
    0xc010302160204020403050a050606040209011704050a0503040605090a0f0605030103020d05031624060315020c0c040612020102060703090803190f0e07050a0e040b0f0903040801090c09060b030907030305 89
    0x46000144480d445880b500043e04076000342c4d000343d440e60081c52852003000801d04c402d96114004039030441c240410280005c0c1400074840d4100c0c152451080441c083c010204200411151300c0412280c0c1c40d03455010042041d004090320b01c0c09011030620101d40410307d0300400042d80d0403a5200c508580c40e58080051804990344152094041081020240c2c0c0c9544c290703000c080d0141c0d03e8100381040044416030001d4035001078500103031510501740006091070790643c114580313198016807505030700089030f42002d0203094002d91143c84d1010000780b0345030b00100c0c520054001d0b000d03501036035106082a4242c0780803550007801c81d9400c00c0028040181940400c414400808001640b4060002c3d07a40403181c8a180301d0324290710031b01c1c0c20450307468084800c0c4054924401009210f042c5a03991945c50f01e0041d0004522030a40c100090780e041d005c1084d58002e004002c002c1c03140000b44e0a2410f2461610700818010a061400120b60400890100ca002e101498000c2c9042c3c0d2554400b1104c7d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 20958315 1250 20957065 20957077
    0xf0207030b0a09080c0f01050f0f04050616030605030a05070305061e131103010c0915170a02090d02031005010305100c0509090603211201050f010903140c040615020610080c010302 79
    0x7004d6000c0c0131101a980382000100c04440341d000000456041403200b9a80c8000010020010b40f02c410b0204000140080b500d80c0d0000f1030482007888004290205801030502d0303800060b058440c81c03d401082c0310002900808581c029810758400da21006811514070340c092803000c403c3c894120201d0f8240e0b00040c0002c1095002c0e0600e0350b5500c043c000042e0a40700c800c0f0408002a200120910084100307042c200388141190928038600300c5900c0821110340002842d085d00c155001c6801201e9442d030b08229048590b0050a40703e85500803003039140144000e00095600f072040d08803001c0c2000c0d4521900a9841c0c00b03807181801c00240400b000207401006000c15094020220031a24015089440c510015a442640c3c0c0d00c0749094414000320680507441144104280136002c101c0d641c1101c2400d023034a03007143e80b001503038189000316480c04440000c0d0b0383e009850b09000007948460740c028a21800c46c141d00303403a074036150f180e0103c100460900070094107401000410031598020307401065 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 20959565 1250 20958315 20958323
    0xc020d080f0f030702010e0c0f0d030503060303040504060303020303090d080121030201060b03070302071a0c0405090406111603020c0109030b1609030c1d070c0b07080601020316060b010f0207030b0a09 88
    0x12400102c81d15480700c0d904140c95501c0507030345032804000580024420304940340405d1700d050181038281000104030900c0144050140070000021941d1610240112400f41c0f9000c0c0040c0000c42e680c1c54020365a5004454503075441c06401c0101d0252440380381030300d04a940e615a0008001aa07181000b84007600340300c110190344da50000003c0c2a01144040e510441c02610700580304d00c1e49084c50865000078500e0240c4c03070a462070802602400380e0f415101920826a94180d45541c0c51400303400500703141c1c802411405c0301056450b000460181c40841c014480d600b500c6904400348015036803410749004c0248026140310001d140f5a80b0700000d03081c25180c0e440e00b600156030301e407075030070007008282c201071022810754603110055180003d145401844528000341080400c0e282e555408002520381d10402c0300c440042480b6038400c10560300601071400d4616410029483c0c42002041004c1030140843c00c0318111043ea10b00100b0250301f02c942110003084150f403481998002441c541c1e100300e03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 20960815 1250 20959565 20959567
    0x809060903040e0a0e060106050a09080601050a150215011e090216080306031204080708010c020a0302210403021906020c0102030a05040302150714060108010501120201020c1003022104120c020d080f 87
    0x805c81480410841c1d00034a80d0b51112030751000440c0004045070b6140d08003911541c840300c010020b545800041fa012140d428803810704d0740c611840e08038101001149090700211070000089044191807140e103100c040301c9149111001d42d80da02c0c520690040c429442c08000d0a2000340000c5a40c4800450344000d0042c10f44440c3c250860402441c1c0d04903070448003166018000610850305d00f40304000c2c3c0084580010900d0102e1a913000755120191b000785441418882609c006046488059070b01540c0d00424084100601c3c00d55501103550900c074480051184240740992540080304136000c4983c15a01c03545000c1c1560203000c041c0224200c40d6070464810410303140071802c40c46246101d4801c2c00c018108039450a150f980c20365006070400307107070203609241a90041c1c0e00051451103094090b101ba900c5071f40f0b0880250002d00031016950405039a0702c40e1421100300088a071071148e88240c4044802088455003144c407400f41c0d000081d001900010403c0100d403c0a000c0c00880c012890300c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 20962065 1250 20960815 20960831
    0x20f1905040e01091a0c0409020a030f0203090307050709060506041a0903060c0c0606010e06190c05120a03060b04050a12062304050c03010509100e010605040614010809060903040e0a 80
    0x100c1c0884184118410b030740d964400c400410805401c00c0c903007403050300c4d4400a48034200308039104400d1003240324244560ba800580d640e2500e000b40c01c0101441c08110045442c0d01c1c11010040d00c80e801020201c41d24064060080b69100e0035220b59400c0e04c101130905030509042c4007102180c42103025043c0844078050010041c2d65500300030340c500c01c2c00202c15154030b60780322008007031038524041c2ca514103101203d107000d64151030342020307070305480d541c407d071440200301c1c0034415141042d912324003409030b016040080b00c0c00b1054000401030402203903020002143d82d905500407034003803401100d0b80148141d00c00c20012040310a140c030b402d400344000042246288801c010a468105481080d4a004908101c24008241301120080c6410b5009003c146003184146880c2c030320300d010355002541d07150a10841d2003030960225000d050041c02c20040c0d1500da01403956040e005100c094006200080044d100c0f000105940380519100002181050306041a03000540e41c0182402d4440c0d68600030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 20963315 1250 20962065 20962069
    0x106050903071a04031b0b0d0c17040b010f0506030603120304170304050607030c0201020a0215090703081c24271802010e03010c08010e070507140c040f09020f1905 72
    0x9040c0800b4216030070f1581c403440e506c1d0041c07a040360f4004c0c203080c0c840004070403c1140c1c0c011080b5200141c09070700c0000c002d81c10910030f94100c0ca40140c1d000d80c56601d54100810006010603150680d205d80300781034000355130380d81005502e22007111115015002080c1c040301c002c0140018580041c4608480d010489502d0380020854004942c1a06c540c1e00542c1440405501403040b005074054610081d4a400b0103c0800395540c9040030841e114048454005a0a240d040c02004013071907002c81540d6695840c103240420901040c2049040ca0b85021280b06480c108020095116074500240022075440c0c2803070b450303a0040c0b4082a101078069600722000c50410b521480c0c1c1003083c03001504032141090f00004222040444d2044d000703a00d400c0b0400280c50700007981c5411142c1c1c46c161503440d0b6841e000100d0307150107038090003092203041038480d0117086c1000c5400d00d807031113007036404105495101d42c0b00e00680d0007200f4003a40058007682003003070301c2c1070080204403082c41503800c401907181d550b80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 20964565 1250 20963315 20963339
    0x106080307030f0f0804110f120d02061602070602100c0e060703080702160b1206040f0905070806060901060f050a020a050d090504050603070312081e07111c0206010605090307 77
    0xc200c0001c0d00f405065000c1c65000700c02c80c0c000e5003451501e0981840c290351011603441344074113014442e01c4015014402035940c070340d000f18005000820f8503001809500060f41d105810344500d00c0b400d80241210000714400900c0b4011140c1a45c010101c40d1150180e40c00240400c0d940070041000584010b0700d6030306c6801c010060944aa40c0c0d4804a18000b10000c0c100135030f195882e2034940318403034208400c803600c000b5514142d40012010300350740c03076040000340280418600d05030302a052040e0501800401300c0c0003012680c5140a0b20000e585407402c00903104d03000d014038408280400d01c000c0800e8860005050f810440e80102c03400e0744036a8560503d0442122031a03c005003110000740020b040c03a01446400140c10790080541c24103669070704000480218803401000f611038002003101d405031040c06065600c00c126403503181003000d00103150313400368420780c1c201c1d106171a22005884407001440302007030507075409050030340d0900c242200c16a111848096061081f40780104000300118 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 20965815 1250 20964565 20964577
    0x15030601061e080106021b03070e0901020a140705030a030b0102030705071502010605030316020409021c05010b09070503100614040b0409020a0e011403070318050609010b01030e010c0212030901060803 88
    0x140b1001010710440e400504000c0c24440d10b0b4082044903c0100500c1e0380004800b0000381c8400e00038945c400b132101c04a0b1801c042039009000c800540700500c01c0034030065000b4080b060180e1f4030010212501d000d03d040510481400401550081040c1d0324503a00c03940c8084000030052040da4a415901d44a40c0d1412a054010a508200c0d544544540d1502403149800070b1806030040c41c03d080d905440300c1090f820b0f21401a003e60785540320502155107490481e0800c01e099034011103480d540313051640c000c1413003c9903207020704201c401041e051070151040d2480340321040c0301084441e090400441c4c4c0b400c0c07102501440310070180404920302c46500040d1010301f03242000180c40740341c107010003001c02d01000c00441c1400302c0104004402180300c0f0490fa4415a01d090204907030854038102155108040c0002d000340c02a017050080c400c5064001b180c1c0000240d8041c864045405402d030308071001c0c100b150025134410400c0c42c2d03206040d1405103500a0340240002000c50380c0d00740c1c9506540c400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 20967065 1250 20965815 20965817
    0xf090906010801180507090e01091a010e0609010803090d0206090d0303140703050906071d09010e0a15062703050f03070302070801020a0813060e0d05070501061d0f1503060106 77
    0x40c40060161000c01d10034840c0130400f00b1020b115000c0035484058a13105640503444525445400030110000300350807912895500c4800d070815807951000041414900303000c0d02c9202040b10011802526010703d90605980000d0042c51504061100300040c02014032012604180b090107008055601c1072003a01c5102d0098030003103485021445c6200c2c1501c0c005194800f8903192806110f00120001111584441503040c01001c000d0f03081a9442e680300c0710005143d200c0300c034600110b600c1c610745950724014030a800b0184a01d04407a841402d80c183c0c00d004007000103100302c00007072040f0380c40301d1003001c03c150761079424818545a03140c007410924000200ea0b142d9100144010816604102082c000e004d203400841c100b040d401001403c1c403801400700400d15591a4149041c031810780d00900000206000311110714030384c050042c010750059a42030b142946892800078480501680601024219029082d6a43d66070314041c101c004019200082001c22800603181c60f440800c51507001e0802 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 20968315 1250 20967065 20967073
    0xb030a0b090604110717120106050408011503030f0c02040b0d03030509060907080c01210c09050102010e0304050f060c03040906030305070b090a0b0105040e030c16051009180b0f0909 80
    0xd00c1441588540640840e0265140a81890340c00d29004252104250b109120a10f007002c40324092503d400b0310308003082c81c400703504000030b0f200703400100506c2207424880003030114043d0460038103000c0d88a0b10010740413442406101c8030745449600d20070402403004000280b540d0501d404100c0b01e802644048009c039644009021202e034042114541c13001d2080020240346041144958031007401a1038a070501c50b181001814030410280344100c0700740300240c00c0100603602071000300645001c3c413940c3d026510f0305070b00141d0030740080100c3c0c00b56240582410340c1818120305100035588891094003050000380004140c0303015900440300158040d50b502520b070340c018113201020070405880c00399141e100004035000500b01231400350440d441100c00103441105030202c14218401c20001d02014001d54032000c81007110300000c003043d21410744400f00003490421055454400a0280e500c51103104403400b000180d494001e00344c4060094080204211030381c0218521010980f418030a50308 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 20969565 1250 20968315 20968331
    0x20c06041e02151b30070804090903050903010c021501050406030b15040902060408070302010905060301061d06040f0b041806050d060c0c0b2403280f02030712050106091b08040201090b030a 83
    0xc600d5281c072210505d04d02c04d680c80c100f1940e60380340d1640304a200c3c42c0e890a4480e8012018540038109131500c00101a00078030400c4c0c1b441c640252251100e101c060444e200d400c00115007418944038140513280c9c0050b04030034544450000358140100400301c26400368803040c2450068170b42c03c000e04000e240d4940200303c810b08510014081c12403a0300020300802c8c051004000441d4001c8584444540b803105060000d40c201000c0346142c4996040f5003101c070400302000904003803000090084414801d00d01501f040585100c009448851080d607a212002c4407a00c4045984c075800918065564100700d80060b01a40c0c6a0b80c0d0581c040350031040c4501c1d4002840c07070032031501c4004103510b00100d006d007104400c1c02e400c5040c05c180e40580d1059410300c10b0954402c02480c441e0040f0100d80080450351055a00d030b03280d00d004c18254508581079401e02c3d0000990301c016000fa00c1c0d14421054038805030031801c041c1100e410400801c241e040001c00071000031004009402140a41da20400c0071031410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 20970815 1250 20969565 20969623
    0x80d0305070e0d020f040605060c0d0e120a080313061b1101050c03010b070212030c01091a040b0a0c02010209130b1219020603061201020c06041e02151b 67
    0x9500400100601a000324503101540c2c0d03480143c4a2190704a907040885a4403e01003801010f01d500001c1e0020800111002c0d003210000d02c043d181d4001d42d4881c40c40003001010300004100e8036a00310380c15403214151170009034966014607440000204504050000e43c0c90300002d66400c200d2200f8070031205800c401845500080c0411400c0442d402840079041c00b5048020310b100510505040c1700300031580d0003c6546940483c0c0d0307500130f124203c9031111220551030f802410000c104803400b03d15007075070740d82e041101f128282c07290341c01400300302581e41c0c0c1344c00c508003400e8045808000c6541c2044135422507a20003620710b005502010001400e5140c0006100c003001803111035203000d0380700e101508069944881f2041e400e990594284e500d9403156808540c0c0d13286800b6400a0a50001c41c2040c0521000a0140e2041d8040c1c2c6004103000c0c910110080c0e000040c4001035000303c103441b0102c1d404045540101584100d030101c440b580d46110f001d0741d0414120508600303410708910b00b01030560b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 20972065 1250 20970815 20970821
    0x204030303060608060306090d05090402040f030c29040302040c0309050d0c0303050c0412080f040b07150c09030b2a0406031a1f030c02011d060402091f0302010804020a030c080d03 79
    0x4051b4002c03c0c003400c0c0300043d140e480c41804103540c1080303170001d41c1000329156501650010607609040c202015141d00d0151400010340c000c00c180800745c0a030500c0403100c4813141d030711404501038240c0d1500f8215003c0c080075210314084441850703121191180040d60030425552000c1096450501c807948502e0020155240506032480c0309205200c140402032042c080100381c107902120300c0b030780c4a8802c011000d481c000c036804050841e90120b071034000d000807051620100c40d2044420001140c1d00034082c0c1d44c2c4981030101404032040507000071110a08510041002c1c0c000700c10340414072038040450b5100d603002d0703080100042d441c0c684005525140a942890400d03045421554800c19036209645004030250075a04058407212a9402c0c43e000b903221031180400190050602501c1c0c5c0c004c01c1e900c2034180c400701d0054840b5000145e040200650014040146040d26042c4a1868004440289010300141da00140441d00040050b080601c4500146049070141050014014016040b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 20973315 1250 20972065 20972071
    0x1030507020102030106090e0619080f0c0a030c09091103010216060501050d0308060d06020c0a06062102090109090804150c140a0206040611010b03010e060a0b0111061503030d0204030303060608 85
    0x7560f0050005203c425004040c10707050b54041c1c40384002d25074404000640e40d422800c0002d40890076407001040001c0003190f0704884000d100122681c0e041b105050003880d911078880a00084141282404600803c1e00011945070181d4007030050040c1c0c03000001c0c2240d214003003900080315281188020000c0e2402402d0040608641a00010704075440207014804004c1c0500d00ca0801d0001c448100411a03041e42c8900d07400c034040356412155031030104010600f0f40100081410080728101d03d9010445101750a281d028080340c007903928151040340a000240d4040b10441d80a000218180031406559040342480b40c0d10361050490703500700354000f403500740803800b51900054090005a12040c00304c1d42194040d2400d1001c616124280500410b00b0202c0c0ea6415401d110142c110602c0c00a00180905a43c100802000711030b000151504481500c0d0064103800000000325100e050410720301041c80b003d41540c0c079224000c54210126441a0011801700396a9601440320300d52140d8036541c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 20974565 1250 20973315 20973317
    0xa0b03040b0609060102070306060f0e0c0c07060516020402030a0207020901050a08061f0e041209080f0a0803040206070f050106181a0d05120403140d02010b150304061806020901030507 81
    0x499400c06848801e880c210081c065400b441021020a010340d01c00c00600000395044401040215220503072880b06195520a101c02c070030304a000310740c00c254540c00b1500c549103c82c000b0002c4901c0c20009440c00d8000d00c481c101c910b600303d403200016071034a000842c440c2c07400c1c240069840025104100d540340041c4c0105001341c1d4504d00034440720000140c02c41d009040f0901d403003900e2800d102d0140c25003503507400c04030300e12145000348070170091480c9409184840b941c8416244a403103406466807520045100001548024072000c085006840150b400c90300242c00d16107415a152615141140c5c46041164144e6484000300015a07640c01e841e02c0141070800d0600085d02c20003411122000b019840c50b00c80c0380f0b101d89100403c4020407030b201c03009090f400b42607141c3d0740da420032a606400c2c49075207194074002c82914151451041c815200d103124000c0c104034140000b0003102d0701a8000030b00444031259640700300351103a0300103102e00481620542c030140c3d42c3c1a42000050035548084d03c200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 20975815 1250 20974565 20974567
    0x60203030c04140f04060303020a030f0e01050a05030907051c060c0203030402090a020319050a020703020708060c07030503070e030109061a0f090712090803040c0816060819020c0d0207050a0b 84
    0x10861800034001c54040311003080403c08148804070000d500d104440840540c090702d09500001050340124041d400d0074029200c00300341240c100400e0340c0c4006030461940c0000c0041103000c182c0c502031130155400c07182e40011030f640d498a1f41b0200c1c0c054900040c14542242101c5180750410445010b400d0120300720344091402d60038290b01240380c0e5980986185055600800040c04004405100007a03040640c8018806810300c1103c41000b584012015001802111404500d107600041c0950144c40019480746c60310350552402c40b8180c101514610411090b04821819035400b4060303107100a00030040050b012408070910000001280c1105000b000c0442c0690710503078503524640c4d0b001e4028140084081441c001c448002c0202d020000c00b141d10100500090018000c401c600b070301d01d5001114a404c0c10041c003950102c1d03c5205000000c2c0810000410071680940300841e414502c46000d030800e048a140c05003002c0d001c0c00440010fa1000c0400c10036440c004c0d258070014684050700d5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 20977065 1250 20975815 20975821
    0x513060605031302040905120c0d09050d060c11060a0203010914040213020a020102040308040e010f05060c0604030f0903050322060c03020a120e0603070203040e0a020315010810081501050a06020303 87
    0x7511500004018981c6107410144000640d200d035005128100e500406803101c020008106242580103070310503803428441c01500380e00d440e010380c0140d015144024020b644020090380c40d0009007414040303000400c400c408144860384010040c85002d2508003070096101d6042a003084121034010100242c03006001c001d110158960701103c82c1c4003e40b0000141e0380e0003c07039078180e01903c030f0743d400203054080020b4002040b08a000c0c80c2c3d8141d50301240800301c0303181d8039002c05c4200e00601e0316141654110b1004900040d004100d40d81040b40c160902c150b05036500d4503100d0031a00b2120340c1c0c040300080032501d40c1c1c280e14111040d80240c04d40342015880c0d448a52402036950700402401003030b5002010200c1501e0b1f02030300701c011160304010300042d0390b8640040020344a401c41e120300345040c440b00002c1101c90f2014002d80703100c1d06070a1180709681d002c50b401140c1030032016014a40c1030f54090750116809809025800da4040d00121228055160006208071144c1356409401150418014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 20978315 1250 20977065 20977067
    0x50403020c1503130305090307060302040801050109060303141c0516081f090506040b040608030403051603020d030516060f0e060105151218060712050a09030504060f0c0c06020705130606 82
    0x262900424004d0401c82c004032646015681403150101040d0300d07115102000480360b80c19001002500c24000080c00b82d80d1fa907070b0500007505e026001c0100810141c00ca08100c00d2055000b80c6501a45101d11707a51114050a825003202d0050781c000708800302e0f021802d1882c0c0e800601c00c1ba0070200c22111760700d4260180707180b0f14105c4028000c6000071900e031808a00d45a07500e40014000481c002d0041081590b55441195294814441120b81d8010901c44408288407110000c00300c913005000f001984d0103669044480d40d02190741e440c00c00f0b4081e4007000c0440d85500c10054145035411000034525131070ba45551420b14168001071281c00ca85201c0185e0b4000781041d1003a202c14400e0b91071498490140080c101c2e580300d0060101840303082c0802030700c16802803403605040f44414080000f07480da5082c15040d11000c03280a00800d00401080001c24403803a55515084076501e040d0340c206410f60340d80c1c0c1c0d64011682c0590700591003c1701c144420314106012081c00e141d2104108206c82ca442c00c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 20979565 1250 20978315 20978317
    0x30f0e0c01020c0409060e1009050609060108030403060903030213030c080c06190e150a090501080105010314010303050901050c0a0c0e090303010f05090a0204170615010504081905150a050403020c15 87
    0x43d114002d40c5c0790b080104c1003240607004080b0340305928051ba45d8150380c81264800400361040182c2d403038410171000c1581c04202041c6141a2883c101c061031800d411510360708003411100c17070101c041542c00c20a41c07416845922001000d18032481501d0207a518004045107400e025601c6076205010030001c0e06041540300d0321035007100c0d4650800710f803c0002c6500003402c000b10802a074080090008003640b070150312000f400c050701c000b41c80300071461740c0751001181101c8180c9c1c102c2120001a5006002103805440a803410001c140f411600e41100c5928190a140030789804a845005804043c8400020404400c0c0c1c030040b544015410f42d890101c43c41c609070601d108207405074041201044d200d4841d90110b601510f03040c02042440c250303a034101540d03654211a400340601e008826521158411411141214650402045042c01c50320041c00e0101c40d18208441038070a00d00c84601840041000c1e81c0b04101007007000403a444c01d0300300a07041c089904a21481800b0801220003411030800c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 20980815 1250 20979565 20979583
    0xb06042301020c060a020c090f06010f11070b0c010203090106060804080403060207060902040203070f0f03050910020c0709050702060a05060402160b060307030c0b22050a1502030f0307030f0e0c0102 87
    0x81040c010100c0e0800140c1c18a400c0c00034154021a00084010b4529000240c5030f00c42c010945104c1216035a0b0b868250210500340c0e10b05000400101004109511810010030920183d5041e504280ea43e0343d11441a54000d052016090b50040f0070807484003420f2249100034045030800001c2490b0035a100c5842d440303603001c000d180c03c0d80031401c0d00074041240c1c090461550301900855072418041c1000d0044070b01141c0b01800140c1c0d03050781c050910700c640601405554248010134003c06c180b4490406034101d03171000095131095200c0064050401e02034075000c0c50158000c1c10140c10082c81f01c00641e6002010b00380101d004204180100c541d030307a6603440d015001580c00382c403615000c001a091402c1755002600345640068041703040c0310418001d10640c030b5103030030481501410100d0081080040c1c440d09a010712501402c000006107101000300000440c81520315080d41005144125003050391220000f95a800c1c07101c001c59454824030f00300c1c7c80e0a02c002c0003034515500000390b8440e502 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 20982065 1250 20980815 20980859
    0x705010507060b09010e0f060f0105090103110c010603080901121103040204050c0c0604060203070e01110601050114040e01062003070c0303030f061205060f01050a0308030601140f070c0305010b0604 87
    0x50210280031296120f06000c96009118040e1541d56120b81c940851080c0c41c03030004c2c62140400300e40c00386010307414044000c0040c1c444509041c401c4005600600211141c0801214200802e29071080288a0100598800c03103c0a03210103401000400b10040b500048400d07a10780050030603d64584400d5952050b81202d02080e13030760300d04951404034007604464550f10302c14001400100806500514402c01003036650358030445001300111119080c00e944121903400100c0140019481075200301d0601c0a1482c1c160300d0240e44040b01c0030210026409803002513807450000d110703000030f400b0407072070218440000d40c1401c010361955a02c55500341300040c1410741c1c0c4c1c00c1148100741d950704180c005100300b403560381c0c0c404110700b041616610119100c000200350100003280618002291200b900d411150031415036480900645190b80001e01e6207884030414807805018201c05c20003802d02c3c6104090252340149146030150075580008006e91160a00344070500c0300e907025445070080c500803 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 20983315 1250 20982065 20982067
    0x702030316050408010c09140f09010302040b0301090b04060c080106080f150103061205030702040608010203091903090314160819020112060807030305040f0b030c0a03020903070e0901150b0a0207050105 89
    0x1180c1d070240c0b800e208942c0642c00750350901400e066241e800180e148120380480704240b070390204401c100103016080d50034203a88003588000500142c03c0513800f10340003110140000030000f503d40c0311040350f9101158101c0340b2a4850442c0403005034010507007030041c5680c1c02c192200d8141401d8030916044001c124002000949540b0368441c1e2103500040d004080e6041441041c25040c1001c50f120780c04090240c0c021820180d002485060500c2100d10655690300508030190f480b0741244514490807100341c0070003103444004400b203040541c2071101405154010072280c1c140c40ea85e44100c04041e4048429608002000345802e0340218030b08122560900e407a554400762541c1020003056140c00815080c03203185008010103801c00c0081c42036400b5140c61181455413003042030b45078803044031000c828aa0500101c00340e9030094029004840001301581e0741e1036180d1141900034507003241c0d1041603030344644154813051380e504034500c05088103c080a140808030007021f03583e41803a104850401c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 20984565 1250 20983315 20983351
    0x90c3002060301050927150c070c0302060703050409110405040e06010501081603091a10090c0e090c122e0503070e0702070806100302010e010c0b0a02030606070f050714060307020303 80
    0xf0034070b11804803c0400c8000d13861441d1041120b680c1d544540303001824030001d0001003008c1c0741103241070305c0c2a2a40204c002480b90704650911085070000b8078100e0070700c80207104c0829090004d0040010700d0591604880d2144d1070314017004207449030100c20250716007140c4010301ca5070340d100300d003154450350914240c0e106074401c00b02100185201e80c00582070178200840140b002200300151401961a40e0030f071440e01c0d0712500b200f03040f9014107600d40b02149900d110028103040c03031040c281d4464000035895086c001d039060302405c1038070110741c2d1058048a0749a2000111021015082c0c01440c2c074050401203801c0c00c020036034441080c0907020000174160300091903603200b0481c040140c07054a042d1102402c00412205048000307000490104c0d04101c00e20481e54483c1502d90115030300411110295224880403100079070001c1c0c81030350402401c110344c42c00324410710580580f15200d50b0041c10110300e4160540c000b000c0655401d0f2040340f0410500020b540d00000f030b2034116504a002c84c00d440303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 20985815 1250 20984565 20984581
    0x40203070605180307030c05010f021b100c05100f050903040609050904020a05031209030105071d010c020105090d080301031b051008130f03031401080c01020304090b0301090c30020603010509 84
    0x94075020300f65850f2142c0b00c0c0c08001c010901c1a61411a1003c9c0c0f5040a407041c001010b90300e80303d40321208a41c105c820b001a09032031600003a0007500294509181002c044c00381c4038541030080e503c6004001d240c803441e80341d040c8009031003100d038051940d2700611304042c1006e800a101c0c80740c51042c00d11505100e808202503581d4000030100411009013140c0315102010380c400816040b10341458429480c1400251200e80103070000115800c1040003009103070740400054524450104099041040c10f11000381030352034080e60740c0001802071320300540721740c50351404c41080303c008107210a8041440404001a46401d003005c60340090a08040c1015914400804480032509902400b5403071001e07503610078590160301c41c0ca0003a03040d0035150380603a21203040310b9403104c011204d14016481048204003040300d039400000e1400008001091014054136102034070b038039507000913918403800290495908550028a400381e61651a0f240d640340d02500028580d0205100b11405541c080c0000b039265 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 20987065 1250 20985815 20985847
    0x6080c0f0a0509040510180b0103080706060306020a230906070b090307020409060c03050f01051311040807030303021b12070f0203031c05070201110c070b1b03070605041505040203070605 82
    0x2801c005010303e50030b89440c2c10f185544100c072040c2d204000d4034000c082c2040154000f528180700d0703045408007401c0e901e150f6880c901c540c00000c0a4543c96503410f80440011481d0006042c0e88045664002c44040c0044818019207282c000b085030b070788802c0004036142d0702c0300313411740d07195030313080304d0034100c25a100c401c198258494280300943c4545884d60b008c08000750361340940c1f03e508c3d2a135001c00c42070343d0702d6126000001007801101c1c0d10003480e01500301c00c1e15007034122549100a240d0150300301a543c0c45464504843d64004030082500170403500a4880c02e507151821000d40c0000a161055140c0341c004803e01c10400d0240c2002c11110600d02551000c000b2129280754400a4020003c02100104014442555444010f500f03002c2c002260000c03510645615030103010140001c1444e06d041c0840c9035004600302e05007007580c0c403114001024140050701c04a80103103008140d0786054506009191003c0500e0810b50f442e0000380300168400048102c241d502505200707548117558043e0280d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 20988315 1250 20987065 20987069
    0xd05010203012705040f060e01060504060e0a050c120103030f0314040c050405070302070203030f030a2a080c03010b070f0c050d0804080c0d0203101109040204030305090a0906080c0f0a 81
    0x198000400091040041d10909540c0ca90341e00c01c0122402080031550151034050740c2c007800c0f540e260241c0101281e03140e8002c10003aa420780c00019859640c0d80454250f03241d607030001d220828000104544480c9a000722540300d610240e145150001222116159035010700024041100c1007110101440c003a40c0300c58049c0c1c0e20310144a40c00d2820f0710304041032045034000c807400f8900342000f10f03600368004d00070b85801c030358020091804c002070090100d03419040102510311071a06d56281e01c0b0380b0505501492582995568040b40b20f00302c0c42c2028298423001b42078076280b01c2003040100b001c0404078007a210000d074814010704c60310840381000460000c680e002942d021140346072400400034241c1c004c00032188a5030a440fa9041440e0070400801003d0300003030b4054201540d0301c01801c1d1075600420044240680050804d040301003c0b0b0101e070020303001200031410000d041046440c1500090000f0b0860f44410702095040c486402e480d000300004003030140242c610092100c1d070310b6840c1400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 20989565 1250 20988315 20988323
    0x2010201110d050402030f0304050109090e011503030206041119030602070311031605120403020a05090919030507060e0a03020d0e22050403140403050304030b0405011b0206070f1106070e0d 83
    0xa202c180d15884030004002c2942c00324840d106660803280f02490120a9a048a10585460700d0003440c0100c40f00241c0b60000c0180d52039582c40d01c80300b040e0303241c0c0f10b4094007071406940103100e24940b601c1d12070031051440164501c549141c0641c0c41402c07019400b02016a40d10600158403003040c0c3c0340945910501400e00e40890002007101d6014070301c01100150014004c40444a4514601541078454421404040d401c015926000e201c03604000c107207180c00940c950308039100600c0d500c4405100d40c0042d841200001c00028008040c40403a005072030f0504507a00140c91901c010399000381d038920341103407014140407000e07000c040141c0c0c5010f480c621045a081c00c00b41c40342c00001d51100103003805c80741180800c400c0c4107000e11400c10340c03050340e0680e91703c54001d500e014110b869040b0749510040003242c40759215152004c102c0211241c40c0e110030120b0f0010300d29030810550107002900c8503201d04080042c1b60f0100b0008400024049030040c8d010300f0018009007102004c611501100800a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 20990815 1250 20989565 20989567
    0x20c01050c030603071a0f0a1b0602120105091501030e0a0c1715040f0f110d14101413020312030106050406020106090b060304031404050a06020105010e1e0c070201020111 75
    0x40d075048500114400c40044040e9041c2a4481e0030352000c1c49002c101c0320050200c1070007040d0b86419170704010011a903160274500c0328240c0109035000604402d40089680540106034090011031000c981805802c1c01c5420032102d281c00864101c1121130f5a5000c2c1c1059150410010241c03424030801c503466401a00d02c4030b0045d1036154440b0040180007014500b40700f2025500300000604500b2405280d025030514541e001c15124400c13240c1803410203803505445c0310701c0860303156154201c0c10111407207810340010000c00160311904104004820540450a020300d961030342042c2e070702ca0b552015031010310600000c940e0001c245802040d94007040300c8500000003107440d51b00706005c1c0c0101d0712194001d20510742c64100c1c5034180c40d2001052a00510144041030000c1d0280c0364203401c00501070301d0541840e81d00d4000492071002607224802603507543c0014840300b0403030120668401c0110f441001c041ca0308110b11050b05c88000d01402c004000810324a04580c0b01707401204407218001803807 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 20992065 1250 20990815 20990821
    0x10309022106060a060906050307050a0504120317010503010b01090e221a0c1603030203090f01020a03020c0114011202010c050a0b0106081f0e0a02070f02030a030503100b0702090a0e01020c0105 85
    0x7950341c40c007041c0d504a01c40c440c880c00000d88a07220b10701e620290354907555040c0c211b40b604501a28250012581001440014400490504036084000220500070340d03c00c071071030304007000994448070103820090203a410411a58034590f00f00e92040304865a83c030250159035200700d610804100f0f40c20130820440c1e604144a01404000d00d03684190240101480080340c0b01c0d12002c0d036981c030074200d62094040b407010101c004a40260302860344450801c0039108800c0ca001c2180e0700320303401040d0710004260301240140c440d4409119525480440301b4180c1d200d941403491903d000c3e0210f0300000e04010741e248140301080001e00c00e0100c1c41c3da100b2280380c40f035610760ba80508082000c440b05001810318809280500c0c10f803a45a50403180201c00344400d5071186070350325010358400b0401b0707295080c1090b81c0c0d8005071010040e001110b4003d88d1041c0d140c1c284003190600e185603950002c000403200b4030281025a40d0b900019811807003e0000086241500d04282e000e8007580700380b0000b9506c2d140030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 20993315 1250 20992065 20992129
    0xc0a09050a1d01090209010c03030506030c0904060c020c060301030804030b0615040305100e0c010e090705120906060a05190b070c03050a0c03050d03090506011203020f060109020702010f0c1101030902 88
    0x1411140c504032a03059682c036a00e0340854012809103282643c00600c1c81122940031900030352107581c020700041d09a507100451354000c66010a82a10210f610b680d885a000c0500c135414000600b44503400c888803031440d45551210010760040d8007025190711041008651030b5070741c01901c20550502075190311780300d5a590400b1620352a00d0031512444a0a103048010b0064000c80d0704a2400c1058441d5a14407045000b40680e40000400b07890503c10308220b6000d030b42070703a040b003507119494071070003088185090800c1c842e03001102e9209a019646150001a507804100c11400070349000031081510340c01c5d80e0501c416601590f82c40502503000e0015840284541c1c0c101040a80f4000c404441d0503009640f021002c8501c243c0b03018045401c03050060040492902c42c10400711300a20483c2c1e03404203088003c2d41810f40c2139000c4961203038006052070865030444d4401c0e1f10030180c0e0828005003400b40d01e078a070100480c1d0790124105503072078150004540d1010650500841040b601002003120a86 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 20994565 1250 20993315 20993339
    0x303030103060c2715091d0403022109030c010c0b0c03060105040f0e060103060506090d0303090611030907080d0c080904090609050d030b0108090304030f020105030a18080714010c05030c0a09050a 86
    0x30305e10341c0c8441340b08884035043c01200004101e031640100c490381c014440b800305441d80d0f0003400441c118040d040c50b001c2000f19541301c10170007100400c6d01554804203030040500c0c04088171100c0b41030080c91300b8040301290305500c0c215403000c880c030350aa42c4d0b56078420040b212486075030440d4440050b0428041280880140c1c2c2ca0b20030f20082e20100112a1a003007040418020841203580c07010049003942c4c0007034482d80120401510441002c69481c20388100681940c104813016401644152000c01140e04104a001010b04071800c2031441c021b6a81c035049003c1c40707a071261a01032034a0382c0b1301d081000490380c000d0303040940050540f5400020000010003521100c10001d0015504e0008600c1d07070200403041b241202e23404a1480d00b441241e6005466503080100804419039586250034005409134005c51003c038440c1c0c29095448200d1f10302680321b0000600c000c0801d030716090f00026071715008400c89412030100d1000e00d403500322036030f0201c1d02c10046410040d0072a241400005841585113 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 20995815 1250 20994565 20994569
    0x5070212070305070b031602010519020c120c010506090a0c050a0e19060305010807050a1503050402060f0309030301031703060102070b09031015050a0b0a050301060c060f2412020303030103060c27 86
    0x10155400704d030f1007c404900340c031400d4900550070130601d011038200600795401031000403a501c05460603542c0d0b03038400d0305180c0c210755520b2100d07075107c0040001e94941044210b0380101d1040e410020000f001c58001e0803801016518010311400c0c8000e0032507239840c4c4203503602103c903030098030164640b42c001c0103018200070f00c0b4035a094841c0c100d021800d0b03d00340010780c05540706465030f0000403001d03440032030290101400c26604500304014100d6000f001c03a000b144602551002150703203525600d450645003040c40085154600d0034002c0c0507150707034040303640710490300900030359070711481c80e00c00090502001c000240109498812040c0f07003444d01089400450780119222100541d9505914150340b00305144040016400c03c014407050740503900321802070740680e4001640c0034841c800b40c012640d098020341310071244509001103402c80071010300050b0075600c40a007081d000343d074042a0390f0301040c00010411740d1145807080003a445481c03924602c504034010f00c000401c0d0402200a5400c0364 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 20997065 1250 20995815 20995831
    0x31003020d03020115060f140921010e07170d0c060b030d0305061305070f050d1104060203030a0506030313051c020315040309090b0f0d03090f09020c0601080a0305070212070305070b03 81
    0x103048001b50050242d440440c00308155210864108a811503078001540000d0300301d580031b24148808a140ca001420340803206020030000103240950054417850302013241c1c00302c2030681101001d00150040481c01010f550304605000394030b5000c1d407400201030101c15031940c0d01403145400394204640d050704514011a81030b81e039910044021b01d04241a00e5040b00d90303c4c0072510450035029001d10600082c0300c02000004001100c003026040440c05074000c1c1d000c3c0b001a0702c04010300070303a0040d038454241c210700201c00031841d05c00301120406d909401c80c400d041c07091202e00c5115001510486199501941c01016a81d5660703504030000c1001d10242c5003540050018000400c0822041c822469855001401007148000c1c1f2010401040004a4214104080d07000001110a401d2809034050111440051780300e0050032603682c64580142e00c0308030306612200c07100020035040012039070b05540580f608012a485641d28a02e421125403000b442071003441c0e0b0002d403000b0a00013960003441a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 20998315 1250 20997065 20997101
    0xb0f0d11062a030f0301121106040303030501170c03060a0903090801050c030702060c1206220f06050415050609120f0601080102030a0c03090309060f0e1201090c0812030c031003020d030201 83
    0x200503d6aa000c0c02c03041d070f001e4010400040c008078005403141c000c007522400182c400d403401c0e10301050558000b03034000c4010070740340c50041c0f1114400c81000038442080d034005007450442c2d100000d6171030350043c20845e03925540d41405410305d0f120740b485070040c00c0f5100c000c0c001c0e0300700401118100e40c000c548220050180c5004039410000710070468102c005000b1400c80c440d119041004000c0b0700d4015010320107003271501207038440c920318000d0000a0041010018000d45450180011f07aa1684011310031703100b1092050000342d0b1400140d031a01c030000c1d2203042000518002c0b0f2442c2210b480b009070705900c1083d00024420313005400462091000240a10007070b6401002a01a0703105100000c0c04201010800e01c699445644040320407601072030a801c5c05003008011800680306003c0c400040e03512004c500d818080c90409000046c1340000040280780d4511344885a140005810883c00a2000005c505032446646d22000907540080000c42d4090441c5006030082c5003403200307a08800c0d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 20999565 1250 20998315 20998387
    0x302040e0d0215131101050c0a0b090c011416020301091403030a06050414070f03060909050c0306070e0603070c0501061505031005011b14070807031a01090b0f0d1106 73
    0xf2032108898016110820b2000d0601c41e5581d500c2c0140001d507244504019041c00381c61030f2840100008003000b070103071500c0348042c00c185040707500b000c0301c3c8088603050084094881e00c03001d4602048459aa00d011101c80d0006010301c00a40940180240906000d141c08407074014084040011400381c4d810b01030070840c15544606200aaa03004401091883c2d0580300040d5040d0040041c10b1a05240d4500040c62030b480d034001d4022140d00c0c210035111540314811100407400c0130050250446054103180b0715032000b06002030f84902c8020400020004401c5a4000704032094004501a1402000501c130742e2a504000903c00d8000305d0f00504c0030710403148000341c10f50103180040d070260604554900842101c1e1a40080c903542001c1703808584c0f260000000b060f03003080c48000e01440c8100140140014800c080200d03118060b00400d12186c80c0103003503032050b500c50040c040320501c280c4103034103040200e0030300c0300c03044000624164020a00080c0310310b044401c040c120300302c0f01c26419000d01d524 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 21000815 1250 20999565 20999593
    0x6060201090c090b01030b0a06021e03030105030a030c0305040e07030e0d080c0f0c0307080409090212010b06070204050903130902130b12010b090303161a010b1303060f060302040e0d02 81
    0x3400501c02401126480341d0034010000c040d040000340c080181000710b4040b2225000c02c0284096910110058005402c000003038410f8034120480e140e202401182103505003000030ba1500c819000c01018000700007000001c040c0110113641c028000703101944036519028170064060080080c0d4100300d4001c1500849403a8000d441d01c500039500904034504040342a07001007410b0b40680c01d0180c952005028000000c4e91600080002d0403507240c000c12028010310501490441c01c0170110416418280441040d07141c060039158203d03011130300400c06803501c00c0340c2c1e829880b4010b410000c40e003d4000c0426000c0080c4c00911032014031f000d282c1c2a0719030b10540301c00d40d4010006521070200f51400104a08140d0700c000e088521070050640740340c00744452519000e41c2c0b40e010100c3c0c070004d2400260a050301c0c41401d1a00501010700864036040c00344104010201b0315000041c10302d9642c03448a20b08109580c03065020f03560244c001c200d80304450390b40719611070a088400c0010311420411040130 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 21002065 1250 21000815 21000821
    0xe01080102131806050409050c0a050603070203030406050a091a04050706050f1909050901030f0c0b09060306010807090f241e03020c10020f031006020613030c14010207050f0106060201 81
    0x2000380704140c9542c6030410310b42040d2140d003410030465050300c9602c0400c083e0703224400c41c00b00d0f034441c000805000002c2010300400f0350f001d51080d8480d0800b0300c10810001e4001c0112640640e02a40c002081d64421000c08020069014090114151350701c4036034030940c081c09034502590203441101d9640c0d81da802e08440078803500c1700b02d040c002c0003030040f00010610030103031010401ca02e0516884194803039000c110307070f075800764003e40d421385015032070300c1c01d0200700d20000014100003441d0a1420000c02d0100f1600e100c09006541000810000210b42600c0b41a04001a010816502600e140c1d101d6603d0b003090906141060f41ea02c0510104601900601c9904850190b24030b010b40e03550010306083e002500210140d4005001d0141020044402d52004040c1e440400010f0f80d20ba091140000e218518150010b00541d4040700500400004042810804503410301d401d4582161510f020141e00104c41c464412940c00809c81e2001c2050218070700412100c44002040200e0390786c00201d00b6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 21003315 1250 21002065 21002077
    0x7080c010b0306010f030b06060c16031109070507020d1505070201020a02060604050601080c1e040605070302100b06030a0b03010f0207030207050907020c01080f090a02100806030c0609090a090302250e01080102 92
    0xc00c03c411030007000059540e47c0d080b64080c0d070040c800340c10003624125184c1403102042182c801030124400610401100d42c50210503076200707a505a016280c09880904948035120010303100300c1c4020759007810403820380c20000c04500c07503007030500941c102000064080d421446c0e600015000320b100250f5607003010700c1028440c400503951030300c00e034440349201401507002180c101522070700c440081b089010b810300280002d004540d960f0307503070790b9084c24024102011240007803010781c10401c008101c0d0303440c0006d83c0e4002003903500000d0711074000d1000074010b0000954140030540007040000a058011441504858068070718220680d519242203032104040d200310307804906198041680f000d85c200e0a9640051007004641010302e854000403100381da400009400102600c04110090a0034403030005403020580b0f00d141043c14200c00505d40314801044d51401a64440c12503041c07507c01c004d101e464030124542c20129241984a140c40341c5400d0040c40341c21042c0d4400060520303014070840303075 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 21004565 1250 21003315 21003329
    0x10504020f01030c02070e0403051e120a0b03010e060a020d0b0307060212090d08073504120302071805040b0f0c07030f0203040b120105100203040609030609150207080c010b030601 79
    0x40c07640c071420015030082010484a0045108030400413170380503142481140158000d0701c80c0c64a83c0e0b4094415000d100c0f07039842440c820300d42441100081e400040c200342d0031100c2c10348085400010213011030700400e02d02420f01550700c18076080c003c0d1512140d000704200e2080003801e0114a1000b030500d641e0760074510448005a020803d141c0500403210050322180c0c2006181007200200c54641c0d80460708000c4003038a40c1a0041c280d04a0f0001c202581c0301201000c2c4a00c4c0010410540d02179080e010354840c0900088a913800f40040510030311558000d0311000844108101c01e0307410b040002c040896080303402d0708407200800d003ea41c50344065803040011404040c03030404166804c075012022102c0301c0c3d042d4070043c0804941c0001e4000904610350341d081c600030b2190b16200400403c44801c0404000359001000305000242d40502860103594105001044a600d145051005c560010304c4090402d44041030483c20840000002c0c4201c017210b2000b406007514120426131a20000c2c45100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 21005815 1250 21004565 21004579
    0x110a0503040305030606040302060c0303060406090c020706120b120d0210090b01120c05090702010b150405090106110703060c09060206060a050919090204020304120801080102040806190f0e01050a06050301050402 93
    0x740c0040e103e8801554052405441503050a07070703da020659a802c100800300c002e400110400c5441c6c10b0500c0707143e0091241c1e80091001e40d1034030101030348901d00c07400360740d0400228401c6910344080a8000940700074020b000c40340c0300050501a603495030b4007014403100601428011084042e9039004007060281c0011552442e6482e015004048054503081101c0f0340303008501c00220703a0b4480304044d01c81c0c90141c00101d000c0300001d0802c911321003541002c0340c11034814031061183c0c2e203601004505560b801e041030a03500c41501200d80c980b240303c3d03100902483c06c01d8500500e0329400340e0840220394883e002c848007511381070104840c4100500903541c100703041e88002908016030f040400902400040d00003046842500801d00780c0e070048030306440250881d001003101c02d1740b000707030f4500410100f002142024100803909403201009000641c40c00004030b0415043d001c5c80d400703004071002c0342c8810419082d5100040c2d0180c44111021441c02d440c0002c00202810180a03030341c800d99000b0551 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 21007065 1250 21005815 21005821
    0x9070806060f011b060c0302040911040308070206090d05071203030c020a05100b06070f06020c0609030309060604050408091306090b010302070201050403081b030307090302030606040911010f02030c1906110a0503 93
    0x440710040391240d4494810313070a80400e40854aa845003001c0d1440540e0050b03912814010810240c3d6460501060101c0c02008208007154512054410040c1d04032000f5a64000d008005200c088e82e10001a00c1402101e10010380400341074821140315200303480501a4144843c0141e0b21001000d1010b800340e0800d10340c0070b9036240c0b02c0c1d0058902c00001000141000d0360b6440b01d128001042100f141c029900198000328801c040041551065000d00110301d589400700d00c040d216000601110b00854545021400b0812808151840c10501401040c800c456035080d0f0800740c8568031804100328600345080f00c19511030300890368400c1c0c040e12410300d81391035075032003001d50ba1080362148645081043d103040320b90700c2840103500a20b41c81e6a480411801d500405081c00d10203051301e44079600e000c1d901000113062909191480e002420081d44280c10f2202c2a41144100c10f0f07044014052203070080d03004e0107102480b034406401810104101620404158680d2280c900914082070041c400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 21008315 1250 21007065 21007067
    0xf090309120102040803040609080c04090221011407020105061002190b0603010b03030c070905070305100905060f030313030b0f040b01120c083301060912020a080601080609070806060f01 82
    0x1000740c0c0c0c0100000500d095076a11006041d900140c10083c00500340050420240100b045600180c0038212010484161194001402c80c4c691181c045c41500300f400d80c0d109078000a51021200d800040141c40701403801c1103000740207107412601c00b4804c1025440d001043c910000b9400031030100e500c00c200410311541c07514040d203400100a00d5040d925022000d41585060019000110b25440107081c904d080c4804181540c00081541040520306010041403942060001c41181d002a80004042c2c03140c10100d148091001200e40d0588000070316442100c5090841e03e08580c003800364160aa124400083e00c0c918003503901501d1030b09440300501c5209007003c41d101c05e0328410403454040a5480e20494140000724081840040d9680b007011340e01400c10052481025400030350564135030406c080500803e00600820701e4560400820100b10b440c1d5804480250424001300d81656940d01c01590396184201c5400550380120040018074480014106010341c20003420000601c0781100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 21009565 1250 21008315 21008329
    0x3020d03020c0a0507030615150207050d081b03031b03060d030806180c031626130503040b04050102120c060622020a0c0309080703150203090102131202090f090309 72
    0x10b1803581d4011101c0e034100140041080c0c0b0021486480c02040c262001080c0c1452000681d0140030499075100c04016210f9010540c507059507011610042900b8503424007038014059a00715084003411101c600042010010165208403104000303517a41c084509450b080038002614000d411040c030100030000a4019001d10750b2202c009000c0412880c050200520b82c410241c43d03e05d4844800000d1010079010000d03428129210f13410302c04000f96210a088a50b0811602c4860f5001c0c480c2d404540442c003401c2500140c1500402100e0302c0300d48840d60381605034424400c0700d0141c410348e56140c3c108801c00d030030f88243c022030001801d0707503681c0c100501c11111764010140040d10581d206500d0110010710107012100419501d203212507010703142c0503020f000c1e2030f0400c04056210702002c00000b1100d001946c2a210010302c05600c940303904074040d000e0700540c410184100c444400100d0f81458200042c0c1485008a620344019110b410000c08840c0d4140d600305050b410410114042e803d040c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 21010815 1250 21009565 21009577
    0xa030c0e0a180308040501050606030103051b040b060703020c0405060a0e04030804020112020a080712060b04060c02060c0d08070e0a060c08070510050c0a020601090c21060305010609020301030212070303020d0302 93
    0x440d011030303102140050034400b446480c40c1140482d140e441800144402403281e1940a04262032941c07440d4110380b0707601ea0394034a0340fa9600d10651914070722041c548503908842c000260107811191540001e190181d200c241046405004603d800d00080b82468040e1100080700d000380620741c05504ca54a0444481e1401081a07050150082d0854412981840240001f50703007559406c0c09403c0c204801041010800c10305c2001da41024428005080a80101c5044800c1814092903202903032000c0340c520701508450303030300501595403a00c40b104d401501040c49462039603078040d07000d880a4100034005600c0d004c0c100002c0d8855941c0300024500c0e8004184141c054812150700031f148003003884c01d079403044810612090001c5000f182c4130b6010041c09002d003548050601c200c00c074902004150703600c6011412200440c185a9004200c0e40741c1c8004007440c0c01100a110f41038941d4000c201a40c0288001c0340106c089400c0c000d0104400f092000907243d2550181036204084141100070f90068 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 21012065 1250 21010815 21010831
    0x1207020703240b01030e0316020d021008010e01090e0a11040209030115060e01030603020319030c05010e0d0f050903150603011404050f011d06040f0c0b07030c0b060a030c0e 76
    0x400c40070001c9040d2001c0107403559100d0b092000c0d0300c01400c15000030f880d01a580281418244180d456000d50b0103c1925240203003032501c00340040581c0001100440c0c04400a0742181c000780800728290b9024021074140e548600b1642c90036642c41d03154000301c85440803d61080e420a2800b00000b800d40050100700b110000d20142c286440c03080024212211751031080c4110144c2d2104020880d009025800080400d08042118602c1c58010a8640a4a415022680b0404559001010b000320101120103070094002c000c14038248036401c2d0344215492541d00400c0010b441006078610030000c1f92101c04014010300b40501403203051201d00d100140909070716540700d8184081030143e01491074410390144000301248880e10464508494034444036010341c1041100241a50b50006010380d00568001503032030614902c0c0c1001c601e00191178210004800e4001007071000e260303004090049442c094072501c40b0607121181000700380c1c4101d100003010201f020b00c0c01c011140c0204600ca511180e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 21013315 1250 21012065 21012073
    0x30a090b1b010e010b100e0609100507050307050106030b010b03270c03030d0b0415030c0303120902040504031808010612080717040e0103060e01020405090a020309010b09010611060a050705120702 86
    0x81100c5050940d82c60061020244e03548102084044c0380204072008019100d0a040c0d10358003001010130380d5440360140303445c01102149065603205100300100c0d0425900602580d8a85000d487c040d80a060366110644001205100100303201503514103c034001c0000c00b41d6000703100c0322105505030005005c0c8130710032a80038a00c07458030651010720090400683c075001c0054008400f00804c41201d0804003820b24601c0e180c1c4c0203000164040301c80c0c105803901410486090340c2c1000810001c2c00704a000290854240001c3c40209030300a820300e800b402803c0100110140c40300070071802c071741c1c541c8100481361900d10103500202d9943c00040960901551411035030341a103800321440340d0b010360f0051030083c9840c17004000744010b51003440144403030040254646841d000010303d008002a0400192940c000080313013101e10258454040d42801402201c1c8940c1c0d1440043c007103445005104913280203800015114030b22a11503107116038030700e4443d0303801c10350b07840e2205c800860020180e0003035100e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 21014565 1250 21013315 21013357
    0x801050907091a0d0f06030c0b0d0f020403030c031b02031b06120f0403090b031603020d0e010c11010605010c12031d0601260105060a0311030304090203090c0102010c02030a090b 78
    0x1d036a15400f081c4401c1c4103161a91684000780c030004581c417504a06200519001c014400100140c04800842d06d0a000481c0c407450000701c01d10003801c140d200280c89901c0010700000301500103182c003481c68040d80f00c6030b0b2182003140e1800c41c0c0d0301d40541d00a506030002071261845424040d0380410024014241e2030038100c400140f150f00300000d40f054800e0718001410041003546c01038090018014655880e811400c0c1440307800c4298a001d42c1120a154010682c4110520294009052844098001c2c040586500740141c21041100920356003942000c01c080f07442d5000f00344100d05030b9401a4440070102c6844412030041880c03414860001c40b20b4442d00e5013030038040000ca4040c12202070080c403565600e8807120903500400c003081500c0c0e410542000095500c0c1c00e07817802100d800268081d00b4801c1500000d055101d02e4100f000420320120030311a015400280d103444240003078000b0005091114403d070b0781e900410307880c2c000048030b0700f1050121006003001741c003032008a09405040c4407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 21015815 1250 21014565 21014579
    0x302090a030f021f020309040b040b1305010311030d0c060c09050306250801050607031202091309020a0b09060307030903020106050d03030911060a020304030f051504050f0606040c080105090709 85
    0xc4540d4015166080c584200c0c2095180c421a40038084110803410286104007200c00380d241c1c0130b40d148091003140e0310a005089912980c010b021610700042c1001d0a50945220b0030008000a01041c0d9102c0c01390b4016079007900700000d00ca0720a50043d01c800850700a01da46401c0170741500b0700c1100403c441a4000941034404000440c05080c5d80b09002202800304140c500e11300c0380606c0b1003010480110010050b41c1c032400c2c05c0341d003515050703e01002c041c0380200c0312002030b00c03441c0103664128404d000092048981903005049903442241c120501a40e26144004140a038440e07495011008201003001c07103009500500351076220f4000495010755a00004500c0c0441000950100303482d50001c0d000c000d0503454120741590304442e4241092400c3c00000d5590280313000062a082d000380c144010300204100407406100703103101184a5103403a2400c030380c8801c41c0f0903d9140340d1040f007000c40c01610b003c0c06040d4007102141d0700d000041e8a8501040701851025068a05000845030003064503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 21017065 1250 21015815 21015829
    0x5060d0204030b04120f02070f17010905070b040602071205030417010b0303030103060902040c0f0e01050c070509010303020304060206240609010c05010c08070e030705030a170409020703120c030e1507030209 91
    0x640d0041044082ea00b0845c0c2c1c018000300e4580c149881150400301080c05426003211100b419100c0b4000c03502c084190070410a8014034038600003400300d00c60004002000c3c1d4103000240207490302c42c0d094644542d5540200c90b000d600c10580201160130520003031000c0109807034a602035034180c40010482c2c0a81c040402e055a00c203810940e121501c900e401d001f5400c01e070003444843c515502e031000d13400414250050441030b111a10904000002900c240d00319402c22201018000040c0310348400c0d656490040d43d242d10600c903020150140f40c5c0010351b503520004500d48462844c08810684000c9039040146940c0002e10b964188090b8403503000114909220f42c80c1000540d844240180c1001c5002411810380b80d000749210383c0c4040c40c1800940c4021880302e2501e07503c032031005241441b4000c40c0707405001759009220000d2020444400b41a03001c0d032511100001e96104010440714218203e040d65112106a0311070782c813031412036030048a943d00b0603600c641a86001420f101c1990700003603035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 21018315 1250 21017065 21017071
    0x1031b030225030c0314030601080a0c020708120306030f19060f1b080103061a0315041a0405030307080a0b0d02010f020106090906091106120a0504020105070c0314010f020405060405060d0204030b 86
    0x5529408130104164000c0101c9840404034280e081c11842c0c6000002c00d080e000408a00d40a520380d903440392818000c010388030181400c5015100d4a06075400e254045800844002d803103031188400181c0c40d440042629139001440903441959070181c0e40720300000d0000d03070207144103c0d941d9021103810307171a40c07080806c07000c0e04681e42c0302103651540c100001501d1111140e492411511081482646d40c001118400b42458125000d070603030313541c01c040c041c1c8a00c81c00c41c1c6444d51460707810041002001f0004511800d65034648941644074291107004482005c2840c542002e1446e01e154055802104840001346191001141081e2a0550f110580d01e4090301210341503200c1d2240030402604412807419410242ea20501301460181d5450403d000584900262503644c0086003d59200710201d4488542000858044943da4903090003003201e0201d1503882c03546070400079002281140211400c9410042140341800e040074100b100310b1380010650004641d0810000000076445001248 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 21019565 1250 21018315 21018317
    0x7050706020d0b041b0e19080604051014010302010806010815060d0b011d010c12030605060a08011e05010801090b0a0801090506011a040e040b130606080705010e01031b03022503 78
    0x220480c1a1042c04150b80c90017400c0301e07000e070541141c6541298458420442824100c0c4d08004601188054412201941e0480103041c000e541c1040103100e4000392084009001d0802041615000300c0940320384d280030300000f800103d5100100c3d00c250700c5583e0580d0841d80325418003540b07140e02c0001803c95800750513260781150301c5415810300d41d03070848040ca0030240442c915030341c50019180000d190500c1010300418490030758099440d018403a5002070090800600542c1d40c0741003644015014241c00d200302c1320516001200246c0101c40245684100c4006031524201a400c00c0b2200026000c10000c841e0440455034000401c10000d024008003107003c5c5014265030350400c14007208840c2417400c10a60303201c04120810088494080903503000c0d4100c1740d00714094079131300113401150f01c42e1400a0320b440c0c10034101040408020030108100c4500340c81e03146019400c2c00054043e900c5090341040e0209204c1c0c2d900301c10500a40040c6504100908104440c01184036441d140303400b800d40c01c0d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 21020815 1250 21019565 21019571
    0x7050c0f07030309080d08060f12100504030503040605130302060604200301090213080712020906010e0402210114010c02040b01020705060309030301050102010c0504080c0f0415030501020315010e150307050706020d 94
    0x1d1141c041c00407111440152807d100646040404030729020300407aa018010014003100c02110042409206828071005a050025052908000b46a130300151810b481641c070b0700c40130550b45824018481c0b04c40c1c1d49074019061564551003000000c19020340b407180c42003102030248800d254564001c602a1030448001071300c820302d013a0300000003545900140480c2e0310000080c02202010361105441ea98102c59155140c0d45410049401c2620000b001c1d40050000c10124503034100520501031000038010440040da81e40d041ca031909002d00684540803400401c400005418146c00c1454034070418011030f0361082d170311004500d05038000c55210405400100040c0155a070a00801c441b11819150403800d1030300b00b44015848050990b081442660594048c4c0743c252200c4d00108a4010300015600045d0369a0800074040e50003120108000034004201580301c2d8099101c44032403880280004070254101124009164000713000002800800d007e4440003c00500040443c8802c080c0c000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 21022065 1250 21020815 21020819
    0x417070302010e06010e06010504121b060c060c020c0a03020f0d020303070807030906080c04140f12030409060f030c0509040f0f060b180c0f0a030908070302150f04080307050c0f07030309 82
    0x50b400c004c41030b0821441c00700c50320b00f88601d0380c0c1d202c4281c1c2c0270350b46168400c003820151460b0582d202e9020703161113081000e114000054040d04100d85608481c002e000501080300310000403610760000d002402c1c1e1006042c101807000d4203000d884810288400380110401d400140c00085c40e60300020b0086684402c0010f2a004055100d00315100618140c1010030322404c00b07003411101c5000782c3c00f8920790603803044001c0c0015998681503050440018214005864540041070707240c0c0d00600480483c6401c00f2000108040032151b0700048079002180c486070941003204020322001701610689000720011200c0000c280401c10705075000d8030507100000c05072807040a0000310b1501d1013140c0340c4180300e44200103030500d060080311000848018059959842200260020081082c0207002c00e02c0200b05602059000100c81c0d030300540600c0c1c00d40c03543d40c0c1c00c01c602d0810802168000e01c0484184007164259024101920940c0d2020742520f500c6929016181d11302200341e0300540001d181c080c01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 21023315 1250 21022065 21022091
    0xa05011409070b04050102031602010c0b09030a0201060503030f0f070326040204061202100305090a050601030506060f2416060c170604020a081303020327010306050d02030a0b041707030201 83
    0x80b01c0c00504555000e02d0070549400c0020b5240d00903070008010800e4460103010031603104d48814100280c2c000c0300c282441c1031011045681ea0000b492900142d8a01040131030703107241c00400c2d101d041d0035042400c2d26000001464110301d42004800b103040c084080b10110500f0b0010303d607142d85040c5000e20b41d0306031609004000941d5100d0b44071054030f480224841000d615441070020b043c1949003404542e179120118664500144ca02c17018040c0c0c0224800401040030200b040c41c085c4030111044182c0506c0801003060004043c0c071551402400d242e810075405c880807002d440c04454180015040c8039480c0c617030f031080e1100340c070200300094940401c04003080d1201d02151703040302065070218144982400042c0c1110005001d210398510f8038a150400c140c42003003255074009071920000c900307801c1b20701c5c1c2417002010400858082410940c0200719400c1200900828640041c0100008549502da0503040440604140c42c800c2030f00080b0140901c07020300500c201c0c0e219a00018001c3e0013641 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 21024565 1250 21023315 21023323
    0x602030901030609061410050c0a0302070503060f09070e06031006060203071214070830010806091204060804030306030b0702030409050f010b070b090c040914010e010e071401020a05011409 83
    0x302150a85c03038240300380840c0440013210100000140d0f2801240303400ca12080c4c649000d24244042e0912900841d402095408640e1904449064085803004e0f114000d82401190044501124581c401c802c2000030030208101c494101c2d00c003505a40014541c810590140c40b81500504056030001807584200508011602c41c100410b282031420300201d5207c03040c0340d00c034000014122160101e202c044103a02c0d41688400040e48000401e141019070042c494150000d106810245c0650b80000308842c0e40881c1e0740e1200b0011191842c0303002d092400c207440000000d031003907080542c1c1e0b030740100000b040803090a003c0c0991b90015034440c0c0c6407400c618265040241007022050b0000010030101500d401611200f5074805030f00c1d4076a03543d030041d5901c4d222121481c6940941000ca18400340114601c0c201c6008480703900070720010300d400c207006081c0c80803811500841d40c4003002c100085250401e0410440c001441503498804450320340a00f5170700252000714641120906111600e00104 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 21025815 1250 21024565 21024569
    0x6030408030f06040911040b1305150a0801141803130f080c011103030105090403111c030506010c030e01050a03140a05011d01031502090f030a14100932030406020309010306 76
    0xe801740302d120403030740d641d4030341291a250030380c010350302d0342c0001040742d94500303402c120340340e0340d082c2040303240f4084d04041400a42200b4546c00348050040c0480c1c00d11040c001c0700c07484c3d041905445004d40b00d0b0083c4144103140c2c2d0035211502e000078081c1020740030030015824020801500e011000508001380f4600300b210755440d09051004056200814050200075a411500d007103031070180a82c0c0e94102070b5007440402800e03035690b0184045050001218075080c440d030f05c4155a081003940d42e000010369948030a0a40034021544040302424550b10480c01820361281b280307030104503814070720703420040b0380d0080d40c20040250700e4100500004000101c80d00c044008080c1c4407120b54559290300203008046800e850615400041149507900c3d500084400404041c04546d9580e440342050440000f520003408403070700130700c1030fa0281c2c655140a1014003a41110b00d0308503500b50080314102728098100c0342400300400e50b2048807500005d1000c1c4c401030010b0b40103117030307200c1221000408640e895 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 21027065 1250 21025815 21025819
    0x30d020309090c0a020f0a0803040b060103020306090a0b01120c0e100302030403090e040305040f0b0a1106060f040203060301090f080a08070311030a0b010207050a090603052103160e06030408030f06 87
    0x3841001c040d65a225036440d080011110542c0d92206040e400b24180b500c2003d120342c1a2082c2030342c9100300710400c4000c41c480ca0042650200d00e403180d90044059100c02d8400d59400b14811000c100b00401c83e502003020a8014141b00c4007190141ca4002c00760380c420703e510700200b001401c0c22201c40c00c0c4821940490099407501710301d5071409960150252000d4020060b0030405940013408041c019011140036000c1944291400c55854a001c002e66000030316103800030301c1c5900c880c90602c10010782140600d2004082d0b1840702c510a041c07000a420007804941c0c19900c07032812401140b010781140d1500740c041da8aa55890080c5180038000c0000a45a242014034101e06000107074003002c180ca403c005d1b192400b0402c1210440101d141034000d8200b41d0b1300c10805134000031000700c0c661118003101e20800c103440000310403000c800d89101e1482d0b906040c088d01080001c00c0d503c60b441841354200b240d03091100761000741c2c80114030b00ea0000c413005ca4107000700100384403d1448480c00e09a1000301 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 21028315 1250 21027065 21027067
    0x6090212011205030408010f020a020d020d0203090d1104051501020609030a0c0b04150c1d04060302030c060c0313060e0f1207030b0901020408030c01020712050307091e03020d05010b030d0203 84
    0x580600e4a180d08014855814500c50201d1828200031090007114010a00c6800900c1103c1c00c1800f8100250701c0f14101d14007510a4404c0700c00154000301e440c00e1130781465001b960400310344038280b1220402d1014201d0300061071503c0300c4099551441030500071280d08051800030068070002900e0050040e1150b8503d40c0180058002d40c0d034407071840140541e229030590310646880c40c20b210b40005000c40d400005007805400d40c3c11036400303007584080011134102e203540756580005100c21a016800040d402d900958020780050030004000c0100c3c100c2c00045a01d4203001000341c800005040e00550000381c21107240c0807461a0a607810303840d0900807070b035941d8030782440d03a407450f501c0907a407100604001c945400103010303d20a40c10340b070042c909001541d50300c103ca074084a00030750000100b00c0d00c44034102c29881c011403048041d01d104013500c1c9c40d504103180c100704100c2022003106502c483c01202c0c410700400143c5840b40d000e080d4a108900124081c4040810175040075200d21500c4110340c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 21029565 1250 21028315 21028327
    0x10030b011101020f031b030c03220f05150105010908030301150c0c060f090b09090a0509010b0d0f0b01140307090207060908071a01050609030309010c0501150b18100c060216020a0902040801060902 86
    0x2440c8c0e021203400c240410449580c01c0301240044003000b078004009041500e221401c50148035000c05d40704c5110404a01150207680c0310070056840104a00401e44213510510042c0031004140c0840003a26055050075500c420499a0380c80308507980d0740041c400560510581d009945d0080c403a0300c0a41180407119040004040c0801c0c000a001440702800c5511080403c0172950290710100a040010784120700f241c0850502c2c01100404603402c40b0300d0204000009040840c055224003622402805481e080e4030700310340c8101135044042c3c103070b0342c0b503990700020303400200c0380c0004012582c400c403213041d1900c1d15941c0c0503c0f0300d0b1051380428020601000b60810947c2c0110407140003d4090030134912140140c101580100404520003120b244400000b080e034a0300c0314050403098105c900d00c20342c61400201440401c0780c07040e0204020640c400401c1d00081c1240e0050300c070720424096540740351100f5800103000652903511000342640d0000303081c407a50b2000e009280103048550010f51504c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 21030815 1250 21029565 21029581
    0x50105040c090c1e03050717090d1409030c10020129031e0705150408060718060c020303031b090d110102150c030a2f090103140610030b011101020f031b03 68
    0x40b50f134010032420507595100141e0600d000348035464524003400c00400712450505c0143d590b4100c9035006502049079100d003000f4031640b070740884c0c1c41c0040140250000d1100b143c1417042c102e4000b00240c00355504c59041c0290701004990b00c0c0710444030f01b054403055070703d00307414142445079082d451040d0034080e0b030500082c0400007074074504403481a1840c000c0009040b051410300d018035080108980502d40a2110150344421440d17541203000310660030240d5204015a070300d40840e030300250190000c0c40003400b240d00d60b82d425240c00c070b1040c0d0031a16000703100c4009840c22100081c02c40c1c1d02c039800d8050300101d5030304116241c002840714282c9549810403260030040c9010090001000c5500d8043c620410550181480d091080c48111156050001da07045007051300f00240c40c1e07000034030b8818080121540d0080e0305001e480058070b14100c00c0364407007003140500107105207541800390b00f4141c1c0d00700385030910040c0080700c1994000c0352241058002c2d1589603500d0751a40d41880014000d010081f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 21032065 1250 21030815 21030857
    0x1031110020c120a0c03200d0f0809010507060e0601090c0f0e06220e011503020304030c060e01060b04080a050601060c0c060f020106030614040309080f0304050f030a050105040c090c 80
    0x42c110884030094182c4004044900d0301a10b080c0c0204903171052000041005001c5810004035011503a030303604503600603c140125a80c2d01c02000c0c2941055805110206021200524403501c0c107140051908a007902c80b403059800c0403423905c805a101c2001005a66801c3c4544441c1064030300d8482c440301d140440082880083d003982a11590000514000369000e03074140d801013003014694991070642e11a03401040000074483d401004400c0301d2119a034030701c68400c4030320565050300d07074065502468541c0340082030481c011800541d40d4240c045a002d000d0f40184c8010001480101905813051074250700308901a40600103200516007a403002074078060312102a11070510b810005100d49020403809001143c0c00541001d182519030342000c0159104140300328020340303400035195a03540040f42d0710030039041c103200c4a40040c4020f1100d4607259001c1201100018215002200a511130310308503a01a1411106d0764405032080040250305d006484010040c7e04048065083c803080c0c1c6426 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 21033315 1250 21032065 21032083
    0x20705010e06070c080a050c0301050c0301120203010603150207140106030f030c05031603090501021510140609120106060f020303040b04060c03021306080709050a05030307030f1202120103111002 86
    0x1448600904200c20b42c5900c010f0320340d030940240100101ea81d8800d68241c45211503841954240070b400c0d0550a6400c050084600a00360b20460360724680c80e00402c9002c0c2c005005c0126859506d414002022800006542d0180d100c1e0f01401640e490152519007510f10082a500c00542d062036400c0010854014800c0660303174050500f400c2000c46403401034254403076810301c08100c0600b0b0041105040c0e0144455040d100c080e005c49241c145603050b000075010084802c2e081a24454030284558480407007840b0303250f00044d0a171030405250308000340c070402c8841c8182480c0e80d51000100004c40c0c0c4042c501013030680238001b039072540c1440d4894000c40040180060f043c2d45d22485010031451181d41101c4a69004171450810180c461000801c00e0209480000005440000c0402e092418a18242c11550700030000c528040c00b030390b801c2d111991030030003290601800714079480d04032005000400d07064013a82d600f14a1503042d0319064140f101a91101d07402152080300304d031070792500010b450b14 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 21034565 1250 21033315 21033317
    0x3060a0203090f1519020315060d090602120609010e01060219021f030903020f070503030d0b04020f0c0d02070e0403020d081b0406080f0115080a02130909050a06050a020a02070501 79
    0x6076a41c1d031001d1062400750100380002d040e20440000000203030007008841d008078910800c0084100d58458104141d0005503115102e18008503074100891602900800284650003c0403070100302076284e074001c82e080340c02e5080c0000710304000c0060500c3c000116a01400d03480ca8031705030650410200030b5407248218a01203a0a0811030000d0075503840030940d00b07846114241c030454082c0da40034001c2c00743c1080c482c100c0251141d0140c60100320000328220080d5031001e8002d40c102034403ca100809031141c1c0624680003a400c11442d043c1b811840014031109080c0001021103406001000b40f030900542d01c4184242c450009220000b540890005000307801850181c005880f6a40748804004002c0400741d01040c000400140076074100d400148140c00008106c841680da50ba0003050040c4c00744400000244c0602c0086e482d10082c2e400341142d2a50381c5020944281c541483c00d0032a06200c6054804d9030181e20703800200030140c001d480d408500b2607001d504103001120013958681186c05428 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 21035815 1250 21034565 21034567
    0x1a040606020d230904050c13061b0204020319050106020703030206100509010e04020f100c0308060a08030406050f04050d061a0f0f010c050a1a0f01060903080a0f030207051209011b0203060a02 84
    0x240c4040f6074182510280f003c0140304106900348100d82c440158040000186002d010080001e1194015085004410000b800030f001c80c180321341c2003000943c40100300c5941c4900c40140010705560b01e204060203050303150010320140b800c40c1070180c40c01034005c240801c8080070742c00900c219212006103070b0448002d002a207940c1c0c5c0b02c61001541001811001c650045072000240c00100e900c865841d40c01030094603140c010b9182c2100b03020540c107441c051880c85034001c201c200407842c03042000384100d0140c01c000314141510703003000801241c201c039400c0c0c1e4aa07490304444a185038900d1034801103c1021500c02c2c200180d0200800c684460901c0300c1c9042c0050b07440c05000f0b100d02440340b40b9049900a548500055040440c550790a00644103e821440d842c0d0010a16900030509030b021f41c1e070061071660030100c002804854550000048504041c2c082c002200064410441844d03035541e9810032a488a140c43c0004180754109109002c1d02c0504034180405a100030512a801c40d11055000d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 21037065 1250 21035815 21035867
    0xc0a08100b071514040b1006050403050c06160b010603020a0801060804020a090c0507020411070c0605030906010509040f02130c030f060509010e0402010c080c06010302010201180201080f0405101a040606020d 91
    0x81030080020700c00c1e510442407030310700300420800c0100060744181b1f081070a2448141c2c40780d100311040e0085001c020119400019060b8003490100c0240895410f2107104d03200e0004240d440003407100d401c0e4000004241c0104440150503000700703589014004c81d1038091250318198000071090b5401d449420300031552589a0085d441c45902228a03444d0090000d00c07028404007041001a800000300344d0f442a80c420000c15400c0c40303041100d00403542c03040140b00e41d900301402c121950001810444665202d03904046c016101d80030007000c04071200400081d0300c00143d502800395828400c90905092030b1510604c240d40da03207a0018150303480e84110800301c0d80c4031310059030400100720b00030b880c25078007081030f096800000070698184e9200b80e00901001c80d090b00e174006054169440280426a010001202e5031507040c030b07e550080c06901156601100021030500b11071b03e00c94003000201002e02c1400d19801c2600403000241001d02c000d100740c9260b10001030072a0907400c049020580b280b099 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 21038315 1250 21037065 21037103
    0x702010e010903090f05030a020d060c170c0705071505041802040f0b0406021002031005010c021504090b0102070b040b19050d02040e0114040b130906060801050c0a08100b07 76
    0x12440d12880d1000800000546040140404c01c80340316501481c10803c00100b214100442c0101c0c609601610240e41c214070341e0380d050090106201108100000314404030107243d00350410034081c1c6902c10b01b1035039445590030141e00b480010340000c1003415021170080b040c81d03442005c5400300d541a410780c400b42a1850300c408064415584403414000c004000850b20114440050044514907002c07290200081c000260607030104951644030b00c3c000000c100207550281c9644684a0720050100a00160440514002d5045500300c40c1c00f10740e5030750000a10f545c0400c200405013861500d61030420f880c144243d411885504110700c110282402c0c3d03040c40f02d006105484607001d003840c0179074039503440d5041034100100900c140c40c0584003101c0c00100d2410302d17118800602d403001e0120402da59202c540d000250120f110101c0d0340c43e584510002c1c3c425000e118a50003507800000c10750740c81440c910014050710010f8007080c0140c1198001300003200d00c07482190445075003c54061082000510 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 21039565 1250 21038315 21038321
    0xc030b01120b040b10030e1b130504020102010b0a0306020a030e0a02101b050706020102030627010e270601030303050708090703031803050d020604120906020601090209040612080d05060d020d0b070201 88
    0xb00380c5400a17113021300380d0030180c0c158012603a0790502c0422541100300a03100707404461a40a841078007c00341042141584003560002a8003900600000c81c4403000c2d00302040074140c2550007030307035100da021070110551681400b40d0014052414001d0003c070700389800048004092803024002e103d200c5d80c0c05441004440c1028440e01d801c41c042e40d03403855540704041e020354412211144180081080c415402004400704c016440c482048020b803a0309255245d840001d001d0101180d40c02071814014000790301d680d441114800c10009045994994900a400d03108050814004d03c05002d04100742e5040000e04d120031690549051800311280b141404881103c5810107422030054403c00f21071217800199081c02139200e000289092410308008031481140b5000b444010780111004100c80440780e00509280f25009100280d0a642c0d0440d034113080b5410001180d08080209180001b04c1591242d1680001c06030740e40341780442281c4c00101401280c00d00200095214008585002d100354 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 21040815 1250 21039565 21039581
    0x2040e06240a05090906010c030503040b09030d1505040b01030603020d080a142d0f0901080907080303070909050a050103080702100306090507120501090608120708090303040e01090c030b01120b04 86
    0xe8101d03542c40d4181040100254031110503903000300320340d0b4041401075114036142c0120a0b015a14a41591200da40f41803645034013070560a981d11085c009509201e44500c580300300c6803000006500d0040c030340f50500c42541c01c0f4100a5050500d800307010400341c1c0350440508020b5510550003030750348c003500c0d900b5101000140107506c10104040f81040c1c0c0c61550400c600900f01001d0500c1000b102e040f480c42450f8402d1805204548609000b44420743d4058100c107604040c10b2001d07204030702e0f25a402075185400880780000000e1440d142004280310300c1c031905070007244149081c8003035030641d03e802130144982c48009000d0941101900c0c18648258008401341110100910003070070304000041403241841c5421003080e151900006402d5898030541080303a00d4032015200600081007240c42503080003030141c80c8c1c14000c01160400b40c4e03050004001416050340e0300707840380d41031026080440e844d100600c0145840c20141c114281e03000b103204035601d16071020102d0b1160741b680115000d440b00b4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 21042065 1250 21040815 21040879
    0x30f0f0c03040f0312020c0301330b0f0307120c020303040201050f090a0801060519030203060103110d06020409020a030606021605120106030209040501052505040e0c0909070c0201020d020102040e06 87
    0x214004410081010102c0090b805c43da42140d410710b004c00304250813241a0b004015140605060780851a004002e0701219000b0300c0021a0010b81d070b950030405250300c00c040740144504000200140d098002c90f60400c601c0034080100504a460000a55640310180003c0d044c0040828042611900d403070441d00142c9014200a141654400c03105010b000c45001c1c46100740107840c514a0300e580c080c040e80c822a60010018603181e46035448440002c80014071017900b160400c3c0c100800300f13903540000d00092582080c01070340c6000d1031800070115031b0b203a00a4411504950412842010b8440c0c166050310011038000c03140c080d00c0e808032401000d69510080d085074862003088140003065000c00e1040a1090703111030103000c0c11000d203100320381111440003c07803020301042c0511451f060700300d54880601c072340180ca0400c0600004000c6401102c071000000c8209800f9411940d0510030a00011080d0009606050030161039410030f10f00104120700881080ca546e8102400a10810200640c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 21043171 1106 21042065 21042089
    0x80105010b07080f03090a020306070e1005030106050901030c0e03010e0307060501050d20010201151401090e0c0706091506030305040f060c0f030e010c0203100e0f030f0f0c0304 78
    0x5c042d01c100440d106075248400141c0382045494081e4a180d00c4460028007403104112039010184d07400c0040010a1004101050b001804e0b100b9951007400c0101d17001405290071101048032198003a803560030b2407030f540702d03483c0003000906909000e2001031005a813114140150040030804c028420300c0f08400034554294141c0c45040320074014030000c501d604440011754002402e42e0420800841040500c01c46582c00944160040c605100f44005514000d0f084041a006000d00070745482e40fa01840c008020707006400d4901d5122640c81040100d44a05004000b900076001c1e140320014180e00c080345541c025541c0070700c000e501038510440840d15541c21506850080d0500c0e0502154151540050394144a23000091141c680c4c00603949203840001840c02050401e041440c1d0410030004031842e9101e411250840c1601c0e1455aa440d511800d091840c8120342c400c00704661 = true := by decide +kernel

theorem cover : BRFrame.Cov 20863315 21043171 := by
  have h0 := BRFrame.cov_init 20863315
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 20863315 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 20863315 ≤ n) (h2 : n < 21043171) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
