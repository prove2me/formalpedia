-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3915
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:02:53.198139+00:00
-- url     : https://prove2.me/submissions/627dc1c1-aa7e-4196-8ba6-13d4578d94d3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 703956834 ≤ n < 704136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 703958084 1250 703956834 703956853
    0x6030706080c0d0504140d090b0a0e04090f0b15040605130c03090203190209010e010b0d0e0f0706080f0702070e130c15020d090b1602040b04112a0a0b1305 68
    0x216001c1d13036000340c2c8140000912482c5e445051450b180100da0180200040c0c040108003d46040007221000c14951a00703e0741d0450032400324000d84403925004007030f00000c00c010010301088900160080410400711010300c1004410002616440d0040c1c90703100080424a5007100c24a5008091064090501040f0102c140c2c001909294000c1418290720655003500402c51802025190260501e07004100442d414090291000c0c010041c4245100d84d42c1c25008202d03810411100e98155003207421a0040c649914004010b44003ea820580f12910f04006c141e46074004602c04040d01d004c200d00e03c01c107548040d20030b0b0b03d1510412054860840b141000b0901114002c4800c410030007540041c9018424100010300c140d61641c8500c0100e0024407080752541041a2810102a01103034042051218400010001c001100445a20700800034070700f1700c1e41d15100880c03030b6803800c0c0145502815080c1325119440c0c982e41c0b4401032442e0110400202d01203003460400305198091400c4034403212 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 703959334 1250 703958084 703958107
    0x604180209120624040c08061c08041205070807080c150c030406110c031c03021b06040f03090803070b01031202210c0c06040b0304170c0111040e07030506030706080c 73
    0x35003580c0b03c0600e20003403800701c040c1422255510404e01340c15141001340506001c0020060348002d4900c6100d40b003d40801e0510341c0c4406000030f602e580000140b40c0d00c1c2d03990b40003030210030640901120310b070141010000d40814007084141c00c4076888805404d490b4019010000010020195210041d40c1448500489a4104003402c080d0880380c40710a504402c1c225014640b10001c035125200ea032144c241c01c0385020082c2d4500c500b4102d82d08026031102030301200c84050b01d4440f03100480c1849214200b000703100c0c0e04402c40d0303c914026128246203c0d10385040a86078440c0300300151810030f290004000140b881c0520080b01c103000d00c151207111220302c11030740312800c45828a0b05054400320310f04642400900c0b800d400842e04031403262400d46401c00c520260f000050016040700b24a083c020500320308c0c4011500c0d510340b202c008002c00c112102241d003807904140596411248284e0028450720f019210f01c900503600100205080361038140100c600807070092504041071414003103620400c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 703960584 1250 703959334 703959343
    0x705060106020307141b040e0a1b031406090a12090506120421020a1e02061207080a090203031603020304170105040618020901030f110a0b0d0b060418020912 69
    0x3031155601640d80e840c0c41d42402801541c04091000c1d098000700d001b10755102c090220840d12520503140440c201640031601ca084c4100a680606031207809000e09107140d01084418003a070303204980d00c0040ca000c403000199281ca003225030419680c0a0071040000c200415501c403140365480c600120159129408100980c1094844900d121002d9041c07104003d000003507030b101120b1951100c203102051540095036141e440340041c2017840301c0b600d040381130300c1c0a003c00c00f1030680103041150760340c904c1103408001030740480d4420001031014001c0342d040c030700c04e000d00e0380895001002582010000681055600261070b411029440104000210550442d070101d09801d440000090b41345401d06080d07080e03d81603d0748038101d80b40004a4401a900c403c20343d815a03800c4248030005010318500401c402181c8540c46500240d400340008260654000a03c0d02c000e0405c021301820740b0b4002404000d001d41d0140180310f01d00c07904407501080655000c1e10201100402c000304500b08005500d060 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 703961834 1250 703960584 703960589
    0x804172703120906090d06060e0906040c092c0f0f0c030c030706080c130308031003120c0c090b01180e0601200a02060307020115170f031c020f07050601 67
    0x16440c0008128146280c140200c03800c405280da0381614103031000340000e2461244401061040c0000c4042100f444460307070013070012703080d10b040d161044c0c107040e0000d503079441e0f045034221030107030b01640041007200c1280101420504210700150001c80701c003103903407400c42a240c0010454459060142c00c2c0203410040007043c2801000681a0f00345200141810080d403641d0660182c3c2c0506402c0204540c4024080e82c015131540f002600e8110954060150804076800503105400200600160310241d040031400c6070312440c40c1020f1710505041c01d44603500d01d0b80024240c0c201c1c01c00200000c0305560010200354105142c50102030220324400100303110190815806180c0200130080303196084010001025203025035201c0c1c040703014115569813456140000c0c040c0c0404000305400707500175008144a041206e1007010315584401c9208412055a030884890f48a2214140e69403900401100e50440c0c070b2081404031000109503040c065440400051a00b050800402012134400c0c01250301 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 703963084 1250 703961834 703961887
    0xa021c091101021212180708070306060f060206040506040b0a09021c05010b030703080706090213020c061012110d1e030206070905041b080403140703090801050c0a080417 75
    0x2007000580024600300e08034002022022080003c40c0c00070202d8a00745a108580d0300001d00341032114000d06040039820f6000740c405100d503000100401082d500003d0039034010154448440303544100c00c903559102510060216008500442c0c0407074420600158810341c5104085499111a80800c2c5403c0744510030004002c2000c41480410600f8041e800100d0421002040500e0858607100281e11812000034101035a400f10801151126400c0805613066244110746070000c0001c110f40f6100d044540244803540088013107502084808049105a0084c8100ca0040d0a04043c44641e2020070410703904400078054240d4080c60707078400c000c0c0482c403a5002d40001d06200201a10755200750300118411414072144201040c6060700c200c1c0100110300c1d05018986841c2400c0e1000a54088481c020100000356541850781003003402e0216010030008100d2a55450441909070003540e03c02d00006015201050201d4105e81368001d417a09801d8101c2c2c680b00c008582e80c0503007021040c2c0c404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 703964334 1250 703963084 703963103
    0x41509090204050f04170a090f06120609111b1e0d030c050708030708131506031e02060702130f0f09050f060702190f02060d02040e0c070b0a021c09 65
    0x10071410039018040d00501000008030050910381d440d0758890100c1d04044403d0000414000741316031007603803108003c092503c2da00781b005850300700c010003903040d000400c4100f6007081e500084845643c41195074005540c110682001700c1c5c544c80340602400e403a40c0707203594841c1c0407902e11003540700c070b41884584040c040103100d1a52503100c094143da80008504c4107001040c0140d0b8003041d0a039080740d520032031600e8400d00c00c1e1b9890050441d0402071300c8001d41005c2d40d00000603c40040c0d07603c044240e0b40507241684642c5200c00c07407061946140d00c1d000390460300520522005040c0310a800e19070300d06c081c001046203194100c2200c221160b081c3c024008580ba2213040051080502500c003240780341c5000b5000c589010301019603110382c0f21107a4400800e209800c8014440c030b2040125006034018034695448210382104800707504207010ba800b14100b03080110301c0d0102003104886c1c00c1c40d48840440318603981c8103000d40007500100742e800c0d8801c40e0b440b21003060000d188280121a4420031420 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 703965584 1250 703964334 703964351
    0x3010c08040b09071a093c09040203070b031b0f3106140d0906060f060f0804061d0604150c1d0d0804080601140118030f11041509 57
    0x8400c4924060054046500050014022030b091000c04008245d42e070109617a5030040e0303102003218001c09007a07082d1240d040b034541003c2400c9003c6c0c040310b51080000c2c00c0d0002c490a004001c08140b05607002075259100c201c0c100706440d2600095640800da01140c81107400c0c0803055a102503028569225440e0f800249902444204c1c40c842c8160b54043d00351030010340f8010040c1407465001d070141d030040c45110302c060700301103140c00d045070310140380400c044c046200c042c9041000780200d8041d00752114000b01c0c01240407482002440c940d4041d6039164503150325103407a410020940006003006d00200d8810b0741030070000c2040954041e43c0304408100402e070214018408460000307210004203d00721020b001c06664443c490402c1071021610403456900a1802d03a0161180e640554060300a00c07000203180c60400512402c0b061080e01d2b05001d410b82c54840c00303903e910300c6c0030044c5100d01c1201244041415203400c280060b0001c0c000244102504240a444218039030000d031400340c641011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 703966834 1250 703965584 703965593
    0x11704060e0f07300237031218030803090a020d05060a0515060912030903190c0e041205070219090c030e03033d0f052403070c03050903010c0804 64
    0x5880c0320f10030544507411010b11406810b0321310703030041302070b1142c03444c40e1044070b402c0180c10300c800180300c10001d481103e54038031408540340c032810f1000b81d4480b0705928400026900070500100c4400d1070308100c41440341140d841040c00c0d0000361910b0000c1c0f003010001d800585910207045076a5005034000c1006180c991055000e4440043c9002c50046402d02c14050640f190780960703601140031030380f035012100c0c140306c810314500662110070340c5440780b075407511000b400061401440d140200c83c5000d03c1078849685840d06401030300d0003480c3c0c09244a150004901c00d274040e20711a40b0041000080401502004d4880b8015404c024501692041c0c0c0c41e002d039405106440000d82200d000d1420f41c0b40008030036200140601e44510911000c94482003d441c0c5020039402c4412401c3d0300855082d03e8845090b8004594002c0d140500045010b84c4212038040c880624080c000f9a401480c60742c580c42c0072140b82d400007100f1014003409101086090742c00b80504c0340701c158661ba4080302483d040c01d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 703968084 1250 703966834 703966859
    0x1b0c080a1106040336051215150315040c0905071206060503010602010e280c08010515120f0a0813080f1c0507030219080c0d0c1b05011704060e0f07 65
    0x80800d00400511017280f07420810901d0402290001c0303039403540e5a40c0312440c0c83d060490b0104142d14502c4103004206040c40c059030301000d140d0041e01103c0000b8042c00300381012540540d00030f01000750a4a0401c00c0d48820341140343d000c801c9240c80740301c1d41c41500840d41502c0b11030f04a40040f600100051000d5076092040b80b120303032200b0006004a4189440301130481c8250306842040d11241240d820520105200389001811400002c2143d403620700c829032551140038880c64030078400e5612380003002000180c002611503010002d84016422a070300c43c003a96100c1008112075541104000400c00424840317400c0040c80c0740060a01018071001005d603c0f03070b00300c01c5002480001d00100d004207900082c1d5400b80380b00040d104040c007030349013040d1415004071120307188103114800c3c04032a616170040f2070b180da2605c034000505240101c46129807030110140900703030028500e000b0303400705e10010740f88058005000d06800604038009281a07420401042800c24099000361400c110b90100b901 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 703969334 1250 703968084 703968137
    0x9091b0303070209040b06190603020702130212131b060201141b0313060207120c0b01051c080906040305061608070e0105030604090c051c061b0c080a11060403 70
    0x340910302e052110380c000b40320482c0150000d0300000b4464000f81c010780301c03000c801c0f0b207884040403040c00e100e54500008001c3d61084074128011400109102c1401005009442c5402410220001c5541e01ca07600500b11410f000f0040c4c0c0d0f0840200c002ea140381110700307280c0001d804c0603800031940b61351505016070450000707030100074880b003015686061810103c05aa401c520814148500010981800f9020f409540d001a00b014100c07000c100551f0307003100c07120380304070301c01c005c040c2e80b0303a0ba41e6003006040d426241100d00c40c4012407100000144a803001808101030007131085007410340300d8032a68504801150701c44000c034400420f4000c1180c00448250b071015041c60250036410a4000003409070001902c018042c80e2a0304214040006240c480b002500003c0c06d000c0c6220740a00386a040665081c0080e1101031130084074205004050b40080d0003c000c03900c802246030b05541d00c4000580c0100180d20420408d041503000740402031180c203025500079038414150300c84124901c0040e113100d6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 703970584 1250 703969334 703969339
    0xb09010909210c0b10050405160318050709151502010c0215091906020c15160e06040e10120b0604050612070b0c01140a02070c0f03110f0402070209091b 67
    0x2e50068211075031083ca100541607000030b609145840720a4950708408040e044540d0242c2008108001116107102d12200c2c1c4016983c00e201003103040d52501c02c9043c0da440301070b0050b0420001801240d0554000c000c2c07589030104007100c2141d07540002c0b061000800d0300d07040187d441e007a8510b40503904002281c1003290040000340d650a04040c41985c8064030328074041e0068415407081c007842401da051782c814543d10000d4410051241d80b00e8400744e4811901c1100c0d00f0501c42a04d02c559110701e1030004040d2000c1c24451a03e400d01d11090a907036030003044041c180070703105804112a225890780300480f5201c1c1c41c0340720041c20311307500f08400d171100184158028403620111000c8038800260a208440210b114070780c3c5e4a010601d0540500460000d01110b008248180030140700349500601002d80182d04552016803a4404503100c05124807010300888119034000d07141c0d2030a03140410100e10018401840c050065021072a1ba4000715140d00c065081143c400c9921044840c20441400c002c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 703971834 1250 703970584 703970633
    0x70906080d050c0706120e0d031d0d0e0904021f0503041110020a060c03061703040306200409231e0c0c1009021908060117030a0c060f0b09010909 64
    0x510340003541c0d6940314400e031000c1000351b075146605041c0750360003480e450010006540304542c080388068040c0410302c00006007003605c07140201c900383c1c011801c00e20200082e6244c00c0a4210501005044040580180d0703124004903403810495400c1091a48045296119240c90b8a000c1c10301c0c61200342110005802a065088000006540814600c3d004d5a111200203240c0b82d031741904500401080e040404490102b07403070601d44140c00406801144d03c43d40d41071002c61580d49403d00440402407000003401e60a220611042a59410107240e800c1250720003051418038811501007020107460001e14003200b1a1441d081d4454404d01c01c1d030010501c42c80a00e08500404c09079a503000070042e03c494555206034010840d607524031040400700c40b1845511000351640017298682e54217104859001c150b21805410410011080d01c1d03214909455005c152201511400080c1021040d951403490b40c0d01e0140c4825501c21144502030841140001461085860a01154004942c006610404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 703973084 1250 703971834 703971847
    0xc06131a120a09060f0501080304050405160801030210111b19080c01030b0f030601060201020910090e0f1e0405010b2b110607060c0c02100807091e08070906080d05 72
    0x10115070452030030b000008030306056050890040c02c180010000c0c4c60300701400080d034004008054000d41d1000c032000c02003521b5502415440c00d00d4481000c010030003210040015251410500c4112840c1e8184480c82d58104010141000040b1817150340b0040518500f42c11800c2c400748254000c4000e0380b034528100d00300000280c0d60251400600e041680b00da801180a490380c0844c007550b000c000d4101c03841540c4502d00a03006c0e41148480600503030f4102d0f50420140d10804400040790b10303083c0b00d4200394540c0018900c2031040140600701441c1c4030580230304a14080d61200b4032030350180000003804041d60041200a42484451042907808140c1c1104224030b5002c0940304170307901c8520038032043c0c031500116040b4007403144050080c0c5d1a02c140b00c8100f58000ca107580b6024801c440d0045140c2c070840c020741d00c4450995416002642100080c40f44180c1045c40b841102c1c481d0644500d07040d984c40e1550310b0310809400014030107071900c8040040160400035031a50071802c0c2804c500300316 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 703974334 1250 703973084 703973107
    0x1051b1b03060f01090b0102071e17030a0801060f171008010e0f190302251401031e050603070f1d0105042003040c0b0f0c060c0c100e0c06131a 63
    0x190600905d0aa00d66401001041e80c0c0208020b100900c0c0c9001701e5100428048240000702405214004030301c00e450301600e84035030f804001ca61000d10719445404c00ca900300041242e080e44100e41000a11410440d070703030003451a0540c854401c074200107540e4085824121514290340d40e0b0254501c050340907007089914444042030041c0140d10420333080c1030f98603440c1422807074803030780b50f00c500310000b2a002074034001015001c000c030030f450111035040d43ca00c500d8401141180c070042126070040b140750405201c102800e800c4641c000000404941c0c0a90b2240d400c401c00c1c10440c0d0250800b4070054011410b02e88100000e1030040200700d03004c0054410040c1070300c110001042c5441d460300400400501048044201000540f2583d115141c0341d02015602c0a103903444001541f4a030b200780e0b400541004440c004a4946104c00c40103400186106501c0a000d80a0b1400a20113401a07031044d02407901d92a0250162840071101d500c0418500681c0c0180b0005001150300104000c020180010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 703975584 1250 703974334 703974361
    0x1a010f0903170d0c02060109110a081504090b2d0c04030305030907150e040506150d0b0109030f0302161d0118090614100f030203120901051b1b0306 65
    0x100e411550104040b60401030000e03051081a40c1c01148038a00250215440d6000542c181a0b941c01c04042080c00300d01e4452860074002c130b040510020f4040c10010b107880d10356031a82145060003a00209072401c0c15514403481e01000c455a41d003031030707196089034904181c82a28040214100900c002e02e0f05100741c00615a01c1180070180900038008013281c1c4120303003006010010710052103202020280c152000b40f80711842519640701d40d0030314020038005c0c0781802c1142c04c443d91142e84985049254500301028200c1501000e05102c800b140000108009030f0304440328511030350180120039507403520b0f5924841260040c9411280000074403545a80c0300902e00e056502808800d003016100390280005403880e034200808160400c0950580080c031141d401c0c1c01110640018011562209000d00d9406000d10010b07503d548a0000b08009001801c018202040c040c94041c3c0391203030307010380c00040025203981c2d55400d512682581c42c00070b1501a00d0340b000c81c0120301814184c20541c0280b4000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 703976834 1250 703975584 703975589
    0xd0f06080a1205041509030c1d04140102090307140301050f070c0b06040b120d090501030207050c15040f030c091116060e0c0d03081803040515090a0b030a1a010f09 72
    0x44242e075140e0800d10901510035100103104c1c042010f600c5030140c42005041c05071034882201c06c02620794021550f203544a000b040c100c000025a510070b0341d100d0f1078101e0b2400407100c6206865508010302039070350300e0a001110203404120b0400c010944844145401c642000b130502200481d04418840120781c08003041e0001c0d9001040345000351a84c00c0090020300e03021070b1565000f00803c52611005002160b0705003008038a0711010000c039540c41c015401d07441004401001a000b828040e120762030726090750070341d286402c4807480c03d054580c2d14802d80002c040c0c0090b112044641d808000c403d1007805500345404140140740e0030802c46050036030b150225a000140600d440e620080b0a0420030444c80c40010801080d21a41070342030300700900b401000355922000c0c13040c4614408007486000003200d04031007019026000c54404034a90403425000245000e81c0081c40c85c40014036503090f40c02030f501400a518000410620307a051800c3c0910495030147d060103144072a8010880c0c0160b02d0004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 703978084 1250 703976834 703976843
    0x30c1e120319090b242404091119021501050d1a1306051b1e0d0f0204061826010e0307051617030306040902010c0204110d0f06080a 58
    0x4880d1510000c1c4081e5042c0c00401d046094a04800801404040380e00310340188843ca00400002d1540e1580d150004503001c492500328041d2115200446d00d1000b80000f144007021105040c56101d9005400307448049072240382c001000b240380500d014142e1000603004007640000d142c00c9075188102c115041052003258410910f041500003440b00f4569280740516240d104d0060b6450510a601040c1c460f5010a84905150000050070401c800a0540400c00d01c0c008060501e00c04040f07001c60700c000b44180902107481809011002070017805200d17459620f0800160302c807401c02d0b100800c2d40c40790701070004501c4460042007001c2850480f240c036030441048000d45503684030003100b0740035140c203040d170340314038407000883c107090000c04030715540310903056156078408a5845a8484c66001902da4614994004002207441e40c40d09070300c0b43c0e41a41c418108103200742c629800007411a1030104500d443c0040029440c500e040c9248200403c2ca4204030003080000e04041a650fa103480304c000051 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 703979334 1250 703978084 703978087
    0x12020a020a060b03100507091e0503030708070c0e011d0a150b0310050d06060603050c03040507140f060a080604060501172205100204031e0201020606010c06060b0408030c1e12 77
    0x500c00d131010300003001440e210100912940c1004000100015940c0c814014921489035003501c09901d026004c804440c2c0041c01141892095119108541e03c031441c2102c041c0742d08600004c485081d030034894020140b40300f05100c14049140c0c0604c181b8001440c01030200d1401048081008c400d0381500103843d0720f5a08603440307584905060141c0f002036000164040c840880385d40070410305421400503900c07075139401e2016480e5850100820700060f58024015041a0030601148064000d402d00c1b030900185003d414035400c0020030b0044e401058100d0020750800c080100605040c05400d00420013841c0c85e07425060100500e02c3c00e01005420a040c00f5007041e050010b00001c5031244014680000940b014201e03c402c503040290700606c022200c04400490400d811694110078010840e0103801402c80c954840e0011a000b080c000406c50b4036031307a00c260200340c2c1000c510241c40075048070300c002c40e95241030800b424070b40758803425030040b001c286902085403d4004201c4041c6030140080d550b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 703980584 1250 703979334 703979351
    0x10909051e0c09060f040906050103050601120b04060506031302010f052a0a060e1b090c0a050a1e020a0b0a0515010c031b030f080907080601120f020d0b0712020a020a06 74
    0x140214440c3c80202e0354841c80214a101029180c003008104882113a101001829a104019400c1c2c030341c2102e1541c00f14042004440e07500c200760b0494034484d00c0c000c0000034420345030400038000d5041078814880b4195111595011560040e01891103100d00d410210b003004484072818050741145001140e010781280040c55180d40304000c1001e0f9281d00100902c40355500092491740d4030081c2c0f01507110104800f50108a600b480030505001c2c411008145240500703900060700c960340728042e034108009400040400d00c20740d10f030038904484825805041503a100b13083c2001c411801401501c0c009142c0320600c5540310140c640003034510000c0c00c0040030310350103040a40305403500c01942c42c034100c0078032540010950b0286a007140b4080035265511141c68031013596235501b8942c010110644d000070010700541d030054004201291080c0391240c1d603100580e000c1102e031a4441011582c07160f9100500c18841d800071080740104075601811400e010700500000e42e5002490406054907581c0d10700c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 703981834 1250 703980584 703980601
    0xc081501033206011d010f081b0310050a0b010e01080f13021801091409011b030510171b090906040209130501180201030b0a1d0a1e0506010909051e 65
    0x40b00324560208080d54503075a958162844504001e42506442c0c02080c000400c4c001540c6441c0016556404024071000c1440c20a82c401141d807105000c0c0c0c14801c07892400b018603214000c0510854100a021400621020024040400a52000e0306000b403580800450018003c0025400503801c0c0500c03002c4c800c0c50012072034400403040084540104000049014003064000c1081004503141c00f010342d5607608003850032200311720444140c40800b1607144002510039040150005054056881720b2552191108a28000600c00c400581c10007040010100c400080144803590140c80b004121724007051070715203c4a004100070303c82c8206002040455100312181420568824003c012405204c419668414640001240001d0a218230489141494050201290141500c04083c00741c4402c0d40b000003c0010140c100d802d6a8000c0304c8480c12a040f8014001c00ca640000682c0341880030005046050680001d003d103401c00c01800481104900c011010f145017045611442e00c5504c00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 703983084 1250 703981834 703981913
    0x130206040314030703020d050901120b12011d16120b040f06090b1603020408030d05040215120f1005090c13090c11010f0c05040b0a03090507030c08150103 68
    0x907110342c101e03051041d05901c0000042c4200d9000fa02154010506580c2c1152284a83c0f13070198000340f100840090840780039004401c0900004140100342c80311900f0f1036084968002d40302010b80058850001400000d01040941041d1012920304c0907041001036148801c03a580b004040d500d406001405204040b103213031202a602c444140322800b100c0c14611201300c01910403009002801e02d4000c0d00501038070888089070600ca020b5410329252142c04401060020070030703a004101b028207804404101c0e00146400c1d8070f00001c40c1d226042224040e03040740401090900c034081d51440620096894001a69005c0d04c2c25550342d56650000798118110714043d0300c10075100d030a080401c3c0001d50081d0204002c0d00c20000200228800c03a5502d03401c1d030724951204070103e14200020300c107912500004101781c00050401180003102659298500f02c0b56600c1901d55503c600070900075140240300d8600c000f800704101d03100c0c80d41142c95203820740c2c294114503045403908a0400b400100c4984 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 703984334 1250 703983084 703983089
    0x507051e042402011b0801140a0302040203010e180307020105070215090d0605070e01170105011b0503040608071707090b03060a0512011d0f06010e071e020106030b070507030813020604 81
    0x140341507030201101d4110402d0305850320340030055403c02c0b13101c1401c1506062041102262580e9111030b0382d10309810740034481c3c04442e8484d0070840010300800540c42d61300045000b000c0464444100349001542140956001c0000e01031a4004018840c007607a0300406032200d0f04e404440c50900c500e010016003c0c1da106035803c142d0000040d0b5180310600125a10551003005162500c1c0e00d007400e00c0d401100c0c441da50794142909201006c00600c40ca52050304c0c00c50703c05036001400319404125440b40c03807564006500c4803001a40f90b0341006150340d03210b031308000c20800d00c0e0600d000e20704000d40041c1404509000b07000c00ca01e8080700040d560764403880740d13800518020307001d000b0b5500400e001c58044c20808a000c2c000000f910030011610100140c22001d83d0a00005032003503909041d500c080600e000340c10581000600f02005240c002840480c813412000c039000040c54a146260912030b1000c010240c1041c03010a0100c0ca02181d00450120b0b13000740510751502e65a900c510008076a0b010f0394 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 703985584 1250 703984334 703984349
    0x60109120609060c050f04170c091f0603061415041229070f033c0507050f0a030f0603080304031107091802040905120c010f0e010507051e04 62
    0x400d000320500a0690150310014054482844034901900c2c043e6005c0c410440d49178003481c01000100565040354284490000c440429122000410800104e141130191203890348055000c00702240400080f1a00d8021314a9003004d010251030617080e182401251031010340100c050460620400c0c400b102100d014103000c00308143d015010f401c0007a24031140c1d444444044141130041e02d43d8042110b6101c0c49548030342d4404a400c1b1a15904401034003440c1000c8211008410101400403924006002461070784840840c00e40180310982e01500d502034010b90600804014248100d808002101e080084904021403160103000441c3c00615640c1e0018100000200c28042055440001034045006a9084401540e2a4045401154241c085000401c5880c80c05507005007029006901c101c0d004200f0f0711054001706000510b503070b00c0340000360807036503482e4200005184248100c00b1940c00b0704000704241e1519040141243c8268090210741d11005c8900e06503c010504c211800342c0b412 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 703986834 1250 703985584 703985609
    0x903080a0e070512030904150509040807060216060b100336061a12120715180305091e09010303031509020a0504060f031811210c040516080a05060109 66
    0x4140c5040d44a0300001b01c0c1e50311940c28010110442c800303008085054610040c5001090380340c541d41ca9480745d20410080390016000d00503084280006040c495115014403c007044031402e4a0810488142180d418000d2604c2d0191800308050404082490b4561051041e132082001444031034862864820042146003840000308521542c7c0b40c2608400340700f542c08840801e60991003d440e6502d41003a14103070841444210081400714840b44000d4a45000c000745c00e012104040511400e002c400f6404030740001451840784c2020940c520b0360070105454900740030044d4000529400041c4000703030425483e04c20050f8000141d0742c141000340100107045540b89200c080c060301e590007910510f0045412803139072160550080c010b1654900f00c80100d0318541070681e803500c140c0300d4001180c035003000c4504190006070000030113060018038460010446800c8840070003007a07500c01800c1310081022200b440748071980084e25550082400c000114141c0c1c0d07140d0040765109440d81c82041c4400c103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 703988084 1250 703986834 703986859
    0x106030c081608030a0e040b19050f060c070506090402090a0e070201050f060d0f0501110d02091e1c020103090210050c06060a14060310090905031308010903080a0e0705 74
    0x102203a0204503404001a140d107a210048440e5080400388900c503000e8104000982100f8424800000720207402803000440da80b05801040c603050b061800300200401c8028144800e00c0c0010145910f0f07002155101e1400c1c074031654070341c0c0711b0b0000d11426004c3c1002080a64107551075070140c62070000094005800640e5843c0030082c410001e660305009035203024041214003480d120503910814000e03184e5664104030b641c5a40d81041c01d01403c1e5115581d8003d00d007481110103000340890640c000016854180c6142044016442805101d280841e10352017401035880715401c5c281e039048855440c40d87d9001500040c1d02602030388200a500c40040c4d181600010342090240007042680303800c4446030341d50141400440b40fa680190115006c0c084103022035450040020745e4840d0300d00b00210b805a5481c401038003561044801154150000b08504200407c0651024000e200c400002d20014002d903c01404150000c0c0412108548071500d1f04080700c3c2c2005064000c04001c1c100607030150 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 703989334 1250 703988084 703988093
    0x9180b040c051803190f0615080102040501030f050f070c0f0803040807030e010806010e04022209020418150911090910080c0307031a07140d06031109040c0b1803010603 74
    0x82c8400c1043d0b00d282d101d141c6618070380c100040d800d01a1654069204031048543d00c070b00c01040340050b4100c900300d8407900700040300c41c2042840f0780100b0b068070015031102c2c104400135060314100a4076601003032034102088542903050f102d00b03070805098103001110141c5800e21480c0e15030100005840918000280010442044000d103003c601a60390744800360124001154032070425545540051410001c0c50100d00c1c0c160b00070700b8030041c80e400013402c00700402c4002810742c2c03e03640409204ca90115080248080c408040180000d01d210200280207203d60040000f655034050240465914059440d0180c210002c842d50408003c00407505480d1440c002964030603d80508415806091280341e05400e0020706070381526402800c50f5101903034406c01d804d90120042040c803c12480000c3d4410131440e40d001030210304800c0304080342c2e80c0c0c214204031140e0455481614000e81c8200100f1004c164407200c40010345a8050790990350300d8040e501c122185520380c0185505500c0c0040000820 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 703990584 1250 703989334 703989337
    0x7020313030f030e03241305010515090c0309030a120605180103020301060603020a0509040b0126040c170d0c030203091c0c1707060f02030426061609180b040c05 71
    0x192180d41d48403581103030581030640312021103500b840441d03146c1801501c25000c482107950f004600c102e400801c4a0b0540300c450949505079a104002c0344925a01300301e03404c080e80682e41c0400980b443e58030f1400c090010603983c0c80780100d16820000c1c509024050b0144503009000100703401006032446018003406a280c106082c4801c130701c00d40c03a040000580074020300a80d140181c0540b60f160902d02a60300740030144c984c51010504000501480440702021850b64a03c00c0c040510103042a1405144c0340401d140d0fa40c0202071100c1055080301c5a858000500800000081c03804040024681c5420381c41c40c040d501503070f94000c0e8049113481042c00c00908210100b8010fa0301d48540b00d070f071360401550031f00220702d04241030740010506009042c0581c1800010748110320459141581d160742407507036080c58190801c00302174100603104404500b00815500000d503100c045543c00d41d040d0000c3d190098611405100d510b525030400291001a80018000304003d4000d0000710031800300104203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 703991834 1250 703990584 703990613
    0x80c0c01020c041a0609120102030103080c070602060f04200303041503110f090607050a0501050708370c11150402091302030703060f0e1e0c09041a0702031303 70
    0x148640b40820800303182034016000d00c010f00724030009100c05010148051a880502100e401981c17440c4510000c00c424402103000f940103a03034154881c002c282d81d4905100041d440350045600c560709000d508507081a40a40141d4030072481c01440e601c904040c1801e80400204035414003000c580040c2c00c0200c020b100515078450b641c04c203d41d03510000c4102840c0505c0c215000095003d01c001c00050900e20014032000b4044d2044803802d4561355545030944408030313070890005010506000910510a408190b00d4110b50540f268041441103070040e4a000d440e030300c1c101152100c2c1a044504c1c000e17034000706134405070000d50307207215903007444028601400d503400ca00400e04400024002c4841640741502554020003400c040c0740b81d925a000070f416040024a0305641d41c2004200e40340003000b401c0d20051004000c1d0ba00e080313030450b20500b443c2d0380c0300020b80039070b4070a01088001101c03480480c0034035620100c100c0c0143c0381d14000300d15500602480c1c4284101400001c4180010301d44034070b46 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 703993084 1250 703991834 703991837
    0x91c0209070e040608011512150606050d0501080607080c0a0e0d05010c180b1c1d07030201110c0f0d080412050105160c121202090612040605090a0c0e060d080c0c01 72
    0x19040e030f5401d001b422034038244103000c2030151107181480780c50b107292401e0480c6030050150f10391a400210703405003103d07019400701c004207100042406494100f0300a81c0d00420748071014003214900f522000d4001c0d0402004680e400c20001004103640b80644001842800c000e4919601d0a05a107000390003040c03d501c140e000706041c1c0d17000401c0d0480c6a040c0780c7c19200a00d0405091420240075130043d140c0d10003140240170746840e4040c031802d0380000c4c07208040354048010944146140000b4141070b415091014031600403102c41021038541e80d1645007540300a41e11805a10a1030030044050b0045410094040c0c1102614000307109054003d42d0241b030403011100c0c0c040c58210070540e0034021a410050080f8158600c940d1610f001c3c0c20b14141d0101c0d014005032400344508005261350b4412a041d4501c4500030046c0818804240f2485a005e903100c4000d0416242c5519002c400915504c9010200b1030b20000041440d100c000c80c1e402011352210700951540c44075851036480300722142c03d0381e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 703994334 1250 703993084 703993091
    0x60a051801111804050423070b221e030b060f1002030301150804030c031101090204061d1026030c0d0c1506060806060a0302070c140a0e0c091c0209070e04 68
    0x5a0611342403080d1402903038045010604107045a00da25034000c500802c00144e4000c81000094401170540140881c0384512071000070035200a2415800c2003054100380b0010380c40500400d910907514041c8000d407608075440c11181c0d81c5d140002541e0400744c0b0441d0b03802400b06401c002055400001841c1610340d611921456000340d840e041790398120840f0080c000840428002d00480c1c058402d607400b020030a00042049202c540106080d0b5240b44d204c94448107403021038400303410030986032941141d81e01400808031454074443c5014242862000c562402c4c0c1c0101e40444450200201c17845941c00c102524918409248090b02c010110364055070032689103110341000c07002c05e20942084c0d80e03198039521001c1e1215818802c1a820450040003499401c02207980843c4242d110940149951035007105103068800c00c0c8040d02c0c00c95880030800d400d0003c140040120407030260b89030007209484842002003e0902c400c480304003504083d400c24010030074025182e0f400500101100c200b82da003070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 703995584 1250 703994334 703994377
    0x70c031b17031206040f180503040815150f18040c0315021c0b011106180d020d0e0f041e050a0c0e0d0f06020f030c0903160305060a05180111 62
    0x719103d01ca020001c0002c2d1508500050306450a6840b0030b02e1500341c0d12000410191101c0e404903082240803003501c4070703030001c101080860001c00c900540300c441004070014a08000c202ca100b4100443c070300500c10500104c1d0122141c9419000e5004085514003441c1242800c0c18024a608a41d0209503225000704468044000142c000c0b5006030402d01c00301561210609000300090408088841c1086083e030750100080908101d000d00480c000340c0d6400842e02d00c890350700c1c82c003806030043e2410b40d007210301a031440c2508805041c100c89810f0703801310501c4500400003001401500403425034485142e001c1404074115038803452040c021aa010070800c030510170309944e40f4042201070340d07002003000340e000000351000004403c4070f0301c220b10250900c1075a01c0014a1500101d80503051402c022600d03200520b01044003040701184000b082c041c82d401c50726190b444220080200040c9a22070f00800c2c082c1402031003101a841601c4001c101070005108803110303540c440c403104114030405140c02e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 703996834 1250 703995584 703995629
    0xa02180109030b04060e070b0a1205090a05070314120d0203040312051506070f14060412053109062c070e0907090306060315052505070c031b 62
    0x107140a4a8100802c11442d0342d440c0c4d01d40c405007020b0b40d058002c9000b010800116011000d010301385100c5d0070b84403540d03080c401a1402341103c84c0108130544a42c020584500403031008100b0105594201c6203403c0f0300452266014500803141d101e40e50b00000000304141c41c0e0307417113501940c040c0d486030761040312043c00b03115044141c0300b040d600b102034101c030014091040e240c80401480c45900c40ca100b00c0742918140c81f1481d008c115208000c106400c110100020404007054002c103d116600b0154200381d5100034550740b03d54602c004588440d500c0c01c240c0500350456142500401c2d048605024142c2c5800c43c1c3e0071080000410b0381c000154960b403020502000d000624800c06c0d032a6500e0744000e00c80010029010806810b890500140160210100d0000c1c01120051801030048800c48128445070000311400100340482c0411001c00f00700c1090003c2d42c45040c05a49441c20540311441401d0044100301c09610041210900d50b58200368144111030b0300c0102c450032010407004d000c08003003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 703998084 1250 703996834 703996847
    0xa0314040f061b14220305010b0a1d0a0e100f0b0109050a030b06041d060c19080417220e040210050a02060415020d0c030b03060601110c04050901140a021801 69
    0x42c040042004d204c00c010b440c40014003d400700006105e424500e6001e070b6460115480c200c0d400503600b503511555404000e052005a00000b01035040740b14030000014074104000000140c2081c10864035941081c15464007044001071621004a0412840030500c0c0040010100c0c6860740d404504040000640d61030b003e80c80c0c10803a50070075555945542c0c3c2c00e00304802061408030110101c030440c4c5e1484c451070820030401c0d11521542003600d40d80c8489441080321010226045410890110304010005000962540304422100141c1d51034082010341121206503d403c42040e07101e901400281d01d052804c615400b56000b620316824146480404a6241c810020160056440100401c0004a400170b482200c0501c5d950018184864039007900b0642d00407403404000291207040c203419502e024002503400101c02d0030722482c240e890700d52640c0c8809503a02aa44199034580001d50304020a402c09041119020301500040c031b40208007200079004502c201c220281e0498100300c42c1c0d4010328 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 703999334 1250 703998084 703998131
    0x1170f150a0b07060f0923070e04150c0318111908030f070309050d2301020a02101112100303020d050f0403080903070b040b0c010b0618060a0314040f06 67
    0x2c0d080c0d031501d281500c500c40a40100c1e8040c0748540c0c3d94001c45070102e02120301021540c0980384d0541d9609122000d0343c1d01d007031655005555030210309001d00001a88000654045c40d2000402180d05081000e00303600900c100144000005a50341c110700420100c10034810058508031092982c89004c50303c55410448079019022040e8400c0029241119659001d0140e0a1092a01c1c186a94990000c509207624144040f200ca40200c00f4001400e081301000c03210032030202c0021410300c10484802942c54207101c100803009036a4004102c125008441140c0c0c42007242801c40e8200d00f00810302881800d900d21081d401030040c800c514810b030f0b00c103008848007110266821820310f42552034200455014010365a8103115200740010081c090201400c02401800d004940383d903c00c08409003501c0300504018403070343c0c041043d8921481045007102d840c4906030790b0b0549a050140080d401407181d401070050700300c2c2d00c0c001c20040086030b0000d0303c2031512481051200ca50700580ca030001040e061b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 704000584 1250 703999334 703999349
    0x90c0f132c10050f060d0f1203020d0c1110020a0c061d120406080621010501091d01061d060d050118060c0f0e09091501120308010b0a05030c070201170f150a 69
    0xb0404159145000406c070103415020b420100f1a50100340d41c0c414840e82c1516a030702c040380d0045046410324810344203d00000310b45003004000c410700007090341e84400061100f050b12590114450311900e100e10414000300340e21110802c010190803150300f21107120106004040d102d40b8502c1007400681c5420769080b1742c0a0707158526140c4070981044021503044258a070070941c3c180608800340800d020302c60003400300318000240900400b0815000000c0e0940d00d03100e40c0e04240042101c6001030070341c034413403c1c143e120344411519402c00113a058003044202070001e600380101402c0c07d00000d50b100c070006200e0f440400c126092800d0a446c1501020b42900110310f00e812440c0b0282840c0c0070307450340207402d00d0540da0b070046518038000c00c4010a80000b401000d00804004c10550403041240c0034207161880c942c24406040c030010a81e00c8005c02d1968802d001140110071a40102a0107860080c011310042c0c1d0781c5003e0b4002c541d4903000f200c1e425500d0312940ba0f00003071400d040d8061000e98542 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 704001834 1250 704000584 704000611
    0x8040528050103090201170f0f180c1017010303030209011b02010815030c0a032301050115030b0310050703020702030c010f0e0108150d0b0f090c0f132c1005 69
    0x41c030340194000c2104100c1039041c04446103080e20000454100385108083c5c0c1c0b4110300260078000c60b0352040c500010400f400b00543c040d50700080711310018082c0e030004021202c81d0300310030446104076800102c18032481980b240c144000f204050f055009044514000e0342e904d119018009140014500a080c1c040d01003858180842c58040c4404000550020042d0840340300e03542200204140d40140e40c000d503a10038441a60140031080102c6890000590074003d01655040480c55074008081085d01030038156140f1260b00551000e20a042d40c8186a590410140c030b800403010b4041e40c08031400324440d01607503107a880e503980150507014412400e035036003061a284480040d200004040c11100d174802c1c800442d40e030b56a48841507924001d202d00320280650400d0301d0f1100181d80c000d848080c03a5040350a82c4034031615220b81d05ca24201d01103409441918000188600802501150009450318019400125260207030040b5403940e9406c110783c54190010449021110240c503a600d84815 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 704003084 1250 704001834 704001839
    0x20405010e09180f0a1b051c030c2112050106080106030902030c03101e0b060f0a0e09091f021216050f0d060504050c030609041506050d08040528 64
    0xc00b8001e95034071280c0148903400050f00e9919031860901c0d01e20050040e0f40c0b0215600c410840c40141c1c03070304110b48860700003510900f00380005490003002001d900d214802d04201c4000d03d40310b81e900d0600c6581002541003402e410160346140c820380c011081010654410f644d02c0d40340c04901c20300381200c0e010350368254280d00b0000118003070403680d901641e041c46008100e0415a8051001c1c1680c0124160001030b40882c01c01c00c0485c10030030305142c1c051645841140c42160300c90104403420503803195070480c0d4840d0038403815680c9007560f408198008948401300b00f4607000009400141074a0044a0001259a00d00280503441091a101c69170070410740421654581607800d903030403030040e0501c5824001c02c00078103181074001030311880009840781010406070030648516900400032000d02490f500c1c0002c00704008403800b403c01022488450045600310105900200c0074143c007e1440700818003034105440360b43c01500540e441002411100360118070014000c051022681726600060351 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 704004334 1250 704003084 704003089
    0x1519081b03150f0a11030a050718081b30160b0418090516051806060909060121090b1005010c1502071406040309170309120c03010e060108060a020405010e 68
    0x9050140b82c181c41c0e1400d15500c04100001c1c0d8070880c41464001240e20702018020400402140500540c02b9124000c0c042210701041c44130300c80001030340703560102000d6008102403041601054000ca90b1410007100c6091120154844851400c801c4400a03070700c09816101242c1e0500c04c14050358001c1000700060460012000c00030004a000020502c02984a20b401c004510700c14541d4241ea00a090003a0724201441c85078500318900174007100c0c605400483c550b4443e0788406889a46401c0c00110268401c0b204010700c14141c24a40102c0540c035025503024007014501105c0d400c0100000504040c025080c4804645050356032040614a0740c407100d030030313080711548118aa41c080008401242d079120b6515410040c09004144074906410014240506500203160790603800b02c0d140c0c0520720002c08d68416110031074504d5804480220345d0361400c29402003850300755007808411030002101140c041d040340e088034151100c696030f05145000303d20850264a0102d000240c1008050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 704005584 1250 704004334 704004361
    0x90402030114010b0703021204120602131703090315090a0b0c22060315180e031e09010906080f010e070c0f0c05011709061519081b0315 60
    0x2400600005044011040621a20a4243c104400b04030340050440200342e410050350a025240340078650500342407800501d0958045180a850340e078000c1140340e480c0160460361402000350000b14864044296104c1c2d40b40e07002020b20070310a009814184d00f401d1010803d00b8445c807880303000b80c04900201e60303915800d103a010303003d00c2c8140c030f0a004402804120302c80000030101c1014002c604203103080001415502c1d80d014100aa03c0d8846c030401c40105001d502c1542d500c019031010074401420711400c2e107140104032805510320080c140019402400000500300d5060a98818505586580d01600d82d40015031728106c07115018401000214544c0424030b410180c149400345000301c190f1291402c260b0a0b0b1825505030160203000c110a40e00300c0485130700c4c040000f43c40b82c644d141c002c2405d0b0312a000100749210b0f180d2114049481a91188012982c8031040000382480d86d413103c0034213542e400442410082014030406000c55841d0018580c0051800e00500001c00d649425054120 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 704006834 1250 704005584 704005591
    0xe0a021809030c070806010906060e150a021024300c05060a030509011d190c0b030c090a0509090604020d020604090c0e040501140a0603020a05070f050f0c030f0c09 72
    0x450006003e400b000f20424000400140f1020000301800d50503ca0601c085a5265115106000c0f00b0b00b414030f03030340d105c1801c8181e0000c002c40718103481d40025002607040502018204040300c0c50181c10b405c80d6901161079009681507264110007003134079000c0d40140c9141d440341c0c115904815400c0c594003499030f6442c1007034013441811004400b43d0b83e200454036540107a184180440d40312010840030743c200744114044504101680741104d1482d102a90310340300000e129142c131004480701202880000f400c010010060320384074030313503d280c020450b4026400243c0954030862039000b0000381450048400e6003e1005c25000d031000313841f02c0d802c0005d41080014100e800940510000540780c1c8244182004500a92500b90040d440347c0308001c01c603041600302056419600e92841580d484907100902501d0941c00c00680d1041c25100030b448034019000c00800d030001c0c80c5000c0c0104400071074001d4500d04180200c0d0100d68070181015101c1c816400f01e0b042a40c010300c6072080e51303c0e103240301c540c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 704008084 1250 704006834 704006851
    0x1103010204030c061d01090b0405061b06090a030f0216271104090b0a08060c0a030603020a03080405031006051e15030a20030103080d090201030f05090c040e0a0218 72
    0x1619642c0d40c0c0d4040196061303031158000c203801249415068552407803182074803c1c04d18003142041d04000c1c181045004a0103102c6c000c0001054160b006400e40801d541001d00410840b482444c02605450390f404481c101140090003464940d0815400060034201102444004e82c80032401c2c41c9038900d5119101108a44d0b4005040311100da500c5140300700540e15615420b00d9030b0b65801c00701e054059071400c1c46910700600b040354081110410200c1c4031601700d15a012401c0c3e54040462084000d40001d81001c0c2d401b801000000040000031402841154019010f03600031154545003101283c11501c2826084498079044c8191540a00300c2c510850400800c2e4410700000003c1c1c60000d5082110800301580e502c3d10703000704e20201411701108022960103424655815540c4401c0c65010301d1941000c00343d112050201160701079080004ea913201800d04204a20f0035001c001c5e540c900168120f4081c600d80103100306400c2000c201e2885007a00604140c1d040c0e62482000d0000c0e1000070f01400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 704009334 1250 704008084 704008087
    0x1403010207150501051509100302090a18021c05040c140103020f0301030c05040b0d030f03110f03040b0f24060d1b05070221060411030304170601090b010f0c11030102 73
    0x82d029a5001c0c419000080b4001055818802401030300b4a40441e90400c10350b0520801e14590b843d900328400d007511074940540c6840d0701c0b0f00800c80011030f0350400c1d0700380d0003402c142c0041c0c80410ba010f00107098080f0345003402203024a8001003114001c1c2e03406004011410700070311000e24805d99281d00c0703600600d00145001c5100c031420305160030a030401c071040d08004404024030310300740c02020312112049601c105205110b54010301211a11058102459203c611500443c42c002c03041d10f05406013590780694a241529041c0e103000000c8a08129400010011a0f41c00180b402c008517001c802c102d42d00b05001c2c100301040303070540002500450342601e6250f002c2c041c00320900320084910107521042c0e119030580c81049000c1d070b0511400380b2a452502d1516070008000603501e508a50025039010141001001017821441603800542d01c01e904a846640e814600145150403501c840c2c200700103c00c94032004591407541c207158a40015080f08595020400f20300f128080050300a0006 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 704010584 1250 704009334 704009347
    0x3030e190f060309060b01020303060a0905041106070302031b0309220e0109082508070204090303151203090f1401350106080a060506030c0706390e060414030102 71
    0x81d03080c01620341154001070f8442161108001c2d2500420020f600240041d5003145001b40110b054241944109484103860780d01040500280071560003101c0d82c040c0040d691803545040103035490b40400004001000c0c41070802d18094004000d0700d031818002401c251000d141c2070b46040c0307024030500700e01c13240e035586110803410b101d400d124218082d4420151207841c1e0480c40c0110741d010800140e440d00c0ca541c00e0088200054440741101c01d12607040320000382004141c14100d00038070a59001c1c010081c40740c400800c0750801c00c42802195171196940700034482c1c8610300404e8100312880b401b031480305a81c503510a258010b900b0000c3c100c0400baa50003242d80260074200c543c681c5103603c2c0702143c6c15240140621648404a25071011800d02d051099624090120b6002d20004220805248000c90b9a00800031184c00210090000c100d40701400c0e400c00e4104d140442440c05e00e40e0302c0c113109440640d803460045814121325031700285602d0400c7c0c600f1a4000381c200039030400315455507007000f58 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 704011834 1250 704010584 704010599
    0x60f030141040c080f0307020a030b0c0904050a050a0b0612040b0c070609060c0e040c140d0b03010e0303010806070903031409060408010507020d0f05091e12031803060105040603030e19 81
    0x40c5108070b008041000c001e42c0340c40e03082400c005076101c140385e242c1c00800c209030250f1512110f40c800c80e98030840d007541950320602441e245004103620180d202d800c000c2030090119481d000240030b00d49084c1e0800c1624111420000103215000703000c140b217200c090009000c20500c15140d5800204811200d10b014265642e00040720142031048035070f15a20050702c03006c81d03031018020603032030425181009111054400070b4034155056190000307017180003802041204140d00f04c22540c1c900a0b0091040d00c9007900c10680f02d4209010f41c2c1007511032030000030200c80c442c00d058409c0301d4164840d07170114032101c40441003d500000c019900808104000103500ea003d10603c0e110750070550140012640e00440101100303020716100e0104803007404015503984e10107040e04070154140b0441d01e50084003d0201e807034a010302d00000c645000c04500c0c1901044101503860b5044e1044007682c000e41c2e00d5000b0002107503030b68040900000d090740c40785c0f4114185040c50b00d28074008807041100c001e6032140c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 704013084 1250 704011834 704011961
    0x302030f0a0506010f08060f0606130e16080c030403080714041d01170c01031d03041805100312080a0902151b0d0c0236060f0301 57
    0x155688181e1010409105100c41404481d014000c02c2e8110440c440c42c120000e41e80b0310000e00790319128804000480c0103695902c048400841040c0f03054041e0503a1091600c040c18811121622088504c001403041d007807103052002e12034110056003504644580c0c5040703a514100901c440d0521045c003102e46c880c440c6040241000344034120030303060210300c81d545083c81e4000c10303405101002c001d941500c414190210355030031801020300c1d00140901d90b08c1682c4108407003441e20300140d070000041c0400d680111a442002d1000044018000d17629420030400d00c0755074900c0301508058107107580c20101c61080210a4008404010108420581d500050110740328414080801b00001443c03003e06410125024a802d0440c400f0f000300001c00f8001801301d001c4458028454440814500800b03443c0c019503107a0121113842d0715110a41c4180d011502a00c06d40e181d91048020f5010359915190500174010002c0605000c1540540a0448010707c241004140401c10088c4810408074400d41c15 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 704014334 1250 704013084 704013103
    0x2280b030c25020a2904060806151809040f0c0810110304120f0c15020a030b12120d0b04050f100503160e0a0e030c01090c0602031201050d0507030203 66
    0x1c41c066941c0d4644164103040070204581400b0814145a41c0b80941c1e90750342d010040300e0a6818004100380110355030f44400c2c0c43c135450200300324408240802c4859203c102e940c49000300380c80c0c130814414060020f641d1030045680d0240c002e282d41408a805081c002e0866030002d111703801118102115586803450300c1000e40007840306500400908440d84220b0041a1004079035030074451440c04c064544110b408110350180050140c0c080c0d42c0d03c50f551003988609103150300280540030000341d03c22004041d42c41070030070b00e00103410907030000102d24110044928541d1490b00a19800f0128044409141c003e21000300d41160358a580c1642c0c0c0d212401503903c80c641003501d4400e6407a01c1103041c650600140c008502962002c1401e200c80c66246c40400c00340d07142c481540c141c03942c41c004004041d05000031188882e0001060f205071a4a05420038031020388101030141c066500c6003012a564003841c2840220585200010052418900c1450050a0045090340d15958580d0046860109440c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 704015584 1250 704014334 704014351
    0x602090a0b0703120c050f0d020c0307140606010f09080309130609090f020a090b0306041e0c060507020a06031e1d010204062d0e040c1815020105010b0702280b03 71
    0x313900c0d094100c075511800c00381a08500b002400d008460900d00100c1c05113416410f9030390750006050072180001c100792049540d000b111648103c8815040341d48be400240c80107808181c401d00d07a110407e014032100c1c07060720803c030000d600b80703480b0908010b08404103e0000600310b030f9907500410707008003c0c0110b07106140994003540b40442140305200a0348096030080314000d152142e0b08540f40c0d00031030f240d500315400c000c1ea084840d00900304400c040502034030091041c980d00800040d000d40046c05800028022500c103080d860f5100404c2d030549101e08102d48a50306100b48520110310654043c40003114200702c09184c07800c00131010b0b422680282c00c004c000c104100c00d4440140412012039000205502290005601c109030146c15a04680005841240c0301d10000241621420008041d00e003039494800b80240d4071140c000b21084c030078113044015401e04002207500a003001c1260240c46c4c2c00f410426950b08040c000800a8100c20124403414084420005038498000069402003101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 704016834 1250 704015584 704015597
    0x15071d04230c04030c0303120b060a0908060603010615120e030412140c01020c090903070b04060e2a06031902040612060e1317090603150f0a120602090a0b0703 70
    0xc120291501d03590080205822038001c1006000041c103105003070044030380c1410a01130404039403000101424500c94010b410034008500c0c0445594000300002c1100c80003000e403101034a03841d080c5030a84e0b15031302407040d030440079030401b4241a2090b4075601c5038035180030300019082086218241140e100d94010981805a8800041801807842c07501003200c2d2100c0040503621007100000c1d48600507280308500c100b09080010300c94100600c225a561540001d2560351403070a031606100900000e80c000086110f4110701c40c140385283c0000d4040701c0745000055078042c2c400c004000d0580c0c801480440c0c001c1c109010400b6900103400580042c0c0000e44411401c800109962000c48089a04c030288801e404400d20040c02008403005045680100d4a410154401200300800b480350401150b0041d000208101e10120007140c4500d020000310b1f0b2010451480b0020891480c54078014050038046801e82c07280010041da0003454052001b405600d2045c1e60303524a810240c000c05c0003600441e50 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 704018084 1250 704016834 704016881
    0x60601080106020604200d0206160303110702030c090709030212030a021c050a0c03031503080c07050f01140702030a08040902130915030206070501020d2c15071d04 72
    0x200306058502421242c0700615581c40c094031803103445284ca00506403070700307042c0c108052261a4030044110b559000781a141c2e4814660070f0300030144000035016030000e0b2900402c104010034070300c120391103aa001401403c21181c218101320041c40e0280a41c0180040c00782c0c00001030701c0741482c03c040000707528055900d408a24001a0030b180c500d00c9000a400300385074040940d182c009059860541603840e002405031107a00d000d800501c1e40382c200c0b900031003d00d4800000c00040800902031070200e00c0507503444640d0b031030500140c3c0f45c3c080d585d0350125082410301000084188041d148440c001004c580c07849816071199862341c1d201e500041446500000e03030580380001d145003000209611042000b201001400050300180c09000091040200061000c05d001003501540c09481340e260301000580c460680398a0340503058185014151001d08040d03644240200c0c0a401d200441c04150040b07648140088070b000d070200103120303034148446058400741d4070f89103e0b000010207900c1c1280880b61 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 704019334 1250 704018084 704018087
    0x2011202070b1006021c080712061806050310060b0a0c29090105060306010806061e1201060810021e480a02060414010207230906041a13021b060601 65
    0x1400b401041b400d5003041504a40355580c00035020741d201d1441d140c08000074075440c3c42c64001c0e04960f40310700c2d105124403420400744403103948044100c410441c04c84241c650a12501010342c1c0692042c000605801d210b000c0e22180245203540409101d0350411415400004050800c0d8480440f1400c0e82c5081c58204000d600342407141c290400401c8004040561514854036903a50006050900803c034410350754a408101d0303c1f040c59050300c014840400c8440c54242c0700d0007010b940c4280403882c41b4251021402800e5171084401400b210303d40b03254542c1c41a040b40106074085400c000304240c0c03805807880700b010305401907802c8485520f09c441c40c111f003c46016654041154007560560801c01d81480140da8000407107045902c52008078040001c102d0060b41070100c00d03400030444440800c1146280980d15400e042c03403403400c80d048981502e6880910049540c041e102c00c1c002402078141d2801881e02c40381902c45007050b0b45001d0b24110300241084895a80e80342500201d40c07108080c040191b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 704020584 1250 704019334 704019343
    0xc0806030f0705040b01020102070b0f090d17040f1505071110060b12040f020307090615030903020a0312060f090506030631020a17031201060e0a0302011202070b100602 74
    0x804100c0041ca00001c10030881510795110744601840345541e50381035940c0341d0007034056661040e008480e60402e8907019000305400c90041f564920140241100c02c401c0d00c0c0034004055009411810150380c80d560340d5128064a103c1003025030b40c821100c20210b54604203402141d1027080c2035690700a2440360301d1001c600d410202044504100d0606c0d00030b00010301001c090309c5c90600c0020a079000b90302c0b0f6052031440e150400c00082d4160244000200301c1d2001ca030400021640c084054407511100c88200314100ca180000003401a0803240082001c03074440c1c2d0101c50a840c410341c00040b45a130355005111740410300d51154440d540c8038410080185020b20610b50701aa01d1130120694400c811305c524003480100c407440090580c40300c42d25040d500d0300d00304640500241c50f0000c414100000300e0a50300e03080150f441515222170f400210341d5034405c41c6007a00d20007010704007601c00e03420740d8015103945030256179620305c4c15030038000e9801141d108e240f0f00e40031301c098a9501c5001d9040241c000d090 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 704021834 1250 704020584 704020591
    0x1e071215080c0402031f0b0c070602010b100c140f010c120209010903150204081207050f122d0a0512070507020f01080a0b090f2205061611100c08 64
    0x444100c204100203201001c180b5942ca4003045a0060341c90752001640521902003200d4800d0305003003c6000b180d005480401040849a444100c683d130303aa440720128240c1d160f8034806600074107521070741580603006000580303034180309a050001a0020744401da1810300e031301460000d079030746480c22a1a10f41d00b0848019508180c1da900794030b030620340c1c0c001815103101d42c840180014454220003003850070540c161400340c60810166608000e03112071111a94104950948041c0100c3d0740d070001d10b5000142802100c440c40c051942000c0f120a0301c8600701241503401d42d140b10442001b1110b401017a001009500b06a0700d0b01511181284901d040e0090002d0001d010301001704940801340c0d4510318030300d410b58001d180404090307942010300c00c080d240000c0119005035500e4240300305407042151451142c051411240d6041140c501d40004800c0c1e100c2c000781041e0844c0b40419154080d1080303039200001d49003042c0d5440e90b00e0b03010346441d00340c041c0070503440c466440d10040f03c1c05a102c25420381 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 704023084 1250 704021834 704021861
    0x90903040501030c1805060f0d0614090a182a0b030106030c020601030f0b040f1e0303050901020a0c1115030412020105010902040305061f08030c0601150305070f081e0712 75
    0x5400d5209410645c2a00c164002e00c1c1c8500300200b050300c4440b400c0400c4511140da042805c0c0b00e200c0c1c2d104000c2010a01e800c4045126606540001d4408641486001e08412180a00b0362541c1d20b2034607920084801c00c00c60bc08035850ba8114001851006802d01340104141e08000341d580d0f24101005007120100009a003c540040d001000880ca4040310150000e030030034200c54250b180e42c50305608402c90b141c0001c2c142540d2411418101110340c0c00d03002e075035000740c6040c402680c8002e00c0d0740c202d128a00b40c41012818011404022441020f440e00c6690006098582c0a54000403041444d400c02c96046543d43c0e04100710a01c4994203005c0d02c0e0040031070746025814241190b03240c58481c00f00038405100c9120544003c031403010004590340c0104251820750740d40348440b07181691500024000c201e070a8525400e11800c40d4400d1141501c41c20f116914030034843d00302103003281e111744054401801559507054503d4010481400c00340a0441c40d01c8001d6024580c82e40803080e1050b000d140340 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 704024334 1250 704023084 704023097
    0xa061503050a080c0304150c110a060903110d0f0c090c05070f06021602132c0303160c08030a0614121c030e0703111e0609040c0e090903040501030c 65
    0x440000c0c82c203240b903070311040c0140c41c1d9400420041c07450145030311190410a086549022a540051030804000c1c080c914130142880c051052000c80c1d0b000344540c00c0000c1c4c40c01810004150092203208178107800034254461042d0648038640d240e104020190b4407075008800400000c12540b00d106060340075800d00a05112258648140201d02d0910113404107030009071080d03040f0900d1000c0d0159603802811144c090306007102d074100070440d207031801182c44a44180c400c0e0640c100c058686e0054800310056203507994040040440c441d0101781b02052003103010811002030420f00285100701a05000040c04c286032002050610402c1c0c0125401480060018581800c0200d2003a01d03030301d41c81c0c0c903004004248200c210020320640c0d2460a0038010071802004110b10034180044100d8226120794000c000754480b0000c44050620859000000b0801e1410501701034020103906141d90904d04c5501c604d01003c5030b5524011a514845500001018441e80d030b018842c50480409614180c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 704025584 1250 704024334 704024339
    0x140408030f160e010c03030b0a0b03090714060708090d06050406050f0c032403070e0a0b0126160509130902120106050102120c070b0c030c01060e090d0305090106170a0615 75
    0x50f0207140042881c038108030441e6418010326000e5001410030190140842900d545d94402001030b68005031105a0580502c00000508441d084501da484a100501140c9060306c9a6102e400075403044010740e4000f281e62400202080d100c0c4a00d601c41c500407000070519260170301c501c2c00c0483c0002c040d42e882c650107009000071841c4801c81d07010400b211002d0003404030305400001c0d280c0006503000d1500c120f4442c4c100081058a9003251000c15020703203074010030410500d07115080b0240b00302c8003c10b03205244005075400c00e8040e00c0c840d1803e42030034801c1c5000f25510104070300b55003c0005045850702c40090404504285482c170500b210300f030008000540c10440001d490f0081c561140010000c08942d2049080d4240310301c0009110f20310300c0680d02c6404a440a0301c94000751012030a652030a000001d42540141c1200c0c032941481d0040e04100c0400081507004040c003a00c84803081d0746e100e0001c944000c807a51540000c1068400405105429241510aa400005100c042c811040c0c804 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 704026834 1250 704025584 704025587
    0xf0a0c080106090c120f0b060a03021b0f0d050a050f210a020910200d02070f0518270f03041403013602040510030201110f0606010e04140408030f16 65
    0x980c0380f400031000001c1b81403070701c10301c5182c054885254810350041e80010184011a01a801403925098401e000103030701003550140c544940b10380001e0150b5812401402101a116600400402c00c80d420b141c3d080c840031952038403c90300f007080608049403040358042c0229051a260a9100d079928606600d001c3d216404074003244c02000c01941071140c04403204044c1940740c0029811020100d007124422005040d0003541c415003840f030301d10140300e2107001180c0b038108024581d00070301c00d84640501c40d4450100c460114141c01104100c2c0112011000202031424011030740341c03028020041d03407511b00348000560012400c0f103d4a20030781c58000d1a07031101441a01d0b140d62200f034440c0c1005601200c0780030402e10a81140000d6200d842e0904100c0300c001245011401e59000380d0381e4000c8000f217464030994603410312940520300d80c00380c0b00040c00c66204811040c24500d0250001c540001c806035a03050041056500710740036100031081007054185065590f5009200032494051100f01010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 704028084 1250 704026834 704026847
    0x1707051c1e020705131401060201092d05010f050a0c02070f0519030816030e030a05070e060a1e060e01022802040608060a090209070c030801090203090f0a0c080106090c 74
    0x8040c41d10007554006605600a1004900420015100300e10300c01c0c000d82c500c4011305042070200c0c9508500000803400620521030041e08a50242c002203410300c0c10307002030319018981c10b0a0440c11f0301c14038645001400a005d40c140080040101041e40e00340150100c060710040240c010440d4048101000034142c003c1b15002192020fa0700300c010030005102d4480c0e03100c4990400b134030404000980900741c19480412080f2300303000b903560301e0100480f4020140c60b00b448544c050019030000405000600c2c03a6003010f504500000e00c02c015950383e845140040c00744503080c0800b01129510f0400402c1c5d00045080c0b01224240b000d0801d105c0e441882c4011000f01e00c030101d55258503030250600319165507004001524000044520a01d81040343c3d1002d0040c008003207000318044000706490900903551a100c030380c0e0603111507910741e0801c85042c000b90001004480c1030304c2402034241082c2307000d002000100b8080c0b50012107040c01d1030b004070f013074601a80c42000d10500e802c0c0c41e118000da0100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 704029334 1250 704028084 704028107
    0x103060c140711010f0e0d1403160501091b0308120a0f09051e0303060d03110a0f080c01110310030204090c0f06052503021c020a1707051c 61
    0x2180091441031980046801c440c4440e419a611000000c2c210284181041c090b019024241c4e0f038030309082801c500888a44115900c06900111500c544600040c3c0c684052100c0074810400c490030b1866a821611161413000d00540e4103942d1010004180090f1018080b001640706000700c052514683c0c0ea4402445080804169a15800d010035601c581e41e42003003558040b0300b18103000318840d40c14590f8540c1c240c152400d03404008424200140440442907a1040c1c50003450241d0402c03460b2000c1e83c1c449200000325515000e41c482001c0011501e141d903441d0503010b140e40f07507111039404c609030b030840701c2d140e980b407074110800d000700105498040c842401b502d605840c0466030181c00d180554440403a17806c0405403501c04407010030960f9220016004400d94508080900e914901440b020480c40701d0780640141c005107401d110703041d1001e08102700c1108502c12501800100d0315500071001280084400030b20b0000703035000c2448010040c000c41c10342c505c903001400d60030780705001d0013010189 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 704030584 1250 704029334 704029343
    0x1051b2e0b100c02120a0b010605090907180909151407080f040f0212010e120d060b070b0c070f0f030e010f1e0815130b0103110a141c14090f0a0b0103 66
    0x44094170542000d00807151000e6020f60300340e5641d40c54070000b50080e0440c1c1095402140c00f00c000030111845800c0458164401005605a0909100c1e240780900212041036591000302c0310405e000003102e2250029001e0003280c6e00b107043c24020002420320102070301ea200001c1d0740000303220200309070403580b84882d0ba0442d05c580074444017943c268050400d9461410450041554070300071b050440700103011801d4904420058aa21190386854030f0145041c003034005603424001031860701001004046550184582200ea440d4540d40c3c08a25040c0c10000c50000e0030241840c1d00d030f07580040e02d140044900341010700c60315006900d12020490030a003504200500f480114a075a404062203800c220400790480e075080510112080141203081c4209002a141c01c0c1c101c41340010000036074035180c05507076903201018031411049480340c0210039010100a48003002c0e00c07002100c2e01c0303412040042c45007044a145005500e8a0a009100c3d85d00c01c040d402461a28000816000f40d00d410760307610 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 704031834 1250 704030584 704030599
    0x180c0a03050a0f090b0f0702070b190c082d0702060a0c080d1104080d03051909060609050f090706030e0307030c0609052a0f01051b2e0b100c02 63
    0x2070102c5040074106100e03c0400043c5000409014008032080307251107020034000e00209600c5490b412651103480b481000071154040c00610440120a03003461a42402c40c40d1807081d80300192140b512540c03143e4880c418840380d01402002e8821228034000051040c803900c1e42c2030034020b0300410365500c500c066820030003e50f583c07000100106501a9000e0528055040044003004003181c421a07200b80102c100301d1091010310200b00d0322a00070103100d0030b0860514100307031016290710030180051940441e2819101c44010420000500c106842402e500074100e00c2e41c00c0041c0c28504000d410b8001100f007500700301140d04c00714000011101000d50519001e01c101702d01c0e0800340018001c3c40c81c014480e010b1810301c2149100710003400e0141ea13000f24003112200c1c1085080005000c080040345001c540c0074001600c0507810342c00c00501e256201c90665016080201602c00100c2078144040800b4800c281c446030094404d21554a203c0c40540d2403000200c450030000e003601d4000b2000078031503400c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 704033084 1250 704031834 704031841
    0x603010603180803071101050903070c0e0a0e01050c0301140405100b071106030114090f01031121070611150c030c1e07120809160b03131b05180c0a0305 67
    0x3040d054031202241c100ca031071a01c0b800d140728014460200224100071b0f648c00d001c0070400703a201c08011916180e5111104044682c0360044080c1031001c02440710142540d00c09041460010038010680314202c10900560f0300d41c10030f1080d1507125400684140218504002c002d12060089082810380317101000003070303c5070340e240740001a209203a003404d50004400b1000003445002d060141d181000304440710601c039a109001810140717002d1002410603500e00c0c2103801c9500b4502040d42c00c406203980c1e01a10300e5240841035203444010740c003460005c1d035450148030a00070140900c110145401d62041c1a038102400d011100b03020141810500f004001010240c003c0d501290859880f2000d0000e0344401c41406c0c1494010240c2c3c200c500456110390001c1c1c160342c40130848030707030030035680540f0046079041c60a040210b8100501190303000c5040985040030451103503036054a04483e295410405051109114504c4d0001d904c2d0b51401600030180010390140c8000d03a00c2c0000d103071034005803569 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 704034334 1250 704033084 704033111
    0x110601060813080c0703020405060315041709040c08090609030c0c040209040e0a03080130030c020f130203150604030201050f0d15080c042909270615010203090603010603 75
    0x40c0c481e00000c04010b000159a9091507005c01c6807800c881c000c490800043d6514810300d074940020418680c500f058200010700091301c840d861940040c1c0c0d0034601803d1103003400100741120413400450010500040c00c0004040e400c22200f6400142500075504000c20381001c29a120404038440b4407441d000718811030310b6240ea9204004582510b403c6a25580b51810060401c0400380240300b0310300c994011880500f010140081c2559103040c00b10b1500c0b4202e41c4003184d846481441c120f03440b1505882d5842207949000c20140f80700002400103950b410100315060b500c80c00d0700080340c09008240400c00250380c0100686507800c2e0603180d41a522945060020000c02440030f402c412510012000708007079800168404444200341c2d81040b00d00000d248600000241c0c449a000c2100c08026541c200d041030019180c001381c1001c2003040c005048007414610b1440c040e800714403503104004014040464100004031080203002440c42d203803d400100783e462005004550605031903840201081 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 704035584 1250 704034334 704034361
    0xa110d050303071206062a0c030210020f0f061608040c05031c1d060922020c03030906010b070507271103010906140307062003281106010608 62
    0x140e00c00e0540307549152075180905220782015042c41d0040c5084008520341c1d0040049100103400600d1609844100003d410201c6d401003d0484407411102400030041c0c0300c80c0e01e0f4410445e0744d500580503045e4401c80142c40c00200303100910340e503485102030100c5141c9240c80034019420915020045030703191b0a10081988182d480b03581c26118100004c1c08a040c1900074800c55205a40c075050700030300d800200404600b41140080d4044420400840300d072400020344640681d5410a51a03444080c0601000302d800000300307581150030000030880740034014482903015001d480303606403d081c0c03180c540d2540c0f030305a1301400104c803d8200c5454110100100e140102c0075160030700740300703082d60440f408a40350428410801100d052040126402500c0765945008a2028000345000d9140c02d00c101c9007000c841c08580308884d00710348032030495441400182118008a4142407105c41c1e500c030340460000042240c08200081c100042d4000180422400c2c11540350b0301c0c0003036451b01c0f03506e000981ca = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 704036834 1250 704035584 704035609
    0x100f1506110f0f0309120609060105010318080f040e07020708060c160525170a1119031103060c0c0c10020c03101407030b031c0309060203042f030a11 66
    0x3840b0710b0f09140c4100d030001004165003402130b501030002003591040196140019030360740010743c02070310040c07001d54032981c00703006401032002070740c81d041c440c0392101c401c0c40c0d202d2000c2c0f00d1078103000902440010004c0a004d40c020105200400d0301c03c2c58a04201c4d02d982000e4402d4203000000034080d1030309031030788011040d07164005041d101c1040f0307105240001d6410614810280c030985500006440844140c0349488094000140000c1071040d50b420040d101c1000e00c0d9607100c2c00720801c0c0380d10001e6400c40c040145100348134074040c00e800b00041500d0600003c2404400e40c0d001c018600301c0d00000320303041ca9540f0013a62015640c4001a1060342090813800541d501072040c90380100003603000d41c001d242040d02040003114541c603074840440c180d0350444411780c0c1550080711860350301101405100c142003410305c0c0001d0b420059540c2c03101039034002e58040d42c045041c25069070302540c021440c01c00e4560060140d10221800d03201198030307100004d801400c1c05181380018a900d880c1d12800e0043d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 704038084 1250 704036834 704036863
    0x609161e05070c1406032d0106050d0f0b011b060204080613150213090504050705041b090b0a0522080111031f0321050f03090a05100207030926010e100f150611 70
    0x48640c0c6503000141250081d0301000030076803d00c004611030b6070f3380780310300c0030301a80680d11141c00201c000d900044440f207010088030b0042e4200000141da210500c000e500449080c0074449200b581414117a11602107601c1807130819204210808a5404d07a85085084621082020629507607a0416078140a101d074007080d04103082540349400b100c608144c10548030700c81d840b2044003a071103001c5c0a50700d0042c2036480010420400a200040e0780d401d2309524040d80b01c8400b0340d01580c031501503a00351214000c0c180c01091001c01800b0b0419022501400000b10307000c0003e1003940b45031500b81081041c1c8400c585d009031601e40c14070711980b084007158554211a02d00d00d81c2c9081c10080703030740c3c1e0742e50f910300640d02c60044461540440185000701d4000581580e50100054140032800c0500e41e4600c690006111180d1083c0b00314010038041c00494000841c0604030030600030f4288130684d114401b413400a14a0044a1490f0390844040c6400396005882c0602281c0503518800b85000c618040c040b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 704039334 1250 704038084 704038171
    0x1502032805040314150f100e060d0204022506020406031805070b03070207030c0f24020307021e030f010f050919060c030b090f1b030609161e05070c140603 68
    0x31b0740c5888100c2c154000d2a100004a078003590360605d40207600001c3c1c41c0c00340d00000c8503200c03002614064024240e0550090460786400d04182d00003c0c1c20f80c0075031000c540c0740d0307000308e420408141c2501c03c09451064444e80003a010729260f0303409072115014003c1d420000008004038004910820140010b03542c000310304601da50704c038180c0c107200307400da44aa6130f442c1140241c20400035000d100c0700342071880c41d50011420902c0d20340c200104484103486440d0407071116003070304100c0d60342004440c0054000d40000111203031140301031000d0b502c009001c0000c95100d1410124402d0b04071242d00d2078641c00210000718030100c034404801410700c6400341c580c860f460205015514400e042c24501030300c0c56890543c40c00d5004600d02255010803079810781e0101d550030001d1203490344030300758004800e014500382e10140b40c80c0d88500303581610080e41c40009040820310108000309002c0c228041c28008070540c07184500500011802d00c0002c01003010040008002e0300600b48051181f48840c58404882 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 704040584 1250 704039334 704039341
    0x605062706070f0506010501090b0f16021302030a0c0206010b0a08060a1208040602010b0a030b0c0c0f0d03060305070503010614120304050301230a0501060e01050a09150203280504031415 82
    0x69448065040f0151064060b00c400051250700070301030403044800b18070301c4034103000030316000a915800c82e491603e0074444003400c07030005a658403480e001c603403c50b040050b141c0c20220400c408071440021200b081d0b601090051001d02c2c00c40040d0b0b21032000b5490001d004d980c850340030510344641f5600040365030030054640010044000040c00543d1010b40c020010b000c6444c0c04c01400c29102d01c0050032002c24035000c5101000024000c09070f50740464115003a1001034001c030740c545115900e1210010340c0e640028410014107100101c020001203009010f90ba00700b5030801e00c45520b0008642c402d41d200c885a000e501d1061040d100100030080003001002225001c41001d03c004550041d0291b80410001d01c0264071440303094184c46280da241120b20000c1001034445502c26003c00c0240201407400095103160511030f07040d118060b50155444244503141e03001d40014020105039003103008401d0b4044d490b4000141c608881d0408009081300c113012120a003000482001480e07600d0440041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 704041834 1250 704040584 704040593
    0x70e131a22032d180308040311030118050718021c0c022a011119290a20070f020105032509030c0b040e040609051606031e060506270607 60
    0x3103403407054094544c490741110070010007041da10070f40001440c07140103000a20100d651180c000c010300c040030b0b000082c0c0051019410b9441e51302c0031403c8078550b02503503042c800c0b800203c040c102c580030119000d5080c036008210007a805107204402c080341c2d03599401c007030300d1207072003000085100903204018800d00081040c42120501d083c4807101e0200310100d5001030001c7e000201002c0348210031103080c100303041c0c0c1d64443ca07640c1d940880d1010040c400c8850022029107510300d840c01507080f44000294590390038152a11022a1302c0c22044402c018028217022506180c00110b040e40d0910b0700941c0c039038400c45496035640c2000b0310350000e07002c00062050710b01c1c0c1280b000c1e01628011a5110600d40e0340703010400700d42c415805a44c0c141e00b4110080340001d10f40303400880c201031144064480761260b40e4114048203540f5480080000e131128180001d420000d500380e001c1c14030080381030013a54280340c00b04019102b008100001d030f4012611841414041e070650090700c40c001842107031b680085041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 704043084 1250 704041834 704041907
    0x8030105090c0307020616030f06060e040501050d0803010e0402130c020f0705240d0b0303130315060e0f060316140a17061602070e131a2203 62
    0x40c140a04030300c0000c42c0700d60361900d0659100d000c0075030040550f0381e10004c0007415603018124010925895200850000d00c0b10300070ba0340070f080305658601c0144130050800c01510f82c10b91140d80100e49200384140072440810448c0c1c15100308102402d07142e00d82e44041507500840102d81040c540c9401404901d0307507804507450604201c242e084803403071900c0e00e040040b250307070056140c45041100311460020380080c0c000b4140c0810400800a0118403840101e4115409450703110111514a48240100145912840c0071149800801c10070503050080045403050302801488001048000044041d075040100300381540b0058030124070269500110000d405030600c2c002c1c81801c070084003064041824103841b40c12008480100351a440315440c100c11a004c08092200710700600c1c00100340840000e07a0340380216616003d41c0349040d034600b400c0450240703840860303c0d1400c090090103510055000404c600d030708002c480306024a542c1ca000e903507440f0144058208042104501006144c8192 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 704044334 1250 704043084 704043089
    0x5120f0403080f0601050334081801060e04020d020f0d050336010806030313261506011107030501061d220803070302040915030c050609010503061219080301 69
    0x44400ca110380b503012200e0065007013101c0140c001201440007581015024194413201441c003005c590b003900201658803000c80001d01c4000c08501c0c800180715082000542c01500c28800c0802004060700b842c41030b0051103400342c00030780715100b54481801035680f4610b28002200000309480e1218100d0700d031841d10b0390800c4c603801040f0003c40d500211560160410b140e10740c5200d1101c100304810340d500541d50341402038465601840305005001c4c0c03084000501d40007408841040c00c2c90b540d1998144103040340c002c07034440e5094000138a4484018030303880fa42c9401c9042400d2808150b864002160705d0501d084c0c2c0050030070740c20035000042108420524400303141d2070707141ca640544d80b5181c40520012000f850b010945102096050214082402441c0c0040c410301d005460300c2d59450600f41600c40e00380e0030307518079034419004104000f0840d406c1d038020030056412a0070f01d428140007030407501005005030701888050f080302e036900702c0a2091141260060028144003902ea00b4800490740090 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 704045584 1250 704044334 704044337
    0x6041806060e04060503101a0d031e1d01210c090e0f0106050406030b041404050c0a0e0c04052205072003072a1a0d1505030c1005120f0403 61
    0x1065071010307900380f6024000641e02c02400400350325808090345001000305001c10200c2400901018210399201d00390078210303600954404055403c00016001c08104100421303080c0704000c1c00103581c0c0b55000302c0e28407103003009003445540c03440b8620030b09020b43c15114a0240817894803c1d8025490307004104041591000e660303d26161b560030290b119100c00a0003110301044050204100700d510a41000400c02e1000e00046440c8882204000d01440181c4007281c4a0b04061500551414828107070001881c602107820350a007441081c44806224074020707140500090140101c0103403024a00035903801c0c0c440001c1080d4a400c44004201c1c03080a0024502c84403000c034048030413074001056440c91a042092030604100c48150045100c103a07034128044031f00d20800010749408110700f40808089112000d699504400c01c4002c00c403034601c2400d1400031503406050020f82c0b0002641d481c4500140c5042101118401d01500c1c213000f0b48a440341c5d001c5510007048101c1c421900481d000354801d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 704046834 1250 704045584 704045597
    0x4030207080303090f16030209010b0307030204030f080d05130209071b0b011e08010c0503010e1302040504030f0908070b0f21070c1101080f0f19020d0621030903030e0604180606 78
    0xb24489501b80200c0d2002a602042c02030043c00f103103401e08001e682081040c1001843e0654a640d0500c0d14404000d054480300c01c0826500048030b42030103080c3e480200f040d0303914000b008590001c4c1e004480604040e0410084501c02d090a1240300200c0d00200d80100201c090ba41c1e4480c000c4049400080c0901d1542c860320000040e1114140902c5040481e5131300d03200e0860307082901d040b003003010040140d0300d082c48141e030b45009a00c071841079901a43c00b0703a0303a6114017503584102a025881d40d5000404c1d9500c04c4c0c2d4100300100852080d94010340e1511401541c60b00c100380620312902181001045e124068020301258980143c2c04a4200b403140071020030095088005560b00b02080329031780316078841200080c042640740d00e00103078061000c00710100b0080b1080d035064101d0700502d01d40c03542c4590f10401030180703108015020a00d03034051101c0d120307901042da80007000d40003103100c0201445a20340250f910781e5110000d83d005840d42c00c0401d052074041c40103010140140d81310781c4001c00c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 704048084 1250 704046834 704046853
    0x14010203030702121c0207200609010507060509070f18111918181d060112030804020f06030403020d030b100504031103072103170f0a0504030207080303090f 69
    0x801078030b200d04202d4004c1c1a0300c0304240083c500300d43c070900d420040000c9422441440380580d101801c3c41c54018580c0d0746242520390520404080d404403800d200310001d01c00030380300782e90207000c66400a52005001c00c05864407003525150031480d070800d480014110f1001f051701c2d0b6000d60342d0205041514030600140c0100c180700ca40e144107000c000900d4049040c84040f00c80d0182d4140251011807100c07015886030340d2044110700d2010061050700c499103c900b039004e80e51004480300c40e900d441da8060800383d403402c3c004002d8204040001014030410000082c255650400ca044620314050503440d0351780b41c035160003900c550703171800d003280420b01d880c10060450409503c0310001100700e407241440d280c210344035004000d000d940d146902d4820014041143c0300781c0301c0c1988200811640800c2001014030b005014080c034485d0700300d83c10f10001d04211050101003820382d0031400a240000311520307a414124101803058005940c02c0c40000180044090700007641c401c042d0440050385c1e07a144 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 704049334 1250 704048084 704048087
    0x1002070506163f0912020f12010c18140105252001030507020703080406110f070303032f041809021e01030b060f040605030612071509120f12050912071401 68
    0x20002d000f810f48410440c45c0d05001800e110705500001440200040c03960301c102e0540e1070175070305400c0701400000c0710042800d442e4141c3c61401d80c05170070010110311192980c4800200640281c01d840c15142600001c3c44414040e100302d00f0345604e0300454101015441040a92000020f1300f10403400280f80c0340002e0701851010400c0001d9980c0400d0291800745003080498828a4600d4500401d01a4450483c13105104000d02c2004504c26100466250000c00b00140d0b0140703c900d0b007580190380f10b11450b13428408074003140d0907509900e9107111401160041c01009001c0110000e4200c05003007101400b800207100c160742080f03400d036420700c010150981030080c180a11200010060400d2000b401418056409160f00400181811035100c8407a50200d1810780664045201d545800303c80981c5280d00c100a140a0704200e100c9052a402c66641c0041c0082050000b80c0540b07800050400b4540c40760084802601000f072108507500014082e0b1600c03001d60348030342c8201d104142019203195 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 704050584 1250 704049334 704049347
    0x312010e1305061b040f0e01030611121f0b0a0e030f0c01210e030d1b030e0a0209040809062a01051e0718141002070506163f 55
    0x6522101802403501d801500190302c03041301050a26211050002080c0317004c036101c00c01c00070100310403264659455400c1180c1150406000641c805600704101480680c40002080e001190700046544840700706030405040180c0da009903c5030000080c0b4105000d90101012404050890030750f000d04064111160355080031140c41d60100303840003510840144401c58030301d40d038101e0000c0071491540c15520f183c01c5a00074031308404c007169a122020b86010b0441c5881b000100641010420003000c820740d140d0314201820000c3c460034072000001c040015040039500c4c1028040c00c0f464a40594494910510b000180300088002902c2030400f04498140142d40c000c0c0440100700312030030310310707030100314404402083d00d02882620b103c2c841c5450981e9580c2d4005280034010030505006440400109240c201040e100b1507105650a204960740c0004813a0144944030000b103144030107142c491045080b043d4800f0785d200003810100039402076004c8038002d094960f00da00d10b0b041d020b01415140f1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 704051834 1250 704050584 704050621
    0x106030f1b27050406060804050d02060709170c09010b0d11070f201302070201260a02130819050d1d0103090525050109060c051015080312010e 63
    0x149042d030790407102d5a40741c500c602c0c00803500c41e071490055101d5010605840a43d40080006040d030720402003804030510241d03030340610071720103010a42030040c2e00805040c600d0282e050f0041e0280350700a01c034001000015030400c8098205011b5603034038a401c0b03c15030042c02500d02a1400c09078440c0403503050344101c80c186540130149410340081074450006260340341c4002c0d00301503500c1c004601c09a550f0348407403402201d04000540c0c0c0d01c14a1000400c030665214102c0748801d0700250305c09201c03042c10542c552000d80700400603100c407c00071904800240c0f6902c010400c0c0207a6101030700c2080d0502c201c46a04d80150111090070703c0c607e2084030701105801820000c0403040b40000841c6d1312903000055840d000e101107030046c011144102983c6464031401d1450190302d48010403407035030441403100c001d000601340410603090f0342e1211500c4201c175110320030b207280d0343c0e0b212500034031080c042c3c20001d004600200c1c0d03180d10340000390886000c0c081c0100320210b004400012020703030710505491413 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 704053084 1250 704051834 704051837
    0x70b04080a03180f0b090a061106060123030c07140d091802070803090f0106080f15040f0b070306050f1c0f1e0308010905060306090d050705150106030f1b 68
    0xc10042d4030101c40d01440a40380d01860001d40c140000d01c031010310b0000c00a4140c4a00032980c442401e0208018090240c1c0200b060000c6407403041107001c1c0110308180d020600782010990f6040442c001082101c08582031040900040706118080f0b02050141890a109000000c0191401302c11203030b40f840030045410021341c4107501803050707446100e440c0e0603d0341154805802c1c03500c2903642e0301c1250011118901107600c0a200a8030b401d0090140da001060380002621007040c200344034903194228041307010b1060800c0c102080410041040c41c26030150000032901c040e007003181e070040103440746203e0140f02c1c440c2c17030500c0400c130301d0940e00c40f98400008184d140401940d680c0c841e030b01441004801e468098618001c17520000400e4038481d400c601c2070751010b03082e44c107111200d0704984020341110f001c3d074002810040300c170350b000500490824085c10000e44400c05031030020310b005c05801121040d00504030000401d2070701904010740b2144505c400b4058002c150b4210021030024052010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 704054334 1250 704053084 704053093
    0x1d0703020a1a1201090c08150d0602090a050303030c03091203241f050405011202070b04030c141506131e0216050105071808060615030a090b070503010602070b0408 72
    0xc02840c00740e1030b006803403221100d0604412404000400c2c0003640101d120a0700c55161a010640c0302041c907601c1940321603424a00d502c0c50002c0b40144041c1c82000f0401940010520a55030310200c0d41d45c01008000c080b2541ca10780303c0b04030389041c0c1007034907400c0c0d1a1055240c8886a1b8110030f05407031103817000c42c041d60001021180f0442c00c264200400503000b90500b4038685160350510b0b094005840c00d078442a0381d0364076140004003455840c201080d1081d1040c003091740007c00701850b451700142c0500d485401c07100c0d141000f110103840000041d00700d101d1024002e410112404090340b00b81c0c42110100d0408185032610411782e4495105070462212402c00e001341060b80d6400303081202d5041c441c00c006208a03540300790846109032070750350101c0c402c1094517200c0c00d82d20480340054202e00d400703000350f42017401c00720306048050b80d50540070100220008600400541c0403620b5190441010701443c1009440501540d00a005034801402502404520b0050281c11074046822050081 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 704055584 1250 704054334 704054339
    0x2709160e0d020f090a0203010f14060d0e0709060306090314090a051c02030102030a05100b1e0d02070618020405070215040b09070f0e0105043602030c131d0703020a 72
    0x8074102186240480e0701c01104401c140181c0c40708002607100d454044070050342c0354100180c50b14011100e13840303914485a1889090701585868040e100203850b24a8040b8441852140c002e0400440380c0103200085d02e850000001d0040c075800c40320072a8040d031101c4080340c00c0c00c4880e107880e00c1a9003500360003c00040042080303040003905170301241c0c05030900d0920850b95a0019007640e1050708c0302124641c130384c400e1082a10003a0103800041c240c000d00300307107050103100040c4a0300e4100e291190b1216030102c1c580c144046543c049648142d80314600300542000d21104100080390140241e0146150038001043c250000031051207094501c54050101e030b8959aa4224100c00184032000d20b009085001806101c25160f50002e0710f9400d620940d03035070500d028031084031204c105500341c10400d0183c07082da5032071001d00040200070720184c0207402a42400843c0c5000d1030785112680040c1e4450400e80721060300d07449621354422440307000c45800301c0c004141d0f40e510001e01010790b116442c0c0008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 704056834 1250 704055584 704055589
    0x40b190209060705030702090601050405010f080a0204050d061e0515120f030310060206060103060b03060108090111270306041208100306050103080702182404022709160e 75
    0x54042148009901500c0c1410040c0070641c0c540001d807040701c441d031022882034210f180070384026503c88400e2a00714100781c6040c0000b13008078004060031041c0100c07117000c80d0400301c07180c0407107000d01070150200c0f050316101e10300500205480c00c032110101c64408070403018642c2602690340100c5031802c401a00c400c803001040f140e00c14003100028184502d6001d0380b200002840035600c07a80612280c05012841c00d01c02a003043d400900186c1058900503003846420845015290000d40a103800d1580d541c9000101c1e0040c1600c198600c4c18080201d0b00c1103416003100c401481a808a84450024010b041d040c03568415081c3c0c2d0003000494100c10110040d4456030846600400d090441c0400d42c3d500c0c0c82d088111070b02030f0020350700c0c0c00d8001020750540c1020807161701c1d0442030003604402d40c81e01040503151858654400d51a00700c0410001c5e03426900d50701907405021102c05400b00213001c4d405247c24194040d00024040c440c8035000403c1524044000d140d9502c00382c0321150821342d030004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 704058084 1250 704056834 704056861
    0x11060103080711040e1f140108030703020f19111306081c0201090b0402042d02041a0c060106050f0c0f0c0111060c040605030a0615020a05210f180907020304150305040b 74
    0x1030048403079940c0311201c0340591602c0c8042c0c006c029040117966101c1e601d040c000c1c243b07101d8400c07101e111742c008050780e0601110101509101c90b0003542d103000d00003640000941c074130303440c010008050f0300f458004501404c004c52004084107408441c105a46801c800c11303820f07144034180c00342c441650b00b400a40503003855000700500d414070102601c01c04c941e06241d582c1c024001c40742c00182c070b50701060a110b400c03005110b47d100558000c148038181200300c007031141c0d41d00381401402d0070010089505200020004156840c1c15603000035210111084a840e0b40e517030b400c1103043d40c0001d0350003030520a111030201d6005e0040900c45882490503040580903a44d0b81c0c00a0304007082e559490000088038103181d80c0079580001c466010300040718403803c100381360004108a16081d560140803400d0b4040d0f020b42101d00042c0e08100c3d09403a00100083c0711542d07a001d0540e00d0b04400c18504000b003150340400100146c82a4040f003445440d03181d0390440484504850041107181d8a4010130b104210100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 704059334 1250 704058084 704058133
    0x80a060608010e0c0102060f07021912020127021002100f0e06010e19050c04090216060b06130512030c011e0f140703022d21070503041211060103080711040e 69
    0x1207510b1512f80d03038408070005a07403d0055900401c0c050b00414950381c21b02590141d00315a8682d03910a4100c9500d0340703c51105060000c3c4034201e1800c40a127854000d02c1038034010f010b0301d08200059001d82201c500907110074501c1100901541002081100002d003029025400501d000502070045214890007410003a1081d1f551400500002404d45e14600003000d07840c490f009490125141803421000b6900003010083c8284418400c031500d0411220955046031400c9504803070281b032040d800e07400d601c20800340106e10750030240040d1409801c54503945034440524000c006458009815404580640b006e00340c1089400c400310380402c0c0700340c000d00302d40102c1d0004149003005034404c201c119580a80c00b01a140b00202d00b038804059112003041d907105030020b61100903d0452002407076440300610090182c0c0c0200318040b4054410b854001045000e1011500d103543c40c0c7c1080c03891508440000c540d4001c903446040e0250902e030041d00544c00d015401010012081d00403880100e2410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 704060584 1250 704059334 704059337
    0x402070506220c0f170106050f040f0b0a15020609010b0319020103023612060711070306140a05090c0a0303030c0302090d060f0b01051c0f0204080a060608010e0c0102060f07 76
    0x560802e001c602810300200052140555901285203040440c1c28454001030441104c0e03490b0160400560300c800050462400c012280011001d844181101c0146801040c0070341000d4440350116912428484074480b200d001c0e002c0ba42a555015021820b9800f0b4804054154008440305051900d4507001d454041d841414058100140e0303101d4010036491200440c4404954030040707002c08840c2c655151503070103090301e91280c0e24846050081d580d044c080c03e20010040c4416000080b074500344101800396900090a01410b2140c0202050340310080c0c1d0041c03605440e007030210344113050008100300c640720b0180c40698813525544054000b000030885410074141c01b08030041003596000d800300c01c0c10740305200c000f0b044040303c2400c0c0100e0f0740001c4514180101040001d0b5400754026942001d0311405101017519100084408042e001c1d55000c4002441502c0c4540108500c81d00100155421400204121640080b8596603106c504d03e00502503040400400c06140283c0103059201019 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 704061834 1250 704060584 704060641
    0x60f060d0c0e15040f0c121512050309090a0203060a090b0f0f0102010f0903020a0b090706050d0207050c0a0303030b1503060607080c010b06210a2c0a0b090d09050402070506 76
    0x10f4070104042d60320305240100c0da20358814207088081e1b0088043c100c180140c00c01044101907144d10509000402c0c021903c1d0180507880f08170070800200111030341c505003e070405c000c5080009540c0043e40058030100d00c00d80d000744000c50311035064820840c05010042010240b1a101001d0000c03224120f5407440c11552540c181c070321500d00901461660f54030a03802085518200e08040718162406802c03070b1100c1d080107400b00170040d805025034520200400005a441c00649411803078801600101c0340c000109101c00028107815901c103a4001e030041d1140f20100055000d9503131540f04c01c1310b026901450501441003c24008405802961224800081c00d0f200502c0000d46582203501608561030000e603c0e0366041c0c0c40c554040c0d0300130034803030018041e100c0d94004000340e00c0250b81105600034581c40301c1c8002c5001c2045240d220903001800c180742410041445515800c541c900c0c1d0012806451000a81d400c041c401c403004690070202804454407a20110b050b070030110751000d04011607 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 704063084 1250 704061834 704061871
    0x30216060c1d12070b0309151003260d110c031219062913170c010c150e0a080a0e0108150a060e130905060f060d0c0e 52
    0x2610401c04081641e456500501c1182d10300306400600d03400c40540100f49001540028890004400080c0c1d2001c40344d294895032412051860309820140029420710000103008649100b034000c4000c5da80a004a101d92410600030103601400381a0b040100240400000200d0b40655000d02d00740c03041c04406e9454496a980e4103407854211011019900742c45c5002d110300590b04114401030070306100740601981d03241c03040c085055020200352100c060070340c01c40b054443c0c40d40f104030790341c0146000e44040c040e078035100129840f0f189210f1b0b881d100d225224402c00658051080300d03031026030001403485181501032403035010340340c85142a2202e100342c5144100281c000005000000c86d280d684000700d14641000402040b0054a07280307115254200006041d05c40307070450b106440c3c060600c81c6e0039016000218001004800d81c0c2d0000c50300c2c2c20300300c008000f8003148150140607000100500f07501d036170040040101d160703640203182802030328080001610441035141d200201c21080d0b11780f001c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 704064334 1250 704063084 704063093
    0x140303011527051212030906060a0f08030304020915120606010f02120415110303130218090a03031a0a081f06060c0f050a02120a03031a010203220306020c10060603021603030216 78
    0x1001920187d00395000002004602d0070000c411134000d05d600d114190409103084103d41d00da20007c0c0c03029006d00800c900003590130000707410100040a001d40010318100300d90b40c00640780c2d07400707076885800100c80c100b03413145240c8009904018039113452105450546800b00301c1080c03c0582501710140b140100d0202c912403001d0015500c074414006840e01c900700c80c0c0c8108040070710000c45860903002d44000f4084001d000160200465a240c10002210641000208110700b20500555800001620086001e0b240443c11002201d201c82d60f10008a0b810215034040c0c07100c6d401103a0008a840301c180011568039081119664090002e440000902e5008030354260b40c00c9600c814035030b00c1604030200301a450311420050a0448400f003031900301c4940001d44921a81034240c001400c00b1400c810310900e48030356130f00110b9000398210f66420b5030f007150580380c202840c4c2824586140c0f01c00008d005010780204c0300701290300640581d08814641d001c0e8001e40198044425142401e400c2c2800038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 704065584 1250 704064334 704064337
    0x241e0305011d010e031e16020405070509010810031127010603020405120c091504110307030912020a0201021e031c02090406050109050a060c140303011527051212 71
    0xc0186201c0c44154065850b0254250741c0c030391521030507a03402001a000d11550703179285140002946001d60b665a40340c0c49400d840346146020195105240c0414065840e420000501503004281c0720550303150360f14440d115104585100140c00c6d03218406a4910503c0c0c0703401050765800703001c5601000406610501001d03000700341c000b540402d40c0020103200c0c51030260101048181d4200042c124a110740001c52001403001d801c1c02401d50341000b0080c0140e460f40c00519800742010704968070fa00c0c1c0044002e000e45100c01003907c00b009030444002d141e6102041104040b038042e0010440070b41d001d000311290700d405a00250b03490005010002220290103030075499400c19840258541500c1d40420049038040da0040c0d06000c1040f40c1045151244103422085442c90b0a0450807002c840c107043c00071048800a0a000380400030010540b08a610014800d0491543d03580601c94003074608010f40b140c02000d0640391a5248404019500d480c175544498403600c2d6041c2c03415a9124540c4440c503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 704066834 1250 704065584 704065601
    0x1090305190c080c0a0902180310020409050c120c0d14070f02060c07021503130f080406031103240319210e1003050403030225020301241e030501 64
    0xd40c40a001c60806000b02d8015401c0078149000180511000300c0340081c02c240c1007441804a21070700030034007503004104590041c95001e070240549243d40e031013010450003517110740102818186810089400c0a03103520a48100301440400190207454000441000c0e4200d0a4440c08a90302c6e403c110100c000c401103018003c4055858109421b4102c3c0710107424250000c0405210a1042c4854000343c0c5d07071f507624044401c41c5040019525198054900d8a90a021401a0002107000300300c20400040d100200102c640a603000c02140b07034040004030071b504c000d40b11343c402c1d031484a006140390400306120007117500d002421600f80c045c41d0440c00b00b0390086001c0c01d45492003450b801c9040300d804551055004001c51614400800b50080011081d400141c1c8000406a686c030000d01098041e504031100d20340844150071001034004040c00c000c03400080220700a5081480143c051301061a819444040d54840001894200144c2d0750490700140480c89180c8030340040003020a60a10402c2c91 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 704068084 1250 704066834 704066863
    0xa0305060901150905130f061d0a02070c1806090c1211070503030f07180e011d010b0307451d01090e0f1006090f02070c0e0601090305 59
    0x51525000082241c0324405900c031040e50b0505a803070701c10865009481209503281150720604010411500c407008043c3d00c0c110070f00c41443c052010034825120f021241c408034426034416001da40705400442a0300400000419010b8280005c0c481c1d000030700c1c0d60284100300d1600000341c150384c4022000507140040180004285200241e0758000414002c4080f80c03001629454544407495482998a20004183d205210405000303e0802807044001041c9201c0c000300c0194107030b441341118560b8640078440c03803018414100c01d80e054505180000c0d0704944d410705aa0341160388640c42034504201f04d00b02984502d8204491502d2180d520480d809034449a850303442c0c004881c84108001c039040c03a00701d8240101405100d040a02c5003608850542c0c0c410722001c192440b0083d4800d10b40030030700b10703852114040c0249a20020009034040004c0b204e241c08284150024005100200d01c9a4940500032000d9041c00f440641e082400c1c0c3d03a0090300c185400b41016990f504d94904103c14001c041e103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 704069334 1250 704068084 704068091
    0xa02090a02030a0e030711210a0605010f2403150504051005040507142b020c0607030506100c120c080301090b010f030e0604020909340603060605250204020a03 70
    0x3c4200703c5480768611200e0500b005500d003258548846805015911107184500700030104041490032180e1103a45174103146080712140d5040349400d0000e00b42c00d0080120320751142c1130021341c944141c0d081120b146071191550110f404141001c0780600407500000340800c5417508002559100c42c894548a91502d4011130b4070389007000108415694082c100408009a108081102c3e8880c482111a540611800000c00350f1411310210a40030302c01982e00089403000c00c44101c810004074601c0d102e02c80a907400c11240e0344601c100200c0704405030741c608c000360070f80c104540007450660b5040d204403518108a40ca00ca080d544404480c1d0090300300e4000740c1d0b00d42c10804500d5801008c1d0b039006410500341406001a0840c0c0940d03140b000074000b0340b240b5085008034441050920450184001004040011500d481c1002c1e04142c0c0010088100c1840b02c440006d00038400d11950701610200d6907018900343c01c988269940103d80b1b000b6030f0410441d8120360300169501e10081419060603200070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 704070584 1250 704069334 704069341
    0x30a091103120414060a2007030f03030c08010e0c1b0c030304030302210f07060207170a030b011e0206010b031e0a060e09010615110717030c1212060f01020a02090a0203 74
    0x1042501c9041320701c3d01480d000d020413210780303410017074003000015141036981d0010042c07207056241c0380e0350b90f101400c076207074440489003410b905800000014210344c4541150380d90790001032144402c111845110410180411210b00141000781c158040f48181124000030940780002d04650140d0b2088002d6032200c480d007071103003403640c00080d0007024411040b401c2c030088500c459000e21640d80020300d41580001c0700350400c013031071071000c1031203026918140d26400d158401400071700e903480311903003c40d411100701c0e002001c0c42c41142d92106501d9020741656440c0001c4495150809010f000e089808180d510340c0030700f0340f000c1845c4074640d40071010840310300c2d001168071500d0029240f1b5070360342d0404e01d00f8000e82c0f100c4620b810311000c071807411040602c03420070005d0034202a07812816003010320b007940e103107401c2b80003024286000d005025aa003d4001200d02d5282d44941c1d2501901c10503c100010210320340811403440208040c015101d00f8035683d0300080b491013044130040380a56001c001d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 704071834 1250 704070584 704070599
    0x305032d131d01050f010e011206091e0902060901080405100c020303070e01050909160309060905010203071403070f0503070c06330605160507210209060114030a0911031204 76
    0xb00d500e070040011440c00d50510f070204400c10700340460103041c001240e07503c0c3c1c3e00340d2144216000c1440f41200401030300d607d601416024003900c0418440c4000c6425420541541078030426101c1e03940145500d10304552040150749440b0300800c1541d071805011070340d004200103806000300c5111a54003841c2c0c1c92808800261523028240003050410105002c164001d850b078010540d0442035135842000c642c011600c003100941480880202000d04065001d0100f081c150041e41c01484d0545801d034001e10103240420280c00308640c4000003d0040045410880c06600110b400a259203060014100c0584071203080c4d60070100c4940202910791140081c2c0c290b450700001d680401d0101c080c918034540b020051a0340100780801200181561092003004400c01560005101c20005044041d161038510a4141d4103003030140d01482015000405030f61103804d42c041d003086940701c483e0440d01e41ea0340c2d0200400301600c1c00c8038403007503042c40e2002541d001c10810b80c01c1d00800d03001c2d55aa1381003000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 704073084 1250 704071834 704071859
    0x41206061505030103031709031b010603050613020604030303050601020a20010e03031306030e03070b040b0a0b0415031e142a0d1b031a01140108010305032d13 70
    0x1020410040140f00510003c0c0d03110100e108224080c0e04103420320b4580100142c210311400807030304a58481513034034070b5011106410200841340900103840c5075076131f211a4002c007010b003050002c4d84030104010600019010b0b03808640c20510601c121a071407c183c2e91440c01100641070316650360000c0c02c144542540c0e11200c12a09144240d001c2c50038000c102c2024200e101e00e90080b9010f03d620303280322071041e66041041c0c400c40e6400508203801400c160805116098050b038013114014240741050030340b410540180d408407884035451210580c516150038840000c0c00070001101040911036001080c55503403400400481000036101e00d00c00008000f1a40d440e070142c241030300b0070710111003600d5641c1400f403459161300f2005c80d24107241c00008102c0c0031601904001e25946c10048034070202080590864165001000d088005102d50303001561a10000d04c001170859004002002c21151040c4c003227208030340c8000d0b00500042c50410b80513a5034218101c0e400c000807138120101b10040056a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 704074334 1250 704073084 704073119
    0x308040e01181415010c060c050c1c050d0b06090d05010c021509060c030c04081009060c080f0103060213030c03120305180d0302070c050d03030f1506210204120606 72
    0xc002000300041c4403002403000402c004e0249114005940540e4029030070b43e0a9264002010080e843c5203101c044d00c9600040b11a641030300c585070044280646014040b00750090a03242e4500301251610a5400340c90f040c483d85420000601a501c1c50ba101c3d1100313040740a2083c400401c03500b0300042c0c000d01d006d03611200b034001481100d05010b05941b0220305540c0016515200b1a9299074840040c1024421a84402458460201d140900c12030703d0f4088040c4500c82d22080c4080890f0348000c40d90703184107587c514081c8a81038010400151140c0c000e0603841d64454441104035a00e4540c0119003140e13038800d6520005511190407016850300c00e207580b01400c0d03880c42c60003010350143d4559600c080710001d4241540081e102c002d120085403ca03000740300081c059460201c603450000d02920b064228401c0c0e480c107107610f10009124000c036030415500940d8a149401c8980e003101c0152040138104201d205900700808151940e2075816580d10602030000401d019180c150820b40b441c4174007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 704075584 1250 704074334 704074379
    0x5190203060a0b09060405180a290c030a0b0f0d0b0105151905181203070b241504120b010f14010e060a021608070f2306130308040e01 59
    0x1403511880c0e501c240380c0c141c01c00d00c146c50002e40366481c0b00c01c07640001c01c425610380d8076202d0715010108022501400e0003130040422804020b100c0c1446807140c90420588200d0290328081c00059078640c0a984680340810005111818480003034010441029a1001c140c2e8903681d240014030450911460359030b215061034241615000520900007814030040304505e013046800259280040640d8084000461000f0030100060814899003903a9603c41802140c031854108c0010310b010180862542c01192401603500e0f105814104100e52161383d107602c2078400400344401305003196500d20202890348110006001541043c10060b44507160b0782c4295a01c480c503049035200c1e641e100500842031203090b18403544400c240c41c016414065016004080c030720b042440003400c544000381c00c50803500b0b2003580e00131058444403849003044900c10303007018400c4076a949d45014188035005180c0c401c0c02e01241e40d400350703c0355a101c00703a42c41036200b5000202d0002c01400281c411209405a09812 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 704076834 1250 704075584 704075591
    0x150c090e0108030906040e070e0604140f0d0506010b0d0e1b03070918030e0f0411030a140c090d08040f03050a0204140708040206030c04050909010219091a090d05190203060a 76
    0x2400107025119a000c7d9003c009405070100360724901880782044005402800d65440360703120b142c0c03032684d804e481034601c0c821060444403034054200f40c2503121010fa0031401410142e800c041400d00700307520140002155955503541d040c544001440310310b81e0030340040d218180b5003800c2e004040c940311f85500b02d150200d00d81208038101401c8200c42580c0070f0344c5810b260013258134000000f001c0b09107c0348444d800c030341400f8004084020a00007184248440c0e041007140410400c180180d1480807900b20800340c40030000e1441d0741c94844142c54456200b012124500350300d0b140c0c072803004086548110382a03840000840d0851502d03000d00c9984140340a01d1035414506400010704420000d4000b900484000021922201c100000c4602070310380134003440610b042a008a500030740c02580350000b440801e011440c034a502ca02d04000454071000d074000d002551600d0714a00c591302640031b050303001c40826070b10f8001460070710807902d040200000a802070602c500501d414400700418600d9040d00c2e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 704078084 1250 704076834 704076847
    0x60a0e130501091a090616030902060903160303030f020702010e15071e0506070f0206060d050106050d0c0f050a15030f0b090703020a0e01020706090306201209070b090913150c090e010803 82
    0x240c00f040d0b40c404c7d01c0034900030800040034000f10b100da2180040147c0c043c0076120700d4040f20107007540064210380c82a034042010b00200343e080812806204802800241c0b4034441028518014460741407010841d90300d2458042580e640424400b48405c0c0704020400901044050003800d00a0503444076003824095424807222600a4840704010071241c8210800c880346401c0c03050940c0850040c0c14058281e40095100703041c5081c00300b09500c62010000d6902d10003182d9424a21854400c481c0101300600c42111b9161081d005040b0600c102060956140644242c0d40d50744941207004005075100107030b840140e010010458880c40b00c0c2c0905550094804000048c0d0160f5103604594001e14001445004d14007280f101c0c01c140c15114019023804141c220305048144003240c024501031701251003580d62011048100d014020385540c4c03100f04000080c6694040c500b560a03600e00c981c0b035a114080752010305000711003c0b00f0b80d8a0006000650921550303070030080184c054a02d04005505001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 704079334 1250 704078084 704078101
    0x15070507063525030603140708030901080a0905010c030920030304052103030702150a150312030e1f061e1e030c0e190203060a0e130501091a0906 64
    0x500d44400032680e000000142008181c0c0341c0e20f1003010314000058124100804009001d000e01e80001e503404e01c00c02c0c002400708040012880202c800f000040c40c00c100300800155200e01c001004052065207800440001620a202e803540c1a10282c40c002140b001070f0070404240f100341104420a920f00f4008824155400002c2d01c2c201c620441d02c06d403060501841200e546122051103511390320011050014060300442d5246a800e00701191840e295035a03814042540c403611440a10303980d49901c1032000c150202400d40b0001d10340e080205220001000080ca42404900e40c001848581160480100402e001304401030466143c03004084144908542c45003580d40b0034814103185500812250411003845a402550403681c0c0070065692a12084402c200864000d20081500140040c0364415482501c1c01035034090b003100211070030031242581b0004040c0101e5490312505088900081d0240140d000c914450751107080d072034403407012088040501812058040e00704500300304121 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 704080584 1250 704079334 704079407
    0x1509060123120f060108071d0d080408061008060610140706090b010b120a0207030f0f020c0a0b07020301050105041811190303021506010203040803040b07021507050706 74
    0x110020140c450481c1d04020030650b10500c42e440c44580c010008000c00c0c00c20002507a485044282c07520343d802d58803600121a098840e607040c00a541c1d4100300720313a5a090180300c040c1c513075102d4454030303203401e440f0485980740150848000c1e0042d050721500744401ea5050201c5900900207541c1002c4400140c0d9015012903a041c02c04002c050000c0b411742d051000355003085680c213401c91114134055071110140021540106484400714010401081040d0490303c200c84580d030301a0350300c4148041c09002121104400040102140f103100440e18442c0c2d90040460001c04410480995403a6144103240c2501c0301640868856894980145201d0188001030805c1a83c00000848402c10380b07000503201380022107611400545065000c400c00d03030000b800854440c1c124aa04010342e9a0074012684c07489a4080c69815400900040004100f4800a07110380c1d0b200030a20300d42c0d20440ca00d040300d0750700503580944260340000400c0008036000751050414201c204d03202e4400c04254501c01f00d00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 704081834 1250 704080584 704080607
    0xe0702070e1b07030503090d020601050f12120c0a0b0112020a0512010f050c03180a030918020702030f150f010b0a120b0a06020106060f0207231504030b15090601 71
    0x880d090000040c1e0001c2c0c1c5044400c01070503800c0030161900d1180c1401040e43c0c20464505250b80b007941065440c07103000152041c1240c000505061088011109100202d11400d10103845441018071108110310020003510621003004000c04005615007440141800103030301c6039042261402c0301d18050f03101c021080c001d440f004d5406c0e000e0740c1c1d0560122030060a01d42c010400292901c0d05000c8116580d10003140110700b0841e1021905005080135601c40710200802008504107240c2084052860060303c214000181001070400e0016001f003802c01c1041102c2c100f0680101059500d0754041500c1d4603008905c903655072039a50b042441c05041449080780c0758080c80810303e902c040110094128500000f4090210283c86a8951010b4068a0346004100119030242c00c50300e54a440081e01000311200c100301840c0040c4900300c0c941c114041145001c0d000f44200d11242400070552000f00000e40c840c51515400f032600c9160000b20b002400b58447c40f400c074500511420380c1e8814000c226 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 704083084 1250 704081834 704081849
    0x5101508030702010525030315060521060315041a011e12060626120909010905070e0a030809030d1e080601110703030c05010e01050f01140a2106060e070207 69
    0x246c0c3c1909403d0318804984a0300740f00c60282248400d4010503601d9001800200c40e0440c0c07041015484040a035564010070505c825401240c000340d4219a04560305075030460005401d685801401c0034181450082c120307000d4a0000c545826044420212604540103101d034019556130300080c4840c6081d41c0c40079100d000b40d542a9101c0c00d8040c0007869114500a003800c402801c4450805400700c000044410041229409a00940070010303013900c0464180c007000429921090303081c04042401400d014111804010110f8100c0003181c44580140c405107010300320094840303e42c20101441e14144915500420603061041d00407220a03900d11400c051543c01e00c10391704c0da01c1c0030040303416001450f8000c40600c2071901c008149500052031401c4140100000d0041c0540040200c0c03c1c2c803800d03100581031111500040040e19006100314403c0c000050601c04c096a68242c034a0440c480d802d040c0b5441d66140e0070040030002c15121f00b10041039004100c483ea450f0a020203522000280308244 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 704084334 1250 704083084 704083087
    0x213060e0f0907171e0c0112090c0b03070507050c06040303050403150f0c0e03071e05012106031112210a02071505040e1312050a050c0703051015080307020105 70
    0x5542c00814440760014007249101d220f81c0748158078100b035507140f02800120710881140f2032040300110100d05000e800f0410b850703541100c40d01d560940018140d8001c251030305400034501003280f003401030046000d031180365582031701c4220600f4014142001d403c215441410200b10400c0080c0e0040142c5085a030030a03070241d4450100c0c15860040c15114503107042c140e203062b0400e0440d84d0043c01034004a030b025030803100b61a0302d8000003060701148089108801d420f00c44100a6076208111080603050280f9402100c0030346000010207030740941d001200d2003955220395070740505110600021154014000300a04440c0f110b20110b00081c120740203444200014030a140b80f07008100200040c000e62900c0003903141c4e5400024120382080c0100c0d14071940d80d1000c1038054a480076030312041e6801011400302e480c0100c100343e450b07030301807981c1400340030080c0310a21003004103106480c0114024000351820150000303a4204607004600201c4172401540c206000200f800801e40f4806c2d6820f0071b009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 704085584 1250 704084334 704084341
    0x1205040e060409020d02090103080c16051c050a0b01080a060c020a030e0913170a110f07060320160308090114010e091f0606090501030501120f08160303090213060e0f 73
    0x2802d1942c000c00040e4208407c0000041046031800c01008070020f00030568161182070300c00086c080500b4030890740d001c40d25142001e448004052802032144c8114102c030000b2a0760f0f074648000300001d0380460140c1c0c00503840001803000754081c8801101c0317584060101500742d5034000c0c0c1142210b00381c40e4000c1c0b00b01d10028050001619800d080b090f0040341c01c0503402c2807080c50945551264580070700003420f108001c030010380700065080d043c1c040306024000e010f00b0b01c0e9040f401020580080c0815845041204c00f60001c410000e00068240c0140d501b11000c99050180c5074103405040003946a140040040c11401d294580606540d8681c84441c0daa4985da00240d14201000e454400054004646a0b090740c0440e44801d089603003e07100c2d1041c0c6503464005400701c41003403041d0320f00000000040000600c07207a010071200c078030461619061080c05612100c0030b05440404070040f903501c01d0030700d05501d416804000c844890f40c60910a880c1001000c0c52940009000440040000c0010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 704086834 1250 704085584 704085589
    0x5060a0b2b0e03180306070c0803060d1202010b040b0609030705090a020c060f07020c0102071d04020d0602040b0403020406090b0f151908070f08060f060915040603091205040e06040902 81
    0x100181c08800ca000d01040038001031031500c1e90f00c03020850000407101042c80d0443d05010a445106490329101c03e80d248010740c07035250055000400d0b0301d034002d00790014140010303601d41d02001600916400091030746191002e0000b25000000f90b00e00c0340e4020f00c40a6100d580000d01e0714281e8405445114460303c178541c000d0064000d409102805000342d0303080003c070201d41310b24a4880c1940d81e0031603080404150040e6280c1850b07002c3d10101c3c07011403a034035521400542c0300ca50091302c098554080380320341d625403d0407604550060080ea03480017908100b94078180c05103402928070389008115800480c0002068098508101802850b02e4032100a0003c1020291a20b650759000c0300c2882d5040c5074401004030608490400115008110444110780b140001074895400130f0b020100d06403028017001455080111a154041906421110340c040131001a000510003034030040703001d800510f803030314004828000700c408009040c0010030124100e100350a4001071306403800105003145001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 704088084 1250 704086834 704086897
    0xa0c03020309060d140a0e0304031103190b0a0e01020c211201060806010f0f0c030e130f0c0e01050a09050603061201180345050d1505060a0b 62
    0x84641e807021000c1283d4030756001350f400207501c1c003ca6003110251565214484021144d100d0000c6001303500920040c80092103842104c01a5140201100d040203c03a50b0700c00280c0360b006800b155084a820107100800c3e0b2103001c0c4409408c5801d00a40c18002030000c1c1d07983e40c0d5141400d01d585800d842d490001c005651034115000001c1c0508120f0345503846900207070509030117480b080e002440d0100000656481900c40e00740c402003559807012480665181103d100003140c1100351311560a0720303250404a0b1901c150000404030b58000302d142907203454064280e04034040d060303040c480308100c08c4001a600840030000e4501c00c8036603644030b460307940220308100c0d00e8410580b015840c201320040034030401a07031605a18071030f9032604020b4480c401c0141110003075881d900f01169069121100d801446c200781c245956582255510300c03542ea80004195001000b41555081e0041c004c881c180c82442c000d0a62012054500801c03192900380f01c460144a0711090010700c0e0024600340e000344030b8030038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 704089334 1250 704088084 704088097
    0x203092b3908190c1a07120f15090207030f0809031917090106060c1712041b061b03050d141e061c150e03130315110a0c030203 56
    0x61030301050512030302e07140400c1d5100c4000400e200404080d241c8a80340300d82001d240b000e60284220307000c0340f6007800c29401d88201400310814041d5200300308071041c0b03062080d200525503900d800305040780300306000905844541c1081040d28010001c1c00003080d0410a222949d64541c40e20701c90907a40d1030b00d000c0c11400f81c0c809031a000f210303000b4180d89040d4028000c1501c8012014030703010782c1e190800d8460890b40d03607103d40703008a000a04120003203000500d400648003000d409181c5041c10580f02c0f0f0003055002c880440d200d95002c10070341c09403e004000080074248031b041c12a25a031041d0342c604443c03000240b00404000d000201c850034000690811104980241b040c0325550910148080d00000b202c03203a0000b0911940000d9524a05040440a21041d40c440b44550f00d0381912081c20704001643c0c111001c03a20b400a4101c440c004100902007451540d211501070f50551400103c0a00c408558201c00d0703050803021080101554101c892000c0706085c82ca070084014542a0b0a502500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 704090584 1250 704089334 704089427
    0x1a0d02040303032c0d0e0616080c1b01080c091807021f020f0d0e03040e04051b030105070807050a1803050106030203012301090f060503010203092b 65
    0x22900004140e0107030400d04a843d090142c1c0710320f00003a5084c0d0690803642c04c41124103548820040c030304441c0544501c035491400942031a107805044d22070b051b1184058081110b42520000e000c3c1e001c46406e12174913010117004000a8054003051000800c0c8034000350181440c28400a094140d40e980c0d00c2d902050300b00700c46400c04003880e102e0b201030740314814900c5007034460103e511034025012161085841407030303400c1d4100303041401e000b406400506507015044ea01d88420440464030b00c900d541d19074400c502c6280105500c400b4a4445a000075803641d51a00036030502c030a00000c65000754145900610f28941141c490b62128801c0310304420200c861a80a00305520200034800c06410680c1560300a40092001072118142d00c9021481230152030f1411803241c00600264089170001e41802000c8040031030766a489100003030032a0b100f40d821019039400350244802214815000080c05c01e0044030a44d0702030103440c4064203108502283e00c500c140c0c50080610440c1c24092a0742001b0180e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 704091834 1250 704090584 704090587
    0xc0302130b120c030f0a0510050a0b061c1b050d0504060204121b06020327010e040606080402030c0f030a020d02030114040503041a18010305270d12020a05041a0d02 72
    0xa01c54803585948007241c43c18080c0c0601000d5050690300001c041d400107511200a211182032401e042c00285806001904800d450321a022000d54429025107184082d040058540d03a400745141360880b03e0080e80100401184d08280c400310f5000015034100065801020401e903441c3c0c07501344000d114641001c10300080c2c140b1400144030b00b40b5225803121142500300c50a0346d03120b00050380d40340241e042c2e41c0e00b17200540c10710f401d0900d51003100c0f034030703911060400030a509060800903081ea8a40d80041001402d80410041586000c02017912480402c1e142e90080d600048003103a21201e18039000790083c028010f41408644003503108070103183c107000d80c0c0d0344070381441c0c60181d03141d84c8188210012440720074002048411343c28100d943c1018031134201800c650000005401924004143c0001d911408004852603943c1003c2038000380d0030200600040302208401904200503564655156803040c400001400e4100013103d05403035186a06410380c9220f2041c0e03130304034800c400591042e81d00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 704093084 1250 704091834 704091859
    0x10c0c080607030c0216030b01061808063610090f0501020a200606060a080703140103140709020405180c0706021303020103050f0405060c0901120e06041209030c0302130b 75
    0xa040c1d110640ca1341c4244d098880140103840702886a00450101905203030250004001d0940100308400c090003880ca1040001075070354103182c0c1090411141d2182034516814400d001030040c0302c0000d042c060a1321110301001c01c03241041c1d60307504266643c205550350b6400400920049140c00d00f19a58040001e566034400340b40d000744075010140121409207002c030101c0407000004100340303103d2100502080c0c101b01c2c3d089030403540008050950414141d0f242c50302e2909101d5103003083e01842c05403a131200d0032182e0030740c80c1d46031800300e41c88210818818001400903949601226141e40d50901004080d41c072511403541e107a2155200003802d072440080e00000080c0d1034010081224000d0300d040100340c6d50360306039070f0810b1022500102a41c010070001214407100e280540700109043c0340100e40c20080c100600125003005074803441f594051410030081210000c820482101c8519000300004e15558552040a01c0c07400004d109440249080040c0850350703000181c0d07000010909050801c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 704094334 1250 704093084 704093087
    0x8090a05070e090a020418032a121b030e090c0f03061215041a0f04030e01120b0a0602060f07030903020307030e060d110c0708010e0c0405040c27050a1a010c0c080607 73
    0x54047e004501048032256400d5410400d00d400520000d10b08285180070466a9142c85001145541e043c05101c109110140c032100541004442603119442c0c0e4420310f410081000302e0002c00902d01c0519800420007480441c103c0340550b900540255401081d0006201003603041a001600401071450301400f0030003070003905041061811071030b0481d65020346406c11140740040c0103c2e80030307020070000708500815500c240889500007514180000e1000c1058000075150b6002e54030800050f800b0406100d100700d49220043c2d0813240364203080081d13486540e80030b51640030703108003c1e0a01860003828074042d1601400c039055001d0002d03040060b024035282101e100d401c120100040d038406c03890081040217051142d800c50362a02c070700915800340c81400304005044000d10032600000384807000100444a0700c612000402407540d00c04041c03011f210041d003240c00003844c40f240f072424a401000d54036000c514084001c0402c0c64070850314034090401c0710944c11180d00c40700f4240708290401c5440d6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 704095584 1250 704094334 704094371
    0x31407080313061704021c050f010e030c0601050d0f0803090106090603060608010b0f01051909030b2a1201030605090102070c2705061309290708090a05070e090a0204 73
    0x12a030644820324082c1c10313642c0414182c10103c500035004602d0300e41d040040421701380b01902c40351141e0700b1100086900f10340715081d10707888049088168000f2070346030b240480500040b80034203015224401040007640b00d946a1a82d04540606a010000701003840e9000c20b405c040050032050900740031a56680c50100d004218a03c42c00c407030b6500e05820350619103000c080307005030190142e4032242489050540c02c4180c503c00c40d0300030144041e1810001c00602e502601520070b1006c580040300301d030302100d0440d6040c196400c03000e826100410415094114401c1600e041d00c0d0401800a0140d4910302e1803402441150b50142c240c4080b420700180030002c45100000200811404000314207034406207038150b03003041d1000d030392044110404070b40c100d800d0740c00320300054012070484401108542801e50202da80d051503081d901d000008101c070190704447ca2940101b00f400c0140881001e9844498a40d613150081c91f41c1c10f0400000311794082000c0040b0703141140c0060081081c04207558282015 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 704096834 1250 704095584 704095589
    0xa0b18090309090c12073014011d041209180c030f0e07120314180307053003040f06080114061e07060f020c0c090a0510031407080313 59
    0x540a1400095003504e100c1044d41c0c20014076030000301c440e886104045d00d0701450174806400407205d0508a4085d440c000401c0e030701104442c0d5000440518410140d4012081600100701c0000300c2c0107c06000344520140c940e010b074018042640e06035000001711000c0c025540704201c2d083c00700c4401e6a15103901c2e4841c0000c2c568945080040c200040440c20a8810458401c0711540049604000503500c5842e605c1a051107482c08010700e0702e5440f070000003504031f000009070030943c882c00c0c840c05081c00c12021001d01001ca8040b20908140b004841122520301c91202c1030503030300d0128001000041055502070207140380301084280d261034004107035903030911030a0041d44024580d81c1c0981400303001c8401f040c503844c5413414024004000e811550b408040101c0720944d40c0c01903030000712243e00c050714400c21910301034881e101e0118100258140e0107894400396600d46802e000054000e0390702e540c102c036440f020b182050310389061110300709070840d40000124003000400c007489600f1801203805 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 704098084 1250 704096834 704096839
    0x4090c080105100c080c010e0a05070e01050409020a090c120e01020a02070e040327050a0b07300e0d0c08010e07061e050306061c0c0e180a0b18090309 66
    0x5035607a9600800c00025a03581c0203101080030b0010480108100074010b1840c403405a00114886611160391031030241c6550b0b0680ba03a412000d0b0074490f003200018010300410046600348241c2840340c000669400b407d00c0f400c0010784e911712009010a018001490b1005211031080203c03e082c1910a03000c0d42c8000c41c800c005024440c0d01054440220200b2030140380c150f07a6034030152707000d0200c1205d00c0b941c0300740c90410121a500c00007802d69848503510081d103800641a6160202c071301c0c000b055184601c006041819880c07049401c1515441c4800805508074604165060700010114035640c100380c4001c1d0925028103004212018150001404d1a4a0b442202c020541d078074400c407900c40848179404003001c2080030799440f03144110f001d0740e00510004d140e149000460030130f01400c107070614580e400c3c90b03480c1c000e224602600082004984503094827052039050003010030a60079032004000101c05503a401805003261500d490082103024a20034040050400000141ea030f40c000c0300e2880d2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 704099334 1250 704098084 704098097
    0x3020d0806031009060e49050a090b0a020d030f0c020c190905040b1005090408090d080f0a0e030706090f0312030204052d06070f0321020d02031e0606040611030d0204090c 75
    0x10487c01d501034510010310341d00000e0050141a00007100c10781c0c840f149400170022240d1000c680c0c1001301d001008bc03101e086d00100301d801a050000341c160781011284000f080e241c80c071100300b034607004290b1344030400c002c03144040804a00400c8000d9212141c01005820b481c1c4801c110402411540041c0114101c501000c0f0169545007004035407402110000c2240c5401c1c007242500e0f050015000c03560a115120300381c20081c0c0504000310580090400000044807a5080311070b5040c00d000c0340010b002c8625002c402c107402c10003180a0b41c01719110062041020b00740c2c015640380300364155001303810000c21300b50714008408040c1450715005e840b103540b0420688070b40c01e910305d010f400f160a455032242441b051200d9030f840949070304c5c0002d5010000c0c00c100075142d0045003a0b52008201141307818500513140e041c035608410003103241a480c05041a601c03801d022003655000190780c22103169280000d10f06010403982801c1d80660445915114004100440e00c00c09a4004070100d0201d581c51a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 704100584 1250 704099334 704099413
    0xe0f0304170a021503070207030803070c020f0a0506120627160306140616020a081b0301060621060b030408071103011a040f0b10090303020d0806031009060e 69
    0x10b45030100a01c0080d440f80710b913450030440c240080c003d1940031b0713081d005603683c0690b65201c400480e4000c842c02c0000401c47d07a890803c518012040c4017038000141c41030807540c0c1c20580461824414035410030704008000000848175903603284240e1075000c80c2c0301c10350250340c5904c5059554180c00d0b20b8018030041c48081c0e04841c1d0307206c0d2080c50b040b12681c0309080e010581d1070043c02000c0d400081c03840d601c08000110100541c0340c088900e8000c1ca4248018a01030300c4d1503a1f400144880a69018800c0e410240204070031a030012500080704c0f140b00702c0425080314410030400416480c0c1c41100313484400f0081100f03205200f005826114041c918912011003d50200b500704c410444a0440103a0500341030800b0341800c0d4080e4100c450074401c009030003002000007030b40314442e0785130320400078038024000d004240d414081a0310310001810001c1150400340000b9840c0e030f582204505d00c081d91410560107012254010481d1090348a080d81d0b4801040070369104800e200349280408840c2c3c45580 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 704101834 1250 704100584 704100629
    0xd03031b030b06090d0813030804050307080316030e01050c0a081201080d0816030b3a0309030b07120c03050610020f0303010911042d1a0d0f0e0f0304 66
    0x2c450707074090001d00c000c0c94203c0c11401c004508481d6201960b40b900e05004004c560040000018050750040000036200c61409040502d800d01e1a0401c0142c2d40091100c1d15415071200640d148a40c0e06003480600c0d1038000f401201c1b14060000754946500c00e40d03e408083c402400c0060488500b040c800c00c00d241e8950340455a03552120002100003440c40340061129551043e0f018044030561402103900c084000024400b004a004071a00d20140070904040600e5803c001c10182c200352016009000b582d0348005c0c3c5002800d10000d0700d01003030140040d080038494024192290400e0004006203825240700900421088944901500030107513801c8a82d400041d440e0701d4800000b004620b16800d21403070b48013910200b01c00c0740c8030803014400844c500610003aa050080c080034941c504010040c04c410303c01103d5644045520030340d91b82c410100441c08001c643d600c003400303d00868070070071886600b8001c080c0c421002030349002c1c0c0200540b000002100510840301c0c4d80c4101c81668803540d14 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 704103084 1250 704101834 704101841
    0x60c15070f030c0503090607110c0312040f090e07120303020d05091b04110d0908042c1f05010f0905030d050903011401060c0f111903141c0509040b0d03031b03 70
    0xc19001ba03601c140001075100b88500d0101c15000760300020764a25448004c082403404038030600c00d410003240441e0510511802210344002044000c20911800200000c4241c940d10306002c0c001c45001d004032180240f6000750116080b0382c219a604008515150a88035120307240345c0e86200002a17400600a02441c10313014a480190300d6600c0b0a181008031000d090007092005400c980c0d41304203000000381c22500031211400d21562911b4001c00c80361408070080c401d44000c3c1540307030340c0881e50000d14000d03a100b41c024064030006e0900101c012180c40e0252100000c0743d01c4554144a060705a101140c0e00c40e01a007134007070060340203122a00c0d0501800318801400d0242d40005100704c0101404616071006050405004080c00f28021310f0000100e9044030200d1514214070030001400c00410070302c00041c2400040c60030241030785001912a40d03079000602540b0307608222000c01c510000d50307220361224113400001045081070701c06a1802270060301600c0c4181120858207000145014000e02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 704104334 1250 704103084 704103091
    0x50405090a0c05011815020f0d230901050d06090218090f0402062101080c0a0803031302010e03150411030c090108100c0e04022a0304030206030105060c15070f030c0503 74
    0x14200003030701c1c1001c1c01168185200c001548401d036200d400000d58a0f43d0380d00c503806d0000c1c07541c00b42a040f41d01400c440d01c0c003a400840c000400c100300300080c000111104840200c802e0503980c1075910003015004a80714043c00a560001d946000360000345210b01e60300a0000203040c0c0090b0103000701003c20483e080c0c60842d0b812103a21002c500003401441c144000380f00c1c03801d1940107442e161000d5902c1c0c0404100c00d0300182c42550010990301c54614140400f000200985001035103145040034595045642a00000b41440324840d0803503a0765600388a150503c52100c00708039800d150604060703c1c00c504840e06c04c0c3c024012010902c0c0e032420302c40091416104880700802900940c80081401801039000328410410355000341032884e40e030750009040382c880d0312690285c082c3c0c5154007106a10140e1812510542c0200410001a01c1e00416a811140c0441d003403038503015103401082c2040c030f240415180b0000c00c0400c018959411001c1080c450649075020404402003010984007440140c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 704105584 1250 704104334 704104343
    0x2b03090c05040c020f0303040b010f050402250c0909080304142103060301090b1314010b010e130f1805120304031b14120a0806060403021507050c130501050405090a 72
    0x19001e1116081c6500040050201841180d81c00c1c1d103200301c900d08641083d202200d8007142180100070f808207803007140011b000107e4046260602140c880d95040346000400c59141e0380c10b07103958060150050b844001400700315401d12005d043c80c035084216900490301111a80482c840c12888140000307220b09507140c0925245114003100188400395810043c845603040d034072016402c0014684190f6079010300703441146111450001c1c682049001c254840c10f526aa00d04032103c02e4a03a44190b10183c00c03c1c0581c1c800c80702409548901d40038002c8544840c40103030034510715403201c0c1a200b108600c1c0a00480603202481c826040c04540c0d44001d88001d00000d44031481950a04031040f519852948a5880c802194201c0051182808001d01e0b50482c004000728243c040b140c0c12a0899a124408076900e516090a45e030010703654901031240d0394002072001ca003590400100f049a0240920014598902814040e4518020304024080c4030301541c20000421124400068550304e0075a11 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 704106834 1250 704105584 704105603
    0x11d03091903050a0308010509091b0d020d1403090109080106050306190e1c0906020111030a09050f160311090f010b09010e06030c0408060c0c2802032b0309 69
    0x10030400c14841007910420301d0300c444402000001600800650030726030300c00d8807014425898502041001c05e002400c40010b0b03000700d101c161481402c000744011440040782c0044020a003400818070303d0b54000801812101c0c11901c02c0f040c0e84000001e4558114260381e40d203816a2a9400329082e07035240c2c412260540d0005c00442d000d03820300c105081c03580d500d85c240007421144003105a45400c1c0c000213901c023032010383c904c7c0e54140c035403080c800009410240000d0100d1260342d01c44100310300c0010580030909a58450500803c00c06100301c0e034414082c01c00310341e144500110b5202c0303102d1480c0700c21031354008032084000e02d508100c04000e10171041c0720170f01121a0310b014080756065010000990400501c1400b400491b5070300c0003c3c50150901142c2182c40b9410711681e2440c0a10241c42c4486004051120301c3e054200001d100824082c035070724002c1c0135215116410107025039004000d516000340d400b04030700046182251441c82500034482030304102d0980f02501100d0f04070a010b01030510 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 704108084 1250 704106834 704106847
    0xe060612120a1209020910030314071a0705070f030e1009080a060f0b0a0e04060b0612071d0907020f010c09060203090f0a030c1e08190b060109090e010e011d03 70
    0x6003400800d6010500750129000c9881d60021b14070b14400c0307501e0112880c0d260814418164008402c02c491814051000c0c6007080c1030321003000c918075412079840c18000460001300260720840986103420360040e8070090382e45003454094484900094458022805d110750b00511500c9048440d04403841000035242165241d1141005000000c5001e50488c0c0c60300701c003c03041c1d19180c04800040c00d0605031030060381801d00d01a4107403400c50200c141b0950090016110115401c01010703008a0241020f203140f003e60300d05100326800b0f01c0340b8035500c1280103041210720354000c61490140d15050008001812185001b03a500b14034a0040c4c8005070300c18030030144541000c40301654a104010074030400c251343caa80e0580001c4072900302408150702d05010800407444c2040d03600c050030000015104042c081c0c124482c0d00126039401410007405080070820740c0c0d002d5410b20002c0c022080080c450010159101ca001c3c10f050280400d5940c41c107002a80d043e0390144010a01e00c110101942c9082c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 704109334 1250 704108084 704108087
    0xa030503190e0126090f07061d03010504080a1101060513020910080c041e080307060e1204060c06090201030e06150f031203040828030c090e04050a12020a060e060612120a 75
    0x1000810030685c510403d44c40348156502000103c0081078243c0c2e643c00501c61213000c41040341c0007040414060b0f8100014030000810302800c0d1602200c2c2880d001c4103050a184c9600d000d0308403988500e03002540c6084540e19890685c009001540b0107540703404110000510803a40304400700c4004c1e1100105100901406484460042c101d01ea4491001d44042d10342c40c01c3e909540c030044045075915a2214100340d06c1c0800d1291440007148003429508240c0b6280015007004003031b01000740900d0b13079a40407408682c002d030320520b12071044904881051400c3c2c40303003c0c44829030035403041c490f845800401145140003d1007400340c618044d0900d007943c4495852000c00c0e08150115070b141c0e400c0c600c4c0342094990001c04a00352420a91340400c80c100702d490081d02c851041e4002440e0345920800b00804204001514030350380768020301580000b840c98070102c0c20300450742401050381d418480002d00700c40000078494041c1d0011150300c0000c051868580340d440c034034010342c0701c0414002d10043c0c001d02e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 704110584 1250 704109334 704109407
    0x4020117070e010e240f2208070e1506390c0609010512090f031603090905010506070210260405060f1027050a14010b0c07050409020a030503190e01 65
    0x3111000b00394107001400300030a01320f007140d035031804110202d01c00801295800b0001c00d001403004450340ac84034204000440160b820654419000e01e0000030107240815031000030540c0800200045002c9400b15400b80074018007030780711507165210301804005240b078440e04072003261030161504c52a0018004403100840402400d04416004180c000c0c0050001031009241d00000d55007003a898200501e405004d480c0d00d90041c000e01d5103000014842502e4070001c60310f905804992030980004403070021514040b000355103204840031540d45c400720800110546005038410400d807041940c2d0564000018031007142d5075070001120070f0f810404210003034482c0c2721840c0c2c0764028040c040c15072301520069034801e81300760101c0c55550031410604650110000e01400080e0748480c50075030344145181e501d62807800b6a51090340e50300300c01400c658a50448100460b80001601c0c0c641c4040040051100f4001c41018007050121008564941c030075100c0c08020b800c4885942080480c0c1802107800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 704111834 1250 704110584 704110597
    0x12030324120203030d0617010c0e0a17010621030305160905130e12190806010f1d03070902070203070b091003020c190506010501020d03110306010804020117070e010e24 74
    0x940020401010039050714002d40000d80003000d0021070303411000030f01d88d003141c0e000381c1e0a00400481c0894114680d40b03260710101140d4010f4040c1408daa18035000300d0041c030440c2e0080d0b03d20020280c030380c1f400030680146030303c04034002e071030801142e5030b80010030480808006080f00004d9880c0c2c0148018540185c1140f50780410000010f00c1c0030002d170750305250590000b2440f04520001c1211078a8402e40c260000d1071044502d440d81d241d050003400030b0035640540f405403040c02008490000c000030307030290000c050800142100c100503600c0354000c0096004a100f030303020740509400400c2c006942001c5444020f0060080141e40814500840094100d40c8001d40780e80200881000b80292000f60b8000050080000c0d00b11545480006071800055040320014103081000c039124180e186801d03a5484042820803902943d100d1004a80c1c8150b0f071040549184001d4003446a0b080d072080002c10403150a0b215201c19042840c10008801850b403100038851006001034103080c400d0700c0c003a004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 704113084 1250 704111834 704111839
    0xc020622030c06050403031b0f02060c1e0403140c010203070809010e0d0f0b19090201170c0405030a0b0106080c0405090a0b040f06090b031501031703040302100204120303241202 78
    0x58580d070303036a110140c0e14141c5e403c4e00026294000155202c1e40c01113000c90310405800e210100c5d00c00005c0c00f80d1110401410450602e00120b051b8825500c00840294100e0944154036a070315201d107080701c000702108038140d8461103007854034900c6500000c101e40000f600195080c3c10030080000440c1c81c1c04000c41ca65802180c9000fa1100290b600106011083e109024111251408100003481458801701000c01503080c0001d400150340c0000c20b600207045030640c07001541d5180039607080c240c071440e84600d4140c4034451500c01070051000206050352660350b0741401c10b0b2240300056000340568081c1c0b950010b5500c021070700050840e4040c00440b00060000b182d4040c005402c01c0440d50113500804505843c1d60340b032940341c40c042c845c90b04442b90030a02080294110349411034108007848541c94003840c004003040c18075008004001e003005000c1c401350b41d1107486050300c00d03036000c540004901081c24914014210f07004015203400b4014044049a00b8602d418000d010300081c80d40183d8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 704114334 1250 704113084 704113097
    0x81306060f031110030b1815091017060610120608010c09050301270b070507020d060921020606010c080d230a09020306160e04140a0c02062203 63
    0x2210301d00749505100850042c0d10303288495050b98140001241e51a001804043c0391607841c401c165102c0703541d190260b11810003c034003552450030700c400c11341140350100e5015013404108001030190064000035030300c0d60f1441e01401903201400b1030b9101d6040c0c0f4030780d6010055940e04550944265240a848407102501060503680c0e00e5160f03084455001080c0d00141074154180040d0602f40100c0d0390382d6281c100b80340740031500202000000501020010500301043c0e0204005a1103202503855845c6c000f400c09c1001c00151502c0e000400c0d155008881e40110b5603040c00b500300514204c1c1c0a2070105070090005940c0307880044411150b154000c5950790000c0c000c807017000200c1e2090854004009002080401a00341000c0850030014143c6510b60b0502410070b0040e1004110b20b0382181800d40000009076840e4011b40760320340940384154000c1c0c500040021040d52040166001301d0b4960030412000c40d40e40801c0344c9640701241d540c4403441d1040e00840060300d112060f040c45500030329042 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 704115584 1250 704114334 704114339
    0x51209011508212106030a1e11060909070810091514032407090801020c0a02010e040903092105030c0303090114060306060d0816050610060801030308130606 69
    0x1c1120940035009031186521244003411100102c007041154990b02c1c299503402c3c030305a2140d07550400200300b0f04490445021020600c0c0d600c1c10002e402103a68801d80c200c1310600d0700c600303086013151042c0c0141d85040d6001030400319410b01d24202c41031048043c3c01c1460503a24800103840d0401c02401348410002c000030001b6a10269104e070000504105d030500400e5417420210780d00c0072012940651286d040300e4000d07940100045030700c4400c0d981d941c0810382d969807011805d03a00100c0c15800074100b9400003d0301d560300354000c160b0b07806e030b030b4400d80316007a441c085801807008071010042c0003404207104110920110342c407100d030100c0c0a8082c00c10061900c096a0311030342980c10000107401c50340d1001c014040401000c4c010141a1400c0c00142c0707040f031500078002940e60318050709050040401900000c2401200707802c071800c2c03c4940d0312240c1c0c1150b444c98070b0f5585800c1181c2c122140040b412011901038429100181280d030103540d01001a15540000f40c01c80385004e10403200c1c80d40e600c000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 704116834 1250 704115584 704115611
    0x1704020a0b2701080f01090b0d06060b0d32250804051009080f0309010e190606080a030e0621040807021207060f0c0203030f030103110a09020a05120901 67
    0xc1100111224240002c10700300302c107011410800d490242c0c1482007110800440d03882c0c29107441d045807401e9401182c2c180b13110b404168206010100a4079440c208140459030a000d00c0051580c001c040f94200090111032a07a14011000141c030b2703034018034400e1042180a96101101c6401891600c540da405d006010030140c0c42c03d01d4240b610020031101401c1000f401070501c02c07807400303041c0c900040c0000c0312035944444051184c41001840c0040200105d012484254801913030b5492a404442000000c010012180310801d40b007142d82d9410310002182d00c03032000c24030305845985511018001000b2000700162070b040681040c1c600004006403024500c03500f4055030041e400b0b445039654030a05401070103080141006008101d501039007080080551040050480d0780c003602d4444040750304d07480040d003075106520861483c0b250120010041c41184140404000381c210b454112144c0e407100d030341c002c0c0d00901c0c25010100320305228030424855180c5402d42e126600702c00003e801c0701071054 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 704118084 1250 704116834 704116837
    0x1208150d051c05161101020f0c0904030f210e0c06160b0c25021507020102060c0a050705150709150806150403060509060601030606021b13060e010803130b07031704020a0b 75
    0xc080e9260f01200e05e500d58156014810300301708407001006401c207590b200020480c20040035000400304801558850001441114020400145007447c00200c070301c42c4650724007800489003844400d01440440d1b20b403d02c0d24100712424500c058500702c0d00702d41d41d51125000010010040080400108103500341411408140d000d000aa0320354206038020038018440c1c100d10007011303646a803e00b0404400582c9e0009100c507445a0000e040d9555890201001c07249401400070052042c402e60621030044410004694410903040d592443d08645d42c0042a40301c03803000901d00045505080402ca0714102401006003040d891810030345031a83c0d95860314100d440495404c01c01e60420428440c4640c2d150140c00010b102610040840030a1284d800402040b051121403240c00110007142104143e40c01000041100c27003040351007981d491685a450b40d00a41c48898844400e610104800c0c1179a019141a550580d55010341d0390141440d080c5032220181007aa032096a400001980c1543c160 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 704119334 1250 704118084 704118127
    0x403060203040506010f030209060d051c0c02030c031c03020a020c0904080304030e192d0e0108060108012901020f0709060e060a0312050d06031208150d051c05 70
    0x14001aa00c1c0b606042c014100300040e003041008a11995081000d80e64070804103400001c1112003c19010032450140e19110b00842e03c0e00700680302d900c000b007107250031000d240d405c14000d805032602c8903544000c06845d600380b0340000c003030020380059002a251207603001c2c00c002d071550700448801a60703160008841c04411201120720041c0082000101a071060031400e2910040e1085200310002c815100160071150098200403107440e20120380a20304c2a001180b04044066080882a11420121584142401049820f02c10304c2c00005022805100b03071a40250869400c5180046e40d039021481441c601102034118420f069901010080c1401204000c1216144c0099443c0c64501440c052400c01408d19104d088580000c00100d080038580b8030020481e03281c0141d482c903040510000034000c035003016001101d0821440481ca82003c165030107040300d842c410042c00541400c1010045031398200505541007100305510030011801c0b050304d800510705005090041c0c4001a01c41c2c0130700309 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 704120584 1250 704119334 704119343
    0x80f0f0a0e010903050309101403070206010302091003020901180f0501080106050109090b06161a281a0114090d23030a3c080f0601020c130c050f0403 66
    0x3021a4816002240464140003e08111039035500c0c6450700e9441c6d000c0c0181641c0944d0f82014280002c034402d0384244c0485203030540d400e40780e0400311002540c0304000d010890003012400042110480d188a1a404a0340d004010100a80c20301c80d2281d80403107458424442142c50751580c1007100c200d40603643c0a880404000610540b416000401004091b40806540740c9003000a076210384650040728460701c00444401c241200920b0400d11159002800072020400f200900c1000304c408002103030078680b00340d422444008010420001c90b448084000a41403005245000c02c1d40103d00c0289075089421406082009420100b41c081811950032030303030b400402c0246c1c4041c9082d0090800741c290034500031420700c0c00030000a81548180d10448020004840216244000d418440000d0b911102c030810210102796502400388030b000c1e90b50030542c00b03801000a0055100060500031030000070728410301d03036105400d10030040030269041802c000c0100248203600d04107500410046129 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 704121834 1250 704120584 704120587
    0x40b0d06090b0610091224020d140c0703080402010e040603230309010212090a09060b070c0504051905150603130515190b030106180b011409030d0c080f0f 68
    0x518100034110b800801c01889500000081c0c0c1c26180c1c004014810765913882d203200398007621401e24031800c0c000d03800a00110340500c00c0b051001c0170540c001d80780210f21000b01b4880b50540b6480105041030813510384d0b00d881000e000c0100441d104502d0705420500606219800750072500220b0240d40f01500305443c903032a5078500f00c01038001102c2c0200708884030300c055410440701200013911010351840b0f1824040012620746550307a2910484001004142c908105860303032082c100e0855000b400b01a510301142103000a4070341840e001c1c60f8070811154028040e084940ca500400510f40540503061a070b407410700c0d0507069140c040007907002d15240280381c2840ba0f0586800d610306040000103245100da07035410700c01e0146070082e40c030040c40c0c0c4080f030100b041c2d80c890300070074014000341d44208608a0642a510180e0310250701c541c2542100fa40c07a940f41c00400d440d82c1c001e41c0700c1da07800e8503059801445078880b01c600c07403075602004c540b0403500c162401c0d855454100054208003070f40d0b80480c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 704123084 1250 704121834 704121851
    0x131d100c0e0a050a030308040510020a0806030c04050402090c0706091403190216030807030519050a020c04051306020309031c05011424090a03140303040c0e090304050d02040b0d06 79
    0x1008007501c201014115a1581820300b02400b00e2074100701e0348001004c1c03255020128080007400d000343c2d8545c10b04c40c10f0840d2142504040244082c00640d0346600901501c0740d5041a404d1501500d07206030b401030811440c0d52201040300c00c01d9400344009075512556104050001103401e001442920002c00007143c861202c1c0221194041201485c00f040d507001b904801001c5041109000803a2703004001c40741c8425a500f8240c8946c4910707040c00782d140601c1030f94400c0c80b0760414050980541c06070700321019a0390800c20301c4211041a10761705040207020940000052142d0000c41c9d01500c0300f810f0700c0c20003003442c04c165180c07001c0711850714076035481d5001400070300b50310882d0751003e40c07044038000070500c60384541003001d1100c13685036204c10360001007109081d02c4240400000b1544070280380c0b00140c000482c2c588a80050760100c0d07120405000002c1c000c104400c5207400703500044042c40c9880d18000800c058000812001c98000f5241d140d0740300c050382c0d20341250902d940907400205041d072 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 704124334 1250 704123084 704123087
    0xd020f0d0f0e0703110402070204020702030d080403120b1e060403021005040e0a2a091505070b01090b330309010509010b01050c1b060405030a031707020309131d100c 73
    0x910b42406240198030801041020800b4880c01d07a082074416035005a444960b400031074040c0c8a0b4032006501445110a0046071a5102c40c0c1a0310850107a6039584403440003034003420030356100815096000e0300000ac042440d100070895500b4005005201525107956540420000000b503c1081c001c03440c0800c080160910840f6420f5000000480c02c0051600040c9803442030004030240040341a6000c1c55003055900500302c4202a20703042d0a6484000c41c0800007d240c1d41c043e05080302c4c2c3c41051400080e180b5030b2402541c450004c010158032007485d0803a1032803155049420907803480c106003558204e800010200542c0078901802c00403c0038942101140d0a403016520000d041200810100da0386d02008102a100303c22000b9988032900e011000040c0d1600886c2c000341d502d07000b202c080c1d0b420150412401070021340401d1000302241e44407481683c89014106203550485a00441c840c000d132400c1d44600b6910f10304000d1500003d00088480d03240004a843c045142996a1038035114103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 704125584 1250 704124334 704124341
    0x6050310080c100c05070911070618021503192c0d0801121401020f0705190c090f1b05040f050919050903071209030c08031e0d020f0d0f 60
    0x2802040000c025001e4590b02042282050340c1101e01004540001582007020030311048008080c00c0030b043c8110340c2c1c4d0f41038040e240c6d03120002c216403d40c41c000808076103410181b04540c13820f8006050707142501211031351a105602c01481021106101030090000c00c1035441496511288110001aa40910110000c81c1112054040c089501c5140884c2106510408a80c190f4a0311050785c1c44a208078600308044000e00c08800545500225104c4a5041104080d11ba001d025608482514006403451880a20024000f0304905c40d4040140a100d4598001b400038491100000a0100c4015203501e070880d501c401010000d100002e042000f007c9001c40d200182c1011101d81c0b105082c901e814004400061001c0a10645c4600c0007030a062410700035194055003041400c2203401aa90000b45001d6075400103d4500302a80c40224000d04004191802d000940d08196100d003400c00001946e42c004104a00300c1903002c000350661030110386c0c090960109654808100d2640c50014501036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 704126834 1250 704125584 704125589
    0x31407032429040c09092a080f040618020d06050906010816030b10030c032d080d0e0f0d02010b030606040b0306070302070c0e0c12090118080f040f06050310 69
    0x1848010b08040051012400240c0010500701c80008020b80180d00c196040240360380501b06441c600050000000902092180b80d201c5541110075005007200065450b00310980c1e5a4554581200000b00010340301c0e03206054503070380e200321700709940e03095800128010b10820040712500e45034024020030580c100400d0b405802c40c04c014006171080001000d00b0a14648006000d80c1004401f00c1c1d031030f01ca0b55a90300040c5030840d100200482d02c904181200810302c144c0342050f44141c81102140e002c600c1038180b03509600504092a040049003058090425000110100c0c06582140514098100320010301c1490179000400c1c081000703020103007091030003860075001d41d040c0088a1525038010031010781c030000b5400c0040c0c4403400707401c120703848034100d0300701194009051080c00340101904016105120181c8015511076940c241d000d82039841c40e010111191040c01450780005111501803d03a110020101c282019501c002408007090f0940c44a00403d0000051009045402e01003102 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 704128084 1250 704126834 704126861
    0x60507020a14060a030f060e0c070c1a0f0c010608031309061715250903060b0a050f010c020301020c0a060903091a0d090219080619050603070314070324 67
    0x7500b02e502c2c00700381d0328444c000ca160100341d070311181c40030360b005a9405070b805400a0f03194581d0f07520b01008900d240ea07000e00801d0f00c2c041d030102c000154440d805608061586200145c160a2406034003c055103138001045222003035480e80b07004100c0d1042000989400c100303081c44503580701d24081004045a143e50010310741d0381501d446018194130300040f04089a2210104240250781d4120b100e001c41c000000c1217100440070300c0901e40c50030382c4121044280e90191a04020f03c280140030040c45442d00d1040a80018480c1c8804a00f507000700c420110703160000d0000f5140642003204182440c2c10720204885a42e9607550303500900d9440349000e40900407400c1c803442c240540310325140c100c0c0103000b200d01c00c03191606d01c01011034a56031001e40c1000c04101008c2c1c1c44503281d550841d1111011109100d50001d81d040c03824848030f00d80241405214060060318040e4256121b41131240c3c494008107900b80305041c800400182c0b001c0381e150107406010a1004491407491080c4e088e1800506c0e42075 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 704129334 1250 704128084 704128109
    0xa02031006050711010509010903050d0c0309060c020109031401090807050307050d080c04030204110912011e02040e1302041b030b090606090108060d03141b0708031908040f060501060507020a 84
    0x20004da601e40d21004000710900300030341c83d84c42c0b0a004803202100ea41009005000340d940602210341c00954441c0d0880c480d454050100c1c0e00c519003140c09204130b5002a00250660004101290710410b001c0d921250000010a03602000d455a502e1a40704007012610f0380e000285a101340282444030b0240711529180a03851130800d00c1c8902e00c03d000e2404064800c607644d0b6680602c0c648101c044840b00d6030054048040f14000c0032113030f4000d1428600c400b107100e0003e00d44a09803c0c807842150103880001d83c480256031103040b030004042c0702c109004c9802540c0c89486584104e4903151703940030001386603004144907503031809010b49003030040c0c62213000300000e00940d00329a030405400c03644400280e40d4071038107543d40c0c01c3c01c8442c20591440680c1040b400a8800c1c107849400c80c85c602125a001c045800d143d07590940035540307205103445007498011850008074414400c10001d13401a00030450900f002c0e000d07488200c100d5801785d00030b03070200300000741380000c5080901100c4024012070700c620 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 704130584 1250 704129334 704129347
    0x8030304020915030106090903050901030b09061003110f07080c0d080402090115120c0239060703121a040b1e010513030501090507060809010507020c060d140a0203100605 75
    0x41080e038000d08a6a030396031000002c01c83d5038500f584080c3c02070441d20310601810116040103005540108021030020382044034003240d40c103114400034018031014010003106039009100320001c0850503c0d24001c00c00c10000c88a000010101900241d402032262942d501011034043d858142102c02501c2809007032010040540c0d10110058116513400144480407500da40d401c6404200c001300d0b07841000c0c58008003c900b15030004d07207443e003090b044510000c0381c5607106108107001400e8040702c0007800c6030401e14040f400c099019080307851203400d0440b01c0355481200c42c0251201203540030303040d0090030303903e0080d464180100110f00005850101c2d2014051074040c104041c50810740d03042c0000040c1100c1070100160016006642110080043e0703502c0c1e2900c42c0d1920082d114840010f1810030109a0800062042034040c0d445a0003c09143d64070b001482030581084903c0c2c0d4406a031058000307101c4120600543c807070303810142e00581c0d9103084007811131214103580004040003810f0001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 704131834 1250 704130584 704130589
    0x161203020706270b030105030c01080c1909080105013b0103021c0c0e0103030e100207050d020a031202070611070b1803120d0f0c0f050304030c140d180803030402 71
    0x94606030340d03052400f0610582c21040009042000c59a0482c044001010010340f440760300340510305842e401c906403145860b1001c011902c8100c10358021504123410890b400155a010781e840000b8440760500020003956040c0c482e0840e04240d000c0c500e02d0b404a007000d54804003000c820b04401d0804480b405440d54050f80200b0450760500000380a01c208504600415062402014609620292410015440e1650500c82d80001e1100710301186150380d90a01c54507200503101301483c035039801408202c0c541820040900e10950050380c100d8000c4502002103034004144010006407a00101507070f074a0b110004102c007488001c80255a00480018402d40c0300400454440c41901a840784580041200185c00c0030581c5d03d042d18110400507060300031a045401c941462803941d84100000036110606481203065880004006401000041c2c0003c2c09003504400150186804c228401c220084a034078001000b9105000716070011041000201207410580c050000c1c00302031421810309601 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 704133084 1250 704131834 704131843
    0x20d060c0314010e2e0303170604020906070b0c07062c0607050d050402031002030103030216090c1e090e010f09061e0b0c0c0618040507030b0f0d210216120302 70
    0xc0075021171052078454000048120b0300c4441c0d28000c0c6a6148000c3c0e4038503003d000303048103c1800c13440d614800001072191a10344242d406020000d8074161400802c0d82c2d56400c04a030040416444090a204c0c0b00081010351141070641104a410000a130f942c640c1c1c501417229200d909141a40e010703038200320382d843c0d20200f80e804c00200f0f50000314450322244000390508090887c044803480c408000002032680c0069086c0318031090213200c00d0007079200d04c00002954a02c015250104104603100d42d80582d0075141400c00034594605950601e4449200359001803081e8080c401c0075040340d0003400841078074071562004001c8207d416524491607001c0c038500e40e00c3ca02c9004181d2601240c0c0c0e5030000c1c805e00400016808c024041a503c80c03001c8118090481e1504a0703600803440c110000e80c21074040c1c4103003103103601c0003041121003074001010003181c12009a802c451070020181000c10b140c5118a1a08a030300d480d8010b400d403188484c594000b92002644280c840654030020040829000304 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 704134334 1250 704133084 704133091
    0xc050906090928080a08010e010602030f0412021207060504080c0303070c060c05071502010614030f12091504080c030123040204020f0c0a060903090f0b190c020d060c0314010e 77
    0x340c0001000381841004030343c40e9180c050180080800240a4404950040d070050684e40c00c00c81040650362124401c07640d0f806019036048251404220901001f02c45a0300702100c1440141840700d25461080d815046c010303158030030008100301040c140140502805150307207080301a40290b04000c1c160301d410b410480c0a1090b9024410659610001d2050501c80c01c000b814034101c80000209402c14000e001304200d03c1103038480c29400d101c0810700d2030080740c04000891218001c00f0040c0c51003600d010660710840c080f035071040d842d0070b6034014294107001030001400b0007005801803040400038182500d04840e90300c0315278482246880e0030510003102068000d60140d60068507480030030046659446006da850031a8800d03081c004041060300e8010124061003552040d0100d5500d045001148503580140156403000340b05540390606c3c5c002d00007103c6082c038900f540440b0758a0700070070300c19008544143c1d8020f488032000324030960180640c0484092103454040158546203283e02c6054018 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 704135584 1250 704134334 704134363
    0x10504150b0d020c160302030d051206040c090906030c030b01080f100b040b0a0816060306120305090a0302091911030708060103050601032a020f01020705070b0a09030f0c0509060909 80
    0x2052148030703010b2507816161103c002000f03c0d60b81a80d003200c0c040013407040e071000304d111340b290783d0348030401510880c26a02e1b001c1c1901000300054590300f08020203043d00c803030400b0402c04c0c900340c0002c3c080ca02e8094400107500801c1d80350501c03401c6003444101040140c005500d2640910802868201d00003115030b01d403c164003000903904940c10004014084040c50160302118038030002c94bc0c04804101d00c03c00c01003d12052550755a2554240c00f83c80b00351146140209001c3d2140c0042401100103019001c1d0044c450f1700d000b0340b29800a59001d105480201106031011070007089410b0038480c9007003107602d8101300750440c0380c908801810072000800b001d04144c0c0303a00c081896039005c1e80010002255404042504081403c003043c22403041d400680c005220324840c4060608041c4200d07043c0c180c104c009010f900f42420650200d55026201007070030040084000000b01c2c56080318102d03800e118002d1842c06502d03010030405410740c05010281304640c40c005005417a500015a03640b550380c0c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 704136690 1106 704135584 704135587
    0x303121805061503100606020102030403120e030d022b0c0f0e0303160c091e061517070302070218090d05030705030f0a0603050a060e06010504150b 65
    0x510340c02030002d4018402169022607444100c9920400240031212022102101c0740c0441e0307555405000141d60100c01e220130190f0182d81c17021003601072001800140d44100c002a141e116013290034208950000303052248228851000f0966a5501800c940c0c0350000020f500181000002c00400904690507881d8858003400007803001e200e010f4000c42c1082c0c0440c1a0a45503035001380183c1c2c1c0403a20440010b080e0025000d49080860006900220404001c42410544045801110321004070f059480c1350150303c0020007000406556200c019034807101e81c150002e100340c00019401031007100c035040700061445400c1c1c1c001d1b4140c404844aa0800800840c0c0601041c1c0b00180019010800700d0040d428004000360005c10303242e00014442d6507569111b24040e515041100e050703072110500710b9003c3e17061060500408003558103000d5911600c050003414005030003041083c480 = true := by decide +kernel

theorem cover : BRFrame.Cov 703956834 704136690 := by
  have h0 := BRFrame.cov_init 703956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 703956834 ≤ n) (h2 : n < 704136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
